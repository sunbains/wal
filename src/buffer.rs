use tokio::sync::Notify;
use tokio::sync::Mutex;
use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use crate::storage::{Error, Store, LSN};

struct Pos {
    read: AtomicUsize,
    write: AtomicUsize,
}

impl Pos {
    pub fn new() -> Self {
        Self {
            read: AtomicUsize::new(0),
            write: AtomicUsize::new(0),
        }
    }
}
pub struct LogBuffer<T: Store> {
    pos : Pos,
    lsn : LSN,
    storage: Arc<Mutex<T>>,
    buffer: Arc<[u8]>,
    pending_writes: Mutex<HashMap<usize, Arc<Notify>>>,
}

impl<T: Store> LogBuffer<T> {
    pub fn new(size: usize, storage: T) -> Arc<Self> {
        Arc::new(Self {
            pos: Pos::new(),
            storage: Arc::new(Mutex::new(storage)),
            lsn: LSN::new(0),
            pending_writes: Mutex::new(HashMap::new()),
            buffer: vec![0; size].into_boxed_slice().into(),
        })
    }

    pub async fn reserve_and_write(self: &Arc<Self>, data: &[u8], require_lsn: bool) -> Result<usize, Error> {
        let mut total_written = 0;
        let mut remaining_data = data;

        while !remaining_data.is_empty() {
            let write_pos = self.pos.write.load(Ordering::Relaxed);
            let read_pos = self.pos.read.load(Ordering::Acquire);
            
            // Calculate actual available space at these positions
            let available_space = if write_pos >= read_pos {
                self.buffer.len() - (write_pos - read_pos)
            } else {
                read_pos - write_pos
            };

            if available_space == 0 {
                self.flush().await?;
                continue;
            }

            // Calculate how much we can write with these exact positions
            let write_size = remaining_data.len().min(available_space);
            let chunk = &remaining_data[..write_size];
            let end_pos = (write_pos + write_size) % self.buffer.len();

            // Try to atomically reserve the space
            match self.pos.write.compare_exchange_weak(
                write_pos,
                end_pos,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    // Double check that read_pos hasn't moved in a way that would
                    // make our write unsafe
                    let current_read_pos = self.pos.read.load(Ordering::Acquire);
                    if current_read_pos != read_pos {
                        // Read position changed, retry with new positions
                        continue;
                    }

                    // Write position updated successfully and read position hasn't changed,
                    // now copy the data
                    if write_pos + write_size <= self.buffer.len() {
                        // Simple case: no wrapping needed
                        unsafe {
                            std::ptr::copy_nonoverlapping(
                                chunk.as_ptr(),
                                self.buffer[write_pos..].as_ptr() as *mut u8,
                                write_size,
                            );
                        }
                    } else {
                        // Handle wrapping around the buffer end
                        let first_part = self.buffer.len() - write_pos;
                        unsafe {
                            std::ptr::copy_nonoverlapping(
                                chunk.as_ptr(),
                                self.buffer[write_pos..].as_ptr() as *mut u8,
                                first_part,
                            );
                            std::ptr::copy_nonoverlapping(
                                chunk[first_part..].as_ptr(),
                                self.buffer.as_ptr() as *mut u8,
                                write_size - first_part,
                            );
                        }
                    }

                    // Update progress
                    remaining_data = &remaining_data[write_size..];
                    total_written += write_size;

                    // If we've written everything and LSN is required, wait for it
                    if remaining_data.is_empty() && require_lsn {
                        self.wait_for_lsn(self.lsn.advance(total_written as i64)).await?;
                    }
                }
                Err(_) => continue, // Another thread modified write pos, retry
            }
        }

        Ok(total_written)
    }

    async fn flush(self: &Arc<Self>) -> Result<(), Error> {
        let read_pos = self.pos.read.load(Ordering::Relaxed);
        let write_pos = self.pos.write.load(Ordering::Acquire);

        if read_pos == write_pos {
            return Ok(());
        }

        let data_to_flush: Vec<u8> = if read_pos < write_pos {
            self.buffer[read_pos..write_pos].to_vec()
        } else {
            let mut combined_data = Vec::with_capacity(self.buffer.len() - read_pos + write_pos);
            combined_data.extend_from_slice(&self.buffer[read_pos..]);
            combined_data.extend_from_slice(&self.buffer[..write_pos]);
            combined_data
        };

        // Take a mutable reference to storage before the await point
        let mut storage = self.storage.lock().await;
        let _bytes_written = storage.persist(&data_to_flush).await?;

        drop(storage); // Explicitly drop the guard

        self.pos.read.store(write_pos, Ordering::Release);

        let mut pending_writes = self.pending_writes.lock().await;
        let positions: Vec<_> = pending_writes
            .keys()
            .filter(|&&pos| pos <= write_pos)
            .copied()
            .collect();

        for pos in positions {
            if let Some(notifier) = pending_writes.remove(&pos) {
                notifier.notify_waiters();
            }
        }

        Ok(())
    }

    async fn wait_for_lsn(self: &Arc<Self>, lsn: LSN) -> Result<(), Error> {
        let notify = Arc::new(Notify::new());
        {
            let mut pending_writes = self.pending_writes.lock().await;
            pending_writes.insert(lsn.value() as usize, notify.clone());
        }

        notify.notified().await;
        Ok(())
    }
}

