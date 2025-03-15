use std::sync::Arc;
use tokio::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering, AtomicU64, AtomicI64, AtomicBool};
use crate::buffer::LogBuffer;
use crate::storage::{Store, Error, LSN};
use tokio::task;

#[derive(Debug, PartialEq, Clone, Copy)]
enum LogSegmentState {
    Queued,
    Active,
    Writing,
}

struct LogSegment {
    buffer: Arc<LogBuffer>,
    // Combined state and writer count in a single atomic
    // Lower 2 bits: state (0=Queued, 1=Active, 2=Writing)
    // Upper 62 bits: writer count
    state_and_count: AtomicI64,

    // Base LSN for this buffer, when we write a log record, we add the
    // write position to this value to get the virtual LSN of the log record.
    base_lsn: AtomicU64,
}

impl LogSegment {
    const STATE_MASK: i64 = 0b11;
    const COUNT_SHIFT: i64 = 2;
    const COUNT_INC: i64 = 1 << Self::COUNT_SHIFT;
    
    const QUEUED: i64 = 0;
    const ACTIVE: i64 = 1;
    const WRITING: i64 = 2;

    fn new(buffer: Arc<LogBuffer>, state: LogSegmentState, base_lsn: u64) -> Self {
        let state_val = match state {
            LogSegmentState::Queued => Self::QUEUED,
            LogSegmentState::Active => Self::ACTIVE,
            LogSegmentState::Writing => Self::WRITING,
        };
        Self { 
            buffer,
            state_and_count: AtomicI64::new(state_val),
            base_lsn: AtomicU64::new(base_lsn),
        }
    }

    fn get_state(&self) -> LogSegmentState {
        match self.state_and_count.load(Ordering::Acquire) & Self::STATE_MASK {
            Self::QUEUED => LogSegmentState::Queued,
            Self::ACTIVE => LogSegmentState::Active,
            Self::WRITING => LogSegmentState::Writing,
            _ => unreachable!("Invalid state value"),
        }
    }

    fn get_writer_count(&self) -> i64 {
        self.state_and_count.load(Ordering::Acquire) >> Self::COUNT_SHIFT
    }

    fn set_state(&self, new_state: LogSegmentState) {
        let state_val = match new_state {
            LogSegmentState::Queued => Self::QUEUED,
            LogSegmentState::Active => Self::ACTIVE,
            LogSegmentState::Writing => Self::WRITING,
        };
        // Preserve writer count while updating state
        let old = self.state_and_count.load(Ordering::Acquire);
        let new = (old & !Self::STATE_MASK) | state_val;
        self.state_and_count.store(new, Ordering::Release);
    }

    fn try_reserve_space(&self, len: usize) -> Option<(usize, usize)> {
        loop {
            let current = self.state_and_count.load(Ordering::Acquire);
            let state = current & Self::STATE_MASK;
            
            // Check if buffer is active
            if state != Self::ACTIVE {
                return None;
            }

            // Try to increment writer count while preserving state
            let new = current + Self::COUNT_INC;
            
            // Attempt the atomic update
            match self.state_and_count.compare_exchange(
                current,
                new,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => {
                    // Successfully incremented count, now try to reserve space
                    match self.buffer.try_reserve_space(len) {
                        Some(result) => return Some(result),
                        None => {
                            // Couldn't reserve space, decrement count
                            self.state_and_count.fetch_sub(Self::COUNT_INC, Ordering::Release);
                            return None;
                        }
                    }
                }
                Err(_) => continue, // State changed, retry
            }
        }
    }

    fn write(&self, pos: usize, data: &[u8]) {
        let current = self.state_and_count.load(Ordering::Acquire);
        assert_eq!(current & Self::STATE_MASK, Self::ACTIVE, 
            "Can only write to active buffer");
        
        self.buffer.write(pos, data);
        self.state_and_count.fetch_sub(Self::COUNT_INC, Ordering::Release);
    }

    fn buffer(&self) -> &[u8] {
        self.buffer.buffer()
    }

    // Get the LSN for a given position in this buffer
    fn get_lsn(&self, pos: usize) -> LSN {
        LSN::new(self.base_lsn.load(Ordering::Acquire) + pos as u64)
    }

    // Set the base LSN for this buffer
    fn set_base_lsn(&self, lsn: u64) {
        self.base_lsn.store(lsn, Ordering::Release);
    }

    // Get the current base LSN
    fn base_lsn(&self) -> u64 {
        self.base_lsn.load(Ordering::Acquire)
    }

    pub fn print(&self) -> String {
        let mut output = String::new();
        let state = self.get_state();
        let writer_count = self.get_writer_count();
        let write_pos = self.buffer.write_pos();
        let capacity = self.buffer.size();
        let base_lsn = self.base_lsn();
        
        output.push_str(&format!("Log Segment State:\n"));
        output.push_str(&format!("State: {:?}\n", state));
        output.push_str(&format!("Writers: {}\n", writer_count));
        output.push_str(&format!("Write Position: {}/{}\n", write_pos, capacity));
        output.push_str(&format!("Usage: {:.1}%\n", (write_pos as f64 / capacity as f64) * 100.0));
        output.push_str(&format!("Base LSN: {}\n", base_lsn));
        output.push_str(&format!("Current End LSN: {}\n", base_lsn + write_pos as u64));
        output.push_str(&self.buffer.print());
        
        output
    }

    fn clear(&self) {
        self.buffer.clear();
    }
}

pub struct Log<T: Store> {
    storage: Arc<Mutex<T>>,
    current_index: AtomicUsize,
    log_segments: Box<[LogSegment]>,
    rotate_in_progress: AtomicBool,  // New atomic flag for rotation
}

impl<T: Store> Log<T> {
    fn create_segments(num_segments: usize, segment_size: usize, initial_lsn: u64) -> Box<[LogSegment]> {
        let mut segments = Vec::with_capacity(num_segments);

        for i in 0..num_segments {
            let buffer = Box::new(vec![0; segment_size]);
            let state = if i == 0 { LogSegmentState::Active } else { LogSegmentState::Queued };
            segments.push(LogSegment::new(LogBuffer::new(buffer), state, initial_lsn));
        }

        segments.into_boxed_slice()
    }

    pub fn new(lsn: LSN, num_segments: usize, segment_size: usize, storage: T) -> Self {
        assert!(num_segments > 1, "Must have at least 2 segments");

        Self {
            log_segments: Self::create_segments(num_segments, segment_size, lsn.value()),
            current_index: AtomicUsize::new(0),
            storage: Arc::new(Mutex::new(storage)),
            rotate_in_progress: AtomicBool::new(false),
        }
    }

    async fn rotate(&self) -> Result<(), Error> {
        let current_index = self.current_index.load(Ordering::Acquire);
        let current_segment = &self.log_segments[current_index];
        let next_index = (current_index + 1) % self.log_segments.len();
        let next_segment = &self.log_segments[next_index];

        // Try to acquire rotation lock
        if !self.rotate_in_progress.compare_exchange(
            false,
            true,
            Ordering::AcqRel,
            Ordering::Acquire,
        ).is_ok() {
            // Check if next segment is already active (rotation in progress)
            if next_segment.get_state() == LogSegmentState::Active {
                return Ok(());  // Can proceed with next segment
            }
            task::yield_now().await;
            return Ok(());  // Let other tasks try
        }

        // We have the rotation lock
        loop {
            let current = current_segment.state_and_count.load(Ordering::Acquire);
            let state = current & LogSegment::STATE_MASK;
            let count = current >> LogSegment::COUNT_SHIFT;

            // If not ACTIVE or writers still present, wait
            if state != LogSegment::ACTIVE || count > 0 {
                task::yield_now().await;
                continue;
            }

            // Try to transition current from ACTIVE to WRITING
            let old_state = (0 << LogSegment::COUNT_SHIFT) | LogSegment::ACTIVE;
            let new_state = (0 << LogSegment::COUNT_SHIFT) | LogSegment::WRITING;
            
            if current_segment.state_and_count.compare_exchange(
                old_state,
                new_state,
                Ordering::AcqRel,
                Ordering::Acquire,
            ).is_ok() {
                // Mark next segment as Active and update current index BEFORE persisting
                next_segment.set_state(LogSegmentState::Active);
                self.current_index.store(next_index, Ordering::Release);

                // Update next segment's base LSN
                let next_base_lsn = current_segment.base_lsn() + current_segment.buffer.write_pos() as u64;
                next_segment.set_base_lsn(next_base_lsn);

                // Persist the current segment asynchronously
                let mut storage = self.storage.lock().await;
                let _persisted_size = storage.persist(current_segment.buffer()).await?;
                current_segment.clear();
                drop(storage);

                // Mark old segment as Queued and release rotation lock
                current_segment.set_state(LogSegmentState::Queued);
                self.rotate_in_progress.store(false, Ordering::Release);
                
                return Ok(());
            }
        }
    }

    /// Returns the LSN of the log record that was written.
    pub async fn write(&self, data: &[u8]) -> Result<LSN, Error> {
        assert!(!data.is_empty(), "Cannot write empty data");

        let mut remaining_data = data;
        let mut write_lsn = None;

        while !remaining_data.is_empty() {
            let current_index = self.current_index.load(Ordering::Acquire);
            let log_segment = &self.log_segments[current_index];

            if log_segment.get_state() != LogSegmentState::Active {
                // Segment not active, yield and retry
                task::yield_now().await;
                continue;
            }

            let Some((pos, len)) = log_segment.try_reserve_space(remaining_data.len()) else {
                // Try to rotate if we can't reserve space
                self.rotate().await?;
                continue;
            };

            // Record LSN of first write
            if write_lsn.is_none() {
                write_lsn = Some(log_segment.get_lsn(pos));
            }

            if len == remaining_data.len() {
                log_segment.write(pos, remaining_data);
                break;
            } else {
                log_segment.write(pos, &remaining_data[..len]);
                remaining_data = &remaining_data[len..];
                self.rotate().await?;
            }
        }
        
        Ok(write_lsn.unwrap())
    }

    pub async fn persist(&self) -> Result<LSN, Error> {
        let current_index = self.current_index.load(Ordering::Acquire);
        let log_segment = &self.log_segments[current_index];
        
        // Only rotate if buffer is Active and has data
        if log_segment.get_state() == LogSegmentState::Active && log_segment.buffer.write_pos() > 0 {
            self.rotate().await?;
        }
        
        // Finally flush storage and return the current LSN
        let result = self.storage.lock().await.flush().await;
        
        // Ensure we return the most up-to-date LSN
        if let Ok(_) = &result {
            result
        } else {
            Ok(LSN::new(self.lsn().value()))
        }
    }

    pub async fn flush(&self) -> Result<LSN, Error> {
        self.persist().await?;
        self.storage.lock().await.flush().await
    }

    pub fn lsn(&self) -> LSN {
        let current_idx = self.current_index.load(Ordering::Acquire);
        let log_segment = &self.log_segments[current_idx];
        LSN::new(log_segment.get_lsn(log_segment.buffer.write_pos()).value())
    }

    pub async fn print(&self) -> String {
        let mut output = String::new();
        output.push_str("=== Log State ===\n");
        output.push_str(&format!("Current LSN: {}\n", self.lsn().value()));
        
        let current_idx = self.current_index.load(Ordering::Acquire);
        output.push_str(&format!("Current Log Segment Index: {}\n", current_idx));
        output.push_str(&format!("Number of Log Segments: {}\n\n", self.log_segments.len()));
        
        for (i, log_segment) in self.log_segments.iter().enumerate() {
            output.push_str(&format!("Log Segment {}{}:\n", i, if i == current_idx { " (CURRENT)" } else { "" }));
            output.push_str(&log_segment.print());
            output.push('\n');
        }
        
        output
    }
}

unsafe impl<T: Store> Send for Log<T> {}
unsafe impl<T: Store> Sync for Log<T> {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::LSN;
    use crate::test_utils::TestStorage;
    

    #[tokio::test]
    async fn test_basic_write() {
        let storage = TestStorage::new(false);
        let log = Log::new(LSN::new(0), 16, 2, storage);
        
        let data = b"0123456789";
        let lsn = log.write(data).await.unwrap();
        log.flush().await.unwrap();
        assert_eq!(lsn.value(), 0);
    }

    #[tokio::test]
    async fn test_log_large_writes_and_segment_rotation() {
        let storage = TestStorage::new(false);
        let log = Log::new(LSN::new(0), 2, 1, storage);
        
        // Write data that will force log segment rotation
        let data1 = b"0123456789";
        
        // First write should fill the log segment
        let lsn = log.write(data1).await.unwrap();
        log.flush().await.unwrap();

        assert_eq!(lsn.value(), 0);
    }

    #[tokio::test]
    async fn test_concurrent_writes() {
        let storage = TestStorage::new(false);
        let log = Arc::new(Log::new(LSN::new(0), 2, 1, storage));

        let mut handles = vec![];
        let lsns = Arc::new(Mutex::new(vec![]));

        for i in 0..9 {
            let log = log.clone();
            let lsns = lsns.clone();
            let data = format!("{} data", i);
            handles.push(tokio::spawn(async move {
                let lsn = log.write(data.as_bytes()).await.unwrap();
                lsns.lock().await.push((i, lsn));
            }));
        }

        for handle in handles {
            handle.await.unwrap();
        }

        // Get the LSNs in order of completion
        let captured_lsns = lsns.lock().await;
        println!("Writes completed in order: {:?}", captured_lsns);

        // Verify LSNs are monotonically increasing
        for window in captured_lsns.windows(2) {
            if let [(_, lsn1), (_, lsn2)] = window {
                assert!(lsn2.value() > lsn1.value(), 
                    "LSNs should be monotonically increasing");
            }
        }

        // Flush and verify all data was written
        log.flush().await.unwrap();

        let log_data = log.storage.lock().await.get_written_data().await;

        for (i, lsn) in captured_lsns.iter() {
            let expected_data = format!("{} data", i);
            let start_pos = lsn.value() as usize;
            let end_pos = start_pos + expected_data.len();
            let actual_data = &log_data[start_pos..end_pos];
            assert_eq!(actual_data, expected_data.as_bytes());
        }
    }

    #[tokio::test]
    #[should_panic(expected = "Cannot write empty data")]
    async fn test_empty_writes() {
        let storage = TestStorage::new(false);
        let log = Arc::new(Log::new(LSN::new(0), 2, 1, storage));

        // Writing empty data should panic
        log.write(b"").await.unwrap();
    }

}