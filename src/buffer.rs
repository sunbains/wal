use std::sync::Arc;
use std::fmt::Write;
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct LogBuffer {
    write_pos: AtomicUsize,
    buffer: Box<Vec<u8>>,
}

impl LogBuffer {
    pub fn new(buffer: Box<Vec<u8>>) -> Arc<Self> {
        assert!(buffer.len() > 0, "Buffer size must be positive");
        
        let buffer = Arc::new(Self {
            write_pos: AtomicUsize::new(0),
            buffer: buffer.into(),
        });
        
        buffer
    }

    pub fn is_full(&self) -> bool {
        assert!(self.write_pos.load(Ordering::Acquire) <= self.size(), "Write position is out of bounds");
        self.write_pos.load(Ordering::Acquire) == self.size()
    }

    pub fn write_pos(&self) -> usize {
        self.write_pos.load(Ordering::Acquire)
    }

    pub fn buffer(&self) -> &[u8] {
        &self.buffer[..self.write_pos.load(Ordering::Acquire)]
    }

    pub fn try_reserve_space(&self, len: usize) -> Option<(usize, usize)> {
        assert!(len > 0, "Cannot reserve zero bytes");
        
        let write_pos = self.write_pos.load(Ordering::Acquire);
        let available_space = self.size() - write_pos;

        if len <= available_space {
            // Try to atomically update write_pos
            match self.write_pos.compare_exchange(
                write_pos,
                write_pos + len,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => Some((write_pos, len)),
                Err(_) => None,
            }
        } else if available_space > 0 {
            // Try to atomically update write_pos with remaining space
            match self.write_pos.compare_exchange(
                write_pos,
                self.size(),
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => Some((write_pos, available_space)),
                Err(_) => None,
            }
        } else {
            None
        }
    }

    /// Return the position of the data in the buffer
    pub fn write(&self, pos: usize, data: &[u8]) {
        assert!(!data.is_empty(), "Cannot write empty data");
        assert!(pos + data.len() <= self.size(), "Write out of bounds");

        unsafe {
            std::ptr::copy_nonoverlapping(
                data.as_ptr(),
                self.buffer[pos..].as_ptr() as *mut u8,
                data.len(),
            );
        }
    }

    /// Clears the buffer by resetting the write position atomically
    pub fn clear(&self) {
        self.write_pos.store(0, Ordering::Release);
    }

    /// Prints a detailed debug view of the buffer's current state
    pub fn print(&self) -> String {
        let mut output = String::new();
        
        // Buffer metadata
        let _ = writeln!(output, "LogBuffer State:");
        let _ = writeln!(output, "Buffer size: {}", self.size());
        
        // Positions
        let write_pos = self.write_pos.load(Ordering::Acquire);
        let _ = writeln!(output, "Write position: {}", write_pos);
        
        // Available space
        let _ = writeln!(output, "Available space: {}", self.size() - write_pos);
        
        // Buffer contents visualization
        let _ = writeln!(output, "\nBuffer contents:");
        
        // Data hexdump
        let _ = writeln!(output, "\nData hexdump:");
        let mut hex_output = String::new();
        let mut ascii_output = String::new();
        let mut count = 0;
        
        let dump_range = 0..write_pos;
        let range_end = dump_range.end;
        
        for i in dump_range {
            if count > 0 && count % 16 == 0 {
                let _ = writeln!(output, "{:08x}: {:48} |{}|", 
                    i - count, hex_output, ascii_output);
                hex_output.clear();
                ascii_output.clear();
                count = 0;
            }
            
            let byte = self.buffer[i];
            let _ = write!(hex_output, "{:02x} ", byte);
            ascii_output.push(if byte.is_ascii_graphic() {
                byte as char
            } else {
                '.'
            });
            count += 1;
        }
        
        // Print remaining bytes if any
        if !hex_output.is_empty() {
            let _ = writeln!(output, "{:08x}: {:48} |{}|",
                range_end - count, hex_output, ascii_output);
        }
        
        output
    }

    /// Returns the size of the buffer
    pub(crate) fn size(&self) -> usize {
        self.buffer.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_buffer_operations() {
        let data = "0123456789";
        let buffer = Box::new(vec![0; 16]);
        let log_buffer = LogBuffer::new(buffer);

        {
            let (pos, len) = log_buffer.try_reserve_space(data.len()).unwrap();

            assert_eq!(pos, 0);
            assert_eq!(len, data.len());

            log_buffer.write(pos, data.as_bytes());

            assert!(log_buffer.buffer[..data.len()].eq(data.as_bytes()));
        }

        {
            let (pos, len) = log_buffer.try_reserve_space(data.len()).unwrap();

            assert_eq!(pos, data.len());
            assert_eq!(len, log_buffer.size() - data.len());

            log_buffer.write(pos, &data[..len].as_bytes());

            assert!(log_buffer.buffer[pos..pos + len].eq(&data.as_bytes()[..len]));
        }

        {
            match log_buffer.try_reserve_space(data.len()) {
                Some(_) => { panic!("Should not be able to reserve space"); }
                None => { }
            }
        }
    }

    #[tokio::test]
    async fn test_print() {
        let data = "0123456789ABCDEF";
        let buffer = Box::new(vec![0; 16]);
        let log_buffer = LogBuffer::new(buffer);

        let (pos, len) = log_buffer.try_reserve_space(16).unwrap();

        assert_eq!(pos, 0);
        assert_eq!(len, data.len());

        log_buffer.write(pos, data.as_bytes());

        println!("{}", log_buffer.print());
    }
}