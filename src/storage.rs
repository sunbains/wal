use std::fmt;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("IO error: {0}")]
    IoError(std::io::Error),
    #[error("Storage is full")]
    StorageFull,
    #[error("Buffer is full")]
    BufferFull,
    #[error("No available buffers")]
    NoAvailableBuffers,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LSN(u64);

impl LSN {
    pub fn new(value: u64) -> Self {
        Self(value)
    }

    pub fn value(&self) -> u64 {
        self.0
    }

    pub fn advance(&self, by: u64) -> Self {
        Self(self.0 + by)
    }
}

impl fmt::Display for LSN {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[async_trait::async_trait]
pub trait Store: Send + Sync {
    /// Persists data to storage returns number of bytes written
    /// The data parameter contains the buffer that should be written
    async fn persist<'a>(&'a mut self, data: &'a [u8]) -> Result<usize, Error>;
    
    /// Ensures all data is flushed to disk and returns the latest LSN
    async fn flush(&mut self) -> Result<LSN, Error>;
}
