use std::sync::atomic::{AtomicI64, Ordering};
use std::cmp::Ordering as CmpOrdering;
use std::io;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),
    #[error("Invalid LSN: {0}")]
    InvalidLSN(i64),
    #[error("Storage is full")]
    StorageFull,
}

pub struct LSN {    
    lsn: AtomicI64,
}

impl LSN {
    pub fn new(lsn: i64) -> Self {
        Self { 
            lsn: AtomicI64::new(lsn) 
        }
    }

    pub fn value(&self) -> i64 {
        self.lsn.load(Ordering::Acquire)
    }

    pub fn is_valid(&self) -> bool {
        self.lsn.load(Ordering::Relaxed) > 0
    }

    pub fn advance(&self, lsn: i64) -> Self {
        Self {
            lsn: AtomicI64::new(self.lsn.load(Ordering::Relaxed) + lsn)
        }
    }   
}

impl PartialEq for LSN {
    fn eq(&self, other: &Self) -> bool {
        self.lsn.load(Ordering::Relaxed) == other.lsn.load(Ordering::Relaxed)
    }
}

impl Eq for LSN {}

impl PartialOrd for LSN {
    fn partial_cmp(&self, other: &Self) -> Option<CmpOrdering> {
        Some(self.cmp(other))
    }
}

impl Ord for LSN {
    fn cmp(&self, other: &Self) -> CmpOrdering {
        let self_val = self.lsn.load(Ordering::Relaxed);
        let other_val = other.lsn.load(Ordering::Relaxed);
        self_val.cmp(&other_val)
    }
}

#[async_trait::async_trait]
pub trait Store: Send + Sync {
    /// Persists data to storage and returns number of bytes written
    async fn persist(&mut self, data: &[u8]) -> Result<usize, Error>;
    
    /// Ensures all data is flushed to disk and returns the latest LSN
    async fn flush(&mut self) -> Result<LSN, Error>;
}
