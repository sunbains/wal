#![cfg(test)]

use std::sync::Arc;
use tokio::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};
use crate::storage::{Store, Error, LSN};

pub struct TestStorage {
    should_fail: Arc<AtomicBool>,
    written_data: Arc<Mutex<Vec<u8>>>,
}

impl TestStorage {
    pub fn new(should_fail: bool) -> Self {
        Self {
            should_fail: Arc::new(AtomicBool::new(should_fail)),
            written_data: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub async fn get_written_data(&self) -> Vec<u8> {
        self.written_data.lock().await.clone()
    }
}

#[async_trait::async_trait]
impl Store for TestStorage {
    async fn persist<'a>(&'a mut self, buffer: &'a [u8]) -> Result<usize, Error> {
        assert!(buffer.len() > 0);

        // println!("Persisting data: '{:?}'", std::str::from_utf8(buffer));

        if self.should_fail.load(Ordering::Relaxed) {
            return Err(Error::StorageFull);
        }

        let mut data = self.written_data.lock().await;

        data.extend_from_slice(buffer);

        Ok(buffer.len())
    }

    async fn flush(&mut self) -> Result<LSN, Error> {
        if self.should_fail.load(Ordering::Relaxed) {
            return Err(Error::StorageFull);
        }
        Ok(LSN::new(1))
    }
} 