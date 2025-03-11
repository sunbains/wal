use tokio::sync::Mutex;
use async_trait::async_trait;

use log_buffer::storage::{Store, LSN, Error};
use log_buffer::buffer::LogBuffer;

struct NullStorage {
    log: Mutex<Vec<Vec<u8>>>,
}

#[async_trait]
impl Store for NullStorage {
    async fn persist(&mut self, data: &[u8]) -> Result<usize, Error> {
        let mut log = self.log.lock().await;
        log.push(data.to_vec());
        Ok(data.len())
    }

    async fn flush(&mut self) -> Result<LSN, Error> {
        Ok(LSN::new(self.log.lock().await.len() as i64))
    }
}

#[tokio::test]
async fn test_log_buffer() {
    let storage = NullStorage { log: Mutex::new(vec![]) };
    let buffer = LogBuffer::new(4 * 1024, storage);

    let lsn1 = buffer.reserve_and_write(b"Hello, World! 1", true).await;
    let lsn2 = buffer.reserve_and_write(b"Hello, World! 2", true).await;

    assert!(lsn1.is_ok());
    assert!(lsn2.is_ok());
    assert!(lsn2.unwrap() > lsn1.unwrap());
}

