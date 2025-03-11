use async_trait::async_trait;
use log_buffer::buffer::LogBuffer;
use log_buffer::storage::{Store, Error, LSN};

struct NullStorage {
    lsn: LSN,
}

#[async_trait]
impl Store for NullStorage {
    async fn persist(&mut self, data: &[u8]) -> Result<usize, Error> {
       self.lsn = self.lsn.advance(data.len() as i64);
       Ok(data.len())
    }

    async fn flush(&mut self) -> Result<LSN, Error> {
        Ok(LSN::new(self.lsn.value()))
    }
}

#[tokio::main]
async fn main() {
    let storage = NullStorage { lsn: LSN::new(0) };
    let buffer = LogBuffer::new(1024, storage);

    let writer1 = buffer.clone();
    let writer2 = buffer.clone();

    tokio::spawn({ async move {
        let lsn = writer1.reserve_and_write(b"Hello, World 1!", true).await;
        println!("Writer1 got LSN: {}", lsn.unwrap());
    }});

    tokio::spawn(async move {
        let lsn = writer2.reserve_and_write(b"Hello, World 2!", false).await;
        println!("Writer2 got LSN: {}", lsn.unwrap());
    });

    tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
}

