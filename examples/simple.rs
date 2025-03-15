use std::sync::Arc;
use std::time::Duration;

use async_trait::async_trait;
use tokio::time;

use log_buffer::log::Log;
use log_buffer::storage::{Store, Error, LSN};

struct NullStorage {
    lsn: LSN,
}

#[async_trait]
impl Store for NullStorage {
    async fn persist<'a>(&'a mut self, buffer: &'a [u8]) -> Result<usize, Error> {
       self.lsn = self.lsn.advance(buffer.len() as u64);
       Ok(buffer.len())
    }

    async fn flush(&mut self) -> Result<LSN, Error> {
        Ok(LSN::new(self.lsn.value()))
    }
}

async fn write_log(log: Arc<Log<NullStorage>>, id: usize) {
    let data = format!("Hello from writer {}!", id);
    for _ in 0..1024 {
        match log.write(data.as_bytes()).await {
            Ok(lsn) => println!("Writer {} got LSN: {}", id, lsn),
            Err(e) => eprintln!("Writer {} failed: {}", id, e),
        }
    }
    log.flush().await.unwrap();
}

async fn monitor_log_state(log: Arc<Log<NullStorage>>) {
    let mut interval = time::interval(Duration::from_millis(1000));
    loop {
        interval.tick().await;
        println!("\n{}", log.print().await);
    }
}

#[tokio::main]
async fn main() {
    let storage = NullStorage { lsn: LSN::new(0) };
    let log = Arc::new(Log::new(LSN::new(0), 2, 64, storage));
    
    // Start the monitoring task
    let monitor_log = log.clone();
    let monitor_handle = tokio::spawn(async move {
        monitor_log_state(monitor_log).await;
    });
    
    let mut handles = vec![];
    
    // Spawn concurrent writers
    for i in 0..100 {
        let log = log.clone();
        handles.push(tokio::spawn(async move {
            write_log(log, i).await;
        }));
    }

    // Wait for all writers to complete
    for handle in handles {
        handle.await.unwrap();
    }

    log.flush().await.unwrap();

    // Print final state
    //println!("\nFinal Log State:");
    //println!("{}", log.print().await);
    
    // Stop the monitor
    monitor_handle.abort();
}

