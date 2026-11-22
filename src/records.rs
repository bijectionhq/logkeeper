use bytes::Bytes;
use tokio::sync::oneshot;

use crate::{Error, Result};

pub(crate) const RECORD_OVERHEAD_BYTES: usize = 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LogOffset(pub i64);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LogMetadata {
    pub offset: LogOffset,
    pub timestamp: i64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogRecord {
    pub metadata: LogMetadata,
    pub payload: Bytes,
}

impl LogRecord {
    pub(crate) fn retain(self, reservation: ReadReservation) -> Result<Self> {
        if reservation.length() < self.payload.len().saturating_add(RECORD_OVERHEAD_BYTES) {
            return Err(Error::Task("log record exceeds its read reservation".into()));
        }
        struct Retained { bytes: Bytes, _reservation: ReadReservation }
        impl AsRef<[u8]> for Retained {
            fn as_ref(&self) -> &[u8] { &self.bytes }
        }
        Ok(Self {
            metadata: self.metadata,
            payload: Bytes::from_owner(Retained { bytes: self.payload, _reservation: reservation }),
        })
    }
}

pub struct ReadReservation {
    length: usize,
    _retention: Box<dyn Send + Sync>,
}

impl ReadReservation {
    /// Retains an allocation charge until the final owner of the returned payload is dropped.
    pub fn new(length: usize, retention: impl Send + Sync + 'static) -> Self {
        Self { length, _retention: Box::new(retention) }
    }

    pub fn length(&self) -> usize { self.length }

    pub fn is_empty(&self) -> bool { self.length == 0 }
}

pub struct AppendReceipt { completion: oneshot::Receiver<Result<LogMetadata>> }

impl AppendReceipt {
    pub(crate) fn new(completion: oneshot::Receiver<Result<LogMetadata>>) -> Self { Self { completion } }

    /// Waits for the append to become durable.
    /// Dropping the receipt leaves the admitted append with its writer.
    pub async fn durable(self) -> Result<LogMetadata> {
        self.completion.await.map_err(|_| Error::Closed("append driver ended before reporting durability".into()))?
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReplayHead {
    pub metadata: LogMetadata,
    pub payload_len: usize,
    pub allocation_bound: usize,
}
