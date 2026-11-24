//! Keeper protocol messages. Rules for each request are in `verification/target-journal.md`, section 3.

use bytes::Bytes;

pub use journal_contract::{Epoch, Lsn, StreamId};

/// The identity of the process that sealed an epoch. Ties at one epoch never succeed for two holders.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Holder(pub u128);

/// A keeper's identity. A replacement keeper always gets a new one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct KeeperId(pub u128);

/// One contiguous run of records written under one epoch, used to rank histories at seal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EpochRun {
    pub epoch: Epoch,
    pub first: Lsn,
    pub last: Lsn,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Request {
    Create { stream: StreamId, ensemble: [KeeperId; 3] },
    Seal { stream: StreamId, epoch: Epoch, holder: Holder },
    Sync { stream: StreamId, epoch: Epoch, from: Lsn, records: Vec<Bytes>, complete: bool },
    Append { stream: StreamId, epoch: Epoch, at: Lsn, records: Vec<Bytes>, commit: Lsn },
    Trim { stream: StreamId, epoch: Epoch, through: Lsn },
    Check { stream: StreamId, epoch: Epoch },
    Read { stream: StreamId, from: Lsn, max: u32, wait_ms: u32 },
    Delete { stream: StreamId },
}

/// A keeper's durable view of one stream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StreamView {
    pub promised: Option<(Epoch, Holder)>,
    pub synced: Option<Epoch>,
    pub end: Lsn,
    pub commit: Lsn,
    pub floor: Lsn,
    pub runs: Vec<EpochRun>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Reply {
    Created,
    Sealed(StreamView),
    Synced { end: Lsn },
    Appended { end: Lsn },
    Trimmed { floor: Lsn },
    Checked(StreamView),
    Records { floor: Lsn, records: Vec<(Lsn, Bytes)>, commit: Lsn },
    Deleted,
    Refused(Refusal),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Refusal {
    Fenced { promised: Epoch },
    NotSynced,
    Gap { end: Lsn },
    Conflict { end: Lsn },
    BelowFloor { floor: Lsn },
    AboveCommit { commit: Lsn },
    Full { floor: Lsn },
    TooLarge { max: u32 },
    NotFound,
    Deleted,
    Unauthorized,
}
