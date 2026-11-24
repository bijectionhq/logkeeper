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
    /// Promise only within the caller's ensemble. Stale routes are fenced after replacement.
    Seal { stream: StreamId, ensemble: [KeeperId; 3], epoch: Epoch, holder: Holder },
    /// Install a range from the chosen history. `runs` covers exactly `records`;
    /// `floor` and `commit` describe the prefix installed by the end of this chunk.
    Sync { stream: StreamId, epoch: Epoch, holder: Holder, floor: Lsn, from: Lsn, records: Vec<Bytes>, runs: Vec<EpochRun>, commit: Lsn, complete: bool },
    Append { stream: StreamId, epoch: Epoch, holder: Holder, at: Lsn, records: Vec<Bytes>, commit: Lsn },
    Trim { stream: StreamId, epoch: Epoch, holder: Holder, through: Lsn },
    Check { stream: StreamId, epoch: Epoch },
    /// Fetch accepted history under the current promise, including above `commit`.
    Recover { stream: StreamId, epoch: Epoch, holder: Holder, from: Lsn, max: u32 },
    /// Fetch committed history. A page can stop early at the wire byte limit.
    Read { stream: StreamId, from: Lsn, max: u32, wait_ms: u32 },
    Delete { stream: StreamId, ensemble: [KeeperId; 3] },
    /// Install a one-keeper replacement at a synced epoch. The proposer must
    /// obtain durable replies from both survivors before installing the learner.
    Replace { stream: StreamId, epoch: Epoch, holder: Holder, from: [KeeperId; 3], to: [KeeperId; 3] },
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
    pub ensemble: [KeeperId; 3],
    /// A replacement cannot vote until it is synced and installed in the ensemble.
    pub learner: bool,
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
    Replaced,
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
    WrongEnsemble { ensemble: [KeeperId; 3] },
}

/// A transport failure. The request may or may not have taken effect.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransportError {
    Unreachable,
    TimedOut,
    Protocol(String),
}

/// How the writer reaches keepers. The keeper side owns the TCP implementation (`src/stream/transport.rs`);
/// tests and simulation use in-memory implementations.
pub trait Transport: Send + Sync {
    fn call(&self, keeper: KeeperId, request: Request) -> journal_contract::BoxFuture<'_, Result<Reply, TransportError>>;
}
