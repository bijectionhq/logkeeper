//! Keeper protocol messages. Rules for each request are in `verification/target-journal.md`, section 3.

use std::sync::Arc;

use bytes::Bytes;

use super::timed::{TimedEvidence, TimedOriginal, TimedSample};

pub use journal_contract::{Epoch, Identity, Lsn, StreamId};

/// A keeper's identity. A replacement keeper always gets a new one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "stream", derive(serde::Serialize, serde::Deserialize))]
pub struct KeeperId(pub u128);

/// One contiguous run of records written under one epoch, used to rank histories at seal.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EpochRun {
    pub epoch: Epoch,
    pub first: Lsn,
    pub last: Lsn,
}

/// Most entries in one `Reply::Listed`.
pub const LIST_MAX: u32 = 4096;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Request {
    Create {
        stream: StreamId,
        ensemble: [KeeperId; 3],
    },
    /// Promise only within the caller's ensemble. Stale routes are fenced after replacement.
    Seal {
        stream: StreamId,
        ensemble: [KeeperId; 3],
        epoch: Epoch,
        proposal: u128,
    },
    /// Install a range from the chosen history. `runs` covers exactly `records`;
    /// `floor` and `head` describe the prefix installed by this chunk.
    Sync {
        stream: StreamId,
        epoch: Epoch,
        floor: Lsn,
        from: Lsn,
        records: Vec<Bytes>,
        runs: Vec<EpochRun>,
        head: Lsn,
        complete: bool,
    },
    Append {
        stream: StreamId,
        epoch: Epoch,
        at: Lsn,
        records: Vec<Bytes>,
        head: Lsn,
    },
    Trim {
        stream: StreamId,
        epoch: Epoch,
        through: Lsn,
    },
    Check {
        stream: StreamId,
        epoch: Epoch,
    },
    /// Fetch accepted history under the current promise, including above `head`.
    Recover {
        stream: StreamId,
        epoch: Epoch,
        from: Lsn,
        max: u32,
    },
    /// Fetch committed history. A page can stop early at the wire byte limit.
    Read {
        stream: StreamId,
        from: Lsn,
        max: u32,
        wait_ms: u32,
    },
    Delete {
        stream: StreamId,
        ensemble: [KeeperId; 3],
    },
    /// Install a one-keeper replacement at a synced epoch. The proposer must
    /// obtain durable replies from both survivors before installing the learner.
    Replace {
        stream: StreamId,
        epoch: Epoch,
        from: [KeeperId; 3],
        to: [KeeperId; 3],
    },
    /// Write exact original bytes to an original keeper's protected staging area.
    StageOriginal {
        stream: StreamId,
        original: TimedOriginal,
        payload: Bytes,
    },
    /// Admit a singleton at its original position with its original write quorum.
    AppendOriginal {
        stream: StreamId,
        evidence: Arc<TimedEvidence>,
        payload: Bytes,
        head: Lsn,
    },
    /// Stage one certified record while installing a successor's chosen history.
    SyncOriginal {
        stream: StreamId,
        epoch: Epoch,
        floor: Lsn,
        evidence: Arc<TimedEvidence>,
        payload: Bytes,
        head: Lsn,
    },
    /// Read retained evidence for a committed position.
    ProveOriginal {
        stream: StreamId,
        at: Lsn,
    },
    /// Enumerate the keeper's live streams whose ensemble contains `member`,
    /// in ascending stream order after the exclusive cursor `stream`. Repair uses it
    /// to find the streams of a lost keeper on the survivors. It only observes state.
    List {
        stream: StreamId,
        member: KeeperId,
        max: u32,
    },
    /// Authenticated-history request, a `stream::authenticated::protocol::AuthRequest`
    /// body. It only observes stream state; a seed writes the keeper's leaf ledger.
    Authenticated {
        stream: StreamId,
        request: Bytes,
    },
    /// Node-level envelope: independent single-stream requests from one client process,
    /// decided in arrival order in one keeper round with one sync. Never nested or empty.
    Batch(Vec<Request>),
}

/// A keeper's durable view of one stream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StreamView {
    /// The epoch, authenticated identity and proposal ID of the current promise.
    pub promised: Option<(Epoch, Identity, u128)>,
    pub synced: Option<Epoch>,
    pub tail: Lsn,
    pub head: Lsn,
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
    Synced {
        tail: Lsn,
    },
    Appended {
        tail: Lsn,
    },
    Trimmed {
        floor: Lsn,
    },
    Checked(StreamView),
    Records {
        floor: Lsn,
        records: Vec<(Lsn, Bytes)>,
        head: Lsn,
    },
    OriginalSample(TimedSample),
    OriginalRecord {
        evidence: Arc<TimedEvidence>,
        payload: Bytes,
    },
    OriginalEvidence(Arc<TimedEvidence>),
    Deleted,
    Replaced,
    /// Matching streams with their ensembles. Fewer than `max` entries ends the listing.
    Listed {
        streams: Vec<(StreamId, [KeeperId; 3])>,
    },
    /// An `AuthReply` body answering `Request::Authenticated`.
    Authenticated(Bytes),
    Refused(Refusal),
    /// One reply per request of a `Request::Batch`, in request order.
    Batch(Vec<Reply>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Refusal {
    Fenced { promised: Epoch },
    NotSynced,
    Gap { head: Lsn },
    Conflict { head: Lsn },
    BelowFloor { floor: Lsn },
    AboveHead { head: Lsn },
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
    /// Identity authenticated for requests made by this transport.
    fn identity(&self) -> &Identity;

    /// Prefer the nearest member first. The default uses ensemble order.
    fn read_order(&self, ensemble: [KeeperId; 3]) -> [KeeperId; 3] {
        ensemble
    }

    /// A capacity refusal ends delivery of this call. Return a transport error if
    /// another copy can still reach the keeper.
    fn call(
        &self,
        keeper: KeeperId,
        request: Request,
    ) -> journal_contract::BoxFuture<'_, Result<Reply, TransportError>>;
}
