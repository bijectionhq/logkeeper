//! The logkeeper: a log server holding many named streams, and a quorum client presenting a durable stream of opaque records.
//!
//! A stream's writer holds an epoch.
//! It seals a write quorum of the stream's servers at that epoch, recovers the committed history onto them, and only then appends; a server accepts an append only from the writer it is synced to at its promised epoch, so a deposed writer cannot commit.
//! An entry is committed once a write quorum holds it durably; readers see committed entries only.

mod client;
mod error;
mod endpoint;
mod records;
mod history;
mod protocol;
mod local;
mod server;

pub mod ordered;

pub use endpoint::{JournalEndpoint, valid_journal_identity};
pub use error::{Error, ErrorKind, Result};
pub use records::{AppendReceipt, LogMetadata, LogOffset, LogRecord, ReadReservation, ReplayHead};
pub use client::{CopyFrom, Loglet, QuorumLog, QuorumRange, QuorumTail, RetainedAudit, StreamConfig, audit_retained, certify_committed_prefix, close_empty_journal, copy_retained, drop_stream, open_reader, open_reader_on, open_writer, open_writer_on, retire, retire_journal_copy, seal, trim};
pub use local::LocalListener;
pub use server::{JournalDigest, PreparedJournal, ServerOptions, inspect_retained, inspect_retained_with_prefix, serve};

/// State-machine and recovery hooks for deterministic simulations.
/// These hooks may change between releases.
#[cfg(feature = "simulation")]
pub mod simulation {
    pub use crate::client::recovery::{Holding, RepairPlan, plan_repair, winner};
    pub use crate::protocol::{Accepted, Entries, Entry, EpochRun, Failed, Refused, ResponseBody, Sealed};
    pub use crate::server::state::{Decision, Event, Held, StreamState};
}
