//! Keeper-hosted stream consensus. Each stream has a Raft group, and each
//! keeper shares one durable log across all of its groups.

mod assignment;
mod catalog;
mod client;
mod decisions;
mod journal;
mod keeper;
mod network;
mod ownership;
mod placement;
mod state;
mod storage;
#[cfg(feature = "consensus-testing")]
pub mod testing;
mod timed;

use std::{collections::BTreeMap, io, net::SocketAddr};

use bincode::Options;
use journal_contract::{Epoch, Lsn, StreamId};
use serde::{Deserialize, Serialize, de::DeserializeOwned};

pub use super::transport::Credentials;
pub use client::Client;
pub use journal::{ConsensusJournal, JournalConfig};
pub use keeper::Config;
pub use placement::Domains;
pub use timed::TimedAuthority;

pub(super) const ALPN: &[u8] = b"logkeeper-consensus/1";
const CONTROL_ALPN: &[u8] = b"logkeeper-consensus-control/2";
const REPLICATION_ALPN: &[u8] = b"logkeeper-consensus-replication/1";
const BULK_ALPN: &[u8] = b"logkeeper-consensus-bulk/1";
const MAX_MESSAGE: u64 = 32 * 1024 * 1024;
const MAX_RECORD: usize = 4 * 1024 * 1024;
const MAX_PAGE: usize = 8 * 1024 * 1024;
const MAX_RECORDS_PER_PAGE: usize = 4096;

type NodeId = u128;

openraft::declare_raft_types!(
    RaftTypes:
        D = state::Command,
        R = state::Outcome,
        NodeId = NodeId,
        Node = openraft::BasicNode,
        SnapshotData = storage::SnapshotFile,
);

type Raft = openraft::Raft<RaftTypes>;
type Entry = openraft::Entry<RaftTypes>;
type LogId = openraft::LogId<NodeId>;
type Vote = openraft::Vote<NodeId>;
type Membership = openraft::StoredMembership<NodeId, openraft::BasicNode>;
type SnapshotMeta = openraft::SnapshotMeta<NodeId, openraft::BasicNode>;
type StorageError = openraft::StorageError<NodeId>;

/// Certificate-bound keeper addresses. A keeper ID is never reused after loss
/// of the directory that holds its vote and log.
pub type Keepers = BTreeMap<uuid::Uuid, SocketAddr>;

/// The right to write as one incarnation of an authenticated principal.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Fence {
    pub epoch: Epoch,
    pub writer: uuid::Uuid,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Sealed {
    pub fence: Fence,
    pub head: Lsn,
}

/// The most recent finalized voter configuration of a stream.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Configuration {
    pub revision: u64,
    pub voters: [uuid::Uuid; 3],
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
struct Genesis {
    stream: StreamId,
    voters: [uuid::Uuid; 3],
    quota_bytes: u64,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
struct Stage {
    stream: StreamId,
    source: u64,
    old: [uuid::Uuid; 3],
    target: [uuid::Uuid; 3],
}

impl Genesis {
    fn valid(&self, keepers: &Keepers) -> bool {
        self.stream.0 != 0
            && self.quota_bytes > 0
            && self.voters.iter().all(|id| keepers.contains_key(id))
            && self.voters.windows(2).all(|pair| pair[0] < pair[1])
    }
}

fn options() -> impl Options {
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .reject_trailing_bytes()
}

fn encode(value: &impl Serialize) -> io::Result<Vec<u8>> {
    options()
        .with_limit(MAX_MESSAGE)
        .serialize(value)
        .map_err(io::Error::other)
}

fn decode<T: DeserializeOwned>(bytes: &[u8]) -> io::Result<T> {
    options()
        .with_limit(MAX_MESSAGE)
        .deserialize(bytes)
        .map_err(io::Error::other)
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}
