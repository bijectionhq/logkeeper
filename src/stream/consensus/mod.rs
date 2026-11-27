//! Keeper-hosted stream consensus. Each stream has a Raft group, and each
//! keeper shares one durable log across all of its groups.

mod address;
mod assignment;
mod catalog;
mod client;
mod decisions;
mod journal;
mod keeper;
pub mod logging;
mod metrics;
mod network;
mod operator;
mod ownership;
mod placement;
#[cfg(test)]
mod simulation;
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
pub use crate::server::durability::SyncMode;
pub use address::Address;
pub use client::Client;
pub use journal::{ConsensusJournal, JournalConfig};
pub use keeper::{AdminConfig, Config, Recovery, RecoveryReport};
pub use logging::LogFormat;
pub use operator::{
    ADMIN_USAGE, AdminOutcome, ClusterProblems, Operator, OperatorConfig, StreamReport,
    admin_command, render as render_report,
};
pub use placement::Domains;
pub use storage::{InspectReport, SalvageReport, SegmentDump, VerifyReport, dump_segment_file};
pub use timed::TimedAuthority;

pub(super) const ALPN: &[u8] = b"logkeeper-consensus/2";
pub(super) const PREV_ALPN: &[u8] = b"logkeeper-consensus/1";
const CONTROL_ALPN: &[u8] = b"logkeeper-consensus-control/9";
const PREV_CONTROL_ALPN: &[u8] = b"logkeeper-consensus-control/8";
const REPLICATION_ALPN: &[u8] = b"logkeeper-consensus-replication/4";
const PREV_REPLICATION_ALPN: &[u8] = b"logkeeper-consensus-replication/3";
const BULK_ALPN: &[u8] = b"logkeeper-consensus-bulk/3";
const PREV_BULK_ALPN: &[u8] = b"logkeeper-consensus-bulk/2";

/// Build version advertised in liveness pings and [`KeeperStatus`].
pub const BUILD_VERSION: &str = env!("CARGO_PKG_VERSION");

/// Cluster feature level before any rolling-upgrade format finalization (N-1).
pub const CLUSTER_VERSION_V1: u32 = 1;
/// Cluster feature level that allows the formats N-1 cannot read: `LKRWAL05`
/// checkpoints, durable park marks, `LKRIDX02` snapshot roots and `LKRIMG04`
/// images. A gate names the level its format needs, not
/// `CLUSTER_VERSION_CURRENT`, so a later level never moves an older gate.
pub const CLUSTER_VERSION_V2: u32 = 2;
/// Cluster feature level enabled once all keepers run this build and an
/// operator finalizes the upgrade.
pub const CLUSTER_VERSION_CURRENT: u32 = CLUSTER_VERSION_V2;

/// Feature bits advertised in liveness pings and [`KeeperStatus`].
pub mod features {
    /// Supports N/N-1 ALPN version negotiation, feature pings, and typed
    /// `Unsupported` replies.
    pub const VERSION_NEGOTIATION: u64 = 1 << 0;
    /// Supports finalized cluster feature levels (write-version gate).
    pub const WRITE_VERSION_GATE: u64 = 1 << 1;
    /// Supports durable corruption quarantine markers and quarantine clearing.
    pub const DURABLE_QUARANTINE: u64 = 1 << 2;
    /// Supports placement changes without quarantine and retired keepers.
    pub const SOFT_PLACEMENT: u64 = 1 << 3;
    /// Runtime status: the operator is moving replicas off this keeper.
    pub const DECOMMISSIONING: u64 = 1 << 4;

    /// All features supported by this build.
    pub const SUPPORTED: u64 =
        VERSION_NEGOTIATION | WRITE_VERSION_GATE | DURABLE_QUARANTINE | SOFT_PLACEMENT;
}
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
        Term = u64,
        LeaderId = openraft::impls::leader_id_std::LeaderId<u64, NodeId>,
);

type Raft = openraft::Raft<RaftTypes, storage::StateMachine>;
type Entry = openraft::type_config::alias::EntryOf<RaftTypes>;
type LogId = openraft::type_config::alias::LogIdOf<RaftTypes>;
type Vote = openraft::type_config::alias::VoteOf<RaftTypes>;
type Membership = openraft::type_config::alias::StoredMembershipOf<RaftTypes>;

/// Snapshot metadata as images and chunk transfers carry it. It keeps the
/// OpenRaft 0.9 layout: `snapshot_id` names a transfer and marks a staged
/// image, which OpenRaft's own metadata no longer records.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct SnapshotMeta {
    last_log_id: Option<LogId>,
    last_membership: Membership,
    snapshot_id: String,
}

impl SnapshotMeta {
    fn raft(&self) -> openraft::type_config::alias::SnapshotMetaOf<RaftTypes> {
        openraft::SnapshotMeta {
            last_log_id: self.last_log_id,
            last_membership: self.last_membership.clone(),
        }
    }
}

/// Certificate-bound keeper addresses. A keeper ID is never reused after loss
/// of the directory that holds its vote and log: peers record the media
/// incarnation they first saw each keeper under, and a keeper whose media
/// was installed again under its old ID registers no replica it does not
/// hold and casts no counted vote.
///
/// An address is `IP:port` or `name:port`; a name resolves at each connect.
pub type Keepers = BTreeMap<uuid::Uuid, Address>;

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

/// What a keeper reports about itself to placement and repair.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct KeeperStatus {
    pub keeper: uuid::Uuid,
    /// Whether the keeper's media is healthy and has room for new streams.
    pub accepting: bool,
    /// Streams with an open group on the keeper.
    pub streams: u32,
    /// Streams the keeper currently leads.
    pub led: u32,
    /// For the stream asked about: whether the keeper holds a healthy
    /// replica, a quarantined one, or none.
    pub replica: Option<bool>,
    /// Build version string advertised by the keeper (empty for N-1 peers).
    pub build_version: String,
    /// Feature bits advertised by the keeper (0 for N-1 peers).
    pub features: u64,
    /// Finalized cluster feature level observed by this keeper.
    pub cluster_version: u32,
}

/// The N-1 wire representation of [`KeeperStatus`] (five fields, no build
/// version, feature bits, or cluster version).
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(super) struct KeeperStatusV1 {
    pub keeper: uuid::Uuid,
    pub accepting: bool,
    pub streams: u32,
    pub led: u32,
    pub replica: Option<bool>,
}

impl From<&KeeperStatus> for KeeperStatusV1 {
    fn from(status: &KeeperStatus) -> Self {
        Self {
            keeper: status.keeper,
            accepting: status.accepting,
            streams: status.streams,
            led: status.led,
            replica: status.replica,
        }
    }
}

impl From<KeeperStatusV1> for KeeperStatus {
    fn from(status: KeeperStatusV1) -> Self {
        Self {
            keeper: status.keeper,
            accepting: status.accepting,
            streams: status.streams,
            led: status.led,
            replica: status.replica,
            build_version: String::new(),
            features: 0,
            cluster_version: CLUSTER_VERSION_V1,
        }
    }
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

impl Stage {
    /// Whether the stage is an operator recovery's: it keeps exactly one
    /// voter, the survivor, and replaces the two lost ones.
    fn recovery(&self) -> bool {
        self.old != self.target
            && self
                .target
                .iter()
                .filter(|voter| self.old.contains(voter))
                .count()
                == 1
    }

    /// The voter a stage keeps from its old configuration when it keeps
    /// exactly one, as a recovery does.
    fn survivor(&self) -> Option<uuid::Uuid> {
        let mut kept = self.old.iter().filter(|voter| self.target.contains(voter));
        match (kept.next(), kept.next()) {
            (Some(survivor), None) => Some(*survivor),
            _ => None,
        }
    }
}

impl Genesis {
    fn valid(&self, keepers: &Keepers) -> bool {
        self.stream.0 != 0
            && self.quota_bytes > 0
            && self.voters.iter().all(|id| keepers.contains_key(id))
            && self.voters.windows(2).all(|pair| pair[0] < pair[1])
    }

    fn valid_with_retired(
        &self,
        keepers: &Keepers,
        retired: &std::collections::BTreeSet<uuid::Uuid>,
    ) -> bool {
        self.stream.0 != 0
            && self.quota_bytes > 0
            && self
                .voters
                .iter()
                .all(|id| keepers.contains_key(id) || retired.contains(id))
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Checks `value` against the bytes OpenRaft 0.9.25 wrote for it.
    fn written_by_0_9<T>(value: &T, captured: &str)
    where
        T: Serialize + DeserializeOwned + PartialEq + std::fmt::Debug,
    {
        let bytes = options().serialize(value).unwrap();
        assert_eq!(storage::hex(&bytes), captured);
        assert_eq!(&options().deserialize::<T>(&bytes).unwrap(), value);
    }

    #[test]
    fn persisted_raft_types_keep_their_encoding() {
        let node = 0x0102_0304_0506_0708_090a_0b0c_0d0e_0f10_u128;
        let log_id = LogId::new(openraft::vote::leader_id_std::CommittedLeaderId::new(7), 42);
        let nodes = [
            (node, openraft::BasicNode::new("k1:7000")),
            (node + 1, openraft::BasicNode::new("k2:7000")),
        ]
        .into_iter()
        .collect::<BTreeMap<_, _>>();
        let membership =
            openraft::Membership::new(vec![nodes.keys().copied().collect()], nodes).unwrap();
        let stored = Membership::new(Some(log_id), membership.clone());
        let (first, second) = (
            "100f0e0d0c0b0a090807060504030201",
            "110f0e0d0c0b0a090807060504030201",
        );
        let membership_hex = format!(
            "0100000000000000\
             0200000000000000{first}{second}\
             0200000000000000{first}07000000000000006b313a37303030\
             {second}07000000000000006b323a37303030"
        );
        written_by_0_9(
            &Vote::new_committed(7, node),
            &format!("070000000000000001{first}01"),
        );
        written_by_0_9(&Vote::new(7, node), &format!("070000000000000001{first}00"));
        written_by_0_9(&log_id, "07000000000000002a00000000000000");
        written_by_0_9(
            &stored,
            &format!("0107000000000000002a00000000000000{membership_hex}"),
        );
        written_by_0_9(
            &Entry {
                log_id,
                payload: openraft::EntryPayload::Blank,
            },
            "07000000000000002a0000000000000000000000",
        );
        written_by_0_9(
            &Entry {
                log_id,
                payload: openraft::EntryPayload::Normal(state::Command::Create),
            },
            "07000000000000002a000000000000000100000000000000",
        );
        written_by_0_9(
            &Entry {
                log_id,
                payload: openraft::EntryPayload::Membership(membership),
            },
            &format!("07000000000000002a0000000000000002000000{membership_hex}"),
        );
        written_by_0_9(
            &SnapshotMeta {
                last_log_id: Some(log_id),
                last_membership: stored,
                snapshot_id: "staged-1".into(),
            },
            &format!(
                "0107000000000000002a000000000000000107000000000000002a00000000000000\
                 {membership_hex}08000000000000007374616765642d31"
            ),
        );
    }
}
