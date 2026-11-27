//! Keeper-hosted stream consensus. Each stream has a Raft group, and each
//! keeper shares one durable log across all of its groups.

mod address;
mod assignment;
mod authority;
mod catalog;
mod client;
mod decisions;
mod journal;
mod keeper;
pub mod logging;
mod metrics;
mod network;
mod offload;
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
#[cfg(test)]
mod trace;
mod voters;

use std::{collections::BTreeMap, io, net::SocketAddr};

use bincode::Options;
use journal_contract::{Epoch, Lsn, StreamId};
use serde::{
    Deserialize, Serialize,
    de::{DeserializeOwned, SeqAccess, Visitor},
    ser::SerializeTuple,
};

pub use super::transport::Credentials;
pub use crate::server::durability::SyncMode;
pub use address::Address;
pub use authority::{Grant, Recovered, RecoveryRecord, RecoverySource};
pub use client::Client;
pub use journal::{ConsensusJournal, JournalConfig};
pub use keeper::{AdminConfig, Config, FenceProof, OffloadStatus, Recovery, RecoveryReport};
pub use logging::LogFormat;
pub use offload::OffloadConfig;
pub use operator::{
    ADMIN_USAGE, AdminOutcome, ClusterProblems, Operator, OperatorConfig, StreamReport,
    admin_command, render as render_report,
};
pub use placement::Domains;
pub use storage::{InspectReport, SalvageReport, SegmentDump, VerifyReport, dump_segment_file};
pub use timed::TimedAuthority;
pub use voters::{MAX_VOTERS, Voters};

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

/// The replicated keeper catalog's reserved stream ID.
pub const CATALOG_STREAM: StreamId = StreamId(u128::MAX);

/// Cluster feature level before any rolling-upgrade format finalization (N-1).
pub const CLUSTER_VERSION_V1: u32 = 1;
/// Cluster feature level for the WAL, parking, and snapshot formats N-1 cannot read.
pub const CLUSTER_VERSION_V2: u32 = 2;
/// Cluster feature level for atomic recovery acknowledgement.
pub const CLUSTER_VERSION_V3: u32 = 3;
/// Cluster feature level for immutable stream genesis and scoped writer sessions.
pub const CLUSTER_VERSION_V4: u32 = 4;
/// Cluster feature level of continuous offload: `Command::Offloaded`,
/// `Command::Restore` and the snapshot formats that carry offload progress.
pub const CLUSTER_VERSION_V5: u32 = 5;
/// The level offload waits for.
pub const CLUSTER_VERSION_OFFLOAD: u32 = CLUSTER_VERSION_V5;
/// Cluster feature level at which the catalog's liveness leases become
/// authoritative: keepers campaign, lead and serve reads only under a valid
/// lease, and the catalog stores keeper records.
pub const CLUSTER_VERSION_V6: u32 = 6;
/// The level liveness leases wait for.
pub const CLUSTER_VERSION_LEASES: u32 = CLUSTER_VERSION_V6;
/// Cluster feature level at which a stream may be created with five voters,
/// whose rosters older keepers cannot read (`voters.rs`).
pub const CLUSTER_VERSION_V7: u32 = 7;
/// The level five-voter streams wait for.
pub const CLUSTER_VERSION_REPLICATION: u32 = CLUSTER_VERSION_V7;
/// Enables atomic checkpoint selection and removes unchecked immutable trim.
pub const CLUSTER_VERSION_CHECKPOINT_INSTALL: u32 = 8;
/// Cluster feature level at which an operator recovery from one of two
/// surviving voters also fences the other survivor, both in the catalog
/// (`authority::Change::RecoverFrom`, `Request::RecoverStreamFrom`) and by
/// identity on that survivor (`Request::LocalProgressFencing`), which older
/// keepers cannot decode.
pub const CLUSTER_VERSION_V9: u32 = 9;
/// The level the survivor fence waits for.
pub const CLUSTER_VERSION_EXCLUSION: u32 = CLUSTER_VERSION_V9;
/// Cluster feature level of the typed recovery entry:
/// `Command::RecoverRecorded`, `Command::RecoveryEntry`, the record kind
/// bit and the snapshot formats that carry a recorded recovery.
pub const CLUSTER_VERSION_V10: u32 = 10;
/// The level the typed recovery entry waits for.
pub const CLUSTER_VERSION_RECOVERY_ENTRY: u32 = CLUSTER_VERSION_V10;
/// Enables durable custody of a selected immutable checkpoint.
pub const CLUSTER_VERSION_CHECKPOINT_CUSTODY: u32 = 11;
/// Cluster feature level enabled once all active keepers support it and an operator finalizes it.
pub const CLUSTER_VERSION_CURRENT: u32 = CLUSTER_VERSION_CHECKPOINT_CUSTODY;

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
    /// Supports the Raft command to append a marker and acknowledge recovery.
    pub const RECOVERY_MARKER: u64 = 1 << 5;
    /// Supports immutable stream genesis and scoped writer sessions.
    pub const IMMUTABLE_STREAMS: u64 = 1 << 6;
    /// Applies `Command::Offloaded` and `Command::Restore` and reads the
    /// snapshot formats that carry offload progress.
    pub const OFFLOAD: u64 = 1 << 7;

    /// Renews liveness leases with the catalog and honours them once the
    /// cluster finalizes `CLUSTER_VERSION_LEASES`.
    pub const LEASES: u64 = 1 << 8;
    /// Reads and serves five-voter rosters (`voters.rs`).
    pub const REPLICATION_FACTOR: u64 = 1 << 9;
    /// Supports checkpoint installation and its durable selection.
    pub const CHECKPOINT_INSTALL: u64 = 1 << 10;
    /// Decodes the catalog's survivor fence of a recovery
    /// (`CLUSTER_VERSION_EXCLUSION`) and refuses recovery-fenced voters by
    /// identity.
    pub const RECOVERY_EXCLUSION: u64 = 1 << 11;
    /// Applies `Command::RecoverRecorded` and `Command::RecoveryEntry` and
    /// reads typed recovery entries in snapshots and offloaded objects.
    pub const RECOVERY_ENTRY: u64 = 1 << 12;
    /// Applies exact recovery holds to the selected checkpoint and its suffix.
    pub const CHECKPOINT_CUSTODY: u64 = 1 << 13;

    /// All features supported by this build.
    pub const SUPPORTED: u64 = VERSION_NEGOTIATION
        | WRITE_VERSION_GATE
        | DURABLE_QUARANTINE
        | SOFT_PLACEMENT
        | RECOVERY_MARKER
        | IMMUTABLE_STREAMS
        | OFFLOAD
        | LEASES
        | REPLICATION_FACTOR
        | CHECKPOINT_INSTALL
        | RECOVERY_EXCLUSION
        | RECOVERY_ENTRY
        | CHECKPOINT_CUSTODY;
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
    pub voters: Voters,
}

const IMMUTABLE_GENESIS_PREFIX: StreamId = StreamId(0);
const IMMUTABLE_GENESIS_FORMAT: u64 = 4;
const IMMUTABLE_GENESIS_PREFIX_BYTES: usize = size_of::<u128>() + size_of::<u64>();

#[derive(Clone, Debug, Eq, PartialEq)]
struct Genesis {
    stream: StreamId,
    voters: Voters,
    quota_bytes: u64,
    immutable: bool,
}

// Stream zero was never a valid genesis. The prefixed layout makes a new
// genesis distinguishable even when it is embedded in a WAL or request,
// while preserving the original bytes for legacy streams. Older decoders
// encounter 4 in the length slot of the first UUID, which requires 16 bytes.
impl Serialize for Genesis {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let mut tuple = serializer.serialize_tuple(if self.immutable { 5 } else { 3 })?;
        if self.immutable {
            tuple.serialize_element(&IMMUTABLE_GENESIS_PREFIX)?;
            tuple.serialize_element(&IMMUTABLE_GENESIS_FORMAT)?;
        }
        tuple.serialize_element(&self.stream)?;
        tuple.serialize_element(&self.voters)?;
        tuple.serialize_element(&self.quota_bytes)?;
        tuple.end()
    }
}

impl<'de> Deserialize<'de> for Genesis {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        struct GenesisVisitor;

        impl<'de> Visitor<'de> for GenesisVisitor {
            type Value = Genesis;

            fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                formatter.write_str("a stream genesis")
            }

            fn visit_seq<A: SeqAccess<'de>>(self, mut elements: A) -> Result<Genesis, A::Error> {
                fn next<'de, T: Deserialize<'de>, A: SeqAccess<'de>>(
                    elements: &mut A,
                ) -> Result<T, A::Error> {
                    elements
                        .next_element()?
                        .ok_or_else(|| serde::de::Error::custom("incomplete stream genesis"))
                }

                let first = next(&mut elements)?;
                let immutable = first == IMMUTABLE_GENESIS_PREFIX;
                let stream = if immutable {
                    if next::<u64, _>(&mut elements)? != IMMUTABLE_GENESIS_FORMAT {
                        return Err(serde::de::Error::custom(
                            "unsupported stream genesis format",
                        ));
                    }
                    next(&mut elements)?
                } else {
                    first
                };
                if stream == IMMUTABLE_GENESIS_PREFIX {
                    return Err(serde::de::Error::custom("stream zero is reserved"));
                }
                Ok(Genesis {
                    stream,
                    voters: next(&mut elements)?,
                    quota_bytes: next(&mut elements)?,
                    immutable,
                })
            }
        }

        deserializer.deserialize_tuple(5, GenesisVisitor)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
struct Stage {
    stream: StreamId,
    source: u64,
    old: Voters,
    target: Voters,
}

impl Stage {
    /// The voters the stage keeps from its old configuration.
    fn kept(&self) -> usize {
        self.target
            .iter()
            .filter(|voter| self.old.contains(voter))
            .count()
    }

    /// The catalog may add two voters while retaining every old voter.
    /// Its genesis stays unchanged and only the joint transition grows it.
    fn grows_catalog(&self) -> bool {
        self.stream == CATALOG_STREAM
            && self.old.len() == 3
            && self.target.len() == 5
            && self.kept() == self.old.len()
    }

    /// Whether the stage is an operator recovery's: it keeps at least one
    /// voter but fewer than a quorum of the old configuration, its
    /// survivors (one of three; one or two of five), and replaces the lost
    /// ones. An ordinary move keeps a quorum, or moves a three-voter stream
    /// to a disjoint roster; `replace` refuses a five-voter move that would
    /// look like a recovery.
    fn recovery(&self) -> bool {
        let kept = self.kept();
        self.old != self.target && kept >= 1 && kept < self.old.quorum()
    }

    /// A recovery stage's survivors, the voters it keeps from its old
    /// configuration; none for an ordinary move. With two survivors of
    /// five, only the more advanced one may write the recovery
    /// (`keeper/recovery.rs`), so equal survivors mean the same recovering
    /// keeper.
    fn survivors(&self) -> Vec<uuid::Uuid> {
        if !self.recovery() {
            return Vec::new();
        }
        self.old
            .iter()
            .copied()
            .filter(|voter| self.target.contains(voter))
            .collect()
    }
}

impl Genesis {
    fn admits_voter_width(&self, voters: Voters) -> bool {
        voters.len() == self.voters.len()
            || (self.stream == CATALOG_STREAM && self.voters.len() == 3 && voters.len() == 5)
    }

    fn valid(&self, keepers: &Keepers) -> bool {
        self.stream.0 != 0
            && self.quota_bytes > 0
            && self.voters.iter().all(|id| keepers.contains_key(id))
            && self.voters.ascending()
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
            && self.voters.ascending()
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

    #[test]
    fn immutable_genesis_preserves_legacy_bytes_and_refuses_old_decode() {
        use super::*;

        #[derive(Serialize, Deserialize)]
        struct LegacyGenesis {
            stream: StreamId,
            voters: [uuid::Uuid; 3],
            quota_bytes: u64,
        }

        let previous = LegacyGenesis {
            stream: StreamId(18),
            voters: [1, 2, 3].map(uuid::Uuid::from_u128),
            quota_bytes: 4096,
        };
        let mut genesis = Genesis {
            stream: previous.stream,
            voters: Voters::from(previous.voters),
            quota_bytes: previous.quota_bytes,
            immutable: false,
        };
        let bytes = encode(&previous).unwrap();
        assert_eq!(encode(&genesis).unwrap(), bytes);
        assert_eq!(decode::<Genesis>(&bytes).unwrap(), genesis);
        genesis.immutable = true;
        let bytes = encode(&genesis).unwrap();
        assert_eq!(decode::<Genesis>(&bytes).unwrap(), genesis);
        assert!(decode::<LegacyGenesis>(&bytes).is_err());
    }
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
