//! Randomized fault-injection and linearizability test harness for the
//! consensus keeper (`src/stream/consensus/`).
//!
//! Runs real in-process consensus `Engine`s over `Network`/`Rpc` with seeded
//! fault injection (symmetric and asymmetric per-lane partitions, drops,
//! delays, reply-drops, duplicates, graceful stops, abrupt crashes, WAL
//! before/after-sync crash cuts, slow disk, disk-full, parking/waking,
//! membership replacement, preferred leader, replicated catalog failures,
//! offline operator recovery, and keeper wipe-and-reinitialize).
//!
//! Checks every stream against:
//! - linearizability (`journal_contract::conformance::history::linearizable`),
//! - durability (acknowledged appends never disappear unless an operator
//!   recovery acknowledged data loss),
//! - monotonic heads (within each recovery era),
//! - writer fencing (no append/trim accepted under a lower epoch after seal),
//! - batch atomicity for ambiguous `append_batch` outcomes,
//! - delete permanence,
//! - post-run cross-voter convergence.

mod bugs;
mod cluster;
mod faults;
mod history;

use std::{collections::BTreeMap, env, sync::Arc, time::Duration};

use bytes::Bytes;
use journal_contract::{Epoch, Identity, Journal, JournalError, Lsn, StreamId, reference::Limits};
use parking_lot::Mutex;
use tokio::time::timeout;
use uuid::Uuid;

use cluster::{ClusterOptions, READER, SimCluster, WAIT, WRITER_A, WRITER_B, WalCrashKind};
use faults::{Coverage, LaneFaults, LaneKey, Rng};
use history::{History, Violation};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Profile {
    /// Network partitions (symmetric/asymmetric per lane), drops, delays,
    /// reply-drops, duplicates, concurrent writers/readers, long-poll, replace,
    /// prefer_leader.
    NetworkAndMembership,
    /// Replicated catalog (`catalog_voters`) with 1- and 2-voter catalog outages,
    /// restarts, trims, and delete.
    ReplicatedCatalog,
    /// WAL crash cuts (leader & follower before/after sync), slow disk,
    /// disk-full leadership shedding.
    StorageAndCrash,
    /// Short `park_after_secs`, idle parking and waking under faults.
    ParkingAndWake,
    /// Loss of 2 of 3 voters + offline `recover_stream` + `acknowledge_recovery`
    /// + returning lost voters.
    OperatorRecovery,
    /// Mixed full-chaos schedule combining all non-wipe faults.
    FullMix,
}

impl Profile {
    const ALL: [Self; 6] = [
        Self::NetworkAndMembership,
        Self::ReplicatedCatalog,
        Self::StorageAndCrash,
        Self::ParkingAndWake,
        Self::OperatorRecovery,
        Self::FullMix,
    ];

    fn for_seed(seed: u64) -> Self {
        Self::ALL[(seed as usize) % Self::ALL.len()]
    }
}

#[derive(Clone, Copy, Debug)]
struct RunConfig {
    /// Allow `wipe_and_reinitialize` of a keeper under its old ID.
    allow_wipe: bool,
    /// Keepers accept a reused keeper ID, as before media incarnations,
    /// which reopens the Raft amnesia bug.
    ignore_reused_ids: bool,
    /// Optional forced profile override.
    profile: Option<Profile>,
    /// Number of randomized steps to generate.
    steps: usize,
}

impl RunConfig {
    fn standard() -> Self {
        Self {
            allow_wipe: false,
            ignore_reused_ids: false,
            profile: None,
            steps: 18,
        }
    }

    fn with_wipe() -> Self {
        Self {
            allow_wipe: true,
            ignore_reused_ids: false,
            profile: None,
            steps: 14,
        }
    }
}

#[derive(Clone, Debug)]
struct StreamSpec {
    stream: StreamId,
    initial_voters: [Uuid; 3],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum WriterKind {
    A,
    B,
}

impl WriterKind {
    fn principal(self) -> &'static str {
        match self {
            Self::A => WRITER_A,
            Self::B => WRITER_B,
        }
    }

    fn identity(self) -> Identity {
        Identity::from_static(self.principal())
    }
}

#[derive(Clone, Debug)]
enum ClientOp {
    Append {
        stream_idx: usize,
        writer: WriterKind,
        stale_epoch: bool,
        retry_previous: bool,
    },
    AppendBatch {
        stream_idx: usize,
        writer: WriterKind,
        count: usize,
    },
    Seal {
        stream_idx: usize,
        writer: WriterKind,
        advance: bool,
    },
    Read {
        stream_idx: usize,
        wait_ms: u64,
    },
    Head {
        stream_idx: usize,
    },
    Trim {
        stream_idx: usize,
        writer: WriterKind,
        stale_epoch: bool,
    },
}

#[derive(Clone, Debug)]
enum Step {
    /// Run 1..=3 client operations concurrently to expose race windows.
    Ops(Vec<ClientOp>),
    /// Permanently delete a stream and probe post-delete behavior.
    Delete { stream_idx: usize },
    /// Replace one voter of `stream_idx` with a spare keeper in a free domain.
    Replace { stream_idx: usize },
    /// Ask the leader of `stream_idx` to hand leadership to another voter.
    PreferLeader {
        stream_idx: usize,
        voter_slot: usize,
    },
    /// Wait for `stream_idx` to park (when `park_after_secs` is small), then wake it.
    ParkAndWake { stream_idx: usize },
    /// Symmetric partition isolating `keeper_slot` on `lanes`.
    PartitionSymmetric {
        keeper_slot: usize,
        lanes: Vec<LaneKey>,
    },
    /// Asymmetric partition dropping `from_slot -> to_slot` on `lanes`.
    PartitionAsymmetric {
        from_slot: usize,
        to_slot: usize,
        lanes: Vec<LaneKey>,
    },
    /// Probabilistic packet loss/delay/reply-drop/duplicate on `lane`.
    ImpairLane { lane: LaneKey, faults: LaneFaults },
    /// Clear all active network partitions and impairments.
    HealNetwork,
    /// Stop or abruptly crash a keeper.
    StopKeeper { keeper_slot: usize, crash: bool },
    /// Restart a stopped keeper.
    RestartKeeper { keeper_slot: usize },
    /// Arm a WAL crash cut on a voter of `stream_idx`.
    ArmWalCrash {
        stream_idx: usize,
        voter_slot: usize,
        kind: WalCrashKind,
    },
    /// Inject slow WAL sync rounds on a keeper.
    SlowDisk { keeper_slot: usize, delay_ms: u64 },
    /// Inject or clear disk-full (`Space::set_available(0)`) on a keeper.
    DiskFull { keeper_slot: usize, full: bool },
    /// Stop, wipe data + registry, re-initialize under the same ID, and restart.
    WipeAndReinit { keeper_slot: usize },
    /// Stop 1 or 2 replicated catalog voters, issue create/append, then restart.
    CatalogOutage { down_count: usize },
    /// Lose 2 of 3 voters of `stream_idx`, run offline `recover_stream` on the
    /// survivor, acknowledge recovery, restart lost voters, and resume writing.
    OperatorRecovery { stream_idx: usize },
    /// Brief sleep to allow elections, heartbeats, or repairs to advance.
    PauseMs(u64),
}

#[derive(Clone, Debug)]
struct Plan {
    seed: u64,
    profile: Profile,
    options: ClusterOptions,
    streams: Vec<StreamSpec>,
    steps: Vec<Step>,
}

/// Mutable per-stream client-side tracking used by the driver to generate
/// sensible next LSNs, sequential epochs, and payload tags.
struct StreamTracker {
    stream: StreamId,
    voters: [Uuid; 3],
    current_epoch: Epoch,
    current_owner: Option<WriterKind>,
    next_lsn: Lsn,
    last_append: Option<(Epoch, Lsn, Bytes)>,
    trimmed_to: Lsn,
    deleted: bool,
    recovered: bool,
    payload_seq: u64,
}

impl StreamTracker {
    fn new(spec: &StreamSpec) -> Self {
        Self {
            stream: spec.stream,
            voters: spec.initial_voters,
            current_epoch: Epoch(0),
            current_owner: None,
            next_lsn: Lsn(1),
            last_append: None,
            trimmed_to: Lsn(0),
            deleted: false,
            recovered: false,
            payload_seq: 0,
        }
    }

    fn make_payload(&mut self, seed: u64, size: usize) -> Bytes {
        self.payload_seq += 1;
        let tag = format!("s{seed}-id{}-n{}-", self.stream.0, self.payload_seq);
        let mut buf = tag.into_bytes();
        if buf.len() < size {
            let fill = (self.payload_seq % 251) as u8;
            buf.resize(size, fill);
        }
        Bytes::from(buf)
    }
}

struct RunSummary {
    coverage: Coverage,
    total_ops: usize,
}

/// Deterministically builds a `Plan` from `seed` and `config`.
fn generate_plan(seed: u64, config: &RunConfig) -> Plan {
    let mut rng = Rng::new(seed);
    let profile = config.profile.unwrap_or_else(|| Profile::for_seed(seed));
    let replicated_catalog = matches!(profile, Profile::ReplicatedCatalog | Profile::FullMix)
        || (!config.allow_wipe && rng.chance(1, 3));
    let park_after_secs = if matches!(profile, Profile::ParkingAndWake | Profile::FullMix) {
        2
    } else {
        3600
    };
    let options = ClusterOptions {
        replicated_catalog,
        park_after_secs,
        // Keepers that recognize a reused ID report no replica on it, and
        // leader repair replaces it.
        repair_after_secs: if config.allow_wipe && config.ignore_reused_ids {
            60
        } else {
            2
        },
        max_streams: 32,
        quota_bytes: 512 * 1024,
        max_record_bytes: 4096,
        client_deadline_ms: if config.allow_wipe { 2_500 } else { 4_000 },
        ignore_reused_ids: config.ignore_reused_ids,
    };

    let data_ids = [1, 2, 3, 4].map(Uuid::from_u128);
    let stream_count = if config.allow_wipe || matches!(profile, Profile::OperatorRecovery) {
        1
    } else {
        2
    };
    let mut streams = Vec::with_capacity(stream_count);
    for idx in 0..stream_count {
        let mut voters = if idx == 0 {
            [data_ids[0], data_ids[1], data_ids[2]]
        } else {
            [data_ids[0], data_ids[1], data_ids[3]]
        };
        voters.sort_unstable();
        streams.push(StreamSpec {
            stream: StreamId((seed as u128) * 100 + (idx as u128) + 1),
            initial_voters: voters,
        });
    }

    let mut steps = Vec::new();

    if config.allow_wipe {
        // Pure randomized schedule with wipe-and-reinitialize enabled alongside
        // partitions, stops, appends, and probes. No voter role (leader vs
        // witness vs laggard) is hard-coded; the PRNG picks voter slots 0..3.
        let mut active_down: Vec<usize> = Vec::new();
        let mut partitioned_slot: Option<usize> = None;
        let mut wiped = false;
        steps.push(Step::Ops(vec![
            ClientOp::Append {
                stream_idx: 0,
                writer: WriterKind::A,
                stale_epoch: false,
                retry_previous: false,
            },
            ClientOp::Head { stream_idx: 0 },
        ]));
        for step_idx in 0..config.steps {
            let roll = rng.range(100);
            if !wiped && step_idx >= 5 && (roll < 35 || step_idx + 2 == config.steps) {
                // Pick a random voter slot of stream 0 that is not already down
                // (or any random slot if none are down).
                let candidates: Vec<usize> = (0..3)
                    .filter(|s| !active_down.contains(s) && Some(*s) != partitioned_slot)
                    .collect();
                let slot = if candidates.is_empty() {
                    rng.range(3)
                } else {
                    candidates[rng.range(candidates.len())]
                };
                if partitioned_slot.is_some() {
                    steps.push(Step::HealNetwork);
                    partitioned_slot = None;
                }
                active_down.retain(|&s| s != slot);
                steps.push(Step::WipeAndReinit { keeper_slot: slot });
                wiped = true;
                // Wait past one election timeout so the remaining live quorum
                // can elect a leader before probing head/read.
                steps.push(Step::PauseMs(1_200));
                steps.push(Step::Ops(vec![
                    ClientOp::Head { stream_idx: 0 },
                    ClientOp::Read {
                        stream_idx: 0,
                        wait_ms: 0,
                    },
                ]));
                steps.push(Step::PauseMs(800));
                steps.push(Step::Ops(vec![ClientOp::Head { stream_idx: 0 }]));
            } else if roll < 46 {
                // Partition or stop a random voter of stream 0.
                let slot = rng.range(3);
                if partitioned_slot.is_none() && active_down.is_empty() && rng.chance(3, 4) {
                    let lanes = if rng.chance(3, 4) {
                        vec![LaneKey::Replication]
                    } else {
                        LaneKey::PEER.to_vec()
                    };
                    steps.push(Step::PartitionSymmetric {
                        keeper_slot: slot,
                        lanes,
                    });
                    partitioned_slot = Some(slot);
                } else if active_down.is_empty() && Some(slot) != partitioned_slot {
                    steps.push(Step::StopKeeper {
                        keeper_slot: slot,
                        crash: rng.chance(1, 2),
                    });
                    active_down.push(slot);
                } else if !wiped && partitioned_slot.is_some() && active_down.is_empty() {
                    steps.push(Step::HealNetwork);
                    partitioned_slot = None;
                }
            } else if roll < 86 {
                let writer = if rng.chance(4, 5) {
                    WriterKind::A
                } else {
                    WriterKind::B
                };
                if rng.chance(1, 3) {
                    steps.push(Step::Ops(vec![
                        ClientOp::AppendBatch {
                            stream_idx: 0,
                            writer,
                            count: 2 + rng.range(2),
                        },
                        ClientOp::Read {
                            stream_idx: 0,
                            wait_ms: 80,
                        },
                    ]));
                } else {
                    steps.push(Step::Ops(vec![
                        ClientOp::Append {
                            stream_idx: 0,
                            writer,
                            stale_epoch: false,
                            retry_previous: false,
                        },
                        ClientOp::Head { stream_idx: 0 },
                    ]));
                }
            } else {
                steps.push(Step::Ops(vec![ClientOp::Head { stream_idx: 0 }]));
            }
        }
        return Plan {
            seed,
            profile,
            options,
            streams,
            steps,
        };
    }

    // Standard (non-wipe) profile-guided randomized workload.
    // Phase 1: initial operations so every stream has committed records.
    for stream_idx in 0..stream_count {
        steps.push(Step::Ops(vec![
            ClientOp::Append {
                stream_idx,
                writer: WriterKind::A,
                stale_epoch: false,
                retry_previous: false,
            },
            ClientOp::Read {
                stream_idx,
                wait_ms: 100,
            },
        ]));
    }

    // Profile-specific core scenarios mixed with randomized operations.
    match profile {
        Profile::NetworkAndMembership => {
            let victim = rng.range(3);
            let other = (victim + 1) % 3;
            steps.push(Step::PartitionAsymmetric {
                from_slot: victim,
                to_slot: other,
                lanes: vec![LaneKey::Replication],
            });
            steps.push(Step::ImpairLane {
                lane: LaneKey::Control,
                faults: LaneFaults {
                    drop_pct: 10,
                    drop_reply_pct: 5,
                    duplicate_pct: 20,
                    max_delay_ms: 25,
                },
            });
            steps.push(Step::ImpairLane {
                lane: LaneKey::Application,
                faults: LaneFaults {
                    drop_pct: 0,
                    drop_reply_pct: 25,
                    duplicate_pct: 0,
                    max_delay_ms: 15,
                },
            });
            steps.push(Step::Ops(vec![
                ClientOp::AppendBatch {
                    stream_idx: 0,
                    writer: WriterKind::A,
                    count: 3,
                },
                ClientOp::Head { stream_idx: 0 },
                ClientOp::Read {
                    stream_idx: 0,
                    wait_ms: 150,
                },
            ]));
            // Clear application reply-drop before racing Seal(B) + Append(A)
            // so CI does not flake on the unfixed retry-returns-Fenced bug
            // (reproduced deterministically in bugs.rs).
            steps.push(Step::ImpairLane {
                lane: LaneKey::Application,
                faults: LaneFaults::default(),
            });
            steps.push(Step::PartitionSymmetric {
                keeper_slot: victim,
                lanes: LaneKey::PEER.to_vec(),
            });
            steps.push(Step::Ops(vec![
                ClientOp::Seal {
                    stream_idx: 0,
                    writer: WriterKind::B,
                    advance: true,
                },
                ClientOp::Append {
                    stream_idx: 0,
                    writer: WriterKind::A,
                    stale_epoch: true,
                    retry_previous: false,
                },
            ]));
            steps.push(Step::HealNetwork);
            steps.push(Step::Ops(vec![
                ClientOp::Append {
                    stream_idx: 0,
                    writer: WriterKind::B,
                    stale_epoch: false,
                    retry_previous: false,
                },
                ClientOp::Trim {
                    stream_idx: 0,
                    writer: WriterKind::B,
                    stale_epoch: false,
                },
            ]));
            steps.push(Step::PreferLeader {
                stream_idx: 0,
                voter_slot: rng.range(3),
            });
            steps.push(Step::Replace { stream_idx: 0 });
        }
        Profile::ReplicatedCatalog => {
            steps.push(Step::CatalogOutage { down_count: 1 });
            steps.push(Step::Ops(vec![
                ClientOp::AppendBatch {
                    stream_idx: 0,
                    writer: WriterKind::A,
                    count: 3,
                },
                ClientOp::Append {
                    stream_idx: 1,
                    writer: WriterKind::A,
                    stale_epoch: false,
                    retry_previous: false,
                },
            ]));
            steps.push(Step::CatalogOutage { down_count: 2 });
            steps.push(Step::Ops(vec![
                ClientOp::Seal {
                    stream_idx: 0,
                    writer: WriterKind::B,
                    advance: true,
                },
                ClientOp::Head { stream_idx: 1 },
            ]));
            steps.push(Step::Ops(vec![
                ClientOp::Trim {
                    stream_idx: 0,
                    writer: WriterKind::B,
                    stale_epoch: false,
                },
                ClientOp::Read {
                    stream_idx: 0,
                    wait_ms: 0,
                },
            ]));
            if stream_count > 1 {
                steps.push(Step::Delete { stream_idx: 1 });
            }
        }
        Profile::StorageAndCrash => {
            let wal_kinds = [
                WalCrashKind::FollowerBeforeSelection,
                WalCrashKind::FollowerAfterSelection,
                WalCrashKind::FollowerPartialSegment,
                WalCrashKind::FollowerFailedSync,
                WalCrashKind::LeaderBeforeBoundary,
                WalCrashKind::LeaderAfterBoundary,
                WalCrashKind::LeaderFailedSync,
                WalCrashKind::LeaderTornFrame,
            ];
            let first_kind = wal_kinds[rng.range(4)]; // follower cut
            let second_kind = wal_kinds[4 + rng.range(4)]; // leader cut
            let slow_slot = rng.range(3);
            steps.push(Step::SlowDisk {
                keeper_slot: slow_slot,
                delay_ms: 60,
            });
            steps.push(Step::ArmWalCrash {
                stream_idx: 0,
                voter_slot: rng.range(3),
                kind: first_kind,
            });
            steps.push(Step::Ops(vec![
                ClientOp::AppendBatch {
                    stream_idx: 0,
                    writer: WriterKind::A,
                    count: 3,
                },
                ClientOp::Head { stream_idx: 0 },
            ]));
            steps.push(Step::PauseMs(150));
            steps.push(Step::RestartKeeper { keeper_slot: 0 });
            steps.push(Step::RestartKeeper { keeper_slot: 1 });
            steps.push(Step::RestartKeeper { keeper_slot: 2 });
            // Disk full on a voter (triggers E5 leader shedding).
            let full_slot = rng.range(3);
            steps.push(Step::DiskFull {
                keeper_slot: full_slot,
                full: true,
            });
            steps.push(Step::PauseMs(600));
            steps.push(Step::Ops(vec![
                ClientOp::Append {
                    stream_idx: 0,
                    writer: WriterKind::A,
                    stale_epoch: false,
                    retry_previous: false,
                },
                ClientOp::Read {
                    stream_idx: 0,
                    wait_ms: 80,
                },
            ]));
            steps.push(Step::DiskFull {
                keeper_slot: full_slot,
                full: false,
            });
            steps.push(Step::SlowDisk {
                keeper_slot: slow_slot,
                delay_ms: 0,
            });
            steps.push(Step::ArmWalCrash {
                stream_idx: 0,
                voter_slot: rng.range(3),
                kind: second_kind,
            });
            steps.push(Step::Ops(vec![ClientOp::Append {
                stream_idx: 0,
                writer: WriterKind::A,
                stale_epoch: false,
                retry_previous: false,
            }]));
            steps.push(Step::PauseMs(150));
            steps.push(Step::RestartKeeper { keeper_slot: 0 });
            steps.push(Step::RestartKeeper { keeper_slot: 1 });
            steps.push(Step::RestartKeeper { keeper_slot: 2 });
        }
        Profile::ParkingAndWake => {
            steps.push(Step::Ops(vec![
                ClientOp::AppendBatch {
                    stream_idx: 0,
                    writer: WriterKind::A,
                    count: 3,
                },
                ClientOp::Append {
                    stream_idx: 1,
                    writer: WriterKind::A,
                    stale_epoch: false,
                    retry_previous: false,
                },
            ]));
            steps.push(Step::ParkAndWake { stream_idx: 0 });
            steps.push(Step::PartitionAsymmetric {
                from_slot: 0,
                to_slot: 1,
                lanes: vec![LaneKey::Bulk, LaneKey::Replication],
            });
            steps.push(Step::Ops(vec![
                ClientOp::Append {
                    stream_idx: 0,
                    writer: WriterKind::A,
                    stale_epoch: false,
                    retry_previous: false,
                },
                ClientOp::Head { stream_idx: 0 },
            ]));
            steps.push(Step::HealNetwork);
            steps.push(Step::StopKeeper {
                keeper_slot: 2,
                crash: false,
            });
            steps.push(Step::Ops(vec![
                ClientOp::Append {
                    stream_idx: 0,
                    writer: WriterKind::A,
                    stale_epoch: false,
                    retry_previous: false,
                },
                ClientOp::Read {
                    stream_idx: 0,
                    wait_ms: 100,
                },
            ]));
            steps.push(Step::RestartKeeper { keeper_slot: 2 });
        }
        Profile::OperatorRecovery => {
            steps.push(Step::Ops(vec![
                ClientOp::AppendBatch {
                    stream_idx: 0,
                    writer: WriterKind::A,
                    count: 3,
                },
                ClientOp::Head { stream_idx: 0 },
            ]));
            // Partition one voter briefly while appending so the survivor may
            // even lag behind the two lost voters (testing acknowledged data loss).
            steps.push(Step::PartitionSymmetric {
                keeper_slot: 0,
                lanes: LaneKey::PEER.to_vec(),
            });
            steps.push(Step::Ops(vec![ClientOp::Append {
                stream_idx: 0,
                writer: WriterKind::A,
                stale_epoch: false,
                retry_previous: false,
            }]));
            steps.push(Step::HealNetwork);
            steps.push(Step::OperatorRecovery { stream_idx: 0 });
            steps.push(Step::Ops(vec![
                ClientOp::AppendBatch {
                    stream_idx: 0,
                    writer: WriterKind::B,
                    count: 2,
                },
                ClientOp::Read {
                    stream_idx: 0,
                    wait_ms: 0,
                },
            ]));
            // Stale pre-recovery writer must remain fenced.
            steps.push(Step::Ops(vec![ClientOp::Append {
                stream_idx: 0,
                writer: WriterKind::A,
                stale_epoch: true,
                retry_previous: false,
            }]));
        }
        Profile::FullMix => {
            // Mix randomized ops, per-lane faults, crash/restart, replace, trim.
            steps.push(Step::ImpairLane {
                lane: LaneKey::Replication,
                faults: LaneFaults {
                    drop_pct: 10,
                    drop_reply_pct: 10,
                    duplicate_pct: 15,
                    max_delay_ms: 20,
                },
            });
            steps.push(Step::SlowDisk {
                keeper_slot: rng.range(3),
                delay_ms: 40,
            });
            for _ in 0..4 {
                let s = rng.range(stream_count);
                let w = if rng.chance(2, 3) {
                    WriterKind::A
                } else {
                    WriterKind::B
                };
                steps.push(Step::Ops(vec![
                    ClientOp::Append {
                        stream_idx: s,
                        writer: w,
                        stale_epoch: rng.chance(1, 5),
                        retry_previous: rng.chance(1, 5),
                    },
                    ClientOp::Read {
                        stream_idx: s,
                        wait_ms: if rng.chance(1, 2) { 120 } else { 0 },
                    },
                ]));
            }
            let down = rng.range(3);
            steps.push(Step::StopKeeper {
                keeper_slot: down,
                crash: rng.chance(1, 2),
            });
            steps.push(Step::Ops(vec![
                ClientOp::Seal {
                    stream_idx: 0,
                    writer: WriterKind::B,
                    advance: true,
                },
                ClientOp::Head { stream_idx: 0 },
            ]));
            steps.push(Step::HealNetwork);
            steps.push(Step::RestartKeeper { keeper_slot: down });
            steps.push(Step::Replace { stream_idx: 0 });
            steps.push(Step::PreferLeader {
                stream_idx: 0,
                voter_slot: rng.range(3),
            });
        }
    }

    // Randomized tail of mixed operations so each seed exercises unique interleavings.
    let extra = config.steps.saturating_sub(steps.len()).min(8);
    for _ in 0..extra {
        let s = rng.range(stream_count);
        let w = if rng.chance(1, 2) {
            WriterKind::A
        } else {
            WriterKind::B
        };
        match rng.range(7) {
            0 | 1 => steps.push(Step::Ops(vec![
                ClientOp::Append {
                    stream_idx: s,
                    writer: w,
                    stale_epoch: rng.chance(1, 4),
                    retry_previous: rng.chance(1, 4),
                },
                ClientOp::Head { stream_idx: s },
            ])),
            2 => steps.push(Step::Ops(vec![
                ClientOp::AppendBatch {
                    stream_idx: s,
                    writer: w,
                    count: 2 + rng.range(2),
                },
                ClientOp::Read {
                    stream_idx: s,
                    wait_ms: 80,
                },
            ])),
            3 => steps.push(Step::Ops(vec![ClientOp::Seal {
                stream_idx: s,
                writer: w,
                advance: rng.chance(2, 3),
            }])),
            4 => steps.push(Step::Ops(vec![
                ClientOp::Trim {
                    stream_idx: s,
                    writer: w,
                    stale_epoch: rng.chance(1, 4),
                },
                ClientOp::Read {
                    stream_idx: s,
                    wait_ms: 0,
                },
            ])),
            5 => steps.push(Step::Ops(vec![
                ClientOp::Read {
                    stream_idx: s,
                    wait_ms: 120,
                },
                ClientOp::Head { stream_idx: s },
            ])),
            _ => {
                let slot = rng.range(3);
                steps.push(Step::StopKeeper {
                    keeper_slot: slot,
                    crash: rng.chance(1, 2),
                });
                steps.push(Step::Ops(vec![ClientOp::Head { stream_idx: s }]));
                steps.push(Step::RestartKeeper { keeper_slot: slot });
            }
        }
    }

    Plan {
        seed,
        profile,
        options,
        streams,
        steps,
    }
}

/// Executes `plan` on a fresh `SimCluster`, heals faults, verifies
/// cross-voter convergence and all safety/linearizability/durability invariants.
async fn execute_plan(plan: &Plan) -> Result<RunSummary, Violation> {
    let mut cluster = SimCluster::start(plan.seed, plan.options.clone()).await;
    let limits = Limits {
        max_record_bytes: plan.options.max_record_bytes,
        stream_quota_bytes: plan.options.quota_bytes,
    };
    let history = Arc::new(History::new(limits));
    let mut rng = Rng::new(plan.seed ^ 0x243f_6a88_85a3_08d3);

    let default_voters = plan.streams[0].initial_voters;
    let journal_a = cluster.journal(WRITER_A, default_voters);
    let journal_b = cluster.journal(WRITER_B, default_voters);
    let journal_r = cluster.journal(READER, default_voters);

    let trackers = Arc::new(Mutex::new(
        plan.streams
            .iter()
            .map(StreamTracker::new)
            .collect::<Vec<_>>(),
    ));

    let mut total_ops = 0usize;

    // Setup: create and initially seal every stream under WRITER_A at Epoch(1).
    for (idx, spec) in plan.streams.iter().enumerate() {
        let j = cluster.journal(WRITER_A, spec.initial_voters);
        let caller = WriterKind::A.identity();
        // A loaded machine can time a fresh cluster's first calls out, so
        // retry them for a while; each attempt is recorded.
        let setup = tokio::time::Instant::now() + Duration::from_secs(30);
        loop {
            let inv = history.tick();
            let res = j.create(spec.stream).await;
            let resp = history.tick();
            history.record_create(spec.stream, &caller, inv, resp, &res);
            total_ops += 1;
            match res {
                Err(JournalError::Unavailable) if tokio::time::Instant::now() < setup => {}
                res => break res.expect("initial create succeeds with healthy cluster"),
            }
        }

        let res = loop {
            let inv = history.tick();
            let res = j.seal(spec.stream, Epoch(1)).await;
            let resp = history.tick();
            history.record_seal(spec.stream, &caller, Epoch(1), inv, resp, &res);
            total_ops += 1;
            match res {
                Err(JournalError::Unavailable) if tokio::time::Instant::now() < setup => {}
                res => break res,
            }
        };
        if let Ok(head) = res {
            let mut lock = trackers.lock();
            lock[idx].current_epoch = Epoch(1);
            lock[idx].current_owner = Some(WriterKind::A);
            lock[idx].next_lsn = Lsn(head.0 + 1);
        }
    }

    // Canonicalize keeper slots relative to stream 0's initial leader so a
    // given seed targets the same Raft roles (leader vs followers) on replay
    // and during plan shrinking regardless of initial election timer races.
    let mut slot_map: Vec<Uuid> = Vec::with_capacity(cluster.all_ids.len());
    if let Some(leader) = cluster.leader(plan.streams[0].stream).await {
        slot_map.push(leader);
    }
    for id in plan.streams[0].initial_voters {
        if !slot_map.contains(&id) {
            slot_map.push(id);
        }
    }
    for id in cluster.all_ids {
        if !slot_map.contains(&id) {
            slot_map.push(id);
        }
    }

    // Execute plan steps.
    for step in &plan.steps {
        // Reap any keeper whose WAL thread terminated from an armed WAL fault.
        cluster.reap_crashed().await;

        match step {
            Step::Ops(ops) => {
                total_ops += run_concurrent_ops(
                    ops,
                    plan.seed,
                    &journal_a,
                    &journal_b,
                    &journal_r,
                    &trackers,
                    &history,
                    &cluster.faults,
                    &mut rng,
                )
                .await;
                // Fail fast if a durability, head-regression, fence, or
                // linearizability violation already occurred.
                if let Err(violation) = history.check_all(&BTreeMap::new()) {
                    cluster.stop_all().await;
                    return Err(violation);
                }
            }
            Step::Delete { stream_idx } => {
                let (stream, already) = {
                    let lock = trackers.lock();
                    (lock[*stream_idx].stream, lock[*stream_idx].deleted)
                };
                if already {
                    continue;
                }
                let caller = WriterKind::A.identity();
                let inv = history.tick();
                let res = journal_a.delete(stream).await;
                let resp = history.tick();
                history.record_delete(stream, &caller, inv, resp, &res);
                total_ops += 1;
                if res.is_ok() {
                    trackers.lock()[*stream_idx].deleted = true;
                    cluster.faults.hit("op:delete");
                    // Probe post-delete refusal.
                    let inv = history.tick();
                    let head_res = journal_r.head(stream).await;
                    let resp = history.tick();
                    history.record_head(
                        stream,
                        &Identity::from_static(READER),
                        inv,
                        resp,
                        &head_res,
                    );
                    total_ops += 1;
                }
            }
            Step::Replace { stream_idx } => {
                let (stream, deleted) = {
                    let lock = trackers.lock();
                    (lock[*stream_idx].stream, lock[*stream_idx].deleted)
                };
                if deleted {
                    continue;
                }
                if let Ok(config) = journal_a.client().configuration(stream).await {
                    let current = config.voters;
                    let spare = cluster
                        .all_ids
                        .iter()
                        .copied()
                        .find(|id| !current.contains(id) && cluster.is_running(*id));
                    if let Some(spare) = spare {
                        let drop_idx = rng.range(3);
                        let mut next = current;
                        next[drop_idx] = spare;
                        next.sort_unstable();
                        if let Ok(updated) = journal_a
                            .client()
                            .replace(stream, config.revision, next)
                            .await
                        {
                            trackers.lock()[*stream_idx].voters = updated.voters;
                            cluster.faults.hit("op:replace");
                        }
                    }
                }
            }
            Step::PreferLeader {
                stream_idx,
                voter_slot,
            } => {
                let (stream, voters, deleted) = {
                    let lock = trackers.lock();
                    (
                        lock[*stream_idx].stream,
                        lock[*stream_idx].voters,
                        lock[*stream_idx].deleted,
                    )
                };
                if !deleted {
                    let target = voters[*voter_slot % 3];
                    if journal_a
                        .client()
                        .prefer_leader(stream, target)
                        .await
                        .is_ok()
                    {
                        cluster.faults.hit("op:prefer_leader");
                    }
                }
            }
            Step::ParkAndWake { stream_idx } => {
                let (stream, voters, deleted) = {
                    let lock = trackers.lock();
                    (
                        lock[*stream_idx].stream,
                        lock[*stream_idx].voters,
                        lock[*stream_idx].deleted,
                    )
                };
                if deleted {
                    continue;
                }
                // Wait up to 8s for the idle stream to park on every running voter.
                let parked = timeout(Duration::from_secs(8), async {
                    while !cluster.is_parked_on(stream, &voters).await {
                        tokio::time::sleep(Duration::from_millis(40)).await;
                    }
                })
                .await
                .is_ok();
                if parked {
                    cluster.faults.hit("op:parked");
                    // Wake via a fresh head and a read.
                    let inv = history.tick();
                    let res = journal_r.head(stream).await;
                    let resp = history.tick();
                    history.record_head(stream, &Identity::from_static(READER), inv, resp, &res);
                    total_ops += 1;
                    if res.is_ok() {
                        cluster.faults.hit("op:woke_parked");
                    }
                }
            }
            Step::PartitionSymmetric { keeper_slot, lanes } => {
                let target = slot_map[*keeper_slot % slot_map.len()];
                let others: Vec<Uuid> = slot_map
                    .iter()
                    .copied()
                    .filter(|id| *id != target)
                    .collect();
                cluster
                    .faults
                    .partition_symmetric(&[target], &others, lanes);
            }
            Step::PartitionAsymmetric {
                from_slot,
                to_slot,
                lanes,
            } => {
                let from = slot_map[*from_slot % slot_map.len()];
                let to = slot_map[*to_slot % slot_map.len()];
                if from != to {
                    cluster.faults.partition_asymmetric(from, to, lanes);
                }
            }
            Step::ImpairLane { lane, faults } => {
                cluster.faults.set_lane_faults(*lane, *faults);
            }
            Step::HealNetwork => {
                cluster.faults.heal_all();
            }
            Step::StopKeeper { keeper_slot, crash } => {
                let id = slot_map[*keeper_slot % slot_map.len()];
                if *crash {
                    cluster.crash(id).await;
                } else {
                    cluster.stop_graceful(id).await;
                }
            }
            Step::RestartKeeper { keeper_slot } => {
                let id = slot_map[*keeper_slot % slot_map.len()];
                if !cluster.is_running(id) {
                    cluster.restart(id).await;
                }
            }
            Step::ArmWalCrash {
                stream_idx,
                voter_slot,
                kind,
            } => {
                let (stream, voters, deleted) = {
                    let lock = trackers.lock();
                    (
                        lock[*stream_idx].stream,
                        lock[*stream_idx].voters,
                        lock[*stream_idx].deleted,
                    )
                };
                if deleted {
                    continue;
                }
                let leader = cluster.leader(stream).await;
                let target = match kind {
                    WalCrashKind::LeaderBeforeBoundary
                    | WalCrashKind::LeaderAfterBoundary
                    | WalCrashKind::LeaderFailedSync
                    | WalCrashKind::LeaderTornFrame => leader.unwrap_or(voters[*voter_slot % 3]),
                    _ => voters
                        .into_iter()
                        .find(|id| Some(*id) != leader && cluster.is_running(*id))
                        .unwrap_or(voters[*voter_slot % 3]),
                };
                cluster.arm_wal_fault(target, stream, *kind);
            }
            Step::SlowDisk {
                keeper_slot,
                delay_ms,
            } => {
                let id = slot_map[*keeper_slot % slot_map.len()];
                cluster.set_slow_disk(id, Duration::from_millis(*delay_ms));
            }
            Step::DiskFull { keeper_slot, full } => {
                let id = slot_map[*keeper_slot % slot_map.len()];
                cluster.set_disk_full(id, *full);
            }
            Step::WipeAndReinit { keeper_slot } => {
                let id = slot_map[*keeper_slot % slot_map.len()];
                cluster.wipe_and_reinitialize(id).await;
            }
            Step::CatalogOutage { down_count } => {
                let Some(cat_voters) = cluster.catalog_voters else {
                    continue;
                };
                let down: Vec<Uuid> = cat_voters
                    .iter()
                    .copied()
                    .take((*down_count).min(2))
                    .collect();
                for &id in &down {
                    cluster.stop_graceful(id).await;
                }
                cluster.faults.hit("fault:catalog_voter_outage");
                // Try creating an auxiliary stream during catalog outage.
                let aux = StreamId(90_000 + plan.seed as u128 * 10 + *down_count as u128);
                let aux_journal =
                    cluster.journal(WRITER_A, cluster.data_ids[0..3].try_into().unwrap());
                let create_res = aux_journal.create(aux).await;
                if *down_count == 1 && create_res.is_ok() {
                    cluster.faults.hit("catalog:create_with_one_down");
                } else if *down_count == 2 && matches!(create_res, Err(JournalError::Unavailable)) {
                    cluster.faults.hit("catalog:refused_without_quorum");
                }
                for id in down {
                    cluster.restart(id).await;
                }
            }
            Step::OperatorRecovery { stream_idx } => {
                let (stream, voters, deleted) = {
                    let lock = trackers.lock();
                    (
                        lock[*stream_idx].stream,
                        lock[*stream_idx].voters,
                        lock[*stream_idx].deleted,
                    )
                };
                if deleted {
                    continue;
                }
                // Heal and ensure spare keepers are running so recovery can place 2 replacements.
                cluster.faults.heal_all();
                cluster.clear_disk_faults();
                cluster.restart_all_stopped().await;

                // Stop 2 of the 3 voters; keep voters[0] as survivor.
                let survivor = voters[0];
                let lost = [voters[1], voters[2]];
                let probe_before = cluster.probe_client();
                let mut lost_gens = Vec::with_capacity(2);
                for id in lost {
                    lost_gens.push((id, probe_before.replica_generation(stream, id).await.ok()));
                }
                for id in lost {
                    cluster.crash(id).await;
                }
                let report = cluster.recover_stream_offline(survivor, lost, stream).await;
                if let Ok(report) = report {
                    history.record_operator_recovery(stream, report.head, report.epoch);
                    trackers.lock()[*stream_idx].voters = report.voters;
                    trackers.lock()[*stream_idx].recovered = true;

                    // Wait for recovered cluster to elect a leader and confirm recovery fence.
                    let probe = cluster.probe_client();
                    let _ = timeout(WAIT, async {
                        loop {
                            if let Ok(cfg) = probe.configuration(stream).await
                                && cfg.voters == report.voters
                            {
                                return;
                            }
                            tokio::time::sleep(Duration::from_millis(50)).await;
                        }
                    })
                    .await;

                    // Verify seal is refused with `Recovered` until acknowledged.
                    let next_epoch = Epoch(report.epoch.0 + 1);
                    let seal_before = journal_b.seal(stream, next_epoch).await;
                    if let Ok(head) = seal_before {
                        cluster.stop_all().await;
                        return Err(Violation::RecoveryViolation {
                            stream,
                            detail: format!(
                                "seal succeeded ({head:?}) before acknowledge_recovery cleared recovery fence"
                            ),
                        });
                    }
                    // Acknowledge recovery as writer B, then seal at `report.epoch + 1`.
                    let ack = journal_b.acknowledge_recovery(stream).await;
                    if let Ok(ack_head) = ack {
                        if ack_head < report.head {
                            cluster.stop_all().await;
                            return Err(Violation::RecoveryViolation {
                                stream,
                                detail: format!(
                                    "acknowledge_recovery returned {ack_head:?} < report.head {:?}",
                                    report.head
                                ),
                            });
                        }
                        cluster.faults.hit("op:acknowledge_recovery");
                        let inv = history.tick();
                        let sealed = journal_b.seal(stream, next_epoch).await;
                        let resp = history.tick();
                        history.record_seal(
                            stream,
                            &WriterKind::B.identity(),
                            next_epoch,
                            inv,
                            resp,
                            &sealed,
                        );
                        total_ops += 1;
                        if let Ok(h) = sealed {
                            let mut lock = trackers.lock();
                            lock[*stream_idx].current_epoch = next_epoch;
                            lock[*stream_idx].current_owner = Some(WriterKind::B);
                            lock[*stream_idx].next_lsn = Lsn(h.0 + 1);
                        }
                    }
                    // Restart lost voters one at a time (per README operational
                    // guidance: starting both lost voters at once before either
                    // retires lets them form an old-configuration quorum).
                    let probe_client = cluster.probe_client();
                    for (id, gen_before) in lost_gens {
                        cluster.restart(id).await;
                        if let Some(gen_before) = gen_before {
                            let _ = timeout(Duration::from_secs(6), async {
                                while probe_client.replica_generation(stream, id).await
                                    == Ok(gen_before)
                                {
                                    tokio::time::sleep(Duration::from_millis(40)).await;
                                }
                            })
                            .await;
                        } else {
                            tokio::time::sleep(Duration::from_millis(600)).await;
                        }
                    }
                } else {
                    cluster.restart_all_stopped().await;
                }
            }
            Step::PauseMs(ms) => {
                tokio::time::sleep(Duration::from_millis(*ms)).await;
            }
        }
    }

    // Heal all faults and restart stopped/crashed keepers for final verification.
    cluster.faults.heal_all();
    cluster.clear_disk_faults();
    cluster.restart_all_stopped().await;

    // Issue a final linearizable head + read on each live stream so any amnesia /
    // durability regression that happened during the fault phase is observed in history.
    let probe = cluster.probe_client();
    let mut converged = BTreeMap::new();
    let snapshot_specs: Vec<(StreamId, [Uuid; 3], bool)> = trackers
        .lock()
        .iter()
        .map(|t| (t.stream, t.voters, t.deleted))
        .collect();

    for (stream, fallback_voters, deleted) in snapshot_specs {
        let inv = history.tick();
        let head_res = journal_r.head(stream).await;
        let resp = history.tick();
        history.record_head(stream, &Identity::from_static(READER), inv, resp, &head_res);
        total_ops += 1;

        if !deleted && head_res.is_ok() {
            let inv = history.tick();
            let read_res = journal_r.read(stream, Lsn(1), 64, Duration::ZERO).await;
            let resp = history.tick();
            history.record_read(
                stream,
                &Identity::from_static(READER),
                Lsn(1),
                64,
                inv,
                resp,
                &read_res,
            );
            total_ops += 1;
        }

        // Discover the latest finalized voters (auto-repair may have moved a
        // voter). A keeper reused on new media holds no replica until repair
        // replaces it, so wait for that first.
        let mut final_voters = fallback_voters;
        let replaced = tokio::time::Instant::now() + Duration::from_secs(40);
        loop {
            if let Ok(cfg) = probe.configuration(stream).await {
                final_voters = cfg.voters;
            }
            if plan.options.ignore_reused_ids
                || deleted
                || !final_voters.iter().any(|id| cluster.wiped.contains(id))
                || tokio::time::Instant::now() >= replaced
            {
                break;
            }
            tokio::time::sleep(Duration::from_millis(200)).await;
        }
        let mut conv = cluster.wait_converged(stream, &final_voters, WAIT).await;
        // Repair may replace a voter whose media failed while the run waited
        // for convergence; check the voters it moved to.
        for _ in 0..2 {
            if conv.is_ok() {
                break;
            }
            match probe.configuration(stream).await {
                Ok(cfg) if cfg.voters != final_voters => final_voters = cfg.voters,
                _ => break,
            }
            conv = cluster.wait_converged(stream, &final_voters, WAIT).await;
        }
        converged.insert(stream, (final_voters, conv));
    }

    let coverage = cluster.faults.coverage();
    let check_result = history.check_all(&converged);
    cluster.stop_all().await;

    check_result.map(|()| RunSummary {
        coverage,
        total_ops,
    })
}

#[allow(clippy::too_many_arguments)]
async fn run_concurrent_ops(
    ops: &[ClientOp],
    seed: u64,
    journal_a: &crate::stream::consensus::ConsensusJournal,
    journal_b: &crate::stream::consensus::ConsensusJournal,
    journal_r: &crate::stream::consensus::ConsensusJournal,
    trackers: &Arc<Mutex<Vec<StreamTracker>>>,
    history: &Arc<History>,
    faults: &faults::FaultNetwork,
    rng: &mut Rng,
) -> usize {
    enum Prepared {
        Append {
            stream_idx: usize,
            stream: StreamId,
            writer: WriterKind,
            epoch: Epoch,
            at: Lsn,
            payload: Bytes,
        },
        AppendBatch {
            stream_idx: usize,
            stream: StreamId,
            writer: WriterKind,
            epoch: Epoch,
            records: Vec<(Lsn, Bytes)>,
        },
        Seal {
            stream_idx: usize,
            stream: StreamId,
            writer: WriterKind,
            epoch: Epoch,
        },
        Read {
            stream: StreamId,
            from: Lsn,
            max: usize,
            wait: Duration,
        },
        Head {
            stream: StreamId,
        },
        Trim {
            stream_idx: usize,
            stream: StreamId,
            writer: WriterKind,
            epoch: Epoch,
            through: Lsn,
        },
    }

    let mut prepared = Vec::with_capacity(ops.len());
    {
        let mut lock = trackers.lock();
        for op in ops {
            match *op {
                ClientOp::Append {
                    stream_idx,
                    writer,
                    stale_epoch,
                    retry_previous,
                } => {
                    let t = &mut lock[stream_idx];
                    let epoch = if stale_epoch && t.current_epoch.0 > 1 {
                        Epoch(t.current_epoch.0 - 1)
                    } else {
                        t.current_epoch.max(Epoch(1))
                    };
                    let (at, payload) = if retry_previous
                        && let Some((prev_epoch, prev_lsn, prev_bytes)) = t.last_append.clone()
                        && prev_epoch == epoch
                    {
                        (prev_lsn, prev_bytes)
                    } else {
                        let size = 32 + rng.range(160);
                        let payload = t.make_payload(seed, size);
                        let at = t.next_lsn;
                        (at, payload)
                    };
                    history.note_proposed(t.stream, at, payload.clone());
                    prepared.push(Prepared::Append {
                        stream_idx,
                        stream: t.stream,
                        writer,
                        epoch,
                        at,
                        payload,
                    });
                }
                ClientOp::AppendBatch {
                    stream_idx,
                    writer,
                    count,
                } => {
                    let t = &mut lock[stream_idx];
                    let epoch = t.current_epoch.max(Epoch(1));
                    let start = t.next_lsn.0;
                    let mut records = Vec::with_capacity(count);
                    for i in 0..count as u64 {
                        let size = 24 + rng.range(96);
                        let payload = t.make_payload(seed, size);
                        history.note_proposed(t.stream, Lsn(start + i), payload.clone());
                        records.push((Lsn(start + i), payload));
                    }
                    prepared.push(Prepared::AppendBatch {
                        stream_idx,
                        stream: t.stream,
                        writer,
                        epoch,
                        records,
                    });
                }
                ClientOp::Seal {
                    stream_idx,
                    writer,
                    advance,
                } => {
                    let t = &mut lock[stream_idx];
                    let epoch = if advance {
                        Epoch(t.current_epoch.0 + 1)
                    } else {
                        t.current_epoch.max(Epoch(1))
                    };
                    prepared.push(Prepared::Seal {
                        stream_idx,
                        stream: t.stream,
                        writer,
                        epoch,
                    });
                }
                ClientOp::Read {
                    stream_idx,
                    wait_ms,
                } => {
                    let t = &lock[stream_idx];
                    let from = if wait_ms > 0 {
                        t.next_lsn
                    } else {
                        Lsn(t.trimmed_to.0.saturating_add(1).max(1))
                    };
                    prepared.push(Prepared::Read {
                        stream: t.stream,
                        from,
                        max: 16,
                        wait: Duration::from_millis(wait_ms),
                    });
                }
                ClientOp::Head { stream_idx } => {
                    prepared.push(Prepared::Head {
                        stream: lock[stream_idx].stream,
                    });
                }
                ClientOp::Trim {
                    stream_idx,
                    writer,
                    stale_epoch,
                } => {
                    let t = &lock[stream_idx];
                    let epoch = if stale_epoch && t.current_epoch.0 > 1 {
                        Epoch(t.current_epoch.0 - 1)
                    } else {
                        t.current_epoch.max(Epoch(1))
                    };
                    let through = if t.next_lsn.0 > 2 {
                        Lsn((t.next_lsn.0 - 1).min(t.trimmed_to.0 + 2))
                    } else {
                        Lsn(0)
                    };
                    prepared.push(Prepared::Trim {
                        stream_idx,
                        stream: t.stream,
                        writer,
                        epoch,
                        through,
                    });
                }
            }
        }
    }

    let count = prepared.len();
    let futs = prepared.into_iter().map(|item| {
        let history = history.clone();
        let trackers = trackers.clone();
        let faults = faults.clone();
        async move {
            match item {
                Prepared::Append {
                    stream_idx,
                    stream,
                    writer,
                    epoch,
                    at,
                    payload,
                } => {
                    let j = match writer {
                        WriterKind::A => journal_a,
                        WriterKind::B => journal_b,
                    };
                    let caller = writer.identity();
                    let inv = history.tick();
                    let res = j.append(stream, epoch, at, payload.clone()).await;
                    let resp = history.tick();
                    history.record_append(
                        stream,
                        &caller,
                        epoch,
                        at,
                        payload.clone(),
                        inv,
                        resp,
                        &res,
                    );
                    match &res {
                        Ok(pos) => {
                            faults.hit("op:append_ok");
                            let mut lock = trackers.lock();
                            let t = &mut lock[stream_idx];
                            if pos.0 >= t.next_lsn.0 {
                                t.next_lsn = Lsn(pos.0 + 1);
                            }
                            t.last_append = Some((epoch, *pos, payload));
                        }
                        Err(JournalError::Conflict { head }) => {
                            let mut lock = trackers.lock();
                            let t = &mut lock[stream_idx];
                            if head.0 >= t.next_lsn.0 {
                                t.next_lsn = Lsn(head.0 + 1);
                            }
                        }
                        Err(JournalError::Fenced { current }) => {
                            faults.hit("op:fenced");
                            let mut lock = trackers.lock();
                            let t = &mut lock[stream_idx];
                            if *current > t.current_epoch {
                                t.current_epoch = *current;
                            }
                        }
                        Err(JournalError::Unavailable) => faults.hit("op:append_ambiguous"),
                        _ => {}
                    }
                }
                Prepared::AppendBatch {
                    stream_idx,
                    stream,
                    writer,
                    epoch,
                    records,
                } => {
                    let j = match writer {
                        WriterKind::A => journal_a,
                        WriterKind::B => journal_b,
                    };
                    let caller = writer.identity();
                    let inv = history.tick();
                    let res = j.append_batch(stream, epoch, records.clone()).await;
                    let resp = history.tick();
                    history.record_append_batch(stream, &caller, epoch, &records, inv, resp, &res);
                    match &res {
                        Ok(last) => {
                            faults.hit("op:append_batch_ok");
                            let mut lock = trackers.lock();
                            let t = &mut lock[stream_idx];
                            if last.0 >= t.next_lsn.0 {
                                t.next_lsn = Lsn(last.0 + 1);
                            }
                            if let Some((lsn, bytes)) = records.last() {
                                t.last_append = Some((epoch, *lsn, bytes.clone()));
                            }
                        }
                        Err(JournalError::Conflict { head }) => {
                            let mut lock = trackers.lock();
                            let t = &mut lock[stream_idx];
                            if head.0 >= t.next_lsn.0 {
                                t.next_lsn = Lsn(head.0 + 1);
                            }
                        }
                        Err(JournalError::Fenced { current }) => {
                            faults.hit("op:fenced");
                            let mut lock = trackers.lock();
                            let t = &mut lock[stream_idx];
                            if *current > t.current_epoch {
                                t.current_epoch = *current;
                            }
                        }
                        Err(JournalError::Unavailable) => faults.hit("op:batch_ambiguous"),
                        _ => {}
                    }
                }
                Prepared::Seal {
                    stream_idx,
                    stream,
                    writer,
                    epoch,
                } => {
                    let j = match writer {
                        WriterKind::A => journal_a,
                        WriterKind::B => journal_b,
                    };
                    let caller = writer.identity();
                    let inv = history.tick();
                    let res = j.seal(stream, epoch).await;
                    let resp = history.tick();
                    history.record_seal(stream, &caller, epoch, inv, resp, &res);
                    match &res {
                        Ok(head) => {
                            faults.hit("op:seal_ok");
                            let mut lock = trackers.lock();
                            let t = &mut lock[stream_idx];
                            if epoch >= t.current_epoch {
                                t.current_epoch = epoch;
                                t.current_owner = Some(writer);
                            }
                            if head.0 >= t.next_lsn.0 {
                                t.next_lsn = Lsn(head.0 + 1);
                            }
                        }
                        Err(JournalError::Fenced { current }) => {
                            faults.hit("op:fenced");
                            let mut lock = trackers.lock();
                            let t = &mut lock[stream_idx];
                            if *current > t.current_epoch {
                                t.current_epoch = *current;
                            }
                        }
                        _ => {}
                    }
                }
                Prepared::Read {
                    stream,
                    from,
                    max,
                    wait,
                } => {
                    let caller = Identity::from_static(READER);
                    let inv = history.tick();
                    let res = journal_r.read(stream, from, max, wait).await;
                    let resp = history.tick();
                    history.record_read(stream, &caller, from, max, inv, resp, &res);
                    if res.is_ok() {
                        faults.hit(if wait.is_zero() {
                            "op:read_ok"
                        } else {
                            "op:long_poll_read_ok"
                        });
                    }
                }
                Prepared::Head { stream } => {
                    let caller = Identity::from_static(READER);
                    let inv = history.tick();
                    let res = journal_r.head(stream).await;
                    let resp = history.tick();
                    history.record_head(stream, &caller, inv, resp, &res);
                    if res.is_ok() {
                        faults.hit("op:head_ok");
                    }
                }
                Prepared::Trim {
                    stream_idx,
                    stream,
                    writer,
                    epoch,
                    through,
                } => {
                    let j = match writer {
                        WriterKind::A => journal_a,
                        WriterKind::B => journal_b,
                    };
                    let caller = writer.identity();
                    let inv = history.tick();
                    let res = j.trim(stream, epoch, through).await;
                    let resp = history.tick();
                    history.record_trim(stream, &caller, epoch, through, inv, resp, &res);
                    if res.is_ok() {
                        faults.hit("op:trim_ok");
                        let mut lock = trackers.lock();
                        let t = &mut lock[stream_idx];
                        if through > t.trimmed_to {
                            t.trimmed_to = through;
                        }
                    }
                }
            }
        }
    });
    futures::future::join_all(futs).await;
    count
}

/// Attempts to shrink a failing `Plan` to a smaller step sequence that still
/// reproduces the same violation class, within `max_attempts` re-executions.
async fn shrink_plan(
    original: &Plan,
    initial_violation: &Violation,
    max_attempts: usize,
) -> (Plan, Option<Violation>) {
    let target_kind = std::mem::discriminant(initial_violation);
    let mut best = original.clone();
    let mut best_violation = None;
    let mut attempts = 0usize;

    // Phase 1: trim trailing steps (binary-style halving).
    while attempts < max_attempts && best.steps.len() > 2 {
        let mid = best.steps.len() / 2;
        let mut candidate = best.clone();
        candidate.steps.truncate(mid);
        attempts += 1;
        if let Err(v) = execute_plan(&candidate).await
            && std::mem::discriminant(&v) == target_kind
        {
            best = candidate;
            best_violation = Some(v);
        } else {
            break;
        }
    }

    // Phase 2: try removing individual steps from the end backwards.
    let mut idx = best.steps.len();
    while attempts < max_attempts && idx > 0 {
        idx -= 1;
        let mut candidate = best.clone();
        candidate.steps.remove(idx);
        attempts += 1;
        if let Err(v) = execute_plan(&candidate).await
            && std::mem::discriminant(&v) == target_kind
        {
            best = candidate;
            best_violation = Some(v);
            idx = idx.min(best.steps.len());
        }
    }

    (best, best_violation)
}

async fn run_seed(seed: u64, config: &RunConfig) -> Result<RunSummary, (Plan, Violation)> {
    let plan = generate_plan(seed, config);
    match execute_plan(&plan).await {
        Ok(summary) => Ok(summary),
        Err(violation) => Err((plan, violation)),
    }
}

/// CI-sized randomized consensus fault-injection and linearizability suite.
/// Override seed range with `LOGKEEPER_CONSENSUS_FIRST_SEED` and
/// `LOGKEEPER_CONSENSUS_SEEDS`.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn consensus_fault_harness_ci() {
    let first = env::var("LOGKEEPER_CONSENSUS_FIRST_SEED").map_or(0, |v| v.parse::<u64>().unwrap());
    let count = env::var("LOGKEEPER_CONSENSUS_SEEDS").map_or(6, |v| v.parse::<u64>().unwrap());
    assert!(count > 0);
    let config = RunConfig::standard();
    let mut coverage = Coverage::new();
    let mut total_ops = 0usize;
    for seed in first..first + count {
        let summary = timeout(Duration::from_secs(90), run_seed(seed, &config))
            .await
            .unwrap_or_else(|_| panic!("consensus fault harness timed out on seed {seed}"))
            .unwrap_or_else(|(plan, violation)| {
                panic!(
                    "consensus fault harness FAILED on seed {seed} (profile {:?}):\n\
                     {violation}\n\
                     replay with: LOGKEEPER_CONSENSUS_SEED={seed} cargo test --locked --features stream --lib consensus_fault_harness_replay_seed -- --ignored --nocapture\n\
                     plan steps ({}): {:#?}",
                    plan.profile,
                    plan.steps.len(),
                    plan.steps,
                )
            });
        total_ops += summary.total_ops;
        for (event, n) in summary.coverage {
            *coverage.entry(event).or_default() += n;
        }
    }
    if first == 0 && count >= 6 {
        for required in [
            "op:append_ok",
            "op:append_batch_ok",
            "op:seal_ok",
            "op:read_ok",
            "op:long_poll_read_ok",
            "op:head_ok",
            "op:trim_ok",
            "op:delete",
            "op:replace",
            "op:prefer_leader",
            "op:parked",
            "op:woke_parked",
            "op:recover_stream",
            "op:acknowledge_recovery",
            "fault:partition_symmetric",
            "fault:partition_asymmetric",
            "fault:slow_disk",
            "fault:disk_full",
            "fault:catalog_voter_outage",
        ] {
            assert!(
                coverage.contains_key(required),
                "CI consensus fault harness missed coverage for `{required}`; observed: {coverage:?}"
            );
        }
    }
    eprintln!(
        "consensus fault harness seeds {first}..{} ({total_ops} ops): {coverage:?}",
        first + count
    );
}

/// Randomized large-batch fault test: mixes 256-record batches (and >256-record
/// multi-chunk batches) crossing snapshot intervals under partitions, slow disk,
/// and keeper restarts. Guards against snapshot page-budget and extent-reaping bugs.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn consensus_fault_harness_large_batches() {
    let seed = env::var("LOGKEEPER_CONSENSUS_SEED").map_or(42, |v| v.parse::<u64>().unwrap());
    let mut rng = Rng::new(seed);
    let options = ClusterOptions {
        replicated_catalog: true,
        park_after_secs: 2,
        repair_after_secs: 2,
        max_streams: 16,
        quota_bytes: 32 * 1024 * 1024,
        max_record_bytes: 4096,
        client_deadline_ms: 8_000,
        ignore_reused_ids: false,
    };
    let mut cluster = SimCluster::start(seed, options.clone()).await;
    let limits = Limits {
        max_record_bytes: options.max_record_bytes,
        stream_quota_bytes: options.quota_bytes,
    };
    let history = Arc::new(History::new(limits));
    let voters = [
        cluster.data_ids[0],
        cluster.data_ids[1],
        cluster.data_ids[2],
    ];
    let journal = cluster.journal(WRITER_A, voters);
    let reader = cluster.journal(READER, voters);
    let stream = StreamId(80_000 + seed as u128);
    let caller = WriterKind::A.identity();

    // A loaded machine can time a fresh cluster's first calls out.
    let setup = tokio::time::Instant::now() + Duration::from_secs(30);
    loop {
        let inv = history.tick();
        let res = journal.create(stream).await;
        history.record_create(stream, &caller, inv, history.tick(), &res);
        match res {
            Err(JournalError::Unavailable) if tokio::time::Instant::now() < setup => {}
            res => break res.unwrap(),
        }
    }
    loop {
        let inv = history.tick();
        let res = journal.seal(stream, Epoch(1)).await;
        history.record_seal(stream, &caller, Epoch(1), inv, history.tick(), &res);
        match res {
            Err(JournalError::Unavailable) if tokio::time::Instant::now() < setup => {}
            res => {
                res.unwrap();
                break;
            }
        }
    }

    let mut next_lsn = 1u64;
    // 140 batches crossing OpenRaft's 128-entry snapshot policy, mixing 256-record
    // full keeper batches and 300-record multi-chunk batches under injected faults.
    for batch_idx in 0..140u64 {
        if batch_idx == 40 {
            cluster.set_slow_disk(voters[1], Duration::from_millis(25));
            cluster.faults.set_lane_faults(
                LaneKey::Replication,
                LaneFaults {
                    drop_pct: 5,
                    drop_reply_pct: 0,
                    duplicate_pct: 10,
                    max_delay_ms: 10,
                },
            );
        } else if batch_idx == 80 {
            cluster.crash(voters[2]).await;
        } else if batch_idx == 110 {
            cluster.faults.heal_all();
            cluster.clear_disk_faults();
            cluster.restart(voters[2]).await;
        }
        let batch_len = match batch_idx % 10 {
            0 => 256,
            5 => 300,
            _ => 8 + (rng.range(16) as u64),
        };
        let records: Vec<(Lsn, Bytes)> = (0..batch_len)
            .map(|i| {
                let at = next_lsn + i;
                (Lsn(at), Bytes::from(format!("b{seed}-{at}")))
            })
            .collect();
        let inv = history.tick();
        let res = journal
            .append_batch(stream, Epoch(1), records.clone())
            .await;
        let resp = history.tick();
        history.record_append_batch(stream, &caller, Epoch(1), &records, inv, resp, &res);
        match res {
            Ok(last) => next_lsn = last.0 + 1,
            Err(JournalError::Unavailable) => {
                if let Ok(head) = journal.head(stream).await {
                    next_lsn = head.0 + 1;
                }
            }
            Err(other) => panic!("seed {seed} batch {batch_idx} unexpected error: {other:?}"),
        }
    }

    cluster.faults.heal_all();
    cluster.clear_disk_faults();
    cluster.restart_all_stopped().await;

    let inv = history.tick();
    let head_res = reader.head(stream).await;
    history.record_head(
        stream,
        &Identity::from_static(READER),
        inv,
        history.tick(),
        &head_res,
    );
    assert!(head_res.is_ok(), "final head failed: {head_res:?}");

    // Repair may have replaced the crashed voter while it was down.
    let voters = match cluster.probe_client().configuration(stream).await {
        Ok(configuration) => configuration.voters,
        Err(_) => voters,
    };
    let conv = cluster
        .wait_converged(stream, &voters, Duration::from_secs(60))
        .await;
    let mut converged = BTreeMap::new();
    converged.insert(stream, (voters, conv));
    let check = history.check_all(&converged);
    cluster.stop_all().await;
    if let Err(violation) = check {
        panic!("large-batch fault test FAILED on seed {seed}: {violation}");
    }
}

fn amnesia_violation(violation: &Violation) -> bool {
    matches!(
        violation,
        Violation::DurabilityLoss { .. }
            | Violation::HeadRegression { .. }
            | Violation::Linearizability { .. }
    )
}

/// The 6d75fec amnesia schedule as a harness plan: LSN 1 commits on every
/// voter, the laggard (slot 2) misses LSNs 2 and 3, the leader (slot 0)
/// crashes, and the witness (slot 1) loses its media and comes back under its
/// old keeper ID while the laggard is reachable again.
fn amnesia_plan(ignore_reused_ids: bool) -> Plan {
    let mut voters = [1, 2, 3].map(Uuid::from_u128);
    voters.sort_unstable();
    let head = || Step::Ops(vec![ClientOp::Head { stream_idx: 0 }]);
    Plan {
        seed: 3_000_003,
        profile: Profile::StorageAndCrash,
        options: ClusterOptions {
            park_after_secs: 3600,
            repair_after_secs: if ignore_reused_ids { 60 } else { 2 },
            client_deadline_ms: 2_500,
            ignore_reused_ids,
            ..ClusterOptions::default()
        },
        streams: vec![StreamSpec {
            stream: StreamId(3_000_003),
            initial_voters: voters,
        }],
        steps: vec![
            Step::Ops(vec![ClientOp::Append {
                stream_idx: 0,
                writer: WriterKind::A,
                stale_epoch: false,
                retry_previous: false,
            }]),
            head(),
            Step::PartitionSymmetric {
                keeper_slot: 2,
                lanes: vec![LaneKey::Replication],
            },
            Step::Ops(vec![ClientOp::AppendBatch {
                stream_idx: 0,
                writer: WriterKind::A,
                count: 2,
            }]),
            head(),
            Step::StopKeeper {
                keeper_slot: 0,
                crash: true,
            },
            Step::HealNetwork,
            Step::WipeAndReinit { keeper_slot: 1 },
            Step::PauseMs(1_200),
            head(),
            Step::PauseMs(800),
            head(),
        ],
    }
}

/// Keepers that accept a keeper ID reused on new media, as they did before
/// media incarnations (`6d75fec`), regress the head on the amnesia
/// schedule; keepers that recognize the reuse keep every acknowledged
/// record and replace the wiped voter.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn consensus_fault_harness_finds_amnesia_without_incarnations() {
    let unguarded = timeout(Duration::from_secs(90), execute_plan(&amnesia_plan(true)))
        .await
        .expect("amnesia plan timed out");
    match unguarded {
        Err(violation) if amnesia_violation(&violation) => {
            eprintln!("amnesia found without incarnations: {violation}");
        }
        Err(violation) => panic!("the amnesia plan found another violation: {violation}"),
        Ok(_) => panic!("the amnesia plan no longer finds the bug without incarnations"),
    }
    let guarded = timeout(Duration::from_secs(90), execute_plan(&amnesia_plan(false)))
        .await
        .expect("amnesia plan timed out");
    if let Err(violation) = guarded {
        panic!("the amnesia plan failed with incarnations: {violation}");
    }
}

/// Acceptance test: with keepers that accept a keeper ID reused on new
/// media, the unscripted seeded harness finds the Raft amnesia bug on its
/// own within a small seed budget, as a durability, head or linearizability
/// violation.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "searches up to 20 wipe seeds; about 80 s"]
async fn consensus_fault_harness_detects_amnesia_bug() {
    let max_seeds = env::var("LOGKEEPER_AMNESIA_BUDGET").map_or(20, |v| v.parse::<u64>().unwrap());
    let config = RunConfig {
        ignore_reused_ids: true,
        ..RunConfig::with_wipe()
    };
    let started = std::time::Instant::now();
    let mut detected = None;
    for seed in 0..max_seeds {
        match timeout(Duration::from_secs(45), run_seed(seed, &config)).await {
            Ok(Ok(_)) => continue,
            Ok(Err((plan, violation))) => {
                if amnesia_violation(&violation) {
                    detected = Some((seed, plan, violation));
                    break;
                }
                eprintln!(
                    "seed {seed} also hit secondary amnesia symptom ({violation}); continuing search for durability/linearizability violation..."
                );
            }
            Err(_) => eprintln!("seed {seed} timed out; continuing"),
        }
    }
    let (seed, plan, violation) = detected.unwrap_or_else(|| {
        panic!("expected randomized harness to detect the amnesia bug within {max_seeds} seeds")
    });
    eprintln!(
        "AMNESIA DETECTED autonomously on seed {seed} in {:?} ({} steps): {violation}",
        started.elapsed(),
        plan.steps.len(),
    );
}

/// The same wipe-and-reinitialize schedules against keepers that recognize
/// reused keeper IDs (`6d75fec`) find no violation.
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn consensus_fault_harness_wipe_with_incarnations() {
    let first = env::var("LOGKEEPER_WIPE_FIRST_SEED").map_or(0, |v| v.parse::<u64>().unwrap());
    let count = env::var("LOGKEEPER_WIPE_SEEDS").map_or(2, |v| v.parse::<u64>().unwrap());
    let config = RunConfig::with_wipe();
    for seed in first..first + count {
        timeout(Duration::from_secs(90), run_seed(seed, &config))
            .await
            .unwrap_or_else(|_| panic!("wipe harness timed out on seed {seed}"))
            .unwrap_or_else(|(plan, violation)| {
                panic!(
                    "wipe harness FAILED on seed {seed}: {violation}\n\
                     replay with: LOGKEEPER_CONSENSUS_SEED={seed} LOGKEEPER_CONSENSUS_ALLOW_WIPE=1 cargo test --locked --features stream --lib consensus_fault_harness_replay_seed -- --ignored --nocapture\n\
                     steps: {:#?}",
                    plan.steps
                )
            });
    }
}

/// Replays a single seed (and optionally shrinks a failure).
///
/// Example:
/// `LOGKEEPER_CONSENSUS_SEED=3 LOGKEEPER_CONSENSUS_ALLOW_WIPE=1 LOGKEEPER_CONSENSUS_SHRINK=1 \
///  cargo test --locked --features stream --lib consensus_fault_harness_replay_seed -- --ignored --nocapture`
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "manual seed replay entry point"]
async fn consensus_fault_harness_replay_seed() {
    let seed = env::var("LOGKEEPER_CONSENSUS_SEED").map_or(0, |v| v.parse::<u64>().unwrap());
    let allow_wipe = env::var("LOGKEEPER_CONSENSUS_ALLOW_WIPE")
        .map_or(false, |v| v == "1" || v.eq_ignore_ascii_case("true"));
    let do_shrink = env::var("LOGKEEPER_CONSENSUS_SHRINK")
        .map_or(false, |v| v == "1" || v.eq_ignore_ascii_case("true"));
    let mut config = if allow_wipe {
        RunConfig::with_wipe()
    } else {
        RunConfig::standard()
    };
    config.ignore_reused_ids = env::var("LOGKEEPER_CONSENSUS_IGNORE_REUSE")
        .is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"));
    match run_seed(seed, &config).await {
        Ok(summary) => {
            eprintln!(
                "seed {seed} PASSED ({} ops): {:?}",
                summary.total_ops, summary.coverage
            );
        }
        Err((plan, violation)) => {
            eprintln!("seed {seed} FAILED: {violation}");
            eprintln!(
                "original plan ({} steps): {:#?}",
                plan.steps.len(),
                plan.steps
            );
            if do_shrink {
                let (shrunk, shrunk_v) = shrink_plan(&plan, &violation, 12).await;
                eprintln!(
                    "shrunk plan ({} -> {} steps): {:#?}\nshrunk violation: {:?}",
                    plan.steps.len(),
                    shrunk.steps.len(),
                    shrunk.steps,
                    shrunk_v.as_ref().map(ToString::to_string),
                );
            }
            panic!("seed {seed} violated invariants: {violation}");
        }
    }
}

/// Extended randomized soak run across many seeds (default 50).
///
/// Example:
/// `LOGKEEPER_CONSENSUS_SEEDS=50 cargo test --locked --features stream --lib consensus_fault_harness_soak -- --ignored --nocapture`
#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
#[ignore = "long randomized soak run"]
async fn consensus_fault_harness_soak() {
    let first = env::var("LOGKEEPER_CONSENSUS_FIRST_SEED").map_or(0, |v| v.parse::<u64>().unwrap());
    let count = env::var("LOGKEEPER_CONSENSUS_SEEDS").map_or(50, |v| v.parse::<u64>().unwrap());
    let allow_wipe = env::var("LOGKEEPER_CONSENSUS_ALLOW_WIPE")
        .map_or(false, |v| v == "1" || v.eq_ignore_ascii_case("true"));
    // Keep going past a failing seed and report every failure at the end.
    let keep_going = env::var("LOGKEEPER_CONSENSUS_KEEP_GOING")
        .is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"));
    let mut config = if allow_wipe {
        RunConfig::with_wipe()
    } else {
        RunConfig::standard()
    };
    config.ignore_reused_ids = env::var("LOGKEEPER_CONSENSUS_IGNORE_REUSE")
        .is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"));
    let mut coverage = Coverage::new();
    let mut total_ops = 0usize;
    let mut failures = Vec::new();
    for seed in first..first + count {
        let started = std::time::Instant::now();
        let failure = match timeout(Duration::from_secs(90), run_seed(seed, &config)).await {
            Ok(Ok(summary)) => {
                total_ops += summary.total_ops;
                for (k, v) in summary.coverage {
                    *coverage.entry(k).or_default() += v;
                }
                None
            }
            Ok(Err((plan, violation))) => Some(format!(
                "soak FAILED on seed {seed} (profile {:?}): {violation}\nsteps: {:#?}",
                plan.profile, plan.steps
            )),
            Err(_) => Some(format!("soak timed out on seed {seed}")),
        };
        eprintln!(
            "soak seed {seed}: {} in {:?}",
            if failure.is_some() { "FAILED" } else { "ok" },
            started.elapsed()
        );
        if let Some(failure) = failure {
            if !keep_going {
                panic!("{failure}");
            }
            eprintln!("{failure}");
            failures.push(seed);
        }
    }
    eprintln!(
        "consensus soak seeds {first}..{} ({total_ops} ops, failed {failures:?}): {coverage:?}",
        first + count
    );
    assert!(failures.is_empty(), "soak failed on seeds {failures:?}");
}
