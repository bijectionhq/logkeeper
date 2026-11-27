//! The configuration authority's records: one liveness record per keeper.
//!
//! The catalog is the configuration authority. Besides each stream's
//! genesis and latest staged move, whose target is the stream's membership
//! and whose revision is its configuration epoch, it keeps one record per
//! keeper: the keeper's epoch, the media incarnation it runs under, and the
//! streams fenced for it. A keeper renews a liveness lease against its
//! record in the background (`keeper/lease.rs`), and it may campaign, lead
//! or serve reads for a stream only while its lease is valid, its epoch is
//! current and the stream is not fenced for its copy
//! (`decisions::holds_authority`).
//!
//! The epoch increments whenever the keeper's identity is in doubt: an
//! operator recovery declares it dead, it was decommissioned, it runs on new
//! media under its old ID, or an operator fenced it. A renewal under an older
//! epoch is refused, so every lease issued under the old epoch ends on its
//! holder's clock. An operator recovery fences the stream for every voter of
//! the configuration it leaves, other than the survivor, below the recovered
//! revision.
//!
//! The lease's expiration is not a durable field, and a renewal writes
//! nothing once the keeper enrolled: it is a read on the catalog's leader
//! after a read barrier. The holder measures its lease from its own send
//! time, and a recovery waits a whole lease plus the drift margin after it
//! commits, so safety needs no expiration at the authority. Each holder
//! reports its own lease age and remaining validity in `/metrics`.

use std::collections::BTreeMap;

use journal_contract::StreamId;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

use super::{Stage, decisions};

/// Media incarnations a record remembers as replaced. Older ones are
/// forgotten; their media was replaced twice since.
const REPLACED_KEPT: usize = 16;

/// One keeper's liveness record.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(super) struct KeeperRecord {
    /// Increments whenever the keeper's identity is in doubt. Starts at 1.
    pub epoch: u64,
    /// The media incarnation the keeper last enrolled under.
    pub incarnation: Option<Uuid>,
    /// Incarnations a newer one replaced. They never renew again.
    pub replaced: Vec<Uuid>,
    /// Streams fenced for this keeper, each below the configuration revision
    /// a recovery installed: a copy that finalized an older revision may not
    /// campaign, lead or serve.
    pub fenced: BTreeMap<StreamId, u64>,
    /// The longest lease and drift margin any catalog keeper granted this
    /// keeper, in milliseconds. Never shrinks, across epochs too, so a
    /// recovery waits out the longest lease the keeper may still hold.
    pub lease_ms: u64,
    pub margin_ms: u64,
}

/// A durable change to the authority's records.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(super) enum Change {
    /// A keeper renews for the first time under `incarnation`. A new
    /// incarnation of a known keeper replaces the old one and bumps the
    /// epoch: the keeper runs on new media under its old ID.
    Enroll { keeper: Uuid, incarnation: Uuid },
    /// An operator fenced the keeper, or it finished decommissioning: bump
    /// its epoch.
    Fence { keeper: Uuid },
    /// A catalog keeper grants `keeper` a lease or margin longer than the
    /// record holds, so it records them before granting.
    Lease {
        keeper: Uuid,
        lease_ms: u64,
        margin_ms: u64,
    },
    /// An operator recovery: the stage's target becomes the stream's
    /// membership at revision `stage.source + 1`, its configuration epoch,
    /// the stream is fenced for every voter of the old configuration outside
    /// the target, and the keepers the operator declared dead have their
    /// epochs bumped. `record` describes what the recovery kept.
    Recover {
        stage: Stage,
        dead: Vec<Uuid>,
        record: RecoveryRecord,
    },
}

/// Where a recovered history's last kept record came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecoverySource {
    /// The surviving voter's log.
    Survivor,
    /// The object store's committed run, longer than the survivor's log.
    ObjectStore,
}

/// The catalog's record of one recovery of a stream.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecoveryRecord {
    pub stream: StreamId,
    /// The configuration epoch the recovery installed: its revision, which
    /// is also the stream's offload lineage from the recovery on.
    pub epoch: u64,
    /// The last record the recovered history kept. Records a writer was
    /// acknowledged above it are lost.
    pub loss_point: journal_contract::Lsn,
    pub source: RecoverySource,
    /// When the survivor committed the recovery, in Unix milliseconds.
    pub time_unix_ms: u64,
}

/// What the authority answers a lease renewal.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Grant {
    /// Whether the lease was renewed. A renewal under a stale epoch or from
    /// replaced media is refused.
    pub granted: bool,
    /// Whether the cluster finalized leases. Until then a lease is advisory.
    pub enforced: bool,
    /// The keeper's current epoch, zero before it enrolled.
    pub epoch: u64,
    /// The streams fenced for the keeper, each below a revision.
    pub fenced: BTreeMap<StreamId, u64>,
    /// Whether the record replaced an earlier media incarnation of this
    /// keeper ID with the one renewing.
    pub reused: bool,
    /// The lease and drift margin the granting catalog keeper is configured
    /// with, in milliseconds. A holder never counts a longer lease.
    pub duration_ms: u64,
    pub margin_ms: u64,
}

/// What a recovery's catalog transaction answers.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Recovered {
    /// The recovery as the catalog recorded it.
    pub record: RecoveryRecord,
    /// The keepers the stream is now fenced for.
    pub fenced: Vec<Uuid>,
    /// Fenced keepers that never enrolled: no lease of theirs ends by time,
    /// so only the operator's word covers them.
    pub unleased: Vec<Uuid>,
    /// How long the recovered configuration must wait before it serves, in
    /// milliseconds from the commit: a lease plus the drift margin.
    pub wait_ms: u64,
    /// False when an earlier attempt already committed this recovery.
    pub written: bool,
}

/// The authority's keeper records.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(super) struct Records {
    pub keepers: BTreeMap<Uuid, KeeperRecord>,
    /// The latest recovery of each stream.
    #[serde(default)]
    pub recoveries: BTreeMap<StreamId, RecoveryRecord>,
}

impl Records {
    fn record(&mut self, keeper: Uuid) -> &mut KeeperRecord {
        let record = self.keepers.entry(keeper).or_default();
        record.epoch = record.epoch.max(1);
        record
    }

    /// Applies one change. Every replica applies the same changes in the
    /// same order, so every replica holds the same records.
    pub fn apply(&mut self, change: &Change) {
        match change {
            Change::Enroll {
                keeper,
                incarnation,
            } => {
                let record = self.record(*keeper);
                match record.incarnation {
                    None => record.incarnation = Some(*incarnation),
                    Some(current)
                        if current != *incarnation && !record.replaced.contains(incarnation) =>
                    {
                        record.replaced.push(current);
                        let excess = record.replaced.len().saturating_sub(REPLACED_KEPT);
                        record.replaced.drain(..excess);
                        record.incarnation = Some(*incarnation);
                        record.epoch = record.epoch.saturating_add(1);
                    }
                    Some(_) => (),
                }
            }
            Change::Lease {
                keeper,
                lease_ms,
                margin_ms,
            } => {
                let record = self.record(*keeper);
                record.lease_ms = record.lease_ms.max(*lease_ms);
                record.margin_ms = record.margin_ms.max(*margin_ms);
            }
            Change::Fence { keeper } => {
                let record = self.record(*keeper);
                record.epoch = record.epoch.saturating_add(1);
            }
            Change::Recover {
                stage,
                dead,
                record,
            } => {
                let revision = stage.source.saturating_add(1);
                if self
                    .recoveries
                    .get(&stage.stream)
                    .is_none_or(|latest| latest.epoch <= record.epoch)
                {
                    self.recoveries.insert(stage.stream, *record);
                }
                for keeper in fenced_by(stage) {
                    let floor = self.record(keeper).fenced.entry(stage.stream).or_default();
                    *floor = (*floor).max(revision);
                }
                for keeper in dead {
                    let record = self.record(*keeper);
                    record.epoch = record.epoch.saturating_add(1);
                }
            }
        }
    }

    /// The change a renewal from `keeper` under `incarnation` must commit
    /// before it is answered, if any.
    pub fn enrollment(&self, keeper: Uuid, incarnation: Uuid) -> Option<Change> {
        let record = self.keepers.get(&keeper);
        let known = record.is_some_and(|record| {
            record.incarnation == Some(incarnation) || record.replaced.contains(&incarnation)
        });
        (!known).then_some(Change::Enroll {
            keeper,
            incarnation,
        })
    }

    /// The change a renewal must commit before it is granted a lease of
    /// `lease_ms` with `margin_ms`: the enrollment first, then a record of a
    /// longer lease than the record holds.
    pub fn pending(
        &self,
        keeper: Uuid,
        incarnation: Uuid,
        lease_ms: u64,
        margin_ms: u64,
    ) -> Option<Change> {
        if let Some(enroll) = self.enrollment(keeper, incarnation) {
            return Some(enroll);
        }
        let record = self.keepers.get(&keeper)?;
        (record.lease_ms < lease_ms || record.margin_ms < margin_ms).then_some(Change::Lease {
            keeper,
            lease_ms,
            margin_ms,
        })
    }

    /// How long a recovery that fences `keepers` waits after it commits:
    /// the longest lease plus margin any of them was granted, and never less
    /// than `own_ms`.
    pub fn recovery_wait(&self, keepers: &[Uuid], own_ms: u64) -> u64 {
        keepers
            .iter()
            .filter_map(|keeper| self.keepers.get(keeper))
            .filter_map(|record| decisions::recovery_wait(record.lease_ms, record.margin_ms))
            .fold(own_ms, u64::max)
    }

    /// Answers a renewal from `keeper` under `incarnation` and `epoch`, zero
    /// when the keeper process joins.
    pub fn grant(
        &self,
        keeper: Uuid,
        incarnation: Uuid,
        epoch: u64,
        enforced: bool,
        duration_ms: u64,
        margin_ms: u64,
    ) -> Grant {
        let record = self.keepers.get(&keeper);
        let current = record.map_or(0, |record| record.epoch);
        let replaced = record.is_some_and(|record| record.replaced.contains(&incarnation));
        let enrolled = record.is_some_and(|record| record.incarnation == Some(incarnation));
        Grant {
            // Before leases are finalized no record is written, and the
            // advisory lease is granted to everyone but replaced media.
            granted: decisions::grants_lease(replaced, epoch, current) && (enrolled || !enforced),
            enforced,
            epoch: current,
            fenced: record
                .map(|record| record.fenced.clone())
                .unwrap_or_default(),
            reused: enrolled && record.is_some_and(|record| !record.replaced.is_empty()),
            duration_ms,
            margin_ms,
        }
    }

    /// Whether `stage` is already recorded as a committed recovery: every
    /// keeper it fences is fenced at its revision.
    pub fn recovered(&self, stage: &Stage) -> bool {
        let revision = stage.source.saturating_add(1);
        fenced_by(stage).into_iter().all(|keeper| {
            self.keepers
                .get(&keeper)
                .and_then(|record| record.fenced.get(&stage.stream))
                .is_some_and(|floor| *floor >= revision)
        })
    }

    /// The keepers of `keepers` that never enrolled.
    pub fn unleased(&self, keepers: &[Uuid]) -> Vec<Uuid> {
        keepers
            .iter()
            .copied()
            .filter(|keeper| {
                self.keepers
                    .get(keeper)
                    .is_none_or(|record| record.incarnation.is_none())
            })
            .collect()
    }
}

/// Whether `record` describes the recovery `stage` stages: its stream and
/// the configuration epoch, the revision the stage installs.
pub(super) fn describes(record: &RecoveryRecord, stage: &Stage) -> bool {
    record.stream == stage.stream && Some(record.epoch) == stage.source.checked_add(1)
}

/// The keepers a recovery fences its stream for: every voter of the old
/// configuration outside the target. Fencing a voter the recovered
/// membership no longer names costs nothing, since its copy can only
/// retire, so the fence never needs the operator to name the lost voters.
pub(super) fn fenced_by(stage: &Stage) -> Vec<Uuid> {
    stage
        .old
        .iter()
        .copied()
        .filter(|voter| !stage.target.contains(voter))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ids() -> [Uuid; 6] {
        [1, 2, 3, 4, 5, 6].map(Uuid::from_u128)
    }

    fn recovery() -> Stage {
        let ids = ids();
        Stage {
            stream: StreamId(9),
            source: 4,
            old: crate::stream::consensus::Voters::from([ids[0], ids[1], ids[2]]),
            target: crate::stream::consensus::Voters::from([ids[0], ids[3], ids[4]]),
        }
    }

    #[test]
    fn a_new_incarnation_bumps_the_epoch_and_the_old_one_never_renews() {
        let ids = ids();
        let (keeper, first, second) = (ids[0], ids[4], ids[5]);
        let mut records = Records::default();
        let enroll = records.enrollment(keeper, first).unwrap();
        records.apply(&enroll);
        assert_eq!(records.keepers[&keeper].epoch, 1);
        assert!(records.enrollment(keeper, first).is_none());
        let joined = records.grant(keeper, first, 0, true, 30_000, 3_000);
        assert!(joined.granted && joined.epoch == 1 && !joined.reused);

        records.apply(&records.enrollment(keeper, second).unwrap());
        assert_eq!(records.keepers[&keeper].epoch, 2);
        // The old media is replaced for good, whatever epoch it asks under.
        assert!(records.enrollment(keeper, first).is_none());
        assert!(!records.grant(keeper, first, 1, true, 30_000, 3_000).granted);
        assert!(!records.grant(keeper, first, 0, true, 30_000, 3_000).granted);
        let renewed = records.grant(keeper, second, 0, true, 30_000, 3_000);
        assert!(renewed.granted && renewed.epoch == 2 && renewed.reused);
        // A renewal under the old epoch is refused with the current one.
        let stale = records.grant(keeper, second, 1, true, 30_000, 3_000);
        assert!(!stale.granted && stale.epoch == 2);
    }

    #[test]
    fn a_recovery_fences_every_lost_voter_and_bumps_only_the_dead() {
        let ids = ids();
        let mut records = Records::default();
        for keeper in [ids[0], ids[1]] {
            records.apply(&Change::Enroll {
                keeper,
                incarnation: keeper,
            });
        }
        let stage = recovery();
        assert!(!records.recovered(&stage));
        assert_eq!(records.unleased(&fenced_by(&stage)), [ids[2]]);
        let record = RecoveryRecord {
            stream: StreamId(9),
            epoch: 5,
            loss_point: journal_contract::Lsn(7),
            source: RecoverySource::Survivor,
            time_unix_ms: 1,
        };
        records.apply(&Change::Recover {
            stage: stage.clone(),
            dead: vec![ids[2]],
            record,
        });
        assert_eq!(records.recoveries[&StreamId(9)], record);
        assert!(records.recovered(&stage));
        assert_eq!(fenced_by(&stage), [ids[1], ids[2]]);
        for keeper in [ids[1], ids[2]] {
            assert_eq!(records.keepers[&keeper].fenced[&StreamId(9)], 5);
        }
        assert!(records.keepers[&ids[0]].fenced.is_empty());
        assert_eq!(records.keepers[&ids[1]].epoch, 1);
        assert_eq!(records.keepers[&ids[2]].epoch, 2);
        let grant = records.grant(ids[1], ids[1], 1, true, 30_000, 3_000);
        assert!(grant.granted);
        assert_eq!(grant.fenced, BTreeMap::from([(StreamId(9), 5)]));
        // An unenrolled keeper gets no enforced lease.
        assert!(
            !records
                .grant(ids[2], ids[2], 0, true, 30_000, 3_000)
                .granted
        );
        assert!(
            records
                .grant(ids[2], ids[2], 0, false, 30_000, 3_000)
                .granted
        );
    }

    #[test]
    fn a_recovery_waits_the_longest_lease_ever_granted() {
        let [keeper, other, ..] = ids();
        let mut records = Records::default();
        records.apply(&records.pending(keeper, keeper, 30_000, 3_000).unwrap());
        // A catalog keeper later configured with a shorter lease records
        // nothing; a longer one is recorded before it grants.
        assert_eq!(
            records.pending(keeper, keeper, 30_000, 3_000),
            Some(Change::Lease {
                keeper,
                lease_ms: 30_000,
                margin_ms: 3_000
            })
        );
        records.apply(&records.pending(keeper, keeper, 30_000, 3_000).unwrap());
        assert_eq!(records.pending(keeper, keeper, 10_000, 1_000), None);
        records.apply(&records.pending(keeper, keeper, 60_000, 6_000).unwrap());
        // The lease shrinks back in configuration; the record does not.
        assert_eq!(records.pending(keeper, keeper, 10_000, 1_000), None);
        assert_eq!(records.recovery_wait(&[keeper, other], 11_000), 66_000);
        records.apply(&Change::Fence { keeper });
        assert_eq!(records.recovery_wait(&[keeper], 11_000), 66_000);
        assert_eq!(records.recovery_wait(&[other], 11_000), 11_000);
    }

    #[test]
    fn a_fence_bumps_the_epoch() {
        let keeper = ids()[0];
        let mut records = Records::default();
        records.apply(&Change::Enroll {
            keeper,
            incarnation: keeper,
        });
        records.apply(&Change::Fence { keeper });
        assert_eq!(records.keepers[&keeper].epoch, 2);
        assert!(!records.grant(keeper, keeper, 1, true, 1, 1).granted);
        assert!(records.grant(keeper, keeper, 2, true, 1, 1).granted);
    }
}
