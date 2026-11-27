//! Operator recovery of a stream that lost a quorum of its voters: two of
//! three, or three or more of five.
//!
//! `logkeeper keeper recover-stream` runs on the stopped survivor's data
//! directory under its media lock. It replays the survivor's log through
//! its durable commit index (`Record::Committed`, its snapshot or purge
//! cut) once the cluster finalized leases, and keeps only that prefix: an
//! entry past it may be one the survivor wrote as leader and never
//! committed, at an LSN where the lost voters then committed and
//! acknowledged another record. The loss point it reports and the catalog
//! records is then exact, `max(offloaded run, survivor's commit)` (Lean
//! `OffloadPrefix.restore_exact`). Before leases are finalized keepers do
//! not write their commit index: it keeps the whole log as before and
//! reports the last point it knows committed, its snapshot, saying that
//! records above it may have been overwritten. It asks every other keeper for its status, and refuses unless the operator
//! acknowledges the data loss and the other voters that answer with a
//! healthy replica do not form a quorum with the survivor (none of three,
//! at most one of five). A voter that does not answer is asked again for
//! longer before it counts as lost: a slow keeper is not a lost one. With
//! two survivors of five, the recovery runs on the one that knows the later
//! commit, then the later last log entry, then the lower keeper ID: it asks
//! the other for both (`Request::LocalProgress`) and refuses on the other's
//! keeper.
//! The other survivor keeps its seat in the recovered configuration and
//! catches up from the survivor like any follower, its divergent
//! uncommitted suffix replaced. It then stages an installed empty copy on
//! each replacement and commits the
//! recovery as one catalog transaction: it bumps the stream's configuration
//! epoch (its revision) and installs the new membership, fences the stream
//! for every voter it leaves, and bumps the epochs of the keepers the
//! operator declared dead with `--lost`. The fence never needs the operator:
//! a voter the recovered membership leaves can only retire its copy. Once
//! the transaction commits, the command waits a whole liveness lease plus
//! the drift margin, so every lease a lost voter held has ended on its own
//! clock, whether or not it still runs and whether or not anyone can reach
//! it (`keeper/lease.rs`). Only then does it write one WAL round on the
//! survivor: a vote for itself in a term above every term it has seen, and
//! two entries in that term, right after the kept prefix, which truncates
//! the uncommitted tail in the same round. The first, `Command::Recover`, stages the move
//! and fences the stream under the recovery writer at an epoch above every
//! applied epoch. The second is the membership of the survivor and the two
//! replacements. When the survivor starts, its replacements elect it with
//! their empty logs, and it replicates its log, which commits the recovery.
//!
//! A lost voter that never held a lease cannot be deposed by time, so the
//! operator must name it with `--lost`, the statement that it is down or
//! fenced. Until the cluster finalizes leases, the recovery stages the move
//! in the catalog as before and needs both lost voters named and proven
//! retired with signed retirement proofs (`keeper/retirement.rs`). After,
//! retirement proofs are optional defence in depth, checked when given.

use std::{collections::BTreeMap, io, time::Duration};

use journal_contract::{Epoch, Lsn, StreamId};
use openraft::{BasicNode, EntryPayload};
use tokio::time::{Instant, timeout};
use uuid::Uuid;

use super::{Config, FenceProof, Reply, Request, catalog_stream, failure, lease};
use crate::stream::consensus::Voters;
use crate::stream::{
    consensus::{
        Entry, LogId, Stage, Vote, assignment,
        authority::{Recovered, RecoveryRecord, RecoverySource},
        catalog::{self, Catalog},
        decisions, invalid,
        network::{Lane, Rpc},
        placement::Placement,
        state::{Command, Outcome},
        storage::{self, Disk, Record},
    },
    wire::KeeperId,
};

const STATUS_TIMEOUT: Duration = Duration::from_secs(2);
/// Further status requests to a lost voter that did not answer the first,
/// each given `LOST_STATUS_TIMEOUT`, with `LOST_STATUS_PAUSE` between them.
const LOST_STATUS_ROUNDS: u32 = 2;
const LOST_STATUS_TIMEOUT: Duration = Duration::from_secs(5);
const LOST_STATUS_PAUSE: Duration = Duration::from_secs(1);
const STAGING_TIMEOUT: Duration = Duration::from_secs(10);
/// Why a loss point below the kept head is not exact.
const UNKNOWN_COMMIT: &str = ", the last point this keeper knows committed: the cluster has not \
     finalized liveness leases, so keepers do not record their commit index, and the records \
     this keeper keeps above it may have been overwritten by the lost voters with records \
     writers were acknowledged";

/// What the operator asked of a recovery.
#[derive(Clone, Debug, Default)]
pub struct Recovery {
    /// The operator accepts that acknowledged records only the lost voters
    /// held are gone.
    pub acknowledge_data_loss: bool,
    /// Voters of the lost configuration the operator declares dead: their
    /// epochs are bumped, which ends every lease they hold for every
    /// stream. Optional once leases are finalized, except for a lost voter
    /// that never held a lease. Before that it must name every lost voter.
    pub lost: Option<Vec<Uuid>>,
    /// The replacement keepers, one per lost voter. Without them the
    /// best-ranked live, accepting keepers in free failure domains are
    /// chosen.
    pub with: Option<Vec<Uuid>>,
    /// One retirement proof per lost voter. Required until leases are
    /// finalized; optional after, and checked when given.
    pub fence_proofs: Vec<FenceProof>,
    /// Exercises protocol compatibility with pre-retirement recovery
    /// histories whose former voters could still boot.
    #[cfg(test)]
    pub(in crate::stream::consensus) legacy_unfenced: bool,
    /// Fails the durable WAL round: 2 before its boundary, 3 after it.
    #[cfg(test)]
    pub(super) interrupt: Option<u8>,
    /// Keepers the command cannot reach, as if partitioned from it.
    #[cfg(test)]
    pub(super) unreachable: Vec<Uuid>,
}

/// What a recovery did, or found already done.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecoveryReport {
    pub stream: StreamId,
    pub lost: Vec<Uuid>,
    pub voters: Voters,
    pub revision: u64,
    /// The last record the survivor keeps: through its durable commit index
    /// once leases are finalized, its whole log before.
    pub head: Lsn,
    /// Every record at or below it is one the stream committed; writers that
    /// were acknowledged records above it lost them.
    pub loss_point: Lsn,
    /// Whether the loss point is exact. False before leases are finalized:
    /// the survivor did not know its commit index, so records between the
    /// loss point and its head may differ from what writers were
    /// acknowledged.
    pub exact: bool,
    pub epoch: Epoch,
    pub term: u64,
    /// False when an earlier run already wrote this recovery.
    pub written: bool,
    /// The offload store's part, when the keeper offloads: the exact loss
    /// point and whether the store's longer run replaced the survivor's.
    pub offload: Option<super::offload::OffloadRecovery>,
    /// The keepers the catalog fences the stream for; empty when leases are
    /// not finalized and the catalog only staged the move.
    pub fenced: Vec<Uuid>,
    /// How long the command waited after the catalog committed, so the
    /// lost voters' leases ended before the recovered configuration serves.
    pub waited: Duration,
}

impl std::fmt::Display for RecoveryReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "stream {:032x} {} from this keeper at head {}: voters {}, revision {}, \
             term {}, recovery fence at epoch {}. Lost voters {} must retire their \
             copies or stay retired; the catalog fences the stream for {} keeper(s), and \
             this command waited {} ms for their leases to end. Start this keeper, then \
             acknowledge the recovery so writers can seal again.",
            self.stream.0,
            if self.written {
                "recovered"
            } else {
                "was already recovered"
            },
            self.head.0,
            listed(&self.voters, " "),
            self.revision,
            self.term,
            self.epoch.0,
            listed(&self.lost, " and "),
            self.fenced.len(),
            self.waited.as_millis(),
        )?;
        write!(f, " Loss point: record {}", self.loss_point.0)?;
        if self.exact {
            write!(f, "; acknowledged records above it are lost.")?;
        } else {
            write!(f, "{UNKNOWN_COMMIT}.")?;
        }
        if let Some(offload) = &self.offload {
            write!(f, " {offload}")?;
        }
        Ok(())
    }
}

impl Config {
    /// Recovers `stream` on this stopped keeper from its local replica, as
    /// the module documentation describes.
    pub async fn recover_stream(
        &self,
        stream: StreamId,
        recovery: Recovery,
    ) -> io::Result<RecoveryReport> {
        let placement = self.validate()?;
        let keeper = KeeperId(self.keeper.as_u128());
        let rpc = Rpc::new(
            self.tls.peer_protocols(keeper, Lane::Application.alpns())?,
            self.keepers.clone(),
            Lane::Application,
        );
        if stream == catalog_stream::STREAM {
            return Err(invalid(
                "the replicated catalog requires its original quorum or disaster restore; \
                 recover-stream cannot rewrite its membership",
            ));
        }
        let enrollment = self.enrollment()?;
        let disk = tokio::task::spawn_blocking(move || Disk::open(enrollment)).await??;
        let result = self
            .recover_on(&disk, &rpc, &placement, stream, recovery)
            .await;
        let shutdown = disk.shutdown().await;
        match result {
            Ok(recovered) => shutdown.map(|()| recovered),
            Err(error) => Err(error),
        }
    }

    async fn recover_on(
        &self,
        disk: &Disk,
        rpc: &Rpc,
        placement: &Placement,
        stream: StreamId,
        recovery: Recovery,
    ) -> io::Result<RecoveryReport> {
        let genesis = disk
            .genesis(stream)
            .ok_or_else(|| invalid("stream is not installed on this keeper"))?;
        if genesis.immutable {
            return Err(invalid(
                "immutable histories require their original quorum or a successor with a fresh stream ID",
            ));
        }
        let generation = disk
            .ownership(stream)
            .filter(|book| book.installed())
            .and_then(|book| book.generation())
            .ok_or_else(|| invalid("this keeper holds no installed replica of the stream"))?;
        disk.check_placement(stream, placement)?;
        let point = disk.recovery_point(stream);
        // Once leases are finalized, keepers write their commit indexes, so
        // the recovery keeps exactly the survivor's committed prefix: an
        // entry past it may be one the lost voters overwrote with other
        // committed records. Before, it keeps the whole log and reports the
        // last point it knows committed as the loss point.
        let version = self.catalog_version(disk, rpc).await;
        let leases = version >= super::super::CLUSTER_VERSION_LEASES;
        // At this level the stream records the catalog's record, and its
        // fence clears only by writing the typed recovery entry.
        let entry = version >= super::super::CLUSTER_VERSION_RECOVERY_ENTRY;
        let exact = leases && point.written.is_none();
        if exact && point.committed.is_none() && point.tip.is_some() {
            return Err(invalid(
                "refused: this keeper never recorded that the stream committed an entry, so a \
                 recovery from it would keep no history; recover from another survivor",
            ));
        }
        let committed_next = point.committed.map_or(0, |id| id.index + 1);
        let next = decisions::recovery_cut(
            exact,
            committed_next,
            point.tip.map_or(0, |tip| tip.index + 1),
        );
        let replayed = storage::replay(disk, genesis.clone(), placement.clone(), next).await?;
        let head = replayed
            .head
            .clone()
            .map_err(|error| invalid(format!("the stream cannot be recovered: {error:?}")))?;
        let configuration = replayed
            .configuration
            .filter(|_| replayed.uniform)
            .ok_or_else(|| {
                invalid(
                    "the survivor's latest membership is not a finalized configuration; \
                         restore the joint quorum before changing membership",
                )
            })?;
        if let Some(done) = point.written {
            let report = RecoveryReport {
                stream,
                lost: lost(&done.old, &done.target),
                voters: done.target,
                revision: configuration.revision,
                head,
                loss_point: head,
                exact: leases,
                epoch: replayed.epoch,
                term: point.vote_term,
                written: false,
                offload: None,
                fenced: Vec::new(),
                waited: Duration::ZERO,
            };
            crate::stream::consensus::logging::audit_recovery(
                self.keeper,
                stream,
                &report.lost,
                &report.voters,
                report.revision,
                report.head,
                report.epoch,
                report.term,
                report.written,
                "already_written",
            );
            return Ok(report);
        }
        let survivor_votes = configuration.voters.contains(&self.keeper);
        if !survivor_votes {
            return Err(invalid(
                "this keeper is not a voter of the stream's latest configuration",
            ));
        }
        let old = configuration.voters;
        let others = old
            .iter()
            .copied()
            .filter(|voter| *voter != self.keeper)
            .collect::<Vec<_>>();
        let mut dead = recovery.lost.clone().unwrap_or_default();
        dead.sort_unstable();
        dead.dedup();
        if dead.iter().any(|keeper| !others.contains(keeper)) {
            return Err(invalid(format!(
                "refused: --lost may name only other voters: {}",
                listed(&others, ", "),
            )));
        }
        let named = dead == others;
        // Once leases are finalized, the catalog's fence and the wait for
        // the lost voters' leases depose them whether or not they still run,
        // so naming them and proving their retirement become optional.
        // Before that, nothing deposes a lost voter that still runs: the
        // operator names both and proves both retired, as before.
        if recovery.acknowledge_data_loss && !leases && !named {
            return Err(invalid(format!(
                "refused: the cluster has not finalized liveness leases, so nothing deposes \
                 a lost voter that still runs. Retire every lost keeper, then name them with \
                 --lost {} and a --fence-proof for each",
                listed(&others, ","),
            )));
        }
        // Preserve regression coverage for installations whose old operator
        // workflows had already performed a recovery without retiring media.
        #[cfg(test)]
        let legacy_unfenced = recovery.legacy_unfenced;
        #[cfg(not(test))]
        let legacy_unfenced = false;
        if recovery.acknowledge_data_loss
            && !legacy_unfenced
            && (!leases || !recovery.fence_proofs.is_empty())
        {
            self.verify_recovery_fences(&dead, &recovery.fence_proofs)?;
        }

        #[cfg(test)]
        let unreachable = &recovery.unreachable;
        let ask = |keeper: Uuid, limit: Duration| async move {
            #[cfg(test)]
            if unreachable.contains(&keeper) {
                return (keeper, None);
            }
            let status = timeout(
                limit,
                rpc.call_application(keeper, Request::KeeperStatus(stream), limit),
            )
            .await;
            match status {
                Ok(Ok(Reply::Status(status))) if status.keeper == keeper => (keeper, Some(status)),
                _ => (keeper, None),
            }
        };
        let mut statuses = BTreeMap::new();
        // Draining retired keepers still hold replicas, so they are asked too.
        let asked = placement
            .all_domains()
            .keys()
            .copied()
            .filter(|keeper| *keeper != self.keeper)
            .map(|keeper| ask(keeper, STATUS_TIMEOUT));
        statuses.extend(futures::future::join_all(asked).await);
        // A lost voter that missed the first request may only be slow. It
        // counts as lost only after it also misses the longer ones.
        // An acknowledged recovery already has affirmative retirement
        // evidence. Retries are only useful in the diagnostic preview.
        for _ in 0..if recovery.acknowledge_data_loss && !legacy_unfenced {
            0
        } else {
            LOST_STATUS_ROUNDS
        } {
            let silent = others
                .iter()
                .copied()
                .filter(|voter| statuses.get(voter).cloned().flatten().is_none())
                .collect::<Vec<_>>();
            if silent.is_empty() {
                break;
            }
            tokio::time::sleep(LOST_STATUS_PAUSE).await;
            let asked = silent
                .into_iter()
                .map(|voter| ask(voter, LOST_STATUS_TIMEOUT));
            for (voter, status) in futures::future::join_all(asked).await {
                if status.is_some() {
                    statuses.insert(voter, status);
                }
            }
        }
        let peers = others
            .iter()
            .copied()
            .filter(|voter| {
                statuses
                    .get(voter)
                    .and_then(|status| status.as_ref())
                    .is_some_and(|status| status.replica == Some(true))
            })
            .collect::<Vec<_>>();
        let healthy = peers.len() as u64;
        if healthy + 1 >= old.quorum() as u64 {
            return Err(invalid(format!(
                "refused: {healthy} other voter(s) of {old:?} answer with a healthy replica, \
                 so the stream still has a quorum; restart this keeper instead"
            )));
        }
        // With two survivors of five, one recovers, so two runs can never
        // write rival recoveries: the one that knows the later commit, then
        // the more advanced log. The other keeps only what the recovered
        // history keeps, so it never knew a later commit than the recovery
        // keeps. A survivor of an older build reports only its tip.
        for peer in &peers {
            let progress = match rpc
                .call_application(*peer, Request::LocalProgress(stream), STATUS_TIMEOUT)
                .await
            {
                Ok(Reply::Progress { tip, committed }) => Some((tip, committed)),
                _ => None,
            };
            let (tip, committed) = match progress {
                Some(progress) => progress,
                None => match rpc
                    .call_application(*peer, Request::LocalTip(stream), STATUS_TIMEOUT)
                    .await
                {
                    Ok(Reply::Tip(tip)) => (tip, point.committed),
                    _ => {
                        return Err(invalid(format!(
                            "refused: surviving voter {peer} did not report its last log \
                             entry, so this recovery cannot tell which survivor is more \
                             advanced; retry"
                        )));
                    }
                },
            };
            let rank = |committed: Option<LogId>, tip: Option<LogId>, keeper: Uuid| {
                (committed.map(|id| id.index), tip, std::cmp::Reverse(keeper))
            };
            if rank(committed, tip, *peer) > rank(point.committed, point.tip, self.keeper) {
                return Err(invalid(format!(
                    "refused: surviving voter {peer} knows the later commit or holds the more \
                     advanced log (committed {committed:?}, last {tip:?} against this keeper's \
                     {:?}, {:?}); stop it and recover from it instead",
                    point.committed, point.tip
                )));
            }
        }
        let mut survivors = peers.clone();
        survivors.push(self.keeper);
        survivors.sort_unstable();
        let others = others
            .into_iter()
            .filter(|voter| !peers.contains(voter))
            .collect::<Vec<_>>();
        // A surviving voter cannot be declared dead.
        if let Some(alive) = dead.iter().find(|keeper| peers.contains(keeper)) {
            return Err(invalid(format!(
                "refused: --lost names {alive}, which answers with a healthy replica"
            )));
        }

        let health = statuses
            .iter()
            .map(|(keeper, status)| {
                (
                    *keeper,
                    assignment::Health {
                        live: status.is_some(),
                        accepting: status.as_ref().is_some_and(|status| status.accepting),
                        streams: status.as_ref().map_or(0, |status| status.streams),
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        let target = match recovery.with {
            Some(with) => {
                let target = Voters::sorted(&[survivors.as_slice(), with.as_slice()].concat())
                    .filter(|target| target.len() == old.len())
                    .ok_or_else(|| {
                        invalid(format!(
                            "--with names one replacement for each of the {} lost voters",
                            others.len()
                        ))
                    })?;
                if with.iter().any(|keeper| {
                    old.contains(keeper)
                        || !statuses
                            .get(keeper)
                            .and_then(|status| status.as_ref())
                            .is_some_and(|status| status.accepting)
                }) || !placement.roster(&target)
                {
                    return Err(invalid(
                        "replacements must be live, accepting keepers outside the lost \
                         configuration, spread over failure domains with the survivors",
                    ));
                }
                target
            }
            None => assignment::recovery_roster(
                stream,
                &survivors,
                old,
                &assignment::View {
                    eligible: placement.domains(),
                    health: &health,
                },
            )
            .ok_or_else(|| {
                invalid("no live, accepting keepers in free failure domains can replace the lost voters")
            })?,
        };
        let stage = Stage {
            stream,
            source: configuration.revision,
            old,
            target,
        };
        if point.snapshot_ahead {
            return Err(invalid(
                "the selected snapshot is ahead of the log; start and stop this keeper first",
            ));
        }
        let term = decisions::recovery_term(point.vote_term, point.log_term)
            .ok_or_else(|| invalid("the stream's term is exhausted"))?;
        // With offload, the history is the survivor plus the object store.
        let offload = self
            .recovery_offload(stream, head, &replayed, stage.source.saturating_add(1))
            .await?;
        // The head the survivor knew committed, its snapshot or purge cut
        // when it never wrote a commit index.
        let known = if next == committed_next {
            head
        } else {
            storage::replay(disk, genesis.clone(), placement.clone(), committed_next)
                .await?
                .head
                .unwrap_or(Lsn(0))
        };
        let restored = offload.as_ref().is_some_and(|(_, report)| report.restored);
        let loss_point = Lsn(decisions::reported_loss_point(
            exact || restored,
            offload
                .as_ref()
                .map_or(head, |(_, report)| report.kept_through)
                .0,
            known.0,
        ));
        let restored_epoch = offload.as_ref().map_or(replayed.epoch, |(restore, _)| {
            restore.epoch.max(replayed.epoch)
        });
        let epoch = decisions::recovery_epoch(restored_epoch.0)
            .map(Epoch)
            .ok_or_else(|| invalid("the stream's epoch is exhausted"))?;
        if !decisions::allows_recovery(
            recovery.acknowledge_data_loss,
            survivor_votes,
            healthy,
            old.len(),
        ) {
            return Err(invalid(format!(
                "refused without --acknowledge-data-loss. This would make this keeper's copy of \
                 stream {:032x} through head {} the only history: records only {} held are \
                 lost, and writers lose every record they were acknowledged above {}{}. The voters would become {target:?} at revision {}, term {term}, with \
                 seals refused under a recovery fence at epoch {} until an administrator \
                 acknowledges the recovery. Once leases are finalized the catalog fences the \
                 stream for {}, and the recovered configuration serves only once their \
                 leases have ended. To proceed, add --acknowledge-data-loss; add --lost {} \
                 to declare any of them dead, which ends its leases for every stream. Before \
                 leases are finalized, also retire them all and add a --fence-proof for each",
                stream.0,
                head.0,
                listed(&others, " and "),
                loss_point.0,
                if exact || restored {
                    ""
                } else {
                    UNKNOWN_COMMIT
                },
                stage.source + 1,
                epoch.0,
                listed(&others, " and "),
                listed(&others, ","),
            )));
        }

        for replacement in target.into_iter().filter(|id| !old.contains(id)) {
            match rpc
                .call_application(
                    replacement,
                    Request::StageRecovered {
                        genesis: genesis.clone(),
                        stage: stage.clone(),
                    },
                    STAGING_TIMEOUT,
                )
                .await?
            {
                Reply::Generation(_) => (),
                _ => {
                    return Err(invalid(format!(
                        "replacement {replacement} refused the recovered copy"
                    )));
                }
            }
        }

        // The catalog commits the recovery before the survivor writes it:
        // the recovered membership, the fence of every voter it leaves, and
        // the epochs of the dead. A lost voter that restarts asks for the
        // staged move before it campaigns or serves a read
        // (`keeper/certify.rs`), and one that kept running loses its lease.
        // So the recovery refuses without the catalog. It commits after the
        // replacements, so a refused replacement leaves the old
        // configuration unfenced.
        let record = RecoveryRecord {
            stream,
            epoch: stage.source.saturating_add(1),
            loss_point,
            source: if restored {
                RecoverySource::ObjectStore
            } else {
                RecoverySource::Survivor
            },
            time_unix_ms: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map_or(0, |since| since.as_millis() as u64),
        };
        let (fenced, wait, record) = match self
            .recover_in_catalog(disk, rpc, placement, &stage, &dead, record)
            .await
            .map_err(|error| {
                invalid(format!(
                    "refused: the catalog must record the recovery so the lost voters stay \
                     fenced: {error}"
                ))
            })? {
            Some(recovered) => {
                let unnamed = recovered
                    .unleased
                    .iter()
                    .filter(|keeper| !dead.contains(keeper))
                    .copied()
                    .collect::<Vec<_>>();
                if !unnamed.is_empty() {
                    return Err(invalid(format!(
                        "refused: {unnamed:?} never held a liveness lease, so no lease of theirs \
                         ends by time. The catalog fences them, but confirm that each is down \
                         or fenced, then name it with --lost and run this again"
                    )));
                }
                // An earlier run may have committed the catalog's record:
                // the stream carries the catalog's, not this run's.
                (
                    recovered.fenced,
                    Duration::from_millis(recovered.wait_ms),
                    Some(recovered.record),
                )
            }
            None if named => {
                self.stage_in_catalog(disk, rpc, placement, &stage)
                    .await
                    .map_err(|error| {
                        invalid(format!(
                            "refused: the catalog must record the recovery so the lost voters \
                             stay fenced: {error}"
                        ))
                    })?;
                (Vec::new(), Duration::ZERO, None)
            }
            None => {
                return Err(invalid(format!(
                    "refused: the cluster has not finalized liveness leases, so nothing deposes \
                     a lost voter that still runs. Confirm that {} are down or fenced, \
                     then name them with --lost {}",
                    listed(&others, " and "),
                    listed(&others, ","),
                )));
            }
        };
        // The recovered configuration serves only after every lease the lost
        // voters held when the catalog committed has ended on their clocks.
        // The survivor stays stopped under this command's media lock.
        lease::wait_for_expiry(wait).await?;
        let log_id = |index| {
            LogId::new(
                openraft::vote::leader_id_std::CommittedLeaderId::new(term),
                index,
            )
        };
        let nodes = target
            .into_iter()
            .map(|id| {
                Ok((
                    id.as_u128(),
                    BasicNode::new(
                        self.keepers
                            .get(&id)
                            .ok_or_else(|| invalid("unknown replacement keeper"))?
                            .to_string(),
                    ),
                ))
            })
            .collect::<io::Result<BTreeMap<_, _>>>()?;
        let membership = openraft::Membership::new(vec![nodes.keys().copied().collect()], nodes)
            .map_err(io::Error::other)?;
        let mut commands = Vec::new();
        if let Some((restore, _)) = &offload {
            commands.push(Command::Restore(restore.clone()));
        }
        commands.push(match record.filter(|_| entry) {
            Some(record) => Command::RecoverRecorded {
                stage: stage.clone(),
                record,
                exact: exact || restored,
            },
            None => Command::Recover(stage.clone()),
        });
        let mut entries = commands
            .into_iter()
            .enumerate()
            .map(|(offset, command)| Entry {
                log_id: log_id(next + offset as u64),
                payload: EntryPayload::Normal(command),
            })
            .collect::<Vec<_>>();
        entries.push(Entry {
            log_id: log_id(next + entries.len() as u64),
            payload: EntryPayload::Membership(membership),
        });
        #[cfg(test)]
        if let Some(cut) = recovery.interrupt {
            disk.interrupt_next(stream, cut);
        }
        disk.write(Record::Owned(
            generation,
            Box::new(Record::Recover(
                stream,
                Vote::new_committed(term, self.keeper.as_u128()),
                entries,
            )),
        ))
        .await?;
        let report = RecoveryReport {
            stream,
            lost: others,
            voters: target,
            revision: stage.source + 1,
            head,
            loss_point,
            exact: exact || restored,
            epoch,
            term,
            written: true,
            offload: offload.map(|(_, report)| report),
            fenced,
            waited: wait,
        };
        crate::stream::consensus::logging::audit_recovery(
            self.keeper,
            stream,
            &report.lost,
            &report.voters,
            report.revision,
            report.head,
            report.epoch,
            report.term,
            report.written,
            "ok",
        );
        Ok(report)
    }

    /// The offload store's part of a recovery, when this keeper offloads.
    async fn recovery_offload(
        &self,
        stream: StreamId,
        head: Lsn,
        replayed: &storage::Replayed,
        revision: u64,
    ) -> io::Result<
        Option<(
            crate::stream::consensus::state::Restore,
            super::offload::OffloadRecovery,
        )>,
    > {
        let (Some(config), Some(view)) = (&self.offload, &replayed.offload) else {
            return Ok(None);
        };
        let store = crate::stream::consensus::offload::Store::open(config)?;
        super::offload::plan_recovery(&store, stream, head, replayed.epoch, view, revision)
            .await
            .map(Some)
            .map_err(|error| {
                invalid(format!(
                    "refused: the offload store must be readable to find the loss point: {error}"
                ))
            })
    }

    /// The catalog's finalized cluster feature level, or V1 when no catalog
    /// keeper answers.
    async fn catalog_version(&self, disk: &Disk, rpc: &Rpc) -> u32 {
        let reply = match self.catalog_voters {
            None if self.catalog == self.keeper => {
                return disk.cluster_version();
            }
            None => rpc
                .call_application(self.catalog, Request::ClusterVersion, STATUS_TIMEOUT)
                .await
                .ok(),
            Some(voters) => {
                let order = voters
                    .into_iter()
                    .chain(self.keepers.keys().copied())
                    .filter(|voter| *voter != self.keeper)
                    .collect::<Vec<_>>();
                catalog::ask(&order, Instant::now() + STAGING_TIMEOUT, |voter| {
                    rpc.call_application(voter, Request::ClusterVersion, STATUS_TIMEOUT)
                })
                .await
                .map(|(_, reply)| reply)
            }
        };
        match reply {
            Some(Reply::ClusterVersion(version)) => version,
            _ => crate::stream::consensus::CLUSTER_VERSION_V1,
        }
    }

    /// Commits the recovery as a catalog transaction. `None` when the
    /// catalog cannot: leases are not finalized, or it runs an older build.
    async fn recover_in_catalog(
        &self,
        disk: &Disk,
        rpc: &Rpc,
        placement: &Placement,
        stage: &Stage,
        dead: &[Uuid],
        record: RecoveryRecord,
    ) -> io::Result<Option<Recovered>> {
        let request = Request::RecoverStream {
            stage: stage.clone(),
            dead: dead.to_vec(),
            record,
        };
        let reply = match self.catalog_voters {
            None if self.catalog == self.keeper => {
                let wait =
                    decisions::recovery_wait(self.lease_millis, self.lease_drift_margin_millis)
                        .ok_or_else(|| invalid("lease duration overflows"))?;
                Catalog::new(disk.clone(), &self.data)?
                    .recover(stage.clone(), dead.to_vec(), record, placement, wait)
                    .await?
            }
            None => {
                rpc.call_application(self.catalog, request, STAGING_TIMEOUT)
                    .await?
            }
            Some(voters) => {
                let order = voters
                    .into_iter()
                    .chain(self.keepers.keys().copied())
                    .filter(|voter| *voter != self.keeper)
                    .collect::<Vec<_>>();
                catalog::ask(&order, Instant::now() + STAGING_TIMEOUT, |voter| {
                    rpc.call_application(voter, request.clone(), STATUS_TIMEOUT)
                })
                .await
                .map_or_else(
                    || failure(journal_contract::JournalError::Unavailable),
                    |(_, reply)| reply,
                )
            }
        };
        match reply {
            Reply::Recovered(mut recovered) => {
                // Never wait less than this keeper's own lease would need.
                let own =
                    decisions::recovery_wait(self.lease_millis, self.lease_drift_margin_millis)
                        .unwrap_or(u64::MAX);
                recovered.wait_ms = recovered.wait_ms.max(own);
                Ok(Some(recovered))
            }
            Reply::Unsupported(_)
            | Reply::Decision(Outcome::Refused(journal_contract::JournalError::Unsupported)) => {
                Ok(None)
            }
            Reply::Decision(Outcome::Refused(journal_contract::JournalError::Conflict {
                ..
            })) => Err(invalid(
                "the catalog records a pending move or a different source configuration; \
                 restore the original quorum and resolve membership first",
            )),
            Reply::Decision(Outcome::Refused(error)) => Err(invalid(format!(
                "the catalog refused the recovery: {error:?}"
            ))),
            _ => Err(invalid("the catalog did not record the recovery")),
        }
    }

    async fn stage_in_catalog(
        &self,
        disk: &Disk,
        rpc: &Rpc,
        placement: &Placement,
        stage: &Stage,
    ) -> io::Result<()> {
        let reply = match self.catalog_voters {
            None if self.catalog == self.keeper => {
                Catalog::new(disk.clone(), &self.data)?
                    .stage(stage.clone(), placement)
                    .await?
            }
            None => {
                rpc.call_application(self.catalog, Request::Stage(stage.clone()), STAGING_TIMEOUT)
                    .await?
            }
            Some(voters) => {
                // Repair may have replaced every configured voter.
                let order = voters
                    .into_iter()
                    .chain(self.keepers.keys().copied())
                    .filter(|voter| *voter != self.keeper)
                    .collect::<Vec<_>>();
                catalog::ask(&order, Instant::now() + STAGING_TIMEOUT, |voter| {
                    rpc.call_application(voter, Request::Stage(stage.clone()), STATUS_TIMEOUT)
                })
                .await
                .map_or_else(
                    || failure(journal_contract::JournalError::Unavailable),
                    |(_, reply)| reply,
                )
            }
        };
        match reply {
            Reply::Staged(receipt) if receipt == *stage => Ok(()),
            Reply::Decision(Outcome::Refused(journal_contract::JournalError::Conflict {
                ..
            })) => Err(invalid(
                "the catalog records a pending move or a different source configuration; +                             restore the original quorum and resolve membership first",
            )),
            Reply::Decision(Outcome::Refused(error)) => {
                Err(invalid(format!("the catalog refused the stage: {error:?}")))
            }
            _ => Err(invalid("the catalog did not stage the recovery")),
        }
    }
}

/// The voters of `old` that `target` no longer names.
fn lost(old: &Voters, target: &Voters) -> Vec<Uuid> {
    old.iter()
        .copied()
        .filter(|voter| !target.contains(voter))
        .collect()
}

fn listed(keepers: &[Uuid], separator: &str) -> String {
    keepers
        .iter()
        .map(Uuid::to_string)
        .collect::<Vec<_>>()
        .join(separator)
}
