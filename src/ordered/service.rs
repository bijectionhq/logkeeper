//! The worker-facing authority of an installed journal group.
//!
//! Only the configured journal coordinators participate in voter exchanges.
//! The accepting transport binds a worker or custodian identity before
//! handing a request to this service.

use super::{
    AppendResult, BarrierClaim, Checkpoint, CheckpointPreparation, Command, Cut, Enrollment,
    Fingerprint, Grant, Hold, Outcome, Placement, Principal, Receipt, Record, Refusal, Request,
    RequestId, RetainedCheckpoint, State, Window, WriterState,
    replication::{self, Group, Replica, RotationSlots},
};
use std::future::Future;
use tokio::sync::Mutex;

pub mod wire;

const ROUND_ATTEMPTS: usize = 4;
pub(super) const MAX_WITHDRAWN_WORKERS: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Session {
    placement: Placement,
    principal: Principal,
}

impl Session {
    /// Binds the result of authenticating this connection to one installed
    /// group and enrollment. Never construct a session from command fields.
    pub fn authenticated(placement: Placement, principal: Principal) -> Self {
        Self {
            placement,
            principal,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Route {
    pub placement: Placement,
    pub writer: WriterState,
    pub position: u64,
    pub history: Fingerprint,
    pub head: Cut,
    pub last_data: Option<Cut>,
    pub last_maintenance: Option<Cut>,
    pub floor: Cut,
    pub erasure_floor: u64,
    /// Custodian-only accounting for the old roots fenced by the erasure floor.
    pub erasure_retirement: Option<ErasureRetirement>,
    pub checkpoint: Checkpoint,
    pub preparing: Option<CheckpointPreparation>,
    pub retirement: Option<RetainedCheckpoint>,
    pub window: Window,
    pub window_spent: u64,
    pub reusable_bytes: u64,
    pub ordinary_limit: u64,
    pub maintenance_limit: u64,
    pub maintenance_retained: u64,
    pub retry_positions: u64,
    /// Journal time of the last chosen decision, in milliseconds.
    pub time: u64,
    pub serving_lease: u64,
    pub clock_drift: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ErasureRetirement {
    pub outstanding_holds: u64,
    pub unsettled_checkpoints: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decision {
    pub receipt: Receipt,
    pub barrier: Option<BarrierClaim>,
    pub rotation: Option<RotationSlots>,
}

pub struct ReplayPage {
    pub checkpoint: Checkpoint,
    pub through: Cut,
    pub records: Vec<Record>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReplayHead {
    pub next: Cut,
    pub timestamp: i64,
    pub payload_bytes: u64,
    pub record_bytes: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WithdrawnWorker {
    pub enrollment: Enrollment,
    /// Earliest eligible journal time in milliseconds. Zero means eligible on
    /// withdrawal. None means the lease and drift exceed the journal clock range.
    pub eligible_at: Option<u64>,
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Journal(#[from] replication::Error),
    #[error("the journal request was refused: {0:?}")]
    Refused(Refusal),
}

impl From<Refusal> for Error {
    fn from(value: Refusal) -> Self {
        Self::Refused(value)
    }
}

/// A coordinator owns the local ballot sequence for the installed group.
/// Another authenticated coordinator can recover and continue on the same
/// voters after this coordinator or its worker disappears.
pub struct Coordinator<R> {
    group: Group,
    peers: Vec<R>,
    round: Mutex<u64>,
}

impl<R: Replica> Coordinator<R> {
    pub fn new(group: Group, peers: Vec<R>) -> Self {
        Self {
            group,
            peers,
            round: Mutex::new(1),
        }
    }

    #[cfg(feature = "ordered-daemon")]
    pub(in crate::ordered) async fn seal_for_repair(
        &self,
        destination: &Group,
    ) -> Result<replication::RepairSeed, Error> {
        if destination.placement() != self.group.placement()
            || destination.predecessor() != Some(self.group.identity())
        {
            return Err(replication::Error::Group.into());
        }
        let state = self
            .ordered(|round| self.group.recover(&self.peers, round))
            .await?;
        if state.successor.is_none() {
            let request = Request {
                placement: state.placement(),
                principal: Principal::Administrator,
                id: RequestId::fresh(state.position(), state.limits.retry_positions)?,
                command: Command::SealCohort {
                    expected: self.group.identity(),
                    successor: destination.identity(),
                },
            };
            let chosen = self
                .ordered(|round| self.group.choose(&self.peers, round, request.clone()))
                .await?;
            match chosen.receipt().outcome {
                Ok(Outcome::CohortSealed(exact)) if exact == destination.identity() => {}
                Err(reason) => return Err(reason.into()),
                _ => return Err(replication::Error::Group.into()),
            }
        }
        self.ordered(|round| self.group.repair_seed(&self.peers, round, destination))
            .await
    }

    /// Returns the current writer binding and exact recovery coordinates
    /// from the installed group. Routing callers can treat discovery as a hint.
    pub async fn route(&self, session: Session) -> Result<Route, Error> {
        let state = self.recover(session).await?;
        if let Principal::Worker(enrollment) = session.principal
            && state.roster.get(&enrollment.worker) != Some(&enrollment)
        {
            return Err(Refusal::Unauthorized.into());
        }
        Ok(Route {
            placement: state.placement(),
            writer: state.writer_state(),
            position: state.position(),
            history: state.command_history(),
            head: state.head(),
            last_data: state
                .records
                .iter()
                .rev()
                .find(|record| record.result.class == super::AppendClass::Data)
                .map(|record| record.result.cut),
            last_maintenance: state
                .records
                .iter()
                .rev()
                .find(|record| record.result.class == super::AppendClass::Maintenance)
                .map(|record| record.result.cut),
            floor: state.floor(),
            erasure_floor: state.erasure_floor(),
            erasure_retirement: (session.principal == Principal::Custodian && state.erasure_floor() != 0)
                .then(|| {
                    let floor = state.erasure_floor();
                    ErasureRetirement {
                        outstanding_holds: state.holds.values()
                            .filter(|entry| entry.hold.checkpoint.cut.next_lsn < floor)
                            .count() as u64,
                        unsettled_checkpoints: state.old_roots.values()
                            .filter(|entry| entry.checkpoint.cut.next_lsn < floor)
                            .count() as u64,
                    }
                }),
            checkpoint: state.checkpoint(),
            preparing: state.preparing,
            retirement: (session.principal == Principal::Custodian)
                .then(|| state.next_checkpoint_retirement())
                .flatten(),
            window: state.window(),
            window_spent: state.spent_bytes(),
            reusable_bytes: state.ordinary_capacity() - state.retained_bytes,
            ordinary_limit: state.ordinary_capacity(),
            maintenance_limit: state.limits.maintenance_bytes,
            maintenance_retained: state.maintenance_retained,
            retry_positions: state.limits.retry_positions,
            time: state.time(),
            serving_lease: state.limits.serving_lease,
            clock_drift: state.limits.clock_drift,
        })
    }

    /// Binds the principal in the chosen frame to the authenticated session.
    pub async fn execute(&self, session: Session, request: Request) -> Result<Decision, Error> {
        self.admit(session)?;
        if session.principal == Principal::RouteReader
            || matches!(&request.command, Command::SealCohort { .. })
            || request.placement != session.placement
            || request.principal != session.principal
        {
            return Err(Refusal::Unauthorized.into());
        }
        let chosen = self
            .ordered(|round| self.group.choose(&self.peers, round, request.clone()))
            .await
            .map_err(|error| match error {
                Error::Journal(replication::Error::Sealed) => Refusal::CohortSealed.into(),
                error => error,
            })?;
        if chosen.state().successor.is_some()
            && !matches!(
                chosen.receipt().outcome,
                Ok(super::Outcome::CohortSealed(_))
            )
        {
            return Err(Refusal::CohortSealed.into());
        }
        let receipt = chosen.receipt();
        let rotation = chosen.rotation_slots(&request);
        if matches!(request.command, Command::PublishAndRotate { .. })
            && receipt.outcome.is_ok()
            && rotation.is_none()
        {
            return Err(Refusal::Unavailable.into());
        }
        Ok(Decision {
            receipt,
            barrier: chosen.barrier_claim(),
            rotation,
        })
    }

    /// Lets the current writer reconcile an original retained request after
    /// replacement. Authority to inspect the stream and identity of the old
    /// append are established independently.
    pub async fn reconcile(
        &self,
        session: Session,
        grant: Grant,
        original: &Request,
    ) -> Result<AppendResult, Error> {
        let state = self.recover(session).await?;
        state.writer(session.principal, grant)?;
        Ok(state.reconcile_append(original)?)
    }

    /// Resolves a retained cut at or beyond the selected checkpoint.
    /// PrepareCheckpoint rechecks its advancing target before any provider effect.
    pub async fn checkpoint_cut(&self, session: Session, next: u64) -> Result<Cut, Error> {
        State::custodian(session.principal)?;
        let state = self.recover(session).await?;
        if next < state.checkpoint.cut.next_lsn {
            return Err(Refusal::Stale.into());
        }
        state.cut(next).ok_or_else(|| Refusal::Unavailable.into())
    }

    /// Returns distinct withdrawn hold owners in enrollment order, strictly
    /// after the cursor, from a recovered journal state.
    pub async fn withdrawn_workers(
        &self,
        session: Session,
        after: Option<Enrollment>,
        limit: usize,
    ) -> Result<Vec<WithdrawnWorker>, Error> {
        State::custodian(session.principal)?;
        let state = self.recover(session).await?;
        Ok(state
            .withdrawn_hold_owners(after, limit.min(MAX_WITHDRAWN_WORKERS))
            .map(|enrollment| WithdrawnWorker {
                enrollment,
                eligible_at: state.expiry_disposal_time(enrollment),
            })
            .collect())
    }

    /// A withdrawn enrollment can release its old exact hold without
    /// reacquiring visibility into the current writer or admitting new work.
    pub async fn release(&self, session: Session, hold: Hold) -> Result<(), Error> {
        if session.principal != Principal::Worker(hold.owner) {
            return Err(Refusal::Unauthorized.into());
        }
        let state = self.recover(session).await?;
        if state
            .holds
            .get(&hold.id)
            .is_none_or(|entry| entry.hold != hold)
        {
            return Ok(());
        }
        let request = Request {
            placement: state.placement(),
            principal: session.principal,
            id: RequestId::fresh(state.position(), state.limits.retry_positions)?,
            command: Command::Release { hold },
        };
        match self.execute(session, request).await?.receipt.outcome {
            Ok(Outcome::Released) | Err(Refusal::Stale) => Ok(()),
            Err(reason) => Err(reason.into()),
            _ => Err(replication::Error::Group.into()),
        }
    }

    /// Reads a bounded continuation of the exact ordered hold. The caller
    /// keeps the hold until it has finished using the provider checkpoint and
    /// every page of the suffix.
    pub async fn replay(
        &self,
        session: Session,
        hold: Hold,
        from: Cut,
        maximum_bytes: usize,
    ) -> Result<ReplayPage, Error> {
        let state = self.recover(session).await?;
        let (replay, skip) = replay_from(&state, session, hold, from)?;
        replay_page(
            replay.checkpoint(),
            replay.through(),
            replay.records().skip(skip),
            maximum_bytes,
        )
    }

    /// Read the chosen input of a live checkpoint preparation. The selected
    /// base and preparation must still be exact, even across writer replacement.
    pub async fn checkpoint_replay(
        &self,
        session: Session,
        preparation: CheckpointPreparation,
        base: Checkpoint,
        from: Cut,
        maximum_bytes: usize,
    ) -> Result<ReplayPage, Error> {
        State::custodian(session.principal)?;
        let state = self.recover(session).await?;
        if state.preparing != Some(preparation) || state.checkpoint() != base {
            return Err(Refusal::Stale.into());
        }
        checkpoint_records(&state, base, from, preparation.checkpoint, maximum_bytes)
    }

    /// Discovers an input before ordering its preparation. Every page
    /// rechecks the base and terminal cut against the current retained history.
    pub async fn inspect_checkpoint(
        &self,
        session: Session,
        base: Checkpoint,
        from: Cut,
        through: Cut,
        maximum_bytes: usize,
    ) -> Result<ReplayPage, Error> {
        State::custodian(session.principal)?;
        let state = self.recover(session).await?;
        if state.checkpoint() != base {
            return Err(Refusal::Stale.into());
        }
        checkpoint_records(&state, base, from, through, maximum_bytes)
    }

    pub async fn replay_head(
        &self,
        session: Session,
        hold: Hold,
        from: Cut,
    ) -> Result<Option<ReplayHead>, Error> {
        let state = self.recover(session).await?;
        let (replay, skip) = replay_from(&state, session, hold, from)?;
        Ok(replay.records().nth(skip).map(|entry| ReplayHead {
            next: entry.result.cut,
            timestamp: entry.timestamp,
            payload_bytes: entry.payload.len() as u64,
            record_bytes: entry.result.byte_end - entry.result.byte_start,
        }))
    }

    fn admit(&self, session: Session) -> Result<(), Error> {
        if session.placement != self.group.placement() {
            return Err(Refusal::WrongPlacement.into());
        }
        Ok(())
    }

    async fn recover(&self, session: Session) -> Result<State, Error> {
        self.admit(session)?;
        let state = self
            .ordered(|round| self.group.recover(&self.peers, round))
            .await?;
        if state.successor.is_some() {
            return Err(Refusal::CohortSealed.into());
        }
        Ok(state)
    }

    async fn ordered<T, F>(&self, mut attempt: impl FnMut(u64) -> F) -> Result<T, Error>
    where
        F: Future<Output = Result<T, replication::Error>>,
    {
        let mut next = self.round.lock().await;
        let mut newest = None;
        for _ in 0..ROUND_ATTEMPTS {
            let ballot = *next;
            *next = ballot.checked_add(1).ok_or(replication::Error::Capacity)?;
            match attempt(ballot).await {
                Err(replication::Error::Deposed(promised)) => {
                    *next = (*next).max(
                        promised
                            .round
                            .checked_add(1)
                            .ok_or(replication::Error::Capacity)?,
                    );
                    newest = Some(promised);
                }
                result => return result.map_err(Error::from),
            }
        }
        Err(newest
            .map_or(replication::Error::Quorum, replication::Error::Deposed)
            .into())
    }
}

fn checkpoint_records(
    state: &State,
    base: Checkpoint,
    from: Cut,
    through: Cut,
    maximum_bytes: usize,
) -> Result<ReplayPage, Error> {
    if from.next_lsn < base.cut.next_lsn
        || from.next_lsn > through.next_lsn
        || state.cut(from.next_lsn) != Some(from)
        || state.cut(through.next_lsn) != Some(through)
    {
        return Err(Refusal::Invalid.into());
    }
    let (first, end) = super::replay_bounds::retained_indices(
        state.floor().next_lsn,
        from.next_lsn,
        through.next_lsn,
        state.records.len(),
    )
    .ok_or(Refusal::Invalid)?;
    replay_page(
        base,
        through,
        state.records.range(first..end),
        maximum_bytes,
    )
}

fn replay_page<'a>(
    checkpoint: Checkpoint,
    through: Cut,
    records: impl Iterator<Item = &'a Record>,
    mut remaining: usize,
) -> Result<ReplayPage, Error> {
    let mut page = Vec::new();
    for record in records {
        let size = usize::try_from(record.result.byte_end - record.result.byte_start)
            .map_err(|_| Refusal::Capacity)?;
        let Some(next) = remaining.checked_sub(size) else {
            if page.is_empty() {
                return Err(Refusal::Capacity.into());
            }
            break;
        };
        remaining = next;
        page.push(record.clone());
    }
    Ok(ReplayPage {
        checkpoint,
        through,
        records: page,
    })
}

fn replay_from(
    state: &State,
    session: Session,
    hold: Hold,
    from: Cut,
) -> Result<(super::HeldReplay<'_>, usize), Error> {
    let replay = state.held_replay(session.principal, hold)?;
    let same_cut = from == replay.start() || state.cut(from.next_lsn) == Some(from);
    let skip = super::replay_bounds::cursor_offset(
        replay.start().next_lsn,
        from.next_lsn,
        replay.through().next_lsn,
        same_cut,
    )
    .ok_or(Refusal::Invalid)?;
    Ok((replay, skip))
}
