//! Application of the ordered commands owned by an installed journal group.
//!
//! The replication owner supplies one authenticated command at each chosen
//! position. A command's position and the stream's data frontier are separate.

#[cfg(test)]
mod acceptance;
mod admission;
mod codec;
#[cfg(feature = "ordered-daemon")]
pub mod daemon;
pub mod replication;
pub mod service;

use bytes::Bytes;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, VecDeque};
use uuid::Uuid;

pub type Fingerprint = [u8; 32];

/// Fixed stream charge for each record's identity and framing. Replica media
/// also budget for staging and their own metadata.
pub const APPEND_RECORD_CHARGE_BYTES: u64 = 209;
const ACTIVATION_HOLD_SLOTS: usize = 4;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AppendClass {
    Data,
    Maintenance,
}

impl AppendClass {
    fn tag(self) -> u8 {
        match self {
            Self::Data => 0,
            Self::Maintenance => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(
    feature = "ordered-daemon",
    derive(serde::Deserialize, serde::Serialize)
)]
pub struct Placement {
    pub deployment: Uuid,
    pub incarnation: Uuid,
    pub group: Uuid,
    pub generation: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(
    feature = "ordered-daemon",
    derive(serde::Deserialize, serde::Serialize)
)]
pub struct Enrollment {
    pub worker: Uuid,
    pub serial: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(
    feature = "ordered-daemon",
    derive(serde::Deserialize, serde::Serialize)
)]
pub struct Grant {
    pub enrollment: Enrollment,
    pub epoch: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WriterState {
    pub epoch: u64,
    pub grant: Option<Grant>,
}

/// An exclusive data frontier and the identity of the prefix before it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(
    feature = "ordered-daemon",
    derive(serde::Deserialize, serde::Serialize)
)]
pub struct Cut {
    pub next_lsn: u64,
    pub history: Fingerprint,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "ordered-daemon", derive(serde::Deserialize))]
pub struct Window {
    pub allocation: Uuid,
    pub serial: u64,
    pub bytes: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(
    feature = "ordered-daemon",
    derive(serde::Deserialize, serde::Serialize)
)]
pub struct Custody {
    pub allocation: Uuid,
    pub revision: u64,
    pub provider: Fingerprint,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(
    feature = "ordered-daemon",
    derive(serde::Deserialize, serde::Serialize)
)]
pub struct Checkpoint {
    pub cut: Cut,
    pub root: Fingerprint,
    pub manifest: Fingerprint,
    pub custody: Custody,
}

/// A custodian's durable authorization for one exact provider capture.
/// The source descriptor belongs to the database adapter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CheckpointPreparation {
    pub checkpoint: Cut,
    pub root: Fingerprint,
    pub source: Grant,
    pub base: Checkpoint,
    pub custody: Custody,
    pub usable_bytes: u64,
    pub descriptor: Fingerprint,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RetainedCheckpoint {
    pub checkpoint: Checkpoint,
    pub closed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[cfg_attr(
    feature = "ordered-daemon",
    derive(serde::Deserialize, serde::Serialize)
)]
pub struct Hold {
    pub id: RequestId,
    pub owner: Enrollment,
    pub admitted_at: u64,
    pub checkpoint: Checkpoint,
    pub start: Cut,
    pub through: Cut,
}

/// The authenticated principal retained in the chosen command frame.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Principal {
    Administrator,
    Worker(Enrollment),
    Custodian,
    RouteReader,
}

/// An invocation identifier with an immutable retry limit in journal order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[cfg_attr(
    feature = "ordered-daemon",
    derive(serde::Deserialize, serde::Serialize)
)]
pub struct RequestId {
    pub nonce: Uuid,
    pub expires_at: u64,
}

impl RequestId {
    /// Allocates an invocation from an observed chosen position. The retry
    /// horizon starts at the next possible decision slot.
    pub fn fresh(position: u64, retry_positions: u64) -> Result<Self, Refusal> {
        if retry_positions == 0 {
            return Err(Refusal::Invalid);
        }
        let expires_at = position
            .checked_add(1)
            .and_then(|first| first.checked_add(retry_positions))
            .ok_or(Refusal::Capacity)?;
        Ok(Self {
            nonce: Uuid::new_v4(),
            expires_at,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Command {
    Enroll {
        worker: Uuid,
        expected: Option<Enrollment>,
    },
    Withdraw {
        enrollment: Enrollment,
    },
    Grant {
        expected: WriterState,
        candidate: Enrollment,
    },
    Append {
        class: AppendClass,
        grant: Grant,
        expected_next: u64,
        timestamp: i64,
        payload: Bytes,
    },
    /// A fresh read. Each admission protects its own basis at the current
    /// head; a retry is a new admission and never replays an earlier read.
    Barrier {
        grant: Grant,
    },
    PrepareCheckpoint {
        preparation: CheckpointPreparation,
    },
    CloseCheckpoint {
        checkpoint: Checkpoint,
    },
    /// The authenticated custodian attests stable disposition of this exact
    /// closed checkpoint and its provider effects.
    SettleCheckpoint {
        checkpoint: Checkpoint,
        disposition: Fingerprint,
    },
    /// The administrator attests that this withdrawn worker's original
    /// running processes and delivery scope are permanently closed.
    DisposeWorker {
        enrollment: Enrollment,
        disposition: Fingerprint,
    },
    /// The custodian attests the exact reconstructable root and manifest.
    Publish {
        checkpoint: Checkpoint,
    },
    /// Install the custodian's next funded allocation in journal order.
    FundWindow {
        window: Window,
    },
    Protect {
        grant: Grant,
        through: Cut,
    },
    ProtectRange {
        grant: Grant,
        from: u64,
        through: u64,
    },
    ProtectRoot {
        source: Hold,
    },
    Vacate {
        grant: Grant,
    },
    SealCohort {
        expected: Fingerprint,
        successor: Fingerprint,
    },
    Release {
        hold: Hold,
    },
    /// Releases a read hold by the identity of the barrier that admitted it,
    /// for a reader that lost the barrier's reply. Only the admitting
    /// principal can release it. An unknown or already released read is
    /// already released.
    ReleaseRead {
        read: RequestId,
    },
    /// Obtains or renews the current writer's serving lease. The worker
    /// serves reads only before the lease end it receives.
    Lease {
        grant: Grant,
    },
    /// Disposes a withdrawn worker's holds without operator evidence once
    /// journal time has passed its last lease end plus the clock drift bound.
    DisposeExpired {
        enrollment: Enrollment,
    },
    Trim {
        selected: Checkpoint,
        through: Cut,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    pub placement: Placement,
    pub principal: Principal,
    pub id: RequestId,
    pub command: Command,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AppendResult {
    pub class: AppendClass,
    pub position: u64,
    pub lsn: u64,
    pub cut: Cut,
    pub window: Window,
    pub byte_start: u64,
    pub byte_end: u64,
}

/// The exact logical range released by the chosen trim. Physical reuse
/// remains the media owner's responsibility.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrimResult {
    pub from: Cut,
    pub through: Cut,
    pub ordinary_bytes: u64,
    pub maintenance_bytes: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Enrolled(Enrollment),
    Withdrawn,
    Granted {
        grant: Grant,
        recovery: Hold,
    },
    Appended(AppendResult),
    Barrier {
        grant: Grant,
        read: Hold,
    },
    Published(Checkpoint),
    CheckpointPrepared(CheckpointPreparation),
    CheckpointClosed(Checkpoint),
    CheckpointSettled(Checkpoint),
    WorkerDisposed(Enrollment),
    /// `lease_end` is `issued_at + serving_lease` in journal time.
    Leased {
        grant: Grant,
        issued_at: u64,
        lease_end: u64,
    },
    WindowFunded(Window),
    Protected(Hold),
    Released,
    Vacated,
    CohortSealed(Fingerprint),
    Trimmed(TrimResult),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    WrongPlacement,
    Unauthorized,
    Stale,
    Conflict,
    Invalid,
    Expired,
    Capacity,
    Unavailable,
    CohortSealed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Receipt {
    pub placement: Placement,
    pub principal: Principal,
    pub request: RequestId,
    pub position: u64,
    pub outcome: Result<Outcome, Refusal>,
}

/// The exact subject of an applied, protected fresh-read attestation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BarrierClaim {
    placement: Placement,
    grant: Grant,
    read: Hold,
}

impl BarrierClaim {
    pub fn placement(self) -> Placement {
        self.placement
    }

    pub fn grant(self) -> Grant {
        self.grant
    }

    pub fn read(self) -> Hold {
        self.read
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Record {
    pub result: AppendResult,
    pub grant: Grant,
    pub timestamp: i64,
    pub payload: Bytes,
    request: RequestId,
    request_fingerprint: Fingerprint,
}

/// The exact source interval protected by an admitted hold.
pub struct HeldReplay<'a> {
    checkpoint: Checkpoint,
    start: Cut,
    through: Cut,
    records: std::collections::vec_deque::Iter<'a, Record>,
}

impl<'a> HeldReplay<'a> {
    pub fn checkpoint(&self) -> Checkpoint {
        self.checkpoint
    }

    pub fn through(&self) -> Cut {
        self.through
    }

    pub fn start(&self) -> Cut {
        self.start
    }

    pub fn records(self) -> impl ExactSizeIterator<Item = &'a Record> {
        self.records
    }
}

#[derive(Clone, Copy, Debug)]
#[cfg_attr(feature = "ordered-daemon", derive(serde::Deserialize))]
pub struct Limits {
    pub enrolled_workers: usize,
    pub replay_holds: usize,
    pub retry_positions: u64,
    /// Total paid bytes for both retained log classes.
    pub retained_data_bytes: u64,
    /// A standing part of the physical capacity that ordinary appends cannot spend.
    pub maintenance_bytes: u64,
    /// Journal-time milliseconds a renewed serving lease lasts. Must be nonzero.
    pub serving_lease: u64,
    /// Journal-time milliseconds that bound clock error over one lease interval.
    ///
    /// Premise: between any two ordered decisions, elapsed journal time exceeds
    /// elapsed real time by at most `clock_drift`, and a worker's monotonic
    /// clock runs slow by at most the same bound over a lease interval. A
    /// withdrawn worker's holds become disposable without evidence once journal
    /// time reaches its last lease end plus this bound.
    pub clock_drift: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ApplyError {
    #[error("command position does not follow the applied journal prefix")]
    Position,
    #[error("decision time precedes the applied journal time")]
    Time,
}

type RequestKey = (Principal, RequestId);

#[derive(Clone)]
struct RetainedOutcome {
    fingerprint: Fingerprint,
    receipt: Receipt,
}

#[derive(Clone, Copy)]
struct HeldAdmission {
    hold: Hold,
    origin: Principal,
    kind: HoldKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HoldKind {
    Ordinary,
    Recovery,
    Root(RequestId),
}

/// The applied image of one stream in a fixed placement.
///
/// A durable checkpoint of the command journal must retain this entire state,
/// including grants, the retry book and holds, at its exact chosen position.
#[derive(Clone)]
pub struct State {
    placement: Placement,
    limits: Limits,
    position: u64,
    time: u64,
    command_history: Fingerprint,
    voter_scope: Fingerprint,
    successor: Option<Fingerprint>,
    writer_epoch: u64,
    enrollment_serial: u64,
    roster: BTreeMap<Uuid, Enrollment>,
    grant: Option<Grant>,
    /// The last lease end issued to each enrollment that is enrolled or
    /// still owns a hold.
    leases: BTreeMap<Enrollment, u64>,
    window: Window,
    spent: u64,
    retained_bytes: u64,
    maintenance_retained: u64,
    floor: Cut,
    head: Cut,
    checkpoint: Checkpoint,
    preparing: Option<CheckpointPreparation>,
    old_roots: BTreeMap<u64, RetainedCheckpoint>,
    records: VecDeque<Record>,
    holds: BTreeMap<RequestId, HeldAdmission>,
    outcomes: BTreeMap<RequestKey, RetainedOutcome>,
    expiry: BTreeMap<(u64, RequestKey), ()>,
}

impl State {
    /// Opens an empty stream at a certified initial checkpoint and paid window.
    pub fn new(
        placement: Placement,
        limits: Limits,
        checkpoint: Checkpoint,
        window: Window,
    ) -> Result<Self, Refusal> {
        if placement.deployment.is_nil()
            || placement.incarnation.is_nil()
            || placement.group.is_nil()
            || placement.generation == 0
            || checkpoint.cut.next_lsn != 0
            || checkpoint.custody.allocation.is_nil()
            || checkpoint.custody.revision != 1
            || (checkpoint.manifest == [0; 32]) != (checkpoint.custody.provider == [0; 32])
            || window.allocation.is_nil()
            || window.serial != 1
            || window.bytes == 0
            || limits.maintenance_bytes == 0
            || limits
                .retained_data_bytes
                .checked_sub(limits.maintenance_bytes)
                .is_none_or(|ordinary| window.bytes > ordinary)
            || limits
                .replay_holds
                .checked_add(ACTIVATION_HOLD_SLOTS)
                .is_none()
            || limits.enrolled_workers == 0
            || limits.replay_holds == 0
            || limits.retry_positions == 0
            || limits.serving_lease == 0
        {
            return Err(Refusal::Invalid);
        }
        Ok(Self {
            placement,
            limits,
            position: 0,
            time: 0,
            command_history: [0; 32],
            voter_scope: [0; 32],
            successor: None,
            writer_epoch: 0,
            enrollment_serial: 0,
            roster: BTreeMap::new(),
            grant: None,
            leases: BTreeMap::new(),
            window,
            spent: 0,
            retained_bytes: 0,
            maintenance_retained: 0,
            floor: checkpoint.cut,
            head: checkpoint.cut,
            checkpoint,
            preparing: None,
            old_roots: BTreeMap::new(),
            records: VecDeque::new(),
            holds: BTreeMap::new(),
            outcomes: BTreeMap::new(),
            expiry: BTreeMap::new(),
        })
    }

    pub fn placement(&self) -> Placement {
        self.placement
    }
    pub fn position(&self) -> u64 {
        self.position
    }
    /// The journal time of the last applied decision.
    pub fn time(&self) -> u64 {
        self.time
    }
    /// The last lease end issued to this enrollment, if it is retained.
    pub fn lease_end(&self, enrollment: Enrollment) -> Option<u64> {
        self.leases.get(&enrollment).copied()
    }
    pub fn command_history(&self) -> Fingerprint {
        self.command_history
    }
    pub fn writer_state(&self) -> WriterState {
        WriterState {
            epoch: self.writer_epoch,
            grant: self.grant,
        }
    }
    pub fn head(&self) -> Cut {
        self.head
    }
    pub fn floor(&self) -> Cut {
        self.floor
    }
    pub fn checkpoint(&self) -> Checkpoint {
        self.checkpoint
    }
    pub fn window(&self) -> Window {
        self.window
    }
    pub fn spent_bytes(&self) -> u64 {
        self.spent
    }

    fn ordinary_capacity(&self) -> u64 {
        self.limits.retained_data_bytes - self.limits.maintenance_bytes
    }

    pub fn record(&self, lsn: u64) -> Option<&Record> {
        let index = usize::try_from(lsn.checked_sub(self.floor.next_lsn)?).ok()?;
        self.records.get(index)
    }

    /// Selects replay only while this exact hold is live in the applied image.
    /// The caller must also open the exact checkpoint through its custody owner.
    pub fn held_replay(&self, principal: Principal, hold: Hold) -> Result<HeldReplay<'_>, Refusal> {
        if principal != Principal::Worker(hold.owner) {
            return Err(Refusal::Unauthorized);
        }
        if self.holds.get(&hold.id).map(|entry| entry.hold) != Some(hold) {
            return Err(Refusal::Unavailable);
        }
        let index = |lsn: u64| {
            let offset = lsn
                .checked_sub(self.floor.next_lsn)
                .ok_or(Refusal::Unavailable)?;
            usize::try_from(offset).map_err(|_| Refusal::Unavailable)
        };
        // An empty interval remains usable past the replay floor.
        let (start, end) = if hold.start == hold.through {
            (0, 0)
        } else {
            (index(hold.start.next_lsn)?, index(hold.through.next_lsn)?)
        };
        if end < start || end > self.records.len() {
            return Err(Refusal::Unavailable);
        }
        Ok(HeldReplay {
            checkpoint: hold.checkpoint,
            start: hold.start,
            through: hold.through,
            records: self.records.range(start..end),
        })
    }

    /// Reconciles the exact original receipt or the retained data record.
    /// A chosen receipt can outlive physical replay retention.
    pub fn reconcile_append(&self, request: &Request) -> Result<AppendResult, Refusal> {
        let Command::Append {
            class,
            grant,
            expected_next,
            timestamp,
            payload,
        } = &request.command
        else {
            return Err(Refusal::Invalid);
        };
        if request.placement != self.placement {
            return Err(Refusal::WrongPlacement);
        }
        if request.principal != Principal::Worker(grant.enrollment) {
            return Err(Refusal::Unauthorized);
        }
        if let Some(previous) = self.outcomes.get(&(request.principal, request.id)) {
            if !admission::matches_fingerprint(&previous.fingerprint, &fingerprint(request)) {
                return Err(Refusal::Conflict);
            }
            return match previous.receipt.outcome? {
                Outcome::Appended(append) => Ok(append),
                _ => Err(Refusal::Conflict),
            };
        }
        let record = self.record(*expected_next).ok_or(Refusal::Unavailable)?;
        if record.request != request.id
            || record.result.class != *class
            || !admission::matches_fingerprint(&record.request_fingerprint, &fingerprint(request))
            || record.grant != *grant
            || record.timestamp != *timestamp
            || record.payload != *payload
        {
            return Err(Refusal::Conflict);
        }
        Ok(record.result)
    }

    fn retained_receipt(&self, request: &Request) -> Option<Receipt> {
        // Reads have no exact lost-reply recovery: a reissued read is applied
        // again and can never be answered with an earlier read's receipt.
        if matches!(request.command, Command::Barrier { .. }) {
            return None;
        }
        let previous = self.outcomes.get(&(request.principal, request.id))?;
        (request.placement == self.placement
            && admission::matches_fingerprint(&previous.fingerprint, &fingerprint(request)))
        .then_some(previous.receipt)
    }

    /// Applies the decision chosen at `position`, stamped by its proposer
    /// with journal time `time` in milliseconds. Journal time never decreases
    /// in decision order.
    pub fn apply(
        &mut self,
        position: u64,
        time: u64,
        request: Request,
    ) -> Result<Receipt, ApplyError> {
        if self.position.checked_add(1) != Some(position) {
            return Err(ApplyError::Position);
        }
        if time < self.time {
            return Err(ApplyError::Time);
        }
        self.position = position;
        self.time = time;
        let fingerprint = fingerprint(&request);
        self.command_history =
            extend_command_history(self.command_history, position, time, fingerprint);
        while let Some((&(until, key), _)) = self.expiry.first_key_value() {
            if until > position {
                break;
            }
            let _ = self.expiry.pop_first();
            let live_hold = self
                .holds
                .get(&key.1)
                .is_some_and(|entry| entry.origin == key.0);
            if !admission::retains_receipt(position, until, live_hold) {
                self.outcomes.remove(&key);
            }
        }
        let placement = self.placement;
        let principal = request.principal;
        let id = request.id;
        let receipt = |outcome| Receipt {
            placement,
            principal,
            request: id,
            position,
            outcome,
        };
        if request.placement != placement {
            return Ok(receipt(Err(Refusal::WrongPlacement)));
        }
        if id.nonce.is_nil() {
            return Ok(receipt(Err(Refusal::Invalid)));
        }
        let key = (principal, id);
        let reading = matches!(&request.command, Command::Barrier { .. });
        if let Some(previous) = self.outcomes.get(&key) {
            // A retained read receipt only proves its hold's provenance. Its
            // identity is spent: a read is never answered by replay, and the
            // original receipt is never overwritten.
            return Ok(
                if !reading && admission::matches_fingerprint(&previous.fingerprint, &fingerprint) {
                    previous.receipt
                } else {
                    receipt(Err(Refusal::Conflict))
                },
            );
        }
        if id.expires_at <= position {
            return Ok(receipt(Err(Refusal::Expired)));
        }
        if self.successor.is_some() {
            return Ok(receipt(Err(Refusal::CohortSealed)));
        }
        if id.expires_at - position > self.limits.retry_positions {
            return Ok(receipt(Err(Refusal::Invalid)));
        }
        let receipt = receipt(self.decide(principal, id, fingerprint, request.command));
        if reading && receipt.outcome.is_err() {
            // A refused read holds nothing and is never replayed, so it leaves
            // no state behind. Only an admitted read retains its receipt, as
            // the provenance of its hold.
            return Ok(receipt);
        }
        self.outcomes.insert(
            key,
            RetainedOutcome {
                fingerprint,
                receipt,
            },
        );
        self.expiry.insert((id.expires_at, key), ());
        Ok(receipt)
    }

    fn writer(&self, principal: Principal, grant: Grant) -> Result<(), Refusal> {
        if principal != Principal::Worker(grant.enrollment) {
            return Err(Refusal::Unauthorized);
        }
        if self.grant != Some(grant) {
            return Err(Refusal::Stale);
        }
        Ok(())
    }

    fn cut(&self, next_lsn: u64) -> Option<Cut> {
        if next_lsn == self.floor.next_lsn {
            return Some(self.floor);
        }
        self.record(next_lsn.checked_sub(1)?)
            .map(|record| record.result.cut)
    }

    fn protect(
        &mut self,
        origin: Principal,
        id: RequestId,
        owner: Enrollment,
        through: Cut,
    ) -> Result<Hold, Refusal> {
        self.protect_range(origin, id, owner, self.checkpoint.cut, through)
    }

    fn protect_range(
        &mut self,
        origin: Principal,
        id: RequestId,
        owner: Enrollment,
        start: Cut,
        through: Cut,
    ) -> Result<Hold, Refusal> {
        if through.next_lsn < start.next_lsn
            || self.cut(start.next_lsn) != Some(start)
            || self.cut(through.next_lsn) != Some(through)
        {
            return Err(Refusal::Unavailable);
        }
        self.admit_hold(
            origin,
            id,
            owner,
            self.checkpoint,
            start,
            through,
            HoldKind::Ordinary,
        )
    }

    fn admit_hold(
        &mut self,
        origin: Principal,
        id: RequestId,
        owner: Enrollment,
        checkpoint: Checkpoint,
        start: Cut,
        through: Cut,
        kind: HoldKind,
    ) -> Result<Hold, Refusal> {
        if self.holds.contains_key(&id) {
            return Err(Refusal::Conflict);
        }
        let ordinary = self
            .holds
            .values()
            .filter(|entry| entry.kind == HoldKind::Ordinary)
            .count();
        if kind == HoldKind::Ordinary && ordinary >= self.limits.replay_holds
            || kind != HoldKind::Ordinary && self.holds.len() - ordinary >= ACTIVATION_HOLD_SLOTS
        {
            return Err(Refusal::Capacity);
        }
        let hold = Hold {
            id,
            owner,
            admitted_at: self.position,
            checkpoint,
            start,
            through,
        };
        self.holds.insert(id, HeldAdmission { hold, origin, kind });
        Ok(hold)
    }

    fn decide(
        &mut self,
        principal: Principal,
        id: RequestId,
        request_fingerprint: Fingerprint,
        command: Command,
    ) -> Result<Outcome, Refusal> {
        match command {
            Command::Enroll { worker, expected } => {
                if principal != Principal::Administrator {
                    return Err(Refusal::Unauthorized);
                }
                if worker.is_nil() {
                    return Err(Refusal::Invalid);
                }
                if self.roster.get(&worker).copied() != expected {
                    return Err(Refusal::Stale);
                }
                if expected.is_none() && self.roster.len() >= self.limits.enrolled_workers {
                    return Err(Refusal::Capacity);
                }
                let serial = self
                    .enrollment_serial
                    .checked_add(1)
                    .ok_or(Refusal::Capacity)?;
                let enrollment = Enrollment { worker, serial };
                self.enrollment_serial = serial;
                self.roster.insert(worker, enrollment);
                if self
                    .grant
                    .is_some_and(|grant| grant.enrollment.worker == worker)
                {
                    self.grant = None;
                }
                self.prune_leases();
                Ok(Outcome::Enrolled(enrollment))
            }
            Command::Withdraw { enrollment } => {
                if principal != Principal::Administrator {
                    return Err(Refusal::Unauthorized);
                }
                if self.roster.get(&enrollment.worker) != Some(&enrollment) {
                    return Err(Refusal::Stale);
                }
                self.roster.remove(&enrollment.worker);
                if self
                    .grant
                    .is_some_and(|grant| grant.enrollment == enrollment)
                {
                    self.grant = None;
                }
                self.prune_leases();
                Ok(Outcome::Withdrawn)
            }
            Command::Grant {
                expected,
                candidate,
            } => {
                if principal != Principal::Administrator
                    && principal != Principal::Worker(candidate)
                {
                    return Err(Refusal::Unauthorized);
                }
                if self.writer_state() != expected
                    || self.roster.get(&candidate.worker) != Some(&candidate)
                {
                    return Err(Refusal::Stale);
                }
                let epoch = expected.epoch.checked_add(1).ok_or(Refusal::Capacity)?;
                let grant = Grant {
                    enrollment: candidate,
                    epoch,
                };
                let recovery = self.admit_hold(
                    principal,
                    id,
                    candidate,
                    self.checkpoint,
                    self.checkpoint.cut,
                    self.head,
                    HoldKind::Recovery,
                )?;
                self.writer_epoch = epoch;
                self.grant = Some(grant);
                Ok(Outcome::Granted { grant, recovery })
            }
            Command::Append {
                class,
                grant,
                expected_next,
                timestamp,
                payload,
            } => {
                self.writer(principal, grant)?;
                if self.head.next_lsn != expected_next {
                    return Err(Refusal::Stale);
                }
                let next_lsn = expected_next.checked_add(1).ok_or(Refusal::Capacity)?;
                let length = u64::try_from(payload.len()).map_err(|_| Refusal::Capacity)?;
                // Charge the fixed record identity too, including an empty payload.
                let bytes = length
                    .checked_add(APPEND_RECORD_CHARGE_BYTES)
                    .ok_or(Refusal::Capacity)?;
                let (byte_start, byte_end) = match class {
                    AppendClass::Data => (
                        self.spent,
                        admission::debit(self.spent, bytes, self.window.bytes)
                            .ok_or(Refusal::Capacity)?,
                    ),
                    AppendClass::Maintenance => (0, bytes),
                };
                let retained_bytes = match class {
                    AppendClass::Data => {
                        admission::debit(self.retained_bytes, bytes, self.ordinary_capacity())
                    }
                    AppendClass::Maintenance => admission::debit(
                        self.maintenance_retained,
                        bytes,
                        self.limits.maintenance_bytes,
                    ),
                }
                .ok_or(Refusal::Capacity)?;
                let history = append_fingerprint(self.head, class, grant, id, timestamp, &payload);
                let cut = Cut { next_lsn, history };
                let result = AppendResult {
                    class,
                    position: self.position,
                    lsn: expected_next,
                    cut,
                    window: self.window,
                    byte_start,
                    byte_end,
                };
                self.records.push_back(Record {
                    result,
                    grant,
                    timestamp,
                    payload,
                    request: id,
                    request_fingerprint,
                });
                self.head = cut;
                match class {
                    AppendClass::Data => {
                        self.spent = byte_end;
                        self.retained_bytes = retained_bytes;
                    }
                    AppendClass::Maintenance => self.maintenance_retained = retained_bytes,
                };
                Ok(Outcome::Appended(result))
            }
            Command::Barrier { grant } => {
                self.writer(principal, grant)?;
                // The head never moves back under one grant, so a later read
                // observes at or after every earlier read's cut.
                let read = self.protect(principal, id, grant.enrollment, self.head)?;
                Ok(Outcome::Barrier { grant, read })
            }
            Command::PrepareCheckpoint { preparation } => {
                Self::custodian(principal)?;
                if let Some(pending) = self.preparing {
                    return if pending == preparation {
                        Ok(Outcome::CheckpointPrepared(pending))
                    } else {
                        Err(Refusal::Conflict)
                    };
                }
                if preparation.checkpoint.next_lsn <= self.checkpoint.cut.next_lsn
                    || self.cut(preparation.checkpoint.next_lsn) != Some(preparation.checkpoint)
                    || preparation.custody.allocation.is_nil()
                    || preparation.custody.provider == [0; 32]
                    || Some(preparation.custody.revision)
                        != self.checkpoint.custody.revision.checked_add(1)
                    || preparation.usable_bytes == 0
                    || preparation.root == [0; 32]
                    || !self.checkpoint_open(preparation.base)
                {
                    return Err(Refusal::Invalid);
                }
                // Preserve headroom to publish alongside previous pinned roots.
                if self.old_roots.len() >= self.limits.replay_holds {
                    return Err(Refusal::Capacity);
                }
                self.preparing = Some(preparation);
                Ok(Outcome::CheckpointPrepared(preparation))
            }
            Command::Publish { checkpoint } => {
                Self::custodian(principal)?;
                if checkpoint == self.checkpoint {
                    return Ok(Outcome::Published(checkpoint));
                }
                let pending = self.preparing.ok_or(Refusal::Unavailable)?;
                if pending.checkpoint != checkpoint.cut
                    || pending.root != checkpoint.root
                    || pending.custody != checkpoint.custody
                    || checkpoint.manifest == [0; 32]
                    || self.cut(checkpoint.cut.next_lsn) != Some(checkpoint.cut)
                {
                    return Err(Refusal::Conflict);
                }
                if self.checkpoint.manifest != [0; 32] {
                    let old = self.checkpoint;
                    self.old_roots.insert(
                        old.custody.revision,
                        RetainedCheckpoint {
                            checkpoint: old,
                            closed: false,
                        },
                    );
                }
                self.preparing = None;
                self.checkpoint = checkpoint;
                Ok(Outcome::Published(checkpoint))
            }
            Command::CloseCheckpoint { checkpoint } => {
                if principal != Principal::Custodian {
                    return Err(Refusal::Unauthorized);
                }
                let entry = self
                    .old_roots
                    .get_mut(&checkpoint.custody.revision)
                    .filter(|entry| entry.checkpoint == checkpoint)
                    .ok_or(Refusal::Stale)?;
                if self
                    .preparing
                    .is_some_and(|pending| pending.base == checkpoint)
                    || self
                        .holds
                        .values()
                        .any(|entry| entry.hold.checkpoint == checkpoint)
                {
                    return Err(Refusal::Unavailable);
                }
                entry.closed = true;
                Ok(Outcome::CheckpointClosed(checkpoint))
            }
            Command::SettleCheckpoint {
                checkpoint,
                disposition,
            } => {
                if principal != Principal::Custodian {
                    return Err(Refusal::Unauthorized);
                }
                if disposition == [0; 32]
                    || self
                        .old_roots
                        .get(&checkpoint.custody.revision)
                        .is_none_or(|entry| entry.checkpoint != checkpoint || !entry.closed)
                {
                    return Err(Refusal::Stale);
                }
                self.old_roots.remove(&checkpoint.custody.revision);
                Ok(Outcome::CheckpointSettled(checkpoint))
            }
            Command::DisposeWorker {
                enrollment,
                disposition,
            } => {
                if principal != Principal::Administrator {
                    return Err(Refusal::Unauthorized);
                }
                if disposition == [0; 32]
                    || enrollment.serial == 0
                    || enrollment.serial > self.enrollment_serial
                    || self.roster.get(&enrollment.worker) == Some(&enrollment)
                {
                    return Err(Refusal::Stale);
                }
                self.dispose(enrollment);
                Ok(Outcome::WorkerDisposed(enrollment))
            }
            Command::DisposeExpired { enrollment } => {
                if principal != Principal::Administrator && principal != Principal::Custodian {
                    return Err(Refusal::Unauthorized);
                }
                if enrollment.serial == 0
                    || enrollment.serial > self.enrollment_serial
                    || self.roster.get(&enrollment.worker) == Some(&enrollment)
                {
                    return Err(Refusal::Stale);
                }
                // A worker that was never leased never served, so it is
                // disposable as soon as it is withdrawn.
                if let Some(lease_end) = self.leases.get(&enrollment) {
                    let disposable = lease_end
                        .checked_add(self.limits.clock_drift)
                        .ok_or(Refusal::Capacity)?;
                    if self.time < disposable {
                        return Err(Refusal::Unavailable);
                    }
                }
                self.dispose(enrollment);
                Ok(Outcome::WorkerDisposed(enrollment))
            }
            Command::Lease { grant } => {
                self.writer(principal, grant)?;
                if self.roster.get(&grant.enrollment.worker) != Some(&grant.enrollment) {
                    return Err(Refusal::Stale);
                }
                let lease_end = self
                    .time
                    .checked_add(self.limits.serving_lease)
                    .ok_or(Refusal::Capacity)?;
                let last = self.leases.entry(grant.enrollment).or_default();
                *last = (*last).max(lease_end);
                Ok(Outcome::Leased {
                    grant,
                    issued_at: self.time,
                    lease_end,
                })
            }
            Command::FundWindow { window } => {
                Self::custodian(principal)?;
                if window.allocation.is_nil()
                    || window.bytes == 0
                    || Some(window.serial) != self.window.serial.checked_add(1)
                {
                    return Err(Refusal::Invalid);
                }
                admission::debit(self.retained_bytes, window.bytes, self.ordinary_capacity())
                    .ok_or(Refusal::Capacity)?;
                self.window = window;
                self.spent = 0;
                Ok(Outcome::WindowFunded(window))
            }
            Command::Protect { grant, through } => {
                self.writer(principal, grant)?;
                let hold = self.protect(principal, id, grant.enrollment, through)?;
                Ok(Outcome::Protected(hold))
            }
            Command::ProtectRange {
                grant,
                from,
                through,
            } => {
                let Principal::Worker(enrollment) = principal else {
                    return Err(Refusal::Unauthorized);
                };
                if self.roster.get(&enrollment.worker) != Some(&enrollment)
                    || self.grant != Some(grant)
                {
                    return Err(Refusal::Stale);
                }
                let start = self.cut(from).ok_or(Refusal::Unavailable)?;
                let through = self.cut(through).ok_or(Refusal::Unavailable)?;
                let hold = self.protect_range(principal, id, enrollment, start, through)?;
                Ok(Outcome::Protected(hold))
            }
            Command::ProtectRoot { source } => {
                if principal != Principal::Worker(source.owner) {
                    return Err(Refusal::Unauthorized);
                }
                if self
                    .holds
                    .get(&source.id)
                    .is_none_or(|entry| entry.hold != source || entry.kind != HoldKind::Recovery)
                {
                    return Err(Refusal::Unavailable);
                }
                let kind = HoldKind::Root(source.id);
                if self.holds.values().any(|entry| entry.kind == kind) {
                    return Err(Refusal::Conflict);
                }
                let checkpoint = source.checkpoint;
                let hold = self.admit_hold(
                    principal,
                    id,
                    source.owner,
                    checkpoint,
                    checkpoint.cut,
                    checkpoint.cut,
                    kind,
                )?;
                Ok(Outcome::Protected(hold))
            }
            Command::Vacate { grant } => {
                self.writer(principal, grant)?;
                self.grant = None;
                Ok(Outcome::Vacated)
            }
            Command::SealCohort {
                expected,
                successor,
            } => {
                if principal != Principal::Administrator {
                    return Err(Refusal::Unauthorized);
                }
                if expected != self.voter_scope || successor == [0; 32] || successor == expected {
                    return Err(Refusal::Invalid);
                }
                self.successor = Some(successor);
                Ok(Outcome::CohortSealed(successor))
            }
            Command::Release { hold } => {
                if principal != Principal::Worker(hold.owner) {
                    return Err(Refusal::Unauthorized);
                }
                let entry = self
                    .holds
                    .get(&hold.id)
                    .filter(|entry| entry.hold == hold)
                    .ok_or(Refusal::Stale)?;
                if hold.id.expires_at <= self.position {
                    self.outcomes.remove(&(entry.origin, hold.id));
                }
                self.holds.remove(&hold.id);
                self.prune_leases();
                Ok(Outcome::Released)
            }
            Command::ReleaseRead { read } => {
                if !matches!(principal, Principal::Worker(_)) {
                    return Err(Refusal::Unauthorized);
                }
                let key = (principal, read);
                let admitted_read = self.outcomes.get(&key).map(|retained| {
                    matches!(retained.receipt.outcome, Ok(Outcome::Barrier { .. }))
                });
                let Some(entry) = self.holds.get(&read).copied() else {
                    // Nothing is held under this identity. It may still name
                    // this principal's mutation, which is never a read.
                    return match admitted_read {
                        Some(false) => Err(Refusal::Conflict),
                        _ => Ok(Outcome::Released),
                    };
                };
                if entry.origin != principal {
                    return Err(Refusal::Unauthorized);
                }
                if entry.kind != HoldKind::Ordinary || admitted_read != Some(true) {
                    return Err(Refusal::Conflict);
                }
                // As with Release, a receipt still inside its retry window stays
                // on the expiry schedule. It keeps a delayed copy of the
                // original barrier from admitting a second hold under the same
                // identity; past its window it leaves with the hold.
                if read.expires_at <= self.position {
                    self.outcomes.remove(&key);
                }
                self.holds.remove(&read);
                self.prune_leases();
                Ok(Outcome::Released)
            }
            Command::Trim { selected, through } => {
                Self::custodian(principal)?;
                if selected != self.checkpoint {
                    return Err(Refusal::Stale);
                }
                if through.next_lsn > selected.cut.next_lsn
                    || self.cut(through.next_lsn) != Some(through)
                {
                    return Err(Refusal::Invalid);
                }
                if self.holds.values().map(|entry| entry.hold).any(|hold| {
                    admission::pins_suffix(
                        hold.start.next_lsn,
                        hold.through.next_lsn,
                        through.next_lsn,
                    )
                }) {
                    return Err(Refusal::Unavailable);
                }
                let trim = usize::try_from(through.next_lsn - self.floor.next_lsn)
                    .map_err(|_| Refusal::Invalid)?;
                let mut result = TrimResult {
                    from: self.floor,
                    through,
                    ordinary_bytes: 0,
                    maintenance_bytes: 0,
                };
                for record in self.records.drain(..trim) {
                    let charge = record.result.byte_end - record.result.byte_start;
                    match record.result.class {
                        AppendClass::Data => result.ordinary_bytes += charge,
                        AppendClass::Maintenance => result.maintenance_bytes += charge,
                    }
                }
                self.retained_bytes -= result.ordinary_bytes;
                self.maintenance_retained -= result.maintenance_bytes;
                self.floor = through;
                Ok(Outcome::Trimmed(result))
            }
        }
    }

    /// Removes every hold the enrollment owns, with any receipt that was
    /// retained only as that hold's provenance.
    fn dispose(&mut self, enrollment: Enrollment) {
        let retired = self
            .holds
            .values()
            .filter(|entry| entry.hold.owner == enrollment)
            .copied()
            .collect::<Vec<_>>();
        for entry in retired {
            self.holds.remove(&entry.hold.id);
            if entry.hold.id.expires_at <= self.position {
                self.outcomes.remove(&(entry.origin, entry.hold.id));
            }
        }
        self.prune_leases();
    }

    /// Keeps a lease end only while its enrollment is enrolled or owns a hold.
    fn prune_leases(&mut self) {
        let roster = &self.roster;
        let holds = &self.holds;
        self.leases.retain(|enrollment, _| {
            roster.get(&enrollment.worker) == Some(enrollment)
                || holds.values().any(|entry| entry.hold.owner == *enrollment)
        });
    }

    fn checkpoint_open(&self, checkpoint: Checkpoint) -> bool {
        checkpoint == self.checkpoint
            || self
                .old_roots
                .get(&checkpoint.custody.revision)
                .is_some_and(|entry| !entry.closed && entry.checkpoint == checkpoint)
            || (checkpoint.manifest == [0; 32]
                && checkpoint.root == [0; 32]
                && checkpoint.cut.next_lsn == 0
                && checkpoint.custody.revision == 1
                && checkpoint.custody.provider == [0; 32]
                && self
                    .holds
                    .values()
                    .any(|entry| entry.hold.checkpoint == checkpoint))
    }

    fn next_checkpoint_retirement(&self) -> Option<RetainedCheckpoint> {
        self.old_roots
            .values()
            .find(|entry| {
                let checkpoint = entry.checkpoint;
                self.preparing
                    .is_none_or(|pending| pending.base != checkpoint)
                    && !self
                        .holds
                        .values()
                        .any(|held| held.hold.checkpoint == checkpoint)
            })
            .copied()
    }

    fn custodian(principal: Principal) -> Result<(), Refusal> {
        if principal == Principal::Custodian {
            Ok(())
        } else {
            Err(Refusal::Unauthorized)
        }
    }
}

fn add_enrollment(hash: &mut Sha256, enrollment: Enrollment) {
    hash.update(enrollment.worker.as_bytes());
    hash.update(enrollment.serial.to_be_bytes());
}

fn add_grant(hash: &mut Sha256, grant: Grant) {
    add_enrollment(hash, grant.enrollment);
    hash.update(grant.epoch.to_be_bytes());
}

fn add_cut(hash: &mut Sha256, cut: Cut) {
    hash.update(cut.next_lsn.to_be_bytes());
    hash.update(cut.history);
}

fn append_fingerprint(
    previous: Cut,
    class: AppendClass,
    grant: Grant,
    request: RequestId,
    timestamp: i64,
    payload: &Bytes,
) -> Fingerprint {
    let mut hash = Sha256::new();
    hash.update(b"logkeeper.applied-append.v2");
    hash.update([class.tag()]);
    add_cut(&mut hash, previous);
    add_grant(&mut hash, grant);
    hash.update(request.nonce.as_bytes());
    hash.update(request.expires_at.to_be_bytes());
    hash.update(timestamp.to_be_bytes());
    hash.update(payload);
    hash.finalize().into()
}

fn fingerprint(request: &Request) -> Fingerprint {
    let mut hash = Sha256::new();
    hash.update(b"logkeeper.ordered-request.v1");
    hash.update(request.encode());
    hash.finalize().into()
}

fn extend_command_history(
    previous: Fingerprint,
    position: u64,
    time: u64,
    request: Fingerprint,
) -> Fingerprint {
    let mut hash = Sha256::new();
    hash.update(b"logkeeper.ordered-history.v2");
    hash.update(previous);
    hash.update(position.to_be_bytes());
    hash.update(time.to_be_bytes());
    hash.update(request);
    hash.finalize().into()
}
