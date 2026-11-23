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
mod receipt;
pub mod replication;
pub mod service;
mod writer;

use bytes::Bytes;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use uuid::Uuid;

pub type Fingerprint = [u8; 32];

/// Fixed stream charge for each record's identity and framing. Replica media
/// also budget for staging and their own metadata.
pub const APPEND_RECORD_CHARGE_BYTES: u64 = 217;
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
    pub key_generation: u64,
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
    pub erasure: bool,
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

/// An opaque immutable object name. Callers must use the same name for all
/// references to a physical object, including references derived during replay.
pub type ObjectName = Fingerprint;

pub const MAX_OBJECT_REFERENCES: usize = 16_384;
const MAX_OBJECT_CONTROL_BYTES: usize = 2 << 20;
const WITHDRAWAL_BYTES: usize = 80;

/// The provider version is bound to the receipt. The name remains fenced even
/// if a provider creates another version at the same key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ObjectWithdrawal {
    pub name: ObjectName,
    pub version: Fingerprint,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ObjectFence {
    pub object: ObjectWithdrawal,
    pub position: u64,
    pub time: u64,
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
    /// Select the prepared clean checkpoint, fence old admissions, and install
    /// its successor key generation in one custody decision.
    PublishAndRotate {
        grant: Grant,
        checkpoint: Checkpoint,
    },
    Append {
        class: AppendClass,
        grant: Grant,
        expected_next: u64,
        timestamp: i64,
        payload: Bytes,
        /// Complete, sorted and unique exact object names. None is a legacy opaque append.
        references: Option<Vec<ObjectName>>,
    },
    /// A fresh read. Each admission protects its own basis at the current
    /// head; a retry is a new admission and never replays an earlier read.
    Barrier,
    PrepareCheckpoint {
        preparation: CheckpointPreparation,
        references: Option<Vec<ObjectName>>,
    },
    WithdrawObject {
        object: ObjectWithdrawal,
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
    Barrier { read: Hold },
    Published(Checkpoint),
    CheckpointPrepared(CheckpointPreparation),
    ObjectWithdrawn(ObjectFence),
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

pub use writer::Refusal;

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
    read: Hold,
}

impl BarrierClaim {
    pub fn placement(self) -> Placement {
        self.placement
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
    pub references: Option<Vec<ObjectName>>,
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
    key_generation: u64,
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
    erasure_floor: u64,
    head: Cut,
    checkpoint: Checkpoint,
    preparing: Option<CheckpointPreparation>,
    old_roots: BTreeMap<u64, RetainedCheckpoint>,
    records: VecDeque<Record>,
    object_control_bytes: usize,
    root_references: BTreeMap<u64, Vec<ObjectName>>,
    object_fences: BTreeMap<ObjectName, ObjectFence>,
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
            key_generation: 1,
            enrollment_serial: 0,
            roster: BTreeMap::new(),
            grant: None,
            leases: BTreeMap::new(),
            window,
            spent: 0,
            retained_bytes: 0,
            maintenance_retained: 0,
            floor: checkpoint.cut,
            erasure_floor: checkpoint.cut.next_lsn,
            head: checkpoint.cut,
            checkpoint,
            preparing: None,
            old_roots: BTreeMap::new(),
            records: VecDeque::new(),
            object_control_bytes: MAX_OBJECT_CONTROL_BYTES,
            root_references: BTreeMap::new(),
            object_fences: BTreeMap::new(),
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
    pub fn erasure_floor(&self) -> u64 {
        self.erasure_floor
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
            ..
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
        if matches!(request.command, Command::Barrier) {
            return None;
        }
        let previous = self.outcomes.get(&(request.principal, request.id))?;
        if request.placement != self.placement {
            return None;
        }
        receipt::replay_mutation(
            &previous.fingerprint,
            &fingerprint(request),
            previous.receipt,
        )
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
        let reading = matches!(&request.command, Command::Barrier);
        if let Some(previous) = self.outcomes.get(&key) {
            // A retained read receipt only proves its hold's provenance. Its
            // identity is spent: a read is never answered by replay, and the
            // original receipt is never overwritten.
            return Ok(receipt::replay(
                reading,
                &previous.fingerprint,
                &fingerprint,
                previous.receipt,
            )
            .unwrap_or_else(|| receipt(Err(Refusal::Conflict))));
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
        if !receipt::record_after_apply(reading, &receipt.outcome) {
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
        writer::authorize(
            principal == Principal::Worker(grant.enrollment),
            self.grant == Some(grant),
        )
    }

    fn install_grant(
        &mut self,
        principal: Principal,
        id: RequestId,
        enrollment: Enrollment,
        key_generation: u64,
    ) -> Result<Outcome, Refusal> {
        self.install_grant_at(principal, id, enrollment, key_generation, self.checkpoint)
    }

    fn install_grant_at(
        &mut self,
        principal: Principal,
        id: RequestId,
        enrollment: Enrollment,
        key_generation: u64,
        checkpoint: Checkpoint,
    ) -> Result<Outcome, Refusal> {
        let epoch = writer::next_epoch(self.writer_epoch)?;
        let grant = Grant {
            enrollment,
            epoch,
            key_generation,
        };
        let recovery = self.admit_hold(
            principal,
            id,
            enrollment,
            checkpoint,
            checkpoint.cut,
            self.head,
            HoldKind::Recovery,
        )?;
        self.writer_epoch = epoch;
        self.key_generation = key_generation;
        self.grant = Some(grant);
        Ok(Outcome::Granted { grant, recovery })
    }

    fn prepared_checkpoint(
        &self,
        checkpoint: Checkpoint,
    ) -> Result<CheckpointPreparation, Refusal> {
        let pending = self.preparing.ok_or(Refusal::Unavailable)?;
        if pending.checkpoint != checkpoint.cut
            || pending.root != checkpoint.root
            || pending.custody != checkpoint.custody
            || checkpoint.manifest == [0; 32]
            || self.cut(checkpoint.cut.next_lsn) != Some(checkpoint.cut)
        {
            return Err(Refusal::Conflict);
        }
        Ok(pending)
    }

    fn publish_checkpoint(&mut self, checkpoint: Checkpoint, closes_history: bool) {
        if self.checkpoint.manifest != [0; 32] {
            let old = self.checkpoint;
            self.old_roots.insert(
                old.custody.revision,
                RetainedCheckpoint {
                    checkpoint: old,
                    closed: closes_history,
                },
            );
        }
        if closes_history {
            self.erasure_floor = checkpoint.cut.next_lsn;
            for entry in self.old_roots.values_mut() {
                entry.closed = true;
            }
        }
        self.preparing = None;
        self.checkpoint = checkpoint;
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
        if start.next_lsn < self.erasure_floor
            || through.next_lsn < start.next_lsn
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
                let replaced_holder = self
                    .grant
                    .is_some_and(|grant| grant.enrollment.worker == worker);
                writer::withdraw(&mut self.grant, replaced_holder);
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
                let withdrew_holder = self
                    .grant
                    .is_some_and(|grant| grant.enrollment == enrollment);
                writer::withdraw(&mut self.grant, withdrew_holder);
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
                self.install_grant(principal, id, candidate, self.key_generation)
            }
            Command::PublishAndRotate { grant, checkpoint } => {
                Self::custodian(principal)?;
                if self.grant != Some(grant)
                    || self.head != checkpoint.cut
                    || self.checkpoint == checkpoint
                {
                    return Err(Refusal::Stale);
                }
                let pending = self.prepared_checkpoint(checkpoint)?;
                if !pending.erasure || pending.source != grant || pending.base != self.checkpoint {
                    return Err(Refusal::Stale);
                }
                let next = grant
                    .key_generation
                    .checked_add(1)
                    .ok_or(Refusal::Capacity)?;
                let outcome =
                    self.install_grant_at(principal, id, grant.enrollment, next, checkpoint)?;
                self.publish_checkpoint(checkpoint, true);
                Ok(outcome)
            }
            Command::Append {
                class,
                grant,
                expected_next,
                timestamp,
                payload,
                references,
            } => {
                self.writer(principal, grant)?;
                let next_lsn = writer::append_next(self.head.next_lsn, expected_next)?;
                self.admit_object_references(references.as_deref())?;
                let bytes = record_charge(payload.len(), references.as_deref())?;
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
                let history = append_fingerprint(
                    self.head,
                    class,
                    grant,
                    id,
                    timestamp,
                    &payload,
                    references.as_deref(),
                );
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
                    references,
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
            Command::Barrier => {
                let Principal::Worker(reader) = principal else {
                    return Err(Refusal::Unauthorized);
                };
                if self.roster.get(&reader.worker) != Some(&reader) {
                    return Err(Refusal::Stale);
                }
                let read = self.protect(principal, id, reader, self.head)?;
                Ok(Outcome::Barrier { read })
            }
            Command::WithdrawObject { object } => {
                Self::custodian(principal)?;
                self.withdraw_object(object).map(Outcome::ObjectWithdrawn)
            }
            Command::PrepareCheckpoint {
                preparation,
                references,
            } => {
                Self::custodian(principal)?;
                let revision = preparation.custody.revision;
                if let Some(pending) = self.preparing {
                    return if pending == preparation
                        && self.root_references.get(&revision) == references.as_ref()
                    {
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
                    || (preparation.erasure
                        && (self.grant != Some(preparation.source)
                            || preparation.base != self.checkpoint
                            || preparation.checkpoint != self.head))
                {
                    return Err(Refusal::Invalid);
                }
                // Preserve headroom to publish alongside previous pinned roots.
                if self.old_roots.len() >= self.limits.replay_holds {
                    return Err(Refusal::Capacity);
                }
                self.admit_object_references(references.as_deref())?;
                if let Some(references) = references {
                    self.charge_object_control(12 + 32 * references.len())?;
                    self.root_references.insert(revision, references);
                }
                self.preparing = Some(preparation);
                Ok(Outcome::CheckpointPrepared(preparation))
            }
            Command::Publish { checkpoint } => {
                Self::custodian(principal)?;
                if checkpoint == self.checkpoint {
                    return Ok(Outcome::Published(checkpoint));
                }
                if self.prepared_checkpoint(checkpoint)?.erasure {
                    return Err(Refusal::Conflict);
                }
                self.publish_checkpoint(checkpoint, false);
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
                self.old_roots.remove(&checkpoint.custody.revision);
                self.root_references.remove(&checkpoint.custody.revision);
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
                let eligible_at = self
                    .expiry_disposal_time(enrollment)
                    .ok_or(Refusal::Capacity)?;
                if self.time < eligible_at {
                    return Err(Refusal::Unavailable);
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
            Command::ProtectRange { from, through } => {
                let Principal::Worker(enrollment) = principal else {
                    return Err(Refusal::Unauthorized);
                };
                if self.roster.get(&enrollment.worker) != Some(&enrollment) {
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
                if !self.checkpoint_open(source.checkpoint) {
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

    fn admit_object_references(&self, references: Option<&[ObjectName]>) -> Result<(), Refusal> {
        match references {
            Some(names) if !valid_object_names(names) => Err(Refusal::Invalid),
            Some(names)
                if names
                    .iter()
                    .any(|name| self.object_fences.contains_key(name)) =>
            {
                Err(Refusal::Conflict)
            }
            None if !self.object_fences.is_empty() => Err(Refusal::Unavailable),
            _ => Ok(()),
        }
    }

    fn charge_object_control(&self, charge: usize) -> Result<(), Refusal> {
        let used = self.object_fences.len() * WITHDRAWAL_BYTES
            + self
                .root_references
                .values()
                .map(|names| 12 + 32 * names.len())
                .sum::<usize>();
        if used.saturating_add(charge) > self.object_control_bytes {
            return Err(Refusal::Capacity);
        }
        Ok(())
    }

    fn has_complete_object_references(&self) -> bool {
        let known = |checkpoint: Checkpoint| {
            (checkpoint.manifest == [0; 32] && checkpoint.root == [0; 32])
                || self
                    .root_references
                    .contains_key(&checkpoint.custody.revision)
        };
        known(self.checkpoint)
            && self
                .holds
                .values()
                .all(|entry| known(entry.hold.checkpoint))
            && self
                .old_roots
                .values()
                .all(|entry| entry.closed || known(entry.checkpoint))
            && self
                .preparing
                .is_none_or(|prep| self.root_references.contains_key(&prep.custody.revision))
            && self
                .records
                .iter()
                .all(|record| record.references.is_some())
    }

    fn withdraw_object(&mut self, object: ObjectWithdrawal) -> Result<ObjectFence, Refusal> {
        if object.name == [0; 32] || object.version == [0; 32] {
            return Err(Refusal::Invalid);
        }
        if let Some(fence) = self.object_fences.get(&object.name).copied() {
            return if fence.object == object {
                Ok(fence)
            } else {
                Err(Refusal::Conflict)
            };
        }
        if !self.has_complete_object_references() {
            return Err(Refusal::Unavailable);
        }
        if self
            .root_references
            .values()
            .chain(
                self.records
                    .iter()
                    .filter_map(|record| record.references.as_ref()),
            )
            .any(|names| names.binary_search(&object.name).is_ok())
        {
            return Err(Refusal::Conflict);
        }
        self.charge_object_control(WITHDRAWAL_BYTES)?;
        let fence = ObjectFence {
            object,
            position: self.position,
            time: self.time,
        };
        self.object_fences.insert(object.name, fence);
        Ok(fence)
    }

    fn withdrawn_hold_owners(
        &self,
        after: Option<Enrollment>,
        limit: usize,
    ) -> impl Iterator<Item = Enrollment> {
        let mut owners = BTreeSet::new();
        for entry in self.holds.values() {
            let owner = entry.hold.owner;
            if after.is_some_and(|cursor| owner <= cursor)
                || self.roster.get(&owner.worker) == Some(&owner)
            {
                continue;
            }
            owners.insert(owner);
            if owners.len() > limit {
                owners.pop_last();
            }
        }
        owners.into_iter()
    }

    fn expiry_disposal_time(&self, enrollment: Enrollment) -> Option<u64> {
        match self.leases.get(&enrollment) {
            Some(lease_end) => lease_end.checked_add(self.limits.clock_drift),
            None => Some(0),
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

    fn checkpoint_retained(&self, checkpoint: Checkpoint) -> bool {
        checkpoint == self.checkpoint
            || self
                .old_roots
                .get(&checkpoint.custody.revision)
                .is_some_and(|entry| entry.checkpoint == checkpoint)
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

    fn checkpoint_open(&self, checkpoint: Checkpoint) -> bool {
        checkpoint.cut.next_lsn >= self.erasure_floor
            && self.checkpoint_retained(checkpoint)
            && !self
                .old_roots
                .get(&checkpoint.custody.revision)
                .is_some_and(|entry| entry.closed)
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
    hash.update(grant.key_generation.to_be_bytes());
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
    references: Option<&[ObjectName]>,
) -> Fingerprint {
    let mut hash = Sha256::new();
    if let Some(names) = references {
        hash.update(b"logkeeper.applied-append-with-references.v1");
        hash.update((names.len() as u32).to_be_bytes());
        for name in names {
            hash.update(name);
        }
    } else {
        hash.update(b"logkeeper.applied-append.v3");
    }
    hash.update([class.tag()]);
    add_cut(&mut hash, previous);
    add_grant(&mut hash, grant);
    hash.update(request.nonce.as_bytes());
    hash.update(request.expires_at.to_be_bytes());
    hash.update(timestamp.to_be_bytes());
    hash.update(payload);
    hash.finalize().into()
}

fn valid_object_names(names: &[ObjectName]) -> bool {
    names.len() <= MAX_OBJECT_REFERENCES
        && names.first().is_none_or(|name| *name != [0; 32])
        && names.windows(2).all(|pair| pair[0] < pair[1])
}

fn record_charge(payload_len: usize, references: Option<&[ObjectName]>) -> Result<u64, Refusal> {
    let overhead = references.map_or(0, |names| 4 + 32 * names.len() as u64);
    (payload_len as u64)
        .checked_add(APPEND_RECORD_CHARGE_BYTES + overhead)
        .ok_or(Refusal::Capacity)
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
