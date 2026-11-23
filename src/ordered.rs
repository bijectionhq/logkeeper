//! Application of the ordered commands owned by an installed journal group.
//!
//! The replication owner supplies one authenticated command at each chosen
//! position. A command's position and the stream's data frontier are separate.

mod codec;
#[cfg(feature = "ordered-daemon")]
pub mod daemon;
pub mod replication;
pub mod service;

use bytes::Bytes;
use sha2::{Digest, Sha256};
use std::cmp::Ordering;
use std::collections::{BTreeMap, VecDeque};
use std::num::NonZeroU64;
use uuid::Uuid;

pub type Fingerprint = [u8; 32];

// The stream's paid byte cursor includes a fixed charge for each record's
// identity and framing. The physical store accounts for its own replicas,
// staging, and metadata in addition to these stream charges.
const APPEND_RECORD_CHARGE_BYTES: u64 = 208;

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
        grant: Grant,
        expected_next: u64,
        timestamp: i64,
        payload: Bytes,
    },
    Barrier {
        grant: Grant,
        nonce: NonZeroU64,
    },
    AbandonRead {
        grant: Grant,
        nonce: NonZeroU64,
    },
    /// The custodian attests the exact reconstructable root and manifest.
    Publish {
        grant: Grant,
        checkpoint: Checkpoint,
    },
    /// Install the custodian's next funded allocation in journal order.
    FundWindow {
        grant: Grant,
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
    Trim {
        grant: Grant,
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
    pub position: u64,
    pub lsn: u64,
    pub cut: Cut,
    pub window: Window,
    pub byte_start: u64,
    pub byte_end: u64,
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
        nonce: NonZeroU64,
        read: Hold,
    },
    ReadAbandoned,
    Published(Checkpoint),
    WindowFunded(Window),
    Protected(Hold),
    Released,
    Vacated,
    CohortSealed(Fingerprint),
    Trimmed(Cut),
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
    ReadPending,
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
    nonce: NonZeroU64,
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

    pub fn nonce(self) -> NonZeroU64 {
        self.nonce
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
    pub retained_data_bytes: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ApplyError {
    #[error("command position does not follow the applied journal prefix")]
    Position,
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
    command_history: Fingerprint,
    voter_scope: Fingerprint,
    successor: Option<Fingerprint>,
    writer_epoch: u64,
    enrollment_serial: u64,
    roster: BTreeMap<Uuid, Enrollment>,
    grant: Option<Grant>,
    read_floor: u64,
    window: Window,
    spent: u64,
    retained_bytes: u64,
    floor: Cut,
    head: Cut,
    checkpoint: Checkpoint,
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
            || window.allocation.is_nil()
            || window.serial != 1
            || window.bytes == 0
            || window.bytes > limits.retained_data_bytes
            || limits.enrolled_workers == 0
            || limits.replay_holds == 0
            || limits.retry_positions == 0
        {
            return Err(Refusal::Invalid);
        }
        Ok(Self {
            placement,
            limits,
            position: 0,
            command_history: [0; 32],
            voter_scope: [0; 32],
            successor: None,
            writer_epoch: 0,
            enrollment_serial: 0,
            roster: BTreeMap::new(),
            grant: None,
            read_floor: 0,
            window,
            spent: 0,
            retained_bytes: 0,
            floor: checkpoint.cut,
            head: checkpoint.cut,
            checkpoint,
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

    /// Reconciles the actual retained append. Position equality alone supplies
    /// no evidence that the caller's record was chosen.
    pub fn reconcile_append(&self, request: &Request) -> Result<AppendResult, Refusal> {
        let Command::Append {
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
        let record = self.record(*expected_next).ok_or(Refusal::Unavailable)?;
        if record.request != request.id
            || record.request_fingerprint != fingerprint(request)
            || record.grant != *grant
            || record.timestamp != *timestamp
            || record.payload != *payload
        {
            return Err(Refusal::Conflict);
        }
        Ok(record.result)
    }

    fn retained_receipt(&self, request: &Request) -> Option<Receipt> {
        let previous = self.outcomes.get(&(request.principal, request.id))?;
        (request.placement == self.placement && previous.fingerprint == fingerprint(request))
            .then_some(previous.receipt)
    }

    pub fn apply(&mut self, position: u64, request: Request) -> Result<Receipt, ApplyError> {
        if self.position.checked_add(1) != Some(position) {
            return Err(ApplyError::Position);
        }
        self.position = position;
        let fingerprint = fingerprint(&request);
        self.command_history = extend_command_history(self.command_history, position, fingerprint);
        while let Some((&(until, key), _)) = self.expiry.first_key_value() {
            if until > position {
                break;
            }
            let _ = self.expiry.pop_first();
            if self
                .holds
                .get(&key.1)
                .is_none_or(|entry| entry.origin != key.0)
            {
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
        if let Some(previous) = self.outcomes.get(&key) {
            return Ok(if previous.fingerprint == fingerprint {
                previous.receipt
            } else {
                receipt(Err(Refusal::Conflict))
            });
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
        let reading = matches!(&request.command, Command::Barrier { .. });
        let receipt = receipt(self.decide(principal, id, fingerprint, request.command));
        if receipt.outcome == Err(Refusal::ReadPending)
            || (reading && receipt.outcome == Err(Refusal::Capacity))
        {
            // A blocked admission has taken neither the nonce nor a hold.
            // The same request can still acquire them once the condition clears.
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

    fn next_read(
        &self,
        principal: Principal,
        grant: Grant,
        nonce: NonZeroU64,
    ) -> Result<(), Refusal> {
        self.writer(principal, grant)?;
        let expected = self.read_floor.checked_add(1).ok_or(Refusal::Stale)?;
        match nonce.get().cmp(&expected) {
            Ordering::Equal => Ok(()),
            Ordering::Less => Err(Refusal::Stale),
            Ordering::Greater => Err(Refusal::ReadPending),
        }
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
        self.admit_hold(origin, id, owner, self.checkpoint, start, through)
    }

    fn admit_hold(
        &mut self,
        origin: Principal,
        id: RequestId,
        owner: Enrollment,
        checkpoint: Checkpoint,
        start: Cut,
        through: Cut,
    ) -> Result<Hold, Refusal> {
        if self.holds.contains_key(&id) {
            return Err(Refusal::Conflict);
        }
        if self.holds.len() >= self.limits.replay_holds {
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
        self.holds.insert(id, HeldAdmission { hold, origin });
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
                let recovery = self.protect(principal, id, candidate, self.head)?;
                self.writer_epoch = epoch;
                self.grant = Some(grant);
                self.read_floor = 0;
                Ok(Outcome::Granted { grant, recovery })
            }
            Command::Append {
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
                let byte_end = self
                    .spent
                    .checked_add(bytes)
                    .filter(|end| *end <= self.window.bytes)
                    .ok_or(Refusal::Capacity)?;
                let retained_bytes = self
                    .retained_bytes
                    .checked_add(bytes)
                    .ok_or(Refusal::Capacity)?;
                let history = append_fingerprint(self.head, grant, id, timestamp, &payload);
                let cut = Cut { next_lsn, history };
                let result = AppendResult {
                    position: self.position,
                    lsn: expected_next,
                    cut,
                    window: self.window,
                    byte_start: self.spent,
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
                self.spent = byte_end;
                self.retained_bytes = retained_bytes;
                Ok(Outcome::Appended(result))
            }
            Command::Barrier { grant, nonce } => {
                self.next_read(principal, grant, nonce)?;
                let read = self.protect(principal, id, grant.enrollment, self.head)?;
                self.read_floor = nonce.get();
                Ok(Outcome::Barrier { grant, nonce, read })
            }
            Command::AbandonRead { grant, nonce } => {
                self.next_read(principal, grant, nonce)?;
                self.read_floor = nonce.get();
                Ok(Outcome::ReadAbandoned)
            }
            Command::Publish { grant, checkpoint } => {
                self.custodian(principal, grant)?;
                if checkpoint.cut.next_lsn < self.checkpoint.cut.next_lsn
                    || self.cut(checkpoint.cut.next_lsn) != Some(checkpoint.cut)
                {
                    return Err(Refusal::Stale);
                }
                if checkpoint.cut == self.checkpoint.cut && checkpoint != self.checkpoint {
                    return Err(Refusal::Conflict);
                }
                if checkpoint != self.checkpoint
                    && (checkpoint.custody.allocation.is_nil()
                        || Some(checkpoint.custody.revision)
                            != self.checkpoint.custody.revision.checked_add(1))
                {
                    return Err(Refusal::Invalid);
                }
                self.checkpoint = checkpoint;
                Ok(Outcome::Published(checkpoint))
            }
            Command::FundWindow { grant, window } => {
                self.custodian(principal, grant)?;
                if window.allocation.is_nil()
                    || window.bytes == 0
                    || Some(window.serial) != self.window.serial.checked_add(1)
                {
                    return Err(Refusal::Invalid);
                }
                if self
                    .retained_bytes
                    .checked_add(window.bytes)
                    .is_none_or(|bytes| bytes > self.limits.retained_data_bytes)
                {
                    return Err(Refusal::Capacity);
                }
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
                    .is_none_or(|entry| entry.hold != source)
                {
                    return Err(Refusal::Unavailable);
                }
                let checkpoint = source.checkpoint;
                let hold = self.admit_hold(
                    principal,
                    id,
                    source.owner,
                    checkpoint,
                    checkpoint.cut,
                    checkpoint.cut,
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
                Ok(Outcome::Released)
            }
            Command::Trim { grant, through } => {
                self.writer(principal, grant)?;
                if through.next_lsn > self.checkpoint.cut.next_lsn
                    || self.cut(through.next_lsn) != Some(through)
                {
                    return Err(Refusal::Invalid);
                }
                if self.holds.values().map(|entry| entry.hold).any(|hold| {
                    hold.through.next_lsn > hold.start.next_lsn
                        && through.next_lsn > hold.start.next_lsn
                }) {
                    return Err(Refusal::Unavailable);
                }
                let trim = usize::try_from(through.next_lsn - self.floor.next_lsn)
                    .map_err(|_| Refusal::Invalid)?;
                for record in self.records.drain(..trim) {
                    self.retained_bytes -= record.result.byte_end - record.result.byte_start;
                }
                self.floor = through;
                Ok(Outcome::Trimmed(through))
            }
        }
    }

    fn custodian(&self, principal: Principal, grant: Grant) -> Result<(), Refusal> {
        if principal != Principal::Custodian {
            return Err(Refusal::Unauthorized);
        }
        if self.grant != Some(grant) {
            return Err(Refusal::Stale);
        }
        Ok(())
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
    grant: Grant,
    request: RequestId,
    timestamp: i64,
    payload: &Bytes,
) -> Fingerprint {
    let mut hash = Sha256::new();
    hash.update(b"logkeeper.applied-append.v1");
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
    request: Fingerprint,
) -> Fingerprint {
    let mut hash = Sha256::new();
    hash.update(b"logkeeper.ordered-history.v1");
    hash.update(previous);
    hash.update(position.to_be_bytes());
    hash.update(request);
    hash.finalize().into()
}
