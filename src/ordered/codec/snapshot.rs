use super::{
    Input, checkpoint, checkpoint_preparation, cut, enrollment, grant, hold_row, principal,
    request_id, window, writer_state,
};
use crate::ordered::{
    ACTIVATION_HOLD_SLOTS, APPEND_RECORD_CHARGE_BYTES, AppendClass, AppendResult, Command,
    HeldAdmission, HoldKind, Outcome, Principal, Receipt, Record, Refusal, Request,
    RetainedCheckpoint, RetainedOutcome, State, Window, admission, append_fingerprint, fingerprint,
};
use bytes::{BufMut, Bytes, BytesMut};
use std::collections::BTreeSet;

use crate::ordered::TrimResult;

const MAGIC: &[u8; 8] = b"LKBASE03";

impl super::super::Limits {
    pub(in crate::ordered) fn base_control_bytes(self) -> Option<usize> {
        // Include the prefix envelope and fixed fields, then the maximum
        // encoded size of each bounded control row. Retained data has its own
        // byte charge and a full outcome row can outlive its data.
        let roster = self.enrolled_workers.checked_mul(24)?;
        let hold_slots = self.replay_holds.checked_add(ACTIVATION_HOLD_SLOTS)?;
        let holds = hold_slots.checked_mul(368)?;
        let retries = usize::try_from(self.retry_positions).ok()?;
        let outcomes = retries.checked_add(hold_slots)?.checked_mul(448)?;
        let checkpoint_retention = self.replay_holds.checked_mul(161)?;
        1024usize
            .checked_add(roster)?
            .checked_add(holds)?
            .checked_add(checkpoint_retention)?
            .checked_add(outcomes)
    }
}

impl State {
    pub(in crate::ordered) fn encode_base(&self) -> Bytes {
        let mut output = BytesMut::new();
        output.put_slice(MAGIC);
        output.put_u64(self.position);
        output.put_slice(&self.command_history);
        output.put_slice(&self.voter_scope);
        output.put_u8(u8::from(self.successor.is_some()));
        if let Some(successor) = self.successor {
            output.put_slice(&successor);
        }
        writer_state(&mut output, self.writer_state());
        output.put_u64(self.enrollment_serial);
        output.put_u64(self.read_floor);
        window(&mut output, self.window);
        output.put_u64(self.spent);
        cut(&mut output, self.floor);
        cut(&mut output, self.head);
        checkpoint(&mut output, self.checkpoint);
        output.put_u8(u8::from(self.preparing.is_some()));
        if let Some(item) = self.preparing {
            checkpoint_preparation(&mut output, item);
        }
        output.put_u64(self.old_roots.len() as u64);
        for entry in self.old_roots.values() {
            checkpoint(&mut output, entry.checkpoint);
            output.put_u8(u8::from(entry.closed));
        }

        output.put_u64(self.roster.len() as u64);
        for member in self.roster.values() {
            enrollment(&mut output, *member);
        }
        output.put_u64(self.records.len() as u64);
        for entry in &self.records {
            record(&mut output, entry);
        }
        output.put_u64(self.holds.len() as u64);
        for admission in self.holds.values() {
            hold_row(&mut output, admission.hold);
            principal(&mut output, admission.origin);
            match admission.kind {
                HoldKind::Ordinary => output.put_u8(0),
                HoldKind::Recovery => output.put_u8(1),
                HoldKind::Root(parent) => {
                    output.put_u8(2);
                    request_id(&mut output, parent);
                }
            }
        }
        output.put_u64(self.outcomes.len() as u64);
        for ((issuer, id), retained) in &self.outcomes {
            principal(&mut output, *issuer);
            request_id(&mut output, *id);
            output.put_slice(&retained.fingerprint);
            output.put_u64(retained.receipt.position);
            result(&mut output, retained.receipt.outcome);
        }
        output.freeze()
    }

    pub(in crate::ordered) fn decode_base(initial: &Self, bytes: Bytes) -> Result<Self, Refusal> {
        let mut input = Input(bytes);
        if &input.take::<8>()? != MAGIC {
            return Err(Refusal::Invalid);
        }
        let mut state = initial.clone();
        state.position = input.u64()?;
        state.command_history = input.take()?;
        state.voter_scope = input.take()?;
        state.successor = input.optional(|input| input.take())?;
        let writer = input.writer_state()?;
        state.writer_epoch = writer.epoch;
        state.grant = writer.grant;
        state.enrollment_serial = input.u64()?;
        state.read_floor = input.u64()?;
        state.window = input.window()?;
        state.spent = input.u64()?;
        state.floor = input.cut()?;
        state.head = input.cut()?;
        state.checkpoint = input.checkpoint()?;
        state.preparing = input.optional(Input::checkpoint_preparation)?;
        for _ in 0..input.count(state.limits.replay_holds)? {
            let checkpoint = input.checkpoint()?;
            let closed = match input.read_byte()? {
                0 => false,
                1 => true,
                _ => return Err(Refusal::Invalid),
            };
            if checkpoint.custody.revision == 0
                || checkpoint.custody.revision >= state.checkpoint.custody.revision
                || checkpoint.custody.allocation.is_nil()
                || checkpoint.custody.provider == [0; 32]
                || checkpoint.manifest == [0; 32]
                || checkpoint.cut.next_lsn >= state.checkpoint.cut.next_lsn
                || state
                    .old_roots
                    .insert(
                        checkpoint.custody.revision,
                        RetainedCheckpoint { checkpoint, closed },
                    )
                    .is_some()
            {
                return Err(Refusal::Invalid);
            }
        }
        if state.position == 0
            || state.voter_scope != initial.voter_scope
            || state
                .successor
                .is_some_and(|next| next == [0; 32] || next == state.voter_scope)
            || state.window.allocation.is_nil()
            || state.window.serial == 0
            || state.window.bytes == 0
            || (state.window.serial == 1 && state.window != initial.window)
            || state.spent > state.window.bytes
            || state.floor.next_lsn > state.checkpoint.cut.next_lsn
            || state.checkpoint.cut.next_lsn > state.head.next_lsn
            || state.checkpoint.custody.allocation.is_nil()
            || state.checkpoint.custody.revision == 0
            || (state.checkpoint.manifest == [0; 32])
                != (state.checkpoint.custody.provider == [0; 32])
            || (state.checkpoint.custody.revision == 1 && state.checkpoint != initial.checkpoint)
            || state.head.next_lsn > state.position
            || state.writer_epoch > state.position
            || state.enrollment_serial > state.position
        {
            return Err(Refusal::Invalid);
        }
        state.read_roster(&mut input)?;
        state.read_records(&mut input)?;
        state.read_holds(&mut input)?;
        if state
            .holds
            .values()
            .any(|entry| !state.checkpoint_open(entry.hold.checkpoint))
            || state.preparing.is_some_and(|item| {
                item.checkpoint.next_lsn <= state.checkpoint.cut.next_lsn
                    || state.cut(item.checkpoint.next_lsn) != Some(item.checkpoint)
                    || Some(item.custody.revision)
                        != state.checkpoint.custody.revision.checked_add(1)
                    || item.custody.allocation.is_nil()
                    || item.custody.provider == [0; 32]
                    || item.root == [0; 32]
                    || item.usable_bytes == 0
                    || (item.base != initial.checkpoint && !state.checkpoint_open(item.base))
            })
        {
            return Err(Refusal::Invalid);
        }
        state.read_outcomes(&mut input)?;
        if !input.0.is_empty() {
            return Err(Refusal::Invalid);
        }
        Ok(state)
    }

    fn read_roster(&mut self, input: &mut Input) -> Result<(), Refusal> {
        let mut serials = BTreeSet::new();
        for _ in 0..input.count(self.limits.enrolled_workers)? {
            let member = input.enrollment()?;
            if member.worker.is_nil()
                || member.serial == 0
                || member.serial > self.enrollment_serial
                || !serials.insert(member.serial)
                || self
                    .roster
                    .last_key_value()
                    .is_some_and(|(id, _)| *id >= member.worker)
            {
                return Err(Refusal::Invalid);
            }
            self.roster.insert(member.worker, member);
        }
        if let Some(writer) = self.grant {
            if writer.epoch == 0
                || writer.epoch != self.writer_epoch
                || self.roster.get(&writer.enrollment.worker) != Some(&writer.enrollment)
            {
                return Err(Refusal::Invalid);
            }
        }
        Ok(())
    }

    fn read_records(&mut self, input: &mut Input) -> Result<(), Refusal> {
        let count = usize::try_from(self.head.next_lsn - self.floor.next_lsn)
            .map_err(|_| Refusal::Invalid)?;
        if input.count(count)? != count {
            return Err(Refusal::Invalid);
        }
        let mut previous = self.floor;
        let mut previous_position = 0;
        let mut previous_window: Option<(Window, u64)> = None;
        for _ in 0..count {
            let entry = input.record()?;
            let Record {
                result,
                grant,
                timestamp,
                request,
                request_fingerprint,
                payload,
            } = &entry;
            let original = Request {
                placement: self.placement,
                principal: Principal::Worker(grant.enrollment),
                id: *request,
                command: Command::Append {
                    class: result.class,
                    grant: *grant,
                    expected_next: result.lsn,
                    timestamp: *timestamp,
                    payload: payload.clone(),
                },
            };
            let length = (payload.len() as u64)
                .checked_add(APPEND_RECORD_CHARGE_BYTES)
                .ok_or(Refusal::Invalid)?;
            if result.position <= previous_position
                || result.position > self.position
                || result.lsn != previous.next_lsn
                || result.lsn.checked_add(1) != Some(result.cut.next_lsn)
                || result.cut.history
                    != append_fingerprint(
                        previous,
                        result.class,
                        *grant,
                        *request,
                        *timestamp,
                        payload,
                    )
                || result.window.allocation.is_nil()
                || result.window.serial == 0
                || result.window.serial > self.window.serial
                || (result.window.serial == self.window.serial && result.window != self.window)
                || result.byte_end.checked_sub(result.byte_start) != Some(length)
                || request.nonce.is_nil()
                || request.expires_at <= result.position
                || *request_fingerprint != fingerprint(&original)
            {
                return Err(Refusal::Invalid);
            }
            previous = result.cut;
            previous_position = result.position;
            match result.class {
                AppendClass::Data => {
                    if result.byte_end > result.window.bytes
                        || previous_window.is_some_and(|(window, end)| {
                            if result.window.serial == window.serial {
                                result.window != window || result.byte_start != end
                            } else {
                                result.window.serial < window.serial || result.byte_start != 0
                            }
                        })
                    {
                        return Err(Refusal::Invalid);
                    }
                    previous_window = Some((result.window, result.byte_end));
                    self.retained_bytes =
                        admission::debit(self.retained_bytes, length, self.ordinary_capacity())
                            .ok_or(Refusal::Invalid)?;
                }
                AppendClass::Maintenance => {
                    if result.byte_start != 0 {
                        return Err(Refusal::Invalid);
                    }
                    self.maintenance_retained = admission::debit(
                        self.maintenance_retained,
                        length,
                        self.limits.maintenance_bytes,
                    )
                    .ok_or(Refusal::Invalid)?;
                }
            }
            self.records.push_back(entry);
        }
        if previous != self.head
            || previous_window.is_some_and(|(window, end)| {
                self.spent != if window == self.window { end } else { 0 }
            })
            || admission::debit(
                self.retained_bytes,
                self.window.bytes - self.spent,
                self.ordinary_capacity(),
            )
            .is_none()
            || self.cut(self.checkpoint.cut.next_lsn) != Some(self.checkpoint.cut)
        {
            return Err(Refusal::Invalid);
        }
        Ok(())
    }

    fn read_holds(&mut self, input: &mut Input) -> Result<(), Refusal> {
        let mut ordinary = 0;
        let mut activation = 0;
        let mut roots = BTreeSet::new();
        for _ in 0..input.count(self.limits.replay_holds + ACTIVATION_HOLD_SLOTS)? {
            let hold = input.hold()?;
            let origin = input.principal()?;
            let kind = match input.read_byte()? {
                0 => {
                    ordinary += 1;
                    HoldKind::Ordinary
                }
                1 => {
                    activation += 1;
                    HoldKind::Recovery
                }
                2 => {
                    activation += 1;
                    let parent = input.request_id()?;
                    if parent == hold.id
                        || parent.nonce.is_nil()
                        || !roots.insert(parent)
                        || hold.start != hold.checkpoint.cut
                        || hold.through != hold.checkpoint.cut
                    {
                        return Err(Refusal::Invalid);
                    }
                    HoldKind::Root(parent)
                }
                _ => return Err(Refusal::Invalid),
            };
            if ordinary > self.limits.replay_holds || activation > ACTIVATION_HOLD_SLOTS {
                return Err(Refusal::Invalid);
            }
            if hold.admitted_at == 0
                || hold.admitted_at > self.position
                || hold.admitted_at >= hold.id.expires_at
                || hold.id.nonce.is_nil()
                || hold.checkpoint.cut.next_lsn > self.checkpoint.cut.next_lsn
                || hold.start.next_lsn > hold.through.next_lsn
                || hold.through.next_lsn > self.head.next_lsn
                || self
                    .holds
                    .last_key_value()
                    .is_some_and(|(id, _)| *id >= hold.id)
                || (hold.start != hold.through
                    && (self.cut(hold.start.next_lsn) != Some(hold.start)
                        || self.cut(hold.through.next_lsn) != Some(hold.through)))
            {
                return Err(Refusal::Invalid);
            }
            self.holds
                .insert(hold.id, HeldAdmission { hold, origin, kind });
        }
        Ok(())
    }

    fn read_outcomes(&mut self, input: &mut Input) -> Result<(), Refusal> {
        let retries = usize::try_from(self.limits.retry_positions).unwrap_or(usize::MAX);
        let count = input
            .count(retries.saturating_add(self.limits.replay_holds + ACTIVATION_HOLD_SLOTS))?;
        for _ in 0..count {
            let issuer = input.principal()?;
            let id = input.request_id()?;
            let key = (issuer, id);
            let fingerprint = input.take()?;
            let position = input.u64()?;
            let outcome = input.result()?;
            if id.nonce.is_nil()
                || position == 0
                || position > self.position
                || position >= id.expires_at
                || id.expires_at - position > self.limits.retry_positions
                || outcome == Err(Refusal::ReadPending)
                || self
                    .outcomes
                    .last_key_value()
                    .is_some_and(|(old, _)| *old >= key)
            {
                return Err(Refusal::Invalid);
            }
            let live_hold = self
                .holds
                .get(&id)
                .is_some_and(|entry| entry.origin == issuer);
            if !admission::retains_receipt(self.position, id.expires_at, live_hold) {
                return Err(Refusal::Invalid);
            }
            if id.expires_at > self.position {
                self.expiry.insert((id.expires_at, key), ());
            }
            let receipt = Receipt {
                placement: self.placement,
                principal: issuer,
                request: id,
                position,
                outcome,
            };
            self.outcomes.insert(
                key,
                RetainedOutcome {
                    fingerprint,
                    receipt,
                },
            );
        }
        for entry in self.holds.values() {
            let hold = entry.hold;
            let receipt = self
                .outcomes
                .get(&(entry.origin, hold.id))
                .ok_or(Refusal::Invalid)?
                .receipt;
            let admitted = match (entry.kind, receipt.outcome) {
                (HoldKind::Recovery, Ok(Outcome::Granted { recovery, .. })) => recovery,
                (
                    HoldKind::Ordinary,
                    Ok(Outcome::Barrier { read, .. } | Outcome::Protected(read)),
                ) => read,
                (HoldKind::Root(_), Ok(Outcome::Protected(read))) => read,
                _ => return Err(Refusal::Invalid),
            };
            if admitted != hold || receipt.position != hold.admitted_at {
                return Err(Refusal::Invalid);
            }
        }
        Ok(())
    }
}

impl Input {
    pub(super) fn count(&mut self, maximum: usize) -> Result<usize, Refusal> {
        let count = usize::try_from(self.u64()?).map_err(|_| Refusal::Invalid)?;
        if count > maximum || count > self.0.len() {
            return Err(Refusal::Invalid);
        }
        Ok(count)
    }

    pub(super) fn payload(&mut self) -> Result<Bytes, Refusal> {
        let length = self.count(usize::MAX)?;
        Ok(self.0.split_to(length))
    }

    pub(super) fn append_result(&mut self) -> Result<AppendResult, Refusal> {
        Ok(AppendResult {
            class: self.append_class()?,
            position: self.u64()?,
            lsn: self.u64()?,
            cut: self.cut()?,
            window: self.window()?,
            byte_start: self.u64()?,
            byte_end: self.u64()?,
        })
    }

    pub(super) fn record(&mut self) -> Result<Record, Refusal> {
        Ok(Record {
            result: self.append_result()?,
            grant: self.grant()?,
            timestamp: i64::from_be_bytes(self.take()?),
            request: self.request_id()?,
            request_fingerprint: self.take()?,
            payload: self.payload()?,
        })
    }

    pub(super) fn result(&mut self) -> Result<Result<Outcome, Refusal>, Refusal> {
        Ok(Ok(match self.read_byte()? {
            0 => Outcome::Enrolled(self.enrollment()?),
            1 => Outcome::Withdrawn,
            2 => Outcome::Granted {
                grant: self.grant()?,
                recovery: self.hold()?,
            },
            3 => Outcome::Appended(self.append_result()?),
            4 => Outcome::Barrier {
                grant: self.grant()?,
                nonce: self.nonce()?,
                read: self.hold()?,
            },
            5 => Outcome::Published(self.checkpoint()?),
            6 => Outcome::Protected(self.hold()?),
            7 => Outcome::Released,
            8 => Outcome::Trimmed(TrimResult {
                from: self.cut()?,
                through: self.cut()?,
                ordinary_bytes: self.u64()?,
                maintenance_bytes: self.u64()?,
            }),
            9 => Outcome::ReadAbandoned,
            10 => Outcome::WindowFunded(self.window()?),
            11 => Outcome::Vacated,
            12 => Outcome::CohortSealed(self.take()?),
            13 => Outcome::CheckpointPrepared(self.checkpoint_preparation()?),
            14 => Outcome::CheckpointClosed(self.checkpoint()?),
            15 => Outcome::CheckpointSettled(self.checkpoint()?),
            16 => Outcome::WorkerDisposed(self.enrollment()?),
            32 => return Ok(Err(Refusal::WrongPlacement)),
            33 => return Ok(Err(Refusal::Unauthorized)),
            34 => return Ok(Err(Refusal::Stale)),
            35 => return Ok(Err(Refusal::Conflict)),
            36 => return Ok(Err(Refusal::Invalid)),
            37 => return Ok(Err(Refusal::Expired)),
            38 => return Ok(Err(Refusal::Capacity)),
            39 => return Ok(Err(Refusal::Unavailable)),
            40 => return Ok(Err(Refusal::ReadPending)),
            41 => return Ok(Err(Refusal::CohortSealed)),
            _ => return Err(Refusal::Invalid),
        }))
    }
}

pub(super) fn append_result(output: &mut BytesMut, value: AppendResult) {
    output.put_u8(value.class.tag());
    output.put_u64(value.position);
    output.put_u64(value.lsn);
    cut(output, value.cut);
    window(output, value.window);
    output.put_u64(value.byte_start);
    output.put_u64(value.byte_end);
}

pub(super) fn record(output: &mut BytesMut, entry: &Record) {
    append_result(output, entry.result);
    grant(output, entry.grant);
    output.put_i64(entry.timestamp);
    request_id(output, entry.request);
    output.put_slice(&entry.request_fingerprint);
    output.put_u64(entry.payload.len() as u64);
    output.put_slice(&entry.payload);
}

pub(super) fn result(output: &mut BytesMut, value: Result<Outcome, Refusal>) {
    match value {
        Ok(Outcome::Enrolled(member)) => {
            output.put_u8(0);
            enrollment(output, member);
        }
        Ok(Outcome::Withdrawn) => output.put_u8(1),
        Ok(Outcome::Granted {
            grant: writer,
            recovery,
        }) => {
            output.put_u8(2);
            grant(output, writer);
            hold_row(output, recovery);
        }
        Ok(Outcome::Appended(append)) => {
            output.put_u8(3);
            append_result(output, append);
        }
        Ok(Outcome::Barrier {
            grant: writer,
            nonce,
            read,
        }) => {
            output.put_u8(4);
            grant(output, writer);
            output.put_u64(nonce.get());
            hold_row(output, read);
        }
        Ok(Outcome::Published(published)) => {
            output.put_u8(5);
            checkpoint(output, published);
        }
        Ok(Outcome::Protected(hold)) => {
            output.put_u8(6);
            hold_row(output, hold);
        }
        Ok(Outcome::Released) => output.put_u8(7),
        Ok(Outcome::Trimmed(result)) => {
            output.put_u8(8);
            cut(output, result.from);
            cut(output, result.through);
            output.put_u64(result.ordinary_bytes);
            output.put_u64(result.maintenance_bytes);
        }
        Ok(Outcome::ReadAbandoned) => output.put_u8(9),
        Ok(Outcome::WindowFunded(allocation)) => {
            output.put_u8(10);
            window(output, allocation);
        }
        Ok(Outcome::Vacated) => output.put_u8(11),
        Ok(Outcome::CohortSealed(successor)) => {
            output.put_u8(12);
            output.put_slice(&successor);
        }
        Ok(Outcome::CheckpointPrepared(item)) => {
            output.put_u8(13);
            checkpoint_preparation(output, item);
        }
        Ok(Outcome::CheckpointClosed(root)) => {
            output.put_u8(14);
            checkpoint(output, root);
        }
        Ok(Outcome::CheckpointSettled(root)) => {
            output.put_u8(15);
            checkpoint(output, root);
        }
        Ok(Outcome::WorkerDisposed(worker)) => {
            output.put_u8(16);
            enrollment(output, worker);
        }
        Err(refusal) => output.put_u8(match refusal {
            Refusal::WrongPlacement => 32,
            Refusal::Unauthorized => 33,
            Refusal::Stale => 34,
            Refusal::Conflict => 35,
            Refusal::Invalid => 36,
            Refusal::Expired => 37,
            Refusal::Capacity => 38,
            Refusal::Unavailable => 39,
            Refusal::ReadPending => 40,
            Refusal::CohortSealed => 41,
        }),
    }
}
