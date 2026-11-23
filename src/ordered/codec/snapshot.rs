use super::{
    Input, checkpoint, cut, enrollment, grant, hold_row, principal, request_id, window,
    writer_state,
};
use crate::ordered::{
    APPEND_RECORD_CHARGE_BYTES, AppendResult, Command, HeldAdmission, Outcome, Principal, Receipt,
    Record, Refusal, Request, RetainedOutcome, State, Window, append_fingerprint, fingerprint,
};
use bytes::{BufMut, Bytes, BytesMut};
use std::collections::BTreeSet;

const MAGIC: &[u8; 8] = b"LKBASE01";

impl super::super::Limits {
    pub(in crate::ordered) fn base_control_bytes(self) -> Option<usize> {
        // Include the prefix envelope and fixed fields, then the maximum
        // encoded size of each bounded control row. Retained data has its own
        // byte charge and a full outcome row can outlive its data.
        let roster = self.enrolled_workers.checked_mul(24)?;
        let holds = self.replay_holds.checked_mul(289)?;
        let retries = usize::try_from(self.retry_positions).ok()?;
        let outcomes = retries.checked_add(self.replay_holds)?.checked_mul(394)?;
        512usize
            .checked_add(roster)?
            .checked_add(holds)?
            .checked_add(outcomes)
    }
}

impl State {
    pub(in crate::ordered) fn encode_base(&self) -> Bytes {
        let mut output = BytesMut::new();
        output.put_slice(MAGIC);
        output.put_u64(self.position);
        output.put_slice(&self.command_history);
        writer_state(&mut output, self.writer_state());
        output.put_u64(self.enrollment_serial);
        output.put_u64(self.read_floor);
        window(&mut output, self.window);
        output.put_u64(self.spent);
        cut(&mut output, self.floor);
        cut(&mut output, self.head);
        checkpoint(&mut output, self.checkpoint);

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
        if state.position == 0
            || state.window.allocation.is_nil()
            || state.window.serial == 0
            || state.window.bytes == 0
            || (state.window.serial == 1 && state.window != initial.window)
            || state.spent > state.window.bytes
            || state.floor.next_lsn > state.checkpoint.cut.next_lsn
            || state.checkpoint.cut.next_lsn > state.head.next_lsn
            || state.checkpoint.custody.allocation.is_nil()
            || state.checkpoint.custody.revision == 0
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
                    grant: *grant,
                    expected_next: result.lsn,
                    timestamp: *timestamp,
                    payload: payload.clone(),
                },
            };
            let length = (payload.len() as u64).checked_add(APPEND_RECORD_CHARGE_BYTES);
            if result.position <= previous_position
                || result.position > self.position
                || result.lsn != previous.next_lsn
                || result.lsn.checked_add(1) != Some(result.cut.next_lsn)
                || result.cut.history
                    != append_fingerprint(previous, *grant, *request, *timestamp, payload)
                || result.window.allocation.is_nil()
                || result.window.serial == 0
                || result.window.serial > self.window.serial
                || (result.window.serial == self.window.serial && result.window != self.window)
                || result.byte_end > result.window.bytes
                || result.byte_end.checked_sub(result.byte_start) != length
                || previous_window.is_some_and(|(window, end)| {
                    if result.window.serial == window.serial {
                        result.window != window || result.byte_start != end
                    } else {
                        result.window.serial < window.serial || result.byte_start != 0
                    }
                })
                || request.nonce.is_nil()
                || request.expires_at <= result.position
                || *request_fingerprint != fingerprint(&original)
            {
                return Err(Refusal::Invalid);
            }
            previous = result.cut;
            previous_position = result.position;
            previous_window = Some((result.window, result.byte_end));
            self.retained_bytes = self
                .retained_bytes
                .checked_add(length.ok_or(Refusal::Invalid)?)
                .ok_or(Refusal::Invalid)?;
            self.records.push_back(entry);
        }
        if previous != self.head
            || previous_window.is_some_and(|(window, end)| {
                self.spent != if window == self.window { end } else { 0 }
            })
            || self
                .retained_bytes
                .checked_add(self.window.bytes - self.spent)
                .is_none_or(|bytes| bytes > self.limits.retained_data_bytes)
            || self.cut(self.checkpoint.cut.next_lsn) != Some(self.checkpoint.cut)
        {
            return Err(Refusal::Invalid);
        }
        Ok(())
    }

    fn read_holds(&mut self, input: &mut Input) -> Result<(), Refusal> {
        for _ in 0..input.count(self.limits.replay_holds)? {
            let hold = input.hold()?;
            let origin = input.principal()?;
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
            self.holds.insert(hold.id, HeldAdmission { hold, origin });
        }
        Ok(())
    }

    fn read_outcomes(&mut self, input: &mut Input) -> Result<(), Refusal> {
        let retries = usize::try_from(self.limits.retry_positions).unwrap_or(usize::MAX);
        let count = input.count(retries.saturating_add(self.limits.replay_holds))?;
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
            if id.expires_at > self.position {
                self.expiry.insert((id.expires_at, key), ());
            } else if self
                .holds
                .get(&id)
                .is_none_or(|entry| entry.origin != issuer)
            {
                return Err(Refusal::Invalid);
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
            let admitted = match receipt.outcome {
                Ok(Outcome::Granted { recovery, .. }) => recovery,
                Ok(Outcome::Barrier { read, .. }) | Ok(Outcome::Protected(read)) => read,
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
            8 => Outcome::Trimmed(self.cut()?),
            9 => Outcome::ReadAbandoned,
            10 => Outcome::WindowFunded(self.window()?),
            11 => Outcome::Vacated,
            32 => return Ok(Err(Refusal::WrongPlacement)),
            33 => return Ok(Err(Refusal::Unauthorized)),
            34 => return Ok(Err(Refusal::Stale)),
            35 => return Ok(Err(Refusal::Conflict)),
            36 => return Ok(Err(Refusal::Invalid)),
            37 => return Ok(Err(Refusal::Expired)),
            38 => return Ok(Err(Refusal::Capacity)),
            39 => return Ok(Err(Refusal::Unavailable)),
            40 => return Ok(Err(Refusal::ReadPending)),
            _ => return Err(Refusal::Invalid),
        }))
    }
}

pub(super) fn append_result(output: &mut BytesMut, value: AppendResult) {
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
        Ok(Outcome::Trimmed(through)) => {
            output.put_u8(8);
            cut(output, through);
        }
        Ok(Outcome::ReadAbandoned) => output.put_u8(9),
        Ok(Outcome::WindowFunded(allocation)) => {
            output.put_u8(10);
            window(output, allocation);
        }
        Ok(Outcome::Vacated) => output.put_u8(11),
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
        }),
    }
}
