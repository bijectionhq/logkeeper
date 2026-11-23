use super::{
    AppendClass, BarrierClaim, Checkpoint, CheckpointPreparation, Command, Custody, Cut,
    Enrollment, Fingerprint, Grant, Hold, MAX_OBJECT_REFERENCES, ObjectName, ObjectWithdrawal,
    Placement, Principal, Refusal, Request, RequestId, Window, WriterState, valid_object_names,
};
use bytes::{BufMut, Bytes, BytesMut};
use uuid::Uuid;

pub(super) mod frame;
mod service;
mod signed;
mod snapshot;
mod snapshot_checks;

use frame::{
    COMMAND_VERSION, decision_header, decode_flag, encode_flag, has_command_version,
    object_name_count, read_decision_time,
};

use signed::{BARRIER_DOMAIN, checkpoint, cut, enrollment, placement, request_id, uuid};

impl Request {
    /// The exact bytes used by ordered replication and crash replay.
    pub fn encode(&self) -> Bytes {
        let mut output = BytesMut::new();
        output.put_u8(COMMAND_VERSION);
        placement(&mut output, self.placement);
        principal(&mut output, self.principal);
        request_id(&mut output, self.id);
        match &self.command {
            Command::Enroll { worker, expected } => {
                output.put_u8(0);
                uuid(&mut output, *worker);
                output.put_u8(encode_flag(expected.is_some()));
                if let Some(expected) = expected {
                    enrollment(&mut output, *expected);
                }
            }
            Command::Withdraw { enrollment: worker } => {
                output.put_u8(1);
                enrollment(&mut output, *worker);
            }
            Command::Grant {
                expected,
                candidate,
            } => {
                output.put_u8(2);
                writer_state(&mut output, *expected);
                enrollment(&mut output, *candidate);
            }
            Command::PublishAndRotate {
                grant: writer,
                checkpoint: root,
            } => {
                output.put_u8(22);
                grant(&mut output, *writer);
                checkpoint(&mut output, *root);
            }
            Command::Append {
                class,
                grant: writer,
                expected_next,
                timestamp,
                payload,
                references,
            } => {
                output.put_u8(if references.is_some() { 23 } else { 3 });
                output.put_u8(class.tag());
                grant(&mut output, *writer);
                output.put_u64(*expected_next);
                output.put_i64(*timestamp);
                if let Some(names) = references {
                    object_names(&mut output, names);
                }
                output.put_slice(payload);
            }
            Command::Barrier => output.put_u8(4),
            Command::PrepareCheckpoint {
                preparation,
                references,
            } => {
                output.put_u8(if references.is_some() { 24 } else { 15 });
                checkpoint_preparation(&mut output, *preparation);
                if let Some(names) = references {
                    object_names(&mut output, names);
                }
            }
            Command::WithdrawObject { object } => {
                output.put_u8(25);
                withdrawal(&mut output, *object);
            }
            Command::CloseCheckpoint { checkpoint: root } => {
                output.put_u8(16);
                checkpoint(&mut output, *root);
            }
            Command::SettleCheckpoint {
                checkpoint: root,
                disposition,
                erasure_floor,
            } => {
                output.put_u8(17);
                checkpoint(&mut output, *root);
                output.put_slice(disposition);
                output.put_u64(*erasure_floor);
            }
            Command::DisposeWorker {
                enrollment: worker,
                disposition,
            } => {
                output.put_u8(18);
                enrollment(&mut output, *worker);
                output.put_slice(disposition);
            }
            Command::Publish {
                checkpoint: offered,
            } => {
                output.put_u8(5);
                checkpoint(&mut output, *offered);
            }
            Command::FundWindow { window: allocation } => {
                output.put_u8(10);
                window(&mut output, *allocation);
            }
            Command::Protect {
                grant: writer,
                through,
            } => {
                output.put_u8(6);
                grant(&mut output, *writer);
                cut(&mut output, *through);
            }
            Command::Trim { selected, through } => {
                output.put_u8(8);
                checkpoint(&mut output, *selected);
                cut(&mut output, *through);
            }
            Command::Release { hold } => {
                output.put_u8(7);
                hold_row(&mut output, *hold);
            }
            Command::ReleaseRead { read } => {
                output.put_u8(19);
                request_id(&mut output, *read);
            }
            Command::Lease { grant: writer } => {
                output.put_u8(20);
                grant(&mut output, *writer);
            }
            Command::LeaseRead { hold } => {
                output.put_u8(26);
                hold_row(&mut output, *hold);
            }
            Command::DisposeExpired { enrollment: worker } => {
                output.put_u8(21);
                enrollment(&mut output, *worker);
            }
            Command::ProtectRange { from, through } => {
                output.put_u8(11);
                output.put_u64(*from);
                output.put_u64(*through);
            }
            Command::ProtectCheckpoint { root, from, through } => {
                output.put_u8(27);
                output.put_slice(root);
                output.put_u64(*from);
                output.put_u64(*through);
            }
            Command::ProtectRoot { source } => {
                output.put_u8(12);
                hold_row(&mut output, *source);
            }
            Command::Vacate { grant: writer } => {
                output.put_u8(13);
                grant(&mut output, *writer);
            }
            Command::SealCohort {
                expected,
                successor,
            } => {
                output.put_u8(14);
                output.put_slice(expected);
                output.put_slice(successor);
            }
        }
        output.freeze()
    }

    /// Decodes a single frame. A transport authenticates the principal and
    /// placement before choosing the frame.
    pub fn decode(frame: Bytes) -> Result<Self, Refusal> {
        let mut input = Input(frame);
        if !has_command_version(input.read_byte()?) {
            return Err(Refusal::Invalid);
        }
        let placement = input.placement()?;
        let principal = input.principal()?;
        let id = input.request_id()?;
        let command = match input.read_byte()? {
            0 => Command::Enroll {
                worker: input.uuid()?,
                expected: input.optional(Input::enrollment)?,
            },
            1 => Command::Withdraw {
                enrollment: input.enrollment()?,
            },
            2 => Command::Grant {
                expected: input.writer_state()?,
                candidate: input.enrollment()?,
            },
            22 => Command::PublishAndRotate {
                grant: input.grant()?,
                checkpoint: input.checkpoint()?,
            },
            tag @ (3 | 23) => Command::Append {
                class: input.append_class()?,
                grant: input.grant()?,
                expected_next: input.u64()?,
                timestamp: i64::from_be_bytes(input.take()?),
                references: (tag == 23).then(|| input.object_names()).transpose()?,
                payload: std::mem::take(&mut input.0),
            },
            4 => Command::Barrier,
            5 => Command::Publish {
                checkpoint: input.checkpoint()?,
            },
            6 => Command::Protect {
                grant: input.grant()?,
                through: input.cut()?,
            },
            7 => Command::Release {
                hold: input.hold()?,
            },
            19 => Command::ReleaseRead {
                read: input.request_id()?,
            },
            20 => Command::Lease {
                grant: input.grant()?,
            },
            26 => Command::LeaseRead { hold: input.hold()? },
            21 => Command::DisposeExpired {
                enrollment: input.enrollment()?,
            },
            8 => Command::Trim {
                selected: input.checkpoint()?,
                through: input.cut()?,
            },
            10 => Command::FundWindow {
                window: input.window()?,
            },
            11 => Command::ProtectRange {
                from: input.u64()?,
                through: input.u64()?,
            },
            27 => Command::ProtectCheckpoint {
                root: input.take()?,
                from: input.u64()?,
                through: input.u64()?,
            },
            12 => Command::ProtectRoot {
                source: input.hold()?,
            },
            13 => Command::Vacate {
                grant: input.grant()?,
            },
            14 => Command::SealCohort {
                expected: input.take()?,
                successor: input.take()?,
            },
            tag @ (15 | 24) => Command::PrepareCheckpoint {
                preparation: input.checkpoint_preparation()?,
                references: (tag == 24).then(|| input.object_names()).transpose()?,
            },
            25 => Command::WithdrawObject {
                object: input.withdrawal()?,
            },
            16 => Command::CloseCheckpoint {
                checkpoint: input.checkpoint()?,
            },
            17 => Command::SettleCheckpoint {
                checkpoint: input.checkpoint()?,
                disposition: input.take()?,
                erasure_floor: input.u64()?,
            },
            18 => Command::DisposeWorker {
                enrollment: input.enrollment()?,
                disposition: input.take()?,
            },
            _ => return Err(Refusal::Invalid),
        };
        if !input.0.is_empty() {
            return Err(Refusal::Invalid);
        }
        Ok(Self {
            placement,
            principal,
            id,
            command,
        })
    }
}

/// The bytes of one chosen decision: the request stamped with the journal
/// time its proposer assigned. The time is outside the request fingerprint,
/// so an exact retry still matches its original receipt.
pub(in crate::ordered) fn encode_decision(time: u64, request: &Request) -> Bytes {
    let body = request.encode();
    let mut output = BytesMut::with_capacity(body.len() + 8);
    output.put_slice(&decision_header(time.to_be_bytes()));
    output.put_slice(&body[1..]);
    output.freeze()
}

pub(in crate::ordered) fn decode_decision(frame: Bytes) -> Result<(u64, Request), Refusal> {
    let time = u64::from_be_bytes(read_decision_time(&frame).ok_or(Refusal::Invalid)?);
    let mut body = BytesMut::with_capacity(frame.len() - 8);
    body.put_slice(&frame[..1]);
    body.put_slice(&frame[9..]);
    Ok((time, Request::decode(body.freeze())?))
}

impl BarrierClaim {
    /// Parses a claim. The receiver still authenticates the original bytes
    /// against the installed journal scope before relying on their contents.
    pub fn decode(frame: Bytes) -> Result<Self, Refusal> {
        let mut input = Input(frame);
        if &input.take::<8>()? != BARRIER_DOMAIN {
            return Err(Refusal::Invalid);
        }
        let placement = input.placement()?;
        let owner = input.enrollment()?;
        let id = input.request_id()?;
        let admitted_at = input.u64()?;
        let checkpoint = input.checkpoint()?;
        let through = input.cut()?;
        if !input.0.is_empty()
            || checkpoint.cut.next_lsn > through.next_lsn
            || (checkpoint.cut.next_lsn == through.next_lsn && checkpoint.cut != through)
            || admitted_at == 0
            || admitted_at >= id.expires_at
        {
            return Err(Refusal::Invalid);
        }
        Ok(Self {
            placement,
            read: Hold {
                id,
                owner,
                admitted_at,
                checkpoint,
                start: checkpoint.cut,
                through,
            },
        })
    }
}

struct Input(Bytes);

impl Input {
    fn take<const N: usize>(&mut self) -> Result<[u8; N], Refusal> {
        if self.0.len() < N {
            return Err(Refusal::Invalid);
        }
        self.0
            .split_to(N)
            .as_ref()
            .try_into()
            .map_err(|_| Refusal::Invalid)
    }

    fn append_class(&mut self) -> Result<AppendClass, Refusal> {
        match self.read_byte()? {
            0 => Ok(AppendClass::Data),
            1 => Ok(AppendClass::Maintenance),
            _ => Err(Refusal::Invalid),
        }
    }

    fn read_byte(&mut self) -> Result<u8, Refusal> {
        Ok(self.take::<1>()?[0])
    }
    fn uuid(&mut self) -> Result<Uuid, Refusal> {
        Ok(Uuid::from_bytes(self.take()?))
    }
    fn u64(&mut self) -> Result<u64, Refusal> {
        Ok(u64::from_be_bytes(self.take()?))
    }

    fn request_id(&mut self) -> Result<RequestId, Refusal> {
        Ok(RequestId {
            nonce: self.uuid()?,
            expires_at: self.u64()?,
        })
    }

    fn principal(&mut self) -> Result<Principal, Refusal> {
        match self.read_byte()? {
            0 => Ok(Principal::Administrator),
            1 => Ok(Principal::Worker(self.enrollment()?)),
            2 => Ok(Principal::Custodian),
            3 => Ok(Principal::RouteReader),
            _ => Err(Refusal::Invalid),
        }
    }

    fn placement(&mut self) -> Result<Placement, Refusal> {
        Ok(Placement {
            deployment: self.uuid()?,
            incarnation: self.uuid()?,
            group: self.uuid()?,
            generation: self.u64()?,
        })
    }

    fn enrollment(&mut self) -> Result<Enrollment, Refusal> {
        Ok(Enrollment {
            worker: self.uuid()?,
            serial: self.u64()?,
        })
    }

    fn grant(&mut self) -> Result<Grant, Refusal> {
        Ok(Grant {
            enrollment: self.enrollment()?,
            epoch: self.u64()?,
            key_generation: self.u64()?,
        })
    }

    fn writer_state(&mut self) -> Result<WriterState, Refusal> {
        Ok(WriterState {
            epoch: self.u64()?,
            grant: self.optional(Self::grant)?,
        })
    }

    fn hold(&mut self) -> Result<Hold, Refusal> {
        Ok(Hold {
            id: self.request_id()?,
            owner: self.enrollment()?,
            admitted_at: self.u64()?,
            checkpoint: self.checkpoint()?,
            start: self.cut()?,
            through: self.cut()?,
        })
    }

    fn cut(&mut self) -> Result<Cut, Refusal> {
        let next_lsn = self.u64()?;
        let history: Fingerprint = self.take()?;
        Ok(Cut { next_lsn, history })
    }

    fn checkpoint_preparation(&mut self) -> Result<CheckpointPreparation, Refusal> {
        Ok(CheckpointPreparation {
            erasure: match self.read_byte()? {
                0 => false,
                1 => true,
                _ => return Err(Refusal::Invalid),
            },
            checkpoint: self.cut()?,
            root: self.take()?,
            source: self.grant()?,
            base: self.checkpoint()?,
            custody: Custody {
                allocation: self.uuid()?,
                revision: self.u64()?,
                provider: self.take()?,
            },
            usable_bytes: self.u64()?,
            descriptor: self.take()?,
        })
    }

    fn checkpoint(&mut self) -> Result<Checkpoint, Refusal> {
        Ok(Checkpoint {
            cut: self.cut()?,
            root: self.take()?,
            manifest: self.take()?,
            custody: Custody {
                allocation: self.uuid()?,
                revision: self.u64()?,
                provider: self.take()?,
            },
        })
    }

    fn window(&mut self) -> Result<Window, Refusal> {
        Ok(Window {
            allocation: self.uuid()?,
            serial: self.u64()?,
            bytes: self.u64()?,
        })
    }

    fn optional<T>(
        &mut self,
        read: impl FnOnce(&mut Self) -> Result<T, Refusal>,
    ) -> Result<Option<T>, Refusal> {
        match decode_flag(self.read_byte()?) {
            Some(false) => Ok(None),
            Some(true) => Ok(Some(read(self)?)),
            None => Err(Refusal::Invalid),
        }
    }
}

fn principal(output: &mut BytesMut, value: Principal) {
    match value {
        Principal::Administrator => output.put_u8(0),
        Principal::Worker(worker) => {
            output.put_u8(1);
            enrollment(output, worker);
        }
        Principal::Custodian => output.put_u8(2),
        Principal::RouteReader => output.put_u8(3),
    }
}

fn grant(output: &mut BytesMut, value: Grant) {
    enrollment(output, value.enrollment);
    output.put_u64(value.epoch);
    output.put_u64(value.key_generation);
}

fn writer_state(output: &mut BytesMut, value: WriterState) {
    output.put_u64(value.epoch);
    output.put_u8(encode_flag(value.grant.is_some()));
    if let Some(authority) = value.grant {
        grant(output, authority);
    }
}

fn hold_row(output: &mut BytesMut, value: Hold) {
    request_id(output, value.id);
    enrollment(output, value.owner);
    output.put_u64(value.admitted_at);
    checkpoint(output, value.checkpoint);
    cut(output, value.start);
    cut(output, value.through);
}

fn checkpoint_preparation(output: &mut BytesMut, item: CheckpointPreparation) {
    output.put_u8(u8::from(item.erasure));
    cut(output, item.checkpoint);
    output.put_slice(&item.root);
    grant(output, item.source);
    checkpoint(output, item.base);
    uuid(output, item.custody.allocation);
    output.put_u64(item.custody.revision);
    output.put_slice(&item.custody.provider);
    output.put_u64(item.usable_bytes);
    output.put_slice(&item.descriptor);
}

fn window(output: &mut BytesMut, value: Window) {
    uuid(output, value.allocation);
    output.put_u64(value.serial);
    output.put_u64(value.bytes);
}

fn object_names(output: &mut BytesMut, names: &[ObjectName]) {
    output.put_u32(names.len() as u32);
    for name in names {
        output.put_slice(name);
    }
}

fn withdrawal(output: &mut BytesMut, item: ObjectWithdrawal) {
    output.put_slice(&item.name);
    output.put_slice(&item.version);
}

impl Input {
    fn object_names(&mut self) -> Result<Vec<ObjectName>, Refusal> {
        let declared = u32::from_be_bytes(self.take()?);
        let count = object_name_count(declared, MAX_OBJECT_REFERENCES, self.0.len())
            .ok_or(Refusal::Invalid)?;
        let names = (0..count)
            .map(|_| self.take())
            .collect::<Result<Vec<_>, _>>()?;
        if !valid_object_names(&names) {
            return Err(Refusal::Invalid);
        }
        Ok(names)
    }

    fn withdrawal(&mut self) -> Result<ObjectWithdrawal, Refusal> {
        let item = ObjectWithdrawal {
            name: self.take()?,
            version: self.take()?,
        };
        if item.name == [0; 32] || item.version == [0; 32] {
            return Err(Refusal::Invalid);
        }
        Ok(item)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(command: Command) -> Request {
        Request {
            placement: Placement {
                deployment: Uuid::from_u128(1),
                incarnation: Uuid::from_u128(2),
                group: Uuid::from_u128(3),
                generation: 1,
            },
            principal: Principal::Administrator,
            id: RequestId {
                nonce: Uuid::from_u128(4),
                expires_at: 10,
            },
            command,
        }
    }

    #[test]
    fn fixed_enroll_command_and_decision_reject_every_prefix_and_an_extra_byte() {
        let command = request(Command::Enroll {
            worker: Uuid::from_u128(5),
            expected: None,
        });
        let time = 0x0123_4567_89ab_cdef;
        let request_frame = command.encode();
        let decision_frame = encode_decision(time, &command);
        assert_eq!(Request::decode(request_frame.clone()).unwrap(), command);
        assert_eq!(
            decode_decision(decision_frame.clone()).unwrap(),
            (time, command)
        );
        for end in 0..request_frame.len() {
            assert_eq!(
                Request::decode(request_frame.slice(..end)),
                Err(Refusal::Invalid)
            );
        }
        for end in 0..decision_frame.len() {
            assert_eq!(
                decode_decision(decision_frame.slice(..end)),
                Err(Refusal::Invalid)
            );
        }
        let mut extra = request_frame.to_vec();
        extra.push(0);
        assert_eq!(Request::decode(extra.into()), Err(Refusal::Invalid));
        let mut extra = decision_frame.to_vec();
        extra.push(0);
        assert_eq!(decode_decision(extra.into()), Err(Refusal::Invalid));

        let mut invalid_marker = request_frame.to_vec();
        *invalid_marker.last_mut().unwrap() = 2;
        assert_eq!(
            Request::decode(invalid_marker.into()),
            Err(Refusal::Invalid)
        );
    }

    #[test]
    fn append_payload_uses_all_remaining_command_and_decision_bytes() {
        let append = |payload: &'static [u8]| {
            let enrollment = Enrollment {
                worker: Uuid::from_u128(5),
                serial: 1,
            };
            let mut request = request(Command::Append {
                class: AppendClass::Data,
                grant: Grant {
                    enrollment,
                    epoch: 1,
                    key_generation: 1,
                },
                expected_next: 0,
                timestamp: 7,
                payload: Bytes::from_static(payload),
                references: None,
            });
            request.principal = Principal::Worker(enrollment);
            request
        };
        let short = append(b"a");
        let original = append(b"ab");
        let long = append(b"abc");
        let time = 17;
        let frame = original.encode();
        let decision = encode_decision(time, &original);

        let short_frame = frame.slice(..frame.len() - 1);
        let short_decision = decision.slice(..decision.len() - 1);
        assert_eq!(short_frame, short.encode());
        assert_eq!(short_decision, encode_decision(time, &short));
        assert_eq!(Request::decode(short_frame).unwrap(), short);
        assert_eq!(decode_decision(short_decision).unwrap(), (time, short));

        let mut extra = frame.to_vec();
        extra.push(b'c');
        let mut extra_decision = decision.to_vec();
        extra_decision.push(b'c');
        assert_eq!(extra, long.encode());
        assert_eq!(extra_decision, encode_decision(time, &long));
        assert_eq!(Request::decode(extra.into()).unwrap(), long);
        assert_eq!(
            decode_decision(extra_decision.into()).unwrap(),
            (time, long)
        );
    }
}
