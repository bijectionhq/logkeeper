use super::{
    AppendClass, Checkpoint, CheckpointPreparation, Command, Custody, Cut, Enrollment, Fingerprint,
    Grant, Hold, MAX_OBJECT_REFERENCES, ObjectName, ObjectWithdrawal, Placement, Principal,
    Refusal, Request, RequestId, Window, WriterState, valid_object_names,
};
use bytes::{BufMut, Bytes, BytesMut};
use sha2::{Digest, Sha256};
use uuid::Uuid;

pub(super) mod frame;
mod service;
mod signed;
mod snapshot;
mod snapshot_checks;

use frame::{
    COMMAND_VERSION, decision_header, decision_request_parts, decode_flag, encode_flag,
    has_command_version, object_name_count, read_fixed_field, withdrawal_identity_admissible,
};

use signed::{checkpoint, cut, enrollment, placement, request_id, uuid};

impl Request {
    /// The exact bytes used by ordered replication and crash replay.
    pub fn encode(&self) -> Bytes {
        let mut output = BytesMut::new();
        self.encode_into(&mut output, None);
        output.freeze()
    }

    fn encode_into(&self, output: &mut BytesMut, journal_time: Option<u64>) {
        let payload = self.encode_prefix(output, journal_time);
        output.put_slice(payload);
    }

    // Writes every field except the opaque append tail, which can also be
    // hashed directly from the request.
    fn encode_prefix(&self, output: &mut BytesMut, journal_time: Option<u64>) -> &[u8] {
        if let Some(time) = journal_time {
            output.put_slice(&decision_header(time.to_be_bytes()));
        } else {
            output.put_u8(COMMAND_VERSION);
        }
        placement(output, self.placement);
        principal(output, self.principal);
        request_id(output, self.id);
        match &self.command {
            Command::Enroll { worker, expected } => {
                output.put_u8(0);
                uuid(output, *worker);
                output.put_u8(encode_flag(expected.is_some()));
                if let Some(expected) = expected {
                    enrollment(output, *expected);
                }
            }
            Command::Withdraw { enrollment: worker } => {
                output.put_u8(1);
                enrollment(output, *worker);
            }
            Command::Grant {
                expected,
                candidate,
            } => {
                output.put_u8(2);
                writer_state(output, *expected);
                enrollment(output, *candidate);
            }
            Command::PublishAndRotate {
                grant: writer,
                checkpoint: root,
            } => {
                output.put_u8(22);
                grant(output, *writer);
                checkpoint(output, *root);
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
                grant(output, *writer);
                output.put_u64(*expected_next);
                output.put_i64(*timestamp);
                if let Some(names) = references {
                    object_names(output, names);
                }
                return payload;
            }
            Command::Barrier => output.put_u8(4),
            Command::PrepareCheckpoint {
                preparation,
                references,
            } => {
                output.put_u8(if references.is_some() { 24 } else { 15 });
                checkpoint_preparation(output, *preparation);
                if let Some(names) = references {
                    object_names(output, names);
                }
            }
            Command::WithdrawObject { object } => {
                output.put_u8(25);
                withdrawal(output, *object);
            }
            Command::CloseCheckpoint { checkpoint: root } => {
                output.put_u8(16);
                checkpoint(output, *root);
            }
            Command::SettleCheckpoint {
                checkpoint: root,
                disposition,
                erasure_floor,
            } => {
                output.put_u8(17);
                checkpoint(output, *root);
                output.put_slice(disposition);
                output.put_u64(*erasure_floor);
            }
            Command::DisposeWorker {
                enrollment: worker,
                disposition,
            } => {
                output.put_u8(18);
                enrollment(output, *worker);
                output.put_slice(disposition);
            }
            Command::Publish {
                checkpoint: offered,
            } => {
                output.put_u8(5);
                checkpoint(output, *offered);
            }
            Command::FundWindow { window: allocation } => {
                output.put_u8(10);
                window(output, *allocation);
            }
            Command::Protect {
                grant: writer,
                through,
            } => {
                output.put_u8(6);
                grant(output, *writer);
                cut(output, *through);
            }
            Command::Trim { selected, through } => {
                output.put_u8(8);
                checkpoint(output, *selected);
                cut(output, *through);
            }
            Command::Release { hold } => {
                output.put_u8(7);
                hold_row(output, *hold);
            }
            Command::ReleaseRead { read } => {
                output.put_u8(19);
                request_id(output, *read);
            }
            Command::Lease { grant: writer } => {
                output.put_u8(20);
                grant(output, *writer);
            }
            Command::LeaseRead { hold } => {
                output.put_u8(26);
                hold_row(output, *hold);
            }
            Command::DisposeExpired { enrollment: worker } => {
                output.put_u8(21);
                enrollment(output, *worker);
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
                hold_row(output, *source);
            }
            Command::Vacate { grant: writer } => {
                output.put_u8(13);
                grant(output, *writer);
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
        &[]
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

pub(super) fn fingerprint(request: &Request) -> Fingerprint {
    let mut prefix = BytesMut::new();
    let payload = request.encode_prefix(&mut prefix, None);
    let mut hash = Sha256::new();
    hash.update(b"logkeeper.ordered-request.v1");
    hash.update(&prefix[..]);
    hash.update(payload);
    hash.finalize().into()
}

/// The bytes of one chosen decision: the request stamped with the journal
/// time its proposer assigned. The time is outside the request fingerprint,
/// so an exact retry still matches its original receipt.
pub(in crate::ordered) fn encode_decision(time: u64, request: &Request) -> Bytes {
    let mut output = BytesMut::new();
    request.encode_into(&mut output, Some(time));
    output.freeze()
}

pub(in crate::ordered) fn decode_decision(frame: Bytes) -> Result<(u64, Request), Refusal> {
    let (time, version, fields) = decision_request_parts(&frame).ok_or(Refusal::Invalid)?;
    let mut body = BytesMut::with_capacity(frame.len() - 8);
    body.put_slice(version);
    body.put_slice(fields);
    Ok((u64::from_be_bytes(time), Request::decode(body.freeze())?))
}

struct Input(Bytes);

impl Input {
    fn take<const N: usize>(&mut self) -> Result<[u8; N], Refusal> {
        let field = read_fixed_field(&self.0).ok_or(Refusal::Invalid)?;
        drop(self.0.split_to(N));
        Ok(field)
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
        if !withdrawal_identity_admissible(&item.name, &item.version) {
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
    fn referenced_append_round_trip_requires_increasing_names() {
        let mut command = request(Command::Append {
            class: AppendClass::Data,
            grant: Grant {
                enrollment: Enrollment { worker: Uuid::from_u128(5), serial: 1 },
                epoch: 1,
                key_generation: 1,
            },
            expected_next: 0,
            timestamp: 0,
            payload: Bytes::from_static(b"opaque"),
            references: Some(vec![[2; 32], [1; 32]]),
        });
        assert_eq!(Request::decode(command.encode()), Err(Refusal::Invalid));
        let Command::Append { references: Some(names), .. } = &mut command.command else {
            unreachable!();
        };
        names.reverse();
        assert_eq!(Request::decode(command.encode()), Ok(command));
    }

    #[test]
    fn append_envelopes_keep_the_v9_request_bytes() {
        use crate::ordered::service::wire::Operation;

        let worker = Enrollment {
            worker: Uuid::from_u128(5),
            serial: 6,
        };
        let writer = Grant {
            enrollment: worker,
            epoch: 7,
            key_generation: 8,
        };
        let authority = Grant { epoch: 9, ..writer };
        let payload = b"\x00opaque\xff";
        let time = 0x0123_4567_89ab_cdef_u64;

        let mut placement_bytes = Vec::new();
        for id in 1..=3 {
            placement_bytes.put_u128(id);
        }
        let mut scope_bytes = placement_bytes.clone();
        scope_bytes.put_u64(2);
        placement_bytes.put_u64(1);

        let mut reconcile_prefix = scope_bytes.clone();
        reconcile_prefix.put_u8(2);
        reconcile_prefix.put_u128(5);
        reconcile_prefix.put_u64(6);
        reconcile_prefix.put_u64(9);
        reconcile_prefix.put_u64(8);
        let mut execute_prefix = scope_bytes;
        execute_prefix.put_u8(1);

        let names = [[0x81; 32], [0x93; 32]];
        for (tag, references) in [(3, None), (23, Some(names.as_slice()))] {
            let mut original = request(Command::Append {
                class: AppendClass::Maintenance,
                grant: writer,
                expected_next: 11,
                timestamp: -12,
                payload: Bytes::from_static(payload),
                references: references.map(<[ObjectName]>::to_vec),
            });
            original.principal = Principal::Worker(worker);
            let scope = Placement {
                generation: 2,
                ..original.placement
            };

            let mut expected = vec![9];
            expected.put_slice(&placement_bytes);
            expected.put_u8(1);
            expected.put_u128(5);
            expected.put_u64(6);
            expected.put_u128(4);
            expected.put_u64(10);
            expected.put_slice(&[tag, 1]);
            expected.put_u128(5);
            expected.put_u64(6);
            expected.put_u64(7);
            expected.put_u64(8);
            expected.put_u64(11);
            expected.put_i64(-12);
            if let Some(names) = references {
                expected.put_u32(2);
                for name in names {
                    expected.put_slice(name);
                }
            }
            expected.put_slice(payload);

            let execute = Operation::Execute(original.clone()).encode(scope);
            let reconcile = Operation::Reconcile {
                grant: authority,
                original: original.clone(),
            }
            .encode(scope);
            let decision = encode_decision(time, &original);

            assert_eq!(original.encode().as_ref(), expected.as_slice());
            assert_eq!(
                execute.as_ref(),
                [execute_prefix.as_slice(), &expected].concat().as_slice()
            );
            assert_eq!(
                reconcile.as_ref(),
                [reconcile_prefix.as_slice(), &expected].concat().as_slice()
            );
            assert_eq!(
                decision.as_ref(),
                [&[9][..], &time.to_be_bytes(), &expected[1..]].concat().as_slice()
            );

            let mut hash = Sha256::new();
            hash.update(b"logkeeper.ordered-request.v1");
            hash.update(&expected);
            let expected_fingerprint: Fingerprint = hash.finalize().into();
            assert_eq!(fingerprint(&original), expected_fingerprint);
        }
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
