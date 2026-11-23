use super::{
    Input, checkpoint, checkpoint_preparation, cut, enrollment, grant, hold_row, placement,
    principal, request_id, snapshot, uuid, window, writer_state,
};
use crate::ordered::RetainedCheckpoint;
use crate::ordered::{
    BarrierClaim, Outcome, Placement, Principal, Receipt, Refusal, Request,
    replication::{Ballot, RotationSlots, SlotImage, SlotPair, VoterSlots},
    service::{
        MAX_WITHDRAWN_WORKERS, ReplayHead, ReplayPage, Route, WithdrawnWorker,
        wire::{Decision, Operation, Reply, Signature, SignedBarrier, SignedRotationSlots},
    },
};
use bytes::{BufMut, Bytes, BytesMut};

impl Operation {
    pub(in crate::ordered) fn encode(&self, scope: Placement) -> Bytes {
        let mut output = BytesMut::new();
        placement(&mut output, scope);
        match self {
            Self::Route => output.put_u8(0),
            Self::Execute(request) => {
                output.put_u8(1);
                output.put_slice(&request.encode());
            }
            Self::Reconcile {
                grant: authority,
                original,
            } => {
                output.put_u8(2);
                grant(&mut output, *authority);
                output.put_slice(&original.encode());
            }
            Self::Replay {
                hold,
                from,
                maximum_bytes,
            } => {
                output.put_u8(3);
                hold_row(&mut output, *hold);
                cut(&mut output, *from);
                output.put_u64(*maximum_bytes);
            }
            Self::CheckpointReplay {
                preparation,
                base,
                from,
                maximum_bytes,
            } => {
                output.put_u8(7);
                checkpoint_preparation(&mut output, *preparation);
                checkpoint(&mut output, *base);
                cut(&mut output, *from);
                output.put_u64(*maximum_bytes);
            }
            Self::InspectCheckpoint {
                base,
                from,
                through,
                maximum_bytes,
            } => {
                output.put_u8(8);
                checkpoint(&mut output, *base);
                cut(&mut output, *from);
                cut(&mut output, *through);
                output.put_u64(*maximum_bytes);
            }
            Self::WithdrawnWorkers { after } => {
                output.put_u8(9);
                output.put_u8(u8::from(after.is_some()));
                if let Some(after) = after {
                    enrollment(&mut output, *after);
                }
            }
            Self::CheckpointCut { next } => {
                output.put_u8(6);
                output.put_u64(*next);
            }
            Self::Release { hold } => {
                output.put_u8(5);
                hold_row(&mut output, *hold);
            }
            Self::ReplayHead { hold, from } => {
                output.put_u8(4);
                hold_row(&mut output, *hold);
                cut(&mut output, *from);
            }
        }
        output.freeze()
    }

    pub(in crate::ordered) fn decode(body: Bytes) -> Result<(Placement, Self), Refusal> {
        let mut input = Input(body);
        let placement = input.placement()?;
        let operation = match input.read_byte()? {
            0 => Self::Route,
            1 => Self::Execute(Request::decode(std::mem::take(&mut input.0))?),
            2 => Self::Reconcile {
                grant: input.grant()?,
                original: Request::decode(std::mem::take(&mut input.0))?,
            },
            3 => Self::Replay {
                hold: input.hold()?,
                from: input.cut()?,
                maximum_bytes: input.u64()?,
            },
            4 => Self::ReplayHead {
                hold: input.hold()?,
                from: input.cut()?,
            },
            5 => Self::Release {
                hold: input.hold()?,
            },
            6 => Self::CheckpointCut { next: input.u64()? },
            7 => Self::CheckpointReplay {
                preparation: input.checkpoint_preparation()?,
                base: input.checkpoint()?,
                from: input.cut()?,
                maximum_bytes: input.u64()?,
            },
            8 => Self::InspectCheckpoint {
                base: input.checkpoint()?,
                from: input.cut()?,
                through: input.cut()?,
                maximum_bytes: input.u64()?,
            },
            9 => Self::WithdrawnWorkers {
                after: input.optional(Input::enrollment)?,
            },
            _ => return Err(Refusal::Invalid),
        };
        input.finish((placement, operation))
    }
}

impl Reply {
    pub(in crate::ordered) fn encode(&self) -> Bytes {
        let mut output = BytesMut::new();
        match self {
            Self::Route(route) => {
                output.put_u8(0);
                placement(&mut output, route.placement);
                writer_state(&mut output, route.writer);
                output.put_u64(route.position);
                output.put_slice(&route.history);
                cut(&mut output, route.head);
                output.put_u8(u8::from(route.last_data.is_some()));
                if let Some(chosen) = route.last_data {
                    cut(&mut output, chosen);
                }
                output.put_u8(u8::from(route.last_maintenance.is_some()));
                if let Some(chosen) = route.last_maintenance {
                    cut(&mut output, chosen);
                }
                cut(&mut output, route.floor);
                output.put_u64(route.erasure_floor);
                checkpoint(&mut output, route.checkpoint);
                output.put_u8(u8::from(route.preparing.is_some()));
                if let Some(item) = route.preparing {
                    checkpoint_preparation(&mut output, item);
                }
                output.put_u8(u8::from(route.retirement.is_some()));
                if let Some(item) = route.retirement {
                    checkpoint(&mut output, item.checkpoint);
                    output.put_u8(u8::from(item.closed));
                }
                window(&mut output, route.window);
                output.put_u64(route.window_spent);
                output.put_u64(route.reusable_bytes);
                output.put_u64(route.ordinary_limit);
                output.put_u64(route.maintenance_limit);
                output.put_u64(route.maintenance_retained);
                output.put_u64(route.retry_positions);
                output.put_u64(route.time);
                output.put_u64(route.serving_lease);
                output.put_u64(route.clock_drift);
            }
            Self::Decision(decision) => {
                if let Some(proof) = &decision.rotation {
                    output.put_u8(9);
                    receipt(&mut output, decision.receipt);
                    output.put_slice(&proof.signature.issuer);
                    output.put_slice(&proof.signature.proof);
                    proof.evidence.encode(&mut output);
                } else {
                    output.put_u8(1);
                    receipt(&mut output, decision.receipt);
                    output.put_u8(u8::from(decision.barrier.is_some()));
                    if let Some(barrier) = decision.barrier {
                        output.put_slice(&barrier.signature.issuer);
                        output.put_slice(&barrier.signature.proof);
                        output.put_slice(&barrier.claim.encode());
                    }
                }
            }
            Self::Reconciled(append) => {
                output.put_u8(2);
                snapshot::append_result(&mut output, *append);
            }
            Self::Replay(page) => {
                output.put_u8(3);
                checkpoint(&mut output, page.checkpoint);
                cut(&mut output, page.through);
                output.put_u64(page.records.len() as u64);
                for record in &page.records {
                    snapshot::record(&mut output, record);
                }
            }
            Self::Refused(refusal) => {
                output.put_u8(4);
                snapshot::result(&mut output, Err(*refusal));
            }
            Self::CheckpointCut(selected) => {
                output.put_u8(7);
                cut(&mut output, *selected);
            }
            Self::WithdrawnWorkers(workers) => {
                output.put_u8(8);
                output.put_u8(workers.len() as u8);
                for worker in workers {
                    enrollment(&mut output, worker.enrollment);
                    output.put_u8(u8::from(worker.eligible_at.is_some()));
                    if let Some(time) = worker.eligible_at {
                        output.put_u64(time);
                    }
                }
            }
            Self::Released(hold) => {
                output.put_u8(6);
                hold_row(&mut output, *hold);
            }
            Self::ReplayHead(head) => {
                output.put_u8(5);
                output.put_u8(u8::from(head.is_some()));
                if let Some(head) = head {
                    cut(&mut output, head.next);
                    output.put_i64(head.timestamp);
                    output.put_u64(head.payload_bytes);
                    output.put_u64(head.record_bytes);
                }
            }
        }
        output.freeze()
    }

    pub(in crate::ordered) fn decode(body: Bytes) -> Result<Self, Refusal> {
        let mut input = Input(body);
        let reply = match input.read_byte()? {
            0 => Self::Route(Route {
                placement: input.placement()?,
                writer: input.writer_state()?,
                position: input.u64()?,
                history: input.take()?,
                head: input.cut()?,
                last_data: input.optional(Input::cut)?,
                last_maintenance: input.optional(Input::cut)?,
                floor: input.cut()?,
                erasure_floor: input.u64()?,
                checkpoint: input.checkpoint()?,
                preparing: input.optional(Input::checkpoint_preparation)?,
                retirement: input.optional(|input| {
                    let checkpoint = input.checkpoint()?;
                    let closed = match input.read_byte()? {
                        0 => false,
                        1 => true,
                        _ => return Err(Refusal::Invalid),
                    };
                    Ok(RetainedCheckpoint { checkpoint, closed })
                })?,
                window: input.window()?,
                window_spent: input.u64()?,
                reusable_bytes: input.u64()?,
                ordinary_limit: input.u64()?,
                maintenance_limit: input.u64()?,
                maintenance_retained: input.u64()?,
                retry_positions: input.u64()?,
                time: input.u64()?,
                serving_lease: input.u64()?,
                clock_drift: input.u64()?,
            }),
            1 => Self::Decision(input.decision()?),
            2 => Self::Reconciled(input.append_result()?),
            3 => {
                let checkpoint = input.checkpoint()?;
                let through = input.cut()?;
                let mut records = Vec::new();
                for _ in 0..input.count(usize::MAX)? {
                    records.push(input.record()?);
                }
                Self::Replay(ReplayPage {
                    checkpoint,
                    through,
                    records,
                })
            }
            4 => Self::Refused(input.result()?.err().ok_or(Refusal::Invalid)?),
            5 => Self::ReplayHead(input.optional(|input| {
                Ok(ReplayHead {
                    next: input.cut()?,
                    timestamp: i64::from_be_bytes(input.take()?),
                    payload_bytes: input.u64()?,
                    record_bytes: input.u64()?,
                })
            })?),
            6 => Self::Released(input.hold()?),
            7 => Self::CheckpointCut(input.cut()?),
            8 => {
                let count = usize::from(input.read_byte()?);
                if count > MAX_WITHDRAWN_WORKERS {
                    return Err(Refusal::Invalid);
                }
                let mut workers = Vec::with_capacity(count);
                for _ in 0..count {
                    workers.push(WithdrawnWorker {
                        enrollment: input.enrollment()?,
                        eligible_at: input.optional(Input::u64)?,
                    });
                }
                Self::WithdrawnWorkers(workers)
            }
            9 => Self::Decision(input.rotation_decision()?),
            _ => return Err(Refusal::Invalid),
        };
        input.finish(reply)
    }
}

fn receipt(output: &mut BytesMut, receipt: Receipt) {
    placement(output, receipt.placement);
    principal(output, receipt.principal);
    request_id(output, receipt.request);
    output.put_u64(receipt.position);
    snapshot::result(output, receipt.outcome);
}

impl RotationSlots {
    pub(in crate::ordered) fn signing_bytes(&self, decision: Receipt) -> Bytes {
        let mut output = BytesMut::new();
        output.put_slice(b"logkeeper.ordered-rotation-slots.v1");
        receipt(&mut output, decision);
        self.encode(&mut output);
        output.freeze()
    }

    fn encode(&self, output: &mut BytesMut) {
        output.put_slice(&self.group);
        output.put_u64(self.cohort_size as u64);
        output.put_u64(self.ballot.round);
        uuid(output, self.ballot.nonce);
        output.put_slice(&self.prefix);
        output.put_u64(self.position);
        checkpoint(output, self.checkpoint);
        output.put_u64(self.key_generation);
        output.put_u64(self.voters.len() as u64);
        for voter in &self.voters {
            uuid(output, voter.voter);
            output.put_u8(voter.slots.selected);
            for image in voter.slots.images {
                output.put_u64(image.generation);
                output.put_slice(&image.digest);
            }
        }
    }
}

impl Input {
    fn receipt(&mut self) -> Result<Receipt, Refusal> {
        Ok(Receipt {
            placement: self.placement()?,
            principal: self.principal()?,
            request: self.request_id()?,
            position: self.u64()?,
            outcome: self.result()?,
        })
    }

    fn decision(&mut self) -> Result<Decision, Refusal> {
        let receipt = self.receipt()?;
        let barrier = self.optional(|input| {
            let signature = Signature {
                issuer: input.take()?,
                proof: input.take()?,
            };
            let claim = BarrierClaim::decode(std::mem::take(&mut input.0))?;
            Ok(SignedBarrier { claim, signature })
        })?;
        match (receipt.outcome, barrier) {
            (Ok(Outcome::Barrier { read }), Some(SignedBarrier { claim, .. }))
                if read == claim.read()
                    && receipt.placement == claim.placement()
                    && receipt.principal == Principal::Worker(read.owner)
                    && receipt.request == read.id
                    && receipt.position == read.admitted_at => {}
            (Ok(Outcome::Barrier { .. }), _) | (_, Some(_)) => return Err(Refusal::Invalid),
            (_, None) => {}
        }
        Ok(Decision {
            receipt,
            barrier,
            rotation: None,
        })
    }

    fn rotation_decision(&mut self) -> Result<Decision, Refusal> {
        let receipt = self.receipt()?;
        let signature = Signature {
            issuer: self.take()?,
            proof: self.take()?,
        };
        let mut evidence = RotationSlots {
            group: self.take()?,
            cohort_size: usize::try_from(self.u64()?).map_err(|_| Refusal::Invalid)?,
            ballot: Ballot {
                round: self.u64()?,
                nonce: self.uuid()?,
            },
            prefix: self.take()?,
            position: self.u64()?,
            checkpoint: self.checkpoint()?,
            key_generation: self.u64()?,
            voters: Vec::new(),
        };
        const VOTER_BYTES: usize = 16 + 1 + 2 * (8 + 32);
        let count = self.count(self.0.len().saturating_sub(8) / VOTER_BYTES)?;
        for _ in 0..count {
            let voter = self.uuid()?;
            let selected = self.read_byte()?;
            let mut image = || -> Result<SlotImage, Refusal> {
                Ok(SlotImage {
                    generation: self.u64()?,
                    digest: self.take()?,
                })
            };
            evidence.voters.push(VoterSlots {
                voter,
                slots: SlotPair {
                    selected,
                    images: [image()?, image()?],
                },
            });
        }
        if !evidence.covers(receipt) {
            return Err(Refusal::Invalid);
        }
        Ok(Decision {
            receipt,
            barrier: None,
            rotation: Some(SignedRotationSlots {
                evidence,
                signature,
            }),
        })
    }

    fn finish<T>(self, value: T) -> Result<T, Refusal> {
        self.0.is_empty().then_some(value).ok_or(Refusal::Invalid)
    }
}
