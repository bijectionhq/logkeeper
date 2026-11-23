use super::{
    Input, checkpoint, checkpoint_preparation, cut, grant, hold_row, placement, principal,
    request_id, snapshot, window, writer_state,
};
use crate::ordered::RetainedCheckpoint;
use crate::ordered::{
    BarrierClaim, Outcome, Placement, Principal, Receipt, Refusal, Request,
    service::{
        ReplayHead, ReplayPage, Route,
        wire::{Decision, Operation, Reply, Signature, SignedBarrier},
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
                cut(&mut output, route.floor);
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
                output.put_u64(route.retry_positions);
            }
            Self::Decision(decision) => {
                output.put_u8(1);
                let receipt = decision.receipt;
                placement(&mut output, receipt.placement);
                principal(&mut output, receipt.principal);
                request_id(&mut output, receipt.request);
                output.put_u64(receipt.position);
                snapshot::result(&mut output, receipt.outcome);
                output.put_u8(u8::from(decision.barrier.is_some()));
                if let Some(barrier) = decision.barrier {
                    output.put_slice(&barrier.signature.issuer);
                    output.put_slice(&barrier.signature.proof);
                    output.put_slice(&barrier.claim.encode());
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
                floor: input.cut()?,
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
                retry_positions: input.u64()?,
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
                })
            })?),
            6 => Self::Released(input.hold()?),
            _ => return Err(Refusal::Invalid),
        };
        input.finish(reply)
    }
}

impl Input {
    fn decision(&mut self) -> Result<Decision, Refusal> {
        let receipt = Receipt {
            placement: self.placement()?,
            principal: self.principal()?,
            request: self.request_id()?,
            position: self.u64()?,
            outcome: self.result()?,
        };
        let barrier = self.optional(|input| {
            let signature = Signature {
                issuer: input.take()?,
                proof: input.take()?,
            };
            let claim = BarrierClaim::decode(std::mem::take(&mut input.0))?;
            Ok(SignedBarrier { claim, signature })
        })?;
        if let Some(SignedBarrier { claim, .. }) = barrier
            && (receipt.outcome
                != Ok(Outcome::Barrier {
                    grant: claim.grant(),
                    nonce: claim.nonce(),
                    read: claim.read(),
                })
                || receipt.placement != claim.placement()
                || receipt.principal != Principal::Worker(claim.grant().enrollment)
                || receipt.request != claim.read().id
                || receipt.position != claim.read().admitted_at)
        {
            return Err(Refusal::Invalid);
        }
        Ok(Decision { receipt, barrier })
    }

    fn finish<T>(self, value: T) -> Result<T, Refusal> {
        self.0.is_empty().then_some(value).ok_or(Refusal::Invalid)
    }
}
