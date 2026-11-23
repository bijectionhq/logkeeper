//! Bounded application RPC on a channel authenticated for an installed group.

use super::{Coordinator, Error, ReplayHead, ReplayPage, Route, Session};
use crate::ordered::{
    AppendResult, BarrierClaim, Command, Cut, Fingerprint, Grant, Hold, Placement, Receipt,
    Refusal, Request, append_fingerprint, replication::Replica,
};
use bytes::Bytes;
use std::io;
use std::time::Duration;
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt};
use tokio::time::timeout;

const MAGIC: &[u8; 8] = b"LKAPPC01";
const REPLAY_OVERHEAD: usize = 1 + 128 + 40 + 8;

#[derive(Clone)]
pub enum Operation {
    Route,
    Execute(Request),
    Reconcile {
        grant: Grant,
        original: Request,
    },
    Replay {
        hold: Hold,
        from: Cut,
        maximum_bytes: u64,
    },
    ReplayHead {
        hold: Hold,
        from: Cut,
    },
}

pub enum Reply {
    Route(Route),
    Decision(Decision),
    Reconciled(AppendResult),
    Replay(ReplayPage),
    ReplayHead(Option<ReplayHead>),
    Refused(Refusal),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Signature {
    pub issuer: Fingerprint,
    pub proof: [u8; 64],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SignedBarrier {
    pub claim: BarrierClaim,
    pub signature: Signature,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Decision {
    pub receipt: Receipt,
    pub barrier: Option<SignedBarrier>,
}

#[derive(Debug, thiserror::Error)]
pub enum WireError {
    #[error(transparent)]
    Service(#[from] Error),
    #[error(transparent)]
    Io(#[from] io::Error),
    #[error("invalid ordered application frame")]
    Frame,
    #[error("ordered application exchange timed out")]
    Timeout,
}

/// The caller retains request identities across lost replies and dial retry.
pub async fn exchange(
    mut channel: impl AsyncRead + AsyncWrite + Unpin,
    placement: Placement,
    operation: Operation,
    maximum_frame: usize,
    deadline: Duration,
) -> Result<Reply, WireError> {
    timeout(deadline, async {
        write_frame(&mut channel, operation.encode(placement), maximum_frame).await?;
        let frame = read_frame(&mut channel, maximum_frame).await?;
        let reply = Reply::decode(frame).map_err(|_| WireError::Frame)?;
        if !reply.matches(placement, &operation) {
            return Err(WireError::Frame);
        }
        Ok(reply)
    })
    .await
    .map_err(|_| WireError::Timeout)?
}

/// The accepting listener supplies an authenticated session and owns
/// connection and workspace reservations before invoking this exchange.
pub async fn serve<R: Replica>(
    coordinator: &Coordinator<R>,
    mut channel: impl AsyncRead + AsyncWrite + Unpin,
    session: Session,
    maximum_frame: usize,
    deadline: Duration,
    sign: impl FnOnce(BarrierClaim) -> io::Result<Signature>,
) -> Result<(), WireError> {
    timeout(deadline, async {
        let frame = read_frame(&mut channel, maximum_frame).await?;
        let (placement, operation) = Operation::decode(frame).map_err(|_| WireError::Frame)?;
        if placement != session.placement {
            let reply = Reply::Refused(Refusal::WrongPlacement);
            return write_frame(&mut channel, reply.encode(), maximum_frame).await;
        }
        let outcome = match operation {
            Operation::Route => coordinator.route(session).await.map(Reply::Route),
            Operation::Execute(request) => match coordinator.execute(session, request).await {
                Ok(decision) => {
                    let barrier = decision
                        .barrier
                        .map(|claim| {
                            Ok::<_, io::Error>(SignedBarrier {
                                claim,
                                signature: sign(claim)?,
                            })
                        })
                        .transpose()?;
                    Ok(Reply::Decision(Decision {
                        receipt: decision.receipt,
                        barrier,
                    }))
                }
                Err(error) => Err(error),
            },
            Operation::Reconcile { grant, original } => coordinator
                .reconcile(session, grant, &original)
                .await
                .map(Reply::Reconciled),
            Operation::Replay {
                hold,
                from,
                maximum_bytes,
            } => {
                let offered = usize::try_from(maximum_bytes).unwrap_or(usize::MAX);
                let limit = maximum_frame
                    .checked_sub(REPLAY_OVERHEAD)
                    .ok_or(WireError::Frame)?;
                coordinator
                    .replay(session, hold, from, offered.min(limit))
                    .await
                    .map(Reply::Replay)
            }
            Operation::ReplayHead { hold, from } => coordinator
                .replay_head(session, hold, from)
                .await
                .map(Reply::ReplayHead),
        };
        let reply = match outcome {
            Ok(reply) => reply,
            Err(Error::Refused(refusal)) => Reply::Refused(refusal),
            Err(error) => return Err(error.into()),
        };
        write_frame(&mut channel, reply.encode(), maximum_frame).await
    })
    .await
    .map_err(|_| WireError::Timeout)?
}

impl Reply {
    fn matches(&self, placement: Placement, operation: &Operation) -> bool {
        match (self, operation) {
            (Self::Route(route), Operation::Route) => route.placement == placement,
            (Self::Decision(decision), Operation::Execute(request)) => {
                decision.receipt.placement == placement
                    && decision.receipt.principal == request.principal
                    && decision.receipt.request == request.id
            }
            (Self::Reconciled(result), Operation::Reconcile { original, .. }) => {
                matches!(&original.command, Command::Append { expected_next, .. } if result.lsn == *expected_next)
            }
            (Self::Replay(page), Operation::Replay { hold, from, .. }) => {
                if page.checkpoint != hold.checkpoint || page.through != hold.through {
                    return false;
                }
                let mut previous = *from;
                for record in &page.records {
                    let result = record.result;
                    if result.lsn != previous.next_lsn
                        || result.lsn.checked_add(1) != Some(result.cut.next_lsn)
                        || result.cut.history
                            != append_fingerprint(
                                previous,
                                record.grant,
                                record.request,
                                record.timestamp,
                                &record.payload,
                            )
                    {
                        return false;
                    }
                    previous = result.cut;
                }
                previous == hold.through
                    || (!page.records.is_empty() && previous.next_lsn < hold.through.next_lsn)
            }
            (Self::ReplayHead(head), Operation::ReplayHead { hold, from }) => match head {
                Some(head) => {
                    from.next_lsn.checked_add(1) == Some(head.next.next_lsn)
                        && head.next.next_lsn <= hold.through.next_lsn
                }
                None => *from == hold.through,
            },
            (Self::Refused(_), _) => true,
            _ => false,
        }
    }
}

async fn read_frame(
    channel: &mut (impl AsyncRead + Unpin),
    limit: usize,
) -> Result<Bytes, WireError> {
    let mut magic = [0; MAGIC.len()];
    channel.read_exact(&mut magic).await?;
    if &magic != MAGIC {
        return Err(WireError::Frame);
    }
    let length = channel.read_u32().await? as usize;
    if length == 0 || length > limit {
        return Err(WireError::Frame);
    }
    let mut body = vec![0; length];
    channel.read_exact(&mut body).await?;
    Ok(Bytes::from(body))
}

async fn write_frame(
    channel: &mut (impl AsyncWrite + Unpin),
    bytes: Bytes,
    limit: usize,
) -> Result<(), WireError> {
    let size = u32::try_from(bytes.len()).map_err(|_| WireError::Frame)?;
    if bytes.is_empty() || bytes.len() > limit {
        return Err(WireError::Frame);
    }
    channel.write_all(MAGIC).await?;
    channel.write_u32(size).await?;
    channel.write_all(&bytes).await?;
    channel.flush().await?;
    Ok(())
}
