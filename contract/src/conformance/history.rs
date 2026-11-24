//! History checks with real-time ordering and committed keeper read snapshots.

use super::{Clients, LIMITS, Schedule};
use crate::{
    BoxFuture, Epoch, Identity, Journal, JournalError, Lsn, Page, Result, StreamId,
    reference::Limits,
};
use bytes::Bytes;
use std::{
    collections::{BTreeMap, HashSet},
    future::poll_fn,
    task::Poll,
    time::Duration,
};

#[derive(Clone, Debug)]
pub enum Op {
    Create,
    Seal(Epoch),
    Append(Epoch, Lsn, Bytes),
    Read(Lsn, usize),
    Head,
    Trim(Epoch, Lsn),
    Delete,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Unit,
    Position(Lsn),
    Page(Page),
}

#[derive(Debug)]
/// One journal operation with invocation and response in a common event order.
pub struct Call {
    pub identity: Identity,
    pub op: Op,
    pub invocation: usize,
    pub response: usize,
    pub result: Result<Value>,
}

impl Op {
    pub fn call<'a>(
        &self,
        journal: &'a dyn Journal,
        stream: StreamId,
    ) -> BoxFuture<'a, Result<Value>> {
        match *self {
            Op::Create => unit(journal.create(stream)),
            Op::Seal(epoch) => position(journal.seal(stream, epoch)),
            Op::Append(epoch, at, ref payload) => {
                position(journal.append(stream, epoch, at, payload.clone()))
            }
            Op::Read(from, max) => {
                let call = journal.read(stream, from, max, Duration::ZERO);
                Box::pin(async move { call.await.map(Value::Page) })
            }
            Op::Head => position(journal.head(stream)),
            Op::Trim(epoch, through) => unit(journal.trim(stream, epoch, through)),
            Op::Delete => unit(journal.delete(stream)),
        }
    }
}

fn unit(call: BoxFuture<'_, Result<()>>) -> BoxFuture<'_, Result<Value>> {
    Box::pin(async move { call.await.map(|()| Value::Unit) })
}

fn position(call: BoxFuture<'_, Result<Lsn>>) -> BoxFuture<'_, Result<Value>> {
    Box::pin(async move { call.await.map(Value::Position) })
}

pub(super) struct History {
    stream: StreamId,
    calls: Vec<Call>,
    clock: usize,
}

impl History {
    pub(super) fn new(stream: StreamId) -> Self {
        Self {
            stream,
            calls: Vec::new(),
            clock: 0,
        }
    }

    pub(super) async fn round(
        &mut self,
        clients: &Clients,
        operations: impl IntoIterator<Item = (usize, Op)>,
        schedule: &mut Schedule,
    ) -> Vec<Result<Value>> {
        let stream = self.stream;
        let mut future_calls = Vec::new();
        for (client, op) in operations {
            let identity = Clients::identity(client);
            let invocation = self.clock;
            self.clock += 1;
            let future = op.call(&*clients.0[client], stream);
            future_calls.push((identity, op, invocation, future, None));
        }

        let mut order: Vec<_> = (0..future_calls.len()).collect();
        let mut remaining = order.len();
        poll_fn(|cx| {
            schedule.shuffle(&mut order);
            for &index in &order {
                let (_, _, _, future, response) = &mut future_calls[index];
                if response.is_none()
                    && let Poll::Ready(result) = future.as_mut().poll(cx)
                {
                    *response = Some((self.clock, result));
                    self.clock += 1;
                    remaining -= 1;
                }
            }
            if remaining == 0 {
                Poll::Ready(())
            } else {
                Poll::Pending
            }
        })
        .await;

        future_calls
            .into_iter()
            .map(|(identity, op, invocation, _, response)| {
                let (response, result) = response.unwrap();
                self.calls.push(Call {
                    identity,
                    op,
                    invocation,
                    response,
                    result: result.clone(),
                });
                result
            })
            .collect()
    }

    pub(super) fn check(&self, name: &str) {
        assert!(
            linearizable(&self.calls, LIMITS),
            "{name}: stream {:?} has no legal order for {:#?}",
            self.stream,
            self.calls
        );
    }
}

// Each operation may linearize at any point in its interval. Pick an
// operation whose real-time predecessors are placed, step the independent
// sequential model, and backtrack when its response disagrees. Memoize dead
// ends by the placed set and model state, not by the order used to reach them.
/// Checks a single stream's history of at most 63 calls.
/// An unavailable mutation may have no effect or may complete after its reply.
pub fn linearizable(calls: &[Call], limits: Limits) -> bool {
    assert!(calls.len() < 64);
    let predecessors: Vec<u64> = calls
        .iter()
        .map(|call| {
            calls.iter().enumerate().fold(0, |mask, (index, other)| {
                if other.result != Err(JournalError::Unavailable)
                    && other.response < call.invocation
                {
                    mask | 1 << index
                } else {
                    mask
                }
            })
        })
        .collect();
    let mut search = Search {
        calls,
        predecessors,
        all: (1 << calls.len()) - 1,
        rejected: HashSet::new(),
        limits,
    };
    search.visit(0, Model::Absent)
}

struct Search<'a> {
    calls: &'a [Call],
    predecessors: Vec<u64>,
    all: u64,
    rejected: HashSet<(u64, Model)>,
    limits: Limits,
}

impl Search<'_> {
    fn visit(&mut self, placed: u64, model: Model) -> bool {
        if placed == self.all {
            return true;
        }
        let key = (placed, model);
        if self.rejected.contains(&key) {
            return false;
        }
        for (index, call) in self.calls.iter().enumerate() {
            let bit = 1 << index;
            if placed & bit != 0 || self.predecessors[index] & !placed != 0 {
                continue;
            }
            let mut next = key.1.clone();
            if call.result == Err(JournalError::Unavailable) {
                if self.visit(placed | bit, next.clone()) {
                    return true;
                }
                if matches!(call.op, Op::Read(..) | Op::Head)
                    || next.step(&call.identity, &call.op, self.limits).is_err()
                    || next == key.1
                {
                    continue;
                }
            } else if !next.matches(call, self.limits) {
                continue;
            }
            if self.visit(placed | bit, next) {
                return true;
            }
        }
        self.rejected.insert(key);
        false
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Model {
    Absent,
    Created {
        deleted: bool,
        sealed: Option<(Epoch, Identity)>,
        head: Lsn,
        floor: Lsn,
        committed: BTreeMap<Lsn, (Epoch, Bytes)>,
    },
}

impl Model {
    fn matches(&mut self, call: &Call, limits: Limits) -> bool {
        use JournalError::*;
        let Op::Read(from, max) = call.op else {
            return self.step(&call.identity, &call.op, limits) == call.result;
        };
        match self {
            Self::Absent => call.result == Err(NotFound),
            Self::Created {
                head,
                floor,
                committed,
                deleted,
                ..
            } => match &call.result {
                Ok(Value::Page(page)) => {
                    page.head <= *head
                        && page.floor <= *floor
                        && page.floor <= from
                        && page.floor.0 > 0
                        && page.floor.0 - 1 <= page.head.0
                        && page
                            .records
                            .iter()
                            .map(|(lsn, payload)| (*lsn, payload))
                            .eq(committed
                                .range(from..)
                                .take_while(|(lsn, _)| **lsn <= page.head)
                                .take(max)
                                .map(|(&lsn, (_, payload))| (lsn, payload)))
                }
                Err(Deleted) => *deleted,
                Err(Trimmed { floor: observed }) => from < *observed && *observed <= *floor,
                _ => false,
            },
        }
    }

    fn step(&mut self, caller: &Identity, op: &Op, limits: Limits) -> Result<Value> {
        use JournalError::*;
        if matches!(self, Self::Created { deleted: true, .. }) {
            return if matches!(op, Op::Delete) {
                Ok(Value::Unit)
            } else {
                Err(Deleted)
            };
        }
        if matches!(op, Op::Create) {
            if matches!(self, Self::Absent) {
                *self = Self::Created {
                    deleted: false,
                    sealed: None,
                    head: Lsn(0),
                    floor: Lsn(1),
                    committed: BTreeMap::new(),
                };
            }
            return Ok(Value::Unit);
        }
        let Self::Created {
            deleted,
            sealed,
            head,
            floor,
            committed,
        } = self
        else {
            return Err(NotFound);
        };
        let fence = Fenced {
            current: sealed.as_ref().map_or(Epoch(0), |(epoch, _)| *epoch),
        };
        let conflict = Conflict { head: *head };
        match op {
            Op::Create => unreachable!(),
            Op::Delete => {
                *deleted = true;
                Ok(Value::Unit)
            }
            Op::Seal(epoch) => {
                if let Some((current, owner)) = sealed.as_ref()
                    && (epoch < current || (epoch == current && caller != owner))
                {
                    return Err(fence);
                }
                *sealed = Some((*epoch, caller.clone()));
                Ok(Value::Position(*head))
            }
            Op::Append(epoch, at, payload) => {
                if !sealed
                    .as_ref()
                    .is_some_and(|(current, owner)| current == epoch && owner == caller)
                {
                    return Err(fence);
                }
                if at < floor {
                    return Err(Trimmed { floor: *floor });
                }
                if at.0 == head.0 + 1 {
                    if payload.len() > limits.max_record_bytes {
                        return Err(TooLarge {
                            max: limits.max_record_bytes,
                        });
                    }
                    let bytes = committed
                        .range(*floor..)
                        .map(|(_, (_, record))| record.len() as u64)
                        .sum::<u64>();
                    if bytes + payload.len() as u64 > limits.stream_quota_bytes {
                        return Err(Full { floor: *floor });
                    }
                    committed.insert(*at, (*epoch, payload.clone()));
                    *head = *at;
                } else if committed.get(at) != Some(&(*epoch, payload.clone())) {
                    return Err(conflict);
                }
                Ok(Value::Position(*at))
            }
            Op::Read(..) => unreachable!("reads use a keeper snapshot"),
            Op::Head => Ok(Value::Position(*head)),
            Op::Trim(epoch, through) => {
                if !sealed
                    .as_ref()
                    .is_some_and(|(current, owner)| current == epoch && owner == caller)
                {
                    return Err(fence);
                }
                if through > head {
                    return Err(conflict);
                }
                if through >= floor {
                    *floor = Lsn(through.0 + 1);
                }
                Ok(Value::Unit)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unknown_append_may_complete_later_but_cannot_change_its_payload() {
        let identity = Identity::from_static("urn:logkeeper:client:1");
        let chosen = Bytes::from_static(b"chosen");
        let at = Lsn(1);
        let mut calls: Vec<_> = [
            (Op::Create, Ok(Value::Unit)),
            (Op::Seal(Epoch(1)), Ok(Value::Position(Lsn(0)))),
            (
                Op::Append(Epoch(1), at, chosen.clone()),
                Err(JournalError::Unavailable),
            ),
            (Op::Head, Ok(Value::Position(Lsn(0)))),
            (Op::Head, Ok(Value::Position(at))),
            (
                Op::Read(at, 1),
                Ok(Value::Page(Page {
                    floor: at,
                    head: at,
                    records: vec![(at, chosen)],
                })),
            ),
        ]
        .into_iter()
        .enumerate()
        .map(|(index, (op, result))| Call {
            identity: identity.clone(),
            op,
            invocation: 2 * index,
            response: 2 * index + 1,
            result,
        })
        .collect();
        assert!(linearizable(&calls, LIMITS));
        let Ok(Value::Page(page)) = &mut calls.last_mut().unwrap().result else {
            unreachable!()
        };
        page.records[0].1 = Bytes::from_static(b"other");
        assert!(
            !linearizable(&calls, LIMITS),
            "a fault cannot authorize a different record"
        );
    }

    #[test]
    fn witnesses_append_on_either_side_of_a_seal() {
        let old = Identity::from_static("urn:logkeeper:client:1");
        let new = Identity::from_static("urn:logkeeper:client:2");
        let mut calls: Vec<_> = [
            (old.clone(), Op::Create, 0, 1, Ok(Value::Unit)),
            (
                old.clone(),
                Op::Seal(Epoch(1)),
                2,
                3,
                Ok(Value::Position(Lsn(0))),
            ),
            (
                new.clone(),
                Op::Seal(Epoch(2)),
                4,
                7,
                Ok(Value::Position(Lsn(1))),
            ),
            (
                old,
                Op::Append(Epoch(1), Lsn(1), Bytes::from_static(b"a")),
                5,
                6,
                Ok(Value::Position(Lsn(1))),
            ),
            (new.clone(), Op::Head, 8, 9, Ok(Value::Position(Lsn(1)))),
        ]
        .into_iter()
        .map(|(identity, op, invocation, response, result)| Call {
            identity,
            op,
            invocation,
            response,
            result,
        })
        .collect();

        // The first seal reply forces the overlapping append to go first.
        assert!(linearizable(&calls, LIMITS));
        calls[3].invocation = 8;
        calls[3].response = 9;
        calls[4].invocation = 10;
        calls[4].response = 11;
        // Identical replies become impossible once the seal returned first.
        assert!(
            !linearizable(&calls, LIMITS),
            "checker must respect real-time precedence"
        );
        calls[2].result = Ok(Value::Position(Lsn(0)));
        calls[3].result = Err(JournalError::Fenced { current: Epoch(2) });
        calls[4].result = Ok(Value::Position(Lsn(0)));
        assert!(linearizable(&calls, LIMITS));
    }
}
