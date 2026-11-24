//! Proposer transitions driven by invocations, transport outcomes and elapsed time.

pub(super) mod append;
pub(super) mod driver;
pub(super) mod head;
pub(super) mod mutation;
pub(super) mod read;
pub(super) mod recovery;
pub(super) mod sweep;
mod ticket;

use std::time::Duration;

use journal_contract::JournalError;

use super::{
    wire::{KeeperId, Refusal, Reply, Request, TransportError},
    writer::decision::QUORUM,
};

type Response = Result<Reply, TransportError>;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::stream) enum Slot {
    First,
    Second,
    Third,
}

impl Slot {
    const ALL: [Self; 3] = [Self::First, Self::Second, Self::Third];
}

pub(in crate::stream) struct Send {
    slot: Slot,
    keeper: KeeperId,
    request: Request,
    /// Deadline relative to the invocation. Expiration is distinct from transport failure.
    deadline: Option<Duration>,
}

impl Send {
    fn new(slot: Slot, keeper: KeeperId, request: Request) -> Self {
        Self {
            slot,
            keeper,
            request,
            deadline: None,
        }
    }
}

pub(in crate::stream) enum Event {
    Invoke,
    Reply(Slot, Response),
    Expired(Slot),
    Timer,
}

pub(in crate::stream) enum Effects<T> {
    Pending,
    Send(Send),
    CancelAndSend(Send),
    Pair([Send; 2]),
    Round([Send; 3]),
    Sleep(Duration),
    Complete(T),
}

pub(in crate::stream) trait Operation {
    type Output;

    fn advance(&mut self, event: Event, elapsed: Duration) -> Effects<Self::Output>;
    fn exhausted() -> Self::Output;
}

struct Call {
    send: Send,
    ticket: u64,
}

enum Input {
    Invoke,
    Reply(Slot, u64, Response),
    Expired(Slot, u64),
    Timer,
}

enum Dispatch<T> {
    Pending,
    Send(Call),
    CancelAndSend(Call),
    Pair([Call; 2]),
    Round([Call; 3]),
    Sleep(Duration),
    Complete(T),
}

/// A response can advance an operation only once, in the slot of its send.
struct Proposer<O> {
    operation: O,
    next: u64,
    pending: [Option<(u64, Option<Duration>)>; 3],
    started: bool,
    finished: bool,
    wake_at: Option<Duration>,
}

impl<O: Operation> Proposer<O> {
    fn new(operation: O) -> Self {
        Self {
            operation,
            next: 0,
            pending: [None; 3],
            started: false,
            finished: false,
            wake_at: None,
        }
    }

    fn start(&mut self, send: Send) -> Option<Call> {
        let slot = &mut self.pending[send.slot as usize];
        if slot.is_some() {
            return None;
        }
        self.next = ticket::next_ticket(self.next)?;
        *slot = Some((self.next, send.deadline));
        Some(Call {
            send,
            ticket: self.next,
        })
    }

    fn step(&mut self, input: Input, elapsed: Duration) -> Dispatch<O::Output> {
        if self.finished {
            return Dispatch::Pending;
        }
        let event = match input {
            Input::Invoke if !self.started => {
                self.started = true;
                Event::Invoke
            }
            Input::Reply(slot, ticket, response) if self.receive(slot, ticket, None) => {
                Event::Reply(slot, response)
            }
            Input::Expired(slot, ticket) if self.receive(slot, ticket, Some(elapsed)) => {
                Event::Expired(slot)
            }
            Input::Timer if self.wake_at.is_some_and(|wake| elapsed >= wake) => {
                self.wake_at = None;
                Event::Timer
            }
            _ => return Dispatch::Pending,
        };
        match self.operation.advance(event, elapsed) {
            Effects::Pending => Dispatch::Pending,
            Effects::Send(send) => {
                if let Some(call) = self.start(send) {
                    return Dispatch::Send(call);
                }
                self.finish(O::exhausted())
            }
            Effects::CancelAndSend(send) => {
                self.pending = [None; 3];
                if let Some(call) = self.start(send) {
                    return Dispatch::CancelAndSend(call);
                }
                self.finish(O::exhausted())
            }
            Effects::Pair([left, right]) => {
                if let Some(left) = self.start(left)
                    && let Some(right) = self.start(right)
                {
                    return Dispatch::Pair([left, right]);
                }
                self.finish(O::exhausted())
            }
            Effects::Round([first, second, third]) => {
                if let Some(first) = self.start(first)
                    && let Some(second) = self.start(second)
                    && let Some(third) = self.start(third)
                {
                    return Dispatch::Round([first, second, third]);
                }
                self.finish(O::exhausted())
            }
            Effects::Sleep(duration) => {
                self.wake_at = Some(elapsed.saturating_add(duration));
                Dispatch::Sleep(duration)
            }
            Effects::Complete(output) => self.finish(output),
        }
    }

    fn receive(&mut self, slot: Slot, ticket: u64, expires: Option<Duration>) -> bool {
        let pending = &mut self.pending[slot as usize];
        let Some((issued, deadline)) = *pending else {
            return false;
        };
        if !ticket::matches_ticket(issued, ticket)
            || expires.is_some_and(|now| deadline.is_none_or(|deadline| now < deadline))
        {
            return false;
        }
        *pending = None;
        true
    }

    fn finish(&mut self, output: O::Output) -> Dispatch<O::Output> {
        self.finished = true;
        Dispatch::Complete(output)
    }
}

fn journal_reply(response: Response) -> journal_contract::Result<Reply> {
    match response {
        Ok(Reply::Refused(refusal)) => Err(map_refusal(refusal)),
        Ok(reply) => Ok(reply),
        Err(_) => Err(JournalError::Unavailable),
    }
}

pub(in crate::stream) fn map_refusal(refusal: Refusal) -> JournalError {
    match refusal {
        Refusal::Fenced { promised } => JournalError::Fenced { current: promised },
        Refusal::Gap { head } | Refusal::Conflict { head } | Refusal::AboveHead { head } => {
            JournalError::Conflict { head }
        }
        Refusal::BelowFloor { floor } => JournalError::Trimmed { floor },
        Refusal::Full { floor } => JournalError::Full { floor },
        Refusal::TooLarge { max } => JournalError::TooLarge { max: max as usize },
        Refusal::Deleted => JournalError::Deleted,
        Refusal::NotFound => JournalError::NotFound,
        Refusal::NotSynced | Refusal::Unauthorized | Refusal::WrongEnsemble { .. } => {
            JournalError::Unavailable
        }
    }
}

pub(in crate::stream) fn refusal(errors: &[JournalError]) -> JournalError {
    for error in [JournalError::Deleted, JournalError::NotFound] {
        if errors.iter().filter(|seen| **seen == error).count() >= QUORUM {
            return error;
        }
    }
    if let Some(error) = errors.iter().find(|first| {
        !matches!(
            first,
            JournalError::Unavailable | JournalError::Fenced { .. }
        ) && errors
            .iter()
            .filter(|second| std::mem::discriminant(*second) == std::mem::discriminant(*first))
            .count()
            >= QUORUM
    }) {
        return error.clone();
    }
    errors
        .iter()
        .filter_map(|error| match error {
            JournalError::Fenced { current } => Some(*current),
            _ => None,
        })
        .max()
        .map_or(JournalError::Unavailable, |current| JournalError::Fenced {
            current,
        })
}
