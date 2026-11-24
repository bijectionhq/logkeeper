//! Quorum completion for Create, Trim and Delete.

use std::time::Duration;

use journal_contract::{Epoch, JournalError, Lsn, Result, StreamId};

use super::{Effects, Event, Operation, Response, Send, Slot, journal_reply, refusal};
use crate::stream::wire::{KeeperId, Reply, Request};

#[derive(Clone, Copy)]
pub(in crate::stream) enum Kind {
    Create,
    Trim { epoch: Epoch, through: Lsn },
    Delete,
}

pub(in crate::stream) struct Mutation {
    kind: Kind,
    stream: StreamId,
    ensemble: [KeeperId; 3],
    first: Option<Lsn>,
    errors: Vec<JournalError>,
}

impl Mutation {
    pub(in crate::stream) fn new(kind: Kind, stream: StreamId, ensemble: [KeeperId; 3]) -> Self {
        Self {
            kind,
            stream,
            ensemble,
            first: None,
            errors: Vec::new(),
        }
    }

    fn send(&self, slot: Slot) -> Send {
        let stream = self.stream;
        let ensemble = self.ensemble;
        let request = match self.kind {
            Kind::Create => Request::Create { stream, ensemble },
            Kind::Delete => Request::Delete { stream, ensemble },
            Kind::Trim { epoch, through } => Request::Trim {
                stream,
                epoch,
                through,
            },
        };
        Send::new(slot, ensemble[slot as usize], request)
    }

    fn receive(&mut self, response: Response) -> Effects<Result<Lsn>> {
        let reply = journal_reply(response).and_then(|reply| match (self.kind, reply) {
            (Kind::Create, Reply::Created) | (Kind::Delete, Reply::Deleted) => Ok(Lsn(0)),
            (Kind::Trim { through, .. }, Reply::Trimmed { floor }) if floor > through => Ok(floor),
            _ => Err(JournalError::Unavailable),
        });
        match reply {
            Ok(floor) => {
                if let Some(first) = self.first {
                    return Effects::Complete(Ok(first.max(floor)));
                }
                self.first = Some(floor);
            }
            Err(error) => self.errors.push(error),
        }
        if self.errors.len() + usize::from(self.first.is_some()) == Slot::ALL.len() {
            return Effects::Complete(Err(refusal(&self.errors)));
        }
        Effects::Pending
    }
}

impl Operation for Mutation {
    type Output = Result<Lsn>;

    fn advance(&mut self, event: Event, _: Duration) -> Effects<Self::Output> {
        match event {
            Event::Invoke => Effects::Round(Slot::ALL.map(|slot| self.send(slot))),
            Event::Reply(_, response) => self.receive(response),
            _ => Effects::Pending,
        }
    }

    fn exhausted() -> Self::Output {
        Err(JournalError::Unavailable)
    }
}
