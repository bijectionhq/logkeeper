//! An observer pins its first eligible read index across confirmation rounds.

use std::time::Duration;

use journal_contract::{Epoch, Identity, JournalError, Lsn, Result, StreamId};

use super::{Effects, Event, Operation, Response, Send, Slot, journal_reply, refusal};
use crate::stream::{
    wire::{KeeperId, Reply, Request, StreamView},
    writer::decision::{eligible_sample, head_quorum, sample_index},
};

pub(in crate::stream) struct Samples {
    epoch: Epoch,
    count: usize,
    tail: Lsn,
    errors: Vec<JournalError>,
}

impl Samples {
    pub(in crate::stream) fn new(epoch: Epoch) -> Self {
        Self {
            epoch,
            count: 0,
            tail: Lsn(0),
            errors: Vec::new(),
        }
    }

    pub(in crate::stream) fn receive(&mut self, reply: Result<Lsn>) -> Option<Result<Lsn>> {
        match reply {
            Ok(tail) => {
                self.count += 1;
                self.tail = Lsn(sample_index(self.tail.0, tail.0));
                head_quorum(self.count).then_some(Ok(self.tail))
            }
            Err(error @ JournalError::Fenced { current }) if current > self.epoch => {
                Some(Err(error))
            }
            Err(error) => {
                self.errors.push(error);
                None
            }
        }
    }

    pub(in crate::stream) fn error(&self) -> JournalError {
        refusal(&self.errors)
    }
}

pub(in crate::stream) fn writer_tail(
    view: StreamView,
    epoch: Epoch,
    identity: &Identity,
    proposal: u128,
) -> Result<Lsn> {
    match view.promised {
        Some((current, owner, id))
            if current > epoch || (current == epoch && (&owner != identity || id != proposal)) =>
        {
            Err(JournalError::Fenced { current })
        }
        Some((current, ..)) if current == epoch && view.synced == Some(epoch) => Ok(view.tail),
        _ => Err(JournalError::Unavailable),
    }
}

const RETRY: Duration = Duration::from_millis(1);
const MAX_RETRY: Duration = Duration::from_millis(32);
const SETTLE: Duration = Duration::from_secs(2);

pub(in crate::stream) struct Observer {
    stream: StreamId,
    ensemble: [KeeperId; 3],
    resamples: bool,
    target: Option<Lsn>,
    pause: Duration,
    outstanding: usize,
    views: Vec<StreamView>,
    errors: Vec<JournalError>,
}

impl Observer {
    pub(in crate::stream) fn new(
        stream: StreamId,
        ensemble: [KeeperId; 3],
        resamples: bool,
    ) -> Self {
        Self {
            stream,
            ensemble,
            resamples,
            target: None,
            pause: RETRY,
            outstanding: 0,
            views: Vec::with_capacity(3),
            errors: Vec::new(),
        }
    }

    fn open(&mut self) -> Effects<Result<Lsn>> {
        self.outstanding = 3;
        self.views.clear();
        self.errors.clear();
        Effects::Round(Slot::ALL.map(|slot| {
            Send::new(
                slot,
                self.ensemble[slot as usize],
                Request::Check {
                    stream: self.stream,
                    epoch: Epoch(0),
                },
            )
        }))
    }

    fn observe(&mut self, response: Response, elapsed: Duration) -> Effects<Result<Lsn>> {
        match journal_reply(response).and_then(|reply| checked_view(reply, self.ensemble)) {
            Ok(view) => self.views.push(view),
            Err(error) => self.errors.push(error),
        }
        if let Some(head) = observed_head(&self.views, self.target) {
            return Effects::Complete(Ok(head));
        }
        self.outstanding -= 1;
        if self.outstanding != 0 {
            return Effects::Pending;
        }
        if self.target.is_none() {
            self.target = read_index(&self.views);
        }
        let error = refusal(&self.errors);
        if error != JournalError::Unavailable || elapsed >= SETTLE {
            return Effects::Complete(Err(error));
        }
        if self.resamples {
            self.target = None;
        }
        let pause = self.pause;
        self.pause = (pause * 2).min(MAX_RETRY);
        Effects::Sleep(pause)
    }
}

impl Operation for Observer {
    type Output = Result<Lsn>;

    fn advance(&mut self, event: Event, elapsed: Duration) -> Effects<Self::Output> {
        match event {
            Event::Invoke | Event::Timer if self.outstanding == 0 => self.open(),
            Event::Reply(_, response) if self.outstanding > 0 => self.observe(response, elapsed),
            _ => Effects::Pending,
        }
    }

    fn exhausted() -> Self::Output {
        Err(JournalError::Unavailable)
    }
}

pub(in crate::stream) fn checked_view(reply: Reply, ensemble: [KeeperId; 3]) -> Result<StreamView> {
    match reply {
        Reply::Checked(view)
            if view.head <= view.tail
                && view.floor.0 > 0
                && view.floor.0 - 1 <= view.head.0
                && view.ensemble == ensemble
                && !view.learner =>
        {
            Ok(view)
        }
        _ => Err(JournalError::Unavailable),
    }
}

/// Views at the highest promised epoch, from a keeper synced at that epoch and with
/// the same promise as `candidate`.
fn eligible<'a>(
    views: &'a [StreamView],
    candidate: &'a StreamView,
) -> impl Iterator<Item = &'a StreamView> + 'a {
    let epoch = views
        .iter()
        .filter_map(|view| view.promised.as_ref().map(|p| p.0))
        .max();
    views.iter().filter(move |view| {
        eligible_sample(
            view.promised.as_ref().map(|p| (p.0).0),
            view.synced.map(|epoch| epoch.0),
            epoch.map(|epoch| epoch.0),
            view.promised == candidate.promised,
        )
    })
}

/// The maximum tail of an eligible quorum, if the views contain one.
fn read_index(views: &[StreamView]) -> Option<Lsn> {
    views.iter().find_map(|candidate| {
        head_quorum(eligible(views, candidate).count())
            .then(|| eligible(views, candidate).map(|view| view.tail).max())
            .flatten()
    })
}

/// Without a target, the eligible maximum tail must already be covered by a quorum of
/// published heads. With a pinned target, a quorum of eligible heads must reach it.
fn observed_head(views: &[StreamView], target: Option<Lsn>) -> Option<Lsn> {
    views.iter().find_map(|candidate| {
        let index = match target {
            Some(target) => target,
            None => eligible(views, candidate).map(|view| view.tail).max()?,
        };
        head_quorum(
            eligible(views, candidate)
                .filter(|view| view.head >= index)
                .count(),
        )
        .then_some(index)
    })
}
