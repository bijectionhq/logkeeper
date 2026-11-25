//! Election and transfer of the selected history to a voting lane.

use std::time::Duration;

use journal_contract::{Epoch, Identity, JournalError, Lsn, Result, StreamId};

use super::{Effects, Event, Operation, Response, Send, Slot, journal_reply, refusal};
use crate::stream::{
    timed::Entry,
    wire::{EpochRun, KeeperId, Reply, Request, StreamView},
    writer::decision::{can_sync_from, matches_epoch, outranks},
};

#[derive(Clone)]
pub(in crate::stream) struct Election {
    stream: StreamId,
    ensemble: [KeeperId; 3],
    epoch: Epoch,
    identity: Identity,
    proposal: u128,
    first: Option<(Slot, StreamView)>,
    failures: Vec<JournalError>,
}

impl Election {
    pub(in crate::stream) fn new(
        stream: StreamId,
        ensemble: [KeeperId; 3],
        epoch: Epoch,
        identity: Identity,
        proposal: u128,
    ) -> Self {
        Self {
            stream,
            ensemble,
            epoch,
            identity,
            proposal,
            first: None,
            failures: Vec::new(),
        }
    }

    fn send(&self, slot: Slot, request: Request) -> Send {
        Send::new(slot, self.ensemble[slot as usize], request)
    }

    fn seal(&self, slot: Slot) -> Send {
        self.send(
            slot,
            Request::Seal {
                stream: self.stream,
                ensemble: self.ensemble,
                epoch: self.epoch,
                proposal: self.proposal,
            },
        )
    }

    fn sealed(&self, response: Response) -> Result<StreamView> {
        match journal_reply(response)? {
            Reply::Sealed(view)
                if view
                    .promised
                    .as_ref()
                    .is_some_and(|(epoch, identity, proposal)| {
                        *epoch == self.epoch
                            && identity == &self.identity
                            && *proposal == self.proposal
                    })
                    && view.head <= view.tail
                    && view.floor.0 != 0
                    && view.floor.0 - 1 <= view.head.0
                    && view.ensemble == self.ensemble
                    && !view.learner
                    && view.synced.is_none_or(|synced| synced <= self.epoch) =>
            {
                Ok(view)
            }
            _ => Err(JournalError::Unavailable),
        }
    }
}

#[derive(Clone)]
pub(in crate::stream) struct Recovery {
    pub(in crate::stream) epoch: Epoch,
    pub(in crate::stream) floor: Lsn,
    election: Election,
    source: Slot,
    history: StreamView,
}

impl Recovery {
    fn choose(
        election: Election,
        (first, a): (Slot, StreamView),
        (second, b): (Slot, StreamView),
    ) -> Result<Self> {
        let floor = a.floor.max(b.floor);
        let head = a.head.max(b.head);
        let (source, history) = if outranks(
            a.synced.map(|e| e.0),
            a.tail.0,
            b.synced.map(|e| e.0),
            b.tail.0,
        ) {
            (second, b)
        } else {
            (first, a)
        };
        if history.tail < head || history.tail.0 == u64::MAX {
            return Err(JournalError::Unavailable);
        }
        Ok(Self {
            epoch: election.epoch,
            floor,
            election,
            source,
            history,
        })
    }

    pub(in crate::stream) fn tail(&self) -> Lsn {
        self.history.tail
    }
}

impl Operation for Election {
    type Output = Result<Recovery>;

    fn advance(&mut self, event: Event, _: Duration) -> Effects<Self::Output> {
        match event {
            Event::Invoke => Effects::Round(Slot::ALL.map(|slot| self.seal(slot))),
            Event::Reply(slot, response) => {
                match self.sealed(response) {
                    Ok(view) => {
                        if let Some(first) = self.first.take() {
                            return Effects::Complete(Recovery::choose(
                                self.clone(),
                                first,
                                (slot, view),
                            ));
                        }
                        self.first = Some((slot, view));
                    }
                    Err(error) => self.failures.push(error),
                }
                if self.failures.len() + usize::from(self.first.is_some()) == Slot::ALL.len() {
                    return Effects::Complete(Err(refusal(&self.failures)));
                }
                Effects::Pending
            }
            _ => Effects::Pending,
        }
    }

    fn exhausted() -> Self::Output {
        Err(JournalError::Unavailable)
    }
}

pub(in crate::stream) struct SyncLane<'a> {
    recovery: &'a Recovery,
    target: Slot,
    requested_floor: Lsn,
    phase: Phase,
}

#[derive(Clone, Copy)]
struct Copy {
    from: Lsn,
    floor: Lsn,
    head: Lsn,
}

enum Phase {
    Seal,
    Fetch(Copy, Epoch),
    Fallback(Copy, Epoch, [Fallback; 3]),
    Stage(Copy),
    Install(Copy),
    Floor,
    Done,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Fallback {
    Seal,
    Fetch,
    Done,
}

impl<'a> SyncLane<'a> {
    pub(in crate::stream) fn new(
        recovery: &'a Recovery,
        keeper: KeeperId,
        requested_floor: Lsn,
    ) -> Result<Self> {
        let target = Slot::ALL
            .into_iter()
            .find(|slot| recovery.election.ensemble[*slot as usize] == keeper)
            .ok_or(JournalError::Unavailable)?;
        Ok(Self {
            recovery,
            target,
            requested_floor,
            phase: Phase::Seal,
        })
    }

    fn start(&mut self, response: Response) -> Result<Effects<Result<Lsn>>> {
        let target = self.recovery.election.sealed(response)?;
        let tail = self.recovery.tail();
        let history = &self.recovery.history;
        if target.synced == Some(self.recovery.epoch) {
            // Keep the elected history after a lost complete Sync reply.
            if target.tail < tail
                || divergence(&target, history, self.requested_floor.max(target.floor)).is_some()
            {
                return Err(JournalError::Unavailable);
            }
            return self.finish(self.requested_floor > target.floor, tail);
        }
        // Install the elected seed before moving the floor past it.
        let floor = self
            .requested_floor
            .min(Lsn(self.recovery.tail().0 + 1))
            .max(target.floor);
        let head = target.head.max(Lsn(floor.0 - 1));
        if head > tail {
            return Err(JournalError::Unavailable);
        }
        let from = divergence(&target, history, floor)
            .unwrap_or_else(|| Lsn(target.tail.min(tail).0.saturating_add(1).max(floor.0)));
        let same_prefix = from > floor && {
            let previous = Lsn(from.0 - 1);
            epoch_at(history, previous).is_some_and(|epoch| {
                matches_epoch(epoch_at(&target, previous).map(|e| e.0), epoch.0)
            })
        };
        if !can_sync_from(floor.0, target.head.0, from.0, same_prefix) {
            return Err(JournalError::Unavailable);
        }
        self.copy(Copy { from, floor, head })
    }

    fn copy(&mut self, copy: Copy) -> Result<Effects<Result<Lsn>>> {
        if copy.from > self.recovery.tail() {
            self.phase = Phase::Install(copy);
            return Ok(Effects::Send(self.sync(copy, None, true)));
        }
        let epoch = epoch_at(&self.recovery.history, copy.from).ok_or(JournalError::Unavailable)?;
        self.phase = Phase::Fetch(copy, epoch);
        Ok(Effects::Send(self.fetch(self.recovery.source, copy.from)))
    }

    fn fetch(&self, slot: Slot, from: Lsn) -> Send {
        let election = &self.recovery.election;
        election.send(
            slot,
            recover_request(election.stream, election.epoch, from, 1),
        )
    }

    fn sync(&self, copy: Copy, record: Option<(Epoch, Entry)>, complete: bool) -> Send {
        let election = &self.recovery.election;
        let (runs, records) = match record {
            Some((_, Entry::Timed { evidence, payload })) => {
                return election.send(
                    self.target,
                    Request::SyncOriginal {
                        stream: election.stream,
                        epoch: election.epoch,
                        floor: copy.floor,
                        evidence,
                        payload,
                        head: copy.head,
                    },
                );
            }
            Some((epoch, Entry::Ordinary(bytes))) => (
                vec![EpochRun {
                    epoch,
                    first: copy.from,
                    last: copy.from,
                }],
                vec![bytes],
            ),
            None => (Vec::new(), Vec::new()),
        };
        election.send(
            self.target,
            Request::Sync {
                stream: election.stream,
                epoch: election.epoch,
                floor: copy.floor,
                from: copy.from,
                records,
                runs,
                head: copy.head,
                complete,
            },
        )
    }

    fn fetched(&self, response: Response, at: Lsn, epoch: Epoch) -> Result<Entry> {
        let entry = single_record(journal_reply(response), at)?;
        if let Entry::Timed { evidence, .. } = &entry {
            let original = evidence.origin.original;
            if original.stream != self.recovery.election.stream || original.epoch != epoch {
                return Err(JournalError::Unavailable);
            }
        }
        Ok(entry)
    }

    fn finish(&mut self, install_floor: bool, tail: Lsn) -> Result<Effects<Result<Lsn>>> {
        if !install_floor {
            return Ok(Effects::Complete(Ok(tail)));
        }
        self.phase = Phase::Floor;
        let election = &self.recovery.election;
        Ok(Effects::Send(election.send(
            self.target,
            floor_request(election.stream, election.epoch, self.requested_floor),
        )))
    }

    fn fallback(&mut self, copy: Copy, epoch: Epoch) -> Effects<Result<Lsn>> {
        let mut status = [Fallback::Seal; 3];
        status[self.recovery.source as usize] = Fallback::Done;
        self.phase = Phase::Fallback(copy, epoch, status);
        let keepers = match self.recovery.source {
            Slot::First => [Slot::Second, Slot::Third],
            Slot::Second => [Slot::First, Slot::Third],
            Slot::Third => [Slot::First, Slot::Second],
        };
        Effects::Pair(keepers.map(|slot| self.recovery.election.seal(slot)))
    }

    fn receive(&mut self, slot: Slot, response: Response) -> Result<Effects<Result<Lsn>>> {
        let phase = std::mem::replace(&mut self.phase, Phase::Done);
        match phase {
            Phase::Seal if slot == self.target => self.start(response),
            Phase::Fetch(copy, epoch) if slot == self.recovery.source => {
                match self.fetched(response, copy.from, epoch) {
                    Ok(bytes) => {
                        self.phase = Phase::Stage(copy);
                        Ok(Effects::Send(self.sync(copy, Some((epoch, bytes)), false)))
                    }
                    Err(_) => Ok(self.fallback(copy, epoch)),
                }
            }
            Phase::Fallback(copy, epoch, mut status) => {
                let step = &mut status[slot as usize];
                match *step {
                    Fallback::Seal => {
                        let matched = self.recovery.election.sealed(response).is_ok_and(|view| {
                            matches_epoch(epoch_at(&view, copy.from).map(|e| e.0), epoch.0)
                        });
                        if matched {
                            *step = Fallback::Fetch;
                            self.phase = Phase::Fallback(copy, epoch, status);
                            return Ok(Effects::Send(self.fetch(slot, copy.from)));
                        }
                    }
                    Fallback::Fetch => {
                        if let Ok(record) = self.fetched(response, copy.from, epoch) {
                            self.phase = Phase::Stage(copy);
                            return Ok(Effects::CancelAndSend(self.sync(
                                copy,
                                Some((epoch, record)),
                                false,
                            )));
                        }
                    }
                    Fallback::Done => {}
                }
                *step = Fallback::Done;
                if status == [Fallback::Done; 3] {
                    return Err(JournalError::Unavailable);
                }
                self.phase = Phase::Fallback(copy, epoch, status);
                Ok(Effects::Pending)
            }
            Phase::Stage(mut copy) if slot == self.target => {
                sync_tail(journal_reply(response)?)?;
                copy.from = Lsn(copy.from.0 + 1);
                self.copy(copy)
            }
            Phase::Install(copy) if slot == self.target => {
                let tail = sync_tail(journal_reply(response)?)?;
                if tail != self.recovery.tail() {
                    return Err(JournalError::Unavailable);
                }
                self.finish(self.requested_floor > copy.floor, tail)
            }
            Phase::Floor if slot == self.target => {
                let tail = floor_reply(journal_reply(response)?, self.requested_floor)?;
                Ok(Effects::Complete(Ok(tail)))
            }
            phase => {
                self.phase = phase;
                Ok(Effects::Pending)
            }
        }
    }
}

impl Operation for SyncLane<'_> {
    type Output = Result<Lsn>;

    fn advance(&mut self, event: Event, _: Duration) -> Effects<Self::Output> {
        match event {
            Event::Invoke => Effects::Send(self.recovery.election.seal(self.target)),
            Event::Reply(slot, response) => self
                .receive(slot, response)
                .unwrap_or_else(|error| Effects::Complete(Err(error))),
            _ => Effects::Pending,
        }
    }

    fn exhausted() -> Self::Output {
        Err(JournalError::Unavailable)
    }
}

pub(in crate::stream) fn recover_request(
    stream: StreamId,
    epoch: Epoch,
    from: Lsn,
    max: u32,
) -> Request {
    Request::Recover {
        stream,
        epoch,
        from,
        max,
    }
}

pub(in crate::stream) fn single_record(reply: Result<Reply>, from: Lsn) -> Result<Entry> {
    match reply? {
        Reply::Records { mut records, .. } if records.len() == 1 && records[0].0 == from => {
            Ok(Entry::Ordinary(records.pop().unwrap().1))
        }
        Reply::OriginalRecord { evidence, payload }
            if evidence.origin.original.at == from
                && evidence.origin.original.matches(&payload) =>
        {
            Ok(Entry::Timed { evidence, payload })
        }
        _ => Err(JournalError::Unavailable),
    }
}

fn sync_tail(reply: Reply) -> Result<Lsn> {
    match reply {
        Reply::Synced { tail } => Ok(tail),
        _ => Err(JournalError::Unavailable),
    }
}

pub(in crate::stream) fn floor_request(stream: StreamId, epoch: Epoch, floor: Lsn) -> Request {
    Request::Sync {
        stream,
        epoch,
        floor,
        from: floor,
        records: Vec::new(),
        runs: Vec::new(),
        head: Lsn(floor.0.saturating_sub(1)),
        complete: false,
    }
}

pub(in crate::stream) fn floor_reply(reply: Reply, floor: Lsn) -> Result<Lsn> {
    let tail = sync_tail(reply)?;
    if tail.0 < floor.0.saturating_sub(1) {
        return Err(JournalError::Unavailable);
    }
    Ok(tail)
}

fn epoch_at(view: &StreamView, lsn: Lsn) -> Option<Epoch> {
    let run = view.runs.get(
        view.runs
            .partition_point(|run| run.first <= lsn)
            .checked_sub(1)?,
    )?;
    (lsn <= run.last).then_some(run.epoch)
}

fn divergence(a: &StreamView, b: &StreamView, floor: Lsn) -> Option<Lsn> {
    let through = a.tail.min(b.tail);
    std::iter::once(floor)
        .chain(a.runs.iter().chain(&b.runs).map(|run| run.first))
        .filter(|lsn| (floor..=through).contains(lsn))
        .filter(|&lsn| epoch_at(a, lsn) != epoch_at(b, lsn))
        .min()
}
