//! Recovery and installation of a replacement ensemble.

use std::time::Duration;

use crate::stream::{codec::MAX_FRAME_BYTES, wire::*};

use super::{Effects, Event, Operation, Response, Send, Slot};

/// The caller nominates an idle stream and reserves an epoch for this sweep.
#[derive(Clone, Copy, Debug)]
pub struct Sweep {
    pub(in crate::stream) stream: StreamId,
    pub(in crate::stream) ensemble: [KeeperId; 3],
    pub(in crate::stream) survivors: [KeeperId; 2],
    pub(in crate::stream) learner: KeeperId,
    pub(in crate::stream) epoch: Epoch,
    pub(in crate::stream) proposal: u128,
}

#[derive(Debug, thiserror::Error)]
pub enum SweepError {
    #[error("keeper {keeper:?} was unreachable: {error:?}")]
    Transport {
        keeper: KeeperId,
        error: TransportError,
    },
    #[error("keeper {keeper:?} returned {reply:?}")]
    Reply { keeper: KeeperId, reply: Reply },
    #[error("the replacement plan or recovery history is inconsistent")]
    History,
}

type Result<T> = std::result::Result<T, SweepError>;

pub(in crate::stream) struct Replacement {
    plan: Sweep,
    identity: Identity,
    next: [KeeperId; 3],
    phase: Phase,
    retried_seal: [bool; 3],
    selected: Option<Selected>,
}

enum Phase {
    New,
    SealSurvivors([Option<Result<StreamView>>; 2]),
    CreateSurvivor {
        slot: Slot,
        other: StreamView,
    },
    SealSurvivor {
        slot: Slot,
        other: StreamView,
    },
    Recover(Copy),
    Sync {
        copy: Copy,
        last: Lsn,
        visible_tail: Lsn,
    },
    SyncSource,
    Publish(Option<Slot>),
    CreateLearner,
    SealLearner,
    ReplaceSurvivors(Option<Slot>),
    ReplaceLearner,
    Done,
}

struct Selected {
    source: Slot,
    history: StreamView,
    floor: Lsn,
    head: Lsn,
}

struct Copy {
    target: Slot,
    head: Lsn,
    from: Lsn,
    target_tail: Lsn,
}

impl Replacement {
    pub(in crate::stream) fn new(plan: Sweep, identity: Identity) -> Self {
        let next = plan.ensemble.map(|id| {
            if plan.survivors.contains(&id) {
                id
            } else {
                plan.learner
            }
        });
        Self {
            plan,
            identity,
            next,
            phase: Phase::New,
            retried_seal: [false; 3],
            selected: None,
        }
    }

    fn keeper(&self, slot: Slot) -> KeeperId {
        match slot {
            Slot::First => self.plan.survivors[0],
            Slot::Second => self.plan.survivors[1],
            Slot::Third => self.plan.learner,
        }
    }

    fn send(&self, slot: Slot, request: Request) -> Send {
        Send::new(slot, self.keeper(slot), request)
    }

    fn create(&self, slot: Slot) -> Send {
        self.send(
            slot,
            Request::Create {
                stream: self.plan.stream,
                ensemble: self.plan.ensemble,
            },
        )
    }

    fn seal(&self, slot: Slot) -> Send {
        self.send(
            slot,
            Request::Seal {
                stream: self.plan.stream,
                ensemble: if self.retried_seal[slot as usize] {
                    self.next
                } else {
                    self.plan.ensemble
                },
                epoch: self.plan.epoch,
                proposal: self.plan.proposal,
            },
        )
    }

    fn replace(&self, slot: Slot) -> Send {
        self.send(
            slot,
            Request::Replace {
                stream: self.plan.stream,
                epoch: self.plan.epoch,
                from: self.plan.ensemble,
                to: self.next,
            },
        )
    }

    fn publish(&self, slot: Slot, tail: Lsn) -> Send {
        self.send(
            slot,
            Request::Append {
                stream: self.plan.stream,
                epoch: self.plan.epoch,
                at: Lsn(tail.0 + 1),
                records: Vec::new(),
                head: tail,
            },
        )
    }

    fn reply(&self, slot: Slot, response: Response) -> Result<Reply> {
        response.map_err(|error| SweepError::Transport {
            keeper: self.keeper(slot),
            error,
        })
    }

    fn expect(&self, slot: Slot, response: Response, expected: Reply) -> Result<()> {
        let reply = self.reply(slot, response)?;
        if reply != expected {
            return Err(SweepError::Reply {
                keeper: self.keeper(slot),
                reply,
            });
        }
        Ok(())
    }

    fn sealed(&self, slot: Slot, response: Response) -> Result<StreamView> {
        match self.reply(slot, response)? {
            Reply::Sealed(view)
                if view
                    .promised
                    .as_ref()
                    .is_some_and(|(epoch, identity, proposal)| {
                        *epoch == self.plan.epoch
                            && identity == &self.identity
                            && *proposal == self.plan.proposal
                    }) =>
            {
                if view.floor.0 == 0
                    || view.head > view.tail
                    || view.floor.0 - 1 > view.head.0
                    || view.tail.0 == u64::MAX
                {
                    return Err(SweepError::History);
                }
                Ok(view)
            }
            reply => Err(SweepError::Reply {
                keeper: self.keeper(slot),
                reply,
            }),
        }
    }

    fn survivors(
        &mut self,
        left: Result<StreamView>,
        right: Result<StreamView>,
    ) -> Result<Effects<Result<()>>> {
        let (slot, other) = match (left, right) {
            (Ok(left), Err(error)) if !left.learner && error.not_found() => (Slot::Second, left),
            (Err(error), Ok(right)) if !right.learner && error.not_found() => (Slot::First, right),
            (Err(left), Err(right)) if left.not_found() => return Err(right),
            (left, right) => return self.select(left?, right?),
        };
        // The other survivor confirms existence, so an absent survivor can be rebuilt.
        self.phase = Phase::CreateSurvivor { slot, other };
        Ok(Effects::Send(self.create(slot)))
    }

    fn select(&mut self, left: StreamView, right: StreamView) -> Result<Effects<Result<()>>> {
        if left.learner || right.learner {
            return Err(SweepError::History);
        }
        let head = left.head.max(right.head);
        let floor = left.floor.max(right.floor);
        let (source, history, other, target) =
            if (left.synced, left.tail) >= (right.synced, right.tail) {
                (Slot::First, left, Slot::Second, right)
            } else {
                (Slot::Second, right, Slot::First, left)
            };
        if history.tail < head || floor.0 > head.0 + 1 {
            return Err(SweepError::History);
        }
        self.selected = Some(Selected {
            source,
            history,
            floor,
            head,
        });
        self.copy(other, target, head)
    }

    fn selected(&self) -> Result<&Selected> {
        self.selected.as_ref().ok_or(SweepError::History)
    }

    fn copy(&mut self, slot: Slot, target: StreamView, head: Lsn) -> Result<Effects<Result<()>>> {
        let selected = self.selected()?;
        if target.synced == Some(self.plan.epoch) {
            if target.tail != selected.history.tail {
                return Err(SweepError::History);
            }
            return self.copied(slot);
        }
        if target.head > selected.history.tail {
            return Err(SweepError::History);
        }
        let from = Lsn(target.head.0 + 1).max(selected.floor);
        self.copy_from(Copy {
            target: slot,
            head,
            from,
            target_tail: target.tail,
        })
    }

    fn copy_from(&mut self, copy: Copy) -> Result<Effects<Result<()>>> {
        let selected = self.selected()?;
        if copy.from <= selected.history.tail {
            let send = self.send(
                selected.source,
                Request::Recover {
                    stream: self.plan.stream,
                    epoch: self.plan.epoch,
                    from: copy.from,
                    max: 8192,
                },
            );
            self.phase = Phase::Recover(copy);
            return Ok(Effects::Send(send));
        }
        let last = Lsn(copy.from.0 - 1);
        self.sync_chunk(copy, last, Vec::new(), Vec::new(), true)
    }

    fn recovered(
        &mut self,
        copy: Copy,
        source: Slot,
        response: Response,
    ) -> Result<Effects<Result<()>>> {
        let selected = self.selected()?;
        let reply = self.reply(source, response)?;
        let Reply::Records { records, .. } = reply else {
            return Err(SweepError::Reply {
                keeper: self.keeper(source),
                reply,
            });
        };
        let mut used = 128usize;
        let mut last = Lsn(copy.from.0 - 1);
        let mut chunk = Vec::new();
        for (lsn, payload) in records {
            if lsn.0 != last.0 + 1 || lsn > selected.history.tail {
                return Err(SweepError::History);
            }
            used = used.saturating_add(35).saturating_add(payload.len());
            if used > MAX_FRAME_BYTES {
                break;
            }
            last = lsn;
            chunk.push(payload);
        }
        if chunk.is_empty() {
            return Err(SweepError::History);
        }
        let start = selected
            .history
            .runs
            .partition_point(|run| run.last < copy.from);
        let runs = selected.history.runs[start..]
            .iter()
            .take_while(|run| run.first <= last)
            .map(|run| EpochRun {
                epoch: run.epoch,
                first: run.first.max(copy.from),
                last: run.last.min(last),
            })
            .collect();
        let complete = last == selected.history.tail;
        self.sync_chunk(copy, last, chunk, runs, complete)
    }

    fn sync_chunk(
        &mut self,
        copy: Copy,
        last: Lsn,
        records: Vec<bytes::Bytes>,
        runs: Vec<EpochRun>,
        complete: bool,
    ) -> Result<Effects<Result<()>>> {
        let send = self.send(
            copy.target,
            Request::Sync {
                stream: self.plan.stream,
                epoch: self.plan.epoch,
                floor: self.selected()?.floor,
                from: copy.from,
                head: copy.head.min(last),
                records,
                runs,
                complete,
            },
        );
        // Staging acknowledges the unchanged visible tail until complete Sync.
        let visible_tail = if complete { last } else { copy.target_tail };
        self.phase = Phase::Sync {
            copy,
            last,
            visible_tail,
        };
        Ok(Effects::Send(send))
    }

    fn copied(&mut self, slot: Slot) -> Result<Effects<Result<()>>> {
        if slot == Slot::Third {
            self.phase = Phase::ReplaceSurvivors(None);
            return Ok(Effects::Pair([
                self.replace(Slot::First),
                self.replace(Slot::Second),
            ]));
        }
        let selected = self.selected()?;
        if selected.history.synced == Some(self.plan.epoch) {
            return self.publish_survivors();
        }
        let send = self.send(
            selected.source,
            Request::Sync {
                stream: self.plan.stream,
                epoch: self.plan.epoch,
                floor: selected.floor,
                from: Lsn(selected.history.tail.0 + 1),
                records: Vec::new(),
                runs: Vec::new(),
                head: selected.head,
                complete: true,
            },
        );
        self.phase = Phase::SyncSource;
        Ok(Effects::Send(send))
    }

    fn publish_survivors(&mut self) -> Result<Effects<Result<()>>> {
        let tail = self.selected()?.history.tail;
        self.phase = Phase::Publish(None);
        Ok(Effects::Pair([
            self.publish(Slot::First, tail),
            self.publish(Slot::Second, tail),
        ]))
    }

    fn reply_step(&mut self, slot: Slot, response: Response) -> Result<Effects<Result<()>>> {
        let phase = std::mem::replace(&mut self.phase, Phase::Done);
        let sealing = matches!(
            phase,
            Phase::SealSurvivors(_) | Phase::SealSurvivor { .. } | Phase::SealLearner
        );
        if sealing
            && !self.retried_seal[slot as usize]
            && response
                == Ok(Reply::Refused(Refusal::WrongEnsemble {
                    ensemble: self.next,
                }))
        {
            // A crash can leave one survivor on each ensemble. Resume the same move.
            self.phase = phase;
            self.retried_seal[slot as usize] = true;
            return Ok(Effects::Send(self.seal(slot)));
        }
        match phase {
            Phase::SealSurvivors(mut views) if slot != Slot::Third => {
                views[slot as usize] = Some(self.sealed(slot, response));
                match views {
                    [Some(left), Some(right)] => self.survivors(left, right),
                    views => {
                        self.phase = Phase::SealSurvivors(views);
                        Ok(Effects::Pending)
                    }
                }
            }
            Phase::CreateSurvivor {
                slot: waiting,
                other,
            } if slot == waiting => {
                self.expect(slot, response, Reply::Created)?;
                self.phase = Phase::SealSurvivor { slot, other };
                self.retried_seal[slot as usize] = false;
                Ok(Effects::Send(self.seal(slot)))
            }
            Phase::SealSurvivor {
                slot: waiting,
                other,
            } if slot == waiting => {
                let view = self.sealed(slot, response)?;
                if slot == Slot::First {
                    self.select(view, other)
                } else {
                    self.select(other, view)
                }
            }
            Phase::Recover(copy) if slot == self.selected()?.source => {
                self.recovered(copy, slot, response)
            }
            Phase::Sync {
                mut copy,
                last,
                visible_tail,
            } if slot == copy.target => {
                self.expect(slot, response, Reply::Synced { tail: visible_tail })?;
                if last == self.selected()?.history.tail {
                    self.copied(slot)
                } else {
                    copy.from = Lsn(last.0 + 1);
                    self.copy_from(copy)
                }
            }
            Phase::SyncSource if slot == self.selected()?.source => {
                self.expect(
                    slot,
                    response,
                    Reply::Synced {
                        tail: self.selected()?.history.tail,
                    },
                )?;
                self.publish_survivors()
            }
            Phase::Publish(first) if slot != Slot::Third => {
                self.expect(
                    slot,
                    response,
                    Reply::Appended {
                        tail: self.selected()?.history.tail,
                    },
                )?;
                if first.is_some_and(|other| other != slot) {
                    self.phase = Phase::CreateLearner;
                    Ok(Effects::Send(self.create(Slot::Third)))
                } else {
                    self.phase = Phase::Publish(Some(slot));
                    Ok(Effects::Pending)
                }
            }
            Phase::CreateLearner if slot == Slot::Third => {
                self.expect(slot, response, Reply::Created)?;
                self.phase = Phase::SealLearner;
                Ok(Effects::Send(self.seal(slot)))
            }
            Phase::SealLearner if slot == Slot::Third => {
                let learner = self.sealed(slot, response)?;
                if !learner.learner && learner.ensemble != self.next {
                    return Err(SweepError::History);
                }
                self.copy(slot, learner, self.selected()?.history.tail)
            }
            Phase::ReplaceSurvivors(first) if slot != Slot::Third => {
                self.expect(slot, response, Reply::Replaced)?;
                if first.is_some_and(|other| other != slot) {
                    self.phase = Phase::ReplaceLearner;
                    Ok(Effects::Send(self.replace(Slot::Third)))
                } else {
                    self.phase = Phase::ReplaceSurvivors(Some(slot));
                    Ok(Effects::Pending)
                }
            }
            Phase::ReplaceLearner if slot == Slot::Third => {
                self.expect(slot, response, Reply::Replaced)?;
                Ok(Effects::Complete(Ok(())))
            }
            phase => {
                self.phase = phase;
                Ok(Effects::Pending)
            }
        }
    }
}

impl Operation for Replacement {
    type Output = Result<()>;

    fn advance(&mut self, event: Event, _: Duration) -> Effects<Self::Output> {
        match event {
            Event::Invoke if matches!(self.phase, Phase::New) => {
                let [first, second] = self.plan.survivors;
                if first == second
                    || self.plan.ensemble.contains(&self.plan.learner)
                    || self
                        .plan
                        .survivors
                        .iter()
                        .any(|id| !self.plan.ensemble.contains(id))
                {
                    return Effects::Complete(Err(SweepError::History));
                }
                self.phase = Phase::SealSurvivors([None, None]);
                Effects::Pair([self.seal(Slot::First), self.seal(Slot::Second)])
            }
            Event::Reply(slot, response) => self
                .reply_step(slot, response)
                .unwrap_or_else(|error| Effects::Complete(Err(error))),
            _ => Effects::Pending,
        }
    }

    fn exhausted() -> Self::Output {
        Err(SweepError::History)
    }
}

impl SweepError {
    fn not_found(&self) -> bool {
        matches!(
            self,
            Self::Reply {
                reply: Reply::Refused(Refusal::NotFound),
                ..
            }
        )
    }
}
