//! Append assignment, lane progress and publication for one proposer epoch.

use std::collections::BTreeMap;

use bytes::Bytes;
use journal_contract::{Epoch, JournalError, Lsn, Result};

use super::refusal;
use crate::stream::writer::decision::{QUORUM, accepted_tail, acknowledged, append_head};

pub(in crate::stream) const APPEND_RECORDS: usize = 1024;
const APPEND_BYTES: usize = 512 * 1024;
const RETAIN_BYTES: usize = 1024 * 1024;

pub(in crate::stream) type Completions = Vec<(u64, Result<Lsn>)>;

pub(in crate::stream) struct State {
    enabled: bool,
    closed: Option<JournalError>,
    head: Lsn,
    floor: Lsn,
    pending: BTreeMap<Lsn, Pending>,
    publishing: BTreeMap<Lsn, Vec<u64>>,
    /// An unanswered Append can still reach a keeper after a later capacity refusal.
    uncertain_through: Lsn,
    /// Chosen payloads that some lane may still need. Bounded by `RETAIN_BYTES`.
    committed: BTreeMap<Lsn, Bytes>,
    committed_bytes: usize,
    lanes: [Lane; 3],
    revision: u64,
    serial: u64,
    next_waiter: u64,
}

#[derive(Default)]
struct Lane {
    accepted: Option<Lsn>,
    published: Option<Lsn>,
    floor: Option<Lsn>,
    failure: Option<Failure>,
}

struct Failure {
    revision: u64,
    at: Lsn,
    error: JournalError,
}

struct Pending {
    payload: Bytes,
    waiters: Vec<u64>,
}

pub(in crate::stream) enum Work {
    Sync(Lsn),
    InstallFloor(Lsn),
    /// `payloads` is the contiguous known run from `at`, or `None` to fetch up to
    /// `limit` committed records that this lane lacks.
    Append {
        at: Lsn,
        payloads: Option<Vec<Bytes>>,
        limit: usize,
        head: Lsn,
    },
    Publish(Lsn),
}

pub(in crate::stream) enum Admission {
    Accepted(u64),
    Retry,
    Waiting,
    Refused(JournalError),
}

/// The append request metadata survives the await and binds its result to the
/// lane position, advertised head and revision that produced it.
pub(in crate::stream) struct Flight {
    at: Lsn,
    published: Lsn,
    floor: Option<Lsn>,
    sent_through: Option<Lsn>,
    revision: u64,
}

impl State {
    pub(in crate::stream) fn new(head: Lsn, floor: Lsn) -> Self {
        Self {
            enabled: false,
            closed: None,
            head,
            floor,
            pending: BTreeMap::new(),
            publishing: BTreeMap::new(),
            uncertain_through: Lsn(0),
            committed: BTreeMap::new(),
            committed_bytes: 0,
            lanes: std::array::from_fn(|_| Lane::default()),
            revision: 0,
            serial: 0,
            next_waiter: 0,
        }
    }

    pub(in crate::stream) fn ready(&mut self) -> Option<Result<()>> {
        if self
            .lanes
            .iter()
            .filter(|lane| lane.accepted.is_some())
            .count()
            >= QUORUM
        {
            self.enabled = true;
            return Some(Ok(()));
        }
        self.impossible(Lsn(0)).map(Err)
    }

    pub(in crate::stream) fn head(&self) -> Lsn {
        self.head
    }

    pub(in crate::stream) fn closed(&self) -> bool {
        self.closed.is_some()
    }

    pub(in crate::stream) fn trim(&mut self, floor: Lsn) {
        self.floor = self.floor.max(floor);
        self.revision += 1;
    }

    pub(in crate::stream) fn close(&mut self, error: JournalError) -> Completions {
        self.closed = Some(error.clone());
        let mut completions = Vec::new();
        for pending in self.pending.values_mut() {
            complete(&mut completions, pending, Err(error.clone()));
        }
        self.finish_publications(&mut completions);
        completions
    }

    pub(in crate::stream) fn append(&mut self, at: Lsn, payload: &Bytes) -> Admission {
        if let Some(error) = &self.closed {
            return Admission::Refused(error.clone());
        }
        if at < self.floor {
            return Admission::Refused(JournalError::Trimmed { floor: self.floor });
        }
        if at <= self.head {
            // A returning lane can catch up from the chosen payload.
            self.revision += 1;
            return Admission::Retry;
        }
        if at.0 == u64::MAX || at.0 > self.last().0 + 1 {
            return Admission::Refused(JournalError::Conflict { head: self.head });
        }
        let Some(waiter) = self.next_waiter.checked_add(1) else {
            return Admission::Refused(JournalError::Unavailable);
        };
        let pending = self.pending.entry(at).or_insert_with(|| Pending {
            payload: payload.clone(),
            waiters: Vec::new(),
        });
        if pending.payload == *payload {
            self.next_waiter = waiter;
            pending.waiters.push(waiter);
            self.revision += 1;
            return Admission::Accepted(waiter);
        }
        if pending.waiters.is_empty() {
            // Only a choice can resolve a conflict with an uncertain earlier append.
            return Admission::Refused(match self.impossible(at) {
                Some(error @ JournalError::Fenced { .. }) => error,
                _ => JournalError::Unavailable,
            });
        }
        Admission::Waiting
    }

    fn last(&self) -> Lsn {
        self.pending
            .last_key_value()
            .map_or(self.head, |(at, _)| *at)
    }

    pub(in crate::stream) fn accepted(&self, index: usize, at: Lsn) -> bool {
        self.lanes[index].accepted.is_some_and(|tail| tail >= at)
    }

    pub(in crate::stream) fn open(&self) -> u64 {
        self.serial
    }

    pub(in crate::stream) fn mark_sent(&mut self) -> u64 {
        self.serial += 1;
        self.serial
    }

    pub(in crate::stream) fn cover(&self, sample: Lsn) -> Option<Result<Lsn>> {
        if let Some(error) = &self.closed {
            return Some(Err(error.clone()));
        }
        if self.head >= sample {
            return Some(Ok(self.head));
        }
        if !self.pending.contains_key(&sample) {
            return Some(Err(JournalError::Unavailable));
        }
        self.impossible(sample).map(Err)
    }

    pub(in crate::stream) fn recover(
        &self,
        at: Lsn,
        target: usize,
        limit: usize,
    ) -> Result<[Option<u32>; 3]> {
        if at < self.floor {
            return Err(JournalError::Trimmed { floor: self.floor });
        }
        let committed = (self.head.0 - at.0 + 1).min(limit.max(1) as u64);
        Ok(std::array::from_fn(|index| {
            self.lanes[index]
                .accepted
                .filter(|tail| index != target && *tail >= at)
                .map(|tail| committed.min(tail.0 - at.0 + 1) as u32)
        }))
    }

    pub(in crate::stream) fn accepted_tail(&self, tail: Lsn, last: Lsn) -> Lsn {
        Lsn(accepted_tail(tail.0, self.last().0, last.0))
    }

    pub(in crate::stream) fn dispatch(
        &self,
        index: usize,
        records: usize,
    ) -> Option<(Work, Flight)> {
        let work = self.work(index, records)?;
        let (at, published, floor) = match &work {
            Work::Sync(floor) => (Lsn(0), Lsn(floor.0 - 1), Some(*floor)),
            Work::InstallFloor(floor) => (*floor, Lsn(floor.0 - 1), Some(*floor)),
            Work::Append { at, head, .. } => (*at, *head, None),
            Work::Publish(head) => (Lsn(head.0 + 1), *head, None),
        };
        let sent_through = match &work {
            Work::Append {
                at,
                payloads: Some(payloads),
                ..
            } => Some(Lsn(at.0 + payloads.len() as u64 - 1)),
            _ => None,
        };
        Some((
            work,
            Flight {
                at,
                published,
                floor,
                sent_through,
                revision: self.revision,
            },
        ))
    }

    pub(in crate::stream) fn receive(
        &mut self,
        epoch: Epoch,
        index: usize,
        flight: Flight,
        result: Result<Option<Lsn>>,
    ) -> Completions {
        let mut completions = Vec::new();
        if self.closed() {
            return completions;
        }
        let Flight {
            at,
            published,
            floor,
            sent_through,
            revision,
        } = flight;
        let lane = &mut self.lanes[index];
        match result {
            Ok(accepted) => {
                if let Some(tail) = accepted {
                    lane.accepted = Some(tail);
                }
                lane.published = lane.published.max(Some(published));
                lane.floor = lane.floor.max(floor);
                lane.failure = None;
                self.advance(epoch);
            }
            Err(error) => {
                let uncertain = matches!(error, JournalError::Unavailable);
                lane.failure = Some(Failure {
                    revision,
                    at,
                    error,
                });
                if let Some(last) = sent_through.filter(|_| uncertain) {
                    self.uncertain_through = self.uncertain_through.max(last);
                }
            }
        }
        self.fail_waiters(&mut completions);
        self.finish_publications(&mut completions);
        completions
    }
}

impl State {
    fn work(&self, index: usize, records: usize) -> Option<Work> {
        let lane = &self.lanes[index];
        if self.closed.is_some()
            || lane
                .failure
                .as_ref()
                .is_some_and(|f| f.revision == self.revision)
        {
            return None;
        }
        let Some(tail) = lane.accepted else {
            return Some(Work::Sync(self.floor));
        };
        if !self.enabled {
            return None;
        }
        let at = Lsn(tail.0 + 1);
        if lane.floor.is_none_or(|floor| floor < self.floor) {
            return Some(Work::InstallFloor(self.floor));
        }
        if self.pending.contains_key(&at) || at <= self.head {
            // A retry after an uncertain outcome carries one record. The keeper verifies
            // it against its history instead of refusing a range that overlaps its tail.
            let limit = if lane.failure.is_some() { 1 } else { records };
            let payloads = Some(self.run_from(at, limit)).filter(|run| !run.is_empty());
            let last = Lsn(at.0 + payloads.as_ref().map_or(1, Vec::len) as u64 - 1);
            return Some(Work::Append {
                at,
                payloads,
                limit,
                head: Lsn(append_head(self.head.0, last.0)),
            });
        }
        if lane.published.is_none_or(|published| published < self.head) {
            return Some(Work::Publish(self.head));
        }
        None
    }

    /// The contiguous retained and pending payloads from `at`, within one append's bounds.
    fn run_from(&self, at: Lsn, records: usize) -> Vec<Bytes> {
        let mut bytes = 0;
        let mut next = at;
        let mut payloads = Vec::new();
        let known = self
            .committed
            .range(at..)
            .chain(self.pending.range(at..).map(|(lsn, p)| (lsn, &p.payload)));
        for (&lsn, payload) in known {
            if lsn != next
                || payloads.len() == records.max(1)
                || (!payloads.is_empty() && bytes + payload.len() > APPEND_BYTES)
            {
                break;
            }
            bytes += payload.len();
            payloads.push(payload.clone());
            next = Lsn(lsn.0 + 1);
        }
        payloads
    }

    /// Forget committed payloads that every lane has accepted, that lie below the floor,
    /// or that exceed the retention bound. A lane that still needs them fetches them.
    fn release_committed(&mut self) {
        let accepted = self
            .lanes
            .iter()
            .map(|lane| lane.accepted.unwrap_or(Lsn(0)))
            .min()
            .unwrap();
        while let Some((&lsn, payload)) = self.committed.first_key_value() {
            if lsn > accepted && lsn >= self.floor && self.committed_bytes <= RETAIN_BYTES {
                break;
            }
            self.committed_bytes -= payload.len();
            self.committed.pop_first();
        }
    }

    fn impossible(&self, at: Lsn) -> Option<JournalError> {
        self.failed(|_, failure| failure.at <= at)
    }

    pub(in crate::stream) fn publication(&self, tail: Lsn) -> Option<Result<()>> {
        if let Some(error) = &self.closed {
            return Some(Err(error.clone()));
        }
        let covered = |lane: &Lane| lane.published.is_some_and(|head| head >= tail);
        if self.lanes.iter().filter(|lane| covered(lane)).count() >= QUORUM {
            return Some(Ok(()));
        }
        // A failed later append can block a lane before it publishes this head.
        self.failed(|lane, _| !covered(lane)).map(Err)
    }

    fn failed(&self, blocked: impl Fn(&Lane, &Failure) -> bool) -> Option<JournalError> {
        let errors: Vec<_> = self
            .lanes
            .iter()
            .filter_map(|lane| {
                lane.failure
                    .as_ref()
                    .filter(|failure| failure.revision == self.revision && blocked(lane, failure))
                    .map(|f| f.error.clone())
            })
            .collect();
        if errors.len() >= QUORUM {
            Some(refusal(&errors))
        } else {
            None
        }
    }

    fn advance(&mut self, epoch: Epoch) {
        let [a, b, c] = self
            .lanes
            .each_ref()
            .map(|lane| lane.accepted.map(|tail| (epoch.0, tail.0)));
        while let Some((&at, _)) = self.pending.first_key_value() {
            if !acknowledged(a, b, c, epoch.0, at.0) {
                break;
            }
            self.head = at;
            let pending = self.pending.pop_first().unwrap().1;
            if !pending.waiters.is_empty() {
                self.publishing.insert(at, pending.waiters);
            }
            self.committed_bytes += pending.payload.len();
            self.committed.insert(at, pending.payload);
        }
        self.release_committed();
    }

    fn finish_publications(&mut self, completions: &mut Completions) {
        while let Some((&at, _)) = self.publishing.first_key_value() {
            let Some(result) = self.publication(at) else {
                break;
            };
            let (_, waiters) = self.publishing.pop_first().unwrap();
            let result = result.map(|_| at).map_err(|_| JournalError::Unavailable);
            completions.extend(waiters.into_iter().map(|waiter| (waiter, result.clone())));
        }
        // A blocked lane can rule out a later publication while an earlier
        // one still has a possible quorum.
        while let Some((&at, _)) = self.publishing.last_key_value() {
            if !matches!(self.publication(at), Some(Err(_))) {
                break;
            }
            let (_, waiters) = self.publishing.pop_last().unwrap();
            completions.extend(
                waiters
                    .into_iter()
                    .map(|waiter| (waiter, Err(JournalError::Unavailable))),
            );
        }
    }

    fn fail_waiters(&mut self, completions: &mut Completions) {
        let Some((&first, _)) = self.pending.first_key_value() else {
            return;
        };
        let failed_at_first = self.lanes.iter().all(|lane| {
            lane.failure.as_ref().is_some_and(|failure| {
                failure.revision == self.revision
                    && failure.at == first
                    && matches!(
                        failure.error,
                        JournalError::Full { .. } | JournalError::TooLarge { .. }
                    )
            })
        });
        if failed_at_first && first > self.uncertain_through {
            // Every lane finished without accepting the first pending record.
            // An earlier unanswered request covering it would still own its bytes.
            let error = self.impossible(first).unwrap();
            for (_, mut pending) in std::mem::take(&mut self.pending) {
                complete(completions, &mut pending, Err(error.clone()));
            }
            return;
        }
        if let Some((&last, _)) = self.pending.last_key_value() {
            if self.impossible(last).is_none() {
                return;
            }
        }
        let failed: Vec<_> = self
            .pending
            .iter()
            .filter(|(_, pending)| !pending.waiters.is_empty())
            .filter_map(|(&at, _)| {
                let error = self.impossible(at)?;
                if matches!(
                    error,
                    JournalError::Full { .. } | JournalError::TooLarge { .. }
                ) {
                    // A third reply can still make the refusal definitive.
                    let outstanding = self.lanes.iter().any(|lane| {
                        lane.accepted.is_none_or(|tail| tail < at)
                            && !lane.failure.as_ref().is_some_and(|failure| {
                                failure.revision == self.revision && failure.at <= at
                            })
                    });
                    if outstanding && at > self.uncertain_through {
                        return None;
                    }
                    return Some((at, JournalError::Unavailable));
                }
                Some((at, error))
            })
            .collect();
        for (at, error) in failed {
            let error = match error {
                JournalError::Conflict { .. } => JournalError::Conflict { head: self.head },
                error => error,
            };
            complete(completions, self.pending.get_mut(&at).unwrap(), Err(error));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn publication_detects_a_lane_blocked_by_a_later_append() {
        let mut state = State {
            enabled: true,
            closed: None,
            head: Lsn(3),
            floor: Lsn(1),
            pending: BTreeMap::new(),
            publishing: BTreeMap::new(),
            uncertain_through: Lsn(0),
            committed: BTreeMap::new(),
            committed_bytes: 0,
            lanes: [
                Lane {
                    accepted: Some(Lsn(4)),
                    published: Some(Lsn(2)),
                    failure: Some(Failure {
                        revision: 1,
                        at: Lsn(5),
                        error: JournalError::Unavailable,
                    }),
                    ..Lane::default()
                },
                Lane {
                    accepted: Some(Lsn(3)),
                    published: Some(Lsn(3)),
                    ..Lane::default()
                },
                Lane {
                    failure: Some(Failure {
                        revision: 1,
                        at: Lsn(1),
                        error: JournalError::Unavailable,
                    }),
                    ..Lane::default()
                },
            ],
            revision: 1,
            serial: 0,
            next_waiter: 0,
        };
        assert_eq!(
            state.publication(Lsn(3)),
            Some(Err(JournalError::Unavailable)),
            "pending publication must finish when both uncovered lanes are blocked"
        );
        state.revision += 1;
        assert_eq!(state.publication(Lsn(3)), None);
    }
}

fn complete(completions: &mut Completions, pending: &mut Pending, result: Result<Lsn>) {
    completions.extend(
        pending
            .waiters
            .drain(..)
            .map(|waiter| (waiter, result.clone())),
    );
}
