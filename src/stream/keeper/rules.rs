//! Keeper decisions. Disk reads needed to compare a retry are supplied in the view.
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == !deleted))]
pub(crate) fn live(deleted: bool) -> bool {
    !deleted
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (!has_promise || current < epoch || (current == epoch && same_holder))
))]
pub(crate) fn may_seal(has_promise: bool, current: u64, epoch: u64, same_holder: bool) -> bool {
    !has_promise || current < epoch || (current == epoch && same_holder)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (from > commit || identical)))]
pub(crate) fn preserves_commit(from: u64, commit: u64, identical: bool) -> bool {
    from > commit || identical
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (promised && synced)))]
pub(crate) fn may_append(promised: bool, synced: bool) -> bool {
    promised && synced
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (through <= commit)))]
pub(crate) fn may_trim(through: u64, commit: u64) -> bool {
    through <= commit
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == current))]
pub(crate) fn checked_end(current: u64, _request_epoch: u64) -> u64 {
    current
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == commit))]
pub(crate) fn read_end(commit: u64, _accepted: u64) -> u64 {
    commit
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (deleted || deleting)))]
pub(crate) fn tombstone(deleted: bool, deleting: bool) -> bool {
    deleted || deleting
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (current <= next && next <= end && 0 < floor && floor as int <= next as int + 1)
))]
pub(crate) fn sync_commit_valid(current: u64, next: u64, end: u64, floor: u64) -> bool {
    current <= next && next <= end && floor > 0 && floor - 1 <= next
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (nonempty && last <= end && identical)))]
pub(crate) fn append_retry(nonempty: bool, last: u64, end: u64, identical: bool) -> bool {
    nonempty && last <= end && identical
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (floor <= from)))]
pub(crate) fn may_read(floor: u64, from: u64) -> bool {
    floor <= from
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (current && synced && member && changed == 1)))]
pub(crate) fn may_replace(current: bool, synced: bool, member: bool, changed: usize) -> bool {
    current && synced && member && changed == 1
}

#[cfg(not(verus_keep_ghost))]
pub use implementation::Limits;
#[cfg(not(verus_keep_ghost))]
pub(super) use implementation::{Decision, StreamView, charge, decide, sync_start, valid_limits};

#[cfg(not(verus_keep_ghost))]
mod implementation {
    use super::*;
    use crate::stream::{
        codec::PAGE_BYTES,
        wire::{self, *},
    };
    use bytes::Bytes;

    /// All configured byte limits are per stream.
    #[derive(Clone, Copy, Debug)]
    #[cfg_attr(
        feature = "stream",
        derive(serde::Deserialize),
        serde(deny_unknown_fields)
    )]
    pub struct Limits {
        pub stream_quota_bytes: u64,
        pub max_record_bytes: u32,
        pub round_bytes_per_stream: usize,
    }

    impl Default for Limits {
        fn default() -> Self {
            Self {
                stream_quota_bytes: 8 * 1024 * 1024 * 1024,
                max_record_bytes: 32 * 1024 * 1024,
                round_bytes_per_stream: 4 * 1024 * 1024,
            }
        }
    }

    /// A projection of the stream plus facts obtained by comparing retained payloads.
    pub(crate) struct StreamView<'a> {
        pub keeper: KeeperId,
        pub durable: Option<&'a wire::StreamView>,
        pub deleted: bool,
        pub same_principal: bool,
        pub seal_allowed: bool,
        pub identical: bool,
        pub retained_bytes: u64,
    }

    #[derive(Debug, PartialEq, Eq)]
    pub(crate) enum Decision {
        Reply(Reply),
        Persist,
        Page { through: Lsn },
    }

    fn refuse(refusal: Refusal) -> Decision {
        Decision::Reply(Reply::Refused(refusal))
    }

    fn fenced(state: &wire::StreamView) -> Decision {
        refuse(Refusal::Fenced {
            promised: state.promised.map_or(Epoch(0), |(epoch, _)| epoch),
        })
    }

    fn wrong_ensemble(state: &wire::StreamView) -> Decision {
        refuse(Refusal::WrongEnsemble {
            ensemble: state.ensemble,
        })
    }

    fn valid_ensemble(ensemble: &[KeeperId; 3]) -> bool {
        !ensemble.contains(&KeeperId(0))
            && ensemble[0] != ensemble[1]
            && ensemble[0] != ensemble[2]
            && ensemble[1] != ensemble[2]
    }

    // Reserve one LSN to represent the floor of a fully trimmed stream.
    pub(crate) fn last(from: Lsn, count: usize) -> Option<Lsn> {
        from.0
            .checked_sub(1)?
            .checked_add(count as u64)
            .filter(|end| *end != u64::MAX)
            .map(Lsn)
    }

    pub(crate) fn charge(record: &[u8]) -> u64 {
        record.len().max(1) as u64
    }

    fn capacity(records: &[Bytes], retained: u64, floor: Lsn, limits: &Limits) -> Option<Decision> {
        if records
            .iter()
            .any(|record| record.len() > limits.max_record_bytes as usize)
        {
            return Some(refuse(Refusal::TooLarge {
                max: limits.max_record_bytes,
            }));
        }
        let bytes = records
            .iter()
            .fold(retained, |sum, record| sum.saturating_add(charge(record)));
        (bytes > limits.stream_quota_bytes).then(|| refuse(Refusal::Full { floor }))
    }

    fn valid_runs(epoch: Epoch, from: Lsn, end: Lsn, runs: &[EpochRun]) -> bool {
        let mut next = from.0;
        for run in runs {
            if run.epoch > epoch || run.first.0 != next || run.last < run.first || run.last > end {
                return false;
            }
            next = run.last.0 + 1;
        }
        next == end.0 + 1
    }

    pub(crate) fn sync_start(state: &wire::StreamView, from: Lsn, floor: Lsn) -> Lsn {
        from.max(state.floor)
            .max(floor)
            .max(Lsn(state.commit.0 + 1))
    }

    pub(crate) fn decide(view: &StreamView<'_>, request: &Request, limits: &Limits) -> Decision {
        if let Request::Delete { ensemble, .. } = request {
            if let Some(state) = view.durable {
                if *ensemble != state.ensemble {
                    return wrong_ensemble(state);
                }
            }
            if view.deleted {
                return Decision::Reply(Reply::Deleted);
            }
            if !valid_ensemble(ensemble) || !ensemble.contains(&view.keeper) {
                return refuse(Refusal::Unauthorized);
            }
            return if tombstone(view.deleted, true) {
                Decision::Persist
            } else {
                Decision::Reply(Reply::Deleted)
            };
        }
        if !live(view.deleted) {
            return refuse(Refusal::Deleted);
        }
        if let Request::Create { ensemble, .. } = request {
            if view.durable.is_some() {
                return Decision::Reply(Reply::Created);
            }
            if !valid_ensemble(ensemble) {
                return refuse(Refusal::Unauthorized);
            }
            return Decision::Persist;
        }
        let Some(state) = view.durable else {
            return refuse(Refusal::NotFound);
        };
        let promised =
            |epoch, holder| state.promised == Some((epoch, holder)) && view.same_principal;

        match request {
            Request::Seal {
                epoch,
                holder,
                ensemble,
                ..
            } => {
                if !view.seal_allowed {
                    return refuse(Refusal::Unauthorized);
                }
                if *ensemble != state.ensemble {
                    return wrong_ensemble(state);
                }
                let current = state.promised.map_or(0, |(current, _)| current.0);
                let identical = promised(*epoch, *holder);
                if !may_seal(state.promised.is_some(), current, epoch.0, identical) {
                    return fenced(state);
                }
                if identical {
                    Decision::Reply(Reply::Sealed(state.clone()))
                } else {
                    Decision::Persist
                }
            }
            Request::Sync {
                epoch,
                holder,
                floor,
                from,
                records,
                runs,
                commit,
                complete,
                ..
            } => {
                if !promised(*epoch, *holder) {
                    return fenced(state);
                }
                let Some(end) = last(*from, records.len()) else {
                    return refuse(Refusal::Gap { end: state.end });
                };
                if floor.0 == 0 || *floor > *from || *from < state.floor {
                    return refuse(Refusal::BelowFloor { floor: state.floor });
                }
                if !sync_commit_valid(state.commit.0, commit.0, end.0, floor.0) {
                    return refuse(Refusal::AboveCommit {
                        commit: state.commit,
                    });
                }
                if *from > Lsn(state.end.0 + 1) && from != floor {
                    return refuse(Refusal::Gap { end: state.end });
                }
                if !valid_runs(*epoch, *from, end, runs)
                    || !preserves_commit(from.0, state.commit.0, view.identical)
                {
                    return refuse(Refusal::Conflict { end: state.end });
                }
                if state.synced == Some(*epoch) {
                    return if *complete
                        && view.identical
                        && end <= state.end
                        && *commit == state.commit
                        && *floor <= state.floor
                    {
                        Decision::Reply(Reply::Synced { end: state.end })
                    } else {
                        refuse(Refusal::Conflict { end: state.end })
                    };
                }
                let skip = (sync_start(state, *from, *floor).0 - from.0).min(records.len() as u64);
                capacity(
                    &records[skip as usize..],
                    view.retained_bytes,
                    state.floor,
                    limits,
                )
                .unwrap_or(Decision::Persist)
            }
            Request::Append {
                epoch,
                holder,
                at,
                records,
                commit,
                ..
            } => {
                if !may_append(
                    promised(*epoch, *holder),
                    state.synced == Some(*epoch) && !state.learner,
                ) {
                    return if promised(*epoch, *holder) {
                        refuse(Refusal::NotSynced)
                    } else {
                        fenced(state)
                    };
                }
                if *at < state.floor {
                    return refuse(Refusal::BelowFloor { floor: state.floor });
                }
                let Some(last) = last(*at, records.len()) else {
                    return refuse(Refusal::Gap { end: state.end });
                };
                let next = Lsn(state.end.0 + 1);
                if *at > next {
                    return refuse(Refusal::Gap { end: state.end });
                }
                if *at < next
                    && !append_retry(!records.is_empty(), last.0, state.end.0, view.identical)
                {
                    return refuse(Refusal::Conflict { end: state.end });
                }
                let end = state.end.max(last);
                if *commit > end {
                    return refuse(Refusal::AboveCommit {
                        commit: state.commit,
                    });
                }
                if *at < next || records.is_empty() {
                    return if *commit > state.commit {
                        Decision::Persist
                    } else {
                        Decision::Reply(Reply::Appended { end: state.end })
                    };
                }
                capacity(records, view.retained_bytes, state.floor, limits)
                    .unwrap_or(Decision::Persist)
            }
            Request::Trim {
                epoch,
                holder,
                through,
                ..
            } => {
                if !promised(*epoch, *holder) {
                    return fenced(state);
                }
                if state.synced != Some(*epoch) || state.learner {
                    return refuse(Refusal::NotSynced);
                }
                if !may_trim(through.0, state.commit.0) {
                    return refuse(Refusal::AboveCommit {
                        commit: state.commit,
                    });
                }
                if *through < state.floor {
                    Decision::Reply(Reply::Trimmed { floor: state.floor })
                } else {
                    Decision::Persist
                }
            }
            Request::Check { epoch, .. } => {
                let mut checked = state.clone();
                checked.end = Lsn(checked_end(state.end.0, epoch.0));
                Decision::Reply(Reply::Checked(checked))
            }
            Request::Read { from, .. } if !may_read(state.floor.0, from.0) => {
                refuse(Refusal::BelowFloor { floor: state.floor })
            }
            Request::Read { .. } => Decision::Page {
                through: Lsn(read_end(state.commit.0, state.end.0)),
            },
            Request::Recover {
                epoch,
                holder,
                from,
                ..
            } => {
                if !promised(*epoch, *holder) {
                    return fenced(state);
                }
                if !may_read(state.floor.0, from.0) {
                    return refuse(Refusal::BelowFloor { floor: state.floor });
                }
                Decision::Page { through: state.end }
            }
            Request::Replace {
                epoch,
                holder,
                from,
                to,
                ..
            } => {
                if !promised(*epoch, *holder) {
                    return fenced(state);
                }
                if state.synced != Some(*epoch) {
                    return refuse(Refusal::NotSynced);
                }
                if state.ensemble == *to {
                    return Decision::Reply(Reply::Replaced);
                }
                if state.ensemble != *from {
                    return wrong_ensemble(state);
                }
                let changed = from.iter().zip(to).filter(|(a, b)| a != b).count();
                if !valid_ensemble(to)
                    || !may_replace(
                        state.ensemble == *from,
                        state.synced == Some(*epoch),
                        to.contains(&view.keeper),
                        changed,
                    )
                {
                    return refuse(Refusal::Unauthorized);
                }
                Decision::Persist
            }
            Request::Create { .. } | Request::Delete { .. } => unreachable!(),
        }
    }

    pub(crate) fn valid_limits(limits: &Limits) -> bool {
        // Leave room for one recovery record, its epoch run, and the Sync header.
        (limits.max_record_bytes as usize) <= PAGE_BYTES - 128
    }
}
