//! Keeper decisions. Disk reads needed to compare a retry are supplied in the view.
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == !deleted))]
pub(crate) fn live(deleted: bool) -> bool {
    !deleted
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (!has_promise || current < epoch || (current == epoch && same_identity))
))]
pub(crate) fn may_seal(has_promise: bool, current: u64, epoch: u64, same_identity: bool) -> bool {
    !has_promise || current < epoch || (current == epoch && same_identity)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (same_owner && stored == requested)
))]
pub(super) fn seal_matches(same_owner: bool, stored: u128, requested: u128) -> bool {
    same_owner && stored == requested
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (epoch <= promised && first == next && first <= last && last <= tail)
))]
pub(super) fn valid_epoch_run(
    epoch: u64, promised: u64, first: u64, last: u64, next: u64, tail: u64,
) -> bool {
    epoch <= promised && first == next && first <= last && last <= tail
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == if len == 0 { 1 } else { len as u64 }
))]
pub(super) fn record_charge(len: usize) -> u64 {
    len.max(1) as u64
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (from > head || identical)))]
pub(crate) fn preserves_head(from: u64, head: u64, identical: bool) -> bool {
    from > head || identical
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (promised && synced)))]
pub(crate) fn may_append(promised: bool, synced: bool) -> bool {
    promised && synced
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (through <= head)))]
pub(crate) fn may_trim(through: u64, head: u64) -> bool {
    through <= head
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == current))]
pub(crate) fn checked_tail(current: u64, _request_epoch: u64) -> u64 {
    current
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == head))]
pub(crate) fn read_head(head: u64, _accepted: u64) -> u64 {
    head
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (deleted || deleting)))]
pub(crate) fn tombstone(deleted: bool, deleting: bool) -> bool {
    deleted || deleting
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (current <= next && next <= tail && 0 < floor && floor as int <= next as int + 1)
))]
pub(crate) fn sync_head_valid(current: u64, next: u64, tail: u64, floor: u64) -> bool {
    current <= next && next <= tail && floor > 0 && floor - 1 <= next
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (nonempty && last <= tail && identical)))]
pub(crate) fn append_retry(nonempty: bool, last: u64, tail: u64, identical: bool) -> bool {
    nonempty && last <= tail && identical
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (floor <= from)))]
pub(crate) fn may_read(floor: u64, from: u64) -> bool {
    floor <= from
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (current && synced && member && changed == 1)))]
pub(crate) fn may_replace(current: bool, synced: bool, member: bool, changed: usize) -> bool {
    current && synced && member && changed == 1
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (first != 0 && second != 0 && third != 0
        && first != second && first != third && second != third)
))]
pub(crate) fn valid_ensemble_ids(first: u128, second: u128, third: u128) -> bool {
    first != 0 && second != 0 && third != 0 && first != second && first != third && second != third
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (to, false)))]
pub(crate) fn install_ensemble<T>(to: T) -> (T, bool) {
    (to, false)
}

pub(crate) enum ReplaceDecision {
    Fenced,
    NotSynced,
    Replaced,
    WrongEnsemble,
    Unauthorized,
    Persist,
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out ==
    if !promised { ReplaceDecision::Fenced }
    else if !synced { ReplaceDecision::NotSynced }
    else if installed { ReplaceDecision::Replaced }
    else if !current { ReplaceDecision::WrongEnsemble }
    else if valid && member && changed == 1 { ReplaceDecision::Persist }
    else { ReplaceDecision::Unauthorized }
))]
pub(crate) fn decide_replace(
    promised: bool,
    synced: bool,
    installed: bool,
    current: bool,
    valid: bool,
    member: bool,
    changed: usize,
) -> ReplaceDecision {
    if !promised {
        ReplaceDecision::Fenced
    } else if !synced {
        ReplaceDecision::NotSynced
    } else if installed {
        ReplaceDecision::Replaced
    } else if !current {
        ReplaceDecision::WrongEnsemble
    } else if valid && may_replace(current, synced, member, changed) {
        ReplaceDecision::Persist
    } else {
        ReplaceDecision::Unauthorized
    }
}

#[cfg(not(verus_keep_ghost))]
pub use implementation::Limits;
#[cfg(not(verus_keep_ghost))]
pub(super) use implementation::{
    Decision, StreamView, decide, installs_floor, promised, sync_start, valid_limits,
};

#[cfg(not(verus_keep_ghost))]
mod implementation {
    use super::*;
    use crate::stream::{
        codec::PAGE_BYTES,
        wire::{self, *},
    };
    use bytes::Bytes;

    /// Byte limits are per stream. The request limit bounds each round queue.
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
        pub round_requests: usize,
    }

    impl Default for Limits {
        fn default() -> Self {
            Self {
                stream_quota_bytes: 8 * 1024 * 1024 * 1024,
                max_record_bytes: 32 * 1024 * 1024,
                round_bytes_per_stream: 4 * 1024 * 1024,
                round_requests: 64,
            }
        }
    }

    /// A projection of the stream plus facts obtained by comparing retained payloads.
    pub(crate) struct StreamView<'a> {
        pub keeper: KeeperId,
        pub durable: Option<&'a wire::StreamView>,
        pub deleted: bool,
        /// The floor and tail of an incomplete Sync's history.
        pub staged: Option<(Lsn, Lsn)>,
        pub identity: &'a Identity,
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
            promised: state
                .promised
                .as_ref()
                .map_or(Epoch(0), |(epoch, ..)| *epoch),
        })
    }

    fn wrong_ensemble(state: &wire::StreamView) -> Decision {
        refuse(Refusal::WrongEnsemble {
            ensemble: state.ensemble,
        })
    }

    fn valid_ensemble(ensemble: &[KeeperId; 3]) -> bool {
        let [KeeperId(first), KeeperId(second), KeeperId(third)] = *ensemble;
        valid_ensemble_ids(first, second, third)
    }

    // Reserve one LSN to represent the floor of a fully trimmed stream.
    pub(crate) fn last(from: Lsn, count: usize) -> Option<Lsn> {
        from.0
            .checked_sub(1)?
            .checked_add(count as u64)
            .filter(|tail| *tail != u64::MAX)
            .map(Lsn)
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
            .fold(retained, |sum, record| sum.saturating_add(record_charge(record.len())));
        (bytes > limits.stream_quota_bytes).then(|| refuse(Refusal::Full { floor }))
    }

    fn valid_runs(epoch: Epoch, from: Lsn, tail: Lsn, runs: &[EpochRun]) -> bool {
        let mut next = from.0;
        for run in runs {
            if !valid_epoch_run(run.epoch.0, epoch.0, run.first.0, run.last.0, next, tail.0) {
                return false;
            }
            next = run.last.0 + 1;
        }
        next == tail.0 + 1
    }

    pub(crate) fn sync_start(state: &wire::StreamView, from: Lsn, floor: Lsn) -> Lsn {
        from.max(state.floor).max(floor).max(Lsn(state.head.0 + 1))
    }

    pub(crate) fn installs_floor(state: &wire::StreamView, request: &Request) -> bool {
        matches!(request, Request::Sync {
            epoch, floor, from, records, runs, head, complete: false, ..
        } if state.synced == Some(*epoch)
            && floor == from && floor.0.checked_sub(1) == Some(head.0)
            && records.is_empty() && runs.is_empty())
    }

    pub(crate) fn promised(state: &wire::StreamView, epoch: Epoch, identity: &Identity) -> bool {
        state
            .promised
            .as_ref()
            .is_some_and(|(current, owner, _)| *current == epoch && owner == identity)
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
        let promised = |epoch| promised(state, epoch, view.identity);

        match request {
            Request::Seal {
                epoch,
                ensemble,
                proposal,
                ..
            } => {
                if !view.seal_allowed {
                    return refuse(Refusal::Unauthorized);
                }
                if *ensemble != state.ensemble {
                    return wrong_ensemble(state);
                }
                let current = state.promised.as_ref().map_or(0, |(current, ..)| current.0);
                let identical = state.promised.as_ref().is_some_and(|(current, owner, id)| {
                    seal_matches(current == epoch && owner == view.identity, *id, *proposal)
                });
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
                floor,
                from,
                records,
                runs,
                head,
                complete,
                ..
            } => {
                if !promised(*epoch) {
                    return fenced(state);
                }
                // A synced replica can skip a prefix that the writer has already trimmed.
                // This Sync form never replaces the retained suffix or lowers the head.
                if installs_floor(state, request) {
                    return if *floor > state.floor {
                        Decision::Persist
                    } else {
                        Decision::Reply(Reply::Synced { tail: state.tail })
                    };
                }
                let Some(tail) = last(*from, records.len()) else {
                    return refuse(Refusal::Gap { head: state.head });
                };
                let (floor, image_tail) = view
                    .staged
                    .map_or((*floor, state.tail), |(staged, tail)| (staged.max(*floor), tail));
                if floor.0 == 0 || floor > *from || *from < state.floor {
                    return refuse(Refusal::BelowFloor { floor: state.floor });
                }
                if !sync_head_valid(state.head.0, head.0, tail.0, floor.0) {
                    return refuse(Refusal::AboveHead { head: state.head });
                }
                if *from > Lsn(image_tail.0 + 1) && *from != floor {
                    return refuse(Refusal::Gap { head: state.head });
                }
                if !valid_runs(*epoch, *from, tail, runs)
                    || !preserves_head(from.0, state.head.0, view.identical)
                {
                    return refuse(Refusal::Conflict { head: state.head });
                }
                if state.synced == Some(*epoch) {
                    return if *complete
                        && view.identical
                        && tail <= state.tail
                        && *head == state.head
                        && floor <= state.floor
                    {
                        Decision::Reply(Reply::Synced { tail: state.tail })
                    } else {
                        refuse(Refusal::Conflict { head: state.head })
                    };
                }
                let skip = (sync_start(state, *from, floor).0 - from.0).min(records.len() as u64);
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
                at,
                records,
                head,
                ..
            } => {
                if !may_append(
                    promised(*epoch),
                    state.synced == Some(*epoch) && !state.learner,
                ) {
                    return if promised(*epoch) {
                        refuse(Refusal::NotSynced)
                    } else {
                        fenced(state)
                    };
                }
                if *at < state.floor {
                    return refuse(Refusal::BelowFloor { floor: state.floor });
                }
                let Some(last) = last(*at, records.len()) else {
                    return refuse(Refusal::Gap { head: state.head });
                };
                let next = Lsn(state.tail.0 + 1);
                if *at > next {
                    return refuse(Refusal::Gap { head: state.head });
                }
                if *at < next
                    && !records.is_empty()
                    && !append_retry(!records.is_empty(), last.0, state.tail.0, view.identical)
                {
                    return refuse(Refusal::Conflict { head: state.head });
                }
                let tail = state.tail.max(last);
                if *head > tail {
                    return refuse(Refusal::AboveHead { head: state.head });
                }
                if *at < next || records.is_empty() {
                    return if *head > state.head {
                        Decision::Persist
                    } else {
                        Decision::Reply(Reply::Appended { tail: state.tail })
                    };
                }
                capacity(records, view.retained_bytes, state.floor, limits)
                    .unwrap_or(Decision::Persist)
            }
            Request::Trim { epoch, through, .. } => {
                if !promised(*epoch) {
                    return fenced(state);
                }
                if state.synced != Some(*epoch) || state.learner {
                    return refuse(Refusal::NotSynced);
                }
                if !may_trim(through.0, state.head.0) {
                    return refuse(Refusal::AboveHead { head: state.head });
                }
                if *through < state.floor {
                    Decision::Reply(Reply::Trimmed { floor: state.floor })
                } else {
                    Decision::Persist
                }
            }
            Request::Check { epoch, .. } => {
                let mut checked = state.clone();
                checked.tail = Lsn(checked_tail(state.tail.0, epoch.0));
                Decision::Reply(Reply::Checked(checked))
            }
            Request::Read { from, .. } if !may_read(state.floor.0, from.0) => {
                refuse(Refusal::BelowFloor { floor: state.floor })
            }
            Request::Read { .. } => Decision::Page {
                through: Lsn(read_head(state.head.0, state.tail.0)),
            },
            Request::Recover { epoch, from, .. } => {
                if !promised(*epoch) {
                    return fenced(state);
                }
                if !may_read(state.floor.0, from.0) {
                    return refuse(Refusal::BelowFloor { floor: state.floor });
                }
                Decision::Page {
                    through: state.tail,
                }
            }
            Request::Replace {
                epoch, from, to, ..
            } => {
                let changed = from.iter().zip(to).filter(|(a, b)| a != b).count();
                match decide_replace(
                    promised(*epoch),
                    state.synced == Some(*epoch),
                    state.ensemble == *to,
                    state.ensemble == *from,
                    valid_ensemble(to),
                    to.contains(&view.keeper),
                    changed,
                ) {
                    ReplaceDecision::Fenced => fenced(state),
                    ReplaceDecision::NotSynced => refuse(Refusal::NotSynced),
                    ReplaceDecision::Replaced => Decision::Reply(Reply::Replaced),
                    ReplaceDecision::WrongEnsemble => wrong_ensemble(state),
                    ReplaceDecision::Unauthorized => refuse(Refusal::Unauthorized),
                    ReplaceDecision::Persist => Decision::Persist,
                }
            }
            // `Keeper::call` splits envelopes before any per-stream decision.
            Request::Batch(_) => refuse(Refusal::Unauthorized),
            Request::Create { .. } | Request::Delete { .. } => unreachable!(),
        }
    }

    pub(crate) fn valid_limits(limits: &Limits) -> bool {
        // Leave room for one recovery record, its epoch run, and the Sync header.
        (limits.max_record_bytes as usize) <= PAGE_BYTES - 128
    }
}
