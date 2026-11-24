#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Index the exact retained interval, with an exclusive upper cut.
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    (out is Some) == (floor <= from && from <= through && through as int - floor as int <= retained),
    out matches Some((first, end)) ==> first <= end <= retained
        && floor as int + first as int == from as int
        && floor as int + end as int == through as int,
))]
pub(super) fn retained_indices(
    floor: u64, from: u64, through: u64, retained: usize,
) -> Option<(usize, usize)> {
    if floor > from || from > through || through - floor > retained as u64 {
        return None;
    }
    Some(((from - floor) as usize, (through - floor) as usize))
}

/// An exact cursor can resume at any cut within the original protected interval.
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    out == if exact_cut && start <= from && from <= through && from as int - start as int <= usize::MAX as int {
        Some((from as int - start as int) as usize)
    } else { None },
))]
pub(super) fn cursor_offset(start: u64, from: u64, through: u64, exact_cut: bool) -> Option<usize> {
    if !exact_cut || from < start || from > through {
        return None;
    }
    let offset = from - start;
    if offset > usize::MAX as u64 {
        return None;
    }
    Some(offset as usize)
}

#[cfg_attr(verus_keep_ghost, verus_spec(charge => ensures
    (charge is Some) == (from as int + 1 == record_cut && record_cut <= through && byte_start <= byte_end),
    charge matches Some(bytes) ==> bytes as int == byte_end as int - byte_start as int,
))]
pub(super) fn replay_record_charge(
    from: u64, record_cut: u64, through: u64, byte_start: u64, byte_end: u64,
) -> Option<u64> {
    if from.checked_add(1) != Some(record_cut) || record_cut > through {
        return None;
    }
    byte_end.checked_sub(byte_start)
}

pub(super) type ReplayCut = (u64, [u8; 32]);

pub(super) struct ReplayCursor {
    pub(super) next: ReplayCut,
    pub(super) through: ReplayCut,
    pub(super) remaining: u64,
    pub(super) emitted: bool,
}

pub(super) struct ReplayRecord<T> {
    pub(super) cut: ReplayCut,
    pub(super) start: u64,
    pub(super) end: u64,
    pub(super) original: T,
}

pub(super) enum ReplayStep<T> {
    Emit(T, u64),
    Complete,
    PageFull,
    Capacity,
    Invalid,
}

#[cfg(verus_keep_ghost)]
verus! {
pub(super) open spec fn selected_cut(left: ReplayCut, right: ReplayCut) -> bool {
    left.0 == right.0 && left.1@ == right.1@
}

pub(super) open spec fn exact_record(
    next: ReplayCut, through: ReplayCut, record: ReplayCut, start: u64, end: u64,
) -> bool {
    next.0 as int + 1 == record.0 && record.0 <= through.0 && start <= end
        && (record.0 == through.0 ==> selected_cut(record, through))
}
}

#[cfg_attr(verus_keep_ghost, verus_spec(equal => ensures
    equal == selected_cut(left, right),
))]
fn same_cut(left: ReplayCut, right: ReplayCut) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! {
        if forall|i: int| #![auto] 0 <= i < 32 ==> left.1@[i] == right.1@[i] {
            assert(left.1@ =~= right.1@);
        }
    }
    left.0 == right.0 && left.1 == right.1
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
    out.next == next, out.through == through, out.remaining == remaining, !out.emitted,
))]
pub(super) fn replay_cursor(next: ReplayCut, through: ReplayCut, remaining: u64) -> ReplayCursor {
    ReplayCursor { next, through, remaining, emitted: false }
}

impl ReplayCursor {
    /// Accept one resident record or the source's end event. A full page leaves
    /// the first unreturned record for the next request at the last emitted cut.
    #[cfg_attr(verus_keep_ghost, verus_spec(out => ensures
        final(self).through == old(self).through,
        match record {
            None => if selected_cut(old(self).next, old(self).through) {
                out is Complete
            } else { out is Invalid },
            Some(entry) =>
                if !exact_record(old(self).next, old(self).through, entry.cut, entry.start, entry.end) {
                    out is Invalid
                } else if entry.end as int - entry.start <= old(self).remaining {
                    out matches ReplayStep::Emit(original, bytes) && original == entry.original
                        && bytes as int == entry.end as int - entry.start
                        && final(self).next == entry.cut && final(self).emitted
                        && final(self).remaining as int + bytes == old(self).remaining
                } else if old(self).emitted { out is PageFull } else { out is Capacity },
        },
        !(out is Emit) ==> final(self).next == old(self).next
            && final(self).emitted == old(self).emitted
            && final(self).remaining == old(self).remaining,
    ))]
    pub(super) fn step<T>(&mut self, record: Option<ReplayRecord<T>>) -> ReplayStep<T> {
        let Some(ReplayRecord { cut, start, end, original }) = record else {
            return if same_cut(self.next, self.through) {
                ReplayStep::Complete
            } else {
                ReplayStep::Invalid
            };
        };
        let Some(bytes) = replay_record_charge(self.next.0, cut.0, self.through.0, start, end) else {
            return ReplayStep::Invalid;
        };
        if cut.0 == self.through.0 && !same_cut(cut, self.through) {
            return ReplayStep::Invalid;
        }

        let Some(remaining) = self.remaining.checked_sub(bytes) else {
            return if self.emitted { ReplayStep::PageFull } else { ReplayStep::Capacity };
        };
        self.next = cut;
        self.remaining = remaining;
        self.emitted = true;
        ReplayStep::Emit(original, bytes)
    }
}
