//! Interval selection for building an offload restore plan.

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// The portion of this lineage above the requested floor and before its
/// successor. Leave space for the cursor one past the final record.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out == window(start as int, floor as int, successor),
        out matches Some((first, last)) ==> first <= last && last < u64::MAX,
))]
pub(super) fn restore_window(start: u64, floor: u64, successor: Option<u64>) -> Option<(u64, u64)> {
    let last = match successor {
        Some(next) => next.saturating_sub(1),
        None => u64::MAX - 1,
    };
    let first = start.max(floor);
    if first <= last {
        Some((first, last))
    } else {
        None
    }
}

/// Reuse the previous run only if it reaches the new lineage's window.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires previous matches Some(last) ==> last < u64::MAX,
    ensures
        out.1 == (previous matches Some(last) && (last as int + 1) >= first),
        out.1 ==> (previous matches Some(last) && out.0 as int == last as int + 1),
        !out.1 ==> out.0 == first,
))]
pub(super) fn restore_cursor(previous: Option<u64>, first: u64) -> (u64, bool) {
    match previous {
        Some(last) if last + 1 >= first => (last + 1, true),
        _ => (first, false),
    }
}

/// A covered cursor can advance only through both the selected object and
/// the current lineage's window.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires _cursor <= object_end, _cursor <= window_end, window_end < u64::MAX,
    ensures _cursor <= out.0 <= object_end, out.0 <= window_end,
        out.0 == object_end || out.0 == window_end,
        out.1 as int == out.0 as int + 1,
))]
pub(super) fn restore_cut(_cursor: u64, object_end: u64, window_end: u64) -> (u64, u64) {
    let last = object_end.min(window_end);
    (last, last + 1)
}

pub(super) enum Selection {
    Object(usize),
    Gap(u64),
    End,
}

/// Choose the covering object with the greatest end, preferring the later
/// listing on ties. With no cover, restart at the first object after the gap.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires cursor <= end,
    ensures
        out matches Selection::Object(i) ==> i < ranges@.len()
            && covers(ranges@[i as int], cursor)
            && (forall|j: int| 0 <= j < ranges@.len() && covers(#[trigger] ranges@[j], cursor)
                ==> ranges@[j].1 <= ranges@[i as int].1
                    && (ranges@[j].1 == ranges@[i as int].1 ==> j <= i)),
        !(out is Object) ==> (forall|j: int| 0 <= j < ranges@.len()
            ==> !covers(#[trigger] ranges@[j], cursor)),
        out matches Selection::Gap(first) ==> cursor < first <= end
            && (exists|j: int| 0 <= j < ranges@.len() && (#[trigger] ranges@[j]).0 == first)
            && (forall|j: int| 0 <= j < ranges@.len() && cursor < (#[trigger] ranges@[j]).0 <= end
                ==> first <= ranges@[j].0),
        out is End ==> (forall|j: int| 0 <= j < ranges@.len()
            ==> !(cursor < (#[trigger] ranges@[j]).0 <= end)),
))]
pub(super) fn select_restore_object(ranges: &[(u64, u64)], cursor: u64, end: u64) -> Selection {
    let mut best: Option<(usize, u64)> = None;
    let mut after: Option<u64> = None;
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= ranges@.len(), cursor <= end,
            best matches Some((index, last)) ==> index < i && covers(ranges@[index as int], cursor)
                && ranges@[index as int].1 == last
                && (forall|j: int| 0 <= j < i && covers(#[trigger] ranges@[j], cursor)
                    ==> ranges@[j].1 <= last && (ranges@[j].1 == last ==> j <= index)),
            best is None ==> (forall|j: int| 0 <= j < i ==> !covers(#[trigger] ranges@[j], cursor)),
            after matches Some(first) ==> cursor < first <= end
                && (exists|j: int| 0 <= j < i && (#[trigger] ranges@[j]).0 == first)
                && (forall|j: int| 0 <= j < i && cursor < (#[trigger] ranges@[j]).0 <= end
                    ==> first <= ranges@[j].0),
            after is None ==> (forall|j: int| 0 <= j < i
                ==> !(cursor < (#[trigger] ranges@[j]).0 <= end)),
        decreases ranges@.len() - i,
    ))]
    while i < ranges.len() {
        let (first, last) = ranges[i];
        if first <= cursor && cursor <= last {
            if match best {
                Some((_, current)) => last >= current,
                None => true,
            } {
                best = Some((i, last));
            }
        } else if cursor < first
            && first <= end
            && match after {
                Some(current) => first < current,
                None => true,
            }
        {
            after = Some(first);
        }
        i += 1;
    }
    match (best, after) {
        (Some((i, _)), _) => Selection::Object(i),
        (None, Some(first)) => Selection::Gap(first),
        (None, None) => Selection::End,
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(super) open spec fn window(start: int, floor: int, successor: Option<u64>) -> Option<(u64, u64)> {
        let last = match successor {
            Some(next) => if next == 0 { 0 } else { next as int - 1 },
            None => u64::MAX as int - 1,
        };
        let first = if start > floor { start } else { floor };
        if first <= last { Some((first as u64, last as u64)) } else { None }
    }

    pub(super) open spec fn covers(range: (u64, u64), cursor: u64) -> bool {
        range.0 <= cursor <= range.1
    }
}
