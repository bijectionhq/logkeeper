#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

// A slot is bound to a single keeper of the ensemble and to the append request.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == match ack {
        Some((accepted_epoch, tail)) => accepted_epoch == epoch && tail >= at,
        None => false,
    }
))]
pub(super) fn covers(ack: Option<(u64, u64)>, epoch: u64, at: u64) -> bool {
    match ack {
        Some((accepted_epoch, tail)) => accepted_epoch == epoch && tail >= at,
        None => false,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (
        ((a matches Some((ae, an)) && ae == epoch && an >= at)
            && (b matches Some((be, bn)) && be == epoch && bn >= at))
        || ((a matches Some((ae, an)) && ae == epoch && an >= at)
            && (c matches Some((ce, cn)) && ce == epoch && cn >= at))
        || ((b matches Some((be, bn)) && be == epoch && bn >= at)
            && (c matches Some((ce, cn)) && ce == epoch && cn >= at))
    )
))]
pub(super) fn acknowledged(
    a: Option<(u64, u64)>,
    b: Option<(u64, u64)>,
    c: Option<(u64, u64)>,
    epoch: u64,
    at: u64,
) -> bool {
    let a = covers(a, epoch, at);
    let b = covers(b, epoch, at);
    let c = covers(c, epoch, at);
    (a && b) || (a && c) || (b && c)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == match (left, right) {
        (Some(a), Some(b)) => b > a || (b == a && right_tail > left_tail),
        (None, Some(_)) => true,
        (None, None) => right_tail > left_tail,
        (Some(_), None) => false,
    }
))]
pub(super) fn outranks(
    left: Option<u64>,
    left_tail: u64,
    right: Option<u64>,
    right_tail: u64,
) -> bool {
    match (left, right) {
        (Some(a), Some(b)) => b > a || (b == a && right_tail > left_tail),
        (None, Some(_)) => true,
        (None, None) => right_tail > left_tail,
        (Some(_), None) => false,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (
        if checked.is_some() { checked == Some(expected) } else { false }
    )
))]
pub(super) fn matches_epoch(checked: Option<u64>, expected: u64) -> bool {
    checked == Some(expected)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (
        if head < last { head } else { last }
    )
))]
pub(super) fn append_head(head: u64, last: u64) -> u64 {
    head.min(last)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (
        if issued < last { last }
        else if tail < last { last }
        else if tail < issued { tail }
        else { issued }
    )
))]
pub(super) fn accepted_tail(tail: u64, issued: u64, last: u64) -> u64 {
    tail.min(issued).max(last)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (opened < sent)
))]
pub(super) fn fresh_sample(opened: u64, sent: u64) -> bool {
    sent > opened
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (if a < b { b } else { a })
))]
pub(super) fn sample_index(a: u64, b: u64) -> u64 {
    a.max(b)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (floor <= start && head < start && (floor == start || matched))
))]
pub(super) fn can_sync_from(floor: u64, head: u64, start: u64, matched: bool) -> bool {
    floor <= start && head < start && (floor == start || matched)
}
