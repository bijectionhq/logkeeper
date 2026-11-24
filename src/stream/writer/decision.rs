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
