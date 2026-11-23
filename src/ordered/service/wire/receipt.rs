use crate::ordered::service::wire::SignedBarrier;
use crate::ordered::{Outcome, Placement, Principal, Receipt, Request};

#[cfg(verus_keep_ghost)]
use {crate::reference::*, vstd::prelude::*};

/// Relates a decoded decision to its signed barrier claim, if present.
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == exactBarrierReceipt(receipt, barrier),
))]
pub(crate) fn barrier_receipt_matches(receipt: Receipt, barrier: Option<SignedBarrier>) -> bool {
    match (receipt.outcome, barrier) {
        (Ok(Outcome::Barrier { read }), Some(SignedBarrier { claim, .. })) => {
            read == claim.read
                && receipt.placement == claim.placement
                && receipt.principal == Principal::Worker(read.owner)
                && receipt.request == read.id
                && receipt.position == read.admitted_at
        }
        (Ok(Outcome::Barrier { .. }), None) | (_, Some(_)) => false,
        (_, None) => true,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == exactReceiptScope(receipt, placement, request),
))]
pub(crate) fn receipt_scope_matches(
    receipt: Receipt,
    placement: Placement,
    request: &Request,
) -> bool {
    receipt.placement == placement
        && receipt.principal == request.principal
        && receipt.request == request.id
}
