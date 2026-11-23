// Refinement of Logkeeper.Premises.BarrierKeys and .SignatureScope.
#![allow(non_snake_case)]

use crate::{
    contracts::{be64, receipt_bytes, signed_message, Uuid},
    ordered::{*, service::wire::{Signature, SignedBarrier}},
    production::{receipt_keys::ReceiptKeys, signed::{BARRIER_DOMAIN, ROTATION_DOMAIN}},
};
use vstd::prelude::*;

verus! {

pub(crate) open spec fn verificationKeys(roster: &ReceiptKeys) -> Set<Fingerprint> {
    roster.active@.values().union(roster.predecessor@.to_set()).union(roster.retained@.to_set())
}

pub(crate) open spec fn repairAuthority(roster: &ReceiptKeys, key: Fingerprint) -> bool {
    roster.predecessor@.contains(key)
}

pub(crate) open spec fn validSuccessorKeys(source: &ReceiptKeys, target: &ReceiptKeys) -> bool {
    target.predecessor@.to_set().subset_of(source.active@.values())
        && verificationKeys(source).subset_of(verificationKeys(target))
}

pub open spec fn canonicalStart(claim: BarrierClaim) -> bool {
    claim.read.start == claim.read.checkpoint.cut
}

pub open spec fn exactBarrierInvocation(
    scope: Placement, expected: &Request, claim: BarrierClaim,
) -> bool {
    expected.command is Barrier
        && claim.placement == scope
        && expected.placement == scope
        && expected.principal == Principal::Worker(claim.read.owner)
        && claim.read.id == expected.id
}

pub open spec fn exactBarrierReceipt(receipt: Receipt, barrier: Option<SignedBarrier>) -> bool {
    match (receipt.outcome, barrier) {
        (Ok(Outcome::Barrier { read }), Some(attestation)) =>
            read == attestation.claim.read
                && receipt.placement == attestation.claim.placement
                && receipt.principal == Principal::Worker(read.owner)
                && receipt.request == read.id
                && receipt.position == read.admitted_at,
        (Ok(Outcome::Barrier { .. }), None) | (_, Some(_)) => false,
        (_, None) => true,
    }
}

pub open spec fn exactReceiptScope(receipt: Receipt, scope: Placement, request: &Request) -> bool {
    receipt.placement == scope && receipt.principal == request.principal && receipt.request == request.id
}

pub open spec fn authenticates(
    keys: Map<Fingerprint, Fingerprint>, signature: Signature, bytes: Seq<u8>,
) -> bool {
    keys.contains_key(signature.issuer)
        && signed_message(keys[signature.issuer], signature.proof@) == Some(bytes)
}

pub open spec fn uuid_bytes(value: Uuid) -> Seq<u8> {
    value.bytes@
}

pub open spec fn request_id_bytes(value: RequestId) -> Seq<u8> {
    uuid_bytes(value.nonce) + be64(value.expires_at)
}

pub open spec fn placement_bytes(value: Placement) -> Seq<u8> {
    ((uuid_bytes(value.deployment) + uuid_bytes(value.incarnation)) + uuid_bytes(value.group))
        + be64(value.generation)
}

pub open spec fn enrollment_bytes(value: Enrollment) -> Seq<u8> {
    uuid_bytes(value.worker) + be64(value.serial)
}

pub open spec fn cut_bytes(value: Cut) -> Seq<u8> {
    be64(value.next_lsn) + value.history@
}

pub open spec fn checkpoint_bytes(value: Checkpoint) -> Seq<u8> {
    (((((cut_bytes(value.cut) + value.root@) + value.manifest@)
        + uuid_bytes(value.custody.allocation)) + be64(value.custody.revision))
        + value.custody.provider@)
}

pub open spec fn domain_bytes(tag: Seq<char>) -> Seq<u8> {
    vstd::utf8::encode_utf8(tag)
}

pub open spec fn barrier_bytes(claim: BarrierClaim) -> Seq<u8> {
    (((((domain_bytes(BARRIER_DOMAIN@) + placement_bytes(claim.placement))
        + enrollment_bytes(claim.read.owner)) + request_id_bytes(claim.read.id))
        + be64(claim.read.admitted_at)) + checkpoint_bytes(claim.read.checkpoint))
        + cut_bytes(claim.read.through)
}

pub open spec fn rotation_bytes(evidence: RotationSlots, receipt: Receipt) -> Seq<u8> {
    (domain_bytes(ROTATION_DOMAIN@) + receipt_bytes(receipt)) + evidence_bytes(evidence)
}

pub broadcast proof fn be64_width(value: u64)
    ensures #[trigger] be64(value).len() == 8,
{
    vstd::bytes::spec_u64_to_le_bytes_to_open(value);
}

}
