use crate::{
    contracts::{be64, fingerprint, signed_message, Uuid},
    ordered::{*, service::wire::{SignedBarrier, SignedRotationSlots}},
    production::{
        receipt::{barrier_receipt_matches, receipt_scope_matches},
        receipt_keys::ReceiptKeys,
        repair::verify_repair_signature,
        signed::{BARRIER_DOMAIN, ROTATION_DOMAIN, barrier_domain_keeps_its_protocol_spelling, decode_barrier_claim, rotation_domain_keeps_its_protocol_spelling},
        verification::BarrierVerifier,
    },
    reference::*,
};
use vstd::prelude::*;

verus! {


broadcast use be64_width;

proof fn equal_parts(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>, d: Seq<u8>)
    requires a.len() == c.len(), a + b == c + d,
    ensures a == c, b == d,
{
    assert((a + b).take(a.len() as int) =~= a);
    assert((c + d).take(c.len() as int) =~= c);
    assert((a + b).skip(a.len() as int) =~= b);
    assert((c + d).skip(c.len() as int) =~= d);
}

proof fn equal_uuid(a: Uuid, b: Uuid)
    requires uuid_bytes(a) == uuid_bytes(b),
    ensures a == b,
{
    assert(a.bytes =~= b.bytes);
}

proof fn equal_u64(a: u64, b: u64)
    requires be64(a) == be64(b),
    ensures a == b,
{
    vstd::bytes::lemma_auto_spec_u64_to_from_le_bytes();
    assert(be64(a).reverse() =~= vstd::bytes::spec_u64_to_le_bytes(a));
    assert(be64(b).reverse() =~= vstd::bytes::spec_u64_to_le_bytes(b));
}

proof fn equal_placement(a: Placement, b: Placement)
    requires placement_bytes(a) == placement_bytes(b),
    ensures a == b,
{
    let ad = uuid_bytes(a.deployment);
    let bd = uuid_bytes(b.deployment);
    let ai = uuid_bytes(a.incarnation);
    let bi = uuid_bytes(b.incarnation);
    let ag = uuid_bytes(a.group);
    let bg = uuid_bytes(b.group);
    equal_parts((ad + ai) + ag, be64(a.generation), (bd + bi) + bg, be64(b.generation));
    equal_parts(ad + ai, ag, bd + bi, bg);
    equal_parts(ad, ai, bd, bi);
    equal_uuid(a.deployment, b.deployment);
    equal_uuid(a.incarnation, b.incarnation);
    equal_uuid(a.group, b.group);
    equal_u64(a.generation, b.generation);
}

proof fn equal_cut(a: Cut, b: Cut)
    requires cut_bytes(a) == cut_bytes(b),
    ensures a == b,
{
    equal_parts(be64(a.next_lsn), a.history@, be64(b.next_lsn), b.history@);
    equal_u64(a.next_lsn, b.next_lsn);
    assert(a.history =~= b.history);
}

proof fn equal_checkpoint(a: Checkpoint, b: Checkpoint)
    requires checkpoint_bytes(a) == checkpoint_bytes(b),
    ensures a == b,
{
    let a0 = cut_bytes(a.cut);
    let b0 = cut_bytes(b.cut);
    let a1 = a0 + a.root@;
    let b1 = b0 + b.root@;
    let a2 = a1 + a.manifest@;
    let b2 = b1 + b.manifest@;
    let a3 = a2 + uuid_bytes(a.custody.allocation);
    let b3 = b2 + uuid_bytes(b.custody.allocation);
    let a4 = a3 + be64(a.custody.revision);
    let b4 = b3 + be64(b.custody.revision);
    equal_parts(a4, a.custody.provider@, b4, b.custody.provider@);
    equal_parts(a3, be64(a.custody.revision), b3, be64(b.custody.revision));
    equal_parts(a2, uuid_bytes(a.custody.allocation), b2, uuid_bytes(b.custody.allocation));
    equal_parts(a1, a.manifest@, b1, b.manifest@);
    equal_parts(a0, a.root@, b0, b.root@);
    equal_cut(a.cut, b.cut);
    equal_uuid(a.custody.allocation, b.custody.allocation);
    equal_u64(a.custody.revision, b.custody.revision);
    assert(a.custody.provider =~= b.custody.provider);
    assert(a.manifest =~= b.manifest);
    assert(a.root =~= b.root);
}

proof fn canonical_fields_bind_claim(a: BarrierClaim, b: BarrierClaim)
    requires canonicalStart(a), canonicalStart(b), barrier_bytes(a) == barrier_bytes(b),
    ensures a == b,
{
    let a0 = domain_bytes(BARRIER_DOMAIN@) + placement_bytes(a.placement);
    let b0 = domain_bytes(BARRIER_DOMAIN@) + placement_bytes(b.placement);
    let a1 = a0 + enrollment_bytes(a.read.owner);
    let b1 = b0 + enrollment_bytes(b.read.owner);
    let a2 = a1 + request_id_bytes(a.read.id);
    let b2 = b1 + request_id_bytes(b.read.id);
    let a3 = a2 + be64(a.read.admitted_at);
    let b3 = b2 + be64(b.read.admitted_at);
    let a4 = a3 + checkpoint_bytes(a.read.checkpoint);
    let b4 = b3 + checkpoint_bytes(b.read.checkpoint);
    equal_parts(a4, cut_bytes(a.read.through), b4, cut_bytes(b.read.through));
    equal_parts(a3, checkpoint_bytes(a.read.checkpoint), b3, checkpoint_bytes(b.read.checkpoint));
    equal_parts(a2, be64(a.read.admitted_at), b2, be64(b.read.admitted_at));
    equal_parts(a1, request_id_bytes(a.read.id), b1, request_id_bytes(b.read.id));
    equal_parts(a0, enrollment_bytes(a.read.owner), b0, enrollment_bytes(b.read.owner));
    equal_parts(domain_bytes(BARRIER_DOMAIN@), placement_bytes(a.placement),
        domain_bytes(BARRIER_DOMAIN@), placement_bytes(b.placement));

    equal_placement(a.placement, b.placement);
    equal_parts(uuid_bytes(a.read.owner.worker), be64(a.read.owner.serial),
        uuid_bytes(b.read.owner.worker), be64(b.read.owner.serial));
    equal_uuid(a.read.owner.worker, b.read.owner.worker);
    equal_u64(a.read.owner.serial, b.read.owner.serial);
    equal_parts(uuid_bytes(a.read.id.nonce), be64(a.read.id.expires_at),
        uuid_bytes(b.read.id.nonce), be64(b.read.id.expires_at));
    equal_uuid(a.read.id.nonce, b.read.id.nonce);
    equal_u64(a.read.id.expires_at, b.read.id.expires_at);
    equal_u64(a.read.admitted_at, b.read.admitted_at);
    equal_checkpoint(a.read.checkpoint, b.read.checkpoint);
    equal_cut(a.read.through, b.read.through);
}

fn decoded_claim_has_canonical_start(frame: crate::Bytes) {
    if let Ok(claim) = decode_barrier_claim(frame) {
        assert(canonicalStart(claim));
    }
}

fn accepted_barrier_binds_claim(
    verifier: &BarrierVerifier,
    attestation: SignedBarrier,
    expected: &Request,
    original: Ghost<BarrierClaim>,
)
    requires
        canonicalStart(attestation.claim),
        canonicalStart(original@),
        authenticates(verifier.keys_spec(), attestation.signature, barrier_bytes(original@)),
{
    if let Ok(claim) = verifier.verify(attestation, expected) {
        assert(exactBarrierInvocation(verifier.scope_spec(), expected, claim));
        proof { canonical_fields_bind_claim(claim, original@); }
        assert(claim == original@);
    }
}

fn accepted_barrier_receipt_is_exact(
    receipt: Receipt,
    attestation: Option<SignedBarrier>,
    placement: Placement,
    request: &Request,
) {
    if barrier_receipt_matches(receipt, attestation)
        && receipt_scope_matches(receipt, placement, request) {
        assert(exactBarrierReceipt(receipt, attestation) && exactReceiptScope(receipt, placement, request));
    }
}

fn authenticated_barrier_receipt_binds_signed_cut(
    verifier: &BarrierVerifier,
    receipt: Receipt,
    attestation: SignedBarrier,
    request: &Request,
    signed: Ghost<BarrierClaim>,
)
    requires canonicalStart(attestation.claim), canonicalStart(signed@),
        authenticates(verifier.keys_spec(), attestation.signature, barrier_bytes(signed@)),
{
    if barrier_receipt_matches(receipt, Some(attestation)) {
        if let Ok(accepted) = verifier.verify(attestation, request) {
            proof { canonical_fields_bind_claim(accepted, signed@); }
            assert(receipt.outcome == Ok(Outcome::Barrier { read: signed@.read }));
            assert(receipt.placement == signed@.placement
                && receipt.principal == Principal::Worker(signed@.read.owner)
                && receipt.request == signed@.read.id
                && receipt.position == signed@.read.admitted_at);
        }
    }
}

fn valid_successor_extends_rotations(source: &ReceiptKeys, target: &ReceiptKeys) {
    if target.validate_successor_keys(source).is_ok() {
        let from = source.barrier_keys();
        let to = target.barrier_keys();
        assert(from@.subset_of(to@));
    }
}

fn repair_authority_is_active(
    source: &ReceiptKeys,
    target: &ReceiptKeys,
    issuer: &Fingerprint,
    seed: &[u8],
    signature: &[u8],
) {
    if target.validate_successor_keys(source).is_ok()
        && verify_repair_signature(target, issuer, seed, signature).is_ok() {
        assert(exists|key: Fingerprint| source.active@.values().contains(key)
            && #[trigger] fingerprint(key) == *issuer
            && signed_message(key, signature@) == Some(seed@)) by {
            let key = choose|key: Fingerprint| repairAuthority(target, key)
                && #[trigger] fingerprint(key) == *issuer
                && signed_message(key, signature@) == Some(seed@);
            assert(target.predecessor@.to_set().contains(key));
        }
    }
}

proof fn first_ascii_byte(tag: Seq<char>, first: char)
    requires tag.len() > 0, tag[0] == first, first as u32 <= 0x7f,
    ensures domain_bytes(tag).len() > 0, domain_bytes(tag)[0] == first as u8,
{
    let head = seq![first];
    assert(head + tag.skip(1) =~= tag);
    vstd::utf8::encode_utf8_concat(head, tag.skip(1));
    assert(vstd::utf8::is_ascii_chars(head));
    vstd::utf8::is_ascii_chars_encode_utf8(head);
}

proof fn rotation_domain_is_distinct(evidence: RotationSlots, receipt: Receipt, claim: BarrierClaim)
    ensures rotation_bytes(evidence, receipt) != barrier_bytes(claim),
{
    rotation_domain_keeps_its_protocol_spelling();
    barrier_domain_keeps_its_protocol_spelling();
    reveal_strlit("logkeeper.ordered-rotation-slots.v1");
    reveal_strlit("LKBRAR04");
    first_ascii_byte(ROTATION_DOMAIN@, 'l');
    first_ascii_byte(BARRIER_DOMAIN@, 'L');
    assert(rotation_bytes(evidence, receipt)[0] == b'l');
    assert(barrier_bytes(claim)[0] == b'L');
}

fn rotation_signs_in_its_own_domain(evidence: &RotationSlots, receipt: Receipt) -> (out: crate::Bytes)
    ensures out@.take(35) == domain_bytes("logkeeper.ordered-rotation-slots.v1"@),
{
    let bytes = evidence.signing_bytes(receipt);
    proof {
        rotation_domain_keeps_its_protocol_spelling();
        assert(bytes@.take(35) =~= domain_bytes(ROTATION_DOMAIN@));
    }
    bytes
}

fn rotation_verification_uses_its_own_domain(
    verifier: &BarrierVerifier,
    attestation: &SignedRotationSlots,
    group: Fingerprint,
    receipt: Receipt,
    barrier: Ghost<BarrierClaim>,
)
    requires authenticates(verifier.keys_spec(), attestation.signature, barrier_bytes(barrier@)),
{
    let verified = verifier.verify_rotation(attestation, group, receipt);
    proof { rotation_domain_is_distinct(attestation.evidence, receipt, barrier@); }
    assert(verified is Err);
}

}
