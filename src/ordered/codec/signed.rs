use super::Input;
use crate::ordered::{
    BarrierClaim, Checkpoint, Cut, Enrollment, Hold, Placement, Receipt, Refusal, RequestId,
    replication::RotationSlots,
};
use bytes::{BufMut, Bytes, BytesMut};
use uuid::Uuid;

#[cfg(verus_keep_ghost)]
use {crate::reference::*, vstd::prelude::*};

pub const BARRIER_DOMAIN: &str = "LKBRAR04";
pub const ROTATION_DOMAIN: &str = "logkeeper.ordered-rotation-slots.v1";

impl BarrierClaim {
    /// Canonical bytes for the journal's scoped receipt issuer to authenticate.
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out@ == barrier_bytes(*self),
    ))]
    pub fn encode(&self) -> Bytes {
        let mut output = BytesMut::new();
        output.put_slice(BARRIER_DOMAIN.as_bytes());
        placement(&mut output, self.placement);
        enrollment(&mut output, self.read.owner);
        request_id(&mut output, self.read.id);
        output.put_u64(self.read.admitted_at);
        checkpoint(&mut output, self.read.checkpoint);
        cut(&mut output, self.read.through);
        output.freeze()
    }

    /// Parses a claim. The receiver still authenticates the original bytes
    /// against the installed journal scope before relying on their contents.
    pub fn decode(frame: Bytes) -> Result<Self, Refusal> {
        decode_barrier_claim(frame)
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out matches Ok(claim) ==> canonicalStart(claim),
))]
pub(crate) fn decode_barrier_claim(frame: Bytes) -> Result<BarrierClaim, Refusal> {
    let mut input = Input(frame);
    if &input.take::<8>()? != BARRIER_DOMAIN.as_bytes() {
        return Err(Refusal::Invalid);
    }
    let placement = input.placement()?;
    let owner = input.enrollment()?;
    let id = input.request_id()?;
    let admitted_at = input.u64()?;
    let checkpoint = input.checkpoint()?;
    let through = input.cut()?;
    if !input.0.is_empty()
        || checkpoint.cut.next_lsn > through.next_lsn
        || (checkpoint.cut.next_lsn == through.next_lsn && checkpoint.cut != through)
        || admitted_at == 0
        || admitted_at >= id.expires_at
    {
        return Err(Refusal::Invalid);
    }
    Ok(BarrierClaim {
        placement,
        read: Hold {
            id,
            owner,
            admitted_at,
            checkpoint,
            start: checkpoint.cut,
            through,
        },
    })
}

impl RotationSlots {
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out@ == rotation_bytes(*self, decision),
    ))]
    pub(in super::super) fn signing_bytes(&self, decision: Receipt) -> Bytes {
        let mut output = BytesMut::new();
        output.put_slice(ROTATION_DOMAIN.as_bytes());
        super::service::receipt(&mut output, decision);
        self.encode(&mut output);
        output.freeze()
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(output)@ == old(output)@ + uuid_bytes(value),
))]
pub(super) fn uuid(output: &mut BytesMut, value: Uuid) {
    output.put_slice(value.as_bytes());
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(output)@ == old(output)@ + request_id_bytes(value),
))]
pub(super) fn request_id(output: &mut BytesMut, value: RequestId) {
    uuid(output, value.nonce);
    output.put_u64(value.expires_at);
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(output)@ == old(output)@ + placement_bytes(value),
))]
pub(super) fn placement(output: &mut BytesMut, value: Placement) {
    uuid(output, value.deployment);
    uuid(output, value.incarnation);
    uuid(output, value.group);
    output.put_u64(value.generation);
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(output)@ == old(output)@ + enrollment_bytes(value),
))]
pub(super) fn enrollment(output: &mut BytesMut, value: Enrollment) {
    uuid(output, value.worker);
    output.put_u64(value.serial);
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(output)@ == old(output)@ + cut_bytes(value),
))]
pub(super) fn cut(output: &mut BytesMut, value: Cut) {
    output.put_u64(value.next_lsn);
    output.put_slice(&value.history);
}

#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(output)@ == old(output)@ + checkpoint_bytes(value),
))]
pub(super) fn checkpoint(output: &mut BytesMut, value: Checkpoint) {
    cut(output, value.cut);
    output.put_slice(&value.root);
    output.put_slice(&value.manifest);
    uuid(output, value.custody.allocation);
    output.put_u64(value.custody.revision);
    output.put_slice(&value.custody.provider);
}

#[cfg(verus_keep_ghost)]
verus! {

pub proof fn barrier_domain_keeps_its_protocol_spelling()
    ensures BARRIER_DOMAIN@ == "LKBRAR04"@,
        domain_bytes(BARRIER_DOMAIN@).len() == 8,
{
    reveal_strlit("LKBRAR04");
    vstd::utf8::is_ascii_chars_encode_utf8(BARRIER_DOMAIN@);
}

pub proof fn rotation_domain_keeps_its_protocol_spelling()
    ensures ROTATION_DOMAIN@ == "logkeeper.ordered-rotation-slots.v1"@,
        domain_bytes(ROTATION_DOMAIN@).len() == 35,
{
    reveal_strlit("logkeeper.ordered-rotation-slots.v1");
    vstd::utf8::is_ascii_chars_encode_utf8(ROTATION_DOMAIN@);
}

}
