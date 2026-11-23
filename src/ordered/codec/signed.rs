use crate::ordered::{
    BarrierClaim, Checkpoint, Cut, Enrollment, Placement, Receipt, RequestId,
    replication::RotationSlots,
};
use bytes::{BufMut, Bytes, BytesMut};
use uuid::Uuid;

pub(super) const BARRIER_DOMAIN: &[u8; 8] = b"LKBRAR04";

impl BarrierClaim {
    /// Canonical bytes for the journal's scoped receipt issuer to authenticate.
    pub fn encode(&self) -> Bytes {
        let mut output = BytesMut::new();
        output.put_slice(BARRIER_DOMAIN);
        placement(&mut output, self.placement);
        enrollment(&mut output, self.read.owner);
        request_id(&mut output, self.read.id);
        output.put_u64(self.read.admitted_at);
        checkpoint(&mut output, self.read.checkpoint);
        cut(&mut output, self.read.through);
        output.freeze()
    }
}

impl RotationSlots {
    pub(in crate::ordered) fn signing_bytes(&self, decision: Receipt) -> Bytes {
        let mut output = BytesMut::new();
        output.put_slice(b"logkeeper.ordered-rotation-slots.v1");
        super::service::receipt(&mut output, decision);
        self.encode(&mut output);
        output.freeze()
    }
}

pub(super) fn uuid(output: &mut BytesMut, value: Uuid) {
    output.put_slice(value.as_bytes());
}

pub(super) fn request_id(output: &mut BytesMut, value: RequestId) {
    uuid(output, value.nonce);
    output.put_u64(value.expires_at);
}

pub(super) fn placement(output: &mut BytesMut, value: Placement) {
    uuid(output, value.deployment);
    uuid(output, value.incarnation);
    uuid(output, value.group);
    output.put_u64(value.generation);
}

pub(super) fn enrollment(output: &mut BytesMut, value: Enrollment) {
    uuid(output, value.worker);
    output.put_u64(value.serial);
}

pub(super) fn cut(output: &mut BytesMut, value: Cut) {
    output.put_u64(value.next_lsn);
    output.put_slice(&value.history);
}

pub(super) fn checkpoint(output: &mut BytesMut, value: Checkpoint) {
    cut(output, value.cut);
    output.put_slice(&value.root);
    output.put_slice(&value.manifest);
    uuid(output, value.custody.allocation);
    output.put_u64(value.custody.revision);
    output.put_slice(&value.custody.provider);
}
