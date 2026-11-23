use super::{invalid, verify_bytes};
use crate::ordered::{
    BarrierClaim, Command, Fingerprint, Placement, Principal, Receipt, Request,
    service::wire::{Signature, SignedBarrier, SignedRotationSlots},
};
use std::collections::BTreeMap;
use std::io;

/// Verification material installed independently of the serving daemon.
/// Carry all previously installed receipt public keys for the placement's
/// lifetime. Verification does not extend the underlying read hold.
pub struct BarrierVerifier {
    pub(super) scope: Placement,
    pub(super) keys: BTreeMap<Fingerprint, [u8; 32]>,
}

impl BarrierVerifier {
    /// Authenticates the exact successful marker for the supplied invocation.
    /// The consumer still has to open and materialize the protected basis.
    pub fn verify(&self, proof: SignedBarrier, expected: &Request) -> io::Result<BarrierClaim> {
        let Command::Barrier = &expected.command else {
            return Err(invalid(
                "a read receipt requires an original read invocation",
            ));
        };
        let claim = proof.claim;
        if claim.placement() != self.scope
            || expected.placement != self.scope
            || expected.principal != Principal::Worker(claim.read().owner)
            || claim.read().id != expected.id
        {
            return Err(invalid("read receipt addresses a different invocation"));
        }
        self.verify_signature(proof.signature, claim.encode().as_ref())?;
        Ok(claim)
    }

    pub(in crate::ordered::daemon) fn verify_rotation(
        &self,
        proof: &SignedRotationSlots,
        group: Fingerprint,
        receipt: Receipt,
    ) -> io::Result<()> {
        if receipt.placement != self.scope
            || proof.evidence.group != group
            || !proof.evidence.covers(receipt)
        {
            return Err(invalid(
                "rotation slots address a different installed decision",
            ));
        }
        self.verify_signature(
            proof.signature,
            proof.evidence.signing_bytes(receipt).as_ref(),
        )
    }

    fn verify_signature(&self, signature: Signature, body: &[u8]) -> io::Result<()> {
        let authority = self
            .keys
            .get(&signature.issuer)
            .ok_or_else(|| invalid("unrecognized journal receipt key"))?;
        verify_bytes(authority, body, &signature.proof)
    }
}
