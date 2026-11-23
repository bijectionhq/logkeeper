use super::{invalid, verify_bytes};
#[cfg(verus_keep_ghost)]
use crate::contracts::BTreeMap;
use crate::ordered::daemon::receipt_keys::fingerprints_match;
use crate::ordered::{
    BarrierClaim, Command, Fingerprint, Placement, Principal, Receipt, Request,
    service::wire::{Signature, SignedBarrier, SignedRotationSlots},
};
#[cfg(not(verus_keep_ghost))]
use std::collections::BTreeMap;
use std::io;

#[cfg(verus_keep_ghost)]
use {
    crate::{ordered::covers, reference::*},
    vstd::prelude::*,
};

/// Verification material installed independently of the serving daemon.
/// Carry all previously installed receipt public keys for the placement's
/// lifetime. Verification does not extend the underlying read hold.
pub struct BarrierVerifier {
    pub(super) scope: Placement,
    pub(super) keys: BTreeMap<Fingerprint, [u8; 32]>,
}

#[cfg(verus_keep_ghost)]
verus! {
impl BarrierVerifier {
    pub closed spec fn scope_spec(&self) -> Placement { self.scope }

    pub closed spec fn keys_spec(&self) -> Map<Fingerprint, Fingerprint> { self.keys@ }
}
}

impl BarrierVerifier {
    /// Authenticates the exact successful marker for the supplied invocation.
    /// The consumer still has to open and materialize the protected basis.
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures
            (out is Ok) == (exactBarrierInvocation(self.scope_spec(), expected, attestation.claim)
                && authenticates(self.keys_spec(), attestation.signature, barrier_bytes(attestation.claim))),
            out matches Ok(claim) ==> claim == attestation.claim,
    ))]
    pub fn verify(
        &self,
        attestation: SignedBarrier,
        expected: &Request,
    ) -> io::Result<BarrierClaim> {
        let Command::Barrier = &expected.command else {
            return Err(invalid(
                "a read receipt requires an original read invocation",
            ));
        };
        let claim = attestation.claim;
        if claim.placement != self.scope
            || expected.placement != self.scope
            || expected.principal != Principal::Worker(claim.read.owner)
            || claim.read.id != expected.id
        {
            return Err(invalid("read receipt addresses a different invocation"));
        }
        self.verify_signature(attestation.signature, claim.encode().as_ref())?;
        Ok(claim)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures (out is Ok) == (receipt.placement == self.scope_spec()
            && attestation.evidence.group == group && covers(attestation.evidence, receipt)
            && authenticates(self.keys_spec(), attestation.signature, rotation_bytes(attestation.evidence, receipt))),
    ))]
    pub(in super::super) fn verify_rotation(
        &self,
        attestation: &SignedRotationSlots,
        group: Fingerprint,
        receipt: Receipt,
    ) -> io::Result<()> {
        if receipt.placement != self.scope
            || !fingerprints_match(&attestation.evidence.group, &group)
            || !attestation.evidence.covers(receipt)
        {
            return Err(invalid(
                "rotation slots address a different installed decision",
            ));
        }
        self.verify_signature(
            attestation.signature,
            attestation.evidence.signing_bytes(receipt).as_ref(),
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures (out is Ok) == authenticates(self.keys_spec(), signature, body@),
    ))]
    fn verify_signature(&self, signature: Signature, body: &[u8]) -> io::Result<()> {
        let Some(authority) = self.keys.get(&signature.issuer) else {
            return Err(invalid("unrecognized journal receipt key"));
        };
        verify_bytes(authority, body, &signature.proof)
    }
}
