use crate::ordered::{
    BarrierClaim, Command, Fingerprint, Placement, Principal, Request,
    service::wire::{Signature, SignedBarrier},
};
use ring::signature::{ED25519, Ed25519KeyPair, KeyPair, UnparsedPublicKey};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::Path;

pub(super) struct Issuer {
    identity: Fingerprint,
    key: Ed25519KeyPair,
}

impl Issuer {
    pub(super) fn load(path: &Path) -> io::Result<Self> {
        let key = Ed25519KeyPair::from_pkcs8_maybe_unchecked(&fs::read(path)?)
            .map_err(|_| super::invalid("invalid read receipt key"))?;
        let identity = Sha256::digest(key.public_key().as_ref()).into();
        Ok(Self { identity, key })
    }

    pub(super) fn sign(&self, claim: BarrierClaim) -> io::Result<Signature> {
        let signature = self.key.sign(&claim.encode());
        let proof = signature
            .as_ref()
            .try_into()
            .map_err(|_| super::invalid("invalid read receipt signature"))?;
        Ok(Signature {
            issuer: self.identity,
            proof,
        })
    }
}

/// Verification material installed independently of the route to a current
/// daemon. Keep an issued key while its protected results can complete.
pub struct BarrierVerifier {
    scope: Placement,
    keys: BTreeMap<Fingerprint, [u8; 32]>,
}

impl BarrierVerifier {
    pub fn new(
        scope: Placement,
        public_keys: impl IntoIterator<Item = [u8; 32]>,
    ) -> io::Result<Self> {
        let keys: BTreeMap<_, _> = public_keys
            .into_iter()
            .map(|key| (Sha256::digest(key).into(), key))
            .collect();
        if keys.is_empty() {
            return Err(super::invalid(
                "the ordered route has no read receipt verification keys",
            ));
        }
        Ok(Self { scope, keys })
    }

    /// Authenticates the exact successful marker for the supplied invocation.
    /// The consumer still has to open and materialize the protected basis.
    pub fn verify(&self, proof: SignedBarrier, expected: &Request) -> io::Result<BarrierClaim> {
        let Command::Barrier { grant, nonce } = &expected.command else {
            return Err(super::invalid(
                "a read receipt requires an original read invocation",
            ));
        };
        let claim = proof.claim;
        if claim.placement() != self.scope
            || expected.placement != self.scope
            || expected.principal != Principal::Worker(grant.enrollment)
            || claim.grant() != *grant
            || claim.nonce() != *nonce
            || claim.read().id != expected.id
        {
            return Err(super::invalid(
                "read receipt addresses a different invocation",
            ));
        }
        let authority = self
            .keys
            .get(&proof.signature.issuer)
            .ok_or_else(|| super::invalid("unrecognized read receipt key"))?;
        UnparsedPublicKey::new(&ED25519, authority)
            .verify(&claim.encode(), &proof.signature.proof)
            .map_err(|_| super::invalid("invalid read receipt signature"))?;
        Ok(claim)
    }
}
