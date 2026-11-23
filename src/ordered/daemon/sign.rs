use crate::ordered::{
    BarrierClaim, Command, Fingerprint, Placement, Principal, Receipt, Request,
    service::wire::{Signature, SignedBarrier, SignedRotationSlots},
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

    pub(super) fn public_key(&self) -> [u8; 32] {
        self.key
            .public_key()
            .as_ref()
            .try_into()
            .expect("Ed25519 public keys have 32 bytes")
    }

    pub(super) fn sign_bytes(&self, bytes: &[u8]) -> io::Result<Signature> {
        let signature = self.key.sign(bytes);
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

pub(super) fn verify_bytes(public: &[u8; 32], body: &[u8], signature: &[u8]) -> io::Result<()> {
    UnparsedPublicKey::new(&ED25519, public)
        .verify(body, signature)
        .map_err(|_| super::invalid("invalid installed-journal signature"))
}

/// Verification material installed independently of the serving daemon.
/// Carry all previously installed receipt public keys for the placement's
/// lifetime. Verification does not extend the underlying read hold.
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
        let Command::Barrier = &expected.command else {
            return Err(super::invalid(
                "a read receipt requires an original read invocation",
            ));
        };
        let claim = proof.claim;
        if claim.placement() != self.scope
            || expected.placement != self.scope
            || expected.principal != Principal::Worker(claim.read().owner)
            || claim.read().id != expected.id
        {
            return Err(super::invalid(
                "read receipt addresses a different invocation",
            ));
        }
        self.verify_signature(proof.signature, &claim.encode())?;
        Ok(claim)
    }

    pub(super) fn verify_rotation(
        &self,
        proof: &SignedRotationSlots,
        group: Fingerprint,
        receipt: Receipt,
    ) -> io::Result<()> {
        if receipt.placement != self.scope
            || proof.evidence.group != group
            || !proof.evidence.covers(receipt)
        {
            return Err(super::invalid(
                "rotation slots address a different installed decision",
            ));
        }
        self.verify_signature(proof.signature, &proof.evidence.signing_bytes(receipt))
    }

    fn verify_signature(&self, signature: Signature, body: &[u8]) -> io::Result<()> {
        let authority = self
            .keys
            .get(&signature.issuer)
            .ok_or_else(|| super::invalid("unrecognized journal receipt key"))?;
        verify_bytes(authority, body, &signature.proof)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ordered::daemon::{GroupConfig, InstalledGroup, VoterRoute, tls::Endpoint};
    use crate::ordered::service::wire::{Decision, Reply};
    use crate::ordered::{
        Checkpoint, Custody, Cut, Enrollment, Grant, Hold, Limits, Outcome, Receipt, RequestId,
        Window,
        replication::{Ballot, RotationSlots, SlotImage, SlotPair, VoterSlots},
    };
    use ring::rand::SystemRandom;
    use uuid::Uuid;

    #[test]
    fn installed_barrier_keys_verify_receipts_after_two_signer_rotations() {
        let placement = Placement {
            deployment: Uuid::new_v4(),
            incarnation: Uuid::new_v4(),
            group: Uuid::new_v4(),
            generation: 1,
        };
        let grant = Grant {
            enrollment: Enrollment {
                worker: Uuid::new_v4(),
                serial: 1,
            },
            epoch: 1,
            key_generation: 1,
        };
        let cut = Cut {
            next_lsn: 0,
            history: [1; 32],
        };
        let checkpoint = Checkpoint {
            cut,
            root: [2; 32],
            manifest: [3; 32],
            custody: Custody {
                allocation: Uuid::new_v4(),
                revision: 1,
                provider: [4; 32],
            },
        };
        let emit = |issuer: Issuer| {
            let request = Request {
                placement,
                principal: Principal::Worker(grant.enrollment),
                id: RequestId::fresh(0, 8).unwrap(),
                command: Command::Barrier,
            };
            let read = Hold {
                id: request.id,
                owner: grant.enrollment,
                admitted_at: 1,
                checkpoint,
                start: cut,
                through: cut,
            };
            let claim = BarrierClaim {
                placement,
                read,
            };
            let signed = SignedBarrier {
                claim,
                signature: issuer.sign_bytes(&claim.encode()).unwrap(),
            };
            (request, signed)
        };
        let a = issuer();
        let b = issuer();
        let c = issuer();
        let initial = cohort(placement, checkpoint, a.public_key(), None, vec![]);
        let middle = cohort(
            placement,
            checkpoint,
            b.public_key(),
            Some(&initial),
            vec![],
        );
        let last_without_history =
            cohort(placement, checkpoint, c.public_key(), Some(&middle), vec![]);
        assert!(middle.validate_successor_keys(&initial).is_ok());
        assert!(
            last_without_history
                .validate_successor_keys(&middle)
                .is_err()
        );

        let mut last = cohort(
            placement,
            checkpoint,
            c.public_key(),
            Some(&middle),
            initial.receipt_keys.values().copied().collect(),
        );
        last.validate_successor_keys(&middle).unwrap();
        last.predecessor_keys.push(a.public_key());
        assert!(last.validate_successor_keys(&middle).is_err());
        assert_eq!(last.predecessor_keys.pop(), Some(a.public_key()));
        let without_history =
            BarrierVerifier::new(placement, last_without_history.barrier_keys()).unwrap();
        let verifier = BarrierVerifier::new(placement, last.barrier_keys()).unwrap();
        let (original, old) = emit(a);
        let (current, new) = emit(c);
        assert!(without_history.verify(old, &original).is_err());
        assert_eq!(verifier.verify(old, &original).unwrap(), old.claim);
        assert_eq!(verifier.verify(new, &current).unwrap(), new.claim);
        assert!(verifier.verify(old, &current).is_err());
        let foreign = Placement {
            incarnation: Uuid::new_v4(),
            ..placement
        };
        assert!(
            BarrierVerifier::new(foreign, last.barrier_keys())
                .unwrap()
                .verify(old, &original)
                .is_err()
        );

        let mut changed = old;
        changed.claim.read.through = Cut {
            next_lsn: 1,
            history: [5; 32],
        };
        assert!(verifier.verify(changed, &original).is_err());

        let receipt = Receipt {
            placement,
            principal: original.principal,
            request: original.id,
            position: old.claim.read().admitted_at,
            outcome: Ok(Outcome::Barrier {
                read: old.claim.read(),
            }),
        };
        let encode = |receipt, barrier| {
            Reply::Decision(Decision {
                receipt,
                barrier,
                rotation: None,
            })
            .encode()
        };
        let encoded = encode(receipt, Some(old));
        let Ok(Reply::Decision(decoded)) = Reply::decode(encoded.clone()) else {
            panic!("the genuine barrier did not round-trip");
        };
        assert_eq!(decoded.receipt, receipt);
        assert_eq!(
            verifier
                .verify(decoded.barrier.unwrap(), &original)
                .unwrap(),
            old.claim
        );
        assert!(Reply::decode(encode(receipt, None)).is_err());
        assert!(Reply::decode(encode(receipt, Some(changed))).is_err());
        assert!(
            Reply::decode(encode(
                Receipt {
                    position: 2,
                    ..receipt
                },
                Some(old)
            ))
            .is_err()
        );
        let mut trailing = encoded.to_vec();
        trailing.push(0);
        assert!(Reply::decode(trailing.into()).is_err());
        let refused = Receipt {
            outcome: Err(crate::ordered::Refusal::Stale),
            ..receipt
        };
        assert!(Reply::decode(encode(refused, None)).is_ok());
        assert!(Reply::decode(encode(refused, Some(old))).is_err());
    }

    #[test]
    fn a_rotation_signature_binds_both_images_of_each_voter_and_the_exact_decision() {
        let issuer = issuer();
        let placement = Placement {
            deployment: Uuid::new_v4(),
            incarnation: Uuid::new_v4(),
            group: Uuid::new_v4(),
            generation: 1,
        };
        let checkpoint = Checkpoint {
            cut: Cut {
                next_lsn: 5,
                history: [1; 32],
            },
            root: [2; 32],
            manifest: [3; 32],
            custody: Custody {
                allocation: Uuid::new_v4(),
                revision: 1,
                provider: [4; 32],
            },
        };
        let grant = Grant {
            enrollment: Enrollment {
                worker: Uuid::new_v4(),
                serial: 1,
            },
            epoch: 2,
            key_generation: 2,
        };
        let request = RequestId::fresh(5, 16).unwrap();
        let receipt = Receipt {
            placement,
            principal: Principal::Worker(grant.enrollment),
            request,
            position: 6,
            outcome: Ok(Outcome::Granted {
                grant,
                recovery: Hold {
                    id: request,
                    owner: grant.enrollment,
                    admitted_at: 6,
                    checkpoint,
                    start: checkpoint.cut,
                    through: checkpoint.cut,
                },
            }),
        };
        let slots = SlotPair {
            selected: 1,
            images: [
                SlotImage {
                    generation: 7,
                    digest: [5; 32],
                },
                SlotImage {
                    generation: 8,
                    digest: [6; 32],
                },
            ],
        };
        let evidence = RotationSlots {
            group: [7; 32],
            cohort_size: 3,
            ballot: Ballot {
                round: 8,
                nonce: Uuid::new_v4(),
            },
            prefix: [8; 32],
            position: 6,
            checkpoint,
            key_generation: 2,
            voters: [1, 2]
                .map(|id| VoterSlots {
                    voter: Uuid::from_u128(id),
                    slots,
                })
                .to_vec(),
        };
        let proof = SignedRotationSlots {
            signature: issuer.sign_bytes(&evidence.signing_bytes(receipt)).unwrap(),
            evidence,
        };
        let verifier = BarrierVerifier::new(placement, [issuer.public_key()]).unwrap();
        let decision = Decision {
            receipt,
            barrier: None,
            rotation: Some(proof.clone()),
        };
        let encoded = Reply::Decision(decision.clone()).encode();
        let Ok(Reply::Decision(decoded)) = Reply::decode(encoded.clone()) else {
            panic!("rotation proof did not round-trip");
        };
        assert_eq!(decoded, decision);
        verifier
            .verify_rotation(&proof, proof.evidence.group, receipt)
            .unwrap();
        assert!(verifier.verify_rotation(&proof, [9; 32], receipt).is_err());
        let other_request = Receipt {
            request: RequestId::fresh(5, 16).unwrap(),
            ..receipt
        };
        assert!(
            verifier
                .verify_rotation(&proof, proof.evidence.group, other_request)
                .is_err()
        );
        for voter in 0..2 {
            for slot in 0..2 {
                let mut changed = proof.clone();
                changed.evidence.voters[voter].slots.images[slot].digest = [42; 32];
                assert!(changed.evidence.covers(receipt));
                assert!(
                    verifier
                        .verify_rotation(&changed, proof.evidence.group, receipt)
                        .is_err()
                );
            }
        }
        let mut truncated = encoded.to_vec();
        truncated.pop();
        assert!(Reply::decode(truncated.into()).is_err());
    }

    fn issuer() -> Issuer {
        let document = Ed25519KeyPair::generate_pkcs8(&SystemRandom::new()).unwrap();
        let key = tempfile::NamedTempFile::new().unwrap();
        fs::write(key.path(), document.as_ref()).unwrap();
        Issuer::load(key.path()).unwrap()
    }

    fn cohort(
        placement: Placement,
        initial_checkpoint: Checkpoint,
        receipt_key: [u8; 32],
        predecessor: Option<&GroupConfig>,
        retained_barrier_keys: Vec<[u8; 32]>,
    ) -> GroupConfig {
        use crate::ordered::daemon::{ClientPin, ClientRole};
        InstalledGroup {
            placement,
            limits: Limits {
                enrolled_workers: 2,
                replay_holds: 2,
                retry_positions: 16,
                retained_data_bytes: 4096,
                maintenance_bytes: 1024,
                serving_lease: 30_000,
                clock_drift: 1_000,
            },
            initial_checkpoint,
            initial_window: Window {
                allocation: Uuid::new_v4(),
                serial: 1,
                bytes: 1024,
            },
            maximum_prefix_bytes: 64 << 10,
            maximum_application_frame: 1024,
            voters: [receipt_key, issuer().public_key(), issuer().public_key()]
                .into_iter()
                .zip(1..)
                .map(|(receipt_key, index)| VoterRoute {
                    voter: Uuid::new_v4(),
                    zone: format!("zone-{index}"),
                    endpoint: Endpoint {
                        address: ([127, 0, 0, 1], index as u16).into(),
                        server_name: "localhost".into(),
                        certificate: [index; 32],
                    },
                    receipt_key,
                })
                .collect(),
            clients: vec![ClientPin {
                certificate: [8; 32],
                role: ClientRole::RouteReader,
            }],
            predecessor: predecessor.map(|config| config.group.identity()),
            predecessor_keys: predecessor.map_or_else(Vec::new, |config| {
                config.receipt_keys.values().copied().collect()
            }),
            retained_barrier_keys,
        }
        .config()
        .unwrap()
    }
}
