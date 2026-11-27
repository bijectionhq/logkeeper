//! Certificate-bound original writes on the StreamJournal keeper protocol.

use std::sync::Arc;

use bytes::Bytes;
use sha2::{Digest, Sha256};

use super::wire::{Epoch, KeeperId, Lsn, StreamId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TimedOriginal {
    pub stream: StreamId,
    pub epoch: Epoch,
    pub at: Lsn,
    pub payload_sha256: [u8; 32],
    pub exclusive_journal_cutoff_micros: i64,
    pub original_receiver_certificate_sha256: [u8; 32],
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TimedOriginalProof {
    pub original: TimedOriginal,
    pub original_quorum_sync_upper_micros: i64,
    pub verified_evidence_sha256: [u8; 32],
}

/// A keeper's attestation that its immutable journal committed a timed original.
/// The attached stage samples authenticate when its exact bytes reached quorum.
/// A verifier must supply the enrolled catalog and its historical keeper keys.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TimedCommitment {
    evidence: TimedEvidence,
    catalog: uuid::Uuid,
    keeper: KeeperId,
    signature: [u8; 64],
}

/// Installed keeper-key trust. Historical keys and their keeper identity bindings
/// must remain verifiable for as long as their original records are retained.
pub trait TimedOriginalVerifier: Send + Sync + 'static {
    fn verify(&self, keeper: KeeperId, statement: &[u8], signature: &[u8; 64]) -> bool;
}

/// Privileged keeper mount for the scope and clock scale of a verified receiver
/// certificate. Called on the keeper's WAL thread. Implementations must fail
/// closed if their authorization or conservative clock bound is unavailable.
pub trait TimedOriginalClock: Send + Sync + 'static {
    fn authorize(&self, original: &TimedOriginal) -> bool;

    /// Sample an upper bound for a durability event already completed on this
    /// keeper, in the original certificate's guarded journal clock scale.
    fn sync_upper_micros(&self, original: &TimedOriginal) -> Option<i64>;

    /// Signs a keeper-generated stage sample or commitment with this keeper's
    /// independently installed attestation key.
    fn sign(&self, statement: &[u8]) -> Option<[u8; 64]>;
}

pub(crate) const ORIGINAL_BYTES: usize = 104;
pub(crate) const SAMPLE_BYTES: usize = 72;
const ORIGIN_BYTES: usize = ORIGINAL_BYTES + 16 * 4;
pub(crate) const EVIDENCE_BYTES: usize = ORIGIN_BYTES + 2 * SAMPLE_BYTES;
const COMMITMENT_BYTES: usize = EVIDENCE_BYTES + 16 + 16 + 64;
// Room for distinct timed wire messages and the retained evidence envelope.
pub(crate) const MAX_TIMED_PAYLOAD: usize = super::codec::PAGE_BYTES - 2 * EVIDENCE_BYTES;

impl TimedOriginal {
    pub(crate) fn valid(self) -> bool {
        self.at.0 > 0
            && self.at.0 < u64::MAX
            && self.exclusive_journal_cutoff_micros > 0
            && self.original_receiver_certificate_sha256 != [0; 32]
    }

    pub(crate) fn matches(self, payload: &[u8]) -> bool {
        self.valid() && self.payload_sha256 == <[u8; 32]>::from(Sha256::digest(payload))
    }

    pub(crate) fn encode(self) -> [u8; ORIGINAL_BYTES] {
        let mut bytes = [0; ORIGINAL_BYTES];
        bytes[..16].copy_from_slice(&self.stream.0.to_be_bytes());
        bytes[16..24].copy_from_slice(&self.epoch.0.to_be_bytes());
        bytes[24..32].copy_from_slice(&self.at.0.to_be_bytes());
        bytes[32..64].copy_from_slice(&self.payload_sha256);
        bytes[64..72].copy_from_slice(&self.exclusive_journal_cutoff_micros.to_be_bytes());
        bytes[72..].copy_from_slice(&self.original_receiver_certificate_sha256);
        bytes
    }

    pub(crate) fn decode(bytes: &[u8]) -> Option<Self> {
        let bytes: &[u8; ORIGINAL_BYTES] = bytes.try_into().ok()?;
        let original = Self {
            stream: StreamId(u128::from_be_bytes(bytes[..16].try_into().ok()?)),
            epoch: Epoch(u64::from_be_bytes(bytes[16..24].try_into().ok()?)),
            at: Lsn(u64::from_be_bytes(bytes[24..32].try_into().ok()?)),
            payload_sha256: bytes[32..64].try_into().ok()?,
            exclusive_journal_cutoff_micros: i64::from_be_bytes(bytes[64..72].try_into().ok()?),
            original_receiver_certificate_sha256: bytes[72..].try_into().ok()?,
        };
        original.valid().then_some(original)
    }
}

/// One original stage sync. Its keeper is identified by its canonical quorum slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TimedSample {
    pub(crate) upper_micros: i64,
    pub(crate) signature: [u8; 64],
}

impl TimedSample {
    pub(crate) fn encode(self) -> [u8; SAMPLE_BYTES] {
        let mut bytes = [0; SAMPLE_BYTES];
        bytes[..8].copy_from_slice(&self.upper_micros.to_be_bytes());
        bytes[8..].copy_from_slice(&self.signature);
        bytes
    }

    pub(crate) fn decode(bytes: &[u8]) -> Option<Self> {
        let bytes: &[u8; SAMPLE_BYTES] = bytes.try_into().ok()?;
        Some(Self {
            upper_micros: i64::from_be_bytes(bytes[..8].try_into().ok()?),
            signature: bytes[8..].try_into().ok()?,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TimedOrigin {
    pub original: TimedOriginal,
    pub ensemble: [KeeperId; 3],
    pub proposal: u128,
}

impl TimedOrigin {
    pub(crate) fn encode(self) -> [u8; ORIGIN_BYTES] {
        let mut bytes = [0; ORIGIN_BYTES];
        bytes[..ORIGINAL_BYTES].copy_from_slice(&self.original.encode());
        for (id, slot) in self
            .ensemble
            .iter()
            .zip(bytes[ORIGINAL_BYTES..].chunks_exact_mut(16))
        {
            slot.copy_from_slice(&id.0.to_be_bytes());
        }
        bytes[ORIGIN_BYTES - 16..].copy_from_slice(&self.proposal.to_be_bytes());
        bytes
    }

    fn decode(bytes: &[u8]) -> Option<Self> {
        let bytes: &[u8; ORIGIN_BYTES] = bytes.try_into().ok()?;
        let original = TimedOriginal::decode(&bytes[..ORIGINAL_BYTES])?;
        let mut ensemble = [KeeperId(0); 3];
        for (id, slot) in ensemble
            .iter_mut()
            .zip(bytes[ORIGINAL_BYTES..].chunks_exact(16))
        {
            *id = KeeperId(u128::from_be_bytes(slot.try_into().ok()?));
        }
        let proposal = u128::from_be_bytes(bytes[ORIGIN_BYTES - 16..].try_into().ok()?);
        let origin = Self {
            original,
            ensemble,
            proposal,
        };
        origin.valid().then_some(origin)
    }

    fn valid(self) -> bool {
        let [first, second, third] = self.ensemble;
        self.original.valid()
            && self.proposal != 0
            && first.0 != 0
            && second.0 != 0
            && third.0 != 0
            && first != second
            && first != third
            && second != third
    }

    pub(crate) fn timely(self, upper_micros: i64) -> bool {
        0 < upper_micros && upper_micros < self.original.exclusive_journal_cutoff_micros
    }

    pub(crate) fn statement(self, keeper: KeeperId, upper_micros: i64) -> Vec<u8> {
        let mut bytes = b"logkeeper/stream/timed-original-stage/v1\0".to_vec();
        bytes.extend_from_slice(&self.encode());
        bytes.extend_from_slice(&keeper.0.to_be_bytes());
        bytes.extend_from_slice(&upper_micros.to_be_bytes());
        bytes
    }

    pub(crate) fn verifies(
        self,
        keeper: KeeperId,
        sample: TimedSample,
        verifier: &dyn TimedOriginalVerifier,
    ) -> bool {
        self.timely(sample.upper_micros)
            && verifier.verify(
                keeper,
                &self.statement(keeper, sample.upper_micros),
                &sample.signature,
            )
    }
}

/// The original write quorum. The first two distinct keepers in the sealed
/// ensemble are fixed for this lane, so retries cannot substitute a new pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TimedEvidence {
    pub(crate) origin: TimedOrigin,
    pub(crate) samples: [TimedSample; 2],
}

impl TimedEvidence {
    pub(crate) fn encode(self) -> [u8; EVIDENCE_BYTES] {
        let mut bytes = [0; EVIDENCE_BYTES];
        bytes[..ORIGIN_BYTES].copy_from_slice(&self.origin.encode());
        for (sample, slot) in self
            .samples
            .iter()
            .zip(bytes[ORIGIN_BYTES..].chunks_exact_mut(SAMPLE_BYTES))
        {
            slot.copy_from_slice(&sample.encode());
        }
        bytes
    }

    pub(crate) fn decode(bytes: &[u8]) -> Option<Self> {
        let bytes: &[u8; EVIDENCE_BYTES] = bytes.try_into().ok()?;
        let origin = TimedOrigin::decode(&bytes[..ORIGIN_BYTES])?;
        let samples = [
            TimedSample::decode(&bytes[ORIGIN_BYTES..ORIGIN_BYTES + SAMPLE_BYTES])?,
            TimedSample::decode(&bytes[ORIGIN_BYTES + SAMPLE_BYTES..])?,
        ];
        samples
            .iter()
            .all(|sample| origin.timely(sample.upper_micros))
            .then_some(Self { origin, samples })
    }

    pub(crate) fn proof(self, verifier: &dyn TimedOriginalVerifier) -> Option<TimedOriginalProof> {
        if !self.origin.valid() {
            return None;
        }
        for (keeper, sample) in self.origin.ensemble.into_iter().zip(self.samples) {
            if !self.origin.verifies(keeper, sample, verifier) {
                return None;
            }
        }
        let mut digest = Sha256::new();
        digest.update(b"logkeeper/stream/timed-original-evidence/v1\0");
        digest.update(self.encode());
        Some(TimedOriginalProof {
            original: self.origin.original,
            original_quorum_sync_upper_micros: self.samples[0]
                .upper_micros
                .max(self.samples[1].upper_micros),
            verified_evidence_sha256: digest.finalize().into(),
        })
    }
}

impl TimedCommitment {
    #[cfg(feature = "stream")]
    pub(crate) fn sign(
        evidence: TimedEvidence,
        catalog: uuid::Uuid,
        keeper: KeeperId,
        clock: &dyn TimedOriginalClock,
        verifier: &dyn TimedOriginalVerifier,
    ) -> Option<Self> {
        evidence.proof(verifier)?;
        let mut commitment = Self {
            evidence,
            catalog,
            keeper,
            signature: [0; 64],
        };
        commitment.signature = clock.sign(&commitment.statement())?;
        Some(commitment)
    }

    /// The version 1 bytes to retain with the issuer's durable outcome.
    pub fn encode(self) -> [u8; COMMITMENT_BYTES] {
        let mut bytes = [0; COMMITMENT_BYTES];
        bytes[..EVIDENCE_BYTES].copy_from_slice(&self.evidence.encode());
        bytes[EVIDENCE_BYTES..EVIDENCE_BYTES + 16].copy_from_slice(self.catalog.as_bytes());
        bytes[EVIDENCE_BYTES + 16..EVIDENCE_BYTES + 32]
            .copy_from_slice(&self.keeper.0.to_be_bytes());
        bytes[EVIDENCE_BYTES + 32..].copy_from_slice(&self.signature);
        bytes
    }

    /// Parses saved version 1 bytes. Call `verify` before using the outcome.
    pub fn decode(bytes: &[u8]) -> Option<Self> {
        let bytes: &[u8; COMMITMENT_BYTES] = bytes.try_into().ok()?;
        let (evidence, signed) = bytes.split_at(EVIDENCE_BYTES);
        Some(Self {
            evidence: TimedEvidence::decode(evidence)?,
            catalog: uuid::Uuid::from_bytes(signed[..16].try_into().ok()?),
            keeper: KeeperId(u128::from_be_bytes(signed[16..32].try_into().ok()?)),
            signature: signed[32..].try_into().ok()?,
        })
    }

    /// Verifies an exact commitment without contacting the original journal.
    pub fn verify(
        self,
        catalog: uuid::Uuid,
        original: TimedOriginal,
        verifier: &dyn TimedOriginalVerifier,
    ) -> Option<TimedOriginalProof> {
        if catalog.is_nil()
            || self.catalog != catalog
            || self.keeper.0 == 0
            || self.evidence.origin.original != original
            || !verifier.verify(self.keeper, &self.statement(), &self.signature)
        {
            return None;
        }
        self.evidence.proof(verifier)
    }

    fn statement(self) -> Vec<u8> {
        let mut bytes = b"logkeeper/stream/timed-original-commitment/v1\0".to_vec();
        let encoded = self.encode();
        bytes.extend_from_slice(&encoded[..COMMITMENT_BYTES - 64]);
        bytes
    }
}

/// Internal retained record used by append lanes and recovery. Timed and
/// ordinary payloads have distinct types on the wire and in keeper storage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Entry {
    Ordinary(Bytes),
    Timed {
        evidence: Arc<TimedEvidence>,
        payload: Bytes,
    },
}

impl Entry {
    pub(crate) fn len(&self) -> usize {
        match self {
            Self::Ordinary(payload) => payload.len(),
            Self::Timed { payload, .. } => EVIDENCE_BYTES + payload.len(),
        }
    }
}
