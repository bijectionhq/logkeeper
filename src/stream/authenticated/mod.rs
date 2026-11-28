//! Authenticated stream history for the writer-driven journal.
//!
//! A quorum of a stream's keepers certifies the Merkle root of its committed
//! prefix. A head is valid when at least two distinct keepers of the ensemble it
//! names sign it with keys in the operator-installed [`KeeperKeys`]. That key set
//! is the trust root: there is no catalog, single signer, lease or clock.
//! Design: `verification/writer-driven-authenticated.md`.
//!
//! The Merkle tree and archive framing in [`merkle`] and `archive` are shared
//! with the consensus keeper's `consensus::authenticated` proofs.

mod archive;
mod keys;
pub mod merkle;
pub(crate) mod protocol;

use journal_contract::{BoxFuture, Epoch, Lsn, Result, StreamId};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use uuid::Uuid;

pub(crate) use archive::{ArchiveReader, ArchiveWriter};
pub use keys::{KeeperKeys, Signer, TrustedKeeper};
pub use merkle::{Frontier, MerkleLeaf};

use crate::stream::wire::KeeperId;

pub type Hash = [u8; 32];

/// The writer-driven Merkle tree.
pub type Tree = merkle::Tree<Leaf>;

#[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
pub enum ProofError {
    #[error("invalid authenticated leaf")]
    Leaf,
    #[error("invalid authenticated stream position or size")]
    Position,
    /// Consensus only: the catalog history does not chain to the pinned root.
    #[error("invalid authenticated catalog history")]
    CatalogHistory,
    #[error("invalid authenticated quorum signature")]
    Signature,
    #[error("invalid authenticated tree head")]
    Head,
    #[error("invalid authenticated Merkle path")]
    Path,
}

/// Evidence of a timed original write, copied from the keeper-signed stage
/// samples retained with the record. See `stream::timed`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Timing {
    pub exclusive_cutoff_micros: i64,
    pub receiver_certificate_sha256: Hash,
    /// The later of the two original-quorum stage sync upper bounds.
    pub quorum_sync_upper_micros: i64,
    /// `TimedOriginalProof::verified_evidence_sha256` of the retained evidence.
    pub evidence_sha256: Hash,
}

/// One committed record. Every keeper holding the record derives the same leaf.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Leaf {
    pub stream: StreamId,
    pub at: Lsn,
    pub writer_epoch: Epoch,
    pub payload_sha256: Hash,
    pub timing: Option<Timing>,
}

impl Leaf {
    pub fn valid(&self) -> bool {
        self.at.0 != 0
            && self.writer_epoch.0 != 0
            && self.timing.is_none_or(|timing| {
                0 < timing.quorum_sync_upper_micros
                    && timing.quorum_sync_upper_micros < timing.exclusive_cutoff_micros
                    && timing.receiver_certificate_sha256 != [0; 32]
                    && timing.evidence_sha256 != [0; 32]
            })
    }

    pub fn hash(&self) -> Hash {
        let mut digest = Sha256::new();
        digest.update([0]);
        digest.update(b"logkeeper/stream/authenticated/leaf/v1\0");
        digest.update(self.stream.0.to_be_bytes());
        digest.update(self.at.0.to_be_bytes());
        digest.update(self.writer_epoch.0.to_be_bytes());
        digest.update(self.payload_sha256);
        match self.timing {
            None => digest.update([0]),
            Some(timing) => {
                digest.update([1]);
                digest.update(timing.exclusive_cutoff_micros.to_be_bytes());
                digest.update(timing.receiver_certificate_sha256);
                digest.update(timing.quorum_sync_upper_micros.to_be_bytes());
                digest.update(timing.evidence_sha256);
            }
        }
        digest.finalize().into()
    }
}

impl MerkleLeaf for Leaf {
    fn stream(&self) -> StreamId {
        self.stream
    }

    fn at(&self) -> Lsn {
        self.at
    }

    fn valid(&self) -> bool {
        Leaf::valid(self)
    }

    fn hash(&self) -> Hash {
        Leaf::hash(self)
    }
}

/// The certified statement: the committed prefix of `stream` through `size`
/// has Merkle root `root`, as held by the keepers of `ensemble`.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Head {
    /// The keeper fleet's identity in `KeeperKeys`. It stays fixed across key
    /// rotation and keeper replacement, so consumers can pin it in records.
    pub journal: Uuid,
    pub stream: StreamId,
    pub size: u64,
    pub root: Hash,
    /// The signers' ensemble when they signed. It can differ between heads of
    /// one stream after a replacement.
    pub ensemble: [KeeperId; 3],
}

impl Head {
    pub fn statement(&self) -> Vec<u8> {
        let mut bytes = b"logkeeper/stream/authenticated/head/v1\0".to_vec();
        bytes.extend_from_slice(self.journal.as_bytes());
        bytes.extend_from_slice(&self.stream.0.to_be_bytes());
        bytes.extend_from_slice(&self.size.to_be_bytes());
        bytes.extend_from_slice(&self.root);
        for keeper in self.ensemble {
            bytes.extend_from_slice(&keeper.0.to_be_bytes());
        }
        bytes
    }

    pub fn valid(&self) -> bool {
        let [a, b, c] = self.ensemble;
        !self.journal.is_nil()
            && a.0 != 0
            && b.0 != 0
            && c.0 != 0
            && a != b
            && a != c
            && b != c
            && (self.size == 0) == (self.root == merkle::empty_root())
    }
}

/// One keeper's Ed25519 signature over `Head::statement`, made with `key`.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct HeadSignature {
    pub keeper: KeeperId,
    pub key: [u8; 32],
    pub signature: Vec<u8>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct SignedHead {
    pub head: Head,
    pub signatures: Vec<HeadSignature>,
}

impl SignedHead {
    /// Requires two distinct members of the head's ensemble with installed keys.
    /// Any invalid signature rejects the head.
    pub fn verify(&self, keys: &KeeperKeys) -> std::result::Result<(), ProofError> {
        if !self.head.valid() || self.head.journal != keys.journal {
            return Err(ProofError::Head);
        }
        keys.verify_quorum(&self.head.statement(), self.head.ensemble, &self.signatures)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Inclusion {
    pub leaf: Leaf,
    pub path: Vec<Hash>,
    pub signed_head: SignedHead,
}

impl Inclusion {
    pub fn verify(&self, keys: &KeeperKeys) -> std::result::Result<&Leaf, ProofError> {
        self.signed_head.verify(keys)?;
        let head = self.signed_head.head;
        if self.leaf.stream != head.stream || !self.leaf.valid() {
            return Err(ProofError::Leaf);
        }
        merkle::verify_inclusion(
            self.leaf.at,
            self.leaf.hash(),
            head.size,
            head.root,
            &self.path,
        )?;
        Ok(&self.leaf)
    }
}

/// The later head extends the earlier one. Either head can name a different
/// ensemble, since both verify against the same installed key set.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Consistency {
    pub earlier: SignedHead,
    pub later: SignedHead,
    pub path: Vec<Hash>,
}

impl Consistency {
    pub fn verify(&self, keys: &KeeperKeys) -> std::result::Result<(), ProofError> {
        self.earlier.verify(keys)?;
        self.later.verify(keys)?;
        let earlier = self.earlier.head;
        let later = self.later.head;
        if earlier.stream != later.stream || earlier.journal != later.journal {
            return Err(ProofError::Head);
        }
        merkle::verify_consistency(
            earlier.size,
            later.size,
            earlier.root,
            later.root,
            &self.path,
        )
    }
}

/// Every leaf through a certified head, enough to produce proofs offline after
/// the records are trimmed.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Archive {
    pub tree: Tree,
    pub signed_head: SignedHead,
}

impl Archive {
    pub fn verify(&self, keys: &KeeperKeys) -> std::result::Result<(), ProofError> {
        self.signed_head.verify(keys)?;
        let head = self.signed_head.head;
        if self.tree.size() != head.size
            || self.tree.root() != head.root
            || self
                .tree
                .stream()
                .is_some_and(|stream| stream != head.stream)
        {
            return Err(ProofError::Head);
        }
        Ok(())
    }

    pub fn inclusion(&self, at: Lsn) -> std::result::Result<Inclusion, ProofError> {
        let leaf = self.tree.leaf(at).ok_or(ProofError::Position)?;
        Ok(Inclusion {
            leaf: *leaf,
            path: self.tree.inclusion(at, self.signed_head.head.size)?,
            signed_head: self.signed_head.clone(),
        })
    }

    /// Replaces the certification with a newer signature over the same prefix,
    /// for example after a signing key was rotated out of the installed set.
    pub fn recertify(&mut self, signed_head: SignedHead) -> std::result::Result<(), ProofError> {
        let (old, new) = (self.signed_head.head, signed_head.head);
        if new.journal != old.journal
            || new.stream != old.stream
            || new.size != old.size
            || new.root != old.root
        {
            return Err(ProofError::Head);
        }
        self.signed_head = signed_head;
        Ok(())
    }
}

/// The consumer-facing authenticated history of a writer-driven journal.
/// Every returned proof has been verified against `keys()`.
pub trait AuthenticatedJournal: Send + Sync {
    /// The installed trust root that every proof from this handle verifies
    /// against. Without one, every call returns `Unsupported`.
    fn keys(&self) -> Option<&KeeperKeys>;

    /// `Ok` when a quorum of the stream's keepers keeps its complete authenticated
    /// history. `Unsupported` when they do not authenticate streams.
    fn require_authenticated(&self, stream: StreamId) -> BoxFuture<'_, Result<()>>;

    /// A quorum-signed head at `size`, or at the current head when `None`.
    fn authenticated_head(
        &self,
        stream: StreamId,
        size: Option<u64>,
    ) -> BoxFuture<'_, Result<SignedHead>>;

    fn inclusion(
        &self,
        stream: StreamId,
        at: Lsn,
        size: Option<u64>,
    ) -> BoxFuture<'_, Result<Inclusion>>;

    fn consistency(
        &self,
        earlier: SignedHead,
        later: SignedHead,
    ) -> BoxFuture<'_, Result<Consistency>>;

    fn authenticated_archive(
        &self,
        stream: StreamId,
        size: Option<u64>,
    ) -> BoxFuture<'_, Result<Archive>>;
}

#[cfg(test)]
mod tests;
