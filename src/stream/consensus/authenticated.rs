//! Portable proofs for authenticated consensus streams.

mod archive;
mod authority;
mod tree;

use journal_contract::{Epoch, Lsn, StreamId};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use uuid::Uuid;

pub use authority::{
    CatalogAuthority, CatalogHistory, CatalogRoot, QuorumSignature, SignedAuthority, VoterKeys,
};
pub use tree::Tree;

pub type Hash = [u8; 32];

#[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
pub enum ProofError {
    #[error("invalid authenticated leaf")]
    Leaf,
    #[error("invalid authenticated stream position or size")]
    Position,
    #[error("invalid authenticated catalog history")]
    CatalogHistory,
    #[error("invalid authenticated quorum signature")]
    Signature,
    #[error("invalid authenticated tree head")]
    Head,
    #[error("invalid authenticated Merkle path")]
    Path,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Timing {
    pub exclusive_cutoff_micros: i64,
    pub receiver_certificate_sha256: Hash,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Leaf {
    pub stream: StreamId,
    pub at: Lsn,
    pub writer_epoch: Epoch,
    pub payload_sha256: Hash,
    pub quorum_durable_upper_micros: i64,
    pub timing: Option<Timing>,
}

impl Leaf {
    pub fn valid(&self) -> bool {
        self.stream.0 != 0
            && self.at.0 != 0
            && self.writer_epoch.0 != 0
            && self.quorum_durable_upper_micros > 0
            && self.timing.is_none_or(|timing| {
                self.quorum_durable_upper_micros < timing.exclusive_cutoff_micros
                    && timing.receiver_certificate_sha256 != [0; 32]
            })
    }

    pub fn hash(&self) -> Hash {
        let mut digest = Sha256::new();
        digest.update([0]);
        digest.update(b"logkeeper/authenticated/leaf/v1\0");
        digest.update(self.stream.0.to_be_bytes());
        digest.update(self.at.0.to_be_bytes());
        digest.update(self.writer_epoch.0.to_be_bytes());
        digest.update(self.payload_sha256);
        digest.update(self.quorum_durable_upper_micros.to_be_bytes());
        match self.timing {
            None => digest.update([0]),
            Some(timing) => {
                digest.update([1]);
                digest.update(timing.exclusive_cutoff_micros.to_be_bytes());
                digest.update(timing.receiver_certificate_sha256);
            }
        }
        digest.finalize().into()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Head {
    pub catalog: Uuid,
    pub stream: StreamId,
    pub size: u64,
    pub root: Hash,
    pub timestamp_micros: i64,
    pub authority_sha256: Hash,
}

impl Head {
    pub fn statement(&self) -> Vec<u8> {
        let mut bytes = b"logkeeper/authenticated/head/v1\0".to_vec();
        bytes.extend_from_slice(self.catalog.as_bytes());
        bytes.extend_from_slice(&self.stream.0.to_be_bytes());
        bytes.extend_from_slice(&self.size.to_be_bytes());
        bytes.extend_from_slice(&self.root);
        bytes.extend_from_slice(&self.timestamp_micros.to_be_bytes());
        bytes.extend_from_slice(&self.authority_sha256);
        bytes
    }

    pub fn valid(&self) -> bool {
        !self.catalog.is_nil()
            && self.stream.0 != 0
            && self.timestamp_micros > 0
            && (self.size == 0) == (self.root == Tree::empty_root())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct SignedHead {
    pub head: Head,
    pub signatures: Vec<QuorumSignature>,
}

impl SignedHead {
    pub fn verify(&self, root: CatalogRoot, history: &CatalogHistory) -> Result<(), ProofError> {
        history.verify_head(root, self)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Inclusion {
    pub leaf: Leaf,
    pub path: Vec<Hash>,
    pub signed_head: SignedHead,
    pub history: CatalogHistory,
}

impl Inclusion {
    pub fn verify(&self, root: CatalogRoot) -> Result<&Leaf, ProofError> {
        self.signed_head.verify(root, &self.history)?;
        let head = self.signed_head.head;
        if self.leaf.stream != head.stream || !self.leaf.valid() {
            return Err(ProofError::Leaf);
        }
        tree::verify_inclusion(
            self.leaf.at,
            self.leaf.hash(),
            head.size,
            head.root,
            &self.path,
        )?;
        Ok(&self.leaf)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Consistency {
    pub earlier: SignedHead,
    pub later: SignedHead,
    pub path: Vec<Hash>,
    pub history: CatalogHistory,
}

impl Consistency {
    pub fn verify(&self, root: CatalogRoot) -> Result<(), ProofError> {
        self.earlier.verify(root, &self.history)?;
        self.later.verify(root, &self.history)?;
        let earlier = self.earlier.head;
        let later = self.later.head;
        if earlier.stream != later.stream || earlier.catalog != later.catalog {
            return Err(ProofError::Head);
        }
        tree::verify_consistency(
            earlier.size,
            later.size,
            earlier.root,
            later.root,
            &self.path,
        )
    }
}

/// The leaf metadata and certification needed to produce proofs after payload retirement.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Archive {
    pub tree: Tree,
    pub signed_head: SignedHead,
    pub history: CatalogHistory,
}

impl Archive {
    pub fn verify(&self, root: CatalogRoot) -> Result<(), ProofError> {
        self.signed_head.verify(root, &self.history)?;
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

    pub fn inclusion(&self, at: Lsn) -> Result<Inclusion, ProofError> {
        let leaf = self.tree.leaf(at).ok_or(ProofError::Position)?;
        Ok(Inclusion {
            leaf: *leaf,
            path: self.tree.inclusion(at, self.signed_head.head.size)?,
            signed_head: self.signed_head.clone(),
            history: self.history.clone(),
        })
    }
}

#[cfg(test)]
mod tests;
