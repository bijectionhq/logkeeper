use std::collections::{BTreeMap, BTreeSet};

use journal_contract::StreamId;
use ring::signature::{ED25519, UnparsedPublicKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use uuid::Uuid;

use super::{Hash, ProofError, SignedHead};
use crate::stream::consensus::{CATALOG_STREAM, MAX_VOTERS};

type Keys = BTreeMap<Uuid, [u8; 32]>;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct CatalogRoot(pub Hash);

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct QuorumSignature {
    pub keeper: Uuid,
    pub signature: Vec<u8>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub enum VoterKeys {
    Stable(Keys),
    Joint { previous: Keys, next: Keys },
}

impl VoterKeys {
    pub fn key(&self, keeper: Uuid) -> Option<&[u8; 32]> {
        match self {
            Self::Stable(keys) => keys.get(&keeper),
            Self::Joint { previous, next } => previous.get(&keeper).or_else(|| next.get(&keeper)),
        }
    }

    pub fn keepers(&self) -> Vec<Uuid> {
        match self {
            Self::Stable(keys) => keys.keys().copied().collect(),
            Self::Joint { previous, next } => previous
                .keys()
                .chain(next.keys())
                .copied()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
        }
    }

    pub fn valid(&self) -> bool {
        let unique_keys = |keys: &Keys| {
            keys.iter().all(|(id, key)| !id.is_nil() && *key != [0; 32])
                && keys.values().collect::<BTreeSet<_>>().len() == keys.len()
        };
        let valid_size = |keys: &Keys| matches!(keys.len(), 3 | 5);
        match self {
            Self::Stable(keys) => valid_size(keys) && unique_keys(keys),
            Self::Joint { previous, next } => {
                if !valid_size(previous) || !valid_size(next) {
                    return false;
                }
                let mut combined = previous.clone();
                for (id, key) in next {
                    if combined.insert(*id, *key).is_some_and(|old| old != *key) {
                        return false;
                    }
                }
                unique_keys(&combined)
            }
        }
    }

    fn encode(&self, bytes: &mut Vec<u8>) {
        let encode_roster = |bytes: &mut Vec<u8>, keys: &Keys| {
            bytes.extend_from_slice(&(keys.len() as u64).to_be_bytes());
            for (keeper, key) in keys {
                bytes.extend_from_slice(keeper.as_bytes());
                bytes.extend_from_slice(key);
            }
        };
        match self {
            Self::Stable(keys) => {
                bytes.push(0);
                encode_roster(bytes, keys);
            }
            Self::Joint { previous, next } => {
                bytes.push(1);
                encode_roster(bytes, previous);
                encode_roster(bytes, next);
            }
        }
    }

    pub fn verify(
        &self,
        statement: &[u8],
        signatures: &[QuorumSignature],
    ) -> Result<(), ProofError> {
        if signatures.len() > 2 * MAX_VOTERS || !self.valid() {
            return Err(ProofError::Signature);
        }
        let mut signers = BTreeSet::new();
        for signature in signatures {
            let key = self.key(signature.keeper).ok_or(ProofError::Signature)?;
            if !signers.insert(signature.keeper) {
                return Err(ProofError::Signature);
            }
            UnparsedPublicKey::new(&ED25519, key)
                .verify(statement, &signature.signature)
                .map_err(|_| ProofError::Signature)?;
        }
        let quorum = |keys: &Keys| {
            signers.iter().filter(|id| keys.contains_key(id)).count() > keys.len() / 2
        };
        let valid = match self {
            Self::Stable(keys) => quorum(keys),
            Self::Joint { previous, next } => quorum(previous) && quorum(next),
        };
        if !valid {
            return Err(ProofError::Signature);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct CatalogAuthority {
    pub catalog: Uuid,
    pub revision: u64,
    pub predecessor_sha256: Option<Hash>,
    pub catalog_voters: VoterKeys,
    /// Stream roster updates at this revision. Unmentioned streams retain their rosters.
    pub stream_voters: BTreeMap<StreamId, VoterKeys>,
}

impl CatalogAuthority {
    pub fn statement(&self) -> Vec<u8> {
        let mut bytes = b"logkeeper/authenticated/catalog-authority/v1\0".to_vec();
        bytes.extend_from_slice(self.catalog.as_bytes());
        bytes.extend_from_slice(&self.revision.to_be_bytes());
        match self.predecessor_sha256 {
            None => bytes.push(0),
            Some(predecessor) => {
                bytes.push(1);
                bytes.extend_from_slice(&predecessor);
            }
        }
        self.catalog_voters.encode(&mut bytes);
        bytes.extend_from_slice(&(self.stream_voters.len() as u64).to_be_bytes());
        for (stream, keys) in &self.stream_voters {
            bytes.extend_from_slice(&stream.0.to_be_bytes());
            keys.encode(&mut bytes);
        }
        bytes
    }

    pub fn digest(&self) -> Hash {
        Sha256::digest(self.statement()).into()
    }

    pub fn root(&self) -> CatalogRoot {
        CatalogRoot(self.digest())
    }

    pub fn valid(&self) -> bool {
        !self.catalog.is_nil()
            && (self.revision == 0) == self.predecessor_sha256.is_none()
            && self.catalog_voters.valid()
            && self
                .stream_voters
                .iter()
                .all(|(stream, keys)| stream.0 != 0 && *stream != CATALOG_STREAM && keys.valid())
    }

    pub fn voters(&self, stream: StreamId) -> Option<&VoterKeys> {
        if stream == CATALOG_STREAM {
            return Some(&self.catalog_voters);
        }
        self.stream_voters.get(&stream)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct SignedAuthority {
    pub authority: CatalogAuthority,
    pub signatures: Vec<QuorumSignature>,
}

impl SignedAuthority {
    pub fn verify(&self, previous: &CatalogAuthority) -> Result<(), ProofError> {
        let authority = &self.authority;
        if !authority.valid()
            || authority.catalog != previous.catalog
            || previous.revision.checked_add(1) != Some(authority.revision)
            || authority.predecessor_sha256 != Some(previous.digest())
        {
            return Err(ProofError::CatalogHistory);
        }
        previous
            .catalog_voters
            .verify(&authority.statement(), &self.signatures)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct CatalogHistory {
    pub genesis: CatalogAuthority,
    pub transitions: Vec<SignedAuthority>,
}

impl CatalogHistory {
    pub fn latest(&self) -> &CatalogAuthority {
        self.transitions
            .last()
            .map_or(&self.genesis, |transition| &transition.authority)
    }

    pub fn verify(&self, root: CatalogRoot) -> Result<(), ProofError> {
        if !self.genesis.valid() || self.genesis.revision != 0 || self.genesis.root() != root {
            return Err(ProofError::CatalogHistory);
        }
        let mut previous = &self.genesis;
        for transition in &self.transitions {
            transition.verify(previous)?;
            previous = &transition.authority;
        }
        Ok(())
    }

    fn authorities(&self) -> impl DoubleEndedIterator<Item = &CatalogAuthority> {
        std::iter::once(&self.genesis).chain(
            self.transitions
                .iter()
                .map(|transition| &transition.authority),
        )
    }

    pub fn authority(
        &self,
        root: CatalogRoot,
        digest: Hash,
    ) -> Result<&CatalogAuthority, ProofError> {
        self.verify(root)?;
        self.authorities()
            .rev()
            .find(|authority| authority.digest() == digest)
            .ok_or(ProofError::CatalogHistory)
    }

    /// Looks up the roster at a revision of a previously verified history.
    pub fn voters_at(&self, authority_digest: Hash, stream: StreamId) -> Option<&VoterKeys> {
        self.authorities()
            .rev()
            .skip_while(|authority| authority.digest() != authority_digest)
            .find_map(|authority| authority.voters(stream))
    }

    pub fn verify_head(&self, root: CatalogRoot, signed: &SignedHead) -> Result<(), ProofError> {
        let head = signed.head;
        if !head.valid() || head.catalog != self.genesis.catalog {
            return Err(ProofError::Head);
        }
        self.verify(root)?;
        self.voters_at(head.authority_sha256, head.stream)
            .ok_or(ProofError::CatalogHistory)?
            .verify(&head.statement(), &signed.signatures)
    }
}
