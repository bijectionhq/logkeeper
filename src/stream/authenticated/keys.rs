//! The operator-installed keeper signing keys, and a keeper's own signer.

use std::{
    collections::BTreeSet,
    fs::File,
    io::{self, Read},
    path::Path,
};

use ring::signature::{ED25519, Ed25519KeyPair, KeyPair, UnparsedPublicKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use uuid::Uuid;

use super::{Hash, Head, HeadSignature, ProofError};
use crate::stream::wire::KeeperId;

/// Signatures from distinct ensemble members needed to certify a head.
pub const QUORUM: usize = 2;
const MAX_KEEPERS: usize = 1024;
const MAX_KEYS_PER_KEEPER: usize = 16;
const MAX_KEYS_FILE_BYTES: u64 = 1024 * 1024;

/// One keeper of the fleet and every public key a verifier accepts from it.
/// Rotation adds the new key before the keeper signs with it and removes the
/// old key only once nothing that must verify depends on it alone.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TrustedKeeper {
    pub identity: Uuid,
    pub keys: Vec<[u8; 32]>,
}

/// The trust root: the full keeper inventory of one journal, including spares
/// and keepers that left, with their Ed25519 signing keys. A head signed by
/// any two members of the ensemble it names verifies, so proofs stay valid
/// across keeper replacement while the signers' keys stay installed.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct KeeperKeys {
    pub journal: Uuid,
    pub keepers: Vec<TrustedKeeper>,
}

impl KeeperKeys {
    /// Reads and validates a JSON key set, for example the keepers'
    /// `authenticated.keys_file` or a consumer's copy of it.
    pub fn read(path: &Path) -> io::Result<Self> {
        let file = File::open(path)?;
        let mut bytes = Vec::new();
        file.take(MAX_KEYS_FILE_BYTES + 1).read_to_end(&mut bytes)?;
        if bytes.len() as u64 > MAX_KEYS_FILE_BYTES {
            return Err(invalid("keeper key set exceeds its size limit"));
        }
        let keys: Self =
            serde_json::from_slice(&bytes).map_err(|_| invalid("invalid keeper key set"))?;
        if !keys.valid() {
            return Err(invalid("invalid keeper key set"));
        }
        Ok(keys)
    }

    /// Every identity and key is nonzero, identities are distinct, and a public
    /// key belongs to exactly one keeper.
    pub fn valid(&self) -> bool {
        let mut identities = BTreeSet::new();
        let mut keys = BTreeSet::new();
        !self.journal.is_nil()
            && self.keepers.len() >= QUORUM
            && self.keepers.len() <= MAX_KEEPERS
            && self.keepers.iter().all(|keeper| {
                !keeper.identity.is_nil()
                    && identities.insert(keeper.identity)
                    && !keeper.keys.is_empty()
                    && keeper.keys.len() <= MAX_KEYS_PER_KEEPER
                    && keeper
                        .keys
                        .iter()
                        .all(|key| *key != [0; 32] && keys.insert(*key))
            })
    }

    /// Whether `key` is installed for `keeper`.
    pub fn accepts(&self, keeper: KeeperId, key: &[u8; 32]) -> bool {
        self.keepers
            .iter()
            .find(|trusted| trusted.identity.as_u128() == keeper.0)
            .is_some_and(|trusted| trusted.keys.contains(key))
    }

    /// One keeper's signature, as a collector checks each share before counting it.
    pub fn verify_one(&self, statement: &[u8], signature: &HeadSignature) -> bool {
        signature.keeper.0 != 0
            && self.accepts(signature.keeper, &signature.key)
            && UnparsedPublicKey::new(&ED25519, signature.key)
                .verify(statement, &signature.signature)
                .is_ok()
    }

    /// At least `QUORUM` distinct members of `ensemble` signed `statement` with
    /// installed keys. Any duplicate, outsider or invalid signature rejects it.
    pub fn verify_quorum(
        &self,
        statement: &[u8],
        ensemble: [KeeperId; 3],
        signatures: &[HeadSignature],
    ) -> Result<(), ProofError> {
        if !self.valid() || signatures.len() > ensemble.len() {
            return Err(ProofError::Signature);
        }
        let mut signers = BTreeSet::new();
        for signature in signatures {
            if !ensemble.contains(&signature.keeper)
                || !signers.insert(signature.keeper)
                || !self.verify_one(statement, signature)
            {
                return Err(ProofError::Signature);
            }
        }
        if signers.len() < QUORUM {
            return Err(ProofError::Signature);
        }
        Ok(())
    }

    /// A digest of the canonical key set, for operators to compare installed copies.
    /// Verification never depends on it, so it may change with every rotation.
    pub fn digest(&self) -> Hash {
        let mut keepers: Vec<_> = self.keepers.iter().collect();
        keepers.sort_by_key(|keeper| keeper.identity);
        let mut digest = Sha256::new();
        digest.update(b"logkeeper/stream/authenticated/keys/v1\0");
        digest.update(self.journal.as_bytes());
        digest.update((keepers.len() as u64).to_be_bytes());
        for keeper in keepers {
            let mut keys = keeper.keys.clone();
            keys.sort();
            digest.update(keeper.identity.as_bytes());
            digest.update((keys.len() as u64).to_be_bytes());
            for key in keys {
                digest.update(key);
            }
        }
        digest.finalize().into()
    }
}

/// A keeper's dedicated history signing key. It is independent of the keeper's
/// TLS key and of its timed-original attestation key.
pub struct Signer {
    keeper: KeeperId,
    journal: Uuid,
    key: Ed25519KeyPair,
}

impl Signer {
    pub fn new(keeper: KeeperId, journal: Uuid, key: Ed25519KeyPair) -> Self {
        Self {
            keeper,
            journal,
            key,
        }
    }

    /// Loads a PKCS#8 Ed25519 key from a private file and checks that `keys`
    /// installs its public key for this keeper and that it differs from the TLS key.
    pub fn load(
        keeper: KeeperId,
        path: &Path,
        keys: &KeeperKeys,
        tls_public_key: &[u8],
    ) -> io::Result<Self> {
        if !path.is_absolute() {
            return Err(invalid("the history signing key path must be absolute"));
        }
        let file = File::open(path)?;
        let metadata = file.metadata()?;
        if !metadata.is_file() || metadata.len() > 256 {
            return Err(invalid("invalid history signing key file"));
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if metadata.permissions().mode() & 0o037 != 0 {
                return Err(invalid("unsafe history signing key permissions"));
            }
        }
        let mut bytes = Vec::new();
        file.take(257).read_to_end(&mut bytes)?;
        let key = Ed25519KeyPair::from_pkcs8_maybe_unchecked(&bytes)
            .map_err(|_| invalid("invalid history signing Ed25519 key"))?;
        let signer = Self::new(keeper, keys.journal, key);
        if signer.public_key().as_slice() == tls_public_key {
            return Err(invalid("history signing and TLS keys must be independent"));
        }
        if !keys.accepts(keeper, &signer.public_key()) {
            return Err(invalid(
                "the keeper key set does not install this keeper's signing key",
            ));
        }
        Ok(signer)
    }

    pub fn keeper(&self) -> KeeperId {
        self.keeper
    }

    pub fn journal(&self) -> Uuid {
        self.journal
    }

    pub fn public_key(&self) -> [u8; 32] {
        self.key.public_key().as_ref().try_into().unwrap()
    }

    pub fn sign(&self, head: &Head) -> HeadSignature {
        HeadSignature {
            keeper: self.keeper,
            key: self.public_key(),
            signature: self.key.sign(&head.statement()).as_ref().to_vec(),
        }
    }
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}
