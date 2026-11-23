use super::invalid;
use crate::ordered::Fingerprint;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::io;
use uuid::Uuid;

pub(crate) struct ReceiptKeys {
    pub(crate) active: BTreeMap<Uuid, [u8; 32]>,
    pub(crate) predecessor: Vec<[u8; 32]>,
    pub(crate) retained: Vec<[u8; 32]>,
}

impl ReceiptKeys {
    pub(crate) fn barrier_keys(&self) -> BTreeSet<[u8; 32]> {
        let mut keys = active_keys(&self.active);
        keys.extend(&self.predecessor);
        keys.extend(&self.retained);
        keys
    }

    pub(crate) fn validate_successor_keys(&self, source: &Self) -> io::Result<()> {
        let active = active_keys(&source.active);
        let mut index = 0;
        while index < self.predecessor.len() {
            if !active.contains(&self.predecessor[index]) {
                return Err(invalid(
                    "a repair key is outside the active predecessor roster",
                ));
            }
            index += 1;
        }
        if !source.barrier_keys().is_subset(&self.barrier_keys()) {
            return Err(invalid(
                "the successor dropped installed barrier verification keys",
            ));
        }
        Ok(())
    }

    pub(crate) fn repair_package_key(&self, issuer: &Fingerprint) -> Option<&[u8; 32]> {
        let mut index = 0;
        while index < self.predecessor.len() {
            let key = &self.predecessor[index];
            if fingerprints_match(&fingerprint(key), issuer) {
                return Some(key);
            }
            index += 1;
        }
        None
    }
}

fn fingerprint(key: &[u8; 32]) -> Fingerprint {
    Sha256::digest(key).into()
}

fn active_keys(active: &BTreeMap<Uuid, [u8; 32]>) -> BTreeSet<[u8; 32]> {
    active.values().copied().collect()
}

pub(crate) fn fingerprints_match(left: &Fingerprint, right: &Fingerprint) -> bool {
    let mut index = 0;
    while index < left.len() {
        if left[index] != right[index] {
            return false;
        }
        index += 1;
    }
    true
}
