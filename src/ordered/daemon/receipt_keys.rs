use super::invalid;
#[cfg(verus_keep_ghost)]
use crate::contracts::{BTreeMap, BTreeSet};
use crate::ordered::Fingerprint;
use sha2::{Digest, Sha256};
#[cfg(not(verus_keep_ghost))]
use std::collections::{BTreeMap, BTreeSet};
use std::io;
use uuid::Uuid;

#[cfg(verus_keep_ghost)]
use {
    crate::{contracts::fingerprint as key_id, reference::*},
    vstd::prelude::*,
};

pub(crate) struct ReceiptKeys {
    pub(crate) active: BTreeMap<Uuid, [u8; 32]>,
    pub(crate) predecessor: Vec<[u8; 32]>,
    pub(crate) retained: Vec<[u8; 32]>,
}

impl ReceiptKeys {
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out@ == verificationKeys(self),
    ))]
    pub(crate) fn barrier_keys(&self) -> BTreeSet<[u8; 32]> {
        let mut keys = active_keys(&self.active);
        keys.extend(&self.predecessor);
        keys.extend(&self.retained);
        keys
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures (out is Ok) == validSuccessorKeys(source, self),
    ))]
    pub(crate) fn validate_successor_keys(&self, source: &Self) -> io::Result<()> {
        let active = active_keys(&source.active);
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                index <= self.predecessor@.len(),
                active@ == source.active@.values(),
                forall|i: int| 0 <= i < index ==> active@.contains(#[trigger] self.predecessor@[i]),
            decreases self.predecessor@.len() - index,
        ))]
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

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out matches Some(key) ==> repairAuthority(self, *key) && key_id(*key) == *issuer,
    ))]
    pub(crate) fn repair_package_key(&self, issuer: &Fingerprint) -> Option<&[u8; 32]> {
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= self.predecessor@.len(),
            decreases self.predecessor@.len() - index,
        ))]
        while index < self.predecessor.len() {
            let key = &self.predecessor[index];
            if fingerprints_match(&fingerprint(key), issuer) {
                #[cfg(verus_keep_ghost)]
                proof! { assert(self.predecessor@[index as int] == *key); }
                return Some(key);
            }
            index += 1;
        }
        None
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == key_id(*key),
))]
fn fingerprint(key: &[u8; 32]) -> Fingerprint {
    Sha256::digest(key).into()
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out@ == active@.values(),
))]
fn active_keys(active: &BTreeMap<Uuid, [u8; 32]>) -> BTreeSet<[u8; 32]> {
    active.values().copied().collect()
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (*left == *right),
))]
pub(crate) fn fingerprints_match(left: &Fingerprint, right: &Fingerprint) -> bool {
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= 32, forall|i: int| 0 <= i < index ==> left@[i] == right@[i],
        decreases 32 - index,
    ))]
    while index < left.len() {
        if left[index] != right[index] {
            return false;
        }
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(*left =~= *right); }
    true
}
