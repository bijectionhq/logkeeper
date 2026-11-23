use crate::ordered::Fingerprint;
use crate::ordered::daemon::{invalid, receipt_keys::ReceiptKeys, sign::verify_bytes};
use std::io;

#[cfg(verus_keep_ghost)]
use {
    crate::{
        contracts::{fingerprint, signed_message},
        reference::*,
    },
    vstd::prelude::*,
};

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out is Ok ==> exists|key: Fingerprint| repairAuthority(keys, key)
        && #[trigger] fingerprint(key) == *issuer
        && signed_message(key, signature@) == Some(seed@),
))]
pub(crate) fn verify_repair_signature(
    keys: &ReceiptKeys,
    issuer: &Fingerprint,
    seed: &[u8],
    signature: &[u8],
) -> io::Result<()> {
    let Some(key) = keys.repair_package_key(issuer) else {
        return Err(invalid(
            "the repair package signer is not in the installed predecessor",
        ));
    };
    verify_bytes(key, seed, signature)
}
