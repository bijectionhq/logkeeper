use crate::ordered::Fingerprint;
use crate::ordered::daemon::{invalid, receipt_keys::ReceiptKeys, sign::verify_bytes};
use std::io;

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
