use super::super::{invalid, receipt_keys::ReceiptKeys, sign::verify_bytes};
use crate::ordered::Fingerprint;
use std::io;

pub(super) fn verify_repair_signature(
    keys: &ReceiptKeys,
    issuer: &Fingerprint,
    seed: &[u8],
    signature: &[u8],
) -> io::Result<()> {
    let key = keys
        .repair_package_key(issuer)
        .ok_or_else(|| invalid("the repair package signer is not in the installed predecessor"))?;
    verify_bytes(key, seed, signature)
}
