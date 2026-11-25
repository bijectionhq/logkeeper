//! Verify the receiver certificate and consume fresh, independently signed
//! clock bounds from the keeper's private local clock service.

use std::{
    fs, io,
    os::unix::fs::{FileTypeExt, PermissionsExt},
    path::PathBuf,
    time::Duration,
};

use ring::{
    rand::{SecureRandom, SystemRandom},
    signature::{Ed25519KeyPair, KeyPair},
};
use serde::Deserialize;
use sha2::{Digest, Sha256};
use tokio::{
    io::{AsyncReadExt, AsyncWriteExt},
    net::UnixStream,
    runtime::Handle,
    time::timeout,
};

use super::{KeeperId, OriginalConfig, StreamId, Trust, invalid, read_mount, verify_signature};
use crate::stream::timed::{TimedOriginal, TimedOriginalClock};

const RECEIVER_PURPOSE: &str = "bijection.rtdb.durable-acceptance-clock.v4";
const MAX_RECEIVER_CERTIFICATE_BYTES: u64 = 4096;
const MAX_SIGNER_BYTES: u64 = 256;
const CLOCK_CHALLENGE_DOMAIN: &[u8] = b"logkeeper/stream/original-clock/v1\0";
const NANOS_PER_MICRO: u64 = 1000;
const CLOCK_READING_BYTES: usize = 16;
const CLOCK_SIGNATURE_BYTES: usize = 64;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Envelope {
    statement: String,
    signature: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
struct ReceiverStatement {
    purpose: String,
    deployment: String,
    source: String,
    cell: String,
    rtdb_image: String,
    service_scope: String,
    max_stage_to_durable_lag_ns: u64,
    max_journal_clock_error_ns: u64,
    expires_at_ns: u64,
    evidence_sha256: String,
}

struct Receiver {
    stream: StreamId,
    certificate_sha256: [u8; 32],
    evidence_sha256: [u8; 32],
    max_error_ns: u64,
    expires_ns: u64,
}

impl Receiver {
    fn load(config: &OriginalConfig) -> io::Result<Self> {
        let invalid_receiver = || invalid("invalid timed-original receiver certificate or binding");
        let bytes = read_mount(
            &config.receiver_certificate_file,
            MAX_RECEIVER_CERTIFICATE_BYTES,
            false,
        )?;
        let envelope: Envelope = serde_json::from_slice(&bytes).map_err(|_| invalid_receiver())?;
        let signature = decode_hex::<64>(&envelope.signature).ok_or_else(invalid_receiver)?;
        if !verify_signature(
            &config.receiver_issuer_key,
            envelope.statement.as_bytes(),
            &signature,
        ) {
            return Err(invalid_receiver());
        }
        let statement: ReceiverStatement =
            serde_json::from_str(&envelope.statement).map_err(|_| invalid_receiver())?;
        let evidence_sha256 = digest(&statement.evidence_sha256).ok_or_else(invalid_receiver)?;
        if config.deployment.is_nil()
            || config.source.is_nil()
            || config.cell.is_empty()
            || config.rtdb_image.is_empty()
            || digest(&config.service_scope).is_none()
            || statement.purpose != RECEIVER_PURPOSE
            || statement.deployment != config.deployment.to_string()
            || statement.source != config.source.to_string()
            || statement.cell != config.cell
            || statement.rtdb_image != config.rtdb_image
            || statement.service_scope != config.service_scope
            || statement.max_journal_clock_error_ns == 0
            || statement.max_journal_clock_error_ns > statement.max_stage_to_durable_lag_ns
            || statement.max_stage_to_durable_lag_ns >= statement.expires_at_ns
            || statement.expires_at_ns > i64::MAX as u64
        {
            return Err(invalid_receiver());
        }
        Ok(Self {
            stream: StreamId(config.source.as_u128()),
            certificate_sha256: Sha256::digest(bytes).into(),
            evidence_sha256,
            max_error_ns: statement.max_journal_clock_error_ns,
            expires_ns: statement.expires_at_ns,
        })
    }

    fn allows(&self, original: &TimedOriginal) -> bool {
        let max_cutoff = (self.expires_ns - self.max_error_ns) / NANOS_PER_MICRO;
        original.stream == self.stream
            && original.original_receiver_certificate_sha256 == self.certificate_sha256
            && u64::try_from(original.exclusive_journal_cutoff_micros)
                .is_ok_and(|cutoff| (1..=max_cutoff).contains(&cutoff))
    }
}

pub(super) struct Clock {
    keeper: KeeperId,
    receiver: Receiver,
    signer: Ed25519KeyPair,
    socket: PathBuf,
    clock_key: [u8; 32],
    timeout: Duration,
    runtime: Handle,
}

impl Clock {
    pub(super) fn load(
        config: OriginalConfig,
        keeper: KeeperId,
        trust: &Trust,
        tls_public_key: &[u8],
        runtime: Handle,
    ) -> io::Result<Self> {
        let independent = |key: &[u8; 32]| {
            *key != [0; 32]
                && key.as_slice() != tls_public_key
                && !trust.0.values().any(|keeper_key| keeper_key == key)
        };
        if config.receiver_issuer_key == config.clock_verification_key
            || !independent(&config.receiver_issuer_key)
            || !independent(&config.clock_verification_key)
        {
            return Err(invalid(
                "timed-original receiver and bound authorities need independent keys",
            ));
        }
        let receiver = Receiver::load(&config)?;
        let bytes = read_mount(&config.signer_pkcs8_file, MAX_SIGNER_BYTES, true)?;
        let signer = Ed25519KeyPair::from_pkcs8_maybe_unchecked(&bytes)
            .map_err(|_| invalid("invalid timed-original keeper PKCS#8 signer"))?;
        if trust.0.get(&keeper.0).map(|key| key.as_slice()) != Some(signer.public_key().as_ref()) {
            return Err(invalid(
                "timed-original signer does not match this keeper's installed key",
            ));
        }
        if !config.clock_socket.is_absolute()
            || !fs::metadata(&config.clock_socket).is_ok_and(|meta| {
                meta.file_type().is_socket() && meta.permissions().mode() & 0o007 == 0
            })
            || !(1..=1000).contains(&config.clock_timeout_ms)
        {
            return Err(invalid(
                "timed-original signing requires an installed private clock socket and a bounded timeout",
            ));
        }
        Ok(Self {
            keeper,
            receiver,
            signer,
            socket: config.clock_socket,
            clock_key: config.clock_verification_key,
            timeout: Duration::from_millis(config.clock_timeout_ms),
            runtime,
        })
    }

    fn clock_upper(&self, original: &TimedOriginal) -> Option<i64> {
        if !self.receiver.allows(original) {
            return None;
        }

        // Called immediately after the original local sync. The clock must
        // sample after receiving this unpredictable challenge.
        let mut nonce = [0; 32];
        SystemRandom::new().fill(&mut nonce).ok()?;
        let mut request = CLOCK_CHALLENGE_DOMAIN.to_vec();
        request.extend_from_slice(&self.keeper.0.to_be_bytes());
        request.extend_from_slice(&original.encode());
        request.extend_from_slice(&self.receiver.evidence_sha256);
        request.extend_from_slice(&nonce);
        let mut reply = [0; CLOCK_READING_BYTES + CLOCK_SIGNATURE_BYTES];
        self.runtime
            .block_on(async {
                timeout(self.timeout, async {
                    let mut socket = UnixStream::connect(&self.socket).await?;
                    socket.write_all(&request).await?;
                    socket.read_exact(&mut reply).await?;
                    Ok::<_, io::Error>(())
                })
                .await
            })
            .ok()?
            .ok()?;
        let (reading, signature) = reply.split_at(CLOCK_READING_BYTES);
        request.extend_from_slice(reading);
        if !verify_signature(&self.clock_key, &request, signature.try_into().ok()?) {
            return None;
        }
        let sampled_ns = u64::from_be_bytes(reading[..8].try_into().ok()?);
        let error_ns = u64::from_be_bytes(reading[8..].try_into().ok()?);
        if sampled_ns == 0 || !(1..=self.receiver.max_error_ns).contains(&error_ns) {
            return None;
        }
        let upper_ns = sampled_ns.checked_add(error_ns)?;
        let upper = i64::try_from(upper_ns.div_ceil(NANOS_PER_MICRO)).ok()?;
        (upper_ns < self.receiver.expires_ns && upper < original.exclusive_journal_cutoff_micros)
            .then_some(upper)
    }
}

impl TimedOriginalClock for Clock {
    fn authorize(&self, original: &TimedOriginal) -> bool {
        self.receiver.allows(original)
    }

    fn sync_upper_micros(&self, original: &TimedOriginal) -> Option<i64> {
        self.clock_upper(original)
    }

    fn sign(&self, statement: &[u8]) -> Option<[u8; 64]> {
        self.signer.sign(statement).as_ref().try_into().ok()
    }
}

fn digest(value: &str) -> Option<[u8; 32]> {
    decode_hex(value).filter(|digest| *digest != [0; 32])
}

fn decode_hex<const N: usize>(value: &str) -> Option<[u8; N]> {
    let digit = |value| match value {
        b'0'..=b'9' => Some(value - b'0'),
        b'a'..=b'f' => Some(value - b'a' + 10),
        _ => None,
    };
    if value.len() != 2 * N {
        return None;
    }
    let mut bytes = [0; N];
    for (byte, pair) in bytes.iter_mut().zip(value.as_bytes().chunks_exact(2)) {
        *byte = digit(pair[0])? << 4 | digit(pair[1])?;
    }
    Some(bytes)
}
