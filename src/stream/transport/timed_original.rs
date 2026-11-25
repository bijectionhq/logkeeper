//! Installed original-write authority for the private stream daemon.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{self, Read},
    path::{Path, PathBuf},
    sync::Arc,
};

use ring::signature::{ED25519, UnparsedPublicKey};
use serde::Deserialize;
use tokio::runtime::Handle;

use super::{Epoch, Identity, Keeper, KeeperId, Limits, SealPolicy, StreamId, invalid};
use crate::stream::timed::{TimedOriginalClock, TimedOriginalVerifier};

#[cfg(unix)]
mod clock;

const MAX_TRUST_BYTES: u64 = 64 * 1024;

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TimedOriginalConfig {
    trust_file: PathBuf,
    original: Option<OriginalConfig>,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct OriginalConfig {
    signer_pkcs8_file: PathBuf,
    receiver_certificate_file: PathBuf,
    receiver_issuer_key: [u8; 32],
    deployment: uuid::Uuid,
    source: uuid::Uuid,
    cell: String,
    rtdb_image: String,
    service_scope: String,
    clock_socket: PathBuf,
    clock_verification_key: [u8; 32],
    clock_timeout_ms: u64,
}

// Keep the registry compatible with RTDB_TIMED_ORIGINAL_TRUST_FILE on the
// paired RTDB adapter. The optional writer limit never grants keeper authority.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TrustConfiguration {
    keepers: Vec<TrustedKeeper>,
    maximum_payload_bytes: Option<usize>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct TrustedKeeper {
    identity: uuid::Uuid,
    verification_key: [u8; 32],
}

struct Trust(BTreeMap<u128, [u8; 32]>);

impl Trust {
    fn read(path: &Path, tls_public_key: &[u8]) -> io::Result<Self> {
        let bytes = read_mount(path, MAX_TRUST_BYTES, false)?;
        let config: TrustConfiguration = serde_json::from_slice(&bytes)
            .map_err(|_| invalid("invalid timed-original keeper trust registry"))?;
        let mut keys = BTreeMap::new();
        let mut public_keys = BTreeSet::new();
        for keeper in config.keepers {
            if keeper.identity.is_nil()
                || keeper.verification_key == [0; 32]
                || keeper.verification_key.as_slice() == tls_public_key
                || !public_keys.insert(keeper.verification_key)
                || keys
                    .insert(keeper.identity.as_u128(), keeper.verification_key)
                    .is_some()
            {
                return Err(invalid(
                    "invalid or reused timed-original keeper verification key",
                ));
            }
        }
        if keys.len() < 2 || config.maximum_payload_bytes == Some(0) {
            return Err(invalid("invalid timed-original keeper trust registry"));
        }
        Ok(Self(keys))
    }
}

impl TimedOriginalVerifier for Trust {
    fn verify(&self, keeper: KeeperId, statement: &[u8], signature: &[u8; 64]) -> bool {
        self.0
            .get(&keeper.0)
            .is_some_and(|key| verify_signature(key, statement, signature))
    }
}

impl TimedOriginalConfig {
    pub(super) fn open(
        self,
        data: &Path,
        id: KeeperId,
        limits: Limits,
        policy: Option<Arc<dyn SealPolicy>>,
        tls_public_key: &[u8],
        runtime: Handle,
    ) -> io::Result<Keeper> {
        let trust = Trust::read(&self.trust_file, tls_public_key)?;
        let clock = self
            .original
            .map(|original| load_clock(original, id, &trust, tls_public_key, runtime))
            .transpose()?;
        let policy = policy.unwrap_or_else(|| Arc::new(|_: &Identity, _: StreamId, _: Epoch| true));
        Keeper::open_with_timed_original(data, id, limits, policy, Arc::new(trust), clock)
    }
}

#[cfg(unix)]
fn load_clock(
    original: OriginalConfig,
    keeper: KeeperId,
    trust: &Trust,
    tls_public_key: &[u8],
    runtime: Handle,
) -> io::Result<Arc<dyn TimedOriginalClock>> {
    Ok(Arc::new(clock::Clock::load(
        original,
        keeper,
        trust,
        tls_public_key,
        runtime,
    )?))
}

#[cfg(not(unix))]
fn load_clock(
    _: OriginalConfig,
    _: KeeperId,
    _: &Trust,
    _: &[u8],
    _: Handle,
) -> io::Result<Arc<dyn TimedOriginalClock>> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "timed-original signing requires a private Unix clock socket",
    ))
}

fn verify_signature(key: &[u8; 32], message: &[u8], signature: &[u8; 64]) -> bool {
    UnparsedPublicKey::new(&ED25519, key)
        .verify(message, signature)
        .is_ok()
}

fn read_mount(path: &Path, limit: u64, private_key: bool) -> io::Result<Vec<u8>> {
    if !path.is_absolute() {
        return Err(invalid("timed-original mount path must be absolute"));
    }
    if !std::fs::metadata(path)?.is_file() {
        return Err(invalid("timed-original mount is not a regular file"));
    }
    let file = File::open(path)?;
    let metadata = file.metadata()?;
    if !metadata.is_file() || metadata.len() > limit {
        return Err(invalid("invalid timed-original mount file"));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        // A private signer can be mounted root-owned and read-only to the
        // daemon's group. Public mounts still need protected integrity.
        let forbidden = if private_key { 0o037 } else { 0o022 };
        if metadata.permissions().mode() & forbidden != 0 {
            return Err(invalid("unsafe permissions on timed-original mount file"));
        }
    }
    #[cfg(not(unix))]
    let _ = private_key;
    let mut bytes = Vec::new();
    file.take(limit + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > limit {
        return Err(invalid("timed-original mount file exceeds its size limit"));
    }
    Ok(bytes)
}
