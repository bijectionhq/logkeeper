use std::{
    collections::BTreeMap,
    fs::{self, File, OpenOptions},
    io::{self, Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
    sync::Arc,
    time::{SystemTime, UNIX_EPOCH},
};

use bytes::Bytes;
use futures::stream::{FuturesUnordered, StreamExt};
use journal_contract::{JournalError, Lsn, StreamId};
use ring::signature::{Ed25519KeyPair, KeyPair};
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use sha2::{Digest, Sha256};
use tokio::time::Instant;
use uuid::Uuid;

use super::{Command, Engine, Group, Outcome, REQUEST_TIMEOUT, Reply, Request, failure, invalid};
use crate::server::durability::{sync_directory, sync_file};
use crate::stream::consensus::{
    CATALOG_STREAM, CLUSTER_VERSION_AUTHENTICATED, Configuration, Voters,
    authenticated::{
        Archive, CatalogAuthority, CatalogHistory, Hash, Head, Leaf, QuorumSignature, SignedHead,
        Tree, VoterKeys,
    },
    decode, encode,
};

pub(in crate::stream::consensus) const ARCHIVE_PAGE: usize = 1024;
pub(in crate::stream::consensus) const HISTORY_PAGE: usize = 128;

const STAGE_RETAIN_MICROS: i64 = 30_000_000;
const STAGE_STRIPES: usize = 64;
const STAGE_LIMIT: usize = super::MAX_PENDING_WRITES * 2;
const STAGE_BYTES_LIMIT: u64 = STAGE_LIMIT as u64 * (super::super::MAX_RECORD as u64 + 65_536);
const STAGE_MAGIC: &[u8; 8] = b"LKASTG01";
const STAMP_BYTES: usize = STAGE_MAGIC.len() + 16;

#[derive(Clone, Copy, Serialize, Deserialize)]
struct DurabilityStamp {
    upper_micros: i64,
    retained_until_micros: i64,
}

impl DurabilityStamp {
    fn valid(self) -> bool {
        self.upper_micros > 0
            && self.upper_micros.checked_add(STAGE_RETAIN_MICROS)
                == Some(self.retained_until_micros)
    }

    fn read(file: &mut File) -> io::Result<Self> {
        file.seek(SeekFrom::End(-(STAMP_BYTES as i64)))?;
        let mut bytes = [0; STAMP_BYTES];
        file.read_exact(&mut bytes)?;
        let stamp = Self {
            upper_micros: i64::from_be_bytes(bytes[8..16].try_into().unwrap()),
            retained_until_micros: i64::from_be_bytes(bytes[16..24].try_into().unwrap()),
        };
        if &bytes[..8] != STAGE_MAGIC || !stamp.valid() {
            return Err(invalid("invalid authenticated durability stage"));
        }
        Ok(stamp)
    }

    fn write(self, file: &mut File) -> io::Result<()> {
        file.write_all(STAGE_MAGIC)?;
        file.write_all(&self.upper_micros.to_be_bytes())?;
        file.write_all(&self.retained_until_micros.to_be_bytes())
    }

    fn quorum_bound(stamps: &[Self], quorum: usize) -> Option<i64> {
        stamps
            .iter()
            .map(|stamp| stamp.upper_micros)
            .filter(|&bound| {
                stamps
                    .iter()
                    .filter(|stamp| {
                        stamp.upper_micros <= bound && bound < stamp.retained_until_micros
                    })
                    .count()
                    >= quorum
            })
            .min()
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AuthenticatedConfig {
    pub signer_pkcs8_file: PathBuf,
    pub archive_directory: PathBuf,
    pub maximum_clock_error_micros: u32,
}

#[derive(Clone)]
struct CachedHead {
    configuration: Configuration,
    voters: VoterKeys,
    checked_at: Instant,
    signed: SignedHead,
}

pub(super) struct Authentication {
    key: Ed25519KeyPair,
    stages: PathBuf,
    stage_locks: [parking_lot::Mutex<()>; STAGE_STRIPES],
    archive_directory: PathBuf,
    maximum_clock_error_micros: u32,
    heads: parking_lot::Mutex<BTreeMap<StreamId, CachedHead>>,
}

#[derive(Clone, Serialize, Deserialize)]
pub(in crate::stream::consensus) enum AuthenticationRequest {
    History { from: usize },
    Head { size: Option<u64> },
    Inclusion { at: Lsn, size: Option<u64> },
    Consistency { earlier: u64, later: u64 },
    ArchivePage { from: Lsn, through: u64 },
}

#[derive(Clone, Serialize, Deserialize)]
pub(in crate::stream::consensus) enum AuthenticationPeerRequest {
    Key,
    Authority {
        stream: StreamId,
        configuration: Configuration,
    },
    AuthorityShare(CatalogAuthority),
    HeadAuthority {
        stream: StreamId,
        digest: Hash,
    },
    HeadShare {
        head: Head,
        voters: Voters,
    },
    StageDurability {
        stream: StreamId,
        configuration: Configuration,
        operation: Bytes,
    },
}

impl AuthenticationPeerRequest {
    pub(in crate::stream::consensus) fn stream(&self) -> StreamId {
        match self {
            Self::Key
            | Self::Authority { .. }
            | Self::AuthorityShare(_)
            | Self::HeadAuthority { .. } => CATALOG_STREAM,
            Self::HeadShare { head, .. } => head.stream,
            Self::StageDurability { stream, .. } => *stream,
        }
    }
}

#[derive(Serialize, Deserialize)]
pub(in crate::stream::consensus) struct Authority {
    pub catalog: Uuid,
    pub digest: Hash,
    pub voters: VoterKeys,
}

#[derive(Serialize, Deserialize)]
pub(in crate::stream::consensus) struct HistoryPage {
    pub genesis: CatalogAuthority,
    pub transitions: Vec<crate::stream::consensus::authenticated::SignedAuthority>,
    pub more: bool,
}

#[derive(Serialize, Deserialize)]
pub(in crate::stream::consensus) struct Included {
    pub leaf: Leaf,
    pub path: Vec<Hash>,
    pub signed_head: SignedHead,
}

impl Authentication {
    pub(super) fn open(
        config: AuthenticatedConfig,
        data: &Path,
        tls_key: &[u8],
    ) -> io::Result<Self> {
        if !config.signer_pkcs8_file.is_absolute()
            || !config.archive_directory.is_absolute()
            || config.archive_directory.starts_with(data)
            || config.maximum_clock_error_micros == 0
        {
            return Err(invalid(
                "invalid authenticated log paths or clock error bound",
            ));
        }
        let signer = File::open(config.signer_pkcs8_file)?;
        let metadata = signer.metadata()?;
        if !metadata.is_file() || metadata.len() > 256 {
            return Err(invalid("invalid authenticated log signing key file"));
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if metadata.permissions().mode() & 0o037 != 0 {
                return Err(invalid("unsafe authenticated log signing key permissions"));
            }
        }
        let mut key = Vec::new();
        signer.take(257).read_to_end(&mut key)?;
        let key = Ed25519KeyPair::from_pkcs8_maybe_unchecked(&key)
            .map_err(|_| invalid("invalid authenticated log Ed25519 key"))?;
        if key.public_key().as_ref() == tls_key {
            return Err(invalid(
                "authenticated log and TLS keys must be independent",
            ));
        }
        let stages = data.join("authenticated-stages");
        fs::create_dir_all(&stages)?;
        sync_directory(data)?;
        fs::create_dir_all(&config.archive_directory)?;
        Ok(Self {
            key,
            stages,
            stage_locks: std::array::from_fn(|_| parking_lot::Mutex::new(())),
            archive_directory: config.archive_directory,
            maximum_clock_error_micros: config.maximum_clock_error_micros,
            heads: parking_lot::Mutex::default(),
        })
    }

    pub(super) fn public_key(&self) -> [u8; 32] {
        self.key.public_key().as_ref().try_into().unwrap()
    }

    pub(super) fn sign(&self, keeper: Uuid, statement: &[u8]) -> QuorumSignature {
        QuorumSignature {
            keeper,
            signature: self.key.sign(statement).as_ref().to_vec(),
        }
    }

    fn remember_head(&self, stream: StreamId, head: CachedHead) {
        let mut heads = self.heads.lock();
        if heads
            .get(&stream)
            .is_none_or(|prior| prior.signed.head.size <= head.signed.head.size)
        {
            heads.insert(stream, head);
        }
    }

    pub(super) fn archive_root(&self) -> &Path {
        &self.archive_directory
    }

    fn clock_nanos(&self) -> Option<u128> {
        Some(
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .ok()?
                .as_nanos(),
        )
    }

    fn time_upper(&self) -> Option<i64> {
        i64::try_from(self.clock_nanos()?.div_ceil(1_000))
            .ok()?
            .checked_add(i64::from(self.maximum_clock_error_micros))
    }

    fn time_lower(&self) -> Option<i64> {
        i64::try_from(self.clock_nanos()? / 1_000)
            .ok()?
            .checked_sub(i64::from(self.maximum_clock_error_micros))
    }

    fn stage_lock(&self, stream: StreamId) -> parking_lot::MutexGuard<'_, ()> {
        self.stage_locks[(stream.0 as usize) % STAGE_STRIPES].lock()
    }

    fn stage_directory(&self, stream: StreamId) -> PathBuf {
        self.stages.join(format!("{:032x}", stream.0))
    }

    fn stage(
        &self,
        stream: StreamId,
        epoch: u64,
        through: Lsn,
        applied: Lsn,
        operation: &Bytes,
    ) -> io::Result<DurabilityStamp> {
        let _stage = self.stage_lock(stream);
        let directory = self.stage_directory(stream);
        fs::create_dir_all(&directory)?;
        sync_directory(&self.stages)?;
        let (count, bytes) = self.remove_stages(&directory, epoch, applied)?;
        let digest = Sha256::digest(operation);
        let target = directory.join(format!("{epoch:016x}-{:016x}-{digest:x}.stage", through.0));
        match File::open(&target) {
            Ok(mut staged) => {
                let stamp = DurabilityStamp::read(&mut staged)?;
                if staged.metadata()?.len() != (operation.len() + STAMP_BYTES) as u64 {
                    return Err(invalid("authenticated durability stage length differs"));
                }
                staged.rewind()?;
                let mut retained = Vec::with_capacity(operation.len());
                staged
                    .take(operation.len() as u64)
                    .read_to_end(&mut retained)?;
                if retained != *operation {
                    return Err(invalid("authenticated durability stage bytes differ"));
                }
                return Ok(stamp);
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => (),
            Err(error) => return Err(error),
        }
        if count >= STAGE_LIMIT
            || bytes.saturating_add((operation.len() + STAMP_BYTES) as u64) > STAGE_BYTES_LIMIT
        {
            return Err(io::Error::other("authenticated durability staging full"));
        }
        let temporary = directory.join(format!(".{}.tmp", Uuid::new_v4()));
        let result = (|| {
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&temporary)?;
            file.write_all(operation)?;
            sync_file(&file)?;
            let upper_micros = self
                .time_upper()
                .ok_or_else(|| invalid("authenticated log clock is unavailable"))?;
            let retained_until_micros = upper_micros
                .checked_add(STAGE_RETAIN_MICROS)
                .ok_or_else(|| invalid("authenticated durability stage expiry overflowed"))?;
            let stamp = DurabilityStamp {
                upper_micros,
                retained_until_micros,
            };
            stamp.write(&mut file)?;
            sync_file(&file)?;
            fs::rename(&temporary, target)?;
            sync_directory(&directory)?;
            Ok(stamp)
        })();
        let _ = fs::remove_file(temporary);
        result
    }

    fn remove_stages(
        &self,
        directory: &Path,
        epoch: u64,
        applied: Lsn,
    ) -> io::Result<(usize, u64)> {
        let entries = match fs::read_dir(directory) {
            Ok(entries) => entries,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok((0, 0)),
            Err(error) => return Err(error),
        };
        let mut count = 0usize;
        let mut bytes = 0u64;
        let lower = self.time_lower();
        for entry in entries {
            let entry = entry?;
            let name = entry.file_name();
            let name = name
                .to_str()
                .ok_or_else(|| invalid("invalid authenticated stage filename"))?;
            let remove = if name.starts_with('.') && name.ends_with(".tmp") {
                true
            } else {
                let mut parts = name.split('-');
                let epoch_at = || invalid("invalid authenticated durability stage coordinate");
                let saved_epoch = u64::from_str_radix(parts.next().ok_or_else(epoch_at)?, 16)
                    .map_err(|_| epoch_at())?;
                let through = u64::from_str_radix(parts.next().ok_or_else(epoch_at)?, 16)
                    .map_err(|_| epoch_at())?;
                if saved_epoch < epoch || through <= applied.0 {
                    true
                } else {
                    let mut file = File::open(entry.path())?;
                    let stamp = DurabilityStamp::read(&mut file)?;
                    if lower.is_some_and(|lower| lower >= stamp.retained_until_micros) {
                        true
                    } else {
                        count += 1;
                        bytes = bytes.saturating_add(file.metadata()?.len());
                        false
                    }
                }
            };
            if remove {
                fs::remove_file(entry.path())?;
            }
        }
        Ok((count, bytes))
    }

    fn prune_stages(&self, stream: StreamId, epoch: u64, at: Lsn) -> io::Result<()> {
        let _stage = self.stage_lock(stream);
        self.remove_stages(&self.stage_directory(stream), epoch, at)
            .map(|_| ())
    }

    fn archive_directory(&self, stream: StreamId) -> PathBuf {
        self.archive_directory.join(format!("{:032x}", stream.0))
    }

    fn save_archive(&self, archive: &Archive) -> io::Result<()> {
        let head = archive.signed_head.head;
        let directory = self.archive_directory(head.stream);
        fs::create_dir_all(&directory)?;
        sync_directory(&self.archive_directory)?;
        let target = directory.join(format!("{:016x}.archive", head.size));
        let temporary = directory.join(format!(".{}.tmp", Uuid::new_v4()));
        let result = (|| {
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&temporary)?;
            archive.write_to(&mut file)?;
            sync_file(&file)?;
            match fs::hard_link(&temporary, &target) {
                Ok(()) => (),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                    let existing = Archive::read_from(&mut File::open(&target)?)?;
                    existing
                        .verify(archive.history.genesis.root())
                        .map_err(io::Error::other)?;
                    if existing.signed_head.head.stream != head.stream
                        || existing.signed_head.head.size != head.size
                        || existing.signed_head.head.root != head.root
                    {
                        return Err(invalid(
                            "retirement left a conflicting authenticated archive",
                        ));
                    }
                }
                Err(error) => return Err(error),
            }
            sync_directory(&directory)
        })();
        let _ = fs::remove_file(temporary);
        result
    }

    fn read_archive(&self, stream: StreamId, size: Option<u64>) -> io::Result<Archive> {
        let directory = self.archive_directory(stream);
        let size = match size {
            Some(size) => size,
            None => {
                let mut largest = None;
                for entry in fs::read_dir(&directory)? {
                    let entry = entry?;
                    if let Some(size) = entry
                        .file_name()
                        .to_str()
                        .and_then(|name| name.strip_suffix(".archive"))
                        .and_then(|name| u64::from_str_radix(name, 16).ok())
                    {
                        largest = largest.max(Some(size));
                    }
                }
                largest.ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?
            }
        };
        let archive = Archive::read_from(&mut File::open(
            directory.join(format!("{size:016x}.archive")),
        )?)?;
        if archive.signed_head.head.stream != stream
            || archive.verify(archive.history.genesis.root()).is_err()
        {
            return Err(invalid("authenticated archive does not match its stream"));
        }
        Ok(archive)
    }
}

pub(super) fn authentication_reply(value: &impl Serialize) -> Reply {
    match encode(value) {
        Ok(bytes) => Reply::Decision(Outcome::Authentication(bytes)),
        Err(_) => failure(JournalError::Unavailable),
    }
}

pub(in crate::stream::consensus) fn authentication_value<T: DeserializeOwned>(
    reply: Reply,
) -> journal_contract::Result<T> {
    match reply {
        Reply::Decision(Outcome::Authentication(bytes)) => {
            decode(&bytes).map_err(|_| JournalError::Corrupted)
        }
        Reply::Decision(Outcome::Refused(error)) => Err(error),
        Reply::Unsupported(_) => Err(JournalError::Unsupported),
        _ => Err(JournalError::Unavailable),
    }
}

fn ordinary_operation(
    command: &Command,
) -> Option<(&crate::stream::consensus::Fence, &str, Lsn, Lsn)> {
    match command {
        Command::Append {
            fence, owner, at, ..
        } => Some((fence, owner, *at, *at)),
        Command::AppendBatch {
            fence,
            owner,
            at,
            payloads,
        } if super::super::state::valid_batch(payloads) => {
            let last = at.0.checked_add((payloads.len() - 1) as u64)?;
            Some((fence, owner, *at, Lsn(last)))
        }
        Command::InstallCheckpoint {
            fence,
            owner,
            checkpoint,
        } => {
            let at = checkpoint.checkpoint_lsn;
            Some((fence, owner, at, at))
        }
        _ => None,
    }
}

impl Engine {
    pub(super) async fn write_with_durability(&self, group: &Group, command: Command) -> Reply {
        if !group.genesis.authenticated {
            return group.write(command).await;
        }
        let Some((_, _, _, through)) = ordinary_operation(&command) else {
            return failure(JournalError::Unsupported);
        };
        let state = match group.state.timed_view(0) {
            Ok(state) if !state.changing => state,
            Ok(_) => return failure(JournalError::Unavailable),
            Err(error) => return failure(error),
        };
        if through <= state.head {
            return group.write(command).await;
        }
        let leadership = group.raft.metrics();
        use openraft::async_runtime::WatchReceiver;
        let leader = leadership.borrow_watched().current_leader;
        if leader != Some(self.id.as_u128()) {
            return super::leader_reply(leader);
        }
        let Ok(bytes) = encode(&command) else {
            return failure(JournalError::Unavailable);
        };
        let stream = group.genesis.stream;
        let configuration = state.configuration;
        let operation = Bytes::from(bytes);
        let mut stages =
            FuturesUnordered::from_iter(configuration.voters.into_iter().map(|keeper| {
                let operation = operation.clone();
                async move {
                    let reply = if keeper == self.id {
                        self.stage_durability(stream, configuration, operation)
                            .await
                    } else {
                        let request = AuthenticationPeerRequest::StageDurability {
                            stream,
                            configuration,
                            operation,
                        };
                        self.rpc
                            .call_application(
                                keeper,
                                Request::AuthenticationPeer(request),
                                REQUEST_TIMEOUT,
                            )
                            .await
                    };
                    reply
                        .ok()
                        .and_then(|reply| authentication_value::<DurabilityStamp>(reply).ok())
                }
            }));
        let mut stamps = Vec::new();
        while let Some(sample) = stages.next().await {
            if let Some(sample) = sample.filter(|sample| sample.valid()) {
                stamps.push(sample);
                if let Some(bound) =
                    DurabilityStamp::quorum_bound(&stamps, configuration.voters.quorum())
                {
                    return group
                        .write(command.with_quorum_durability(bound, configuration.revision))
                        .await;
                }
            }
        }
        failure(JournalError::Unavailable)
    }

    async fn stage_durability(
        &self,
        stream: StreamId,
        configuration: Configuration,
        operation: Bytes,
    ) -> io::Result<Reply> {
        let Some(authentication) = &self.authentication else {
            return Ok(failure(JournalError::Unsupported));
        };
        let Some(group) = self.groups.lock().await.get(&stream).cloned() else {
            return Ok(failure(JournalError::Unavailable));
        };
        if !group.genesis.authenticated || !self.holds_authority(&group) || !group.state.healthy() {
            return Ok(failure(JournalError::Unavailable));
        }
        let command: Command = decode(&operation)?;
        let Some((fence, owner, _, through)) = ordinary_operation(&command) else {
            return Ok(failure(JournalError::Unsupported));
        };
        let state = match group.state.timed_view(0) {
            Ok(state) => state,
            Err(error) => return Ok(failure(error)),
        };
        let max_ahead =
            super::MAX_PENDING_WRITES as u64 * super::super::state::MAX_BATCH_RECORDS as u64;
        if state.changing
            || configuration != state.configuration
            || !configuration.voters.contains(&self.id)
            || through <= state.head
            || through.0 > state.head.0.saturating_add(max_ahead)
        {
            return Ok(failure(JournalError::Unavailable));
        }
        if state
            .writer
            .as_ref()
            .is_none_or(|(current, principal)| current != fence || principal != owner)
        {
            return Ok(failure(JournalError::Fenced {
                current: state
                    .writer
                    .map_or(journal_contract::Epoch(0), |(current, _)| current.epoch),
            }));
        }
        let epoch = fence.epoch.0;
        let reservation = match self
            .disk
            .space
            .reserve((operation.len() + STAMP_BYTES) as u64)
        {
            Ok(reservation) => reservation,
            Err(_) => return Ok(failure(JournalError::Unavailable)),
        };
        let authentication = Arc::clone(authentication);
        let result = tokio::task::spawn_blocking(move || {
            let _reservation = reservation;
            authentication.stage(stream, epoch, through, state.head, &operation)
        })
        .await;
        Ok(match result {
            Ok(Ok(upper)) => authentication_reply(&upper),
            _ => failure(JournalError::Unavailable),
        })
    }

    pub(super) async fn authentication_peer(
        &self,
        request: AuthenticationPeerRequest,
    ) -> io::Result<Reply> {
        if !self
            .disk
            .write_version_allows(CLUSTER_VERSION_AUTHENTICATED)
            && !matches!(request, AuthenticationPeerRequest::Key)
        {
            self.sync_cluster_version().await;
        }
        let Some(authentication) = &self.authentication else {
            return Ok(failure(JournalError::Unsupported));
        };
        if !self
            .disk
            .write_version_allows(CLUSTER_VERSION_AUTHENTICATED)
            && !matches!(request, AuthenticationPeerRequest::Key)
        {
            return Ok(failure(JournalError::Unsupported));
        }
        match request {
            AuthenticationPeerRequest::Key => {
                Ok(authentication_reply(&authentication.public_key()))
            }
            AuthenticationPeerRequest::Authority {
                stream,
                configuration,
            } => self.stream_authority(stream, configuration).await,
            AuthenticationPeerRequest::AuthorityShare(proposed) => {
                self.authority_share(&proposed).await
            }
            request @ AuthenticationPeerRequest::HeadAuthority { .. } => {
                self.serve_catalog_stream(Request::AuthenticationPeer(request))
                    .await
            }
            AuthenticationPeerRequest::HeadShare { head, voters } => {
                self.head_share(authentication, head, voters).await
            }
            AuthenticationPeerRequest::StageDurability {
                stream,
                configuration,
                operation,
            } => {
                self.stage_durability(stream, configuration, operation)
                    .await
            }
        }
    }

    pub(super) async fn roster_keys(
        &self,
        voters: Voters,
        previous: Option<&VoterKeys>,
    ) -> journal_contract::Result<VoterKeys> {
        let mut keys = BTreeMap::new();
        let mut calls = FuturesUnordered::from_iter(voters.into_iter().map(|keeper| async move {
            let key = if keeper == self.id {
                self.authentication
                    .as_ref()
                    .map(|authentication| authentication.public_key())
            } else {
                self.rpc
                    .call_application(
                        keeper,
                        Request::AuthenticationPeer(AuthenticationPeerRequest::Key),
                        REQUEST_TIMEOUT,
                    )
                    .await
                    .ok()
                    .and_then(|reply| authentication_value::<[u8; 32]>(reply).ok())
            };
            (keeper, key)
        }));
        while let Some((keeper, key)) = calls.next().await {
            let key = key
                .or_else(|| previous.and_then(|roster| roster.key(keeper).copied()))
                .ok_or(JournalError::Unavailable)?;
            keys.insert(keeper, key);
        }
        Ok(VoterKeys::Stable(keys))
    }

    async fn head_share(
        &self,
        authentication: &Authentication,
        head: Head,
        voters: Voters,
    ) -> io::Result<Reply> {
        let Some(group) = self.groups.lock().await.get(&head.stream).cloned() else {
            return Ok(failure(JournalError::Unavailable));
        };
        let Ok((_, configuration, _, membership)) = group.state.placement() else {
            return Ok(failure(JournalError::Unavailable));
        };
        if !group.genesis.authenticated
            || !self.holds_authority(&group)
            || !group.state.healthy()
            || head.catalog != self.catalog_id
            || !voters.contains(&self.id)
            || voters != configuration.voters
            || membership.membership().get_joint_config().len() != 1
        {
            return Ok(failure(JournalError::Unavailable));
        }
        let Some(tree) = group.state.authenticated_tree() else {
            return Ok(failure(JournalError::Unavailable));
        };
        if !head.valid() || tree.root_at(head.size).ok() != Some(head.root) {
            return Ok(failure(JournalError::Unavailable));
        }
        let request = Request::AuthenticationPeer(AuthenticationPeerRequest::HeadAuthority {
            stream: head.stream,
            digest: head.authority_sha256,
        });
        let authority: Authority = match authentication_value(self.catalog_request(request).await?)
        {
            Ok(authority) => authority,
            Err(error) => return Ok(failure(error)),
        };
        if authority.catalog != head.catalog
            || authority.digest != head.authority_sha256
            || authority
                .voters
                .keepers()
                .into_iter()
                .ne(voters.into_iter())
            || authority.voters.key(self.id).copied() != Some(authentication.public_key())
        {
            return Ok(failure(JournalError::Unavailable));
        }
        Ok(authentication_reply(
            &authentication.sign(self.id, &head.statement()),
        ))
    }

    async fn certify_head(
        &self,
        group: &Group,
        tree: &Tree,
        size: u64,
    ) -> Result<SignedHead, Reply> {
        let failed = || failure(JournalError::Unavailable);
        let authentication = self.authentication.as_ref().ok_or_else(failed)?;
        let stream = group.genesis.stream;
        let (_, configuration, _, membership) = group.state.placement().map_err(failure)?;
        if membership.membership().get_joint_config().len() != 1 {
            return Err(failed());
        }
        let root = tree.root_at(size).map_err(|_| failed())?;
        let cached = authentication
            .heads
            .lock()
            .get(&stream)
            .cloned()
            .filter(|head| {
                head.configuration == configuration
                    && head.signed.head.size == size
                    && head.signed.head.root == root
            });
        if let Some(cached) = &cached
            && cached.checked_at.elapsed() < std::time::Duration::from_secs(1)
        {
            return Ok(cached.signed.clone());
        }
        let request = Request::AuthenticationPeer(AuthenticationPeerRequest::Authority {
            stream: group.genesis.stream,
            configuration,
        });
        let reply = self.catalog_request(request).await.map_err(|_| failed())?;
        let authority: Authority = authentication_value(reply).map_err(failure)?;
        if let Some(mut cached) = cached
            && cached.voters == authority.voters
        {
            cached.checked_at = Instant::now();
            let signed = cached.signed.clone();
            authentication.remember_head(stream, cached);
            return Ok(signed);
        }
        let head = Head {
            catalog: authority.catalog,
            stream: group.genesis.stream,
            size,
            root,
            timestamp_micros: authentication.time_upper().ok_or_else(failed)?,

            authority_sha256: authority.digest,
        };
        let statement = head.statement();
        let request = AuthenticationPeerRequest::HeadShare {
            head: head.clone(),
            voters: configuration.voters,
        };
        let mut shares =
            FuturesUnordered::from_iter(configuration.voters.into_iter().map(|keeper| {
                let request = request.clone();
                async move {
                    let reply = if keeper == self.id {
                        self.head_share(authentication, head, configuration.voters)
                            .await
                    } else {
                        self.rpc
                            .call_application(
                                keeper,
                                Request::AuthenticationPeer(request),
                                REQUEST_TIMEOUT,
                            )
                            .await
                    };
                    reply
                        .ok()
                        .and_then(|reply| authentication_value::<QuorumSignature>(reply).ok())
                        .filter(|signature| signature.keeper == keeper)
                }
            }));
        let mut signatures = Vec::new();
        while let Some(signature) = shares.next().await {
            if let Some(signature) = signature {
                signatures.push(signature);
                signatures.sort_by_key(|signature| signature.keeper);
                if authority.voters.verify(&statement, &signatures).is_ok() {
                    let signed = SignedHead { head, signatures };
                    authentication.remember_head(
                        stream,
                        CachedHead {
                            configuration,
                            voters: authority.voters,
                            checked_at: Instant::now(),
                            signed: signed.clone(),
                        },
                    );
                    return Ok(signed);
                }
            }
        }
        Err(failed())
    }

    pub(super) async fn tend_authenticated(&self) -> io::Result<()> {
        let Some(authentication) = &self.authentication else {
            return Ok(());
        };
        let mut schedule = tokio::time::interval(std::time::Duration::from_secs(1));
        schedule.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        loop {
            tokio::select! {
                _ = self.stop.cancelled() => return Ok(()),
                _ = schedule.tick() => (),
            }
            let groups = self
                .groups
                .lock()
                .await
                .values()
                .filter(|group| group.genesis.authenticated)
                .cloned()
                .collect::<Vec<_>>();
            futures::stream::iter(groups)
                .for_each_concurrent(4, |group| async move {
                    let stream = group.genesis.stream;
                    let retained = group.state.timed_view(0);
                    let cleanup = match &retained {
                        Ok(view) => view
                            .writer
                            .as_ref()
                            .map(|(fence, _)| (fence.epoch.0, view.head)),
                        Err(JournalError::Deleted) => Some((u64::MAX, Lsn(u64::MAX))),
                        Err(_) => None,
                    };
                    if let Some((epoch, at)) = cleanup {
                        let authentication = Arc::clone(authentication);
                        let _ = tokio::task::spawn_blocking(move || {
                            authentication.prune_stages(stream, epoch, at)
                        })
                        .await;
                    }
                    if !self.holds_authority(&group) || !group.state.healthy() || retained.is_err()
                    {
                        return;
                    }
                    use openraft::async_runtime::WatchReceiver;
                    if group.raft.metrics().borrow_watched().current_leader
                        != Some(self.id.as_u128())
                    {
                        return;
                    }
                    if let Some(tree) = group.state.authenticated_tree() {
                        let _ = self.certify_head(&group, &tree, tree.size()).await;
                    }
                })
                .await;
        }
    }

    pub(super) async fn authenticated_read(
        &self,
        group: &Group,
        request: AuthenticationRequest,
    ) -> Reply {
        if !group.genesis.authenticated {
            return failure(JournalError::Unsupported);
        }
        if let Err(reply) = group.barrier(Instant::now() + REQUEST_TIMEOUT).await {
            return reply;
        }
        let Some(tree) = group.state.authenticated_tree() else {
            return failure(JournalError::Unavailable);
        };
        match request {
            AuthenticationRequest::Head { size } => {
                match self
                    .certify_head(group, &tree, size.unwrap_or_else(|| tree.size()))
                    .await
                {
                    Ok(head) => authentication_reply(&head),
                    Err(reply) => reply,
                }
            }
            AuthenticationRequest::Inclusion { at, size } => {
                let size = size.unwrap_or_else(|| tree.size());
                let (Some(leaf), Ok(path)) = (tree.leaf(at), tree.inclusion(at, size)) else {
                    return failure(JournalError::NotFound);
                };
                match self.certify_head(group, &tree, size).await {
                    Ok(signed_head) => authentication_reply(&Included {
                        leaf: leaf.clone(),
                        path,
                        signed_head,
                    }),
                    Err(reply) => reply,
                }
            }
            request => Self::tree_read(&tree, request),
        }
    }

    fn tree_read(tree: &Tree, request: AuthenticationRequest) -> Reply {
        match request {
            AuthenticationRequest::Consistency { earlier, later } => {
                match tree.consistency(earlier, later) {
                    Ok(path) => authentication_reply(&path),
                    Err(_) => failure(JournalError::NotFound),
                }
            }
            AuthenticationRequest::ArchivePage { from, through } => {
                let Ok(start) = usize::try_from(from.0.saturating_sub(1)) else {
                    return failure(JournalError::NotFound);
                };
                let Ok(through) = usize::try_from(through) else {
                    return failure(JournalError::NotFound);
                };
                if from.0 == 0 || start > through || through > tree.leaves().len() {
                    return failure(JournalError::NotFound);
                }
                let leaves = &tree.leaves()[start..through.min(start.saturating_add(ARCHIVE_PAGE))];
                authentication_reply(&leaves)
            }
            _ => failure(JournalError::Unsupported),
        }
    }

    pub(super) async fn read_authentication_archive(
        &self,
        stream: StreamId,
        request: AuthenticationRequest,
    ) -> Option<Reply> {
        let authentication = Arc::clone(self.authentication.as_ref()?);
        let size = match &request {
            AuthenticationRequest::Head { size }
            | AuthenticationRequest::Inclusion { size, .. } => *size,
            _ => None,
        };
        let archive =
            tokio::task::spawn_blocking(move || authentication.read_archive(stream, size))
                .await
                .ok()?
                .ok()?;
        Some(match request {
            AuthenticationRequest::Head { size }
                if size.is_none_or(|size| size == archive.tree.size()) =>
            {
                authentication_reply(&archive.signed_head)
            }
            AuthenticationRequest::Inclusion { at, size }
                if size.is_none_or(|size| size == archive.tree.size()) =>
            {
                match (
                    archive.tree.leaf(at),
                    archive.tree.inclusion(at, archive.tree.size()),
                ) {
                    (Some(leaf), Ok(path)) => authentication_reply(&Included {
                        leaf: leaf.clone(),
                        path,
                        signed_head: archive.signed_head,
                    }),
                    _ => failure(JournalError::NotFound),
                }
            }
            request => Self::tree_read(&archive.tree, request),
        })
    }

    pub(super) async fn archive_and_delete(&self, group: &Group) -> Reply {
        let Some(authentication) = self.authentication.clone() else {
            return failure(JournalError::Unsupported);
        };
        if let Err(reply) = group.barrier(Instant::now() + REQUEST_TIMEOUT).await {
            return reply;
        }
        let Some(tree) = group.state.authenticated_tree() else {
            return failure(JournalError::Unavailable);
        };
        let size = tree.size();
        let root = tree.root();
        let signed_head = match self.certify_head(group, &tree, size).await {
            Ok(head) => head,
            Err(reply) => return reply,
        };
        let history = match self.authentication_history().await {
            Ok(history) => history,
            Err(error) => return failure(error),
        };
        let archive = Archive {
            tree,
            signed_head,
            history,
        };
        if archive.verify(archive.history.genesis.root()).is_err() {
            return failure(JournalError::Corrupted);
        }
        if !matches!(
            tokio::task::spawn_blocking(move || authentication.save_archive(&archive)).await,
            Ok(Ok(()))
        ) {
            return failure(JournalError::Unavailable);
        }
        group
            .write(Command::DeleteAuthenticated { size, root })
            .await
    }

    async fn authentication_history(&self) -> journal_contract::Result<CatalogHistory> {
        let mut from = 0;
        let mut transitions = Vec::new();
        loop {
            let request = Request::Authentication {
                stream: CATALOG_STREAM,
                request: AuthenticationRequest::History { from },
            };
            let page: HistoryPage = authentication_value(
                self.catalog_request(request)
                    .await
                    .map_err(|_| JournalError::Unavailable)?,
            )?;
            transitions.extend(page.transitions);
            if !page.more {
                return Ok(CatalogHistory {
                    genesis: page.genesis,
                    transitions,
                });
            }
            if from == transitions.len() {
                return Err(JournalError::Corrupted);
            }
            from = transitions.len();
        }
    }
}
