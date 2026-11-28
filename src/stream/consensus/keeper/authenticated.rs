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
        Archive, CatalogAuthority, CatalogHistory, Certification, Hash, Head, Leaf, QuorumSignature,
        SignedHead, SignedStreamAuthority, StreamAuthority, Tree, VoterKeys,
    },
    decode, encode,
};

pub(in crate::stream::consensus) const ARCHIVE_PAGE: usize = 1024;
pub(in crate::stream::consensus) const HISTORY_PAGE: usize = 128;

mod archives;
mod certification;
mod stages;

use certification::CachedHead;
use stages::STAGE_STRIPES;

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AuthenticatedConfig {
    pub signer_pkcs8_file: PathBuf,
    pub archive_directory: PathBuf,
    pub maximum_clock_error_micros: u32,
}

pub(super) struct Authentication {
    key: Ed25519KeyPair,
    stages: PathBuf,
    stage_locks: [parking_lot::Mutex<()>; STAGE_STRIPES],
    /// This catalog's stream archives within the shared mount.
    archive_directory: PathBuf,
    maximum_clock_error_micros: u32,
    heads: parking_lot::Mutex<BTreeMap<StreamId, CachedHead>>,
    /// The verified catalog history as last read, extended once per tend.
    history: parking_lot::Mutex<Option<CatalogHistory>>,
}

#[derive(Clone, Serialize, Deserialize)]
pub(in crate::stream::consensus) enum AuthenticationRequest {
    History { from: usize },
    StreamAuthority { stream: StreamId },
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
    StreamAuthorityShare(StreamAuthority),
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
            | Self::StreamAuthorityShare(_)
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
        catalog: Uuid,
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
        let archive_directory = config
            .archive_directory
            .join(format!("catalog-{:032x}", catalog.as_u128()));
        fs::create_dir_all(&archive_directory)?;
        sync_directory(&config.archive_directory)?;
        Ok(Self {
            key,
            stages,
            stage_locks: std::array::from_fn(|_| parking_lot::Mutex::new(())),
            archive_directory,
            maximum_clock_error_micros: config.maximum_clock_error_micros,
            heads: parking_lot::Mutex::default(),
            history: parking_lot::Mutex::default(),
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

impl Engine {

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
            AuthenticationPeerRequest::StreamAuthorityShare(proposed) => {
                self.stream_authority_share(&proposed).await
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

}
