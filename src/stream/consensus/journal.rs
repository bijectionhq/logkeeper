//! The `journal-contract` boundary over keeper-hosted consensus streams.
//!
//! RTDB Multi and other contract consumers use [`ConsensusJournal`] without
//! knowing about voter placement, fences or the consensus client.

use std::{collections::BTreeSet, io, path::Path, sync::Arc, time::Duration};

use bytes::Bytes;
use journal_contract::{BoxFuture, Epoch, Journal, JournalError, Lsn, Page, Result, StreamId};
use parking_lot::RwLock;
use serde::Deserialize;

use super::{
    Client, Configuration, Credentials, Domains, Fence, Keepers, MAX_RECORD, assignment,
    state::{MAX_BATCH_BYTES, MAX_BATCH_RECORDS},
};

/// The writer UUID every contract seal uses. The contract identifies a
/// writer by its authenticated principal, and the keeper checks that
/// principal on every seal, append and trim. One fixed UUID therefore makes
/// a reseal by the same principal succeed after a process restart.
const CONTRACT_WRITER: uuid::Uuid =
    uuid::Uuid::from_u128(0x6a6f_7572_6e61_6c2d_636f_6e74_7261_6374);

/// How a contract consumer reaches and places its streams.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JournalConfig {
    /// Application addresses of every keeper.
    pub keepers: Keepers,
    /// The keeper that assigns stream genesis.
    pub catalog: uuid::Uuid,
    /// The three voters of every stream this consumer creates. Give either
    /// this fixed roster or `placement`.
    #[serde(default)]
    pub voters: Option<[uuid::Uuid; 3]>,
    /// Keepers eligible to vote, with their failure domains. Each created
    /// stream gets three of them in distinct domains.
    #[serde(default)]
    pub placement: Option<Domains>,
    /// Placement keepers that streams move off. They keep serving until
    /// every stream has moved.
    #[serde(default)]
    pub draining: BTreeSet<uuid::Uuid>,
    /// Retained byte quota of every stream this consumer creates.
    pub quota_bytes: u64,
    /// Largest record this consumer may append, at most 4 MiB.
    #[serde(default = "default_max_record_bytes")]
    pub max_record_bytes: usize,
    /// Deadline for each client operation, in milliseconds.
    #[serde(default = "default_deadline_ms")]
    pub deadline_ms: u64,
}

fn default_max_record_bytes() -> usize {
    MAX_RECORD
}

fn default_deadline_ms() -> u64 {
    10_000
}

impl JournalConfig {
    pub fn read(path: &Path) -> io::Result<Self> {
        let config: Self = serde_json::from_slice(&std::fs::read(path)?)?;
        config.validate()?;
        Ok(config)
    }

    fn validate(&self) -> io::Result<()> {
        let invalid = |message| io::Error::new(io::ErrorKind::InvalidInput, message);
        if self.max_record_bytes == 0 || self.max_record_bytes > MAX_RECORD {
            return Err(invalid(
                "journal record limit must be between 1 byte and 4 MiB",
            ));
        }
        match (&self.voters, &self.placement) {
            (Some(voters), None) if voters.iter().all(|voter| self.keepers.contains_key(voter)) => {
                ()
            }
            (None, Some(placement))
                if placement
                    .keys()
                    .all(|keeper| self.keepers.contains_key(keeper))
                    && self
                        .draining
                        .iter()
                        .all(|keeper| placement.contains_key(keeper)) => {}
            _ => {
                return Err(invalid(
                    "a journal configuration names fixed voters or a placement of known keepers",
                ));
            }
        }
        Ok(())
    }
}

/// Where streams are placed. Fixed rosters never move.
#[derive(Clone, Debug)]
enum Placement {
    Fixed([uuid::Uuid; 3]),
    Ranked { eligible: Domains },
}

impl Placement {
    fn new(config: &JournalConfig) -> Self {
        match (config.voters, &config.placement) {
            (Some(voters), _) => Self::Fixed(voters),
            (None, Some(placement)) => Self::Ranked {
                eligible: placement
                    .iter()
                    .filter(|(keeper, _)| !config.draining.contains(keeper))
                    .map(|(keeper, domain)| (*keeper, domain.clone()))
                    .collect(),
            },
            (None, None) => unreachable!("validated journal configuration"),
        }
    }

    fn voters(&self, stream: StreamId) -> Result<[uuid::Uuid; 3]> {
        match self {
            Self::Fixed(voters) => Ok(*voters),
            Self::Ranked { eligible } => {
                assignment::choose(stream, eligible).ok_or(JournalError::Unavailable)
            }
        }
    }
}

/// A `journal_contract::Journal` backed by keeper-hosted consensus streams.
#[derive(Clone)]
pub struct ConsensusJournal {
    client: Client,
    placement: Arc<RwLock<Placement>>,
    quota_bytes: u64,
    max_record_bytes: usize,
}

impl ConsensusJournal {
    pub fn new(credentials: &Credentials, config: &JournalConfig) -> io::Result<Self> {
        config.validate()?;
        let client = Client::new(
            credentials,
            config.keepers.clone(),
            config.catalog,
            Duration::from_millis(config.deadline_ms),
        )?;
        Ok(Self {
            client,
            placement: Arc::new(RwLock::new(Placement::new(config))),
            quota_bytes: config.quota_bytes,
            max_record_bytes: config.max_record_bytes,
        })
    }

    /// Applies a changed eligible keeper set or draining list. The keeper
    /// inventory, quota and limits stay as constructed.
    pub fn update_placement(&self, config: &JournalConfig) -> io::Result<()> {
        config.validate()?;
        *self.placement.write() = Placement::new(config);
        Ok(())
    }

    /// Moves one voter of `stream` toward its placement when a current voter
    /// is draining, no longer eligible, or shares a failure domain. Returns
    /// the new configuration after a move, or `None` when the roster already
    /// fits or no eligible keeper can take the voter. Call it again until it
    /// returns `None`. Fixed rosters never move.
    pub async fn reconcile_placement(&self, stream: StreamId) -> Result<Option<Configuration>> {
        let Placement::Ranked { eligible } = self.placement.read().clone() else {
            return Ok(None);
        };
        let current = self.client.configuration(stream).await?;
        let Some(next) = assignment::next_roster(stream, current.voters, &eligible) else {
            return Ok(None);
        };
        self.client
            .replace(stream, current.revision, next)
            .await
            .map(Some)
    }

    /// Commits a contiguous group in LSN order and returns its last LSN.
    /// The group is sent as keeper batches of at most 256 records and 4 MiB.
    /// Each batch commits atomically, so an error can leave a committed
    /// prefix of whole batches. The caller recovers that prefix from the
    /// journal.
    pub async fn append_batch(
        &self,
        stream: StreamId,
        epoch: Epoch,
        records: Vec<(Lsn, Bytes)>,
    ) -> Result<Lsn> {
        let Some(&(last, _)) = records.last() else {
            return Err(JournalError::Unavailable);
        };
        if records
            .windows(2)
            .any(|pair| pair[0].0.0.checked_add(1) != Some(pair[1].0.0))
        {
            return Err(JournalError::Unavailable);
        }
        if records
            .iter()
            .any(|(_, payload)| payload.len() > self.max_record_bytes)
        {
            return Err(JournalError::TooLarge {
                max: self.max_record_bytes,
            });
        }
        let mut records = records.into_iter().peekable();
        while let Some(&(at, _)) = records.peek() {
            let mut payloads = Vec::new();
            let mut bytes = 0usize;
            while let Some((_, payload)) = records.peek() {
                if payloads.len() == MAX_BATCH_RECORDS
                    || bytes.saturating_add(payload.len()) > MAX_BATCH_BYTES
                {
                    break;
                }
                bytes += payload.len();
                payloads.push(records.next().unwrap().1);
            }
            self.client
                .append_batch(stream, Self::fence(epoch), at, payloads)
                .await?;
        }
        Ok(last)
    }

    /// The consensus client, for placement and replica administration.
    pub fn client(&self) -> &Client {
        &self.client
    }

    fn fence(epoch: Epoch) -> Fence {
        Fence {
            epoch,
            writer: CONTRACT_WRITER,
        }
    }

    /// Seals `epoch` for this principal. The keeper's seal installs the epoch
    /// after the expected one, so a seal that jumps ahead installs each
    /// intermediate epoch in turn. Every step is a separate compare-and-set:
    /// a competitor at or above `epoch` fences this seal, and a reseal at the
    /// current epoch by the same principal returns the head.
    async fn seal_epoch(&self, stream: StreamId, epoch: Epoch) -> Result<Lsn> {
        let Some(previous) = epoch.0.checked_sub(1).map(Epoch) else {
            // Consensus streams start at epoch zero with no writer, so epoch
            // zero is never a sealed writer epoch.
            return Err(JournalError::Fenced { current: Epoch(0) });
        };
        loop {
            match self.client.seal(stream, previous, CONTRACT_WRITER).await {
                Ok(sealed) if sealed.fence == Self::fence(epoch) => return Ok(sealed.head),
                Ok(_) => return Err(JournalError::Unavailable),
                Err(JournalError::Fenced { current }) if current < previous => {
                    match self.client.seal(stream, current, CONTRACT_WRITER).await {
                        Ok(_) | Err(JournalError::Fenced { .. }) => continue,
                        Err(error) => return Err(error),
                    }
                }
                Err(error) => return Err(error),
            }
        }
    }
}

impl Journal for ConsensusJournal {
    fn create(&self, stream: StreamId) -> BoxFuture<'_, Result<()>> {
        Box::pin(async move {
            let voters = self.placement.read().voters(stream)?;
            self.client.create(stream, voters, self.quota_bytes).await
        })
    }

    fn seal(&self, stream: StreamId, epoch: Epoch) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(self.seal_epoch(stream, epoch))
    }

    fn append(
        &self,
        stream: StreamId,
        epoch: Epoch,
        at: Lsn,
        payload: Bytes,
    ) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(async move {
            if payload.len() > self.max_record_bytes {
                return Err(JournalError::TooLarge {
                    max: self.max_record_bytes,
                });
            }
            self.client
                .append(stream, Self::fence(epoch), at, payload)
                .await
        })
    }

    fn read(
        &self,
        stream: StreamId,
        from: Lsn,
        max: usize,
        wait: Duration,
    ) -> BoxFuture<'_, Result<Page>> {
        Box::pin(self.client.read(stream, from, max, wait))
    }

    fn head(&self, stream: StreamId) -> BoxFuture<'_, Result<Lsn>> {
        Box::pin(self.client.head(stream))
    }

    fn trim(&self, stream: StreamId, epoch: Epoch, through: Lsn) -> BoxFuture<'_, Result<()>> {
        Box::pin(self.client.trim(stream, Self::fence(epoch), through))
    }

    fn delete(&self, stream: StreamId) -> BoxFuture<'_, Result<()>> {
        Box::pin(self.client.delete(stream))
    }
}
