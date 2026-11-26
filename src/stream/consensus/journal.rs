//! The `journal-contract` boundary over keeper-hosted consensus streams.
//!
//! RTDB Multi and other contract consumers use [`ConsensusJournal`] without
//! knowing about voter placement, fences or the consensus client.

use std::{collections::BTreeSet, io, path::Path, sync::Arc, time::Duration};

use bytes::Bytes;
use journal_contract::{BoxFuture, Epoch, Journal, JournalError, Lsn, Page, Result, StreamId};
use parking_lot::RwLock;

use crate::stream::timed::{
    EVIDENCE_BYTES, MAX_TIMED_PAYLOAD, TimedEvidence, TimedOriginal, TimedOriginalProof,
    TimedOriginalVerifier,
};
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
    /// This consumer's own failure domain. With a `placement`, reads go first
    /// to a voter in this domain, which avoids a cross-zone round trip.
    #[serde(default)]
    pub domain: Option<String>,
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
    timed: Option<TimedReader>,
    deadline: Duration,
}

/// Retries an idempotent append while the keepers report `Unavailable`, for
/// example while write admission or the log suffix is momentarily full.
/// Definitive refusals return at once. The last error returns at `deadline`.
async fn retry_unavailable<T, F: Future<Output = Result<T>>>(
    deadline: Duration,
    mut attempt: impl FnMut() -> F,
) -> Result<T> {
    let end = tokio::time::Instant::now() + deadline;
    let mut backoff = Duration::from_millis(5);
    loop {
        match attempt().await {
            Err(JournalError::Unavailable) if tokio::time::Instant::now() + backoff < end => {
                tokio::time::sleep(backoff).await;
                backoff = (backoff * 2).min(Duration::from_millis(200));
            }
            result => return result,
        }
    }
}

/// Installed keeper trust and the largest timed payload this consumer
/// appends. Without a payload limit the trust only verifies retained proofs.
#[derive(Clone)]
struct TimedReader {
    verifier: Arc<dyn TimedOriginalVerifier>,
    max_payload_bytes: Option<usize>,
}

impl ConsensusJournal {
    pub fn new(credentials: &Credentials, config: &JournalConfig) -> io::Result<Self> {
        config.validate()?;
        let local = match (&config.domain, &config.placement) {
            (Some(domain), Some(placement)) => placement
                .iter()
                .filter(|(_, keeper_domain)| *keeper_domain == domain)
                .map(|(keeper, _)| *keeper)
                .collect(),
            _ => BTreeSet::new(),
        };
        let client = Client::new(
            credentials,
            config.keepers.clone(),
            config.catalog,
            Duration::from_millis(config.deadline_ms),
        )?
        .with_local_keepers(local);
        Ok(Self {
            client,
            placement: Arc::new(RwLock::new(Placement::new(config))),
            quota_bytes: config.quota_bytes,
            max_record_bytes: config.max_record_bytes,
            timed: None,
            deadline: Duration::from_millis(config.deadline_ms),
        })
    }

    /// Installs keeper trust for timed originals. With `max_payload_bytes`
    /// this journal can append timed originals up to that size.
    pub fn with_timed_original(
        mut self,
        verifier: Arc<dyn TimedOriginalVerifier>,
        max_payload_bytes: Option<usize>,
    ) -> Self {
        let limit = MAX_TIMED_PAYLOAD.min(MAX_RECORD - EVIDENCE_BYTES);
        self.timed = Some(TimedReader {
            verifier,
            max_payload_bytes: max_payload_bytes.map(|bytes| bytes.min(limit)),
        });
        self
    }

    pub fn maximum_timed_original_bytes(&self) -> Option<usize> {
        self.timed.as_ref()?.max_payload_bytes
    }

    /// Appends a timed original and returns its verified quorum proof. The
    /// exact payload is first staged on the stream's two signing voters,
    /// whose signed sync samples become the record's evidence. A retry after
    /// an uncertain outcome returns the committed proof.
    pub async fn append_timed_original(
        &self,
        original: TimedOriginal,
        payload: Bytes,
    ) -> Result<TimedOriginalProof> {
        let timed = self.timed.as_ref().ok_or(JournalError::Unavailable)?;
        let max = timed.max_payload_bytes.ok_or(JournalError::Unavailable)?;
        if payload.len() > max {
            return Err(JournalError::TooLarge { max });
        }
        if !original.matches(&payload) {
            return Err(JournalError::Unavailable);
        }
        if let Ok(proof) = self.prove_timed_original(original).await {
            return Ok(proof);
        }
        let configuration = self.client.configuration(original.stream).await?;
        let mut voters = configuration.voters;
        voters.sort_unstable();
        let stage = |keeper| {
            self.client.stage_original(
                keeper,
                original.stream,
                configuration.revision,
                original,
                payload.clone(),
            )
        };
        let (first, second) = futures::try_join!(stage(voters[0]), stage(voters[1]))?;
        let evidence = TimedEvidence {
            origin: super::timed::origin(original, voters, configuration.revision),
            samples: [first, second],
        };
        let proof = evidence
            .proof(&*timed.verifier)
            .ok_or(JournalError::Unavailable)?;
        let fence = Self::fence(original.epoch);
        match self
            .client
            .append_original(original.stream, fence, &evidence, payload)
            .await
        {
            Ok(at) if at == original.at => Ok(proof),
            Ok(_) => Err(JournalError::Unavailable),
            Err(error) => Err(error),
        }
    }

    /// Reopens the retained proof of a timed original, for example after a
    /// writer takeover. The retained evidence must name the exact original.
    pub async fn prove_timed_original(
        &self,
        original: TimedOriginal,
    ) -> Result<TimedOriginalProof> {
        let timed = self.timed.as_ref().ok_or(JournalError::Unavailable)?;
        let evidence = self
            .client
            .prove_original(original.stream, original.at)
            .await?;
        if evidence.origin.original != original {
            return Err(JournalError::Unavailable);
        }
        evidence
            .proof(&*timed.verifier)
            .ok_or(JournalError::Unavailable)
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
        let health = self.health(stream, &eligible).await;
        let view = assignment::View {
            eligible: &eligible,
            health: &health,
        };
        let Some(next) = assignment::repair_roster(stream, current.voters, &view) else {
            return Ok(None);
        };
        self.client
            .replace(stream, current.revision, next)
            .await
            .map(Some)
    }

    /// The status of every eligible keeper, asked concurrently. A keeper that
    /// does not answer within 2 s counts as down.
    async fn health(
        &self,
        stream: StreamId,
        eligible: &Domains,
    ) -> std::collections::BTreeMap<uuid::Uuid, assignment::Health> {
        let asked = eligible.keys().map(|keeper| async move {
            let status = tokio::time::timeout(
                Duration::from_secs(2),
                self.client.keeper_status(*keeper, stream),
            )
            .await
            .ok()
            .and_then(Result::ok);
            (
                *keeper,
                assignment::Health {
                    live: status.is_some(),
                    accepting: status.is_some_and(|status| status.accepting),
                    streams: status.map_or(0, |status| status.streams),
                },
            )
        });
        futures::future::join_all(asked).await.into_iter().collect()
    }

    /// The status `keeper` reports about itself, with its replica of
    /// `stream`. Operators use it to see whether a draining keeper still
    /// holds the stream.
    pub async fn keeper_status(
        &self,
        keeper: uuid::Uuid,
        stream: StreamId,
    ) -> Result<super::KeeperStatus> {
        self.client.keeper_status(keeper, stream).await
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
            retry_unavailable(self.deadline, || {
                self.client
                    .append_batch(stream, Self::fence(epoch), at, payloads.clone())
            })
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
            let placement = self.placement.read().clone();
            let Placement::Ranked { eligible } = placement else {
                let voters = placement.voters(stream)?;
                return self.client.create(stream, voters, self.quota_bytes).await;
            };
            // A retried or concurrent create reuses the catalog's genesis, so
            // a changed keeper view never proposes a second one.
            let voters = match self.client.claimed_voters(stream).await? {
                Some(voters) => voters,
                None => {
                    let health = self.health(stream, &eligible).await;
                    assignment::choose_balanced(
                        stream,
                        &assignment::View {
                            eligible: &eligible,
                            health: &health,
                        },
                    )
                    .ok_or(JournalError::Unavailable)?
                }
            };
            match self.client.create(stream, voters, self.quota_bytes).await {
                Err(JournalError::Conflict { .. }) => {
                    let voters = self
                        .client
                        .claimed_voters(stream)
                        .await?
                        .ok_or(JournalError::Unavailable)?;
                    self.client.create(stream, voters, self.quota_bytes).await
                }
                result => result,
            }
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
            retry_unavailable(self.deadline, || {
                self.client
                    .append(stream, Self::fence(epoch), at, payload.clone())
            })
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
