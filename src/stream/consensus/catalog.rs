//! The catalog assigns one immutable genesis. Later contacts help discovery
//! while the stream's own membership log decides voting authority.
//!
//! A single keeper holds the catalog on its own media unless keepers name
//! `catalog_voters`; then the catalog is a consensus stream of its own (see
//! `keeper/catalog_stream.rs`), and callers find its leader with [`ask`].

use std::{
    collections::BTreeSet,
    io,
    path::{Path, PathBuf},
    sync::Arc,
    time::Duration,
};

use journal_contract::{JournalError, Lsn, StreamId};
use tokio::{sync::Mutex, time::Instant};

use crate::server::durability::{sync_directory, sync_file};

use super::{
    Genesis, Stage, authority, invalid,
    network::Reply,
    placement::Placement,
    state::Outcome,
    storage::{CatalogEntry, Disk, Record},
};

/// The single-keeper catalog's keeper records, beside its data. A
/// development catalog only: production replicates the catalog.
pub(super) const AUTHORITY_FILE: &str = "authority-records.json";

pub(super) struct Catalog {
    disk: Disk,
    claim: Arc<Mutex<()>>,
    /// The authority's keeper records, stored in `authority`.
    records: Arc<Mutex<authority::Records>>,
    authority: PathBuf,
}

impl Catalog {
    pub fn new(disk: Disk, data: &Path) -> io::Result<Self> {
        let authority = data.join(AUTHORITY_FILE);
        let records = match std::fs::read(&authority) {
            Ok(bytes) => serde_json::from_slice(&bytes)
                .map_err(|error| invalid(format!("{}: {error}", authority.display())))?,
            Err(error) if error.kind() == io::ErrorKind::NotFound => Default::default(),
            Err(error) => return Err(error),
        };
        Ok(Self {
            disk,
            claim: Arc::default(),
            records: Arc::new(Mutex::new(records)),
            authority,
        })
    }

    fn enforced(&self) -> bool {
        self.disk.cluster_version() >= super::CLUSTER_VERSION_LEASES
    }

    /// Applies `change` to the records and stores them before they answer.
    async fn change(
        &self,
        records: &mut authority::Records,
        change: authority::Change,
    ) -> io::Result<()> {
        let mut next = records.clone();
        next.apply(&change);
        let bytes = serde_json::to_vec(&next).map_err(io::Error::other)?;
        let path = self.authority.clone();
        tokio::task::spawn_blocking(move || {
            let temporary = path.with_extension("json.tmp");
            let file = std::fs::File::create(&temporary)?;
            std::io::Write::write_all(&mut &file, &bytes)?;
            sync_file(&file)?;
            drop(file);
            std::fs::rename(&temporary, &path)?;
            sync_directory(path.parent().unwrap_or(Path::new(".")))
        })
        .await
        .map_err(io::Error::other)??;
        *records = next;
        Ok(())
    }

    /// Answers `keeper`'s lease renewal, enrolling it first once leases are
    /// enforced.
    pub async fn renew(
        &self,
        keeper: uuid::Uuid,
        incarnation: uuid::Uuid,
        epoch: u64,
        lease: (u64, u64),
    ) -> io::Result<Reply> {
        self.require_trusted()?;
        let enforced = self.enforced();
        let mut records = self.records.lock().await;
        while enforced && let Some(change) = records.pending(keeper, incarnation, lease.0, lease.1)
        {
            self.change(&mut records, change).await?;
        }
        Ok(Reply::Lease(records.grant(
            keeper,
            incarnation,
            epoch,
            enforced,
            lease.0,
            lease.1,
        )))
    }

    /// Bumps `keeper`'s epoch.
    pub async fn fence(&self, keeper: uuid::Uuid) -> io::Result<Reply> {
        self.require_trusted()?;
        if !self.enforced() {
            return Ok(Reply::Decision(Outcome::Refused(JournalError::Unsupported)));
        }
        let mut records = self.records.lock().await;
        self.change(&mut records, authority::Change::Fence { keeper })
            .await?;
        Ok(Reply::Decision(Outcome::Unit))
    }

    /// An operator recovery's catalog transaction. The fence is stored
    /// before the stage, so a crash between them leaves the lost voters
    /// fenced and a rerun stages again.
    pub async fn recover(
        &self,
        stage: Stage,
        dead: Vec<uuid::Uuid>,
        record: authority::RecoveryRecord,
        writer: Option<uuid::Uuid>,
        placement: &Placement,
        wait_ms: u64,
    ) -> io::Result<Reply> {
        self.require_trusted()?;
        if !self.enforced() {
            return Ok(Reply::Decision(Outcome::Refused(JournalError::Unsupported)));
        }
        let lost = authority::fenced_by(&stage);
        let fenced = authority::fenced_from(&stage, writer);
        if !authority::describes(&record, &stage)
            || !stage.recovery()
            || !placement.stage(&stage)
            || dead.iter().any(|keeper| !lost.contains(keeper))
        {
            return Err(invalid("invalid recovery stage"));
        }
        let change = authority::recovery_change(stage.clone(), dead, record, writer)
            .ok_or_else(|| invalid("a recovery's writer must be one of its survivors"))?;
        let _guard = self.claim.lock().await;
        let entry = self
            .disk
            .catalog(stage.stream)
            .ok_or_else(|| invalid("missing catalog entry"))?;
        if !admits_stage(&entry, &stage) {
            return Ok(stage_conflict());
        }
        let mut records = self.records.lock().await;
        let written =
            !(records.recovered(&stage, &fenced) && entry.staged.as_ref() == Some(&stage));
        if written {
            self.change(&mut records, change).await?;
            if entry.staged.as_ref() != Some(&stage) {
                self.disk.write(Record::Stage(stage.clone())).await?;
            }
        }
        let wait_ms = records.recovery_wait(&fenced, wait_ms);
        Ok(Reply::Recovered(authority::Recovered {
            record: records
                .recoveries
                .get(&stage.stream)
                .copied()
                .unwrap_or(record),
            // Another survivor answered this recovery, so only the lost
            // voters need the operator's word when they never held a lease.
            unleased: records.unleased(&lost),
            fenced,
            wait_ms,
            written,
        }))
    }

    pub async fn claim(&self, genesis: Genesis, placement: &Placement) -> io::Result<Reply> {
        if !placement.genesis(&genesis) {
            return Ok(Reply::Decision(Outcome::Refused(JournalError::Conflict {
                head: Lsn(0),
            })));
        }
        // Five voters need every keeper to read their roster.
        if !super::decisions::creates_replication(
            genesis.voters.len(),
            self.disk.cluster_version(),
            super::CLUSTER_VERSION_REPLICATION,
        ) {
            return Ok(Reply::Decision(Outcome::Refused(JournalError::Unsupported)));
        }
        // A disconnected caller must not release the claim lock between enqueue
        // and sync, when a competing claim could still see an empty catalog.
        let catalog = Self {
            disk: self.disk.clone(),
            claim: self.claim.clone(),
            records: self.records.clone(),
            authority: self.authority.clone(),
        };
        tokio::spawn(async move { catalog.claim_validated(genesis).await })
            .await
            .map_err(io::Error::other)?
    }

    async fn claim_validated(&self, genesis: Genesis) -> io::Result<Reply> {
        let _guard = self.claim.lock().await;
        self.require_trusted()?;
        if let Some(existing) = self.disk.catalog(genesis.stream) {
            return if existing.genesis == genesis {
                let contacts = existing.ordered_contacts();
                Ok(Reply::Catalog(existing.genesis, contacts))
            } else {
                Ok(Reply::Decision(Outcome::Refused(JournalError::Conflict {
                    head: Lsn(0),
                })))
            };
        }
        let stream = genesis.stream;
        self.disk.write(Record::Claim(genesis)).await?;
        self.locate(stream)
    }

    pub fn locate(&self, stream: StreamId) -> io::Result<Reply> {
        self.require_trusted()?;
        Ok(match self.disk.catalog(stream) {
            Some(entry) => {
                let contacts = entry.ordered_contacts();
                Reply::Catalog(entry.genesis, contacts)
            }
            None => Reply::Decision(Outcome::Refused(JournalError::NotFound)),
        })
    }

    /// The latest move staged for `stream`, which certifies a keeper's copy.
    /// The streams whose genesis or latest staged move names `keeper`.
    pub fn named(&self, keeper: uuid::Uuid) -> io::Result<Reply> {
        self.require_trusted()?;
        Ok(Reply::Named(named(&self.disk.catalog_entries(), keeper)))
    }

    pub fn staged(&self, stream: StreamId) -> io::Result<Reply> {
        self.require_trusted()?;
        Ok(match self.disk.catalog(stream) {
            Some(entry) => entry
                .staged
                .map_or(Reply::Decision(Outcome::Unit), Reply::Staged),
            None => Reply::Decision(Outcome::Refused(JournalError::NotFound)),
        })
    }

    pub async fn stage(&self, stage: Stage, placement: &Placement) -> io::Result<Reply> {
        if !placement.stage(&stage) {
            return Err(invalid("invalid staged placement"));
        }
        let catalog = Self {
            disk: self.disk.clone(),
            claim: self.claim.clone(),
            records: self.records.clone(),
            authority: self.authority.clone(),
        };
        tokio::spawn(async move { catalog.stage_validated(stage).await })
            .await
            .map_err(io::Error::other)?
    }

    async fn stage_validated(&self, stage: Stage) -> io::Result<Reply> {
        // Hold the lock through durable publication even if its caller goes
        // away. A competing stage must compare against the committed move.
        let _guard = self.claim.lock().await;
        self.require_trusted()?;
        let entry = self
            .disk
            .catalog(stage.stream)
            .ok_or_else(|| invalid("missing catalog entry"))?;
        if !admits_stage(&entry, &stage) {
            return Ok(stage_conflict());
        }
        if entry.staged.as_ref() != Some(&stage) {
            self.disk.write(Record::Stage(stage.clone())).await?;
        }
        Ok(Reply::Staged(stage))
    }

    pub fn cluster_version(&self) -> io::Result<Reply> {
        self.require_trusted()?;
        Ok(Reply::ClusterVersion(self.disk.cluster_version()))
    }

    pub async fn finalize_version(&self, target: u32) -> io::Result<Reply> {
        let _guard = self.claim.lock().await;
        self.require_trusted()?;
        if target < super::CLUSTER_VERSION_V1 || target > super::CLUSTER_VERSION_CURRENT {
            return Ok(Reply::Decision(Outcome::Refused(JournalError::Unsupported)));
        }
        let current = self.disk.cluster_version();
        if target < current {
            return Ok(Reply::Decision(Outcome::Refused(JournalError::Conflict {
                head: Lsn(0),
            })));
        }
        if target > current {
            self.disk.write(Record::ClusterVersion(target)).await?;
            self.disk.set_write_version(target);
        }
        Ok(Reply::ClusterVersion(target))
    }

    fn require_trusted(&self) -> io::Result<()> {
        if !self.disk.healthy() {
            return Err(invalid("catalog media is unavailable"));
        }
        Ok(())
    }
}

/// A new recovery may only start from a roster whose predecessor the catalog
/// knows. A move at this revision could already be joint or finalized on a
/// quorum the survivor never contacted. Same-origin recovery retries are
/// permitted because the successful survivor reports its durable result
/// locally instead of attempting another stage.
pub(super) fn admits_stage(entry: &CatalogEntry, stage: &Stage) -> bool {
    let Some(current) = &entry.staged else {
        return !stage.recovery() || (stage.source == 0 && stage.old == entry.genesis.voters);
    };
    if current == stage {
        return true;
    }
    match stage.source.cmp(&current.source) {
        std::cmp::Ordering::Less => false,
        std::cmp::Ordering::Equal => {
            stage.old == current.old
                && stage.recovery() == current.recovery()
                && stage.survivors() == current.survivors()
        }
        std::cmp::Ordering::Greater => {
            !stage.recovery()
                || (current.source.checked_add(1) == Some(stage.source)
                    && current.target == stage.old)
        }
    }
}

pub(super) fn stage_conflict() -> Reply {
    Reply::Decision(Outcome::Refused(JournalError::Conflict { head: Lsn(0) }))
}

/// Asks the replicated catalog's voters in `order`, following leader hints,
/// until one gives an answer other than a hint or `Unavailable`. Rounds
/// repeat until `end`.
pub(super) async fn ask<F>(
    order: &[uuid::Uuid],
    end: Instant,
    mut call: impl FnMut(uuid::Uuid) -> F,
) -> Option<(uuid::Uuid, Reply)>
where
    F: Future<Output = io::Result<Reply>>,
{
    while Instant::now() < end {
        let mut visited = BTreeSet::new();
        let mut pending = order.to_vec();
        pending.reverse();
        while let Some(keeper) = pending.pop() {
            if Instant::now() >= end {
                return None;
            }
            if !visited.insert(keeper) {
                continue;
            }
            match call(keeper).await {
                Ok(Reply::Leader(Some(leader))) => pending.push(leader),
                Ok(Reply::Leader(None))
                | Ok(Reply::Decision(Outcome::Refused(JournalError::Unavailable)))
                | Err(_) => (),
                Ok(reply) => return Some((keeper, reply)),
            }
        }
        tokio::time::sleep(
            Duration::from_millis(50).min(end.saturating_duration_since(Instant::now())),
        )
        .await;
    }
    None
}

/// The streams among `entries` that may still name `keeper`: in their
/// genesis voters, or on either side of their latest staged move. Every
/// voter change is staged here before it happens, so a stream outside this
/// list never named the keeper after its genesis.
pub(super) fn named<'a>(
    entries: impl IntoIterator<Item = &'a super::storage::CatalogEntry>,
    keeper: uuid::Uuid,
) -> Vec<StreamId> {
    entries
        .into_iter()
        .filter(|entry| {
            entry.genesis.voters.contains(&keeper)
                || entry.staged.as_ref().is_some_and(|stage| {
                    stage.old.contains(&keeper) || stage.target.contains(&keeper)
                })
        })
        .map(|entry| entry.genesis.stream)
        .collect()
}
