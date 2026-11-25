//! The catalog assigns one immutable genesis. Later contacts help discovery
//! while the stream's own membership log decides voting authority.

use std::{io, sync::Arc};

use journal_contract::{JournalError, Lsn, StreamId};
use tokio::sync::Mutex;

use super::{
    Genesis, Stage, invalid,
    network::Reply,
    placement::Placement,
    state::Outcome,
    storage::{Disk, Record},
};

pub(super) struct Catalog {
    disk: Disk,
    claim: Arc<Mutex<()>>,
}

impl Catalog {
    pub fn new(disk: Disk) -> Self {
        Self {
            disk,
            claim: Arc::default(),
        }
    }

    pub async fn claim(&self, genesis: Genesis, placement: &Placement) -> io::Result<Reply> {
        if !placement.genesis(&genesis) {
            return Ok(Reply::Decision(Outcome::Refused(JournalError::Conflict {
                head: Lsn(0),
            })));
        }
        // A disconnected caller must not release the claim lock between enqueue
        // and sync, when a competing claim could still see an empty catalog.
        let catalog = Self {
            disk: self.disk.clone(),
            claim: self.claim.clone(),
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

    pub async fn stage(&self, stage: Stage, placement: &Placement) -> io::Result<Reply> {
        self.require_trusted()?;
        if !placement.stage(&stage) {
            return Err(invalid("invalid staged placement"));
        }
        let entry = self
            .disk
            .catalog(stage.stream)
            .ok_or_else(|| invalid("missing catalog entry"))?;
        if entry.staged.as_ref() != Some(&stage) {
            self.disk.write(Record::Stage(stage.clone())).await?;
        }
        Ok(Reply::Staged(stage))
    }

    fn require_trusted(&self) -> io::Result<()> {
        if !self.disk.healthy() {
            return Err(invalid("catalog media is unavailable"));
        }
        Ok(())
    }
}
