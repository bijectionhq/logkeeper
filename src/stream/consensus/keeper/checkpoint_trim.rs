use journal_contract::{
    CheckpointAnchor, CheckpointCustody, CheckpointInstallation, JournalError, Lsn,
};
use sha2::{Digest, Sha256};
use tokio::time::Instant;

use super::{Command, Engine, Fence, Group, Outcome, REQUEST_TIMEOUT, Reply, Request, failure};
use crate::stream::consensus::{
    CLUSTER_VERSION_CHECKPOINT_CUSTODY, CLUSTER_VERSION_CHECKPOINT_INSTALL, MAX_RECORD,
};

impl Engine {
    async fn checkpoint_install_enabled(&self) -> journal_contract::Result<bool> {
        self.checkpoint_feature_finalized(CLUSTER_VERSION_CHECKPOINT_INSTALL)
            .await
    }

    async fn checkpoint_feature_finalized(&self, feature: u32) -> journal_contract::Result<bool> {
        if self.disk.write_version_allows(feature) {
            return Ok(true);
        }
        // A lagging keeper must read the authoritative version before it
        // admits an old operation. Once learned, the local gate is monotonic.
        match self.catalog_request(Request::ClusterVersion).await {
            Ok(Reply::ClusterVersion(version)) => {
                self.disk.set_write_version(version);
                Ok(self.disk.write_version_allows(feature))
            }
            _ => Err(JournalError::Unavailable),
        }
    }

    pub(super) async fn checkpoint_custody(
        &self,
        group: &Group,
        change: Option<CheckpointCustody>,
    ) -> Reply {
        match self
            .checkpoint_feature_finalized(CLUSTER_VERSION_CHECKPOINT_CUSTODY)
            .await
        {
            Ok(true) if group.genesis.immutable => (),
            Ok(_) => return failure(JournalError::Unsupported),
            Err(error) => return failure(error),
        }
        if let Some(change) = change {
            return group.write(Command::CheckpointCustody(change)).await;
        }
        if let Err(reply) = group.barrier(Instant::now() + REQUEST_TIMEOUT).await {
            return reply;
        }
        Reply::Decision(
            group
                .state
                .checkpoint_custody()
                .map(Outcome::CheckpointCustody)
                .into(),
        )
    }

    pub(super) async fn compatibility_trim(
        &self,
        group: &Group,
        fence: Fence,
        owner: String,
        through: Lsn,
    ) -> Reply {
        if group.genesis.immutable {
            match self.checkpoint_install_enabled().await {
                Ok(false) => (),
                Ok(true) => return failure(JournalError::Unsupported),
                Err(error) => return failure(error),
            }
        }
        group
            .write(Command::Trim {
                fence,
                owner,
                through,
            })
            .await
    }

    pub(super) async fn install_checkpoint(
        &self,
        group: &Group,
        fence: Fence,
        owner: String,
        checkpoint: CheckpointInstallation,
    ) -> Reply {
        if !group.genesis.immutable {
            return failure(JournalError::Unsupported);
        }
        if checkpoint.record.len() > MAX_RECORD {
            return failure(JournalError::TooLarge { max: MAX_RECORD });
        }
        match self.checkpoint_install_enabled().await {
            Ok(true) => {
                self.write_with_durability(
                    group,
                    Command::InstallCheckpoint {
                        fence,
                        owner,
                        checkpoint,
                    },
                )
                .await
            }
            Ok(false) => failure(JournalError::Unsupported),
            Err(error) => failure(error),
        }
    }

    pub(super) async fn select_checkpoint(
        &self,
        group: &Group,
        fence: Fence,
        owner: String,
        anchor: CheckpointAnchor,
    ) -> Reply {
        if !group.genesis.immutable {
            return failure(JournalError::Unsupported);
        }
        if let Err(reply) = group.barrier(Instant::now() + REQUEST_TIMEOUT).await {
            return reply;
        }
        let page = match group
            .read(anchor.announced_at, 1, 0, Lsn(0), self.offload.as_deref())
            .await
        {
            Outcome::Page(page) => page,
            Outcome::Refused(error) => return failure(error),
            _ => return failure(JournalError::Unavailable),
        };
        let [(announced_at, record)] = page.records.as_slice() else {
            return failure(JournalError::Conflict { head: page.head });
        };
        if *announced_at != anchor.announced_at
            || anchor.covered_through >= anchor.announced_at
            || <[u8; 32]>::from(Sha256::digest(record)) != anchor.record_sha256
        {
            return failure(JournalError::Conflict { head: page.head });
        }
        // The order rechecks the fence and retained cut after the read.
        let command = match self.checkpoint_install_enabled().await {
            Ok(true) => Command::SelectCheckpoint {
                fence,
                owner,
                anchor,
            },
            Ok(false) => Command::Trim {
                fence,
                owner,
                through: anchor.covered_through,
            },
            Err(error) => return failure(error),
        };
        match group.write(command).await {
            Reply::Decision(Outcome::Checkpoint(Some(_))) => Reply::Decision(Outcome::Unit),
            reply => reply,
        }
    }
}

impl Group {
    pub(super) async fn selected_checkpoint(&self) -> Reply {
        if let Err(reply) = self.barrier(Instant::now() + REQUEST_TIMEOUT).await {
            return reply;
        }
        Reply::Decision(
            self.state
                .selected_checkpoint()
                .map(Outcome::Checkpoint)
                .into(),
        )
    }
}
