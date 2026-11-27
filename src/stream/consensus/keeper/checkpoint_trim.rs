use journal_contract::{CheckpointAnchor, JournalError, Lsn};
use sha2::{Digest, Sha256};
use tokio::time::Instant;

use super::{Command, Fence, Group, Outcome, REQUEST_TIMEOUT, Reply, failure, offload::Offloader};

impl Group {
    pub(super) async fn trim_checkpoint(
        &self,
        fence: Fence,
        owner: String,
        anchor: CheckpointAnchor,
        offload: Option<&Offloader>,
    ) -> Reply {
        if !self.genesis.immutable {
            return failure(JournalError::Unsupported);
        }
        if let Err(reply) = self.barrier(Instant::now() + REQUEST_TIMEOUT).await {
            return reply;
        }
        let page = match self.read(anchor.announced_at, 1, 0, Lsn(0), offload).await {
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
        // Committed bytes in this history are immutable. The write still
        // rechecks the exact writer fence after the read or a leadership change.
        self.write(Command::Trim {
            fence,
            owner,
            through: anchor.covered_through,
        })
        .await
    }
}
