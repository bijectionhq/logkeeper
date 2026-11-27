use journal_contract::{CheckpointAnchor, CheckpointInstallation, CheckpointReceipt};
use sha2::{Digest, Sha256};

use super::*;

/// The exact receipt required to reopen or retry the selected recovery base.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub(in crate::stream::consensus) struct Selection {
    receipt: CheckpointReceipt,
    operation_id: Option<u128>,
    record_sha256: [u8; 32],
}

impl Selection {
    fn new(
        checkpoint_lsn: Lsn,
        covered_through_lsn: Lsn,
        operation_id: Option<u128>,
        record_sha256: [u8; 32],
    ) -> Self {
        Self {
            receipt: CheckpointReceipt {
                checkpoint_lsn,
                covered_through_lsn,
                logical_floor_lsn: Lsn(covered_through_lsn.0 + 1),
            },
            operation_id,
            record_sha256,
        }
    }

    pub(super) fn valid(self, live: &Live) -> bool {
        self.operation_id != Some(0)
            && self.receipt.covered_through_lsn < self.receipt.checkpoint_lsn
            && self.receipt.checkpoint_lsn <= live.head
            && self.receipt.covered_through_lsn.0.checked_add(1)
                == Some(self.receipt.logical_floor_lsn.0)
            && self.receipt.logical_floor_lsn == live.logical_floor()
    }

    fn same_announcement(self, other: Self) -> bool {
        self.receipt == other.receipt && self.record_sha256 == other.record_sha256
    }

    fn outcome(self) -> Outcome {
        Outcome::Checkpoint(Some(self.receipt))
    }
}

impl State {
    pub(in crate::stream::consensus) fn selected_checkpoint(
        &self,
    ) -> Result<Option<CheckpointReceipt>> {
        self.immutable_live()?;
        Ok(self.selection().map(|selected| selected.receipt))
    }

    pub(super) fn selection(&self) -> Option<Selection> {
        match self {
            Self::Checkpointed { selected, .. } => Some(*selected),
            _ => None,
        }
    }

    fn immutable_live(&self) -> Result<&Live> {
        match self {
            Self::Immutable { live, .. } | Self::Checkpointed { live, .. } => Ok(live),
            Self::Live(_) => Err(JournalError::Unsupported),
            Self::Absent => Err(JournalError::NotFound),
            Self::Deleted => Err(JournalError::Deleted),
        }
    }

    fn record_selection(&mut self, selection: Selection) -> Outcome {
        match self {
            Self::Checkpointed { selected, .. } => *selected = selection,
            Self::Immutable { .. } => {
                let Self::Immutable {
                    live,
                    sealed_head_lsn,
                } = std::mem::take(self)
                else {
                    unreachable!();
                };
                *self = Self::Checkpointed {
                    live,
                    sealed_head_lsn,
                    selected: selection,
                };
            }
            _ => unreachable!("checkpoint selection needs a live immutable history"),
        }
        selection.outcome()
    }

    pub(super) fn install_checkpoint(
        &mut self,
        fence: Fence,
        owner: &str,
        checkpoint: CheckpointInstallation,
        segment: Arc<super::super::storage::Object>,
        genesis: &Genesis,
    ) -> io::Result<Outcome> {
        let CheckpointInstallation {
            operation_id,
            checkpoint_lsn,
            covered_through_lsn,
            record,
        } = checkpoint;
        let live = match self.immutable_live() {
            Ok(live) => live,
            Err(error) => return Ok(Outcome::Refused(error)),
        };
        if let Err(error) = live.require_writer(fence, owner) {
            return Ok(Outcome::Refused(error));
        }
        let conflict = || Outcome::Refused(JournalError::Conflict { head: live.head });
        if operation_id == 0 || covered_through_lsn >= checkpoint_lsn {
            return Ok(conflict());
        }
        if record.len() > MAX_RECORD {
            return Ok(Outcome::Refused(JournalError::TooLarge { max: MAX_RECORD }));
        }
        let selection = Selection::new(
            checkpoint_lsn,
            covered_through_lsn,
            Some(operation_id),
            Sha256::digest(&record).into(),
        );
        if let Some(selected) = self.selection()
            && selected.operation_id == Some(operation_id)
        {
            return Ok(if selected.same_announcement(selection) {
                selected.outcome()
            } else {
                conflict()
            });
        }
        if checkpoint_lsn.0 == u64::MAX
            || live.head.0.checked_add(1) != Some(checkpoint_lsn.0)
            || selection.receipt.logical_floor_lsn < live.logical_floor()
        {
            return Ok(conflict());
        }

        // Charge the retained suffix and its announcement together. This
        // operation can free a full stream, and every refusal leaves it intact.
        let reclaimed_count = selection
            .receipt
            .logical_floor_lsn
            .0
            .saturating_sub(live.floor.0) as usize;
        let reclaimed_bytes = live
            .records
            .iter()
            .take(reclaimed_count)
            .map(|record| record_charge(record.len()))
            .sum::<u64>();
        let used = (live.bytes - reclaimed_bytes)
            .checked_add(record_charge(record.len()))
            .filter(|used| *used <= genesis.quota_bytes);
        let Some(used) =
            used.filter(|_| live.records.len() - reclaimed_count < MAX_RETAINED_RECORDS)
        else {
            return Ok(Outcome::Refused(JournalError::Full {
                floor: live.logical_floor(),
            }));
        };
        let len = record.len() as u32;
        let offset = segment.len().checked_sub(u64::from(len)).ok_or_else(|| {
            super::super::invalid("accepted WAL extent does not contain the checkpoint")
        })?;
        let live = self.live_mut().expect("checked immutable live state");
        live.trim(covered_through_lsn)
            .expect("validated checkpoint cut");
        live.record_append(
            checkpoint_lsn,
            Payload::Extent {
                object: segment,
                offset,
                len,
                crc: crc32fast::hash(&record),
                timed: false,
            },
            used,
        );
        Ok(self.record_selection(selection))
    }

    pub(super) fn select_announcement(
        &mut self,
        fence: Fence,
        owner: &str,
        anchor: CheckpointAnchor,
    ) -> Result<Outcome> {
        let live = self.immutable_live()?;
        live.require_writer(fence, owner)?;
        let conflict = JournalError::Conflict { head: live.head };
        if anchor.covered_through >= anchor.announced_at || anchor.announced_at > live.head {
            return Err(conflict);
        }
        let selection = Selection::new(
            anchor.announced_at,
            anchor.covered_through,
            None,
            anchor.record_sha256,
        );
        if let Some(selected) = self.selection() {
            if selected.same_announcement(selection) {
                return Ok(selected.outcome());
            }
            if anchor.announced_at <= selected.receipt.checkpoint_lsn {
                return Err(conflict);
            }
        }
        if selection.receipt.logical_floor_lsn < live.logical_floor() {
            return Err(conflict);
        }
        self.live_mut()?.trim(anchor.covered_through)?;
        Ok(self.record_selection(selection))
    }
}
