//! Releases exact slot evidence for a fresh or retained rotation receipt.

use super::{Chosen, Command, Request, RotationSlots};

impl Chosen {
    /// A retained rotation can be attested again while the recovered head
    /// still serves from its exact clean checkpoint and generation.
    pub(in crate::ordered) fn rotation_slots(&self, request: &Request) -> Option<RotationSlots> {
        let Command::PublishAndRotate { grant, checkpoint } = request.command else {
            return None;
        };
        if request.placement != self.receipt.placement
            || request.principal != self.receipt.principal
            || request.id != self.receipt.request
            || grant.key_generation.checked_add(1) != Some(self.state.authority.key_generation)
            || checkpoint != self.state.checkpoint()
            || !self.rotation_suffix_matches(checkpoint.cut.next_lsn)
        {
            return None;
        }
        let evidence = RotationSlots {
            group: self.group,
            cohort_size: self.cohort_size,
            ballot: self.ballot,
            prefix: self.prefix,
            position: self.state.position(),
            checkpoint,
            key_generation: self.state.authority.key_generation,
            voters: self.images.clone(),
        };
        if evidence.covers(self.receipt) {
            Some(evidence)
        } else {
            None
        }
    }

    fn rotation_suffix_matches(&self, next_lsn: u64) -> bool {
        let mut index = 0;
        while index < self.state.records.len() {
            let record = &self.state.records[index];
            if record.result.lsn >= next_lsn
                && record.grant.key_generation != self.state.authority.key_generation
            {
                return false;
            }
            index += 1;
        }
        true
    }
}
