//! Encoding shared by rotation replies and the signed evidence transcript.

use super::{BufMut, BytesMut, RotationSlots, checkpoint, uuid};

impl RotationSlots {
    pub(super) fn encode(&self, output: &mut BytesMut) {
        output.put_slice(&self.group);
        output.put_u64(self.cohort_size as u64);
        output.put_u64(self.ballot.round);
        uuid(output, self.ballot.nonce);
        output.put_slice(&self.prefix);
        output.put_u64(self.position);
        checkpoint(output, self.checkpoint);
        output.put_u64(self.key_generation);
        output.put_u64(self.voters.len() as u64);
        let mut index = 0;
        while index < self.voters.len() {
            let voter = &self.voters[index];
            uuid(output, voter.voter);
            output.put_u8(voter.slots.selected);
            let [first, second] = voter.slots.images;
            output.put_u64(first.generation);
            output.put_slice(&first.digest);
            output.put_u64(second.generation);
            output.put_slice(&second.digest);
            index += 1;
        }
    }
}
