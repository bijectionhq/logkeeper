use super::{Ballot, Error, Fingerprint, Inner, Media, SlotPair, VoterState, slot_size};

impl Inner {
    pub(super) fn mirror(&self, media: &mut Media, next: VoterState) -> Result<SlotPair, Error> {
        // A torn slot must never roll back an acknowledged vote or the
        // promise that prevented an older proposer from completing.
        let (_, alternate) = self.install(media, next.clone())?;
        let (selected, image) = self.install(media, next)?;
        let images = if selected == 0 {
            [image, alternate]
        } else {
            [alternate, image]
        };
        Ok(SlotPair {
            selected: selected as u8,
            images,
        })
    }

    pub(super) fn read_back(
        &self,
        media: &mut Media,
        ballot: Ballot,
        digest: Fingerprint,
        slots: SlotPair,
    ) -> Result<(), Error> {
        let size = slot_size(&self.group)?;
        self.read_back_slot(media, 0, size, ballot, digest, slots.images[0])?;
        self.read_back_slot(media, 1, size, ballot, digest, slots.images[1])
    }
}
