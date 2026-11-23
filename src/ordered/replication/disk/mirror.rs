use super::{Error, Inner, Media, SlotPair, VoterState};

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
}
