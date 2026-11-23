use super::{Ballot, Error, Fingerprint, Inner, Media, SlotPair, VoterState, slot_size};

#[cfg(verus_keep_ghost)]
use super::{mirrored, reads_both_images, reply_requires_both_syncs};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

impl Inner {
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires old(media).selected matches Some(i) && i < 2,
        ensures out matches Ok(pair) ==> mirrored(*final(media), next, pair)
            && reply_requires_both_syncs(*old(media), *final(media)),
    ))]
    pub(crate) fn mirror(&self, media: &mut Media, next: VoterState) -> Result<SlotPair, Error> {
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

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out.is_ok() ==> reads_both_images(*old(media), *final(media), ballot, digest, slots),
    ))]
    pub(crate) fn read_back(
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
