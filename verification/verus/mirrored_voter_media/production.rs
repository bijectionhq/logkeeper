use vstd::prelude::*;

#[path = "../../../src/ordered/admission.rs"]
mod admission;
use admission::matches_fingerprint;
#[path = "../../../src/ordered/codec/frame.rs"]
mod frame;
#[path = "../../../src/ordered/replication/disk/selection.rs"]
pub mod selection;
#[path = "../../../src/ordered/replication/disk/mirror.rs"]
mod mirror;
#[path = "../../../src/ordered/replication/disk/recover.rs"]
pub mod recover;
#[path = "../../../src/ordered/replication/slot_header.rs"]
mod slot_header;
use slot_header::{decode_header, decodeBE, matches_slot, voterSlotMagic, HEADER};

pub type Fingerprint = [u8; 32];
#[derive(Clone, Copy)]
pub struct Ballot {
    pub round: u64,
    pub nonce: u128,
}

#[derive(Clone, Copy)]
pub struct Uuid(pub [u8; 16]);

impl Uuid {
    #[verus_spec(out => ensures out == self.0)]
    pub fn as_bytes(&self) -> &[u8; 16] { &self.0 }
}

pub struct Group { pub identity: Fingerprint }

pub struct Selected {
    pub index: usize,
    pub generation: u64,
    pub state: VoterState,
}

pub struct File {
    pub header: Option<[u8; HEADER]>,
    pub body: Ghost<Seq<u8>>,
}


pub enum Error {
    Diverged,
    Stopped,
    Group,
}

#[derive(Copy, Clone)]
pub struct SlotImage {
    pub generation: u64,
    pub digest: [u8; 32],
}

#[derive(Clone, Copy)]
pub struct SlotPair {
    pub selected: u8,
    pub images: [SlotImage; 2],
}

#[derive(Copy, Clone)]
pub struct VoterState {
    pub promised: Option<Ballot>,
    pub accepted: Option<(Ballot, u64)>,
}

pub struct Media {
    pub selected: Option<usize>,
    pub a: Option<(VoterState, SlotImage)>,
    pub b: Option<(VoterState, SlotImage)>,
    pub writes: Ghost<Seq<usize>>,
    pub reads: Ghost<Seq<(usize, Ballot, Fingerprint, SlotImage)>>,
}

pub struct Inner { pub group: Group }

verus! {

impl File {
    pub open spec fn snapshot(&self) -> (Option<[u8; HEADER]>, Seq<u8>) {
        (self.header, self.body@)
    }
}

pub uninterp spec fn slot_digest(descriptor: Seq<u8>, body: Seq<u8>) -> Seq<u8>;
pub uninterp spec fn decoded_state(group: &Group, body: Seq<u8>) -> Option<VoterState>;

#[verifier::external_body]
pub fn read_slot_header(file: &mut File) -> (out: Result<[u8; HEADER], Error>)
    ensures old(file).snapshot() == final(file).snapshot(),
        out matches Ok(header) ==> old(file).header == Some(header),
{ unimplemented!() }

#[verifier::external_body]
pub fn read_slot_body(file: &mut File, header: &[u8; HEADER], length: usize)
    -> (out: Result<(Vec<u8>, Fingerprint), Error>)
    ensures old(file).snapshot() == final(file).snapshot(),
        out matches Ok((body, digest)) ==> length <= old(file).body@.len()
            && body@ == old(file).body@.take(length as int) && digest@ == slot_digest(header@.take(72), body@),
{ unimplemented!() }

#[verifier::external_body]
pub fn load_state(group: &Group, body: Vec<u8>) -> (out: Result<VoterState, Error>)
    ensures out matches Ok(state) ==> decoded_state(group, body@) == Some(state),
{ unimplemented!() }

pub(crate) open spec fn eligible_slot(
    file: &File, group: &Group, voter: Uuid, size: usize, index: usize,
    used: usize, selected: Selected, digest: Fingerprint,
) -> bool {
    file.header matches Some(header)
    && header@.subrange(0, 8) == voterSlotMagic()
    && header@.subrange(8, 40) == group.identity@
    && header@.subrange(40, 56) == voter.0@
    && decodeBE(header@.subrange(56, 64)) != 0
    && 2 <= used as int <= size as int - HEADER as int
    && used == decodeBE(header@.subrange(64, 72)) && used <= file.body@.len()
    && digest@ == header@.subrange(72, 104)
    && digest@ == slot_digest(header@.take(72), file.body@.take(used as int))
    && selected.index == index && selected.generation == decodeBE(header@.subrange(56, 64))
    && decoded_state(group, file.body@.take(used as int)) == Some(selected.state)
}

#[verifier::external_body]
pub(crate) fn slot_size(group: &Group) -> (out: Result<usize, Error>)
    ensures out matches Ok(size) ==> size >= HEADER,
{ unimplemented!() }

pub open spec fn reads_both_images(
    before: Media, after: Media, ballot: Ballot, digest: Fingerprint, pair: SlotPair,
) -> bool {
    after.reads@ == before.reads@.push((0usize, ballot, digest, pair.images@[0]))
        .push((1usize, ballot, digest, pair.images@[1]))
}

impl Inner {
    // A successful event denotes a read, recovery validation and an exact
    // comparison of the physical slot, promise and accepted ballot/prefix.
    #[verifier::external_body]
    pub(crate) fn read_back_slot(
        &self, media: &mut Media, index: usize, size: usize,
        ballot: Ballot, digest: Fingerprint, expected: SlotImage,
    ) -> (out: Result<(), Error>)
        requires size >= HEADER, index < 2,
        ensures out.is_ok() ==> final(media).reads@ == old(media).reads@.push((index, ballot, digest, expected)),
    { unimplemented!() }
}

pub open spec fn slot(media: Media, index: int) -> Option<(VoterState, SlotImage)> {
    if index == 0 { media.a } else { media.b }
}

pub open spec fn slot_selection(a: Option<u64>, b: Option<u64>) -> Result<Option<usize>, Error> {
    match (a, b) {
        (None, None) => Ok(None),
        (Some(_), None) => Ok(Some(0)),
        (None, Some(_)) => Ok(Some(1)),
        (Some(a), Some(b)) => if a == b { Err(Error::Diverged) }
            else if a < b { Ok(Some(1)) } else { Ok(Some(0)) },
    }
}

// Successful fsync/install writes the alternate and advances the in-memory
// selector. Failure does not authorize a reply.
impl Inner {
    #[verifier::external_body]
    pub fn install(&self, media: &mut Media, next: VoterState) -> (out: Result<(usize, SlotImage), Error>)
        requires old(media).selected matches Some(i) && i < 2,
        ensures out matches Ok((index, descriptor)) ==>
            index == 1 - old(media).selected.unwrap()
            && final(media).selected == Some(index)
            && slot(*final(media), index as int) == Some((next, descriptor))
            && slot(*final(media), 1 - index as int) == slot(*old(media), 1 - index as int)
            && final(media).writes@ == old(media).writes@.push(index),
    { unimplemented!() }
}

pub open spec fn mirrored(media: Media, next: VoterState, pair: SlotPair) -> bool {
    pair.selected < 2
    && media.selected == Some(pair.selected as usize)
    && media.a == Some((next, pair.images@[0]))
    && media.b == Some((next, pair.images@[1]))
}

pub open spec fn reply_requires_both_syncs(before: Media, after: Media) -> bool {
    let selected = before.selected.unwrap();
    after.selected == Some(selected)
    && after.writes@ == before.writes@.push((1 - selected) as usize).push(selected)
}

}
