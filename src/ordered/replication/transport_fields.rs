//! Fixed fields of an LKORPC04 voter exchange.

use super::slot_header::{bytes_equal, read_be, read_field, write_be};

#[cfg(verus_keep_ghost)]
use super::slot_header::{decodeBE, encodeBE};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {

pub(super) open spec fn transportMagic() -> Seq<u8> {
    seq![76u8, 75, 79, 82, 80, 67, 48, 52]
}

pub(super) open spec fn transportGroupMatches(group: Seq<u8>, authorized: Seq<u8>, installed: Seq<u8>) -> bool {
    group == authorized && group == installed
}

pub(super) open spec fn responseKind(kind: u8, expected: u8) -> ResponseKind {
    if kind == expected { ResponseKind::Expected }
    else if kind == 5 { ResponseKind::Deposed }
    else if kind == 6 { ResponseKind::Rejected }
    else { ResponseKind::Invalid }
}

pub(super) open spec fn ballotBytes(round: u64, nonce: Seq<u8>) -> Seq<u8> {
    encodeBE(round) + nonce
}

pub(super) open spec fn ballotValid(bytes: Seq<u8>) -> bool {
    bytes.len() == 24
        && decodeBE(bytes.take(8)) != 0
        && exists|i: int| 8 <= i < 24 && bytes[i] != 0
}

pub(super) open spec fn voteSlotsMatch(bytes: Seq<u8>, slots: VoteSlots) -> bool {
    bytes.len() == 81
        && slots.selected == bytes[0]
        && slots.images@[0].generation == decodeBE(bytes.subrange(1, 9))
        && slots.images@[0].digest@ == bytes.subrange(9, 41)
        && slots.images@[1].generation == decodeBE(bytes.subrange(41, 49))
        && slots.images@[1].digest@ == bytes.subrange(49, 81)
}

}

pub(super) const TRANSPORT_MAGIC: [u8; 8] = [b'L', b'K', b'O', b'R', b'P', b'C', b'0', b'4'];
pub(super) const PREPARE: u8 = 1;
pub(super) const ACCEPT: u8 = 2;
pub(super) const PROMISE: u8 = 3;
pub(super) const VOTE: u8 = 4;
pub(super) const DEPOSED: u8 = 5;
pub(super) const REJECTED: u8 = 6;

pub(super) struct BallotFields {
    pub(super) round: u64,
    pub(super) nonce: [u8; 16],
}

pub(super) struct ImageFields {
    pub(super) generation: u64,
    pub(super) digest: [u8; 32],
}

pub(super) struct VoteSlots {
    pub(super) selected: u8,
    pub(super) images: [ImageFields; 2],
}

pub(super) enum ResponseKind {
    Expected,
    Deposed,
    Rejected,
    Invalid,
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (magic@ == transportMagic()),))]
pub(super) fn transport_magic_matches(magic: &[u8; 8]) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! { assert(TRANSPORT_MAGIC@ =~= transportMagic()); }
    bytes_equal(magic, &TRANSPORT_MAGIC)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == transportGroupMatches(group@, authorized@, installed@),))]
pub(super) fn transport_group_matches(
    group: &[u8; 32],
    authorized: &[u8; 32],
    installed: &[u8; 32],
) -> bool {
    bytes_equal(group, authorized) && bytes_equal(group, installed)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (voter@ == expected@),))]
pub(super) fn transport_voter_matches(voter: &[u8; 16], expected: &[u8; 16]) -> bool {
    bytes_equal(voter, expected)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == responseKind(kind, expected),))]
pub(super) fn response_kind(kind: u8, expected: u8) -> ResponseKind {
    match kind {
        kind if kind == expected => ResponseKind::Expected,
        DEPOSED => ResponseKind::Deposed,
        REJECTED => ResponseKind::Rejected,
        _ => ResponseKind::Invalid,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out@ =~= ballotBytes(round, nonce@),))]
pub(super) fn encode_ballot(round: u64, nonce: &[u8; 16]) -> [u8; 24] {
    let mut bytes = [0; 24];
    bytes[..8].copy_from_slice(&write_be(round));
    bytes[8..].copy_from_slice(nonce);
    bytes
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out.is_some() == ballotValid(bytes@),
        out matches Some(ballot) ==> ballot.round == decodeBE(bytes@.take(8))
            && ballot.nonce@ == bytes@.subrange(8, 24),
))]
pub(super) fn decode_ballot(bytes: &[u8]) -> Option<BallotFields> {
    if bytes.len() != 24 {
        return None;
    }
    let round = read_be(read_field(bytes, 0));
    let nonce = read_field(bytes, 8);
    let nil = [0; 16];
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bytes@.take(8) =~= bytes@.subrange(0, 8));
        assert(nonce@ == nil@ <==> !(exists|i: int| 8 <= i < 24 && bytes@[i] != 0)) by {
            if nonce@ != nil@ {
                assert(exists|i: int| 0 <= i < 16 && nonce@[i] != nil@[i]) by {
                    if !(exists|i: int| 0 <= i < 16 && nonce@[i] != nil@[i]) {
                        assert forall|i: int| 0 <= i < 16 implies nonce@[i] == nil@[i] by {}
                        assert(nonce@ =~= nil@);
                    }
                }
                let i = choose|i: int| 0 <= i < 16 && nonce@[i] != nil@[i];
                assert(bytes@[i + 8] != 0);
            } else {
                assert forall|i: int| 8 <= i < 24 implies bytes@[i] == 0 by {
                    assert(nonce@[i - 8] == nil@[i - 8]);
                }
            }
        }
    }
    if round == 0 || bytes_equal(&nonce, &nil) {
        return None;
    }
    Some(BallotFields { round, nonce })
}

#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == (tag == if requested { 1u8 } else { 0u8 }),))]
pub(super) fn vote_read_back_matches(tag: u8, requested: bool) -> bool {
    tag == requested as u8
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        out.is_some() == (bytes@.len() == 81),
        out matches Some(slots) ==> voteSlotsMatch(bytes@, slots),
))]
pub(super) fn decode_vote_slots(bytes: &[u8]) -> Option<VoteSlots> {
    if bytes.len() != 81 {
        return None;
    }
    Some(VoteSlots {
        selected: bytes[0],
        images: [
            ImageFields {
                generation: read_be(read_field(bytes, 1)),
                digest: read_field(bytes, 9),
            },
            ImageFields {
                generation: read_be(read_field(bytes, 41)),
                digest: read_field(bytes, 49),
            },
        ],
    })
}
