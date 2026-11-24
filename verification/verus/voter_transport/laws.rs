use crate::production::*;
use crate::slot_header::{big_endian_round_trips, decodeBE, encodeBE};
use vstd::prelude::*;

verus! {

fn transport_ballot_round_trips(round: u64, nonce: &[u8; 16])
    requires round != 0, exists|i: int| 0 <= i < 16 && nonce@[i] != 0,
{
    let encoded = encode_ballot(round, nonce);
    proof {
        big_endian_round_trips(round);
        assert(encoded@.take(8) =~= encodeBE(round));
        assert(encoded@.subrange(8, 24) =~= nonce@);
        let i = choose|i: int| 0 <= i < 16 && nonce@[i] != 0;
        assert(encoded@[i + 8] != 0);
    }
    let decoded = decode_ballot(&encoded);
    assert(decoded matches Some(ballot) && ballot.round == round && ballot.nonce@ == nonce@);
}

fn vote_reads_the_two_physical_slots_in_order(bytes: &[u8]) {
    let decoded = decode_vote_slots(bytes);
    if let Some(slots) = decoded {
        assert(slots.selected == bytes@[0]);
        assert(slots.images@[0].generation == decodeBE(bytes@.subrange(1, 9)));
        assert(slots.images@[0].digest@ == bytes@.subrange(9, 41));
        assert(slots.images@[1].generation == decodeBE(bytes@.subrange(41, 49)));
        assert(slots.images@[1].digest@ == bytes@.subrange(49, 81));
    } else {
        assert(bytes@.len() != 81);
    }
}

fn scope_requires_both_groups(group: &[u8; 32], authorized: &[u8; 32], installed: &[u8; 32]) {
    let accepted = transport_group_matches(group, authorized, installed);
    assert(accepted ==> group@ == authorized@ && group@ == installed@);
}

fn a_reply_cannot_change_witness_mode(tag: u8, requested: bool) {
    let accepted = vote_read_back_matches(tag, requested);
    assert(accepted ==> (requested && tag == 1) || (!requested && tag == 0));
}

}
