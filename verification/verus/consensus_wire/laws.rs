use crate::production::*;
use vstd::prelude::*;

verus! {

fn an_n_only_value_cannot_pass_the_n_minus_one_gate(introduced: WireVersion)
    requires introduced is Current,
{
    let send = introduced.supported_on(WireVersion::Previous);
    assert(!send);
}

fn every_classified_value_can_travel_on_the_current_connection(introduced: WireVersion) {
    let send = introduced.supported_on(WireVersion::Current);
    assert(send);
}

fn a_new_nested_outcome_is_replaced_by_the_legacy_fallback<T>(value: T, fallback: T) {
    let sent = legacy_payload(WireVersion::Current, value, fallback);
    assert(sent == fallback);
}

fn a_previous_nested_outcome_is_preserved<T>(value: T, fallback: T) {
    let sent = legacy_payload(WireVersion::Previous, value, fallback);
    assert(sent == value);
}

// No frame introduced in N is ever encoded on an N-1 connection, whatever it
// carries. The ping is the one frame N-1 receives in another form, and that
// form, liveness, is one N-1 knows.
fn an_n_only_frame_never_travels_on_n_minus_one(ping: bool, legacy: bool) {
    let send = frame_send(WireVersion::Previous, WireVersion::Current, ping, legacy);
    assert(!(send is Encode));
    assert(send is Liveness <==> ping);
}

// A five-voter roster never reaches an N-1 peer, which reads only three.
fn a_five_voter_roster_never_travels_on_n_minus_one(introduced: WireVersion, ping: bool) {
    let send = frame_send(WireVersion::Previous, introduced, ping, false);
    assert(!(send is Encode));
    let reply = legacy_sends(introduced, false);
    assert(!reply);
}

// N-1 loses nothing it can read: a frame it knows with rosters it reads is
// sent unchanged, and every frame goes unchanged on an N connection.
fn n_minus_one_receives_every_frame_it_reads(ping: bool, legacy: bool, introduced: WireVersion) {
    let previous = frame_send(WireVersion::Previous, WireVersion::Previous, false, true);
    assert(previous is Encode);
    let current = frame_send(WireVersion::Current, introduced, ping, legacy);
    assert(current is Encode);
}

// A reply reaches N-1 unchanged only when N-1 knows it and reads its rosters.
fn an_n_only_reply_never_travels_on_n_minus_one(legacy: bool) {
    let sent = legacy_sends(WireVersion::Current, legacy);
    assert(!sent);
    let kept = legacy_sends(WireVersion::Previous, true);
    assert(kept);
}

}
