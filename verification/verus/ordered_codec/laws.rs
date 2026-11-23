use crate::production::{
    bodyLengthBounded, commandVersion, decision_header, decode_flag, encode_flag,
    has_command_version, read_decision_time, bounded_body_length,
};
use vstd::prelude::*;

verus! {

fn decision_time_round_trips(time: [u8; 8]) {
    let header = decision_header(time);
    let decoded = read_decision_time(&header);
    assert(decoded matches Some(copy) && copy@ == time@);
}

fn short_decision_header_is_rejected(frame: &[u8])
    requires frame@.len() < 9,
{
    let decoded = read_decision_time(frame);
    assert(decoded is None);
}

fn wrong_command_version_is_rejected(version: u8)
    requires version != commandVersion(),
{
    let admitted = has_command_version(version);
    assert(!admitted);
}

fn flag_round_trips(value: bool) {
    let marker = encode_flag(value);
    let decoded = decode_flag(marker);
    assert(decoded == Some(value));
}

fn noncanonical_flag_is_rejected(tag: u8)
    requires tag > 1,
{
    let decoded = decode_flag(tag);
    assert(decoded is None);
}

fn body_over_limit_is_rejected(declared: u64, minimum: usize, maximum: usize)
    requires maximum < declared,
{
    let decoded = bounded_body_length(declared, minimum, maximum);
    assert(!bodyLengthBounded(declared as int, minimum as int, maximum as int));
    assert(decoded is None);
}

}
