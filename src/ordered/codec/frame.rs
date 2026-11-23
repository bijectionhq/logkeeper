#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn commandVersion() -> u8 { 8 }

pub(crate) open spec fn decisionHeader(time: Seq<u8>) -> Seq<u8> {
    seq![commandVersion()] + time
}

pub(crate) open spec fn decisionHeaderMatches(frame: Seq<u8>, time: Seq<u8>) -> bool {
    frame.len() >= 9 && frame[0] == commandVersion() && time == frame.subrange(1, 9)
}

pub(crate) open spec fn flagByte(value: bool) -> u8 {
    if value { 1 } else { 0 }
}

pub(crate) open spec fn readFlag(tag: u8) -> Option<bool> {
    if tag == 0 { Some(false) } else if tag == 1 { Some(true) } else { None }
}

pub(crate) open spec fn bodyLengthBounded(declared: int, minimum: int, maximum: int) -> bool {
    minimum <= declared <= maximum
}

}

pub(super) const COMMAND_VERSION: u8 = 8;

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (version == commandVersion()),
))]
pub(super) fn has_command_version(version: u8) -> bool {
    version == COMMAND_VERSION
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out@ == decisionHeader(time@),
))]
pub(super) fn decision_header(time: [u8; 8]) -> [u8; 9] {
    let header = [
        COMMAND_VERSION,
        time[0],
        time[1],
        time[2],
        time[3],
        time[4],
        time[5],
        time[6],
        time[7],
    ];
    #[cfg(verus_keep_ghost)]
    proof! { assert(header@ =~= decisionHeader(time@)); }
    header
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures match out {
        Some(time) => decisionHeaderMatches(frame@, time@),
        None => frame@.len() < 9 || frame@[0] != commandVersion(),
    },
))]
pub(super) fn read_decision_time(frame: &[u8]) -> Option<[u8; 8]> {
    if frame.len() < 9 || !has_command_version(frame[0]) {
        return None;
    }
    let time = [
        frame[1], frame[2], frame[3], frame[4], frame[5], frame[6], frame[7], frame[8],
    ];
    #[cfg(verus_keep_ghost)]
    proof! { assert(time@ =~= frame@.subrange(1, 9)); }
    Some(time)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == flagByte(value),
))]
pub(crate) fn encode_flag(value: bool) -> u8 {
    if value { 1 } else { 0 }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == readFlag(tag),
))]
pub(crate) fn decode_flag(tag: u8) -> Option<bool> {
    match tag {
        0 => Some(false),
        1 => Some(true),
        _ => None,
    }
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures match out {
        Some(length) => length as int == declared && bodyLengthBounded(declared as int, minimum as int, maximum as int),
        None => !bodyLengthBounded(declared as int, minimum as int, maximum as int),
    },
))]
pub(crate) fn bounded_body_length(
    declared: u64,
    minimum: usize,
    maximum: usize,
) -> Option<usize> {
    if declared < minimum as u64 || declared > maximum as u64 {
        return None;
    }
    Some(declared as usize)
}

pub(super) fn object_name_count(declared: u32, maximum: usize, remaining: usize) -> Option<usize> {
    bounded_body_length(u64::from(declared), 0, maximum.min(remaining / 32))
}
