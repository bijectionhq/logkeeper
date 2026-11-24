use crate::ordered::admission::matches_fingerprint;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn commandVersion() -> u8 { 9 }

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

pub(crate) open spec fn objectNameCountFits(declared: int, maximum: int, remaining: int) -> bool {
    declared <= maximum && 32 * declared <= remaining
}

pub(crate) open spec fn decisionRequestBytes(frame: Seq<u8>) -> Seq<u8> {
    frame.take(1) + frame.skip(9)
}

pub(crate) open spec fn withdrawalIdentityAdmissible(name: Seq<u8>, version: Seq<u8>) -> bool {
    name != Seq::new(32, |_i| 0u8) && version != Seq::new(32, |_i| 0u8)
}

pub(crate) open spec fn withdrawnWorkerCountBounded(count: int) -> bool { count <= 64 }

pub(crate) open spec fn readFixedField(frame: Seq<u8>, width: usize) -> Option<Seq<u8>> {
    if width <= frame.len() { Some(frame.take(width as int)) } else { None }
}

}

pub(super) const COMMAND_VERSION: u8 = 9;
pub(crate) const MAX_WITHDRAWN_WORKERS: usize = 64;

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
    ensures match out {
        Some((time, version, fields)) =>
            decisionHeaderMatches(frame@, time@)
            && version@ == frame@.take(1) && fields@ == frame@.skip(9),
        None => frame@.len() < 9 || frame@[0] != commandVersion(),
    },
))]
pub(super) fn decision_request_parts(frame: &[u8]) -> Option<([u8; 8], &[u8], &[u8])> {
    let time = read_decision_time(frame)?;
    let (version, _) = frame.split_at(1);
    let (_, fields) = frame.split_at(9);
    Some((time, version, fields))
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures match out {
        Some(field) => readFixedField(frame@, N) == Some(field@),
        None => readFixedField(frame@, N) is None,
    },
))]
pub(super) fn read_fixed_field<const N: usize>(frame: &[u8]) -> Option<[u8; N]> {
    let (prefix, _) = frame.split_at_checked(N)?;
    let mut field = [0; N];
    field.copy_from_slice(prefix);
    Some(field)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == withdrawalIdentityAdmissible(name@, version@),
))]
pub(super) fn withdrawal_identity_admissible(name: &[u8; 32], version: &[u8; 32]) -> bool {
    let zero = [0; 32];
    #[cfg(verus_keep_ghost)]
    proof! { assert(zero@ =~= Seq::new(32, |_i| 0u8)); }
    !matches_fingerprint(name, &zero) && !matches_fingerprint(version, &zero)
}

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == withdrawnWorkerCountBounded(count as int),
))]
pub(super) fn withdrawn_worker_count_bounded(count: usize) -> bool {
    count <= MAX_WITHDRAWN_WORKERS
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

#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures match out {
        Some(count) => count as int == declared && objectNameCountFits(declared as int, maximum as int, remaining as int),
        None => !objectNameCountFits(declared as int, maximum as int, remaining as int),
    },
))]
pub(super) fn object_name_count(declared: u32, maximum: usize, remaining: usize) -> Option<usize> {
    bounded_body_length(u64::from(declared), 0, maximum.min(remaining / 32))
}
