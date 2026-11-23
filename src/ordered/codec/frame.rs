pub(super) const COMMAND_VERSION: u8 = 8;

pub(super) fn has_command_version(version: u8) -> bool {
    version == COMMAND_VERSION
}

pub(super) fn decision_header(time: [u8; 8]) -> [u8; 9] {
    [
        COMMAND_VERSION,
        time[0],
        time[1],
        time[2],
        time[3],
        time[4],
        time[5],
        time[6],
        time[7],
    ]
}

pub(super) fn read_decision_time(frame: &[u8]) -> Option<[u8; 8]> {
    if frame.len() < 9 || !has_command_version(frame[0]) {
        return None;
    }
    Some([
        frame[1], frame[2], frame[3], frame[4], frame[5], frame[6], frame[7], frame[8],
    ])
}

pub(crate) fn encode_flag(value: bool) -> u8 {
    if value { 1 } else { 0 }
}

pub(crate) fn decode_flag(tag: u8) -> Option<bool> {
    match tag {
        0 => Some(false),
        1 => Some(true),
        _ => None,
    }
}

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
