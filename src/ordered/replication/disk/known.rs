use super::mirror_body::{MirrorBody, mirror_body};
use super::recover::recover_slot;
use super::selection::authenticates_body;
use super::{
    DESCRIPTOR_BYTES, Error, File, Fingerprint, Group, HEADER, Prefix, Selected, Uuid, VoterState,
    decode_header, matches_slot, read_slot_header, slot_body_len, slot_framing,
};
use sha2::{Digest, Sha256};
use std::io::{BufReader, Read, Seek, SeekFrom};

// A matching mirror can reuse state only after checking the complete body and the
// descriptor-bound digest of this slot independently of the other slot.
pub(super) fn recover_slot_against(
    file: &mut File,
    index: usize,
    group: &Group,
    voter: Uuid,
    size: usize,
    known: Option<&VoterState>,
) -> Result<(usize, Option<(Selected, Fingerprint)>), Error> {
    let Some(known) = known else {
        return recover_slot(file, index, group, voter, size);
    };
    let raw = read_slot_header(file)?;
    let payload_limit = size - HEADER;
    let Some(header) = decode_header(&raw, payload_limit) else {
        return Ok((payload_limit, None));
    };
    let (framing, framing_len, prefix) = slot_framing(known);
    if slot_body_len(framing_len, prefix) == Some(header.length) {
        let mut source = BufReader::with_capacity(32 * 1024, (&mut *file).take(header.length as u64));
        let mut hash = Sha256::new();
        hash.update(&raw[..DESCRIPTOR_BYTES]);
        let mut scratch = [0; 8192];
        let mut body = mirror_body(header.length);
        compare_part(&mut source, &mut hash, &mut scratch, &mut body, &framing[..framing_len])?;
        for (length, payload) in prefix.into_iter().flat_map(Prefix::framed_payloads) {
            compare_part(&mut source, &mut hash, &mut scratch, &mut body, &length)?;
            compare_part(&mut source, &mut hash, &mut scratch, &mut body, payload)?;
        }
        let observed: Fingerprint = hash.finalize().into();
        if !authenticates_body(&observed, &header.digest) {
            return Ok((payload_limit, None));
        }
        if !matches_slot(&header, &group.identity, voter.as_bytes()) {
            return Err(Error::Group);
        }
        if body.matches() {
            return Ok((
                header.length,
                Some((
                    Selected {
                        index,
                        generation: header.descriptor.generation,
                        state: known.clone(),
                    },
                    observed,
                )),
            ));
        }
    }
    // An independently valid different image still needs its own decode and replay.
    file.seek(SeekFrom::Start(0))?;
    recover_slot(file, index, group, voter, size)
}

fn compare_part(
    file: &mut impl Read,
    hash: &mut Sha256,
    scratch: &mut [u8],
    body: &mut MirrorBody,
    expected: &[u8],
) -> Result<(), Error> {
    for part in expected.chunks(scratch.len()) {
        let read = &mut scratch[..part.len()];
        file.read_exact(read)?;
        hash.update(&*read);
        body.observe(part, read);
    }
    Ok(())
}
