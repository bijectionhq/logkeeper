//! Append-only WAL segment files.
//!
//! A segment starts with a fixed header and holds frames of
//! `length | crc32 | body`. Every frame extends a SHA-256 chain seeded by the
//! media incarnation, so a trusted (segment, offset, chain) boundary
//! authenticates every frame before it.

use std::{
    fs::{File, OpenOptions},
    io::{self, Read, Write},
    path::Path,
};

use sha2::{Digest, Sha256};
use uuid::Uuid;

use crate::stream::{consensus::invalid, keeper::durability::sync_directory};

const MAGIC: &[u8; 8] = b"LKRSEG01";
pub(super) const DIRECTORY: &str = "raft-segments";
pub(super) const HEADER: u64 = 32;
pub(super) const FRAME_HEADER: u64 = 8;
pub(super) const FIRST: u64 = 1;
pub(super) const MAX_FRAME: u64 = 128 * 1024 * 1024;

pub(super) fn name(id: u64) -> String {
    format!("{id:020}.seg")
}

pub(super) fn parse(name: &str) -> Option<u64> {
    let id = name.strip_suffix(".seg")?;
    (id.len() == 20).then(|| id.parse().ok())?
}

fn header(id: u64, incarnation: Uuid) -> [u8; HEADER as usize] {
    let mut header = [0; HEADER as usize];
    header[..8].copy_from_slice(MAGIC);
    header[8..16].copy_from_slice(&id.to_le_bytes());
    header[16..].copy_from_slice(incarnation.as_bytes());
    header
}

/// Creates segment `id` and makes its name durable.
pub(super) fn create(directory: &Path, id: u64, incarnation: Uuid) -> io::Result<File> {
    let mut file = OpenOptions::new()
        .read(true)
        .append(true)
        .create_new(true)
        .open(directory.join(name(id)))?;
    file.write_all(&header(id, incarnation))?;
    crate::stream::keeper::durability::sync_file(&file)?;
    sync_directory(directory)?;
    Ok(file)
}

pub(super) fn check_header(file: &mut impl Read, id: u64, incarnation: Uuid) -> io::Result<()> {
    let mut found = [0; HEADER as usize];
    file.read_exact(&mut found)
        .map_err(|_| invalid("WAL segment lost its header"))?;
    if found != header(id, incarnation) {
        return Err(invalid("WAL segment belongs to another position or media"));
    }
    Ok(())
}

/// Reads and parses a segment header without requiring a known ID or incarnation.
pub(super) fn read_header(file: &mut impl Read) -> io::Result<(u64, Uuid)> {
    let mut found = [0; HEADER as usize];
    file.read_exact(&mut found)
        .map_err(|_| invalid("WAL segment lost its header"))?;
    if &found[..8] != MAGIC {
        return Err(invalid("WAL segment has invalid magic"));
    }
    let id = u64::from_le_bytes(found[8..16].try_into().unwrap());
    let incarnation = Uuid::from_bytes(found[16..32].try_into().unwrap());
    Ok((id, incarnation))
}

pub(super) fn seed(incarnation: Uuid) -> [u8; 32] {
    let mut digest = Sha256::new();
    digest.update(b"logkeeper segment chain");
    digest.update(incarnation.as_bytes());
    digest.finalize().into()
}

pub(super) fn chain(previous: &[u8; 32], header: &[u8], body: &[u8]) -> [u8; 32] {
    let mut digest = Sha256::new();
    digest.update(previous);
    digest.update(header);
    digest.update(body);
    digest.finalize().into()
}

/// Extends `chain` over every frame in `frames`, which holds whole frames.
pub(super) fn chain_frames(mut chain: [u8; 32], mut frames: &[u8]) -> [u8; 32] {
    while !frames.is_empty() {
        let (header, rest) = frames.split_at(FRAME_HEADER as usize);
        let len = u32::from_le_bytes(header[..4].try_into().unwrap()) as usize;
        chain = self::chain(&chain, header, &rest[..len]);
        frames = &rest[len..];
    }
    chain
}

/// Seals the body that follows the 8-byte placeholder at `start`.
pub(super) fn seal(buffer: &mut [u8], start: usize) -> io::Result<()> {
    let body = &buffer[start + FRAME_HEADER as usize..];
    if body.is_empty() || body.len() as u64 > MAX_FRAME {
        return Err(invalid("WAL frame exceeds its size limit"));
    }
    let len = (body.len() as u32).to_le_bytes();
    let crc = crc32fast::hash(body).to_le_bytes();
    buffer[start..start + 4].copy_from_slice(&len);
    buffer[start + 4..start + 8].copy_from_slice(&crc);
    Ok(())
}

pub(super) enum Frame {
    Complete { header: [u8; 8], body: Vec<u8> },
    End,
    Torn,
}

/// Reads the next frame. A short or damaged frame is torn; recovery decides
/// whether that is an unacknowledged tail or lost acknowledged bytes.
pub(super) fn next(file: &mut impl Read) -> io::Result<Frame> {
    let mut header = [0; FRAME_HEADER as usize];
    let mut read = 0;
    while read < header.len() {
        match file.read(&mut header[read..]) {
            Ok(0) if read == 0 => return Ok(Frame::End),
            Ok(0) => return Ok(Frame::Torn),
            Ok(count) => read += count,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => (),
            Err(error) => return Err(error),
        }
    }
    let len = u32::from_le_bytes(header[..4].try_into().unwrap());
    let crc = u32::from_le_bytes(header[4..].try_into().unwrap());
    if len == 0 || u64::from(len) > MAX_FRAME {
        return Ok(Frame::Torn);
    }
    let mut body = Vec::new();
    file.take(u64::from(len)).read_to_end(&mut body)?;
    if body.len() != len as usize || crc32fast::hash(&body) != crc {
        return Ok(Frame::Torn);
    }
    Ok(Frame::Complete { header, body })
}

pub(super) enum RawFrame {
    Complete {
        header: [u8; 8],
        body: Vec<u8>,
        expected_crc: u32,
        actual_crc: u32,
    },
    End,
    Torn {
        reason: String,
    },
}

/// Reads the next frame while reporting CRC mismatches distinctly from EOF/short reads.
pub(super) fn next_raw(file: &mut impl Read) -> io::Result<RawFrame> {
    let mut header = [0; FRAME_HEADER as usize];
    let mut read = 0;
    while read < header.len() {
        match file.read(&mut header[read..]) {
            Ok(0) if read == 0 => return Ok(RawFrame::End),
            Ok(0) => {
                return Ok(RawFrame::Torn {
                    reason: format!("truncated frame header ({read} of {FRAME_HEADER} bytes)"),
                });
            }
            Ok(count) => read += count,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => (),
            Err(error) => return Err(error),
        }
    }
    let len = u32::from_le_bytes(header[..4].try_into().unwrap());
    let expected_crc = u32::from_le_bytes(header[4..].try_into().unwrap());
    if len == 0 || u64::from(len) > MAX_FRAME {
        return Ok(RawFrame::Torn {
            reason: format!("invalid frame length {len}"),
        });
    }
    let mut body = Vec::new();
    file.take(u64::from(len)).read_to_end(&mut body)?;
    if body.len() != len as usize {
        return Ok(RawFrame::Torn {
            reason: format!("truncated frame body ({} of {len} bytes)", body.len()),
        });
    }
    let actual_crc = crc32fast::hash(&body);
    Ok(RawFrame::Complete {
        header,
        body,
        expected_crc,
        actual_crc,
    })
}

pub(super) fn read_at(file: &File, offset: u64, buf: &mut [u8]) -> io::Result<()> {
    #[cfg(unix)]
    {
        std::os::unix::fs::FileExt::read_exact_at(file, buf, offset)
    }
    #[cfg(windows)]
    {
        let mut done = 0;
        while done < buf.len() {
            let count = std::os::windows::fs::FileExt::seek_read(
                file,
                &mut buf[done..],
                offset + done as u64,
            )?;
            if count == 0 {
                return Err(io::ErrorKind::UnexpectedEof.into());
            }
            done += count;
        }
        Ok(())
    }
}
