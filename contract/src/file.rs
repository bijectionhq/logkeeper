use crate::{
    Epoch, Identity, Journal, Lsn, StreamId,
    reference::{Engine, Limits},
    state::{Mutation, State},
};
use bytes::{Buf, BufMut, Bytes};
use std::{
    fs::{File, OpenOptions},
    io::{self, Read, Seek, SeekFrom, Write},
    path::Path,
    sync::Arc,
};

/// A single-file reference journal for local development.
///
/// Open a file once and share the resulting journal or its handles in the process.
/// Each mutation is synchronized to the file before its result is visible. The file
/// retains a log of all mutations, including records later trimmed or deleted.
#[derive(Clone)]
pub struct FileJournal(Arc<Engine>);

impl FileJournal {
    /// Opens or creates a journal file. Reopen it with the same limits.
    ///
    /// The journal takes an exclusive file lock while any handle is alive. Recovery
    /// replays complete frames and cuts an incomplete final write before serving calls.
    pub fn open(path: impl AsRef<Path>, limits: Limits) -> io::Result<Self> {
        let (storage, state) = Storage::open(path.as_ref(), limits)?;
        Ok(Self(Arc::new(Engine::new(state, Some(storage)))))
    }

    /// Returns an owned handle that makes calls as this identity.
    pub fn handle(&self, identity: Identity) -> impl Journal + use<> {
        self.0.handle(identity)
    }
}

pub(crate) struct Storage {
    file: File,
    #[cfg(test)]
    sync: fn(&File) -> io::Result<()>,
}

const MAGIC: &[u8; 8] = b"JKREF\0\0\x01";
const FILE_HEADER_LEN: usize = 24;
const FRAME_HEADER_LEN: u64 = 20;
const STREAM_MUTATION_LEN: u64 = 17; // tag and stream
const APPEND_MUTATION_LEN: u64 = 37; // tag, stream, epoch, URI length and LSN

impl Storage {
    fn open(path: &Path, limits: Limits) -> io::Result<(Self, State)> {
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(path)?;
        file.try_lock()?;

        let mut expected = [0; FILE_HEADER_LEN];
        expected[..8].copy_from_slice(MAGIC);
        expected[8..16].copy_from_slice(&(limits.max_record_bytes as u64).to_le_bytes());
        expected[16..].copy_from_slice(&limits.stream_quota_bytes.to_le_bytes());
        let mut end = file.metadata()?.len();
        let header_len = end.min(FILE_HEADER_LEN as u64) as usize;
        let mut header = [0; FILE_HEADER_LEN];
        file.read_exact(&mut header[..header_len])?;
        if header[..header_len] != expected[..header_len] {
            return Err(invalid("journal format or limits do not match"));
        }
        if header_len < FILE_HEADER_LEN {
            file.write_all(&expected[header_len..])?;
            end = FILE_HEADER_LEN as u64;
        }
        let mut state = State::new(limits);
        let mut position = FILE_HEADER_LEN as u64;
        while end - position >= FRAME_HEADER_LEN {
            let mut frame = [0; FRAME_HEADER_LEN as usize];
            file.read_exact(&mut frame)?;
            let len = u64::from_le_bytes(frame[..8].try_into().unwrap());
            let complement = u64::from_le_bytes(frame[8..16].try_into().unwrap());
            if complement != !len
                || len < STREAM_MUTATION_LEN
                || len
                    > (limits.max_record_bytes as u64)
                        .saturating_add(APPEND_MUTATION_LEN + u64::from(u32::MAX))
            {
                return Err(invalid("invalid journal frame length"));
            }
            if len > end - position - FRAME_HEADER_LEN {
                break;
            }
            let size = usize::try_from(len)
                .map_err(|_| invalid("journal frame does not fit in memory"))?;
            let mut body = vec![0; size];
            file.read_exact(&mut body)?;
            let checksum = u32::from_le_bytes(frame[16..].try_into().unwrap());
            if checksum != crc32(&[&body]) {
                return Err(invalid("journal frame checksum mismatch"));
            }
            let (stream, mutation) =
                decode(Bytes::from(body)).ok_or_else(|| invalid("invalid journal mutation"))?;
            match state.decide(stream, &mutation) {
                Ok(decision) if decision.changed => state.apply(stream, mutation),
                _ => return Err(invalid("invalid journal history")),
            }
            position += FRAME_HEADER_LEN + len;
        }

        if position < end {
            file.set_len(position)?;
        }
        // A prior open may have failed to sync a complete frame that replay found.
        file.sync_all()?;
        let path = path.canonicalize()?;
        File::open(
            path.parent()
                .ok_or_else(|| invalid("journal file has no parent"))?,
        )?
        .sync_all()?;
        file.seek(SeekFrom::Start(position))?;
        Ok((
            Self {
                file,
                #[cfg(test)]
                sync: File::sync_all,
            },
            state,
        ))
    }

    pub(crate) fn persist(&mut self, stream: StreamId, mutation: &Mutation) -> io::Result<()> {
        let mut prefix = [0; APPEND_MUTATION_LEN as usize];
        let mut body = &mut prefix[..];
        let tag = match mutation {
            Mutation::Create => 0,
            Mutation::Seal { .. } => 5,
            Mutation::Append { .. } => 6,
            Mutation::Trim { .. } => 7,
            Mutation::Delete => 4,
        };
        body.put_u8(tag);
        body.put_u128_le(stream.0);

        let identity = match mutation {
            Mutation::Seal { epoch, identity }
            | Mutation::Append {
                epoch, identity, ..
            }
            | Mutation::Trim {
                epoch, identity, ..
            } => {
                body.put_u64_le(epoch.0);
                let uri = identity.as_str().as_bytes();
                body.put_u32_le(
                    uri.len()
                        .try_into()
                        .map_err(|_| invalid("identity too large"))?,
                );
                uri
            }
            Mutation::Create | Mutation::Delete => &[],
        };
        let payload = match mutation {
            Mutation::Append { at, payload, .. } => {
                body.put_u64_le(at.0);
                payload.as_ref()
            }
            Mutation::Trim { through, .. } => {
                body.put_u64_le(through.0);
                &[]
            }
            _ => &[],
        };

        let prefix_len = APPEND_MUTATION_LEN as usize - body.len();
        let body = &prefix[..prefix_len];
        let len = (body.len() as u64)
            .checked_add(identity.len() as u64)
            .and_then(|len| len.checked_add(payload.len() as u64))
            .ok_or_else(|| invalid("journal frame length overflow"))?;
        let mut frame = [0; FRAME_HEADER_LEN as usize];
        frame[..8].copy_from_slice(&len.to_le_bytes());
        frame[8..16].copy_from_slice(&(!len).to_le_bytes());
        let (prefix, suffix) = body.split_at(body.len() - if matches!(tag, 6 | 7) { 8 } else { 0 });
        frame[16..].copy_from_slice(&crc32(&[prefix, identity, suffix, payload]).to_le_bytes());
        self.file.write_all(&frame)?;
        self.file.write_all(prefix)?;
        self.file.write_all(identity)?;
        self.file.write_all(suffix)?;
        self.file.write_all(payload)?;
        #[cfg(test)]
        let sync = self.sync;
        #[cfg(not(test))]
        let sync = File::sync_all;
        sync(&self.file)
    }
}

fn decode(mut body: Bytes) -> Option<(StreamId, Mutation)> {
    let tag = body.try_get_u8().ok()?;
    let stream = StreamId(body.try_get_u128_le().ok()?);
    let mutation = match tag {
        0 => Mutation::Create,
        5..=7 => {
            let epoch = Epoch(body.try_get_u64_le().ok()?);
            let len = body.try_get_u32_le().ok()? as usize;
            if len > body.len() {
                return None;
            }
            let identity = Identity::from(std::str::from_utf8(&body.split_to(len)).ok()?);
            match tag {
                5 => Mutation::Seal { epoch, identity },
                6 => {
                    let at = Lsn(body.try_get_u64_le().ok()?);
                    let payload = std::mem::take(&mut body);
                    Mutation::Append {
                        epoch,
                        identity,
                        at,
                        payload,
                    }
                }
                7 => {
                    let through = Lsn(body.try_get_u64_le().ok()?);
                    Mutation::Trim {
                        epoch,
                        identity,
                        through,
                    }
                }
                _ => unreachable!(),
            }
        }
        4 => Mutation::Delete,
        _ => return None,
    };
    body.is_empty().then_some((stream, mutation))
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

const CRC32_TABLE: [u32; 256] = {
    let mut table = [0; 256];
    let mut index = 0;
    while index < table.len() {
        let mut crc = index as u32;
        let mut bit = 0;
        while bit < 8 {
            crc = (crc >> 1) ^ (0xedb88320 * (crc & 1));
            bit += 1;
        }
        table[index] = crc;
        index += 1;
    }
    table
};

fn crc32(parts: &[&[u8]]) -> u32 {
    let mut crc = u32::MAX;
    for part in parts {
        for &byte in *part {
            crc = (crc >> 8) ^ CRC32_TABLE[((crc as u8) ^ byte) as usize];
        }
    }
    !crc
}

#[cfg(test)]
mod tests;
