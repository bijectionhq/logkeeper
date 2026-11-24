//! Read the previous per-stream checkpoint format during the first open after upgrade.
use std::{
    collections::{HashMap, VecDeque},
    fs::{self, File},
    io::{self, BufReader, Read, Seek, SeekFrom},
    path::{Path, PathBuf},
    sync::Arc,
};

use bytes::Buf;

use super::{
    state::{Extent, Payload, Record, Staging, Stream},
    wal::{Decoder, read_frame},
};
use crate::stream::{
    codec::{self, MAX_FRAME_BYTES, invalid},
    wire::{Epoch, Lsn, StreamId},
};

fn extent_path(dir: &Path, sequence: u64, staged: bool) -> PathBuf {
    let kind = if staged { "staged" } else { "extent" };
    dir.join(format!("{sequence:020}.{kind}"))
}

#[derive(Clone, Copy)]
struct Span {
    sequence: u64,
    staged: bool,
    first: Lsn,
    last: Lsn,
}

pub(super) fn load(root: &Path) -> io::Result<HashMap<StreamId, Stream>> {
    let mut states = HashMap::new();
    for entry in fs::read_dir(root)? {
        let entry = entry?;
        let name = entry.file_name();
        let id = name
            .to_str()
            .filter(|name| name.len() == 32)
            .and_then(|name| u128::from_str_radix(name, 16).ok())
            .ok_or_else(|| invalid("invalid stream directory"))?;
        let dir = entry.path();
        let file = match File::open(dir.join("state")) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                continue;
            }
            Err(error) => return Err(error),
        };
        let length = file.metadata()?.len();
        let body = read_frame(&mut BufReader::new(file), length, u32::MAX as usize)?
            .filter(|body| body.len() as u64 + 8 == length)
            .ok_or_else(|| invalid("damaged stream checkpoint"))?;
        let mut input = Decoder(body);
        let checkpoint = Some(input.u64()?);
        let deleted = input.boolean()?;
        let view = codec::decode_checkpoint_view(input.bytes()?)?;
        let mut state = Stream {
            checkpoint,
            deleted,
            view,
            ..Stream::default()
        };
        let spans = input.spans()?;
        let staged = if input.boolean()? {
            Some((Lsn(input.u64()?), Lsn(input.u64()?), input.spans()?))
        } else {
            None
        };
        input.finish()?;
        if read_extents(&dir, state.view.floor, &spans, &mut state.records)? != state.view.tail {
            return Err(invalid("stream checkpoint is missing records"));
        }
        state.bytes = state
            .records
            .iter()
            .map(|record| record.len().max(1) as u64)
            .sum();
        if let Some((from, floor, staged)) = staged {
            if from.0 == 0 {
                return Err(invalid("invalid staged stream history"));
            }
            let mut staging = Staging {
                from,
                floor,
                records: VecDeque::new(),
            };
            read_extents(&dir, from, &staged, &mut staging.records)?;
            state.staging = Some(staging);
        }
        states.insert(StreamId(id), state);
    }
    Ok(states)
}

/// Read contiguous spans from `first` and return the last position read.
fn read_extents(
    dir: &Path,
    first: Lsn,
    spans: &[Span],
    records: &mut VecDeque<Record>,
) -> io::Result<Lsn> {
    let mut next = first.0;
    for span in spans {
        if span.first.0 != next || span.last < span.first {
            return Err(invalid("noncontiguous stream checkpoint extents"));
        }
        read_extent(dir, *span, records)?;
        next = span.last.0 + 1;
    }
    Ok(Lsn(next - 1))
}

fn read_extent(dir: &Path, span: Span, records: &mut VecDeque<Record>) -> io::Result<()> {
    let path = extent_path(dir, span.sequence, span.staged);
    let file = File::open(&path)?;
    let extent = Arc::new(Extent {
        sequence: span.sequence,
        path,
    });
    let length = file.metadata()?.len();
    let mut input = BufReader::new(file);
    let mut next = span.first.0;
    let mut offset = 0;
    while offset < length {
        let mut header = [0; 24];
        input.read_exact(&mut header)?;
        let mut bytes = &header[..];
        let lsn = bytes.get_u64();
        let epoch = Epoch(bytes.get_u64());
        let len = bytes.get_u32();
        let crc = bytes.get_u32();
        offset += 24;
        if offset + u64::from(len) > length || len as usize > MAX_FRAME_BYTES {
            return Err(invalid("short stream extent"));
        }
        if lsn >= span.first.0 {
            if lsn != next {
                return Err(invalid("out of order stream extent"));
            }
            records.push_back(Record::new(
                epoch,
                Payload::Extent {
                    extent: Arc::clone(&extent),
                    offset,
                    len,
                    crc,
                },
            ));
            next += 1;
            if lsn == span.last.0 {
                return Ok(());
            }
        }
        offset += u64::from(len);
        input.seek(SeekFrom::Start(offset))?;
    }
    Err(invalid("stream extent is missing records"))
}

impl Decoder {
    fn spans(&mut self) -> io::Result<Vec<Span>> {
        (0..self.count(25)?)
            .map(|_| {
                Ok(Span {
                    sequence: self.u64()?,
                    staged: self.boolean()?,
                    first: Lsn(self.u64()?),
                    last: Lsn(self.u64()?),
                })
            })
            .collect()
    }
}
