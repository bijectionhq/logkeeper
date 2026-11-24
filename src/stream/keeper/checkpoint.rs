//! One keeper-wide checkpoint indexes immutable extent packs. Its atomic publication
//! is the only event that makes a newly written pack live or a WAL prefix redundant.

use std::{
    collections::{HashMap, HashSet, VecDeque},
    fs::{self, File},
    io::{self, BufReader, BufWriter, Read, Write},
    path::{Path, PathBuf},
    sync::Arc,
};

use bytes::{BufMut, Bytes, BytesMut};

use super::{
    durability::{sync_directory, sync_file},
    state::{Extent, ExtentReader, Payload, Record, Staging, Stream},
    wal::{Decoder, SEGMENT_BYTES, atomic_file, put_bytes, put_count, read_frame, sequence},
};
use crate::stream::{
    codec::{self, MAX_FRAME_BYTES, invalid},
    wire::{Epoch, Lsn, StreamId},
};

const MAGIC: &[u8; 8] = b"LKPACK01";
const RECORD_BYTES: usize = 32;

#[derive(Default)]
pub(super) struct Checkpoint {
    streams: HashMap<StreamId, Indexed>,
    compaction_due: bool,
    #[cfg(test)]
    pub syncs: usize,
}

struct Indexed {
    snapshot: Snapshot,
    body: Bytes,
    packs: HashSet<u64>,
    bytes: u64,
}

impl Indexed {
    fn new(snapshot: Snapshot) -> Self {
        Self {
            snapshot,
            body: Bytes::new(),
            packs: HashSet::new(),
            bytes: 0,
        }
    }

    fn write(&mut self, pack: &mut Pack) -> io::Result<()> {
        self.packs.clear();
        let mut body = BytesMut::new();
        let snapshot = &self.snapshot;
        body.put_u128(snapshot.stream.0);
        body.put_u8(u8::from(snapshot.deleted));
        put_bytes(&mut body, &codec::encode_checkpoint_view(&snapshot.view)?)?;
        self.bytes = pack.index(&mut body, &mut self.packs, &snapshot.records)?;
        body.put_u8(u8::from(snapshot.staged.is_some()));
        if let Some((from, floor, records)) = &snapshot.staged {
            body.put_u64(from.0);
            body.put_u64(floor.0);
            self.bytes += pack.index(&mut body, &mut self.packs, records)?;
        }
        self.body = body.freeze();
        Ok(())
    }
}

pub(super) struct Snapshot {
    stream: StreamId,
    view: crate::stream::wire::StreamView,
    deleted: bool,
    records: VecDeque<Record>,
    staged: Option<(Lsn, Lsn, VecDeque<Record>)>,
}

impl Snapshot {
    pub fn of(stream: StreamId, state: &Stream) -> Self {
        Self {
            stream,
            view: state.view.clone(),
            deleted: state.deleted,
            records: state.records.clone(),
            staged: state
                .staging
                .as_ref()
                .map(|s| (s.from, s.floor, s.records.clone())),
        }
    }
}
fn pack_path(dir: &Path, seq: u64) -> PathBuf {
    dir.join(format!("{seq:020}.pack"))
}

struct Pack {
    extent: Arc<Extent>,
    output: Option<BufWriter<File>>,
    offset: u64,
    rewrite: bool,
    reader: ExtentReader,
    moved: Vec<(Record, Location)>,
}

#[derive(Clone, Copy)]
struct Location {
    seq: u64,
    offset: u64,
    len: u32,
    crc: u32,
}

impl Pack {
    fn index(
        &mut self,
        out: &mut BytesMut,
        packs: &mut HashSet<u64>,
        records: &VecDeque<Record>,
    ) -> io::Result<u64> {
        let mut bytes = 0;
        put_count(out, records.len())?;
        for record in records {
            let existing = match &*record.payload.read() {
                Payload::Extent {
                    extent,
                    offset,
                    len,
                    crc,
                } if !self.rewrite => Some(Location {
                    seq: extent.sequence,
                    offset: *offset,
                    len: *len,
                    crc: *crc,
                }),
                _ => None,
            };
            let location = if let Some(location) = existing {
                location
            } else {
                let payload = record.read(&mut self.reader)?;
                if self.output.is_none() {
                    self.output = Some(BufWriter::new(
                        File::options()
                            .create_new(true)
                            .write(true)
                            .open(&self.extent.path)?,
                    ));
                }
                self.output
                    .as_mut()
                    .expect("pack open")
                    .write_all(&payload)?;
                let location = Location {
                    seq: self.extent.sequence,
                    offset: self.offset,
                    len: payload.len() as u32,
                    crc: crc32fast::hash(&payload),
                };
                self.offset += u64::from(location.len);
                self.moved.push((record.clone(), location));
                location
            };
            out.put_u64(record.epoch.0);
            out.put_u64(location.seq);
            out.put_u64(location.offset);
            out.put_u32(location.len);
            out.put_u32(location.crc);
            packs.insert(location.seq);
            bytes += u64::from(location.len);
        }
        Ok(bytes)
    }

    fn sync(&mut self, root: &Path) -> io::Result<()> {
        if let Some(mut file) = self.output.take() {
            file.flush()?;
            sync_file(file.get_ref())?;
            // Publish the pack name before the index can refer to it.
            sync_directory(root)?;
        }
        Ok(())
    }

    fn install(self) {
        for (record, location) in self.moved {
            *record.payload.write() = Payload::Extent {
                extent: Arc::clone(&self.extent),
                offset: location.offset,
                len: location.len,
                crc: location.crc,
            };
        }
    }
}

impl Checkpoint {
    pub fn write(
        &mut self,
        root: &Path,
        next: u64,
        snapshots: Vec<Snapshot>,
        rewrite: bool,
    ) -> io::Result<()> {
        let path = pack_path(root, next);
        if !self.references(next) {
            // An earlier crash may have written this pack without publishing its index.
            // Reuse the boundary rather than creating an extra WAL segment on each boot.
            match fs::remove_file(&path) {
                Ok(()) => {}
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => return Err(error),
            }
        }
        let mut pack = Pack {
            extent: Arc::new(Extent {
                sequence: next,
                path,
            }),
            output: None,
            offset: 0,
            rewrite,
            reader: ExtentReader::default(),
            moved: Vec::new(),
        };
        for snapshot in snapshots {
            self.streams.insert(snapshot.stream, Indexed::new(snapshot));
        }
        for indexed in self.streams.values_mut() {
            if rewrite || indexed.body.is_empty() {
                indexed.write(&mut pack)?;
            }
        }
        pack.sync(root)?;
        atomic_file(&root.join("INDEX"), |file| {
            file.write_all(MAGIC)?;
            file.write_all(&next.to_be_bytes())?;
            let count: u32 = self
                .streams
                .len()
                .try_into()
                .map_err(|_| invalid("too many indexed streams"))?;
            file.write_all(&count.to_be_bytes())?;
            let mut crc = crc32fast::Hasher::new();
            crc.update(&next.to_be_bytes());
            crc.update(&count.to_be_bytes());
            file.write_all(&crc.finalize().to_be_bytes())?;
            for stream in self.streams.values() {
                let len: u32 = stream
                    .body
                    .len()
                    .try_into()
                    .map_err(|_| invalid("stream index too large"))?;
                file.write_all(&len.to_be_bytes())?;
                file.write_all(&crc32fast::hash(&stream.body).to_be_bytes())?;
                file.write_all(&stream.body)?;
            }
            Ok(())
        })?;
        pack.install();
        self.retire_packs(root)
    }

    pub fn references(&self, seq: u64) -> bool {
        self.streams
            .values()
            .any(|stream| stream.packs.contains(&seq))
    }

    fn live_packs(&self) -> HashSet<u64> {
        self.streams
            .values()
            .flat_map(|stream| stream.packs.iter().copied())
            .collect()
    }

    pub fn has_orphan_packs(&self, root: &Path) -> io::Result<bool> {
        let live = self.live_packs();
        for entry in fs::read_dir(root)? {
            let path = entry?.path();
            if path.extension().is_some_and(|ext| ext == "pack")
                && !live.contains(&sequence(&path)?)
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub fn compaction_due(&self) -> bool {
        self.compaction_due
    }

    fn retire_packs(&mut self, root: &Path) -> io::Result<()> {
        let live = self.live_packs();
        let mut removed = false;
        let mut packed_bytes = 0;
        for entry in fs::read_dir(root)? {
            let entry = entry?;
            let path = entry.path();
            if path.extension().is_some_and(|ext| ext == "pack") {
                if live.contains(&sequence(&path)?) {
                    packed_bytes += entry.metadata()?.len();
                } else {
                    fs::remove_file(path)?;
                    removed = true;
                }
            }
        }
        let live_bytes: u64 = self.streams.values().map(|stream| stream.bytes).sum();
        self.compaction_due =
            packed_bytes > SEGMENT_BYTES.saturating_add(live_bytes.saturating_mul(2));
        let legacy = root.join("streams");
        if legacy.exists() {
            fs::remove_dir_all(legacy)?;
            removed = true;
        }
        if removed {
            sync_directory(root)?;
        }
        Ok(())
    }

    pub fn load(root: &Path) -> io::Result<Option<(u64, Self, HashMap<StreamId, Stream>)>> {
        let file = match File::open(root.join("INDEX")) {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(error),
        };
        let length = file.metadata()?.len();
        let mut file = BufReader::new(file);
        let mut magic = [0; 8];
        let mut next = [0; 8];
        let mut count = [0; 4];
        let mut crc = [0; 4];
        file.read_exact(&mut magic)?;
        file.read_exact(&mut next)?;
        file.read_exact(&mut count)?;
        file.read_exact(&mut crc)?;
        let mut hash = crc32fast::Hasher::new();
        hash.update(&next);
        hash.update(&count);
        if &magic != MAGIC || hash.finalize() != u32::from_be_bytes(crc) {
            return Err(invalid("damaged keeper index header"));
        }
        let next = u64::from_be_bytes(next);
        let mut remaining = length - 24;
        let mut packs = HashMap::new();
        let mut states = HashMap::new();
        let mut index = Self::default();
        for _ in 0..u32::from_be_bytes(count) {
            let body = read_frame(&mut file, remaining, u32::MAX as usize)?
                .ok_or_else(|| invalid("damaged keeper index stream"))?;
            remaining -= 8 + body.len() as u64;
            let mut decoder = Decoder(body.clone());
            let stream = StreamId(decoder.u128()?);
            let deleted = decoder.boolean()?;
            let view = codec::decode_checkpoint_view(decoder.bytes()?)?;
            let mut live = HashSet::new();
            let mut records = PackReader {
                root,
                next,
                known: &mut packs,
                live: &mut live,
            };
            let retained = records.read(&mut decoder)?;
            let staging = if decoder.boolean()? {
                let from = Lsn(decoder.u64()?);
                let floor = Lsn(decoder.u64()?);
                if from.0 == 0 {
                    return Err(invalid("invalid staged stream history"));
                }
                Some(Staging {
                    from,
                    floor,
                    records: records.read(&mut decoder)?,
                })
            } else {
                None
            };
            decoder.finish()?;
            if view
                .tail
                .0
                .checked_add(1)
                .and_then(|end| end.checked_sub(view.floor.0))
                != Some(retained.len() as u64)
                || (deleted && (!retained.is_empty() || staging.is_some()))
            {
                return Err(invalid("invalid retained range in keeper index"));
            }
            let bytes = retained
                .iter()
                .map(|record| record.len().max(1) as u64)
                .sum();
            let state = Stream {
                view,
                deleted,
                records: retained,
                staging,
                bytes,
                ..Stream::default()
            };
            let snapshot = Snapshot::of(stream, &state);
            let bytes = state
                .records
                .iter()
                .chain(state.staging.iter().flat_map(|s| &s.records))
                .map(|record| record.len() as u64)
                .sum();
            if states.insert(stream, state).is_some() {
                return Err(invalid("duplicate stream in keeper index"));
            }
            index.streams.insert(
                stream,
                Indexed {
                    snapshot,
                    body,
                    packs: live,
                    bytes,
                },
            );
        }
        if remaining != 0 {
            return Err(invalid("trailing data in keeper index"));
        }
        Ok(Some((next, index, states)))
    }
}

struct PackReader<'a> {
    root: &'a Path,
    next: u64,
    known: &'a mut HashMap<u64, (Arc<Extent>, u64)>,
    live: &'a mut HashSet<u64>,
}

impl PackReader<'_> {
    fn read(&mut self, input: &mut Decoder) -> io::Result<VecDeque<Record>> {
        (0..input.count(RECORD_BYTES)?)
            .map(|_| {
                let epoch = Epoch(input.u64()?);
                let seq = input.u64()?;
                let offset = input.u64()?;
                let len = input.u32()?;
                let crc = input.u32()?;
                let (extent, size) = match self.known.entry(seq) {
                    std::collections::hash_map::Entry::Occupied(entry) => entry.into_mut(),
                    std::collections::hash_map::Entry::Vacant(entry) => {
                        let path = pack_path(self.root, seq);
                        let size = fs::metadata(&path)?.len();
                        entry.insert((
                            Arc::new(Extent {
                                sequence: seq,
                                path,
                            }),
                            size,
                        ))
                    }
                };
                if seq > self.next
                    || len as usize > MAX_FRAME_BYTES
                    || offset
                        .checked_add(u64::from(len))
                        .is_none_or(|end| end > *size)
                {
                    return Err(invalid("invalid extent reference in keeper index"));
                }
                self.live.insert(seq);
                Ok(Record::new(
                    epoch,
                    Payload::Extent {
                        extent: Arc::clone(extent),
                        offset,
                        len,
                        crc,
                    },
                ))
            })
            .collect()
    }
}
