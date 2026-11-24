//! One keeper-wide checkpoint indexes immutable extent packs. Its atomic publication
//! is the only event that makes a newly written pack live or a WAL prefix redundant.

use std::{
    collections::{HashMap, HashSet, VecDeque},
    fs::{self, File},
    io::{self, BufReader, BufWriter, Read, Write},
    path::{Path, PathBuf},
    sync::Arc,
};

use bytes::Bytes;

use super::{
    checkpoint_bytes::{
        self, EXTENT_BYTES, INDEX_HEADER_BYTES, Location, StagedIndex, StreamIndex,
    },
    durability::{sync_directory, sync_file},
    state::{Extent, ExtentReader, Payload, Record, Staging, Stream},
    wal::{SEGMENT_BYTES, atomic_file, read_frame, sequence},
    wal_bytes::{self, FRAME_HEADER_BYTES},
    wal_layout::{extent_fits, stored_length},
};
use crate::stream::{
    codec::{self, MAX_FRAME_BYTES, invalid},
    wire::{Epoch, Lsn, StreamId},
};

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
        let snapshot = &self.snapshot;
        let view = codec::encode_checkpoint_view(&snapshot.view)?;
        let (retained, retained_bytes) = pack.index(&mut self.packs, &snapshot.records)?;
        let (staged, staged_bytes) = match &snapshot.staged {
            Some((_, _, records)) => pack.index(&mut self.packs, records)?,
            None => (Vec::new(), 0),
        };
        self.bytes = retained_bytes + staged_bytes;
        self.body = Bytes::from(
            checkpoint_bytes::encode_stream_index(StreamIndex {
                stream: snapshot.stream.0,
                deleted: snapshot.deleted,
                view: &view,
                retained: &retained,
                staged: snapshot
                    .staged
                    .as_ref()
                    .map(|(from, floor, _)| StagedIndex {
                        from: from.0,
                        floor: floor.0,
                        rows: &staged,
                    }),
            })
            .ok_or_else(|| invalid("invalid stream index"))?,
        );
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

impl Pack {
    fn index(
        &mut self,
        packs: &mut HashSet<u64>,
        records: &VecDeque<Record>,
    ) -> io::Result<(Vec<u8>, u64)> {
        let mut bytes = 0;
        let capacity = stored_length(records.len())
            .and_then(|count| (count as usize).checked_mul(EXTENT_BYTES))
            .ok_or_else(|| invalid("too many indexed records"))?;
        let mut rows = Vec::with_capacity(capacity);
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
                let (offset, end, len, crc) =
                    checkpoint_bytes::describe_extent(self.offset, &payload)
                        .ok_or_else(|| invalid("keeper pack extent is too large"))?;
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
                    offset,
                    len,
                    crc,
                };
                self.offset = end;
                self.moved.push((record.clone(), location));
                location
            };
            rows.extend_from_slice(&checkpoint_bytes::encode_extent(record.epoch.0, location));
            packs.insert(location.seq);
            bytes += u64::from(location.len);
        }
        Ok((rows, bytes))
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
            let count: u32 = self
                .streams
                .len()
                .try_into()
                .map_err(|_| invalid("too many indexed streams"))?;
            file.write_all(&checkpoint_bytes::encode_index_header(next, count))?;
            for stream in self.streams.values() {
                let header = wal_bytes::encode_frame(&[], &stream.body)
                    .ok_or_else(|| invalid("stream index too large"))?;
                file.write_all(&header)?;
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
        let mut header = [0; INDEX_HEADER_BYTES];
        file.read_exact(&mut header)?;
        let (next, count) = checkpoint_bytes::decode_index_header(&header)
            .ok_or_else(|| invalid("damaged keeper index header"))?;
        let mut remaining = length - INDEX_HEADER_BYTES as u64;
        let mut packs = HashMap::new();
        let mut states = HashMap::new();
        let mut index = Self::default();
        for _ in 0..count {
            let body = read_frame(&mut file, remaining, u32::MAX as usize)?
                .ok_or_else(|| invalid("damaged keeper index stream"))?;
            remaining -= FRAME_HEADER_BYTES as u64 + body.len() as u64;
            let row = checkpoint_bytes::decode_stream_index(&body)
                .ok_or_else(|| invalid("invalid keeper index stream"))?;
            let stream = StreamId(row.stream);
            let deleted = row.deleted;
            let view = codec::decode_checkpoint_view(body.slice_ref(row.view))?;
            let mut live = HashSet::new();
            let mut records = PackReader {
                root,
                next,
                known: &mut packs,
                live: &mut live,
            };
            let retained = records.read(row.retained)?;
            let staging = row
                .staged
                .map(|staged| -> io::Result<_> {
                    Ok(Staging {
                        from: Lsn(staged.from),
                        floor: Lsn(staged.floor),
                        records: records.read(staged.rows)?,
                    })
                })
                .transpose()?;
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
    fn read(&mut self, rows: &[u8]) -> io::Result<VecDeque<Record>> {
        rows.chunks_exact(EXTENT_BYTES)
            .map(|row| {
                let (
                    epoch,
                    Location {
                        seq,
                        offset,
                        len,
                        crc,
                    },
                    _,
                ) = checkpoint_bytes::decode_extent(row)
                    .ok_or_else(|| invalid("short keeper index extent"))?;
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
                if !extent_fits(seq, self.next, offset, len, MAX_FRAME_BYTES, *size) {
                    return Err(invalid("invalid extent reference in keeper index"));
                }
                self.live.insert(seq);
                Ok(Record::new(
                    Epoch(epoch),
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
