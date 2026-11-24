//! Segmented keeper WAL. The checkpoint chooses a complete segment boundary.
//! Physical segments may roll between fragments, but never exceed their byte cap.
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs::{self, File, OpenOptions},
    io::{self, BufReader, BufWriter, Read, Write},
    path::{Path, PathBuf},
};

use bytes::{Buf, BufMut, Bytes, BytesMut};
use fs2::FileExt;

use super::{
    checkpoint::{Checkpoint, Snapshot},
    durability::{sync_directory, sync_file},
    state::{ExtentReader, Stream},
    wal_bytes::{self, FRAME_HEADER_BYTES},
};
use crate::stream::{
    codec::{self, MAX_FRAME_BYTES, invalid},
    wire::{Identity, KeeperId, Request, StreamId},
};

pub(super) const SEGMENT_BYTES: u64 = 64 * 1024 * 1024;
pub(super) const MAX_WAL_SUFFIX_BYTES: u64 = 4 * SEGMENT_BYTES;
pub(super) use wal_bytes::FRAME_OVERHEAD;
pub(super) const MAX_IDENTITY_BYTES: usize = 4096;
const MAX_ENTRY_BYTES: usize = MAX_FRAME_BYTES + 4 + MAX_IDENTITY_BYTES;
const START: u8 = 1;
const END: u8 = 2;
const CONTINUED: u8 = 4;

pub(super) struct Wal {
    _lock: File,
    segments: PathBuf,
    root: PathBuf,
    file: File,
    sequence: u64,
    bytes: u64,
    pub uncheckpointed: u64,
    pub bootstrap: bool,
    index: Option<Checkpoint>,
    pub dirty: HashSet<StreamId>,
    pub reader: ExtentReader,
    rotation: Option<Rotation>,
    /// Holds the checkpoint worker until the test releases it.
    #[cfg(test)]
    pub rotation_gate: Option<std::sync::mpsc::Receiver<()>>,
    #[cfg(test)]
    pub rounds: Vec<usize>,
    #[cfg(test)]
    pub segment_bytes: u64,
    #[cfg(test)]
    pub fail_sync: bool,
    #[cfg(test)]
    pub retain_unsynced: Option<usize>,
}

pub(super) fn entry(request: &Request, identity: Option<&Identity>) -> io::Result<Bytes> {
    let request = codec::encode_request(request)?;
    let identity = identity.map_or("", Identity::as_str).as_bytes();
    wal_bytes::encode_entry(identity, &request)
        .map(Bytes::from)
        .ok_or_else(|| invalid("oversized WAL entry"))
}

fn decode_identity(uri: &[u8]) -> io::Result<Option<Identity>> {
    if uri.is_empty() {
        return Ok(None);
    }
    if uri.len() > MAX_IDENTITY_BYTES {
        return Err(invalid("oversized WAL identity"));
    }
    let uri = std::str::from_utf8(uri).map_err(|_| invalid("invalid WAL identity"))?;
    Ok(Some(Identity::from(uri)))
}

pub(super) fn fragment(
    buffer: &mut Vec<u8>,
    stream: StreamId,
    first: bool,
    last: bool,
    bytes: &[u8],
) {
    let flags = u8::from(first) * START | u8::from(last) * END;
    assert!(wal_bytes::encode_fragment(buffer, stream.0, flags, bytes));
}

pub(super) fn read_frame(
    reader: &mut impl Read,
    remaining: u64,
    max: usize,
) -> io::Result<Option<Bytes>> {
    if remaining < FRAME_HEADER_BYTES as u64 {
        return Ok(None);
    }
    let mut header = [0; FRAME_HEADER_BYTES];
    reader.read_exact(&mut header)?;
    let Some((len, _)) = wal_bytes::decode_frame_header(&header, remaining, max) else {
        return Ok(None);
    };
    let mut frame = vec![0; FRAME_HEADER_BYTES + len as usize];
    frame[..FRAME_HEADER_BYTES].copy_from_slice(&header);
    reader.read_exact(&mut frame[FRAME_HEADER_BYTES..])?;
    if wal_bytes::decode_frame(&frame, max).is_none() {
        return Ok(None);
    }
    let mut bytes = Bytes::from(frame);
    bytes.advance(FRAME_HEADER_BYTES);
    debug_assert_eq!(bytes.len(), len as usize);
    Ok(Some(bytes))
}

pub(super) fn atomic_file(
    path: &Path,
    write: impl FnOnce(&mut BufWriter<File>) -> io::Result<()>,
) -> io::Result<()> {
    let temporary = path.with_extension("tmp");
    let mut file = BufWriter::new(File::create(&temporary)?);
    write(&mut file)?;
    file.flush()?;
    sync_file(file.get_ref())?;
    drop(file);
    fs::rename(temporary, path)?;
    sync_directory(path.parent().expect("file has parent"))
}

fn directories(path: &Path) -> io::Result<()> {
    if path.is_dir() {
        return Ok(());
    }
    let parent = path
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    directories(parent)?;
    fs::create_dir(path)?;
    sync_directory(parent)
}

fn segment_path(dir: &Path, sequence: u64) -> PathBuf {
    dir.join(format!("{sequence:020}.seg"))
}

pub(super) fn sequence(path: &Path) -> io::Result<u64> {
    path.file_stem()
        .and_then(|stem| stem.to_str())
        .and_then(|stem| stem.parse().ok())
        .ok_or_else(|| invalid("invalid keeper sequence"))
}

fn segments(dir: &Path) -> io::Result<BTreeMap<u64, PathBuf>> {
    let mut paths = BTreeMap::new();
    for entry in fs::read_dir(dir)? {
        let path = entry?.path();
        if path.extension().is_some_and(|ext| ext == "seg")
            && paths.insert(sequence(&path)?, path).is_some()
        {
            return Err(invalid("duplicate keeper segment sequence"));
        }
    }
    Ok(paths)
}

fn new_segment(dir: &Path, sequence: u64, continuation: bool) -> io::Result<(File, u64)> {
    let mut file = OpenOptions::new()
        .create_new(true)
        .append(true)
        .open(segment_path(dir, sequence))?;
    let mut marker = Vec::new();
    if continuation {
        assert!(wal_bytes::encode_fragment(&mut marker, 0, CONTINUED, &[0]));
        file.write_all(&marker)?;
    }
    sync_file(&file)?;
    sync_directory(dir)?;
    Ok((file, marker.len() as u64))
}

impl Wal {
    pub fn open(data: &Path, keeper: KeeperId) -> io::Result<(Self, HashMap<StreamId, Stream>)> {
        directories(data)?;
        let lock = OpenOptions::new()
            .create(true)
            .truncate(false)
            .write(true)
            .open(data.join("LOCK"))?;
        lock.try_lock_exclusive()?;
        let segment_dir = data.join("segments");
        directories(&segment_dir)?;
        let identity = data.join("KEEPER");
        let mut paths = segments(&segment_dir)?;
        match fs::read(&identity) {
            Ok(id) if id == keeper.0.to_be_bytes() && !paths.is_empty() => {}
            Ok(_) => return Err(invalid("keeper identity differs or its WAL is missing")),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                let empty_initial = paths.is_empty()
                    || (paths.len() == 1
                        && paths.get(&0).is_some_and(|path| {
                            fs::metadata(path).is_ok_and(|meta| meta.len() == 0)
                        }));
                if data.join("INDEX").exists() || !empty_initial {
                    return Err(invalid("existing keeper data has no installed identity"));
                }
                if paths.is_empty() {
                    new_segment(&segment_dir, 0, false)?;
                    paths.insert(0, segment_path(&segment_dir, 0));
                }
                atomic_file(&identity, |file| file.write_all(&keeper.0.to_be_bytes()))?;
            }
            Err(error) => return Err(error),
        }
        let (&latest, path) = paths
            .last_key_value()
            .expect("installed keeper has a segment");
        let (first, index, mut states) = match Checkpoint::load(data)? {
            Some((first, index, states)) => {
                // Also finish namespace changes left visible by an interrupted cleanup.
                sync_directory(data)?;
                (first, index, states)
            }
            None => (0, Checkpoint::default(), HashMap::new()),
        };
        if !paths.contains_key(&first) {
            return Err(invalid("keeper checkpoint does not match its WAL"));
        }
        let mut dirty = HashSet::new();
        let mut fragments = HashMap::new();
        let mut uncheckpointed = 0;
        for (expected, (&seq, segment)) in (first..).zip(paths.range(first..)) {
            if seq != expected {
                return Err(invalid("missing keeper WAL segment"));
            }
            uncheckpointed += replay(
                segment,
                seq == latest,
                keeper,
                &mut states,
                &mut dirty,
                &mut fragments,
            )?;
        }
        let file = OpenOptions::new().append(true).open(path)?;
        let bytes = file.metadata()?.len();
        let bootstrap = !dirty.is_empty()
            || paths.len() > 1
            || bytes != 0
            || data.join("INDEX.tmp").exists()
            || index.has_orphan_packs(data)?;
        let mut wal = Self {
            _lock: lock,
            segments: segment_dir,
            root: data.to_path_buf(),
            file,
            sequence: latest,
            bytes,
            uncheckpointed,
            index: Some(index),
            bootstrap,
            dirty,
            reader: ExtentReader::default(),
            rotation: None,
            #[cfg(test)]
            rotation_gate: None,
            #[cfg(test)]
            rounds: Vec::new(),
            #[cfg(test)]
            segment_bytes: SEGMENT_BYTES,
            #[cfg(test)]
            fail_sync: false,
            #[cfg(test)]
            retain_unsynced: None,
        };
        if bytes != 0 || !fragments.is_empty() {
            // Incomplete entries from a previous boot must never join a new entry.
            wal.open_next_segment(false)?;
        }
        Ok((wal, states))
    }

    pub fn remaining(&self) -> usize {
        #[cfg(not(test))]
        let limit = SEGMENT_BYTES;
        #[cfg(test)]
        let limit = self.segment_bytes;
        limit.saturating_sub(self.bytes) as usize
    }

    pub fn roll_segment(&mut self) -> io::Result<()> {
        self.open_next_segment(true).map(|_| ())
    }

    pub fn write_round(&mut self, buffer: &[u8]) -> io::Result<()> {
        if buffer.is_empty() {
            return Ok(());
        }
        debug_assert!(buffer.len() <= self.remaining());
        self.file.write_all(buffer)?;
        #[cfg(test)]
        if let Some(retain) = self.retain_unsynced.take() {
            let retained = retain.min(buffer.len() - 1);
            self.file.set_len(self.bytes + retained as u64)?;
            return Err(io::Error::other("simulated crash before WAL sync"));
        }
        #[cfg(test)]
        if self.fail_sync {
            return Err(io::Error::other("injected sync failure"));
        }
        sync_file(&self.file)?;
        self.bytes += buffer.len() as u64;
        self.uncheckpointed += buffer.len() as u64;
        #[cfg(test)]
        self.rounds.push(buffer.len());
        Ok(())
    }

    pub fn rotating(&self) -> bool {
        self.rotation.is_some()
    }

    pub async fn rotation_ready(&mut self) {
        if let Some(rotation) = &mut self.rotation {
            let _ = (&mut rotation.ready).await;
        } else {
            std::future::pending::<()>().await;
        }
    }

    /// Capture a boundary between complete admissions. The worker writes the packs
    /// and index, moves the records it copied, and unlinks the covered files.
    pub fn start_rotation(
        &mut self,
        states: &HashMap<StreamId, Stream>,
        delete: bool,
    ) -> io::Result<()> {
        let mut index = self.index.take().expect("one checkpoint at a time");
        let dirty = std::mem::take(&mut self.dirty);
        let rewrite = delete
            || index.compaction_due()
            || dirty.iter().any(|id| states[id].deleted);
        let snapshots = dirty
            .into_iter()
            .map(|id| Snapshot::of(id, &states[&id]))
            .collect();
        // When startup already switched segments, its empty WAL can be the boundary.
        let next = if self.bytes == 0 && !(rewrite && index.references(self.sequence)) {
            self.sequence
        } else {
            self.open_next_segment(false)?
        };
        let root = self.root.clone();
        let segment_dir = self.segments.clone();
        let (done, ready) = tokio::sync::oneshot::channel();
        #[cfg(test)]
        let gate = self.rotation_gate.take();
        let worker = std::thread::Builder::new()
            .name("stream-keeper-checkpoint".into())
            .spawn(move || {
                #[cfg(test)]
                if let Some(gate) = gate {
                    let _ = gate.recv();
                }
                let result = (|| {
                    index.write(&root, next, snapshots, rewrite)?;
                    retire_segments(&segment_dir, next)?;
                    #[cfg(test)]
                    {
                        index.syncs = super::durability::syncs();
                    }
                    Ok(index)
                })();
                let _ = done.send(());
                result
            })?;
        self.rotation = Some(Rotation {
            worker,
            ready,
            covered: self.uncheckpointed,
        });
        self.bootstrap = false;
        Ok(())
    }

    pub fn rotation_finished(&self) -> bool {
        self.rotation
            .as_ref()
            .is_some_and(|rotation| rotation.worker.is_finished())
    }

    pub fn finish_rotation(&mut self) -> io::Result<()> {
        let rotation = self.rotation.take().expect("checkpoint in progress");
        self.index = Some(
            rotation
                .worker
                .join()
                .map_err(|_| io::Error::other("keeper checkpoint worker panicked"))??,
        );
        self.uncheckpointed -= rotation.covered;
        self.reader = ExtentReader::default();
        Ok(())
    }

    fn open_next_segment(&mut self, continuation: bool) -> io::Result<u64> {
        let next = self
            .sequence
            .checked_add(1)
            .ok_or_else(|| invalid("keeper segment sequence exhausted"))?;
        (self.file, self.bytes) = new_segment(&self.segments, next, continuation)?;
        self.sequence = next;
        self.uncheckpointed += self.bytes;
        Ok(next)
    }

    #[cfg(test)]
    pub fn segment(&self) -> PathBuf {
        segment_path(&self.segments, self.sequence)
    }

    #[cfg(test)]
    pub fn rotation_syncs(&self) -> usize {
        self.index.as_ref().unwrap().syncs
    }

    #[cfg(test)]
    pub fn rotate(&mut self, states: &HashMap<StreamId, Stream>) -> io::Result<()> {
        if self.rotating() {
            self.finish_rotation()?;
        }
        self.start_rotation(states, false)?;
        self.finish_rotation()
    }
}

fn retire_segments(dir: &Path, next: u64) -> io::Result<()> {
    let paths = segments(dir)?;
    if paths.range(..next).next().is_some() {
        for (_, path) in paths.range(..next) {
            fs::remove_file(path)?;
        }
        sync_directory(dir)?;
    }
    Ok(())
}

impl Drop for Wal {
    fn drop(&mut self) {
        // Hold the directory lock until its checkpoint worker stops using the files.
        if let Some(rotation) = self.rotation.take() {
            let _ = rotation.worker.join();
        }
    }
}

struct Rotation {
    worker: std::thread::JoinHandle<io::Result<Checkpoint>>,
    ready: tokio::sync::oneshot::Receiver<()>,
    covered: u64,
}

fn replay(
    path: &Path,
    tail: bool,
    keeper: KeeperId,
    states: &mut HashMap<StreamId, Stream>,
    dirty: &mut HashSet<StreamId>,
    fragments: &mut HashMap<StreamId, BytesMut>,
) -> io::Result<u64> {
    let file = File::open(path)?;
    let length = file.metadata()?.len();
    let mut input = BufReader::new(file);
    let mut position = 0;
    if length == 0 {
        fragments.clear();
    }
    while let Some(body) = read_frame(
        &mut input,
        length - position,
        MAX_ENTRY_BYTES + FRAME_OVERHEAD,
    )? {
        let at_start = position == 0;
        position += FRAME_HEADER_BYTES as u64 + body.len() as u64;
        let (stream, flags, payload) = wal_bytes::decode_fragment(&body)
            .ok_or_else(|| invalid("invalid keeper WAL fragment"))?;
        let id = StreamId(stream);
        let payload = body.slice_ref(payload);
        if flags == CONTINUED {
            if at_start {
                continue;
            }
            return Err(invalid("invalid keeper WAL fragment"));
        }
        if at_start {
            fragments.clear();
        }
        let body = if flags == START | END {
            if fragments.contains_key(&id) {
                return Err(invalid("overlapping keeper WAL entries"));
            }
            payload
        } else if flags == START {
            if fragments
                .insert(id, BytesMut::from(payload.as_ref()))
                .is_some()
            {
                return Err(invalid("overlapping keeper WAL entries"));
            }
            continue;
        } else {
            let fragment = fragments
                .get_mut(&id)
                .ok_or_else(|| invalid("keeper WAL fragment without start"))?;
            if fragment.len() + payload.len() > MAX_ENTRY_BYTES {
                return Err(invalid("oversized keeper WAL entry"));
            }
            fragment.put_slice(&payload);
            if flags != END {
                continue;
            }
            fragments.remove(&id).expect("finished entry").freeze()
        };
        let (identity, request) =
            wal_bytes::decode_field(&body).ok_or_else(|| invalid("short keeper WAL entry"))?;
        let identity = decode_identity(identity)?;
        let request = codec::decode_request(body.slice_ref(request))?;
        if codec::stream(&request) != id
            || identity.is_some() != matches!(request, Request::Seal { .. })
        {
            return Err(invalid("invalid keeper WAL entry"));
        }
        states
            .entry(id)
            .or_default()
            .apply(keeper, request, identity)?;
        dirty.insert(id);
    }
    if position != length {
        if !tail {
            return Err(invalid("damaged frame before keeper WAL tail"));
        }
        let file = OpenOptions::new().write(true).open(path)?;
        file.set_len(position)?;
        sync_file(&file)?;
    }
    Ok(position)
}
