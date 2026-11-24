//! A shared append-only segment, drained into immutable extents for streams it touched.
//! A checkpoint is published after its extent and before the segment can be removed.
//! Replay skips each stream's checkpointed prefix independently.
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fs::{self, File, OpenOptions},
    io::{self, BufReader, BufWriter, Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
    sync::Arc,
};

use bytes::{Buf, BufMut, Bytes, BytesMut};
use fs2::FileExt;

use super::{
    durability::{sync_directory, sync_file},
    rules::charge,
    state::{Extent, ExtentReader, Payload, Record, Stream},
};
use crate::stream::{
    codec::{self, MAX_FRAME_BYTES, invalid},
    wire::{Epoch, Identity, KeeperId, Lsn, Request, StreamId, StreamView},
};

mod legacy;

pub(super) const SEGMENT_BYTES: u64 = 64 * 1024 * 1024;
pub(super) const FRAME_OVERHEAD: usize = 8 + 16 + 1;
pub(super) const MAX_IDENTITY_BYTES: usize = 4096;
const MAX_ENTRY_BYTES: usize = MAX_FRAME_BYTES + 8 + MAX_IDENTITY_BYTES;
// The legacy format starts with a bounded identity length at these offsets.
const PROTOBUF: u32 = u32::MAX;
const START: u8 = 1;
const END: u8 = 2;

pub(super) struct Wal {
    _lock: File,
    segments: PathBuf,
    streams: PathBuf,
    file: File,
    sequence: u64,
    pub bytes: u64,
    pub dirty: HashSet<StreamId>,
    pub reader: ExtentReader,
    #[cfg(test)]
    pub rounds: Vec<usize>,
    #[cfg(test)]
    pub fail_sync: bool,
}

pub(super) fn entry(request: &Request, identity: Option<&Identity>) -> io::Result<Bytes> {
    let body = codec::encode_request(request)?;
    let identity = identity.map_or("", Identity::as_str).as_bytes();
    let mut entry = BytesMut::with_capacity(8 + identity.len() + body.len());
    entry.put_u32(PROTOBUF);
    put_bytes(&mut entry, identity)?;
    entry.put_slice(&body);
    Ok(entry.freeze())
}

fn put_count(out: &mut BytesMut, len: usize) -> io::Result<()> {
    out.put_u32(
        len.try_into()
            .map_err(|_| invalid("keeper collection too large"))?,
    );
    Ok(())
}

fn put_bytes(out: &mut BytesMut, bytes: &[u8]) -> io::Result<()> {
    put_count(out, bytes.len())?;
    out.put_slice(bytes);
    Ok(())
}

fn decode_identity(uri: Bytes) -> io::Result<Option<Identity>> {
    if uri.is_empty() {
        return Ok(None);
    }
    if uri.len() > MAX_IDENTITY_BYTES {
        return Err(invalid("oversized WAL identity"));
    }
    let uri = std::str::from_utf8(&uri).map_err(|_| invalid("invalid WAL identity"))?;
    Ok(Some(Identity::from(uri)))
}

pub(super) fn fragment(
    buffer: &mut BytesMut,
    stream: StreamId,
    first: bool,
    last: bool,
    bytes: &[u8],
) {
    let at = buffer.len();
    buffer.put_u32((FRAME_OVERHEAD - 8 + bytes.len()) as u32);
    buffer.put_u32(0);
    buffer.put_u128(stream.0);
    buffer.put_u8(u8::from(first) * START | u8::from(last) * END);
    buffer.put_slice(bytes);
    let crc = crc32fast::hash(&buffer[at + 8..]);
    buffer[at + 4..at + 8].copy_from_slice(&crc.to_be_bytes());
}

fn read_frame(reader: &mut impl Read, remaining: u64, max: usize) -> io::Result<Option<Bytes>> {
    if remaining < 8 {
        return Ok(None);
    }
    let mut header = [0; 8];
    reader.read_exact(&mut header)?;
    let mut header = &header[..];
    let len = header.get_u32() as usize;
    let crc = header.get_u32();
    if len > max || len as u64 > remaining - 8 {
        return Ok(None);
    }
    let mut bytes = vec![0; len];
    reader.read_exact(&mut bytes)?;
    Ok((crc32fast::hash(&bytes) == crc).then(|| Bytes::from(bytes)))
}

fn atomic_file(
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

fn extent_path(dir: &Path, sequence: u64) -> PathBuf {
    dir.join(format!("{sequence:020}.extent"))
}

fn sequence(path: &Path) -> io::Result<u64> {
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

fn new_segment(dir: &Path, sequence: u64) -> io::Result<File> {
    let file = OpenOptions::new()
        .create_new(true)
        .append(true)
        .open(segment_path(dir, sequence))?;
    sync_file(&file)?;
    sync_directory(dir)?;
    Ok(file)
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
        let streams = data.join("streams");
        let segment_dir = data.join("segments");
        directories(&streams)?;
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
                if fs::read_dir(&streams)?.next().is_some() || !empty_initial {
                    return Err(invalid("existing keeper data has no installed identity"));
                }
                if paths.is_empty() {
                    new_segment(&segment_dir, 0)?;
                    paths.insert(0, segment_path(&segment_dir, 0));
                }
                atomic_file(&identity, |file| file.write_all(&keeper.0.to_be_bytes()))?;
            }
            Err(error) => return Err(error),
        }
        let mut states = load_streams(&streams)?;

        let (&latest, path) = paths
            .last_key_value()
            .expect("installed keeper has a segment");
        if states
            .values()
            .any(|state| state.checkpoint.is_some_and(|seq| seq > latest))
        {
            return Err(invalid("stream checkpoint ahead of keeper WAL"));
        }
        let mut dirty = HashSet::new();
        for (&sequence, segment) in &paths {
            replay(
                segment,
                sequence,
                sequence == latest,
                keeper,
                &mut states,
                &mut dirty,
            )?;
        }
        let file = OpenOptions::new().append(true).open(path)?;
        let bytes = file.metadata()?.len();
        let mut wal = Self {
            _lock: lock,
            segments: segment_dir,
            streams,
            file,
            sequence: latest,
            bytes,
            dirty,
            reader: ExtentReader::default(),
            #[cfg(test)]
            rounds: Vec::new(),
            #[cfg(test)]
            fail_sync: false,
        };
        // Start on a clean segment so incomplete fragments from this boot need no replay state.
        if bytes != 0 || paths.len() > 1 || !wal.dirty.is_empty() {
            wal.rotate(&mut states)?;
        }
        Ok((wal, states))
    }

    pub fn write_round(&mut self, buffer: &[u8]) -> io::Result<()> {
        if buffer.is_empty() {
            return Ok(());
        }
        self.file.write_all(buffer)?;
        #[cfg(test)]
        if self.fail_sync {
            return Err(io::Error::other("injected sync failure"));
        }
        sync_file(&self.file)?;
        self.bytes += buffer.len() as u64;
        #[cfg(test)]
        self.rounds.push(buffer.len());
        Ok(())
    }

    pub fn rotate(&mut self, states: &mut HashMap<StreamId, Stream>) -> io::Result<()> {
        self.reader = ExtentReader::default();
        for stream in std::mem::take(&mut self.dirty) {
            let state = states.get_mut(&stream).expect("dirty stream has state");
            self.checkpoint_stream(stream, state)?;
        }
        let next = self
            .sequence
            .checked_add(1)
            .ok_or_else(|| invalid("keeper segment sequence exhausted"))?;
        self.file = new_segment(&self.segments, next)?;
        self.sequence = next;
        self.bytes = 0;
        for (_, path) in segments(&self.segments)?.range(..next) {
            fs::remove_file(path)?;
        }
        sync_directory(&self.segments)
    }

    pub fn checkpoint_stream(&self, stream: StreamId, state: &mut Stream) -> io::Result<()> {
        let dir = self.streams.join(format!("{:032x}", stream.0));
        directories(&dir)?;
        checkpoint(&dir, self.sequence, state)
    }
}

fn replay(
    path: &Path,
    sequence: u64,
    tail: bool,
    keeper: KeeperId,
    states: &mut HashMap<StreamId, Stream>,
    dirty: &mut HashSet<StreamId>,
) -> io::Result<()> {
    let file = File::open(path)?;
    let length = file.metadata()?.len();
    let mut input = BufReader::new(file);
    let mut position = 0;
    let mut fragments = HashMap::<StreamId, BytesMut>::new();
    while let Some(body) = read_frame(
        &mut input,
        length - position,
        MAX_ENTRY_BYTES + FRAME_OVERHEAD,
    )? {
        position += 8 + body.len() as u64;
        let mut frame = Decoder(body);
        let id = StreamId(frame.u128()?);
        let flags = frame.u8()?;
        if flags > START | END || frame.0.is_empty() {
            return Err(invalid("invalid keeper WAL fragment"));
        }
        if states
            .get(&id)
            .and_then(|stream| stream.checkpoint)
            .is_some_and(|last| sequence <= last)
        {
            continue;
        }
        let body = if flags == START | END {
            if fragments.contains_key(&id) {
                return Err(invalid("overlapping keeper WAL entries"));
            }
            frame.0
        } else if flags == START {
            if fragments
                .insert(id, BytesMut::from(frame.0.as_ref()))
                .is_some()
            {
                return Err(invalid("overlapping keeper WAL entries"));
            }
            continue;
        } else {
            let fragment = fragments
                .get_mut(&id)
                .ok_or_else(|| invalid("keeper WAL fragment without start"))?;
            if fragment.len() + frame.0.len() > MAX_ENTRY_BYTES {
                return Err(invalid("oversized keeper WAL entry"));
            }
            fragment.put_slice(&frame.0);
            if flags != END {
                continue;
            }
            fragments.remove(&id).expect("finished entry").freeze()
        };
        let mut entry = Decoder(body);
        let protobuf = entry.take_format();
        let identity = decode_identity(entry.bytes()?)?;
        let request = if protobuf {
            codec::decode_request(entry.0)?
        } else {
            entry.legacy_request()?
        };
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
    Ok(())
}

#[derive(Clone, Copy)]
struct Span {
    sequence: u64,
    first: Lsn,
    last: Lsn,
}

fn checkpoint(dir: &Path, sequence: u64, state: &mut Stream) -> io::Result<()> {
    let mut spans: Vec<Span> = Vec::new();
    let mut offsets = Vec::new();
    let first = state
        .records
        .iter()
        .position(|record| matches!(record.payload, Payload::Pending(_)));
    if let Some(first) = first {
        let path = extent_path(dir, sequence);
        atomic_file(&path, |file| {
            let mut offset = 0;
            for (index, record) in state.records.iter().enumerate().skip(first) {
                let Payload::Pending(payload) = &record.payload else {
                    return Err(invalid("pending records are not a suffix"));
                };
                let lsn = state.view.floor.0 + index as u64;
                let len = payload.len() as u32;
                let crc = crc32fast::hash(payload);
                file.write_all(&lsn.to_be_bytes())?;
                file.write_all(&record.epoch.0.to_be_bytes())?;
                file.write_all(&len.to_be_bytes())?;
                file.write_all(&crc.to_be_bytes())?;
                file.write_all(payload)?;
                offsets.push((offset + 24, len, crc));
                offset += 24 + u64::from(len);
            }
            Ok(())
        })?;
        let extent = Arc::new(Extent { sequence, path });
        for (record, (offset, len, crc)) in state.records.iter_mut().skip(first).zip(offsets) {
            record.payload = Payload::Extent {
                extent: Arc::clone(&extent),
                offset,
                len,
                crc,
            };
        }
    }
    for (index, record) in state.records.iter().enumerate() {
        let Payload::Extent { extent, .. } = &record.payload else {
            unreachable!()
        };
        let lsn = Lsn(state.view.floor.0 + index as u64);
        match spans.last_mut() {
            Some(span) if span.sequence == extent.sequence => span.last = lsn,
            _ => spans.push(Span {
                sequence: extent.sequence,
                first: lsn,
                last: lsn,
            }),
        }
    }
    let mut body = BytesMut::new();
    body.put_u64(sequence);
    body.put_u8(u8::from(state.deleted));
    body.put_u32(PROTOBUF);
    put_bytes(&mut body, &codec::encode_checkpoint_view(&state.view)?)?;
    put_count(&mut body, spans.len())?;
    for span in &spans {
        body.put_u64(span.sequence);
        body.put_u64(span.first.0);
        body.put_u64(span.last.0);
    }
    atomic_file(&dir.join("state"), |file| {
        let length: u32 = body
            .len()
            .try_into()
            .map_err(|_| invalid("stream checkpoint too large"))?;
        file.write_all(&length.to_be_bytes())?;
        file.write_all(&crc32fast::hash(&body).to_be_bytes())?;
        file.write_all(&body)
    })?;
    state.checkpoint = Some(sequence);
    clean_extents(dir, &spans)
}

fn clean_extents(dir: &Path, live: &[Span]) -> io::Result<()> {
    let live: HashSet<_> = live.iter().map(|span| span.sequence).collect();
    let mut removed = false;
    for entry in fs::read_dir(dir)? {
        let path = entry?.path();
        if path.extension().is_some_and(|ext| ext == "tmp")
            || (path.extension().is_some_and(|ext| ext == "extent")
                && !live.contains(&sequence(&path)?))
        {
            fs::remove_file(path)?;
            removed = true;
        }
    }
    if removed {
        sync_directory(dir)?;
    }
    Ok(())
}

fn load_streams(root: &Path) -> io::Result<HashMap<StreamId, Stream>> {
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
                clean_extents(&dir, &[])?;
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
        let view = if input.take_format() {
            codec::decode_checkpoint_view(input.bytes()?)?
        } else {
            let identity = decode_identity(input.bytes()?)?;
            input.legacy_view(identity)?
        };
        let mut state = Stream {
            checkpoint,
            deleted,
            view,
            ..Stream::default()
        };
        let spans = (0..input.count(24)?)
            .map(|_| {
                Ok(Span {
                    sequence: input.u64()?,
                    first: Lsn(input.u64()?),
                    last: Lsn(input.u64()?),
                })
            })
            .collect::<io::Result<Vec<_>>>()?;
        input.finish()?;
        let mut next = state.view.floor.0;
        for span in &spans {
            if span.first.0 != next || span.last < span.first || span.last > state.view.tail {
                return Err(invalid("noncontiguous stream checkpoint extents"));
            }
            read_extent(&dir, *span, &mut state)?;
            next = span.last.0 + 1;
        }
        if next != state.view.tail.0 + 1 {
            return Err(invalid("stream checkpoint is missing records"));
        }
        clean_extents(&dir, &spans)?;
        states.insert(StreamId(id), state);
    }
    Ok(states)
}

fn read_extent(dir: &Path, span: Span, state: &mut Stream) -> io::Result<()> {
    let path = extent_path(dir, span.sequence);
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
            state.records.push_back(Record {
                epoch,
                payload: Payload::Extent {
                    extent: Arc::clone(&extent),
                    offset,
                    len,
                    crc,
                },
            });
            state.bytes += charge_len(len);
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

fn charge_len(len: u32) -> u64 {
    if len == 0 {
        charge(&[])
    } else {
        u64::from(len)
    }
}

struct Decoder(Bytes);

impl Decoder {
    fn take_format(&mut self) -> bool {
        if self.0.get(..4) == Some(&PROTOBUF.to_be_bytes()) {
            self.0.advance(4);
            true
        } else {
            false
        }
    }

    fn take(&mut self, length: usize) -> io::Result<Bytes> {
        if self.0.len() < length {
            return Err(invalid("short keeper message"));
        }
        Ok(self.0.split_to(length))
    }

    fn u8(&mut self) -> io::Result<u8> {
        Ok(self.take(1)?.get_u8())
    }

    fn u32(&mut self) -> io::Result<u32> {
        Ok(self.take(4)?.get_u32())
    }

    fn u64(&mut self) -> io::Result<u64> {
        Ok(self.take(8)?.get_u64())
    }

    fn u128(&mut self) -> io::Result<u128> {
        Ok(self.take(16)?.get_u128())
    }

    fn boolean(&mut self) -> io::Result<bool> {
        match self.u8()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(invalid("invalid keeper boolean")),
        }
    }

    fn bytes(&mut self) -> io::Result<Bytes> {
        let count = self.u32()? as usize;
        self.take(count)
    }

    fn count(&mut self, element_minimum: usize) -> io::Result<usize> {
        let count = self.u32()? as usize;
        if count > self.0.len() / element_minimum {
            return Err(invalid("short keeper collection"));
        }
        Ok(count)
    }

    fn finish(self) -> io::Result<()> {
        if self.0.is_empty() {
            Ok(())
        } else {
            Err(invalid("trailing keeper message bytes"))
        }
    }
}
