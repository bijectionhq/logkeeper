//! Immutable objects shared by WAL indexes, snapshots and exact read handles.
//!
//! An object is either a standalone file (snapshot pages, and entries written
//! before the segmented WAL) or a slice of an append-only WAL segment. A
//! segment is deleted once no slice holds it, it lies before the published
//! checkpoint, and no quarantined scope ever wrote to it.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs::{self, File, OpenOptions, ReadDir},
    io::{self, Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
    sync::{Arc, Weak},
};

use journal_contract::StreamId;
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use uuid::Uuid;

use super::segment;
use crate::stream::{
    consensus::invalid,
    keeper::durability::{sync_directory, sync_file},
};

const MAX_OBJECT_BYTES: u64 = 5 * 1024 * 1024;
const REAP_ITEMS: usize = 64;
const MAX_PENDING_REAP: usize = 4096;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(in crate::stream::consensus) struct Key {
    pub scope: StreamId,
    pub id: Uuid,
    pub len: u64,
    pub digest: [u8; 32],
}

impl Key {
    fn name(self) -> String {
        format!("{:032x}-{}", self.scope.0, self.id)
    }
}

/// Exact bytes of one entry inside a WAL segment.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(in crate::stream::consensus) struct Location {
    pub scope: StreamId,
    pub segment: u64,
    pub offset: u64,
    pub len: u64,
    pub crc: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(in crate::stream::consensus) enum Reference {
    Object(Key),
    Segment(Location),
}

#[derive(Clone)]
pub(super) struct Objects(Arc<Inner>);

struct Inner {
    root: PathBuf,
    segments: PathBuf,
    state: Mutex<State>,
}

#[derive(Default)]
struct State {
    live: BTreeMap<(StreamId, Uuid), Weak<Object>>,
    dead: VecDeque<(StreamId, Uuid)>,
    protected: BTreeSet<StreamId>,
    ready: bool,
    scan: Option<ReadDir>,
    segments: Segments,
}

#[derive(Default)]
struct Segments {
    live: BTreeMap<u64, Weak<Segment>>,
    dead: VecDeque<u64>,
    scopes: BTreeMap<u64, BTreeSet<StreamId>>,
    // Recovery replays segments from here on.
    floor: u64,
    scan: Option<ReadDir>,
}

#[derive(Debug)]
pub(in crate::stream::consensus) struct Segment {
    id: u64,
    file: File,
    #[cfg(test)]
    path: PathBuf,
    store: Weak<Inner>,
}

#[derive(Debug)]
pub(in crate::stream::consensus) struct Object(Body);

#[derive(Debug)]
enum Body {
    File {
        key: Key,
        store: Weak<Inner>,
        path: PathBuf,
    },
    Slice {
        segment: Arc<Segment>,
        location: Location,
    },
}

impl Objects {
    pub fn open(data: &Path) -> io::Result<Self> {
        let root = data.join("objects");
        let segments = data.join(segment::DIRECTORY);
        fs::create_dir_all(&root)?;
        fs::create_dir_all(&segments)?;
        sync_directory(data)?;
        Ok(Self(Arc::new(Inner {
            root,
            segments,
            state: Mutex::new(State::default()),
        })))
    }

    pub fn segment_directory(&self) -> &Path {
        &self.0.segments
    }

    pub fn publish_files(&self) -> io::Result<()> {
        sync_directory(&self.0.root)
    }

    pub fn put(&self, scope: StreamId, bytes: &[u8]) -> io::Result<Arc<Object>> {
        let key = Key {
            scope,
            id: Uuid::new_v4(),
            len: bytes.len() as u64,
            digest: Sha256::digest(bytes).into(),
        };
        if key.len > MAX_OBJECT_BYTES {
            return Err(invalid("immutable object exceeds its size limit"));
        }
        let object = self.pin(key)?;
        let mut file = OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(self.0.root.join(key.name()))?;
        file.write_all(bytes)?;
        sync_file(&file)?;
        Ok(object)
    }

    pub fn pin(&self, key: Key) -> io::Result<Arc<Object>> {
        if key.len > MAX_OBJECT_BYTES || key.id.is_nil() {
            return Err(invalid("invalid immutable object reference"));
        }
        let mut state = self.0.state.lock();
        if let Some(found) = state.live.get(&(key.scope, key.id)).and_then(Weak::upgrade) {
            drop(state);
            if found.key() != Some(key) {
                return Err(invalid("immutable object reference changed"));
            }
            return Ok(found);
        }
        let object = Arc::new(Object(Body::File {
            key,
            store: Arc::downgrade(&self.0),
            path: self.0.root.join(key.name()),
        }));
        state
            .live
            .insert((key.scope, key.id), Arc::downgrade(&object));
        Ok(object)
    }

    pub fn resolve(&self, reference: Reference) -> io::Result<Arc<Object>> {
        match reference {
            Reference::Object(key) => self.pin(key),
            Reference::Segment(location) => self.slice(location),
        }
    }

    pub fn slice(&self, location: Location) -> io::Result<Arc<Object>> {
        if location.len == 0
            || location.len > segment::MAX_FRAME
            || location.offset < segment::HEADER + segment::FRAME_HEADER
            || location.offset.checked_add(location.len).is_none()
        {
            return Err(invalid("invalid WAL segment reference"));
        }
        let mut state = self.0.state.lock();
        let segment = self.open_segment(&mut state, location.segment)?;
        state
            .segments
            .scopes
            .entry(location.segment)
            .or_default()
            .insert(location.scope);
        Ok(Arc::new(Object(Body::Slice { segment, location })))
    }

    fn open_segment(&self, state: &mut State, id: u64) -> io::Result<Arc<Segment>> {
        if let Some(found) = state.segments.live.get(&id).and_then(Weak::upgrade) {
            return Ok(found);
        }
        let path = self.0.segments.join(segment::name(id));
        let segment = Arc::new(Segment {
            id,
            file: File::open(&path)?,
            #[cfg(test)]
            path,
            store: Arc::downgrade(&self.0),
        });
        state.segments.live.insert(id, Arc::downgrade(&segment));
        Ok(segment)
    }

    /// Segments before `floor` hold only bytes that slices may still need.
    pub fn set_floor(&self, floor: u64) {
        self.0.state.lock().segments.floor = floor;
    }

    pub fn segment_scopes(&self) -> BTreeMap<u64, BTreeSet<StreamId>> {
        self.0.state.lock().segments.scopes.clone()
    }

    pub fn restore_segment_scopes(&self, scopes: BTreeMap<u64, BTreeSet<StreamId>>) {
        let mut state = self.0.state.lock();
        for (id, scopes) in scopes {
            state.segments.scopes.entry(id).or_default().extend(scopes);
        }
    }

    pub fn protect(&self, scope: StreamId) {
        self.0.state.lock().protected.insert(scope);
    }

    pub fn enable_reaping(&self) {
        self.0.state.lock().ready = true;
    }

    pub fn disable_reaping(&self) {
        self.0.state.lock().ready = false;
    }

    pub fn reap(&self) -> io::Result<()> {
        let mut state = self.0.state.lock();
        if !state.ready {
            return Ok(());
        }
        let mut removed = false;
        for _ in 0..REAP_ITEMS {
            let candidate = if let Some(candidate) = state.dead.pop_front() {
                Some(candidate)
            } else {
                if state.scan.is_none() {
                    state.scan = Some(fs::read_dir(&self.0.root)?);
                }
                let Some(item) = state.scan.as_mut().unwrap().next() else {
                    state.scan = None;
                    break;
                };
                let name = item?.file_name();
                name.to_str().and_then(|name| {
                    let (scope, id) = name.split_once('-')?;
                    Some((
                        StreamId(u128::from_str_radix(scope, 16).ok()?),
                        Uuid::parse_str(id).ok()?,
                    ))
                })
            };
            let Some((scope, id)) = candidate else {
                continue;
            };
            // Hold the table while unlinking so a late pin cannot resurrect
            // a name already proven unreachable.
            if state.protected.contains(&scope)
                || state
                    .live
                    .get(&(scope, id))
                    .is_some_and(|weak| weak.strong_count() != 0)
            {
                continue;
            }
            match fs::remove_file(self.0.root.join(format!("{:032x}-{id}", scope.0))) {
                Ok(()) => removed = true,
                Err(error) if error.kind() == io::ErrorKind::NotFound => (),
                Err(error) => return Err(error),
            }
            state.live.remove(&(scope, id));
        }
        if removed {
            sync_directory(&self.0.root)?;
        }
        self.reap_segments(&mut state)
    }

    fn reap_segments(&self, state: &mut State) -> io::Result<()> {
        let mut removed = false;
        for _ in 0..REAP_ITEMS {
            let candidate = if let Some(candidate) = state.segments.dead.pop_front() {
                Some(candidate)
            } else {
                if state.segments.scan.is_none() {
                    state.segments.scan = Some(fs::read_dir(&self.0.segments)?);
                }
                let Some(item) = state.segments.scan.as_mut().unwrap().next() else {
                    state.segments.scan = None;
                    break;
                };
                item?.file_name().to_str().and_then(segment::parse)
            };
            let Some(id) = candidate else {
                continue;
            };
            let segments = &state.segments;
            if id >= segments.floor
                || segments
                    .live
                    .get(&id)
                    .is_some_and(|weak| weak.strong_count() != 0)
                || segments
                    .scopes
                    .get(&id)
                    .is_some_and(|scopes| !scopes.is_disjoint(&state.protected))
            {
                continue;
            }
            match fs::remove_file(self.0.segments.join(segment::name(id))) {
                Ok(()) => removed = true,
                Err(error) if error.kind() == io::ErrorKind::NotFound => (),
                Err(error) => return Err(error),
            }
            state.segments.live.remove(&id);
            state.segments.scopes.remove(&id);
        }
        if removed {
            sync_directory(&self.0.segments)?;
        }
        Ok(())
    }
}

impl Drop for Segment {
    fn drop(&mut self) {
        if let Some(store) = self.store.upgrade() {
            let mut state = store.state.lock();
            let segments = &mut state.segments;
            if segments
                .live
                .get(&self.id)
                .is_some_and(|segment| segment.strong_count() == 0)
            {
                segments.live.remove(&self.id);
            }
            if segments.dead.len() < MAX_PENDING_REAP {
                segments.dead.push_back(self.id);
            }
        }
    }
}

impl Object {
    pub fn key(&self) -> Option<Key> {
        match &self.0 {
            Body::File { key, .. } => Some(*key),
            Body::Slice { .. } => None,
        }
    }

    pub fn reference(&self) -> Reference {
        match &self.0 {
            Body::File { key, .. } => Reference::Object(*key),
            Body::Slice { location, .. } => Reference::Segment(*location),
        }
    }

    pub fn len(&self) -> u64 {
        match &self.0 {
            Body::File { key, .. } => key.len,
            Body::Slice { location, .. } => location.len,
        }
    }

    #[cfg(test)]
    pub fn path(&self) -> &Path {
        match &self.0 {
            Body::File { path, .. } => path,
            Body::Slice { segment, .. } => &segment.path,
        }
    }

    /// Where the object's first byte sits in the file at `path`.
    #[cfg(test)]
    pub fn position(&self) -> u64 {
        match &self.0 {
            Body::File { .. } => 0,
            Body::Slice { location, .. } => location.offset,
        }
    }

    pub fn read(&self) -> io::Result<Vec<u8>> {
        match &self.0 {
            Body::File { key, path, .. } => {
                let mut bytes = Vec::new();
                File::open(path)?
                    .take(key.len + 1)
                    .read_to_end(&mut bytes)?;
                if bytes.len() as u64 != key.len
                    || <[u8; 32]>::from(Sha256::digest(&bytes)) != key.digest
                {
                    return Err(invalid("immutable object failed its selected checksum"));
                }
                Ok(bytes)
            }
            Body::Slice { segment, location } => {
                let mut bytes = vec![0; location.len as usize];
                segment::read_at(&segment.file, location.offset, &mut bytes)?;
                if crc32fast::hash(&bytes) != location.crc {
                    return Err(invalid("WAL segment slice failed its checksum"));
                }
                Ok(bytes)
            }
        }
    }

    pub fn read_range(&self, offset: u64, buf: &mut [u8]) -> io::Result<()> {
        if offset
            .checked_add(buf.len() as u64)
            .is_none_or(|end| end > self.len())
        {
            return Err(invalid("extent range exceeds its immutable object"));
        }
        match &self.0 {
            Body::File { path, .. } => {
                let mut file = File::open(path)?;
                file.seek(SeekFrom::Start(offset))?;
                file.read_exact(buf)
            }
            Body::Slice { segment, location } => {
                segment::read_at(&segment.file, location.offset + offset, buf)
            }
        }
    }
}

impl Drop for Object {
    fn drop(&mut self) {
        let Body::File { key, store, .. } = &self.0 else {
            return;
        };
        if let Some(store) = store.upgrade() {
            let mut state = store.state.lock();
            if state
                .live
                .get(&(key.scope, key.id))
                .is_some_and(|object| object.strong_count() == 0)
            {
                state.live.remove(&(key.scope, key.id));
            }
            if state.dead.len() < MAX_PENDING_REAP {
                state.dead.push_back((key.scope, key.id));
            }
        }
    }
}
