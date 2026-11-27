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
    sync::{
        Arc, Weak,
        atomic::{AtomicUsize, Ordering as AtomicOrdering},
    },
};

use journal_contract::StreamId;
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use uuid::Uuid;

use super::{
    rules::{self, LiveBytes},
    segment,
};
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
    // Scopes whose standalone objects a closed replica still needs.
    held: BTreeMap<StreamId, usize>,
    ready: bool,
    scan: Option<ReadDir>,
    segments: Segments,
}

#[derive(Default)]
struct Segments {
    live: BTreeMap<u64, Weak<Segment>>,
    dead: VecDeque<u64>,
    scopes: BTreeMap<u64, BTreeSet<StreamId>>,
    // Every live slice, by segment and offset, so two holders of the same
    // bytes share one object and each segment's live bytes are exact.
    slices: BTreeMap<(u64, u64), Weak<Object>>,
    bytes: BTreeMap<u64, LiveBytes>,
    // Segments whose slices moved, kept until each scope that held them
    // selects a snapshot built after the move: until then its selected
    // snapshot may still name them. Numbered so a build knows which moves
    // it saw.
    moved: BTreeMap<StreamId, Vec<(u64, Arc<Segment>)>>,
    moves: u64,
    // Recovery replays segments from here on.
    floor: u64,
    scan: Option<ReadDir>,
}

/// Segments before the published checkpoint by the share of their bytes
/// that slices still hold.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(in crate::stream::consensus) struct Usage {
    /// Below 10%, 25%, 50%, 75%, and the rest.
    pub buckets: [u32; 5],
    pub live: u64,
    pub total: u64,
}

impl Usage {
    const BOUNDS: [u64; 4] = [10, 25, 50, 75];

    fn add(&mut self, live: u64, size: u64) {
        let percent = live.saturating_mul(100) / size.max(1);
        let bucket = Self::BOUNDS
            .iter()
            .position(|bound| percent < *bound)
            .unwrap_or(Self::BOUNDS.len());
        self.buckets[bucket] += 1;
        self.live += live;
        self.total += size;
    }
}

impl std::fmt::Display for Usage {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let [a, b, c, d, e] = self.buckets;
        write!(
            f,
            "<10%={a} <25%={b} <50%={c} <75%={d} rest={e} live={}MiB of {}MiB",
            self.live >> 20,
            self.total >> 20
        )
    }
}

impl Segments {
    fn add(&mut self, location: Location) {
        let usage = self.bytes.entry(location.segment).or_default();
        *usage = usage.add(location.len);
    }

    fn remove(&mut self, location: Location) {
        if let Some(usage) = self.bytes.get_mut(&location.segment) {
            *usage = usage.remove(location.len);
            if usage.slices == 0 {
                self.bytes.remove(&location.segment);
            }
        }
    }
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
pub(in crate::stream::consensus) struct Object(Body, AtomicUsize);

/// The objects a WAL checkpoint names. Each counts its checkpoint holders,
/// so compaction can tell a slice only checkpoints hold, which dies at the
/// next checkpoint, from one a stream still needs.
#[derive(Default)]
pub(in crate::stream::consensus) struct Pins(Vec<Arc<Object>>);

impl From<Vec<Arc<Object>>> for Pins {
    fn from(objects: Vec<Arc<Object>>) -> Self {
        for object in &objects {
            object.1.fetch_add(1, AtomicOrdering::Relaxed);
        }
        Self(objects)
    }
}

impl Drop for Pins {
    fn drop(&mut self) {
        for object in &self.0 {
            object.1.fetch_sub(1, AtomicOrdering::Relaxed);
        }
    }
}

#[derive(Debug)]
enum Body {
    File {
        key: Key,
        store: Weak<Inner>,
        path: PathBuf,
    },
    /// Compaction may move a slice's bytes to a newer segment; every
    /// holder then reads them there.
    Slice(parking_lot::RwLock<At>),
}

#[derive(Debug, Clone)]
struct At {
    segment: Arc<Segment>,
    location: Location,
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

    /// Opens an object handle against a stopped directory without creating
    /// directories or syncing metadata.
    pub fn open_readonly(data: &Path) -> Self {
        Self(Arc::new(Inner {
            root: data.join("objects"),
            segments: data.join(segment::DIRECTORY),
            state: Mutex::new(State::default()),
        }))
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
        let object = Arc::new(Object(
            Body::File {
                key,
                store: Arc::downgrade(&self.0),
                path: self.0.root.join(key.name()),
            },
            AtomicUsize::new(0),
        ));
        state
            .live
            .insert((key.scope, key.id), Arc::downgrade(&object));
        Ok(object)
    }

    pub(super) fn path_for(&self, key: Key) -> io::Result<PathBuf> {
        if key.len > MAX_OBJECT_BYTES || key.id.is_nil() {
            return Err(invalid("invalid immutable object reference"));
        }
        Ok(self.0.root.join(key.name()))
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
        let key = (location.segment, location.offset);
        if let Some(found) = state.segments.slices.get(&key).and_then(Weak::upgrade) {
            drop(state);
            if found.reference() != Reference::Segment(location) {
                return Err(invalid("WAL segment reference changed"));
            }
            return Ok(found);
        }
        let segment = self.open_segment(&mut state, location.segment)?;
        let segments = &mut state.segments;
        segments
            .scopes
            .entry(location.segment)
            .or_default()
            .insert(location.scope);
        segments.add(location);
        let object = Arc::new(Object(
            Body::Slice(parking_lot::RwLock::new(At { segment, location })),
            AtomicUsize::new(0),
        ));
        segments.slices.insert(key, Arc::downgrade(&object));
        Ok(object)
    }

    /// How full the segments before the published checkpoint are with
    /// bytes some slice still holds.
    pub fn usage(&self) -> Usage {
        // A segment upgraded here may lose its last other holder meanwhile,
        // and dropping it takes the table lock: drop them after it.
        let mut upgraded = Vec::new();
        let state = self.0.state.lock();
        let segments = &state.segments;
        let mut usage = Usage::default();
        for (&id, segment) in segments.live.range(..segments.floor) {
            let Some(segment) = segment.upgrade() else {
                continue;
            };
            if let Ok(size) = segment.file.metadata().map(|meta| meta.len()) {
                let live = segments
                    .bytes
                    .get(&id)
                    .map_or(0, |usage| usage.bytes)
                    .min(size);
                usage.add(live, size);
            }
            upgraded.push(segment);
        }
        drop(state);
        drop(upgraded);
        usage
    }

    /// The live bytes some slice holds in segment `id`.
    #[cfg(test)]
    pub fn live_bytes(&self, id: u64) -> u64 {
        self.0
            .state
            .lock()
            .segments
            .bytes
            .get(&id)
            .map_or(0, |usage| usage.bytes)
    }

    /// The segments before the published checkpoint, other than the newest
    /// `keep`, whose live slices hold less than `share` percent of their
    /// bytes and that nothing but those slices holds, least live first.
    pub fn cold_segments(&self, keep: u64, share: u64) -> Vec<u64> {
        let mut upgraded = Vec::new();
        let state = self.0.state.lock();
        let segments = &state.segments;
        let mut cold = Vec::new();
        for (&id, segment) in segments
            .live
            .range(..rules::cold_before(segments.floor, keep))
        {
            let Some(segment) = segment.upgrade() else {
                continue;
            };
            let usage = segments.bytes.get(&id).copied().unwrap_or_default();
            let Ok(size) = segment.file.metadata().map(|meta| meta.len()) else {
                upgraded.push(segment);
                continue;
            };
            // This upgrade and one per slice; anything else is a pin of a
            // closed copy, a quarantine or a relocation hold.
            let protected = segments
                .scopes
                .get(&id)
                .is_some_and(|scopes| !scopes.is_disjoint(&state.protected));
            if rules::compactable(usage, size, share, Arc::strong_count(&segment), protected) {
                cold.push((usage.bytes, id));
            }
            upgraded.push(segment);
        }
        drop(state);
        drop(upgraded);
        cold.sort();
        cold.into_iter().map(|(_, id)| id).collect()
    }

    /// The live slices of segment `id`.
    pub fn slices_in(&self, id: u64) -> Vec<Arc<Object>> {
        let state = self.0.state.lock();
        let slices = state
            .segments
            .slices
            .range((id, 0)..(id + 1, 0))
            .filter_map(|(_, slice)| slice.upgrade())
            .collect();
        drop(state);
        slices
    }

    /// Points the live slice at `from` at `to`, a copy of its bytes, and
    /// returns the segment it left, which the caller keeps until nothing
    /// durable names `from`. `None` when no slice holds `from` any more.
    ///
    /// With `hold`, the segment left is also kept until the scope selects a
    /// snapshot built after this call, in the same critical section as the
    /// swap: a park pin that sees the slice at `to` then also sees the hold
    /// on `from`, which the selected snapshot may still name.
    pub fn relocate(
        &self,
        from: Location,
        to: Location,
        hold: bool,
    ) -> io::Result<Option<Arc<Segment>>> {
        if from.scope != to.scope || from.len != to.len || from.crc != to.crc {
            return Err(invalid("relocated slice differs from its source"));
        }
        // Dropping the last holder of the slice or of a segment takes the
        // table lock, so both are dropped after it.
        let object;
        let mut state = self.0.state.lock();
        object = state
            .segments
            .slices
            .get(&(from.segment, from.offset))
            .and_then(Weak::upgrade);
        let Some(object) = &object else {
            return Ok(None);
        };
        let Body::Slice(at) = &object.0 else {
            unreachable!("segment slice table holds a file object");
        };
        if at.read().location != from {
            return Ok(None);
        }
        let segment = self.open_segment(&mut state, to.segment)?;
        let segments = &mut state.segments;
        let previous = std::mem::replace(
            &mut *at.write(),
            At {
                segment,
                location: to,
            },
        );
        segments.slices.remove(&(from.segment, from.offset));
        segments
            .slices
            .insert((to.segment, to.offset), Arc::downgrade(object));
        segments.remove(from);
        segments.add(to);
        segments
            .scopes
            .entry(to.segment)
            .or_default()
            .insert(to.scope);
        if hold {
            segments.moves += 1;
            let number = segments.moves;
            segments
                .moved
                .entry(from.scope)
                .or_default()
                .push((number, previous.segment.clone()));
        }
        drop(state);
        Ok(Some(previous.segment))
    }

    /// The newest move of `scope`'s slices, or `None` when its selected
    /// snapshot names no segment its slices left.
    pub fn last_move(&self, scope: StreamId) -> Option<u64> {
        let state = self.0.state.lock();
        state
            .segments
            .moved
            .get(&scope)
            .and_then(|moved| moved.last())
            .map(|(number, _)| *number)
    }

    /// Releases the segments `scope`'s slices left up to move `through`,
    /// once a snapshot built after them is selected.
    pub fn release_moved(&self, scope: StreamId, through: u64) {
        let mut state = self.0.state.lock();
        let mut released = Vec::new();
        if let Some(moved) = state.segments.moved.get_mut(&scope) {
            let kept;
            (released, kept) = std::mem::take(moved)
                .into_iter()
                .partition(|(number, _)| *number <= through);
            *moved = kept;
            if moved.is_empty() {
                state.segments.moved.remove(&scope);
            }
        }
        // Dropping a segment's last holder takes the table lock.
        drop(state);
        drop(released);
    }

    /// The segments held for `scope`'s selected snapshot after its slices
    /// moved.
    pub fn moved_segments(&self, scope: StreamId) -> Vec<u64> {
        let state = self.0.state.lock();
        state
            .segments
            .moved
            .get(&scope)
            .map(|moved| moved.iter().map(|(_, segment)| segment.id).collect())
            .unwrap_or_default()
    }

    /// The scopes holding segments for a snapshot not yet rebuilt.
    pub fn moved_scopes(&self) -> Vec<StreamId> {
        self.0.state.lock().segments.moved.keys().copied().collect()
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

    /// Lets the reaper reclaim `scope`'s objects again, once an open state
    /// machine pins the ones it still references.
    pub fn unprotect(&self, scope: StreamId) {
        self.0.state.lock().protected.remove(&scope);
    }

    /// Keeps every standalone object of `scope` until the hold drops.
    pub fn hold(&self, scope: StreamId) -> Hold {
        *self.0.state.lock().held.entry(scope).or_default() += 1;
        Hold {
            scope,
            store: Arc::downgrade(&self.0),
        }
    }

    /// Pins segment `id`, which must still exist.
    pub fn segment(&self, id: u64) -> io::Result<Arc<Segment>> {
        let mut state = self.0.state.lock();
        self.open_segment(&mut state, id)
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
                || state.held.contains_key(&scope)
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

/// A closed replica's hold on its scope's standalone objects.
pub(in crate::stream::consensus) struct Hold {
    scope: StreamId,
    store: Weak<Inner>,
}

impl Drop for Hold {
    fn drop(&mut self) {
        if let Some(store) = self.store.upgrade() {
            let mut state = store.state.lock();
            if let Some(count) = state.held.get_mut(&self.scope) {
                *count -= 1;
                if *count == 0 {
                    state.held.remove(&self.scope);
                }
            }
        }
    }
}

impl Segment {
    pub(super) fn read_at(&self, offset: u64, buffer: &mut [u8]) -> io::Result<()> {
        segment::read_at(&self.file, offset, buffer)
    }

    pub fn id(&self) -> u64 {
        self.id
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
    /// Whether something other than checkpoints and `held` handles of the
    /// caller's holds this object.
    pub fn needed(self: &Arc<Self>, held: usize) -> bool {
        Arc::strong_count(self) > held + self.1.load(AtomicOrdering::Relaxed)
    }

    pub fn key(&self) -> Option<Key> {
        match &self.0 {
            Body::File { key, .. } => Some(*key),
            Body::Slice(_) => None,
        }
    }

    fn at(&self) -> Option<At> {
        match &self.0 {
            Body::File { .. } => None,
            Body::Slice(at) => Some(at.read().clone()),
        }
    }

    /// The segment a slice lies in.
    pub fn segment(&self) -> Option<Arc<Segment>> {
        self.at().map(|at| at.segment)
    }

    pub fn reference(&self) -> Reference {
        match &self.0 {
            Body::File { key, .. } => Reference::Object(*key),
            Body::Slice(at) => Reference::Segment(at.read().location),
        }
    }

    pub fn len(&self) -> u64 {
        match &self.0 {
            Body::File { key, .. } => key.len,
            Body::Slice(at) => at.read().location.len,
        }
    }

    #[cfg(test)]
    pub fn path(&self) -> PathBuf {
        match &self.0 {
            Body::File { path, .. } => path.clone(),
            Body::Slice(at) => at.read().segment.path.clone(),
        }
    }

    /// Where the object's first byte sits in the file at `path`.
    #[cfg(test)]
    pub fn position(&self) -> u64 {
        match &self.0 {
            Body::File { .. } => 0,
            Body::Slice(at) => at.read().location.offset,
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
            Body::Slice(at) => {
                let At { segment, location } = at.read().clone();
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
            Body::Slice(at) => {
                let At { segment, location } = at.read().clone();
                segment::read_at(&segment.file, location.offset + offset, buf)
            }
        }
    }
}

impl Drop for Object {
    fn drop(&mut self) {
        let (key, store) = match &mut self.0 {
            Body::File { key, store, .. } => (key, store),
            Body::Slice(at) => {
                let At { segment, location } = at.get_mut();
                if let Some(store) = segment.store.upgrade() {
                    let mut state = store.state.lock();
                    let segments = &mut state.segments;
                    let key = (location.segment, location.offset);
                    if segments
                        .slices
                        .get(&key)
                        .is_some_and(|slice| slice.strong_count() == 0)
                    {
                        segments.slices.remove(&key);
                    }
                    segments.remove(*location);
                }
                return;
            }
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
