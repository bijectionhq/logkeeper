//! Immutable objects shared by WAL indexes, snapshots and exact read handles.

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

#[derive(Clone)]
pub(super) struct Objects(Arc<Inner>);

struct Inner {
    root: PathBuf,
    state: Mutex<State>,
    #[cfg(test)]
    partial_put: Mutex<Option<StreamId>>,
}

#[derive(Default)]
struct State {
    live: BTreeMap<(StreamId, Uuid), Weak<Object>>,
    dead: VecDeque<(StreamId, Uuid)>,
    protected: BTreeSet<StreamId>,
    ready: bool,
    scan: Option<ReadDir>,
}

#[derive(Debug)]
pub(in crate::stream::consensus) struct Object {
    key: Key,
    store: Weak<Inner>,
    path: PathBuf,
}

impl Objects {
    pub fn open(data: &Path) -> io::Result<Self> {
        let root = data.join("objects");
        fs::create_dir_all(&root)?;
        sync_directory(data)?;
        Ok(Self(Arc::new(Inner {
            root,
            state: Mutex::new(State::default()),
            #[cfg(test)]
            partial_put: Mutex::default(),
        })))
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
            .open(&object.path)?;
        #[cfg(test)]
        if self
            .0
            .partial_put
            .lock()
            .take_if(|pending| *pending == scope)
            .is_some()
        {
            file.write_all(&bytes[..bytes.len() / 2])?;
            sync_file(&file)?;
            return Err(io::Error::other("injected partial WAL extent write"));
        }
        file.write_all(bytes)?;
        sync_file(&file)?;
        Ok(object)
    }

    #[cfg(test)]
    pub fn interrupt_next_put(&self, scope: StreamId) {
        *self.0.partial_put.lock() = Some(scope);
    }

    pub fn pin(&self, key: Key) -> io::Result<Arc<Object>> {
        if key.len > MAX_OBJECT_BYTES || key.id.is_nil() {
            return Err(invalid("invalid immutable object reference"));
        }
        let mut state = self.0.state.lock();
        if let Some(found) = state.live.get(&(key.scope, key.id)).and_then(Weak::upgrade) {
            drop(state);
            if found.key != key {
                return Err(invalid("immutable object reference changed"));
            }
            return Ok(found);
        }
        let object = Arc::new(Object {
            key,
            store: Arc::downgrade(&self.0),
            path: self.0.root.join(key.name()),
        });
        state
            .live
            .insert((key.scope, key.id), Arc::downgrade(&object));
        Ok(object)
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
        Ok(())
    }
}

impl Object {
    pub fn key(&self) -> Key {
        self.key
    }

    #[cfg(test)]
    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn read(&self) -> io::Result<Vec<u8>> {
        let mut bytes = Vec::new();
        File::open(&self.path)?
            .take(self.key.len + 1)
            .read_to_end(&mut bytes)?;
        if bytes.len() as u64 != self.key.len
            || <[u8; 32]>::from(Sha256::digest(&bytes)) != self.key.digest
        {
            return Err(invalid("immutable object failed its selected checksum"));
        }
        Ok(bytes)
    }

    pub fn read_range(&self, offset: u64, buf: &mut [u8]) -> io::Result<()> {
        if offset
            .checked_add(buf.len() as u64)
            .is_none_or(|end| end > self.key.len)
        {
            return Err(invalid("extent range exceeds its immutable object"));
        }
        let mut file = File::open(&self.path)?;
        file.seek(SeekFrom::Start(offset))?;
        file.read_exact(buf)
    }
}

impl Drop for Object {
    fn drop(&mut self) {
        if let Some(store) = self.store.upgrade() {
            let mut state = store.state.lock();
            if state
                .live
                .get(&(self.key.scope, self.key.id))
                .is_some_and(|object| object.strong_count() == 0)
            {
                state.live.remove(&(self.key.scope, self.key.id));
            }
            if state.dead.len() < MAX_PENDING_REAP {
                state.dead.push_back((self.key.scope, self.key.id));
            }
        }
    }
}
