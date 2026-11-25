//! A segmented WAL. The trusted boundary selects a small directory of
//! immutable per-stream indexes. Indexes refer to immutable log segments.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, File, OpenOptions},
    io::{self, Read, Seek, Write},
    sync::Arc,
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use uuid::Uuid;

use super::{
    Boundary, CatalogEntry, Entry, Genesis, Log, LogId, Media, Selected, Space, State, StreamId,
    Vote, decode, encode, invalid, recover, sync_directory, sync_file,
};
use crate::stream::consensus::storage::objects::{Key, Object, Objects};

const MAGIC: &[u8; 8] = b"LKRWAL03";
pub(super) const MAX_SCOPES: usize = 4096;
pub(super) const MAX_SUFFIX: usize = 1024;
const MAX_DIRECTORY_BYTES: u64 = 384 * 1024;
const MAX_STREAM_INDEX_BYTES: usize = 160 * 1024;

#[derive(Serialize, Deserialize)]
struct Leaf {
    genesis: Option<Genesis>,
    catalog: Option<CatalogEntry>,
    vote: Option<Vote>,
    purged: Option<LogId>,
    snapshot: Option<Selected>,
    ownership: Option<crate::stream::consensus::ownership::Ownership>,
    entries: BTreeMap<u64, Key>,
}

pub(super) struct Indexed {
    generation: Uuid,
    len: u64,
    file: File,
    leaves: BTreeMap<StreamId, Arc<Object>>,
    #[cfg(test)]
    cut: std::cell::Cell<u8>,
}

impl Indexed {
    pub fn generation(&self) -> Uuid {
        self.generation
    }

    pub fn contains_scope(&self, scope: StreamId) -> bool {
        self.leaves.contains_key(&scope)
    }

    pub fn scope_count(&self) -> usize {
        self.leaves.len()
    }
    pub fn open(
        media: &Media,
        boundary: Boundary,
        objects: &Objects,
        space: &Space,
    ) -> io::Result<(Self, State)> {
        let selected = media.wal(boundary.generation);
        let mut file = OpenOptions::new().read(true).write(true).open(&selected)?;
        if file.metadata()?.len() < boundary.len {
            return Err(invalid("selected WAL prefix is missing"));
        }
        let mut prefix = (&file).take(boundary.len);
        let mut digest = Sha256::new();
        io::copy(&mut prefix, &mut digest)?;
        if <[u8; 32]>::from(digest.finalize()) != boundary.digest {
            return Err(invalid(
                "selected WAL prefix does not match its trusted boundary",
            ));
        }
        file.rewind()?;
        let mut magic = [0; 8];
        let indexed = boundary.len >= 8 && file.read_exact(&mut magic).is_ok() && &magic == MAGIC;
        if indexed {
            if boundary.len > MAX_DIRECTORY_BYTES || file.metadata()?.len() != boundary.len {
                return Err(invalid("invalid WAL index directory length"));
            }
            let mut bytes = Vec::new();
            file.read_to_end(&mut bytes)?;
            let entries: BTreeMap<StreamId, Key> = decode(&bytes)?;
            if entries.len() > MAX_SCOPES {
                return Err(invalid("WAL index directory exceeds its scope limit"));
            }
            let mut state = State::default();
            let mut leaves = BTreeMap::new();
            for (scope, key) in entries {
                if key.scope != scope || key.len > MAX_STREAM_INDEX_BYTES as u64 {
                    return Err(invalid("WAL index has a foreign or oversized leaf"));
                }
                let leaf = objects.pin(key)?;
                let value: Leaf = decode(&leaf.read()?)?;
                value.restore(scope, objects, &mut state)?;
                leaves.insert(scope, leaf);
            }
            state.check_hard_state()?;
            return Ok((
                Self {
                    generation: boundary.generation,
                    len: boundary.len,
                    file,
                    leaves,
                    #[cfg(test)]
                    cut: Default::default(),
                },
                state,
            ));
        }

        // The old framed WAL remains the authoritative basis until every
        // migrated segment, leaf and the new directory have been synced.
        file.rewind()?;
        let (mut state, read) = recover((&file).take(boundary.len))?;
        if read != boundary.len {
            return Err(invalid("selected WAL boundary splits a frame"));
        }
        state.check_hard_state()?;
        let scopes = state
            .genesis
            .keys()
            .chain(state.catalog.keys())
            .copied()
            .collect::<BTreeSet<_>>();
        if scopes.len() > MAX_SCOPES
            || state
                .logs
                .values()
                .any(|log| log.entries.len() > MAX_SUFFIX)
        {
            return Err(invalid("legacy WAL exceeds the indexed format geometry"));
        }
        let block = space.allocation_unit();
        let mut budget =
            1024 * 1024 + scopes.len() as u64 * (MAX_STREAM_INDEX_BYTES as u64 + 2 * block);
        for log in state.logs.values() {
            for entry in log.entries.values() {
                let size = bincode::serialized_size(entry).map_err(io::Error::other)?;
                budget = budget.saturating_add(size).saturating_add(2 * block);
            }
        }
        let _migration = space.reserve(budget)?;
        for (&scope, log) in &mut state.logs {
            for (&index, entry) in &log.entries {
                log.segments
                    .insert(index, store_entry(objects, scope, entry)?);
            }
        }
        let mut next = Self {
            generation: boundary.generation,
            len: file.metadata()?.len(),
            file,
            leaves: BTreeMap::new(),
            #[cfg(test)]
            cut: Default::default(),
        };
        next.commit(media, objects, &state, &scopes)?;
        Ok((next, state))
    }

    pub fn commit(
        &mut self,
        media: &Media,
        objects: &Objects,
        state: &State,
        scopes: &BTreeSet<StreamId>,
    ) -> io::Result<()> {
        #[cfg(test)]
        let cut = self.cut.replace(0);
        media.check_wal(self.generation, &self.file, self.len)?;
        let mut additions = Vec::new();
        let mut directory = self
            .leaves
            .iter()
            .map(|(&scope, leaf)| (scope, leaf.key()))
            .collect::<BTreeMap<_, _>>();
        for &scope in scopes {
            let leaf = encode(&Leaf::capture(state, scope)?)?;
            if leaf.len() > MAX_STREAM_INDEX_BYTES {
                return Err(invalid("stream WAL index exceeds its size limit"));
            }
            let leaf = objects.put(scope, &leaf)?;
            directory.insert(scope, leaf.key());
            additions.push((scope, leaf));
        }
        if directory.len() > MAX_SCOPES {
            return Err(invalid("WAL index directory exceeds its scope limit"));
        }
        objects.publish_files()?;
        let mut body = MAGIC.to_vec();
        body.extend(encode(&directory)?);
        if body.len() as u64 > MAX_DIRECTORY_BYTES {
            return Err(invalid("WAL index directory exceeds its size limit"));
        }
        let generation = Uuid::new_v4();
        let mut file = OpenOptions::new()
            .write(true)
            .read(true)
            .create_new(true)
            .open(media.wal(generation))?;
        file.write_all(&body)?;
        #[cfg(test)]
        if cut == 5 {
            return Err(io::Error::other("injected WAL index sync failure"));
        }
        sync_file(&file)?;
        sync_directory(media.data())?;
        #[cfg(test)]
        if cut == 1 {
            return Err(io::Error::other("interrupted before WAL index selection"));
        }
        media.prepare_boundary(generation, body.len() as u64, Sha256::digest(&body).into())?;
        #[cfg(test)]
        if cut == 2 {
            return Err(io::Error::other(
                "interrupted with a synced WAL boundary temporary",
            ));
        }
        media.publish_boundary()?;
        #[cfg(test)]
        if cut == 3 {
            return Err(io::Error::other("interrupted after WAL index selection"));
        }
        let old = self.generation;
        *self = Self {
            generation,
            len: body.len() as u64,
            file,
            leaves: std::mem::take(&mut self.leaves),
            #[cfg(test)]
            cut: Default::default(),
        };
        self.leaves.extend(additions);
        fs::remove_file(media.wal(old))?;
        #[cfg(test)]
        if cut == 4 {
            return Err(io::Error::other(
                "interrupted after unlink before returning the WAL reservation",
            ));
        }
        sync_directory(media.data())
    }

    #[cfg(test)]
    pub fn interrupt(&self, cut: u8) {
        self.cut.set(cut);
    }
}

impl Leaf {
    fn capture(state: &State, stream: StreamId) -> io::Result<Self> {
        let log = state.logs.get(&stream);
        let entries = if let Some(log) = log {
            if log.entries.len() != log.segments.len() || log.entries.len() > MAX_SUFFIX {
                return Err(invalid("accepted WAL suffix exceeds its index geometry"));
            }
            log.segments
                .iter()
                .map(|(&index, object)| (index, object.key()))
                .collect()
        } else {
            BTreeMap::new()
        };
        Ok(Self {
            genesis: state.genesis.get(&stream).cloned(),
            catalog: state.catalog.get(&stream).cloned(),
            vote: log.and_then(|log| log.vote),
            purged: log.and_then(|log| log.purged),
            snapshot: log.and_then(|log| log.snapshot),
            ownership: log.map(|log| log.ownership.clone()),
            entries,
        })
    }

    fn restore(self, scope: StreamId, objects: &Objects, state: &mut State) -> io::Result<()> {
        if let Some(genesis) = self.genesis {
            if genesis.stream != scope || self.entries.len() > MAX_SUFFIX {
                return Err(invalid("WAL leaf scope or suffix bound differs"));
            }
            let mut log = Log {
                vote: self.vote,
                purged: self.purged,
                snapshot: self.snapshot,
                ownership: self
                    .ownership
                    .ok_or_else(|| invalid("WAL leaf lacks replica ownership"))?,
                ..Log::default()
            };
            let mut next = self.purged.map_or(0, |purged| purged.index + 1);
            for (index, key) in self.entries {
                if index != next || key.scope != scope {
                    return Err(invalid("noncontiguous or foreign WAL segment"));
                }
                let object = objects.pin(key)?;
                let entry = decode::<Entry>(&object.read()?)?;
                if index != entry.log_id.index {
                    return Err(invalid("WAL segment log position differs"));
                }
                log.entries.insert(index, entry);
                log.segments.insert(index, object);
                next = next
                    .checked_add(1)
                    .ok_or_else(|| invalid("WAL index exhausted"))?;
            }
            state.genesis.insert(scope, genesis);
            state.logs.insert(scope, log);
        } else if !self.entries.is_empty()
            || self.vote.is_some()
            || self.purged.is_some()
            || self.snapshot.is_some()
        {
            return Err(invalid("unregistered WAL leaf contains hard state"));
        }
        if let Some(catalog) = self.catalog {
            if catalog.genesis.stream != scope {
                return Err(invalid("catalog leaf scope differs"));
            }
            state.catalog.insert(scope, catalog);
        }
        Ok(())
    }
}

pub(super) fn store_entry(
    objects: &Objects,
    stream: StreamId,
    entry: &Entry,
) -> io::Result<Arc<Object>> {
    objects.put(stream, &encode(entry)?)
}
