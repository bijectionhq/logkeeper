//! Readers for the WAL formats before segments, kept to migrate old media.
//!
//! `LKRWAL03` media select a directory of immutable per-stream index leaves
//! through a JSON boundary; the leaves refer to one object per entry. Older
//! media hold a single framed WAL.

use std::{
    collections::BTreeMap,
    fs::File,
    io::{self, Read, Seek},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{
    Boundary, CatalogEntry, Entry, Genesis, Log, LogId, Media, Selected, State, StreamId, Vote,
    decode, invalid, recover,
    segmented::{MAX_SCOPES, MAX_SUFFIX},
};
use crate::stream::consensus::storage::objects::{Key, Objects};

pub(super) const MAGIC: &[u8; 8] = b"LKRWAL03";
const MAX_DIRECTORY_BYTES: u64 = 384 * 1024;
pub(super) const MAX_STREAM_INDEX_BYTES: usize = 160 * 1024;

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

/// Reads the state an old boundary selects. Entries of an indexed WAL keep
/// their objects; entries of a framed WAL have none yet.
pub(super) fn open(media: &Media, boundary: Boundary, objects: &Objects) -> io::Result<State> {
    let mut file = File::open(media.wal(boundary.generation))?;
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
        for (scope, key) in entries {
            if key.scope != scope || key.len > MAX_STREAM_INDEX_BYTES as u64 {
                return Err(invalid("WAL index has a foreign or oversized leaf"));
            }
            let leaf = objects.pin(key)?;
            let value: Leaf = decode(&leaf.read()?)?;
            value.restore(scope, objects, &mut state)?;
        }
        state.check_hard_state()?;
        return Ok(state);
    }

    file.rewind()?;
    let (state, read) = recover((&file).take(boundary.len))?;
    if read != boundary.len {
        return Err(invalid("selected WAL boundary splits a frame"));
    }
    state.check_hard_state()?;
    if state.scope_ids().len() > MAX_SCOPES
        || state
            .logs
            .values()
            .any(|log| log.entries.len() > MAX_SUFFIX)
    {
        return Err(invalid("legacy WAL exceeds the indexed format geometry"));
    }
    Ok(state)
}

impl Leaf {
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

/// Writes `state` as an `LKRWAL03` index exactly as keepers before segments
/// committed a round, so tests can migrate media written by that code path.
#[cfg(test)]
pub(super) fn commit(
    media: &Media,
    objects: &Objects,
    state: &mut State,
    current: uuid::Uuid,
) -> io::Result<uuid::Uuid> {
    use std::{fs::OpenOptions, io::Write};

    use crate::stream::{
        consensus::encode,
        keeper::durability::{sync_directory, sync_file},
    };

    let current_file = File::open(media.wal(current))?;
    media.check_wal(current, &current_file, current_file.metadata()?.len())?;
    let mut directory = BTreeMap::new();
    for scope in state.scope_ids() {
        let log = state.logs.get_mut(&scope);
        let entries = match log {
            Some(log) => {
                let mut keys = BTreeMap::new();
                for (&index, entry) in &log.entries {
                    let object = objects.put(scope, &encode(entry)?)?;
                    keys.insert(index, object.key().unwrap());
                    log.segments.insert(index, object);
                }
                keys
            }
            None => BTreeMap::new(),
        };
        let log = state.logs.get(&scope);
        let leaf = Leaf {
            genesis: state.genesis.get(&scope).cloned(),
            catalog: state.catalog.get(&scope).cloned(),
            vote: log.and_then(|log| log.vote),
            purged: log.and_then(|log| log.purged),
            snapshot: log.and_then(|log| log.snapshot),
            ownership: log.map(|log| log.ownership.clone()),
            entries,
        };
        let leaf = objects.put(scope, &encode(&leaf)?)?;
        directory.insert(scope, leaf.key().unwrap());
    }
    objects.publish_files()?;
    let mut body = MAGIC.to_vec();
    body.extend(encode(&directory)?);
    let generation = uuid::Uuid::new_v4();
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(media.wal(generation))?;
    file.write_all(&body)?;
    sync_file(&file)?;
    sync_directory(media.data())?;
    media.publish(generation, body.len() as u64, Sha256::digest(&body).into())?;
    std::fs::remove_file(media.wal(current))?;
    sync_directory(media.data())?;
    Ok(generation)
}
