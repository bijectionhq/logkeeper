//! A selected snapshot describes exact retained bytes without copying them.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fs::File,
    io::{self, Read, Write},
    path::Path,
    sync::Arc,
};

use journal_contract::StreamId;
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};

use super::{Genesis, Image, Payload, Selected, SnapshotMeta, invalid, sha256};
use crate::stream::consensus::{
    decode, encode,
    state::{EpochRuns, MAX_RETAINED_RECORDS, Offload, TIMED_RECORD},
    storage::objects::{Key, Location, Object, Objects, Reference},
};

/// Roots that also store the epochs of the retained records. An N format:
/// written only once the cluster version is finalized, since a keeper from
/// before it cannot open one.
pub(super) const MAGIC: &[u8; 8] = b"LKRIDX02";
/// Roots without epochs, which reopen with unknown record epochs. Written
/// until the cluster version is finalized, so a keeper can roll back.
pub(super) const MAGIC_WITHOUT_EPOCHS: &[u8; 8] = b"LKRIDX01";
/// Roots that also store offload progress. Written only once a stream has
/// offloaded, which needs the finalized `CLUSTER_VERSION_OFFLOAD`.
const MAGIC_WITH_OFFLOAD: &[u8; 8] = b"LKRIDX03";

/// Whether a selected snapshot starts with an index root.
pub(in crate::stream::consensus::storage) fn indexed(magic: &[u8; 8]) -> bool {
    magic == MAGIC || magic == MAGIC_WITHOUT_EPOCHS || magic == MAGIC_WITH_OFFLOAD
}
const PAGE: usize = 128;
const MAX_PAGES: usize = MAX_RETAINED_RECORDS / PAGE + 1;
const MAX_PAGE_BYTES: usize = 16 * 1024;
pub(in crate::stream::consensus::storage) const MAX_ROOT_BYTES: u64 = 384 * 1024;
// The encoded size of one page reference. A full stream's references take
// under half the root, which leaves the rest for its genesis, metadata and
// image.
const PAGE_REF_BYTES: u64 = 92;
const _: () = assert!(MAX_PAGES as u64 * PAGE_REF_BYTES <= MAX_ROOT_BYTES / 2);

// One full set of index pages and a root. A snapshot rewrites only the pages
// that changed since the previous one, but keeper batches of up to 256 records
// per entry can change every page between two snapshots, so the scratch
// reservation covers a full set.
pub(super) const SCRATCH: u64 = 36 * 1024 * 1024;
const _: () = assert!((MAX_PAGES * MAX_PAGE_BYTES) as u64 + MAX_ROOT_BYTES <= SCRATCH);
const _: () = assert!(SCRATCH <= crate::stream::consensus::decisions::SCRATCH_BYTES);

#[derive(Clone, Default)]
pub(super) struct Dependencies {
    pages: BTreeMap<u64, (usize, Arc<Object>)>,
    legacy: BTreeSet<[u8; 32]>,
}

impl Dependencies {
    pub fn legacy(digest: [u8; 32]) -> Self {
        Self {
            legacy: BTreeSet::from([digest]),
            ..Self::default()
        }
    }

    pub fn legacy_files(&self) -> &BTreeSet<[u8; 32]> {
        &self.legacy
    }
}

#[derive(Serialize, Deserialize)]
struct Root {
    genesis: Genesis,
    meta: SnapshotMeta,
    image: Image,
    pages: Vec<PageRef>,
    legacy: BTreeSet<[u8; 32]>,
}

#[derive(Serialize, Deserialize)]
struct PageRef {
    first: u64,
    count: u32,
    object: Key,
}

#[derive(Serialize, Deserialize)]
struct Span {
    source: Source,
    offset: u64,
    len: u32,
    crc: u32,
}

#[derive(Serialize, Deserialize)]
enum Source {
    Object(Key),
    Legacy([u8; 32]),
    Segment(Location),
}

pub(super) fn build(
    file: &mut File,
    objects: &Objects,
    genesis: &Genesis,
    meta: &SnapshotMeta,
    image: &Image,
    previous: &Dependencies,
    with_epochs: bool,
) -> io::Result<Dependencies> {
    let mut dependencies = Dependencies::default();
    let mut first = image.state.retained_floor().0;
    let mut left = usize::try_from(image.state.record_count()?).map_err(io::Error::other)?;
    if left > MAX_RETAINED_RECORDS {
        return Err(invalid("snapshot exceeds retained record geometry"));
    }
    let mut records = image.state.records();
    let mut pages = Vec::new();
    while left > 0 {
        let count = left.min(PAGE - ((first - 1) % PAGE as u64) as usize);
        let payloads = records.by_ref().take(count);
        let leaf = match previous.pages.get(&first).filter(|(len, _)| *len == count) {
            Some((_, page)) => {
                for payload in payloads {
                    if let Payload::Snapshot { digest, .. } = payload {
                        dependencies.legacy.insert(*digest);
                    }
                }
                page.clone()
            }
            None => {
                let spans = payloads
                    .map(|payload| Span::from_record(payload, &mut dependencies.legacy))
                    .collect::<Vec<_>>();
                let body = encode(&spans)?;
                if spans.len() != count || body.len() > MAX_PAGE_BYTES {
                    return Err(invalid("snapshot page exceeds its geometry"));
                }
                objects.put(genesis.stream, &body)?
            }
        };
        pages.push(PageRef {
            first,
            count: count as u32,
            object: leaf
                .key()
                .ok_or_else(|| invalid("snapshot page is not a standalone object"))?,
        });
        dependencies.pages.insert(first, (count, leaf));
        first += count as u64;
        left -= count;
    }
    if pages.len() > MAX_PAGES || dependencies.legacy.len() > 1 {
        return Err(invalid("snapshot dependency geometry exceeded"));
    }
    objects.publish_files()?;
    let root = Root {
        genesis: genesis.clone(),
        meta: meta.clone(),
        image: image.clone(),
        pages,
        legacy: dependencies.legacy.clone(),
    };
    let offload = image.state.offload();
    let (magic, root) = if offload != Offload::default() {
        (
            MAGIC_WITH_OFFLOAD,
            encode(&(root, image.state.epoch_runs(), offload))?,
        )
    } else if with_epochs {
        (MAGIC, encode(&(root, image.state.epoch_runs()))?)
    } else {
        (MAGIC_WITHOUT_EPOCHS, encode(&root)?)
    };
    if root.len() as u64 > MAX_ROOT_BYTES {
        return Err(invalid("snapshot root exceeds its bound"));
    }
    file.write_all(magic)?;
    file.write_all(&root)?;
    Ok(dependencies)
}

pub(super) fn open(
    file: File,
    directory: &Path,
    selected: Selected,
    genesis: &Genesis,
    objects: &Objects,
) -> io::Result<(SnapshotMeta, Image, Dependencies)> {
    let mut bytes = Vec::new();
    file.take(MAX_ROOT_BYTES + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > MAX_ROOT_BYTES {
        return Err(invalid("invalid indexed snapshot root"));
    }
    let (mut root, epochs, offload) = decode_root(&bytes)?;
    root.image.stage_intent = root.meta.snapshot_id.starts_with(super::STAGED_IMAGE);
    if &root.genesis != genesis
        || root.meta.last_log_id != Some(selected.log_id)
        || root.image.applied != root.meta.last_log_id
        || root.image.membership != root.meta.last_membership
        || root.pages.len() > MAX_PAGES
        || root.legacy.len() > 1
    {
        return Err(invalid(
            "indexed snapshot differs from the selected scope or cut",
        ));
    }
    let mut dependencies = Dependencies {
        legacy: root.legacy,
        ..Dependencies::default()
    };
    let mut legacy = BTreeMap::new();
    for &digest in &dependencies.legacy {
        let path = Selected {
            digest,
            log_id: selected.log_id,
        }
        .path(directory);
        let file = File::open(path)?;
        if sha256(&file)? != digest {
            return Err(invalid("legacy extent checksum changed"));
        }
        legacy.insert(digest, Arc::new(Mutex::new(file)));
    }
    let count = root.image.state.record_count()?;
    if count > MAX_RETAINED_RECORDS as u64 {
        return Err(invalid("snapshot has too many records"));
    }
    let mut first = root.image.state.retained_floor().0;
    let mut records = VecDeque::new();
    let mut entry = None;
    for page in root.pages {
        if page.first != first
            || page.count == 0
            || page.count as usize > PAGE
            || page.object.scope != genesis.stream
            || page.object.len > MAX_PAGE_BYTES as u64
        {
            return Err(invalid("invalid snapshot page reference"));
        }
        let object = objects.pin(page.object)?;
        let spans: Vec<Span> = decode(&object.read()?)?;
        if spans.len() != page.count as usize || records.len() as u64 + page.count as u64 > count {
            return Err(invalid(
                "snapshot page does not cover its declared retained position",
            ));
        }
        for span in spans {
            records.push_back(span.open(genesis.stream, objects, &legacy, &mut entry)?);
        }
        dependencies
            .pages
            .insert(first, (page.count as usize, object));
        first += page.count as u64;
    }
    if records.len() as u64 != count {
        return Err(invalid("incomplete retained snapshot"));
    }
    root.image
        .state
        .restore_records(records, genesis.quota_bytes)?;
    root.image.state.restore_epochs(epochs)?;
    root.image.state.restore_offload(offload)?;
    Ok((root.meta, root.image, dependencies))
}

fn decode_root(bytes: &[u8]) -> io::Result<(Root, EpochRuns, Offload)> {
    if bytes.len() as u64 > MAX_ROOT_BYTES {
        return Err(invalid("invalid indexed snapshot root"));
    }
    if let Some(body) = bytes.strip_prefix(MAGIC) {
        let (root, epochs) = decode(body)?;
        Ok((root, epochs, Offload::default()))
    } else if let Some(body) = bytes.strip_prefix(MAGIC_WITH_OFFLOAD) {
        decode(body)
    } else if let Some(body) = bytes.strip_prefix(MAGIC_WITHOUT_EPOCHS) {
        Ok((decode(body)?, EpochRuns::default(), Offload::default()))
    } else {
        Err(invalid("invalid indexed snapshot root"))
    }
}

/// Walks the authenticated dependency list without opening a replica.
pub(in crate::stream::consensus::storage) fn scrub_root(
    bytes: &[u8],
    stream: StreamId,
    selected: Selected,
) -> io::Result<(VecDeque<Key>, VecDeque<[u8; 32]>)> {
    let (root, _, _) = decode_root(bytes)?;
    if root.genesis.stream != stream
        || root.meta.last_log_id != Some(selected.log_id)
        || root.pages.len() > MAX_PAGES
        || root.legacy.len() > 1
    {
        return Err(invalid(
            "indexed snapshot differs from the selected scope or cut",
        ));
    }
    let pages = root.pages.into_iter().map(|page| {
        if page.object.scope != stream || page.object.len > MAX_PAGE_BYTES as u64 {
            return Err(invalid("invalid snapshot page reference"));
        }
        Ok(page.object)
    });
    Ok((
        pages.collect::<io::Result<_>>()?,
        root.legacy.into_iter().collect(),
    ))
}

pub(in crate::stream::consensus::storage) fn scrub_page(
    bytes: &[u8],
    stream: StreamId,
) -> io::Result<VecDeque<Reference>> {
    let spans: Vec<Span> = decode(bytes)?;
    if spans.len() > PAGE {
        return Err(invalid("invalid snapshot page"));
    }
    spans
        .into_iter()
        .filter_map(|span| match span.source {
            Source::Object(key) if key.scope == stream => Some(Ok(Reference::Object(key))),
            Source::Segment(location) if location.scope == stream => {
                Some(Ok(Reference::Segment(location)))
            }
            Source::Legacy(_) => None,
            _ => Some(Err(invalid("snapshot page references a different stream"))),
        })
        .collect()
}

impl Span {
    fn from_record(payload: &Payload, legacy: &mut BTreeSet<[u8; 32]>) -> Self {
        match payload {
            Payload::Extent {
                object,
                offset,
                len,
                crc,
                timed,
            } => Self {
                source: match object.reference() {
                    Reference::Object(key) => Source::Object(key),
                    Reference::Segment(location) => Source::Segment(location),
                },
                offset: *offset,
                len: *len | if *timed { TIMED_RECORD } else { 0 },
                crc: *crc,
            },
            Payload::Snapshot {
                digest,
                offset,
                len,
                crc,
                timed,
                ..
            } => {
                legacy.insert(*digest);
                Self {
                    source: Source::Legacy(*digest),
                    offset: *offset,
                    len: *len | if *timed { TIMED_RECORD } else { 0 },
                    crc: *crc,
                }
            }
        }
    }

    fn open(
        self,
        scope: StreamId,
        objects: &Objects,
        legacy: &BTreeMap<[u8; 32], Arc<Mutex<File>>>,
        entry: &mut Option<(Location, Arc<Object>)>,
    ) -> io::Result<Payload> {
        let Self {
            source,
            offset,
            len,
            crc,
        } = self;
        let timed = len & TIMED_RECORD != 0;
        let len = len & !TIMED_RECORD;
        if len as usize > crate::stream::consensus::MAX_RECORD {
            return Err(invalid("snapshot extent exceeds record bound"));
        }
        let payload = match source {
            Source::Object(key) if key.scope == scope => Payload::Extent {
                object: objects.pin(key)?,
                offset,
                len,
                crc,
                timed,
            },
            // Records of one batch entry share its slice, as they did when
            // the entry was applied.
            Source::Segment(location) if location.scope == scope => Payload::Extent {
                object: match entry {
                    Some((last, object)) if *last == location => object.clone(),
                    _ => entry.insert((location, objects.slice(location)?)).1.clone(),
                },
                offset,
                len,
                crc,
                timed,
            },
            Source::Legacy(digest) => Payload::Snapshot {
                file: legacy
                    .get(&digest)
                    .ok_or_else(|| invalid("undeclared legacy extent"))?
                    .clone(),
                digest,
                offset,
                len,
                crc,
                timed,
            },
            _ => return Err(invalid("foreign snapshot payload extent")),
        };
        payload.load()?;
        Ok(payload)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_full_stream_of_page_references_fits_its_share_of_the_root() {
        let page = PageRef {
            first: u64::MAX,
            count: PAGE as u32,
            object: Key {
                scope: StreamId(u128::MAX),
                id: uuid::Uuid::from_u128(u128::MAX),
                len: u64::MAX,
                digest: [0xff; 32],
            },
        };
        assert_eq!(encode(&page).unwrap().len() as u64, PAGE_REF_BYTES);
        let pages = (0..MAX_PAGES)
            .map(|_| PageRef { ..page })
            .collect::<Vec<_>>();
        assert!(encode(&pages).unwrap().len() as u64 <= MAX_ROOT_BYTES / 2);
    }
}
