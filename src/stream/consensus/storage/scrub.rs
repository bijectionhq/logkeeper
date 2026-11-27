//! Online checks of the immutable bytes selected by each installed copy.

use std::{
    collections::VecDeque,
    fs::File,
    io::{self, Read},
    ops::Bound::{Excluded, Included, Unbounded},
    path::Path,
    sync::{Arc, atomic::Ordering},
};

use journal_contract::StreamId;
use sha2::{Digest, Sha256};

use super::{
    Disk,
    objects::{Key, Reference, Segment},
    segment,
    snapshot::{Selected, index},
};
use crate::stream::consensus::{invalid, ownership};

pub(in crate::stream::consensus) const CHUNK: usize = 64 * 1024;
const ITEMS_PER_PASS: usize = 128;

#[derive(Default)]
pub(in crate::stream::consensus) struct Scrub {
    cursor: Option<StreamId>,
    scan: Option<Scan>,
}

struct Scan {
    scope: StreamId,
    generation: u64,
    selected: Option<Selected>,
    root_pending: bool,
    pages: VecDeque<Key>,
    legacy: VecDeque<[u8; 32]>,
    references: VecDeque<Reference>,
    last_reference: Option<Reference>,
    wal_after: Option<u64>,
    wal_end: Option<u64>,
    check: Option<Check>,
    evidence: Evidence,
}

#[derive(Clone, Copy)]
enum Evidence {
    Snapshot(Selected),
    Wal(u64, Reference),
    None,
}

pub(in crate::stream::consensus) struct Failure {
    pub scope: StreamId,
    generation: u64,
    evidence: Evidence,
    pub error: io::Error,
}

impl Failure {
    pub fn current(&self, disk: &Disk) -> bool {
        disk.maybe_log(self.scope, |log| {
            log.ownership.installed()
                && log.ownership.generation() == Some(self.generation)
                && match self.evidence {
                    Evidence::Snapshot(selected) => log.snapshot == Some(selected),
                    Evidence::Wal(index, reference) => log
                        .segments
                        .get(&index)
                        .is_some_and(|object| object.reference() == reference),
                    Evidence::None => false,
                }
        })
        .unwrap_or(false)
    }
}

impl Scrub {
    pub fn pass(&mut self, disk: &Disk, mut budget: usize) -> (Option<Failure>, bool) {
        let mut scratch = vec![0; CHUNK];
        for _ in 0..ITEMS_PER_PASS {
            if budget < CHUNK || !disk.responsive() || disk.near_slow() {
                break;
            }
            if let Some(scan) = &mut self.scan {
                if disk.is_quarantined(scan.scope) {
                    self.scan = None;
                    continue;
                }
                match scan.step(disk, &mut scratch, &mut budget) {
                    Ok(true) => {}
                    Ok(false) => self.scan = None,
                    Err(error) => {
                        let failure = Failure {
                            scope: scan.scope,
                            generation: scan.generation,
                            evidence: scan.evidence,
                            error,
                        };
                        self.scan = None;
                        return (Some(failure), false);
                    }
                }
            } else {
                self.cursor = disk.next_log_scope(self.cursor);
                let Some(scope) = self.cursor else {
                    return (None, true);
                };
                self.scan = Scan::start(disk, scope);
            }
        }
        (None, false)
    }
}

impl Scan {
    fn start(disk: &Disk, scope: StreamId) -> Option<Self> {
        if disk.is_quarantined(scope) {
            return None;
        }
        disk.maybe_log(scope, |log| {
            if !log.ownership.installed() {
                return None;
            }
            let selected = log.snapshot;
            // The selected snapshot already names the retained bytes before its
            // cut. Freeze the suffix end so a busy stream cannot monopolize work.
            let wal_after = selected.map(|selected| selected.log_id.index);
            Some(Self {
                scope,
                generation: log.ownership.generation()?,
                selected,
                root_pending: selected.is_some(),
                pages: VecDeque::new(),
                legacy: VecDeque::new(),
                references: VecDeque::new(),
                last_reference: None,
                wal_after,
                wal_end: log.segments.last_key_value().map(|(&index, _)| index),
                check: None,
                evidence: Evidence::None,
            })
        })
        .flatten()
    }

    fn step(&mut self, disk: &Disk, scratch: &mut [u8], budget: &mut usize) -> io::Result<bool> {
        if let Some(check) = &mut self.check {
            let len = scratch.len().min(*budget).min(check.remaining());
            *budget -= len;
            let complete = check.read(&mut scratch[..len])?;
            disk.metrics
                .scrub_bytes
                .fetch_add(len as u64, Ordering::Relaxed);
            if complete {
                crate::stream::consensus::metrics::count(&disk.metrics.scrub_objects);
                let check = self.check.take().unwrap();
                match check.kind {
                    Kind::Root(Some(bytes)) => {
                        (self.pages, self.legacy) =
                            index::scrub_root(&bytes, self.scope, self.selected.unwrap())?;
                    }
                    Kind::Page(bytes) => self.references = index::scrub_page(&bytes, self.scope)?,
                    _ => {}
                }
            }
            return Ok(true);
        }

        if self.root_pending {
            let selected = self.selected.unwrap();
            self.root_pending = false;
            self.evidence = Evidence::Snapshot(selected);
            self.check = Some(Check::file(
                &self.snapshot_path(disk, selected),
                None,
                selected.digest,
                Kind::Root(None),
            )?);
        } else if let Some(digest) = self.legacy.pop_front() {
            let legacy = Selected {
                digest,
                ..self.selected.unwrap()
            };
            self.check = Some(Check::file(
                &self.snapshot_path(disk, legacy),
                None,
                digest,
                Kind::Extent,
            )?);
        } else if let Some(reference) = self.references.pop_front() {
            // Multiple contiguous records can name the same WAL slice.
            if self.last_reference != Some(reference) {
                self.last_reference = Some(reference);
                self.check = Some(Check::extent(disk, reference, Kind::Extent)?);
            }
        } else if let Some(key) = self.pages.pop_front() {
            self.check = Some(Check::extent(
                disk,
                Reference::Object(key),
                Kind::Page(Vec::new()),
            )?);
        } else if let Some(end) = self
            .wal_end
            .filter(|end| self.wal_after.is_none_or(|after| after < *end))
        {
            let next = disk
                .maybe_log(self.scope, |log| {
                    if log.ownership.generation() != Some(self.generation)
                        || !log.ownership.installed()
                    {
                        return None;
                    }
                    log.segments
                        .range((self.wal_after.map_or(Unbounded, Excluded), Included(end)))
                        .next()
                        .map(|(&index, object)| (index, object.reference()))
                })
                .flatten();
            let Some((index, reference)) = next else {
                return Ok(false);
            };
            self.wal_after = Some(index);
            self.evidence = Evidence::Wal(index, reference);
            if self.last_reference != Some(reference) {
                self.last_reference = Some(reference);
                self.check = Some(Check::extent(disk, reference, Kind::Extent)?);
            }
        } else {
            return Ok(false);
        }
        Ok(true)
    }

    fn snapshot_path(&self, disk: &Disk, selected: Selected) -> std::path::PathBuf {
        selected.path(&ownership::directory(
            &disk.path,
            self.scope,
            self.generation,
        ))
    }
}

enum Source {
    File(File, Sha256, [u8; 32]),
    Segment(Arc<Segment>, u64, crc32fast::Hasher, u32),
}

enum Kind {
    // Includes the root's bytes only for bounded indexed roots.
    Root(Option<Vec<u8>>),
    Page(Vec<u8>),
    Extent,
}

struct Check {
    source: Source,
    kind: Kind,
    left: u64,
}

impl Check {
    fn file(path: &Path, len: Option<u64>, digest: [u8; 32], kind: Kind) -> io::Result<Self> {
        let file = File::open(path)?;
        let size = file.metadata()?.len();
        if len.is_some_and(|len| size != len) {
            return Err(invalid("immutable object length changed"));
        }
        Ok(Self {
            source: Source::File(file, Sha256::new(), digest),
            kind,
            left: size,
        })
    }

    fn extent(disk: &Disk, reference: Reference, kind: Kind) -> io::Result<Self> {
        match reference {
            Reference::Object(key) => {
                let path = disk.objects.path_for(key)?;
                Self::file(&path, Some(key.len), key.digest, kind)
            }
            Reference::Segment(location) => {
                if location.len == 0
                    || location.len > segment::MAX_FRAME
                    || location.offset < segment::HEADER + segment::FRAME_HEADER
                    || location.offset.checked_add(location.len).is_none()
                {
                    return Err(invalid("invalid WAL segment reference"));
                }
                Ok(Self {
                    source: Source::Segment(
                        disk.objects.segment(location.segment)?,
                        location.offset,
                        crc32fast::Hasher::new(),
                        location.crc,
                    ),
                    kind,
                    left: location.len,
                })
            }
        }
    }

    fn remaining(&self) -> usize {
        usize::try_from(self.left).unwrap_or(usize::MAX)
    }

    fn read(&mut self, bytes: &mut [u8]) -> io::Result<bool> {
        match &mut self.source {
            Source::File(file, hash, _) => {
                file.read_exact(bytes)?;
                hash.update(&*bytes);
            }
            Source::Segment(segment, offset, hash, _) => {
                segment.read_at(*offset, bytes)?;
                hash.update(bytes);
                *offset += bytes.len() as u64;
            }
        }
        match &mut self.kind {
            Kind::Root(root @ None)
                if bytes
                    .get(..8)
                    .and_then(|magic| magic.try_into().ok())
                    .is_some_and(index::indexed) =>
            {
                if self.left > index::MAX_ROOT_BYTES {
                    return Err(invalid("indexed snapshot root exceeds its bound"));
                }
                *root = Some(bytes.to_vec());
            }
            Kind::Root(Some(body)) | Kind::Page(body) => body.extend_from_slice(bytes),
            _ => {}
        }
        self.left -= bytes.len() as u64;
        if self.left != 0 {
            return Ok(false);
        }
        let matches = match &self.source {
            Source::File(_, hash, digest) => <[u8; 32]>::from(hash.clone().finalize()) == *digest,
            Source::Segment(_, _, hash, crc) => hash.clone().finalize() == *crc,
        };
        if !matches {
            return Err(invalid("immutable extent failed its selected checksum"));
        }
        Ok(true)
    }
}
