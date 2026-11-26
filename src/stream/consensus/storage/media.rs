//! The enrollment registry survives loss of a keeper's journal directory.
//!
//! The registry also holds the trusted WAL boundary: two fixed-size slots
//! written in place in turn. Each names the (segment, offset, chain hash) the
//! data volume must still hold and the checkpoint recovery starts from, so a
//! data volume that silently loses acknowledged writes is refused at open.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::{self, File, OpenOptions},
    io::{self, Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
};

use fs2::FileExt;
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use sha2::Digest;
use uuid::Uuid;

use super::segment;
use crate::stream::{
    consensus::{Domains, invalid},
    keeper::durability::{sync_data, sync_directory, sync_file},
};

const FORMAT: &str = "logkeeper-raft-3";
const LEGACY_FORMAT: &str = "logkeeper-raft-2";
const SLOT_MAGIC: &[u8; 8] = b"LKRBND01";
const SLOT_BYTES: usize = 512;

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(in crate::stream::consensus) struct Provision {
    pub keeper: Uuid,
    pub data: PathBuf,
    pub domain: String,
    pub certificate_sha256: String,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(in crate::stream::consensus) struct Authority {
    pub catalog: Uuid,
    pub domains: Domains,
}

impl Authority {
    pub fn read(registry: &Path) -> io::Result<Self> {
        // The authority can describe the full inventory, unlike a single
        // enrollment document.
        read_bounded(&registry.join("placement.json"), 1024 * 1024)
    }
}

pub(in crate::stream::consensus) struct Enrollment {
    registry: PathBuf,
    data: PathBuf,
    keeper: Uuid,
    catalog: Uuid,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
struct Identity {
    format: String,
    keeper: Uuid,
    catalog: Uuid,
    incarnation: Uuid,
}

pub(super) struct Media {
    enrollment: Enrollment,
    identity: Identity,
}

/// The media incarnations a keeper has seen its peers under, trusted on
/// first contact. It lives in the registry, beside the enrollment, so a
/// peer's records of this keeper outlive this keeper's media: a keeper
/// whose media was installed again under its old ID meets peers that still
/// know its old incarnation.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(in crate::stream::consensus) struct Incarnations {
    /// The incarnation this keeper first saw each peer under.
    pub peers: BTreeMap<Uuid, Uuid>,
    /// Peers seen since under another incarnation.
    pub reincarnated: BTreeSet<Uuid>,
    /// Whether a peer knows this keeper under another incarnation.
    pub reused: bool,
}

impl Incarnations {
    pub fn path(registry: &Path, keeper: Uuid) -> PathBuf {
        registry.join(format!("{keeper}.incarnations.json"))
    }

    /// The record at `path`, empty before the first one is stored.
    pub fn load(path: &Path) -> io::Result<Self> {
        match read_bounded(path, 1024 * 1024) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(Self::default()),
            result => result,
        }
    }

    /// Adds this record to the one at `path` and replaces it by a synced
    /// rename. Records only grow, so a store that a cancelled exchange or a
    /// stopped keeper left running loses nothing when it lands last.
    pub fn store(&self, path: &Path) -> io::Result<()> {
        static STORES: std::sync::Mutex<()> = std::sync::Mutex::new(());
        let _store = STORES
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let stored = Self::load(path)?;
        let mut merged = stored.clone();
        for (peer, first) in &self.peers {
            merged.peers.entry(*peer).or_insert(*first);
        }
        merged.reincarnated.extend(&self.reincarnated);
        merged.reused |= self.reused;
        if merged == stored {
            return Ok(());
        }
        replace_json(path, &merged)
    }
}

/// The boundary of the WAL format before segments, a JSON file replaced by
/// rename on every round.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub(super) struct Boundary {
    incarnation: Uuid,
    pub generation: Uuid,
    pub len: u64,
    pub digest: [u8; 32],
}

pub(super) enum Opened {
    Legacy(Boundary),
    Current,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(super) struct CheckpointRef {
    pub id: Uuid,
    pub len: u64,
    pub digest: [u8; 32],
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub(super) struct Slot {
    pub sequence: u64,
    pub segment: u64,
    pub offset: u64,
    pub chain: [u8; 32],
    pub checkpoint: Option<CheckpointRef>,
}

pub(super) struct Boundaries {
    file: File,
    incarnation: Uuid,
    last: Slot,
}

impl Enrollment {
    pub fn authorized(
        registry: &Path,
        data: &Path,
        keeper: Uuid,
        catalog: Uuid,
        domain: &str,
        certificate: &Path,
    ) -> io::Result<Self> {
        let registry = registry.canonicalize()?;
        let data = canonical_target(data)?;
        if registry.starts_with(&data) || data.starts_with(&registry) {
            return Err(invalid("enrollment registry must be outside keeper media"));
        }
        let provision: Provision = read_json(&registry.join(format!("{keeper}.provision.json")))?;
        if provision.keeper != keeper
            || provision.data != data
            || provision.domain != domain
            || provision.certificate_sha256 != hex(&sha256(File::open(certificate)?)?)
        {
            return Err(invalid(
                "keeper does not match its enrollment authorization",
            ));
        }
        Ok(Self {
            registry,
            data,
            keeper,
            catalog,
        })
    }

    pub fn initialize(self) -> io::Result<()> {
        let media = self.enroll(FORMAT)?;
        sync_file(
            &OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(media.data().join("LOCK"))?,
        )?;
        let segments = media.data().join(segment::DIRECTORY);
        fs::create_dir(&segments)?;
        sync_directory(media.data())?;
        segment::create(&segments, segment::FIRST, media.identity.incarnation)?;
        media.create_boundaries(&Slot {
            sequence: 1,
            segment: segment::FIRST,
            offset: segment::HEADER,
            chain: segment::seed(media.identity.incarnation),
            checkpoint: None,
        })?;
        create_json(&media.data().join("KEEPER"), &media.identity)?;
        sync_directory(media.data())
    }

    /// Installs media in the format before segments, as older keepers did.
    #[cfg(test)]
    pub fn initialize_legacy(self) -> io::Result<()> {
        let media = self.enroll(LEGACY_FORMAT)?;
        let generation = Uuid::new_v4();
        sync_file(
            &OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(media.wal(generation))?,
        )?;
        sync_file(
            &OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(media.data().join("LOCK"))?,
        )?;
        sync_directory(media.data())?;
        media.publish(generation, 0, sha2::Sha256::digest([]).into())?;
        create_json(&media.data().join("KEEPER"), &media.identity)?;
        sync_directory(media.data())
    }

    fn enroll(self, format: &str) -> io::Result<Media> {
        match fs::create_dir(&self.data) {
            Ok(()) => sync_directory(self.data.parent().unwrap())?,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => (),
            Err(error) => return Err(error),
        }
        if fs::read_dir(&self.data)?.next().transpose()?.is_some() {
            return Err(invalid("keeper initialization requires empty media"));
        }
        let identity = Identity {
            format: format.into(),
            keeper: self.keeper,
            catalog: self.catalog,
            incarnation: Uuid::new_v4(),
        };
        // The exclusive creation is the one-shot enrollment CAS. Once it has
        // reached stable storage, a failed install needs a fresh keeper ID.
        create_json(&self.enrolled(), &identity)?;
        sync_directory(&self.registry)?;
        Ok(Media {
            enrollment: self,
            identity,
        })
    }

    pub(super) fn open(self) -> io::Result<(Media, File, Opened)> {
        let lock = OpenOptions::new()
            .write(true)
            .open(self.data.join("LOCK"))?;
        lock.try_lock_exclusive()?;
        let identity: Identity = read_json(&self.enrolled())?;
        let installed: Identity = read_json(&self.data.join("KEEPER"))?;
        let legacy = identity.format == LEGACY_FORMAT;
        let unfinished = installed.format == LEGACY_FORMAT;
        if identity.keeper != installed.keeper
            || identity.catalog != installed.catalog
            || identity.incarnation != installed.incarnation
            || identity.keeper != self.keeper
            || identity.catalog != self.catalog
            || identity.incarnation.is_nil()
            || !matches!(
                (identity.format.as_str(), installed.format.as_str()),
                (FORMAT, FORMAT) | (FORMAT, LEGACY_FORMAT) | (LEGACY_FORMAT, LEGACY_FORMAT)
            )
        {
            return Err(invalid("missing or foreign installed keeper media"));
        }
        // A warm restart can observe either side of an interrupted publication.
        sync_directory(&self.registry)?;
        sync_directory(&self.data)?;
        let media = Media {
            enrollment: self,
            identity,
        };
        if legacy {
            let boundary: Boundary = read_json(&media.enrollment.legacy_boundary())?;
            if boundary.incarnation != media.identity.incarnation || boundary.generation.is_nil() {
                return Err(invalid("WAL boundary belongs to another media incarnation"));
            }
            return Ok((media, lock, Opened::Legacy(boundary)));
        }
        if unfinished {
            // The registry committed a migration the data volume did not
            // finish recording.
            media.finish_migration()?;
        }
        Ok((media, lock, Opened::Current))
    }

    fn enrolled(&self) -> PathBuf {
        self.registry.join(format!("{}.enrolled", self.keeper))
    }

    fn legacy_boundary(&self) -> PathBuf {
        self.registry.join(format!("{}.wal", self.keeper))
    }

    fn boundaries(&self) -> PathBuf {
        self.registry.join(format!("{}.boundary", self.keeper))
    }

    #[cfg(test)]
    pub fn test(data: PathBuf, registry: PathBuf, keeper: Uuid) -> Self {
        Self {
            data,
            registry,
            keeper,
            catalog: keeper,
        }
    }

    #[cfg(test)]
    pub fn boundary_path(&self) -> PathBuf {
        self.boundaries()
    }
}

impl Media {
    pub fn data(&self) -> &Path {
        &self.enrollment.data
    }

    pub fn incarnation(&self) -> Uuid {
        self.identity.incarnation
    }

    pub fn wal(&self, generation: Uuid) -> PathBuf {
        self.data().join(format!("raft-{generation}.wal"))
    }

    pub fn boundaries(&self) -> io::Result<(Boundaries, Slot)> {
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(self.enrollment.boundaries())?;
        let mut bytes = Vec::new();
        (&mut file)
            .take(2 * SLOT_BYTES as u64 + 1)
            .read_to_end(&mut bytes)?;
        if bytes.len() != 2 * SLOT_BYTES {
            return Err(invalid("WAL boundary slots have the wrong size"));
        }
        let incarnation = self.identity.incarnation;
        let last = bytes
            .chunks(SLOT_BYTES)
            .enumerate()
            .filter_map(|(index, slot)| Slot::decode(slot, incarnation, index * SLOT_BYTES))
            .max_by_key(|slot| slot.sequence)
            .ok_or_else(|| invalid("WAL boundary has no intact slot"))?;
        Ok((
            Boundaries {
                file,
                incarnation,
                last,
            },
            last,
        ))
    }

    fn create_boundaries(&self, slot: &Slot) -> io::Result<()> {
        let mut bytes = vec![0; 2 * SLOT_BYTES];
        let at = slot.index();
        bytes[at..at + SLOT_BYTES].copy_from_slice(&slot.encode(self.identity.incarnation)?);
        let target = self.enrollment.boundaries();
        let temporary = target.with_extension("boundary.tmp");
        let mut file = OpenOptions::new()
            .write(true)
            .truncate(true)
            .create(true)
            .open(&temporary)?;
        file.write_all(&bytes)?;
        sync_file(&file)?;
        fs::rename(&temporary, &target)?;
        sync_directory(&self.enrollment.registry)
    }

    /// Commits a migration from the format before segments. Until the
    /// registry identity changes, a restart migrates again from the old WAL.
    pub fn migrate(&self, slot: &Slot) -> io::Result<()> {
        self.create_boundaries(slot)?;
        let identity = Identity {
            format: FORMAT.into(),
            ..self.identity.clone()
        };
        replace_json(&self.enrollment.enrolled(), &identity)?;
        self.finish_migration()
    }

    fn finish_migration(&self) -> io::Result<()> {
        let identity = Identity {
            format: FORMAT.into(),
            ..self.identity.clone()
        };
        replace_json(&self.data().join("KEEPER"), &identity)?;
        let legacy = self.enrollment.legacy_boundary();
        remove_if_present(&legacy.with_extension("wal.tmp"))?;
        remove_if_present(&legacy)?;
        sync_directory(&self.enrollment.registry)?;
        for item in fs::read_dir(self.data())? {
            let item = item?;
            if item
                .file_name()
                .to_str()
                .is_some_and(|name| name.starts_with("raft-") && name.ends_with(".wal"))
            {
                fs::remove_file(item.path())?;
            }
        }
        sync_directory(self.data())
    }

    /// Removes what an interrupted migration wrote before its commit.
    pub fn discard_unpublished_boundaries(&self) -> io::Result<()> {
        let target = self.enrollment.boundaries();
        remove_if_present(&target.with_extension("boundary.tmp"))?;
        remove_if_present(&target)?;
        sync_directory(&self.enrollment.registry)
    }

    #[cfg(test)]
    pub fn check_wal(&self, generation: Uuid, file: &File, len: u64) -> io::Result<()> {
        let named = fs::metadata(self.wal(generation))?;
        let opened = file.metadata()?;
        if len != opened.len() || len != named.len() {
            return Err(invalid("open WAL no longer matches its published length"));
        }
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            if (opened.dev(), opened.ino()) != (named.dev(), named.ino()) {
                return Err(invalid("open WAL no longer matches its generation"));
            }
        }
        Ok(())
    }

    #[cfg(test)]
    pub fn publish(&self, generation: Uuid, len: u64, digest: [u8; 32]) -> io::Result<()> {
        let boundary = Boundary {
            incarnation: self.identity.incarnation,
            generation,
            len,
            digest,
        };
        let target = self.enrollment.legacy_boundary();
        let temporary = target.with_extension("wal.tmp");
        let mut file = OpenOptions::new()
            .write(true)
            .truncate(true)
            .create(true)
            .open(&temporary)?;
        serde_json::to_writer(&mut file, &boundary)?;
        sync_file(&file)?;
        fs::rename(temporary, target)?;
        sync_directory(&self.enrollment.registry)
    }
}

impl Slot {
    fn index(&self) -> usize {
        (self.sequence % 2) as usize * SLOT_BYTES
    }

    // magic | incarnation | body length | body | crc32 of all before it
    fn encode(&self, incarnation: Uuid) -> io::Result<Vec<u8>> {
        let body = crate::stream::consensus::encode(self)?;
        let mut bytes = SLOT_MAGIC.to_vec();
        bytes.extend(incarnation.as_bytes());
        bytes.extend((body.len() as u16).to_le_bytes());
        bytes.extend(body);
        bytes.extend(crc32fast::hash(&bytes).to_le_bytes());
        if bytes.len() > SLOT_BYTES {
            return Err(invalid("WAL boundary slot exceeds its size"));
        }
        bytes.resize(SLOT_BYTES, 0);
        Ok(bytes)
    }

    fn decode(bytes: &[u8], incarnation: Uuid, at: usize) -> Option<Self> {
        let rest = bytes
            .strip_prefix(SLOT_MAGIC)?
            .strip_prefix(incarnation.as_bytes())?;
        let len = u16::from_le_bytes(rest.get(..2)?.try_into().ok()?) as usize;
        let end = SLOT_MAGIC.len() + 16 + 2 + len;
        let crc = bytes.get(end..end + 4)?;
        if crc32fast::hash(&bytes[..end]).to_le_bytes() != crc {
            return None;
        }
        let slot: Self = crate::stream::consensus::decode(&rest[2..2 + len]).ok()?;
        (slot.index() == at).then_some(slot)
    }
}

impl Boundaries {
    /// Publishes the next boundary over the older slot. A torn write leaves
    /// the newer slot, which names a boundary the data volume still holds.
    pub fn write(
        &mut self,
        segment: u64,
        offset: u64,
        chain: [u8; 32],
        checkpoint: Option<CheckpointRef>,
    ) -> io::Result<()> {
        let slot = Slot {
            sequence: self.last.sequence + 1,
            segment,
            offset,
            chain,
            checkpoint,
        };
        self.file.seek(SeekFrom::Start(slot.index() as u64))?;
        self.file.write_all(&slot.encode(self.incarnation)?)?;
        sync_data(&self.file)?;
        self.last = slot;
        Ok(())
    }
}

fn canonical_target(path: &Path) -> io::Result<PathBuf> {
    let name = path
        .file_name()
        .ok_or_else(|| invalid("keeper media needs a directory name"))?;
    let parent = path
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let canonical = parent.canonicalize()?.join(name);
    if canonical
        .symlink_metadata()
        .is_ok_and(|metadata| metadata.file_type().is_symlink())
    {
        return Err(invalid("keeper media path cannot be a symlink"));
    }
    Ok(canonical)
}

fn read_json<T: DeserializeOwned>(path: &Path) -> io::Result<T> {
    read_bounded(path, 16 * 1024)
}

fn read_bounded<T: DeserializeOwned>(path: &Path, limit: u64) -> io::Result<T> {
    let file = File::open(path)?;
    let mut bytes = Vec::new();
    file.take(limit + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 > limit {
        return Err(invalid("enrollment registry record exceeds its size bound"));
    }
    serde_json::from_slice(&bytes).map_err(io::Error::other)
}

fn create_json(path: &Path, value: &impl Serialize) -> io::Result<()> {
    let mut file = OpenOptions::new().write(true).create_new(true).open(path)?;
    serde_json::to_writer(&mut file, value)?;
    file.flush()?;
    sync_file(&file)
}

fn replace_json(path: &Path, value: &impl Serialize) -> io::Result<()> {
    let temporary = path.with_extension("tmp");
    let mut file = OpenOptions::new()
        .write(true)
        .truncate(true)
        .create(true)
        .open(&temporary)?;
    serde_json::to_writer(&mut file, value)?;
    sync_file(&file)?;
    fs::rename(&temporary, path)?;
    sync_directory(path.parent().unwrap())
}

fn remove_if_present(path: &Path) -> io::Result<()> {
    match fs::remove_file(path) {
        Err(error) if error.kind() != io::ErrorKind::NotFound => Err(error),
        _ => Ok(()),
    }
}

pub(in crate::stream::consensus) fn sha256(mut source: impl Read) -> io::Result<[u8; 32]> {
    let mut digest = sha2::Sha256::new();
    io::copy(&mut source, &mut digest)?;
    Ok(digest.finalize().into())
}

pub(in crate::stream::consensus) fn hex(digest: &[u8]) -> String {
    use std::fmt::Write as _;
    digest.iter().fold(String::new(), |mut out, byte| {
        write!(&mut out, "{byte:02x}").unwrap();
        out
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn incarnation_records_only_grow() {
        let root = tempfile::tempdir().unwrap();
        let path = Incarnations::path(root.path(), Uuid::new_v4());
        assert_eq!(Incarnations::load(&path).unwrap(), Incarnations::default());
        let (peer, other) = (Uuid::new_v4(), Uuid::new_v4());
        let (first, second) = (Uuid::new_v4(), Uuid::new_v4());
        let newer = Incarnations {
            peers: BTreeMap::from([(peer, first), (other, first)]),
            reincarnated: BTreeSet::from([peer]),
            reused: true,
        };
        newer.store(&path).unwrap();
        // A stale store that lands last keeps the first incarnations and
        // the marks.
        Incarnations {
            peers: BTreeMap::from([(peer, second)]),
            ..Incarnations::default()
        }
        .store(&path)
        .unwrap();
        assert_eq!(Incarnations::load(&path).unwrap(), newer);
    }

    #[test]
    fn interrupted_enrollment_burns_identity_before_media_publication() {
        let root = tempfile::tempdir().unwrap();
        let registry = root.path().join("registry");
        let data = root.path().join("data");
        fs::create_dir(&registry).unwrap();
        fs::create_dir(&data).unwrap();
        let keeper = Uuid::new_v4();
        let enrollment = || Enrollment::test(data.clone(), registry.clone(), keeper);
        assert!(enrollment().open().is_err());
        create_json(
            &enrollment().enrolled(),
            &Identity {
                format: FORMAT.into(),
                keeper,
                catalog: keeper,
                incarnation: Uuid::new_v4(),
            },
        )
        .unwrap();
        sync_directory(&registry).unwrap();
        assert!(enrollment().open().is_err());
        assert!(enrollment().initialize().is_err());
        assert!(fs::read_dir(&data).unwrap().next().is_none());
        Enrollment::test(data, registry, Uuid::new_v4())
            .initialize()
            .unwrap();
    }
}
