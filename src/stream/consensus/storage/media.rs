//! The enrollment registry survives loss of a keeper's journal directory.

use std::{
    fs::{self, File, OpenOptions},
    io::{self, Read, Write},
    path::{Path, PathBuf},
};

use fs2::FileExt;
use serde::{Deserialize, Serialize, de::DeserializeOwned};
use sha2::{Digest, Sha256};
use uuid::Uuid;

use crate::stream::{
    consensus::{Domains, invalid},
    keeper::durability::{sync_directory, sync_file},
};

const FORMAT: &str = "logkeeper-raft-2";

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

#[derive(Debug, Eq, PartialEq, Serialize, Deserialize)]
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

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
pub(super) struct Boundary {
    incarnation: Uuid,
    pub generation: Uuid,
    pub len: u64,
    pub digest: [u8; 32],
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
        match fs::create_dir(&self.data) {
            Ok(()) => sync_directory(self.data.parent().unwrap())?,
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => (),
            Err(error) => return Err(error),
        }
        if fs::read_dir(&self.data)?.next().transpose()?.is_some() {
            return Err(invalid("keeper initialization requires empty media"));
        }
        let identity = Identity {
            format: FORMAT.into(),
            keeper: self.keeper,
            catalog: self.catalog,
            incarnation: Uuid::new_v4(),
        };
        // The exclusive creation is the one-shot enrollment CAS. Once it has
        // reached stable storage, a failed install needs a fresh keeper ID.
        create_json(&self.enrolled(), &identity)?;
        sync_directory(&self.registry)?;
        let media = Media {
            enrollment: self,
            identity,
        };
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
        media.publish(generation, 0, Sha256::digest([]).into())?;
        create_json(&media.data().join("KEEPER"), &media.identity)?;
        sync_directory(media.data())
    }

    pub(super) fn open(self) -> io::Result<(Media, File, Boundary)> {
        let lock = OpenOptions::new()
            .write(true)
            .open(self.data.join("LOCK"))?;
        lock.try_lock_exclusive()?;
        let identity: Identity = read_json(&self.enrolled())?;
        let installed: Identity = read_json(&self.data.join("KEEPER"))?;
        if identity != installed
            || identity.keeper != self.keeper
            || identity.catalog != self.catalog
            || identity.format != FORMAT
            || identity.incarnation.is_nil()
        {
            return Err(invalid("missing or foreign installed keeper media"));
        }
        let boundary: Boundary = read_json(&self.boundary())?;
        if boundary.incarnation != identity.incarnation || boundary.generation.is_nil() {
            return Err(invalid("WAL boundary belongs to another media incarnation"));
        }
        // A warm restart can observe either side of an interrupted publication.
        sync_directory(&self.registry)?;
        sync_directory(&self.data)?;
        Ok((
            Media {
                enrollment: self,
                identity,
            },
            lock,
            boundary,
        ))
    }

    fn enrolled(&self) -> PathBuf {
        self.registry.join(format!("{}.enrolled", self.keeper))
    }

    fn boundary(&self) -> PathBuf {
        self.registry.join(format!("{}.wal", self.keeper))
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
}

impl Media {
    pub fn data(&self) -> &Path {
        &self.enrollment.data
    }

    pub fn wal(&self, generation: Uuid) -> PathBuf {
        self.data().join(format!("raft-{generation}.wal"))
    }

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

    pub fn publish(&self, generation: Uuid, len: u64, digest: [u8; 32]) -> io::Result<()> {
        self.prepare_boundary(generation, len, digest)?;
        self.publish_boundary()
    }

    pub fn prepare_boundary(&self, generation: Uuid, len: u64, digest: [u8; 32]) -> io::Result<()> {
        let boundary = Boundary {
            incarnation: self.identity.incarnation,
            generation,
            len,
            digest,
        };
        let target = self.enrollment.boundary();
        let temporary = target.with_extension("wal.tmp");
        let mut file = OpenOptions::new()
            .write(true)
            .truncate(true)
            .create(true)
            .open(&temporary)?;
        serde_json::to_writer(&mut file, &boundary)?;
        sync_file(&file)
    }

    pub fn publish_boundary(&self) -> io::Result<()> {
        let target = self.enrollment.boundary();
        fs::rename(target.with_extension("wal.tmp"), target)?;
        sync_directory(&self.enrollment.registry)
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

pub(in crate::stream::consensus) fn sha256(mut source: impl Read) -> io::Result<[u8; 32]> {
    let mut digest = Sha256::new();
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
