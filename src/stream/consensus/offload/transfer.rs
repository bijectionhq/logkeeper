//! Online backup, export, import and restore through the offload store:
//! `logkeeper admin export-stream`, `import-stream` and `restore-stream`.
//!
//! An export asks the stream's leader to upload everything committed, then
//! copies the segment objects that hold the committed run from the logical
//! floor to the head, verbatim, into a directory with a manifest. An import
//! or a restore uploads those records under a new stream's lineage 0,
//! creates the stream and points it at them (`Request::Restore`), so the
//! keepers serve the history from the store and new appends continue at
//! the restored head. `restore-stream` reads the source stream's objects in
//! the store directly, which needs no surviving voter.

use std::{io, path::Path};

use journal_contract::{Epoch, Lsn, StreamId};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{Record, Store, format};
use crate::stream::consensus::{Client, invalid};

const MANIFEST: &str = "manifest.json";
const EXPORT_FORMAT: &str = "logkeeper-export/1";

/// What an export directory holds.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Manifest {
    pub format: String,
    pub stream: uuid::Uuid,
    /// The exported records are `floor..=head`.
    pub floor: Lsn,
    pub head: Lsn,
    /// The writer epoch when the export was taken.
    pub epoch: Epoch,
    pub parts: Vec<Part>,
    /// Whether the exported stream is immutable, so an import keeps its
    /// kind. Exports from before this field are of mutable streams.
    #[serde(default)]
    pub immutable: bool,
}

/// One copied segment object and the records of it the export uses.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Part {
    pub file: String,
    pub lineage: u64,
    pub first: Lsn,
    pub last: Lsn,
    pub sha256: String,
}

/// Records to load into a new stream, and the run they form.
pub struct Loaded {
    pub floor: Lsn,
    pub head: Lsn,
    pub epoch: Epoch,
    pub batches: Vec<Vec<Record>>,
    /// Whether the source stream is immutable: the restored or imported
    /// stream is created with the same kind.
    pub immutable: bool,
}

/// Whether the catalog claimed `stream` as immutable.
pub async fn immutable(client: &Client, stream: StreamId) -> io::Result<bool> {
    match client.require_immutable(stream).await {
        Ok(()) => Ok(true),
        Err(journal_contract::JournalError::Unsupported) => Ok(false),
        Err(error) => Err(journal_error(error)),
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn journal_error(error: journal_contract::JournalError) -> io::Error {
    io::Error::other(format!("{error:?}"))
}

/// Exports `stream` into `directory`, which must not exist yet.
pub async fn export(
    client: &Client,
    store: &Store,
    stream: StreamId,
    directory: &Path,
) -> io::Result<Manifest> {
    let status = client
        .offload_status(stream, true)
        .await
        .map_err(journal_error)?;
    if status.offloaded_through < status.head {
        return Err(invalid("the leader did not upload every committed record"));
    }
    let plan = store.plan(stream, &status.lineages, status.floor).await?;
    let covered = status.head < status.floor
        || plan
            .run
            .is_some_and(|(first, last)| first <= status.floor && last >= status.head);
    if !covered {
        return Err(invalid(format!(
            "the object store does not hold records {}..={} contiguously",
            status.floor.0, status.head.0
        )));
    }
    std::fs::create_dir(directory)?;
    std::fs::create_dir(directory.join("objects"))?;
    let mut parts = Vec::new();
    for (object, first, last) in &plan.parts {
        if *last < status.floor || *first > status.head {
            continue;
        }
        let bytes = store.get(&object.path).await?;
        // Verify before copying: an export never carries a damaged object.
        store.segment(stream, object).await?;
        let file = format!(
            "objects/{:016x}-{:020}-{:020}.seg",
            object.lineage, object.first.0, object.last.0
        );
        std::fs::write(directory.join(&file), &bytes)?;
        parts.push(Part {
            file,
            lineage: object.lineage,
            first: (*first).max(status.floor),
            last: (*last).min(status.head),
            sha256: hex(&Sha256::digest(&bytes)),
        });
    }
    let manifest = Manifest {
        format: EXPORT_FORMAT.into(),
        stream: uuid::Uuid::from_u128(stream.0),
        floor: status.floor,
        head: status.head,
        epoch: status.epoch,
        parts,
        immutable: immutable(client, stream).await?,
    };
    let encoded = serde_json::to_vec_pretty(&manifest)?;
    std::fs::write(directory.join(MANIFEST), encoded)?;
    crate::stream::keeper::durability::sync_directory(directory)?;
    Ok(manifest)
}

/// Reads and verifies an export directory.
pub fn read_export(directory: &Path) -> io::Result<Loaded> {
    let manifest: Manifest = serde_json::from_slice(&std::fs::read(directory.join(MANIFEST))?)?;
    if manifest.format != EXPORT_FORMAT {
        return Err(invalid(format!(
            "unknown export format {:?}",
            manifest.format
        )));
    }
    let stream = StreamId(manifest.stream.as_u128());
    let mut batches = Vec::new();
    let mut next = manifest.floor;
    for part in &manifest.parts {
        if part.file.contains("..") || part.first != next || part.last < part.first {
            return Err(invalid("the export's parts are not contiguous"));
        }
        let bytes = bytes::Bytes::from(std::fs::read(directory.join(&part.file))?);
        if hex(&Sha256::digest(&bytes)) != part.sha256 {
            return Err(invalid(format!("{} is damaged", part.file)));
        }
        let segment = format::decode_segment(&bytes)?;
        if segment.header.stream != stream || segment.header.lineage != part.lineage {
            return Err(invalid(format!("{} belongs to another stream", part.file)));
        }
        batches.push(
            segment
                .records
                .into_iter()
                .filter(|record| record.lsn >= part.first && record.lsn <= part.last)
                .collect::<Vec<_>>(),
        );
        if batches.last().map(Vec::len) != Some((part.last.0 - part.first.0 + 1) as usize) {
            return Err(invalid(format!(
                "{} lacks records it should hold",
                part.file
            )));
        }
        next = Lsn(part.last.0 + 1);
    }
    if manifest.head >= manifest.floor && next != Lsn(manifest.head.0 + 1) {
        return Err(invalid("the export ends before its head"));
    }
    Ok(Loaded {
        floor: manifest.floor,
        head: manifest.head,
        epoch: manifest.epoch,
        batches,
        immutable: manifest.immutable,
    })
}

/// Reads the longest committed run of `source` the store holds from
/// `floor` on, for a restore with no surviving voter. The store does not
/// know the writer's trim floor: objects uploaded before a trim still hold
/// the trimmed records, so the operator names the floor to keep them out.
pub async fn read_store(store: &Store, source: StreamId, floor: Lsn) -> io::Result<Loaded> {
    let (_, lineages) = store.discover(source).await?;
    let plan = store.plan(source, &lineages, floor.max(Lsn(1))).await?;
    let Some((floor, head)) = plan.run else {
        return Err(invalid("the object store holds no records of the stream"));
    };
    let mut epoch = Epoch(0);
    let mut batches = Vec::new();
    for (segment, first, last) in store.segments(source, &plan).await? {
        epoch = epoch.max(segment.max_epoch());
        batches.push(
            segment
                .records
                .iter()
                .filter(|record| record.lsn >= first && record.lsn <= last)
                .cloned()
                .collect(),
        );
    }
    // The store holds records, not the stream's kind: the caller takes it
    // from the catalog's claim for the source.
    Ok(Loaded {
        floor,
        head,
        epoch,
        batches,
        immutable: false,
    })
}

/// Uploads loaded records under `target`'s lineage 0. Idempotent.
pub async fn stage(store: &Store, target: StreamId, loaded: &Loaded) -> io::Result<()> {
    for batch in loaded.batches.iter().filter(|batch| !batch.is_empty()) {
        store.upload(target, 0, batch, Vec::new()).await?;
    }
    Ok(())
}
