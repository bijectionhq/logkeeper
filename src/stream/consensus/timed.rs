//! Timed originals on consensus streams.
//!
//! A writer stages the exact payload of a timed original on the first two
//! voters of the stream's current roster. Each voter syncs the stage as a
//! shadow file outside the log, samples its commissioned clock for an upper
//! bound on that durability event and signs the sample. The writer then
//! appends the record with both samples as its evidence. Any reader can later
//! fetch the retained evidence and verify it against installed keeper keys.

use std::{
    collections::HashMap,
    fmt,
    fs::{self, File, OpenOptions},
    io::{self, Read, Write},
    path::{Path, PathBuf},
    sync::Arc,
};

use bytes::Bytes;
use journal_contract::StreamId;
use parking_lot::Mutex;

use crate::stream::{
    keeper::durability::{sync_directory, sync_file},
    timed::{
        ORIGINAL_BYTES, SAMPLE_BYTES, TimedOrigin, TimedOriginal, TimedOriginalClock,
        TimedOriginalVerifier, TimedSample,
    },
    wire::KeeperId,
};

/// A keeper's installed timed-original trust and, on a signing keeper, its
/// commissioned clock and attestation key.
#[derive(Clone)]
pub struct TimedAuthority {
    pub verifier: Arc<dyn TimedOriginalVerifier>,
    pub clock: Option<Arc<dyn TimedOriginalClock>>,
}

impl fmt::Debug for TimedAuthority {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TimedAuthority")
            .field("signing", &self.clock.is_some())
            .finish()
    }
}

/// The roster binding of a staged original: its sorted voters and a
/// nonzero proposal derived from the configuration revision.
pub(super) fn origin(
    original: TimedOriginal,
    voters: [uuid::Uuid; 3],
    revision: u64,
) -> TimedOrigin {
    let mut voters = voters;
    voters.sort_unstable();
    TimedOrigin {
        original,
        ensemble: voters.map(|voter| KeeperId(voter.as_u128())),
        proposal: u128::from(revision) + 1,
    }
}

/// Durable shadow stages, one per stream, under the keeper's data directory.
pub(super) struct Stages {
    root: PathBuf,
    originals: Mutex<HashMap<StreamId, TimedOriginal>>,
}

impl Stages {
    pub fn open(data: &Path) -> io::Result<Self> {
        let root = data.join("timed-original");
        fs::create_dir_all(&root)?;
        let mut originals = HashMap::new();
        for file in fs::read_dir(&root)? {
            let path = file?.path();
            if path.extension().is_some_and(|ext| ext == "tmp") {
                fs::remove_file(path)?;
                continue;
            }
            let mut header = [0; ORIGINAL_BYTES];
            File::open(&path)?.read_exact(&mut header)?;
            let original = TimedOriginal::decode(&header)
                .ok_or_else(|| super::invalid("invalid timed original stage file"))?;
            let stream = StreamId(original.stream.0);
            if path != Self::path_in(&root, stream) {
                return Err(super::invalid("misplaced timed original stage file"));
            }
            originals.insert(stream, original);
        }
        sync_directory(&root)?;
        Ok(Self {
            root,
            originals: Mutex::new(originals),
        })
    }

    fn path_in(root: &Path, stream: StreamId) -> PathBuf {
        root.join(format!("{:032x}.stage", stream.0))
    }

    /// Stages `payload` for `origin` and returns this keeper's signed sample.
    /// A repeated stage of the same original returns the stored sample and
    /// never samples again. A different original replaces the stage only
    /// when the earlier one can no longer commit: its position is at or below
    /// `applied_head` or its epoch is below `epoch`.
    pub fn stage(
        &self,
        keeper: KeeperId,
        origin: TimedOrigin,
        payload: &Bytes,
        applied_head: u64,
        epoch: u64,
        clock: &dyn TimedOriginalClock,
        verifier: &dyn TimedOriginalVerifier,
    ) -> io::Result<Option<TimedSample>> {
        let original = origin.original;
        let stream = StreamId(original.stream.0);
        let path = Self::path_in(&self.root, stream);
        let header = origin.encode();
        let mut originals = self.originals.lock();
        if let Some(prior) = originals.get(&stream).copied() {
            if prior == original {
                let mut stored = Vec::new();
                File::open(&path)?
                    .take((header.len() + payload.len() + SAMPLE_BYTES + 1) as u64)
                    .read_to_end(&mut stored)?;
                // A crash after the first sync can leave the bytes without a
                // bound. That stage never signs.
                let sample = stored
                    .strip_prefix(header.as_slice())
                    .and_then(|bytes| bytes.strip_prefix(payload.as_ref()))
                    .and_then(TimedSample::decode)
                    .filter(|sample| origin.verifies(keeper, *sample, verifier));
                return Ok(sample);
            }
            if prior.at.0 > applied_head && prior.epoch.0 >= epoch {
                return Ok(None);
            }
        }
        if !clock.authorize(&original) {
            return Ok(None);
        }
        atomic_write(&self.root, &path, &[&header, payload])?;
        originals.insert(stream, original);
        let Some(upper_micros) = clock
            .sync_upper_micros(&original)
            .filter(|upper| origin.timely(*upper))
        else {
            return Ok(None);
        };
        let Some(signature) = clock.sign(&origin.statement(keeper, upper_micros)) else {
            return Ok(None);
        };
        let sample = TimedSample {
            upper_micros,
            signature,
        };
        if !origin.verifies(keeper, sample, verifier) {
            return Ok(None);
        }
        // Publish the witness only after the exact stage was synced and
        // sampled. Either file at the replacement holds the original bytes.
        atomic_write(&self.root, &path, &[&header, payload, &sample.encode()])?;
        Ok(Some(sample))
    }
}

fn atomic_write(root: &Path, path: &Path, parts: &[&[u8]]) -> io::Result<()> {
    let temporary = path.with_extension("tmp");
    let mut file = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&temporary)?;
    for part in parts {
        file.write_all(part)?;
    }
    sync_file(&file)?;
    fs::rename(&temporary, path)?;
    sync_directory(root)
}
