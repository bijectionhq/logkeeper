//! Keeper-local original stages are durable shadow writes. They never increase
//! the accepted tail. Only a certified AppendOriginal can enter the log.

use std::{
    collections::HashMap,
    fs::{self, File},
    io::{self, Read, Write},
    path::{Path, PathBuf},
    sync::Arc,
};

use bytes::Bytes;

use super::{
    Limits,
    durability::sync_directory,
    rules::{self, Decision},
    state::{ExtentReader, Stream},
    wal::{atomic_file, directories},
};
use crate::stream::{
    codec::invalid,
    timed::{
        EVIDENCE_BYTES, MAX_TIMED_PAYLOAD, ORIGINAL_BYTES, SAMPLE_BYTES, TimedOrigin,
        TimedOriginal, TimedOriginalClock, TimedOriginalVerifier, TimedSample,
    },
    wire::*,
};

pub(super) struct Authority {
    pub verifier: Arc<dyn TimedOriginalVerifier>,
    pub clock: Option<Arc<dyn TimedOriginalClock>>,
}

pub(super) struct Stages {
    root: PathBuf,
    originals: HashMap<StreamId, TimedOriginal>,
}

impl Stages {
    pub fn open(
        path: &Path,
        streams: &HashMap<StreamId, Stream>,
        create: bool,
    ) -> io::Result<Self> {
        let root = path.join("timed-original");
        if create {
            directories(&root)?;
        }
        let mut stages = Self {
            root,
            originals: HashMap::new(),
        };
        let files = match fs::read_dir(&stages.root) {
            Ok(files) => files,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(stages),
            Err(error) => return Err(error),
        };
        for file in files {
            let path = file?.path();
            if path.extension().is_some_and(|ext| ext == "tmp") {
                fs::remove_file(path)?;
                continue;
            }
            let mut header = [0; ORIGINAL_BYTES];
            File::open(&path)?.read_exact(&mut header)?;
            let original = TimedOriginal::decode(&header)
                .filter(|original| path == stages.path(original.stream))
                .ok_or_else(|| invalid("invalid original stage file"))?;
            stages.originals.insert(original.stream, original);
        }
        let ids: Vec<_> = stages.originals.keys().copied().collect();
        for id in ids {
            stages.retire(id, streams.get(&id))?;
        }
        sync_directory(&stages.root)?;
        Ok(stages)
    }

    fn path(&self, stream: StreamId) -> PathBuf {
        self.root.join(format!("{:032x}.stage", stream.0))
    }

    /// Retire a stage only after the superseding journal change is durable.
    pub fn retire(&mut self, id: StreamId, stream: Option<&Stream>) -> io::Result<()> {
        let Some(original) = self.originals.get(&id) else {
            return Ok(());
        };
        if stream.is_some_and(|state| {
            !state.deleted
                && original.at > state.view.tail
                && state
                    .view
                    .promised
                    .as_ref()
                    .is_some_and(|(epoch, ..)| *epoch == original.epoch)
        }) {
            return Ok(());
        }
        fs::remove_file(self.path(id))?;
        sync_directory(&self.root)?;
        self.originals.remove(&id);
        Ok(())
    }

    pub fn blocks(&self, request: &Request) -> bool {
        let Request::Append {
            stream,
            epoch,
            at,
            records,
            ..
        } = request
        else {
            return false;
        };
        self.originals.get(stream).is_some_and(|original| {
            original.epoch == *epoch
                && *at <= original.at
                && rules::last(*at, records.len()).is_some_and(|last| last >= original.at)
        })
    }

    pub fn write(
        &mut self,
        keeper: KeeperId,
        origin: TimedOrigin,
        payload: Bytes,
        clock: &dyn TimedOriginalClock,
        verifier: &dyn TimedOriginalVerifier,
    ) -> io::Result<Reply> {
        let original = origin.original;
        let path = self.path(original.stream);
        let header = origin.encode();
        if let Some(prior) = self.originals.get(&original.stream) {
            if *prior != original {
                return Ok(Reply::Refused(Refusal::Unauthorized));
            }
            let mut stored = Vec::new();
            File::open(&path)?
                .take((header.len() + payload.len() + SAMPLE_BYTES + 1) as u64)
                .read_to_end(&mut stored)?;
            let witness = stored
                .strip_prefix(header.as_slice())
                .and_then(|bytes| bytes.strip_prefix(payload.as_ref()))
                .and_then(TimedSample::decode);
            // A crash after the first sync can leave the bytes without a bound.
            // Recovery must never sample that write again.
            return Ok(match witness {
                Some(sample) if origin.verifies(keeper, sample, verifier) => {
                    Reply::OriginalSample(sample)
                }
                _ => Reply::Refused(Refusal::Unauthorized),
            });
        }
        if !clock.authorize(&original) {
            return Ok(Reply::Refused(Refusal::Unauthorized));
        }
        atomic_file(&path, |file| {
            file.write_all(&header)?;
            file.write_all(&payload)
        })?;
        self.originals.insert(original.stream, original);

        let Some(upper_micros) = clock
            .sync_upper_micros(&original)
            .filter(|upper| origin.timely(*upper))
        else {
            return Ok(Reply::Refused(Refusal::Unauthorized));
        };
        let Some(signature) = clock.sign(&origin.statement(keeper, upper_micros)) else {
            return Ok(Reply::Refused(Refusal::Unauthorized));
        };
        let sample = TimedSample {
            upper_micros,
            signature,
        };
        if !origin.verifies(keeper, sample, verifier) {
            return Ok(Reply::Refused(Refusal::Unauthorized));
        }
        // Publish the witness only after the exact stage was synced and sampled.
        // Both files at the atomic replacement boundary hold the original bytes.
        atomic_file(&path, |file| {
            file.write_all(&header)?;
            file.write_all(&payload)?;
            file.write_all(&sample.encode())
        })?;
        Ok(Reply::OriginalSample(sample))
    }
}

pub(super) fn stage(
    stages: &mut Stages,
    authority: Option<&Authority>,
    keeper: KeeperId,
    state: Option<&Stream>,
    identity: &Identity,
    original: TimedOriginal,
    payload: Bytes,
    limits: &Limits,
) -> io::Result<Reply> {
    let refused = |refusal| Ok(Reply::Refused(refusal));
    let Some((authority, clock)) = authority.and_then(|a| Some((a, a.clock.as_deref()?))) else {
        return refused(Refusal::Unauthorized);
    };
    let Some(state) = state else {
        return refused(Refusal::NotFound);
    };
    if state.deleted {
        return refused(Refusal::Deleted);
    }
    let view = &state.view;
    let Some((epoch, owner, proposal)) = &view.promised else {
        return refused(Refusal::NotSynced);
    };
    if *epoch != original.epoch || owner != identity {
        return refused(Refusal::Fenced { promised: *epoch });
    }
    if view.synced != Some(*epoch) || view.learner || !view.ensemble[..2].contains(&keeper) {
        return refused(Refusal::NotSynced);
    }
    if original.at < view.floor {
        return refused(Refusal::BelowFloor { floor: view.floor });
    }
    if original.at.0 != view.tail.0 + 1 || view.head != view.tail {
        return refused(Refusal::Gap { head: view.head });
    }
    let max = (limits.max_record_bytes as usize)
        .saturating_sub(EVIDENCE_BYTES)
        .min(MAX_TIMED_PAYLOAD);
    if limits.max_record_bytes as usize <= EVIDENCE_BYTES || payload.len() > max {
        return refused(Refusal::TooLarge { max: max as u32 });
    }
    if rules::add_charge(
        state.bytes,
        rules::record_charge(EVIDENCE_BYTES + payload.len()),
    ) > limits.stream_quota_bytes
    {
        return refused(Refusal::Full { floor: view.floor });
    }
    if !original.matches(&payload) {
        return refused(Refusal::Unauthorized);
    }
    let origin = TimedOrigin {
        original,
        ensemble: view.ensemble,
        proposal: *proposal,
    };
    stages.write(keeper, origin, payload, clock, &*authority.verifier)
}

pub(super) fn check(
    authority: Option<&Authority>,
    state: Option<&Stream>,
    request: &Request,
    identity: &Identity,
    reader: &mut ExtentReader,
) -> io::Result<Option<Decision>> {
    let unauthorized = || Some(Decision::Reply(Reply::Refused(Refusal::Unauthorized)));
    match request {
        Request::AppendOriginal {
            stream,
            evidence,
            payload,
            ..
        }
        | Request::SyncOriginal {
            stream,
            evidence,
            payload,
            ..
        } => {
            let original = evidence.origin.original;
            if original.stream != *stream
                || payload.len() > MAX_TIMED_PAYLOAD
                || !original.matches(payload)
                || authority
                    .and_then(|a| evidence.proof(&*a.verifier))
                    .is_none()
            {
                return Ok(unauthorized());
            }
            if matches!(request, Request::AppendOriginal { .. })
                && let Some(state) = state
                && rules::promised(&state.view, original.epoch, identity)
                && (state.view.ensemble != evidence.origin.ensemble
                    || state.view.promised.as_ref().map(|(_, _, p)| *p)
                        != Some(evidence.origin.proposal))
            {
                return Ok(unauthorized());
            }
            Ok(None)
        }
        Request::ProveOriginal { stream, at } => {
            let reply = match state {
                None => Reply::Refused(Refusal::NotFound),
                Some(state) if state.deleted => Reply::Refused(Refusal::Deleted),
                Some(state) if *at < state.view.floor => Reply::Refused(Refusal::BelowFloor {
                    floor: state.view.floor,
                }),
                Some(state) if *at > state.view.head => Reply::Refused(Refusal::AboveHead {
                    head: state.view.head,
                }),
                Some(state) if !state.view.learner => {
                    if let Some(record) = state.record(*at).filter(|record| record.timed) {
                        let (evidence, _) = record.original(reader, *stream, *at)?;
                        if authority
                            .and_then(|a| evidence.proof(&*a.verifier))
                            .is_some()
                        {
                            Reply::OriginalEvidence(Arc::new(evidence))
                        } else {
                            Reply::Refused(Refusal::Unauthorized)
                        }
                    } else {
                        Reply::Refused(Refusal::Unauthorized)
                    }
                }
                Some(_) => Reply::Refused(Refusal::Unauthorized),
            };
            Ok(Some(Decision::Reply(reply)))
        }
        _ => Ok(None),
    }
}

/// An old or differently mounted keeper must fail closed when it reopens
/// certified media, including a staged successor copy awaiting installation.
pub(super) fn verify_retained(
    streams: &HashMap<StreamId, Stream>,
    authority: Option<&Authority>,
    reader: &mut ExtentReader,
) -> io::Result<()> {
    for (&id, stream) in streams {
        let retained = stream
            .records
            .iter()
            .enumerate()
            .map(|(i, record)| (Lsn(stream.view.floor.0 + i as u64), record));
        let staged = stream.staging.iter().flat_map(|stage| {
            stage
                .records
                .iter()
                .enumerate()
                .map(move |(i, record)| (Lsn(stage.from.0 + i as u64), record))
        });
        for (at, record) in retained.chain(staged).filter(|(_, record)| record.timed) {
            let (evidence, _) = record.original(reader, id, at)?;
            if authority
                .and_then(|a| evidence.proof(&*a.verifier))
                .is_none()
            {
                return Err(invalid("missing authority for retained timed evidence"));
            }
        }
    }
    Ok(())
}
