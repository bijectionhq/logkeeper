use std::{collections::VecDeque, fs::File, io, path::PathBuf, sync::Arc};

use bytes::{Bytes, BytesMut};
use tokio::sync::watch;

use super::{
    checkpoint_bytes::check_extent,
    rules::{self, Decision, Limits},
    wal_layout::checksum_matches,
};
use crate::stream::{
    codec::{PAGE_BYTES, invalid},
    timed::{EVIDENCE_BYTES, MAX_TIMED_PAYLOAD, TimedEvidence},
    wire::{self, *},
};

pub(super) struct Extent {
    pub sequence: u64,
    pub path: PathBuf,
}

pub(super) const EXTENT_COPY_BYTES: usize = 64 * 1024;

/// Keep one file open across sequential record reads, independent of stream count.
#[derive(Default)]
pub(super) struct ExtentReader(Option<(Arc<Extent>, File)>);

impl ExtentReader {
    fn file(&mut self, extent: &Arc<Extent>) -> io::Result<&mut File> {
        if !self
            .0
            .as_ref()
            .is_some_and(|(cached, _)| Arc::ptr_eq(cached, extent))
        {
            self.0 = Some((Arc::clone(extent), File::open(&extent.path)?));
        }
        Ok(&mut self.0.as_mut().expect("extent is open").1)
    }

    pub fn copy_checked(
        &mut self,
        extent: &Arc<Extent>,
        mut offset: u64,
        len: u32,
        expected_crc: u32,
        buffer: &mut [u8; EXTENT_COPY_BYTES],
        output: &mut impl io::Write,
    ) -> io::Result<()> {
        let end = offset
            .checked_add(u64::from(len))
            .ok_or_else(|| invalid("invalid stream extent range"))?;
        let file = self.file(extent)?;
        let mut crc = crc32fast::Hasher::new();
        while offset < end {
            let chunk_len = (end - offset).min(buffer.len() as u64) as usize;
            let chunk = &mut buffer[..chunk_len];
            read_at(file, chunk, offset)?;
            crc.update(chunk);
            output.write_all(chunk)?;
            offset += chunk_len as u64;
        }
        if !checksum_matches(expected_crc, crc.finalize()) {
            return Err(invalid("stream extent checksum mismatch"));
        }
        Ok(())
    }
}

// Keep shared backing small even when one reply outlives the other slices.
const PAGE_RUN_RECORDS: usize = 256;

struct ExtentRun {
    extent: Arc<Extent>,
    offset: u64,
    end: u64,
    records: Vec<(Lsn, u32, u32)>,
}

impl ExtentRun {
    fn can_extend(&self, extent: &Arc<Extent>, offset: u64, end: u64) -> bool {
        Arc::ptr_eq(&self.extent, extent)
            && offset == self.end
            && end - self.offset <= EXTENT_COPY_BYTES as u64
            && self.records.len() < PAGE_RUN_RECORDS
    }

    fn read(self, reader: &mut ExtentReader, output: &mut Vec<(Lsn, Bytes)>) -> io::Result<()> {
        let mut bytes = vec![0; (self.end - self.offset) as usize];
        read_at(reader.file(&self.extent)?, &mut bytes, self.offset)?;
        let bytes = Bytes::from(bytes);
        let mut start = 0;
        for (lsn, len, crc) in self.records {
            let end = start + len as usize;
            let payload = bytes.slice(start..end);
            if !check_extent(crc, &payload) {
                return Err(invalid("stream extent checksum mismatch"));
            }
            output.push((lsn, payload));
            start = end;
        }
        Ok(())
    }
}

#[cfg(unix)]
fn read_at(file: &mut File, bytes: &mut [u8], offset: u64) -> io::Result<()> {
    use std::os::unix::fs::FileExt;
    file.read_exact_at(bytes, offset)
}

#[cfg(not(unix))]
fn read_at(file: &mut File, bytes: &mut [u8], offset: u64) -> io::Result<()> {
    use std::io::{Read, Seek, SeekFrom};
    file.seek(SeekFrom::Start(offset))?;
    file.read_exact(bytes)
}

pub(super) enum Payload {
    Pending(Bytes),
    Extent {
        extent: Arc<Extent>,
        offset: u64,
        len: u32,
        crc: u32,
    },
}

impl Payload {
    pub fn len(&self) -> usize {
        match self {
            Self::Pending(bytes) => bytes.len(),
            Self::Extent { len, .. } => *len as usize,
        }
    }

    fn read(&self, reader: &mut ExtentReader) -> io::Result<Bytes> {
        match self {
            Self::Pending(bytes) => Ok(bytes.clone()),
            Self::Extent {
                extent,
                offset,
                len,
                crc,
            } => {
                let mut bytes = vec![0; *len as usize];
                read_at(reader.file(extent)?, &mut bytes, *offset)?;
                if !check_extent(*crc, &bytes) {
                    return Err(invalid("stream extent checksum mismatch"));
                }
                Ok(Bytes::from(bytes))
            }
        }
    }
}

#[derive(Clone)]
pub(super) struct Record {
    pub epoch: Epoch,
    pub timed: bool,
    // A checkpoint can move the same record even if a later Sync installed it
    // in a different position in the keeper's state.
    pub payload: Arc<parking_lot::RwLock<Payload>>,
}

impl Record {
    pub fn new(epoch: Epoch, payload: Payload) -> Self {
        Self {
            epoch,
            timed: false,
            payload: Arc::new(parking_lot::RwLock::new(payload)),
        }
    }

    pub fn with_timed(mut self, timed: bool) -> Self {
        self.timed = timed;
        self
    }

    pub fn len(&self) -> usize {
        self.payload.read().len()
    }

    fn read(&self, reader: &mut ExtentReader) -> io::Result<Bytes> {
        self.payload.read().read(reader)
    }

    pub(super) fn original(
        &self,
        reader: &mut ExtentReader,
        stream: StreamId,
        at: Lsn,
    ) -> io::Result<(TimedEvidence, Bytes)> {
        let bytes = self.read(reader)?;
        let evidence = bytes
            .get(..EVIDENCE_BYTES)
            .and_then(TimedEvidence::decode)
            .ok_or_else(|| invalid("damaged retained timed evidence"))?;
        let original = evidence.origin.original;
        let payload = bytes.slice(EVIDENCE_BYTES..);
        if original.stream != stream
            || original.at != at
            || original.epoch != self.epoch
            || !original.matches(&payload)
        {
            return Err(invalid("timed evidence differs from the retained record"));
        }
        Ok((evidence, payload))
    }
}

/// The records of an incomplete Sync. The keeper's view changes only when the Sync completes.
pub(super) struct Staging {
    pub from: Lsn,
    pub floor: Lsn,
    pub records: VecDeque<Record>,
}

impl Staging {
    pub fn tail(&self) -> Lsn {
        Lsn(self.from.0 - 1 + self.records.len() as u64)
    }
}

pub(super) struct Stream {
    pub view: wire::StreamView,
    pub deleted: bool,
    pub records: VecDeque<Record>,
    pub staging: Option<Staging>,
    pub bytes: u64,
    pub changed: watch::Sender<()>,
}

pub(super) fn decide(
    state: Option<&Stream>,
    keeper: KeeperId,
    request: &Request,
    identity: &Identity,
    seal_allowed: bool,
    limits: &Limits,
    reader: &mut ExtentReader,
) -> io::Result<Decision> {
    let normalized = normalize_original(request)?;
    let request = normalized.as_ref().unwrap_or(request);
    let (identical, retained_bytes) = match state {
        Some(state) => (
            state.matches_retained(request, normalized.is_some(), identity, reader)?,
            state.retained_charge(request),
        ),
        None => (false, 0),
    };
    let view = rules::StreamView {
        keeper,
        durable: state.map(|state| &state.view),
        deleted: state.is_some_and(|state| state.deleted),
        staged: state
            .and_then(|state| state.staging.as_ref())
            .map(|staging| (staging.floor, staging.tail())),
        identity,
        seal_allowed,
        identical,
        retained_bytes,
    };
    Ok(rules::decide(&view, request, limits))
}

impl Default for Stream {
    fn default() -> Self {
        Self {
            view: wire::StreamView {
                promised: None,
                synced: None,
                tail: Lsn(0),
                head: Lsn(0),
                floor: Lsn(1),
                runs: Vec::new(),
                ensemble: [KeeperId(0); 3],
                learner: true,
            },
            deleted: false,
            records: VecDeque::new(),
            staging: None,
            bytes: 0,
            changed: watch::channel(()).0,
        }
    }
}

impl Stream {
    pub fn page(
        &self,
        from: Lsn,
        max: u32,
        through: Lsn,
        reader: &mut ExtentReader,
    ) -> io::Result<Reply> {
        self.page_at(from, max, through, reader, None)
    }

    /// Recovery stops a plain page at a timed boundary. At the boundary it
    /// transfers the exact original evidence and payload as one typed record.
    pub(super) fn recover(
        &self,
        stream: StreamId,
        from: Lsn,
        max: u32,
        through: Lsn,
        reader: &mut ExtentReader,
    ) -> io::Result<Reply> {
        self.page_at(from, max, through, reader, Some(stream))
    }

    fn page_at(
        &self,
        from: Lsn,
        max: u32,
        through: Lsn,
        reader: &mut ExtentReader,
        recovery_stream: Option<StreamId>,
    ) -> io::Result<Reply> {
        let mut bytes = 0;
        let mut records = Vec::new();
        let mut run: Option<ExtentRun> = None;
        if from <= through && max != 0 {
            let count = (through.0 - from.0 + 1).min(u64::from(max));
            let offset = (from.0 - self.view.floor.0) as usize;
            for (index, record) in self
                .records
                .range(offset..offset + count as usize)
                .enumerate()
            {
                let lsn = Lsn(from.0 + index as u64);
                if let Some(stream) = recovery_stream
                    && record.timed
                {
                    if !records.is_empty() || run.is_some() {
                        break;
                    }
                    let (evidence, payload) = record.original(reader, stream, lsn)?;
                    return Ok(Reply::OriginalRecord {
                        evidence: Arc::new(evidence),
                        payload,
                    });
                }
                let payload = record.payload.read();
                bytes += 20 + payload.len();
                if bytes > PAGE_BYTES {
                    break;
                }
                if record.timed {
                    if let Some(run) = run.take() {
                        run.read(reader, &mut records)?;
                    }
                    let bytes = payload.read(reader)?;
                    if bytes.len() < EVIDENCE_BYTES {
                        return Err(invalid("short retained timed record"));
                    }
                    records.push((lsn, bytes.slice(EVIDENCE_BYTES..)));
                    continue;
                }
                match &*payload {
                    Payload::Pending(bytes) => {
                        if let Some(run) = run.take() {
                            run.read(reader, &mut records)?;
                        }
                        records.push((lsn, bytes.clone()));
                    }
                    Payload::Extent { extent, offset, len, crc } => {
                        let end = offset.checked_add(u64::from(*len))
                            .ok_or_else(|| invalid("invalid stream extent range"))?;
                        if let Some(current) = run.as_mut().filter(|run| run.can_extend(extent, *offset, end)) {
                            current.end = end;
                            current.records.push((lsn, *len, *crc));
                        } else {
                            if let Some(run) = run.take() {
                                run.read(reader, &mut records)?;
                            }
                            // Open while the current record still guards the pack name.
                            // The reader holds this file until the run has been read.
                            reader.file(extent)?;
                            run = Some(ExtentRun {
                                extent: Arc::clone(extent),
                                offset: *offset,
                                end,
                                records: vec![(lsn, *len, *crc)],
                            });
                        }
                    }
                }
            }
        }
        if let Some(run) = run {
            run.read(reader, &mut records)?;
        }
        Ok(Reply::Records {
            floor: self.view.floor,
            records,
            head: self.view.head,
        })
    }

    pub(super) fn record(&self, at: Lsn) -> Option<&Record> {
        let offset = rules::retained_index(self.view.floor.0, self.records.len(), at.0)?;
        self.records.get(offset)
    }

    fn matches_retained(
        &self,
        request: &Request,
        timed: bool,
        identity: &Identity,
        reader: &mut ExtentReader,
    ) -> io::Result<bool> {
        let (from, records, runs, epoch, through) = match request {
            Request::Append {
                at, records, epoch, ..
            } => (*at, records, None, *epoch, self.view.tail),
            Request::Sync {
                from,
                records,
                runs,
                epoch,
                ..
            } => {
                let through = if self.view.synced == Some(*epoch) {
                    self.view.tail
                } else {
                    self.view.head
                };
                (*from, records, Some(runs), *epoch, through)
            }
            _ => return Ok(true),
        };
        if !rules::promised(&self.view, epoch, identity) || from < self.view.floor {
            return Ok(false);
        }
        let mut remaining_runs = runs.into_iter().flatten().peekable();
        for (index, payload) in records.iter().enumerate() {
            let Some(position) = from.0.checked_add(index as u64) else {
                return Ok(false);
            };
            let lsn = Lsn(position);
            if lsn > through {
                break;
            }
            let Some(offset) = rules::retained_index(self.view.floor.0, self.records.len(), lsn.0)
            else {
                return Ok(false);
            };
            let stored = &self.records[offset];
            let expected = if runs.is_some() {
                while remaining_runs.peek().is_some_and(|run| run.last < lsn) {
                    remaining_runs.next();
                }
                remaining_runs
                    .peek()
                    .filter(|run| rules::epoch_run_contains(run.first.0, run.last.0, lsn.0))
                    .map(|run| run.epoch)
            } else {
                Some(epoch)
            };
            if expected != Some(stored.epoch)
                || stored.timed != timed
                || payload.len() != stored.len()
                || *payload != stored.read(reader)?
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// The charge already used by the records that the request will keep.
    fn retained_charge(&self, request: &Request) -> u64 {
        let Request::Sync { from, floor, .. } = request else {
            return self.bytes;
        };
        let floor = self.staged_floor(*floor);
        let start = rules::sync_start(from.0, floor.0, self.view.floor.0, self.view.head.0);
        self.image_charge(self.view.floor.max(floor), Lsn(start))
    }

    fn staged_floor(&self, floor: Lsn) -> Lsn {
        self.staging
            .as_ref()
            .map_or(floor, |staging| staging.floor.max(floor))
    }

    /// The charge of the positions in `[first, end)` of the history an incomplete Sync builds.
    fn image_charge(&self, first: Lsn, end: Lsn) -> u64 {
        let Some(staging) = &self.staging else {
            return range_charge(&self.records, self.view.floor, first, end);
        };
        rules::add_charge(
            range_charge(&self.records, self.view.floor, first, end.min(staging.from)),
            range_charge(&staging.records, staging.from, first, end),
        )
    }

    fn discard_before(&mut self, floor: Lsn) {
        if floor <= self.view.floor {
            return;
        }
        let count = rules::retained_offset(self.view.floor.0, self.records.len(), floor.0);
        for record in self.records.drain(..count) {
            self.bytes -= rules::record_charge(record.len());
        }
        let count = self.view.runs.partition_point(|run| run.last < floor);
        self.view.runs.drain(..count);
        if let Some(first) = self.view.runs.first_mut() {
            first.first = first.first.max(floor);
        }
        self.view.floor = floor;
    }

    fn truncate(&mut self, from: Lsn) {
        let keep = rules::retained_offset(self.view.floor.0, self.records.len(), from.0);
        for record in self.records.drain(keep..) {
            self.bytes -= rules::record_charge(record.len());
        }
        let keep = self.view.runs.partition_point(|run| run.first < from);
        self.view.runs.truncate(keep);
        if let Some(last) = self.view.runs.last_mut() {
            last.last = last.last.min(Lsn(from.0 - 1));
        }
        self.view.tail = Lsn(from.0 - 1);
    }

    fn push(&mut self, record: Record) {
        let lsn = Lsn(self.view.tail.0 + 1);
        match self.view.runs.last_mut() {
            Some(run) if run.epoch == record.epoch => run.last = lsn,
            _ => self.view.runs.push(EpochRun {
                epoch: record.epoch,
                first: lsn,
                last: lsn,
            }),
        }
        self.bytes += rules::record_charge(record.len());
        self.records.push_back(record);
        self.view.tail = lsn;
    }

    /// Replace the history from the staged position. A staged floor can skip the whole history.
    fn install(&mut self, staging: Staging, head: Lsn) {
        if staging.from.0 > self.view.tail.0 + 1 {
            self.discard_before(Lsn(self.view.tail.0 + 1));
            self.view.floor = staging.from;
            self.view.tail = Lsn(staging.from.0 - 1);
        } else {
            self.truncate(staging.from);
        }
        for record in staging.records {
            self.push(record);
        }
        self.discard_before(staging.floor);
        self.view.head = head;
    }

    /// Apply an admitted WAL entry. Replay uses the identical transition.
    pub fn apply(
        &mut self,
        keeper: KeeperId,
        request: Request,
        identity: Option<Identity>,
    ) -> io::Result<Reply> {
        let normalized = normalize_original(&request)?;
        let timed = normalized.is_some();
        let request = normalized.unwrap_or(request);
        if rules::installs_floor(&self.view, &request)
            && let Request::Sync { floor, head, .. } = request
        {
            self.discard_before(floor);
            self.view.tail = self.view.tail.max(head);
            self.view.head = self.view.head.max(head);
            return Ok(Reply::Synced {
                tail: self.view.tail,
            });
        }
        match request {
            Request::Create { ensemble, .. } => {
                self.view.ensemble = ensemble;
                self.view.learner = !ensemble.contains(&keeper);
                Ok(Reply::Created)
            }
            Request::Seal {
                epoch, proposal, ..
            } => {
                self.staging = None;
                self.view.promised = Some((
                    epoch,
                    identity.ok_or_else(|| invalid("missing seal identity"))?,
                    proposal,
                ));
                Ok(Reply::Sealed(self.view.clone()))
            }
            Request::Sync {
                epoch,
                from,
                floor,
                records,
                runs,
                head,
                complete,
                ..
            } => {
                let floor = self.staged_floor(floor);
                let start = Lsn(rules::sync_start(
                    from.0,
                    floor.0,
                    self.view.floor.0,
                    self.view.head.0,
                ));
                let mut staging = self
                    .staging
                    .take()
                    .and_then(|mut staging| {
                        let keep =
                            rules::staged_prefix(staging.from.0, staging.records.len(), start.0)?;
                        staging.records.truncate(keep);
                        Some(staging)
                    })
                    .unwrap_or_else(|| Staging {
                        from: start,
                        floor,
                        records: VecDeque::new(),
                    });
                staging.floor = floor;
                let skip = rules::retained_offset(from.0, records.len(), start.0);
                let epochs = runs
                    .into_iter()
                    .flat_map(|run| (run.first.0..=run.last.0).map(move |_| run.epoch));
                for (payload, epoch) in records.into_iter().zip(epochs).skip(skip) {
                    staging
                        .records
                        .push_back(Record::new(epoch, Payload::Pending(payload)).with_timed(timed));
                }
                if complete {
                    self.install(staging, head);
                    self.view.synced = Some(epoch);
                } else {
                    self.staging = Some(staging);
                }
                Ok(Reply::Synced {
                    tail: self.view.tail,
                })
            }
            Request::Append {
                epoch,
                at,
                records,
                head,
                ..
            } => {
                if at > self.view.tail {
                    for payload in records {
                        self.push(Record::new(epoch, Payload::Pending(payload)).with_timed(timed));
                    }
                }
                self.view.head = self.view.head.max(head);
                Ok(Reply::Appended {
                    tail: self.view.tail,
                })
            }
            Request::Trim { through, .. } => {
                self.discard_before(Lsn(through.0 + 1));
                Ok(Reply::Trimmed {
                    floor: self.view.floor,
                })
            }
            Request::Delete { ensemble, .. } => {
                *self = Self {
                    deleted: rules::tombstone(self.deleted, true),
                    changed: self.changed.clone(),
                    ..Self::default()
                };
                self.view.ensemble = ensemble;
                Ok(Reply::Deleted)
            }
            Request::Replace { to, .. } => {
                (self.view.ensemble, self.view.learner) = rules::install_ensemble(to);
                Ok(Reply::Replaced)
            }
            _ => Err(invalid("nonmutation in stream WAL")),
        }
    }
}

/// Use the existing singleton append and staged Sync reducer with a typed
/// storage envelope. Old ordinary requests cannot match a timed record.
fn normalize_original(request: &Request) -> io::Result<Option<Request>> {
    let (stream, evidence, payload) = match request {
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
        } => (*stream, evidence, payload),
        _ => return Ok(None),
    };
    let original = evidence.origin.original;
    if original.stream != stream || !original.valid() || payload.len() > MAX_TIMED_PAYLOAD {
        return Err(invalid("invalid timed keeper record"));
    }
    let mut stored = BytesMut::with_capacity(EVIDENCE_BYTES + payload.len());
    stored.extend_from_slice(&evidence.encode());
    stored.extend_from_slice(payload);
    let records = vec![stored.freeze()];
    Ok(Some(match request {
        Request::AppendOriginal { head, .. } => Request::Append {
            stream,
            epoch: original.epoch,
            at: original.at,
            records,
            head: *head,
        },
        Request::SyncOriginal {
            epoch, floor, head, ..
        } => Request::Sync {
            stream,
            epoch: *epoch,
            floor: *floor,
            from: original.at,
            records,
            runs: vec![EpochRun {
                epoch: original.epoch,
                first: original.at,
                last: original.at,
            }],
            head: *head,
            complete: false,
        },
        _ => unreachable!(),
    }))
}

fn range_charge(records: &VecDeque<Record>, from: Lsn, first: Lsn, end: Lsn) -> u64 {
    let offset = |at: Lsn| rules::retained_offset(from.0, records.len(), at.0);
    let end = offset(end);
    let start = offset(first).min(end);
    rules::quota_charge(end - start, |i| records[start + i].len())
}
