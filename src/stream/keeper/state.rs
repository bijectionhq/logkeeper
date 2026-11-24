use std::{collections::VecDeque, fs::File, io, path::PathBuf, sync::Arc};

use bytes::Bytes;
use tokio::sync::watch;

use super::rules::{self, Decision, Limits};
use crate::stream::{
    codec::{PAGE_BYTES, invalid},
    wire::{self, *},
};

pub(super) struct Extent {
    pub sequence: u64,
    pub path: PathBuf,
}

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
                if crc32fast::hash(&bytes) != *crc {
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
    // A checkpoint can move the same record even if a later Sync installed it
    // in a different position in the keeper's state.
    pub payload: Arc<parking_lot::RwLock<Payload>>,
}

impl Record {
    pub fn new(epoch: Epoch, payload: Payload) -> Self {
        Self {
            epoch,
            payload: Arc::new(parking_lot::RwLock::new(payload)),
        }
    }

    pub fn len(&self) -> usize {
        self.payload.read().len()
    }

    pub fn read(&self, reader: &mut ExtentReader) -> io::Result<Bytes> {
        self.payload.read().read(reader)
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
    let (identical, retained_bytes) = state
        .map(|state| state.facts(request, identity, reader))
        .transpose()?
        .unwrap_or((false, 0));
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
                proposal: None,
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
        let mut bytes = 0;
        let mut records = Vec::new();
        if from <= through && max != 0 {
            let count = (through.0 - from.0 + 1).min(u64::from(max));
            let offset = (from.0 - self.view.floor.0) as usize;
            for (index, record) in self
                .records
                .range(offset..offset + count as usize)
                .enumerate()
            {
                bytes += 20 + record.len();
                if bytes > PAGE_BYTES {
                    break;
                }
                records.push((Lsn(from.0 + index as u64), record.read(reader)?));
            }
        }
        Ok(Reply::Records {
            floor: self.view.floor,
            records,
            head: self.view.head,
        })
    }

    /// Compare the retained overlap and calculate the charge of the prefix that a Sync will keep.
    fn facts(
        &self,
        request: &Request,
        identity: &Identity,
        reader: &mut ExtentReader,
    ) -> io::Result<(bool, u64)> {
        let (from, records, runs, epoch, match_through, bytes) = match request {
            Request::Append {
                at, records, epoch, ..
            } => (*at, records, None, *epoch, self.view.tail, self.bytes),
            Request::Sync {
                from,
                floor,
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
                let floor = self.staged_floor(*floor);
                let start = rules::sync_start(&self.view, *from, floor);
                let bytes = self.image_bytes(self.view.floor.max(floor), start);
                (*from, records, Some(runs), *epoch, through, bytes)
            }
            _ => return Ok((true, self.bytes)),
        };
        if !rules::promised(&self.view, epoch, identity) || from < self.view.floor {
            return Ok((false, bytes));
        }
        let mut remaining_runs = runs.into_iter().flatten().peekable();
        for (index, payload) in records.iter().enumerate() {
            let Some(position) = from.0.checked_add(index as u64) else {
                return Ok((false, bytes));
            };
            let lsn = Lsn(position);
            if lsn > match_through {
                break;
            }
            let Some(stored) = self.records.get((lsn.0 - self.view.floor.0) as usize) else {
                return Ok((false, bytes));
            };
            let expected = if runs.is_some() {
                while remaining_runs.peek().is_some_and(|run| run.last < lsn) {
                    remaining_runs.next();
                }
                remaining_runs
                    .peek()
                    .filter(|run| run.first <= lsn)
                    .map(|run| run.epoch)
            } else {
                Some(epoch)
            };
            if expected != Some(stored.epoch)
                || payload.len() != stored.len()
                || *payload != stored.read(reader)?
            {
                return Ok((false, bytes));
            }
        }
        Ok((true, bytes))
    }

    fn staged_floor(&self, floor: Lsn) -> Lsn {
        self.staging
            .as_ref()
            .map_or(floor, |staging| staging.floor.max(floor))
    }

    /// The charge of the positions in `[first, end)` of the history an incomplete Sync builds.
    fn image_bytes(&self, first: Lsn, end: Lsn) -> u64 {
        let Some(staging) = &self.staging else {
            return self.bytes_between(first, end);
        };
        let index = |lsn: Lsn| lsn.0.saturating_sub(staging.from.0) as usize;
        let end_index = index(end).min(staging.records.len());
        self.bytes_between(first, end.min(staging.from))
            + staging
                .records
                .range(index(first).min(end_index)..end_index)
                .map(|record| record.len().max(1) as u64)
                .sum::<u64>()
    }

    fn bytes_between(&self, first: Lsn, tail: Lsn) -> u64 {
        let offset = |lsn: Lsn| {
            lsn.0
                .saturating_sub(self.view.floor.0)
                .min(self.records.len() as u64) as usize
        };
        let tail = offset(tail);
        self.records
            .range(offset(first).min(tail)..tail)
            .map(|record| record.len().max(1) as u64)
            .sum()
    }

    fn discard_before(&mut self, floor: Lsn) {
        if floor <= self.view.floor {
            return;
        }
        let count = (floor.0 - self.view.floor.0).min(self.records.len() as u64) as usize;
        for record in self.records.drain(..count) {
            self.bytes -= record.len().max(1) as u64;
        }
        let count = self.view.runs.partition_point(|run| run.last < floor);
        self.view.runs.drain(..count);
        if let Some(first) = self.view.runs.first_mut() {
            first.first = first.first.max(floor);
        }
        self.view.floor = floor;
    }

    fn truncate(&mut self, from: Lsn) {
        let keep = (from.0 - self.view.floor.0).min(self.records.len() as u64) as usize;
        for record in self.records.drain(keep..) {
            self.bytes -= record.len().max(1) as u64;
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
        self.bytes += record.len().max(1) as u64;
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
            Request::Seal { epoch, proposal, .. } => {
                self.staging = None;
                self.view.proposal = proposal;
                self.view.promised = Some((
                    epoch,
                    identity.ok_or_else(|| invalid("missing seal identity"))?,
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
                let start = rules::sync_start(&self.view, from, floor);
                let mut staging = match self.staging.take() {
                    Some(mut staging)
                        if staging.from <= start && start.0 <= staging.tail().0 + 1 =>
                    {
                        staging
                            .records
                            .truncate((start.0 - staging.from.0) as usize);
                        staging
                    }
                    _ => Staging {
                        from: start,
                        floor,
                        records: VecDeque::new(),
                    },
                };
                staging.floor = floor;
                let skip = (start.0 - from.0).min(records.len() as u64) as usize;
                let epochs = runs
                    .into_iter()
                    .flat_map(|run| (run.first.0..=run.last.0).map(move |_| run.epoch));
                for (payload, epoch) in records.into_iter().zip(epochs).skip(skip) {
                    staging
                        .records
                        .push_back(Record::new(epoch, Payload::Pending(payload)));
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
                        self.push(Record::new(epoch, Payload::Pending(payload)));
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
