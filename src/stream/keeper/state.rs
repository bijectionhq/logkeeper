use std::{collections::VecDeque, fs::File, io, path::PathBuf, sync::Arc};

use bytes::Bytes;
use tokio::sync::watch;

use super::rules::{self, charge};
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

pub(super) struct Record {
    pub epoch: Epoch,
    pub payload: Payload,
}

pub(super) struct Stream {
    pub view: wire::StreamView,
    pub principal: Bytes,
    pub deleted: bool,
    pub records: VecDeque<Record>,
    pub bytes: u64,
    pub checkpoint: Option<u64>,
    pub changed: watch::Sender<()>,
}

impl Default for Stream {
    fn default() -> Self {
        Self {
            view: wire::StreamView {
                promised: None,
                synced: None,
                end: Lsn(0),
                commit: Lsn(0),
                floor: Lsn(1),
                runs: Vec::new(),
                ensemble: [KeeperId(0); 3],
                learner: true,
            },
            principal: Bytes::new(),
            deleted: false,
            records: VecDeque::new(),
            bytes: 0,
            checkpoint: None,
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
                bytes += 12 + record.payload.len();
                if bytes > PAGE_BYTES {
                    break;
                }
                records.push((Lsn(from.0 + index as u64), record.payload.read(reader)?));
            }
        }
        Ok(Reply::Records {
            floor: self.view.floor,
            records,
            commit: self.view.commit,
        })
    }

    /// Compare the retained overlap and calculate the charge of the prefix that a Sync will keep.
    pub fn facts(
        &self,
        request: &Request,
        principal: &[u8],
        reader: &mut ExtentReader,
    ) -> io::Result<(bool, u64)> {
        let (from, records, runs, epoch, holder, match_through, bytes) = match request {
            Request::Append {
                at,
                records,
                epoch,
                holder,
                ..
            } => (
                *at,
                records,
                None,
                *epoch,
                *holder,
                self.view.end,
                self.bytes,
            ),
            Request::Sync {
                from,
                floor,
                records,
                runs,
                epoch,
                holder,
                ..
            } => {
                let through = if self.view.synced == Some(*epoch) {
                    self.view.end
                } else {
                    self.view.commit
                };
                let start = rules::sync_start(&self.view, *from, *floor);
                let first = self.view.floor.max(*floor);
                let bytes = self.bytes_between(first, start);
                (*from, records, Some(runs), *epoch, *holder, through, bytes)
            }
            _ => return Ok((true, self.bytes)),
        };
        if self.view.promised != Some((epoch, holder))
            || self.principal != principal
            || from < self.view.floor
        {
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
                || payload.len() != stored.payload.len()
                || *payload != stored.payload.read(reader)?
            {
                return Ok((false, bytes));
            }
        }
        Ok((true, bytes))
    }

    fn bytes_between(&self, first: Lsn, end: Lsn) -> u64 {
        let offset = |lsn: Lsn| {
            lsn.0
                .saturating_sub(self.view.floor.0)
                .min(self.records.len() as u64) as usize
        };
        let end = offset(end);
        self.records
            .range(offset(first).min(end)..end)
            .map(|record| record.payload.len().max(1) as u64)
            .sum()
    }

    fn discard_before(&mut self, floor: Lsn) {
        if floor <= self.view.floor {
            return;
        }
        let count = (floor.0 - self.view.floor.0).min(self.records.len() as u64) as usize;
        for record in self.records.drain(..count) {
            self.bytes -= record.payload.len().max(1) as u64;
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
            self.bytes -= record.payload.len().max(1) as u64;
        }
        let keep = self.view.runs.partition_point(|run| run.first < from);
        self.view.runs.truncate(keep);
        if let Some(last) = self.view.runs.last_mut() {
            last.last = last.last.min(Lsn(from.0 - 1));
        }
        self.view.end = Lsn(from.0 - 1);
    }

    fn push(&mut self, epoch: Epoch, payload: Bytes) {
        let lsn = Lsn(self.view.end.0 + 1);
        match self.view.runs.last_mut() {
            Some(run) if run.epoch == epoch => run.last = lsn,
            _ => self.view.runs.push(EpochRun {
                epoch,
                first: lsn,
                last: lsn,
            }),
        }
        self.bytes += charge(&payload);
        self.records.push_back(Record {
            epoch,
            payload: Payload::Pending(payload),
        });
        self.view.end = lsn;
    }

    /// Apply an admitted WAL entry. Replay uses the identical transition.
    pub fn apply(
        &mut self,
        keeper: KeeperId,
        request: Request,
        principal: Bytes,
    ) -> io::Result<Reply> {
        match request {
            Request::Create { ensemble, .. } => {
                self.view.ensemble = ensemble;
                self.view.learner = !ensemble.contains(&keeper);
                Ok(Reply::Created)
            }
            Request::Seal { epoch, holder, .. } => {
                self.view.promised = Some((epoch, holder));
                self.principal = principal;
                Ok(Reply::Sealed(self.view.clone()))
            }
            Request::Sync {
                epoch,
                from,
                floor,
                records,
                runs,
                commit,
                complete,
                ..
            } => {
                let start = rules::sync_start(&self.view, from, floor);
                self.discard_before(floor);
                self.truncate(start);
                let skip = (start.0 - from.0).min(records.len() as u64) as usize;
                let epochs = runs
                    .into_iter()
                    .flat_map(|run| (run.first.0..=run.last.0).map(move |_| run.epoch));
                for (payload, epoch) in records.into_iter().zip(epochs).skip(skip) {
                    self.push(epoch, payload);
                }
                self.view.commit = commit;
                if complete {
                    self.view.synced = Some(epoch);
                }
                Ok(Reply::Synced { end: self.view.end })
            }
            Request::Append {
                epoch,
                at,
                records,
                commit,
                ..
            } => {
                if at > self.view.end {
                    for payload in records {
                        self.push(epoch, payload);
                    }
                }
                self.view.commit = self.view.commit.max(commit);
                Ok(Reply::Appended { end: self.view.end })
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
                    checkpoint: self.checkpoint,
                    ..Self::default()
                };
                self.view.ensemble = ensemble;
                Ok(Reply::Deleted)
            }
            Request::Replace { to, .. } => {
                self.view.ensemble = to;
                self.view.learner = false;
                Ok(Reply::Replaced)
            }
            _ => Err(invalid("nonmutation in stream WAL")),
        }
    }
}
