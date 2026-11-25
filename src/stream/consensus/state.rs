//! Deterministic decisions over the committed journal view.

pub(super) const MAX_RETAINED_RECORDS: usize = 65_536;

use std::{
    collections::VecDeque,
    fs::File,
    io::{self, Read, Seek, SeekFrom},
    sync::Arc,
};

use bytes::Bytes;
use journal_contract::{Epoch, JournalError, Lsn, Page, Result};
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};

use super::{Fence, Genesis, MAX_PAGE, MAX_RECORD, MAX_RECORDS_PER_PAGE, Sealed, Stage};
use crate::stream::keeper::record_charge;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Command {
    Create,
    Seal {
        expected: Epoch,
        writer: uuid::Uuid,
        owner: String,
    },
    Append {
        fence: Fence,
        owner: String,
        at: Lsn,
        payload: Bytes,
    },
    Trim {
        fence: Fence,
        owner: String,
        through: Lsn,
    },
    Delete,
    Stage(Stage),
    StageOwned(Stage),
    Admitted(
        uuid::Uuid,
        #[serde(deserialize_with = "unticketed_command")] Box<Command>,
    ),
}

fn unticketed_command<'de, D: serde::Deserializer<'de>>(
    decoder: D,
) -> std::result::Result<Box<Command>, D::Error> {
    // A local proposal wraps exactly one unwrapped command (an application
    // command or a staging receipt). Keep the existing enum positions on disk
    // and reject recursive wrappers before the decoder can recurse through an
    // authenticated peer's frame.
    #[derive(Deserialize)]
    #[serde(remote = "Command")]
    enum Application {
        Create,
        Seal {
            expected: Epoch,
            writer: uuid::Uuid,
            owner: String,
        },
        Append {
            fence: Fence,
            owner: String,
            at: Lsn,
            payload: Bytes,
        },
        Trim {
            fence: Fence,
            owner: String,
            through: Lsn,
        },
        Delete,
        Stage(Stage),
        StageOwned(Stage),
    }
    Application::deserialize(decoder).map(Box::new)
}

impl Command {
    pub fn body(&self) -> &Self {
        match self {
            Self::Admitted(_, command) => command,
            command => command,
        }
    }

    pub fn into_body(self) -> Self {
        match self {
            Self::Admitted(_, command) => *command,
            command => command,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Outcome {
    Unit,
    Sealed(Sealed),
    At(Lsn),
    Page(Page),
    Refused(JournalError),
    Configuration(super::Configuration),
}

impl From<Result<Outcome>> for Outcome {
    fn from(result: Result<Outcome>) -> Self {
        result.unwrap_or_else(Self::Refused)
    }
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub(super) enum State {
    #[default]
    Absent,
    Live(Live),
    Deleted,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(super) struct Live {
    writer: Option<(Fence, String)>,
    head: Lsn,
    floor: Lsn,
    bytes: u64,
    #[serde(skip)]
    records: VecDeque<Payload>,
}

#[derive(Clone, Debug)]
pub(super) enum Payload {
    Extent {
        object: Arc<super::storage::Object>,
        offset: u64,
        len: u32,
        crc: u32,
    },
    Snapshot {
        file: Arc<Mutex<File>>,
        digest: [u8; 32],
        offset: u64,
        len: u32,
        crc: u32,
    },
}

impl Payload {
    pub(super) fn len(&self) -> usize {
        match self {
            Self::Extent { len, .. } | Self::Snapshot { len, .. } => *len as usize,
        }
    }

    pub fn load(&self) -> io::Result<Bytes> {
        let mut bytes = vec![0; self.len()];
        let crc = match self {
            Self::Extent {
                object,
                offset,
                crc,
                ..
            } => {
                object.read_range(*offset, &mut bytes)?;
                *crc
            }
            Self::Snapshot {
                file, offset, crc, ..
            } => {
                let mut file = file.lock();
                file.seek(SeekFrom::Start(*offset))?;
                file.read_exact(&mut bytes)?;
                *crc
            }
        };
        if crc32fast::hash(&bytes) != crc {
            return Err(super::invalid("retained record checksum changed"));
        }
        Ok(Bytes::from(bytes))
    }
}

pub(super) struct ReadPage {
    floor: Lsn,
    head: Lsn,
    records: Vec<(Lsn, Payload)>,
}

impl ReadPage {
    pub fn needs_disk(&self) -> bool {
        !self.records.is_empty()
    }

    pub fn load(self) -> io::Result<Page> {
        let records = self
            .records
            .into_iter()
            .map(|(lsn, payload)| Ok((lsn, payload.load()?)))
            .collect::<io::Result<_>>()?;
        Ok(Page {
            floor: self.floor,
            records,
            head: self.head,
        })
    }
}

impl State {
    pub fn apply(
        &mut self,
        command: Command,
        genesis: &Genesis,
        segment: Arc<super::storage::Object>,
    ) -> io::Result<Outcome> {
        if let Command::Append {
            fence,
            owner,
            at,
            payload,
        } = command
        {
            let live = match self.live_mut() {
                Ok(live) => live,
                Err(error) => return Ok(Outcome::Refused(error)),
            };
            if let Err(error) = live.require_writer(fence, &owner) {
                return Ok(Outcome::Refused(error));
            }
            if at >= live.floor && at <= live.head {
                let retained = &live.records[(at.0 - live.floor.0) as usize];
                return Ok(
                    if retained.len() == payload.len() && retained.load()? == payload {
                        Outcome::At(at)
                    } else {
                        Outcome::Refused(JournalError::Conflict { head: live.head })
                    },
                );
            }
            let len = payload.len() as u32;
            let offset = segment
                .key()
                .len
                .checked_sub(u64::from(len))
                .ok_or_else(|| {
                    super::invalid("accepted WAL extent does not contain the payload")
                })?;
            let retained = Payload::Extent {
                object: segment,
                offset,
                len,
                crc: crc32fast::hash(&payload),
            };
            return Ok(live.append(at, retained, genesis.quota_bytes).into());
        }
        Ok(self.decide(command).into())
    }

    fn decide(&mut self, command: Command) -> Result<Outcome> {
        if matches!(command, Command::Create) {
            return match self {
                Self::Absent => {
                    *self = Self::Live(Live {
                        writer: None,
                        head: Lsn(0),
                        floor: Lsn(1),
                        bytes: 0,
                        records: VecDeque::new(),
                    });
                    Ok(Outcome::Unit)
                }
                Self::Live(_) => Ok(Outcome::Unit),
                Self::Deleted => Err(JournalError::Deleted),
            };
        }
        if matches!(command, Command::Delete) && matches!(self, Self::Deleted) {
            return Ok(Outcome::Unit);
        }
        let live = self.live_mut()?;
        match command {
            Command::Seal {
                expected,
                writer,
                owner,
            } => live.seal(expected, writer, owner),
            Command::Trim {
                fence,
                owner,
                through,
            } => {
                live.require_writer(fence, &owner)?;
                live.trim(through)
            }
            Command::Delete => {
                *self = Self::Deleted;
                Ok(Outcome::Unit)
            }
            Command::Create
            | Command::Append { .. }
            | Command::Stage(_)
            | Command::StageOwned(_)
            | Command::Admitted(..) => unreachable!(),
        }
    }

    pub fn head(&self) -> Result<Lsn> {
        Ok(self.live()?.head)
    }

    pub fn read(&self, from: Lsn, limit: usize) -> Result<ReadPage> {
        self.live()?.read(from, limit)
    }

    pub fn records(&self) -> impl Iterator<Item = &Payload> {
        self.live().ok().into_iter().flat_map(|live| &live.records)
    }

    pub fn snapshot_bytes(&self) -> u64 {
        self.live().ok().map_or(0, |live| {
            live.bytes
                .saturating_add((live.records.len() as u64).saturating_mul(8))
        })
    }

    pub fn retained_floor(&self) -> Lsn {
        self.live().ok().map_or(Lsn(1), |live| live.floor)
    }

    pub fn record_count(&self) -> io::Result<u64> {
        let Ok(live) = self.live() else { return Ok(0) };
        live.head
            .0
            .checked_add(1)
            .and_then(|end| end.checked_sub(live.floor.0))
            .filter(|_| live.floor.0 != 0)
            .ok_or_else(|| super::invalid("invalid retained snapshot interval"))
    }

    pub fn restore_records(&mut self, records: VecDeque<Payload>, quota: u64) -> io::Result<()> {
        if let Self::Live(live) = self {
            let bytes = records
                .iter()
                .map(|record| record_charge(record.len()))
                .sum::<u64>();
            if live.bytes != bytes || bytes > quota {
                return Err(super::invalid("invalid retained snapshot quota"));
            }
            live.records = records;
        }
        Ok(())
    }

    fn live(&self) -> Result<&Live> {
        match self {
            Self::Absent => Err(JournalError::NotFound),
            Self::Live(live) => Ok(live),
            Self::Deleted => Err(JournalError::Deleted),
        }
    }

    fn live_mut(&mut self) -> Result<&mut Live> {
        match self {
            Self::Absent => Err(JournalError::NotFound),
            Self::Live(live) => Ok(live),
            Self::Deleted => Err(JournalError::Deleted),
        }
    }
}

impl Live {
    fn epoch(&self) -> Epoch {
        self.writer
            .as_ref()
            .map_or(Epoch(0), |(fence, _)| fence.epoch)
    }

    fn seal(&mut self, expected: Epoch, writer: uuid::Uuid, owner: String) -> Result<Outcome> {
        let epoch = expected
            .0
            .checked_add(1)
            .map(Epoch)
            .ok_or(JournalError::Unavailable)?;
        let fence = Fence { epoch, writer };
        if self.epoch() == expected {
            self.writer = Some((fence, owner));
        } else {
            self.require_writer(fence, &owner)?;
        }
        Ok(Outcome::Sealed(Sealed {
            fence,
            head: self.head,
        }))
    }

    fn require_writer(&self, fence: Fence, owner: &str) -> Result<()> {
        if self
            .writer
            .as_ref()
            .is_some_and(|(current, principal)| *current == fence && principal == owner)
        {
            Ok(())
        } else {
            Err(JournalError::Fenced {
                current: self.epoch(),
            })
        }
    }

    fn append(&mut self, at: Lsn, payload: Payload, quota_bytes: u64) -> Result<Outcome> {
        let conflict = JournalError::Conflict { head: self.head };
        if at < self.floor {
            return Err(JournalError::Trimmed { floor: self.floor });
        }
        if self.head.0.checked_add(1) != Some(at.0) || at.0 == u64::MAX {
            return Err(conflict);
        }
        if payload.len() > MAX_RECORD {
            return Err(JournalError::TooLarge { max: MAX_RECORD });
        }
        if self.records.len() >= MAX_RETAINED_RECORDS {
            return Err(JournalError::Full { floor: self.floor });
        }
        let charge = record_charge(payload.len());
        let used = self
            .bytes
            .checked_add(charge)
            .filter(|used| *used <= quota_bytes)
            .ok_or(JournalError::Full { floor: self.floor })?;
        self.records.push_back(payload);
        self.bytes = used;
        self.head = at;
        Ok(Outcome::At(at))
    }

    fn trim(&mut self, through: Lsn) -> Result<Outcome> {
        if through > self.head {
            return Err(JournalError::Conflict { head: self.head });
        }
        if through >= self.floor {
            let count = (through.0 - self.floor.0 + 1) as usize;
            for payload in self.records.drain(..count) {
                self.bytes -= record_charge(payload.len());
            }
            if self.records.capacity() > self.records.len().saturating_mul(2).max(1024) {
                self.records.shrink_to_fit();
            }
            self.floor = Lsn(through.0 + 1);
        }
        Ok(Outcome::Unit)
    }

    fn read(&self, from: Lsn, limit: usize) -> Result<ReadPage> {
        if from < self.floor {
            return Err(JournalError::Trimmed { floor: self.floor });
        }
        let mut records = Vec::new();
        if from <= self.head {
            let mut bytes = 0;
            for payload in self
                .records
                .iter()
                .skip((from.0 - self.floor.0) as usize)
                .take(limit.min(MAX_RECORDS_PER_PAGE))
            {
                bytes += payload.len();
                if bytes > MAX_PAGE {
                    break;
                }
                records.push((Lsn(from.0 + records.len() as u64), payload.clone()));
            }
        }
        Ok(ReadPage {
            floor: self.floor,
            records,
            head: self.head,
        })
    }
}
