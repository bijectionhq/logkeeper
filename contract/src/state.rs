use crate::{Epoch, Identity, JournalError, Limits, Lsn, Page, Result, StreamId};
use bytes::Bytes;
use std::collections::{HashMap, VecDeque};

#[derive(Debug)]
pub(crate) enum Mutation {
    Create,
    Seal {
        epoch: Epoch,
        identity: Identity,
    },
    Append {
        epoch: Epoch,
        identity: Identity,
        at: Lsn,
        payload: Bytes,
    },
    Trim {
        epoch: Epoch,
        identity: Identity,
        through: Lsn,
    },
    Delete,
}

impl Mutation {
    pub(crate) fn wakes_readers(&self) -> bool {
        matches!(self, Self::Append { .. } | Self::Trim { .. } | Self::Delete)
    }
}

pub(crate) struct State {
    streams: HashMap<StreamId, Stream>,
    limits: Limits,
}

enum Stream {
    Live(Live),
    Deleted,
}

pub(crate) struct Live {
    sealed: Option<(Epoch, Identity)>,
    pub(crate) floor: Lsn,
    pub(crate) end: Lsn,
    records: VecDeque<(Epoch, Bytes)>,
    bytes: u64,
}

pub(crate) struct Decision {
    pub(crate) position: Lsn,
    pub(crate) changed: bool,
}

impl State {
    pub(crate) fn new(limits: Limits) -> Self {
        Self {
            streams: HashMap::new(),
            limits,
        }
    }

    pub(crate) fn live(&self, stream: StreamId) -> Result<&Live> {
        match self.streams.get(&stream) {
            Some(Stream::Live(live)) => Ok(live),
            Some(Stream::Deleted) => Err(JournalError::Deleted),
            None => Err(JournalError::NotFound),
        }
    }

    pub(crate) fn decide(&self, stream: StreamId, mutation: &Mutation) -> Result<Decision> {
        if matches!(mutation, Mutation::Create) {
            return match self.live(stream) {
                Ok(live) => Ok(Decision {
                    position: live.end,
                    changed: false,
                }),
                Err(JournalError::NotFound) => Ok(Decision {
                    position: Lsn(0),
                    changed: true,
                }),
                Err(error) => Err(error),
            };
        }

        let live = self.live(stream)?;
        let mut end = live.end;
        let changed = match mutation {
            Mutation::Create => unreachable!(),
            Mutation::Seal { epoch, identity } => match live.sealed {
                Some(sealed) if sealed == (*epoch, *identity) => false,
                Some((current, _)) if *epoch <= current => {
                    return Err(JournalError::Fenced { current });
                }
                _ => true,
            },
            Mutation::Append {
                epoch,
                identity,
                at,
                payload,
            } => {
                live.check_seal(*epoch, *identity)?;
                if *at < live.floor {
                    return Err(JournalError::Trimmed { floor: live.floor });
                }
                if *at <= live.end {
                    let index = (at.0 - live.floor.0) as usize;
                    let (record_epoch, record) = &live.records[index];
                    if record_epoch == epoch && record == payload {
                        return Ok(Decision {
                            position: *at,
                            changed: false,
                        });
                    }
                    return Err(live.conflict());
                }
                if end.0.checked_add(1) != Some(at.0) {
                    return Err(live.conflict());
                }
                if payload.len() > self.limits.max_record_bytes {
                    return Err(JournalError::TooLarge {
                        max: self.limits.max_record_bytes,
                    });
                }
                if payload.len() as u64 > self.limits.stream_quota_bytes - live.bytes {
                    return Err(JournalError::Full { floor: live.floor });
                }
                end = *at;
                true
            }
            Mutation::Trim {
                epoch,
                identity,
                through,
            } => {
                live.check_seal(*epoch, *identity)?;
                if *through > end {
                    return Err(live.conflict());
                }
                if through.0 == u64::MAX {
                    return Err(JournalError::Unavailable);
                }
                *through >= live.floor
            }
            Mutation::Delete => true,
        };
        Ok(Decision {
            position: end,
            changed,
        })
    }

    // Apply only decisions that changed state, after any required durable write.
    pub(crate) fn apply(&mut self, stream: StreamId, mutation: Mutation) {
        match mutation {
            Mutation::Create => {
                self.streams.insert(
                    stream,
                    Stream::Live(Live {
                        sealed: None,
                        floor: Lsn(1),
                        end: Lsn(0),
                        records: VecDeque::new(),
                        bytes: 0,
                    }),
                );
            }
            Mutation::Delete => {
                self.streams.insert(stream, Stream::Deleted);
            }
            mutation => {
                let Some(Stream::Live(live)) = self.streams.get_mut(&stream) else {
                    unreachable!();
                };
                match mutation {
                    Mutation::Seal { epoch, identity } => live.sealed = Some((epoch, identity)),
                    Mutation::Append {
                        epoch, at, payload, ..
                    } => {
                        live.bytes += payload.len() as u64;
                        live.records.push_back((epoch, payload));
                        live.end = at;
                    }
                    Mutation::Trim { through, .. } => {
                        let count = (through.0 - live.floor.0 + 1) as usize;
                        for (_, record) in live.records.drain(..count) {
                            live.bytes -= record.len() as u64;
                        }
                        live.floor = Lsn(through.0 + 1);
                    }
                    Mutation::Create | Mutation::Delete => unreachable!(),
                }
            }
        }
    }
}

impl Live {
    fn check_seal(&self, epoch: Epoch, identity: Identity) -> Result<()> {
        if self.sealed == Some((epoch, identity)) {
            return Ok(());
        }
        Err(JournalError::Fenced {
            current: self.sealed.map_or(Epoch(0), |(epoch, _)| epoch),
        })
    }

    fn conflict(&self) -> JournalError {
        JournalError::Conflict {
            committed_end: self.end,
        }
    }

    pub(crate) fn page(&self, from: Lsn, max: usize) -> Page {
        let records = if from > self.end {
            Vec::new()
        } else {
            let offset = (from.0 - self.floor.0) as usize;
            self.records
                .iter()
                .skip(offset)
                .take(max)
                .enumerate()
                .map(|(index, (_, payload))| (Lsn(from.0 + index as u64), payload.clone()))
                .collect()
        };
        Page {
            floor: self.floor,
            records,
            end: self.end,
        }
    }
}
