//! Durable local ownership of replica directories. Placement proof is
//! obtained by the keeper before submitting an ownership transition.

use std::{
    io,
    path::{Path, PathBuf},
};

use journal_contract::StreamId;
use serde::{Deserialize, Serialize};

use super::{LogId, Stage};

const MAX_DETACHED: usize = 16;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(super) struct Ownership {
    high: u64,
    greatest_generation: u64,
    pub current: Option<Copy>,
    detached: Vec<u64>,
    retired: Option<(u64, u64)>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(super) struct Copy {
    pub generation: u64,
    revision: u64,
    stage: Option<Stage>,
    installed: bool,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(super) enum Change {
    Stage(Stage),
    Install {
        stage: Stage,
        generation: u64,
        through: LogId,
    },
    Detach {
        revision: u64,
        generation: u64,
    },
    Release(u64),
    Observe {
        revision: u64,
        generation: u64,
    },
}

impl Default for Ownership {
    fn default() -> Self {
        Self {
            high: 0,
            greatest_generation: 0,
            current: Some(Copy {
                generation: 0,
                revision: 0,
                stage: None,
                installed: true,
            }),
            detached: Vec::new(),
            retired: None,
        }
    }
}

impl Ownership {
    pub fn generation(&self) -> Option<u64> {
        self.current.as_ref().map(|copy| copy.generation)
    }

    pub fn installed(&self) -> bool {
        self.current.as_ref().is_some_and(|copy| copy.installed)
    }

    pub fn high_water(&self) -> u64 {
        self.high
    }

    pub fn detached(&self) -> &[u64] {
        &self.detached
    }

    pub fn contains_stage(&self, stage: &Stage) -> bool {
        self.current
            .as_ref()
            .is_some_and(|copy| copy.stage.as_ref() == Some(stage))
    }

    pub fn was_retired(&self, revision: u64, generation: u64) -> bool {
        self.retired == Some((revision, generation))
    }

    // Returns true when the old log and its selected snapshot cease to own
    // the replica. The durable vote remains at its enclosing log.
    pub fn apply(&mut self, change: Change, has_cut: impl Fn(LogId) -> bool) -> io::Result<bool> {
        match change {
            Change::Stage(stage) => {
                if self.contains_stage(&stage) {
                    return Ok(false);
                }
                let revision = stage.source.checked_add(1).ok_or_else(stale)?;
                if revision <= self.high {
                    return Err(stale());
                }
                let generation = self.greatest_generation.checked_add(1).ok_or_else(stale)?;
                self.detach_current()?;
                self.greatest_generation = generation;
                self.high = revision;
                self.current = Some(Copy {
                    generation,
                    revision,
                    stage: Some(stage),
                    installed: false,
                });
                Ok(true)
            }
            Change::Install {
                stage,
                generation,
                through,
            } => {
                let copy = self.current.as_mut().ok_or_else(stale)?;
                if copy.generation != generation
                    || copy.stage.as_ref() != Some(&stage)
                    || !has_cut(through)
                {
                    return Err(stale());
                }
                copy.installed = true;
                Ok(false)
            }
            Change::Detach {
                revision,
                generation,
            } => {
                if self.was_retired(revision, generation) {
                    return Ok(false);
                }
                if revision < self.high
                    || self.current.as_ref().is_none_or(|copy| {
                        copy.generation != generation || !copy.installed || revision < copy.revision
                    })
                {
                    return Err(stale());
                }
                self.detach_current()?;
                self.high = revision;
                self.retired = Some((revision, generation));
                Ok(true)
            }
            Change::Release(generation) => {
                self.detached.retain(|pending| *pending != generation);
                Ok(false)
            }
            Change::Observe {
                revision,
                generation,
            } => {
                let copy = self
                    .current
                    .as_mut()
                    .filter(|copy| copy.generation == generation)
                    .ok_or_else(stale)?;
                self.high = self.high.max(revision);
                copy.revision = copy.revision.max(revision);
                Ok(false)
            }
        }
    }

    fn detach_current(&mut self) -> io::Result<()> {
        if self.current.is_some() && self.detached.len() == MAX_DETACHED {
            return Err(io::Error::new(
                io::ErrorKind::WouldBlock,
                "too many detached replica handles",
            ));
        }
        if let Some(copy) = self.current.take() {
            self.detached.push(copy.generation);
        }
        Ok(())
    }
}

pub(super) fn stale() -> io::Error {
    io::Error::new(io::ErrorKind::WouldBlock, "replica ownership changed")
}

pub(super) fn directory(data: &Path, stream: StreamId, generation: u64) -> PathBuf {
    if generation == 0 {
        data.join(format!("{:032x}", stream.0))
    } else {
        data.join(format!("{:032x}-{generation:016x}", stream.0))
    }
}
