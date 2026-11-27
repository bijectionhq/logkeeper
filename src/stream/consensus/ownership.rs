//! Durable local ownership of replica directories. Placement proof is
//! obtained by the keeper before submitting an ownership transition.

use std::{
    io,
    path::{Path, PathBuf},
};

use journal_contract::StreamId;
use serde::{Deserialize, Serialize};

use super::{LogId, Stage, decisions};

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
    /// Stages an empty copy for a replacement that an operator recovery
    /// names, installed at once: the recovered survivor is elected by its
    /// replacements before any of them holds the log. Added last, so older
    /// keepers refuse a WAL that holds it.
    Recover(Stage),
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

    /// The recovery stage of the current copy, when it is an installed
    /// replacement that an operator recovery staged for `keeper`.
    pub fn recovery_stage(&self, keeper: uuid::Uuid) -> Option<&Stage> {
        let copy = self.current.as_ref().filter(|copy| copy.installed)?;
        copy.stage.as_ref().filter(|stage| {
            stage.recovery() && stage.target.contains(&keeper) && !stage.old.contains(&keeper)
        })
    }

    pub fn was_retired(&self, revision: u64, generation: u64) -> bool {
        self.retired == Some((revision, generation))
    }

    // Returns true when the old log and its selected snapshot cease to own
    // the replica. The durable vote remains at its enclosing log.
    pub fn apply(&mut self, change: Change, has_cut: impl Fn(LogId) -> bool) -> io::Result<bool> {
        match change {
            Change::Recover(stage) => {
                if let Some(copy) = self
                    .current
                    .as_mut()
                    .filter(|copy| copy.stage.as_ref() == Some(&stage))
                {
                    copy.installed = true;
                    return Ok(false);
                }
                // A retried recovery restages the copy an aborted attempt
                // left at the same revision. Keepers older than this refuse
                // the record when they replay it.
                let staged = self.current.as_ref().and_then(|copy| copy.stage.as_ref());
                let changed = match staged {
                    Some(staged)
                        if decisions::restages_recovery(
                            staged.recovery(),
                            stage.recovery(),
                            staged.stream == stage.stream
                                && staged.source == stage.source
                                && staged.old == stage.old
                                && staged.survivor() == stage.survivor(),
                        ) =>
                    {
                        let revision = stage.source.checked_add(1).ok_or_else(stale)?;
                        if revision < self.high {
                            return Err(stale());
                        }
                        self.stage_copy(stage, revision)?
                    }
                    _ => self.apply(Change::Stage(stage), has_cut)?,
                };
                if let Some(copy) = self.current.as_mut() {
                    copy.installed = true;
                }
                Ok(changed)
            }
            Change::Stage(stage) => {
                if self.contains_stage(&stage) {
                    return Ok(false);
                }
                let revision = stage.source.checked_add(1).ok_or_else(stale)?;
                // A move aborted before its joint configuration committed
                // leaves its copy at this revision; another move from the
                // same source restages it.
                let restages = self
                    .current
                    .as_ref()
                    .and_then(|copy| copy.stage.as_ref())
                    .is_some_and(|staged| {
                        decisions::restages_replacement(
                            staged.recovery(),
                            stage.recovery(),
                            staged.stream == stage.stream
                                && staged.source == stage.source
                                && staged.old == stage.old,
                            *staged == stage,
                        )
                    });
                if revision < self.high || (revision == self.high && !restages) {
                    return Err(stale());
                }
                self.stage_copy(stage, revision)
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

    /// Detaches the current copy and stages an empty one in a new
    /// generation.
    fn stage_copy(&mut self, stage: Stage, revision: u64) -> io::Result<bool> {
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

#[cfg(test)]
mod tests {
    use super::*;

    fn stage(old: [u128; 3], target: [u128; 3]) -> Stage {
        Stage {
            stream: StreamId(1),
            source: 0,
            old: old.map(uuid::Uuid::from_u128),
            target: target.map(uuid::Uuid::from_u128),
        }
    }

    fn recovered(first: &Stage) -> Ownership {
        let mut book = Ownership {
            current: None,
            ..Ownership::default()
        };
        assert!(
            book.apply(Change::Recover(first.clone()), |_| false)
                .unwrap()
        );
        book
    }

    #[test]
    fn a_retried_recovery_restages_the_copy_of_an_aborted_attempt() {
        let first = stage([1, 2, 3], [1, 4, 5]);
        let mut book = recovered(&first);
        let retry = stage([1, 2, 3], [1, 4, 6]);
        assert!(
            book.apply(Change::Recover(retry.clone()), |_| false)
                .unwrap()
        );
        assert!(book.contains_stage(&retry) && book.installed());
        assert_eq!(book.generation(), Some(2));
        assert_eq!(book.detached(), [1]);
        assert_eq!(book.high_water(), 1);
    }

    #[test]
    fn another_move_from_the_same_source_restages_an_aborted_copy() {
        let mut book = Ownership {
            current: None,
            ..Ownership::default()
        };
        let aborted = stage([1, 2, 3], [1, 2, 4]);
        assert!(book.apply(Change::Stage(aborted), |_| false).unwrap());
        let repair = stage([1, 2, 3], [2, 3, 4]);
        assert!(
            book.apply(Change::Stage(repair.clone()), |_| false)
                .unwrap()
        );
        assert!(book.contains_stage(&repair) && !book.installed());
        assert_eq!(book.generation(), Some(2));
        assert_eq!(book.detached(), [1]);
        assert_eq!(book.high_water(), 1);
        // Another source configuration at that revision stays refused.
        let mut other = stage([1, 2, 5], [1, 2, 4]);
        assert!(book.apply(Change::Stage(other.clone()), |_| false).is_err());
        // So does any stage below the high-water mark.
        other.old = [1, 2, 3].map(uuid::Uuid::from_u128);
        book.high = 2;
        assert!(book.apply(Change::Stage(other), |_| false).is_err());
    }

    #[test]
    fn another_stage_at_the_same_revision_stays_refused() {
        let first = stage([1, 2, 3], [1, 4, 5]);
        // Another survivor of the same lost configuration.
        let other = stage([1, 2, 3], [2, 4, 6]);
        let mut book = recovered(&first);
        assert!(book.apply(Change::Recover(other), |_| false).is_err());
        // An ordinary move at the same revision.
        let moved = stage([1, 2, 3], [1, 2, 4]);
        assert!(book.apply(Change::Stage(moved), |_| false).is_err());
        assert!(book.contains_stage(&first));
    }
}
