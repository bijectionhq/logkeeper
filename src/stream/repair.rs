//! Automatic repair of writer-driven streams after a keeper is lost.
//!
//! The repairer is an ordinary proposer with its own writer identity. For each stream
//! whose ensemble names the lost keeper, it runs the replacement protocol of
//! `verification/target-journal.md` section 3 at a fresh epoch above every promise it
//! observed. Safety rests on the keeper rules alone: epochs fence other proposers,
//! including a live writer, and Replace changes one slot after both survivors hold the
//! adopted history. Time only decides when to start, never what keepers accept.
//! Design: `verification/writer-driven-repair.md`.

use std::collections::BTreeMap;

use crate::stream::{
    proposer::{driver, sweep::Replacement},
    wire::*,
};

pub use crate::stream::proposer::sweep::{Sweep, SweepError};

#[cfg(feature = "stream")]
mod daemon;
#[cfg(feature = "stream")]
pub use daemon::{Config, KeeperEntry, USAGE, command};

/// Fresh-epoch attempts per stream in one pass when another proposer fences the sweep.
const ATTEMPTS: usize = 3;

/// One keeper of the cluster and its failure domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Member {
    pub id: KeeperId,
    pub zone: String,
}

/// Every keeper a stream can be placed on, including spares.
#[derive(Clone, Debug, Default)]
pub struct Roster {
    members: Vec<Member>,
}

impl Roster {
    pub fn new(members: impl IntoIterator<Item = Member>) -> Self {
        let mut members: Vec<_> = members.into_iter().collect();
        members.sort_by_key(|member| member.id);
        members.dedup_by_key(|member| member.id);
        Self { members }
    }

    pub fn members(&self) -> &[Member] {
        &self.members
    }

    fn zone(&self, keeper: KeeperId) -> Option<&str> {
        self.members
            .iter()
            .find(|member| member.id == keeper)
            .map(|member| member.zone.as_str())
    }

    /// A spare for `lost` outside `ensemble`, preferring the lost keeper's zone and
    /// otherwise a zone that neither survivor uses. The stream ID spreads streams over
    /// equal candidates, and the choice is stable across retries of the same move.
    fn spare(
        &self,
        stream: StreamId,
        ensemble: [KeeperId; 3],
        lost: KeeperId,
        unavailable: &[KeeperId],
    ) -> Option<KeeperId> {
        let eligible = |member: &&Member| {
            !ensemble.contains(&member.id) && member.id != lost && !unavailable.contains(&member.id)
        };
        let survivor_zones: Vec<_> = ensemble
            .iter()
            .filter(|&&id| id != lost)
            .filter_map(|&id| self.zone(id))
            .collect();
        let same: Vec<_> = match self.zone(lost) {
            Some(zone) => self
                .members
                .iter()
                .filter(eligible)
                .filter(|member| member.zone == zone)
                .collect(),
            None => Vec::new(),
        };
        let candidates = if same.is_empty() {
            self.members
                .iter()
                .filter(eligible)
                .filter(|member| !survivor_zones.contains(&member.zone.as_str()))
                .collect()
        } else {
            same
        };
        let pick = (stream.0 % candidates.len().max(1) as u128) as usize;
        candidates.get(pick).map(|member| member.id)
    }
}

/// What happened to one stream.
#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    /// The stream's ensemble now names `learner` instead of the lost keeper.
    Repaired { learner: KeeperId, epoch: Epoch },
    /// A previous pass or another repairer already completed the move.
    AlreadyRepaired,
    /// No eligible spare exists.
    NoSpare,
    /// The move did not complete. A later pass retries it; the protocol keeps every
    /// partial state safe and resumable.
    Failed(String),
}

#[derive(Debug, Default)]
pub struct Report {
    /// Streams found on reachable keepers whose ensemble names the lost keeper.
    pub listed: usize,
    pub outcomes: Vec<(StreamId, Outcome)>,
}

impl Report {
    /// The streams that still need a pass.
    pub fn pending(&self) -> usize {
        self.outcomes
            .iter()
            .filter(|(_, outcome)| matches!(outcome, Outcome::NoSpare | Outcome::Failed(_)))
            .count()
    }
}

/// Move every stream off `lost`. `unavailable` lists other keepers that must not be
/// chosen as spares, such as keepers that are also declared lost.
pub async fn repair_lost(
    transport: &dyn Transport,
    roster: &Roster,
    lost: KeeperId,
    unavailable: &[KeeperId],
) -> Report {
    let streams = affected(transport, roster, lost, unavailable).await;
    let mut report = Report {
        listed: streams.len(),
        outcomes: Vec::with_capacity(streams.len()),
    };
    for (stream, ensemble) in streams {
        let outcome = repair_stream(transport, roster, lost, unavailable, stream, ensemble).await;
        report.outcomes.push((stream, outcome));
    }
    report
}

/// The streams whose ensemble names `lost`, as listed by every reachable keeper. A
/// learner lists its stream too, so a move interrupted after both survivors installed
/// the new ensemble is still found through its learner.
pub async fn affected(
    transport: &dyn Transport,
    roster: &Roster,
    lost: KeeperId,
    unavailable: &[KeeperId],
) -> BTreeMap<StreamId, [KeeperId; 3]> {
    let mut found = BTreeMap::new();
    for member in roster.members() {
        if member.id == lost || unavailable.contains(&member.id) {
            continue;
        }
        let mut after = StreamId(0);
        loop {
            let request = Request::List {
                stream: after,
                member: lost,
                max: LIST_MAX,
            };
            let reply =
                tokio::time::timeout(driver::RPC_TIMEOUT, transport.call(member.id, request)).await;
            let Ok(Ok(Reply::Listed { streams })) = reply else {
                break;
            };
            let complete = streams.len() < LIST_MAX as usize;
            for (stream, ensemble) in &streams {
                if *stream <= after {
                    break;
                }
                found.entry(*stream).or_insert(*ensemble);
            }
            match streams.last() {
                Some((last, _)) if !complete && *last > after => after = *last,
                _ => break,
            }
        }
    }
    found
}

/// Replace `lost` in one stream's ensemble.
pub async fn repair_stream(
    transport: &dyn Transport,
    roster: &Roster,
    lost: KeeperId,
    unavailable: &[KeeperId],
    stream: StreamId,
    ensemble: [KeeperId; 3],
) -> Outcome {
    let Ok(survivors) = <[KeeperId; 2]>::try_from(
        ensemble
            .iter()
            .copied()
            .filter(|&id| id != lost)
            .collect::<Vec<_>>(),
    ) else {
        return Outcome::Failed(format!("ensemble {ensemble:?} does not name {lost:?}"));
    };
    let views =
        futures::future::join_all(survivors.map(|keeper| check(transport, keeper, stream))).await;
    let views: Vec<_> = views.into_iter().flatten().collect();
    let mut floor = views
        .iter()
        .filter_map(|view| view.promised.as_ref().map(|(epoch, ..)| *epoch))
        .max()
        .unwrap_or(Epoch(0));
    // A move interrupted after a survivor installed it names its learner. Resume it.
    let resumed = views
        .iter()
        .filter(|view| !view.learner)
        .find_map(|view| learner_of(ensemble, lost, view.ensemble));
    if views.len() == 2 && views.iter().all(|view| !view.ensemble.contains(&lost)) {
        if let Some(learner) = resumed {
            if check(transport, learner, stream)
                .await
                .is_some_and(|view| !view.learner && view.ensemble == views[0].ensemble)
            {
                return Outcome::AlreadyRepaired;
            }
        }
    }
    let Some(learner) = resumed.or_else(|| roster.spare(stream, ensemble, lost, unavailable))
    else {
        return Outcome::NoSpare;
    };
    let mut last = String::new();
    for _ in 0..ATTEMPTS {
        let Some(epoch) = floor.0.checked_add(1).map(Epoch) else {
            return Outcome::Failed("epoch space exhausted".into());
        };
        let plan = Sweep::new(stream, ensemble, survivors, learner, epoch);
        let operation = Replacement::new(plan, transport.identity().clone());
        match driver::run(transport, operation, Some(driver::RPC_TIMEOUT)).await {
            Ok(()) => return Outcome::Repaired { learner, epoch },
            Err(SweepError::Reply {
                reply: Reply::Refused(Refusal::Fenced { promised }),
                ..
            }) if promised >= epoch => {
                // Another proposer holds a higher promise. Seal above it.
                last = format!("fenced by epoch {}", promised.0);
                floor = promised;
            }
            Err(error) => return Outcome::Failed(error.to_string()),
        }
    }
    Outcome::Failed(last)
}

async fn check(
    transport: &dyn Transport,
    keeper: KeeperId,
    stream: StreamId,
) -> Option<StreamView> {
    let request = Request::Check {
        stream,
        epoch: Epoch(0),
    };
    match tokio::time::timeout(driver::RPC_TIMEOUT, transport.call(keeper, request)).await {
        Ok(Ok(Reply::Checked(view))) => Some(view),
        _ => None,
    }
}

/// The keeper that `installed` puts in place of `lost`, if it differs from `old`
/// exactly there.
fn learner_of(old: [KeeperId; 3], lost: KeeperId, installed: [KeeperId; 3]) -> Option<KeeperId> {
    let mut learner = None;
    for (before, after) in old.into_iter().zip(installed) {
        if before == after {
            continue;
        }
        if before != lost || learner.is_some() || old.contains(&after) {
            return None;
        }
        learner = Some(after);
    }
    learner
}

#[cfg(test)]
mod tests;
