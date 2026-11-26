mod inflight;
mod media;
mod objects;
mod segment;
mod snapshot;
mod space;
#[cfg(test)]
mod tests;
mod wal;
mod watchdog;

use std::{collections::BTreeMap, io, ops::RangeBounds, sync::Arc};

use journal_contract::StreamId;
use openraft::{
    LogState, RaftLogReader,
    storage::{IOFlushed, RaftLogStorage},
};
use parking_lot::Mutex;
use uuid::Uuid;

use super::network::has_application_entries;
use super::{Entry, Genesis, LogId, RaftTypes, Vote};

pub(super) use inflight::Inflight;
pub(super) use media::{Authority, Enrollment, Incarnations};
#[cfg(any(test, feature = "consensus-testing"))]
pub(super) use media::{Provision, hex, sha256};
pub(super) use objects::Object;
pub(super) use snapshot::{Pin, SnapshotFile, StateMachine, repair_snapshot, replay};
pub(super) use space::{Admission, MAX_TRANSFER_FILE};
#[cfg(test)]
pub(super) use wal::ReplicaFault;
pub(super) use wal::{CatalogEntry, Disk, Record};

#[derive(Clone, Default)]
struct Log {
    vote: Option<Vote>,
    purged: Option<LogId>,
    snapshot: Option<snapshot::Selected>,
    entries: BTreeMap<u64, Entry>,
    ownership: super::ownership::Ownership,
    segments: BTreeMap<u64, std::sync::Arc<objects::Object>>,
}

#[derive(Clone)]
pub(super) struct LogStore {
    pub disk: Disk,
    pub stream: StreamId,
    pub state: StateMachine,
    pub keeper: u128,
    pub generation: u64,
    pub follower: Arc<FollowerAppend>,
    /// The leader's own appends return before their WAL write is durable.
    pub asynchronous: bool,
    pub inflight: Arc<Inflight>,
}

// One per replica generation. OpenRaft may omit an already accepted prefix,
// so only the exact ordered suffix of the authenticated request may take it.
#[derive(Default)]
pub(super) struct FollowerAppend {
    active: Mutex<Option<AcceptedAppend>>,
}

struct AcceptedAppend {
    vote: Vote,
    entries: Vec<Entry>,
    disk: Option<space::Reservation>,
}

pub(super) struct FollowerGuard(Arc<FollowerAppend>);

impl FollowerAppend {
    pub fn admit(
        self: &Arc<Self>,
        disk: &Disk,
        scope: StreamId,
        vote: Vote,
        entries: &[Entry],
    ) -> Result<FollowerGuard, Admission> {
        let mut active = self.active.lock();
        if active.is_some() {
            return Err(Admission::Space);
        }
        let reservation = disk.reserve_replication(scope, Uuid::new_v4(), entries)?;
        *active = Some(AcceptedAppend {
            vote,
            entries: entries.to_vec(),
            disk: Some(reservation),
        });
        Ok(FollowerGuard(self.clone()))
    }

    fn take(&self, vote: Option<Vote>, entries: &[Entry]) -> Option<space::Reservation> {
        let mut active = self.active.lock();
        let accepted = active.as_mut()?;
        if vote != Some(accepted.vote) || entries.is_empty() || !accepted.entries.ends_with(entries)
        {
            return None;
        }
        accepted.disk.take()
    }
}

impl Drop for FollowerGuard {
    fn drop(&mut self) {
        self.0.active.lock().take();
    }
}

enum Queue {
    Ordinary,
    Maintenance,
    Covered,
    Protocol,
}

impl RaftLogReader<RaftTypes> for LogStore {
    async fn try_get_log_entries<R: RangeBounds<u64> + Clone + std::fmt::Debug + Send>(
        &mut self,
        range: R,
    ) -> io::Result<Vec<Entry>> {
        // Read the writes in flight first: one that lands meanwhile is then
        // in the WAL, and never in neither.
        let inflight = self.inflight.read(range.clone());
        Ok(self.disk.log(self.stream, |log| {
            if inflight.is_empty() {
                return log
                    .entries
                    .range(range)
                    .map(|(_, entry)| entry.clone())
                    .collect();
            }
            let mut entries = log
                .entries
                .range(range)
                .map(|(index, entry)| (*index, entry.clone()))
                .collect::<BTreeMap<_, _>>();
            entries.extend(inflight);
            entries.into_values().collect()
        }))
    }

    async fn read_vote(&mut self) -> io::Result<Option<Vote>> {
        // OpenRaft reads the vote only at startup. A keeper that led a term
        // would otherwise resume leadership in that term and reuse its old
        // no-op as the read floor. The commit index is not persisted, so a
        // fresh `head` or configuration read could then miss entries that
        // were committed and acknowledged before the restart. Presenting the
        // keeper's own committed vote as uncommitted keeps the same ballot,
        // so it still refuses other candidates in that term. It also forces
        // an election, and the new leader's no-op commits the whole prefix
        // before any read is served.
        Ok(self.disk.log(self.stream, |log| log.vote).map(|vote| {
            if super::decisions::demotes_vote(
                vote.is_committed(),
                vote.leader_id().voted_for == self.keeper,
            ) {
                Vote::new(vote.leader_id().term, self.keeper)
            } else {
                vote
            }
        }))
    }
}

impl RaftLogStorage<RaftTypes> for LogStore {
    type LogReader = Self;

    async fn get_log_state(&mut self) -> io::Result<LogState<RaftTypes>> {
        Ok(self.disk.log(self.stream, |log| LogState {
            last_purged_log_id: log.purged,
            last_log_id: self.inflight.last().or(log
                .entries
                .last_key_value()
                .map(|(_, entry)| entry.log_id)
                .or(log.purged)),
        }))
    }

    async fn get_log_reader(&mut self) -> Self {
        self.clone()
    }

    async fn save_vote(&mut self, vote: &Vote) -> io::Result<()> {
        self.write(Record::Vote(self.stream, *vote)).await?;
        if vote.leader_id().voted_for == self.keeper {
            if vote.is_committed() {
                super::metrics::count(&self.disk.metrics.elections_won);
            } else {
                super::metrics::count(&self.disk.metrics.elections_started);
            }
        }
        Ok(())
    }

    async fn append<I>(&mut self, entries: I, callback: IOFlushed<RaftTypes>) -> io::Result<()>
    where
        I: IntoIterator<Item = Entry> + Send,
        I::IntoIter: Send,
    {
        let entries = entries.into_iter().collect::<Vec<_>>();
        let vote = self.disk.log(self.stream, |log| log.vote);
        let own = vote.is_some_and(|vote| vote.leader_id().voted_for == self.keeper);
        if own && self.asynchronous && has_application_entries(&entries) {
            return self.append_in_flight(entries, callback).await;
        }
        // Anything else lands only after the writes in flight, which another
        // WAL queue could overtake.
        self.inflight.drained().await;
        let result = if let Some(reservation) = self.follower.take(vote, &entries) {
            let record = Record::Owned(
                self.generation,
                Box::new(Record::Append(self.stream, entries)),
            );
            self.disk.replicate(record, reservation).await
        } else if has_application_entries(&entries) {
            if own {
                self.write_log(Record::Append(self.stream, entries), Queue::Ordinary)
                    .await
            } else {
                Err(super::invalid(
                    "follower append lacks its exact destination ticket",
                ))
            }
        } else if vote.is_none() && entries.first().is_some_and(|entry| entry.log_id.index == 0) {
            self.write_log(Record::Append(self.stream, entries), Queue::Maintenance)
                .await
        } else {
            self.write_log(Record::Append(self.stream, entries), Queue::Protocol)
                .await
        };
        match result {
            Ok(()) => {
                callback.io_completed(Ok(()));
                Ok(())
            }
            Err(error) => {
                callback.io_completed(Err(io::Error::other(error.to_string())));
                Err(error)
            }
        }
    }

    async fn truncate_after(&mut self, last_log_id: Option<LogId>) -> io::Result<()> {
        let start = last_log_id.map_or(0, |log_id| log_id.index + 1);
        // A truncation applied before an append still in flight would make
        // that append land past a gap.
        self.inflight.drained().await;
        self.write(Record::Truncate(self.stream, start)).await
    }

    async fn purge(&mut self, log_id: LogId) -> io::Result<()> {
        self.state.wait_for_snapshot(log_id).await?;
        self.inflight.drained().await;
        self.write_log(Record::Purge(self.stream, log_id), Queue::Covered)
            .await
    }
}

impl LogStore {
    /// Queues the leader's own entries and returns before they are durable,
    /// so they replicate while the leader syncs. OpenRaft counts the leader
    /// toward commit only once `callback` reports them durable.
    async fn append_in_flight(
        &self,
        entries: Vec<Entry>,
        callback: IOFlushed<RaftTypes>,
    ) -> io::Result<()> {
        if !self.state.healthy() {
            let error = io::Error::other("quarantined stream replica");
            callback.io_completed(Err(io::Error::other(error.to_string())));
            return Err(error);
        }
        let id = self.inflight.begin(&entries);
        let record = Record::Owned(
            self.generation,
            Box::new(Record::Append(self.stream, entries)),
        );
        let durable = match self.disk.submit_application(record).await {
            Ok(durable) => durable,
            Err(error) => {
                self.inflight.finish(id, false);
                callback.io_completed(Err(io::Error::other(error.to_string())));
                return Err(error);
            }
        };
        let inflight = self.inflight.clone();
        tokio::spawn(async move {
            let result = durable.await.map_err(io::Error::other).and_then(|r| r);
            inflight.finish(id, result.is_ok());
            callback.io_completed(result);
        });
        Ok(())
    }

    async fn write(&self, record: Record) -> io::Result<()> {
        self.write_log(record, Queue::Protocol).await
    }

    async fn write_log(&self, record: Record, queue: Queue) -> io::Result<()> {
        let record = Record::Owned(self.generation, Box::new(record));
        if !self.state.healthy() {
            return Err(io::Error::other("quarantined stream replica"));
        }
        match queue {
            Queue::Ordinary => self.disk.application(record).await,
            Queue::Maintenance => self.disk.maintenance(record).await,
            Queue::Covered => self.disk.covered(record).await,
            Queue::Protocol => self.disk.protocol(record).await,
        }
    }
}
