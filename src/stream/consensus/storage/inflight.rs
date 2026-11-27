//! A leader's appends whose WAL write is still in flight.
//!
//! A leader returns from `append` once its entries are queued for the WAL,
//! so OpenRaft replicates them while the leader's own sync runs, and reports
//! durability later through `IOFlushed`. OpenRaft counts the leader toward
//! commit only then, so a commit still needs two durable copies. Until the
//! write lands, the entries are read from here.
//!
//! Every queued write of a stream goes through the application WAL queue,
//! which the WAL thread drains in order. A write on another queue, such as a
//! truncation or a follower append, could overtake it, so it waits here
//! until the stream has nothing in flight.

use std::{
    collections::{BTreeMap, VecDeque},
    io,
    ops::RangeBounds,
};

use parking_lot::Mutex;
use tokio::sync::watch;

use super::{Entry, LogId};

pub(in crate::stream::consensus) struct Inflight {
    writes: Mutex<Writes>,
    changed: watch::Sender<u64>,
}

#[derive(Default)]
struct Writes {
    next: u64,
    /// The writes in flight: id, first and last index.
    queue: VecDeque<(u64, u64, u64)>,
    entries: BTreeMap<u64, Entry>,
    failed: bool,
}

impl Default for Inflight {
    fn default() -> Self {
        Self {
            writes: Mutex::default(),
            changed: watch::channel(0).0,
        }
    }
}

impl Inflight {
    /// Makes `entries` readable before their write is queued. Returns the
    /// write's ID for `finish`.
    pub fn begin(&self, entries: &[Entry]) -> u64 {
        let mut writes = self.writes.lock();
        let id = writes.next;
        writes.next += 1;
        if let (Some(first), Some(last)) = (entries.first(), entries.last()) {
            let (first, last) = (first.log_id.index, last.log_id.index);
            writes.entries.split_off(&first);
            writes.entries.extend(
                entries
                    .iter()
                    .map(|entry| (entry.log_id.index, entry.clone())),
            );
            writes.queue.push_back((id, first, last));
        }
        id
    }

    /// Ends write `id`. Its entries are durable once it succeeded, so they
    /// are read from the WAL from now on.
    pub fn finish(&self, id: u64, durable: bool) {
        {
            let mut writes = self.writes.lock();
            writes.queue.retain(|(write, ..)| *write != id);
            let queue = writes.queue.clone();
            writes.entries.retain(|index, _| {
                queue
                    .iter()
                    .any(|(_, first, last)| (*first..=*last).contains(index))
            });
            writes.failed |= !durable;
        }
        self.changed.send_modify(|version| *version += 1);
    }

    /// The entries in flight within `range`.
    pub fn read(&self, range: impl RangeBounds<u64>) -> Vec<(u64, Entry)> {
        self.writes
            .lock()
            .entries
            .range(range)
            .map(|(index, entry)| (*index, entry.clone()))
            .collect()
    }

    pub fn last(&self) -> Option<LogId> {
        self.writes
            .lock()
            .entries
            .last_key_value()
            .map(|(_, entry)| entry.log_id)
    }

    #[cfg(test)]
    pub fn idle(&self) -> bool {
        self.writes.lock().queue.is_empty()
    }

    /// Waits until nothing is in flight.
    pub async fn drained(&self) {
        self.wait(|writes| writes.queue.is_empty()).await;
    }

    /// Waits until every entry through `index` is durable. Fails once a
    /// write in flight failed, since its entries never reach the WAL.
    pub async fn durable_through(&self, index: u64) -> io::Result<()> {
        let failed = self
            .wait(|writes| writes.failed || writes.queue.iter().all(|(_, first, _)| *first > index))
            .await;
        if failed {
            Err(io::Error::other("a leader WAL append failed"))
        } else {
            Ok(())
        }
    }

    /// Clears a failure once nothing is in flight, for a reopened group.
    pub fn reset(&self) {
        let mut writes = self.writes.lock();
        if writes.queue.is_empty() {
            writes.failed = false;
        }
    }

    /// Waits for `ready`, then reports whether a write failed.
    async fn wait(&self, ready: impl Fn(&Writes) -> bool) -> bool {
        let mut changed = self.changed.subscribe();
        loop {
            {
                let writes = self.writes.lock();
                if ready(&writes) {
                    return writes.failed;
                }
            }
            if changed.changed().await.is_err() {
                return true;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stream::consensus::state::Command;

    fn entry(index: u64) -> Entry {
        Entry {
            log_id: LogId::new(
                openraft::vote::leader_id_std::CommittedLeaderId::new(2),
                index,
            ),
            payload: openraft::EntryPayload::Normal(Command::Delete),
        }
    }

    #[tokio::test]
    async fn entries_stay_readable_until_their_own_write_ends() {
        let inflight = Inflight::default();
        let first = inflight.begin(&[entry(1), entry(2)]);
        let second = inflight.begin(&[entry(3)]);
        assert_eq!(inflight.last().map(|id| id.index), Some(3));
        let through_two = inflight.durable_through(2);
        let through_three = inflight.durable_through(3);
        tokio::pin!(through_two, through_three);
        assert!(futures::poll!(through_two.as_mut()).is_pending());
        // The later write may report first; the earlier entries stay.
        inflight.finish(second, true);
        assert_eq!(
            inflight
                .read(..)
                .into_iter()
                .map(|(i, _)| i)
                .collect::<Vec<_>>(),
            [1, 2]
        );
        assert!(futures::poll!(through_two.as_mut()).is_pending());
        inflight.finish(first, true);
        through_two.await.unwrap();
        through_three.await.unwrap();
        assert!(inflight.read(..).is_empty() && inflight.idle());
        inflight.drained().await;
    }

    #[tokio::test]
    async fn a_failed_write_fails_its_waiters_until_reset() {
        let inflight = Inflight::default();
        let id = inflight.begin(&[entry(1)]);
        let waiting = inflight.durable_through(1);
        tokio::pin!(waiting);
        assert!(futures::poll!(waiting.as_mut()).is_pending());
        inflight.finish(id, false);
        assert!(waiting.await.is_err());
        assert!(inflight.read(..).is_empty());
        inflight.reset();
        inflight.durable_through(1).await.unwrap();
    }
}
