//! Seal and recovery over the accepted prefix.

use bytes::Bytes;
use futures::{StreamExt, stream::FuturesUnordered};
use journal_contract::{Epoch, JournalError, Lsn, Result, StreamId};

use super::{Io, KeeperId, Reply, Request, Stream, decision::outranks, quorum};

use crate::stream::wire::{EpochRun, StreamView};

// A keeper is synced at epoch e once e's writer has copied its whole recovered history onto it;
// only then does it accept e's appends.
// The winner is the reply greatest by (synced epoch, end), as in Viewstamped Replication's view
// change: a commit at e reached a quorum of keepers synced at e, every seal quorum meets that
// quorum, and a keeper synced later holds a history that already contains the commit.
// Two keepers agreeing on a record's epoch at an LSN agree on the record and everything before it,
// because one writer creates at most one record per LSN and copies only whole prefixes.
#[derive(Clone)]
pub(super) struct Recovery {
    pub(super) epoch: Epoch,
    source: KeeperId,
    history: StreamView,
    pub(super) floor: Lsn,
}

impl Recovery {
    pub(super) async fn choose(io: &Io, stream: &Stream, epoch: Epoch) -> Result<Self> {
        let replies = quorum(FuturesUnordered::from_iter(stream.ensemble.map(
            |keeper| async move {
                Ok((
                    keeper,
                    seal(io, keeper, stream.id, stream.ensemble, epoch).await?,
                ))
            },
        )))
        .await?;
        let [(first, a), (second, b)] = replies.try_into().unwrap();
        let floor = a.floor.max(b.floor);
        let commit = a.commit.max(b.commit);
        let (source, history) = if outranks(
            a.synced.map(|e| e.0),
            a.end.0,
            b.synced.map(|e| e.0),
            b.end.0,
        ) {
            (second, b)
        } else {
            (first, a)
        };
        if history.end < commit || history.end.0 == u64::MAX {
            return Err(JournalError::Unavailable);
        }
        Ok(Self {
            epoch,
            source,
            history,
            floor,
        })
    }

    pub(super) fn end(&self) -> Lsn {
        self.history.end
    }

    pub(super) async fn sync(
        &self,
        io: &Io,
        id: StreamId,
        ensemble: [KeeperId; 3],
        keeper: KeeperId,
        floor: Lsn,
    ) -> Result<Lsn> {
        let target = seal(io, keeper, id, ensemble, self.epoch).await?;
        if target.synced == Some(self.epoch) {
            // A lost complete reply is retried at the same epoch and with the same history.
            if target.end < self.end()
                || divergence(&target, &self.history, floor.max(target.floor)).is_some()
            {
                return Err(JournalError::Unavailable);
            }
            if floor > target.floor {
                return install_floor(io, keeper, id, self.epoch, floor).await;
            }
            return Ok(self.end());
        }

        let floor = floor.max(target.floor);
        let commit = target.commit.max(Lsn(floor.0 - 1));
        let expected_end = self.end().max(commit);
        let mut from = divergence(&target, &self.history, floor)
            .unwrap_or_else(|| Lsn(target.end.min(self.end()).0.saturating_add(1).max(floor.0)));
        if from <= target.commit {
            return Err(JournalError::Unavailable);
        }
        while from <= self.end() {
            // Each chunk is at most one record, including when records reach the transport limit.
            let (epoch, record) = self.fetch(io, id, ensemble, from).await?;
            let run = EpochRun {
                epoch,
                first: from,
                last: from,
            };
            send_sync(
                io,
                keeper,
                id,
                self.epoch,
                floor,
                from,
                Some((run, record)),
                commit,
                false,
            )
            .await?;
            from = Lsn(from.0 + 1);
        }
        let end = send_sync(io, keeper, id, self.epoch, floor, from, None, commit, true).await?;
        if end != expected_end {
            return Err(JournalError::Unavailable);
        }
        Ok(end)
    }

    async fn fetch(
        &self,
        io: &Io,
        stream: StreamId,
        ensemble: [KeeperId; 3],
        from: Lsn,
    ) -> Result<(Epoch, Bytes)> {
        let epoch = epoch_at(&self.history, from).ok_or(JournalError::Unavailable)?;
        // Prefer the selected keeper. Other keepers may already hold an identical repaired prefix.
        if let Ok(record) = fetch(io, self.source, stream, self.epoch, from).await {
            return Ok((epoch, record));
        }
        let mut calls =
            FuturesUnordered::from_iter(ensemble.into_iter().filter(|id| *id != self.source).map(
                |keeper| async move {
                    let view = seal(io, keeper, stream, ensemble, self.epoch).await?;
                    if epoch_at(&view, from) != Some(epoch) {
                        return Err(JournalError::Unavailable);
                    }
                    fetch(io, keeper, stream, self.epoch, from).await
                },
            ));
        while let Some(result) = calls.next().await {
            if let Ok(record) = result {
                return Ok((epoch, record));
            }
        }
        Err(JournalError::Unavailable)
    }
}

pub(super) async fn install_floor(
    io: &Io,
    keeper: KeeperId,
    stream: StreamId,
    epoch: Epoch,
    floor: Lsn,
) -> Result<Lsn> {
    let through = Lsn(floor.0 - 1);
    let end = send_sync(
        io, keeper, stream, epoch, floor, floor, None, through, false,
    )
    .await?;
    if end < through {
        return Err(JournalError::Unavailable);
    }
    Ok(end)
}

pub(super) async fn fetch(
    io: &Io,
    keeper: KeeperId,
    stream: StreamId,
    epoch: Epoch,
    from: Lsn,
) -> Result<Bytes> {
    match io
        .call(
            keeper,
            Request::Recover {
                stream,
                epoch,
                holder: io.holder,
                from,
                max: 1,
            },
        )
        .await?
    {
        Reply::Records { mut records, .. } if records.len() == 1 && records[0].0 == from => {
            Ok(records.pop().unwrap().1)
        }
        _ => Err(JournalError::Unavailable),
    }
}

async fn seal(
    io: &Io,
    keeper: KeeperId,
    stream: StreamId,
    ensemble: [KeeperId; 3],
    epoch: Epoch,
) -> Result<StreamView> {
    match io
        .call(
            keeper,
            Request::Seal {
                stream,
                ensemble,
                epoch,
                holder: io.holder,
            },
        )
        .await?
    {
        Reply::Sealed(view)
            if view.promised == Some((epoch, io.holder))
                && view.commit <= view.end
                && view.floor.0 != 0
                && view.floor.0 - 1 <= view.commit.0
                && view.ensemble == ensemble
                && !view.learner
                && view.synced.is_none_or(|synced| synced <= epoch) =>
        {
            Ok(view)
        }
        _ => Err(JournalError::Unavailable),
    }
}

async fn send_sync(
    io: &Io,
    keeper: KeeperId,
    stream: StreamId,
    epoch: Epoch,
    floor: Lsn,
    from: Lsn,
    record: Option<(EpochRun, Bytes)>,
    commit: Lsn,
    complete: bool,
) -> Result<Lsn> {
    let (runs, records) = record.into_iter().unzip();
    match io
        .call(
            keeper,
            Request::Sync {
                stream,
                epoch,
                holder: io.holder,
                floor,
                from,
                records,
                runs,
                commit,
                complete,
            },
        )
        .await?
    {
        Reply::Synced { end } => Ok(end),
        _ => Err(JournalError::Unavailable),
    }
}

fn epoch_at(view: &StreamView, lsn: Lsn) -> Option<Epoch> {
    let run = view.runs.get(
        view.runs
            .partition_point(|run| run.first <= lsn)
            .checked_sub(1)?,
    )?;
    (lsn <= run.last).then_some(run.epoch)
}

fn divergence(a: &StreamView, b: &StreamView, floor: Lsn) -> Option<Lsn> {
    let through = a.end.min(b.end);
    std::iter::once(floor)
        .chain(a.runs.iter().chain(&b.runs).map(|run| run.first))
        .filter(|lsn| (floor..=through).contains(lsn))
        .filter(|&lsn| epoch_at(a, lsn) != epoch_at(b, lsn))
        .min()
}
