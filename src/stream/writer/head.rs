//! A fresh quorum round for the callers queued when the round opens.

use std::{sync::Arc, time::Duration};

use futures::{StreamExt, stream::FuturesUnordered};
use journal_contract::{Epoch, JournalError, Lsn, Result};
use tokio::sync::oneshot;

use super::{
    Io, KeeperId, Reply, Request, Stream,
    append::Active,
    decision::{eligible_sample, head_quorum, sample_index},
    refusal,
};
use crate::stream::wire::StreamView;

const RETRY: Duration = Duration::from_millis(1);
const MAX_RETRY: Duration = Duration::from_millis(32);
/// How long an observer waits for its read index to be covered by published heads.
const SETTLE: Duration = Duration::from_secs(2);

pub(super) async fn head(io: Arc<Io>, stream: Arc<Stream>) -> Result<Lsn> {
    let (send, receive) = oneshot::channel();
    {
        let mut heads = stream.heads.lock();
        if heads.is_empty() {
            let stream = stream.clone();
            tokio::spawn(async move {
                tokio::task::yield_now().await;
                let waiting = std::mem::take(&mut *stream.heads.lock());
                let active = stream.active.lock().clone();
                let result = match check(&io, &stream, active.clone()).await {
                    Err(JournalError::Fenced { .. } | JournalError::Unavailable)
                        if active.is_some() =>
                    {
                        observer(&io, &stream).await
                    }
                    result => result,
                };
                for head in waiting {
                    let _ = head.send(result.clone());
                }
            });
        }
        heads.push(send);
    }
    receive.await.unwrap_or(Err(JournalError::Unavailable))
}

pub(super) async fn check(io: &Io, stream: &Stream, active: Option<Arc<Active>>) -> Result<Lsn> {
    if let Some(active) = active {
        writer(io, stream, &active).await
    } else {
        observer(io, stream).await
    }
}

async fn writer(io: &Io, stream: &Stream, active: &Active) -> Result<Lsn> {
    let opened = active.open_round();
    // Give append lanes an opportunity to issue a request after the round opens.
    tokio::task::yield_now().await;
    let mut calls = FuturesUnordered::from_iter(stream.ensemble.into_iter().enumerate().map(
        |(index, keeper)| async move {
            if let Some(mut observation) = active.observation(index, opened) {
                if let Ok(tail) = observation.wait_for(|seen| seen.is_some()).await {
                    match tail.as_ref().unwrap() {
                        Ok(tail) => return Ok(*tail),
                        Err(error @ JournalError::Fenced { .. }) => return Err(error.clone()),
                        _ => {}
                    }
                }
            }
            let view = check_keeper(io, stream, keeper, active.epoch).await?;
            match view.promised {
                Some((current, identity))
                    if current > active.epoch
                        || (current == active.epoch
                            && (&identity != io.transport.identity()
                                || view.proposal != Some(io.proposal))) =>
                {
                    Err(JournalError::Fenced { current })
                }
                Some((epoch, _)) if epoch == active.epoch && view.synced == Some(epoch) => {
                    Ok(view.tail)
                }
                _ => Err(JournalError::Unavailable),
            }
        },
    ));
    let mut count = 0;
    let mut sample = Lsn(0);
    let mut errors = Vec::new();
    while let Some(reply) = calls.next().await {
        match reply {
            Ok(tail) => {
                count += 1;
                sample = Lsn(sample_index(sample.0, tail.0));
                if head_quorum(count) {
                    let head = active.cover(sample).await?;
                    active.published(head).await?;
                    return Ok(head);
                }
            }
            Err(error @ JournalError::Fenced { current }) if current > active.epoch => {
                return Err(error);
            }
            Err(error) => errors.push(error),
        }
    }
    Err(refusal(&errors))
}

/// How an observer chooses the position that later rounds must cover.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Index {
    /// Keep the first quorum's maximum eligible tail. Later rounds wait for it.
    Pinned,
    /// Negative control: every round samples a new tail, which concurrent appends
    /// can keep ahead of the published heads indefinitely.
    #[cfg(test)]
    Resampled,
}

impl Index {
    fn resamples(self) -> bool {
        match self {
            Self::Pinned => false,
            #[cfg(test)]
            Self::Resampled => true,
        }
    }
}

async fn observer(io: &Io, stream: &Stream) -> Result<Lsn> {
    observe(io, stream, Index::Pinned).await
}

/// The read index is the maximum tail of an eligible quorum in the first complete round.
/// It covers every chosen record, hence every acknowledged append, at the invocation.
/// Any committed position at or above it is a linearizable head. Appends that keep
/// arriving advance tails but never move the index, so they cannot starve the call.
pub(super) async fn observe(io: &Io, stream: &Stream, index: Index) -> Result<Lsn> {
    let deadline = tokio::time::Instant::now() + SETTLE;
    let mut target = None;
    let mut pause = RETRY;
    loop {
        let result = observer_round(io, stream, &mut target).await;
        if result != Err(JournalError::Unavailable) || tokio::time::Instant::now() >= deadline {
            return result;
        }
        if index.resamples() {
            target = None;
        }
        tokio::time::sleep(pause).await;
        pause = (pause * 2).min(MAX_RETRY);
    }
}

async fn observer_round(io: &Io, stream: &Stream, target: &mut Option<Lsn>) -> Result<Lsn> {
    let mut calls = FuturesUnordered::from_iter(
        stream
            .ensemble
            .map(|keeper| check_keeper(io, stream, keeper, Epoch(0))),
    );
    let mut views = Vec::<StreamView>::new();
    let mut errors = Vec::new();
    while let Some(reply) = calls.next().await {
        match reply {
            Ok(view) => views.push(view),
            Err(error) => errors.push(error),
        }
        if let Some(head) = observed_head(&views, *target) {
            return Ok(head);
        }
    }
    if target.is_none() {
        *target = read_index(&views);
    }
    Err(refusal(&errors))
}

/// Views at the highest promised epoch, from a keeper synced at that epoch and with
/// the same promise as `candidate`.
fn eligible<'a>(
    views: &'a [StreamView],
    candidate: &'a StreamView,
) -> impl Iterator<Item = &'a StreamView> + 'a {
    let epoch = views
        .iter()
        .filter_map(|view| view.promised.as_ref().map(|p| p.0))
        .max();
    views.iter().filter(move |view| {
        eligible_sample(
            view.promised.as_ref().map(|p| (p.0).0),
            view.synced.map(|epoch| epoch.0),
            epoch.map(|epoch| epoch.0),
            view.promised == candidate.promised && view.proposal == candidate.proposal,
        )
    })
}

/// The maximum tail of an eligible quorum, if the views contain one.
fn read_index(views: &[StreamView]) -> Option<Lsn> {
    views.iter().find_map(|candidate| {
        head_quorum(eligible(views, candidate).count())
            .then(|| eligible(views, candidate).map(|view| view.tail).max())
            .flatten()
    })
}

/// Without a target, the eligible maximum tail must already be covered by a quorum of
/// published heads. With a pinned target, a quorum of eligible heads must reach it.
pub(super) fn observed_head(views: &[StreamView], target: Option<Lsn>) -> Option<Lsn> {
    views.iter().find_map(|candidate| {
        let index = match target {
            Some(target) => target,
            None => eligible(views, candidate).map(|view| view.tail).max()?,
        };
        head_quorum(
            eligible(views, candidate)
                .filter(|view| view.head >= index)
                .count(),
        )
        .then_some(index)
    })
}

pub(super) async fn check_keeper(
    io: &Io,
    stream: &Stream,
    keeper: KeeperId,
    epoch: Epoch,
) -> Result<StreamView> {
    match io
        .call(
            keeper,
            Request::Check {
                stream: stream.id,
                epoch,
            },
        )
        .await?
    {
        Reply::Checked(view)
            if view.head <= view.tail
                && view.floor.0 > 0
                && view.floor.0 - 1 <= view.head.0
                && view.ensemble == stream.ensemble
                && !view.learner =>
        {
            Ok(view)
        }
        _ => Err(JournalError::Unavailable),
    }
}
