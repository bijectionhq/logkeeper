//! A fresh quorum round for the callers queued when the round opens.

use std::{sync::Arc, time::Duration};

use futures::{StreamExt, stream::FuturesUnordered};
use journal_contract::{Epoch, JournalError, Lsn, Result};
use tokio::sync::oneshot;

use super::{Io, KeeperId, QUORUM, Reply, Request, Stream, append::Active, refusal};
use crate::stream::wire::StreamView;

const RETRY: Duration = Duration::from_millis(1);
const SETTLE: Duration = Duration::from_millis(25);

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
                if let Ok(end) = observation.wait_for(|seen| seen.is_some()).await {
                    match end.as_ref().unwrap() {
                        Ok(end) => return Ok(*end),
                        Err(error @ JournalError::Fenced { .. }) => return Err(error.clone()),
                        _ => {}
                    }
                }
            }
            let view = check_keeper(io, stream, keeper, active.epoch).await?;
            match view.promised {
                Some((current, holder))
                    if current > active.epoch
                        || (current == active.epoch && holder != io.holder) =>
                {
                    Err(JournalError::Fenced { current })
                }
                Some((epoch, _)) if epoch == active.epoch && view.synced == Some(epoch) => {
                    Ok(view.end)
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
            Ok(end) => {
                count += 1;
                sample = sample.max(end);
                if count == QUORUM {
                    let end = active.cover(sample).await?;
                    active.published(end).await?;
                    return Ok(end);
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

async fn observer(io: &Io, stream: &Stream) -> Result<Lsn> {
    // Allow a concurrent seal or commit publication to finish. Each attempt
    // opens its own quorum round and must independently cover the result.
    let deadline = tokio::time::Instant::now() + SETTLE;
    loop {
        let result = observer_round(io, stream).await;
        if result != Err(JournalError::Unavailable) || tokio::time::Instant::now() >= deadline {
            return result;
        }
        tokio::time::sleep(RETRY).await;
    }
}

async fn observer_round(io: &Io, stream: &Stream) -> Result<Lsn> {
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
        if let Some(end) = observed_end(&views) {
            return Ok(end);
        }
    }
    Err(refusal(&errors))
}

fn observed_end(views: &[StreamView]) -> Option<Lsn> {
    let epoch = views
        .iter()
        .filter_map(|view| view.promised.map(|p| p.0))
        .max();
    views
        .iter()
        .filter(|view| view.synced == epoch)
        .find_map(|candidate| {
            let eligible = |view: &&StreamView| {
                view.promised == candidate.promised
                    && view.synced == epoch
                    && view.promised.map(|p| p.0) == epoch
            };
            let end = views.iter().filter(eligible).map(|view| view.end).max()?;
            (views
                .iter()
                .filter(eligible)
                .filter(|view| view.commit >= end)
                .count()
                >= QUORUM)
                .then_some(end)
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
            if view.commit <= view.end
                && view.floor.0 > 0
                && view.floor.0 - 1 <= view.commit.0
                && view.ensemble == stream.ensemble
                && !view.learner =>
        {
            Ok(view)
        }
        _ => Err(JournalError::Unavailable),
    }
}
