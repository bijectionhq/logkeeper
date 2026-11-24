//! A fresh quorum round for the callers queued when the round opens.

use std::sync::Arc;

use futures::{StreamExt, stream::FuturesUnordered};
use journal_contract::{Epoch, JournalError, Lsn, Result};
use tokio::sync::oneshot;

use super::{Io, KeeperId, Request, Stream, append::Active};
use crate::stream::{
    proposer::{
        driver,
        head::{Observer, Samples, checked_view, writer_tail},
    },
    wire::StreamView,
};

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
            writer_tail(view, active.epoch, io.transport.identity(), io.proposal)
        },
    ));
    let mut samples = Samples::new(active.epoch);
    while let Some(reply) = calls.next().await {
        if let Some(sample) = samples.receive(reply) {
            let head = active.cover(sample?).await?;
            active.published(head).await?;
            return Ok(head);
        }
    }
    Err(samples.error())
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

pub(super) async fn observe(io: &Io, stream: &Stream, index: Index) -> Result<Lsn> {
    let operation = Observer::new(stream.id, stream.ensemble, index.resamples());
    driver::run(&*io.transport, operation, Some(driver::RPC_TIMEOUT)).await
}

pub(super) async fn check_keeper(
    io: &Io,
    stream: &Stream,
    keeper: KeeperId,
    epoch: Epoch,
) -> Result<StreamView> {
    checked_view(
        io.call(
            keeper,
            Request::Check {
                stream: stream.id,
                epoch,
            },
        )
        .await?,
        stream.ensemble,
    )
}
