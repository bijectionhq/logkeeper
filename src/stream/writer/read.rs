//! Validate the stream floor on a fresh quorum before reading keeper payloads.

use std::time::Duration;

use futures::{StreamExt, stream::FuturesUnordered};
use journal_contract::{Epoch, JournalError, Lsn, Page, Result};
use tokio::time::{Instant, timeout_at};

use super::{Io, KeeperId, Reply, Request, Stream, head::check_keeper, quorum, refusal};

pub(super) async fn read(
    io: &Io,
    stream: &Stream,
    from: Lsn,
    max: usize,
    wait: Duration,
) -> Result<Page> {
    let deadline = Instant::now() + wait.min(Duration::from_millis(u32::MAX.into()));
    loop {
        let mut samples = quorum(FuturesUnordered::from_iter(stream.ensemble.map(
            |keeper| async move {
                let view = check_keeper(io, stream, keeper, Epoch(0)).await?;
                Ok((keeper, view.floor, view.head))
            },
        )))
        .await?;

        // A completed trim and this read each contact two members of the same ensemble.
        let floor = samples.iter().map(|&(_, floor, _)| floor).max().unwrap();
        if from < floor {
            return Err(JournalError::Trimmed { floor });
        }
        samples.sort_unstable_by_key(|&(_, _, tail)| std::cmp::Reverse(tail));
        let tail = samples[0].2;

        if from <= tail {
            let mut errors = Vec::new();
            for (keeper, _, head) in samples {
                if head < tail {
                    break;
                }
                match records(io, keeper, stream, from, max, tail).await {
                    Ok(records) => {
                        return Ok(Page {
                            floor,
                            records,
                            head: tail,
                        });
                    }
                    Err(error @ JournalError::Trimmed { .. }) => return Err(error),
                    Err(error) => errors.push(error),
                }
            }
            return Err(refusal(&errors));
        }
        if Instant::now() >= deadline {
            return Ok(Page {
                floor,
                records: Vec::new(),
                head: tail,
            });
        }

        // A single keeper can wake the read. Refresh the quorum before serving it.
        let remaining = deadline.saturating_duration_since(Instant::now());
        let wait_ms = remaining.as_nanos().div_ceil(1_000_000) as u32;
        let mut polls = FuturesUnordered::from_iter(samples.into_iter().map(|(keeper, _, _)| {
            io.call(
                keeper,
                Request::Read {
                    stream: stream.id,
                    from,
                    max: 1,
                    wait_ms,
                },
            )
        }));
        while let Ok(Some(reply)) = timeout_at(deadline, polls.next()).await {
            match reply {
                Ok(Reply::Records { head, .. }) if head >= from => break,
                Err(JournalError::Trimmed { .. } | JournalError::Deleted) => break,
                _ if !polls.is_empty() => continue,
                _ => tokio::time::sleep_until(deadline).await,
            }
        }
    }
}

async fn records(
    io: &Io,
    keeper: KeeperId,
    stream: &Stream,
    from: Lsn,
    max: usize,
    tail: Lsn,
) -> Result<Vec<(Lsn, bytes::Bytes)>> {
    let count = (tail.0 - from.0 + 1).min(max as u64);
    let mut records = Vec::new();
    while (records.len() as u64) < count {
        let at = Lsn(from.0 + records.len() as u64);
        let max = u32::try_from(count - records.len() as u64).unwrap_or(u32::MAX);
        let reply = io
            .call(
                keeper,
                Request::Read {
                    stream: stream.id,
                    from: at,
                    max,
                    wait_ms: 0,
                },
            )
            .await?;
        let Reply::Records {
            records: chunk,
            head,
            ..
        } = reply
        else {
            return Err(JournalError::Unavailable);
        };
        if head < tail
            || chunk.is_empty()
            || chunk.len() > max as usize
            || !chunk
                .iter()
                .enumerate()
                .all(|(i, (lsn, _))| at.0.checked_add(i as u64) == Some(lsn.0))
        {
            return Err(JournalError::Unavailable);
        }
        records.extend(chunk);
    }
    Ok(records)
}
