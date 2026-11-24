//! Serve a page from one keeper in transport preference order.

use std::time::Duration;

use journal_contract::{JournalError, Lsn, Page, Result};
use tokio::time::Instant;

use super::{Io, KeeperId, Reply, Request, Stream, refusal};

pub(super) async fn read(
    io: &Io,
    stream: &Stream,
    from: Lsn,
    max: usize,
    wait: Duration,
) -> Result<Page> {
    let deadline = Instant::now() + wait.min(Duration::from_millis(u32::MAX.into()));
    let mut empty = None;
    let mut errors = Vec::new();
    for keeper in io.transport.read_order(stream.ensemble) {
        let remaining = deadline.saturating_duration_since(Instant::now());
        let wait_ms = remaining.as_nanos().div_ceil(1_000_000) as u32;
        match page(io, keeper, stream, from, max, wait_ms).await {
            Ok(page) if max == 0 || !page.records.is_empty() => return Ok(page),
            Ok(page) => {
                empty.get_or_insert(page);
            }
            Err(error @ JournalError::Deleted) => return Err(error),
            Err(error) => errors.push(error),
        }
    }
    // A lagging keeper's empty page cannot satisfy a range observed trimmed.
    let floor = errors
        .iter()
        .filter_map(|error| match error {
            JournalError::Trimmed { floor } => Some(*floor),
            _ => None,
        })
        .max();
    if let Some(floor) = floor {
        return Err(JournalError::Trimmed { floor });
    }
    empty.ok_or_else(|| refusal(&errors))
}

async fn page(
    io: &Io,
    keeper: KeeperId,
    stream: &Stream,
    from: Lsn,
    max: usize,
    wait_ms: u32,
) -> Result<Page> {
    let request = |from, max, wait_ms| {
        io.call(
            keeper,
            Request::Read {
                stream: stream.id,
                from,
                max: u32::try_from(max).unwrap_or(u32::MAX),
                wait_ms,
            },
        )
    };
    let Reply::Records {
        floor,
        records,
        head,
    } = request(from, max, wait_ms).await?
    else {
        return Err(JournalError::Unavailable);
    };
    if floor.0 == 0 || floor > from || floor.0 - 1 > head.0 {
        return Err(JournalError::Unavailable);
    }
    let count = if from <= head {
        (head.0 - from.0 + 1).min(max as u64)
    } else {
        0
    };
    check_chunk(from, count, &records)?;
    let mut page = Page {
        floor,
        records,
        head,
    };

    // The keeper may split a page at the frame size. Use the first reply's
    // head for the whole page, even if the keeper has since advanced.
    while (page.records.len() as u64) < count {
        let at = Lsn(from.0 + page.records.len() as u64);
        let left = count - page.records.len() as u64;
        let Reply::Records {
            records,
            head: current,
            ..
        } = request(at, left as usize, 0).await?
        else {
            return Err(JournalError::Unavailable);
        };
        if current < head {
            return Err(JournalError::Unavailable);
        }
        check_chunk(at, left, &records)?;
        page.records.extend(records);
    }
    Ok(page)
}

fn check_chunk(from: Lsn, remaining: u64, records: &[(Lsn, bytes::Bytes)]) -> Result<()> {
    if (remaining != 0 && records.is_empty())
        || records.len() as u64 > remaining
        || !records
            .iter()
            .enumerate()
            .all(|(offset, (lsn, _))| from.0.checked_add(offset as u64) == Some(lsn.0))
    {
        return Err(JournalError::Unavailable);
    }
    Ok(())
}
