//! A page comes from one keeper and is bounded by its first reply's head.

use std::time::Duration;

use journal_contract::{JournalError, Lsn, Page, Result, StreamId};

use super::{Effects, Event, Operation, Response, Send, Slot, journal_reply, refusal};
use crate::stream::wire::{KeeperId, Reply, Request};

pub(in crate::stream) struct Read {
    stream: StreamId,
    from: Lsn,
    max: usize,
    wait: Duration,
    keepers: std::array::IntoIter<KeeperId, 3>,
    phase: Phase,
    empty: Option<Page>,
    errors: Vec<JournalError>,
}

enum Phase {
    New,
    First {
        keeper: KeeperId,
        poll: bool,
    },
    Rest {
        keeper: KeeperId,
        count: u64,
        page: Page,
    },
    Done,
}

impl Read {
    pub(in crate::stream) fn new(
        stream: StreamId,
        from: Lsn,
        max: usize,
        wait: Duration,
        keepers: [KeeperId; 3],
    ) -> Self {
        Self {
            stream,
            from,
            max,
            wait: wait.min(Duration::from_millis(u32::MAX.into())),
            keepers: keepers.into_iter(),
            phase: Phase::New,
            empty: None,
            errors: Vec::new(),
        }
    }

    fn next_keeper(&mut self, elapsed: Duration) -> Effects<Result<Page>> {
        if let Some(keeper) = self.keepers.next() {
            return self.first(keeper, self.wait.saturating_sub(elapsed));
        }
        let floor = self
            .errors
            .iter()
            .filter_map(|error| match error {
                JournalError::Trimmed { floor } => Some(*floor),
                _ => None,
            })
            .max();
        Effects::Complete(if let Some(floor) = floor {
            Err(JournalError::Trimmed { floor })
        } else {
            self.empty.take().ok_or_else(|| refusal(&self.errors))
        })
    }

    fn first(&mut self, keeper: KeeperId, remaining: Duration) -> Effects<Result<Page>> {
        let wait_ms = if self.max == 0 {
            0
        } else {
            remaining.as_nanos().div_ceil(1_000_000) as u32
        };
        self.phase = Phase::First {
            keeper,
            poll: wait_ms != 0,
        };
        let mut send = self.request(keeper, self.from, self.max as u64, wait_ms);
        if wait_ms != 0 {
            send.deadline = Some(self.wait);
        }
        Effects::Send(send)
    }

    fn request(&self, keeper: KeeperId, from: Lsn, max: u64, wait_ms: u32) -> Send {
        Send::new(
            Slot::First,
            keeper,
            Request::Read {
                stream: self.stream,
                from,
                max: u32::try_from(max).unwrap_or(u32::MAX),
                wait_ms,
            },
        )
    }

    fn rest(&mut self, keeper: KeeperId, count: u64, page: Page) -> Effects<Result<Page>> {
        let have = page.records.len() as u64;
        let send = self.request(keeper, Lsn(self.from.0 + have), count - have, 0);
        self.phase = Phase::Rest {
            keeper,
            count,
            page,
        };
        Effects::Send(send)
    }

    fn finish_page(&mut self, page: Result<Page>, elapsed: Duration) -> Effects<Result<Page>> {
        match page {
            Ok(page) if self.max == 0 || !page.records.is_empty() => Effects::Complete(Ok(page)),
            Ok(page) => {
                self.empty.get_or_insert(page);
                self.next_keeper(elapsed)
            }
            Err(JournalError::Deleted) => Effects::Complete(Err(JournalError::Deleted)),
            Err(error) => {
                self.errors.push(error);
                self.next_keeper(elapsed)
            }
        }
    }
}

impl Operation for Read {
    type Output = Result<Page>;

    fn advance(&mut self, event: Event, elapsed: Duration) -> Effects<Self::Output> {
        let phase = std::mem::replace(&mut self.phase, Phase::Done);
        match (phase, event) {
            (Phase::New, Event::Invoke) => self.next_keeper(elapsed),
            (Phase::First { keeper, poll: true }, Event::Expired(Slot::First)) => {
                // At the deadline take an immediate sample, including a racing publication.
                self.first(keeper, Duration::ZERO)
            }
            (Phase::First { keeper, .. }, Event::Reply(Slot::First, response)) => {
                let result = chunk(response, self.from).and_then(|page| {
                    let count = if self.from <= page.head {
                        (page.head.0 - self.from.0)
                            .saturating_add(1)
                            .min(self.max as u64)
                    } else {
                        0
                    };
                    check_chunk(self.from, count, &page.records)?;
                    Ok((count, page))
                });
                match result {
                    Ok((count, page)) if (page.records.len() as u64) < count => {
                        self.rest(keeper, count, page)
                    }
                    result => self.finish_page(result.map(|(_, page)| page), elapsed),
                }
            }
            (
                Phase::Rest {
                    keeper,
                    count,
                    mut page,
                },
                Event::Reply(Slot::First, response),
            ) => {
                let have = page.records.len() as u64;
                let at = Lsn(self.from.0 + have);
                let result = chunk(response, at).and_then(|next| {
                    if next.head < page.head {
                        return Err(JournalError::Unavailable);
                    }
                    check_chunk(at, count - have, &next.records)?;
                    page.records.extend(next.records);
                    Ok(page)
                });
                match result {
                    Ok(page) if (page.records.len() as u64) < count => {
                        self.rest(keeper, count, page)
                    }
                    result => self.finish_page(result, elapsed),
                }
            }
            (phase, _) => {
                self.phase = phase;
                Effects::Pending
            }
        }
    }

    fn exhausted() -> Self::Output {
        Err(JournalError::Unavailable)
    }
}

fn chunk(response: Response, from: Lsn) -> Result<Page> {
    match journal_reply(response) {
        Ok(Reply::Records {
            floor,
            records,
            head,
        }) if floor.0 > 0 && floor <= from && floor.0 - 1 <= head.0 => Ok(Page {
            floor,
            records,
            head,
        }),
        Err(JournalError::Trimmed { floor }) if floor <= from => Err(JournalError::Unavailable),
        Err(error) => Err(error),
        _ => Err(JournalError::Unavailable),
    }
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
