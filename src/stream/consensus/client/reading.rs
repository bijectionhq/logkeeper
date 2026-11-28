use std::{collections::BTreeSet, time::Duration};

use futures::stream::{FuturesUnordered, StreamExt};
use journal_contract::{JournalError, Lsn, Page, Result, StreamId};
use tokio::time::{Instant, sleep_until};
use uuid::Uuid;

use super::{Client, Configuration, Genesis, Outcome, Reply, Request, Route, remaining};
use crate::stream::consensus::{MAX_PAGE, MAX_RECORD, MAX_RECORDS_PER_PAGE, network::Proof};

const HEDGE_DELAY: Duration = Duration::from_millis(25);
/// How long past its wait a long poll runs before the read hedges.
const LONG_POLL_MARGIN: Duration = Duration::from_millis(250);
const DISCOVERY_ATTEMPTS: usize = 8;
const FALLBACK_ATTEMPTS: usize = 8;

impl Client {
    pub async fn read(
        &self,
        stream: StreamId,
        from: Lsn,
        limit: usize,
        wait: Duration,
    ) -> Result<Page> {
        self.read_at_least(stream, from, limit, wait, Lsn(0)).await
    }

    /// Reads one applied page whose head covers the caller's minimum.
    /// Use `head` for a fresh quorum-confirmed position.
    pub async fn read_at_least(
        &self,
        stream: StreamId,
        from: Lsn,
        limit: usize,
        wait: Duration,
        minimum_head: Lsn,
    ) -> Result<Page> {
        let deadline = Instant::now() + self.deadline;
        let mut route = self.route(stream, deadline).await?;
        if route.preferred.is_none() {
            if let Some((keeper, proof)) = self.discover_placement(stream, &route, deadline).await {
                self.remember_placement(stream, keeper, &proof);
                route = self.routes.lock().get(&stream).cloned().unwrap_or(route);
            }
        }
        let genesis = route.genesis.clone().ok_or(JournalError::Unavailable)?;
        let wait = wait.min(Duration::from_secs(5));
        let request = Request::ReadAt {
            genesis: genesis.clone(),
            from,
            minimum_head,
            limit,
            wait_ms: wait.as_millis() as u32,
        };
        let attempt = wait.saturating_add(super::ATTEMPT);
        let call = |keeper| {
            let request = request.clone();
            async move {
                let result = self
                    .rpc
                    .call_application(keeper, request, remaining(deadline).min(attempt))
                    .await
                    .ok();
                (keeper, result)
            }
        };
        let mut view = Seen::default();
        let accept = |view: &mut Seen, keeper, reply| {
            let outcome = checked_page(reply?, &genesis, from, limit, minimum_head)?;
            if let Some(configuration) = outcome.configuration {
                self.remember_placement(
                    stream,
                    keeper,
                    &Proof {
                        genesis: genesis.clone(),
                        configuration,
                        joint: None,
                        stage: None,
                    },
                );
            }
            view.record(outcome.outcome, limit)
        };
        let mut tried = BTreeSet::new();
        let preferred = route.ordered_preferred(&self.local);
        if let Some(&first) = preferred.first() {
            tried.insert(first);
            let mut pending = FuturesUnordered::new();
            pending.push(call(first));
            let mut alternates = preferred[1..].iter().copied().peekable();
            let mut delay = hedge_delay(wait);
            let mut hedge_at = Instant::now() + delay;
            loop {
                let hedging = alternates.peek().is_some() && !remaining(deadline).is_zero();
                tokio::select! {
                    biased;
                    reply = pending.next() => {
                        let Some((keeper, reply)) = reply else { break };
                        let pages = view.pages;
                        if let Some(page) = accept(&mut view, keeper, reply) {
                            return Ok(page);
                        }
                        // A voter that waited out a long poll answered it.
                        if !wait.is_zero() && view.pages > pages {
                            return view.finish();
                        }
                        // A failed voter is hedged at once.
                        if pending.is_empty()
                            && hedging
                            && let Some(next) = alternates.next()
                        {
                            tried.insert(next);
                            pending.push(call(next));
                            hedge_at = Instant::now() + delay;
                        }
                    }
                    () = sleep_until(hedge_at.min(deadline)), if hedging => {
                        if let Some(next) = alternates.next() {
                            tried.insert(next);
                            pending.push(call(next));
                        }
                        delay = delay.saturating_mul(2);
                        hedge_at = Instant::now() + delay;
                    }
                }
            }
        }

        // A cache miss or unreachable old roster gets one trusted lookup.
        // The lookup contributes contacts, never a preferred configuration.
        let updated = if remaining(deadline).is_zero() {
            None
        } else {
            self.refresh(stream, deadline).await.ok()
        };
        let discoveries = updated
            .iter()
            .flat_map(|route| route.contacts.iter().copied());
        let fallback = preferred
            .into_iter()
            .chain(discoveries)
            .chain(route.contacts)
            .chain(self.rpc.keepers().keys().copied())
            .filter(|id| tried.insert(*id))
            .take(FALLBACK_ATTEMPTS)
            .collect::<Vec<_>>();
        let mut calls = futures::stream::iter(fallback.into_iter().map(call)).buffer_unordered(3);
        while let Some((keeper, reply)) = calls.next().await {
            if let Some(page) = accept(&mut view, keeper, reply) {
                return Ok(page);
            }
        }
        view.finish()
    }

    async fn discover_placement(
        &self,
        stream: StreamId,
        route: &Route,
        deadline: Instant,
    ) -> Option<(Uuid, Proof)> {
        let mut seen = BTreeSet::new();
        let mut pending = FuturesUnordered::new();
        let call = |id| async move {
            let reply = self
                .rpc
                .call_application(
                    id,
                    Request::PlacementProof(stream),
                    (remaining(deadline) / 3).min(Duration::from_millis(350)),
                )
                .await;
            (id, reply)
        };
        for peer in route
            .leader
            .into_iter()
            .chain(route.contacts.iter().copied())
            .filter(|id| seen.insert(*id))
            .take(DISCOVERY_ATTEMPTS)
        {
            pending.push(call(peer));
        }
        while let Some((keeper, reply)) = pending.next().await {
            match reply {
                Ok(Reply::Placement(proof))
                    if route
                        .genesis
                        .as_ref()
                        .is_none_or(|known| known == &proof.genesis)
                        && self.valid_proof(stream, &proof) =>
                {
                    return Some((keeper, proof));
                }
                Ok(Reply::Leader(Some(next)))
                    if seen.len() < DISCOVERY_ATTEMPTS
                        && self.rpc.keepers().contains_key(&next)
                        && seen.insert(next) =>
                {
                    pending.push(call(next));
                }
                _ => (),
            }
        }
        None
    }

    fn valid_proof(&self, stream: StreamId, proof: &Proof) -> bool {
        proof.genesis.stream == stream
            && proof
                .genesis
                .valid_with_retired(self.rpc.keepers(), &self.retired)
            && proof
                .configuration
                .voters
                .windows(2)
                .all(|pair| pair[0] < pair[1])
            && proof
                .configuration
                .voters
                .iter()
                .all(|id| self.rpc.keepers().contains_key(id) || self.retired.contains(id))
    }

    fn remember_placement(&self, stream: StreamId, keeper: Uuid, proof: &Proof) {
        if !self.valid_proof(stream, proof) {
            return;
        }
        let mut routes = self.routes.lock();
        let route = routes.entry(stream).or_insert_with(|| Route {
            genesis: Some(proof.genesis.clone()),
            contacts: Vec::new(),
            leader: None,
            preferred: None,
        });
        if route
            .genesis
            .as_ref()
            .is_some_and(|known| known != &proof.genesis)
        {
            return;
        }
        route.genesis = Some(proof.genesis.clone());
        let incoming = proof.configuration;
        if route
            .preferred
            .is_none_or(|(current, _)| incoming.revision > current.revision)
        {
            route.preferred = Some((
                incoming,
                if incoming.voters.contains(&keeper) {
                    keeper
                } else {
                    incoming.voters[0]
                },
            ));
        } else if let Some((current, last)) = &mut route.preferred
            && *current == incoming
            && incoming.voters.contains(&keeper)
        {
            *last = keeper;
        }
    }
}

/// How long a read waits for one voter before it also asks the next. A
/// short read hedges after 25 ms. A long poll is expected to wait, so it
/// hedges only once its wait and a margin have passed; a failed voter is
/// hedged at once either way. Each later hedge waits twice as long.
fn hedge_delay(wait: Duration) -> Duration {
    if wait.is_zero() {
        HEDGE_DELAY
    } else {
        wait.saturating_add(LONG_POLL_MARGIN)
    }
}

impl Route {
    /// The voters to read from, in order: a voter in the client's own failure
    /// domain, then the keeper that answered last, then the rest.
    fn ordered_preferred(&self, local: &BTreeSet<Uuid>) -> Vec<Uuid> {
        self.preferred
            .map_or_else(Vec::new, |(configuration, preferred)| {
                let mut voters = configuration.voters.to_vec();
                voters.sort_by_key(|id| (!local.contains(id), *id != preferred));
                voters
            })
    }
}

struct Checked {
    configuration: Option<Configuration>,
    outcome: Outcome,
}

fn checked_page(
    reply: Reply,
    expected: &Genesis,
    from: Lsn,
    limit: usize,
    minimum: Lsn,
) -> Option<Checked> {
    let Reply::ScopedPage {
        genesis,
        configuration,
        outcome,
    } = reply
    else {
        return None;
    };
    if &genesis != expected {
        return None;
    }
    if let Outcome::Page(page) = &outcome {
        if page.head < minimum
            || page.floor.0 == 0
            || from < page.floor
            || page
                .head
                .0
                .checked_add(1)
                .is_none_or(|after| page.floor.0 > after)
            || page.records.len() > limit.min(MAX_RECORDS_PER_PAGE)
            || page
                .records
                .iter()
                .map(|(_, payload)| payload.len())
                .sum::<usize>()
                > MAX_PAGE
            || page
                .records
                .iter()
                .enumerate()
                .any(|(offset, (at, payload))| {
                    from.0.checked_add(offset as u64) != Some(at.0)
                        || *at > page.head
                        || payload.len() > MAX_RECORD
                })
            // Each recovery entry names a record of the page, in order,
            // whose bytes are its canonical encoding.
            || page.recoveries.windows(2).any(|pair| pair[0].0 >= pair[1].0)
            || page.recoveries.iter().any(|(at, entry)| {
                at.0.checked_sub(from.0)
                    .and_then(|offset| page.records.get(offset as usize))
                    .is_none_or(|(_, bytes)| entry.at() != *at || *bytes != entry.encode())
            })
        {
            return None;
        }
    }
    Some(Checked {
        configuration,
        outcome,
    })
}

#[derive(Default)]
struct Seen {
    /// Valid pages received, empty or not.
    pages: usize,
    empty: Option<Page>,
    floor: Option<Lsn>,
    deleted: bool,
    corrupted: bool,
}

impl Seen {
    fn record(&mut self, outcome: Outcome, limit: usize) -> Option<Page> {
        if matches!(outcome, Outcome::Page(_)) {
            self.pages += 1;
        }
        match outcome {
            Outcome::Page(page) if !page.records.is_empty() || limit == 0 => return Some(page),
            Outcome::Page(page)
                if self
                    .empty
                    .as_ref()
                    .is_none_or(|prior| page.head > prior.head) =>
            {
                self.empty = Some(page);
            }
            Outcome::Refused(JournalError::Trimmed { floor }) => {
                self.floor = self.floor.max(Some(floor))
            }
            Outcome::Refused(JournalError::Deleted) => self.deleted = true,
            Outcome::Refused(JournalError::Corrupted) => self.corrupted = true,
            _ => (),
        }
        None
    }

    fn finish(self) -> Result<Page> {
        if self.deleted {
            return Err(JournalError::Deleted);
        }
        if let Some(floor) = self.floor {
            return Err(JournalError::Trimmed { floor });
        }
        if let Some(empty) = self.empty {
            return Ok(empty);
        }
        if self.corrupted {
            return Err(JournalError::Corrupted);
        }
        Err(JournalError::Unavailable)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stream::consensus::Voters;

    #[test]
    fn reads_try_a_voter_in_the_clients_domain_first() {
        let [a, b, c] = [1, 2, 3].map(Uuid::from_u128);
        let route = Route {
            genesis: None,
            preferred: Some((
                Configuration {
                    revision: 1,
                    voters: Voters::from([a, b, c]),
                },
                b,
            )),
            contacts: Vec::new(),
            leader: None,
        };
        assert_eq!(route.ordered_preferred(&BTreeSet::new())[0], b);
        assert_eq!(route.ordered_preferred(&BTreeSet::from([c])), vec![c, b, a]);
        assert_eq!(route.ordered_preferred(&BTreeSet::from([b])), vec![b, a, c]);
    }
    use bytes::Bytes;

    #[test]
    fn pages_are_bound_to_scope_minimum_and_request_bounds() {
        let genesis = Genesis {
            stream: StreamId(4),
            voters: Voters::from([1, 2, 3].map(Uuid::from_u128)),
            quota_bytes: 128,
            immutable: false,
            authenticated: false,
        };
        let page = |scope: Genesis, head| Reply::ScopedPage {
            genesis: scope,
            configuration: None,
            outcome: Outcome::Page(Page::new(
                Lsn(1),
                vec![(Lsn(1), Bytes::from_static(b"one"))],
                Lsn(head),
            )),
        };
        assert!(checked_page(page(genesis.clone(), 4), &genesis, Lsn(1), 1, Lsn(4)).is_some());
        assert!(checked_page(page(genesis.clone(), 3), &genesis, Lsn(1), 1, Lsn(4)).is_none());
        assert!(checked_page(page(genesis.clone(), 4), &genesis, Lsn(2), 1, Lsn(4)).is_none());
        let foreign = Genesis {
            quota_bytes: 129,
            ..genesis.clone()
        };
        assert!(checked_page(page(foreign, 4), &genesis, Lsn(1), 1, Lsn(4)).is_none());
    }
}
