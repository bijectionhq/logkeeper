use super::*;

#[derive(Clone)]
pub(super) struct CachedHead {
    configuration: Configuration,
    /// The catalog history length when the head was certified; a catalog
    /// roster change may retire its signers.
    catalog_revisions: usize,
    signed: SignedHead,
}

impl Authentication {
    pub(super) fn remember_head(&self, stream: StreamId, head: CachedHead) {
        let mut heads = self.heads.lock();
        if heads
            .get(&stream)
            .is_none_or(|prior| prior.signed.head.size <= head.signed.head.size)
        {
            heads.insert(stream, head);
        }
    }

    /// The cached head of `stream` at this prefix, while its roster is the
    /// one the last observed catalog history holds for the stream.
    pub(super) fn current_head(
        &self,
        stream: StreamId,
        configuration: Configuration,
        size: u64,
        root: Hash,
    ) -> Option<SignedHead> {
        let cached = self.heads.lock().get(&stream).cloned()?;
        let head = cached.signed.head;
        let current = self.catalog_revisions() == Some(cached.catalog_revisions);
        (current && cached.configuration == configuration && head.size == size && head.root == root)
            .then_some(cached.signed)
    }

    pub(super) fn catalog_revisions(&self) -> Option<usize> {
        self.history.lock().as_ref().map(|history| history.transitions.len())
    }

    /// Whether a leader's head timestamp agrees with this keeper's clock:
    /// both clocks lie within the configured error of true time, and the
    /// request reached this voter within its timeout.
    pub(super) fn timely(&self, head: Head) -> bool {
        let error = i64::from(self.maximum_clock_error_micros);
        let transit = REQUEST_TIMEOUT.as_micros() as i64;
        match (self.time_lower(), self.time_upper()) {
            (Some(lower), Some(upper)) => {
                lower.saturating_sub(error + transit) <= head.timestamp_micros
                    && head.timestamp_micros <= upper.saturating_add(2 * error)
            }
            _ => false,
        }
    }
}

impl Engine {
    pub(in crate::stream::consensus::keeper) async fn roster_keys(
        &self,
        voters: Voters,
        previous: Option<&VoterKeys>,
    ) -> journal_contract::Result<VoterKeys> {
        let mut keys = BTreeMap::new();
        let mut calls = FuturesUnordered::from_iter(voters.into_iter().map(|keeper| async move {
            let key = if keeper == self.id {
                self.authentication
                    .as_ref()
                    .map(|authentication| authentication.public_key())
            } else {
                self.rpc
                    .call_application(
                        keeper,
                        Request::AuthenticationPeer(AuthenticationPeerRequest::Key),
                        REQUEST_TIMEOUT,
                    )
                    .await
                    .ok()
                    .and_then(|reply| authentication_value::<[u8; 32]>(reply).ok())
            };
            (keeper, key)
        }));
        while let Some((keeper, key)) = calls.next().await {
            let key = key
                .or_else(|| previous.and_then(|roster| roster.key(keeper).copied()))
                .ok_or(JournalError::Unavailable)?;
            keys.insert(keeper, key);
        }
        Ok(VoterKeys::Stable(keys))
    }

    pub(super) async fn head_share(
        &self,
        authentication: &Authentication,
        head: Head,
        voters: Voters,
    ) -> io::Result<Reply> {
        let Some(group) = self.groups.lock().await.get(&head.stream).cloned() else {
            return Ok(failure(JournalError::Unavailable));
        };
        let Ok((_, configuration, _, membership)) = group.state.placement() else {
            return Ok(failure(JournalError::Unavailable));
        };
        if !group.genesis.authenticated
            || !self.holds_authority(&group)
            || !group.state.healthy()
            || head.catalog != self.catalog_id
            || !voters.contains(&self.id)
            || voters != configuration.voters
            || membership.membership().get_joint_config().len() != 1
        {
            return Ok(failure(JournalError::Unavailable));
        }
        let applied = group
            .state
            .with_authenticated_tree(|tree| tree.root_at(head.size).ok());
        if !head.valid() || applied.flatten() != Some(head.root) || !authentication.timely(head) {
            return Ok(failure(JournalError::Unavailable));
        }
        let request = Request::AuthenticationPeer(AuthenticationPeerRequest::HeadAuthority {
            stream: head.stream,
            digest: head.authority_sha256,
        });
        let authority: Authority = match authentication_value(self.catalog_request(request).await?)
        {
            Ok(authority) => authority,
            Err(error) => return Ok(failure(error)),
        };
        if authority.catalog != head.catalog
            || authority.digest != head.authority_sha256
            || authority
                .voters
                .keepers()
                .into_iter()
                .ne(voters.into_iter())
            || authority.voters.key(self.id).copied() != Some(authentication.public_key())
        {
            return Ok(failure(JournalError::Unavailable));
        }
        Ok(authentication_reply(
            &authentication.sign(self.id, &head.statement()),
        ))
    }

    /// A quorum-signed head over the applied prefix of `size` leaves with
    /// `root`. A cached head serves until its roster is replaced, so an idle
    /// stream costs no catalog requests.
    pub(super) async fn certify_head(&self, group: &Group, size: u64, root: Hash) -> Result<SignedHead, Reply> {
        let failed = || failure(JournalError::Unavailable);
        let authentication = self.authentication.as_ref().ok_or_else(failed)?;
        let stream = group.genesis.stream;
        let (_, configuration, _, membership) = group.state.placement().map_err(failure)?;
        if membership.membership().get_joint_config().len() != 1 {
            return Err(failed());
        }
        if let Some(cached) = authentication.current_head(stream, configuration, size, root) {
            return Ok(cached);
        }
        let request = Request::AuthenticationPeer(AuthenticationPeerRequest::Authority {
            stream: group.genesis.stream,
            configuration,
        });
        let reply = self.catalog_request(request).await.map_err(|_| failed())?;
        let authority: Authority = authentication_value(reply).map_err(failure)?;
        let head = Head {
            catalog: authority.catalog,
            stream: group.genesis.stream,
            size,
            root,
            timestamp_micros: authentication.time_upper().ok_or_else(failed)?,
            authority_sha256: authority.digest,
        };
        let statement = head.statement();
        let request = AuthenticationPeerRequest::HeadShare {
            head: head.clone(),
            voters: configuration.voters,
        };
        let mut shares =
            FuturesUnordered::from_iter(configuration.voters.into_iter().map(|keeper| {
                let request = request.clone();
                async move {
                    let reply = if keeper == self.id {
                        self.head_share(authentication, head, configuration.voters)
                            .await
                    } else {
                        self.rpc
                            .call_application(
                                keeper,
                                Request::AuthenticationPeer(request),
                                REQUEST_TIMEOUT,
                            )
                            .await
                    };
                    reply
                        .ok()
                        .and_then(|reply| authentication_value::<QuorumSignature>(reply).ok())
                        .filter(|signature| signature.keeper == keeper)
                }
            }));
        let mut signatures = Vec::new();
        while let Some(signature) = shares.next().await {
            if let Some(signature) = signature {
                signatures.push(signature);
                signatures.sort_by_key(|signature| signature.keeper);
                if authority.voters.verify(&statement, &signatures).is_ok() {
                    let signed = SignedHead { head, signatures };
                    authentication.remember_head(
                        stream,
                        CachedHead {
                            configuration,
                            catalog_revisions: authentication.catalog_revisions().unwrap_or(usize::MAX),
                            signed: signed.clone(),
                        },
                    );
                    return Ok(signed);
                }
            }
        }
        Err(failed())
    }

    pub(in crate::stream::consensus::keeper) async fn tend_authenticated(&self) -> io::Result<()> {
        let Some(authentication) = &self.authentication else {
            return Ok(());
        };
        let mut schedule = tokio::time::interval(std::time::Duration::from_secs(1));
        schedule.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        loop {
            tokio::select! {
                _ = self.stop.cancelled() => return Ok(()),
                _ = schedule.tick() => (),
            }
            let _ = self.extend_history(authentication).await;
            let groups = self
                .groups
                .lock()
                .await
                .values()
                .filter(|group| group.genesis.authenticated)
                .cloned()
                .collect::<Vec<_>>();
            futures::stream::iter(groups)
                .for_each_concurrent(4, |group| async move {
                    let stream = group.genesis.stream;
                    let retained = group.state.timed_view(0);
                    let cleanup = match &retained {
                        Ok(view) => view
                            .writer
                            .as_ref()
                            .map(|(fence, _)| (fence.epoch.0, view.head)),
                        Err(JournalError::Deleted) => Some((u64::MAX, Lsn(u64::MAX))),
                        Err(_) => None,
                    };
                    if let Some((epoch, at)) = cleanup {
                        let authentication = Arc::clone(authentication);
                        let _ = tokio::task::spawn_blocking(move || {
                            authentication.prune_stages(stream, epoch, at)
                        })
                        .await;
                    }
                    if !self.holds_authority(&group) || !group.state.healthy() || retained.is_err()
                    {
                        return;
                    }
                    use openraft::async_runtime::WatchReceiver;
                    if group.raft.metrics().borrow_watched().current_leader
                        != Some(self.id.as_u128())
                    {
                        return;
                    }
                    if let Some((size, root)) = group
                        .state
                        .with_authenticated_tree(|tree| (tree.size(), tree.root()))
                    {
                        let _ = self.certify_head(&group, size, root).await;
                    }
                })
                .await;
        }
    }

    pub(in crate::stream::consensus::keeper) async fn authenticated_read(
        &self,
        group: &Group,
        request: AuthenticationRequest,
    ) -> Reply {
        if !group.genesis.authenticated {
            return failure(JournalError::Unsupported);
        }
        if let Err(reply) = group.barrier(Instant::now() + REQUEST_TIMEOUT).await {
            return reply;
        }
        enum Read {
            Head(u64, Hash),
            Inclusion(Leaf, Vec<Hash>, u64, Hash),
            Reply(Reply),
        }
        let read = group.state.with_authenticated_tree(|tree| match request {
            AuthenticationRequest::Head { size } => {
                let size = size.unwrap_or_else(|| tree.size());
                match tree.root_at(size) {
                    Ok(root) => Read::Head(size, root),
                    Err(_) => Read::Reply(failure(JournalError::NotFound)),
                }
            }
            AuthenticationRequest::Inclusion { at, size } => {
                let size = size.unwrap_or_else(|| tree.size());
                match (tree.leaf(at), tree.inclusion(at, size), tree.root_at(size)) {
                    (Some(leaf), Ok(path), Ok(root)) => Read::Inclusion(*leaf, path, size, root),
                    _ => Read::Reply(failure(JournalError::NotFound)),
                }
            }
            request => Read::Reply(Self::tree_read(tree, request)),
        });
        match read {
            None => failure(JournalError::Unavailable),
            Some(Read::Reply(reply)) => reply,
            Some(Read::Head(size, root)) => match self.certify_head(group, size, root).await {
                Ok(head) => authentication_reply(&head),
                Err(reply) => reply,
            },
            Some(Read::Inclusion(leaf, path, size, root)) => {
                match self.certify_head(group, size, root).await {
                    Ok(signed_head) => authentication_reply(&Included {
                        leaf,
                        path,
                        signed_head,
                    }),
                    Err(reply) => reply,
                }
            }
        }
    }

    pub(super) fn tree_read(tree: &Tree, request: AuthenticationRequest) -> Reply {
        match request {
            AuthenticationRequest::Consistency { earlier, later } => {
                match tree.consistency(earlier, later) {
                    Ok(path) => authentication_reply(&path),
                    Err(_) => failure(JournalError::NotFound),
                }
            }
            AuthenticationRequest::ArchivePage { from, through } => {
                let Ok(start) = usize::try_from(from.0.saturating_sub(1)) else {
                    return failure(JournalError::NotFound);
                };
                let Ok(through) = usize::try_from(through) else {
                    return failure(JournalError::NotFound);
                };
                if from.0 == 0 || start > through || through as u64 > tree.size() {
                    return failure(JournalError::NotFound);
                }
                let leaves = tree.leaf_range(start as u64, through.min(start.saturating_add(ARCHIVE_PAGE)) as u64);
                authentication_reply(&leaves)
            }
            _ => failure(JournalError::Unsupported),
        }
    }

    /// Reads the catalog history's new transitions into this keeper's copy.
    pub(super) async fn extend_history(&self, authentication: &Authentication) -> journal_contract::Result<()> {
        let (genesis, mut latest, from) = match &*authentication.history.lock() {
            Some(history) => (
                Some(history.genesis.clone()),
                Some(history.latest().clone()),
                history.transitions.len(),
            ),
            None => (None, None, 0),
        };
        let mut transitions = Vec::new();
        loop {
            let request = Request::Authentication {
                stream: CATALOG_STREAM,
                request: AuthenticationRequest::History {
                    from: from + transitions.len(),
                },
            };
            let page: HistoryPage = authentication_value(
                self.catalog_request(request)
                    .await
                    .map_err(|_| JournalError::Unavailable)?,
            )?;
            if genesis.as_ref().is_some_and(|genesis| *genesis != page.genesis) {
                return Err(JournalError::Corrupted);
            }
            let mut previous = latest.take().unwrap_or_else(|| page.genesis.clone());
            for transition in &page.transitions {
                transition
                    .verify(&previous)
                    .map_err(|_| JournalError::Corrupted)?;
                previous = transition.authority.clone();
            }
            latest = Some(previous);
            let empty = page.transitions.is_empty();
            transitions.extend(page.transitions);
            if !page.more || empty {
                let mut known = authentication.history.lock();
                match &mut *known {
                    Some(history) if history.transitions.len() == from => {
                        history.transitions.extend(transitions)
                    }
                    Some(_) => (),
                    None => {
                        *known = Some(CatalogHistory {
                            genesis: page.genesis,
                            transitions,
                        })
                    }
                }
                return Ok(());
            }
        }
    }

    pub(super) async fn fetch_stream_authorities(
        &self,
        stream: StreamId,
    ) -> journal_contract::Result<Vec<SignedStreamAuthority>> {
        let request = Request::Authentication {
            stream: CATALOG_STREAM,
            request: AuthenticationRequest::StreamAuthority { stream },
        };
        authentication_value(
            self.catalog_request(request)
                .await
                .map_err(|_| JournalError::Unavailable)?,
        )
    }

    pub(super) async fn authentication_history(&self) -> journal_contract::Result<CatalogHistory> {
        let mut from = 0;
        let mut transitions = Vec::new();
        loop {
            let request = Request::Authentication {
                stream: CATALOG_STREAM,
                request: AuthenticationRequest::History { from },
            };
            let page: HistoryPage = authentication_value(
                self.catalog_request(request)
                    .await
                    .map_err(|_| JournalError::Unavailable)?,
            )?;
            transitions.extend(page.transitions);
            if !page.more {
                return Ok(CatalogHistory {
                    genesis: page.genesis,
                    transitions,
                });
            }
            if from == transitions.len() {
                return Err(JournalError::Corrupted);
            }
            from = transitions.len();
        }
    }
}
