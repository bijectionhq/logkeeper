//! Replica retirement and staging share the local opening gate.

use std::{fs, io, path::Path};

use journal_contract::{JournalError, StreamId};
use openraft::async_runtime::WatchReceiver;
use tokio::time::Instant;
use uuid::Uuid;

use super::{Engine, Group, Outcome, REQUEST_TIMEOUT, Reply, Request, failure, invalid};
use crate::stream::consensus::{
    Genesis, LogId, Stage,
    network::{Frame, Proof},
    ownership::{self, Change},
    storage::Record,
};

impl Engine {
    pub(super) async fn verified_proof(
        &self,
        authority: Uuid,
        genesis: &Genesis,
    ) -> io::Result<Proof> {
        if authority == self.id {
            return Err(invalid(
                "replica ownership requires independent placement evidence",
            ));
        }
        let Reply::Placement(proof) = self
            .rpc
            .call(
                authority,
                Frame::Client(Request::PlacementProof(genesis.stream)),
                REQUEST_TIMEOUT,
            )
            .await?
        else {
            return Err(invalid("current placement is unknown"));
        };
        if &proof.genesis != genesis
            || !self.placement.roster(&proof.configuration.voters)
            || proof
                .joint
                .is_some_and(|roster| !self.placement.roster(&roster))
        {
            return Err(invalid(
                "proof does not identify the checked stream placement",
            ));
        }
        Ok(proof)
    }

    async fn verified_stage(
        &self,
        authority: Uuid,
        genesis: &Genesis,
        stage: &Stage,
    ) -> io::Result<()> {
        if !self.placement.genesis(genesis)
            || !self.placement.stage(stage)
            || stage.stream != genesis.stream
            || !stage.old.contains(&authority)
            || stage.old.contains(&self.id)
            || !stage.target.contains(&self.id)
        {
            return Err(invalid("stage is outside the authenticated move"));
        }
        let proof = self.verified_proof(authority, genesis).await?;
        if proof.configuration.revision != stage.source
            || proof.configuration.voters != stage.old
            || proof.stage.as_ref() != Some(stage)
            || proof.joint.is_some()
        {
            return Err(invalid(
                "current source has no matching committed staging receipt",
            ));
        }
        Ok(())
    }

    pub(super) async fn stage_replica(
        &self,
        authority: Uuid,
        genesis: Genesis,
        stage: Stage,
    ) -> io::Result<Reply> {
        let stream = genesis.stream;
        let opening = self.opening(stream).await?;
        let _guard = opening.lock().await;
        self.verified_stage(authority, &genesis, &stage).await?;
        match self.disk.genesis(stream) {
            Some(local) if local != genesis => return Err(invalid("staging would change genesis")),
            Some(_) => (),
            None => self.disk.maintenance(Record::Register(genesis)).await?,
        }
        let current = self.disk.ownership(stream).ok_or_else(ownership::stale)?;
        if !current.contains_stage(&stage) {
            self.remember_pin(stream).await;
            self.disk
                .maintenance(Record::Ownership(stream, Change::Stage(stage)))
                .await?;
            self.close_copy(stream).await;
        }
        let generation = self
            .disk
            .ownership(stream)
            .and_then(|book| book.generation())
            .ok_or_else(ownership::stale)?;
        Ok(Reply::Generation(generation))
    }

    /// Stages an installed empty copy for an operator recovery. The
    /// survivor's keeper, authenticated as `authority`, asks while it is
    /// stopped for the recovery; no committed state can certify the move,
    /// so the operator's acknowledgement on the survivor is the authority.
    /// This keeper refuses when its own open replica votes in its
    /// configuration, which means the survivor's view is stale.
    pub(super) async fn stage_recovered(
        &self,
        authority: Uuid,
        genesis: Genesis,
        stage: Stage,
    ) -> io::Result<Reply> {
        let stream = genesis.stream;
        if !self.placement.genesis(&genesis)
            || !self.placement.stage(&stage)
            || !stage.recovery()
            || stage.stream != stream
            || !stage.old.contains(&authority)
            || !stage.target.contains(&authority)
            || stage.old.contains(&self.id)
            || !stage.target.contains(&self.id)
        {
            return Err(invalid("stage is outside the authenticated recovery"));
        }
        let opening = self.opening(stream).await?;
        let _guard = opening.lock().await;
        match self.disk.genesis(stream) {
            Some(local) if local != genesis => return Err(invalid("staging would change genesis")),
            Some(_) => (),
            None => self.disk.maintenance(Record::Register(genesis)).await?,
        }
        let current = self.disk.ownership(stream).ok_or_else(ownership::stale)?;
        if !(current.contains_stage(&stage) && current.installed()) {
            if let Some(group) = self.groups.lock().await.get(&stream).cloned() {
                let metrics = group.raft.metrics().borrow_watched().clone();
                if metrics
                    .membership_config
                    .membership()
                    .voter_ids()
                    .any(|id| id == self.id.as_u128())
                {
                    return Err(invalid("keeper holds a voting replica of the stream"));
                }
            }
            self.remember_pin(stream).await;
            self.disk
                .maintenance(Record::Ownership(stream, Change::Recover(stage)))
                .await?;
            self.close_copy(stream).await;
        }
        let generation = self
            .disk
            .ownership(stream)
            .and_then(|book| book.generation())
            .ok_or_else(ownership::stale)?;
        Ok(Reply::Generation(generation))
    }

    pub(super) async fn install_replica(
        &self,
        authority: Uuid,
        genesis: Genesis,
        stage: Stage,
        generation: u64,
        through: LogId,
    ) -> io::Result<Reply> {
        let scope = genesis.stream;
        let opening = self.opening(scope).await?;
        let _guard = opening.lock().await;
        self.verified_stage(authority, &genesis, &stage).await?;
        if self.disk.genesis(scope).as_ref() != Some(&genesis) {
            return Err(ownership::stale());
        }
        let group = self
            .groups
            .lock()
            .await
            .get(&scope)
            .cloned()
            .ok_or_else(ownership::stale)?;
        group.require_healthy()?;
        self.disk
            .maintenance(Record::Ownership(
                scope,
                Change::Install {
                    stage,
                    generation,
                    through,
                },
            ))
            .await?;
        Ok(Reply::Decision(Outcome::Unit))
    }

    pub(super) async fn retire_copy(
        &self,
        scope: StreamId,
        authority: Uuid,
        revision: u64,
        generation: u64,
    ) -> io::Result<Reply> {
        let opening = self.opening(scope).await?;
        let _guard = opening.lock().await;
        let genesis = self
            .disk
            .genesis(scope)
            .ok_or_else(|| invalid("replica placement is unknown"))?;
        let current = self.disk.ownership(scope).ok_or_else(ownership::stale)?;
        if current.was_retired(revision, generation) {
            return Ok(Reply::Decision(Outcome::Unit));
        }
        if current.generation() != Some(generation) {
            return Err(ownership::stale());
        }
        let proof = self.verified_proof(authority, &genesis).await?;
        if proof.configuration.revision != revision
            || proof.configuration.voters.contains(&self.id)
            || proof.joint.is_some_and(|target| target.contains(&self.id))
        {
            return Err(invalid(
                "current placement does not certify replica exclusion",
            ));
        }
        self.remember_pin(scope).await;
        self.disk
            .maintenance(Record::Ownership(
                scope,
                Change::Detach {
                    revision,
                    generation,
                },
            ))
            .await?;
        self.close_copy(scope).await;
        Ok(Reply::Decision(Outcome::Unit))
    }

    async fn remember_pin(&self, scope: StreamId) {
        if let Some(group) = self.groups.lock().await.get(&scope) {
            self.detached_pins
                .lock()
                .insert((scope, group.state.generation()), group.state.lifetime());
        }
    }

    /// Closes a parked or deleted stream's group while keeping its replica.
    /// The closed state machine stays referenced, because its snapshot and
    /// applied records are the only references to objects and segments the
    /// reaper would otherwise delete; the reopened group takes them over.
    pub(super) async fn close_retaining(&self, scope: StreamId) {
        if let Some(group) = self.groups.lock().await.get(&scope) {
            self.closed_states.lock().insert(scope, group.state.clone());
        }
        self.close_copy(scope).await;
    }

    pub(super) async fn close_copy(&self, scope: StreamId) {
        if let Some(group) = self.groups.lock().await.remove(&scope) {
            group.state.suspend();
            group.stop.cancel();
            tokio::spawn(async move {
                let _ = group.raft.shutdown().await;
                group.state.shutdown().await;
            });
        }
    }

    pub(super) async fn reclaim_detached(&self, cursor: &mut Option<StreamId>) -> io::Result<()> {
        let batch = self.disk.detached(*cursor);
        *cursor = batch.last().map(|(scope, _)| *scope);
        for (scope, generation) in batch {
            let Some(generation) = generation else {
                continue;
            };
            if self
                .detached_pins
                .lock()
                .get(&(scope, generation))
                .is_some_and(|pin| pin.strong_count() != 0)
            {
                continue;
            }
            let path = ownership::directory(&self.disk.path, scope, generation);
            if tokio::task::spawn_blocking(move || unlink_copy(&path)).await?? {
                self.disk
                    .maintenance(Record::Ownership(scope, Change::Release(generation)))
                    .await?;
                self.detached_pins.lock().remove(&(scope, generation));
            }
            // Schedule directory cleanup in bounded batches even with many
            // concurrent moves. The detached record survives a crash here.
            break;
        }
        Ok(())
    }
}

impl Group {
    pub(super) async fn proof(&self) -> Reply {
        if let Err(reply) = self.barrier(Instant::now() + REQUEST_TIMEOUT).await {
            return reply;
        }
        match self.state.placement_proof() {
            Ok(proof) => Reply::Placement(proof),
            Err(error) => failure(match error {
                JournalError::Deleted => JournalError::Unavailable,
                error => error,
            }),
        }
    }
}

fn unlink_copy(path: &Path) -> io::Result<bool> {
    let sync_parent = || crate::stream::keeper::durability::sync_directory(path.parent().unwrap());
    let contents = match fs::read_dir(path) {
        Ok(contents) => contents,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            sync_parent()?;
            return Ok(true);
        }
        Err(error) => return Err(error),
    };
    for entry in contents.take(16) {
        let entry = entry?;
        match fs::remove_file(entry.path()) {
            Ok(()) => (),
            Err(error) if error.kind() == io::ErrorKind::NotFound => (),
            Err(error) => return Err(error),
        }
    }
    match fs::remove_dir(path) {
        Ok(()) => (),
        Err(error) if error.kind() == io::ErrorKind::NotFound => (),
        Err(error) if error.kind() == io::ErrorKind::DirectoryNotEmpty => return Ok(false),
        Err(error) => return Err(error),
    }
    sync_parent()?;
    Ok(true)
}
