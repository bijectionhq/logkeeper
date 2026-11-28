use super::*;

pub(super) const STAGE_RETAIN_MICROS: i64 = 30_000_000;

pub(super) const STAGE_STRIPES: usize = 64;

pub(super) const STAGE_LIMIT: usize = crate::stream::consensus::keeper::MAX_PENDING_WRITES * 2;

pub(super) const STAGE_BYTES_LIMIT: u64 = STAGE_LIMIT as u64 * (crate::stream::consensus::MAX_RECORD as u64 + 65_536);

pub(super) const STAGE_MAGIC: &[u8; 8] = b"LKASTG01";

pub(super) const STAMP_BYTES: usize = STAGE_MAGIC.len() + 16;

#[derive(Clone, Copy, Serialize, Deserialize)]
pub(super) struct DurabilityStamp {
    upper_micros: i64,
    retained_until_micros: i64,
}

impl DurabilityStamp {
    pub(super) fn valid(self) -> bool {
        self.upper_micros > 0
            && self.upper_micros.checked_add(STAGE_RETAIN_MICROS)
                == Some(self.retained_until_micros)
    }

    pub(super) fn read(file: &mut File) -> io::Result<Self> {
        file.seek(SeekFrom::End(-(STAMP_BYTES as i64)))?;
        let mut bytes = [0; STAMP_BYTES];
        file.read_exact(&mut bytes)?;
        let stamp = Self {
            upper_micros: i64::from_be_bytes(bytes[8..16].try_into().unwrap()),
            retained_until_micros: i64::from_be_bytes(bytes[16..24].try_into().unwrap()),
        };
        if &bytes[..8] != STAGE_MAGIC || !stamp.valid() {
            return Err(invalid("invalid authenticated durability stage"));
        }
        Ok(stamp)
    }

    pub(super) fn write(self, file: &mut File) -> io::Result<()> {
        file.write_all(STAGE_MAGIC)?;
        file.write_all(&self.upper_micros.to_be_bytes())?;
        file.write_all(&self.retained_until_micros.to_be_bytes())
    }

    pub(super) fn quorum_bound(stamps: &[Self], quorum: usize) -> Option<i64> {
        stamps
            .iter()
            .map(|stamp| stamp.upper_micros)
            .filter(|&bound| {
                stamps
                    .iter()
                    .filter(|stamp| {
                        stamp.upper_micros <= bound && bound < stamp.retained_until_micros
                    })
                    .count()
                    >= quorum
            })
            .min()
    }
}

pub(super) fn ordinary_operation(
    command: &Command,
) -> Option<(&crate::stream::consensus::Fence, &str, Lsn, Lsn)> {
    match command {
        Command::Append {
            fence, owner, at, ..
        } => Some((fence, owner, *at, *at)),
        Command::AppendBatch {
            fence,
            owner,
            at,
            payloads,
        } if crate::stream::consensus::state::valid_batch(payloads) => {
            let last = at.0.checked_add((payloads.len() - 1) as u64)?;
            Some((fence, owner, *at, Lsn(last)))
        }
        Command::InstallCheckpoint {
            fence,
            owner,
            checkpoint,
        } => {
            let at = checkpoint.checkpoint_lsn;
            Some((fence, owner, at, at))
        }
        _ => None,
    }
}

impl Authentication {
    pub(super) fn stage_lock(&self, stream: StreamId) -> parking_lot::MutexGuard<'_, ()> {
        self.stage_locks[(stream.0 as usize) % STAGE_STRIPES].lock()
    }

    pub(super) fn stage_directory(&self, stream: StreamId) -> PathBuf {
        self.stages.join(format!("{:032x}", stream.0))
    }

    pub(super) fn stage(
        &self,
        stream: StreamId,
        epoch: u64,
        through: Lsn,
        applied: Lsn,
        operation: &Bytes,
    ) -> io::Result<DurabilityStamp> {
        let _stage = self.stage_lock(stream);
        let directory = self.stage_directory(stream);
        fs::create_dir_all(&directory)?;
        sync_directory(&self.stages)?;
        let (count, bytes) = self.remove_stages(&directory, epoch, applied)?;
        let digest = Sha256::digest(operation);
        let target = directory.join(format!("{epoch:016x}-{:016x}-{digest:x}.stage", through.0));
        match File::open(&target) {
            Ok(mut staged) => {
                let stamp = DurabilityStamp::read(&mut staged)?;
                if staged.metadata()?.len() != (operation.len() + STAMP_BYTES) as u64 {
                    return Err(invalid("authenticated durability stage length differs"));
                }
                staged.rewind()?;
                let mut retained = Vec::with_capacity(operation.len());
                staged
                    .take(operation.len() as u64)
                    .read_to_end(&mut retained)?;
                if retained != *operation {
                    return Err(invalid("authenticated durability stage bytes differ"));
                }
                return Ok(stamp);
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => (),
            Err(error) => return Err(error),
        }
        if count >= STAGE_LIMIT
            || bytes.saturating_add((operation.len() + STAMP_BYTES) as u64) > STAGE_BYTES_LIMIT
        {
            return Err(io::Error::other("authenticated durability staging full"));
        }
        let temporary = directory.join(format!(".{}.tmp", Uuid::new_v4()));
        let result = (|| {
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&temporary)?;
            file.write_all(operation)?;
            sync_file(&file)?;
            let upper_micros = self
                .time_upper()
                .ok_or_else(|| invalid("authenticated log clock is unavailable"))?;
            let retained_until_micros = upper_micros
                .checked_add(STAGE_RETAIN_MICROS)
                .ok_or_else(|| invalid("authenticated durability stage expiry overflowed"))?;
            let stamp = DurabilityStamp {
                upper_micros,
                retained_until_micros,
            };
            stamp.write(&mut file)?;
            sync_file(&file)?;
            fs::rename(&temporary, target)?;
            sync_directory(&directory)?;
            Ok(stamp)
        })();
        let _ = fs::remove_file(temporary);
        result
    }

    pub(super) fn remove_stages(
        &self,
        directory: &Path,
        epoch: u64,
        applied: Lsn,
    ) -> io::Result<(usize, u64)> {
        let entries = match fs::read_dir(directory) {
            Ok(entries) => entries,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok((0, 0)),
            Err(error) => return Err(error),
        };
        let mut count = 0usize;
        let mut bytes = 0u64;
        let lower = self.time_lower();
        for entry in entries {
            let entry = entry?;
            let name = entry.file_name();
            let name = name
                .to_str()
                .ok_or_else(|| invalid("invalid authenticated stage filename"))?;
            let remove = if name.starts_with('.') && name.ends_with(".tmp") {
                true
            } else {
                let mut parts = name.split('-');
                let epoch_at = || invalid("invalid authenticated durability stage coordinate");
                let saved_epoch = u64::from_str_radix(parts.next().ok_or_else(epoch_at)?, 16)
                    .map_err(|_| epoch_at())?;
                let through = u64::from_str_radix(parts.next().ok_or_else(epoch_at)?, 16)
                    .map_err(|_| epoch_at())?;
                if saved_epoch < epoch || through <= applied.0 {
                    true
                } else {
                    let mut file = File::open(entry.path())?;
                    let stamp = DurabilityStamp::read(&mut file)?;
                    if lower.is_some_and(|lower| lower >= stamp.retained_until_micros) {
                        true
                    } else {
                        count += 1;
                        bytes = bytes.saturating_add(file.metadata()?.len());
                        false
                    }
                }
            };
            if remove {
                fs::remove_file(entry.path())?;
            }
        }
        Ok((count, bytes))
    }

    pub(super) fn prune_stages(&self, stream: StreamId, epoch: u64, at: Lsn) -> io::Result<()> {
        let _stage = self.stage_lock(stream);
        self.remove_stages(&self.stage_directory(stream), epoch, at)
            .map(|_| ())
    }
}

impl Engine {
    pub(in crate::stream::consensus::keeper) async fn write_with_durability(&self, group: &Group, command: Command) -> Reply {
        if !group.genesis.authenticated {
            return group.write(command).await;
        }
        let Some((_, _, _, through)) = ordinary_operation(&command) else {
            return failure(JournalError::Unsupported);
        };
        let state = match group.state.timed_view(0) {
            Ok(state) if !state.changing => state,
            Ok(_) => return failure(JournalError::Unavailable),
            Err(error) => return failure(error),
        };
        if through <= state.head {
            return group.write(command).await;
        }
        let leadership = group.raft.metrics();
        use openraft::async_runtime::WatchReceiver;
        let leader = leadership.borrow_watched().current_leader;
        if leader != Some(self.id.as_u128()) {
            return crate::stream::consensus::keeper::leader_reply(leader);
        }
        let Ok(bytes) = encode(&command) else {
            return failure(JournalError::Unavailable);
        };
        let stream = group.genesis.stream;
        let configuration = state.configuration;
        let operation = Bytes::from(bytes);
        let mut stages =
            FuturesUnordered::from_iter(configuration.voters.into_iter().map(|keeper| {
                let operation = operation.clone();
                async move {
                    let reply = if keeper == self.id {
                        self.stage_durability(stream, configuration, operation)
                            .await
                    } else {
                        let request = AuthenticationPeerRequest::StageDurability {
                            stream,
                            configuration,
                            operation,
                        };
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
                        .and_then(|reply| authentication_value::<DurabilityStamp>(reply).ok())
                }
            }));
        let mut stamps = Vec::new();
        while let Some(sample) = stages.next().await {
            if let Some(sample) = sample.filter(|sample| sample.valid()) {
                stamps.push(sample);
                if let Some(bound) =
                    DurabilityStamp::quorum_bound(&stamps, configuration.voters.quorum())
                {
                    return group
                        .write(command.with_quorum_durability(bound, configuration.revision))
                        .await;
                }
            }
        }
        failure(JournalError::Unavailable)
    }

    pub(super) async fn stage_durability(
        &self,
        stream: StreamId,
        configuration: Configuration,
        operation: Bytes,
    ) -> io::Result<Reply> {
        let Some(authentication) = &self.authentication else {
            return Ok(failure(JournalError::Unsupported));
        };
        let Some(group) = self.groups.lock().await.get(&stream).cloned() else {
            return Ok(failure(JournalError::Unavailable));
        };
        if !group.genesis.authenticated || !self.holds_authority(&group) || !group.state.healthy() {
            return Ok(failure(JournalError::Unavailable));
        }
        let command: Command = decode(&operation)?;
        let Some((fence, owner, _, through)) = ordinary_operation(&command) else {
            return Ok(failure(JournalError::Unsupported));
        };
        let state = match group.state.timed_view(0) {
            Ok(state) => state,
            Err(error) => return Ok(failure(error)),
        };
        let max_ahead =
            crate::stream::consensus::keeper::MAX_PENDING_WRITES as u64 * crate::stream::consensus::state::MAX_BATCH_RECORDS as u64;
        if state.changing
            || configuration != state.configuration
            || !configuration.voters.contains(&self.id)
            || through <= state.head
            || through.0 > state.head.0.saturating_add(max_ahead)
        {
            return Ok(failure(JournalError::Unavailable));
        }
        if state
            .writer
            .as_ref()
            .is_none_or(|(current, principal)| current != fence || principal != owner)
        {
            return Ok(failure(JournalError::Fenced {
                current: state
                    .writer
                    .map_or(journal_contract::Epoch(0), |(current, _)| current.epoch),
            }));
        }
        let epoch = fence.epoch.0;
        let reservation = match self
            .disk
            .space
            .reserve((operation.len() + STAMP_BYTES) as u64)
        {
            Ok(reservation) => reservation,
            Err(_) => return Ok(failure(JournalError::Unavailable)),
        };
        let authentication = Arc::clone(authentication);
        let result = tokio::task::spawn_blocking(move || {
            let _reservation = reservation;
            authentication.stage(stream, epoch, through, state.head, &operation)
        })
        .await;
        Ok(match result {
            Ok(Ok(upper)) => authentication_reply(&upper),
            _ => failure(JournalError::Unavailable),
        })
    }
}
