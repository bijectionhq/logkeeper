//! Background installation of idle streams. An idle stream still needs the same
//! two surviving promises and history selection as a writer taking over.
use bytes::Bytes;

use crate::stream::{codec::MAX_FRAME_BYTES, wire::*};

/// The caller nominates an idle stream and reserves an epoch for this sweep.
#[derive(Clone, Copy, Debug)]
pub struct Sweep {
    pub stream: StreamId,
    pub ensemble: [KeeperId; 3],
    pub survivors: [KeeperId; 2],
    pub learner: KeeperId,
    pub epoch: Epoch,
}

#[derive(Debug, thiserror::Error)]
pub enum SweepError {
    #[error("keeper {keeper:?} was unreachable: {error:?}")]
    Transport {
        keeper: KeeperId,
        error: TransportError,
    },
    #[error("keeper {keeper:?} returned {reply:?}")]
    Reply { keeper: KeeperId, reply: Reply },
    #[error("the replacement plan or recovery history is inconsistent")]
    History,
}

/// Sweep each nominated idle stream independently. The learner completes only
/// after both surviving members have installed the new ensemble.
pub async fn sweep_idle(
    transport: &dyn Transport,
    plans: impl IntoIterator<Item = Sweep>,
) -> Vec<(StreamId, Result<(), SweepError>)> {
    let mut outcomes = Vec::new();
    for plan in plans {
        outcomes.push((plan.stream, plan.install(transport).await));
    }
    outcomes
}

impl Sweep {
    async fn install(&self, transport: &dyn Transport) -> Result<(), SweepError> {
        let [first, second] = self.survivors;
        if first == second
            || self.ensemble.contains(&self.learner)
            || self.survivors.iter().any(|id| !self.ensemble.contains(id))
        {
            return Err(SweepError::History);
        }
        let next = self.ensemble.map(|id| {
            if self.survivors.contains(&id) {
                id
            } else {
                self.learner
            }
        });
        let (left, right) = tokio::join!(
            self.seal(transport, first, next),
            self.seal(transport, second, next)
        );
        // A create quorum may have included the lost keeper. Rebuild an absent
        // survivor only after the other survivor confirms the stream exists.
        let (left, right) = match (left, right) {
            (Ok(left), Err(error)) if !left.learner && error.not_found() => {
                self.create(transport, second).await?;
                (left, self.seal(transport, second, next).await?)
            }
            (Err(error), Ok(right)) if !right.learner && error.not_found() => {
                self.create(transport, first).await?;
                (self.seal(transport, first, next).await?, right)
            }
            (left, right) => (left?, right?),
        };
        if left.learner || right.learner {
            return Err(SweepError::History);
        }
        let known_commit = left.head.max(right.head);
        let floor = left.floor.max(right.floor);
        let (source, history, other, target) =
            if (left.synced, left.tail) >= (right.synced, right.tail) {
                (first, left, second, right)
            } else {
                (second, right, first, left)
            };
        if history.tail < known_commit || floor.0 > known_commit.0 + 1 {
            return Err(SweepError::History);
        }

        self.copy(
            transport,
            source,
            &history,
            other,
            &target,
            floor,
            known_commit,
        )
        .await?;
        if history.synced != Some(self.epoch) {
            self.sync(
                transport,
                source,
                floor,
                Lsn(history.tail.0 + 1),
                Vec::new(),
                Vec::new(),
                known_commit,
                true,
            )
            .await?;
        }
        // Both survivors now hold the selected history. Publish the adopted tail to
        // them before the replacement can acknowledge that it is a member.
        tokio::try_join!(
            self.head(transport, first, history.tail),
            self.head(transport, second, history.tail),
        )?;
        self.create(transport, self.learner).await?;
        let learner = self.seal(transport, self.learner, next).await?;
        if !learner.learner && learner.ensemble != next {
            return Err(SweepError::History);
        }
        self.copy(
            transport,
            source,
            &history,
            self.learner,
            &learner,
            floor,
            history.tail,
        )
        .await?;
        tokio::try_join!(
            self.replace(transport, first, next),
            self.replace(transport, second, next)
        )?;
        self.replace(transport, self.learner, next).await
    }

    async fn create(&self, transport: &dyn Transport, keeper: KeeperId) -> Result<(), SweepError> {
        self.expect(
            transport,
            keeper,
            Request::Create {
                stream: self.stream,
                ensemble: self.ensemble,
            },
            Reply::Created,
        )
        .await
    }

    async fn copy(
        &self,
        transport: &dyn Transport,
        source: KeeperId,
        history: &StreamView,
        keeper: KeeperId,
        target: &StreamView,
        floor: Lsn,
        head: Lsn,
    ) -> Result<(), SweepError> {
        if target.synced == Some(self.epoch) {
            return if target.tail == history.tail {
                Ok(())
            } else {
                Err(SweepError::History)
            };
        }
        let mut from = Lsn(target.head.0 + 1).max(floor);
        while from <= history.tail {
            let request = Request::Recover {
                stream: self.stream,
                epoch: self.epoch,
                from,
                max: 8192,
            };
            let reply = self.call(transport, source, request).await?;
            let Reply::Records { records, .. } = reply else {
                return Err(SweepError::Reply {
                    keeper: source,
                    reply,
                });
            };
            let mut used = 128;
            let mut last = Lsn(from.0 - 1);
            let mut chunk = Vec::new();
            for (lsn, payload) in records {
                if lsn.0 != last.0 + 1 || lsn > history.tail {
                    return Err(SweepError::History);
                }
                used += 35 + payload.len();
                if used > MAX_FRAME_BYTES {
                    break;
                }
                last = lsn;
                chunk.push(payload);
            }
            if chunk.is_empty() {
                return Err(SweepError::History);
            }
            let start = history.runs.partition_point(|run| run.last < from);
            let runs = history.runs[start..]
                .iter()
                .take_while(|run| run.first <= last)
                .map(|run| EpochRun {
                    epoch: run.epoch,
                    first: run.first.max(from),
                    last: run.last.min(last),
                })
                .collect();
            self.sync(
                transport,
                keeper,
                floor,
                from,
                chunk,
                runs,
                head.min(last),
                last == history.tail,
            )
            .await?;
            if last == history.tail {
                return Ok(());
            }
            from = Lsn(last.0 + 1);
        }
        self.sync(
            transport,
            keeper,
            floor,
            from,
            Vec::new(),
            Vec::new(),
            head,
            true,
        )
        .await
    }

    async fn seal(
        &self,
        transport: &dyn Transport,
        keeper: KeeperId,
        next: [KeeperId; 3],
    ) -> Result<StreamView, SweepError> {
        let seal = |ensemble| Request::Seal {
            stream: self.stream,
            ensemble,
            epoch: self.epoch,
        };
        let mut reply = self.call(transport, keeper, seal(self.ensemble)).await?;
        // A crash can leave one survivor on each ensemble. Resume the same move.
        if reply == Reply::Refused(Refusal::WrongEnsemble { ensemble: next }) {
            reply = self.call(transport, keeper, seal(next)).await?;
        }
        match reply {
            Reply::Sealed(view)
                if view.promised.as_ref().is_some_and(|(epoch, identity)| {
                    *epoch == self.epoch && identity == transport.identity()
                }) =>
            {
                Ok(view)
            }
            _ => Err(SweepError::Reply { keeper, reply }),
        }
    }

    async fn replace(
        &self,
        transport: &dyn Transport,
        keeper: KeeperId,
        to: [KeeperId; 3],
    ) -> Result<(), SweepError> {
        self.expect(
            transport,
            keeper,
            Request::Replace {
                stream: self.stream,
                epoch: self.epoch,
                from: self.ensemble,
                to,
            },
            Reply::Replaced,
        )
        .await
    }

    async fn sync(
        &self,
        transport: &dyn Transport,
        keeper: KeeperId,
        floor: Lsn,
        from: Lsn,
        records: Vec<Bytes>,
        runs: Vec<EpochRun>,
        head: Lsn,
        complete: bool,
    ) -> Result<(), SweepError> {
        let tail = Lsn(from.0 - 1 + records.len() as u64);
        self.expect(
            transport,
            keeper,
            Request::Sync {
                stream: self.stream,
                epoch: self.epoch,
                floor,
                from,
                records,
                runs,
                head,
                complete,
            },
            Reply::Synced { tail },
        )
        .await
    }

    async fn head(
        &self,
        transport: &dyn Transport,
        keeper: KeeperId,
        tail: Lsn,
    ) -> Result<(), SweepError> {
        self.expect(
            transport,
            keeper,
            Request::Append {
                stream: self.stream,
                epoch: self.epoch,
                at: Lsn(tail.0 + 1),
                records: Vec::new(),
                head: tail,
            },
            Reply::Appended { tail },
        )
        .await
    }

    async fn expect(
        &self,
        transport: &dyn Transport,
        keeper: KeeperId,
        request: Request,
        expected: Reply,
    ) -> Result<(), SweepError> {
        let reply = self.call(transport, keeper, request).await?;
        if reply == expected {
            Ok(())
        } else {
            Err(SweepError::Reply { keeper, reply })
        }
    }

    async fn call(
        &self,
        transport: &dyn Transport,
        keeper: KeeperId,
        request: Request,
    ) -> Result<Reply, SweepError> {
        transport
            .call(keeper, request)
            .await
            .map_err(|error| SweepError::Transport { keeper, error })
    }
}

impl SweepError {
    fn not_found(&self) -> bool {
        matches!(
            self,
            Self::Reply {
                reply: Reply::Refused(Refusal::NotFound),
                ..
            }
        )
    }
}
