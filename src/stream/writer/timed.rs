//! Exact timed-original operations on the same writer and keeper ensemble.

use bytes::Bytes;
use journal_contract::{JournalError, Lsn, Result};

use super::{Io, KeeperId, Reply, Request, Writer, quorum};
use crate::stream::timed::{
    Entry, MAX_TIMED_PAYLOAD, TimedEvidence, TimedOrigin, TimedOriginal, TimedOriginalProof,
    TimedOriginalVerifier, TimedSample,
};
use std::sync::Arc;

pub(super) struct Authority {
    verifier: Arc<dyn TimedOriginalVerifier>,
    max_payload_bytes: Option<usize>,
}

impl Writer {
    /// Mount trusted historical keeper keys and the provisioned payload limit
    /// for this route. A verify-only mount has no timed write capacity.
    /// The route owner supplies a limit supported by its mounted original keepers.
    pub fn with_timed_original(
        mut self,
        verifier: Arc<dyn TimedOriginalVerifier>,
        max_payload_bytes: Option<usize>,
    ) -> Self {
        self.timed_authority = Some(Arc::new(Authority {
            verifier,
            max_payload_bytes: max_payload_bytes
                .filter(|max| *max > 0)
                .map(|max| max.min(MAX_TIMED_PAYLOAD)),
        }));
        self
    }

    pub fn maximum_timed_original_bytes(&self) -> Option<usize> {
        self.timed_authority.as_ref()?.max_payload_bytes
    }

    pub async fn append_timed_original(
        &self,
        original: TimedOriginal,
        exact_sealed_payload: Bytes,
    ) -> Result<TimedOriginalProof> {
        if !original.matches(&exact_sealed_payload) {
            return Err(JournalError::Unavailable);
        }
        if let Ok(proof) = self.prove_timed_original(original).await {
            return Ok(proof);
        }
        let max = self
            .maximum_timed_original_bytes()
            .ok_or(JournalError::Unavailable)?;
        if exact_sealed_payload.len() > max {
            return Err(JournalError::TooLarge { max });
        }
        let authority = self
            .timed_authority
            .as_ref()
            .ok_or(JournalError::Unavailable)?;
        let stream = self.stream(original.stream);
        let _mutation = stream.mutation.lock().await;
        let active = self.active(&stream, original.epoch)?;

        let entry = match active.timed_entry(original) {
            Some(entry) => entry,
            None => {
                let previous = Lsn(original.at.0 - 1);
                if active.head() != previous {
                    // A timed append may have finished while this request waited.
                    return self.prove_timed_original(original).await;
                }
                active.published(previous).await?;
                active.reserve_timed(original)?;
                active.retry_lanes();
                let origin = TimedOrigin {
                    original,
                    ensemble: stream.ensemble,
                    proposal: self.io.proposal,
                };
                let [first, second, _] = stream.ensemble;
                let sample =
                    |keeper| stage(&self.io, keeper, original, exact_sealed_payload.clone());
                let (first, second) = tokio::try_join!(sample(first), sample(second))?;
                let evidence = TimedEvidence {
                    origin,
                    samples: [first, second],
                };
                evidence
                    .proof(&*authority.verifier)
                    .ok_or(JournalError::Unavailable)?;
                Entry::Timed {
                    evidence: Arc::new(evidence),
                    payload: exact_sealed_payload,
                }
            }
        };
        active.append(original.at, entry).await?;
        self.prove_timed_original(original).await
    }

    /// Read-only verification. The current quorum establishes committed
    /// visibility. The bound and digest come from the original signed samples.
    pub async fn prove_timed_original(
        &self,
        original: TimedOriginal,
    ) -> Result<TimedOriginalProof> {
        let authority = self
            .timed_authority
            .as_ref()
            .ok_or(JournalError::Unavailable)?;
        if !original.valid() {
            return Err(JournalError::Unavailable);
        }
        let stream = self.stream(original.stream);
        let [first, second] = quorum(stream.ensemble.map(|keeper| async move {
            match self
                .io
                .call(
                    keeper,
                    Request::ProveOriginal {
                        stream: original.stream,
                        at: original.at,
                    },
                )
                .await?
            {
                Reply::OriginalEvidence(evidence) if evidence.origin.original == original => {
                    evidence
                        .proof(&*authority.verifier)
                        .ok_or(JournalError::Unavailable)
                }
                _ => Err(JournalError::Unavailable),
            }
        }))
        .await?;
        if first != second {
            return Err(JournalError::Unavailable);
        }
        Ok(first)
    }
}

async fn stage(
    io: &Io,
    keeper: KeeperId,
    original: TimedOriginal,
    payload: Bytes,
) -> Result<TimedSample> {
    match io
        .call(
            keeper,
            Request::StageOriginal {
                stream: original.stream,
                original,
                payload,
            },
        )
        .await?
    {
        Reply::OriginalSample(sample) => Ok(sample),
        _ => Err(JournalError::Unavailable),
    }
}
