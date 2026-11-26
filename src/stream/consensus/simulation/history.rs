//! Operation history recording, linearizability checking, durability/fence
//! invariants, ambiguous batch atomicity, and cross-voter convergence checks.

use std::{
    collections::BTreeMap,
    fmt,
    sync::atomic::{AtomicUsize, Ordering},
};

use bytes::Bytes;
use journal_contract::{
    Epoch, Identity, JournalError, Lsn, Page, Result as ContractResult, StreamId,
    conformance::history::{Call, Op, Value, linearizable},
    reference::Limits,
};
use parking_lot::Mutex;
use uuid::Uuid;

use super::cluster::VoterSnapshot;
use crate::stream::consensus::state::{MAX_BATCH_BYTES, MAX_BATCH_RECORDS};

/// A detected safety, durability, fencing, linearizability, or convergence bug.
#[derive(Clone, Debug)]
pub(super) enum Violation {
    Linearizability {
        stream: StreamId,
        phase: &'static str,
        call_count: usize,
        summary: String,
    },
    DurabilityLoss {
        stream: StreamId,
        lsn: Lsn,
        detail: String,
    },
    HeadRegression {
        stream: StreamId,
        previous: Lsn,
        observed: Lsn,
        detail: String,
    },
    FenceViolation {
        stream: StreamId,
        sealed_epoch: Epoch,
        sealed_by: String,
        accepted_epoch: Epoch,
        accepted_by: String,
        op: &'static str,
    },
    BatchAtomicity {
        stream: StreamId,
        start: Lsn,
        detail: String,
    },
    DeletedResurrection {
        stream: StreamId,
        op: String,
    },
    RecoveryViolation {
        stream: StreamId,
        detail: String,
    },
    CrossVoterDivergence {
        stream: StreamId,
        voters: [Uuid; 3],
        detail: String,
    },
}

impl fmt::Display for Violation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Linearizability {
                stream,
                phase,
                call_count,
                summary,
            } => write!(
                f,
                "LINEARIZABILITY violation on {stream:?} ({phase}, {call_count} calls): {summary}"
            ),
            Self::DurabilityLoss {
                stream,
                lsn,
                detail,
            } => write!(f, "DURABILITY LOSS on {stream:?} at {lsn:?}: {detail}"),
            Self::HeadRegression {
                stream,
                previous,
                observed,
                detail,
            } => write!(
                f,
                "HEAD REGRESSION on {stream:?}: previous {previous:?} -> observed {observed:?} ({detail})"
            ),
            Self::FenceViolation {
                stream,
                sealed_epoch,
                sealed_by,
                accepted_epoch,
                accepted_by,
                op,
            } => write!(
                f,
                "FENCE VIOLATION on {stream:?}: {op} accepted under {accepted_epoch:?} ({accepted_by}) after seal at {sealed_epoch:?} ({sealed_by})"
            ),
            Self::BatchAtomicity {
                stream,
                start,
                detail,
            } => write!(
                f,
                "BATCH ATOMICITY violation on {stream:?} at {start:?}: {detail}"
            ),
            Self::DeletedResurrection { stream, op } => {
                write!(f, "DELETED RESURRECTION on {stream:?}: {op}")
            }
            Self::RecoveryViolation { stream, detail } => {
                write!(f, "RECOVERY violation on {stream:?}: {detail}")
            }
            Self::CrossVoterDivergence {
                stream,
                voters,
                detail,
            } => write!(
                f,
                "CROSS-VOTER DIVERGENCE on {stream:?} ({voters:?}): {detail}"
            ),
        }
    }
}

#[derive(Clone, Debug)]
struct HeadObservation {
    invocation: usize,
    response: usize,
    head: Lsn,
    era: usize,
    source: &'static str,
}

#[derive(Clone, Debug)]
struct SealedFence {
    epoch: Epoch,
    owner: Identity,
    response: usize,
}

#[derive(Clone, Debug)]
struct AcceptedWrite {
    epoch: Epoch,
    owner: Identity,
    invocation: usize,
    era: usize,
    op: &'static str,
}

#[derive(Clone, Debug)]
struct AmbiguousBatch {
    era: usize,
    /// Sub-batches matching `ConsensusJournal::append_batch` chunking.
    chunks: Vec<Vec<(Lsn, Bytes)>>,
}

#[derive(Debug)]
struct StreamHistory {
    /// Current operator-recovery era (0 before any recovery).
    era: usize,
    /// Calls recorded for the `journal_contract` linearizability checker
    /// (capped at 63 calls, and frozen before any operator recovery).
    calls: Vec<Call>,
    /// True once `calls` stopped recording because of the 63-call bitmask cap
    /// or because an operator recovery started.
    calls_frozen: bool,
    /// True only if no call before freezing/recovery was dropped at the 63-call cap.
    calls_complete: bool,
    /// Pre-recovery calls saved when operator recovery begins.
    pre_recovery_calls: Option<(Vec<Call>, bool)>,
    /// Every record ever proposed (for validating reads & surviving recovery records).
    proposed: BTreeMap<Lsn, Vec<Bytes>>,
    /// Records acknowledged in the current recovery era.
    acked: BTreeMap<Lsn, Bytes>,
    /// Highest acknowledged LSN in the current recovery era.
    max_acked: Lsn,
    /// Linearizable head observations (from `head`, `seal`, `append`, `append_batch`).
    heads: Vec<HeadObservation>,
    /// Completed seals (for fencing invariant).
    seals: Vec<SealedFence>,
    /// Accepted writes (`append`, `append_batch`, `trim`) for fencing invariant.
    writes: Vec<AcceptedWrite>,
    /// Ambiguous `append_batch` calls (`Err(Unavailable)`) for batch atomicity check.
    ambiguous_batches: Vec<AmbiguousBatch>,
    /// Response timestamp of the first successful `delete()`, if any.
    deleted_at: Option<usize>,
    /// Operations that succeeded after `deleted_at`.
    post_delete_successes: Vec<(usize, String)>,
    /// Read pages observed (to validate against acked/proposed records).
    observed_reads: Vec<(usize, Page)>,
    /// Highest epoch seen before the latest operator recovery.
    pre_recovery_max_epoch: Option<Epoch>,
    /// Recovery head reported by `acknowledge_recovery` (if any).
    recovered_head: Option<Lsn>,
    /// Early violation detected inline.
    inline_violation: Option<Violation>,
}

impl Default for StreamHistory {
    fn default() -> Self {
        Self {
            era: 0,
            calls: Vec::new(),
            calls_frozen: false,
            calls_complete: true,
            pre_recovery_calls: None,
            proposed: BTreeMap::new(),
            acked: BTreeMap::new(),
            max_acked: Lsn(0),
            heads: Vec::new(),
            seals: Vec::new(),
            writes: Vec::new(),
            ambiguous_batches: Vec::new(),
            deleted_at: None,
            post_delete_successes: Vec::new(),
            observed_reads: Vec::new(),
            pre_recovery_max_epoch: None,
            recovered_head: None,
            inline_violation: None,
        }
    }
}

/// Thread-safe history recorder shared across concurrent client tasks.
pub(super) struct History {
    clock: AtomicUsize,
    streams: Mutex<BTreeMap<StreamId, StreamHistory>>,
    limits: Limits,
}

impl History {
    pub fn new(limits: Limits) -> Self {
        Self {
            clock: AtomicUsize::new(0),
            streams: Mutex::default(),
            limits,
        }
    }

    pub fn tick(&self) -> usize {
        self.clock.fetch_add(1, Ordering::SeqCst)
    }

    /// Registers `(at, payload)` as proposed before the append future is polled,
    /// so a concurrent `read` that observes the record before the append reply
    /// returns is recognized as a valid proposed payload.
    pub fn note_proposed(&self, stream: StreamId, at: Lsn, payload: Bytes) {
        self.streams
            .lock()
            .entry(stream)
            .or_default()
            .proposed
            .entry(at)
            .or_default()
            .push(payload);
    }

    pub fn record_create(
        &self,
        stream: StreamId,
        caller: &Identity,
        invocation: usize,
        response: usize,
        result: &ContractResult<()>,
    ) {
        let mut streams = self.streams.lock();
        let entry = streams.entry(stream).or_default();
        if result.is_ok() && entry.deleted_at.is_some_and(|at| invocation > at) {
            entry
                .post_delete_successes
                .push((invocation, "Create".to_owned()));
        }
        entry.push_call(Call {
            identity: caller.clone(),
            op: Op::Create,
            invocation,
            response,
            result: result.clone().map(|()| Value::Unit),
        });
    }

    pub fn record_seal(
        &self,
        stream: StreamId,
        caller: &Identity,
        epoch: Epoch,
        invocation: usize,
        response: usize,
        result: &ContractResult<Lsn>,
    ) {
        let mut streams = self.streams.lock();
        let entry = streams.entry(stream).or_default();
        if let Ok(head) = result {
            if entry.deleted_at.is_some_and(|at| invocation > at) {
                entry
                    .post_delete_successes
                    .push((invocation, format!("Seal({epoch:?}) -> {head:?}")));
            }
            entry.seals.push(SealedFence {
                epoch,
                owner: caller.clone(),
                response,
            });
            entry.heads.push(HeadObservation {
                invocation,
                response,
                head: *head,
                era: entry.era,
                source: "seal",
            });
        }
        if !matches!(result, Err(JournalError::Recovered { .. })) {
            entry.push_call(Call {
                identity: caller.clone(),
                op: Op::Seal(epoch),
                invocation,
                response,
                result: result.clone().map(Value::Position),
            });
        }
    }

    pub fn record_append(
        &self,
        stream: StreamId,
        caller: &Identity,
        epoch: Epoch,
        at: Lsn,
        payload: Bytes,
        invocation: usize,
        response: usize,
        result: &ContractResult<Lsn>,
    ) {
        let mut streams = self.streams.lock();
        let entry = streams.entry(stream).or_default();
        entry.proposed.entry(at).or_default().push(payload.clone());
        if let Ok(pos) = result {
            if entry.deleted_at.is_some_and(|del| invocation > del) {
                entry
                    .post_delete_successes
                    .push((invocation, format!("Append({epoch:?}, {at:?}) -> {pos:?}")));
            }
            if *pos != at && entry.inline_violation.is_none() {
                entry.inline_violation = Some(Violation::DurabilityLoss {
                    stream,
                    lsn: at,
                    detail: format!("append at {at:?} acknowledged wrong LSN {pos:?}"),
                });
            }
            if let Some(prev) = entry.acked.get(&at)
                && prev != &payload
                && entry.inline_violation.is_none()
            {
                entry.inline_violation = Some(Violation::DurabilityLoss {
                    stream,
                    lsn: at,
                    detail: format!(
                        "two different payloads acknowledged at {at:?}: {} vs {} bytes",
                        prev.len(),
                        payload.len()
                    ),
                });
            }
            entry.acked.insert(at, payload.clone());
            if at > entry.max_acked {
                entry.max_acked = at;
            }
            entry.heads.push(HeadObservation {
                invocation,
                response,
                head: *pos,
                era: entry.era,
                source: "append",
            });
            entry.writes.push(AcceptedWrite {
                epoch,
                owner: caller.clone(),
                invocation,
                era: entry.era,
                op: "append",
            });
        }
        entry.push_call(Call {
            identity: caller.clone(),
            op: Op::Append(epoch, at, payload),
            invocation,
            response,
            result: result.clone().map(Value::Position),
        });
    }

    pub fn record_append_batch(
        &self,
        stream: StreamId,
        caller: &Identity,
        epoch: Epoch,
        records: &[(Lsn, Bytes)],
        invocation: usize,
        response: usize,
        result: &ContractResult<Lsn>,
    ) {
        if records.is_empty() {
            return;
        }
        let mut streams = self.streams.lock();
        let entry = streams.entry(stream).or_default();
        for (lsn, payload) in records {
            entry
                .proposed
                .entry(*lsn)
                .or_default()
                .push(payload.clone());
        }
        let chunks = split_keeper_batches(records);
        match result {
            Ok(last) => {
                let expected_last = records.last().unwrap().0;
                if entry.deleted_at.is_some_and(|del| invocation > del) {
                    entry.post_delete_successes.push((
                        invocation,
                        format!("AppendBatch({epoch:?}, len={}) -> {last:?}", records.len()),
                    ));
                }
                if *last != expected_last && entry.inline_violation.is_none() {
                    entry.inline_violation = Some(Violation::DurabilityLoss {
                        stream,
                        lsn: expected_last,
                        detail: format!(
                            "append_batch ending at {expected_last:?} acknowledged {last:?}"
                        ),
                    });
                }
                for (lsn, payload) in records {
                    if let Some(prev) = entry.acked.get(lsn)
                        && prev != payload
                        && entry.inline_violation.is_none()
                    {
                        entry.inline_violation = Some(Violation::DurabilityLoss {
                            stream,
                            lsn: *lsn,
                            detail: format!("divergent batch payload acknowledged at {lsn:?}"),
                        });
                    }
                    entry.acked.insert(*lsn, payload.clone());
                    if *lsn > entry.max_acked {
                        entry.max_acked = *lsn;
                    }
                }
                entry.heads.push(HeadObservation {
                    invocation,
                    response,
                    head: *last,
                    era: entry.era,
                    source: "append_batch",
                });
                entry.writes.push(AcceptedWrite {
                    epoch,
                    owner: caller.clone(),
                    invocation,
                    era: entry.era,
                    op: "append_batch",
                });
                if !entry.calls_frozen && entry.calls.len() + records.len() <= 63 {
                    for (lsn, payload) in records {
                        entry.calls.push(Call {
                            identity: caller.clone(),
                            op: Op::Append(epoch, *lsn, payload.clone()),
                            invocation,
                            response,
                            result: Ok(Value::Position(*lsn)),
                        });
                    }
                } else {
                    entry.calls_frozen = true;
                    entry.calls_complete = false;
                }
            }
            Err(JournalError::Unavailable) => {
                entry.ambiguous_batches.push(AmbiguousBatch {
                    era: entry.era,
                    chunks,
                });
                if !entry.calls_frozen && entry.calls.len() + records.len() <= 63 {
                    for (lsn, payload) in records {
                        entry.calls.push(Call {
                            identity: caller.clone(),
                            op: Op::Append(epoch, *lsn, payload.clone()),
                            invocation,
                            response,
                            result: Err(JournalError::Unavailable),
                        });
                    }
                } else {
                    entry.calls_frozen = true;
                    entry.calls_complete = false;
                }
            }
            Err(
                err
                @ (JournalError::Fenced { .. } | JournalError::Deleted | JournalError::NotFound),
            ) => {
                let (first_lsn, first_payload) = &records[0];
                entry.push_call(Call {
                    identity: caller.clone(),
                    op: Op::Append(epoch, *first_lsn, first_payload.clone()),
                    invocation,
                    response,
                    result: Err(err.clone()),
                });
            }
            Err(err) => {
                if records.len() == 1 {
                    let (lsn, payload) = &records[0];
                    entry.push_call(Call {
                        identity: caller.clone(),
                        op: Op::Append(epoch, *lsn, payload.clone()),
                        invocation,
                        response,
                        result: Err(err.clone()),
                    });
                }
            }
        }
    }

    pub fn record_read(
        &self,
        stream: StreamId,
        caller: &Identity,
        from: Lsn,
        max: usize,
        invocation: usize,
        response: usize,
        result: &ContractResult<Page>,
    ) {
        let mut streams = self.streams.lock();
        let entry = streams.entry(stream).or_default();
        if let Ok(page) = result {
            if entry.deleted_at.is_some_and(|del| invocation > del) {
                entry
                    .post_delete_successes
                    .push((invocation, format!("Read({from:?}, {max})")));
            }
            entry.observed_reads.push((entry.era, page.clone()));
        }
        entry.push_call(Call {
            identity: caller.clone(),
            op: Op::Read(from, max),
            invocation,
            response,
            result: result.clone().map(Value::Page),
        });
    }

    pub fn record_head(
        &self,
        stream: StreamId,
        caller: &Identity,
        invocation: usize,
        response: usize,
        result: &ContractResult<Lsn>,
    ) {
        let mut streams = self.streams.lock();
        let entry = streams.entry(stream).or_default();
        if let Ok(head) = result {
            if entry.deleted_at.is_some_and(|del| invocation > del) {
                entry
                    .post_delete_successes
                    .push((invocation, format!("Head -> {head:?}")));
            }
            entry.heads.push(HeadObservation {
                invocation,
                response,
                head: *head,
                era: entry.era,
                source: "head",
            });
        }
        entry.push_call(Call {
            identity: caller.clone(),
            op: Op::Head,
            invocation,
            response,
            result: result.clone().map(Value::Position),
        });
    }

    pub fn record_trim(
        &self,
        stream: StreamId,
        caller: &Identity,
        epoch: Epoch,
        through: Lsn,
        invocation: usize,
        response: usize,
        result: &ContractResult<()>,
    ) {
        let mut streams = self.streams.lock();
        let entry = streams.entry(stream).or_default();
        if result.is_ok() {
            if entry.deleted_at.is_some_and(|del| invocation > del) {
                entry
                    .post_delete_successes
                    .push((invocation, format!("Trim({epoch:?}, {through:?})")));
            }
            entry.writes.push(AcceptedWrite {
                epoch,
                owner: caller.clone(),
                invocation,
                era: entry.era,
                op: "trim",
            });
        }
        entry.push_call(Call {
            identity: caller.clone(),
            op: Op::Trim(epoch, through),
            invocation,
            response,
            result: result.clone().map(|()| Value::Unit),
        });
    }

    pub fn record_delete(
        &self,
        stream: StreamId,
        caller: &Identity,
        invocation: usize,
        response: usize,
        result: &ContractResult<()>,
    ) {
        let mut streams = self.streams.lock();
        let entry = streams.entry(stream).or_default();
        if result.is_ok() && entry.deleted_at.is_none() {
            entry.deleted_at = Some(response);
        }
        entry.push_call(Call {
            identity: caller.clone(),
            op: Op::Delete,
            invocation,
            response,
            result: result.clone().map(|()| Value::Unit),
        });
    }

    /// Marks an operator recovery on `stream`. Freezes the pre-recovery
    /// linearizability history and starts a new recovery era where data loss
    /// above `recovered_head` was explicitly acknowledged by the operator.
    pub fn record_operator_recovery(
        &self,
        stream: StreamId,
        recovered_head: Lsn,
        recovery_epoch: Epoch,
    ) {
        let mut streams = self.streams.lock();
        let entry = streams.entry(stream).or_default();
        if entry.pre_recovery_calls.is_none() {
            let calls = std::mem::take(&mut entry.calls);
            entry.pre_recovery_calls = Some((calls, entry.calls_complete));
        }
        entry.calls_frozen = true;
        entry.pre_recovery_max_epoch = Some(
            entry
                .seals
                .iter()
                .map(|s| s.epoch)
                .max()
                .unwrap_or(Epoch(0))
                .max(Epoch(recovery_epoch.0.saturating_sub(1))),
        );
        entry.era += 1;
        // Records above `recovered_head` may have been on the two lost voters;
        // records at or below `recovered_head` must still survive intact.
        entry.acked.retain(|&lsn, _| lsn <= recovered_head);
        entry.max_acked = recovered_head;
        entry.recovered_head = Some(recovered_head);
    }

    /// Checks all invariants on recorded histories + converged voter snapshots.
    pub fn check_all(
        &self,
        converged: &BTreeMap<
            StreamId,
            (
                [Uuid; 3],
                Result<Vec<VoterSnapshot>, Vec<Option<VoterSnapshot>>>,
            ),
        >,
    ) -> Result<(), Violation> {
        let streams = self.streams.lock();
        for (&stream, history) in streams.iter() {
            if let Some(violation) = &history.inline_violation {
                return Err(violation.clone());
            }

            // 1. Delete permanence.
            if let Some((_, op)) = history.post_delete_successes.first() {
                return Err(Violation::DeletedResurrection {
                    stream,
                    op: op.clone(),
                });
            }

            // 1b. Every record returned by any read must match a proposed payload
            //     (and any acknowledged payload in the same recovery era).
            for (era, page) in &history.observed_reads {
                for (lsn, payload) in &page.records {
                    if *era == history.era
                        && let Some(acked) = history.acked.get(lsn)
                        && acked != payload
                    {
                        return Err(Violation::DurabilityLoss {
                            stream,
                            lsn: *lsn,
                            detail: format!(
                                "read returned different payload at {lsn:?} than acknowledged"
                            ),
                        });
                    }
                    if history
                        .proposed
                        .get(lsn)
                        .is_none_or(|candidates| !candidates.contains(payload))
                    {
                        return Err(Violation::DurabilityLoss {
                            stream,
                            lsn: *lsn,
                            detail: format!("read returned unproposed phantom payload at {lsn:?}"),
                        });
                    }
                }
            }

            // 2. Monotonic heads within each recovery era (strict real-time order).
            for a in &history.heads {
                for b in &history.heads {
                    if a.era == b.era && b.invocation > a.response && b.head < a.head {
                        return Err(Violation::HeadRegression {
                            stream,
                            previous: a.head,
                            observed: b.head,
                            detail: format!(
                                "{} (resp {}) saw {:?}, later {} (inv {}) saw {:?}",
                                a.source, a.response, a.head, b.source, b.invocation, b.head
                            ),
                        });
                    }
                }
            }

            // 3. Fencing invariant: no write invoked after a completed seal may
            //    succeed under a lower epoch (or same epoch by a different owner).
            for seal in &history.seals {
                for write in &history.writes {
                    if write.invocation > seal.response
                        && (write.epoch < seal.epoch
                            || (write.epoch == seal.epoch && write.owner != seal.owner))
                    {
                        return Err(Violation::FenceViolation {
                            stream,
                            sealed_epoch: seal.epoch,
                            sealed_by: seal.owner.as_str().to_owned(),
                            accepted_epoch: write.epoch,
                            accepted_by: write.owner.as_str().to_owned(),
                            op: write.op,
                        });
                    }
                }
            }

            // 4. Operator recovery: no pre-recovery epoch may be accepted post-recovery.
            if let Some(pre_epoch) = history.pre_recovery_max_epoch {
                for write in &history.writes {
                    if write.era == history.era && write.epoch <= pre_epoch {
                        return Err(Violation::RecoveryViolation {
                            stream,
                            detail: format!(
                                "post-recovery {} accepted pre-recovery epoch {:?} (<= {:?})",
                                write.op, write.epoch, pre_epoch
                            ),
                        });
                    }
                }
            }

            // 5. Linearizability check via `journal_contract::conformance::history::linearizable`.
            let (phase, calls, complete) = match &history.pre_recovery_calls {
                Some((pre, complete)) => ("pre-recovery", pre.as_slice(), *complete),
                None => ("full", history.calls.as_slice(), history.calls_complete),
            };
            if complete
                && !calls.is_empty()
                && calls.len() < 64
                && !linearizable(calls, self.limits)
            {
                return Err(Violation::Linearizability {
                    stream,
                    phase,
                    call_count: calls.len(),
                    summary: format_calls(calls),
                });
            }

            // 6. Cross-voter convergence, durability against final state, and
            //    ambiguous batch atomicity.
            if let Some((voters, outcome)) = converged.get(&stream) {
                let snaps = match outcome {
                    Ok(snaps) => snaps,
                    Err(partial) => {
                        return Err(Violation::CrossVoterDivergence {
                            stream,
                            voters: *voters,
                            detail: format!(
                                "voters did not converge: {:?}",
                                partial
                                    .iter()
                                    .map(|s| s.as_ref().map(|v| (
                                        v.keeper,
                                        v.deleted,
                                        v.floor,
                                        v.head,
                                        v.records.len()
                                    )))
                                    .collect::<Vec<_>>()
                            ),
                        });
                    }
                };
                if snaps.len() != 3
                    || snaps.windows(2).any(|w| {
                        w[0].deleted != w[1].deleted
                            || w[0].floor != w[1].floor
                            || w[0].head != w[1].head
                            || w[0].records != w[1].records
                    })
                {
                    return Err(Violation::CrossVoterDivergence {
                        stream,
                        voters: *voters,
                        detail: format!(
                            "voters disagree after convergence: {:?}",
                            snaps
                                .iter()
                                .map(|v| (v.keeper, v.deleted, v.floor, v.head, v.records.len()))
                                .collect::<Vec<_>>()
                        ),
                    });
                }

                let final_state = &snaps[0];
                if !final_state.deleted {
                    // Every acknowledged append in the current era must survive.
                    if final_state.head < history.max_acked {
                        return Err(Violation::DurabilityLoss {
                            stream,
                            lsn: history.max_acked,
                            detail: format!(
                                "converged head {:?} is below acknowledged {:?}",
                                final_state.head, history.max_acked
                            ),
                        });
                    }
                    let final_map: BTreeMap<Lsn, &Bytes> = final_state
                        .records
                        .iter()
                        .map(|(lsn, bytes)| (*lsn, bytes))
                        .collect();
                    for (&lsn, expected) in &history.acked {
                        if lsn < final_state.floor {
                            continue;
                        }
                        match final_map.get(&lsn) {
                            Some(actual) if *actual == expected => {}
                            Some(actual) => {
                                return Err(Violation::DurabilityLoss {
                                    stream,
                                    lsn,
                                    detail: format!(
                                        "converged bytes at {lsn:?} mismatch acknowledged payload ({} vs {} bytes)",
                                        actual.len(),
                                        expected.len()
                                    ),
                                });
                            }
                            None => {
                                return Err(Violation::DurabilityLoss {
                                    stream,
                                    lsn,
                                    detail: format!(
                                        "acknowledged record at {lsn:?} missing from converged voters (floor {:?}, head {:?})",
                                        final_state.floor, final_state.head
                                    ),
                                });
                            }
                        }
                    }

                    // Every record on disk must match some payload actually proposed for that LSN.
                    for (lsn, bytes) in &final_state.records {
                        if history
                            .proposed
                            .get(lsn)
                            .is_none_or(|candidates| !candidates.contains(bytes))
                        {
                            return Err(Violation::DurabilityLoss {
                                stream,
                                lsn: *lsn,
                                detail: format!(
                                    "converged voter holds unproposed payload at {lsn:?}"
                                ),
                            });
                        }
                    }

                    // Ambiguous append_batch atomicity: within each single keeper batch
                    // whose records are still retained above floor, either ALL records
                    // with this batch's unique payloads committed or NONE did, and across
                    // multi-chunk batches only a whole-batch prefix may commit.
                    for batch in &history.ambiguous_batches {
                        if batch.era != history.era {
                            continue;
                        }
                        let mut saw_absent_chunk = false;
                        for chunk in &batch.chunks {
                            let retained: Vec<&(Lsn, Bytes)> = chunk
                                .iter()
                                .filter(|(lsn, _)| *lsn >= final_state.floor)
                                .collect();
                            if retained.is_empty() {
                                continue;
                            }
                            let matched = retained
                                .iter()
                                .filter(|(lsn, payload)| final_map.get(lsn) == Some(&payload))
                                .count();
                            if matched > 0 && matched < retained.len() {
                                return Err(Violation::BatchAtomicity {
                                    stream,
                                    start: chunk[0].0,
                                    detail: format!(
                                        "ambiguous keeper batch partially committed: {matched}/{} retained records present",
                                        retained.len()
                                    ),
                                });
                            }
                            if matched == 0 {
                                saw_absent_chunk = true;
                            } else if saw_absent_chunk {
                                return Err(Violation::BatchAtomicity {
                                    stream,
                                    start: chunk[0].0,
                                    detail: "later chunk of append_batch committed without earlier chunk".to_owned(),
                                });
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

impl StreamHistory {
    fn push_call(&mut self, call: Call) {
        if self.calls_frozen {
            return;
        }
        if self.calls.len() < 63 {
            self.calls.push(call);
        } else {
            self.calls_frozen = true;
            self.calls_complete = false;
        }
    }
}

/// Splits `records` into keeper batches identically to `ConsensusJournal::append_batch`.
fn split_keeper_batches(records: &[(Lsn, Bytes)]) -> Vec<Vec<(Lsn, Bytes)>> {
    let mut chunks = Vec::new();
    let mut iter = records.iter().peekable();
    while iter.peek().is_some() {
        let mut chunk = Vec::new();
        let mut bytes = 0usize;
        while let Some((lsn, payload)) = iter.peek() {
            if chunk.len() == MAX_BATCH_RECORDS
                || bytes.saturating_add(payload.len()) > MAX_BATCH_BYTES
            {
                break;
            }
            bytes += payload.len();
            chunk.push((*lsn, payload.clone()));
            iter.next();
        }
        chunks.push(chunk);
    }
    chunks
}

fn format_calls(calls: &[Call]) -> String {
    let mut out = String::new();
    for (i, c) in calls.iter().enumerate() {
        let op = match &c.op {
            Op::Create => "Create".to_owned(),
            Op::Seal(e) => format!("Seal({e:?})"),
            Op::Append(e, lsn, p) => format!("Append({e:?}, {lsn:?}, {}B)", p.len()),
            Op::Read(from, max) => format!("Read({from:?}, {max})"),
            Op::Head => "Head".to_owned(),
            Op::Trim(e, through) => format!("Trim({e:?}, {through:?})"),
            Op::Delete => "Delete".to_owned(),
        };
        let res = match &c.result {
            Ok(Value::Unit) => "Ok(())".to_owned(),
            Ok(Value::Position(lsn)) => format!("Ok({lsn:?})"),
            Ok(Value::Page(p)) => format!(
                "Ok(Page(floor={:?}, head={:?}, n={}))",
                p.floor,
                p.head,
                p.records.len()
            ),
            Err(e) => format!("Err({e:?})"),
        };
        out.push_str(&format!(
            "\n  #{i:02} [{}..{}] {} {op} => {res}",
            c.invocation,
            c.response,
            c.identity.as_str(),
        ));
    }
    out
}
