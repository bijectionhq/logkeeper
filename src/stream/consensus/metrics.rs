//! Process-wide counters for consensus keeper refusals and stalls.
//!
//! Every refusal a keeper answers as `Unavailable` names its reason here, so an
//! operator can tell admission pressure from lost quorum or full media. The
//! keeper prints the counters that changed every few seconds.

use std::{
    sync::atomic::{AtomicU64, Ordering},
    time::Duration,
};

use tokio_util::sync::CancellationToken;

macro_rules! counters {
    ($($name:ident: $label:literal),* $(,)?) => {
        /// One counter per refusal or stall reason.
        #[derive(Default)]
        pub(super) struct Counters { $(pub $name: AtomicU64,)* }

        impl Counters {
            pub const fn new() -> Self { Self { $($name: AtomicU64::new(0),)* } }

            fn snapshot(&self) -> Vec<(&'static str, u64)> {
                vec![$(($label, self.$name.load(Ordering::Relaxed)),)*]
            }
        }
    };
}

counters! {
    write_unhealthy: "write.unhealthy",
    write_pending: "write.pending_limit",
    write_full_suffix: "write.full_suffix",
    write_space: "write.space",
    write_proposal: "write.proposal_failed",
    write_timeout: "write.timeout",
    head_queue: "head.queue_full",
    head_timeout: "head.timeout",
    peer_busy: "peer.busy",
    peer_unreachable: "peer.unreachable",
    parked: "stream.parked",
    unparked_by_peer: "stream.unparked_by_peer",
    unparked_by_client: "stream.unparked_by_client",
    unparked_for_repair: "stream.unparked_for_repair",
    park_declined: "stream.park_declined",
    reopened_stopped: "stream.reopened_stopped",
    evicted: "stream.evicted",
    compacted_bytes: "segments.compacted_bytes",
}

pub(super) static COUNTERS: Counters = Counters::new();

static SAMPLES: AtomicU64 = AtomicU64::new(0);

/// Logs the detail of refusals, rate-limited per reason with a dropped count.
pub(super) fn sample(reason: &'static str, detail: impl FnOnce() -> String) {
    if SAMPLES.fetch_add(1, Ordering::Relaxed) < 8 {
        tracing::warn!(reason = reason, detail = %detail(), dropped = 0u64, "consensus refusal");
    } else if let Some(dropped) = super::logging::rate_limit(reason, None) {
        tracing::warn!(reason = reason, detail = %detail(), dropped = dropped, "consensus refusal");
    }
}

pub(super) fn count(counter: &AtomicU64) {
    counter.fetch_add(1, Ordering::Relaxed);
}

pub(super) fn add(counter: &AtomicU64, amount: u64) {
    counter.fetch_add(amount, Ordering::Relaxed);
}

/// The counters that changed since `previous`, as `name=total(+delta)` pairs.
fn changed(previous: &[(&'static str, u64)], current: &[(&'static str, u64)]) -> Vec<String> {
    current
        .iter()
        .zip(previous)
        .filter(|((_, now), (_, before))| now != before)
        .map(|((name, now), (_, before))| format!("{name}={now}(+{})", now - before))
        .collect()
}

/// Prints the counters that changed every `interval` until `stop`, and the
/// keeper's gauges whenever their summary changes.
pub(super) async fn report(
    keeper: uuid::Uuid,
    interval: Duration,
    stop: CancellationToken,
    gauges: impl Fn() -> String,
) {
    let mut previous = COUNTERS.snapshot();
    let mut summary = gauges();
    loop {
        tokio::select! {
            () = stop.cancelled() => return,
            () = tokio::time::sleep(interval) => {}
        }
        let current = COUNTERS.snapshot();
        let changes = changed(&previous, &current);
        if !changes.is_empty() {
            tracing::info!(
                keeper = %keeper,
                refusals = %changes.join(" "),
                "consensus refusal counters"
            );
        }
        previous = current;
        let current = gauges();
        if current != summary {
            eprintln!("logkeeper consensus {keeper} segments: {current}");
            summary = current;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_changed_counters_are_reported() {
        let before = vec![("a", 1), ("b", 2)];
        let after = vec![("a", 1), ("b", 5)];
        assert_eq!(changed(&before, &after), vec!["b=5(+3)".to_owned()]);
    }
}
