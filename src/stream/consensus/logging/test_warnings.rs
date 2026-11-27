//! Fails tests on unexpected warning and error logs (third review pass, T18).
//!
//! `install` sets a process-wide subscriber that records every event at warn
//! level or above whose target is `logkeeper` or below and whose text no
//! entry of `ALLOWED` (or one added by `allow`) matches. `check`, which the
//! keeper test cluster calls when it stops, panics with the unexpected events
//! recorded since the last check and clears them.
//!
//! The subscriber is global because a keeper logs from tokio worker threads
//! and blocking threads, which carry no trace of the test that started them.
//! Tests in one binary run in parallel, so an unexpected event fails a test
//! that checks after it was recorded, not necessarily the one that caused it;
//! the panic names the event, its target and its fields. Set
//! `LOGKEEPER_TEST_WARNINGS=report` to print unexpected events instead of
//! failing, for example to survey a suite.

use std::{
    fmt::{self, Write as _},
    sync::{
        LazyLock, Once,
        atomic::{AtomicU64, Ordering},
    },
};

use parking_lot::Mutex;
use tracing::{
    Event, Level, Metadata, Subscriber,
    field::{Field, Visit},
    span::{Attributes, Id, Record},
};

/// Warnings and errors that a correct keeper logs in ordinary test runs:
/// faults the tests inject on purpose, and peers that are stopped, restarted
/// or partitioned. Each entry matches when the event's text contains it, or,
/// for an entry of parts joined by `&&`, every part.
/// Add an entry only for a condition a test causes deliberately.
const ALLOWED: &[&str] = &[
    // A peer that a test stopped, restarted or made drop appends.
    "reason=\"peer.unreachable\"",
    // A proposal whose Raft core shut down under it while a test stopped
    // its keeper.
    "reason=\"write.proposal_failed\" detail=Err(RecvError(()))",
    // Keepers wiped and installed again under their old ID (incarnation
    // tests).
    "peer answered under a new incarnation",
    "a peer knows this keeper under another incarnation",
    // A replicated catalog voter waits for a peer to confirm its media
    // incarnation before it bootstraps the catalog stream.
    "catalog bootstrap deferred",
    // Every test keeper shares one disk, so on a loaded machine one WAL
    // round can pass the slow-round limit on several keepers at once. A
    // slow keeper still votes, so this costs a hand-off, not availability.
    "consensus WAL round slow; handing off leadership",
    // Auto-repair of a voter a test stopped, refused when the voter
    // returns or the stream moved first.
    "voter repair did not complete",
    // N-1 peers in the rolling-upgrade tests.
    "peer runs an incompatible protocol version",
    // A copy a replacement or recovery moved away fences itself.
    "fenced this copy: the catalog's latest move leaves its configuration",
    // Crashes injected around the WAL boundary.
    "error=interrupted before the WAL boundary",
    "error=interrupted after the WAL boundary",
    // Damage injected into replicas, retained records and segments, and the
    // quarantines and repairs that follow.
    "error=injected",
    "error=transient open failure",
    "scrub found a corrupt copy and quarantined it",
    "error=integrity scrub:",
    "loaded a durable quarantine",
    "reopening stream replica whose Raft core stopped",
    // A keeper still running while its test removes or replaces its data
    // directory, or after a failed test dropped it.
    "object cleanup deferred&&No such file or directory",
    "could not record peer incarnations&&No such file or directory",
    // Liveness leases: a test that stops or cuts off the catalog, fences a
    // keeper, decommissions one, or recovers over lost voters.
    "liveness lease lapsed",
    "the catalog bumped this keeper's epoch",
    "the catalog fenced this copy",
    "an operator recovery fenced the lost voters of this copy by identity",
    "the catalog knows this keeper under another incarnation",
    // Offload tests: an injected corrupt object, and a store not yet
    // reachable.
    "offloaded read failed&&offloaded object checksum mismatch",
    "offload deferred",
];

static UNEXPECTED: LazyLock<Mutex<Vec<String>>> = LazyLock::new(Mutex::default);
static EXTRA: LazyLock<Mutex<Vec<String>>> = LazyLock::new(Mutex::default);
static INSTALL: Once = Once::new();

/// Installs the recording subscriber once per test process.
pub(in crate::stream::consensus) fn install() {
    INSTALL.call_once(|| {
        let _ = tracing::subscriber::set_global_default(Recorder::default());
    });
}

/// Allows events containing `text` for the rest of the process, for a test
/// that causes a condition only it expects.
#[allow(dead_code)]
pub(in crate::stream::consensus) fn allow(text: &str) {
    EXTRA.lock().push(text.to_owned());
}

/// Panics with the unexpected events recorded since the last check.
pub(in crate::stream::consensus) fn check() {
    let events = std::mem::take(&mut *UNEXPECTED.lock());
    if events.is_empty() {
        return;
    }
    let report = events.join("\n  ");
    if std::env::var("LOGKEEPER_TEST_WARNINGS").is_ok_and(|mode| mode == "report") {
        eprintln!("unexpected keeper log events:\n  {report}");
    } else {
        panic!(
            "unexpected keeper warning or error logs (allow a deliberate one in \
             logging/test_warnings.rs):\n  {report}"
        );
    }
}

fn allowed(text: &str) -> bool {
    let matches = |entry: &str| entry.split("&&").all(|part| text.contains(part));
    ALLOWED.iter().any(|entry| matches(entry)) || EXTRA.lock().iter().any(|entry| matches(entry))
}

#[derive(Default)]
struct Recorder {
    spans: AtomicU64,
}

impl Subscriber for Recorder {
    fn enabled(&self, metadata: &Metadata<'_>) -> bool {
        *metadata.level() <= Level::WARN && metadata.target().starts_with("logkeeper")
    }

    fn new_span(&self, _: &Attributes<'_>) -> Id {
        Id::from_u64(self.spans.fetch_add(1, Ordering::Relaxed) + 1)
    }

    fn record(&self, _: &Id, _: &Record<'_>) {}

    fn record_follows_from(&self, _: &Id, _: &Id) {}

    fn event(&self, event: &Event<'_>) {
        let metadata = event.metadata();
        let mut text = format!("{} {}:", metadata.level(), metadata.target());
        event.record(&mut Text(&mut text));
        if !allowed(&text) {
            UNEXPECTED.lock().push(text);
        }
    }

    fn enter(&self, _: &Id) {}

    fn exit(&self, _: &Id) {}
}

struct Text<'a>(&'a mut String);

impl Visit for Text<'_> {
    fn record_debug(&mut self, field: &Field, value: &dyn fmt::Debug) {
        if field.name() == "message" {
            let _ = write!(self.0, " {value:?}");
        } else {
            let _ = write!(self.0, " {}={value:?}", field.name());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::allowed;

    #[test]
    fn deliberate_faults_are_allowed_and_other_warnings_are_not() {
        assert!(allowed(
            "WARN logkeeper::stream::consensus::metrics: consensus refusal \
             reason=\"peer.unreachable\" detail=refused dropped=0"
        ));
        assert!(allowed(
            "ERROR logkeeper::stream::consensus::keeper: quarantined stream replica \
             error=injected replica damage"
        ));
        assert!(!allowed(
            "ERROR logkeeper::stream::consensus::storage::wal: consensus WAL stopped \
             keeper=1 error=Input/output error (os error 5)"
        ));
        assert!(allowed(
            "WARN logkeeper::stream::consensus::keeper: object cleanup deferred \
             keeper=1 error=No such file or directory (os error 2) dropped=0"
        ));
        assert!(!allowed(
            "WARN logkeeper::stream::consensus::keeper: object cleanup deferred \
             keeper=1 error=Permission denied (os error 13) dropped=0"
        ));
        assert!(!allowed(
            "ERROR logkeeper::stream::consensus::keeper: quarantined stream replica \
             error=WAL segment slice failed its checksum"
        ));
    }
}
