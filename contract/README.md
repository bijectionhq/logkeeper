# Journal contract

Consumers can depend on `journal-contract` without depending on Logkeeper. Use
`MemoryJournal` for in-process fixtures and `FileJournal` when a local journal
must survive reopening. Create one journal and call `handle(Identity::from(uri))`
for each caller. Handles outlive the journal value that created them.

    let journal = journal_contract::reference::MemoryJournal::default();
    let writer = journal.handle(journal_contract::Identity::from_static("urn:logkeeper:client:writer"));
    let reader = journal.handle(journal_contract::Identity::from_static("urn:logkeeper:client:reader"));

To persist the fixture, create it with
`FileJournal::open(path, Limits::default())?`. Reopen with the same limits
after dropping every handle. File mutations perform synchronous file writes
and `fsync` on the calling thread. Older numeric identities reopen as
`urn:logkeeper:client:<number>` reference identities. Trim releases the stream's payload quota.
The underlying append-only file retains past mutations. Use the file journal
on a local filesystem for development.

## Run conformance

Enable the `conformance` feature in the consumer or implementation's test
dependency on `journal-contract`. Call `conformance::run` inside your async
test runner. The suite requires a fresh journal namespace, a healthy backend,
and the small fixture limits in `conformance::LIMITS`.

RTDB can exercise the journal contract with either reference and use a handle
from the same fixture for its own integration tests.

```rust
use journal_contract::{conformance, reference::MemoryJournal};
use std::sync::Arc;

async fn check_reference() {
    let journal = MemoryJournal::new(conformance::LIMITS);
    conformance::run(|identity| Arc::new(journal.handle(identity))).await;
}
```

A Logkeeper writer test can start one fresh keeper ensemble configured with
`conformance::LIMITS` and connect three writer clients with distinct
authenticated identities authorized in both `clients` and `writers`. The factory receives `urn:logkeeper:client:1` through
`urn:logkeeper:client:3` in order. Map each to its authenticated client and
share the ensemble across the three clients.

```rust
use journal_contract::{Journal, conformance};
use std::sync::Arc;

async fn check_writers(writers: [Arc<dyn Journal>; 3]) {
    conformance::run(|identity| {
        let name = identity.as_str().strip_prefix("urn:logkeeper:client:").unwrap();
        Arc::clone(&writers[name.parse::<usize>().unwrap() - 1])
    }).await;
}
```

After a takeover, the consumer must apply the stream through the head
returned by `seal` before serving requests.

Failures panic with the check name. A seeded history failure includes the seed
and the recorded calls, intervals, and results. The suite uses 24 seeds with
41 calls each, plus directed scenarios for errors, retries, fencing, trim
races, and long polls.
