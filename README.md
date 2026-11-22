# Logkeeper

Logkeeper is a Rust journal server and quorum client for named streams of opaque records.
The caller supplies the ensemble and the writer epoch.
The client seals an intersecting quorum before opening a writer.
It reports append durability once a write quorum has persisted the record.
Readers receive committed records in stream order.

## Run locally

Use Rust 1.94.1 or newer.

```sh
cargo test --locked --all-features
cargo run --locked -- 127.0.0.1:7654 ./journal-data local-journal-a
```

Run a separate process with its own address, directory, and identity for each ensemble member.
Use three independent journals and a quorum of two to tolerate one journal failure.
A restart uses the same durable directory and journal identity.
The serving process takes an exclusive journal lock before accepting traffic.
Run listeners on a trusted private network.
A deployment that needs its own discovery, credential, or placement policy can embed `PreparedJournal` and supply its own listener.

## Integration

Pin a release tag and consume the Rust client from this repository.

```toml
logkeeper = { git = "https://github.com/bijectionhq/logkeeper", tag = "v0.1.0" }
```

A single authority allocates increasing epochs for a stream and supplies an ensemble with intersecting write quorums.
The caller owns checkpoint publication and sets the safe trim boundary.
The journal owns the persisted promise, commit position, and record retention for that stream.
The server, client and journal format ship together.
The `simulation` feature exposes state-machine hooks for tests, with compatibility tied to the pinned release.

The initial release extracts the journal from [RTDB Multi](https://github.com/bijectionhq/rtdb/tree/d445003c4f/rust/crates/logkeeper).
It preserves the on-disk record and wire formats.
RTDB's adapter continues to own its storage types, checkpoint policy, and directory membership.
