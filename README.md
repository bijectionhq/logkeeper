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
cargo run --locked -- 127.0.0.1:7654 ./journal-data 65f66914-8889-40a8-91f6-a31476b84014
```

Run a separate process with its own address, directory, and nonzero UUID for each ensemble member.
Use three independent journals and a quorum of two to tolerate one journal failure.
A restart uses the same durable directory and journal identity.
The serving process takes an exclusive journal lock before accepting traffic.
Run listeners on a trusted private network.
A deployment that needs its own discovery, credential, or placement policy can embed `PreparedJournal` and supply its own listener.

## Integration

Pin a release tag and consume the Rust client from this repository.

```toml
logkeeper = { git = "https://github.com/bijectionhq/logkeeper", tag = "v0.2.0" }
```

A single authority allocates increasing epochs for a stream and supplies an ensemble with intersecting write quorums.
The caller owns checkpoint publication and sets the safe trim boundary.
The journal owns the persisted promise, commit position, and record retention for that stream.
The server, client and journal format ship together.
Version 0.2 adds the durable journal identity handshake from [RTDB](https://github.com/bijectionhq/rtdb/commit/65d0a3d9f1340372d4bd71453b7af980fe02b91f).
For identity-bound streams, the client verifies the journal on connection and requires that identity on operations.
Version 0.1 remains available for installations using the earlier elastic-cell wire layout.
Upgrade those clients and journal services together before using version 0.2 administrative operations.
The `simulation` feature exposes state-machine hooks for tests, with compatibility tied to the pinned release.

The initial release extracts the journal from [RTDB Multi](https://github.com/bijectionhq/rtdb/tree/d445003c4f/rust/crates/logkeeper).
It preserves the original on-disk records.
RTDB's adapter continues to own its storage types, checkpoint policy, and directory membership.

## Ordered journal implementation branch

The `logkeeper::ordered` module implements fixed-cohort grant, append, barrier,
checkpoint and trim decisions. Its voter transport takes an already authenticated
channel and its replay API returns the exact journal interval of a live hold.
The embedding service authenticates coordinator and worker identities before choosing any command.
Checkpoint publication and replenishment require the custodian identity at the exact current grant.
The custodian establishes reconstructability and reserves physical allocations before ordering those commands.

The standalone daemon's `ordered-daemon` feature exposes `logkeeper ordered initialize <manifest>` and `logkeeper ordered serve <manifest>`.
Initialize provisions a fresh voter directory once.
Serve recovers only installed directories and accepts mutual TLS 1.3 using the endpoint certificate pins and roles in the installed manifest.
Peer certificates used for voter traffic have no worker or custodian role in that group.
Application clients retain the installed route and receipt verification keys independently of the serving daemon.

The ordered implementation can compact an accepted prefix into a bounded recovery base.
A voter replaces its local selected file atomically and confirms the exact selected image after syncing it.
Running voters can reclaim payloads below the authorized trim floor from their selected files.
Ordered window renewal preserves historical window identities and installs a fresh byte cursor.
The embedding service still needs physical capacity admission and repair of unavailable cohort members.
