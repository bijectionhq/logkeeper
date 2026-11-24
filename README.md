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
Application wire version 12 (`LKAPPC12`) carries the erasure replay floor and requires signed slot evidence on a successful erasure switch. The withdrawn hold owner query remains restricted to the custodian.
Each page contains at most 64 distinct enrollments in enrollment order and fits the configured application frame.
Pass the last enrollment as a cursor to continue.
Each page reflects its own selected state and gives the journal-time threshold for expiry disposal.
Voter wire version 4 (`LKORPC04`) carries both durable image identities and confirms explicit readback on an erasure accept.
Update the voter cohort and application clients together before using rotation evidence.
Provision fresh voter media and compact recovery images with this protocol.
Keep every previously trusted barrier receipt public key for the lifetime of the logical placement, including its incarnation and generation.
Rotate signers through a cohort successor and distribute the updated trusted `ApplicationRoute.verification_keys` to clients before using its new signers.
Set `predecessor_keys` from the immediate predecessor's active voter roster and carry older public keys in `retained_barrier_keys`.
The seal checks that the successor carries the source's full verification set and that its repair keys come from the source's active roster.
Use the same trusted destination manifest for the seal, reservation, installation, and route publication.
Old public keys verify issued receipts offline. A verified receipt still needs a live hold and its protected basis to serve a read.
Retire old private keys once their cohort and repair signing are finished. Retaining the public keys is sufficient for offline verification.

A voter initialized with an empty `groups` array can persist runtime groups.
Its `management` pins authorize the management protocol over mutual TLS.
Only an administrator can install a group, publish its route or retire it.
`InstallGroup` with `expected_absent: true` can create an absent group.
An identical definition returns the installed route on retry.
A changed definition or a retired deployment is refused.
The daemon syncs the group definition and two voter slots before it publishes the room.
A separate durable `PublishRoute` binds a deployment to its name and organization.
Discover `ApplicationRoute` by deployment UUID or by name using a pinned management credential.
Callers making cell-wide installation or discovery decisions require matching replies from a strict majority of their pinned voters.
`RetireGroup` requires an exact selected checkpoint at the head, a vacant writer, no remaining holds and no checkpoint preparation.
It orders a terminal seal in the next decision slot, then persists a local tombstone that excludes the group from application discovery and service.
The daemon retains sealed voter media for retirement reconciliation.

The ordered implementation can compact an accepted prefix into a bounded recovery base.
Provisioning reserves two durable slots per voter and group.
To select a new slot the voter syncs its body and checksummed generation header together while the prior selected slot stays intact.
Recovery verifies the combined digest before considering a slot, including when a crash partially persists an unsynced replacement.
Before returning any promise or vote the voter installs the same promised ballot and accepted prefix in both slots, in succession.
Either remaining valid slot therefore covers the acknowledged ballot and vote after a tear.
A voter whose slots are both invalid cannot vote.
Recovery syncs the selected slot and its directory before admitting another rotation, including after a warm restart that observes a still-volatile header.
Reusing a slot clears residual bytes from its previous body.
An installed voter needs a filesystem that honours file preallocation and the configured durability barriers.
Ordered window renewal preserves historical window identities and installs a fresh byte cursor.
Each new voter preallocates both files before joining. The volume owner funds their physical footprint, metadata and all co-resident allocations. See the [installation premises](verification/evidence.md#c9-installed-boundaries).
A repair reserves media with `reserve-repair`, orders the exact successor with `seal-repair` on an old coordinator, and consumes the signed package with `install-repair` on each prepared successor.
The predecessor serves no fresh commands after choosing its seal.
The successor installs the exact sealed state in both slots before voting and preserves the original writer, retained receipts, checkpoint holds and paid append cursor.

A custodian orders `PublishAndRotate` against the exact incumbent, head and erasure preparation. One decision selects the clean checkpoint, commits the successor payload key generation and closes new holds on the preceding roots and replay range. Existing hold owners retain access until their holds end.
The command returns signed evidence of a strict accepting majority at the clean checkpoint and successor suffix generation.
Each named voter reads both durable slots after the mirrored write and checks the accepted ballot, prefix and image identities before acknowledgement.
The coordinator obtains those records over authenticated voter channels and signs the rotation receipt and slot evidence together.
The installed client verifies the signature and the cohort it contacted.
Other voters can still hold stale local images, and every eligible recovery majority intersects the acknowledging majority.
The surviving slot of an intersecting voter carries its acknowledged vote or a later one, allowing ranked recovery to select the rotation or a continuation.
The same rule protects the seal through cohort repair.
An exact rotation retry can reissue the evidence while the selected root and suffix generation still match.
