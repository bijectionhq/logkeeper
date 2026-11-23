# RTDB recovery dependencies at f3be4137350e

This audit uses the local RTDB source at commit `f3be4137350ee6ac69634226ef1695744da9ccb0`.
The Allium contracts and Rust paths below define the checked boundary.
This study exercises a Lean abstraction of the decoded representation and one transcribed source fixture.

## Current checkpoint inventory

| Boundary | Current source and precise behavior | Reference obligation |
| --- | --- | --- |
| Root and table identity | The root registry and optional table-block manifest are decoded in `BlockCatalog`. A present manifest covers exactly the registered OIDs and supplies a 32-byte digest per OID. The replication loader checks an expected root digest and verifies every table body when the root supplies those digests. [Format catalog](../../../rtdb/rust/crates/format/src/catalog.rs) · [Replication block loader](../../../rtdb/rust/crates/replication/src/blocks.rs) | Accept a modern root with its exact table bodies. For a legacy root, require authenticated inventory evidence for those table digests before using the portable publication path. |
| Declared recovery members | The archive path derives the root and table keys from the verified cut and traverses the decoded table metadata. Populated partition lists determine the trie details, and an empty partition list uses legacy flat details. Replay includes data and metadata of live and nascent tries and retained garbage L0. Recorded live or nascent artefacts use their own canonical keys, including shared group keys. [Archive closure](../../../rtdb/rust/crates/multi/src/archive.rs) · [Format catalog](../../../rtdb/rust/crates/format/src/catalog.rs) | Derive the dependency set from the decoder and named closure. Deduplicate equal logical keys by their actual canonical names. |
| Exact physical carriers | Pack index reading checks the observed version for the head, trailer and index and validates entry bounds. Member reads verify the range's same physical publication. The packed observation supplies the containing pack's version for its logical members. `PhysicalObjectVersion` contains the provider namespace, full provider key and version. [Packing store](../../../rtdb/rust/crates/multi/src/packing.rs) · [Version type](../../../rtdb/rust/crates/types/src/position.rs) | A packed member's coverage and debit identify its containing version. Many members can depend on one allocation. A change of carrier uses its own exact observation and custody. |
| Current inventory commitment | `recovery_manifest_sha256` commits the exact root digest, storage epoch, first required replica offset and ordered inventory of logical path, length, observed physical version and metadata digest. The current RTDB Multi holder records it through a directory update. Startup verifies it before exposing the opened store. [Archive digest](../../../rtdb/rust/crates/multi/src/archive.rs) · [Publisher](../../../rtdb/rust/crates/multi/src/agent.rs) · [Hosted store admission](../../../rtdb/rust/crates/multi/src/store.rs) | Carry the authenticated logical cut and its selected physical custody together in the journal's published result. Another residence can preserve the logical cut and has its own physical inventory commitment. |
| External replay bodies | The current inventory derives only from the checkpoint objects. The replica player fetches an oversized proxy's named object right after term admission, before the stale and hold decisions. It checks only the term and sequence of the decoded body, which can be any non-oversized `ReplicaBody`. Admission checks the first required offset against the current retained prefix. [Replica logs](../../../rtdb/rust/crates/replication/src/logs.rs) · [Replay start](../../../rtdb/rust/crates/multi/src/hosted_recovery.rs) · [Replica envelope](../../../rtdb/rust/crates/format/src/envelope.rs) | Include each admitted oversized payload and its decoded body's dependencies. Bind each payload to its exact storage epoch, authorized frame, digest and physical custody. |

The [RTDB Multi spec](../../../rtdb/allium/rtdb-multi.allium) still names the directory as the checkpoint authority and describes separate manifest and boot objects.
The inspected Rust path uses the block catalogue as its logical root and the pack carrying it as the boot object in the packed store.
Rust supports legacy roots without the optional table digest map and distinct archive content versions.
The [database](../../../rtdb/dev/doc/db.allium), [trie catalog](../../../rtdb/dev/doc/trie-cat.allium), [block collection](../../../rtdb/dev/doc/block-gc.allium), and [trie collection](../../../rtdb/dev/doc/gc.allium) specifications describe the table digest, replay inputs, physical version and retention boundaries.
Moving authoritative checkpoint publication to Logkeeper and requiring custody-backed replay is the target architecture.

## Replay tail reads

`apply_admitted` in the [replication driver](../../../rtdb/rust/crates/replication/src/driver.rs) dispatches on the decoded body.

| Body | Guard in the inspected source | Storage reads and later references |
| --- | --- | --- |
| `BlockUploaded` that matches | A block is pending, and `matches_upload` holds: equal block index, storage version and epoch | `blocks.load(index)` reads `block_key(index)` through `head_fresh` and `get_fresh_exact`. Each table block is checked against the manifest when one is present. `adopt_block` adds the upload's tries to the live trie catalog, or replaces the catalog after a naming-epoch reset. |
| `BlockUploaded` that does not match | `upload_for_installed_block` or `stale` (index at or below the installed block) | None, complete. Without a pending block, an upload above the installed block is an error. |
| Any body while a block is pending | No match | Held in memory and reprocessed after adoption, in order. |
| `TriesAdded` | Above the compaction cutoff, matching version and epoch, not stale by source position | References the added trie files. |
| `ArtefactsAdded` | Matching version and epoch, not stale | References the added artefacts. |
| `TriesDeleted`, `ArtefactsRemoved` | Cutoff or staleness | Drop references and invalidate the local cache. |
| `ResolvedTx`, `NoOp`, `BlockBoundary` | — | No object read in the inspected branches. A transaction can apply a database operation as an effect. |
| `OversizedMessage` | Resolved before dispatch, and rejected if it reaches apply | Nested oversized bodies are rejected by `unwrap_payload`. |

The upload at this pin names its root only by block index, with no digest.
The model therefore takes a certified binding of each adopted root as a premise.

### Drift to RTDB `origin/main`

RTDB `origin/main` at `455daa515d` is ahead of this pin and contains the counterpart's `8af2d6e` and `3b605d6`.
Between the pin and that head, the driver, replica logs, block loader, envelope and archive paths change by about 2,300 lines.
Inspection of the head shows the same branch structure for the reads above, with two binding additions:

- `BlockUploaded` carries `catalog_sha256`, and `validate_uploaded_root` checks it when `requires_checkpoint_digest()` holds.
- An installed oversized proxy carries `payload_sha256`, and `resolve_oversized_fresh` reads it from the original writer's replica-object scope.

Both checks are conditional.
A legacy upload or payload without a digest can still pass when no digest is required, so portable publication must refuse it or authenticate it by inventory.
Re-pinning this audit and the fixture to the counterpart revision is the next refinement step.

## Fixture and scope of the proof

The Lean fixture transcribes the partitioned live and nascent entries, garbage L0, garbage higher-level entry, shared-group artefact and ignored legacy flat entry from `replay_closure_preserves_l0_inputs_and_usable_artefacts`.
The [format fixture](../../../rtdb/rust/crates/format/tests/catalog_retention.rs) expects set semantics.
The Lean base list may repeat an identical shared key and the coverage law is over membership.
The [serving digest fixture](../../../rtdb/rust/crates/multi/src/archive.rs) rejects missing retained L0 or artefacts and observes a different commitment after restoring those objects at new provider versions.
The fixture is transcribed and executed in Lean.
The Rust tests and production decoders were inspected here.

The Lean model assumes the protobuf decoder and authenticated verifier supplied the decoded table bodies and exact canonical keys.
It does not implement protobuf field parsing, canonical packing, provider version verification, plaintext cryptography, or the production archive reader.
Recoverability is conditional on selected RTDB data and every retained replay frame and side attachment being correctly projected and bound.
The contract can conservatively protect all named oversized objects in the needed chosen suffix.
Pruning a side object whose outer frame will be filtered needs a verified replay decision that excludes every selectable path that could read it.
