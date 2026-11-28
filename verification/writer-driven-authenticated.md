# Authenticated history for the writer-driven journal

2026-11-28. Branch `writer-driven/authenticated`, based on `writer-driven/repair`.
This note extends `target-journal.md` section 3 and `writer-driven-repair.md`.

RTDB's lineage, portable backups, timed Store settlement and recovery cuts need a
portable proof that a record is part of a stream's committed history. Today only
the consensus keeper (`stream::consensus::authenticated`) provides it, with the
replicated catalog as the trust root (`CatalogRoot`). This note gives the
writer-driven journal the same proofs with a keeper-quorum trust root, so RTDB can
drop the consensus keeper for these features.

## Decisions

1. **Trust root: the operator-pinned keeper key set.** `KeeperKeys { journal: Uuid,
   keepers: [{ identity, keys: [Ed25519 public key] }] }` lists every keeper the
   journal ever placed streams on, spares and departed keepers included. It
   replaces `CatalogRoot`. `journal` names the keeper fleet and stays fixed across
   rotation and replacement, so consumers pin it in records instead of a digest.
   `KeeperKeys::digest()` exists only for operators to compare installed copies.
2. **What is signed.** `Head { journal, stream, size, root, ensemble }`: the
   committed prefix of `stream` through `size` has RFC 6962 Merkle root `root`,
   as held by the members of `ensemble`. Domain `logkeeper/stream/authenticated/head/v1`.
   No timestamp, lease or catalog revision.
3. **Who signs, and validity.** Each keeper signs with its own dedicated key. A
   `SignedHead` is valid when two distinct members of `head.ensemble` signed the
   identical statement with keys installed for them. A duplicate signer, an
   outsider, an uninstalled key or any invalid signature rejects the head.
4. **When.** On demand, through a proof read. Appends and seals are unchanged and
   pay nothing beyond leaf ingestion. A keeper signs `size` only if `size` is at
   or below its own head, which the protocol guarantees is committed, and only
   after recomputing the root from its own leaves. Keepers still never talk to
   each other: the client collects the two shares.
5. **Leaves.** `Leaf { stream, at, writer_epoch, payload_sha256, timing }`. Every
   keeper holding a committed record derives the same leaf from the record, its
   epoch run, and, for a timed original, its retained evidence:
   `Timing { exclusive_cutoff_micros, receiver_certificate_sha256,
   quorum_sync_upper_micros, evidence_sha256 }`. The bound comes from the two
   keeper-signed stage samples (`stream::timed`), never from the signing keeper's
   clock. Ordinary records carry no time. (The consensus leaf's
   `quorum_durable_upper_micros` has no writer-driven equivalent for ordinary
   records; RTDB only reads it for timed leaves.)
6. **Dedicated signing keys, not TLS keys.** Keeper TLS keys sign handshake
   transcripts, rotate with certificate renewal, and may live in a terminator.
   History signatures must outlive certificates and must never be producible by a
   TLS oracle. Both existing precedents already refuse reuse: the consensus
   keeper's `signer_pkcs8_file` and the timed-original trust registry reject a key
   equal to the TLS key. `Signer::load` does the same. The history key is also
   separate from the timed-original attestation key, which sits behind the
   private clock mount and is optional.
7. **Where leaves live.** A per-stream append-only ledger
   `DATA/authenticated/<stream>.leaves` (133-byte CRC-framed records) beside the
   WAL, not in the WAL or checkpoint formats. It is derived data, so the verified
   keeper storage and its byte proofs are untouched. Leaves are ingested after
   each round for committed records (no sync). Before a Trim is decided, the
   leaves it discards are synced. A torn tail is cut on load and recomputed from
   retained records.
8. **Seeding instead of keeper-to-keeper transfer.** A replacement keeper, or a
   lagging keeper that synced past a trimmed prefix, has a gap below its floor
   and answers `Missing { ingested, floor }`. A client copies the missing leaves
   from a signer (`Seed` pages) and attaches a head two other keepers signed. The
   keeper installs them only if the head verifies against its installed key set
   and the staged leaves plus its own retained records reproduce the signed root.
   A faulty relay cannot plant leaves.
9. **Enablement is per keeper, not per stream.** A keeper with an
   `authenticated` config section authenticates every stream. No per-stream mode
   enters the wire `Create`, the WAL or the checkpoint. `require_authenticated`
   succeeds when two members report a complete ledger.

## Protocol

One new request and reply carry bincode bodies (`stream::authenticated::protocol`),
so the protobuf schema gains one opaque field each way (request tag 18, reply tag 16):

| `AuthRequest` | Reply | Rule |
| --- | --- | --- |
| `Status` | `Status { ingested, floor, complete }` | Client read. |
| `Sign { size }` | `Signed { head, signature }` or `Missing` | Voting member only (`NotSynced` otherwise); `size <= head` (`AboveHead` otherwise). |
| `Leaves { from, through }` | `Leaves(≤1024)` or `Missing` | Any member with the leaves. |
| `Path { at, size }` | `Path { leaf, path }` | Built from the ledger. |
| `Consistency { earlier, later }` | `Consistency(path)` | Built from the ledger. |
| `Seed { from, leaves, head }` | `Seeded { ingested }` | Writer authorization. Pages start at `ingested + 1`; the last carries the head. |

A keeper without the feature answers `Unsupported`. Stream refusals (`NotFound`,
`Deleted`, `AboveHead`) use the outer `Reply::Refused`.

## Proof and archive formats

`stream::authenticated` (feature `stream`) exports `KeeperKeys`, `TrustedKeeper`,
`Signer`, `Leaf`, `Timing`, `Head`, `HeadSignature`, `SignedHead`, `Inclusion`,
`Consistency`, `Archive`, `Tree`, `ProofError` and the `AuthenticatedJournal`
trait. Every `verify` takes `&KeeperKeys`. `Archive { tree, signed_head }` is
written as magic `LKSARCH1`, the bincode `SignedHead`, then each leaf. The consensus
archive keeps magic `LKAARCH1` and its exact bytes. Both use the shared framing
(`authenticated/archive.rs`) and the shared generic Merkle tree
(`authenticated/merkle.rs`, moved from `consensus/authenticated/tree.rs`);
`consensus::authenticated::Tree` is now `merkle::Tree<consensus Leaf>`.
`Archive::recertify` swaps in a newer head over the same prefix.

## Ensemble changes and keeper replacement

A head names the ensemble that signed it, and verification only needs the
signers' keys in the installed inventory. So an archive certified by `{1, 3}` of
`[1, 2, 3]` still verifies after keeper 3 is replaced by 4, and a `Consistency`
proof can join a head of `[1, 2, 3]` to a head of `[1, 2, 4]`. A replacement
cannot co-sign a head naming an ensemble it was not in, because the statement
binds the ensemble and an honest keeper signs only its current one.

We do not chain signed ensemble transitions. A chain would still start from a
genesis ensemble that only the inventory vouches for, so it cannot resist two
compromised inventory keys any better, and it would need keepers to sign
`Replace`, which the repair protocol does not route through them. The honest
threshold is "any two keys of the inventory". Operators who need a stronger
binding pin per-stream genesis ensembles out of band.

During a half-installed move the survivors can name different ensembles, so no
two shares match and certification returns `Unavailable` until the move
completes. That costs availability, not safety. After a repair, the repairer (or
any client) must call `Writer::seed_authenticated(stream)` while two members still
hold the full history. `authenticated_head` also seeds a member that reports
`Missing` before the quorum forms, in the background. If two members of one
ensemble lack the prefix and the third alone holds it, the stream cannot be
certified again; this is the authenticated analogue of the repair note's
"second loss".

## Key rotation

1. Generate the new key and add its public key to the keeper's `TrustedKeeper`
   entry in every installed copy (keepers and consumers). Both keys verify.
2. Point the keeper's `signer_pkcs8_file` at the new key and restart it. New
   heads use the new key. `Signer::load` refuses a key the set does not install.
3. Remove the old key only when nothing that must verify depends on it alone.
   Re-sign retained archives first: request `authenticated_head(stream,
   Some(archive size))` and `Archive::recertify`. Keepers keep their ledgers, so
   any size can be re-signed while two members hold it.
4. A departed keeper's keys stay installed for as long as its signatures must
   verify, or until the affected archives are recertified by current members.
   Removing a compromised key invalidates everything only it co-signed, by design.

## Safety and limits

- Signing reads no clock or lease. A keeper signs only prefixes at or below its
  head, which are committed and immutable, so two honest signatures over one
  root are two independent witnesses of the committed history.
- A ledger fault (lost file, damaged record) costs availability on that keeper
  and is repaired by seeding. A sidecar I/O error refuses the Trim (`TimedOut`)
  rather than discarding unrecorded leaves.
- Operator minority recovery that rewinds a head would make earlier signatures
  describe a history the journal no longer holds. The writer-driven journal has
  no such path today; one must retire the key set's `journal` UUID when added.
- Cost: one SHA-256 per committed record on the keeper engine thread, one ledger
  append per changed stream per round, one data sync per Trim, and `O(size)` ledger
  reads to sign a size below the ledger's end or to build a path. Signing the
  current head uses the in-memory frontier.
- Pre-existing streams whose prefix was trimmed before the feature was enabled
  can never be certified: no keeper holds those leaves. Enable it before RTDB
  creates lineage streams.

## RTDB changes (not made on this branch)

Inventory of RTDB `origin/main` uses of `consensus::authenticated` and
`ConsensusJournal`'s authenticated methods, and their replacement. `J` is
`Arc<dyn stream_logkeeper::stream::authenticated::AuthenticatedJournal>`, in
practice a `StreamJournal` built from `Writer::with_authentication(keys)`.

| RTDB site | Today | Writer-driven |
| --- | --- | --- |
| `journal-logkeeper/src/lib.rs` | re-exports `consensus::{ConsensusJournal, JournalConfig, authenticated}`; `connect_consensus` | re-export `stream::authenticated`; add `StreamJournal::connect_authenticated(url, credentials, deadline, keys: KeeperKeys)` and forward the `AuthenticatedJournal` methods to the inner `Writer` |
| `db/src/lib.rs:14`, `node/src/serving.rs:11` | re-export `CatalogRoot` | re-export `KeeperKeys` (and `Uuid` journal ids) |
| `db/src/journal.rs` `authenticated_journal: Option<Arc<ConsensusJournal>>`, `with_authenticated_journal` | concrete consensus handle | `Option<J>` |
| `db/src/journal.rs:227` create path | `require_authenticated` → `NotFound` → `create_authenticated` | `create(stream)` then `require_authenticated`; keep the `Unsupported` anomaly text, reworded to "the application keepers must keep authenticated history" |
| `db/src/multi/backup.rs` `AuthenticatedCut { head, catalog_root }` | consensus `Head` + root | `{ head: authenticated::Head }`; `matches` checks `head.valid()`, `head.journal != nil`, stream, size |
| `backup.rs` `InstallationAnchor { catalog, catalog_root, position }` | catalog id + root | `{ journal: Uuid, position }`; `is_in` compares `cut.head.journal` |
| `backup.rs` `archive_cut`, `BackupHeader::archive`, `Archive::read_from` | consensus archive | `authenticated::Archive::read_from` (magic `LKSARCH1`); new backup header markers so old consensus backups still parse with the consensus reader |
| `backup.rs` `lineage_archive(bytes, CatalogRoot)` | `archive.verify(root)` | `lineage_archive(bytes, &KeeperKeys)` → `archive.verify(keys)` |
| `backup.rs` `PortableBackup::verify` | self-consistency via `history.genesis.root()` | takes the source journal's `&KeeperKeys`; a backup is accepted only if its archive verifies against them |
| `backup.rs:296` backup creation | `journal.authenticated_archive(stream, Some(lsn))`, `archive.verify(root)` | same call on `J`; `archive.verify(J.keys())` |
| `backup.rs:448` restore anchor | `journal.catalog_history()` → `genesis.catalog`, `genesis.root()` | `J.keys().journal` |
| `backup.rs:667` `has_authentication` | `require_authenticated`: `Unsupported` → false | unchanged semantics on `J` |
| `db/src/multi/timed_store.rs` `TimedStoreAppend.application_root: CatalogRoot` | `catalog_history()` + `history.verify(root)`; commitment `catalog = genesis.catalog` | `application_journal: Uuid`; require `J.keys().journal == application_journal` after `require_authenticated`; commitment `catalog = J.keys().journal` |
| `flight-sql/src/v1/store/timed_append.rs:181` | 32-byte `application_root` | 16-byte `application_journal` (wire field change) |
| `server/src/multi/activation.rs` `authenticated_journal`, `bootstrap`, `supports_lineage` | `require_authenticated` / `create_authenticated` / `create_immutable` | `Option<J>`; `create` then `require_authenticated`; `Unsupported` still means no lineage |
| `activation/journal_custody.rs` `KeeperJournal` | `ConsensusJournal::new(credentials, JournalConfig)`; binding hashes `(catalog, catalog_voters, keepers)` | `StreamJournal::connect_authenticated`; binding hashes the journal URL entries and `KeeperKeys::digest()`. Its `CheckpointCustody` holds are a separate consensus feature and stay out of scope |
| `activation/history.rs:115` `publish_lineage_floor` | `authenticated_head` → `(SignedHead, CatalogHistory)`; `LineageFloor { source_root, source_head }` | `authenticated_head` → `SignedHead`; `LineageFloor { source_head }` (journal inside the head) |
| `activation/recovery.rs:611-630` | `authenticated_head(stream, Some(end))`, `head.verify(root, &history)` | `authenticated_head(stream, Some(end))`, `head.verify(J.keys())`; `AuthenticatedCut { head }` |
| `activation/lineage.rs` `LineageSegment { source_catalog, source_root, source_head }` | consensus `Head` in the digest | `{ source_journal, source_head }` with writer-driven `Head::statement()`; bump the digest domain to `lineage-segment/v2` |
| `lineage.rs` `PublicationProof.control_inclusion: Inclusion`, `verify(.., control_root)` | consensus `Inclusion::verify(root)` | writer-driven `Inclusion::verify(control_keys)` |
| `lineage.rs` `Authorization { catalog, timing: Timing }`, `verify_settlement(.., control_root, application_root, ..)` | compares `leaf.timing` and `leaf.quorum_durable_upper_micros < cutoff` | `journal` instead of `catalog`; compare `(exclusive_cutoff_micros, receiver_certificate_sha256)` of `leaf.timing`; capture when `timing.quorum_sync_upper_micros < cutoff` (already implied by `Leaf::valid`); take `&KeeperKeys` for both journals and require distinct `journal` ids and disjoint keeper keys for independence |
| `activation/operator/settlement.rs` CLI | `--application-root HEX --control-root HEX` | `--application-keys FILE --control-keys FILE` (`KeeperKeys` JSON) |
| tests: `server/src/multi.rs:2600,2643`, `recovery.rs:908-1013`, `timed_store_flight_tests.rs`, `lineage/tests.rs` | `catalog_history().genesis.root()`, consensus archives | build a key set from the local keepers' signers; use `J.keys()` |

RTDB deployment adds a `journal_keys_file` (the same `KeeperKeys` JSON the keepers
mount) next to `journal_url`, and switches `journal_url` to the named form with
spares from `writer-driven-repair.md`.

## Logkeeper deployment

Keeper config gains:

```json
"authenticated": { "signer_pkcs8_file": "/etc/logkeeper/history.pk8", "keys_file": "/etc/logkeeper/keeper-keys.json" }
```

`keeper-keys.json`:

```json
{ "journal": "UUID", "keepers": [ { "identity": "UUID", "keys": [[32 bytes]] } ] }
```

## Tests on this branch (unrun)

`stream::authenticated::tests`: tree and frontier agree on every prefix; two or
three ensemble signatures verify; under-quorum, duplicate, outsider, extra,
forged, truncated, relabelled and foreign-journal signatures are refused; key-set
validation; archive framing and offline inclusion; a late timed leaf is refused;
proofs across a replacement (including a forked history and retiring the replaced
keeper with recertification); a key rotation. `keeper::tests::authenticated`:
two members certify after trim and restart; a replacement keeper refuses forged
and under-quorum seeds and signs after a two-page verified seed. `keeper::ledger`:
leaf record framing. Codec round trips cover the new request and reply.

The repairer seeds moved streams: `repair::seed_repaired` binds each
`Outcome::Repaired` stream to its new ensemble and calls `seed_authenticated`, and
`logkeeper repair` runs it after every pass when its config sets `keys_file`.
`keeper::tests::authenticated::the_repairer_seeds_the_spares_ledger_after_moving_a_trimmed_stream`
covers it end to end. A repairer that crashes between the move and the seed leaves
the spare unseeded; later passes no longer list the stream, so only
`authenticated_head` (which seeds a `Missing` member once two others certify) or
an explicit `seed_authenticated` repairs it.

Open work: writer-level tests through `MemoryJournal`-style transports, a ledger
cache bound and off-thread proof building, and TLA+/Verus coverage of the
signing rule (sign only at or below the local head).
