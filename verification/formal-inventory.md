# Formal verification inventory

2026-11-24 (second edition; the first edition of 2026-11-23 set waves F0–F3)

This inventory lists what is machine-checked for RTDB Multi with Logkeeper, what is only modeled, and what remains.
It builds on the [readiness matrix](readiness.md), the [mechanism independence](mechanism-independence.md) report and RTDB's `verification/PROGRAMME.md`.

## Status vocabulary

| Status | Meaning |
| --- | --- |
| **Shipped-verified** | Verus proves the shipped Rust function against laws named after a Lean definition, and each control that mutates the shipped source fails at its declared law. |
| **Shipped-partial** | As above for the decisions named, while the whole operation (dispatch, async wiring, I/O) is source-inspected or test-covered only. |
| **Modeled** | General Lean theorem or bounded TLC result over a model; no production link. |
| **Premise** | Stated assumption, not proved. |
| **False / open defect** | A counterexample exists in shipped code. |

## Proof stack (2026-11-24)

| Layer | Tool | Logkeeper | RTDB |
| --- | --- | --- | --- |
| Shared and composed reference | Lean 4.35 | `verification/lean/Logkeeper`: 25+ modules, every runner passes, standard axioms only | `verification/multi`: 27 jobs, including `AcknowledgedRecovery`, `InstalledJournalProgress`, `InstalledRead`, `NativeAppend`, `ExactReclamation`, `InstalledErasureCommit` |
| Production refinement | Verus `0.2026.11.20.9da409b`, Z3 4.16 | 20+ areas, about 470 verified items, about 160 controls | 81 areas, including replay closure, replica admission, maintenance, directory bypass, retention, adapter, native acknowledgement, read selection, append projection, erasure commit, exact reclamation |
| Liveness | TLC 2.19 | Studies 111–113 | `InstalledJournalProgress.tla`: 9 temporal properties, 31 stall controls |
| Conformance | Recorded traces, native tests | `run_prefix_traces.py`: 658 events in 5 traces; 96 tests | Installed-journal and erasure tests (RTDB `main` has 28 upstream failing tests, all also failing without our changes) |
| Verus–Lean link | `run_ordered_correspondence.py` | 52 concrete agreeing cases | README correspondence only |

## Logkeeper

| ID | Property | Status | Evidence | What remains |
| --- | --- | --- | --- | --- |
| L1 | Writer and history safety | Shipped-partial | `ordered_writer`, `ordered_admission` | Whole `State::apply` refinement (G1) |
| L2 | Exact receipts | Shipped-partial | `ordered_receipt`, PM receipt scope | G1 |
| L3 | Codec canonicality | Shipped-partial | `ordered_codec`, `object_name_codec`, `voter_slot_header`, `voter_transport`; PL3c rejects the three accepted aliases; admissible domains named in Lean and Verus | Whole-message typed left inverses; `Bytes` cursor composition; production `encode(decode(b)) = b` |
| L4 | Decoded image satisfies the reducer invariant | Shipped-partial (was **false**, fixed by PL3c) | `compact_image`: unique receipt positions, receipt partition, expiry index | Parser-loop invariants, hold/withdrawal joins, roster and record accounting, global reference coverage |
| L5 | Trim safety and credit | Shipped-verified | `ordered_trim` | — |
| L6 | Budgets | Shipped-verified | `ordered_budgets`; M08 independence | Reachable funded counterexample for the retained guard alone |
| L7 | Object withdrawal fence | Shipped-verified | `object_withdrawal`, `ObjectWithdrawal` | Physical drain is RTDB R7 |
| L8 | Serving lease and disposal | Shipped-verified | `ordered_serving_lease`, `ordered_lease_reducer` (PL8b: `LeaseRead`, induction over every lease and hold step) | Bridge from `apply` dispatch (G1); clock-drift premise |
| L9 | Rotation guard | Shipped-verified | `ordered_rotation`, `ordered_checkpoint` | Payload cleanliness, physical key revocation |
| L10 | Mirrored voter media | Shipped-partial | `mirrored_voter_media` under a single-tear sync premise | Filesystem crash model (G3) |
| L11 | Prefix agreement | Shipped-partial | `prefix_agreement` decisions; bounded trace validation | Asynchronous refinement for every execution (G2) |
| L12 | Signatures | Shipped-verified under premise | `receipt_signatures` | Ed25519/SHA-256 premise; same-manifest premise |
| L13 | Rotation slot evidence | Shipped-verified | `rotation_slot_evidence` | Peer authentication premise |
| L14 | **Whole-reducer refinement** (new) | Open | — | G1 |
| L15 | **Verus–Lean mechanical link** (new) | Open | 52 concrete cases | G4 |
| L16 | **Decoded image is an authentic chosen history** (new) | Open | — | Projection from a compact image back to a chosen trace |

## RTDB Multi

| ID | Property | Status | Evidence | What remains |
| --- | --- | --- | --- | --- |
| R1 | Typed replay closure | Shipped-verified | `replay_closure` | Append projection completeness is a premise |
| R2 | Fenced term admission | Shipped-verified | `replica_admission`, `recovery_promotion::may_promote` | Async authority between observation and ordering |
| R3 | Maintenance classification | Shipped-verified | `maintenance_class`, Study 111 bound | Fenced receiver-terminal settlement still charged to maintenance (accounting gap) |
| R4 | Installed read admission | Shipped-verified | `installed_read_selection` (PX3) | Frozen reads, restored tokens and audience paths use separate selection |
| R5 | Erasure commit gate | Shipped-partial | `erasure_commit`: 31 items, 11 controls; `InstalledErasureCommit` | Async census and provider drain refinement; enforcing custody authority qualification |
| R6 | Generation-bound sealing | Shipped-verified | F2 PR4 | — |
| R7 | Exact reclamation | Shipped-partial, **open defect** | `exact_reclamation`, `ExactReclamation` | Expiry disposal can release holds before detached provider I/O completes (`io_region.rs:282`); hosted preflight skips a visible replacement |
| R8 | Fork and export custody | Open | Peer fork admissions on main | Exact-basis copy (W5) needs broker admission through durable destination publication |
| R9 | Bypass fences | Shipped-verified | `installed_directory_bypass` | Backend wiring source-reviewed |
| R10 | Custodian ordering | Shipped-verified | `installed_custodian_retention` | — |
| R11 | Clean successor rewrite | Superseded by peers' survivor checkpoint; unproved | — | Prove peers' survivor producer keeps exactly the surviving events |
| R12 | Native acknowledgement | Shipped-verified | `native_acknowledgement` | Chosen-record identity, detached delivery, Arrow effect semantics |
| R13 | **Local raw-object reclamation** (new) | Open design | — | Shared durable inventory and drain for loose and packed slot aliases |
| R14 | **Driver refinement** (new) | Open | — | Replication driver and appender async refinement, analogous to L14 |

## Cross-system theorems

| ID | Theorem | Status | What remains |
| --- | --- | --- | --- |
| X1 | Acknowledged transaction survives one-AZ loss, writer replacement and repair, and is visible at a fresh read | Modeled with production-bound read, cut, query and acknowledgement hypotheses (PX1, PX3) | `initial : RecordedAppend` chosen-result projection, `journalAgreesAtReadCut`, publication meaning, checkpoint and suffix fidelity, SQL semantics |
| X2 | Refinement maps | Partial | L14, R14, L15 |
| X3 | Adapter contract | Shipped-verified | Semantic completeness of the append projection |
| X4 | **Progress** (new) | Modeled (PX2, bounded TLC) | Tie fairness to Tokio and retry loops; repeated interrupted attempts; sustained throughput |

## Premises stated, not proved

Cryptographic hash and signature security; filesystem and directory sync semantics (being narrowed by G3); bounded clock rate error; independent AZ failure; S3 conditional-write and versioning; Prost decoding; Tokio fairness; authenticated stable voter identity; same destination manifest at seal and install; enforcing custody authority for fixed-deadline erasure; provider inventory completeness.

## Waves

| Wave | Scope | State |
| --- | --- | --- |
| F0–F3 | Toolchain, decision proofs, protocol traces, X1 | Landed |
| F4 | L3/L4 fixes, `LeaseRead`, R5, R7, X1 read bindings, wave 3 triage | Landed 2026-11-24 |
| G | L14 reducer, L11 async group, L10 crash model, L15 link | Running |
| H | L16, R7 defect, R8, R11, R14, X1 remaining hypotheses, X4 runtime premises, codec whole messages | Proposed |
