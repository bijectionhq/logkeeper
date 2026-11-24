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
| Conformance | Recorded traces, native tests | `run_prefix_traces.py`: five fixed traces and 24 seeded fault schedules, with four trace controls | Installed-journal and erasure tests (RTDB `main` has 28 upstream failing tests, all also failing without our changes) |
| Verus–Lean link | `verification/link/run.py`, `run_ordered_correspondence.py` | Kernel-checked equivalences for selected live Verus definitions, three link controls and 52 concrete correspondence cases | README correspondence only |

## Logkeeper

| ID | Property | Status | Evidence | What remains |
| --- | --- | --- | --- | --- |
| L1 | Writer and history safety | Shipped-partial | `ordered_writer`, `ordered_admission`, and G1's append-commit and vacancy projections in `ordered_reducer` | Connect the concrete authority and append guards, computed cut and charge, and returned receipt through `State::apply` |
| L2 | Exact receipts | Shipped-partial | `ordered_receipt`, PM receipt scope, and G1's request admission and paired receipt/expiry updates in `ordered_reducer` | Connect position, time, placement, nonce, hash, expiry traversal, dispatch and the exact constructed receipt |
| L3 | Codec canonicality | Shipped-partial | `ordered_codec`, `object_name_codec`, `voter_slot_header`, `voter_transport`. PL3c rejects the three compact-image aliases under the existing tag. Lean and Verus name the admissible domains. | Whole-message typed left inverses, `Bytes` cursor composition and production `encode(decode(b)) = b` |
| L4 | Decoded image satisfies the reducer invariant | Shipped-partial (prior defect fixed by PL3c) | `compact_image` checks unique receipt positions, receipt partition and expiry index. Lean `ReducerInv` states the target semantic invariant. | Establish the complete decode projection, including parser loops, hold/withdrawal joins, roster and record accounting, and global reference coverage |
| L5 | Trim safety and credit | Shipped-verified | `ordered_trim` checks the live-hold scan, checkpoint bound, removed prefix and credits per class | Establish the adapter's exact cut and accounting inputs from the full reducer state |
| L6 | Budgets | Shipped-verified | `ordered_budgets`, G1's paid append and funding projections, and M08 independence | Full-state funding establishment and a reachable funded counterexample for the retained guard alone |
| L7 | Object withdrawal fence | Shipped-verified | `object_withdrawal` checks root and record traversal and the admission and fence decisions. G1 checks paid fresh-fence insertion. Lean `ObjectWithdrawal` covers traces under an exact `Carries` premise. | Concrete reference projection, per-row membership and opaque name completeness, byte-level compaction and repair, and RTDB R7 physical drain |
| L8 | Serving lease and disposal | Shipped-verified | `ordered_serving_lease`, `ordered_lease_reducer` (`LeaseRead` and induction over modeled lease and hold steps). A successful expiry disposal attests to the absence of custody for that identity. | Actual `State::apply` dispatch and owner-map projection, with the clock-drift premise |
| L9 | Rotation guard | Shipped-verified | `ordered_rotation` and `ordered_checkpoint` check the exact incumbent, head and preparation, successor generation and old-history floor | Whole-arm sequencing and old-root updates, payload cleanliness and physical key revocation |
| L10 | Mirrored voter media | Shipped-partial | `mirrored_voter_media` checks validation, selection and mirror sequencing under a single-tear sync premise | G3 filesystem crash refinement and the protocol's rank-monotonicity premise |
| L11 | Prefix agreement | Shipped-partial | `prefix_agreement` local decisions. G2 proves the arbitrary-trace `AsyncGroup` model refines the prefix ledger and durable acceptor, with conditional exact-image repair and seeded native conformance. | Native simulation through dispatch, receive and cancellation, issue and replay, sync and reopen, and repair authority |
| L12 | Signatures | Shipped-verified under premise | `receipt_signatures` checks exact invocation and receipt scope, transitive verification-key retention and immediate predecessor repair authority | Ed25519/SHA-256 and same-destination-manifest premises |
| L13 | Rotation slot evidence | Shipped-verified | `rotation_slot_evidence` and the shared prefix-vote recorder check a strict majority of distinct configured voters and both exact slot attestations | Peer authentication and physical readback qualification |
| L14 | **Whole-reducer refinement** | Shipped-partial | G1's Lean `Reducer` models all 25 command variants and proves invariant preservation and reference projections. Verus covers local projections for `Append`, `Vacate`, `FundWindow`, `LeaseRead`, `WithdrawObject` and request bookkeeping. | Zero complete `State::apply` simulations. Prove the whole-state abstraction, envelope, all dispatch and receipt projections, and invariant establishment from fresh and decoded images. |
| L15 | **Verus–Lean mechanical link** | Shipped-partial | G4 regenerates selected predicates from live Verus sources and checks their named Lean equivalences and standard axioms. The [correspondence inventory](link/inventory.md) lists each binding. | Remaining codecs, signature and sync/media predicates, and full transition projections. The translator and representation maps are trusted. |
| L16 | **Decoded image is an authentic chosen history** | Open | The compact-image laws check projected invariants. G2 traces reconstruct observed compacted history from recorded frames and the history commitment. | Universal projection from an accepted native image to an authenticated chosen trace, including the archived prefix and reducer invariant |

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
| G | L14 reducer, L11 async group, L10 crash model, L15 link | G1, G2 and G4 integrated. G3 pending. |
| H | L16, R7 defect, R8, R11, R14, X1 remaining hypotheses, X4 runtime premises, codec whole messages | Proposed |
