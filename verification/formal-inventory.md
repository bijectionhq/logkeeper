# Formal verification inventory

2026-11-23

This inventory lists what should be machine-checked for RTDB Multi with Logkeeper. For each property it gives the claim, the current evidence and the proof we want.
It builds on the [readiness matrix](readiness.md), the [mechanism independence](mechanism-independence.md) report and RTDB's `verification/PROGRAMME.md`.

## Proof stack

| Layer | Tool | Role | Existing assets |
| --- | --- | --- | --- |
| Design models | TLC 2.19, Lean 4.35 | Bounded comparisons, negative controls and general theorems for each design decision | Studies 01–113 in this directory |
| Shared reference | Lean package `verification/lean/Logkeeper` | Definitions both repos import, plus theorems over arbitrary traces | `Kernel`, `PrefixAgreement`, `DurableAcceptor`, `JournalRefinement`, `Protocol`, `RecoveryCertificate`, `ObjectWithdrawal`, `SelectionFence`, `Premises` |
| RTDB composition | Lean `verification/multi` in RTDB | RTDB models instantiated against the shared reference | `RecoveryComposition`, `ReplayCertificate`, `ReplayClosure`, `OrderedJournal` and others |
| Production refinement | Verus, pinned at `0.2026.11.20.9da409b` with Z3 4.16 | Proofs over the shipped Rust functions, with declared mutation controls per area | RTDB: 58 areas. Logkeeper: `ordered_admission` only, never run. |
| Conformance | Native tests, recorded traces | Executable checks that tie production behavior to a model where a proof is out of reach | RTDB replay-closure conformance, the installed-journal acceptance tests, the Logkeeper acceptance tests |

A claim reaches **production-verified** status only when three things hold:
- a Verus proof over the shipped function is linked to a named Lean definition;
- each declared control fails at its named law;
- the model it refines has a general Lean theorem, or a stated TLC bound.

## Logkeeper

| ID | Property | Production code | Current evidence | Target proof | Priority |
| --- | --- | --- | --- | --- | --- |
| L1 | **Writer and history safety.** An append commits only under the current grant at exactly the next LSN. History is contiguous and irrevocable. A superseded grant can never append again. | `src/ordered.rs` `State::apply`, the `Append`, `Grant`, `Withdraw` and `PublishAndRotate` arms | Lean `Kernel` and `Protocol`; Study 68 weakenings; C12's next-LSN control; acceptance tests | Verus over each command arm, refining `Kernel` transitions through an abstraction function from `State` to the Lean state | P1 |
| L2 | **Exact receipts.** A positive receipt is recorded only after a successful applied outcome. Mutation retry is exact by fingerprint within the horizon, and reads are never replayed (D01). | `State::apply` retry path, `retained_receipt`, the fingerprint | Lean `same_chosen_append`; C12 controls; D01 tests | Verus on the receipt book and fingerprint matching, extending `ordered_admission` | P1 |
| L3 | **Codec canonicality.** `decode(encode(x)) = x`, and `decode` rejects every non-canonical or truncated input for command codec v6, decision frames with journal time, snapshot `LKBASE06`, wire `LKAPPC12`, voter media `LKORV005` and transport `LKORPC04`. | `src/ordered/codec.rs`, `codec/snapshot.rs`, `codec/service.rs`, `service/wire.rs`, `replication/disk.rs`, `replication/transport.rs` | Round-trip unit tests | Verus decoder proofs in the style of RTDB's `framing_decoders`, plus round-trip lemmas for the encoders | P1 |
| L4 | **Snapshot invariants.** A decoded compact image satisfies the reducer invariants: every hold has a retained receipt; leases, fences and references are bounded and consistent; key generation persists through vacancy. | `codec/snapshot.rs` validation (`read_leases`, hold and receipt checks) | Tests | Verus: decoder acceptance implies the `State` invariant used by L1 | P1 |
| L5 | **Trim safety and credit.** Trim never removes a record pinned by a live hold or needed after the selected checkpoint. Refunded bytes equal the removed records' charges, per class. | `Command::Trim`, `admission::pins_suffix` | Lean `trimCredit`; partial Verus `ordered_admission` | Verus over the trim arm with the pin and credit laws | P1 |
| L6 | **Maintenance and ordinary budgets.** Charged bytes, including object reference charges (W1), never exceed the funded window and the maintenance reserve. | `admission::debit`, append charge | Verus `ordered_admission` (not yet run) | Run and extend `ordered_admission` | P1 |
| L7 | **Object withdrawal fence (W1).** An object is either referenced, so withdrawal is refused, or fenced, so new references are refused. Fences survive compaction and repair. | `admit_object_references`, the `WithdrawObject` arm | Lean `ObjectWithdrawal`, one object; durable integration test | Lean generalization to many objects and to compaction; Verus over the admission and withdrawal arms | P1 |
| L8 | **Serving lease and disposal.** Journal time is monotone. A lease is issued only under the current grant. `DisposeExpired` succeeds only once time reaches the lease end plus drift. The withdrawn-owner query is exact and bounded. | `Lease`, `DisposeExpired`, `apply` time check, the withdrawn-owner query | Study 113 (TLC and Lean); tests | Verus over the guards; refine Study 113's `DisposalLease` | P2 |
| L9 | **Key rotation guard.** `PublishAndRotate` advances epoch and generation only for the exact incumbent and erasure preparation at the exact head. It publishes the clean checkpoint and closes fresh old-history admission in the same decision. The generation and erasure floor persist through vacancy. | `PublishAndRotate` arm | Study 112; two production mutations | Verus over the arm | P2 |
| L10 | **Mirrored voter media (W2).** A voter acknowledges a promise or accept only after both slots hold it. Selection after any single torn write never returns an image older than the last acknowledged one. | `replication/disk.rs` write and select | Lean `SelectionFence`; real-disk regression | Verus over the selection function and a sync-event state machine linked to `SelectionFence` | P2 |
| L11 | **Prefix agreement implementation.** The running group refines `PrefixAgreement` and `DurableAcceptor`: one chosen prefix per position across leader changes and repair. | `replication.rs` `choose`, accept, recovery, seal and install | Lean `PrefixAgreement`, `DurableAcceptor`, `JournalRefinement`, transfer theorem; Studies 25–27 and 106 | Trace validation: record executions in tests and check them against an executable form of the Lean or TLA model. Verus over the local accept rule. | P3 |
| L12 | **Receipt and barrier signatures.** The verifier accepts only an exact claim for the exact scope. Verification keys are retained transitively across rotation, and repair authority comes only from the immediate predecessor roster. | `daemon/sign.rs`, `daemon/repair.rs` | C9 Lean `Premises`; tests | Verus over the verifier logic with signature checking as an uninterpreted contract | P2 |
| L13 | **Rotation slot evidence (W2).** The signed evidence names a strict majority whose voters read and authenticated both images at the exact fence. | `replication.rs` evidence assembly, `codec/service.rs` | Lean `SelectionFence`; signed-evidence tests | Verus over the evidence assembly | P2 |

## RTDB Multi

| ID | Property | Production code | Current evidence | Target proof | Priority |
| --- | --- | --- | --- | --- | --- |
| R1 | **Typed replay closure.** Every object that replay of a base and an admitted suffix can read or reference is in `checkpoint_dependencies ∪ tail_dependencies`, including adopted catalogs, search runs and oversized payloads. | `replication/src/replay_closure.rs`, `format` `checkpoint_trie_files` | Lean `ReplayClosure` (Step soundness); conformance replay with a negative control | Verus over the enumeration, refining Lean `bodyKeys` and `baseKeys` with protobuf decoding as RTDB's existing Prost contract | P1 |
| R2 | **Fenced term admission.** With journal-fenced terms, promotion happens only after an empty read, at highest term plus one, starting at sequence 0, and a holder without the grant never leads. No record of a superseded term is applied. | `replication/src/admission.rs` `TermFence::admit`, driver promotion | Study 111; mutation-checked tests | Verus over `admit` and the promotion predicate, extending RTDB's `replica_admission` area | P1 |
| R3 | **Maintenance classification.** In fenced mode only boundaries and uploads are maintenance, so the lane stays within three records under any number of replacements. | `replication/src/logs.rs` classification | Lean `MaintenanceBound`; tests | Verus over the classifier, linked to `MaintenanceBound` | P1 |
| R4 | **Installed read admission.** Every byte read checks the serving lease on the monotonic clock. Each read is a fresh barrier. The set of unsettled reads stays bounded and settles only at or after the retry horizon. | `multi/src/journal/hosted/storage.rs` `ServingLease`, `journal/log.rs` `protect` and `settle_reads` | Tests | Verus over the lease state and the settle predicate with an abstract clock; TLA for the retry loop | P2 |
| R5 | **Erasure commit gate.** Commit requires a strict majority of signed slot evidence at the clean checkpoint and successor generation. The receipt and deadline form one durable decision. Operations check the deadline at admission and completion. | `journal/hosted/erasure.rs`, `keys/journal/deadline.rs` | Study 112; W4 TLA `JournalErasureDeadline`; nine evidence-fault tests; controls | Verus over `require_clean_slots` and the deadline predicates, linked to Study 112 and the W4 TLA model | P1 |
| R6 | **Generation-bound sealing.** A record opens only with its original grant's generation, and a revoked generation yields `rtdb/erased-under-view`, never plaintext. | `multi/src/keys/journal.rs`, `journal/log.rs` | Tests and controls | Verus over generation selection and the error mapping | P2 |
| R7 | **Exact reclamation.** A physical delete happens only after the Logkeeper fence, the reader-lease drain and an exact provider-version match. A lost reply reconciles from stable absence. | `journal/hosted/reclamation*.rs` | Tests and controls | Verus over the effect decision; TLA for lost-reply reconciliation | P2 |
| R8 | **Fork and export custody.** Holds persist until the destination publication is durable. A dependent fork stays in the source erasure domain, and an export is independent only after re-encryption. | `journal/hosted/copy.rs` | Acceptance test with controls | TLA model of hold, publish and withdraw; Verus over the release condition | P2 |
| R9 | **Bypass fences (D05).** No directory path acts on an installed deployment: reservation, control guards and pressure selection. | `directory/src/lib.rs`, `multi/src/agent.rs` guards | Audit; seven executed mutations (W6) | Verus over the guard predicates as a W7-style area | P2 |
| R10 | **Custodian ordering.** Disposal precedes trim, and trim never passes boundary plus one of the selected root (C6). | `journal/hosted.rs` `retain_selected`, `publish_checkpoint` | Source inspection; tests | Verus over the trim-target computation | P2 |
| R11 | **Clean successor rewrite.** The clean closure keeps exactly the surviving events and no erased ones, and references only newly produced members. | W3's rewrite producer | Native tests and controls | A Lean model of the rewrite as a filter over event sets, with a conformance check on real fixtures | P3 |
| R12 | **Commit path (RTDB W3).** Each RTDB acknowledgement corresponds to the same applied outcome after failover and replay. | `replication/src/driver.rs` read-back pipeline | Lean `RecoveryComposition` (receipt reissue) | Extend the composition to the driver's apply relation; Verus over read-back validation | P3 |

## Cross-system theorems

| ID | Theorem | Ingredients | Priority |
| --- | --- | --- | --- |
| X1 | **End-to-end durability and visibility.** A transaction RTDB acknowledges survives any single AZ loss, any number of writer replacements and voter repairs, and is visible after recovery, unless an erasure that admits it has committed (D02). | L1, L2, L10, L11, R1, R2, R12, `RecoveryCertificate` | P3 |
| X2 | **Refinement maps.** Abstraction functions from Logkeeper `State` and the RTDB driver state into the Lean reference, used by every Verus area's laws, with a check that the Verus spec functions and the Lean definitions agree. | All P1 items | P1 (foundation) |
| X3 | **Adapter contract.** Every command RTDB's adapter sends satisfies Logkeeper's preconditions: current grant, complete references, exact barrier identity. | `multi/src/journal.rs`, `journal/log.rs` | P2 |

## Premises stated, not proved

These are explicit environment assumptions, as in C9:
- cryptographic hash and signature security;
- file and directory sync semantics on the deployed filesystem;
- a bounded clock rate error (lease and deadline);
- independent failure of AZs;
- S3 conditional-write and versioning semantics;
- protobuf decoding, under RTDB's Prost contract;
- Tokio scheduling fairness for liveness.

Each premise names the qualification test that would discharge it in a deployment.

## Proposed passes

| Wave | Scope | Notes |
| --- | --- | --- |
| F0 | Verus toolchain at the pinned version; run Logkeeper's existing `ordered_admission`; add a Logkeeper `verification/verus` runner modeled on RTDB's `verification/run.py` | Prerequisite for everything else |
| F1 | X2, L1, L2, L3, L4, L5, L6, L7, R1, R2, R3, R5 | Highest value and tractable: pure decision functions and decoders |
| F2 | L8, L9, L10, L12, L13, R4, R6, R7, R8, R9, R10, X3 | Guards with abstract clocks, providers and crypto |
| F3 | L11, R11, R12, X1 | Protocol trace validation and the end-to-end theorem |
