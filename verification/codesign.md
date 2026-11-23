# RTDB Multi and Logkeeper co-design

2026-11-23

This plan joins the Logkeeper design studies, the Logkeeper implementation and its Lean package, and RTDB's integration and verification programme into one contract.
The owner decisions are [D01–D06](requirements.md#owner-decisions--2026-11-23).
RTDB's own decisions and workstreams are in RTDB's `verification/PROGRAMME.md`.

## Evidence bodies

| Body | Location | Role |
| --- | --- | --- |
| Design studies 01–110 | `verification/NN-*` in this repository | Bounded comparisons, controls and design-level proofs |
| Logkeeper Lean package | `verification/lean/Logkeeper` | The shared reference that RTDB imports |
| Logkeeper implementation | `src/ordered/*`, Verus harness in `verification/verus` | Ordered journal, voter repair, custodian checkpoint and trim |
| RTDB integration | RTDB `rust/crates/multi/src/journal`, `dev/doc/rtdb-multi-installed-journal.md` | Installed-journal worker, custodian and gateway |
| RTDB proofs | RTDB `verification/multi`, `verification/PROGRAMME.md` W1–W9 | Composition with `Logkeeper.Protocol` and RTDB-side refinement |

## Shared interfaces in Lean

| Interface | Logkeeper module | RTDB instance |
| --- | --- | --- |
| Exact chosen append and receipt reissue across voter repair | `Logkeeper.Protocol` | `compose/RecoveryComposition.lean` |
| Recovery certificate over opaque dependencies | `Logkeeper.RecoveryCertificate` | `lean/ReplayClosure.lean` with `compose/ReplayCertificate.lean` |

`ReplayCertificate` proves that a ready certificate covers every read of any reachable typed replay under one-AZ loss.
Its premises are the decoder projection, the digest-bound adopted roots, and the provider survival contract.

## Workstreams

| ID | Side | Work | State |
| --- | --- | --- | --- |
| C1 | Both | Bring the design onto main and port shared results into the Lean package | Studies imported. Recovery certificate shared and instantiated by RTDB. |
| C2 | Both | D01: retry reads as fresh admissions | Landed. Logkeeper `895bc30` removes exact read reissue and adds `ReleaseRead`. RTDB `76f4ad2189` issues fresh barriers and releases lost reads by identity. |
| C3 | Both | D02 erasure by key-generation rotation | Logkeeper `RotateKey` at an exact published head, with the generation carried on grants and kept through vacancy (A474-A475; formats LKBASE05, codec v5, LKAPPC08, LKORV004, LKORPC02). RTDB seals installed records by grant key generation and reports `rtdb/erased-under-view` for a revoked generation (A476). Open: clean successor construction at a quiesced cut (A477), the slot-evidence coordinator, held-view deadlines, and offloaded and archive objects. |
| C4 | RTDB | Reclaim serving-prefix garbage, offloaded objects and old writer-epoch prefixes under journal custody | New finding. The installed `ServingStore::delete` drops every delete (`journal/hosted/storage.rs:423-428`), so installed storage grows without bound. No RTDB deletion can harm a Logkeeper holder today. Reclamation must use the typed closure (C5) and Logkeeper holds. |
| C5 | RTDB | Production typed closure and conformance replay | Landed in RTDB `e7e429626b` with the Lean composition `e6b5c5ff91`. The closure is not yet used by reclamation or checkpoint custody. |
| C6 | RTDB | Recovery at a cut inside a pending block | Reduced. RTDB roots sit at block boundaries, and held records after a boundary belong to the next block, so recovery at any cut is the root plus the suffix through that cut (Study 110's closure). Under D01 and D04 no self-contained image at an arbitrary cut is required; forks and exports at a basis already use base and suffix replay (`find_held_publication`). Source inspection at RTDB `fd3d6dcb32`: the published cut is the boundary plus one (`journal/hosted.rs:380-388`) and `retain_selected` trims only through it (`:563-573`). A proof against the driver remains. |
| C7 | Both | Worker disposal and dead workers blocking trim | Lease and per-read check landed. RTDB adds the operator command `ordered-dispose-expired-worker`. Automatic custodian disposal needs a Logkeeper view of withdrawn hold owners (A478). |
| C8 | Both | Maintenance lane liveness | Landed. RTDB `2144d3eae3` takes installed terms from the grant, promotes after an empty read and appends no claim. Tests show no maintenance charge across six replacements, and two mutations fail them. |
| C9 | Logkeeper | Open premises | Media stabilization on reopen and transitive barrier verification keys landed, with five Lean theorems in `Logkeeper/Premises.lean` (A479-A480). Provider disposition and per-volume peak funding stay environment contracts (A481-A482). |
| C10 | Both | Commit path refinement (RTDB W3) using `Logkeeper.Protocol` receipts as the premise | Partly in `RecoveryComposition`. |
| C11 | RTDB | Bypass audit (D05) | Mixed cells reserve installed UUIDs, and node controls refuse installed names (A483-A484). See RTDB `verification/redesign/installed-journal-bypass.md`. Installed fork and export remain open (A485). |
| C12 | Both | Independence and readiness | All 15 mechanisms break at their checked reference boundary, with four D01 mechanisms retired. See [mechanism independence](mechanism-independence.md) and [readiness](readiness.md) (A486-A489). Production-stack enforcement of each mechanism remains open. |

## Landing

Logkeeper `main` carries the implementation at `895bc30`, and RTDB `main` pins it from `6475f29e27`.
RTDB's crates `rtdb-replication` and `rtdb-multi` passed their full suites locally before the final rebase.
At the push, RTDB `main` did not compile because of unrelated peer commits in `rtdb-tx`.
