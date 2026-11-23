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
| C3 | Both | D02: journal key generations aligned with an ordered clean checkpoint; erasure commit arms revocation; replay tolerates revoked generations | [Study 112](112-erasure-rotation/report.md) fixes the commit rule: every selectable slot clean, generation carried on the grant, held views kept until the deadline. RTDB has none of the machinery yet: one deployment key, logical `ERASE`, fail-closed replay. Implementation needs a Logkeeper grant generation field and RTDB's R7 successor construction and key service. |
| C4 | RTDB | Reclaim serving-prefix garbage, offloaded objects and old writer-epoch prefixes under journal custody | New finding. The installed `ServingStore::delete` drops every delete (`journal/hosted/storage.rs:423-428`), so installed storage grows without bound. No RTDB deletion can harm a Logkeeper holder today. Reclamation must use the typed closure (C5) and Logkeeper holds. |
| C5 | RTDB | Production typed closure and conformance replay | Landed in RTDB `e7e429626b` with the Lean composition `e6b5c5ff91`. The closure is not yet used by reclamation or checkpoint custody. |
| C6 | RTDB | Recovery at a cut inside a pending block | Reduced. RTDB roots sit at block boundaries, and held records after a boundary belong to the next block, so recovery at any cut is the root plus the suffix through that cut (Study 110's closure). Under D01 and D04 no self-contained image at an arbitrary cut is required; forks and exports at a basis already use base and suffix replay (`find_held_publication`). Source inspection at RTDB `fd3d6dcb32`: the published cut is the boundary plus one (`journal/hosted.rs:380-388`) and `retain_selected` trims only through it (`:563-573`). A proof against the driver remains. |
| C7 | Both | Worker disposal and dead workers blocking trim | Landed. Logkeeper `895bc30` adds journal time, `Lease` and `DisposeExpired`. RTDB `41b05aea15` checks the lease before every worker read. Remaining: an operator or custodian task that issues `DisposeExpired`. |
| C8 | Both | Maintenance lane liveness | Landed. RTDB `2144d3eae3` takes installed terms from the grant, promotes after an empty read and appends no claim. Tests show no maintenance charge across six replacements, and two mutations fail them. |
| C9 | Logkeeper | Authenticated wire framing, signer rotation, durable receipt recovery, provider disposition, peak capacity | Open premises. |
| C10 | Both | Commit path refinement (RTDB W3) using `Logkeeper.Protocol` receipts as the premise | Partly in `RecoveryComposition`. |
| C11 | Both | Bypass audit: no directory path serves an installed deployment (D05) | Not started. |
| C12 | Both | Mechanism independence and a combined readiness matrix | Not started. |

## Landing

Logkeeper `main` carries the implementation at `895bc30`, and RTDB `main` pins it from `6475f29e27`.
RTDB's crates `rtdb-replication` and `rtdb-multi` passed their full suites locally before the final rebase.
At the push, RTDB `main` did not compile because of unrelated peer commits in `rtdb-tx`.
