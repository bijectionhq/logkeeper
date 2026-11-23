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
| C3 | Both | D02 erasure by key-generation rotation | Landed: `RotateKey` with generations kept through vacancy (A474-A475), generation-bound sealing and `rtdb/erased-under-view` (A476), and an RTDB erasure coordinator behind an explicit custody interface with native fixtures (A494). Open: exact-head clean closure and successor rewrite (A477, A494), authenticated evidence for every crash-selectable slot (A495), and a qualified atomic deadline authority (A496). |
| C4 | RTDB | Reclamation inside the current writer's prefix | Landed: installed deletes become durable reclamation candidates, and old offloaded payloads are nominated (A490). Physical removal inside a live prefix needs an exact-object withdrawal fence in Logkeeper and RTDB reader drains (A491-A492). |
| C5 | RTDB | Production typed closure and conformance replay | Landed in RTDB `e7e429626b` with the Lean composition `e6b5c5ff91`. The closure is not yet used by reclamation or checkpoint custody. |
| C6 | RTDB | Recovery at a cut inside a pending block | Reduced. RTDB roots sit at block boundaries, and held records after a boundary belong to the next block, so recovery at any cut is the root plus the suffix through that cut (Study 110's closure). Under D01 and D04 no self-contained image at an arbitrary cut is required; forks and exports at a basis already use base and suffix replay (`find_held_publication`). Source inspection at RTDB `fd3d6dcb32`: the published cut is the boundary plus one (`journal/hosted.rs:380-388`) and `retain_selected` trims only through it (`:563-573`). A proof against the driver remains. |
| C7 | Both | Worker disposal and dead workers blocking trim | Landed: the serving lease and per-read check, the operator command, and automatic custodian disposal from a bounded withdrawn-hold-owner query (Logkeeper `a5d21eb`, A478, A493). |
| C8 | Both | Maintenance lane liveness | Landed. RTDB `2144d3eae3` takes installed terms from the grant, promotes after an empty read and appends no claim. Tests show no maintenance charge across six replacements, and two mutations fail them. |
| C9 | Logkeeper | Open premises | Media stabilization on reopen and transitive barrier verification keys landed, with five Lean theorems in `Logkeeper/Premises.lean` (A479-A480). Provider disposition and per-volume peak funding stay environment contracts (A481-A482). |
| C10 | Both | Commit path refinement (RTDB W3) using `Logkeeper.Protocol` receipts as the premise | Partly in `RecoveryComposition`. |
| C11 | RTDB | Bypass audit (D05) | Mixed cells reserve installed UUIDs, and node controls refuse installed names (A483-A484). See RTDB `verification/redesign/installed-journal-bypass.md`. Installed fork and export remain open (A485). |
| C12 | Both | Independence and readiness | All 15 mechanisms break at their checked reference boundary, with four D01 mechanisms retired. See [mechanism independence](mechanism-independence.md) and [readiness](readiness.md) (A486-A489). Production-stack enforcement of each mechanism remains open. |

## Landing

Logkeeper `main` carries the implementation at `895bc30`, and RTDB `main` pins it from `6475f29e27`.
RTDB's crates `rtdb-replication` and `rtdb-multi` passed their full suites locally before the final rebase.
At the push, RTDB `main` did not compile because of unrelated peer commits in `rtdb-tx`.

## Exact-object withdrawal (W1)

Ordered appends and checkpoint preparations may declare a complete, canonical list of immutable object names.
The record debit includes its reference list.
The preparation retains its references through publication and through settlement of any old root.
A read hold retains its checkpoint and replay interval, so the same reference check covers reads.
Opaque legacy dependencies block withdrawal until the corresponding roots, preparations, and records retire.
After the first fence, an opaque append or preparation is refused.

A custodian can fence an unreferenced name and bind the decision to an exact provider version.
New references to the name are then refused, including references issued before the fence and delivered afterward.
The same exact withdrawal returns the original fence and its decision coordinates after request expiry.
Snapshot compaction and cohort repair carry the reference lists and fences.
For voter groups, half of the prefix space above existing data and control reservations, capped at 2 MiB, funds the object control rows.
A full reservation refuses further rows.
Fences have stream lifetime.
The physical custodian must independently establish that earlier I/O has drained and that the provider effect matches the version named by the receipt.

`Logkeeper.ObjectWithdrawal` models one immutable object, two admission states and four reference roles.
It proves separation after an arbitrary modeled step and constructs a reachable fence.
The negative control permits a suffix acquisition after that fence and witnesses a violation.
The model assumes exact references and recovery of the chosen state and does not verify the Rust codec, provider or RTDB projection.
