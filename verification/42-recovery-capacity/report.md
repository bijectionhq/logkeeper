# Study 42 report · Compose ranked recovery, custody, and capacity

2026-11-23

## Verdict

Before sealing, reserve final residency for the physical footprint of any eligible ranked cut.
Enforce that envelope at vote admission, including votes the learner has yet to see.
Also reserve enough staging space for the incumbent and its replacement to coexist.
Promotion spends the existing residency credit on the exact installed image.
It does not need a new ordinary admission.
The old candidate stays physically protected until the switch and charged until exact disposition.

## Bounded comparison

The TLC model has one handoff, competing ordinary allocations, a lagging learner, two staged images of the selected cut, and one restart.
The old-custodian outage stops disposition of the incumbent. Source evidence and target staging remain available in that case.
The model charges separate physical copies of the incumbent and replacement.
Promotion converts the exact staged image into a resident image in one accounting transition.

| Candidate or setting | Ordinary capacity / workspace / maximum cut | Distinct states | Checked result |
| --- | --- | ---: | --- |
| Full reservation, connected | 3 / 4 / 2 | 233 | Five safety laws, post-seal installation, and old workspace reclamation hold. |
| Full reservation, connected | 4 / 6 / 3 | 674 | The same laws hold at a larger bound. |
| Full reservation, old disposition unavailable | 3 / 4 / 2 | 167 | Five safety laws and post-seal installation hold. |
| Ordinary residency already exhausted | 3 / 4 / 2 | 6 | Five safety laws hold and the move stays unsealed. |

The safety laws cover capacity ceilings, reservation of the exact sealed cut, installation of that cut, continuing physical charges, and protection of the incumbent before the switch.
The post-seal property assumes fair staging and activation using reachable exact media and a target quorum.
Returning the old workspace also assumes that the original custodian can provide verified disposition.

| Amendment | Weakening | TLC evidence |
| --- | --- | --- |
| A161 | `accepted_over_envelope` | Accept a cut above the budget and then seal in four transitions. |
| A161 | `learned_cut` | Seal the learned image and omit an accepted suffix in three transitions. |
| A161 | Reserve the learned footprint | An eligible larger cut cannot spend the reserved credit. |
| A162 | Stage without residency | Ordinary admissions fill the pool before promotion and a sealed move stalls. |
| A162 | Lend workspace to ordinary work | An ordinary allocation holds the committed repair workspace forever. |
| A162 | `forget_credit` | Restart loses a promised credit in three transitions. |
| A162 | Charge promotion again | The already reserved pool is full, so an exact ready image cannot install. |
| A163 | Reserve space for one image | A full incumbent occupies the only workspace while its replacement needs an independent copy. |
| A163 | `erase_early` | Erase the required incumbent before the switch in four transitions. |
| A164 | `install_wrong_cut` | Publish the wrong cut in five transitions. |
| A165 | `drop_old_charge`, `release_on_timeout` | Installation or timeout loses the old physical charge in five or six transitions. |
| A165 | Old custodian unavailable | The handoff installs and the obsolete image's charge remains indefinitely. |

In eight transitions the full-capacity witness reserves space before the accepted cut grows beyond the learner, restarts after both images stage, and installs while the old custody remains charged.
A seven-transition witness returns the old workspace after verified stable absence.

## General proofs

Lean checked fourteen theorems using standard axioms only. [Proof source](RecoveryCapacity.lean)
Metered voter traces project to the existing scoped voter machine and keep every accepted vote inside the envelope.
The proof recovers the envelope of any ranked cut, including fallback to the installed basis.
Every trace of the handoff preserves ordinary capacity, protected workspace, and the original provider's custody laws.
The accepted incumbent stays present while the replacement is prepared.
Releasing its charge requires stable absence from the same custody state.

The composed acceptance proof runs a sealed move with a fully booked ordinary pool.
It builds both staging steps within the workspace and installs through the authorized target quorum.
It preserves the old provider state, derives the exact cut on a current recovery majority, and replays prior chosen outcomes.
Its projection advances the shared stream kernel to the successor with the exact installed history and preserved stream bounds.
The arithmetic proof rules out one full-image reservation when two disjoint maximal images must coexist.

Six Lean controls fail at their predicted proof sites when the model admits an unmetered vote, reserves only one image, installs a different cut, accepts an unrelated family, drops required media, or releases a charge without stable absence.

## Remaining obligations

The study models one concurrent handoff and one incumbent physical custody state.
Its footprint function abstracts exact serialized bytes and required dependencies.
The authorized target predicate and installed quorum carry the earlier authentication and durability premises.
The installation proof assumes the target can promote the same staged extents. A provider that must copy during promotion needs the additional peak space.
The result protects one already admitted move. Multiple moves and successive repairs still need aggregate ordinary, workspace, and disposal accounting per failure domain.
An inaccessible old custodian can continue to consume capacity needed by a later admission.

Apply [A161–A165](../amendments.md#study-42--2026-11-23).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner stores commands, settings, traces, and proof diagnostics in the ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/42-recovery-capacity/run.py
```
