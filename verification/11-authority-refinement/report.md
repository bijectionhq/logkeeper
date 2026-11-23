# Study 11 report · Placement ownership and writer identity

2026-11-22

## Verdict

A new writer grant after seal reintroduces a directory dependency into portable handoff.
The directory can disappear after the move is authorized, leaving both groups healthy and the stream unable to activate.
A move should carry the exact holder and writer epoch committed at seal and change only the placement generation and group.
Installing a different holder remains a separate ordered, higher-epoch fence.

The concrete Lean model of group-local rows and one-use reservations now has a checked forward simulation to the actual logical reference kernel.
Every finite trace of its modeled transitions has a corresponding reference trace.

## Properties and comparison

Both designs pass the three finite safety laws.
The carrying design also satisfies eventual completion after preparation with the stated weak fairness.
The fresh-grant design fails that liveness claim.
Its counterexample prepares the move, loses the directory, seals the source, and stays in a state where the fresh grant can never be issued.

| LSN bound | New grant after seal | Carry writer from seal |
| --- | ---: | ---: |
| Two records | 6,346 states | 5,176 states |
| Three records | 25,362 states | 21,232 states |

The comparison assumes the sealed cut can reach the target and both modeled group quorums function.
The positive nine-transition witness moves after a holder change and appends on the target while the directory is down.

| Amendment | Mutation | Shortest counterexample |
| --- | --- | --- |
| A32 | `stale_prepare` | Prepare under holder 1 → fence to holder 2 → seal → install holder 1 from the preparation. Four transitions. |
| A32 | `replace_holder` | Prepare → seal → replace holder without advancing the epoch at activation. Three transitions. |
| A33 | `ignore_holder` | Stage under the wrong holder and commit. Two transitions. |
| A33 | `ignore_placement` | Stage under the wrong placement and commit. Two transitions. |
| A33 | `ignore_lsn` | Stage and commit a record, then stage a record at its occupied LSN and accept it. Four transitions. |

## General refinement proof

Lean checks nine reported theorems with only standard axioms.

| Theorems | Claim within the model |
| --- | --- |
| `step_refines`, `traces_refine` | A local dispatch, source seal, or destination install takes the matching reference step. A destination preparation stutters. The relation is preserved across any finite trace. |
| `reachable_writer_is_unique` | Reachable group states have at most one serving group for the stream. |
| `reachable_rows_preserve_logical_bounds` | Every serving projection has valid checkpoint, replay and retention bounds. |
| `observed_history_survives_move` | Two serving observations along a trace have prefix-related histories, even when all intervening moves complete at different groups. |
| `retired_world_cannot_reopen` | After a committed retirement no continuation, including replay of authentic old seals, can reopen a serving row. |
| `old_placement_grant_refused`, `previous_generation_refused` | The old source credential cannot append at the target. A generation mismatch also excludes a stale grant even after the physical group is reused. |
| `prepared_move_is_executable` | A valid source with a prepared target can seal and install the same writer at its exact cut without an extra grant or directory step. |

The proof relates every non-current certificate to a spent nonce.
Activation consumes the matching live slot atomically.
The certificate that can activate therefore has to be the one represented by the abstract sealed state.
The two Lean mutations fail the matching simulation obligations when the source row is left writable or when the target changes the holder.

## Residue

This is safety refinement for the modeled local state machines and certificate transitions.
Local durable consensus, target authentication, independent fault domains, and exact snapshot installation are premises.
The Lean trace model excludes reservation abort so far, which has a separate [bounded study](../10-cancel-move/report.md).
It also excludes message delivery over unbounded time and custody proofs at disposed media.
A healthy old holder can resume at the new placement.
An unavailable holder still needs normal RTDB failover or an already approved higher grant.
The handoff provides no new means of electing a holder.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/11-authority-refinement/run.py
```

The runner builds the two imported study modules, checks both Lean mutations and the baseline proof, then runs the pinned TLC comparison.
Configs, command lines, counterexamples and proof diagnostics are under `.results/`.
