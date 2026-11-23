# Study 10 report · Cancelling a prepared move

2026-11-22

## Verdict

A cancellation request becomes effective at the source's ordered decision, which binds the exact reservation nonce.
If abort commits first, the source cannot seal against that reservation, and the target can reclaim it using the abort receipt.
If seal commits first, complete the transfer and consume the slot.
An isolated target must keep unresolved custody and admission state when it lacks either proof.

## Properties and comparison

Both safety invariants and eventual release or installation with a stable source link hold at the checked bounds.
TLC explored 34 states with two nonces and 66 with four.
The stronger liveness claim without a source-link premise fails with two nonces.

| Amendment | Mutation | Shortest counterexample |
| --- | --- | --- |
| A29 | `ignore_abort` | Prepare → request cancel → commit source abort → seal against the aborted nonce. Four transitions. |
| A30 | `abort_by_stream` | Abort and reclaim the first slot → prepare and seal against a second slot → use the old abort to discard the second slot. Seven transitions. |
| A30 | `no_source_evidence` | Prepare → seal → partition → let the isolated target guess that the slot can be reclaimed. Four transitions. |

The temporal counterexample leaves requested release unfulfilled during a source-link outage.
A positive seven-transition trace cancels the first slot, issues a fresh reservation, and uses it to complete a move.

## Acceptance program

A caller requests cancellation for the exact prepared reservation.
The source returns abort evidence, or the already-sealed outcome.
The target validates the nonce on retry.
Either it frees the slot using the abort evidence or it installs the authorized successor.
Pending is a valid response while the needed evidence is unreachable.

## Residue

This execution model tests the cancellation rule at one pair of groups.
It neither verifies signed transport and receipt storage nor bounds how long unresolved slot reservations occupy the real fleet.
Quota sizing and competing-successor reclamation require broader refinement.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java python3 verification/10-cancel-move/run.py
```
