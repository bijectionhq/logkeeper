# Study 15 report · Replay permit identity and composition

2026-11-22

## Verdict

Use a non-reused permit ID scoped to the stream incarnation.
An authenticated prepared envelope gives the holder a way to attempt admission.
Only the still-live matching reservation can become a hold.
An acknowledged close consumes either the pending reservation or the admitted hold under that exact ID.
The move image carries the live table and its issuance high-water mark.

## TLC results

All four invariants hold across 853 states with two permits and 10,504 states with three.
There are two possible replay starts, one source-to-target move, and a floor transition.
The eight-transition acceptance program opens the older hold, carries a prepared second permit across the move, selectively closes the older permit, and trims without invalidating the second.
A seven-transition witness closes a still-prepared permit at the source, moves, and observes explicit refusal of its delayed envelope at the target while another hold at the same LSN remains valid.

| Amendment | Mutation | Shortest safety counterexample |
| --- | --- | --- |
| A44 | `trust_old_envelope` | Prepare an ID → acknowledge its close → deliver the old admission envelope. Three transitions. |
| A44 | `close_range` | Admit one permit and close a separate prepared permit with the same range. The first hold disappears after four transitions. |
| A45 | `check_latest_only` | Admit an earlier hold at the first record, prepare a later ID, and trim using only the latest ID's constraint. Four transitions. |
| A46 | `forget_issued` | Prepare and close an ID → seal and install without its issuance watermark → allocate the closed ID again. Five transitions. |
| A46 | `forget_pending` | Prepare → seal → install without the live preparation. Three transitions. |

## General reference and composition proofs

The [reference kernel](../07-reference/Kernel.lean) uses an arbitrary permit table, with the states unused, prepared, and holding.
Five new kernel theorems cover monotone issuance, preservation of spent IDs, an arbitrary-trace refusal of delayed admission, constructive prepare-and-admit, and selective close.
Its strengthened replay invariant protects every held range.
A new mutation verifies that removing the prepared-reservation guard breaks the spent-ID proof.

Five [composition theorems](ReplayComposition.lean) use only standard axioms.
A product trace refines both the logical stream kernel and the physical read protocol.
A live borrow has both the original committed bytes and its physical protection across arbitrary finite traces.
The tracked hold stays active while its admission gate remains open.
The constructive trace closes that gate, releases the exact logical hold, trims under the checkpoint and other-hold constraints, and finishes the old physical borrow.
The wrong-bytes and open-gate release mutations fail the matching preservation laws.

## Residue

The composed invariant assumes a verifiable stop capability and an effective local admission gate.
The proof binds a scoped physical operation to one exact image and observes one permit in the product.
The reference table covers arbitrarily many logical permits and the separate physical model covers arbitrarily many operations sharing storage.
Actual provider leases, admission authority on either side of a partition, multi-site resource accounting, and reclaim receipt formation remain premises to refine.
An early logical release also requires the operation's complete physical read set to be reserved.
It cannot admit new storage dependencies after closure.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/15-replay-permits/run.py
```

The runner builds the current kernel and physical custody modules.
