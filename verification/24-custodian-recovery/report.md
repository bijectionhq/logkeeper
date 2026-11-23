# Study 24 report · Physical custodian recovery

2026-11-22

## Verdict

Recover the current custodian incarnation's complete certified control state from its active quorum.
That state includes the issuance counter, live channel controls and floors, uncompressed refusal markers, exact grants, active borrow obligations, and pending and confirmed erasure state.
A new voter set needs exact coverage and a durable fence against stale decisions by the old voters.

Record and acknowledge an authenticated cancellation even when its exact grant has yet to arrive.
The receiver installs the appropriate spent marker or uses the existing floor or retired handle fence.
Later recovery preserves that refusal.

Commit the exact erasure fence before dispatching an irreversible provider request.
The provider can finish while the coordinator is down.
After exact recovery the coordinator can retry the same operation idempotently and commit completion once it receives exact absence evidence.

## TLC results

The eight safety laws and both conditional progress properties hold in 65,016 distinct states with two possible channel handles and 95,736 with three.
Each bound has one restart, one membership replacement, one AZ loss and a separately reachable provider.

| Amendment | Weakening | Shortest safety counterexample |
| --- | --- | --- |
| A81 | `switch_without_copy` | Switch from voters 1, 2 and 3 to 2, 3 and 4 while only 1 and 2 have the current image. One transition. |
| A81 | `switch_without_fence` | Copy the image, switch membership and let an old quorum decide. Three transitions. |
| A82 | `forget_issuance` | Retire the first handle, crash, restore its old issuance counter and mint the retired identity again. Four transitions. |
| A82 | `forget_spent` | Fence an empty slot, crash and restore without its spent record, then admit the delayed request. Six transitions. |
| A82 | `forget_floor` | Fence an empty slot and compact its marker into the floor. Restore without that floor and admit the delayed request. Seven transitions. |
| A83 | `forget_grant` | Acknowledge a grant, crash and restore an image that drops it. Four transitions. |
| A83 | `forget_borrow` | Open a borrow, crash and drop the borrow from recovered state. Five transitions. A ten-transition trace goes on to erase the still-borrowed bytes. |
| A84 | `release_absence_without_fence` | Queue acquisition, cancel while absent and acknowledge, then admit the old acquisition. Four transitions. |
| A85 | `forget_delete_fence` | Authorize and dispatch deletion, crash, then reopen the version while the provider operation is still pending. Four transitions. |
| A85 | `early_provider_effect` | Dispatch an erase before the fence commits. One transition. A four-transition trace lets the provider erase a concurrently acquired live grant. |

In seven transitions an empty slot is canceled and its refusal marker compacted before crash, then the recovered custodian refuses the delayed acquisition.
In six transitions a committed delete is dispatched before crash, delivered while the coordinator is down, and settled after recovery.
In seven transitions the custodian retains an already live grant and borrow across voter replacement with one AZ down and recovers them after restart.
A permanently inaccessible provider defeats unconditional disposal completion even with the metadata quorum available.
Conditional restart and completion hold with the modeled fairness and reachability.

## General proofs

Lean checks sixteen theorems with standard axioms only. [Proofs](CustodianRecovery.lean)
Any current recovery majority can read the exact fully materialized image or the exact retained records required with a certified checkpoint.
Recovery from the checkpoint and tail reconstructs the complete current receiver state.
Combining exact image coverage with three distinct failure domains gives recoverability after one AZ loss.
New membership can preserve that image and exclude stale old decisions using the previous journal proofs.

The channel model now represents cancellation when the slot is empty, as required by the registration protocol.
The earlier typed release could run only when a grant already existed.
The corrected guard accepts an empty slot or the exact binding, under the same release authority.
Lean proves that such a canceled empty slot still refuses a delayed acquisition after exact recovery.

The prior exact-version fence remains valid through later custody transitions at that residence.
The recovered provider effect preserves every version still open for readers and is idempotent.
Verifying exact absence allows the metadata completion transition.
Three proof controls remove new membership coverage, the effect fence, or exact absence evidence and fail their corresponding laws.

## Residue

The exact current log cut, checkpoint authenticity, media identity and provider observations remain contracts the implementation must fulfill.
The materialized-image proof does not require full snapshots on every production mutation.
The replay result covers a deterministic receiver reducer under a certified base and exact tail.
Actual receiver reducer encoding, consensus and disk recovery, durable borrow evidence, and authenticated provider requests and receipts remain refinement obligations.
The bounded model abstracts repeated simultaneous voter changes and multiple in-flight erasures.
The old physical incarnation's fences remain necessary while exact delayed operations can reach it.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/24-custodian-recovery/run.py
```
