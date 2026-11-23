# Study 71 · Late pool preparation and exact terminal closure

2026-11-23

## Verdict

A custodian checks the original authorized plan and its own admission state.
An issued prepare can arrive after the source aborts and before the custodian receives that decision.
If it is locally eligible, acquiring the grant and charging its exact extent form one decision.
The source's ordered outcome stays aborted.
Delivery of that outcome closes the exact local grant and stops issuance of new provider tickets.
Previously issued work can still take effect under its original debit.
A source result can compact once the pool certifies closure with no remaining physical obligation, or keeps the remaining work in durable charged custody.
The physical debit can return after verified stable absence of its own extent.

## Bounded comparison

[LatePrepare.tla](LatePrepare.tla) checks a pool with one unit of capacity, two successive plans, an old delayed request, an in-flight provider operation, independent source and pool compaction, and one pool takeover.
TLC checked six invariants across 1,531 states.
A 13-transition witness prepares after abort, settles the original debit, compacts the old closure into the floor, changes the pool owner, and seals the next plan.
An eight-transition witness compacts the source's abort result while a previously issued real effect remains pending and charged at the original pool.

| Weakening | Shortest counterexample |
| --- | --- |
| Ignore the installed floor | Abort, fence, acknowledge, and compact the pool's spent row. An old request reacquires capacity under the old identity. Six transitions. |
| Forget a fence on takeover | Take over after the source receives the local settlement acknowledgment. Its certified fence disappears in five transitions. |
| Acknowledge using abort alone | Plan and abort while the original pool has no hold. Acknowledge without closing its admission. Three transitions. |
| Seal using a late receipt | Plan, abort, prepare, and seal with the newly delivered receipt. Four transitions. |
| Refund on local fence | Prepare and abort, fence, and return the charge while the provider scope is still open. Five transitions. |
| Issue a new provider ticket after the fence | Prepare, abort, fence, then issue a fresh provider ticket. Five transitions. |

## General proofs

[LatePrepare.lean](LatePrepare.lean) checks ten theorems.
Every composed step projects to the existing custody-channel and shared physical ledger rules.
Preparing creates the exact grant and debit together.
An exact retry returns the existing grant as a replay.
Arbitrary finite interleavings preserve the pointwise capacity bound, backing for live grants, and backing for physical work.
An authenticated exact abort fences an issued scope even if no grant has arrived.
The fence survives unrelated scope admission, authorized floors and channel rollover.
Once a fenced extent is absent from the ledger, no subsequent admitted transition can recharge it.
The fence also excludes issuance of a new provider ticket.
An acknowledgment uses either no remaining charged work or the exact original paid custody.
Returning its charge requires the physical reducer's verified stable absence.

[AbortCut.lean](AbortCut.lean) checks three theorems.
A ranked chosen prefix ending in cancel or retire replays to the exact canceled move row and participant obligation.
The source reducer refuses any seal from that already decided row, regardless of the late receipts.
The certified result authorizes the original local fence after a delayed request has acquired its backed grant.
The fence leaves the physical debit unchanged.
The Lean negative control removes the physical key check from certified result intake and fails the exact-scope law.

## Amendments

[A277–A281](../amendments.md#study-71--2026-11-23) define when the local plan can act, which authority can close it, and when the two independent closure records can compact.

## Acceptance coverage

- P119 and P121. Delay the original request until after ordered abort. Acquire a paid grant at the pool before the local fence, then close it under that abort. The source refuses the resulting late seal.
- P122. Fence a scope with a pending physical write. Preserve its exact charged custody when the source forgets the old result. Recover local admission closure before serving the same scope and refuse new tickets.
- P123. Compact the spent scope into an installed floor and reuse the capacity under a fresh identity. Old requests remain refused.

## Residue

The generalized proof uses the existing logical extent ledger and assumes injective immutable extent ownership.
That ledger still issues a consecutive abstract physical ordinal.
A real pool needs to mint its own non-reused scope without synchronizing across other pools or waiting behind a delayed plan's old planned ordinal.
The proof assumes an authenticated original registry mapping the source intent and move key to the exact local key and immutable binding, plus exact ranked chosen-prefix evidence.
It checks the application of that evidence and does not establish how a voter forms and recovers it across concrete failure domains.
The general local trace includes channel rollover and floor advancement.
TLC covers controller replacement at this bound.
Composition of the gate and physical ledger into the same durably recoverable pool image is still open.
The TLA+ disposition abstracts effective provider closure and absence as one transition.
The Lean proofs depend on the existing provider refinement premises for those observations.
The integration of live prepared scopes with the current regional funded-move claim view, and progress under many competing moves, remain open.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records exact commands, configurations, checked theorems, and failing traces under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/71-delayed-pool-prepare/run.py
```
