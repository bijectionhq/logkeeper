# Study 62 · Fund each append without a pool round trip

2026-11-23

## Verdict

The pool charges a journal window when it grants the allocation.
The stream installs the exact non-reused window and orders how much of it each append consumes.
A successful append advances the stream LSN and the byte cursor together.
It can use its paid window even when new allocations would exceed the pool limit.
Recovery applies the historical request at its original stream and window state, independent of the allocator's current free space.

## Bounded comparison

[AppendWindows.tla](AppendWindows.tla) has two streams, one window of two units per stream, requests of one or two units, and one competing unit of move preparation.
The same pool limit covers both the windows and the prepared unit.
The checker distinguishes granting a window, appending a byte range, trimming, and recovering prior replies.

| Case | Distinct states | Result |
| --- | ---: | --- |
| Three units of capacity | 91 | All four safety invariants hold. One window and a move hold can coexist at full capacity. |
| Five units of capacity | 1,028 | The same invariants hold with both windows and the move hold. |

| Weakening | Shortest counterexample |
| --- | --- |
| Reuse a free-space quote | Quote room for one window. Grant another window, then grant the quoted window against the old observation. Capacity is exceeded in three transitions. |
| Permit an unfunded append | Append without a window. The new record has no pool debit after one transition. |
| Reuse an offset | Grant a window and append twice at the same starting offset. The ranges overlap after three transitions. |
| Refund a live window | Grant a window and return its debit while the stream still owns it. Two transitions. |
| Query current capacity on replay | Prepare the move, grant the window, and append using it. Recovery drops the original success at full capacity. Four transitions. |

## General proofs

[FundedAppend.lean](FundedAppend.lean) checks thirteen theorems with standard axioms only.
The granted allocation is an actual exact debit in the regional pool reducer.
Every ordered step that grows logical history goes through the funded decision, producing the same append and receipt as the existing stream reducer.
Each successful request uses its own stream and placement's current window, a positive range starting at its cursor, and attached exact frame evidence.
The cursor advances on success and is preserved on refusal.
Consumed ranges remain unavailable through arbitrary later steps, including after window pruning, because issuance preserves the owner watermark.

Every finite trace preserves the previous regional invariants together with window ownership and debit bounds.
Publishing a new window checks the exact pool incarnation's eligibility and charged allocation.
Independent regional actions must preserve every still-owned window's backing.
The decision reads the historical stream state, the window book, and the original request, which makes the result independent of the current allocator.
The Lean negative control removes the exact cursor equality and fails the proof that ranges begin at their owned cursor.

## Amendments

[A239–A243](../amendments.md#study-62--2026-11-23) require an actual precharge, exact local range consumption, stable backing, and historical application.

## Acceptance programs

- P95. Prepare one unit of move capacity and grant a stream the other two units. Append through the paid window under a full pool. TLC constructs this in three transitions, and the Lean acceptance decision uses no pool operation.
- P96. Recover the same certified source and window basis after the pool is full. Preserve the exact append result and cursor update. TLC checks recorded successes and Lean proves the ordered decision independent of the current pool state.
- P97. Submitting a second append for a consumed range or admitting a stream append without its exact window must fail. The Lean refusal preserves the window cursor and logical history.

## Residue

The physical book abstracts provisioned allocation footprint and attached exact frame evidence.
The storage and quorum interface still needs a checked refinement that prevents competing unchosen writes from owning or overwriting the same range and charges staged and obsolete bytes while an earlier cut can still need them.
The authenticated provider grant must retain custody through delayed publication and release.
The proof covers the historical decision given its exact window basis, while checkpoint encoding and ranked recovery still need to carry the window book and its dependencies in that basis.
Window pruning follows the source's trim or retirement, with provider disposal still subject to all independent original custody.
The finite move preparation consumes the common budget, and the general proof still needs the exact multi-pool prepared move vector and its transfer into installed-window funding.
No throughput or replenishment-liveness claim is established by these checks.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records commands, configurations, theorem checks, and failing traces below `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/62-funded-appends/run.py
```
