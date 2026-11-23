# Study 14 report · Physical custody for admitted reads

2026-11-22

## Verdict

Replay permission establishes the logical range a reader may use.
An admitted I/O operation also needs an exact physical borrow.
Acquire it in the same storage metadata decision that checks present contents and the current index binding.
Keep it until the operation completes or an effective storage-side fence makes subsequent success impossible.

Logical expiry can release its replay hold after new admission is fenced if every outstanding operation already holds all of its needed extents.
Operations that might discover further dependencies need the drain-first contract.
A source borrow survives a stream move as an obligation against the source physical extent.

## TLC results

Both candidates satisfy all three safety invariants and conditional drainage with an eventually reachable source.
Each execution has one permit, up to two requests, three extents, one compaction, and at most one stream move.

| Bounded candidate | One request | Two requests |
| --- | ---: | ---: |
| Exact physical borrows with early logical release | 3,680 states | 32,452 states |
| Drain before logical release | 3,000 states | 22,236 states |

An exact borrow can complete after logical trim in six transitions.
The drain-first candidate excludes that ordering at the checked one-request bound.
A six-transition witness has a source borrow and a target borrow outstanding together after a move.
The strong claim of eventual drain even when the source is permanently unreachable fails.
Once the endpoint is unreachable, weak fairness cannot enable a fence that needs that endpoint.

| Amendment | Mutation | Shortest safety counterexample |
| --- | --- | --- |
| A41 | `stale_lookup` | Build a replacement, look up the old extent, publish and reclaim it, then grant a borrow from the old lookup. Five transitions. |
| A42 | `logical_only` | Borrow an extent, publish its replacement, then reclaim the borrowed extent. Five transitions. |
| A43 | `admit_after_close` | Locate an extent, close admission, then accept the delayed borrow. Three transitions. |
| A43 | `timeout_is_stop` | Borrow an extent, publish its replacement, request close, observe a timeout, and reclaim the still-borrowed extent. Seven transitions. |
| A43 | `late_reply` | Locate and borrow, close admission, effectively fence the request, then let it report a new success. Five transitions. |

## General proofs

Six Lean theorems use only standard axioms.
Every finite trace preserves exact physical bytes for all still-borrowing operations.
An admission gate that has closed never reopens in the modeled permit lifetime.
A stopped operation never becomes successful again.
An operation already borrowing can finish after admission closes.
The observer theorem rules out safely inferring an effective stop from a timeout that is indistinguishable from a still-running remote read.

The Lean controls fail at the intended decisions when borrowing skips the exact bytes or reclamation ignores outstanding physical borrows.
The [composition proof](../15-replay-permits/report.md) ties these physical borrows to an exact logical replay grant and committed record.

## Residue

Storage must implement the effective admission and stop fences.
A misplaced acknowledgment from a client or an unreachable endpoint does not discharge a physical custody obligation.
The model leaves the transport, real descriptor and object leases, lease authentication, and repair of lost local state to refinement.
Logical expiry can proceed under the stated exact-borrow premise, while unresolved extents remain charged to the physical custody budget.
This is a proposed design change from RTDB's current conservative drain-before-release rule.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/14-read-custody/run.py
```
