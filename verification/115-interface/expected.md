# Expected results

## Lean 4.35.0

The baseline checks 30 named theorems, including the reachability witness. The only reported axioms are `propext` and `Quot.sound`. The runner permits the standard Lean axioms and rejects all others. Every counterexample changes an operational definition, compiles that variant, requires the named theorem to evaluate to false, then proves its negation without axioms.

| Named theorem | Baseline observation | Negative control |
| --- | --- | --- |
| `exactTemporalRead` | Earlier cut sees 7, latest sees 12, and the exclusive valid end is absent. | Resolve every exact selector to the latest cut. |
| `projectedRange` | The first row and the total come from the same two-row range. | Truncate the range before computing its projection and count. |
| `validateAtDecision` | Concurrent point and count changes refuse their stale guarded requests and the refused writes stay invisible. | Check both guards at the requested old basis. |
| `retryUsesOriginal` | Exact retries return the original accepted and refused decisions and append no new decision. | Return a constructed success at the current head. |
| `retryRejectsChanged` | A changed mutation body cannot claim the original receipt. | Reuse any receipt under the same owner and identifier. |
| `exactHold` | A live owner-bound hold keeps its cut through trim. Wrong owner, wrong release and expiration preserve access rules. | Trim past the live hold. |
| `freshReadRetry` | A fresh read retry admits a new handle at the same retained cut and fails after that cut is trimmed. | Reuse the previous handle identifier. |
| `watchResets` | A cursor below retention receives a snapshot restart basis. | Ignore the retention floor. |
| `watchOrdered` | The watch covers the refused cut without delivering its uncommitted writes. | Emit refused requests as deltas. |
| `effectiveOverlay` | With no override the point comes from the parent. A winning tombstone yields absence. | Fill a tombstoned point from the parent. |
| `forgetAtDecision` | Latest suppresses the forgotten subject, preserves its neighbor, and refuses reintroduction. An admitted old cut still works before the deadline. | Skip suppression in current point projection. |
| `forgetAtDeadline` | The hold survives, its read fails at the deadline, and a cursor crossing erasure restarts. | Keep old-generation reads working at the exact deadline. |

The inductive `Reachable` witness starts from an empty store. It commits a two-subject write, holds the original cut, overwrites at a later cut, orders a refusal, forgets the first subject and reaches the deadline. The neighbor remains readable at cut 4, the hold returns an erasure error, the subscription restarts, and the exact mutation retry returns the original refusal at cut 3.

## TLC 1.7.4

The strict model visits **86 distinct states** and generates **493 states** with no invariant violation. Bounds are one deployment, one nonzero incarnation, three serving image states, one independent archive flag, one row, one active borrow, and one physical custody flag. Before-state and operation variables record the latest transition. There is no depth limit or fairness assumption. The runner checks the exact failure name for every counterexample.

| Configuration | Expected outcome | Transitions |
| --- | --- | --- |
| `strict` | All safety invariants hold. | Exhaustive |
| `self-install` | `InstallRequiresAuthority` fails when a transaction creates its missing authority. | 1 |
| `row-archive` | `ArchiveRequiresAuthority` fails when an ordinary write certifies archive custody. | 2 |
| `replace-with-row` | `RestoreRequiresEvidence` fails when an ordinary row becomes the recovery selection. | 3 |
| `subject-retire` | `RetireRequiresAuthority` fails when subject erasure closes deployment admission. | 2 |
| `late-hold` | `RetireClosesAdmission` fails when a closed authority admits a new borrow. | 3 |
| `undrained-disposal` | `DisposalDrains` fails when physical custody is removed while a borrow is live. | 4 |
| `strict` with the witness assertion | The deliberately inverted `TerminalWitness` fails. The trace installs, archives, restores, writes, holds, retires, drains, and then disposes. | 8 |
