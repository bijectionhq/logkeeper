# Study 31 report · Standing snapshot custody

2026-11-22

## Verdict

Many fresh reads can share one durable physical registration for an exact applied view.
Each read still checks its invocation-bound quorum floor, the selected view's authority, and the current local gate in the decision that acquires its borrow.
Durable custody precedes gate opening and lasts until the gate has sealed and every operation completes or meets an effective stop.
An old window keeps its exact root and replay suffix after a checkpoint switch or endpoint restart.
With spare custody capacity, prepare a successor and switch admission in one local action while old work drains.

Quorum terminal closure and a strict deadline for local physical admission have different availability requirements.
The quorum can close the stream when the read gate is unreachable.
New invocations must then refuse because their verified group-command floor includes the terminal decision and no live view covers it.
An overlapping invocation can still linearize at its certified earlier live view.
A contract that forbids even its first physical borrow after terminal closure needs admission that intersects the terminal decision, or an effective seal on every gate still allowed to open before the receipt.
The latter contract lets an inaccessible gate delay the terminal receipt.

## Bounded results

Each case has one stream and one serving endpoint.
Except where shown, the limits are one append, two window identities, one read, one session restart, and two charged windows.
The endpoint's control link is fixed for each case.
The group can keep choosing commands throughout.

| Candidate | Distinct states | Result |
| --- | ---: | --- |
| Quorum closure | 188,938 | Seven safety laws hold. |
| Quorum closure with one charged window | 110,886 | Seven safety laws hold. |
| Seal before terminal closure | 152,170 | Seven safety laws and the stricter physical deadline hold. |
| Two reads, one window, no append | 9,792 | Seven safety laws hold. |
| Two appends, no restart | 753,094 | Seven safety laws hold. |
| Prepare before switching | 240,170 | Seven safety laws hold with both windows charged during the switch. |
| Prepare before switching with strict closure | 163,552 | The stricter deadline also holds when closure includes staged gates. |
| Close before preparing, two reads, no restart | 1,907,670 | Reads at both cuts without an intervening gate outage are excluded. |

| Temporal property | Always reachable gate | Permanently unreachable gate |
| --- | --- | --- |
| Terminal closure after all gates seal | Holds over 152,170 states. | A fair execution stays open forever because the gate cannot seal. |
| Quorum terminal closure | Covered by the settlement case. | Holds over 1,704 states. |
| Terminal closure and eventual custody settlement | Holds over 188,938 states. | A fair execution reaches terminal closure while the recorded hold remains. |

Weak fairness applies to the request, sealing and terminal actions.
Settlement additionally gives weak fairness to effective stop and release.
The unreachable case disables the actions that need the endpoint link.
Fairness cannot force work that never becomes enabled.

| Amendment | Weakening | Shortest bounded failure |
| --- | --- | --- |
| A110 | `cached_gate` | Inspect an open gate, seal and release it, then admit the delayed request. Six transitions. |
| A110 | `omit_suffix` | Pin and borrow an older root and a one-record suffix, then reclaim the suffix under a newer checkpoint. Nine transitions. |
| A111 | `forget_restart` | Admit a borrow, restart, seal, then release its still-live custody from the new session. Seven transitions. |
| A111 | `reuse_after_restart` | Admit new work in a restarted session under the old gate. Five transitions. |
| A111 | `late_success` | Seal and effectively stop a live operation, then let it finish successfully. Six transitions. |
| A112 | `count_open_only` | Seal a charged window and register another at a limit of one. Two transitions. |
| A112 | `unprotected_stage` | Stage a window at a one-record suffix, publish a later checkpoint, and reclaim the staged suffix. Five transitions. |
| A113 | `stream_lsn_floor` | Retire, start a fresh call and give it a stale live view at the unchanged data LSN. Five transitions. |
| A114 | `ignore_staged_gate` | Prepare a new gate, close the existing gate and issue the strict terminal receipt, then open the prepared gate and admit an earlier invocation. Eight transitions. |

The checked witnesses have two simultaneous reads sharing one registration in six transitions, and first local admission of an overlapping call after the terminal receipt in seven.
An old nonempty suffix can serve through later checkpoint publication in nine.
A result captured before terminal closure can be delivered after closure and release in nine.
A restarted session can serve through a newer gate while a precrash borrow stays charged, and can separately settle an old borrow through an effective stop and reclaim its root, each in ten.
The prepared switch witness has active reads on both the old and new cuts without an intervening gate outage, in ten transitions.
These traces establish possibility within the stated bounds.

## General proofs

Lean checked eleven theorems with standard axioms only. [Proofs](StandingCustody.lean)
An arbitrary finite trace preserves every registered dependency for every live operation, including after admission closes and the local session changes.
A sealed gate cannot reopen.
A stopped operation stays stopped.
Two distinct readers can acquire one registration without modifying the registered basis.

The read certificate binds the certified applied cut to the invocation and same stream lineage using the earlier quorum result.
The custody proof composes that evidence with containment of the exact corresponding physical dependencies.
Under the logical command-boundary contract, the resulting barrier cut has a witness inside the invocation interval and each required dependency remains present while the operation uses it.
The terminal proof separately uses the ordered reducer and absorbing retirement.
A round for an invocation starting after terminal contains the terminal prefix in its lower bound, so its covered applied view cannot have live authority.

A local admission decision with identical observations in two runs cannot both admit in one and refuse in the other.
That observation lemma explains why the strict deadline needs an observable fence, and TLC supplies the compared schedules and progress tests.
Four proof controls fail when release skips real drainage, reclaim ignores exact dependencies, a command floor is discarded, or the held physical basis is independent of the certified snapshot.

## Developer cost

Register the full exact dependency set and a new session-bound gate before publishing a serving window.
For each independent invocation, certify its floor and borrow the current matching open window in one local decision.
After restart, reconcile the prior window by its durable identity and release it from verified completion or effective stop.
If the group orders a reservation at its current head instead, that group decision can supply both the cut and the logical reservation.
That reference path is checked separately. [Ordered application](../28-ordered-application/report.md)

## Remaining obligations

The models treat exact multi-custodian registration and verified stop as premises.
They leave the physical adapter, real request identity, gate/transport ownership, verified session fencing, and atomic switching across process failover for refinement.
The finite model checks staging and active replacement, while the general custody proof begins with one registered exact window.
The modeled cost is a window charge.
Production budgets must also account for retained bytes, overlapping copies, staging, and individual in-flight work.

Fast-path availability also depends on a registered window reaching the requested floor.
A bounded full pool or a lagging replacement can postpone that path.
These runs do not prove that fixed-view window refresh keeps up with arbitrary write or checkpoint churn, or that there is enough headroom for uninterrupted replacement.
An extensible physical hold or reuse of a basis at a later group position that leaves its stream view unchanged needs its own exactness, accounting and progress argument.
Dynamic membership and cross-placement refinement remain separate.

RTDB Multi currently requires a durable drop acknowledgment from every addressed replica before deletion advances.
An earlier quorum terminal receipt is an additional authority result.
The adapter must keep that separate from the existing all-location deletion acknowledgment.
Confirm whether an overlapping call may first take a physical borrow after that earlier receipt.
[RTDB Multi drop contract](https://github.com/bijectionhq/rtdb/blob/fc6da3a4a3/allium/rtdb-multi.allium#L510-L516)

Apply [A110–A114](../amendments.md#study-31--2026-11-22).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner writes exact commands, case configurations, and full counterexamples under the ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/31-standing-custody/run.py
```
