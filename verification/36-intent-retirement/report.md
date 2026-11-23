# Study 36 report · Retire an activation intent

2026-11-23

## Verdict

Close the exact incoming admission once the source has durably aborted it or the target has ordered its installation.
The original admission handle stays closed under a durable issuance fence.
Keep live serving custody, physical settlement, and exact result delivery independent of that admission row.
Reserve capacity for the result before the source can seal.
When the result quota fills, defer fresh moves before they become irreversible.

## Bounded comparison

TLC explored one reusable admission slot, two or three monotonically issued handles, an independently charged physical copy plan per handle, and at most one target voter replacement.
The model has two different sealed image values.
Its history fields let laws refer to chosen and retired handles after their admission rows disappear.
Each action is atomic at its stated authority.
The disconnected cases disable only the named provider or source record action throughout the run.

| Candidate and setting | Handles / copy credits / result credits | Distinct states | Result |
| --- | --- | ---: | --- |
| Detached, reachable | 2 / 1 / 1 | 1,402 | Eight safety laws, ready installation, and settlement of retired aborted copies hold. |
| Detached, reachable | 2 / 2 / 2 | 7,086 | Same laws hold. |
| Drain before closing, reachable | 2 / 2 / 2 | 1,446 | Eight safety laws and ready installation hold. |
| Detached, repeated handles | 3 / 1 / 1 | 10,102 | Eight safety laws hold. |
| Detached, provider disconnected | 2 / 2 / 2 | 50 | Retirement with exact terminal evidence holds. |
| Detached, source result path down | 2 / 2 / 2 | 2,274 | Retirement with exact terminal evidence holds. |
| Detached, source result path down at single result credit | 2 / 2 / 1 | 674 | Eight safety laws, retirement with exact terminal evidence, and ready installation hold. |

Safety covers non-reuse, exact terminal disposition, exact installation, retained results, physical plan tracking, serving custody, quota bounds, and result credit before sealing.
The temporal properties use weak fairness of closing, cleanup, and installation.
They cover closing once terminal evidence exists, installing a sealed intent once its exact image is held, and settling a retired aborted copy when its provider can fence it.

## Counterexamples

| Amendment | Weakening | TLC evidence |
| --- | --- | --- |
| A135 | `forget_issued` | Close the first handle, replace voters, and reissue its identity in five transitions. |
| A135 | `guess_terminal` | Close a prepared handle with no terminal evidence in two transitions. |
| A135 | `retire_by_route`, `install_by_route` | Old exact evidence closes a different intent in five transitions or installs a different intent's image in eight. |
| A136 | Drain before closing | A queued plan and unavailable provider block an aborted intent's retirement. A chosen result and unavailable source record path block an installed intent's retirement. Both executions can stutter with exact retirement evidence present. |
| A137 | `drop_on_retire`, `drop_on_move`, `forget_receipts` | Lose the only exact result after closure, onward movement, or voter replacement in six transitions each. |
| A137 | `send_is_ack` | A send permits forgetting without a durable source record in seven transitions. |
| A138 | `forget_cleanup`, `no_missing_fence` | Closure forgets a queued plan in four transitions. Settlement without an effective fence permits the delayed copy to create untracked bytes in five. |
| A138 | `needs_gate` | A retired aborted plan remains charged forever with its original provider reachable because its admission handle can never become live again. |
| A139 | `late_credit` | A source can seal without result credit in two transitions. At a limit of one, an earlier installed result remains unacknowledged while the second sealed intent has a ready image and cannot install. The second execution can stutter even after the first serving copy has been settled. |

Four acceptance witnesses exercise the intended behavior.
The five-transition trace reuses the admission row while a prior copy plan stays charged.
The seven-transition trace fences the empty old slot after reuse and refuses delayed copy delivery.
One fourteen-transition trace installs, closes admission, mints a new handle, moves onward, and replaces voters before the source drops a reply and recovers and acknowledges the original exact result.
At one result credit the fourteen-transition trace mints the new handle after the source's durable acknowledgment instead.

## General proofs

Lean checked eleven theorems using standard axioms only. [Proof source](IntentRetirement.lean)
An unresolved seal cannot supply retirement evidence.
The admission projection preserves refusal of any stale handle over arbitrary finite traces.
The result invariant proves that each chosen image has its exact unresolved result at the target or its exact durable record at the source.
That invariant holds initially and over arbitrary finite traces of the reducer, including after onward movement and restart.
Any step removing an existing exact physical plan requires matching settlement evidence.
An acceptance theorem constructs closure followed by fresh admission while an old plan remains, given room for the new entrant.

The three Lean controls fail at the predicted proof sites when a source acknowledgment omits the durable record, admission closure deletes results, or admission closure deletes physical plans.

## Remaining obligations

The Lean model treats authentic ordered source decisions, target recovery of durable records, onward adoption, room, and settlement as premises.
The finite model checks quota and liveness in its two-outage comparison.
It represents one charged slot per copy, rather than bytes, and models voter replacement as restoring the correct durable image.
The target scoped by the exact handle must remain discoverable for result recovery.
An eventual shutdown of that authority, or migration of its outstanding debts, needs a routing and custody proof that spans both source and target lifecycles.
[Study 37](../37-obligation-home/report.md) checks exact home handoff, planned shutdown, and discovery of retained obligations.
Reserving result capacity alone says nothing about whether all necessary staged media can be made ready in the first place.

Apply [A135–A139](../amendments.md#study-36--2026-11-23).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner saves commands, configurations, TLC traces, and proof mutation diagnostics under the ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/36-intent-retirement/run.py
```
