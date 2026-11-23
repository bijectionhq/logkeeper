# Study 53 · Separate evacuation from physical disposition

2026-11-23

## Verdict

Restore protection by installing independently funded exact coverage in the surviving placement.
Once the new placement covers the required failure domains, withdraw the old copy from fresh use at the placement authority.
Its original physical charge and exact old borrows survive withdrawal.
Provider settlement can proceed later.

A second copy in the survivor's AZ is useful as another local source, but both copies fail with that AZ.
A full surviving destination needs additional verified capacity in a suitable domain.
Idle capacity in the unavailable pool cannot fund it.

## Bounded comparison

[PoolEvacuation.tla](PoolEvacuation.tla) models one immutable image, four physical pools in three AZs, one new AZ outage at a time, reservation, materialization, verification, placement, withdrawal, an original physical borrow, and separate disposition.
Two destinations share the same image requirement, and one shares the surviving pool's AZ.
Reservations cover a whole unit at their own pool, independently of ordinary occupancy.
A wrong image can land without becoming eligible.
The quarantined pool stays offline for the modeled outage.

| Case | Distinct states | Result |
| --- | ---: | --- |
| Independent placement and disposition, one unit per pool | 504 | All seven safety laws hold at the bound. |
| Same design, two units per pool | 6,864 | The same laws hold with more ordinary traffic. |
| Stable outage of the original pool and dedicated replacement room | 6 | The same safety laws and eventual replacement plus withdrawal hold. |
| Independent replacement pool already full | 48 | All seven safety laws hold. No repair debit enters the full pool. |

The progress check starts with an already unavailable original pool, one reachable exact installed copy, and an eligible destination with continuously available room.
Weak fairness covers reservation, exact copy, verification, registration, and withdrawal.
The surviving source and replacement stay reachable in this case.
The check models eventual exact materialization under fair reachable service. The general safety cases also explore a foreign image on the destination.

| Weakening | Counterexample |
| --- | --- |
| Return credit when the AZ fails | A single fault transition removes a live charge while the bytes may still exist. |
| Spend capacity from the unavailable pool at the destination | Start with a full destination and one unused unit in the original pool. Lose the original AZ and reserve the replacement above the destination's own limit. Two transitions. |
| Certify a foreign image | Reserve, land the wrong bytes, verify and join. Four transitions. |
| Count pools as independent domains | Lose the original AZ and register a copy alongside the sole survivor in the same AZ. Five transitions. |
| Withdraw once any other copy is readable | Remove half the healthy coverage in one planned transition. |
| Require a response from the old pool before withdrawal | The exact funded replacement joins and the protocol stutters indefinitely with the unreachable old copy still in the placement. |

## General proofs

[PoolEvacuation.lean](PoolEvacuation.lean) imports the Study 52 reducer.
It checks eight theorems using standard axioms only.
Each step and each finite trace preserves the numeric ledger and exact backing for its installed placement.
New debits require a reachable local pool and fit that pool's actual configured limit in the model.
If an eligible placement covers every single-zone removal, losing any one zone leaves an eligible, charged, exact version.
Any set of copies confined to one zone fails this requirement.

A planned withdrawal preserves the failure envelope.
The constructive withdrawal theorem applies while the original pool stays offline and preserves its accounting state, original borrow, and original debit.
An AZ loss alone changes reachability while preserving every old charge.
The inherited exact refund law still bars disposition of a live borrow.
The two Lean negative controls fail when a foreign image can join or a withdrawal can proceed without the survivor coverage.

## Amendments

[A203–A206](../amendments.md#study-53--2026-11-23) bind restored protection to exact independent coverage, preserve old custody through evacuation, segregate failed-pool capacity, and preserve protection on a planned withdrawal.

## Acceptance programs

- P66. Borrow from the original pool, lose its AZ, and independently reserve, copy, verify and install the replacement. Withdraw the original with its borrow and debit still recorded. TLC finds this in seven transitions.
- P67. Refuse an independent replacement at its full destination. In a separate trace, place a second copy in the survivor's AZ and keep the image's health degraded. TLC reaches that outcome in five transitions.
- P68. Install exact independent coverage, withdraw the intact old source, and complete scoped disposition. TLC finds this in six transitions.

## Residue

This check covers the physical inputs to a certified cut.
Journal voter eligibility, quorum installation and the source of the authoritative cut have their own rules.
The combined reference still needs to derive physical coverage for every required input at the same cut and prove how certification gets its current evidence.
The model gives the verifier accurate scope, topology and durable availability at a modeled step.
Operators can observe fault detection and coverage evidence with delay, so a health observation has a scope and time.

Provider disposition, including any proof of irreversible destruction and closure of old write paths, must refine the original exact scope.
The model intentionally keeps a failed domain's obligations while no usable evidence can settle them.
A replacement grant from a returned pool needs fresh validation under its exact physical incarnation.
Repeated replacement of failed pools without terminal evidence can exhaust a bounded inventory of unresolved obligations.
The baseline progress check assumes one outage and has independent destination capacity available. It establishes no progress bound when spare capacity or the surviving exact inputs disappear.

## Reproduction

The checked run used Python 3.13, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19 and Lean 4.35.0.
The runner saves settings, traces and diagnostics in `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/53-pool-evacuation/run.py
```
