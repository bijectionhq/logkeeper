# Study 23 report · Custody issuer authority handoff

2026-11-22

## Verdict

Move the issuer's exact committed intent book under the existing authority seal.
Keep every unresolved plan and its original physical key, even when the grant's existence is still unknown.
Carry terminal decisions as part of the same cut.
The sealed predecessor can forward previously committed evidence while its authority to create new decisions is closed.

Physical grants stay with their custodians.
A late, previously authorized acquisition can arrive at the old custodian after the issuer has moved.
The successor can reconcile or release that exact grant through the inherited intent.
It discharges the plan only with durable settlement evidence that makes a delayed registration harmless.
New work can use fresh keys under its own capacity budget while an old pin remains pending.

## TLC results

The six safety laws and both conditional progress properties hold across 2,736 distinct states with one old plan and 87,096 with two.
Both bounds have one new destination plan and separate connectivity for the old issuer and old physical custodian.
The fairness checks cover installation after staging the exact seal and sending and delivering exact release when access stabilizes.

| Amendment | Mutation | Counterexample |
| --- | --- | --- |
| A76 | `observed_only` | Prepare and send an acquisition. Seal, stage and install an image of currently held grants, omitting the in-flight interest. Five transitions. |
| A76 | `stale_precopy` | Pre-copy, then commit another intent before seal. Install the old image and lose that committed plan. Five transitions. |
| A77 | `forget_terminal` | Cancel a plan at the source, then stage and install it without the cancellation. Five transitions. |
| A77 | `source_after_seal` | Prepare and seal, then commit a new cancellation at the predecessor. Three transitions. |
| A78 | `rebind_old_intent` | Deliver an old acquisition after install and retarget it to the successor's physical key. Six transitions. |
| A79 | `absence_is_settled` | Send an acquisition, cancel, and forget the plan after observing no grant while the request is still in flight. Four transitions. |
| A80 | `needs_old_issuer` | Stage the seal and lose the link to the predecessor. A healthy target cannot install despite fair scheduling. Temporal counterexample. |
| A80 | Permanent old custodian loss | Cancel an old interest with the target installed. The original custodian can remain unreachable forever, leaving settlement pending. Temporal counterexample. |

An eleven-transition witness sends the acquisition at the source and delivers it only after the successor installs with the issuer link down.
The target recovers that grant, cancels its intent and settles the exact physical key.
An eight-transition witness carries a prior cancellation across offline install and fences its key despite the absence of an acquired grant.
In twelve transitions an already pinned old grant stays at an inaccessible custodian while a successor installs with both old sites unreachable and publishes an independent new grant.
The fresh key represents available admission capacity.
The witness establishes a feasible schedule, while the temporal checks concern install and old release.

## General proofs

Lean checks fifteen theorems with standard axioms only. [Proofs](CustodyAuthorityHandoff.lean)
Every authorized settlement has the exact physical fence, and every still-possible grant keeps its binding through arbitrary finite ordered issuer traces.
Committed terminal decisions remain closed across arbitrary appended decisions and moves.
A certified checkpoint and admitted retained tail reconstruct the same book as folding the full committed prefix.
Exact installation reuses the existing one-use seal and carries the same book, while the predecessor loses its serving row.

The inherited key selects the original custodian for an exact replay or authenticated release.
The release leaves every other custodian unchanged.
An authoritative absence under a retired handle survives subsequent channel renewals.
A new command for a different custodian leaves the old plan unchanged.
The three Lean controls identify the missing physical fence, reopened terminal plan and incorrect lookup location at their intended proof sites.

## Residue

The proof uses the previous authority protocol as a reusable mechanism.
Its exact installed journal and checkpoint guarantees are modeled contracts.
Actual issuer journal storage, certificate authentication, distributed replay of side effects, and accounting of duplicate staging and inaccessible old pins still require refinement.
The TLC runs have one handoff.
The general proof covers ordered finite continuations and authentic final installation.
Source reachability is still necessary until its exact seal becomes durable at the target.
The source issuer authority and the physical custody endpoints are separate roles.
Physical relocation and release of their exact old versions use the channel and residence contracts.
[Study 24](../24-custodian-recovery/report.md) covers the abstract recovery of the custodian's own replicated state.
Its refinement to media and provider effects remains open.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/23-custody-authority-handoff/run.py
```
