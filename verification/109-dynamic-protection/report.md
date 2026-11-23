# Study 109 · Change protected dependencies during withdrawal

2026-11-23

## Verdict

A prepared checkpoint's exact registrations can be acquired at the original custodians and then published at the installed journal.
Each custodian serializes acquisition and withdrawal of that version.
The publisher uses durable exact receipts and verifies that the held plan covers the current fault cases.
A plan prepared under an earlier interval remains publishable if the exact held plan still covers every required case.
An earlier crash-selectable root keeps its own registrations during the switch.

Publish and abort share one logical decision at the owner of the plan.
An exact durable abort can settle across the original custodians without waiting for replies from the earlier acquisition.
Closing the original registration fences delayed acquisition.
A preparation with an unresolved decision remains charged until its outcome can be recovered.

## General proofs

Lean 4.35.0 checked twelve theorems with standard axioms only.
`ordered_publication_uses_previously_observed_durable_grants` obtains the exact holds from the earlier registration study's durable-receipt contract, joined to the actual original custody references.
`a_pending_deletion_cannot_supply_a_publication_hold` and `a_held_registration_prevents_authorizing_withdrawal` establish the two orders of the race.
`every_interleaving_preserves_the_current_obligation_set` composes publication, changes to the required loss cases, ordinary shared custody operations and exact physical deletion for arbitrary finite traces.
`every_live_root_has_a_backed_version_for_every_declared_input` derives an actual held version for each required input under each current loss case.
`cancellation_fences_delayed_grants_through_custodian_progress` composes exact release of an unknown acquisition outcome with the existing receiver closure law.
The Lean control removes the guard that requires a hold for every exact version and fails at that law.

## Bounded comparison

TLC 2.19 uses three AZs, two roots, one publication attempt, one possible renewal, and one disconnection of the custody control plane.
Stable readable data and access to the original control plane are independent inputs to the model.

| Weakened design | Result |
| --- | --- |
| Pin a version after withdrawal has been ordered | A withdrawing generation becomes a new hold in four transitions. |
| Publish using a physical scan without exact grants | Publish with no custody protection in two transitions. |
| Trust preparation's previous fault scope after renewal | Publish the B-only plan after full protection has returned in seven transitions. |
| Reject every held plan prepared under an earlier scope | Temporal stall after renewal, despite the exact still-held B-and-C plan covering the full envelope. |
| Require a live custodian control round trip at publication | Temporal stall after disconnection with the required durable receipts and readable bytes already available. |
| Publish after durable cancel | A canceled plan publishes in ten transitions. |
| Infer abort of an already published root | Its live outcome collides with an abort in ten transitions. |
| Require an acquisition acknowledgment before closing a canceled plan | Temporal stall with a granted hold, lost reply and available custodian. |
| Ignore the custodian's cancel fence | A delayed acquisition reopens an original canceled reference in six transitions. |
| Release an old root's only-use version when the new root first becomes visible | Delete an input for the still-selectable root in eleven transitions. |

| Reference case | Bounded evidence |
| --- | --- |
| Compete to hold and withdraw the same version | Safety holds in 37 states. |
| Renew with a previously qualifying B-only preparation | Publication is refused in the seven-state scope. |
| Renew with earlier B-and-C grants intact | Eventual qualified publication holds in 20 states. |
| Race publish and cancel | The irreversible outcome holds in 72 states. |
| Preserve the old root while the new root is visible | Safety holds in 40 states. Witnesses reach concurrent selectability in nine transitions and old-root removal after sync in twelve. |
| Publish with the exact committed receipts after disconnection | Eventual publication holds in 20 states. |
| Cancel with at least one actual grant and no observed replies | Eventual closure of the original scopes holds in 26 states. |

Temporal checks assume weak fairness for stable eligible actions.
Conditional abort progress uses an available original custodian and a chosen abort.
Conditional publication uses complete durable grants, currently valid coverage and an available installed publisher.

## Amendments and acceptance

[A440–A445](../amendments.md#study-109--2026-11-23) connect acquisition, publication, abort and retirement of the old selector.
P223 exercises both orders of the acquire-withdrawal race.
P224 tests insufficiency and reuse respectively after renewal.
P225 combines offline publication with retention of the earlier selector.
P226 tests exact abort reconciliation and fencing without acquisition replies.

## Residue

The proofs assume an immutable exact root plan, complete RTDB dependency enumeration, stable version identity and a trusted binding from each authenticated receipt to its original custody reference.
The trace covers a changing set of live roots and current loss cases over a fixed set of modeled physical versions.
Dynamic physical provisioning, canonical named closure and proof encoding, the full crash and membership transport of plans and receipts, and the peak capacity charge across independent custodians still need a common refinement.
The model treats exact root retirement eligibility as supplied by the selector and borrower authorities.
The failure-case set can be computed over an immutable registered plan.
Its compact wire representation and its verified extraction from real manifests remain open.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/109-dynamic-protection/run.py
```

[run.py](run.py) saves case configurations, counterexamples, commands and proof diagnostics under .results/.
