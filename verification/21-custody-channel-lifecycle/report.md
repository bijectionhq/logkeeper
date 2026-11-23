# Study 21 report · Custody channel rollover and retirement

2026-11-22

## Verdict

A custody channel gates new registrations.
Its installed grants have their own lifetime and exact keys.
The custodian issues a fresh handle under its durable issuance counter, scoped to the custodian incarnation, issuer and route.
Closing that handle removes the channel's floor and retry markers while preserving all installed grants.
The successor starts with a fresh handle even when it occupies the same route and reuses the same serial number.

Once a retired handle's exact grant is absent, that absence is stable.
An installed grant can still answer an authenticated exact retry or be released by its own authority.
An issuer recovering an ambiguous acquire learns whether the grant is still held from an exact observation at the responsible custodian.
Closing the channel settles eligibility for future acquisition while any existing grant remains independently accounted.

## TLC comparison

The seven safety invariants and release progress under weak fairness and eventual stable access hold for both designs at the configured bounds.
The model has one reusable route, two serials per handle, and a separate physical pin limit of two.

| Configured handles | Close admission and keep grants | Drain before closing |
| --- | ---: | ---: |
| Two | 11,640 states | 2,214 states |
| Three | 128,472 states | 11,350 states |

The drain-first candidate excludes the rollover program with a previously published grant still live.
The chosen design reaches that program in six transitions.
In ten transitions it reconciles the exact old live grant after rollover and releases that same grant on authorized withdrawal.
In five it delivers an old unacquired request to the successor and refuses it.
The acceptance configurations enable retries and observational history for those witnesses.
The history used by the checker to identify retired handles and earlier admissions is ghost state.

| Amendment | Mutation | Counterexample |
| --- | --- | --- |
| A67 | `reuse_handle` | Open, close and reopen with the same handle. Three transitions. |
| A68 | `drop_live_pins` | Grant and publish a reference, then close the channel and delete its still-live pin. Five transitions. |
| A69 | `ignore_channel` | Queue an acquire, close its channel, open a successor, and accept the old key anyway. Five transitions. |
| A69 | `rebind_to_route` | Queue and deliver the old request after rollover, rewriting its identity to an unplanned successor key. Five transitions. |
| A69 | `close_by_route` | Queue a close, rotate the channel, then apply the old close to the successor. Five transitions. |
| A69 | `floor_by_route` | Queue an old floor message after a grant, rotate, then apply the old floor to the successor. Seven transitions. |
| A69 | `release_by_serial` | Use one serial under successive handles, then release the old grant and remove the new published pin. Ten transitions. |
| A70 | `release_requires_channel` | Retire the channel and authorize withdrawal of its held grant. The link can remain healthy forever while the old release stays disabled. Temporal counterexample. |

## General proofs

Fifteen [Lean theorems](ChannelLifecycle.lean) use only standard axioms.
They check that matching active requests use the earlier registration decision, and that a stale close or floor receipt leaves state unchanged.
Each transition preserves a held binding unless it has specific release authority for that exact key and binding.
Closing a channel preserves every grant and frees its control row.
A retired handle remains retired through arbitrary finite service traces, and a missing old grant can never be recreated.
The constructive rotation program replays and releases a preserved grant while the successor remains active.

The Lean transition state has a durable issuance counter, a table of current channels bounded by the configured route slots, and the separate table of installed grants.
The proofs bound control rows independently of the number of past channels and ensure every current handle's nonce was issued.
The counter is modeled as a natural number.
A real representation must prevent wraparound and reuse within a custodian incarnation.
Removing stale-handle refusal, exact release authority or the route-slot capacity guard fails a matching Lean proof.

## Residue

The model authenticates operation scope as a premise and keeps the custodian incarnation fixed.
A replacement that reuses that incarnation must preserve the issuance counter, active channel gates and exact grants.
A replacement with a new physical incarnation needs explicit custody transfer and a route for settling old grants.
[Study 22](../22-residence-transfer/report.md) verifies relocation of a published physical checkpoint while retaining source obligations.
[Study 23](../23-custody-authority-handoff/report.md) checks movement of issuer intents while the physical grants and their settlement remain at their original custodian.
Recovery of the custodian's own replicated metadata remains a separate obligation.
[Study 24](../24-custodian-recovery/report.md) checks the abstract recovery contract and corrects the release step to fence an authenticated exact key when the slot is empty.
Release progress still needs an authorized source decision and access to the custodian holding the grant.
The rotation proof starts with a valid active handle and authority to close and mint a successor.
Lost open acknowledgments, repeated concurrent admission of issuers, grant-byte accounting, and actual provider and metadata storage remain refinement work.
A bound on channel control rows leaves physical pins and unsettled issuer intents under their separate budgets.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/21-custody-channel-lifecycle/run.py
```
