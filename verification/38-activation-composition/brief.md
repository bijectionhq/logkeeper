# Study 38 · Compose activation with its home handoff

2026-11-23

## Question

Can the source and physical custodian finish work during a home transfer without making its exact sealed cut stale or rolling back either external decision?

## Sources

Use the [requirements](../requirements.md), the [admission and result reducer](../36-intent-retirement/IntentRetirement.lean), and the [home handoff and discovery reducer](../37-obligation-home/ObligationHome.lean).

## Model and comparison

Compose those two Lean reducers with separate durable source and provider state.
Represent a movable target cut, exact replies in flight, and durable external settlement.
Use the same state machine to compare an owner-local cut with restoring external state from that cut and with admitting target mutations after it has sealed.
In the bounded model, follow an already installed activation and a live cleanup plan across one or two owner changes.
Treat authentic source result and provider receipts and exact successor storage as explicit boundaries.

## Properties and acceptance

- Project every composed history to the activation trace and the home routing trace, permitting internal steps to stutter.
- Keep the exact result recoverable until the source durably records it.
- Record the source result and fence the physical copy after staging the target cut, install the cut, and reconcile at the new owner after shutdown.
- Preserve a duplicate reply and stale acknowledgment as safe retries across the handoff.
- Preserve the issuance fence, exact copy key, and non-regressing routing.
- Locate the safety failure when restoration rewinds the source or custodian, or when a sealed predecessor reports a target mutation as successful.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap, and 60 seconds per case.
Use Lean 4.35.0 for trace projection, composition invariants, and acceptance.
Run negative controls before each reference baseline.
