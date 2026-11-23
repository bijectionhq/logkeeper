# Study 60 · Recover the provider's durable fence

2026-11-23

## Question

How can an ordered provider root expose scoped provisioning or terminal evidence while making the same authority recoverable after power loss and selector rotation?

## Sources

Use [journal media durability](../25-media-crash-consistency/report.md), [repeated journal rotation](../26-journal-rotation/report.md), [ordered incarnation recovery](../57-ordered-inventory-recovery/report.md), and [namespace closure](../59-namespace-closure/report.md).

## Model

Place guard creation and root retirement inside one provider's durable decision history.
Compare describing a transition as chosen before both media barriers with publishing an applied result backed by exact recoverable frames.
Check baseline selection and exact suffix reconstruction against opening an older selected base as the current guard.
Use Lean to reduce admitted root commands to the namespace model and derive exact recovery through the existing journal contracts.

## Properties

- Each published retirement receipt names an exact chosen and applied retirement.
- Every legal recovery selector preserves the fence behind a previously published receipt.
- A queued old create cannot apply after certified closure and recovery.
- New scope admission uses the recovered issuance watermark, including when no client learned the earlier result.
- Replay reconstructs the guard book using original inputs and does not rerun external effects.

## Tools

Use TLC 2.19 with a single worker, a 512 MiB heap, and 60 seconds per case.
Use Lean 4.35.0 for the model composition.
