# Study 33 · Recover the successor activation slot

2026-11-22

## Question

How can a successor choose and recover exactly one installation when candidate images are staged concurrently, a quorum reply is lost, or a zone fails?

## Sources

Use the [requirements](../requirements.md), [target install composition](../13-install-durability/report.md), [fixed-group ballot recovery](../27-prefix-consensus/report.md), and [configuration closure](../32-configuration-closure/report.md).
Use RTDB Multi's durable journal identity, write quorum, and recovery contracts. [RTDB Multi at fc6da3a4a3](https://github.com/bijectionhq/rtdb/blob/fc6da3a4a3/allium/rtdb-multi.allium#L449-L474)

## Model

Use one authorized successor intent and one activation slot with a certified target membership.
Represent two exact eligible installation images and three durable target voters across distinct AZs.
Separate materialized readiness, per-ballot promises and votes, an implicit quorum choice, and learner publication.
Prepare samples are durable and retain the latest accepted value.
Profile later leader terms after a loss and keep delayed messages from earlier terms possible under their local promises.

Compare data-bearing votes against independently quorum-protected references and metadata-only votes.
Model the protected reference's holders explicitly.
Model loss of an image after phase one and loss of optional local staging before a delayed vote.
For placement pressure, compare allowing one local image with keeping space for a second image while the current accepted binding is still live.
Give fair recovery a stable last term after the modeled fault.

## Properties and acceptance

- A single exact seed can be chosen and exposed in the slot.
- Every recovery majority can obtain a chosen seed despite a lost result and one AZ loss.
- Losing the only copy of an unchosen local acceptance can permit a fresh higher ballot to select a different value.
- Losing a phase-one donor can require a fresh ballot even when the old reports are authentic.
- Higher promises preserve the exact physical backing of accepted state.
- Replace an older accepted binding within bounded staging capacity, then reclaim its unneeded copy.

## Tools and evidence

Use TLC 2.19 with one worker, a 512 MiB heap, and a 60-second case limit.
Use Lean 4.35.0 for unbounded local histories and exact single-slot agreement.
Record normalized configuration identities, all counterexamples, and the distinct assumptions of sealed predecessor recovery and successor activation.
The model trusts exact authorized candidate descriptors and a fixed certified target voter family for this slot.
