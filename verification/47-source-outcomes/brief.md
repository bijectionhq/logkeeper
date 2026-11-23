# Study 47 · Retain move decisions until their participants settle

2026-11-23

## Question

Can Logkeeper recover and compact exact source move decisions while disconnected participants still owe refunds or custody?

## Sources

Use the [requirements](../requirements.md), [activation obligation recovery](../37-obligation-home/report.md), [certified replay](../39-certified-activation-replay/report.md), [compact provider tickets](../41-provider-ticket-compaction/report.md), and [the funded seal](../46-funded-source-seal/report.md).

## Model and comparison

Compare individually compacted source outcomes with a representation that keeps exact rows above one contiguous settled prefix.
Keep each live or unsettled attempt in a reserved source result slot.
Model authenticated participant receipts as exact bindings to the decision and the local action that discharges that participant.
Separate the ordered source book, a learner's older view, and quorum recovery of the exact chosen prefix.
Abstract endpoint custody and charging as certified in the previous studies.

## Properties and acceptance

- Recover an exact source decision and its outstanding consumers even before the old learner applies it.
- Keep exact evidence while any participant still needs it.
- Refuse wrong-scope acknowledgments, lost or offered evidence, and premature compaction.
- Compact an individually settled outcome behind a disconnected earlier one and reuse only its result slot.
- Report stable closure for an issued compacted identity. Preserve original outcomes while owed and distinguish unissued future identities.
- Preserve the compact interpretation across exact recovery without contacting participants.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap and a 60-second limit per case.
Use Lean 4.35.0 and reuse the ranked configuration proof from Study 32.
