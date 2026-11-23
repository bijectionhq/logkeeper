# Study 39 report · Recover activation decisions from certified evidence

2026-11-23

## Verdict

Choose the activation acknowledgment or cleanup together with its validated historical evidence.
Recover its exact command from the ranked sealed prefix even when the old learner never applied it.
Replay from the certified basis using that command's attachment.
A refusal with no eligible attachment stays refused even if a counterpart supplies the fact later.
The later fact can authorize a new ordered command.

Discharging a copy needs the original custodian's committed refusal fence and its exact physical disposition.
If bytes or in-flight work remain, an independently durable custody record accounts for them.
Erasure completion still requires exact absence.

## Bounded comparison

The TLC model has one source record, one original copy with a possibly queued acquisition, and a target journal of at most two or three decisions.
Its chosen command list and lagging learned index model the input and local view of the ranked recovery protocol.
In the disconnected cases sealing makes the two counterpart lookups unavailable to the successor.
Their durable state can still change independently.
Quorum choice, the commit of the original fence, and exact physical disposition are atomic model boundaries.

| Journal bound | Counterpart path after seal | Distinct states | Checked result |
| --- | --- | ---: | --- |
| 2 | Available | 10,743 | Six safety laws and installation after seal hold. |
| 2 | Unavailable | 10,743 | Same laws hold. |
| 3 | Available | 98,243 | Same laws hold. |
| 3 | Unavailable | 98,243 | Same laws hold. |

Safety covers original outcomes and effects, grounded acknowledgment, exact cleanup evidence, refusal of delayed recreation, and physical charge for present bytes.
Installation assumes weak fairness of recovery and an available exact target cut.

| Amendment | Weakening | TLC evidence |
| --- | --- | --- |
| A148 | `learned_only` | Copy the learned view and lose a hidden chosen command in three transitions. |
| A149 | `reread_external` | Replay a refusal as a success by substituting external state for its ordered input in four transitions. |
| A149 | `unavailable_as_absence` | Replay a chosen success as refusal during a counterpart outage in four transitions. |
| A149 | `lookup_required` | A fair execution stutters after sealing because recovery requires remote lookups. |
| A150 | `accept_foreign` | Clear an obligation against a foreign receipt in one transition. |
| A150 | `absence_as_fence` | Clear a momentarily empty slot in one transition. A two-transition check follows through and recreates the copy from its queued request. |
| A151 | `fence_as_disposition` | Materialize the copy, commit its fence, and clear the plan while its physical bytes remain uncharged in three transitions. |

The positive traces cover offline recovery of a hidden cleanup in five transitions, preservation of a historical refusal when complete disposition evidence arrives before replay in five, refusal of a queued acquisition after certified cleanup in six, and transfer of the physical charge while bytes remain in six.

## General proofs

Lean checked eighteen theorems using standard axioms only. [Replay proofs](CertifiedActivationReplay.lean) · [Custodian proofs](CopyFence.lean)
The ordered reducer consumes an exact attachment and projects acknowledgment and cleanup onto the Study 38 activation reducer.
Arbitrary extensions of the two-command-family replay preserve the earlier outcomes and never recreate a discharged copy plan.
Under ranked handoff and installed current-quorum coverage, any current recovery majority contains a surviving voter with the exact recovered history, including every old chosen prefix.
Replaying it preserves the old outcomes and discharged copy plans.

The custodian proof checks absence of the exact grant, durable issuance, and closure by the active spent marker or floor when the exact channel remains active.
Those conditions survive every custodian transition, including compaction and route reuse, over arbitrary finite traces.
Matching the original full receipt and recovering the exact committed image yields the fence at a voter of any recovery majority.
A composite settlement certificate adds exact physical absence or a durable charge at the custodian.
The acceptance theorem uses it to introduce the external fence evidence in Study 38 and order the corresponding cleanup at the open current owner.

The Lean controls fail when a receipt ignores the immutable binding, source intake accepts acknowledgment evidence before its durable record, or a settlement certificate drops the physical disposition.

## Remaining obligations

The ranked theorem assumes authenticated closure reports, exact installed-quorum coverage, and the replay basis and immutable plan bindings shared with the original decision.
The model covers acknowledgment and cleanup in the target journal.
Projection of the other ordered operations remains in the earlier models.
The wire format, exact command and checkpoint encoding, and storage proof adapters still need refinement.
The custodian proof closes future admission of that registration.
Disposal and initial allocation may also involve existing I/O or shared objects.
The exact absence predicate includes completion or effective stop of existing I/O. The durable charge predicate covers each remaining byte and physical effect.
The finite model exercises both disposition branches with one copy slot and abstracts bytes as presence.
Provider-specific evidence and actual capacity composition remain open.
[Study 40](../40-provider-io-closure/report.md) checks provider-side I/O closure and supplies the disposition proof used by this study.

Apply [A148–A151](../amendments.md#study-39--2026-11-23).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner writes settings and traces to the ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/39-certified-activation-replay/run.py
```
