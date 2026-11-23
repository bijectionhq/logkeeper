# Study 100 · Recover returned capacity in the installed quorum

2026-11-23

## Verdict

The successor must replay the exact ranked pool history through the installed cut, including any already chosen charge that spent an earlier refund.
It can reproduce the original refund receipt after that credit was used.
A new charge checks the current applied pool in the installed order.
It may materialize only after its own successful decision.
Historical reconciliation and new capacity admission therefore have different inputs.
Both use the same ledger and neither needs a separate allocator to recognize earlier choices.

## Evidence

Lean 4.35.0 checked six theorems with standard axioms only.
The ranked successor proof uses the exact durable installed basis at a survivor on any current recovery majority.
For any finite chain of valid handoffs, that basis includes the whole earlier chosen prefix.
The mount ties the installed command list to a real trace of the existing typed settlement and locally crash-selectable journal models.
For the chosen selector, recovery reconstructs that exact applied ledger and preserves its bounds.
The constructive full-pool program reports the old refund after the dependent debit spent it, and refuses every additional positive debit at that cut.
A Lean control that matches only the length of a cut fails the exact-command law.

TLC 2.19 holds old reports fixed until the exact successor voters install the selected basis.
Readiness is monotone after exact media preparation, and all eligible required actions receive weak fairness.
The old accepted order may contain a longer exact prefix than the learned receipt.

| Case | Bounded result |
| --- | --- |
| Hidden chosen refund and loss of each AZ in turn | Three passing configurations of 110 states each. Reissue the refund and admit an eligible new charge. |
| Hidden chosen refund and hidden dependent debit, with each AZ lost in turn | Three passing configurations of 108 states each. Reissue the historical refund and refuse a second spend. |
| Raw old staging without a vote | One passing configuration of 106 states. A recovered empty cut cannot turn staging into a refund. |
| Exact accepted minority reported during the fence | One passing configuration of 110 states. The target's exact quorum installation can adopt the ranked cut and make the refund available. |

| Weakening | Shortest failure |
| --- | --- |
| Recover only what the old coordinator learned | Lose the earlier chosen refund in eight transitions. |
| Recover the refund but discard its hidden dependent debit | Materialize a second charge in ten transitions. |
| Use the authentic refund receipt as reusable capacity | Materialize a second charge in eleven transitions. |
| Count the visible copy alone or substitute a same-length rival | Count an inexact install vote in five transitions in each case. |
| Permit effects from a staged refund | Materialize before a debit was chosen in five transitions. |
| Promote raw old staging at the ranked cutoff | Report an unselected refund in nine transitions. |

## Amendments

[A397–A400](../amendments.md#study-100--2026-11-23) bind the refund and dependent reuse to the exact ranked order and separate historical receipts from fresh authorization.

## Limits

The model recovers through an installed cut without subsequently chosen commands in the new scope.
Fresh admission in an already active scope must also apply its current chosen suffix before using the ledger.
The Lean media link requires install evidence to name an exact backed local trace.
The actual snapshot and frame codecs, two-selector media allocation, current-scope authorization, and durable quorum attestation remain refinement obligations.
The proof covers numeric debit admission.
The bounded materialization comparison abstracts the existing provider authorization and exact physical effect gate.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/100-ranked-pool-refund/run.py
```

[run.py](run.py) saves commands, exact configurations and raw traces under .results/.
