# Ordered cohort confirmation and repair

The harness imports [the shipped cohort predicates](../../../src/ordered/cohort.rs).

| Shipped guard and call site | Lean reference in [OrderedGuards](../../lean/Logkeeper/OrderedGuards.lean) | Verus control and failing law |
| --- | --- | --- |
| `accept_quorum` in `Group::confirm` | `OrderedCohort.accept_quorum`, the counted form of `JournalRefinement.Majority` | `acknowledge-one-accept` → `accept_quorum_is_majority` |
| `has_paid_repair_quorum` in `validate_tickets` | `OrderedCohort.has_paid_repair_quorum` | `seal-with-one-paid-ticket` → `seal_requires_paid_successor_quorum` |
| `may_extend` in `State::apply` | `OrderedCohort.may_extend` | `allow-fresh-command-after-seal` → `sealed_cohort_refuses_new_decisions` |
| `matches_chosen_seal` in the `seal_image` and `install_image` calls for cohort repair | `OrderedCohort.matches_chosen_seal` | `seed-from-unsealed-predecessor` and `seed-a-different-successor` → `repair_requires_the_chosen_destination` |

The confirmation count is the number of replies matching the prepared voter's identity, ballot, prefix digest, mirrored-slot check and readback mode.
The funding count comes from distinct configured successor voters whose signed tickets name that successor and the required reserved bytes.
Both counts use the installed roster size.
The seal predicates project the recovered state's `successor` directly, with the digest standing for the exact successor configuration.
The guard in `State::apply` applies to fresh execution after the retained-receipt branch.

The checked decisions take authenticated, distinct vote and ticket counts and the replay-selected state as inputs.
The call-site audit identifies how these values are obtained.
The [prefix agreement area](../prefix_agreement/README.md) checks exact vote collection, the final configured majority and ranked recovery, and exercises the coordinator with recorded traces.
An arbitrary-execution refinement to `PrefixAgreement.Chosen` and `SelectionFence.DurableReports` remains open, including AZ placement and live fault classification.
The paid ticket check covers physical repair of one journal cohort. [Study 70](../../70-distributed-preparation/report.md) additionally requires an entire vector across independent pools for an installed move.

The [mechanical link inventory](../../link/inventory.md) lists the checked
projections and the remaining Lean correspondence for this area.
