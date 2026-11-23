# Ordered append budgets (L6)

The shipped `budget::record_charge` and `budget::append_debit` compute the
charge and debit returned to the ordered append arm. The harness also checks
the original `admission::debit` used by append, window funding, and snapshot
recovery. This area extends the budget slice of `ordered_admission` while
keeping its manifest and controls independent.

| Lean reference | Rust projection and Verus law |
| --- | --- |
| `Logkeeper.OrderedBudgets.referenceCharge` and `recordCharge` | Pass the payload length and either the number of explicitly declared names or `None` for legacy opaque references. Each explicit list pays four bytes plus 32 per name, including four bytes for an empty explicit list. `record_charge_matches_reference` checks the total and overflow refusal. |
| `Logkeeper.OrderedBudgets.fundedBudget` and `appendBudget` | Map `State.spent`, `retained_bytes`, and `maintenance_retained` to the budget fields. Ordinary retained bytes plus the window's unspent bytes fit ordinary capacity, with the maintenance sum separately bounded by its reserve. `admitted_ordinary_append_preserves_funding` and `maintenance_funding_is_independent` check the executable debit and exact resulting endpoints. |
| `Logkeeper.OrderedBudgets.funding_new_window` and `trace_preserves_funding` | A replacement starts with zero spend after the retained ordinary total and the new paid window fit ordinary capacity. The Verus `funding_new_window` law checks the debit used by that arm. The Lean trace theorem includes append, window funding and trim. |

The charge contract takes the name-count limit already checked by the
reducer or snapshot decoder. The model starts from a funded state and the
reducer adapter installs the debit's fields in the chosen class.
Checkpoint reference rows and fence rows use the separate object-control
budget. Provider and replica media consumption require independent bounds.

The controls omit reference charges, omit the active-window limit, and
let maintenance debit the ordinary capacity. Lean reaches a full paid
window and witnesses both an undercharged reference list and an underfunded
maintenance append.
