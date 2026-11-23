# Study 09 report · Stream contents and shared capacity observations

2026-11-22

## Verdict

Stream-scoped kernel effects protect the observed record projection.
A fully shared durable budget can still expose contention through admission responses.
Protecting an immediate reservation means preventing unrelated irrevocable writes from consuming its space.

## Properties and controls

Lean checks four general theorems with only standard axioms.

| Theorem | Finding |
| --- | --- |
| `record_projection_ignores_other_streams` | An arbitrary finite sequence of writes to other streams leaves the selected stream's record projection identical. |
| `pooled_admission_distinguishes_other_load` | For any positive cap, the same one-record request with no prior own usage is accepted when other usage is zero and refused when other usage fills the cap. |
| `reservation_protects_eligible_admission` | For any charges and capacities, a correctly reserved request fits when unrelated usage stays within its complementary budget. |
| `borrowed_durable_capacity_blocks_guaranteed_arrival` | Once irrevocable work fills the shared pool, no positive new allocation can fit. |

The broadcast-write and weakened reservation variants each fail the declared proof.
The admission distinction is a concrete two-run counterexample to full overload noninterference under work-conserving pooling.
It uses equal low inputs and different background occupancy.

## Decision and residue

Logkeeper protects stream contents and authorization.
Admission status and latency share documented aggregate contention channels unless their resources and observable scheduling are independently reserved.
An unconditional durable reserve cannot be loaned against already acknowledged work.
Borrow only capacity that can be reclaimed before the guarantee applies, or define a weaker conditional service objective.

This proof does not model the I/O scheduler, a capacity reservation implementation, black-box timing observations, or actual authentication.
It supplies conditions for the scheduler and admission refinement.

## Reproduction

```sh
LEAN_BIN=/path/to/elan/bin/lean python3 verification/09-isolation/run.py
```
