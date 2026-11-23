# Study 97 · Keep settlement workspace free of remote waits

2026-11-23

## Verdict

Reserving capacity for settlement is insufficient if an operation can hold the reserve while waiting for an unrelated authority.
One such wait can indefinitely prevent the refund of an independently ready charge in the same pool.
Keep the wait in the original funded obligation.
Use shared local publication workspace only after the exact disposition evidence is locally verifiable, then apply the ordinary exact refund transition.
A dedicated workspace per obligation also permits independent progress when fully funded, at a reservation cost that grows with the number of live obligations.

The same rule applies to funded cleanup for both read designs.
A scope awaiting its own provider keeps its existing charge.
Other eligible scopes have a path to refund at full ordinary occupancy.
Let the owner schedule ready work on bounded slots with one rotating cursor.
Repeatedly racing for the shared workspace can starve a ready refund even when each acquire action has weak fairness.

## General proofs

Lean 4.35.0 checked nine workspace theorems and seven scheduling theorems with standard axioms only.

| Claim | Evidence and premises |
| --- | --- |
| A staged row has exact local evidence and is still charged. A row awaiting required evidence cannot take the workspace. | `a_stage_requires_local_evidence`, `a_workspace_holder_is_already_ready`, and `a_waiting_row_cannot_take_the_shared_workspace`. Local evidence names a present row with its own closed gate and verified erased state. |
| Every workspace step either leaves the durable pool alone or uses its existing exact refund. This holds for arbitrary finite traces. | `every_workspace_step_is_a_stutter_or_exact_pool_refund` and `a_workspace_trace_refines_the_original_physical_pool`. The publication transition matches the original row against the current ledger. |
| Physical usage fits the ordinary limit plus one reserved publication peak. | `local_publication_fits_its_own_reserved_peak`. The initial pool is sound and the actual maximum bytes for the local publication fit the reserve. |
| A local restart clears tentative workspace state and preserves every original charge. A ready charge can be released at full ordinary occupancy while a preceding row remains pending and charged. | `restart_returns_the_workspace_and_keeps_all_original_charges` and `ready_refund_progresses_at_capacity_while_its_peer_waits`. Restart is a modeled durability boundary. The second theorem constructs a complete execution with an empty workspace. |
| More than one live obligation with a positive dedicated workspace cannot be backed by one workspace of that size. | `reserving_a_positive_workspace_per_obligation_cannot_fit_one_workspace`. Each reservation must be simultaneously available to its owner. |
| The nearest ready slot exists for any nonempty ready set. A continuously eligible slot is bypassed fewer times than the number of slots, even if other slots change eligibility. | `every_nonempty_ready_set_has_a_next_slot` and `a_persistently_ready_slot_cannot_be_bypassed_slots_times`. Advance the cursor at every selection and retain a fixed slot and identity for the waiting job. The bound measures turns rather than elapsed time. |

The Lean control allows staging without local evidence.
The evidence law fails at its designated proof step.

## Comparative models

TLC 2.19 exhausted four bounded passing configurations.
Each starts at full ordinary occupancy with two or three already funded obligations at one pool.
Each can refill ordinary space after refund and lose tentative workspace to one local restart.
Storage sizes are expressed in unit slots.
The temporal checks give weak fairness to each receipt arrival permitted by the scenario and to staging and publication for each job.
There are finitely many jobs and one possible restart in each run.

| Schedule | Result |
| --- | --- |
| Shared reserve with one older indefinitely stalled peer | The ready refund completes in the eight-state configuration. The older charge remains. |
| Shared reserve with three ready obligations | All complete in the 88-state configuration. |
| Shared reserve with three obligations and one initially unavailable proof that eventually arrives | All complete in the 116-state configuration. The other ready jobs need no reply from the delayed peer. |
| Dedicated reserve with one older indefinitely stalled peer | The ready refund completes in the eight-state configuration with two units of workspace reserved for two jobs. The shared reference needs one. |
| Restart, refund and ordinary refill while the peer stays stalled | The acceptance witness takes five transitions. |

| Deliberate weakening | Counterexample |
| --- | --- |
| Give one shared slot to a job still waiting for evidence | After one transition the stalled job owns the slot. A fair temporal trace shows that even a restart can be followed by the same wait while the ready refund never runs. |
| Let ordinary work occupy the entire hard budget | A positive-cost publication has nowhere to stage. The initial full state admits a temporal counterexample. |
| Demand new ordinary headroom at publication | The ready job occupies its reserved space but publication waits indefinitely for the headroom its own refund would create. |
| Substitute another job's physical disposition | Stage and publish a refund for an unverified original in two transitions. |
| Return the charge on tentative staging | Stage and refund before durable publication in two transitions. |

A publication that fits wholly inside its already charged durable record can meet the same budget rule.
The required reserve is for the actual peak of all additional local bytes, including any selectable and staged coexistence.
The comparison does not establish a latency objective or a provider-specific footprint.

### Continuing admission

The separate dispatch model has one parked obligation, one continuously ready target, and a slot that continually receives new ready jobs.
Local publish and each dispatch action have weak fairness.
With uncoordinated acquisition, the recurring job continually takes the workspace, disabling the target on every busy interval.
A scan that chooses the next increasing allocation serial and wraps only when it sees no newer serial has the same failure when the target is behind its cursor and new work keeps arriving ahead.
These give two temporal counterexamples.
A fixed bounded round-robin scan publishes the target while recurring work continues in the seven-state passing configuration.
A finite issuance field eventually stops new work, but waiting for its exhaustion provides no bound in terms of the number of live slots.
The cyclic index is a scheduling position.
The refund still validates the exact non-reused identity of the physical allocation at publication.

## Amendments

[A388–A391](../amendments.md#study-97--2026-11-23) bind local settlement workspace to ready work, the physical publication budget, and a bounded turn through the ready set.

## Acceptance programs

1. Fill ordinary capacity with two live charges.
   Leave the older charge waiting for an unreachable authority and deliver exact locally verifiable disposition for the newer one.
   Refund the newer charge through the original pool while the older charge stays funded.
2. Lose the tentative workspace during refund staging and reopen the local authority.
   Preserve both original charges, restage from exact evidence, publish the ready refund, and reuse the returned ordinary space.
   Refuse evidence for the older charge until its own proof becomes available.
3. Leave a ready refund in its stable local slot while another slot refills continuously.
   Dispatch the ready refund within one turn under continuing local service.

## Residue

Lean models one local settlement lane and projects its state changes onto the existing pool ledger.
TLC interleaves ordinary refill but bounds ongoing work, evidence receipt and crashes.
The separate scheduling proof handles recurring competitors for a fixed slot set.
The adapter still needs to maintain stable scheduling slots and a continuing cursor through the selected local service interval.
The actual local publication protocol must either complete under its local authority or vacate its workspace safely.
If durable staging survives a crash, reuse must preserve every selectable root and stay within the precharged peak.
Transport buffering, proof materialization, local quorum durability and the full encoded workspace cost still need a refinement.
A physical operation that itself requires unavailable evidence cannot refund.

## Reproduction

Use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/97-settlement-workspace/run.py
```

[run.py](run.py) records commands, configurations and raw counterexamples under .results/.
