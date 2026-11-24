# Expected results

Reproduced with TLC 2.19 from the pinned 1.7.4 jar and Lean 4.35.0. Distances count transitions from the initial state. The runner accepts a negative result only when TLC reports the designated invariant, or Lean reports the designated proof obligation. Witness runs assert the complement of the target state.

## TLC baselines

| Run | Distinct states | Result |
| --- | ---: | --- |
| A, one attempt with replacement or rotation | 76,566 | All applicable invariants pass |
| B, one attempt with replacement or rotation | 202,456 | All applicable invariants pass |
| A, two attempts in one epoch | 8,484 | All applicable invariants pass |
| B, two attempts in one epoch | 34,430 | All applicable invariants pass |
| B with ordered named fallback, two attempts in one epoch | 38,018 | Includes `RetainedNamedAdmission` |
| B with lagging apply, one attempt with reconfiguration | 278,127 | Checks `CommittedPrefix` under the weaker contract |
| Exact dependency floor | 20 | `ReplayRetained` and `ObjectsRetained` pass |

`RetainedNamedAdmission` applies to A and the hybrid. A fully local named path can temporarily refuse a still-eligible basis.

## TLC witnesses

| Reached state | Invariant | A | B |
| --- | --- | ---: | ---: |
| Reply, release, and collect the old basis | `ServedAndCollectedWitness` | 7 | 11 |
| Read from the predecessor's held view after replacement and read from the successor | `AcrossReplacementWitness` | 7 | 10 |
| Use an old held view after rotation and before the deadline | `ViewBeforeErasureDeadlineWitness` | 4 | 7 |
| Use the held view at or after the deadline and receive an erasure error | `ErasedHeldViewWitness` | 6 | 9 |
| Return a clean successor view while the held old view returns the erasure error | `CleanAndErasedWitness` | 9 | 12 |
| Lose the first reply and admit the original basis under the replacement at a newer head | `SameBasisRetryWitness` | 10 | 13 |
| Lose a reply, expire the orphan and collect below the later cut | `OrphanExpiryWitness` | 9 | 11 |

| Reached state | Run | Invariant | Transitions |
| --- | --- | --- | ---: |
| Renew with two distinct active cuts and preserve the older cut | Local B | `ReportedMinimumWitness` | 9 |
| Refuse a still-resident named retry below the published floor | Local B | `BelowReportRetryWitness` | 11 |
| Serve and release two local reads with one shared renewal | Local B | `RenewedBatchWitness` | 10 |
| Serve the below-floor retry on an ordered hold at the same basis | Hybrid B | `OrderedFallbackWitness` | 12 |
| Finish a read on the older exact dependencies, then collect them | Exact dependencies | `FinishAndCollectWitness` | 7 |

## TLC negative controls

| Run | Weakened rule | Violated invariant | Transitions |
| --- | --- | --- | ---: |
| A | Select the lagging applied cut at the barrier | `LatestLinearizable` | 4 |
| A | Accept a barrier from a deposed writer | `FreshAuthority` | 3 |
| A | Trim through a live journal hold | `TrimPreservesHolds` | 4 |
| A | Collect an object behind a live journal hold | `CollectionPreservesHolds` | 4 |
| A | Retry an old named basis at latest | `SameBasisRetry` | 7 |
| A | Count explicit ordered release as free | `CostAccounting` | 4 |
| A | Revoke at rotation commit | `ErasureDeadline` | 4 |
| B | Admit a read after the serving deadline | `ServingDeadline` | 5 |
| B | Allow clock lag beyond the stated bound | `ServingDeadline` | 5 |
| B | Install a successor during the predecessor lease | `FreshAuthority` | 3 |
| B | Install a successor during the predecessor lease and miss its rotation cut | `LatestLinearizable` | 3 |
| B | Serve a lagging applied cut under a valid lease | `LatestLinearizable` | 4 |
| B | Expose an unchosen pending append | `CommittedPrefix` | 3 |
| B | Admit an unreported reader below the periodic report and trim | `TrimPreservesHolds` | 12 |
| B | Drop the report at lease expiry with a reader still active | `TrimPreservesHolds` | 8 |
| B | Collect despite the registered floor | `CollectionPreservesHolds` | 5 |
| B | Serve an old held view after key revocation | `ErasureDeadline` | 9 |
| B | Resample latest for a named retry | `SameBasisRetry` | 8 |
| B | Remove ordered fallback for a still-eligible named retry | `RetainedNamedAdmission` | 5 |
| B | Charge the local capture as an ordered command | `CostAccounting` | 2 |
| B | Count the shared renewal as a free journal entry | `CostAccounting` | 2 |
| Hybrid B | Resample latest for a named retry | `SameBasisRetry` | 8 |
| Exact dependencies | Report the logical read cut to the journal trimmer | `ReplayRetained` | 4 |
| Exact dependencies | Report the logical read cut to the object collector | `ObjectsRetained` | 5 |

## Lean

All three theorems compile using only standard axioms. Each mutated definition fails its named proof.

| Theorem | Control |
| --- | --- |
| `admission_precedes_cutover` | Omit the drift margin from local admission |
| `report_covers_existing_borrow` | Report the applied cut alone despite an older borrow |
| `report_covers_later_borrow` | Admit a later borrow without checking the reported floor |
