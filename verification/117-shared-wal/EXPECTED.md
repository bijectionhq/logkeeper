# Expected results

TLC 2.19 from the pinned 1.7.4 release and Lean 4.35.0. The checker bounds and abstraction boundaries are in the [study](README.md#models-and-bounds). Steps count transitions after the initial state. A dash indicates a case specific to the other layout.

## Passing baselines

| Model | Invariants checked | A distinct states | B distinct states |
| --- | --- | ---: | ---: |
| VoterWAL | `PromiseDurable`, `AcceptDurable`, `ExactDemux`, `IsolatedCoverage` | 11,473 | 389,144 |
| WALAgreement | `PrefixAgreement`, `QuorumAtOneBallot`, `OneCoveringSync`, `SyncCount` | 1,538 | 7,954 |
| WALErasure | `NoResurrection`, `ExactRecovery`, `NoPlaintextAfterDeadline`, `D02HeldView`, `NeighbourUnchanged`, `ScopedCleanup`, `CiphertextOnly` | 48 | 78 |

## Reachable executions

These are counterexamples to the negation of a desired state in a baseline, separate from the mutation checks.

| Witness | Observation | A steps | B steps |
| --- | --- | ---: | ---: |
| `WALWitness` | Power loss discards an uncovered tail after both groups have replied to accepts. | 14 | 12 |
| `TwoGroupTearWitness` | One shared barrier covers both promises. Both reply, then the crash discards a later tail containing both groups. | — | 8 |
| `QuotaWitness` | Group 1 exhausts its quota. Group 2 replies to its second accept. | 15 | 14 |
| `QuarantineWitness` | Group 1's durable bytes are quarantined. Group 2 replies to its second accept. | 15 | 14 |
| `ChangedMajorityWitness` | Voter 1's AZ is lost. Voters 2 and 3 choose exact extensions in both groups. | 53 | 45 |
| `BatchedQuorumWitness` | Four choices agree after the AZ loss. Each barrier covers both groups, for eight barriers total. | — | 45 |
| `DeadlineWitness` | Recovery crashes and reopens after revocation. Scoped compaction and both new appends succeed. The old archive physically retains unreadable ciphertext. | 9 | 9 |

## Negative controls

| Fault | Invariant violated | Why it fails | A steps | B steps |
| --- | --- | --- | ---: | ---: |
| `early-promise` | `PromiseDurable` | Reply before covering the exact promise. | 2 | 2 |
| `early-accept` | `AcceptDurable` | Reply before covering the exact accept. | 5 | 5 |
| `wrong-group` | `ExactDemux` | Recovery assigns a persisted frame to the other group. | — | 4 |
| `cross-frontier` | `PromiseDurable` | Tear from one group's uncovered frame into the neighbour's covered promise. | — | 5 |
| `cross-frontier` | `AcceptDurable` | Tear from one group's uncovered frame into the neighbour's covered accept. | — | 8 |
| `global-truncate` | `IsolatedCoverage` | One corrupt group discards the shared frontier and with it the neighbour's reply coverage. | — | 5 |
| `quota-evicts-neighbour` | `IsolatedCoverage` | One group's exhausted allocation invalidates another group's covered record. | — | 5 |
| `empty-rejoin` | `PrefixAgreement` | Lose AZ 1 after the first choice. Voter 2 loses its state and votes under the same identity. Voters 2 and 3 choose a conflicting prefix. | 54 | 46 |
| `split-ballot` | `QuorumAtOneBallot` | Send a different proposal to one voter in the same ballot. | 45 | 39 |
| `no-coalesce` | `OneCoveringSync` | A voter with two queued updates covers just one on sync. | — | 3 |
| `double-barrier` | `SyncCount` | Add a separate second logical barrier to every sync. | 52 | 45 |
| `early-rotation` | `NoResurrection` | Commit while the old recovery path is still crash-selectable. | 3 | 3 |
| `stale-append` | `ExactRecovery` | A successor append uses the old generation after the cut. | 5 | 5 |
| `revoke-hold` | `D02HeldView` | Drop the admitted hold at rotation. | 4 | 4 |
| `key-alias` | `NoPlaintextAfterDeadline` | The old generation remains independently openable after revocation. | 5 | 5 |
| `raw-archive` | `NoPlaintextAfterDeadline` | A persisted plaintext copy survives key destruction. | 6 | 6 |
| `raw-archive` | `CiphertextOnly` | Persist raw payload bytes. | 1 | 1 |
| `shared-key` | `NeighbourUnchanged` | Revocation also disables the neighbour's generation. | 5 | 5 |
| `copy-obsolete` | `ScopedCleanup` | Retain an obsolete erased-tenant frame in the compacted WAL. Its ciphertext is still unreadable. | 6 | 6 |
| `drop-neighbour` | `NeighbourUnchanged` | Omit the neighbour's frames from the shared replacement. | — | 6 |

The eight Lean axiom reports contain only standard axioms. The two Lean controls remove demultiplexing and relax reply admission. They fail at the designated proof of `recovery_respects_scope` and `reply_survives_torn_tail`, respectively.
