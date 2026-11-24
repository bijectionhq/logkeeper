# Expected results

Lean 4.35.0 and TLC 2.19 from the pinned 1.7.4 release. Counts are for
the [stated bounds](README.md#tlc-model-and-bounds). Witness and control
lengths count transitions after the initial state.

## Lean

The Lake package builds. The 21 stream-journal reports, nine replacement
reports, seven WAL reports and one Study 117 bridge report contain only
standard axioms. The reports include the two-keeper commit, split install
and background checkpoint witnesses.

| Control | Failing check |
| --- | --- |
| Append without complete Sync | `append_requires_sync` |
| Two identities at the same promised epoch | `seal_tie_has_same_identity` |
| Rank by the last record's epoch | `recovery_rank_is_synced_then_tail` |
| Trim beyond the local head | `trim_below_head` |
| Read through the accepted tail | `read_returns_exact_committed_records` |
| Reuse a round from before invocation | `confirmed_round_is_fresh` |

## Passing TLC baselines

| Scenario | Distinct states |
| --- | ---: |
| rules | 26 |
| rank | 18 |
| protocol | 27,083 |
| wal | 544 |
| handoff | 17 |
| retention | 23 |
| replacement | 86 |

## Reachable TLC executions

The invariant names deny a desired state. The reported violation proves
that state is reachable with the baseline guards.

| Witness | Observation | Transitions |
| --- | --- | ---: |
| `NoProtocolWitness` | The first reply is lost, a shared tail tears, a retry succeeds, an AZ is lost, a zombie request is attempted, a learner is repaired, and head returns 2. | 33 |
| `NoNonWriterWitness` | A non-writer returns 2 with fresh Check and commit coverage. | 31 |
| `NoWalWitness` | One barrier covers both streams, both reply and a later tail from both streams tears. | 8 |
| `NoDelayedAppendWitness` | The original writer's delayed second accept succeeds at the unfenced third keeper after the new seal publishes the same record. | 16 |
| `NoTrimReadWitness` | One keeper returns the committed record below the completed trim's floor and hides its accepted tail. | 19 |
| `NoSplitInstallWitness` | One survivor installs, the old route is refused, and the retry on the installed route succeeds. Neither route has a quorum. | 25 |
| `NoReplacementRecoveryWitness` | The sweep resumes from a split and promotes the learner with the acknowledged prefix on all three keepers. | 27 |
| `NoSecondLossWitness` | A second loss after promotion leaves two copies of the transferred record. | 26 |
| `NoNewEnsembleWriteWitness` | After a split and recovery, a later epoch publishes a new record and a read returns both records. | 36 |

## TLC controls

| Fault | Violated invariant | Transitions |
| --- | --- | ---: |
| recreate | `CreateGuard` | 24 |
| seal-lower | `SealOrder` | 17 |
| seal-tie | `SealHolder` | 4 |
| sync-promise | `SyncPromise` | 5 |
| sync-truncate | `SyncRetainsCommit` | 18 |
| sync-incomplete | `SyncComplete` | 6 |
| append-promise | `AppendPromise` | 16 |
| append-unsynced | `AppendSynced` | 3 |
| append-gap | `AppendCondition` | 8 |
| append-conflict | `AppendCondition` | 13 |
| append-retry | `AppendRetry` | 14 |
| trim-epoch | `TrimEpoch` | 20 |
| trim-above | `TrimCommit` | 12 |
| trim-above | `KeeperBounds` | 12 |
| check-mutates | `CheckPure` | 11 |
| read-below | `ReadFloor` | 22 |
| read-uncommitted | `ReadExact` | 10 |
| delete-forgets | `DeleteTerminal` | 23 |
| last-entry | `WinnerRank` | 17 |
| single-accept | `QuorumCommit` | 10 |
| uncommitted-watermark | `CommittedPrefix` | 10 |
| empty-rejoin | `RecoverableAfterLoss` | 13 |
| skip-repair | `BothSurvivorsAfterRepair` | 19 |
| seal-short | `ServedSeal` | 19 |
| stale-head | `HeadLinearizable` | 14 |
| learner-votes | `LearnerExcluded` | 14 |
| early-wal-reply | `ReplyDurable` | 2 |
| cross-frontier | `ReplyDurable` | 5 |
| wrong-stream | `ExactDemux` | 4 |
| read-uncommitted (retention) | `RetentionReadCommitted` | 19 |
| stale-route (replacement) | `StaleRouteRefused` | 24 |
| count-wrong-route (replacement) | `OneEnsembleAuthority` | 3 |
| early-learner-install (replacement) | `LearnerAfterSurvivors` | 23 |
| learner-append (replacement) | `LearnerCannotAppend` | 23 |
| skip-repair (replacement) | `PublishedOnSurvivors` | 19 |
| append-promise (replacement) | `ReplacementFencesOldAppends` | 16 |
| read-uncommitted (replacement) | `ReplacementReadExact` | 31 |

## TLC specification probes

| Interpretation tested | Violated invariant | Transitions |
| --- | --- | ---: |
| Immediate D03 with two acknowledgements | `BothSurvivorsAfterLoss` | 13 |
| Writer answers with its locally known cut after a lost reply | `HeadLinearizable` | 16 |
| Seal returns only the advertised commit watermark | `DelayedAppendAlreadyCommitted` | 16 |
