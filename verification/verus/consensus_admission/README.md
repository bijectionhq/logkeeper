# Consensus admission verification

`proof.rs` imports the shipped `src/stream/consensus/decisions.rs`. The keeper-hosted consensus code calls these functions on its real paths. `network.rs` uses them to classify each decoded peer request and to split oversized AppendEntries batches. `keeper/admission.rs` uses them for replication message and control admission and for every meter update and release. `keeper/ingress.rs` uses them to check each received batch, `storage/space.rs` for disk floors and suffix slots, `storage/wal.rs` for durable lane rotation and `storage/mod.rs` for the restart vote. `keeper/recovery.rs` uses them to admit an operator recovery and to choose its term, `state.rs` to choose its fence epoch, and `ownership.rs` to decide whether a retried recovery, or another move from the same source, restages a replacement. `keeper/liveness.rs` and `keeper/repair.rs` use them to decide when a keeper is dead and how long a stream whose repair or wake failed waits. `keeper/ingress.rs` also uses them to decide which replicas vote and which peers it refuses without an answer. `keeper/incarnation.rs` uses them to recognize a keeper ID reused on new media, `keeper.rs` to decide whether a keeper registers a replica it does not hold, and `network.rs` to decide whether a campaign counts a peer's grant. `keeper/park.rs` uses them to decide when a group is idle, when a leader asks its followers to park and when a follower accepts, and `keeper/ingress.rs` to decide how a parked replica answers. `keeper/repair.rs` uses them to decide which voters are silent and which learners are stale, to order the repair queue and start its work, and to decide when a copy looks for a retiring proof and whether that proof names it; `keeper/replicas.rs` uses the same check before it detaches the copy. `assignment.rs` uses them for the load ceiling, the roomy test and the two-live-voters rule, `keeper.rs` to decide a handoff to the writer's preferred voter, `state.rs` to decide a seal under the recovery fence, `storage/media.rs` to choose the trusted boundary slot, and `storage/wal/segmented.rs` to check the checkpoint against that boundary and to decide each replayed frame. `keeper/lease.rs` uses them for the liveness lease and the gate on campaigning, leading and serving, `authority.rs` for granting renewals, and `keeper/recovery.rs` for the wait before a recovered configuration serves. The harness uses no custom axioms, assumptions or external bodies.

`laws.rs` states independent laws over the shipped functions. Each law names the checked Lean theorem it refines.

| Law | Lean theorem | Shipped functions |
| --- | --- | --- |
| `payload_append_is_never_control` | `PeerBudget.control_header_cannot_dispatch_payload` | `carries_application`, `peer_lane` |
| `vote_and_metadata_only_append_are_control`, `snapshots_use_bulk` | `PeerBudget.vote_and_empty_append_are_control` | `carries_application`, `peer_lane` |
| `admitted_body_preserves_budgets` | `PeerBudget.reserve_body_preserves_budget` | `body_charge`, `admits_body` |
| `one_sender_leaves_the_others_their_share` | `PeerBudget.one_sender_cannot_spend_others_remaining_body_capacity` | `body_charge`, `admits_body` |
| `one_sender_leaves_the_others_their_frames` | Frame share of `PeerBudget.one_sender_cannot_spend_others_remaining_body_capacity` | `body_charge`, `admits_body` |
| `release_is_exact` | Release half of `PeerBudget.reserve_body_preserves_budget` | `body_charge`, `admits_body`, `meter_admit`, `meter_release` |
| `one_sender_leaves_control_work_for_others` | Control share of `PeerBudget.saturated_data_admits_control_and_maintenance` | `admits_control`, `meter_admit`, `meter_release` |
| `ordinary_admission_keeps_reserved_classes_feasible` | `PeerBudget.saturated_data_admits_control_and_maintenance`, `Headroom.Follower.replication_preserves_maintenance_and_control` | `fits` and the class floors |
| `suffix_admission_respects_the_limit` | Suffix projection of `Headroom.Follower.trace_preserves_all_budgets` | `suffix_admits` |
| `rotation_serves_a_ready_lane_within_five` | `PeerBudget.persistent_lane_served_within_five` | `probe`, `after` |
| `oversized_batches_shrink` | Sender resize in the admission contract | `fit_append` |
| `restart_never_restores_leadership` | `RestartRead.present_never_restores_leadership` | `demotes_vote` |
| `accepted_batches_are_consecutive` | Decoded-cut validation before dispatch | `indices_follow`, `terms_ordered`, `consecutive_cut` |
| `recovery_needs_acknowledgement_and_no_live_quorum` | Operator recovery admission (design section R): the healthy survivors are fewer than a quorum of three or five | `allows_recovery` |
| `recovery_outranks_the_lost_history` | Recovery term and fence epoch above the survivor's history | `recovery_term`, `recovery_epoch` |
| `a_recovery_restages_only_its_own_aborted_copy` | A retried recovery reuses a replacement only when no other history could have written to its copy | `restages_recovery` |
| `only_certified_members_serve_reads` | A copy serves applied pages only once its placement is certified (TLA+ CE-3, `RecoverySingleReturnSnap`) | `serves_reads` |
| `the_catalog_fences_only_superseded_configurations` | The catalog's latest move fences a recovery's lost configuration and any configuration older than a move, never the one the stream goes on from (TLA+ CE-4, `RecoveryBothReturn`) | `fences_copy` |
| `an_aborted_move_restages_only_for_the_same_source` | A copy an aborted move staged is restaged only by another ordinary move from the same source (TLA+ `AbortedJointRestageSafety`) | `restages_replacement` |
| `only_superseded_outsiders_are_excluded` | A refusal never hides a newer history | `excludes_sender` |
| `only_installed_members_vote` | Vote eligibility, with recovery replacements | `votes` |
| `dead_only_after_the_repair_delay` | A keeper that answered within the repair delay is never treated as dead | `keeper_dead` |
| `backoff_is_bounded_and_grows` | Repair and wake backoff stays within its cap and never shrinks with another failure | `backoff` |
| `only_another_incarnation_is_a_reuse` | A keeper ID is reused only when a peer saw it under another media incarnation first | `reincarnated` |
| `a_reused_keeper_never_registers` | A keeper with reinstalled media never votes with an empty log | `registers` |
| `a_reused_keeper_grants_nothing` | A grant from a reused keeper ID never counts toward a campaign | `counts_grant` |
| `version_mismatch_never_triggers_repair` | A keeper on an incompatible protocol version is alive and never repaired, however long it is silent | `triggers_repair` |
| `write_version_and_peer_feature_gates` | A new format waits for the finalized cluster version, and a peer supports a feature only with every required bit | `write_version_allows`, `peer_supports` |
| `slow_media_is_never_responsive` | A keeper whose WAL round runs past the soft limit, or within the hold after one, never votes, leads on or accepts streams | `media_responsive` |
| `a_parked_follower_holds_the_leaders_applied_log` | `Parking.accept_requires_exact_log` | `accepts_park`, `same_index` |
| `only_a_quiet_applied_uniform_group_is_idle` | A parked group has applied its whole log under a uniform membership | `idle` |
| `only_a_settled_idle_leader_parks` | `Parking.leader_parks_only_settled` | `leader_parks` |
| `a_parked_replica_reopens_only_for_work` | `Parking.parked_answers_preserve_state` | `parked_answer` |
| `a_recently_heard_voter_is_not_silent` | A voter that acknowledged within the repair delay is never replaced | `silent` |
| `learners_leave_only_after_the_stale_delay` | Stale learner removal | `learner_stale` |
| `repair_order_prefers_priority_then_rotation` | Joint changes, then stale learners, then dead voters; round-robin within a priority | `repair_key` |
| `a_repair_pass_respects_its_slots` | At most `MAX_REPAIRS` at once, never a running or backed-off stream | `starts_repair` |
| `a_roster_moves_only_with_a_live_quorum` | Nothing moves without a live quorum of the current roster: two of three, three of five | `repair_allowed` |
| `quorums_of_a_roster_intersect` | A stream has three or five voters, and two quorums of one roster share a voter | `replication_factor`, `quorum` |
| `a_spread_roster_survives_any_domain` | An admitted roster keeps a quorum after losing any one failure domain: 1+1+1 for three voters, at most two per domain for five | `spread_allows` |
| `five_voters_wait_for_the_finalized_version` | A five-voter stream is created only once the cluster finalized the replication-factor version | `creates_replication` |
| `average_keepers_stay_roomy` | The load ceiling never refuses a keeper at or below the average | `load_ceiling`, `roomy` |
| `leadership_moves_only_to_a_matched_voter` | Writer-domain handoff only to a matched voter, outside the hold-down | `hands_off` |
| `only_orphaned_copies_seek_retirement` | Only an excluded or leaderless copy asks for a retiring proof | `orphaned` |
| `retirement_never_removes_a_named_copy` | `RetireOnProof.retired_copy_outside_every_quorum` | `certifies_exclusion` |
| `a_named_voter_never_refuses_a_vote` | A voter refuses to vote only on a newer finalized configuration that names it nowhere | `refuses_stale_vote` |
| `a_recovery_fence_refuses_every_seal` | `RecoveryFence.fence_refuses_every_seal` | `seal_step`, `recovery_epoch` |
| `restart_trusts_the_newest_intact_slot` | Studies 25 and 26's valid-image selection rule | `newest_slot` |
| `a_checkpoint_past_the_boundary_is_refused` | A checkpoint never lies past the trusted boundary | `checkpoint_within` |
| `replay_detects_a_rolled_back_segment` | A data volume rolled back below the trusted boundary fails replay | `replay_step` |
| `a_lease_ends_before_the_recovery_serves` | Endgame rule 2: the holder counts a lease expired before the recovery wait ends | `lease_bounds`, `lease_valid`, `recovery_wait` |
| `authority_needs_lease_epoch_and_no_fence` | Endgame rule 3: campaign, lead and serve need a valid lease, the current epoch and an unfenced copy once enforced | `holds_authority` |
| `a_fence_spares_newer_configurations` | A recovery's fence covers only copies older than the recovered revision | `copy_fenced` |
| `a_stale_epoch_or_replaced_media_never_renews` | Endgame rule 2: an epoch bump ends every lease issued under the old epoch | `grants_lease` |

## Scope

Verus checks each decision exactly, including overflow. `fits` and `suffix_admits` use exact integer comparisons, and `body_charge` saturates at `usize::MAX`. The rotation law shows that a scan reaches a continuously ready lane within five probes. When the scan serves another ready lane first, the next scan starts strictly closer. The glue that probes tokio channels in `Queues::try_recv` is unverified Rust that calls `probe` and `after`.

A frame in these laws is one peer message in flight. The control and replication lanes multiplex many messages on one connection and batch them into frames, and the receiver charges each message on its own, so the per-sender shares hold however messages are grouped into connections or batches. A batch frame is charged as one message while it is read; the unverified `ReplicationIngress::split` releases that charge and admits each decoded message under one lock with the same decisions.

These proofs cover the decisions, not the stateful bookkeeping around them. Unverified Rust holds the per-sender meter maps, the disk ticket ledger, settle-once and hold-until-reconciled behaviour, the follower ticket handoff and the WAL worker. The Rust tests cover them. The restart law covers the committed flag, and `Vote::new(term, keeper)` keeps the term and ballot. OpenRaft's vote type and its election and commit rules are trusted.

## Controls

`area.json` declares 79 production mutations. Each one removes or inverts one decision, such as sending application entries on control, charging a body once, ignoring the per-sender byte, message or control cap, releasing a message without its bytes, spending a class floor, stalling rotation, splitting without shrinking, restoring a restarted leader, accepting a term regression or index gap, recovering beside a live voter or without the acknowledgement, stepping the recovery term or epoch too little, restaging a replacement for another survivor's recovery, restaging a copy of a move from another source configuration, serving reads from an uncertified copy, letting a recovery's lost configuration go on, fencing an ordinary move's source configuration, letting an uninstalled copy vote, refusing a member without an answer, counting a keeper live at the repair delay, growing a repair backoff by one millisecond, trusting a peer's new incarnation, registering a replica on a reused or unconfirmed keeper, counting a reused keeper's grant, counting media responsive past the soft round limit or during the hold after a slow round, repairing a keeper on another protocol version, allowing a new format before finalization, accepting a peer that advertises only some of the required feature bits, accepting a drift margin of half the lease, counting a lease without its margin, letting a lapsed or fenced keeper keep its authority, fencing the recovered revision, serving a recovery without the margin, or renewing a stale epoch or replaced media. The keeper controls park a follower with a longer or unapplied log, ask for parks from a follower, reopen a parked group for a heartbeat within the park round, count a voter silent or a learner stale early, restart the repair rotation, start a repair past the slots or during a backoff, move a roster with one live voter, drop the load ceiling's headroom, refuse a keeper at the ceiling, hand leadership to an unmatched voter or within the hold-down, let a leading copy seek retirement, retire on another revision or while a joint target names the copy, refuse a vote on a configuration no newer than the copy's or one that names the voter, refuse a vote on a configuration no newer than the copy's or one that names the voter, seal through the recovery fence or at the current epoch, trust the older boundary slot or lose the surviving one, trust a checkpoint past the boundary, and apply a split frame or finish replay at a torn frame or short of the boundary. The baseline verifies 151 functions. Each control fails exactly its declared contracts or loop invariant and verifies the other 150.

The incarnation laws cover the decisions only. That each keeper stores the incarnations it first saw durably before it answers with them, and marks itself reused before that mark could be outrun by a confirmation, is unverified Rust covered by the keeper tests. So is the trust on first contact itself: a keeper whose peers never saw its old incarnation is not recognized.

The keeper laws cover the decisions only. That the leader asks every live follower before it parks and parks only when all accepted, that the repair loop inserts each started stream into the running set and clears it when the repair task ends, that a proof comes from another keeper and names the copy's genesis, and that the WAL replay loop stops exactly when its offset reaches the boundary and then compares the running hash, are unverified Rust covered by the keeper and WAL tests. The replay law models that loop over whole frames and shows that a segment holding fewer bytes than the boundary acknowledged never finishes. Durations enter the decisions as exact nanosecond counts, so each comparison is the one the Rust code made on `Duration`. The protocol-level consequences are the [Lean consensus additions](../../lean/Logkeeper/ConsensusAdditions.lean).

The recovery laws cover the decisions only. That the recovery write is one durable WAL round, that the recovered membership follows only an applied `Command::Recover`, and that a lost voter retires only on a certified placement proof are unverified Rust covered by the keeper tests.

Run the area from the repository root.

```sh
python3 verification/verus/run.py --verus /Users/sachaichbiah/code/codesign-agents/tools/verus consensus_admission
```
