# Consensus admission verification

`proof.rs` imports the shipped `src/stream/consensus/decisions.rs`. The keeper-hosted consensus code calls these functions on its real paths. `network.rs` uses them to classify each decoded peer request and to split oversized AppendEntries batches. `keeper/admission.rs` uses them for replication message and control admission and for every meter update and release. `keeper/ingress.rs` uses them to check each received batch, `storage/space.rs` for disk floors and suffix slots, `storage/wal.rs` for durable lane rotation and `storage/mod.rs` for the restart vote. `keeper/recovery.rs` uses them to admit an operator recovery and to choose its term, and `state.rs` to choose its fence epoch. `keeper/liveness.rs` and `keeper/repair.rs` use them to decide when a keeper is dead and how long a stream whose repair or wake failed waits. `keeper/ingress.rs` also uses them to decide which replicas vote and which peers it refuses without an answer. The harness uses no custom axioms, assumptions or external bodies.

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
| `recovery_needs_acknowledgement_and_no_live_quorum` | Operator recovery admission (design section R) | `allows_recovery` |
| `recovery_outranks_the_lost_history` | Recovery term and fence epoch above the survivor's history | `recovery_term`, `recovery_epoch` |
| `only_superseded_outsiders_are_excluded` | A refusal never hides a newer history | `excludes_sender` |
| `only_installed_members_vote` | Vote eligibility, with recovery replacements | `votes` |
| `dead_only_after_the_repair_delay` | A keeper that answered within the repair delay is never treated as dead | `keeper_dead` |
| `backoff_is_bounded_and_grows` | Repair and wake backoff stays within its cap and never shrinks with another failure | `backoff` |

## Scope

Verus checks each decision exactly, including overflow. `fits` and `suffix_admits` use exact integer comparisons, and `body_charge` saturates at `usize::MAX`. The rotation law shows that a scan reaches a continuously ready lane within five probes. When the scan serves another ready lane first, the next scan starts strictly closer. The glue that probes tokio channels in `Queues::try_recv` is unverified Rust that calls `probe` and `after`.

A frame in these laws is one peer message in flight. The control and replication lanes multiplex many messages on one connection and batch them into frames, and the receiver charges each message on its own, so the per-sender shares hold however messages are grouped into connections or batches. A batch frame is charged as one message while it is read; the unverified `ReplicationIngress::split` releases that charge and admits each decoded message under one lock with the same decisions.

These proofs cover the decisions, not the stateful bookkeeping around them. Unverified Rust holds the per-sender meter maps, the disk ticket ledger, settle-once and hold-until-reconciled behaviour, the follower ticket handoff and the WAL worker. The Rust tests cover them. The restart law covers the committed flag, and `Vote::new(term, keeper)` keeps the term and ballot. OpenRaft's vote type and its election and commit rules are trusted.

## Controls

`area.json` declares 26 production mutations. Each one removes or inverts one decision, such as sending application entries on control, charging a body once, ignoring the per-sender byte, message or control cap, releasing a message without its bytes, spending a class floor, stalling rotation, splitting without shrinking, restoring a restarted leader, accepting a term regression or index gap, recovering beside a live voter or without the acknowledgement, stepping the recovery term or epoch too little, letting an uninstalled copy vote, refusing a member without an answer, counting a keeper live at the repair delay, or growing a repair backoff by one millisecond. The baseline verifies 70 functions. Each control fails exactly its declared contract or loop invariant and verifies the other 69.

The recovery laws cover the decisions only. That the recovery write is one durable WAL round, that the recovered membership follows only an applied `Command::Recover`, and that a lost voter retires only on a certified placement proof are unverified Rust covered by the keeper tests.

Run the area from the repository root.

```sh
python3 verification/verus/run.py --verus /Users/sachaichbiah/code/codesign-agents/tools/verus consensus_admission
```
