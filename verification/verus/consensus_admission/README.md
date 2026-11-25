# Consensus admission verification

`proof.rs` imports the shipped `src/stream/consensus/decisions.rs`. The keeper-hosted consensus code calls these functions on its real paths. `network.rs` uses them to classify each decoded peer request and to split oversized AppendEntries batches. `keeper/admission.rs` uses them for replication body and control admission. `keeper/ingress.rs` uses them to check each received batch, `storage/space.rs` for disk floors and suffix slots, `storage/wal.rs` for durable lane rotation and `storage/mod.rs` for the restart vote. The harness uses no custom axioms, assumptions or external bodies.

`laws.rs` states independent laws over the shipped functions. Each law names the checked Lean theorem it refines.

| Law | Lean theorem | Shipped functions |
| --- | --- | --- |
| `payload_append_is_never_control` | `PeerBudget.control_header_cannot_dispatch_payload` | `carries_application`, `peer_lane` |
| `vote_and_metadata_only_append_are_control`, `snapshots_use_bulk` | `PeerBudget.vote_and_empty_append_are_control` | `carries_application`, `peer_lane` |
| `admitted_body_preserves_budgets` | `PeerBudget.reserve_body_preserves_budget` | `body_charge`, `admits_body` |
| `one_sender_leaves_the_others_their_share` | `PeerBudget.one_sender_cannot_spend_others_remaining_body_capacity` | `body_charge`, `admits_body` |
| `one_sender_leaves_control_work_for_others` | Control share of `PeerBudget.saturated_data_admits_control_and_maintenance` | `admits_control` |
| `ordinary_admission_keeps_reserved_classes_feasible` | `PeerBudget.saturated_data_admits_control_and_maintenance`, `Headroom.Follower.replication_preserves_maintenance_and_control` | `fits` and the class floors |
| `suffix_admission_respects_the_limit` | Suffix projection of `Headroom.Follower.trace_preserves_all_budgets` | `suffix_admits` |
| `rotation_serves_a_ready_lane_within_five` | `PeerBudget.persistent_lane_served_within_five` | `probe`, `after` |
| `oversized_batches_shrink` | Sender resize in the admission contract | `fit_append` |
| `restart_never_restores_leadership` | `RestartRead.present_never_restores_leadership` | `demotes_vote` |
| `accepted_batches_are_consecutive` | Decoded-cut validation before dispatch | `indices_follow`, `terms_ordered`, `consecutive_cut` |

## Scope

Verus checks each decision exactly, including overflow. `fits` and `suffix_admits` use exact integer comparisons, and `body_charge` saturates at `usize::MAX`. The rotation law shows that a scan reaches a continuously ready lane within five probes. When the scan serves another ready lane first, the next scan starts strictly closer. The glue that probes tokio channels in `Queues::try_recv` is unverified Rust that calls `probe` and `after`.

These proofs cover the decisions, not the stateful bookkeeping around them. Unverified Rust holds the per-sender meters, the disk ticket ledger, settle-once and hold-until-reconciled behaviour, the follower ticket handoff and the WAL worker. The Rust tests cover them. The restart law covers the committed flag, and `Vote::new(term, keeper)` keeps the term and ballot. OpenRaft's vote type and its election and commit rules are trusted.

## Controls

`area.json` declares 16 production mutations. Each one removes or inverts one decision, such as sending application entries on control, charging a body once, ignoring the per-sender byte or control cap, spending a class floor, stalling rotation, splitting without shrinking, restoring a restarted leader or accepting a term regression or index gap. The baseline verifies 48 functions. Each control fails exactly its declared contract or loop invariant and verifies the other 47.

Run the area from the repository root.

```sh
python3 verification/verus/run.py --verus /Users/sachaichbiah/code/codesign-agents/tools/verus consensus_admission
```
