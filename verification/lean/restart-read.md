# Fresh reads after a keeper restart

This note records a Rust defect found while implementing LK-REPLICATION-ADMISSION, and the Lean check of its fix in [RestartRead.lean](Logkeeper/LeaderJournal/RestartRead.lean).

## Defect

The keeper does not persist Raft's commit index. OpenRaft 0.9 restores a keeper as leader at startup when its stored vote is committed and names itself. The restored leader reuses its earlier no-op in that term, so its read floor `max noop knownCommit` can fall below writes acknowledged before the restart. In a failing Rust run, a fresh configuration read after a full restart returned the roster from before a replacement whose `replace` call had already succeeded. The leader's log reached index 176, including the final membership at 175, but its known commit after restart was 171.

## Fix

`LogStore::read_vote` presents the keeper's own committed vote as uncommitted, with the same term and ballot. The stored vote is unchanged. The keeper must win an election in a newer term. Its new no-op follows its whole log and commits only after it, so the next fresh read includes every acknowledged write. The cost is one election before a stream's first reads after a full restart. The write path and the media format are unchanged.

## Checked theorems

| Property | Theorem |
| --- | --- |
| The presented vote grants exactly the ballots of the stored vote, and still refuses another candidate in its term | `present_grants_the_same_ballots`, `present_refuses_another_candidate_in_its_term` |
| Startup never restores leadership from a presented vote | `present_never_restores_leadership` |
| A restored leader can read below an acknowledged write | `restored_leader_can_read_below_an_acknowledged_write` |
| Given leader completeness, an elected leader's read floor covers every acknowledged write, so every fresh read after a restart does | `elected_read_floor_covers_acknowledged`, `fresh_read_after_restart_includes_acknowledged` |

Leader completeness is a premise. A leader elected under Raft's rules holds every committed entry, and the model does not re-prove it. The model also takes OpenRaft's read floor and startup rule as stated in its 0.9.25 source (`LeaderHandler::get_read_log_id`, `Engine::startup`). The link to Rust is the regression test `a_restarted_leader_reads_only_after_committing_in_a_new_term`, which fails without the fix.

## Verification

`lake build Logkeeper.LeaderJournal.RestartRead` passed with 2 jobs, and `lake build Logkeeper` passed with 59 jobs on Lean 4.35.0. An environment audit covered all 74 public theorems declared in `PeerBudget`, `Headroom` and `RestartRead`. Every one depends only on `propext`, `Classical.choice` and `Quot.sound`, or on none of them.
