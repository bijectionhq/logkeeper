# Study 17 report · Exact historical feed

2026-11-22

## Verdict

If a product requires exact event replay beyond the journal window, trim needs both checkpoint coverage and an exact, durable event prefix within the promised history window.
An RTDB state checkpoint can safely stand in for old transactions during recovery while still losing their order as events.
An existing RTDB history format can meet the event requirement if it proves the required projection and its continuity.
With exact-history coverage, capture the upper cut once, select a join position, and validate the journal floor when admitting the suffix.
A trim between planning and admission can move the join forward into the now-longer archive.

## TLC results

The three invariants hold across 2,972 distinct states with two records and 31,796 with three.
Both bounds allow two distinct events, one reader, one staged archive segment, and concurrent publication, trim, and journal growth.
A nine-transition trace refreshes after trim and returns the exact nonempty captured window.
A separate nine-transition trace returns at least one event from each physical source after trim.

| Amendment | Weakened rule | Shortest counterexample |
| --- | --- | --- |
| A51 | `archive_gap` | Commit two events and publish the second as the next archive segment. Four transitions. |
| A51 | `checkpoint_only` | Commit, checkpoint and trim the record before a durable exact event exists. Three transitions. |
| A52 | `skip_recheck` | Plan a journal read, archive and trim its first record, and admit the stale plan. The successful response omits the record at eight transitions. |
| A52 | `duplicate_seam` | Capture a journal window while the archive is empty, advance the archive across the join, and serve its first event from both sources. Six transitions. |

## General model proofs

Ten [Lean theorems](FeedComposition.lean) check exact archive and actual journal slices, their half-open concatenation, stability under later appends, loss of event order through a state reducer, and the retention cost of lagging archive coverage.
For any captured window and any current floor covered by the archive, a constructive theorem chooses a valid join and proves the response exact.
It handles windows entirely within either source and avoids reading an empty side.
The countermodel reduces both event orders `[1, 2]` and `[2, 1]` to state 3 with count 2, so a generic state-and-count decoder cannot return the original order.
If trim cannot exceed the archive watermark and retained capacity is finite, the committed head is bounded above by the watermark plus that capacity.
A stalled archive can force write backpressure even while checkpoints keep succeeding.
Dropping the floor check, the archive coverage bound, or the premise that lets a raced reader replan breaks the corresponding proof.
The checker reports only standard axioms.

## Residue

This study is conditional on the product choosing exact historical resume.
The alternative is to return the stale-cursor error and reopen from a checkpoint.
For the exact contract, define the events, window, authorization, and expiry, then prove either RTDB's event projection or an archive producer to be exact.
The bounded checks use a persistent archive and one reader.
Deletion and concurrent archive readers must refine custody and retention.
The checks establish safety and existence of successful programs under these assumptions.
Event delivery under load, resubscription token semantics and a concrete storage implementation remain separate obligations.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/17-exact-feed/run.py
```
