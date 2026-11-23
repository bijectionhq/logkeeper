# Study 47 · Retain move decisions until their participants settle

2026-11-23

## Verdict

Give every admitted move a result slot before participants can act.
Retain its exact source decision until all its recorded consumers durably settle.
Reclaim fully settled rows independently so a disconnected older participant cannot block reuse of a later result's slot.

Recovery needs the closed ranked source prefix and its certified base.
An unlearned abort in that prefix still exists, and a compaction in that prefix still frees its slot.
Replaying the ordered evidence requires no fresh participant lookup.

A compacted key can prove closure once authenticated issuance and absence are known.
The same compacted book can follow either a seal or an abort.
Any exact result that is still promised needs its own retained evidence.

## Properties and comparison

[SourceOutcomes.tla](SourceOutcomes.tla) separates an authoritative book, a lagging learner, and participant settlement receipts.
There are three modeled consumers per attempt, representing two pools and the target.
The outage keeps the first attempt's first consumer unreachable.
The general case allows either seal or abort.
The outage comparison uses canceled attempts.
The model assumes authenticated scope for nonmutated receipts and abstracts the durable effects each participant certifies.

| Candidate | Attempts / result slots | Distinct states | Checked result |
| --- | ---: | ---: | --- |
| Sparse compaction with all participants available | 2 / 1 | 10,020 | Seven safety and two temporal laws hold up to the bound. |
| Sparse compaction with one older participant unavailable | 3 / 2 | 42,536 | Same laws hold up to the bound. |
| Prefix compaction with one older participant unavailable | 3 / 2 | 14,159 | Seven safety laws and install progress hold. Independent return of fully acknowledged credit fails. |

The safety laws cover exact unsettled outcomes, durable issuance, exact acknowledgments, charged evidence rows, closure with all participant work accounted, absence of invented exact results, and refusal to restore a compacted row.
The temporal model gives weak fairness to installation and eligible compaction.
The slot-return law applies once all acknowledgments for that row are durably recorded.
It assumes no response from the older unavailable participant.
With all slots occupied by genuine unresolved debt, further admission waits.

| TLC weakening or candidate | Shortest safety failure or temporal result |
| --- | --- |
| Recover the learner | Choose abort while the learner lags and install an image that loses the required result in four transitions. |
| Recover the learner after compaction | Settle and compact a result, then install a stale image that restores its row in twelve transitions. |
| Compact before settlement | Reserve, choose, and erase a result while participants still need it in three transitions. |
| Accept a foreign acknowledgment | Apply one attempt's local effect and use its receipt for a different attempt in six transitions. |
| Lose issuance during recovery | Issue an exact attempt and install a book that reports a smaller issuance range in three transitions. |
| Read absence as abort | Seal, settle and compact, then return abort for that same identity in thirteen transitions. |
| Require participant lookup for install | Seal the book with a retained result and an unreachable participant. The successor can stutter forever. |
| Compact only a settled prefix | Fully settle the second result while a first participant remains unavailable. The fully acknowledged row stays charged forever. |

[SourceOutcomes.lean](SourceOutcomes.lean) checks thirteen theorems using standard axioms only.
Its reference book has a fixed number of slots, with an issuance serial separate from slot reuse.
Recording a chosen result uses its existing row.
The proof checks that exact identity and the recorded outcome gate acknowledgment, and that compaction cannot remove a waiting row.
Returning a settled slot preserves an unrelated older row and the issuance value.
An authenticated issued key can query its exact result while retained, or closure after compaction.
An unissued key supplies no terminal evidence.
Lean constructs the same compacted book from distinct fully settled outcomes and rules out an exact decoder for both.

The ranked proof reuses the configuration-closure theorem.
Any current recovery majority has a surviving voter with the installed basis extending the earlier chosen source history.
Replaying that basis equals replay of the original chosen commands followed by the remaining suffix.
The reducer uses the original scope and evidence premises attached to those commands.
The proof does not assume that an old learner had applied the chosen prefix or that a participant is reachable during replay.
The two Lean controls reject weakening the receipt binding and compacting despite outstanding debt.

## Amendments

[A180–A183](../amendments.md#study-47--2026-11-23) require exact reserved evidence, sparse release of settled credit, durable issuance with closure-only compact lookup, and ranked replay of the authoritative book.

## Acceptance programs

- P52. Record a plan at the learner, choose abort before it learns the result, seal the authority, lose the predecessor, and install the exact result with one participant still unavailable. The bounded model reaches this and retirement of new admission in seven transitions. The Lean query lemma gives the exact result from the retained row.
- P53. Retain the first result while its participant is unavailable. Settle the second, return its slot, issue a third, and query closure of the second. TLC reaches this in sixteen transitions at width two. Exhaustive search excludes it for the prefix policy at the same parameters.

## Residue

The formal reducer treats exact authorized source decisions and durable participant settlement as input evidence.
The complete composition still needs to establish that evidence from the funded-source command and pool and target effect paths.
The book's authority certification must bind the slot, serial, and full intent to durable issuance before any prepare can become effective.
The result bound is a bound on rows. The actual encoding must bound participant lists, result evidence, and counter representation.
Retiring the whole stable discovery namespace after all debts settle needs its own fencing and routing contract.
The ranked theorem assumes a common certified replay basis and authenticated command coverage.

## Reproduction

Run with Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
TLC uses one worker and a 512 MiB heap. Each check has a 60-second limit.
The runner saves the checked configurations, traces, and diagnostics in `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/47-source-outcomes/run.py
```
