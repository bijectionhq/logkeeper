# Study 29 report · Fresh reads without a command per invocation

2026-11-22

## Verdict

The no-marker read needs a fresh round in the exact ready replica scope.
Its voters must have durable coverage of the group prefix chosen when the round opens.
The greatest accepted position reported by the quorum then bounds that chosen prefix from above, including commands the serving replica has yet to learn.

Use the maximum as the minimum position the serving snapshot must cover.
Serve the sampled prefix once its exact contents are certified and applied, or independently validate an applied chosen snapshot that covers the maximum.
Both paths evaluate read authority at the snapshot they will serve.
A speculative sample is a lower bound for the required coverage.
The bytes returned come from the exact applied choice.

For logical cuts between complete ordered commands, sufficient coverage supplies a point inside the invocation interval.
A physical batch can skip such a cut.
For the physical-frontier interpretation, a round can instead check that its maximum equals the cut already certified when that round started.
The matching cuts witness the physical frontier at round opening.

## Bounded results

Each bound has three voters, a two-voter quorum, two ballots, and two command values.
The finite model uses the earlier recovery protocol as a premise when choosing an activation basis.
The five safety laws cover the current invocation, earlier majority fences, prior choices, exact applied contents and an exact cut in the chosen window.

| Candidate | Command bound | Distinct states | Contract checked |
| --- | ---: | ---: | --- |
| Exact sampled prefix | 1 | 30,538 | Logical command cuts |
| Exact sampled prefix | 2 | 912,114 | Logical command cuts |
| Independently certified cut covering the sample | 1 | 30,574 | Logical command cuts |
| Precertified cut matches the fresh sampled maximum | 2 | 630,038 | Physical batch frontier |

| Amendment | Weakening | Shortest bounded failure |
| --- | --- | --- |
| A102 | `reuse_old_round` | Open a round before the read invocation and use its replies for that read. Six transitions. A nine-transition trace caches an empty quorum answer, then misses a choice made before the invocation. |
| A102 | `ignore_promise` | Open an old-ballot round after a higher promise on a quorum and count the fenced peers. Eight transitions. |
| A103 | `open_before_coverage` | Choose an old-ballot record, activate a new ballot with empty local accepted prefixes, and return the empty cut. Twelve transitions. |
| A103 | `known_cut_only` | Choose a record, begin a fresh read while its serving replica is behind, and answer from that replica's known starting cut. Nine transitions. |
| A104 | `expose_candidate` | Sample a tail voted for by a minority and return it before group choice and application. Eight transitions. |
| A104 | `apply_by_position` | Capture an old ballot's minority value, activate a successor that does not inherit it, choose different bytes at that position, and reply from the old capture. Fifteen transitions. |
| A105 | `atomic_batch` | Capture position 1 and then choose 2 in one physical transition. Applying and returning position 1 has no physical cut witness because only 0 and 2 were visible. Twelve transitions. |

The logical candidate can serve during a partial fence in seven transitions.
In nine, it delivers an earlier valid round after the successor activates.
In ten, it returns a cut above the already applied position at round start.
In ten, it covers a command chosen before invocation while the serving replica still has an earlier applied cut when it opens the round.
The physical matching candidate waits or retries in that case.
The physical candidate also completes a nonempty read in eleven transitions after a batch jumps from 0 to 2 and the cut at 2 is certified before opening its fresh round.
In twenty, the exact-capture path abandons a lost nonempty candidate and retries under the successor, returning different certified bytes at the same position.
The independently certified candidate can revalidate the successor's applied prefix without returning the original sampled bytes in fifteen transitions.
The abandoned-target witness retains the old bytes and requires the replacement to differ.
These results give reachability and safety in the checked spaces.

## General proofs

Lean checked twelve theorems with standard axioms only. [Proofs](ReadIndexProof.lean)
Round evidence binds an exact invocation, round identity and replica scope to the durable snapshots it counts.
Quorum intersection with persistent promises rules out a positive old round opened after a higher majority fence.
Intersecting the observation quorum with the durable basis quorum proves that the sampled maximum covers the opening cut.
The proof uses monotone exact prefixes under one scope and earlier choices that already have coverage in that scope.

The logical proof finds a command boundary in the interval after round opening and through delivery.
It covers an arbitrary exact applied choice at or above the sampled position.
The captured-prefix path is a specialization that proves the sampled bytes themselves were chosen.
Deterministic application then gives the exact stream cut and authorized writer at that boundary, matching the ordered barrier without adding a command.

The physical-batch proof avoids the one-command increment premise.
At round opening, the previously certified cut bounds the actual frontier from below.
The matching fresh sampled maximum bounds it from above.
The exact prefixes are equal.
Lean also constructs an atomic-batch history that skips the intermediate position.

Four controls weaken the invocation freshness, promised-ballot check, maximum observation, or exact applied prefix check.
Each fails its designated proof.

## Remaining obligations

Durable basis and monotone same-scope histories are protocol premises at this boundary.
The fixed-group consensus and journal studies give supporting results under their own premises.
Actual read transport still needs authenticated replica and round identity, persisted activation and promises, and correct binding to certified application.
Changing voter membership or stream placement during a round requires a separate refinement.
The reconfiguration proof covers scoped voter changes and reservation within the same placement. [Read reservation across voter changes](../30-reconfigured-reads/report.md)
Packing several invocations into one round needs a freshness argument for every admitted invocation.

Snapshot service still needs the atomic checkpoint and replay reservation at the selected exact cut.
The results do not establish liveness under continuous fences, stalled replication or repeated physical matching rounds.
The ordered-command interpretation includes cuts between complete commands within a durable batch.
A product contract that requires a physical batch endpoint instead can use the matching-cut candidate and must account for retries when writes keep the sampled maximum ahead.
The current proof makes that semantic choice explicit.

The incumbent samples the greatest held LSN of a quorum that confirms the active ensemble and waits for committed application through it.
The formal scope and window obligations specify what that shape needs at the design level. [Client read index](../../src/client/mod.rs) · [Voter read index](../../src/server/state.rs)

Apply [A102–A105](../amendments.md#study-29--2026-11-22).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner retains commands, configurations and counterexamples in the ignored `.results` directory.
Set `LOGKEEPER_TLC_SCRATCH` to an existing directory with room for the state queue.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/29-read-index/run.py
```
