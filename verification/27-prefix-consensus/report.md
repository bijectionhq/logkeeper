# Study 27 report · Commit agreement across replica-group ballots

2026-11-22

## Verdict

In a fixed voter group, recover the greatest complete accepted prefix reported by a quorum of durable promises.
Compare the ballot that accepted the prefix first, then its length.
Length counts all logical positions from the same history origin, including checkpointed positions.
Each ballot has one prefix chain, and each of its votes includes its adopted seed.
Persist the promise before sending the reply.
Preserve the exact accepted rank independently of that promise.
A receipt refers to a quorum of exact votes under a single ballot.
A chosen prefix forms a contiguous group decision and can contain records accepted previously under another ballot.

## Bounded results

The baseline satisfies prefix agreement and inheritance in every checked state.
There are three voters, a two-voter quorum, and two command values at each generic bound.

| Schedule | Ballots | Prefix length | Distinct states |
| --- | ---: | ---: | ---: |
| Generic | 2 | 1 | 4,384 |
| Generic | 2 | 2 | 115,312 |
| Generic | 3 | 1 | 217,984 |
| Focused divergent tails | 3 | 2 | 34 |
| Focused receipt formation | 4 | 1 | 26 |

The focused schedules constrain which voters participate and when the ballots start to isolate the respective comparisons.
At the receipt bound the baseline also satisfies the rule that its receipt agrees with the chosen value.
The unrestricted three-ballot, two-record length-only control exceeded the initial 60-second checker budget.
The tested schedule and the Lean general proof cover different evidence scopes.

| Amendment | Weakening | Shortest inheritance / agreement trace | Failure |
| --- | --- | --- | --- |
| A94 | `length_only` | 15 / 17 steps in the focused schedule | Vote for a two-command minority tail in ballot 1 and choose a divergent one-command tail in ballot 2. Prepare ballot 3 with one report from each. Choosing solely by length revives the divergent minority tail. |
| A94 | `ballot_only` | 11 / 14 steps | Choose a two-command prefix. The next ballot takes a one-command report from the same old ballot and can choose a different second command. |
| A95 | `lose_promise` | 10 / 13 steps | A majority prepares a later ballot. One voter restarts with a lower promise and casts an earlier vote that the retained prepare report could never have seen. |
| A96 | `promote_promise` | 9 / 12 steps | A voter without an accepted prefix stamps its empty report with the new promise ballot. It outranks the real accepted vote in the intersecting quorum. |
| A97 | `aggregate_votes` | 20 steps in the focused schedule | Voter 1 votes for A in ballot 1, voter 2 for B in ballot 2, and voter 3 for A in ballot 3. Ballot 4 sees the first two voters and adopts B. A mixed-ballot receipt reports A just before ballot 4's second exact vote chooses B. |

The ranked rule extends the shorter chosen branch in eighteen transitions at the focused three-ballot bound.
The model reaches adoption of a minority vote with no preceding choice in eight transitions.
In the generic two-ballot model, nine transitions suffice to obtain matching bytes across a quorum of different ballot votes while no single ballot has a quorum.
The focused four-ballot baseline answers B with genuine quorum evidence in twenty transitions.
These are reachability results.

## General proofs

Lean checked thirteen theorems with standard axioms only. [Agreement proof](PrefixAgreement.lean) · [Durable acceptor proof](DurableAcceptor.lean)
For arbitrary ballots, values, prefix sizes and fixed voter lists, any later ballot inherits every earlier chosen prefix if proposals satisfy the stated quorum and chain rules.
The proof intersects the earlier choice with the later prepare quorum.
The intersecting voter's exact, fenced reply dominates its earlier vote.
If the maximal reported vote is in that earlier ballot, the common chain and length establish inclusion.
If it is in an intervening ballot, the induction hypothesis establishes inclusion.
Every pair of chosen prefixes is therefore comparable by extension and agrees at every shared position.
Learning a late or shorter certificate preserves the longer known committed prefix.

An independent acceptor trace proof establishes report coverage and authenticity from atomic durable prepare, monotone accepted rank, and preserved restart state.
Compose its reply-coverage theorem with the agreement proof.
This proves prefix agreement for the modeled durable acceptor executions, conditional on authentic assembly of their reports and votes and the ballot proposal rules.
Two controls weaken the ranking, and a third discards the promise across restart.
Each fails its designated proof obligation.

## What the model leaves open

The model specifies fixed-group agreement.
It uses exact immutable proposal chains and certified identity.
The deployed protocol still needs to enforce ownership of a ballot, serialize its proposed prefix, hold captured recovery inputs through transfer, and preserve the same durable binding through channel retries and repair.
The proof votes for complete histories logically.
Real incremental transfers and checkpoints must preserve their exact representation and their accepted rank while compaction runs.
The proof's historical votes and reply tables are modeling records.
The local acceptance rule uses the current durable promise and the latest accepted binding.
Actual acknowledgement handling must derive the correct choice instant, apply commands in order with their logical guards, and settle a fresh read through the current authority.
The agreement proof does not settle liveness, concurrent membership changes, or timing across distinct RTDB writer and placement grants.

The incumbent winner compares complete synced epochs before last LSN and confirms the recovered tail on a quorum before opening.
The checked model makes those obligations explicit at the fixed-group boundary.
It does not assert that incumbent source refines the model. [Winner selection](../../src/client/recovery.rs) · [Quorum recovery](../../src/client/writer.rs)
The source contains a separate Kani harness for the scalar ranking over three replies.
This study's results come from the protocol models. [Source harness](../../src/client/recovery/proofs.rs)

Apply [A94–A97](../amendments.md#study-27--2026-11-22).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
Exact commands, configurations and traces stay in the ignored `.results` directory.
The runner releases its temporary TLC state queue after each run.
Set `LOGKEEPER_TLC_SCRATCH` to an existing directory if the state queue should live on another volume.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/27-prefix-consensus/run.py
```
