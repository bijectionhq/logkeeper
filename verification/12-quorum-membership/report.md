# Study 12 report · Journal voter replacement

2026-11-22

## Verdict

Overlapping membership lists can have disjoint majorities.
Direct replacement can allow a stale old-only commit or strand an acknowledged record.
Both tested safe protocols need a durable fence excluding old-only votes and exact payload coverage on the successor membership.
Joint voting allows writes while both majorities can decide.
A sealed transition pauses writes until the successor is ready.

## TLC bounds and results

Both candidates satisfy `NoStaleCommit`, `QuorumCanRecover` and `SurvivingCopy` over the configured finite executions.
The source and successor each have three voters, with one identity replacement in the same AZ and at most one lost AZ.
The model stops each history at the stated bound.

| History bound | Joint transition | Sealed transition |
| --- | ---: | ---: |
| Two records | 43,100 states | 35,148 states |
| Three records | 343,452 states | 273,996 states |

A six-transition witness writes under both majorities after an AZ loss, adopts the new membership, and delivers a receipt for an already decided old entry.
Delivering a previous decision and making a new old-only decision are different operations.

| Amendment | Weakened rule | Shortest counterexample |
| --- | --- | --- |
| A34 | Direct replacement with no previous-member fence. | Switch membership and then let an old-only majority issue a new receipt. Two transitions. |
| A34 | Direct replacement with no new-member evidence. | Commit with the old majority and switch to a new majority that lacks the record. Two transitions. |
| A35 | Metadata end stands in for bytes. | Commit → apply metadata without its payload → enter joint → adopt → lose the AZ with the only eligible copy. Five transitions. |
| A35 | A correct length stands in for exact bytes. | Commit → enter joint → install a learner's same-length, wrong payload → adopt → lose the only correct copy in the adopted membership. Five transitions. |
| A35 | Old persistence counts for a new durable identity at the same address. | Commit → enter joint → adopt using the old disk's proof for its replacement → lose the remaining eligible copy. Four transitions. |
| A36 | Release old storage while joint. | Enter joint → commit → lose an AZ → reclaim the last copy in the still-protecting old membership. Four transitions. |
| A37 | Accept a new-only vote in the joint phase. | Enter joint → commit with a new-only majority. An old-side recovery majority has no exact copy. Two transitions. |
| Successor quorum | Accept one voter in the installed successor. | Seal → adopt → commit on one successor voter → lose its AZ. No surviving copy. Four transitions. |

## General proofs and acceptance program

Nine reported Lean theorems use only standard axioms.
Two majorities intersect within one certified voter list.
A durable old-majority fence excludes a later old-only majority while recipients refuse stale votes.
A three-voter configuration with pairwise distinct AZs retains a majority after loss of any one AZ, conditional on the surviving replicas being reachable.

`trace_refines_and_preserves_cut` proves that arbitrary finite sequences of the modeled journal steps refine the imported logical kernel and preserve exact majority coverage for each retained record.
`any_recovery_quorum_can_read_exact_entry` gives an actual replica in any available majority for each such record.
`verified_membership_change_program` constructs a membership switch once the current new voters certify the retained cut, with the same logical stream state afterward.
These are operator and storage transitions.
The client keeps the writer, LSN, and receipt contract from the logical kernel.

Four Lean controls fail at the expected proof cases when finalization skips the new cut, append skips payload evidence, reclaim loses an active retained copy, or a fenced voter can accept an old vote.

## Decision and residue

Normal replacement should use a vetted membership protocol with the documented old and joint ordering guarantees.
Persist an exact retained cut on the new membership before releasing storage that the old configuration still protects.
A metadata-only consensus snapshot can help establish control state.
The replay payload remains a separate durability obligation unless its certified references describe an equally recoverable copy.

The proof treats a quorum decision, authentic durable identities and fences, retained-data attestation, and the fault envelope as its boundary.
It does not verify an actual consensus implementation, the lifetime of a staged handoff receipt, or service latency during repair.
The [install study](../13-install-durability/report.md) covers the new race between target certification and membership change.
The [configuration closure study](../32-configuration-closure/report.md) distinguishes quorum completions that arrive late from an old decision that extends the recovered history.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/12-quorum-membership/run.py
```

The runner builds the current Lean kernel and saves exact commands, checker output and traces under `.results/`.
