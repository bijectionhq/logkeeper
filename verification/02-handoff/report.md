# Study 02 report · Authority between replica groups

2026-11-22

## Verdict

Directory-dependent activation preserves safety in the finite model but can strand a sealed stream when the directory becomes unavailable.
The portable variant commits an authorized successor at the source, seals the source, and installs the exact certified prefix before the target activates.
Directory updates are route discovery after activation.
A target with an installed cut can activate during loss of both the directory and inter-group link.
Without proof of a fence the target cannot replace an unreachable source that might still be writable.

## Properties and comparison

TLC explored one stream, two independently functioning groups, two payloads, one cross-group move, and up to two or three records in each history.
The directory and link can independently stay up, fail, or flap.
Weak fairness applies to the durable actions listed in the [brief](brief.md).

| Property | Directory activation | Portable activation |
| --- | --- | --- |
| Single authority, no fork, exact cut | Hold at both bounds | Hold at both bounds |
| Eventual progress with stable link and directory | Holds at both bounds | Holds at both bounds |
| Eventual progress with stable link after authorization and no directory premise | Fails at bound 2 | Holds at both bounds |
| Eventual activation from installed cut with no external connectivity premise | Fails at bound 2 | Holds at both bounds |
| Distinct states at bounds 2 and 3 | 436 / 1,236 | 624 / 1,840 |

Lean proves `unique_authority`, `exact_source_prefix`, and the constructive acceptance program `authorized_handoff_extends` for the one-handoff reference machine and histories of arbitrary length.
`cannot_fail_over_without_evidence` holds when the target's local observations agree between a writable source and a sealed source.
`distinguishable_evidence_allows_failover` exhibits a policy when those observations differ.
Lean reports only standard axioms and no admitted proofs.
These theorems concern the reference machine.
Conformance of an actual quorum certificate and its transfer path remains to be established.

## Amendments and counterexamples

| Amendment | Check | Counterexample |
| --- | --- | --- |
| A08 | Directory design violates `LinkOnlyProgress`. | Authorize → lose the directory permanently → seal → install → stutter. The source is frozen and publication is disabled. A separate run also finds a counterexample during directory flapping under weak fairness. |
| A08 | Directory design violates `InstalledProgress`. | Install an exact cut, then leave directory publication unavailable or repeatedly disabled by flapping. The target remains inactive forever. |
| A09 | `skip_seal` violates `SingleAuthority` in three transitions and `NoFork` in five. | Authorize → partition the groups → activate the target on local timeout → append A at the source and B at the target. Both commit at the same LSN. |
| A10 | `trust_precopy` violates `ExactCut` in five transitions. | Authorize → append at the source while the target's staged prefix is empty → seal → install the empty precopy → activate. |
| A11 | `reopen_source` violates `SingleAuthority` in six transitions. | Authorize → seal → install → activate → partition → reopen the source locally. |
| A12 | `LinkOnlyProgress` fails without fairness. | Authorize → seal → install → stutter indefinitely while activation is possible. |

Safety trace lengths come from one-worker breadth-first search.
The infinite traces are TLC lassos, with no claim that their stem or cycle is minimal.
The two Lean controls weaken the activation and installation preconditions.
They fail exactly at the corresponding case in the invariant preservation proof.

## Acceptance programs and developer cost

Both comparisons expose the same append interface.
A caller plans a move, continues source appends while copying, and retries the same move ID after interruption.

The portable variant needs no directory publication before accepting a target append.
TLC reaches a post-handoff target append during directory loss in seven transitions and activation with both external paths disconnected in six.
The proofs establish continuation for an arbitrary already committed source sequence in the single-move abstraction.

Clients using a stale source route must still be able to discover the successor or safely report unavailable.
Discovery requires a committed target hint with the move intent.
Protecting that hint's lifetime and proving route-chain bounds need a separate study.

## Residue

The formal models assume a single authenticated move slot bound to its stream, source and successor generation.
They exclude specifically competing valid proposals, multi-move cycles, certificate forgery or storage loss, retirement, and the mechanics of Raft membership.
The positive progress result assumes both group quorums function and there is a path to transfer final evidence until it is installed.
It says nothing about the duration of the pause or admission pressure.
An unreachable source with no transferred or recoverable proof triggers unavailable, even if the target has a recent precopy.
RTDB's current planned-handoff latency promise needs separate performance qualification at that exact boundary.

## Reproduction

Use Python 3.13, Temurin Java 21.0.13+9, and the pinned Lean 4.35.0 toolchain.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/02-handoff/run.py
```

The [runner](run.py) pins the TLA+ tools artifact by SHA-256 and saves configurations, commands, and logs under `.results/`.
The Lean toolchain pin lives in this study.
