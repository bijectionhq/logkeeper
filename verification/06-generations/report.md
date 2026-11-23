# Study 06 report · Repeated moves and stale certificates

2026-11-22

## Verdict

A permanent per-group generation floor can prevent replays.
Its history grows with former placements.
A one-use destination reservation also prevents replays and lets a group discard the old per-stream generation floor.
The reservation must resist expiry once the source has sealed against it.
A group can reclaim a prepared slot only with evidence that the source can no longer seal under it.

## Properties and comparison

Both candidates satisfy unique authority, receipt preservation, and terminal retirement at the two bounds.
The reservation candidate also satisfies the pending-reservation invariant, including when local old generation floors are forgotten.
This invariant guarantees an eligible activation proof in the bounded model.
It makes no claim about real-time completion.

| Bound | Generation floor | Single-use reservation |
| --- | ---: | ---: |
| Two groups and three generations | 134 states | 864 states |
| Three groups and four generations | 1,444 states | 265,874 states |

Each history has at most two committed records.
The state counts reflect the modeled choices, including tentative prepared slots.

| Amendment | Mutation | Counterexample |
| --- | --- | --- |
| A21 | `accept_equal` | Move A to B and back to A. Replay the old A-to-B certificate. B opens alongside A in five transitions. Another five-transition trace makes an acknowledged record disappear from a serving history. |
| A21 | `forget_generation` | Forget B's floor after moving away. Its old certificate can reopen it in six transitions, or resurrect it after retirement in seven. |
| A22 | `wrong_target` | With the floor design, one certificate opens two groups in three transitions. With reservations, two destinations can each have nonce 1 for the same predecessor generation. Omitting target binding opens both in five transitions. |
| A22 | `reuse_nonce` | Consume a reservation, move away, recreate the same slot nonce using a delayed prepare, and replay the authentic certificate. Two groups are open after eight transitions. |
| A23 | `expire_slot` | Prepare → seal → expire the slot. No authority can write and the only usable certificate can no longer activate. Three transitions. |

Lean shows that consumed nonces cannot match a later live slot through any finite sequence of preparations and consumptions, that live nonces have been issued, and that a fresh nonce can be issued from an empty slot.
The nonce-reuse mutation fails the exact proof case.
The theorem treats durable issuance state as a premise.

## Acceptance programs and developer cost

Clients follow the same writer and stream contract.
The reservation adds one target preparation before source sealing.
A complete A-to-B-to-A program preserves old history and can append on return.
TLC reaches the program in six transitions with floors and eight with reservations.
These counts are abstract actions.

## Residue

Repeated aborted preparations, cancellation proof transport, durable publication of route hints, nonces across group replacement, and quota exhaustion need refinement.
A crash that preserves the old group identity but loses its durable issuance counter violates the model premise.
The sound reclamation protocol must distinguish an abandoned slot from a slot that an unreachable source already sealed against.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/06-generations/run.py
```

The runner pins TLA+ tools 1.7.4 and Lean 4.35.0 and retains all commands and traces under `.results/`.
