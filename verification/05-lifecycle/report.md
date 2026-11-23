# Study 05 report · Move and retirement composition

2026-11-22

## Verdict

A retirement request reaching a sealed predecessor cannot produce a global retirement receipt.
The predecessor can still report the authorized successor or an unavailable transition.
The current authority decides whether to close.
The same handoff that carries the committed cut must carry the outstanding custody obligations.

## Properties and comparison

The baseline satisfies unique authority, exact cut, terminal receipts, absence of post-receipt appends, and complete custody coverage.
TLC explored 591 states at two LSNs and 916 at three LSNs.
The bound includes one move and three possible custody locations.

| Amendment | Mutation | Shortest counterexample |
| --- | --- | --- |
| A19 | `seal_after_retire` | Reserve a move → acknowledge retirement at the source → seal the retired source. Its terminal receipt loses the state that justified it in three transitions. |
| A19 | `sealed_claims_retired` | Reserve → seal → let the source return a retirement receipt. A six-transition variant installs the cut, activates the successor, and commits after that receipt. |
| A20 | `forget_custody` | Reserve a move → seal → install only target custody → activate and retire the target → dispose its local copy → declare completion with the source bytes present. Seven transitions. |

## Acceptance programs

TLC reaches durable retirement and completion at the source after a move has been reserved but before it seals, in five transitions.
It reaches retirement at the successor after a stale-route redirect in nine transitions.
In a real client, a delayed response can be retried using the same authorized operation.
A routing hint never substitutes for a terminal receipt.

## Residue

One stream moves once.
The model abstracts independent retries, payload integrity, group liveness, and irreversible local disposition as studied separately.
It establishes no claim about route chains, certificate identity across successive moves, or eventual discovery when every known group is unreachable.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java python3 verification/05-lifecycle/run.py
```

The shared runner pins the TLA+ tools 1.7.4 distribution and records the exact command, model configuration, and log for each run.
