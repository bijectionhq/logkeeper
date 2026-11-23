# Study 55 · Bound outstanding pool incarnations

2026-11-23

## Verdict

Spend one durable inventory slot before exposing a physical pool incarnation.
Use that same slot while the incarnation serves, is quarantined, or awaits disposition.
Failure changes eligibility and leaves the scope's existing inventory and charges in place.
A returned incarnation can reuse its existing slot after authenticating its current access epoch and exact recovered book.
A new physical incarnation needs a fresh slot and a fresh namespace.

Without settlement, each new incarnation consumes one more slot.
A fixed inventory and unlimited new incarnations without terminal evidence are incompatible.
An eligible destination with spare bytes can still lack an inventory slot.
At the limit, defer new incarnations and keep validation and verified settlement available.

## Bounded comparison

[PoolIncarnations.tla](PoolIncarnations.tla) uses monotonically assigned incarnation IDs, one modeled physical charge per incarnation, up to two access-epoch advances per incarnation, and one in-flight verification receipt.
A current controlled book may change while a return is being validated.
An external disposition action supplies terminal evidence for the exact offline namespace and settles its modeled charge.

| Case | Distinct states | Result |
| --- | ---: | --- |
| One durable inventory slot, two possible issued IDs | 384 | The five safety laws hold. |
| Two slots, three possible issued IDs | 34,978 | The same laws hold. A third ID requires earlier exact disposition. |
| Full one-slot inventory, stable outage, and verified terminal evidence available | 101 | The same laws and eventual slot replenishment hold with weak fairness of evidence recording, retirement, and registration. |

The third case begins with the original scope offline and keeps it offline.
The external service can supply its exact terminal evidence.
The replacement has an available destination in the abstraction.
The model establishes eventual admission of the replacement scope under those conditions.

| Weakening | Shortest counterexample or temporal result |
| --- | --- |
| Count online incarnations alone | Lose the original scope, register a replacement, then admit a third scope into a two-slot inventory. Three transitions. |
| Release the inventory slot on failure | A single fault leaves charged work with no recorded incarnation. |
| Forget an unreachable scope on timeout | Fail the original and forget it without verified disposition. Two transitions. |
| Validate against another incarnation | A valid receipt from another scope with the same epoch and book can reopen the wrong scope in seven transitions. |
| Accept an earlier access epoch | Probe a quarantined incarnation, fail and reconnect it, then apply the earlier receipt. Five transitions including registration. |
| Ignore the current book | Probe an incarnation, advance its book, and apply the stale receipt. Four transitions including registration. |
| Require headroom for retirement | Verified terminal evidence arrives at a full inventory, but retirement stays disabled and a fresh namespace never registers. |

## General proofs

[PoolIncarnations.lean](PoolIncarnations.lean) checked ten theorems using standard axioms only.
Its accounting transitions call the actual Study 52 reducer for physical custody and pointwise numeric capacity.
The combined safety invariant holds over arbitrary finite traces.
Every live physical effect has its own debit, and each debit or ordinary occupancy points to a registered physical scope.
A live physical borrow prevents forgetting that scope.

An exogenous failure consumes no new slot and preserves the exact book of physical obligations.
An earlier access-epoch proof cannot authorize a return.
Exact current validation can reopen a pool with the same inventory and ledger.
Exact settlement at full capacity makes a fresh registration possible.
Across subsequent transitions, a forgotten issued namespace stays absent and no physical work can materialize under it in the model.

In any segment without completed settlement, the inventory length equals its initial length plus the number of registrations.
That sum remains within the configured slot limit after arbitrarily many faults, retries, and eligible ledger operations.
The proof controls reject returning without an exact access epoch and forgetting a namespace with outstanding physical charges.

## Amendments

[A211–A214](../amendments.md#study-55--2026-11-23) precharge the incarnation slot, validate the exact returned scope, preserve terminal namespace history through monotone issuance, and let verified settlement run independently of fresh registration headroom.

## Acceptance programs

- P73. At full inventory, lose the original pool, reconnect it, probe the current scope and reopen in the same slot. TLC reaches this in four transitions. Negative controls refuse stale epochs, foreign namespaces, and stale books.
- P74. Lose two charged scopes without terminal evidence and preserve both rows. TLC reaches full unresolved inventory in six transitions. The two-slot baseline excludes issuing a third ID without earlier disposition.
- P75. At capacity, record exact disposition for the original scope while its endpoint stays offline. Forget the closed incarnation and register a fresh ID. The eleven-transition witness charges both the surviving and newly registered incarnations. The fair case verifies eventual replenishment with stable terminal evidence.

## Residue

Validation authenticates the reported book to a trusted exact expected value and requires the scope's returned storage to uphold that book.
Production adapters still need to implement that observation and binding to the actual media and effect paths.
Provider disposition must certify irreversible closure of the exact namespace and account for every physical charge and possible delayed materialization.
A provider epoch, health check, unreachable address, or identity recycled by infrastructure cannot substitute for that evidence.
The model abstracts network and authorization transport and establishes no timing bound.
It bounds the number of registered scopes, with encoded row and issuance sizes subject to their own budgets.
The mathematical namespace and epoch counters are natural numbers. A finite representation needs an explicit exhaustion rule that preserves non-reuse.

## Reproduction

The checked run used Python 3.13, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19 and Lean 4.35.0.
The runner saves commands, traces and diagnostics in `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/55-pool-incarnations/run.py
```
