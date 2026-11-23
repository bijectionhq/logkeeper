# Study 41 report · Bound provider write-ticket state

2026-11-23

## Verdict

Store the provider's issuance watermark and its exact live tickets.
Issue the serial and live row together.
Materialization uses the live row and consumes it with the effect.
The provider can then forget the terminal row.
A delayed capability cannot recreate authority at a missing row.

An authenticated issued serial with no live row proves permanent closure, including after restart.
The same observation for a still-unissued serial supplies no terminal proof.
An exact result with its original payload requires its own evidence while it is owed.

After stable absence, discard the entire old namespace's ticket book.
Keep the address's namespace issuance fence.
The replacement uses a fresh scope even when its first local ticket has the same serial as an old request.

## Bounded comparison

The ticket model has one physical version, an issued window, replayable old requests, and one restart.
The alternate capability protocol uses a terminal marker to prevent a duplicate effect.
The model's historical completion and restart fields track observations for the checker.
They are independent of the live rows and the capability protocol's actual marker table.

| Protocol | Possible tickets / live width | Distinct states | Checked result |
| --- | --- | ---: | --- |
| Positive live admission | 3 / 1 | 896 | Six safety laws and the terminal-row bound hold. |
| Negative check against terminal markers | 3 / 1 | 896 | Six safety laws hold. |
| Positive live admission | 5 / 2 | 76,918 | Six safety laws and the terminal-row bound hold. |
| Negative check against terminal markers | 5 / 2 | 76,918 | Six safety laws hold. |
| Exact namespace at one reused address | Two namespaces, one local serial each | 183 | Three safety laws hold. |

The six ticket laws cover issued-ticket accounting, closed and completed ticket non-reuse, at most one effect, stable erasure, and bounded live rows.
The address laws cover exact effect scope, no old namespace reuse, and stable absence before reclamation.
TLC checks the terminal-row limit separately at the same width for both representations.
The bounded scans supply safety and acceptance evidence. They make no temporal claim about a provider that stays unavailable.

| Amendment | Weakening | TLC evidence |
| --- | --- | --- |
| A157 | `missing_is_live` | Use an issued capability with no live row to recreate deleted bytes in five transitions. |
| A157 | `forget_markers` | Discard a marker in the negative-check protocol and recreate deleted bytes in six transitions. |
| A157 | Keep individual completed markers | Retain three completed rows at live width two in six transitions. |
| A158 | `split_issue` | Certify a ticket closed before delayed registration in three transitions. A five-transition trace recreates bytes after erasure. |
| A158 | `certify_unissued` | Certify a future serial and subsequently issue it live in two transitions. |
| A158 | `restart_drops_issuance` | Complete a ticket, reset issuance at restart, and reissue its serial in four transitions. |
| A159 | `route_only` | Apply an old request to the next occupant of the address in seven transitions. |
| A159 | `forget_namespace_issuance` | Reclaim the old namespace and reopen its identity after restart in five transitions. |
| A159 | `reclaim_before_absence` | Reclaim the namespace without its stable absence proof in one transition. |

The four-transition closure witness completes the ticket before restart and certifies closure afterward without a terminal row.
The six-transition erasure witness rejects a duplicate after erasure and restart.
The four-transition width witness keeps the first ticket pending, completes a later ticket, and allocates beyond the original live width.
The eight-transition address witness restarts while the address is vacant and refuses the old request after fresh issuance at the same local serial.

## General proofs

Lean checked nineteen theorems using standard axioms only. [Proof source](TicketBook.lean)
Unique active serials ensure a live row selects one exact binding.
The book stays within the configured live width across arbitrary finite traces.
An issued absent serial stays closed under later commands.
Effect completion establishes that closed state without a terminal row.
The information proof gives two distinct payloads whose completed books are identical, so no lookup on the compacted book recovers both exact payloads.

The issuance and consumption steps refine the provider I/O model from Study 40.
An authenticated view of the compact book reconstructs the closure facts needed by its erasure decision.
The scoped address wrapper refines the non-reused reservation slot from Study 06.
A retired scope cannot return across arbitrary further changes, even when its address can serve an otherwise identical local ticket.
The three proof controls fail when a serial substitutes for the full live binding, reclamation omits absence, or the effect decision omits its exact namespace.

## Remaining obligations

The positive lookup needs an authoritative physical effect boundary, a durable issued watermark, and exact non-reused namespace identities.
The study assumes the physical delete and confirmed absence contract from the provider closure study.
It proves ticket memory and closure, while exact result retention and the independent bytes and I/O budgets still follow their own contracts.
The adapter must refine this closed universe of issued tickets to actual authenticated effect routing and recovery.
Finite counter representation, shared objects and simultaneous full-footprint takeovers still need checks.

Apply [A157–A160](../amendments.md#study-41--2026-11-23).

## Reproduction

Use Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner writes configurations, traces, and proof diagnostics to the ignored `.results` directory.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/41-provider-ticket-compaction/run.py
```
