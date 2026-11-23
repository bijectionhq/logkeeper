# Study 45 · Move a capacity pool's authority

2026-11-23

## Verdict

Changing a pool's owner must preserve the exact closed pool ledger.
Copying the charged occupancy alone can preserve the byte count while reopening a canceled key.
An earlier staged image can also omit a live hold that arrived before the pool sealed.
The successor needs the live debits, the channel's issuance and refusal state, ordinary occupancy, and the effective resource limit from the same cut.

An installed channel floor and a bounded issuance window make it possible to compact individual cancellation rows.
Live debits retain their exact scope across floor compaction, owner replacement, and an offline predecessor.
Planned contraction checks the full charged ledger before lowering a pool's limit.

## Properties and comparison

[PoolAuthority.tla](PoolAuthority.tla) models one physical pool, one issue channel, two potential pool owners, and separate move decisions.
The issued keys carry immutable weights of one or two units.
Ordinary occupancy and prepared and committed holds share a limit of three units, which the controller can reduce to two.
Floor certification, installation, and durable acknowledgment are separate actions.
A prepare authorized earlier can arrive after the move has decided to abort. Local refusal takes effect once the pool applies cancellation or installs the covering floor.

| Baseline | Ticket identities / issuance width | Distinct states | Checked result |
| --- | --- | ---: | --- |
| Exact pool cut and compact refusal | 3 / 1 | 240,305 | Eight safety laws hold up to the bound. |
| Exact pool cut and compact refusal | 3 / 2 | 656,771 | Same safety laws hold up to the bound. |
| Eventual installation and reconciliation | 2 / 1 | 35,713 | Both temporal laws hold up to the bound. |

The safety checks cover numeric occupancy, preservation of the effective limit, persistent refusal, observed and committed hold preservation, exclusion of old owners, installed credit, and cancellation row bounds.
The temporal model gives weak fairness to successor installation and application of already chosen decisions.
Its seal makes the cut available to a ready successor, and the modeled decision evidence remains retrievable.
The results quantify over the reachable states or behaviors at each listed bound.
They make no claim that a disconnected pool or unavailable quorum can continue to admit new work.

| TLC weakening | Shortest safety failure or temporal trace |
| --- | --- |
| Ignore prepared occupancy | Ordinary admission fills space already held by a prepare in five transitions. |
| Shrink below charged use | Reduce the limit while three units are charged in four transitions. |
| Restore the original limit at takeover | Shrink, seal, and install with the old limit of three in four transitions. |
| Lose the installed floor | Cancel an empty key, compact, and install an image with a regressed floor. The old key is eligible again in eight transitions. |
| Lose an individual refusal | Cancel before the floor covers the key, then install without its individual refusal in six transitions. |
| Lose live debit rows | Grant and observe a hold, then install without the hold in six transitions. |
| Install the earlier stage | Stage before a hold, then grant it and install the stale stage in six transitions. |
| Admit at the old owner | Install the successor and accept a new prepare at the old owner in five transitions. |
| Issue credit from an offered floor | Plan and abort an intent, offer its floor, and plan another before the floor is installed in four transitions. |
| Retain every cancellation marker | Cancel two distinct keys under issuance width one in nine transitions. |
| Require the predecessor to remain available | Stage and seal, then disconnect the old owner. Installation remains disabled forever. |

[PoolAuthority.lean](PoolAuthority.lean) checks ten theorems using standard axioms only.
The covered recovery majority can read the exact latest pool image.
The chosen cut determines the image uniquely and preserves the exact result of key lookup, acquisition checks, and ordinary capacity checks on installation.
The proof reuses the channel gate to close an empty key and preserve its refusal after exact recovery.
Installing a floor preserves every debit and its numeric charge.
Exact release cannot increase the sum of charged bytes.
The issued window assigns each retained cancellation serial a distinct slot in the configured width.
The two Lean controls catch admission at a stale owner and contraction that ignores live debits.

## Amendments

[A172–A175](../amendments.md#study-45--2026-11-23) require exact cut adoption, acknowledged floor credit, stable reservation scope with a current effect boundary, and funded contraction.
The channel uses the same issuance and compaction mechanism as the earlier custody registration studies.
It adds a weighted capacity charge to each live held binding.

## Acceptance programs

- P47. Cancel the first key with no hold, install and acknowledge its refusal floor, and prepare and choose bind for the second key. Seal the pool before applying bind. Disconnect the predecessor and install the successor. The successor refuses the delayed first key and applies the existing bind against the second key's recovered debit. TLC reaches this in sixteen transitions.
- P48. Shrink from three units to two while a live hold fits the lower limit, and take over with that limit in force. TLC reaches this in six transitions. The unsafe limit reduction fails the occupancy law.

## Residue

The TLA+ model assumes a single logical pool over the same physical resources before and after takeover.
The Lean sizing argument measures the exact grant bindings enumerated in the image.
The production refinement must prove that enumeration includes each charged key exactly once and that its declared footprint covers the physical bytes and pending effects.
The studies still need a common model with multiple moving pools, the complete vector decision at the move authority, and durable evidence delivery.
The proof does not equate a physical loss or evacuation with a planned limit change.
Moving actual bytes and restoring the degraded placement budget need separate verified custody and admission transitions.

## Reproduction

Run with Python 3.13, Java 21.0.13+9, TLC 2.19, and Lean 4.35.0.
The runner checks the pinned TLC jar and saves the configurations, commands, and diagnostics under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/45-pool-authority/run.py
```
