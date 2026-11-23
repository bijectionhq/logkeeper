# Study 56 · Encode and exhaust the incarnation inventory

2026-11-23

## Verdict

Refuse new physical namespace issuance once the issuer reaches its largest serial.
Keep existing inventory and settlement operations available.
If a fault occurs at the largest usable access epoch, close the scope with an explicit terminal phase.
It retains its original custody and can settle.
Its last usable epoch cannot authorize a return.

An older inventory checkpoint can still be selected after a successful issuance.
Replay its complete certified ordered suffix before resuming.
The selected image alone can contain an earlier issuance watermark or access phase.

## Bounded comparison

[FiniteInventory.tla](FiniteInventory.tla) uses finite serial and epoch widths, cached proof delivery, exact terminal settlement, and stable and visible inventory selectors.
The chosen checkpoint suffix is abstracted as its exact final inventory state.
The model records every issued identity and whether a fault invalidated the cached proof so it can detect reuse.

| Case | Distinct states | Result |
| --- | ---: | --- |
| Two live slots, two serials, largest epoch one | 230 | All four safety laws hold. |
| Two live slots, three serials, largest epoch two | 4,828 | The same laws hold across more scope lifetimes and epochs. |
| One slot and serial with checkpoint publication, sync, and recovery | 510 | The same laws hold while both checkpoint selectors are possible. |

| Weakening | Shortest counterexample |
| --- | --- |
| Wrap the issuer | Issue the last serial, lose and settle its scope, then issue that serial again. Four transitions. |
| Keep using the maximum access epoch | Capture a proof at the maximum, lose the scope, reconnect it, and reuse the invalidated proof. Seven transitions including initial setup. |
| Restore a selectable image without its suffix | Issue once after the old checkpoint and recover the old watermark. Two transitions. |
| Issue from the rolled-back watermark | Repeat issuance after recovering the old checkpoint without its suffix. Three transitions. |

## General proofs

[FiniteCounters.lean](FiniteCounters.lean) checks eight theorems using standard axioms only.
Finite transitions project to the original scoped custody machine and preserve its physical, inventory, and issuance invariants.
They also preserve ascending issuance and descending order of the registered IDs.
An exhausted issuer refuses registrations, and a fault at the last usable epoch can still close access without altering any custody.
Existing exact terminal settlement is admissible regardless of either counter's value.
An exhausted scope stays offline across reconnect attempts.
Replaying the certified exact selected base and suffix returns the same inventory as replaying the complete chosen ordered history.

[InventoryCodec.lean](InventoryCodec.lean) checks nine theorems using standard axioms only.
The reference format uses one domain byte, one fixed-width issued watermark, and rows in descending incarnation order.
Each row has one phase byte and two fixed-width words for its scope and epoch.
A sealed row stores the maximum epoch and decodes to a terminal logical state beyond the usable range.
The range and ordering proofs establish that representable reference states produce well-formed inventory bodies.
A parser enforces the configured row limit and checks range, ordering, terminal phase, and the exact canonical wire representation.

With word width `w` bytes and at most `K` entries, the two crash-selectable inventory bodies fit in `2 × (1 + w + (2w + 1) × K)` bytes.
For eight-byte words, that is `18 + 34K` bytes.
This count is for the inventory bodies. The outer authenticated envelope, ordered suffix, working space, and underlying custody records have their own budgets.
The two Lean controls fail if recovery can omit the ordered suffix or the decoder maps a sealed row back to its last usable epoch.

## Amendments

[A215–A218](../amendments.md#study-56--2026-11-23) require bounded refusal at issuer exhaustion, terminal closure at access exhaustion, exact suffix replay before admission, and canonical bounded rows.

## Acceptance programs

- P76. Exhaust issuance, keep the first scope serving, and exactly settle the second. TLC reaches this in six transitions.
- P77. Lose a scope after reaching its final epoch, seal it, and perform exact terminal settlement. TLC reaches this in five transitions. Reusing the epoch admits a previously invalidated proof in the negative control.
- P78. Issue at the limit, publish the newer image, then select the older stable image while the newer one is visible. Recovery preserves the chosen issuer in the three-transition witness. The negative control reissues a used ID when it skips suffix replay.
- P79. Encode and reopen an arbitrary well-formed inventory, preserving both the issued watermark and sealed states. Lean verifies the round trip, unambiguous bytes, and two-image byte cap.

## Residue

The proofs use authenticated exact checkpoint and ordered-history inputs as premises.
They leave concrete persistence, provider namespaces and transport framing to their refinements.
The reference decoder checks canonicality by re-encoding the bounded inventory.
The byte bound concerns the stored and selectable inventory sections, with scratch allocation and physical-media claims outside its scope.
The design deliberately chooses terminal refusal for exhaustion of this issuer and this access scope.
A new outer issuer, if ever needed, requires independent non-reuse and authority handoff evidence.

## Reproduction

The checked run used Python 3.13, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19 and Lean 4.35.0.
The runner saves commands, traces and diagnostics in `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/56-finite-inventory/run.py
```
