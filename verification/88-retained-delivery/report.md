# Study 88 · Bound and recover unfinished delivery evidence

2026-11-23

## Verdict

The ordered authorization of a reply creates an obligation with a lifetime of its own.
Closing or reusing the original logical read slot can leave the authorized physical use outstanding.
Retaining the original command until every delivery finishes would let a slow operation pin the global replay window.

The shared ordered reducer now records the exact chosen reply in a distinct bounded delivery slot.
Its scoped paid proof binds the slot and non-reused delivery serial, original invocation and basis, and exact physical borrow.
The physical proof still leaves the frame's global ordered position to the journal.
A grant and its result row are one transition.
A stale or occupied slot refuses.
Other commands share that order and keep the result book intact.

Each selectable authenticated checkpoint names the book and covers its independent physical dependencies.
A checked result row can recreate the original canonical packet after the old frame disappears.
Delivery still requires the authenticated original caller and the exact still-held borrow.
Exact original-custodian completion or effective stop clears the entry, and the issuance floor survives.
A full book leaves existing results and settlement available.

## Bounded comparison

[RetainedDelivery.tla](RetainedDelivery.tla) models one slot, a still-held original borrow, one raw authorization frame and two crash-selectable bases.

| Reference case | Distinct states | Checked result |
| --- | ---: | --- |
| Close, checkpoint, compact and crash | 8 | The independent result completes without its raw frame. |
| Exact settlement | 11 | Foreign custody evidence cannot clear the live entry. |
| Recycle a slot | 18 | The original issued identity cannot reopen. |
| Full delivery book | 6 | A second operation cannot take an occupied slot. |

The first scenario checks eventual compaction and completion under weak fairness for its valid actions.
The other scenarios check safety.

| Negative control | Shortest counterexample or temporal result |
| --- | --- |
| Couple the result to the original read row | Closing, checkpointing and crashing loses a still-held chosen result in six transitions. |
| Collect after publishing only the visible checkpoint | A crash selects the older path with the raw suffix gone in five transitions. |
| Accept settlement for the wrong physical binding | Clear the original entry using a different identity in two transitions. |
| Forget the durable issuance floor | Reopen the settled serial in three transitions. |
| Ignore slot capacity | A competing operation overwrites the charged live entry in two transitions. |
| Keep the raw frame until completion | The reference recovery program cannot compact while the result is still outstanding. Temporal counterexample. |

## General proofs

[DeliveryRecovery.lean](DeliveryRecovery.lean) reports twenty Lean theorems with standard axioms only, including the book and reducer laws.

- [RetainedDelivery.lean](RetainedDelivery.lean) composes the original delivery decision with its paid bounded result insertion in the same reducer.
  The direct lower-level delivery command cannot bypass it.
  Closing the logical read preserves the independent result.
  Authenticated settlement requires the exact key and original physical binding and preserves other slots and the issued counter.
  The same immutable funding proof cannot be rebound to a new identity.
- [DeliveryBook.lean](DeliveryBook.lean) checks exact round-trip framing for each representable row and the finite typed section.
  The basis end is derived from the original receipt cut.
  Each row body uses one format byte and seventeen fixed-width words.
  With word width \(w\) and delivery slot limit \(n\), a section needs at most \(w + n(2 + 17w)\) bytes for its issuance counter and tagged slots.
  Every accepted replay preserves the representable state required by that bound.
- The named opener reads the bounded section from the same authenticated control envelope as the ordered journal and read state.
  It checks the independently retained delivery dependencies even when the logical read is gone.
  Both certified bases with their exact suffixes recover the same combined state.
  A checked named checkpoint can supply the exact original reply without reading the old authorization frame.
- The raw frame can leave when neither selectable replay nor a borrower still needs it and every outstanding result has exact coverage in each selectable recovery path.
  The removed frame can be absent while the delivery continues under the original physical borrow.

Lean rejects a mutation that lets the bare delivery branch bypass the retained book.

## Amendments and acceptance programs

[A346–A350](../amendments.md#study-88--2026-11-23) establish independent bounded retention, exact settlement, and joint checkpoint coverage.

- P172. Choose a paid delivery, close its original read, compact the old frame, and reopen the ordered control image.
  Recreate the original canonical reply during source loss while the independent borrow remains held.
- P173. Keep both crash selectors alive during a checkpoint switch.
  Retain the raw suffix until the older path can also recover the exact chosen result.
- P174. Refuse settlement for another physical use.
  Settle the original, reuse the slot, and refuse a delayed old serial or an attempt to rebind the same paid evidence.
- P175. Fill the delivery book, refuse an extra grant, and keep existing delivery and exact settlement available.

## Residue

The proofs use authentic fixed bindings for the provider proof and terminal stop or completion.
They also use exact certified prefix selection and immutable named checkpoint contents.
The row codec and typed section bound do not specify the complete checkpoint transport.
The complete sealed handoff attachment, live provider funding and release of unused preparations, signer authorization, and physical durability still require refinement.
The proof does not establish progress when all paid slots stay blocked by independently unsettled operations.
The original full-frame proof remains a reference for the selected history; the wire representation of proof compaction still needs the authentic checkpoint issuer and manifest.

## Reproduction

Use TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.

~~~sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/88-retained-delivery/run.py
~~~
