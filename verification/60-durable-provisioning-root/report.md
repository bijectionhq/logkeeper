# Study 60 · Recover the provider's durable fence

2026-11-23

## Verdict

Use an ordered provider journal for changes to the provisioning root.
A terminal result can escape once the exact command is chosen and applied and its frames and recovery path are durable.
Either crash-selectable base must reach the same chosen cutoff before the provider resumes admission.
Readable frames beyond that authorized cutoff remain outside the recovered state.

The recovered root preserves its generation and each prior retirement.
A queued create remains subject to the current recovered guard even when it was queued before the retirement receipt.

## Bounded comparison

[DurableRoot.tla](DurableRoot.tla) separates application, result publication, byte durability, locator durability, and selector publication.
It starts with a funded empty namespace and covers one replacement and one power loss.
The active bank model includes scoped provisioning, registration, and retirement commands.
Command and selector histories are finite, and the media fault outcomes are abstracted.

| Case | Distinct states | Result |
| --- | ---: | --- |
| Up to two root decisions | 5,492 | All four safety laws hold. |
| Up to three root decisions | 99,628 | The same laws hold through a new namespace and a delayed old request. |

| Weakening | Shortest counterexample |
| --- | --- |
| Publish with bytes unverified | The receipt escapes ahead of the durable command in five transitions. After power loss the retired scope can reopen in seven. |
| Publish with its recovery path unverified | The receipt escapes in five transitions and becomes inconsistent with the recovered guard in seven. |
| Serve immediately from the crash-selected base | A receipt escapes, a crash selects an older base, and that base reopens the namespace before replay. Eight transitions. |
| Apply an intact unchosen frame | Stage a command, crash with its frame readable, and apply it while recovering. Three transitions. |

## General proofs

[DurableRoot.lean](DurableRoot.lean) checks nine theorems using standard axioms only.
The ordered reducer handles scoped reserve, create and finish commands and admits other child commands through their refinement of the namespace reducer.
Its replay produces a legal namespace trace.
A terminal receipt requires the exact accepted finish at an applied position of the durable prefix.
The two media durability checks are independent.

The media theorem derives preservation of the receipted frames through either legal selector.
The authorized reader checks the exact chosen prefix and returns only that prefix, including when additional intact frames are present.
The composition with journal rotation recovers the exact prefix through any selectable base and its suffix.
It preserves earlier terminal evidence across arbitrary later namespace changes and refuses the old provisioning request at the recovered root.
The two Lean negative controls fail when publication omits byte durability or opening includes intact but unchosen frames.

## Amendments

[A231–A234](../amendments.md#study-60--2026-11-23) bind root receipts to recoverable applied commands, require exact reached cuts through either selector, and separate framing validity from the authorized prefix.

## Acceptance programs

- P89. Publish a retirement receipt, retain two possible selectors, and crash into the older one. Recover the fence, admit the replacement, and refuse the old create. The witness takes twenty transitions.
- P90. Choose a retirement and crash before it applies or produces a receipt, with two possible selectors. Recover through the older one and derive the original receipt. The witness takes fifteen transitions.
- P91. Open an exact chosen prefix when intact later frames survive. Lean constructs the result for every later suffix, and the weakened TLC reader applies an unchosen frame.

## Residue

The journal proof assumes the byte and namespace observations imply the modeled crash durability and a certified prefix authenticates the selected command stream.
The selected base contains the exact reducer state at its cut.
The storage adapter still has to establish both facts, authenticate original inputs, and enforce the physical effect boundary when applying a live decision.
The subordinate reducer carries the existing guarded child contract.
Root replay reconstructs decisions and does not by itself repeat external effects.
Any original scope bytes stored separately, including bytes retained by other logs or staging, remain part of that scope's custody inventory.
The bounded check covers a single provider authority and gives safety evidence rather than an election or latency guarantee.

## Reproduction

The checked run used Python 3.13, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19 and Lean 4.35.0.
The runner records commands, settings and diagnostic traces below `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/60-durable-provisioning-root/run.py
```
