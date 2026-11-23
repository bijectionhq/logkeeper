# Study 64 · Recover the chosen append and its exact funding basis

2026-11-23

## Verdict

Order window installation, pruning, and source commands alongside appends.
A window installation advances the ordered position while the logical data cut stays the same.
Bind the checkpoint to the exact source state and window book at that ordered position.
Recover from the actually selected pair and consume exactly the chosen suffix.
The append reducer uses that frame's original request and spends the matching range in the recovered book.

## Bounded comparison

[ChosenReplay.tla](ChosenReplay.tla) models one stream, two journal windows, and up to three chosen commands.
It starts with the chosen frames available and can stage a rival at the first position, a first-position frame from another lineage, and a valid continuation beyond the chosen cutoff.
An older checkpoint and a pending selector for the new checkpoint can coexist.
The model checks the exact final state and suffix results at each successful open.

| Installed cutoff | Distinct states | Result |
| --- | ---: | --- |
| Through the window installation | 112 | Every successful open matches its exact chosen suffix. |
| Through one append in the new window | 112 | The same law holds through the post-install append. |

| Weakening | Shortest counterexample |
| --- | --- |
| Match by position alone | Stage different bytes for the first position, then open with those bytes. Two transitions. |
| Ignore lineage | Stage another lineage's first frame and substitute it for the chosen frame. Two transitions. |
| Graft on the newest window state | Publish the pending replacement selector, then open the older base using the newer window and cursor. An earlier append and window install lose their original results. Two transitions. |
| Replay every intact frame | Stage the intact continuation after the exact installed cutoff and open through it. The extra frame advances the recovered state. Two transitions. |

## General proofs

[ChosenReplay.lean](ChosenReplay.lean) checks thirteen theorems with standard axioms only.
The certificate proof uses the staged durable acceptors' ranked votes and proves agreement on the entire frame at a shared position.
The scoped replay entry point checks lineage and exact next ordered position, and checks that the physical suffix starts with every required chosen frame.
Under the stated vote authentication premise, its accepted input is the original ordered command.
A positive append in the live product uses the existing funded append reducer and spends a positive exact range of the actual pool-backed window.

The general recovery proof accepts either certified base and reconstructs the same source state and window book.
The recovered reply suffix matches the original ordered application from that base, with its full correlating frames.
The envelope composition uses the exact named data and control components and the manifest's covered dependency set.
The proof retains the exact-prefix premise on the selected body and excludes truncated, substituted, or overlong applied histories.
The two Lean controls remove stream binding and allow extra intact frames past the installed cut.

## Amendments

[A249–A252](../amendments.md#study-64--2026-11-23) bind funding to the chosen frame, require the exact selected source and window basis, and cap replay at the installed cutoff.

## Acceptance programs

- P101. Publish a pending new selector, stage the rival and foreign frames and the intact extra continuation, and recover from both selectable bases while selector publication remains unresolved. TLC reaches both opens in six transitions.
- P102. Supply a rival at the original position, a frame from another lineage, or an incomplete suffix. The exact reader or the scoped replay gate refuses it.
- P103. Supply the exact chosen suffix followed by more intact frames. Lean recovers the same suffix for arbitrary later frames.
- P104. Install a funded replacement window without advancing the logical data cut. Lean checks the advance of its ordered position and window generation, and shows why recovery needs the control state at the selected ordered position.

## Residue

The model assumes authentic vote attribution, exact immutable frame decoding, a genuine checkpoint body at its certified prefix, and enumeration of all necessary recovery dependencies.
The envelope theorem uses the existing canonical envelope check. Canonical encoding of the frame and the window book needs its own implementation refinement.
Replay evaluates original grant attachments under the same deterministic rules.
Live grant installation still needs the full prepared move vector to establish the same exact charges and physical custody across independently moving pools.
The recovery proof reconstructs the retained suffix. Older replies that remain owed require the previously specified retained evidence.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records commands, configurations, theorem checks, and failing traces below `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/64-chosen-append-recovery/run.py
```
