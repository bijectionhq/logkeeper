# Study 57 · Recover the chosen incarnation state

2026-11-23

## Verdict

Publish an incarnation result only from the exact chosen command after it has been applied.
A quorum can choose an issuance before the learner sees it or a client receives its reply.
Recover to the exact installed cutoff selected by the ranked authority protocol, including previously chosen but unlearned decisions.
A locally accepted candidate becomes usable only through the corresponding certified installation.

Open a certified inventory body at its actual selected base and replay its exact ordered suffix.
Use the same deterministic rules and immutable evidence recorded with each command.
Later evidence can authorize a new command at a new position. The earlier refusal stays the same.

## Bounded comparison

[InventoryRecovery.tla](InventoryRecovery.tla) uses three voters, a durable majority of two, one in-flight proposal, separate application and reply, and one crash.
The last application position and both crash-selectable inventory bases can lag the chosen head.
The reference supplies the exact installed recovery cutoff as an abstraction of the ranked protocol.
The finite commands model issuance and return with or without attached evidence.

| Case | Distinct states | Result |
| --- | ---: | --- |
| Issuance and return with up to two chosen positions | 4,320 | All four safety laws hold. |
| Issuance with up to three chosen positions | 2,782 | The same safety laws hold. |

| Weakening | Shortest counterexample |
| --- | --- |
| Reveal an issuance after one durable vote | Propose, persist one vote, and release a receipt. Three transitions. |
| Resume at the last learned position | Choose an issuance with two votes, crash before application, and resume at the old position. Five transitions. |
| Treat a locally accepted candidate as chosen | Propose, persist one vote, crash, and replay the candidate as an inventory change. Four transitions. |
| Refresh evidence during replay | Choose a return without evidence, receive evidence later, crash, and replay the old command as a success. Six transitions. |

## General proofs

[OrderedInventory.lean](OrderedInventory.lean) checks nine theorems using standard axioms only.
The reducer applies issuance, fault, reconnect, validation, settlement, and ledger commands using the finite scoped custody reference.
Successful commands refine its exact transitions.
A refusal leaves the inventory unchanged.
An issuance request names the exact next scope. Repeating that request after it succeeded cannot allocate another scope.
The reference reply guard checks the chosen proof, applied cut, and original command at the requested position.

After any sequence of these ordered decisions, the exact incarnation and physical custody invariants, finite counter bounds, and canonical record order hold if they held initially.
The recovery proof joins canonical decoding, either selected journal base, and exact suffix frames.
Replay gives the inventory obtained by applying the full ordered prefix.
The ranked composition obtains a live exact donor in the current recovery majority after any number of certified family changes.
Earlier chosen commands retain their original reply values and positions in the recovered prefix, without a learner or delivery premise.
Both Lean controls make the reply law fail by weakening its prerequisites.

## Amendments

[A219–A222](../amendments.md#study-57--2026-11-23) bind external issuance to a chosen and applied command, recover an exact current cutoff, preserve original evidence, and replay the same ordered results from each selectable base.

## Acceptance programs

- P80. Choose an issuance, crash before application or reply, recover through the older base, and obtain the original issuance result. TLC finds this in seven transitions.
- P81. Choose two issuances, publish a new visible base, crash into the still-selectable older base, and recover both issuances. TLC finds this in twelve transitions.
- P82. Choose a return without evidence, let proof arrive after the decision, then crash and replay. The old return remains refused in the seven-transition witness.

## Residue

The ordered proof assumes a certified base binds the exact replay state, including its separately stored custody ledger, to the selected inventory body and ordered prefix.
The corresponding command format and validity rules are stable for each position.
Donor evidence assumes its media meets the prior journal durability contract.
The Lean account command uses a deterministic subordinate ledger reducer under its refinement premise.
Provider authentication, transport, persistent certificate formation, correlation of a lost registration response to its original chosen request, and actual command encoding remain implementation obligations.
The bounded model abstracts ranked cutoff formation and does not demonstrate availability or latency across leadership contention.

## Reproduction

The checked run used Python 3.13, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19 and Lean 4.35.0.
The runner writes exact commands, diagnostics and counterexamples below `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/57-ordered-inventory-recovery/run.py
```
