# Study 85 · Bind named recovery to the current ranked installation

2026-11-23

## Verdict

A predecessor can lose its learner after a quorum chose a close.
The last learned checkpoint and the newest ranked accepted prefix can also share the same data frontier.
Recover from the greatest exact, durably fenced quorum report and inherit the previously installed basis.
Open the checkpoint named by the certified historical prefix and replay only its exact covered suffix.
The candidate can be staged before the successor installs it.
The existing single-choice installation slot then binds the exact image and ordered prefix, after the voting replicas have durable backing.

A historical installation can remain genuine after the journal advances within the same membership revision.
Initial publication therefore validates both the current lineage and revision and the exact current ordered frontier.
A delayed activation cannot reopen the bootstrap state once live order has advanced.
After staging, the activation path consumes the locally prepared result and current installation evidence.
A live recovery quorum can open the exact chosen image from a voter whose latest accepted seed still binds it.

## Bounded comparison

[RankedNamedRecovery.tla](RankedNamedRecovery.tla) starts with a learned read admission, a later quorum-chosen close that the learner missed, and a still later accepted nonce abandonment.
Two predecessor reports survive.
One is longer at a lower ballot and contains a rival suffix.
The ordinary scenario lets either exact named checkpoint stage and excludes a third checkpoint with the right position and wrong control.
The small model holds the data frontier fixed.

| Reference case | Distinct states | Checked result |
| --- | ---: | --- |
| Surviving fenced quorum and complete inputs | 12 | Either exact base stages. The successor installs and publishes the closed read and advanced nonce state. |
| Incomplete suffix | 2 | No candidate can stage. |
| Fenced reports name another successor | 2 | No candidate can stage for the requested successor. |
| Superseded revision | 20 | Publication after replacement refuses. |
| Existing revision advanced | 14 | Publication after a later ordered frontier refuses. |
| Installed target loses its live quorum | 14 | The historical install remains genuine and publication refuses. |

In the covered case weak fairness covers report capture, staging, each surviving target installation, and publication.
The remaining baseline runs check safety.

| Negative control | Shortest trace or temporal result |
| --- | --- |
| Recover only the learned prefix | Publish an older cutoff that omits the close in five transitions. |
| Rank reports by length alone | Publish the longer lower-ballot rival in five transitions. |
| Match the checkpoint by ordered position alone | Publish the live result from a rival checkpoint in five transitions. |
| Publish the ranked winner before successor install | Serve with no installed quorum in three transitions. |
| Skip the successor binding | Publish under a certificate addressed elsewhere in five transitions. |
| Skip the current revision check | Publish after replacement in six transitions. |
| Skip the current ordered frontier | Publish an older image in the same revision in six transitions. |
| Skip the live target quorum | Publish after the installed target loses its quorum in six transitions. |
| Skip suffix coverage | Publish despite a missing final frame in five transitions. |
| Require every predecessor voter | One unavailable voter stalls the covered handoff. Temporal counterexample. |
| Require successor installation before staging | Staging and installation wait on each other. Temporal counterexample. |

## General proofs

[RankedNamedRecovery.lean](RankedNamedRecovery.lean) checks twelve theorems with standard axioms only.

- Durable fenced reports cover every source choice, including a certificate assembled after fencing. A checkpoint published for an earlier chosen or inherited installed prefix lies within the exact recovered cutoff.
- The canonical envelope and immutable component names make a historical and current opening select the same typed image. That image includes the result rows, paired holds, and consumed nonce floor. The named base and covered suffix reproduce the complete ranked application.
- Preparation checks the successor, selected scope and named historical prefix, the currently accessible checkpoint and required custody, and every exact suffix frame. Installation is a later step.
- The existing activation slot decides the seed containing the exact lineage, revision, history and image. Any live recovery quorum can open that seed from a member whose latest accepted vote still binds it. The same device rules permit collecting superseded unbound images. Two competing successful seed certificates for the same slot agree on the entire installed state.
- Initial activation checks the current lineage, revision and ordered frontier. Either selectable base produces the same activated image. Spent nonces in an earlier certified choice survive the resulting active replay.
- Lean rejects a predicate that compares only lineage and revision while ignoring the current ordered frontier.

The historical prefix and application fields in the publication are typed proof evidence.
On the wire the authority needs compact authenticated names for that prefix and the exact typed contents.
The proof orders full frame identities and never requires a finite commitment to be mathematically injective over arbitrary histories.
The storage interface assumes authentic names and identical immutable resolutions when both historical and current lookups succeed.

## Amendments and acceptance programs

[A334–A337](../amendments.md#study-85--2026-11-23) settle ranked input selection, historical checkpoint binding, one chosen installation, and initial publication at the exact current frontier.

- P162. Lose a learner after a protected-read close is chosen. Recover the highest ranked exact report from the surviving quorum, including a later accepted nonce transition. Either exact named base reproduces the same state. A rival same-position body or missing suffix refuses.
- P163. Stage with an addressed predecessor fence and complete exact media. Choose and apply the same image at the successor slot on a durable quorum. A delayed or competing attempt through the same slot cannot choose a different image.
- P164. Refuse publication from a foreign successor, a superseded revision, or a bootstrap cutoff older than the current ordered frontier of the same revision.

## Residue

The publication carries certified historical application and exact envelope issuance as a typed premise.
The runtime still needs canonical full-frame and control encoding, a proof of real authenticated publication, compact prefix verification, and immutable provider lookup.
The capture and target evidence use the existing abstract replica and durability contracts.
Binding actual voters to protected zones, exact manifests and media, and the current frontier check at the serialized effect boundary remains open.
The staged token represents successfully validated local material; transport, crash durability of staging and cleanup accounting still need runtime refinement.
After initial activation, fresh service still verifies the current admission and custody conditions of the operation.

## Reproduction

Use TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.

~~~sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/85-ranked-named-recovery/run.py
~~~
