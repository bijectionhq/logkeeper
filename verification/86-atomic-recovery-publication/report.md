# Study 86 · Serialize local recovery publication and protect use separately

2026-11-23

## Verdict

A validated recovery candidate can go stale between validation and publication.
The local serving owner atomically compares the candidate's captured lineage, revision, exact applied frontier and process session, then fills an empty slot.
A delayed candidate cannot overwrite the live book.
The live reducer applies chosen extensions under the matching journal scope and advances the attached image together with its frontier.
The existing successor quorum still chooses the authoritative installation.

Physical reachability can change after the last recovery reply arrives.
A local attachment is a materialized view that may lag a later certified group decision.
Fresh use needs its own current journal authorization on the matching applied view and exact protected inputs.
An already admitted operation may finish with its own still-held physical borrow if the group loses quorum.
Effective stop of that borrow prevents completion.

## Bounded comparison

[AtomicPublication.tla](AtomicPublication.tla) abstracts exact image content into a stamp and uses a separate Boolean for physical reachability.
An initial quorum observation is available before the model loses the group.
The model separates the local effect from admission and completion.

| Reference case | Distinct states | Checked result |
| --- | ---: | --- |
| Frontier moves after an initial check | 8 | The older candidate refuses at attachment. |
| Replacement at the same data cut | 5 | The older revision cannot attach. |
| Process restarts at the same revision and cut | 5 | The old session cannot attach. |
| Address reused for another lineage | 5 | The old lineage cannot attach. |
| Concurrent recoveries | 5 | A filled slot is never replaced by recovery. |
| Group becomes unreachable after evidence arrives | 10 | An attached view grants no fresh use during the outage. |
| Exact effective stop | 8 | The admitted operation cannot complete after its own borrow stops. |
| Admitted operation overlaps quorum loss | 10 | The admitted exact operation can still finish while its borrow is protected. |
| Restart of an already advanced revision | 7 | A fresh session reopens the later certified frontier through the existing installation. |

The overlap case uses weak fairness for attachment, admission, loss, and delivery.
The reopen case uses weak fairness for old preparation, restart, fresh staging and attachment.
The other cases check safety.

| Negative control | Shortest trace or temporal result |
| --- | --- |
| Reuse the earlier successful check | Check, advance, and attach the stale image in four transitions. |
| Omit the revision, session, or lineage | Each missing comparison admits an old image in three transitions. |
| Let recovery overwrite an open slot | The second recovery replaces the first in three transitions. |
| Let the attached image authorize fresh use | The group loses quorum and the image starts a new use in four transitions. |
| Ignore effective stop | Complete the stopped operation in five transitions. |
| Demand physical quorum reachability again at completion | An already admitted operation with its own protected inputs can stall forever. Temporal counterexample. |

## General proofs

[AtomicPublication.lean](AtomicPublication.lean) checks nineteen theorems with standard axioms only.

- A candidate comes from Study 85's exact ranked activation proof and carries the captured matching local stamp. A successful effect compares the entire current stamp, fills an empty slot, and installs the exact applied image.
- A process starting in an already installed scope can use exact certified checkpoint and suffix replay at a later frontier to attach under its new session.
- A prior successful comparison cannot authorize attachment after the stamp changes. A previously increased revision, prefix or session cannot roll back through subsequent monotone observations. A later observation atomically detaches the old image.
- A chosen extension from a different journal scope refuses. Applying the exact chosen suffix updates the image and frontier together. Every finite interleaving of accepted attachment, observation and application steps preserves a sound image and monotone scope.
- The same observed quorum messages can occur with the quorum currently reachable or newly unreachable. No predicate on that transcript decides instantaneous physical reachability when failures can happen without a new message.
- Fresh recovered reply admission requires its own ordered authorization, caller authentication, the original live row and paired exact basis, and an exact delivery borrow. The original caller can find its retained result without supplying the lost permit.
- The admitted reply completes only while its own borrow remains held. Completion uses the original immutable packet and does not consult the current installed run or reachability.
- Two Lean mutations reject ignoring the session or granting read use from cache alone. The external harness compiles for an admitted token, then rejects both forging a token and rewriting one to use a different physical borrow.

The complete command list in the stamp is proof evidence.
The effect implementation should compare an exact compact certified frontier identifier.
The boot identity names the local publication lifetime.
Existing immutable image bytes can be validated for a new lifetime under a fresh recovery task.

## Amendments and acceptance programs

[A338–A341](../amendments.md#study-86--2026-11-23) bind attachment to the effect, separate authority from local publication, and preserve independently protected completion.

- P165. Validate a chosen bootstrap image, then advance, replace or restart its endpoint before publication. Refuse the old attempt even when the data cut stayed fixed. An exact new attempt fills an empty current slot and a second one cannot replace it. A fresh local session can reopen the already installed journal at a later certified cutoff.
- P166. Advance an attached image through an exact chosen suffix under the same journal scope. The applied image and ordered position move together. Refuse an extension from a foreign revision.
- P167. Attach after quorum evidence arrives and the group subsequently becomes unreachable. Deny any new use without current authority even though the local image is valid.
- P168. Reconcile an authenticated live original invocation and take its exact delivery borrow. Finish the admitted operation through group loss while the borrow remains held. Refuse after effective stop, and refuse a forged or redirected admitted token.

## Residue

The serialization point models a compare-and-attach operation over local endpoint state.
The running application still needs one actual owner or conditional transaction for that effect and a non-reused process identity bound before dispatch.
The ordered frontier is the local certified application frontier.
Network progress can leave higher chosen work to apply, so the serving boundary still needs an exact authorization witness at use.
The combined model checks that witness and the exact borrow; the live protocol must refine authorization issuance, retirement races, provider reservation and effective stop.
The Lean compile-fail checks cover this reference module's constructor privacy.
Transport, signer authorization, production code admission, and integrated fault tests remain separate.
The model does not prove startup progress under continual replacement or unlimited backlog.

## Reproduction

Use TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.

~~~sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/86-atomic-recovery-publication/run.py
~~~
