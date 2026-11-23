# Study 84 · Keep closed read invocations spent

2026-11-23

## Verdict

A journal with available space can admit a delayed invocation again after closing and reclaiming its result row.
The second admission can return a different cut for the same identity.
The ordered source now carries a one-word floor for the current writer grant.
A fresh protected admission consumes exactly the next nonce in the same decision that records its result and hold.
An authenticated abandonment can consume that next nonce without allocating or releasing any read hold.
Closing a result releases its resources and leaves the floor intact.

The rule orders fresh admissions within a grant.
Several protected reads can be live and finish independently.
Journal traffic such as append and checkpoint publication does not consume read nonces.
Pending work progresses when the writer sends or explicitly abandons each earlier issued nonce under fair journal service.
If the writer loses the state that ties pending calls to issued identities, the ordered fence establishes a new grant before fresh issuance resumes.
A live old result remains recoverable by its original authenticated invocation.

## Architecture comparison

| Candidate | Decision and cost | Finding |
| --- | --- | --- |
| Deduplicate live result rows | Closing a read frees all of its metadata. | A delayed request can recreate a closed invocation. |
| Advance a largest-seen watermark | The first later nonce can retire every lower nonce implicitly. | A single out-of-order proposal can discard an earlier pending read. |
| Exact next nonce with ordered abandonment | One floor for the installed grant and a control command to abandon the next nonce. | One-use admission survives row reclamation. Earlier pending nonces receive an explicit decision. |
| Store exact spent identities in arbitrary order | Keep an exact membership classifier for every admissible spent subset. | Lean proves the summary must distinguish every spent subset. For \(n\) independently usable identities this implies \(2^n\) possible summaries, or at least \(n\) bits. |
| Use the next journal ordinal as the attempt's nonce | Validate a conditional marker at its named position. All journal traffic competes for that same ordinal. | An argued alternative. It needs a way to name an attempt before a lost reply and to resolve positions taken by unrelated commands. The separate read floor makes those commands irrelevant to read issuance. |

## Bounded comparison

[InvocationFloor.tla](InvocationFloor.tla) has one result slot, two grants, two usable nonces per grant, and a visible data-cut advance after release.

| Reference case | Distinct states | Checked result |
| --- | ---: | --- |
| Compacted exact retry | 4 | A read closes and its slot empties. Recovery restores its floor and refuses an old fresh admission. |
| Chosen abandonment | 3 | An early proposal for nonce two waits. Under weak fairness, abandoning nonce one allows nonce two to proceed. |
| Writer replacement | 6 | Under weak fairness, the successor reissues the live predecessor result, closes it, and admits its own nonce one. |
| Exhaustion | 5 | Fresh admission refuses both a wrapped nonce and an out-of-range nonce. |

| Negative control | Shortest trace or temporal result |
| --- | --- |
| Consult only live rows | Admit, close, reopen, then admit the original invocation again in four transitions. |
| Restore a rolled-back floor | The same four-transition duplicate after reopening the compacted image. |
| Use a largest-seen watermark | Admit nonce two ahead of an explicitly unresolved nonce one in one transition. |
| Remove abandonment | The absent next request prevents the later request from making progress. Temporal counterexample. |
| Remove exact grant matching | An old grant consumes the successor's fresh nonce space in five transitions. |
| Wrap after fixed-width exhaustion | The spent first nonce admits again in five transitions. |

The progress checks assume the named valid actions eventually stay enabled and apply fairly.
TLC does not establish availability for arbitrary clients or schedules.

## General proofs

[InvocationFloorProof.lean](InvocationFloorProof.lean) checks eleven theorems with standard axioms only.
It uses the actual [combined chosen reducer](../83-ordered-read-replay/OrderedReadReplay.lean) and its [pure grant and floor rules](../83-ordered-read-replay/ReadInvocationFloor.lean).

- The classical arbitrary-order exact-deduplication summary is injective over spent sets.
- The read floor can be carried across every valid abstract kernel writer step. Freeze keeps it until activation. A move to a greater placement generation or an exact same-placement epoch advance starts fresh nonce space. Retirement is terminal.
- Successful joint admission consumes its exact nonce. Spent calls and out-of-order higher nonces refuse before taking a new hold. An authenticated next-nonce abandonment preserves all holds and results. Exhaustion refuses both fresh admission and abandonment.
- Every intervening combined decision preserves the spent status of an admitted, abandoned, or superseded invocation. Either recovered base preserves spent status proved at any earlier certified prefix of the chosen cutoff.
- The floor has a canonical fixed-width encoding. The named checkpoint opener gets the read book and floor from the same authenticated typed control body, alongside the aligned journal. It rejects a malformed floor and cannot substitute a floor from a different control image.

Lean also rejects a weakening of the exact-next predicate that admits gaps.

## Amendments and acceptance programs

[A330–A333](../amendments.md#study-84--2026-11-23) record the compact issuance rule, authenticated gap resolution, grant fencing, and checkpoint binding.

- P159. Admit, close and compact a read, then recover using either selectable checkpoint. Refuse to admit the original nonce again even with free capacity and a different current cut.
- P160. Deliver nonce two while nonce one is unresolved. Refuse the overtaking attempt. Apply an authenticated abandonment for nonce one and then admit nonce two. An already admitted nonce cannot be abandoned.
- P161. Fence the writer, reissue a protected old read from its retained row, refuse a fresh predecessor admission, and admit nonce one under the new grant. At fixed-width exhaustion refuse fresh admission until a valid newer grant is available.

## Residue

The serialization policy is at the writer grant per stream.
The journal enforces durable one-use admission.
The front end still needs a contract for assigning a pending identity exactly once per grant, reconciling a lost response, and fencing issuance before proceeding after assignment-state loss.
This study assumes authenticated abandonment can reach the current grant owner under the same bounded control budget as other journal commands.
The proof of compatibility is for the abstract kernel; the complete lower-to-upper authority projection remains linked through the checked source decision.
The typed checkpoint associates the floor with the authenticated journal scope and read book.
Whole-control framing, the exact contemporary ranked cutoff and its named-prefix binding, the production authenticator and provider custody remain separate verification obligations.

## Reproduction

Use TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/84-read-invocation-floor/run.py
```
