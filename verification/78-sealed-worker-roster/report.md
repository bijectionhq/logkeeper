# Study 78 · Bind the worker roster to the sealed cut

2026-11-23

## Verdict

The ordered transfer must carry the exact worker roster and its enrollment watermark.
Two states can have the same retained log and data frontier yet authorize different workers.
A destination can also have the right set of live workers and still reuse a withdrawn enrollment if it recovers an earlier watermark.

The installed group includes the canonical roster bytes in the chosen seal alongside the realized funding and storage record.
The target checks durable import evidence for that same sealed body and installs the decoded roster with its existing funded window.
It uses the retained evidence locally.
The named checkpoint loader also decodes and validates the roster section with the same codec.

## Bounded comparison

[RosterTransfer.tla](RosterTransfer.tla) starts with one candidate enrolled at serial one.
Withdrawal changes the ordered worker state while leaving the data frontier fixed.
Three possible mount offers all cover the exact data frontier.
One is the sealed roster, one is from before withdrawal, and one has the same live rows as the seal but an earlier watermark.
The source route stays unavailable for activation.
The model allows one re-enrollment and one replay of the original nomination.

TLC checked six distinct states in the reference.
The checks cover exact mount, preservation or extension of the sealed roster after activation, stale nomination refusal, and eventual offline activation under weak fairness for withdrawal, seal, exact mount, and activation.

| Control | Shortest trace or temporal result |
| --- | --- |
| Validate only the data cut | Withdraw, seal, and mount a stale roster in three transitions. |
| Validate only the data cut, observe actual stale grant | Mount the pre-withdrawal roster, activate, and issue the old grant in five transitions from the start. |
| Check live rows and omit the watermark | Mount the older empty roster after withdrawal and seal. Three transitions. |
| Omit the watermark, observe actual stale grant | Mount the older empty roster, activate, re-enroll the worker with reused serial one, and issue the old grant in six transitions from the start. |
| Use a local eligibility cache after exact mount | Activate with the pre-withdrawal roster in four transitions. |
| Require a source route after exact mount | The mounted target can stutter forever after source-route loss. |

The schedules are small by design.
The model holds resolved bytes, funding and source seal validity fixed and isolates the worker authorization component.

## General proofs

[SealedWorkers.lean](SealedWorkers.lean) checks nine theorems with standard axioms only over the codec and the actual chosen source and recovery reducers.

- A valid worker edit keeps the roster encodable under fixed limits. Enrollment adds one newer unique row and refuses an unrepresentable worker identity. Withdrawal preserves the relative order of remaining rows and spends no enrollment serial.
- The canonical roster format has one domain byte, one fixed-width unsigned watermark and two words per live worker. Each word decodes back to its exact bytes. Valid rosters round-trip. The decoder refuses trailing partial words or rows, duplicate worker identities, unordered or invalid serials, and over-capacity rosters.
- The integrated source refuses a body whose roster disagrees with the current source even if its vector matches. An opened seal uses the exact retained move slot and decodes its roster. Target certification must cover that same body. Successful activation installs the decoded roster and funded window, and refuses an authenticated nomination for an absent or superseded enrollment.
- A named control image decodes the same roster that its canonical bytes identify. Two certified bases with their exact suffixes recover one complete state, including the same canonical roster bytes.

For a word width (w) and a configured maximum of (n) live workers, one section occupies at most (1 + (1 + 2n)w) bytes.
A control image with up to (s) retained seal slots reserves at most (s+1) such sections, including its current roster.
Account for both selectable images and any separately staged or retained source frames in their existing budgets.
The wire width and limits stay fixed for the current stream format.
The existing pool inventory and the roster use the same proved fixed-width word codec.

## Amendments and acceptance

[A309–A311](../amendments.md#study-78--2026-11-23) bind worker eligibility to the exact source cut, make activation install its retained bytes locally, and give the roster section a canonical bounded format.

- P146. Recover either certified base through its exact suffix. Both recover the same ordered roster and watermark.
- P147. Withdraw a candidate and seal without another append. Refuse a mount that supplies pre-withdrawal eligibility at the exact data frontier. Install the exact certified source body with the source route down and refuse the old nomination.
- P148. Refuse a roster with the correct live rows and a rolled-back watermark. After correct install, issue a fresh serial when the worker re-enrolls and refuse a nomination for its previous enrollment.

The numbered programs are covered by the stated finite histories and the general decoder, ordered-source, activation, and replay laws under their premises.
The proofs name exact chosen frames, exact certified base images, and target import and nomination authentication as premises.

## Residue

Provider manifests, quorum signatures and the actual target import attestation must bind all bytes of the same seal and control image.
The complete frame and combined control-image encodings still need concrete transport and durability refinement.
The same-placement RTDB outage program P142 and end-to-end provider qualification remain open.

## Reproduction

Run with TLC 2.19, Java 21, Lean 4.35.0, and Python 3.13.
The runner verifies the TLC jar and Lean version and runs the six negative checks before the reference baseline.
It records the commands, configurations and raw logs in .results/.

```sh
export JAVA_BIN=/path/to/jdk/bin/java
export LEAN_BIN=/path/to/elan/bin/lean
python3 -u verification/78-sealed-worker-roster/run.py
```
