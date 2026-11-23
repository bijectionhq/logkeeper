# Study 58 · Put the guard at the storage effect boundary

2026-11-23

## Verdict

An already provisioned slot can implement positive live admission with one durable conditional replacement.
The provider checks the exact location, non-reused allocation generation, and live permission in the operation that creates the payload.
Successful creation consumes the permission.
Authorized fencing makes the same guard refuse materialization.
Clearing the current payload leaves a compact vacant guard at the location.
Reuse advances the generation and preserves refusal of old requests.

Complete disposition additionally needs the stable absence of separately retained provider versions and staging work.
Those obligations keep their original charges until they settle.

## Bounded comparison

[StorageBoundary.tla](StorageBoundary.tla) models one preprovisioned slot, a new scoped permission per allocation, a reserve, and optional separately retained physical bytes.
The staging model permits a previously issued operation to materialize after the current payload has cleared.
Provider-side staging closure and purging an exact retained version are trusted actions in the model.

| Case | Distinct states | Result |
| --- | ---: | --- |
| Two allocations, atomic slot without staging | 19 | Five safety laws hold. |
| Two allocations with independent staging | 81 | The same laws hold. |
| Three potential allocations, two charge slots, staging and retained versions | 400 | The same laws hold with overlapping physical obligations. |

| Weakening | Shortest counterexample |
| --- | --- |
| Precheck once and issue a later raw write | Arm, precheck, fence, and materialize after the fence. Four transitions. |
| Let an absent key authorize recreation | Arm, fence, clear, and deliver a write to the empty location. Four transitions. |
| Reuse a content tag as the generation | Retire the first allocation, arm a second, and apply the first request to the second. Five transitions. |
| Forget the effective fence during recovery | Fence a live permit, restore the old guard, and let the old put land. Four transitions including arming. |
| Ignore multipart or staged bytes | Stage one possible effect, clear the current slot, and refund while the staged effect is still possible. Five transitions. |
| Ignore an old retained version | Write a payload, fence, clear its current representation, and refund while the old version remains. Five transitions. |

## General proofs

[StorageBoundary.lean](StorageBoundary.lean) checks ten theorems using standard axioms only.
A successful guarded write refines an actual atomic effect in the Study 40 provider model.
A fence excludes the exact old permission through arbitrary finite traces of clearing, restart, and later allocation.
An issued vacant or replaced generation has stable absence in the slot projection, and the new scope can materialize without reactivating the old scope.
The slot state carries only its current body and issuance watermark.

The full disposition predicate adds the previous stable absence contract for every separately tracked physical dependency.
A pending staged effect or present retained version defeats that predicate.
The Lean control removing the exact permission serial fails at the live-scope law.

## Documented provider behavior

- S3 `If-Match` compares the current object's ETag in the write. `If-None-Match: *` permits creation when the current key is absent. That condition cannot represent a terminally closed scope after deletion. [S3 conditional writes](https://docs.aws.amazon.com/AmazonS3/latest/userguide/conditional-writes.html)
- S3 documents ETags that depend on content, with metadata-only changes leaving them unchanged. A reusable content ETag alone supplies no incarnation freshness. A backend for the checked slot must enforce a non-repeating revision at the same compare-and-replace boundary. [S3 integrity and ETags](https://docs.aws.amazon.com/AmazonS3/latest/userguide/checking-object-integrity-upload.html)
- A simple deletion in a versioned S3 bucket can install a delete marker and leave the previous bytes retrievable via the version ID. Reclamation tracks exact versions and their dispositions. [S3 version deletion](https://docs.aws.amazon.com/AmazonS3/latest/userguide/DeletingObjectVersions.html)
- S3 multipart abort can race part uploads already underway. AWS says abort may have to be repeated and directs callers to verify the parts list is empty. Fencing final publication and settling original upload IDs are independent checks. [S3 AbortMultipartUpload](https://docs.aws.amazon.com/AmazonS3/latest/API/API_AbortMultipartUpload.html)

These are provider contract observations and a reference adapter design.
The tests exercise the modeled primitive and simulate its weakenings.
Provider-specific qualification remains open.

## Amendments

[A223–A226](../amendments.md#study-58--2026-11-23) require a durable same-effect check on the exact generation, positive admission through empty and reused representations, and separate stable absence of auxiliary bytes.

## Acceptance programs

- P83. Arm and fence a scope, clear it, return its charge, and fund the next scope at the same guard location. Its write succeeds in the six-transition witness at capacity one. An exact delayed old permission remains refused.
- P84. Issue a staged operation, clear the original slot, and materialize the staging bytes afterward. The old charge and a new charged payload coexist in the seven-transition witness.
- P85. Clear the current representation on a provider that retains an older version. Reuse the guard with a new charged allocation and preserve the original charge until exact version disposition. The six-transition witness covers the overlap.

## Residue

The slot proof starts with an already provisioned and funded guard.
Its atomic primitive compares the exact authenticated live revision and replaces the current body durably.
It abstracts body validation, provider authorization, real storage accounting, and whole-bank provisioning and destruction.
Bank closure must include proof that delayed first-create or administrative operations cannot revive a guard.
Auxiliary settlement assumes the full original inventory, stable namespace fences and exact provider observations.
Availability during provider outages and performance lie outside this finite model.

## Reproduction

The checked run used Python 3.13, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19 and Lean 4.35.0.
The runner saves exact commands, settings, and counterexamples under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/58-storage-effect-boundary/run.py
```
