# Study 63 · Isolate competing vote bytes and charge their overlap

2026-11-23

## Verdict

Different proposals can compete for one logical position.
Use a funded physical version for each staged set of bytes that can coexist, and check its generation when materializing it.
Persist the exact bytes and their locator before durably installing the vote that selects them.
The accepted binding can name the staged bytes directly.
Older copies remain charged while a selectable recovery path or another holder still needs them.
Replacement requires headroom for the physical versions that coexist.

## Bounded comparison

[StagedVotes.tla](StagedVotes.tla) models one voter's local record at a shared logical position, with a separate vote binding and at most one independent older pin.
Attempts have non-reused generations, alternate between two command values, and use one unit per physical allocation.
The modeled reclamation action combines effective closure, exact absence, and return of the original charge.
Reopen consumes the durable vote binding, so the checker tests its recoverability in every durable state.

| Case | Distinct states | Result |
| --- | ---: | --- |
| Two slots, two attempts | 99 | Every accepted and pinned version is exact, every live stage is paid, materialized bytes match their current scope, and delayed writes cannot use an old generation. |
| Three slots, three attempts, with an older pin | 3,388 | All five invariants hold. |
| One slot, two attempts | 13 | The model excludes replacing an already accepted copy while it remains required. |
| Two slots, three attempts, with an older pin | 463 | The model excludes installing a third vote after the second while the first still has its independent pin. |

| Weakening | Shortest counterexample |
| --- | --- |
| Stage by logical offset | Accept the first record, then sync competing bytes for the same logical position. The earlier accepted locator reads the competing record after six transitions. |
| Vote before bytes are durable | Acquire a slot, persist its locator, and vote before its bytes are recoverable. Three transitions. |
| Vote before the locator is durable | Acquire a slot, persist its bytes, and vote before the recovery address is durable. Three transitions. |
| Forget the staging debit | Grant a slot and return its charge while the original stage is still live. Two transitions. |
| Reuse a physical address without its generation | Grant a slot, reclaim it, grant the same address at a new generation, and deliver the old write. The new allocation contains old bytes after four transitions. |
| Drop an independent pin on newer acceptance | Accept and pin the original version, accept a replacement, and reclaim the older pinned copy. Ten transitions. |

## General proofs

[StagedVotes.lean](StagedVotes.lean) checks nine theorems with standard axioms only.
The staged voter advances the existing durable acceptor and accounts for its allocations in the exact pool reducer.
It keeps the accepted binding exact, every current or staged copy charged, and every live pin recoverable through arbitrary finite traces.
A pinned version retains the same bytes through later votes.
A discarded version at or below the issuance watermark cannot return through a delayed effect.

For any set of simultaneously retained exact versions, the sum of their individual physical debits and ordinary occupancy fits each pool's limit.
Two different exact vote values cannot have the same physical version in this model.
The proof with multiple replicas uses the earlier ranked prefix theorem under authenticated correspondence between the observed votes and durable acceptors.
Each current acceptor recovers exactly the vote named in its durable state, and any two chosen prefixes agree.
The two Lean negative controls remove byte and locator persistence independently and fail the respective proof obligations.

## Amendments

[A244–A248](../amendments.md#study-63--2026-11-23) separate staging identity from stream offset, require both durability barriers before acceptance, and retain charges through live storage dependencies and scoped disposition.

## Acceptance programs

- P98. Keep an accepted record recoverable while preparing a divergent candidate for the same logical position, then install the ranked replacement from its own durable physical version. The two-slot witness takes eight transitions.
- P99. Keep an independent pin on the first accepted version, accept a second, and stage and accept a third while preserving the first. The three-slot witness takes thirteen transitions. Two slots exclude the same sequence under the modeled retention rules.
- P100. Grant a physical address, reclaim it, and accept a replacement at the same address under a fresh generation. TLC verifies that the old write cannot execute, and Lean proves permanent exclusion of the discarded scope.

## Residue

The model gives separate physical debits to candidate copies, while real packing can share any unchanged immutable frames.
The three-slot witness concerns three independently live versions at one logical position.
Measured capacity follows the exact physical footprints of those versions, which can span only their changed ranges.
Byte sync and locator sync are explicit media premises, and installation is an atomic durable binding.
The adapter still has to refine write-once effects, complete pin registration, ranked recovery of the funded window book, and exact canonical frame evidence for the append reducer.
An already funded workspace can supply a local physical range. The combined debit proof still has to track its reclassification when that same range becomes resident.
The proof assumes authentic quorum assembly within the checked voter protocol, while cross-membership recovery still uses the other studies' contracts.
The full prepared-move vector still has to fund these exact versions in the same regional ledger.

## Reproduction

The checked run used Python 3.13.15, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19, and Lean 4.35.0.
The runner records commands, configurations, theorem checks, and failing traces below `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/63-staged-votes/run.py
```
