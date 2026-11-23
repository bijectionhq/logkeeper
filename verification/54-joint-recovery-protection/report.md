# Study 54 · Certify an entire recoverable cut

2026-11-23

## Verdict

Certify recovery for the current voter family and exact ordered prefix.
For each allowed AZ loss, require a surviving majority in that family and exact readable coverage for every input of every checkpoint and suffix that a crash could select.
A recovery majority contains an exact installed-basis donor.
The recovering process can fetch the other inputs independently from their charged immutable allocations.

A visible replacement checkpoint can coexist with a still-selectable stable checkpoint.
Old-only attachments remain protected until the last selector that uses them is excluded, subject to independent borrow and result obligations.

## Bounded comparison

[JointProtection.tla](JointProtection.tla) starts with one installed history, a three-voter family, three AZs, and separately placed immutable inputs.
The old and new views have two common inputs and one distinct tail input each.
The checker explores one voter replacement, one checkpoint publication, independent selector sync, scoped certification, old attachment withdrawal, and one AZ failure.
Each staged voter holds the exact inherited basis.
Physical copies stand for already verified and funded placements.

| Design and topology | Distinct states | Result |
| --- | ---: | --- |
| Distributed inputs, successor has three distinct AZs | 960 | Every crash-selectable view remains readable, every surviving current recovery majority can obtain the exact installed basis, and certification is scoped to its current family. |
| Distributed inputs, candidate places two successor voters in one AZ | 480 | The same laws hold. The unsafe candidate cannot install. |
| Require one complete local image in every recovery majority | 128 | The safety laws hold from the same inherited state. The candidate excludes certification of the independently placed image. |

| Weakening | Shortest counterexample |
| --- | --- |
| Ignore tail attachments | Withdraw the only old tail input at the initial stable view in one transition. |
| Cover the visible selector only | Copy the new tail input, publish a replacement, and withdraw the old tail before selector sync. Three transitions. |
| Reuse an older family's scope | Stage two successor voters, observe the old family, install the successor, and certify using the old observation. Five transitions. |
| Ignore voter failure domains | Stage two copies, install a successor with two voters in one AZ, and lose that AZ. The journal loses its majority in four transitions, even though the immutable input coverage survives. |

## General proofs

[JointProtection.lean](JointProtection.lean) checks nine theorems using standard axioms only.
The recovery contract imports the canonical envelope opener, ranked membership recovery, checkpoint selector and evidence protection, and exact pointwise storage accounting.
It binds each selector's immutable envelope name, base position and authenticated components to the full exact installed command sequence.
It includes the envelope, each typed component and manifest descendant, and the exact attachments enumerated by the selected suffix.
This applies to arbitrary command sequences, dependency sets, physical allocations, and memberships in the model.

For a given failed AZ, the same certificate yields two results.
Any available current recovery majority intersects a quorum that certified installation of the exact basis.
Every required input has an exact reachable provider-backed allocation outside that AZ with a debit in its own pool.
The proof permits different allocations for different inputs and permits a single charged pack to contain multiple required inputs.

The publication theorem retains coverage of the stable selector when a fully checked new view becomes visible.
Choosing a durable selector preserves both the full protection proof and the independent evidence-retention obligations.
After arbitrarily many certified family changes, the selected split of the installed prefix includes previously chosen history and supplies the same input to deterministic replay.
The two Lean controls fail if the required set excludes tail attachments or the authority comparison accepts a stale scope.

## Amendments

[A207–A210](../amendments.md#study-54--2026-11-23) require the same exact recovery prefix and fault scope, preserve both live selector paths, include all required input roles, and bind certification to current authority.

## Acceptance programs

- P69. Stage and install the successor family, publish a covered new checkpoint, and then lose an AZ before selector sync. In the six-transition witness the exact installed basis and both selectable views remain available.
- P70. Refuse scoped certification using verifier state from the prior family. Refuse installation of the independent object placement with a successor voter family that would lose its majority in one AZ failure. Both weakenings yield the counterexamples above.
- P71. Install and certify a successor family, durably select a new view, withdraw the old-only attachment, and survive an AZ loss. TLC reaches this in ten transitions.
- P72. Certify an already installed basis whose required inputs are distributed across independent pools. TLC reaches this in two transitions. The complete-local-image policy excludes the same program at the same bound.

## Residue

The proof inputs include exact immutable name resolution, accurate voter and pool failure-domain identities, and complete typed dependency and suffix-attachment enumeration.
The counted voter list contains distinct durable identities.
The model assumes the voter availability predicate captures required local control and media access, and the provider exposes the exact bytes certified for each physical allocation.
The certification proof checks those premises together at a single authoritative decision.
Distributed read retries, physical provider implementations, and availability under additional AZ loss still need their own refinement or qualification.
The bounded comparison establishes no repair-time or quorum-election liveness.
Repeated evacuation and bounded unresolved custody remain open.

## Reproduction

The checked run used Python 3.13, Homebrew OpenJDK 21.0.13.0.3, TLC 2.19 and Lean 4.35.0.
The runner saves commands, traces, and diagnostics under `.results/`.

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 -u verification/54-joint-recovery-protection/run.py
```
