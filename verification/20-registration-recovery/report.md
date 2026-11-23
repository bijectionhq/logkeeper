# Study 20 report · Interrupted custody registration and bounded retry state

2026-11-22

## Verdict

Record each immutable acquisition intent before the first send.
Recovery can repeat the exact request to resolve a lost receipt or durably close the attempt and release every planned interest.
Release works even without learning whether the acquisition ran.
Retain the plan until exact closure settles.
An advanced receiver floor can still cover a serial holding a physical grant.

A per-channel receiver floor fences new acquisitions at older serials.
Install a floor only when every covered planned interest has irreversibly closed or has a matching durable grant receipt.
Keep existing grants at and below the floor, and accept their exact retries and releases.
Closed-reference markers below the installed floor can then be discarded.

The issuer replenishes its finite serial window only from an acknowledgment of the installed receiver floor.
Existing physical pins have their own budget, including pins left by interrupted publications.
Release can run when that budget is full.

## TLC comparison

The seven baseline safety laws and the conditional release-progress property hold at both bounds.
Each bound sets the maximum physical pin count to the serial window size while accounting for the two independently.

| Bound | Receipt-backed cutoff | Terminal-only cutoff |
| --- | ---: | ---: |
| Two serials, window one | 2,260 states | 1,636 states |
| Three serials, window two | 112,436 states | 59,556 states |

The receipt-backed candidate admits a third serial while the first remains published, in ten transitions.
The terminal-only design cannot run that program at the larger bound.
Weakly fair release finishes after cancellation when the issuer and link become stably available.
Permanent provider inaccessibility and coupling release to spare foreground pin capacity each defeat that progress claim.

| Amendment | Mutation | Shortest safety counterexample |
| --- | --- | --- |
| A62 | `forget_intent` | Allocate, send and install a grant. Crash before its reply is recorded and lose the durable plan. Four transitions. |
| A62 | `drop_closed_plan_at_floor` | Acquire, close, and acknowledge the installed floor before exact release. The issuer forgets the plan while the physical grant is still held. Seven transitions. |
| A62 | `publish_after_close` | Prepare and observe a matching grant, close the intent, then allow publication with that old grant. Six transitions. |
| A63 | `promise_without_receipt` | Prepare, propose a cutoff on the strength of the intent alone, and install it before the acquisition. Three transitions. |
| A63 | `ignore_floor` | Queue an acquisition, close and release it, then compact the exact marker and admit the delayed message. Seven transitions. |
| A64 | `forget_held` | Publish under a live grant, then discard that grant when installing a floor through its serial. Seven transitions. |
| A65 | `early_credit` | Treat an offered cutoff as an installed one. The issuer acknowledges unearned capacity after four transitions. |
| A65 | `unbounded_window` | Prepare three requests with credit for only two. Three transitions. |
| A66 | `unmetered_pins` | Advance and acknowledge the floor while keeping the first grant, then acquire a second pinned batch with a pin limit of one. Ten transitions. |

The bounded model records a live exact retry below the floor in eight transitions and refuses a delayed acquisition after marker compaction in seven.
It recovers a crash after the grant but before the issuer observes its receipt, then releases and compacts the exact slot in nine transitions.
Baseline runs omit fresh retries after an issuer has observed the grant.
They retain delayed requests already in flight.
The acceptance configurations also enable fresh exact retries and the observations used to identify their traces.

## General proofs

Fifteen [Lean theorems](RegistrationRecovery.lean) use only standard axioms.
They prove that an exact retry reuses its installed binding and a changed request is refused.
For an absent reference, the floor and every still-retained terminal marker prevent a fresh admission.
The abstract closed reference survives compaction and arbitrary finite delayed traces.

A delayed cutoff certificate survives issuer progress when allocated plans are immutable and terminal decisions and acknowledged grants preserve their meaning.
Installing that floor preserves every live grant, including a still-preparing root's acknowledged interest.
The terminal-only counterpart cannot advance through a live root.
The canceled-plan theorem constructs independent exact releases at every planned custodian without requiring acquisition acknowledgments.
Those actions can be replayed when the corresponding custodians are accessible.

The issue bound and the injection of all uncompacted marker serials into the configured finite window hold for arbitrary natural serials and window sizes.
This arithmetic bounds terminal markers, independently of the physical footprint of active grants.
Removing the receiver floor, authenticated close on release, or installed-credit premise causes the corresponding Lean control to fail.

## Residue

The proofs assume a durable, authentic issuance history, exact scope binding, and durable receiver acknowledgments.
The data structures and network protocol must refine that boundary across changes of owner, membership and provider availability.
The model reports per-channel bounds.
Issuer preparation records and unsettled releases need their own accounting and reclamation proof.
[Study 21](../21-custody-channel-lifecycle/report.md) checks a configured active-channel bound and safe retirement and rollover at a durable custodian.
A live channel retains its floor until an exact handle fence makes the entire channel ineligible for new admission.
Proof of actual RTDB graph enumeration, rehome copy equivalence, and provider disposition remains separate.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean python3 verification/20-registration-recovery/run.py
```
