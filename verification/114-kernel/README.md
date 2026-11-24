# Study 114 · Decision kernel and reducer refinement

The checked kernel has **eight operation families**. The five proposed
families cover append, custody, configuration, checkpoint lifecycle and
collection. Funding a window, fencing an object name and disposing of worker
custody require their own effects. The count is for typed families with
different state changes and authority. Each family can have several admission
paths. The study does not minimize the alphabet over arbitrary encodings.

A chosen decision advances position, decision time and the decision hash,
and expires receipts before dispatch. This envelope is common to all eight
families. A chosen replay or refusal can still change that envelope. A bad
decision coordinate stutters.

## Kernel and refinement

[DecisionKernel.lean](DecisionKernel.lean) defines the state, operation
payloads, admission, writes, step and invariant. It uses the existing value
types and concern relations. The kernel applies a typed operation with its
own success guards. Its checked concern transitions remain obligations for a
concrete implementer. The model starts at the ordered reducer, after
consensus choice.

[Refinement.lean](Refinement.lean) preserves every G1 state field, including
archived records, receipt identity, custody and opaque-reference evidence.
`effect_refines` checks each command and success outcome. `step_refines`
simulates each chosen decision in one step with the same receipt.
`trace_refines` lifts the result to arbitrary finite traces. A bad outer
coordinate gives equality of the abstract images and preserves the error.
The theorem starts from G1's Lean relation. The full shipped Rust dispatcher
and certificate and provider encodings remain separate refinement work.

The family names have precise scope. A **lease** operation may add or release
a durable hold, or issue a timed permission to serve from a protected basis.
The grant that fences appends and the roster that admits workers are ordered
configuration, even when no timed permission exists. **Reconfigure** covers
writer, roster, generation and cohort authority. The cohort command seals to
a named successor. Physical voter repair is outside the reducer.
**Checkpoint** includes preparation, selection and closing admission to an
old root. Erasure selection and generation rotation happen atomically in
`reconfigure.rotate`. **Collect** trims a certified prefix or settles a
closed, unpinned root with exact disposition evidence.

## Safety

| Guarantee | Kernel proof | Finite control |
| --- | --- | --- |
| Current writer and exact next append cut | `append_uses_current_writer` | `stale-writer` |
| Durable history prefix through trim and writer changes | `trace_preserves_history` | `rewrite-prefix` |
| Exact original mutation receipt and fresh read admission | `cached_mutation_returns_original`, `a_cached_barrier_refuses`, `a_refused_barrier_leaves_no_receipt`, `barrier_holds_exact_cut` | `new-receipt`, `replay-read`, `stale-cut` |
| Exact trim cut and credit, bounded by selected checkpoint and protected ranges | `trim_respects_protected_range`, `trim_drops_only_unreachable_record_references` | `live-roots-only` |
| Funded ordinary window and maintenance reserve | `step_preserves_budget` | `unchecked-budget` |
| Object withdrawal needs complete physical reference evidence and permanently fences the exact version | `fence_requires_complete_unreferenced_name`, `step_preserves_object_separation`, `trace_preserves_fence` | `sweep-name`, `ignore-opaque`, `late-reference` |
| Monotone lease end at the issued duration, with an open read basis | `lease_renewals_preserve_later_end`, `read_renewal_requires_open_basis` | `shorten-lease`, `renew-erased` |
| Disposal clears the exact owner's holds and lease. Timed disposal waits through the drift margin | `disposal_leaves_no_custody`, `expiry_disposal_cannot_race_a_bounded_worker` | `no-drift` |
| Rotation uses the exact incumbent, head and preparation | `rotation_requires_exact_preparation` | `wrong-rotation` |
| Erasure atomically installs the new checkpoint, raises the key generation, closes old recovery and preserves holds | `erasure_commit_is_atomic`, `erasure_closes_every_old_root` | `no-key-rotation` |
| Settlement needs a closed, unpinned root and disposition at the exact erasure floor | `settled_root_is_unreachable`, `settlement_requires_closed_root_and_exact_evidence` | `sweep-root`, `no-disposition` |

Certified disposal takes disposal evidence as an opaque input. The drift
proof applies to timed disposal. The source permits an absence attestation
for a serial in range with no issued custody. For erasure, the atomic
journal step proves state changes and admission exclusion. Recovery
readability also needs a certified clean recovery image and a new-generation
suffix, as stated by
`erased_recovery_readability_requires_image_evidence`. The key provider's
destruction deadline and the later physical removal of old ciphertext have
no representation in G1.

## What collection can derive

[Collection.lean](Collection.lean) defines the protection graph. The selected
checkpoint roots the replay suffix, each durable hold roots its exact
checkpoint and record interval, and an in-flight preparation roots its base
and registered objects. A root or record reaches its registered objects.
The physical registration graph additionally contains retained records and
old roots awaiting settlement. Completeness of opaque reference evidence is
a separate predicate.

- **Trim.** A record dropped by trim is unreachable in the protection graph.
  The proof also identifies exactly which reference rows can disappear. The
  ordered trim still uses the certified cut and derives the credit by folding
  the debits of the removed records. Arbitrary unreachable holes are not a
  valid prefix trim.
- **Retention.** Hold presence protects a range after the timed permission
  ends and even when it was never issued. A reachable TLC witness has an
  unleased hold and a newer selected checkpoint. A collector rooted only in
  live leases and that checkpoint trims the held record on its next step.
  A checkpoint preparation can also pin its base without a worker hold.
- **Closure and reclamation.** Closing a checkpoint writes its admission
  state. Settlement removes a closed root's registration with exact provider
  evidence and the current erasure floor. The unreachability theorem assumes
  the old root differs from the selected root. That identity relationship is
  not a conjunct of the G1 invariant. Certifying registration identity and
  the concrete provider effect remains open.
- **Withdrawal fence.** Physical unreachability and complete reference
  evidence are admission inputs. `fence_is_not_graph_determined` constructs
  two reachable images from the same valid state with identical reachability
  and different fences. The ordered fence remembers the version and stops
  a delayed reference from making the name live again.
- **Worker disposal.** Disposal changes the roots of the protection graph.
  It checks exact withdrawal and either certified disposition or ordered
  time plus drift. The timed control removes a hold at the journal's lease end while a worker
  behind by the allowed drift can still use it. Graph traversal after successful
  disposal can discover newly reclaimable resources.

[Footprint.lean](Footprint.lean) proves that every trace using only the five
original families preserves the window identity and fence map. Reachable
funding and fencing states lie outside that trace relation.
`disposal_success_requires_dispose` identifies the unique family that can
issue the successful absence receipt. An authenticated worker's release of
one hold has a different authority and receipt from atomic disposal of all
custody for a withdrawn enrollment.

## One removable command

`protect` can be lowered to one `protectRange` operation with the selected
checkpoint's starting LSN and the requested ending LSN. An ordered grant
installs an enrolled holder. Roster removal vacates that authority, so
`enrolled_holder_is_preserved` holds from any initial image with an enrolled
holder or vacant authority. Under that invariant, `protect_step_is_range`
replaces each chosen success, refusal or retry with the same receipt and
whole image. `deletion_preserves_reachable_states` proves both inclusions for
the reducer restricted to commands other than `protect`.

This is a reducer-level deletion. It uses G1's opaque fingerprint unchanged.
The wire adapter needs to preserve exact request identity and the narrower
writer and cut authentication for existing `Protect` callers. The
unconditional refinement retains the writer selector to cover arbitrary
G1 starting images.

## Command images

The expressed rows use `effect_refines` and `step_refines`. The essential
rows also use those theorems with the added family.

| Reducer command | Kernel image | Verdict and proof |
| --- | --- | --- |
| `Enroll` | `reconfigure.enroll` | Expressed. Fresh roster serial and incumbent vacancy |
| `Withdraw` | `reconfigure.withdraw` | Expressed. Removes eligibility and preserves surviving custody |
| `Grant` | `reconfigure.transfer` | Expressed. Installs successor authority and recovery hold |
| `PublishAndRotate` | `reconfigure.rotate` | Expressed. `erasure_commit_is_atomic` |
| `Append` | `append` | Expressed. `append_uses_current_writer` |
| `Barrier` | `lease.acquire(read)` | Expressed. `barrier_holds_exact_cut` |
| `PrepareCheckpoint` | `checkpoint.prepare` | Expressed. Registers candidate and references |
| `WithdrawObject` | `fence` | Essential. `original_five_cannot_install_a_fence` |
| `CloseCheckpoint` | `checkpoint.close` | Expressed. Closes admission before settlement |
| `SettleCheckpoint` | `collect.root` | Expressed. `settlement_requires_closed_root_and_exact_evidence` |
| `DisposeWorker` | `dispose(certified)` | Essential. `disposal_success_requires_dispose` |
| `Publish` | `checkpoint.select` | Expressed. Installs a prepared ordinary root |
| `FundWindow` | `fund` | Essential. `original_five_cannot_fund_a_successor` |
| `Protect` | `lease.acquire(writer)`, lowers to `lease.acquire(range)` | Accidental. `deletion_preserves_reachable_states` |
| `ProtectRange` | `lease.acquire(range)` | Expressed. Shares exact hold insertion |
| `ProtectCheckpoint` | `lease.acquire(checkpoint)` | Expressed. Checks named root and range |
| `ProtectRoot` | `lease.acquire(recoveryRoot)` | Expressed. Checks named recovery custody |
| `Vacate` | `reconfigure.vacate` | Expressed. Clears the incumbent under the rotation guard |
| `SealCohort` | `reconfigure.seal` | Expressed. Orders a named successor and closes admission |
| `Release` | `lease.release(exact)` | Expressed. Releases the specific worker hold |
| `ReleaseRead` | `lease.release(read)` | Expressed. Checks the read's hold provenance and allows a missing hold |
| `Lease` | `lease.renew(writer)` | Expressed. `lease_renewals_preserve_later_end` |
| `LeaseRead` | `lease.renew(read)` | Expressed. `read_renewal_requires_open_basis` |
| `DisposeExpired` | `dispose(expired)` | Essential. `expiry_disposal_cannot_race_a_bounded_worker` |
| `Trim` | `collect.prefix` | Expressed. `trimmed_records_are_unreachable` |

**Final size: eight operation families.** At the source-command level, 20
commands are expressed, four use the three essential added families, and one
is accidental under the stated initialization invariant.

## Owner decisions and evidence

D01 and D02 keep their specified behavior. The layer begins after choice
(D03), carries installed-journal semantics (D05), and makes no claim about
an exact historical feed (D04) or measured performance targets (D06). This
study proposes no owner-decision change. The local-read and pooled-WAL speed
hypotheses concern other layers.

Run `python3 verification/114-kernel/run.py` from the worktree root. It
builds G1 and the study on Lean 4.35.0, audits the proof dependencies, checks
three source mutations, and runs the TLC baseline, controls and reachability
witnesses. The optional `lean` and `tla` arguments run one part. See
[expected results](expected.md) for the TLC bounds and checked outcomes.
