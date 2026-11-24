# Ordered read leases and reducer retention (PL8b)

The harness imports the production functions used by the ordered reducer.
`LeaseRead` uses the exact live hold, an available replay interval, and a
checkpoint that remains open under the erasure floor. The principal and the
worker's roster slot must both name the hold's exact enrollment. This path
works with a writer present and during vacancy. An empty interval remains
usable beyond the replay floor. The receipt returns the end of the new lease.
The durable lease map keeps the greatest issued end for that enrollment.

| Shipped operation | Verus law | Lean reference in `DisposalLease` |
| --- | --- | --- |
| `lease_reducer::issue_read`, `held_indices`, `replay_bounds::retained_indices` | `read_lease_requires_exact_protected_basis`, `vacancy_never_substitutes_for_enrollment` | `read_lease_end`, `interval_available` |
| `lease_reducer::issue_read`, `lease::issue` | `read_lease_retains_greatest_end`, `writer_lease_does_not_regress_or_change_other_ends` | `retained_end`, `OwnerStep.leaseRead`, `OwnerStep.lease`, `lease_end` |
| `lease_reducer::release_hold` | `release_read_keeps_end_if_backed` | `OwnerImage.prune`, `OwnerStep.release` |
| `lease_reducer::dispose_expired`, `dispose_owner`, `dispose_holds` | `expiry_disposal_clears_owner` | `may_dispose`, `expiry_disposal_clears_owner`, `OwnerStep.dispose`, `unissued_disposal_is_noop` |
| `lease_reducer::update_roster`, `prune_end` | `withdrawal_preserves_pending_owners` | `OwnerStep.enroll`, `OwnerStep.withdraw`, `OwnerImage.backed` |
| `writer::insert_hold`, `Authority::install`, `rotation::publish_selection` | `rotation_adds_recovery_without_dropping_existing_holds` | `grant_holds`, `OwnerStep.rotate` and `ErasureCommit.erasure_floor` |
| `rotation::check_writer_open`, `Authority::vacate` | `pending_erasure_blocks_writer_changes`, `vacancy_preserves_epoch_and_generation` | `writer_open`, `OwnerStep.vacate` and `ErasureCommit.generation_survives_vacancy` |
| `CheckpointAccess::is_open`, `rotation::check_settlement_fence` | `old_root_cannot_renew`, `settlement_must_match_erasure_floor` | `checkpoint_open`, `settlement_fence` |
| `lease::withdrawn_page`, `lease::disposal_time` | `withdrawn_owner_page_is_exact_and_bounded` in [ordered serving lease](../ordered_serving_lease/README.md) | `qualifying_owners`, `owner_page`, `disposal_time` |

## Reducer projection

Project each exact enrollment independently. Roster membership is equality
with the entry under the enrollment's worker UUID. Count holds by their exact
owner in the request-keyed hold map, and take the recorded end from the
enrollment-keyed lease map. For the Lean trace, interpret issuance and greatest
end from the chosen prefix. The initial reducer has empty maps. The trace
theorem `reducer_establishes` proves preservation for every projected step
and any finite number of decisions. A live hold's issued owner is either
enrolled or withdrawn and pending disposal. While an enrollment has roster
membership or owns a hold, its recorded end equals its greatest issued end.

The Rust state dispatch supplies the following projections.

- `Enroll` allocates a fresh serial. Replacement removes the prior
  enrollment's roster backing. `Withdraw` does the same without a replacement.
  Both retain the prior end when a hold remains. A superseded or withdrawn
  current writer loses its grant.
- `Grant`, `Barrier`, the protect commands and `PublishAndRotate` add a
  fresh hold. The owner comes from the exact roster entry, the current grant,
  or the exact retained recovery hold in `ProtectRoot`. The current grant and
  its owner stay tied to an exact roster entry from installation to vacancy.
  The shipped rotation command is `PublishAndRotate`.
- `Lease` and `LeaseRead` update one end and leave the holds unchanged.
  `Release` and `ReleaseRead` remove one hold. `DisposeWorker` and
  `DisposeExpired` remove every hold for the exact enrollment and clean up
  its retired receipts. A refused request, a retained receipt
  retry, or any other command leaves these books unchanged.
- `Vacate` changes writer authority alone. A pending erasure preparation
  blocks a fresh append, grant or vacancy. Read leases on an open checkpoint
  can still be issued during preparation. After rotation, the former
  checkpoint can remain held, and renewal for that basis is closed.
  Settlement requires the current erasure floor and an exact closed
  checkpoint with no hold or preparation using it.

The page scans the current hold map and subtracts exact roster matches,
then selects the first distinct owners strictly after the cursor. It
includes owners waiting for their lease and drift to elapse and attaches
each owner's earliest eligible time. The disposal guard uses the same
lease-end arithmetic. Successful expiry disposal certifies absence of
holds and a lease for the exact identity. An unissued identity with an
in-range serial can succeed as a no-op.

Verus checks the concrete map operations and decision functions through the
standard ordered-map, comparison and iterator contracts. The command dispatch,
construction of projected arguments and snapshot recovery are covered by
source inspection and native scenarios. The historical issuance and greatest
end statements apply to chosen traces and exact encodings of those traces.
A full Rust reducer and compact-image refinement, clock qualification and
physical key revocation remain open obligations.

Run the area with `verification/verus/run.py ordered_lease_reducer` and the
pinned launcher. The Lean package's `run_ordered_lease_rotation.py` audits
theorems and negative controls. `run_ordered_correspondence.py` checks the
same boundary cases in Lean and the Verus specifications.
