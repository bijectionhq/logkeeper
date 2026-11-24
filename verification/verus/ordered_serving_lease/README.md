# Ordered serving leases and disposal (L8)

The harness imports the shipped journal-time, lease, disposal and page
operations from `src/ordered/lease.rs` and PL1's authority, writer check and hold
insertion from `src/ordered/writer.rs`. The reducer calls these operations in
`State::apply`, `State::decide`, `State::admit_hold` and
`State::withdrawn_hold_owners`.

| Shipped operation | Law | Lean reference |
| --- | --- | --- |
| `advance_decision` | `decision_time_is_monotone` | `DisposalLease.decision_time` |
| `issue`, `writer::authorize` | `lease_requires_current_enrolled_grant` | `DisposalLease.lease_end`, `Logkeeper.Kernel.Ordered.authorize_writer` |
| `check_disposal`, `disposal_time` | `disposal_requires_withdrawal_and_drift` | `DisposalLease.withdrawn`, `may_dispose`, `MayDispose` and `Admits` |
| `withdrawn_page`, `offer_owner`, `eligible_for_page` | `withdrawn_owner_page_is_exact_and_bounded` | `DisposalLease.eligible_owner`, `qualifying_owners` and `owner_page` |
| `writer::insert_hold`, `Authority::install` | `grant_change_preserves_holds` | `DisposalLease.grant_holds` and `Logkeeper.Kernel.Ordered.ImageStep.fence` |

[Study 113](../../113-worker-disposal/DisposalLease.lean) supplies
`Admits`, `MayDispose` and the bounded-clock theorem. The [package
model](../../lean/Logkeeper/DisposalLease.lean) adds the ordered operations and
uses PL1's exact writer identity. The Rust clock and serials project to Lean
naturals. The arithmetic bound is `u64::MAX`. An overflowing lease or
eligibility time refuses the decision. An absent retained lease has eligibility
time zero. Lease renewal retains the maximum end in the lease map.
The issuance law covers `Command::Lease` for the current grant.
The [ordered lease reducer area](../ordered_lease_reducer/README.md) covers
`Command::LeaseRead` authorization, lease updates and retention across the
reducer's lease and hold operations.

The owner projection takes each real held entry's exact enrollment and its
worker UUID. The roster is keyed by worker UUID and the query compares the
entire enrollment, including the serial. The page contains the least distinct
eligible owners strictly after the cursor, in enrollment order. Every omitted
eligible owner follows every returned owner and requires a full page. The
public coordinator caps the request at 64 before calling the proved scan.
The scan stores at most the effective limit and visits all holds. The Rust
proof uses the standard Verus contracts for ordered maps, iteration and
comparison. The Lean law permits arbitrary finite hold collections.

The grant path admits a recovery hold at a fresh request ID before
installing authority. An existing hold keeps its exact key and value in the
map. Enrollment replacement, withdrawal and vacancy use authority operations
that touch the grant and leave holds in place. Mutation retries can return the
original applied lease or disposal receipt.

The serial high-water check and the current roster determine the shipped meaning
of `withdrawn`. A fabricated identifier with an in-range serial, no current
roster match and no lease can receive a successful no-op disposal. The
`absent_unleased_identity_is_disposable` law records this behavior. A successful
disposal attests only that no hold or lease remains for the exact enrollment.
Historical enrollment authenticity across snapshot recovery, the complete
reducer refinement and clock and per-read qualification remain open.

With the pinned F0 runner, run
`python3 verification/verus/run.py --verus /path/to/shared/tools/verus ordered_serving_lease`.
Run `python3 verification/lean/run_ordered_lease_rotation.py` for the
reference theorems and controls, and `run_ordered_correspondence.py` in the
same directory for sampled Lean and Verus agreement.

The [mechanical link inventory](../../link/inventory.md) lists the checked
projections and the remaining Lean correspondence for this area.
