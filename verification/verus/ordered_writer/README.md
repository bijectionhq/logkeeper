# Ordered writer and logical history

The harness compiles the same [writer and history operations](../../../src/ordered/writer.rs)
called by [the ordered reducer](../../../src/ordered.rs). It verifies exact
authorization, LSN and epoch arithmetic including overflow refusal, authority
installation and withdrawal, the append write to the actual deque and cut,
and prefix removal from that deque. The contracts erase in ordinary builds.

## Lean correspondence

| Verus definition or law | Lean reference in [Logkeeper.Kernel.Ordered](../../lean/Logkeeper/OrderedWriter.lean) |
| --- | --- |
| `authorize_writer` | `authorize_writer` on the authenticated worker and its full current grant. |
| `append_next_lsn` | `append_next_lsn` at the maximum representable next LSN, with `append_at_next_lsn`. |
| `next_writer_epoch` | `next_writer_epoch` at the maximum representable epoch. The installed successor meets the strict epoch condition of `Kernel.Step.fenceWriter`. |
| `withdraw_grant`, `abstract_authority` | `withdraw_grant` and `abstract_authority`. A vacancy keeps the last epoch and key generation while removing the active grant. |
| `abstract_history`, `abstract_state` | `abstract_history` and `abstract_state` of the writer and history projection. |
| `applied_append_extends_history`, `trim_keeps_the_logical_history` | The append case of `image_step_refines_kernel` and `trim_keeps_the_logical_history`. |

Fix the authenticated journal placement. Map the Rust group UUID and placement
generation to `Kernel.Placement`. Map each current grant to a `Kernel.Writer`
with the grant epoch and an injective natural-number encoding of the enrollment
UUID, enrollment serial, and key generation in `Writer.holder`. Deployment and
incarnation are checked by the surrounding request placement check. When the
grant is absent, the trace supplies the previous grant at the stored epoch.
An initial vacancy uses an inactive epoch-zero writer.

Map each retained record to a `Kernel.Entry` with its grant epoch and exact
record identity as the payload. Prepend the logical prefix of length
`floor.next_lsn` from the prior trace to the retained records. The concrete
image keeps the floor cut and digest. The trace supplies the archived entries.
The head invariant equates `head.next_lsn` to the length of the concatenation.
The Lean model uses both abstract count ceilings at the maximum LSN. Production
byte-budget, custody, and reference guards remain additional conditions.
`history_is_irrevocable` and `superseded_writer_cannot_append_again` give the
trace-level history and fencing results.

## Reducer correspondence

| Applied decision family | Writer and history projection |
| --- | --- |
| `Append` | Exact worker and grant comparison precedes the checked next LSN and other admission checks. The successful deque write appends the record and advances the same head one place. This is `Kernel.Step.append`. |
| `Grant`, `PublishAndRotate` | Both install the checked next epoch after the recovery hold is admitted. The same placement is preserved. These are `Kernel.Step.fenceWriter`. |
| `Withdraw`, `Enroll` | Matching current enrollment withdrawal or replacement clears the active grant. This is `Kernel.Step.withdrawWriter`. Changes to other enrollments leave the projection unchanged. |
| `Vacate` | The exact current grant is cleared. This is `Kernel.Step.withdrawWriter`. |
| `Trim` | The admitted trim range moves an exact prefix from the retained deque into the logical archive. The projected history is unchanged. |
| `Barrier`, `Lease`, `Protect`, `ProtectRange`, `ProtectRoot`, `Release`, `ReleaseRead`, `PrepareCheckpoint`, `Publish`, `CloseCheckpoint`, `SettleCheckpoint`, `DisposeWorker`, `DisposeExpired`, `WithdrawObject`, `FundWindow`, `SealCohort` | The projected authority and history are unchanged. The projection omits checkpoint and hold state, lease and seal policy, and funding. |
| Unapplied, refused, or replayed decisions | The projected authority and history are unchanged. |

This table records a source inspection of the command dispatcher. The Verus
entry point covers the imported operations and their composition laws. The
complete dispatcher proof, its grant and LSN argument wiring, and establishment
of the trace witnesses by compact-image decoding remain open. Trim's fold
callback is used for accounting. The verified property of the deque operation
is removal of the exact prefix.

The runner declares and checks controls for ignoring the grant epoch, skipping
an LSN, reusing an epoch, failing to withdraw or vacate, prepending an append,
and trimming from the tail. The shared
[correspondence check](../../lean/run_ordered_correspondence.py) compares Lean
evaluation with Verus specs on boundary cases.
