# Ordered reducer projections

The I/O-free [reducer](../../../src/ordered.rs) runs at each chosen position.
This area imports its shipped writer and funding updates, request admission
and receipt scheduling, and paid fence installation. The
proofs use the actual deque and map operations through their vstd views.
The other ordered areas check the shared writer, budget, receipt, cohort, and
object-withdrawal operations used by these functions. The shipped read lease
and disposal transitions use [ordered lease reducer](../ordered_lease_reducer/README.md).

Run from the checkout root with the pinned Verus launcher.

```sh
python3 verification/verus/run.py --verus /path/to/verus ordered_reducer
python3 verification/lean/run_reducer_refinement.py
```

## Lean correspondence

| Shipped function or law | Reference in [Logkeeper.Reducer](../../lean/Logkeeper/Reducer.lean) |
| --- | --- |
| `finish_append`, `a_paid_append_advances_history_and_charges_one_lane` | `commitAppend` and the writer and budget projections of `appendEffect`. The real deque projects to retained records. Each record's logical identity comprises its exact record and grant. An externally supplied archived sequence precedes the deque in `Kernel.Ordered.abstract_history`. The proof takes the supplied cut and its next LSN as inputs and checks that the committed head uses it. Its digest and the computed charge's attachment to the record remain caller obligations. |
| `fund_window` | `fundWindow` and the funding case of `effect`. The supplied allocation witness and both serials select the successor. The actual window field is replaced and spend resets after an ordinary-capacity check. Custodian authorization and projection of Rust `Window` fields remain caller obligations. |
| `vacate` | `canVacate`, `vacate`, and `ErasureCommit.Step.vacate`. The optional exact grant compares its enrollment, epoch, and generation through the tuple passed by the dispatcher. Clearing the actual authority preserves its stored epoch and generation. The last writer used to interpret vacancy is trace evidence. |
| `admit_request` | `RequestStep.cached` and `RequestStep.late`, through `cachedReceipt` and `lateRefusal`. The map is the retry book after expiry. The key and fingerprint are supplied by the caller. `Ok(Some(original))` reuses the original receipt, `Ok(None)` permits dispatch, and the caller wraps an error in a receipt for the current position. |
| `finish_request` | `recordReceipt` through `Protocol.Ordered.record_after_apply`. The same applied receipt enters the retry book and its expiry schedule. A refused barrier leaves both maps untouched. `RequestStep.applied` supplies the prior book after command effects such as releasing expired provenance. |
| `commit_withdrawal` | `commitWithdrawal` and `ObjectWithdrawal.Step.withdraw`. The prior decision supplies a fresh name and the paid control limit. The map inserts exactly the supplied fence, which the caller builds with its provider version and chosen coordinates. The reference model projects that fence to its version. |

## Evidence boundary

The Lean transition covers all 25 command variants and distinguishes an
unchosen call, an early refusal, cached retry, a late refusal, and a refusal
or success after dispatch. `Step` projects to the existing writer-image,
Kernel writer/history, erasure-authority, budget, and object-withdrawal
relations. The hold/receipt and lease-bound invariants are preserved in the
composed model. The witness is one chosen funding step with a 1,024-position
model limit, a 1,024-byte ordinary capacity, and a 128-byte reserve. The
preservation and projection theorems quantify over arbitrary states and finite
traces.

The Lean specification abstracts opaque values, models dispatched errors
nondeterministically, and requires `Applied` witnesses for the synchronized
concern effects. Its `ReducerInv` covers semantic history, funding,
generation, reference separation, hold receipts, and lease bounds. Successful `DisposeExpired` removes the owner’s lease and holds. An identity
within the issuance bounds with neither kind of custody can succeed as a
no-op, without certifying historical enrollment. The collection size and ordering checks in `CompactImage.reducerInvariant`,
certificate authentication, and exact correspondence of opaque reference
completeness to concrete rows remain separate obligations.

The Verus area discharges the projections in the table. The full
`State::apply` dispatcher and abstraction from its complete state remain
open. They must connect selected commands, passed arguments, hashing,
position and time, expiry traversal, all changed and framed fields, and the
receipt to a single `Reducer.spec_step`. Caller wiring and establishment of
`ReducerInv` from initialization and recovered images remain open.

The [mechanical link inventory](../../link/inventory.md) records the
remaining equivalence obligations for these local laws.
