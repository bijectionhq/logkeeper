# Expected results

## Lean 4.35.0

The pinned G1 reducer builds. [Audit.lean](Audit.lean) reports 39 theorems.
Their axiom dependencies are subsets of `propext`, `Classical.choice` and
`Quot.sound`.

| Mutated rule | Expected failing proof |
| --- | --- |
| Map `FundWindow` to a fence | `effect_refines` |
| Shift the selected start LSN in the `Protect` lowering | `protect_effect_as_range` |
| Treat funding as one of the five original families | `original_effect_keeps_window_and_fences` |

The Lean witnesses reach a funded successor directly and via the G1
refinement. A separate fork reaches successful and refused fence decisions
from the same valid initial image with identical graph reachability.
Their fences differ. The unrestricted kernel can reach a new funding
window or fence, and the original five-family trace relation excludes those
two paths.

## TLC 1.7.4 distribution

`KernelCuts` is a finite scenario model of the ordered effects. It has one
tenant, one starting writer and enrollment, at most two records and one
checkpoint replacement. The initial root has a physical registration. The
model permits one held interval, one worker lease end, one object name to
fence and one fence version. Records use names 0 through 2, with 0
representing opaque references. Each record consumes one unit of ordinary
capacity and the capacity is 2. The ordered clock ranges from 0 through 4,
the lease duration is 2, and the drift margin is 1. Each path has at most
eight chosen steps. The model abstracts authentication, exact digests,
maintenance accounting, recovery certificates, quorum choice and provider
I/O. It tests safety under interleaving within these bounds.

The baseline passes every safety invariant in the table. It generates
149,708 states, visits 56,102 distinct states, leaves no queued states and
reaches search depth 9 including the initial state.

| Mutated rule | Expected violated invariant | Steps from initial state |
| --- | --- | ---: |
| Accept a superseded or unissued writer epoch | `WriterSafe` | 1 |
| Overwrite the first committed record on a later append | `HistoryStable` | 3 |
| Reissue a mutation receipt at the new decision position | `ReceiptExact` | 2 |
| Replay a prior read reply | `ReadFresh` | 3 |
| Capture a cut earlier than the decision head | `CaptureExact` | 2 |
| Issue a shortened worker lease | `LeaseRenewal` | 3 |
| Renew a read on an erased basis | `LeaseBasisOpen` | 5 |
| Trim using only live timed roots | `TrimSafe` | 5 |
| Fund a window without a capacity check | `Funded` | 1 |
| Install a fence despite a physical reference | `FenceSafe` | 2 |
| Install a fence despite opaque references | `FenceSafe` | 2 |
| Admit a late reference after the fence | `FenceSafe` | 2 |
| Dispose at lease end without waiting through drift | `DisposalSafe` | 6 |
| Rotate from a cut other than the exact preparation and head | `RotationGuard` | 3 |
| Commit an erasure without rotating the payload key generation | `ErasureAtomic` | 3 |
| Reclaim an open old root | `SettlementSafe` | 4 |
| Settle a closed root without disposition evidence | `SettlementSafe` | 4 |

Witness runs use baseline transitions and negate their respective target
states. Each named violation confirms reachability.

| Reachability target | Expected violated invariant | Steps from initial state |
| --- | --- | ---: |
| Fund, append, rotate, replay the mutation, trim and fence | `NoMaintenanceWitness` | 7 |
| Dispose of a withdrawn worker after an issued lease and drift | `NoDisposalWitness` | 6 |
| Select an ordinary checkpoint, close and settle the old root | `NoSettlementWitness` | 5 |
| Hold a record with no timed lease after erasure selects a newer root | `NoUnleasedHoldWitness` | 4 |
| Reach the journal lease end for a withdrawn worker whose durable hold remains | `NoDriftWindowWitness` | 5 |
