# Study 06 · Repeated moves and stale certificates

## Question

Can a placement be reused or compacted while an authentic old seal certificate is still in flight?

## Sources and comparisons

Use S07, S08, and B02 and the portable activation protocol in [study 02](../02-handoff/report.md).
The generation-floor design keeps the latest installed generation at every former owner.
The reservation design uses an authenticated, single-use destination reservation with a durable issuance counter.
A seal binds the stream, the predecessor generation, the exact destination, and that reservation.
Installed certificates may arrive again in any order.

The reservation design permits the old per-stream generation floor to be forgotten.
A missing reservation denies installation.
A consumed nonce cannot appear in a subsequent reservation.
Group identities and counters are distinct durable resources in the model.

## Model and properties

One stream moves among two or three groups and up to three or four placement generations.
Every certificate contains the exact source history.
Each group observes only its local activation gate when consuming an authentic delivered certificate.
The model allows tentative reservations for stale generations.
They can reserve space and cannot produce an authoritative seal.
Retirement is terminal.

Check unique authority, preservation of all received append receipts, terminal retirement, and a usable pending reservation after the predecessor has sealed.
Mutate the destination binding, replay floor, nonce freshness, and slot expiry.
Use Lean for all-length traces of the reservation nonce state machine.
The model abstracts authenticated creation, reservation abort, resource limits on unresolved slots, redirect lifetime and physical custody.

## Rules

Use pinned TLC to compare both candidates under the same bounds and Lean 4.35.0 for the nonce proofs.
Run controls before reporting each baseline.
See the [report](report.md) for outcomes and reproduction.
