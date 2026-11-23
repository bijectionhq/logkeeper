# Study 10 · Cancelling a prepared move

## Question

When can a target reclaim a prepared destination slot without invalidating a source seal that may already exist?

## Sources and model

Use the one-use reservation protocol from [study 06](../06-generations/report.md).
The target reserves a unique nonce and can receive a cancellation request independently of the source.
The source serializes issue of an abort receipt and seal under that nonce.
The target is a separate authority and accepts the abort receipt against the exact live nonce.
The source link can fail and recover.
Model up to two or four issued nonces, with one source-target pair and one successful move.

Check that seal and abort are exclusive, that a sealed move keeps its activation slot, and that a requested slot is eventually freed or installed when the source link stays available.
Use the three weakened guards to test those laws.
The model assumes trusted receipts, durable source decisions, and weak fairness for eligible abort, cancel and install actions.
It abstracts reservation quotas, competing destinations and record transfer.
See the [report](report.md) for the disputed availability claim and the reproduction command.
