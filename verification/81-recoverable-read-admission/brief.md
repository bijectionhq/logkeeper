# Study 81 · Recover a protected read admission before its first receipt

2026-11-23

## Question

What can a successor return when a marker applied before its issuer failed, but the caller received no receipt or newly allocated permit?

[Study 18](../18-snapshot-admission/report.md) captures and protects the exact latest basis in one ordered reservation.
[Study 80](../80-applied-barrier-receipt/report.md) verifies a genuine receipt after source loss and leaves failure before issuance open.

## Comparison

Use the same pending invocation and marker across source loss, compaction, and optional retirement.
Compare a coupled protected admission, a volatile result, a surviving pin without the result, a result without the pin, and a rule that requires the old suffix or the lost permit.
Allow a new invocation when recovery establishes the old attempt has no admitted result and the deployment is live.
Require an exact original result when protection was already admitted.
Reuse a released slot under a new permit and attempt delayed old work.
Leave a second paid slot free and retry the original invocation.

Use TLC for the finite failures and conditional progress.
Use Lean to join the actual successful chosen marker with the existing snapshot admission, establish the retained-row invariant, refine reissue to the original guarded issuer, and check bounded row encoding.
Treat the correctly selected combined control image and scoped authorization as explicit premises.
Production qualification and wire authentication remain outside the model.

See the [report](report.md) for evidence and limits.
