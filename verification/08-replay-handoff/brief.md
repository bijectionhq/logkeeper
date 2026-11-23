# Study 08 · Snapshot basis across a stream move

## Question

Can a snapshot protect both an RTDB checkpoint and its replay suffix through concurrent trim, a handoff, and expiry?

## Sources and model

Compose the [retention study](../03-retention/report.md) and the [handoff study](../02-handoff/report.md).
One reader chooses an old checkpoint whose object custody is managed separately from the log authority.
The object can be reaped if unpinned.
The tail can move its floor beyond the chosen checkpoint if no replay hold remains.
One cross-group move can happen between any actions.
A read can be in flight when its permit expires or closes.

Check that successful exposure requires both protections, that an active snapshot or admitted in-flight read never loses either part of its basis, and that a completed close releases both.
Verify failure paths where the object is unprotected, the target forgets a live hold, or expiry reclaims resources before draining.
The model abstracts content certification, wall time, retries with duplicate lease IDs, links, and simultaneous readers.
Use the shared TLC runner and record exact evidence in the [report](report.md).
