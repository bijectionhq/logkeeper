# Study 76 · Replace a worker inside its existing journal placement

2026-11-23

## Question

Can an admitted RTDB worker acquire the exact ordered writer grant and recover its cut using the installed journal and prepaid window while the directory, incumbent worker, and capacity allocator are unavailable?

## Sources

Use the [authority model](../02-handoff/report.md), [ordered source](../49-unified-source-history/report.md), [prepaid appends](../62-funded-appends/report.md), and [joint realized replay](../75-joint-realized-replay/report.md).
RTDB Multi's current target contract describes its directory CAS and selection of a fresh loglet in `allium/rtdb-multi.allium` under `Claim`.

## Models

Compare a same-placement grant with a compulsory physical migration, a directory-authorized publication step, and a path that waits for the old worker.
Check old-writer fencing, successor catch-up, authenticated nomination, and actual reuse of the exact paid window.
Use TLC 2.19 and Lean 4.35.0.
