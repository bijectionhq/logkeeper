# Study 34 · Pending activation across target reconfiguration

2026-11-22

## Question

How can an existing target group replace a voter while an incoming stream installation is pending, without losing an unreported decision or making group repair wait on unrelated source staging?

## Sources

Use the [requirements](../requirements.md), [target install durability](../13-install-durability/report.md), [ordered application](../28-ordered-application/report.md), [configuration closure](../32-configuration-closure/report.md), and [fixed target activation slot](../33-activation-slot/report.md).
RTDB Multi distinguishes durable journal identity, exact append quorums and sealed recovery. [RTDB Multi](https://github.com/bijectionhq/rtdb/blob/fc6da3a4a3/allium/rtdb-multi.allium#L449-L474)

## Model

Compare ordering activation in an existing target journal, transferring a distinct pending slot with its accepted binding, and deferring target voter changes until the pending installation produces a result.
Use one already authorized incoming intent, one target voter replacement, and two eligible exact images.
Distinguish accepted evidence, quorum choice, publication, current payload coverage, and the source link.
Allow an unfenced voter to finish a delayed predecessor vote.
In the replay model, distinguish the revision at a command's log position from the physical membership of the learner replaying it.
Treat authorization, exact stage evidence and stable media according to the earlier contracts.

## Properties and acceptance

- Preserve an unreported choice across voter replacement and publish it from the new target quorum.
- Carry a recovered accepted binding even if the old voters never assembled a quorum for it.
- Reject a second installation, a stale readiness grant, and service from historical evidence alone.
- Replay a pre-change activation under its original ordered state after the learner changes membership.
- Refuse a delayed old packet ordered after the revision changes or after its exact staging grant is discarded.
- Replace a target voter while the source image has yet to arrive and the target journal has no command depending on it.
- Check the wait policy separately with a ready image and with the source still unavailable.

## Tools and evidence

Use TLC 2.19 with one worker, a 512 MiB heap, and 60 seconds per case.
Use Lean 4.35.0 for arbitrary ordered histories and their composition with ranked closure.
Keep physical readiness and historical application as separate evidence.
The study models an already authorized target, so initial bootstrap and source-side cancellation only enter through their previously established contracts.
