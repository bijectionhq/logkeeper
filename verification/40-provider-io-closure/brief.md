# Study 40 · Close outstanding provider writes

2026-11-23

## Question

Which evidence lets a custodian certify stable absence or take over the charge for a copy whose write may still arrive?

## Sources

Use the [requirements](../requirements.md), [physical read custody](../14-read-custody/report.md), [custodian recovery](../24-custodian-recovery/report.md), [standing custody](../31-standing-custody/report.md), and [certified activation replay](../39-certified-activation-replay/report.md).

## Model and comparison

Separate admission, durable provider effect, and disposition for one immutable physical version.
Compare draining exact issued tickets with a provider-enforced fence for the entire retiring version.
Represent queued writes, retransmissions, independent counterpart reachability, crash recovery, and transfer of the entire outstanding charge.
Treat media operations and transfer of provider obligations as explicit atomic boundaries.

## Properties and acceptance

- Refuse new physical effects after certified absence, including old writes and duplicate successful writes delayed past deletion.
- Seal admission and retain protection for every previously issued ticket until its durable completion or an effective provider stop.
- Refuse to infer effective stop from a timeout, an unrelated receipt, or a local admission fence.
- Recover exact provider fences and one-use decisions after restart.
- Release the target charge while the provider is unavailable when the original custodian durably covers all possible remaining writes and bytes.
- Keep erasure pending during that outage unless stable absence was already proved.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap and 60 seconds per case.
Use Lean 4.35.0 for arbitrary finite traces, the disposition proof, and mechanism controls.
