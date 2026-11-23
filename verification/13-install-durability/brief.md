# Study 13 · Installation and membership durability

## Question

Can an exact staged image become unsafe to activate after the destination changes membership or reclaims one of the copies it certified?

## Sources and comparison

Compose the [placement trace proof](../11-authority-refinement/report.md) and the [journal membership proof](../12-quorum-membership/report.md).
A sealed source retains a one-record cut.
The destination pre-copies onto some voters, can replace one member, and can certify and activate its placement.
One AZ can be lost, and the source can reclaim its handoff copy after positive installation.

Compare a staging receipt checked against current membership and a prepared image registered as a durability obligation that membership changes must preserve.
The stale-proof control treats a pre-copy receipt as proof of current recoverability.
Further controls reclaim certified bytes without invalidating the receipt and release the source on preparation.

## Properties and general proof

Check that an active target has an exact record in every available recovery quorum and that either the source still holds custody or the serving target owns a surviving copy.
Use one target voter replacement, four durable identities across three AZs, one logical payload, and one source-target move.
A target revision names its authentic member identities.
Prepared copies are exact in this model.
Source availability and the group-majority storage proof are abstractions supplied by the journal study.

Use Lean to check that successful installation both takes a concrete authority transition and leaves a recoverable exact cut in the journal view of the target at that decision.
Prove registered coverage survives physical or membership transitions that leave the prepared image unchanged.
Mutate the exact-image, adopted-membership and current-copy premises.
Use the pinned runners and record results in the [report](report.md).
