# Study 105 · Separate a serving cut from its protection promise

2026-11-23

## Question

Can a funded installed journal open a verified surviving cut without diagnosing the missing AZ, and still honour one-AZ recoverability for every acknowledged input?

## Sources

Use S02, S57, L01 and L26 in the [requirements](../requirements.md), the [exact admission model](../67-full-admission/report.md), and the [indistinguishable diagnosis histories](../99-degraded-evidence/report.md).
Keep the existing approval to serve independently of the regional decision service and keep the existing durability envelope.

## Model and checks

Compare a service cut with independent durability checks against using timeout as diagnosis and against waiting to serve until diagnosis.
Use the same reachable majority, input placement and headroom for each paired history.
Compare withdrawing retained copies when they leave the serving cut against checking post-withdrawal protection.
Compare renewal based on voter readiness against renewal with exact data coverage too.

Check that an acknowledged input survives each credible loss, that a served cut has the exact installed inputs, and that renewal restores the full envelope.
Check progress under stable installed support and enough durable placement to acknowledge when diagnosis is unavailable.
Include the known-outage path with a single surviving input copy and the ambiguous one-copy case that refuses acknowledgment.

TLC checks three AZs, one prior acknowledged input, one candidate, one service cut, and at most one renewal.
Lean checks the protection predicate across arbitrary histories of abstract authorized steps and the indistinguishable one-copy impossibility.
The shared runner uses a 60-second limit per command and pins TLC 2.19 and Lean 4.35.0.

## Boundaries

Assume certified copies contain the exact input and remain recoverable when their AZ survives.
Assume the verified cut contains its eligible window, current quorum and all exact required inputs.
Treat the prior evidence of an actual AZ loss and repair readiness as externally established premises.
Model full copies to compare the two architectures on common histories.
Keep the design criterion at exact reconstructibility under each credible loss, including if a future implementation uses fragments or a different durable arrangement.
