# Study 31 · Standing snapshot custody

2026-11-22

## Question

Can reads share custody of an exact applied snapshot without each read becoming an ordered group command, including during checkpoint replacement, restart, and retirement?

## Sources

Use the [requirements](../requirements.md), [terminal closure](../04-retirement/report.md), [effective read stop](../14-read-custody/report.md), [snapshot admission](../18-snapshot-admission/report.md), and [carried read floors](../30-reconfigured-reads/report.md).
RTDB Multi's `ReadIndexUsesTheActiveLoglet`, `TrimFollowsPublication` and `DroppedStreamsAreTerminal` are the upstream read, retention and deletion contracts. [RTDB Multi at fc6da3a4a3](https://github.com/bijectionhq/rtdb/blob/fc6da3a4a3/allium/rtdb-multi.allium)

## Model

Use the earlier ordered per-read reservation as the reference.
Model local admission into a standing window backed by one registered physical hold.
Each window is bound to one exact applied prefix, complete root and replay dependency set, and fresh endpoint session.
Opening the window precedes any local admission.
A physical release follows effective gate closure and verified drainage or stop for the original session.
Model a restart that loses the local per-read table while admitted I/O can still succeed.
Compare preparing a charged replacement in advance with closing the old gate first.

Compare terminal closure at the write quorum with a stronger deadline that excludes even the first local admission of an overlapping preterminal invocation.
Model the retirement command at its ordered group position, and compare the original invocation's verified floor with the window's live applied position.
Also compare requiring every open gate to seal before terminal closure.
Keep physical disposal separate.

Abstract authentic quorum observations into their certified invocation-bound lower bound.
Represent applied prefixes by positions in one exact chosen history.
Treat complete physical registration and an effective fence on an endpoint session as premises and test their use.
Use unit command positions and project the terminal command independently of the stream LSN.

## Properties and acceptance

- Check continued physical backing for every live borrow, including after restart, replacement, and simultaneous borrows under one registration.
- Check freshness, rejection of calls started after terminal closure, and terminal receipt progress at quorum when a serving gate is disconnected.
- Exhibit an overlapping call that may first borrow after terminal closure, and a finished preterminal borrow whose reply arrives later.
- Check terminal progress for the all-gates candidate under both stable reachability and a permanently isolated serving gate.
- Demonstrate that old pinned resources remain charged against bounded storage admission and never authorize a new end-point session.

## Tools and report

Use TLC 2.19 with one worker, a 512 MiB heap and 60 seconds per case.
Use Lean 4.35.0 and record the axioms and negative controls.
Record bounds and the precise strength of the result for each candidate.
