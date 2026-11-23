# Study 08 report · Snapshot basis across a stream move

2026-11-22

## Verdict

A snapshot succeeds only after acquiring both the checkpoint object pin and the exact log replay hold.
Those acquisitions can be separate operations.
A source seal freezes the replay hold with the floor, and the successor installs both.
Expiry stops new reads and drains admitted reads before releasing custody.

## Properties and comparison

The baseline satisfies all three safety laws across 144 states, for one object, one replay hold, two floor positions, and one move.

| Amendment | Mutation | Shortest counterexample |
| --- | --- | --- |
| A24 | `unprotected_objects` | Begin without pinning checkpoint objects → acquire replay → expose → let the object reaper remove the active basis. Four transitions. |
| A25 | `forget_replay_hold` | Acquire both pins → expose → seal → activate without the hold → trim away the admitted replay range. Six transitions. |
| A26 | `expire_before_drain` | Acquire both pins → expose → begin a read → expire → release the object pin → reap before the admitted read completes. Seven transitions. |

The 13-transition positive witness continues a snapshot after handoff, closes both protections, and lets trim and object reaping advance.
The six-transition refusal witness releases the partially acquired snapshot when the chosen checkpoint's cursor has already been trimmed.

## Residue

The proof is bounded and protects readability, with no claim that either service remains reachable.
This study's drain-first rule applies to full snapshots with unresolved storage dependencies.
The later [physical custody study](../14-read-custody/report.md) checks an earlier logical release for independently pinned exact I/O.
Its drain premise needs a real rule for stalled I/O, crashed clients, and reissued permits.
A deployment can reclaim a timed-out permit after it has effectively revoked new work and fenced or drained the work already admitted under that permit.
RTDB continues to own object security and checkpoint construction.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java python3 verification/08-replay-handoff/run.py
```

The runner retains the exact TLC configuration, command, and logs.
