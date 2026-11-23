# Study 25 · Journal media crash consistency

2026-11-22

## Question

Can an exact local durability vote survive any permitted crash during journal compaction while foreground appends continue?

## Sources

Read the shared [requirements](../requirements.md), the [quorum membership model](../12-quorum-membership/report.md), the [physical read model](../14-read-custody/report.md), and the [checkpoint reconstruction model](../16-checkpoint-reconstruction/report.md).
Use RTDB Multi's `LogService` contract at RTDB commit `fc6da3a4a3` and the Logkeeper [journal](../../src/server/journal.rs) at `85a594e` to identify the real interface and the difference between local compaction and RTDB trim.

## Model

Model a local replica with ordered exact records, separately synced data and names, an acknowledged prefix, and a distinct externally certified commit cut.
Model one compaction with a captured cut, a replacement base, the selector publication and durability barriers, and predecessor reclamation.
A crash can expose either selector after publication starts and before its durability barrier completes.
A crash may lose or tear unsynced frames and may leave valid suffix fragments.
A record is available only if recovery can discover its extent and decode that exact record in order.

Scope the media assumptions to one intact replica.
A successful data barrier preserves the exact synchronized bytes.
A successful namespace barrier preserves their recovery names and the published selector.
Atomic selector replacement exposes an old or a new identity while durability is in doubt.
Decoder validation represents exact framing and identity.
Media loss, undetected corruption, concurrent selector replacements, consensus decisions, and the data layout of an actual filesystem are outside this model.
Use the existing recovery quorum intersection to lift a durable local vote to per-record availability.

## Checks and comparison

- Safety under crash. The exact acknowledged prefix remains recoverable under either permitted selector.
- Structural safety. Recovery never joins records across an invalid frame and never exposes bytes beyond the externally committed cut.
- Expressiveness. A copy can publish after the acknowledged head advances past its captured cut. A replica can acknowledge another write during selector uncertainty, recover with the old selector, and recover the same suffix with the durable new selector after predecessor reclamation.
- Compare a fixed base replacement with an exact shared suffix against the same recovery rules with publication requiring the acknowledged head to equal the captured cut.
- Falsify independently by weakening data sync, name sync, decoding, use of commit evidence, replacement sync, predecessor protection, suffix preservation, and suffix reachability during selector uncertainty.

## Tool and report

Run each negative control before its intact checker.
Use TLC 2.19 with one worker and a 512 MiB heap, pinned by the repository runner, and Lean 4.35.0 with the study's toolchain file.
The runner stores raw commands and results under the ignored study directory and times out each tool invocation after 60 seconds.
Report the shortest failing traces, the compared bounds, the general theorem statements, the remaining media assumptions, and the amendments needed by the design.
