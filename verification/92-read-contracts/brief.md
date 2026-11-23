# Study 92 · Fresh observation and exact read recovery

2026-11-23

## Question

Can ordinary RTDB latest observation use a standing protected read without a journal command per invocation while exact protected result recovery retains the existing semantics?

## Sources

Use the [architecture tensions review](../architecture-reopening/tensions.md), [read index](../29-read-index/report.md), [reconfigured reads](../30-reconfigured-reads/report.md), [standing custody](../31-standing-custody/report.md), [ordered reply admission](../87-ordered-reply-admission/report.md), and [retained delivery](../88-retained-delivery/report.md).
Inspect the RTDB and Bijection call sites listed in the report at their recorded revisions.

## Model and comparisons

Compare a model that journals both kinds of fresh calls with a model that journals exact protected captures and allows markerless latest observations.
Compare an exact request falling back to a fresh observation when original evidence is missing.
Use one invocation per attempt, one authority replacement or terminal transition, and one protected delivery in TLC.
Model arbitrary finite histories for the same-scope logical cut proof and generic exact observations for the information requirement in Lean.
Use the existing standing custody and retained delivery reducers for both completion paths.

## Properties and programs

- A latest-only retry is a fresh invocation and can see a more recent applied cut.
- An explicit exact recovery returns its original result under the new authority and never substitutes the more recent cut.
- A fresh probe covers the ordered frontier, binds the invocation and scope, and admits only under an exact live local gate and session.
- A preceding terminal decision excludes a fresh invocation even with the same data frontier.
- An ordered logical close wins against exact reissue that has only probed.
- A protected borrow still supports completion through loss of the authorizer and never resumes after effective stop.

## Reproduction

Use TLC 2.19 with Java 21, Lean 4.35.0 and Python 3.13.
Run negative controls before the reference models.
Keep configurations and raw traces under .results/.
