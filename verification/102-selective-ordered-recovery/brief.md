# Study 102 · Recover the selective read window with the ordered state

2026-11-23

## Question

Can independent exact reads overtake a gap while preserving the existing capture, close, retained delivery, and writer handoff guarantees across either selectable checkpoint?

## Sources and comparisons

Use the [ordered read reducer](../83-ordered-read-replay/OrderedReadReplay.lean), [writer-scope fence](../84-read-invocation-floor/InvocationFloorProof.lean), [retained delivery path](../88-retained-delivery/report.md), [ranked transfer](../32-configuration-closure/report.md), and [selective window proof](../101-selective-read-window/report.md).
Keep exact original reservation, terminal stop and live delivery custody checks in the shared reducer.
Compare missing suffix, lost sparse marks, close clearing either consumed identities or custody, and accepting an old scope after activation.
The finite model has two possible nonces, one result slot, one independent delivery, two writer scopes and one recovery.
It represents chosen frames by their exact ordered postimages.
Lean replays the interpreted frames and ties the summary to the existing named checkpoint opener.

## Acceptance

1. Open and close the later invocation while the earlier request is delayed.
   Recover through the stable or newer selector.
   Refuse restart of the later invocation and admit the earlier one.
2. Retain an independently funded delivery from an older read.
   Close its admission and recover, then seal and activate a greater writer.
   Refuse predecessor use of the new bitmap.
   Admit fresh work in the successor while its predecessor's hold remains separately settleable.

## Reproduction

Use Python 3.13, Java 21, TLC 2.19 and Lean 4.35.0.
The runner checks counterexamples before the passing schedules and records each build and trace under .results/.
