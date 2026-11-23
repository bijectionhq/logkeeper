# Study 07 · Consolidated stream reference machine

## Question

Do the local stream rules preserve committed history, retirement, and bounded retention together for arbitrary finite traces?

## Sources and scope

Use the [revised requirements](../requirements.md) and amendments from the commit, handoff, retention, and lifecycle studies.
Use one abstract stream with arbitrary payload type and two natural-number budgets.
The model sees an authenticated, ordered authority transition.
It stores the entire committed history for specification purposes.
A trim changes which range is retained.
A handoff freezes and reinstalls an exact cut.
Checkpoint publication certifies that its represented prefix can be reconstructed.
A physical durability theorem independently counts two durable locations and a single lost zone.

This is a reference machine for logical transitions.
Group consensus, distributed takeover, signed permits, independent snapshots, and physical custody require refinement against their separate models.

## Checked properties and mutations

Prove initial validity, preservation of bounds and replay protection, monotone committed history, terminal retirement, exact receipts, and correct read barriers.
Show that an authorized append with headroom yields an exact receipt.
Derive explicit refusal for stale writers and wrong LSNs.
Mutate the LSN, writer, trim certificate, replay protection, and barrier rules.
Use the Lean 4.35.0 pin and match each negative control to its proof location.
See the [report](report.md) for exact claims and reproduction.
