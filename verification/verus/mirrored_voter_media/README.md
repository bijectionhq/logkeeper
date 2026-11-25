# Mirrored voter media (L10)

This area imports the shipped recovery, selection and two-slot sequencing
functions from [ordered voter media](../../../src/ordered/replication/disk.rs).
The production crate and the Verus harness compile the same function bodies.
The ghost contracts erase from normal builds.

| Lean `Logkeeper.SelectionFence` | Rust and Verus correspondence |
| --- | --- |
| `selectSlot` | `select_slot` projects the generations of eligible A/B candidates. `false` maps to index 0 and `true` to index 1. Selection takes the sole eligible candidate or the greater generation and rejects equal generations. |
| `Image.Dominates`, `Keeps`, `Step` | The image projects its promised ballot and optional accepted ballot with logical history length. The lexicographic pair of round and UUID nonce maps to the ordered Lean ballot, with absence at the bottom. A complete replacement dominates the durable survivor. An invalidated slot projects to `none`. The step law proves that replacement or invalidation preserves `Keeps`, and Lean lifts it to arbitrary finite traces. |
| `SyncStep`, `SyncTrace`, `mirrored`, `reply_requires_both_syncs` | A successful install syncs the alternate, preserves the survivor and advances the in-memory selector. The next install syncs the original slot with the same state. The shipped `Inner::mirror` yields a successful result only after both events and returns the actual physical descriptors in A/B order. The Verus state machine admits an acknowledgment only after those two transitions. |
| `one_tear_leaves_the_mirrored_image`, `any_surviving_slot_keeps_the_acknowledged_rank` | `recover_slot` checks body bounds, the header/body digest, slot identity and a decoded state before yielding a candidate. Under the tear premise, the surviving image after a single tear of either slot is the acknowledged image. After intervening steps satisfying `Keeps`, every returned image dominates the acknowledged rank. |
| `AtFence`, `MirrorsFence` | The shared L13 readback check requires the physical descriptor, exact promised ballot, exact accepted ballot and exact prefix digest. The shipped `Inner::read_back` visits A and B and propagates a failed visit. |

The file adapter supplies the raw fixed-size header and the declared body
bytes, with SHA-256 over the header descriptor and that body. Recovery uses
the shipped [slot header decoder and scope check](../voter_slot_header/README.md). A detectable
partial write invalidates one slot. A tear may also preserve a complete image
when the resulting descriptor and body are unchanged. The model assumes the
digest binds that pair and that successful filesystem syncs persist it without
damaging the other file. It covers one tear on the preallocated two-slot media.
An unrecoverable file I/O error can propagate. The model's guarantee is about
returned images.

The second-slot fast path feeds the exact ballot framing, length words, and
payload chunks into the [checked mirror-body comparison](../voter_mirror_body/area.json).
An earlier mismatch remains a mismatch through later chunks, and reuse
requires the full declared body. The reader also verifies this slot's digest
and group and voter identities. A valid differing image goes through the
original decode and replay path. That path's correspondence between the
decoded compact base and the complete chosen history is still open.

The foreign contracts cover file reads, hashing, semantic prefix decoding,
`install` and a single physical readback visit. In the shipped adapter,
`persist` writes the body and header then calls `sync_all`. The install
updates the selector after that returns. Warm reopen syncs the recovered
selected slot before reuse. `Inner::prepare` and `Inner::accept` propagate
a failed mirror before constructing a positive reply. The voter lock
serializes that sequence. These outer call sites and the file adapter were
inspected. Prefix replay and the protocol-level argument that complete updates
are rank-monotone are separate L3 and L11 obligations.

The existing native media tests exercise header and body tears, a changed
accepting majority and a sealed successor repaired from surviving images.
The Lean witnesses reach two syncs followed by acknowledgment and a selected
slot tear after a majority change. The general theorems have no fixed
trace-length or command-history bound.

The [mechanical link inventory](../../link/inventory.md) lists the checked
projections and the remaining Lean correspondence for this area.
