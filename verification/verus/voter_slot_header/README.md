# LKORV005 voter slot header

The harness imports [the shipped slot header codec](../../../src/ordered/replication/slot_header.rs).
[Persistence](../../../src/ordered/replication/disk.rs) uses it to write the descriptor. The [mirrored media recovery proof](../mirrored_voter_media/README.md) imports the same decoder and scope check that [recovery](../../../src/ordered/replication/disk/recover.rs) calls.

The Verus sequence views correspond to byte lists in [Logkeeper.VoterSlotHeader](../../lean/Logkeeper/VoterSlotHeader.lean).
`encodeBE` and `decodeBE` agree with the Lean bit-vector operations on eight-byte words.
`slotDescriptor` concatenates the magic, 32-byte group, 16-byte voter, generation and payload length in wire order.
`slotHeaderLengthValid` checks exactly 104 header bytes and a declared payload length between two bytes and the slot's payload capacity, inclusive.
`slotHeaderMatches` checks the exact magic, group, and voter and a nonzero generation.
`voter_slot_header_round_trips` checks all the typed fields and the trailing 32 stored digest bytes.

The file adapter reads the exact bounded payload extent, computes SHA-256 and checks the digest before applying the scope check. An all-zero header fails the minimum-length check. File I/O, SHA-256, the payload's ballot and prefix decoder, and durability are outside this area.

The [manifest](area.json) covers a wrong generation offset, a skipped payload capacity check, a wrong digest offset, and a weakened voter check.

The [mechanical link inventory](../../link/inventory.md) lists the checked
projections and the remaining Lean correspondence for this area.
