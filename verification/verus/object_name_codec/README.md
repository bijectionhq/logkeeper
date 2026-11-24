# Canonical codec object names

The [shipped name check](../../../src/ordered/object_names.rs) is used by the command and compact-image decoders, the service replay record decoder, and the reducer's object admission. It applies to fixed 32-byte names. The surrounding decoder reads the count and byte extent before calling the check.

`objectNameBefore` uses the first differing byte. On equal-width names it agrees with the lexicographic list relation in [Logkeeper.CompactImage](../../lean/Logkeeper/CompactImage.lean). `objectNamesCanonical` checks the exact count ceiling, requires a nonzero first name in a nonempty list, and checks each adjacent pair. The law `admitted_object_names_are_bounded_sorted_unique_and_nonzero` proves the global property for every pair and every member.

The [manifest](area.json) mutates the shipped first-difference comparison, the inclusive limit and the zero-name check. The harness also checks the production budget constant used by the codec.
