# Logkeeper Lean interface

Use `Logkeeper.Protocol` for typed data and decision cuts, durable chosen
prefixes, exact append receipts, and trim charges from the chosen application
interval. The quorum module incorporates the reference, quorum membership, and
durable prefix studies. A concrete caller supplies the durable voter trace and
relates the ledger to the real prepare and accept exchanges. The transfer theorem connects independent cohorts by the exact predecessor image decoded at installation. The byte-level refinement of the signed repair package is a separate obligation.

This package has source-level model obligations. A journal installation must
still discharge codec, provider, authentication and crash durability premises.
Pin dependants to the exact Logkeeper revision and the same Lean toolchain.

`Logkeeper.SelectionFence` starts each acknowledged promise or vote with
two durable images and models later complete writes, detectable slot tears,
and restart. It applies Studies 25 and 26's valid-image selection rule and
Study 106's exact sealed basis rule to ranked recovery majorities.
The theorem ranges over arbitrary journal histories, finite local traces,
strict majorities and finite repair chains. The reachability witness uses
three voters, two writes and one selected-slot tear.
The model assumes checked images, authenticated correct coordinators,
and exact repair and compaction bases. It abstracts disk barriers, wire
signatures and encoding to their inspected implementations.

Run `python3 run_selection_fence.py` from this directory to build the package
and check the one-slot control. Set `LAKE_BIN` if Lake is outside the path.
