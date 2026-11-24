# Stream writer decisions

The harness imports [the production decisions](../../../src/stream/writer/decision.rs).
It verifies the acknowledgement predicate and recovery ordering over all
representable epochs and LSNs. It uses standard Verus axioms and no external
bodies or assumptions.

The acknowledgement decision takes three slots, each assigned to a distinct
keeper by the writer. A slot covers a requested LSN only when the request's epoch
matches and the keeper has acknowledged at least that LSN. The harness checks
that a single keeper, an acknowledgement at another epoch, and an
acknowledgement for a shorter prefix each fail to commit. Every pair of survivors
can commit. Recovery compares synced epoch first and tail second, with a synced
epoch of zero ordered above an absent synced epoch.

The five controls mutate the production functions and must fail the named
postconditions. The proof boundary leaves keeper durability, request binding,
the asynchronous writer, and preservation of prefix contents to the protocol
and its integration tests.

```sh
python3 verification/verus/run.py --verus /Users/sachaichbiah/code/codesign-agents/tools/verus stream_writer
```
