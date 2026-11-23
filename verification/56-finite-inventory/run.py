#!/usr/bin/env python3
"""Check finite issuance, durable recovery, and canonical inventory bytes."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("NoNameReuse", "NoStaleAccess", "RecoveredExact", "Bounded")


def check(name, laws, *, budget=2, serials=2, epochs=1, variant="reference",
          scenario="counters", expected=None):
    constants = {"Budget": budget, "MaxSerial": serials, "MaxEpoch": epochs,
                 "Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}
    check_tla(ROOT, "FiniteInventory", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_tla():
    check("control-wrap-issuer", ("NoNameReuse",), budget=1, serials=1,
          variant="wrap_issuer", expected="NoNameReuse")
    check("control-reuse-epoch", ("NoStaleAccess",), budget=1, serials=1,
          variant="reuse_epoch", expected="NoStaleAccess")
    check("control-ignore-suffix", ("RecoveredExact",), budget=1, serials=1,
          variant="skip_tail", scenario="checkpoint", expected="RecoveredExact")
    check("control-reissue-after-rollback", ("NoNameReuse",), budget=1, serials=1,
          variant="skip_tail", scenario="checkpoint", expected="NoNameReuse")
    check("finite-counters", LAWS)
    check("finite-counters-larger", LAWS, serials=3, epochs=2)
    check("checkpoint-and-exact-suffix", LAWS, scenario="checkpoint", budget=1, serials=1)
    for name, law in (("settle-at-issuer-limit", "NeverSettlesAtMax"),
                      ("settle-sealed-epoch", "NeverSettlesSealed")):
        check(f"witness-{name}", (law,), expected=law)
    law = "NeverRecoversOlderAtMax"
    check("witness-recover-older-at-issuer-limit", (law,), budget=1, serials=1,
          scenario="checkpoint", expected=law)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
        "51-checkpoint-envelope/EnvelopeCodec.lean",
        "52-shared-extent-accounting/SharedExtentAccounting.lean",
        "55-pool-incarnations/PoolIncarnations.lean",
        "56-finite-inventory/FiniteCounters.lean",
    ))
    counters = ROOT / "FiniteCounters.lean"
    check_lean_mutation(ROOT, command, counters, "recover-a-prefix-without-its-tail",
        (("(verifiedTail : base ++ tail = chosen)", "(verifiedTail : base = chosen)"),),
        "rw [← verifiedBase, ← verifiedTail, List.foldl_append]")
    check_lean_theorems(ROOT, command, counters, count=8)
    codec = ROOT / "InventoryCodec.lean"
    check_lean_mutation(ROOT, command, codec, "decode-sealed-as-a-usable-epoch",
        (("| .sealed => ⟨.offline, row.epoch + 1⟩", "| .sealed => ⟨.offline, row.epoch⟩"),),
        "change Access.mk .offline (wordLimit width - 1 + 1)")
    check_lean_theorems(ROOT, command, codec, count=9)


if __name__ == "__main__":
    if len(sys.argv) == 1 or sys.argv[1:] == ["tla"]:
        verify_tla()
    if len(sys.argv) == 1 or sys.argv[1:] == ["lean"]:
        verify_lean()
