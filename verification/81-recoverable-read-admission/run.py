#!/usr/bin/env python3
"""Check recoverable protected read admission and stale permit refusal."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_theorems, check_tla, compile_lean_modules


def check(name, laws, *, variant="reference", scenario="admitted-live", progress=False, expected=None):
    properties = [("INVARIANT", law) for law in laws]
    if progress:
        properties.append(("PROPERTY", "DegradedCompletes"))
    check_tla(ROOT, "ReadRecovery", name, "Fair" if progress else "Spec",
              {"Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}, properties, expected=expected)


def verify_tla():
    check("forget-outcome", (), variant="volatile-outcome", progress=True, expected="liveness")
    check("recover-from-pin-alone", ("ReturnedOriginal",), variant="pin-only-invents", expected="ReturnedOriginal")
    check("drop-basis", ("ExactHold",), variant="omit-basis", expected="ExactHold")
    check("keep-all-history", (), variant="needs-old-suffix", progress=True, expected="liveness")
    check("needs-lost-handle", (), variant="needs-lost-handle", progress=True, expected="liveness")
    check("retry-after-terminal", ("TerminalBound",), variant="retry-through-retirement",
          scenario="unadmitted-retired", expected="TerminalBound")
    check("recycled-slot", ("SettledClosed",), variant="slot-only", scenario="reuse", expected="SettledClosed")
    check("duplicate-invocation", ("NoDuplicateCharge",), variant="admit-duplicate",
          scenario="two-slots", expected="NoDuplicateCharge")
    laws = ("ReturnedOriginal", "ExactHold", "TerminalBound", "SettledClosed", "PointwiseCharge", "NoDuplicateCharge")
    check("admitted-live", laws, progress=True)
    check("admitted-retired", laws, scenario="admitted-retired", progress=True)
    check("unadmitted-live", laws, scenario="unadmitted-live", progress=True)
    check("unadmitted-retired", laws, scenario="unadmitted-retired")
    check("closed-slot-reused", laws, scenario="reuse")
    check("spare-slot-refuses-duplicate", laws, scenario="two-slots", progress=True)


def verify_lean():
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean",
                                        "79-rtdb-failover/RTDBFailover.lean",
                                        "80-applied-barrier-receipt/AppliedBarrierReceipt.lean"))
    check_lean_theorems(ROOT, command, ROOT / "RecoverableRead.lean", count=14)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
