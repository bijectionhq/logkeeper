#!/usr/bin/env python3
"""Compare maintenance reserve designs under repeated writer replacement."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def lane(name, policy, reserve, crashes, laws, *, progress=False, expected=None):
    constants = {"Policy": f'"{policy}"', "Reserve": str(reserve), "MaxCrashes": str(crashes)}
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", "EventuallyCheckpoints"))
    check_tla(ROOT, "MaintenanceLane", name, "Fair" if progress else "Spec", constants, checks,
              expected=expected)


def verify_tla():
    lane("per-term-claim-exhausts-the-sized-reserve", "per-term-claim", 5, 4, ["ProgressHeadroom"],
         expected="ProgressHeadroom")
    lane("per-term-claim-stalls-checkpoint-progress", "per-term-claim", 5, 4, ["WithinReserve"],
         progress=True, expected="liveness")
    lane("unfenced-grant-admits-a-stale-upload", "grant-unfenced", 4, 2, ["OneUploadPerBlock"],
         expected="OneUploadPerBlock")
    lane("grant-fenced-three-records", "grant-fenced", 3, 6,
         ["WithinReserve", "ProgressHeadroom", "OneUploadPerBlock"], progress=True)
    lane("per-term-claim-without-crashes", "per-term-claim", 5, 0,
         ["WithinReserve", "ProgressHeadroom"], progress=True)


def verify_lean():
    command = compile_lean_modules(ROOT, ())
    source = ROOT / "MaintenanceBound.lean"
    check_lean_mutation(ROOT, command, source, "claim-on-every-regrant",
                        [("Step lane { lane with grant := lane.grant + 1 }",
                          "Step lane { lane with grant := lane.grant + 1, used := lane.used + 1 }")],
                        "    | regrant => exact shape")
    check_lean_theorems(ROOT, command, source, count=4)


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
