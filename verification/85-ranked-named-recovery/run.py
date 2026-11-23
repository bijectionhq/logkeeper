#!/usr/bin/env python3
"""Check ranked, named, and installed recovery as one path."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def check(scenario, name, laws=(), *, progress=False, expected=None):
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", "Progress"))
    variant = name if expected else "reference"
    check_tla(ROOT, "RankedNamedRecovery", name, "Fair" if progress else "Spec",
              {"Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}, checks, expected=expected)


def verify_tla():
    check("covered", "learned", ("ExactChoice",), expected="ExactChoice")
    check("covered", "length", ("ExactChoice",), expected="ExactChoice")
    check("covered", "same-position", ("NeverReopens",), expected="NeverReopens")
    check("covered", "winner-serves", ("InstalledFirst",), expected="InstalledFirst")
    check("foreign", "skip-scope", ("BindsSuccessor",), expected="BindsSuccessor")
    check("superseded", "stale-serve", ("BindsSuccessor",), expected="BindsSuccessor")
    check("advanced", "ignore-current-cut", ("AtCurrentCut",), expected="AtCurrentCut")
    check("target-unreachable", "ignore-target-quorum", ("ReachableInstall",), expected="ReachableInstall")
    check("missing", "ignore-missing", ("CompleteMedia",), expected="CompleteMedia")
    check("covered", "every-replica", progress=True, expected="liveness")
    check("covered", "install-before-stage", progress=True, expected="liveness")

    laws = ("ExactChoice", "CompleteMedia", "NeverReopens", "InstalledFirst", "BindsSuccessor", "AtCurrentCut",
            "ReachableInstall")
    check("covered", "covered", laws, progress=True)
    check("missing", "missing", laws)
    check("foreign", "foreign", laws)
    check("superseded", "superseded", laws)
    check("advanced", "advanced", laws)
    check("target-unreachable", "target-unreachable", laws)


def verify_lean():
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "33-activation-slot/ActivationSlot.lean",
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean",
                                        "79-rtdb-failover/RTDBFailover.lean",
                                        "80-applied-barrier-receipt/AppliedBarrierReceipt.lean",
                                        "81-recoverable-read-admission/RecoverableRead.lean",
                                        "82-joint-read-recovery/JointReadRecovery.lean",
                                        "83-ordered-read-replay/ReadInvocationFloor.lean",
                                        "83-ordered-read-replay/OrderedReadReplay.lean",
                                        "84-read-invocation-floor/InvocationFloorProof.lean"))
    source = ROOT / "RankedNamedRecovery.lean"
    check_lean_mutation(ROOT, command, source, "omit-current-cut",
                        [("target.frontier = frames\n\ntheorem the_current_target",
                          "frames = frames\n\ntheorem the_current_target")],
                        "  exact Iff.rfl")
    check_lean_theorems(ROOT, command, source, count=12)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
