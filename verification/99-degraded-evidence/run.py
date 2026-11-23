#!/usr/bin/env python3
"""Compare physical diagnosis with an explicitly authorized operating mode."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def compare(name, world, policy, *, approved=True, inputs=True, progress=True, expected=None):
    constants = {
        "World": f'"{world}"', "Policy": f'"{policy}"', "OwnerApproved": "TRUE" if approved else "FALSE",
        "InputsAvailable": "TRUE" if inputs else "FALSE",
    }
    laws = [("INVARIANT", law) for law in ("NoFalseDiagnosis", "AuthorizedMode", "ServesWithExactInputs")]
    if progress:
        laws.append(("PROPERTY", "EventuallyServes"))
    check_tla(ROOT, "DegradedEvidence", name, "Fair", constants, laws, expected=expected)


def main():
    compare("timeout-false-diagnosis", "slow", "infer-failure", expected="NoFalseDiagnosis")
    compare("wait-for-proof", "failed", "await-proof", expected="liveness")
    compare("missing-owner-authorization", "failed", "ordered-exclusion", approved=False, expected="liveness")
    compare("ignore-exact-inputs", "failed", "ignore-inputs", inputs=False, expected="ServesWithExactInputs")
    compare("diagnosis-happens-to-be-correct", "failed", "infer-failure")
    compare("approved-exclusion-slow", "slow", "ordered-exclusion")
    compare("approved-exclusion-failed", "failed", "ordered-exclusion")

    command = compile_lean_modules(ROOT, ())
    source = ROOT / "DegradedEvidence.lean"
    check_lean_mutation(ROOT, command, source, "weaken-diagnosis",
                        [("enter (observes world) = true → failed world",
                          "enter (observes world) = true → True")],
                        "  exact alive")
    check_lean_theorems(ROOT, command, source, count=2)


if __name__ == "__main__":
    main()
