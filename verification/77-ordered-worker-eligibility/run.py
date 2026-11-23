#!/usr/bin/env python3
"""Check ordered worker eligibility, bounded enrollment and exact recovery."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_tla, compile_lean_modules, check_lean_theorems


def check(name, *, variant="reference", scenario="race", property_name=None, expected=None):
    constants = {"Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}
    laws = [("INVARIANT", "GrantHasEnrollment"), ("INVARIANT", "ExactWithdrawal")]
    if property_name is not None:
        laws.append(("PROPERTY", property_name))
    check_tla(ROOT, "Eligibility", name, "Spec" if property_name is None else "Fair",
              constants, laws, expected=expected)


def verify_tla():
    for variant in ("trust-ticket", "match-id-only", "leave-grant"):
        check(variant, variant=variant, expected="GrantHasEnrollment")
    check("ignore-binding", variant="ignore-binding", expected="ExactWithdrawal")
    check("need-holder", variant="need-holder", scenario="retire-vacant",
          property_name="RetirementCompletes", expected="liveness")
    check("needs-new-serial", variant="needs-new-serial", scenario="exhausted",
          property_name="RetirementCompletes", expected="liveness")
    check("race")
    check("retire-vacant", scenario="retire-vacant", property_name="RetirementCompletes")
    check("exhausted", scenario="exhausted", property_name="RetirementCompletes")
    check("unrelated-churn", scenario="unrelated-churn",
          property_name="UnrelatedChangesKeepNominationLive")


def verify_lean():
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean"))
    check_lean_theorems(ROOT, command, ROOT / "OrderedEligibility.lean", count=12)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
