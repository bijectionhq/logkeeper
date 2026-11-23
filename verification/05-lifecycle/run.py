#!/usr/bin/env python3
"""Check composition of a group move, custody transfer, and terminal retirement."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_tla

LAWS = (
    "OneAuthority", "ExactCut", "AcknowledgedRetirementIsTerminal",
    "NoPostRetirementCommit", "CompleteCoversCustody",
)


def check(name, invariants, *, mutation="none", expected=None, bound=2):
    constants = {"Mutation": f'"{mutation}"', "MaxLsn": bound}
    checks = tuple(("INVARIANT", law) for law in invariants)
    check_tla(ROOT, "Lifecycle", name, "Spec", constants, checks, expected=expected)


def main():
    for mutation, law in (
        ("seal_after_retire", "AcknowledgedRetirementIsTerminal"),
        ("sealed_claims_retired", "AcknowledgedRetirementIsTerminal"),
        ("sealed_claims_retired", "NoPostRetirementCommit"),
        ("forget_custody", "CompleteCoversCustody"),
    ):
        check(f"control-{mutation}-{law}", (law,), mutation=mutation, expected=law)
    for bound in (2, 3):
        check(f"baseline-{bound}", LAWS, bound=bound)
    for law in ("NeverRetiresAfterRedirect", "NeverRetiresBeforeSeal"):
        check(f"witness-{law}", (law,), expected=law)


if __name__ == "__main__":
    main()
