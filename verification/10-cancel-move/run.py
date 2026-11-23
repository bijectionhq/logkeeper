#!/usr/bin/env python3
"""Check abort versus seal ordering and destination slot reuse."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_tla

LAWS = ("SealAndAbortAreExclusive", "SealRetainsItsDestination")


def check(name, checks, *, mutation="none", expected=None, bound=2):
    constants = {"Mutation": f'"{mutation}"', "MaxNonce": bound}
    check_tla(ROOT, "CancelMove", name, "FairSpec", constants, checks, expected=expected)


def main():
    for mutation, law in (
        ("ignore_abort", "SealAndAbortAreExclusive"),
        ("abort_by_stream", "SealRetainsItsDestination"),
        ("no_source_evidence", "SealRetainsItsDestination"),
    ):
        check(f"control-{mutation}", (("INVARIANT", law),), mutation=mutation, expected=law)
    checks = tuple(("INVARIANT", law) for law in LAWS) + (("PROPERTY", "RequestedReleaseWithSource"),)
    for bound in (2, 4):
        check(f"baseline-{bound}", checks, bound=bound)
    check("source-partition", (("PROPERTY", "RequestedReleaseWithoutSource"),), expected="liveness")
    law = "NeverCancelsThenInstallsNew"
    check("witness-reuse", (("INVARIANT", law),), expected=law)


if __name__ == "__main__":
    main()
