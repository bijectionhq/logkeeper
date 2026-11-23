#!/usr/bin/env python3
"""Check replay admission across object custody, stream moves, and expiry."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_tla

LAWS = ("NoPartialSnapshot", "OpenRangeAvailable", "FinishedReleasesBoth")


def check(name, laws, *, mutation="none", expected=None):
    constants = {"Mutation": f'"{mutation}"'}
    check_tla(ROOT, "ReplayHandoff", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def main():
    for mutation in ("unprotected_objects", "forget_replay_hold", "expire_before_drain"):
        law = "OpenRangeAvailable"
        check(f"control-{mutation}", (law,), mutation=mutation, expected=law)
    check("baseline", LAWS)
    for law in ("NeverContinuesAndCloses", "NeverRejectsAndReleases"):
        check(f"witness-{law}", (law,), expected=law)


if __name__ == "__main__":
    main()
