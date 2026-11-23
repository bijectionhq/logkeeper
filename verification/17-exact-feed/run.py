#!/usr/bin/env python3
"""Check the optional exact history-to-tail feed contract."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("ArchiveIsExact", "NoUncoveredTrim", "SuccessfulFeedIsExact")


def check(name, laws, *, mutation="none", expected=None, bound=3):
    constants = {"Mutation": f'"{mutation}"', "MaxLsn": bound}
    check_tla(ROOT, "ExactFeed", name, "Spec", constants,
              tuple(("INVARIANT", law) for law in laws), expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, ())
    source = ROOT / "FeedComposition.lean"
    check_lean_mutation(ROOT, command, source, "stale-floor",
        (("(archiveCoversSeam : seam ≤ archiveEnd) (admitted : floor ≤ seam)",
          "(archiveCoversSeam : seam ≤ archiveEnd) (admitted : True)"),),
        "have activeFloor")
    check_lean_mutation(ROOT, command, source, "uncovered-trim",
        (("""{head floor archiveEnd capacity : Nat} (covered : floor ≤ archiveEnd)
    (boundedDebt""", """{head floor archiveEnd capacity : Nat} (covered : True)
    (boundedDebt"""),),
        "uncovered_archive_tail_lower_bounds_retained_debt covered")
    check_lean_mutation(ROOT, command, source, "replan-past-coverage",
        (("(archivedFloor : floor ≤ archiveEnd)", "(_archivedFloor : True)"),),
        "have journalGuard")
    check_lean_theorems(ROOT, command, source, count=10)


def main():
    verify_lean()
    for mutation, law in (
        ("archive_gap", "ArchiveIsExact"),
        ("checkpoint_only", "NoUncoveredTrim"),
        ("skip_recheck", "SuccessfulFeedIsExact"),
        ("duplicate_seam", "SuccessfulFeedIsExact"),
    ):
        check(f"control-{mutation}", (law,), mutation=mutation, expected=law)
    for bound in (2, 3):
        check(f"baseline-{bound}", LAWS, bound=bound)
    for law in ("NeverRefreshesAndCompletes", "NeverJoinsBothSources"):
        check(f"witness-{law}", (law,), expected=law)


if __name__ == "__main__":
    main()
