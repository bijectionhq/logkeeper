#!/usr/bin/env python3
"""Check the bounded selective read admission and compaction laws."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, compile_lean_modules


def main():
    command = compile_lean_modules(ROOT, ())
    source = ROOT / "SelectiveReadWindow.lean"
    check_lean_mutation(ROOT, command, source, "compact-an-unresolved-head",
                        [("  | compact {before} (head : Spent before (before.floor + 1)) :",
                          "  | compact {before} (head : True) :")],
                        "      have same := compacting_one_resolved_head_preserves_all_spent_identities _ head")
    check_lean_theorems(ROOT, command, source, count=9)


if __name__ == "__main__":
    main()
