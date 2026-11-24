#!/usr/bin/env python3
"""Audit ordered reducer theorems and run the writer and receipt controls."""

import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems


def main():
    lake = os.environ.get("LAKE_BIN", str(Path.home() / ".elan/bin/lake"))
    subprocess.run([lake, "build"], cwd=ROOT, check=True, stdout=subprocess.DEVNULL)
    command = [lake, "env", "lean"]
    writer = ROOT / "Logkeeper/OrderedWriter.lean"
    receipt = ROOT / "Logkeeper/OrderedReceipt.lean"
    check_lean_theorems(ROOT, command, writer, count=9, case="ordered-writer")
    check_lean_theorems(ROOT, command, receipt, count=9, case="ordered-receipt")
    check_lean_theorems(ROOT, command, ROOT / "Logkeeper/OrderedGuards.lean",
                        count=8, case="ordered-guards")
    check_lean_theorems(ROOT, command, ROOT / "Logkeeper/OrderedBudgets.lean",
                        count=9, case="ordered-budgets")
    check_lean_mutation(
        ROOT, command, writer, "trim-extra-record",
        [("records := image.records.drop count", "records := image.records.drop (count + 1)")],
        "  have same : (abstract_state (trimImage image count)).history",
    )
    check_lean_mutation(
        ROOT, command, writer, "skip-next-lsn",
        [("  if head = expected ∧ expected < limit then", "  if head ≤ expected ∧ expected < limit then")],
        "    expected = head ∧ next = head + 1 := by",
    )
    check_lean_mutation(
        ROOT, command, receipt, "record-refused-barrier",
        [("    | .error _ => false", "    | .error _ => true")],
        "  rfl\n\ntheorem reissued_append_identifies_chosen_append",
    )


if __name__ == "__main__":
    main()
