#!/usr/bin/env python3
"""Check the runtime group reference and its negative controls."""

import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems


def main():
    command = [os.environ.get("LAKE_BIN", "lake"), "env", "lean"]
    source = ROOT / "Logkeeper" / "RuntimeGroups.lean"
    check_lean_theorems(ROOT, command, source, count=6, case="runtime-groups")
    for name, old, new, failure in [
        ("conflicting-install", "| some false => .refuse", "| some false => .alreadyInstalled", ".refuse := by rfl"),
        ("unpersisted-serving", "persisted && !retired", "!retired", "mayServe false retired = false := by rfl"),
        ("skip-final-checkpoint", "head = final ∧ vacant", "True ∧ vacant",
         "  exact ⟨accepted.1, accepted.2.1⟩"),
        ("late-seal", "chosen = observed + 1\n", "observed + 1 ≤ chosen\n", "  omega"),
    ]:
        check_lean_mutation(ROOT, command, source, name, [(old, new)], failure)


if __name__ == "__main__":
    main()
