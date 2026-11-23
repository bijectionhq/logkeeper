#!/usr/bin/env python3
"""Check the ordered admission reference and its four negative controls."""

import os
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems


def main():
    command = [os.environ.get("LAKE_BIN", "lake"), "env", "lean"]
    source = ROOT / "Logkeeper" / "OrderedAdmission.lean"
    check_lean_theorems(ROOT, command, source, count=4, case="ordered-admission")
    for name, old, new, failure in [
        (
            "reject-exact-reserve",
            "if used + charge ≤ ceiling",
            "if used + charge < ceiling",
            "  · exact ite_eq_left funded",
        ),
        (
            "pin-at-floor",
            "start < stop ∧ start < floor",
            "start < stop ∧ start ≤ floor",
            "    exact ⟨start, Nat.le_refl _, pins.1, pins.2⟩",
        ),
        (
            "keep-at-expiry",
            "position < expiresAt ∨",
            "position ≤ expiresAt ∨",
            "    retainsReceipt position position ownsLiveHold ↔ ownsLiveHold = true := by",
        ),
        (
            "compare-only-lengths",
            "  stored = presented\n",
            "  stored.length = presented.length\n",
            "  exact different",
        ),
    ]:
        check_lean_mutation(ROOT, command, source, f"ordered-admission-{name}", [(old, new)], failure)


if __name__ == "__main__":
    main()
