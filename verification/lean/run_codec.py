#!/usr/bin/env python3
"""Build the codec references, audit their axioms, and check weakened premises."""

import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems


def main():
    lake = os.environ.get("LAKE_BIN", "lake")
    subprocess.run([lake, "build"], cwd=ROOT, check=True)
    command = [lake, "env", "lean"]
    codec = ROOT / "Logkeeper" / "Codec.lean"
    image = ROOT / "Logkeeper" / "CompactImage.lean"
    check_lean_theorems(ROOT, command, codec, count=7, case="codec")
    check_lean_theorems(ROOT, command, image, count=6, case="compact-image")
    check_lean_mutation(
        ROOT, command, codec, "codec-ignore-maximum",
        [("minimum ≤ declared ∧ declared ≤ maximum", "minimum ≤ declared ∧ True")],
        "    boundedBodyLength declared minimum maximum = none := by",
    )
    check_lean_mutation(
        ROOT, command, image, "compact-image-vacancy-resets-generation",
        [("{ writer with holder := none }", "{ writer with holder := none, keyGeneration := 1 }")],
        "  rfl\n",
    )
    check_lean_mutation(
        ROOT, command, image, "compact-image-accept-missing-receipt",
        [("receiptPosition = some admittedAt", "receiptPosition = some admittedAt ∨ receiptPosition = none")],
        "  exact ⟨row.1, checked row member, rfl⟩",
    )


if __name__ == "__main__":
    main()
