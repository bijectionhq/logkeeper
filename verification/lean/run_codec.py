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
    slot = ROOT / "Logkeeper" / "VoterSlotHeader.lean"
    transport = ROOT / "Logkeeper" / "VoterTransport.lean"
    check_lean_theorems(ROOT, command, codec, count=7, case="codec")
    check_lean_theorems(ROOT, command, image, count=8, case="compact-image")
    check_lean_theorems(ROOT, command, slot, count=4, case="voter-slot-header")
    check_lean_theorems(ROOT, command, transport, count=4, case="voter-transport")
    check_lean_mutation(
        ROOT, command, transport, "transport-ignore-installed-group",
        [("  group = authorized ∧ group = installed\n", "  group = authorized ∧ True\n")],
        "  exact accepted",
    )
    check_lean_mutation(
        ROOT, command, slot, "voter-slot-header-ignore-voter",
        [("header.voter = voter ∧", "True ∧")],
        "  rfl\n\nprivate theorem take_field",
    )
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
        ROOT, command, image, "compact-image-accept-torn-object-name",
        [("count ≤ maximum ∧ 32 * count ≤ remaining", "count ≤ maximum ∧ count ≤ remaining")],
        "  omega\n\ndef rootReferenceRowValid",
    )
    check_lean_mutation(
        ROOT, command, image, "compact-image-accept-unknown-root",
        [("known = true ∧ match previous with", "True ∧ match previous with")],
        "  accepted\n",
    )
    check_lean_mutation(
        ROOT, command, image, "compact-image-accept-missing-receipt",
        [("receiptPosition = some admittedAt", "receiptPosition = some admittedAt ∨ receiptPosition = none")],
        "  exact ⟨row.1, checked row member, rfl⟩",
    )


if __name__ == "__main__":
    main()
