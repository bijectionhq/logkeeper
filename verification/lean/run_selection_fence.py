#!/usr/bin/env python3
"""Check the shared selection theorem and the legacy one-slot control."""

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
    source = ROOT / "Logkeeper" / "SelectionFence.lean"
    check_lean_theorems(ROOT, command, source, count=6, case="selection-fence")
    control = ROOT / ".results" / "SelectionFenceControl.lean"
    control.write_text(
        source.read_text(encoding="utf-8").split("theorem a_torn_slot_cannot", 1)[0]
        + "end Logkeeper.SelectionFence\n",
        encoding="utf-8",
    )
    check_lean_mutation(
        ROOT, command, control, "acknowledge-only-selected",
        [("fun _ => some image", "fun slot => if slot then some image else some ⟨0, none⟩")],
        "      have equal : ack = image",
    )


if __name__ == "__main__":
    main()
