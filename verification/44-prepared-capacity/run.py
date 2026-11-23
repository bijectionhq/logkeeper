#!/usr/bin/env python3
"""Check prepared capacity's accounting and admission observations."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, compile_lean_modules


if __name__ == "__main__":
    command = compile_lean_modules(ROOT, ())
    source = ROOT / "PreparedCapacity.lean"
    check_lean_mutation(ROOT, command, source, "attribute-without-transferring",
        (("prepared := fun pool => book.prepared pool - held pool",
          "prepared := book.prepared"),), "omega")
    check_lean_theorems(ROOT, command, source, count=5)
