#!/usr/bin/env python3
"""Check the composed reducer model and its negative controls."""

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
    reducer = ROOT / "Logkeeper/Reducer.lean"
    check_lean_theorems(ROOT, command, reducer, count=18, case="reducer-refinement")
    check_lean_mutation(
        ROOT, command, reducer, "reducer-keeps-append-head",
        [("head := next }", "head := history.head }"),
         ("(record : Record) (next : Nat)", "(record : Record) (_next : Nat)")],
        "  rfl\n\ntheorem funding_resets_spend",
    )
    check_lean_mutation(
        ROOT, command, reducer, "reducer-keeps-vacated-holder",
        [("  ErasureCommit.vacate authority", "  authority")],
        "  rfl\n\ntheorem a_cached_barrier_refuses",
    )
    check_lean_mutation(
        ROOT, command, reducer, "reducer-replays-barrier",
        [("  (replay r.command.isBarrier retained.fingerprint", "  (replay false retained.fingerprint")],
        "  rw [reading, Protocol.Ordered.barriers_never_replay]",
    )

    check_lean_mutation(
        ROOT, command, reducer, "reducer-keeps-disposed-holds",
        [("(holds id).filter (·.owner != owner)", "(holds id).filter (·.owner == owner)")],
        "      simpa [removesOwner, found] using present",
    )


if __name__ == "__main__":
    main()
