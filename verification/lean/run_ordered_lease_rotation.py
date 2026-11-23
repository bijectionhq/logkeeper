#!/usr/bin/env python3
"""Check the serving lease and erasure rotation reference laws and controls."""

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
    lease = ROOT / "Logkeeper/DisposalLease.lean"
    erasure = ROOT / "Logkeeper/ErasureCommit.lean"
    check_lean_theorems(ROOT, command, lease, count=6, case="ordered-serving-lease")
    check_lean_theorems(ROOT, command, erasure, count=9, case="ordered-rotation")
    controls = [
        (lease, "decision-time-rewinds",
         "  if previous ≤ incoming then some incoming else none",
         "  if previous ≤ incoming then some incoming else some incoming",
         "old ≤ applied ∧ applied = incoming := by"),
        (lease, "lease-without-roster",
         "  if authorize_writer principal current grant && decide (enrolled = some grant.1) &&",
         "  if authorize_writer principal current grant && decide (enrolled = enrolled) &&",
         "time = now + duration := by"),
        (lease, "disposal-skips-drift",
         "  | some time => if time + drift ≤ maxTime then some (time + drift) else none",
         "  | some time => if time + drift ≤ maxTime then some time else none",
         "  · simpa [MayDispose, disposal_time, bounded] using accepted.2"),
        (lease, "allow-underfilled-model-page",
         "      page.length = limit ∧ ∀ listed ∈ page, listed < owner)",
         "      page.length ≤ limit ∧ ∀ listed ∈ page, listed < owner)",
         "  exactPage.2.2.2 owner qualifies omitted"),
        (lease, "grant-drops-holds",
         "  | some entry => entry :: holds",
         "  | some entry => [entry]",
         "entry ∈ grant_holds holds newHold := by"),
        (erasure, "erasure-commit-without-fence",
         "∀ image ∈ selectable, ∀ generation ∈ image.suffix, image.root ≤ generation",
         "∀ image ∈ selectable, ∀ generation ∈ image.suffix, 0 ≤ generation ∧ image.root = image.root",
         "    Nat.lt_of_lt_of_le (commit image member) (fenced image member generation listed)"),
        (erasure, "rotation-without-head",
         "current = some grant ∧ head = requestedCut ∧ published ≠ requested)",
         "current = some grant ∧ head = head ∧ requestedCut = requestedCut ∧ published ≠ requested)",
         "  simpa [rotation_head, Bool.and_eq_true] using accepted"),
        (erasure, "rotation-without-prepared-root",
         "manifestPresent && decide (preparedCut = cut ∧ preparedRoot = root ∧",
         "manifestPresent && decide (preparedCut = cut ∧ preparedRoot = preparedRoot ∧ root = root ∧",
         "  exact (by simpa [exact_preparation, Bool.and_eq_true] using accepted :"),
        (erasure, "publish-leaves-old-history-open",
         "  if closesHistory then chosenCut else previous",
         "  if closesHistory && decide (chosenCut = chosenCut) then previous else previous",
         "  exact decide_eq_false (Nat.not_le_of_lt older)"),
    ]
    for source, name, original, change, failure in controls:
        check_lean_mutation(ROOT, command, source, name, [(original, change)], failure)


if __name__ == "__main__":
    main()
