#!/usr/bin/env python3
"""Check the consensus keeper's protocol additions and their controls."""

import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems


MODULES = {
    "RecoveryFence": 10, "Parking": 7, "RetireOnProof": 4, "CatalogClaim": 6,
    "EpochLease": 10, "OffloadPrefix": 11,
}

CONTROLS = [
    (
        "RecoveryFence", "answer-a-lost-voter",
        "      Step s w (if excludes true (s.recovered.contains keeper) (w keeper).term (w s.survivor).term\n        then w",
        "      Step s w (if false\n        then w",
        "      rw [survivor_excludes_lost_voters clean lost]",
    ),
    (
        "RecoveryFence", "unbounded-lost-elections",
        "      s.Lost keeper → (w keeper).term + 1 < s.term →\n",
        "      s.Lost keeper → (w keeper).term < s.term →\n",
        "      exact clean_set_lost clean lost ⟨by simp only; omega, old.2⟩",
    ),
    (
        "RecoveryFence", "exclude-newer-senders",
        "  configured && !known && decide (senderTerm < ownTerm)",
        "  configured && !known && decide (ownTerm < senderTerm)",
        "  exact decide_eq_true (by omega)",
    ),
    (
        "RecoveryFence", "confirm-a-stale-term",
        "decide ((w keeper).term ≤ (w serving).term))",
        "decide ((w keeper).term ≤ (w serving).term + gap))",
        "    cases (w s.survivor).online <;> simp <;> omega",
    ),
    (
        "RecoveryFence", "lead-without-the-recovery",
        "      keeper ∈ s.recovered → s.history <+: (w keeper).log → s.term ≤ (w keeper).term →",
        "      keeper ∈ s.recovered → (w keeper).log <+: (w keeper).log → s.term ≤ (w keeper).term →",
        "        (newWorld_append (clean.recoveredLogs keeper recovered) complete current)",
    ),
    (
        "Parking", "park-with-a-longer-log",
        "replica.log.length == lastIndex && replica.idle",
        "replica.log.length == replica.log.length && replica.idle",
        "  have length : replica.log.length = leader.applied := sameLength",
    ),
    (
        "Parking", "park-truncates",
        "      Step w (w.set keeper { w keeper with parked := true })\n  /-- The leader",
        "      Step w (w.set keeper { w keeper with parked := true, log := (w keeper).log.take (w keeper).applied })\n  /-- The leader",
        "  | accept changed => by_cases",
    ),
    (
        "RetireOnProof", "retire-a-joint-target",
        "    (proof.joint.any (fun target => target.contains keeper))",
        "    false",
        "      rw [target] at joint",
    ),
    (
        "RetireOnProof", "retire-a-restaged-copy",
        "  if copy.generation = generation ∧ retires proof keeper revision = true then",
        "  if copy.generation ≤ generation + 1 ∧ retires proof keeper revision = true then",
        "    (copy.stage.retire copy.generation proof keeper revision).detached = false := by",
    ),
    (
        "EpochLease", "act-as-the-wait-out-ends",
        "  ∀ lost member t u, g.lostActs lost t → g.newActs member u → t < u",
        "  ∀ lost member t u, g.lostActs lost t → g.newActs member u → t ≤ u",
        "  exact Nat.lt_irrefl u (Nat.lt_of_le_of_lt past before)",
    ),
    (
        "EpochLease", "margin-below-drift",
        "    {holder waiter : Clock D H} (margin : D ≤ M) (horizon : L + M + D ≤ H)",
        "    {holder waiter : Clock D H} (margin : D ≤ M + 1) (horizon : L + M + D ≤ H)",
        "  omega -- the lease ends before the wait-out",
    ),
    (
        "EpochLease", "read-without-a-lease",
        "      s.Lost keeper → g.lostActs keeper st.time →\n      Step s g st (observe",
        "      s.Lost keeper → True →\n      Step s g st (observe",
        "  | lostRead keeper _ lost acts => exact absurd ⟨lost, acts⟩ (closed keeper)",
    ),
    (
        "EpochLease", "lost-voter-writes-the-recovery",
        "      s.Lost keeper → g.lostActs keeper st.time → entry ≠ s.recovery →",
        "      s.Lost keeper → g.lostActs keeper st.time → True →",
        "        have grown := recFree_append (untouched_lost before lost) distinct",
    ),
    (
        "OffloadPrefix", "upload-unapplied-records",
        "      o.through + count ≤ o.applied →",
        "      o.through + count ≤ o.committed.length →",
        "      refine ⟨by simp; omega, within, appliedCommitted,",
    ),
    (
        "OffloadPrefix", "restore-the-whole-survivor-log",
        "  if o.through ≤ survivor.commit then (survivor.log.take survivor.commit).drop o.floor",
        "  if o.through ≤ survivor.commit then survivor.log.drop o.floor",
        "    · next covers =>\n        rw [Nat.max_eq_right covers]",
    ),
    (
        "CatalogClaim", "reply-with-the-proposal",
        "  (catalog stream).getD genesis",
        "  ((catalog stream).map (fun _ => genesis)).getD genesis",
        "    | some held => simp [apply, current]",
    ),
]


def main():
    lake = os.environ.get("LAKE_BIN", "lake")
    subprocess.run([lake, "build"], cwd=ROOT, check=True)
    command = [lake, "env", "lean"]
    directory = ROOT / "Logkeeper" / "ConsensusAdditions"
    for module, count in MODULES.items():
        check_lean_theorems(
            ROOT, command, directory / f"{module}.lean", count=count,
            case=f"consensus-additions-{module}",
        )
    for module, name, old, new, failure in CONTROLS:
        check_lean_mutation(
            ROOT, command, directory / f"{module}.lean", f"consensus-additions-{name}",
            [(old, new)], failure,
        )


if __name__ == "__main__":
    main()
