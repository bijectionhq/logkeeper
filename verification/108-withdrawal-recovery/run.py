#!/usr/bin/env python3
"""Verify exact copy withdrawal through crash recovery and provider settlement."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def compare(name, scenario, *, policy="ordered", law=None, progress=False, expected=None):
    constants = {"Scenario": f'"{scenario}"', "Policy": f'"{policy}"'}
    laws = (law,) if law else ("ExactReplay", "ExactHolds", "AuthorizedEffect",
                               "ChargedUntilAbsent", "SurvivesB")
    checks = [("INVARIANT", key) for key in laws]
    if progress:
        checks.append(("PROPERTY", "EventuallySettled"))
    check_tla(ROOT, "WithdrawalRecovery", name, "Fair" if progress else "Spec",
              constants, checks, expected=expected)


def verify_tla():
    compare("old-root-still-needs-the-copy", "settlement", policy="visible-only",
            law="ExactHolds", expected="ExactHolds")
    compare("closed-read-does-not-finish-delivery", "pinned-delivery", policy="drop-delivery",
            law="ExactHolds", expected="ExactHolds")
    compare("staging-must-not-mint-a-delete", "staging", policy="send-staged",
            law="AuthorizedEffect", expected="AuthorizedEffect")
    compare("crash-chooses-then-forgets-the-old-suffix", "recovery-race", policy="base-only",
            law="ExactReplay", expected="ExactReplay")
    compare("scan-cannot-find-pending-authorizations", "recovery-race", policy="scan-physical",
            law="SurvivesB", expected="SurvivesB")
    compare("probe-does-not-release-charge", "settlement", policy="probe-is-receipt",
            law="ChargedUntilAbsent", expected="ChargedUntilAbsent")
    compare("effect-waits-for-original-authority", "offline-effect", policy="needs-live-authority",
            progress=True, expected="liveness")

    compare("recovery-keeps-withdrawal-excluded", "recovery-race")
    compare("effect-and-settlement-survive-crash", "offline-effect", progress=True)
    compare("held-delivery-prevents-withdrawal", "pinned-delivery")
    compare("verified-terminal-settlement", "settlement", progress=True)
    compare("staging-is-invisible-for-effects", "staging")
    compare("settles-from-newer-selector-witness", "offline-effect", law="NeverSettlesFromNewerSelector",
            expected="NeverSettlesFromNewerSelector")
    compare("settles-from-older-selector-witness", "offline-effect", law="NeverSettlesFromOlderSelector",
            expected="NeverSettlesFromOlderSelector")


def verify_lean():
    deps = (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
        "26-journal-rotation/JournalRotation.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
        "105-service-scope-protection/ScopeProtection.lean",
    )
    command = compile_lean_modules(ROOT, deps)
    source = ROOT / "WithdrawalRecovery.lean"
    check_lean_mutation(ROOT, command, source, "accept-disposition-for-another-copy",
                        [("\n  receipt.version = version ∧ rules.authentic receipt ∧\n",
                          "\n  version = version ∧ rules.authentic receipt ∧\n")],
                        "  exact stable.1")
    check_lean_theorems(ROOT, command, source, count=13)


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
