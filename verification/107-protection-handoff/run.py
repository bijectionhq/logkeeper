#!/usr/bin/env python3
"""Check fault protection across journal transfer and physical withdrawal."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def move(name, scenario, *, policy="carry", law=None, progress=False, expected=None):
    constants = {"Scenario": f'"{scenario}"', "Policy": f'"{policy}"'}
    laws = (law,) if law else ("KeepsInterval", "LeavesNeighbor", "Survives")
    checks = [("INVARIANT", key) for key in laws]
    if progress:
        checks.append(("PROPERTY", "ServesExistingInterval"))
    check_tla(ROOT, "ProtectionMove", name, "Fair" if progress else "Spec",
              constants, checks, expected=expected)


def withdrawal(name, layout, *, policy="reserve", law=None, expected=None):
    constants = {"Layout": f'"{layout}"', "Policy": f'"{policy}"'}
    laws = (law,) if law else ("StillProtected", "HasWitnesses", "ActualSurvivor")
    check_tla(ROOT, "ConcurrentWithdrawal", name, "Spec", constants,
              [("INVARIANT", key) for key in laws], expected=expected)


def verify_tla():
    move("reset-a-spent-interval", "spent", policy="reset-interval", law="KeepsInterval",
         expected="KeepsInterval")
    move("same-data-rival-protection", "rival-control", policy="match-data-only", law="KeepsInterval",
         expected="KeepsInterval")
    move("source-needed-after-seal", "spent", policy="recontact-source", progress=True,
         expected="liveness")
    move("move-must-renew-in-advance", "spent", policy="healthy-gate", progress=True,
         expected="liveness")
    move("move-overwrites-neighbor", "spent", policy="overwrite-neighbor", law="LeavesNeighbor",
         expected="LeavesNeighbor")
    move("activate-then-drop-the-only-independent-copy", "withdrawal", policy="release-on-activation",
         law="Survives", expected="Survives")
    withdrawal("two-old-coverage-checks-lose-data", "separate", policy="independent-check",
               law="ActualSurvivor", expected="ActualSurvivor")
    withdrawal("two-replicas-in-one-zone-do-not-count", "same-zone", policy="count-copies",
               law="ActualSurvivor", expected="ActualSurvivor")
    withdrawal("delayed-effect-removes-replacement", "key-reuse", policy="delete-by-address",
               law="HasWitnesses", expected="HasWitnesses")

    move("carry-known-loss-while-source-offline", "spent", progress=True)
    move("accept-confirmation-of-loss-across-handoff", "arriving-loss", progress=True)
    move("refuse-rival-interval-at-same-data-frontier", "rival-control")
    move("activate-with-original-custody", "withdrawal")
    move("copy-then-release-and-survive-witness", "withdrawal", law="NeverSafelyReleases",
         expected="NeverSafelyReleases")
    withdrawal("reserve-against-pending-withdrawal", "separate")
    withdrawal("refuse-same-domain-replacement", "same-zone")
    withdrawal("late-effect-keeps-new-version", "key-reuse")
    withdrawal("authorized-effect-completes-witness", "separate", law="NeverCompletesWithdrawal",
               expected="NeverCompletesWithdrawal")


def verify_lean():
    deps = (
        "07-reference/Kernel.lean",
        "06-generations/Reservation.lean",
        "11-authority-refinement/AuthorityRefinement.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "13-install-durability/DurableInstall.lean",
        "26-journal-rotation/JournalRotation.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "27-prefix-consensus/DurableAcceptor.lean",
        "32-configuration-closure/ConfigurationClosure.lean",
        "105-service-scope-protection/ScopeProtection.lean",
        "106-ordered-fault-interval/OrderedFaultInterval.lean",
    )
    command = compile_lean_modules(ROOT, deps)
    source = ROOT / "ProtectionHandoff.lean"
    check_lean_mutation(ROOT, command, source, "omit-sealed-interval",
                        [("frozen.image.interval = mounted.image.interval ∧ frozen.owed",
                          "frozen.image.interval = frozen.image.interval ∧ frozen.owed")],
                        "  exact exact.2.1")
    check_lean_theorems(ROOT, command, source, count=6, case="lean-handoff")
    compile_lean_modules(ROOT, ("107-protection-handoff/ProtectionHandoff.lean",))
    source = ROOT / "CoverageWithdrawal.lean"
    check_lean_mutation(ROOT, command, source, "allow-an-unissued-effect",
                        [("def Issued (state : State Input Copy) (removed : Copy) : Prop :=\n  state.pending removed",
                          "def Issued (_state : State Input Copy) (_removed : Copy) : Prop := True")],
                        "  safe.excl input removed issued")
    check_lean_theorems(ROOT, command, source, count=6, case="lean-withdrawal")


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
