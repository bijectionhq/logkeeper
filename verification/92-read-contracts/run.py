#!/usr/bin/env python3
"""Compare fresh observation with exact protected-read recovery."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def run(path, scenario, *, variant="reference", progress=None, invariant=None, expected=None):
    constants = {"Path": f'"{path}"', "Scenario": f'"{scenario}"', "Variant": f'"{variant}"'}
    laws = (invariant,) if invariant else (
        "OriginalAnswer", "FreshAnswer", "AdmittedUnderGate", "NoPostTerminal", "NoClosedReissue",
        "NoLogWriteForSplitObservation",
    )
    checks = [("INVARIANT", law) for law in laws]
    if progress:
        checks.append(("PROPERTY", progress))
    name = f"{path}-{scenario}-{variant}"
    check_tla(ROOT, "ReadContracts", name, "Fair" if progress else "Spec", constants, checks, expected=expected)


def verify_tla():
    run("split", "terminal-before", variant="data-floor", invariant="NoPostTerminal", expected="NoPostTerminal")
    run("split", "gate-race", variant="cached-gate", invariant="AdmittedUnderGate", expected="AdmittedUnderGate")
    run("split", "scope-race", variant="stale-scope", invariant="AdmittedUnderGate", expected="AdmittedUnderGate")
    run("volatile", "lost-exact", variant="exact-as-fresh", invariant="OriginalAnswer", expected="OriginalAnswer")
    run("split", "close-reissue", variant="probe-allows-closed", invariant="NoClosedReissue", expected="NoClosedReissue")
    run("split", "lost-exact", variant="lose-handle", progress="OldAnswer", expected="liveness")
    run("split", "lose-after-admit", variant="recontact", progress="OldAnswer", expected="liveness")

    for path in ("ordered", "split"):
        run(path, "lost-fresh", progress="NewAnswer")
        run(path, "lost-exact", progress="OldAnswer")
    for scenario in ("terminal-before", "gate-race", "scope-race", "close-reissue"):
        run("split", scenario, progress="Refusal")
    run("split", "overlap")
    run("split", "lose-after-admit", progress="OldAnswer")


def verify_lean():
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "29-read-index/ReadIndexProof.lean",
                                        "30-reconfigured-reads/ReconfiguredReads.lean",
                                        "31-standing-custody/StandingCustody.lean",
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean",
                                        "79-rtdb-failover/RTDBFailover.lean",
                                        "80-applied-barrier-receipt/AppliedBarrierReceipt.lean",
                                        "81-recoverable-read-admission/RecoverableRead.lean",
                                        "82-joint-read-recovery/JointReadRecovery.lean",
                                        "83-ordered-read-replay/ReadInvocationFloor.lean",
                                        "83-ordered-read-replay/OrderedReadReplay.lean",
                                        "88-retained-delivery/DeliveryBook.lean",
                                        "88-retained-delivery/RetainedDelivery.lean"))
    source = ROOT / "ReadContracts.lean"
    check_lean_mutation(ROOT, command, source, "ignore-gate-session",
                        [("  session : state.currentSession = window.session",
                          "  session : True")],
                        "  exact admitted.session")
    check_lean_theorems(ROOT, command, source, count=10)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
