#!/usr/bin/env python3
"""Check grant-wide read policy, exact historical width and replay."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def compare(name, scenario, *, variant="reference", law=None, expected=None):
    constants = {"Scenario": f'"{scenario}"', "Variant": f'"{variant}"'}
    laws = (law,) if law else ("ExactWidth", "NoDuplicate", "CurrentGrantAuthorized", "OldUsePersists")
    checks = [("INVARIANT", key) for key in laws]
    if not law:
        checks.append(("PROPERTY", "Progress"))
    check_tla(ROOT, "GrantReadPolicy", name, "Spec" if law else "Fair", constants, checks, expected=expected)


def verify_tla():
    compare("accept-equal-packed-size", "alias", variant="trust-packed-size",
            law="ExactWidth", expected="ExactWidth")
    compare("change-width-inside-grant", "trim", variant="shrink-live-window",
            law="NoDuplicate", expected="NoDuplicate")
    compare("substitute-foreign-grant", "foreign-offer", variant="trust-other-grant",
            law="CurrentGrantAuthorized", expected="CurrentGrantAuthorized")
    compare("forget-old-delivery", "successor", variant="forget-old-delivery",
            law="OldUsePersists", expected="OldUsePersists")
    compare("latest-width-for-old-selector", "old-selector", variant="latest-policy-opens-old", expected="liveness")
    compare("read-requires-unreachable-offer", "no-offer", variant="policy-needed-on-every-call", expected="liveness")
    compare("replacement-requires-unreachable-offer", "failover-without-offer", variant="replacement-requires-offer",
            expected="liveness")
    for scenario in ("alias", "trim", "successor", "old-selector", "foreign-offer", "no-offer", "failover-without-offer"):
        compare(scenario, scenario)


def verify_lean():
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean",
                                        "79-rtdb-failover/RTDBFailover.lean",
                                        "80-applied-barrier-receipt/AppliedBarrierReceipt.lean",
                                        "81-recoverable-read-admission/RecoverableRead.lean",
                                        "82-joint-read-recovery/JointReadRecovery.lean",
                                        "83-ordered-read-replay/ReadInvocationFloor.lean",
                                        "83-ordered-read-replay/OrderedReadReplay.lean",
                                        "84-read-invocation-floor/InvocationFloorProof.lean",
                                        "88-retained-delivery/DeliveryBook.lean",
                                        "88-retained-delivery/RetainedDelivery.lean",
                                        "88-retained-delivery/DeliveryRecovery.lean",
                                        "101-selective-read-window/SelectiveReadWindow.lean",
                                        "102-selective-ordered-recovery/SelectiveOrderedRecovery.lean",
                                        "102-selective-ordered-recovery/SelectiveCheckpoint.lean"))
    source = ROOT / "GrantReadPolicy.lean"
    check_lean_mutation(ROOT, command, source, "accept-equal-width",
                        [("  authenticated = expected\n\ntheorem",
                          "  authenticated.horizon = expected.horizon\n\ntheorem")],
                        "  exact checked")
    check_lean_theorems(ROOT, command, source, count=13)


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
