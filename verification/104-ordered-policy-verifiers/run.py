#!/usr/bin/env python3
"""Check ordered policy verifier replacement and historical retention."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def compare(name, scenario, *, variant="reference", selector="old", law=None, expected=None):
    constants = {"Scenario": f'"{scenario}"', "Variant": f'"{variant}"', "Selector": f'"{selector}"'}
    laws = (law,) if law else ("NoNewFromRetired", "ExactSignedPolicy", "HeldAcrossSelectors", "ReplayExact")
    checks = [("INVARIANT", key) for key in laws]
    if not law:
        checks.append(("PROPERTY", "Progress"))
    check_tla(ROOT, "OrderedPolicyVerifiers", name, "Spec" if law else "Fair",
              constants, checks, expected=expected)


def verify_tla():
    compare("retired-key-authorizes-a-fresh-offer", "late-old", variant="trust-retired-key",
            law="NoNewFromRetired", expected="NoNewFromRetired")
    compare("different-width-outside-the-signature", "rival-offer", variant="trust-fields-outside-signature",
            law="ExactSignedPolicy", expected="ExactSignedPolicy")
    compare("collect-before-the-old-selector-retires", "historical", variant="collect-on-visible",
            law="HeldAcrossSelectors", expected="HeldAcrossSelectors")
    compare("skip-the-unverifiable-historical-offer", "historical", variant="skip-unverifiable",
            law="ReplayExact", expected="ReplayExact")
    compare("replay-using-the-live-verifier", "historical", variant="use-live-verifier", expected="liveness")
    compare("replay-needs-the-policy-service", "historical", variant="history-needs-policy-service", expected="liveness")
    compare("old-signer-needed-to-rotate", "historical", variant="rotate-needs-old-signer", expected="liveness")
    compare("older-selector", "historical")
    compare("newer-selector", "historical", selector="new")
    for scenario in ("new-offer", "late-old", "rival-offer"):
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
                                        "102-selective-ordered-recovery/SelectiveCheckpoint.lean",
                                        "103-grant-read-policy/GrantReadPolicy.lean"))
    wire = ROOT / "GrantPolicyWire.lean"
    check_lean_mutation(ROOT, command, wire, "allow-retired-version",
                        [("  seen = expected\n\ntheorem",
                          "  seen = seen ∧ expected = expected\n\ntheorem")],
                        "  exact current")
    check_lean_theorems(ROOT, command, wire, count=6, case="lean-wire")
    compile_lean_modules(ROOT, ("104-ordered-policy-verifiers/GrantPolicyWire.lean",))
    check_lean_theorems(ROOT, command, ROOT / "OrderedPolicyVerifiers.lean", count=8)


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
