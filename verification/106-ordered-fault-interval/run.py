#!/usr/bin/env python3
"""Verify the ordered AZ protection interval and its crash selectors."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules



def compare(name, scenario, *, policy="ordered", law=None, progress=False, expected=None):
    constants = {"Scenario": f'"{scenario}"', "Policy": f'"{policy}"'}
    laws = (law,) if law else ("ExactServing", "AcknowledgedInOriginalLoss", "ExactRenewal")
    checks = [("INVARIANT", key) for key in laws]
    if progress:
        checks.append(("PROPERTY", "EventuallyAck"))
    check_tla(ROOT, "FaultInterval", name, "Fair" if progress else "Spec",
              constants, checks, expected=expected)


def verify_tla():
    compare("old-checkpoint-forgets-confirmation", "recover-confirmation",
            policy="checkpoint-only", law="ExactServing", expected="ExactServing")
    compare("old-checkpoint-resurrects-confirmation", "recover-renewal",
            policy="checkpoint-only", law="AcknowledgedInOriginalLoss", expected="AcknowledgedInOriginalLoss")
    compare("fresh-recovery-depends-on-live-detector", "recover-confirmation",
            policy="requires-live-detector", progress=True, expected="liveness")
    compare("vote-replacement-forgets-interval", "new-majority",
            policy="reset-on-voters", law="ExactServing", expected="ExactServing")
    compare("late-confirmation-spends-new-interval", "late-confirmation",
            policy="ignore-interval", law="AcknowledgedInOriginalLoss", expected="AcknowledgedInOriginalLoss")
    for field in ("frontier", "voters", "custody"):
        compare(f"renewal-ignores-{field}", "renewal-race", policy=f"ignore-{field}",
                law="ExactRenewal", expected="ExactRenewal")

    compare("recover-confirmation-without-detector", "recover-confirmation", progress=True)
    compare("recover-confirmation-in-new-majority", "new-majority", progress=True)
    compare("recover-renewal-from-either-base", "recover-renewal")
    compare("reject-late-confirmation", "late-confirmation")
    compare("refresh-renewal-after-race", "renewal-race")
    compare("renew-after-repaired-obligation-witness", "renewal-race",
            law="NeverRenewAfterRepair", expected="NeverRenewAfterRepair")


def traffic(name, policy, *, uncovered=False, progress=False, expected=None):
    constants = {"Policy": f'"{policy}"', "AddUncovered": str(uncovered).upper()}
    checks = [("INVARIANT", "RenewalIsCovered")]
    if progress:
        checks.append(("PROPERTY", "EventuallyRenews"))
    check_tla(ROOT, "RenewalTraffic", name, "Fair" if progress else "Spec",
              constants, checks, expected=expected)


def verify_traffic():
    traffic("every-advance-invalidates-renewal", "exact-frontier", progress=True, expected="liveness")
    traffic("carry-cert-through-uncovered-write", "carry-everything", uncovered=True,
            expected="RenewalIsCovered")
    traffic("carry-cert-through-covered-traffic", "covered-deltas", progress=True)
    traffic("clear-cert-on-uncovered-write", "covered-deltas", uncovered=True)
    traffic("bounded-turn-for-ready-renewal", "reserve-ready-turn", progress=True)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "26-journal-rotation/JournalRotation.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "27-prefix-consensus/DurableAcceptor.lean",
        "32-configuration-closure/ConfigurationClosure.lean",
        "105-service-scope-protection/ScopeProtection.lean",
    ))
    source = ROOT / "OrderedFaultInterval.lean"
    check_lean_mutation(ROOT, command, source, "drop-incident-anchor",
                        [("ticket.start = before.interval.start\n\ndef SameRenewalBasis",
                          "ticket.start = ticket.start\n\ndef SameRenewalBasis")],
                        "    exact ⟨verified.1.1, verified.1.2, verified.2.1, verified.2.2, rfl⟩")
    check_lean_theorems(ROOT, command, source, count=12)


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
        verify_traffic()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
