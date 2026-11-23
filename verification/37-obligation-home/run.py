#!/usr/bin/env python3
"""Check stable discovery, fenced custody transfer, and teardown."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

CONTENT = ("ExactUnresolvedBook", "ChargeMatchesOutstanding", "OnlyExactSettlement",
           "PublishedIsInstalled", "CurrentOwnerSurvives")
SAFETY = (*CONTENT, "LocatorSurvivesShutdown", "NoFalseTerminalAbsence")
TEMPORAL = {"InstallsSealedCut", "CanShutDownPredecessors", "EventuallyDischarges",
            "ReconcilesAfterShutdown"}


def check(name, laws, *, sites=3, policy="stable", variant="reference", scenario="general", expected=None):
    constants = {"Sites": sites, "Policy": f'"{policy}"', "Variant": f'"{variant}"',
                 "Scenario": f'"{scenario}"'}
    spec = "Fair" if any(law in TEMPORAL for law in laws) else "Spec"
    checks = tuple(("PROPERTY" if law in TEMPORAL else "INVARIANT", law) for law in laws)
    check_tla(ROOT, "ObligationHome", name, spec, constants, checks, expected=expected)


def verify_tla():
    for variant, law in (
        ("omit_result", "ExactUnresolvedBook"),
        ("omit_plan", "ExactUnresolvedBook"),
        ("rebind_plan", "ExactUnresolvedBook"),
        ("stale_image", "ExactUnresolvedBook"),
        ("post_seal_discharge", "ExactUnresolvedBook"),
        ("forget_charge", "ChargeMatchesOutstanding"),
        ("assume_settled", "OnlyExactSettlement"),
        ("publish_before_install", "PublishedIsInstalled"),
        ("regress_locator", "LocatorSurvivesShutdown"),
        ("stop_before_publish", "LocatorSurvivesShutdown"),
        ("stale_is_missing", "NoFalseTerminalAbsence"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)

    check("control-forwarder-shutdown", ("EventuallyDischarges",), policy="forward", expected="liveness")
    check("control-hold-forwarders", ("CanShutDownPredecessors",), policy="hold_forwarders",
          scenario="debt_endpoints_down", expected="liveness")
    check("control-locator-unavailable", ("CanShutDownPredecessors",),
          scenario="locator_down", expected="liveness")
    complete = (("PROPERTY", "Complete"),)
    check_tla(ROOT, "DiscoveryChurn", "control-weak-fairness-under-churn",
              "WeakDelivery", {}, complete, expected="liveness")
    check_tla(ROOT, "DiscoveryChurn", "delivery-fairness-under-churn",
              "FairDelivery", {}, complete)

    for sites in (2, 4):
        check(f"stable-{sites}", (*SAFETY, "InstallsSealedCut", "CanShutDownPredecessors", "EventuallyDischarges"),
              sites=sites)
    check("stable-observers-unreachable", (*SAFETY, "InstallsSealedCut", "CanShutDownPredecessors"),
          sites=4, scenario="debt_endpoints_down")
    check("stable-reconnect-after-shutdown",
          (*SAFETY, "InstallsSealedCut", "CanShutDownPredecessors", "ReconcilesAfterShutdown"),
          sites=4, scenario="reconnect_after_shutdown")
    check("stable-locator-unavailable", (*SAFETY, "InstallsSealedCut"), scenario="locator_down")
    check("forward-only-safety", (*CONTENT, "InstallsSealedCut", "CanShutDownPredecessors"), policy="forward")
    check("hold-forwarders-reachable", (*CONTENT, "InstallsSealedCut", "CanShutDownPredecessors", "EventuallyDischarges"),
          policy="hold_forwarders")
    after_shutdown = "NeverSettlesAfterAllPredecessorsStop"
    check("witness-reconcile-after-three-moves", (after_shutdown,), sites=4, scenario="reconnect_after_shutdown",
          expected=after_shutdown)
    still_owed = "NeverLeavesBothDebtsAtLastOwner"
    check("witness-old-endpoints-off-during-outages", (still_owed,), sites=4, scenario="debt_endpoints_down",
          expected=still_owed)


def verify_lean():
    command = compile_lean_modules(ROOT, ())
    source = ROOT / "ObligationHome.lean"
    check_lean_mutation(ROOT, command, source, "allow-non-exact-image",
        (("def ExactImage (state : Home Key Binding) (image : Key → Obligation Binding) : Prop :=\n"
          "  image = state.book",
          "def ExactImage (_state : Home Key Binding) (_image : Key → Obligation Binding) : Prop := True"),),
        "exact exactImage")
    check_lean_mutation(ROOT, command, source, "settle-without-authenticated-evidence",
        (("def ValidSettlement (settled : Key → Binding → Prop) (key : Key) (binding : Binding) : Prop :=\n"
          "  settled key binding",
          "def ValidSettlement (_settled : Key → Binding → Prop) (_key : Key) (_binding : Binding) : Prop := True"),),
        "exact proof")
    check_lean_mutation(ROOT, command, source, "stop-without-independent-route",
        (("  site < state.owner ∧ site < state.locator", "  site < state.owner ∧ site < state.owner"),),
        "exact same ▸ covered.2")
    check_lean_mutation(ROOT, command, source, "assume-result-visible-during-outage",
        (("def RecoveryObservation (result : Binding) (resolved : Bool) : Option Binding :=\n"
          "  if resolved then some result else none",
          "def RecoveryObservation (result : Binding) (_resolved : Bool) : Option Binding := some result"),),
        "rfl\n  rw [noEvidence]")
    check_lean_theorems(ROOT, command, source, count=13)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
