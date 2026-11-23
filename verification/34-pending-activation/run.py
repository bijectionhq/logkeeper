#!/usr/bin/env python3
"""Check pending activation and historical command replay across target reconfiguration."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ("OneDecision", "RetainsOldChoice", "NewScopeCarriesExactBinding",
          "HasCurrentCopies", "PublishedHasDecision", "ServingHasCurrentDecision")
LIVENESS = {"EventuallyChanges", "EventuallyPublishes"}


def pending(name, laws, *, protocol="ordered", variant="reference", scenario="general", loss=0,
            temporal=False, expected=None):
    constants = {"Protocol": f'"{protocol}"', "Variant": f'"{variant}"',
                 "Scenario": f'"{scenario}"', "InitialLostZone": loss}
    check_tla(ROOT, "PendingActivation", name, "Fair" if temporal else "Spec", constants,
              tuple(("PROPERTY" if law in LIVENESS else "INVARIANT", law) for law in laws),
              expected=expected)


def history(name, law, *, variant="reference", bound=3, expected=None):
    constants = {"Variant": f'"{variant}"', "MaxCommands": bound}
    check_tla(ROOT, "HistoricalInstall", name, "Spec", constants, (("INVARIANT", law),),
              expected=expected)


def verify_tla():
    for variant, law, protocol in (
        ("learned_only", "RetainsOldChoice", "ordered"),
        ("learned_only", "OneDecision", "ordered"),
        ("forget_slot", "NewScopeCarriesExactBinding", "carry"),
        ("forget_slot", "OneDecision", "carry"),
        ("skip_install_copy", "HasCurrentCopies", "ordered"),
        ("stale_ready", "HasCurrentCopies", "carry"),
        ("publish_stale", "ServingHasCurrentDecision", "carry"),
    ):
        pending(f"control-{variant}-{law}", (law,), variant=variant, protocol=protocol, expected=law)
    pending("control-all-topology-waits-for-input", ("EventuallyChanges",), protocol="wait",
            scenario="unready", loss=1, temporal=True, expected="liveness")
    for variant, bound in (("replay_current_revision", 3), ("ignore_stage_revision", 4),
                           ("reuse_dead_ready", 3)):
        history(f"control-{variant}", "ReplayAgrees", variant=variant, bound=bound,
                expected="ReplayAgrees")
    history("control-replay-current-changes-result", "AppliedRepliesAgree",
            variant="replay_current_revision", expected="AppliedRepliesAgree")

    for protocol in ("ordered", "carry"):
        pending(f"{protocol}-general", SAFETY, protocol=protocol)
        pending(f"{protocol}-unready-changes", ("EventuallyChanges",), protocol=protocol,
                scenario="unready", loss=1, temporal=True)
        for loss in (1, 2, 3):
            pending(f"{protocol}-hidden-{loss}", ("EventuallyPublishes", *SAFETY), protocol=protocol,
                    scenario="hidden", loss=loss, temporal=True)
        law = "NeverMovesOnlyAccepted"
        pending(f"witness-{protocol}-transfers-an-accepted-command", (law,),
                protocol=protocol, expected=law)
        law = "NeverRecoversHiddenChoice"
        pending(f"witness-{protocol}-recovers-an-unreported-choice", (law,),
                protocol=protocol, scenario="settled_hidden", loss=1, expected=law)
    pending("wait-ready", ("EventuallyPublishes", *SAFETY), protocol="wait",
            scenario="ready", loss=1, temporal=True)
    pending("witness-order-repairs-before-materialization", ("NeverMovesUnready",),
            scenario="unready", loss=1, expected="NeverMovesUnready")
    history("historical-3", "ReplayAgrees", bound=3)
    history("historical-4", "ReplayAgrees", bound=4)
    for law in ("NeverAppliesOldChoiceAfterPhysicalChange", "NeverRefusesLaterStalePacket"):
        history(f"witness-{law}", law, expected=law)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "27-prefix-consensus/DurableAcceptor.lean",
        "32-configuration-closure/ConfigurationClosure.lean",
    ))
    source = ROOT / "PendingActivation.lean"
    check_lean_mutation(ROOT, command, source, "ignore-ordered-revision",
        (("  ticket.intent = state.intent ∧ ticket.revision = state.revision",
          "  ticket.intent = state.intent"),), "exact allowed.1")
    check_lean_mutation(ROOT, command, source, "ignore-live-grant",
        (("  InOrderedScope state ticket ∧ CurrentGrant state ticket ∧ state.installed = none",
          "  InOrderedScope state ticket ∧ True ∧ state.installed = none"),), "exact allowed.2.1")
    check_lean_mutation(ROOT, command, source, "forget-installation-on-replacement",
        (("then ({state with revision := revision}, .replaced)",
          "then ({state with revision := revision, installed := none}, .replaced)"),),
        "split <;> exact .stayed state.installed")
    check_lean_mutation(ROOT, command, source, "forget-spent-fence-on-replacement",
        (("then ({state with revision := revision}, .replaced)",
          "then ({state with revision := revision, attempts := fun _ => .absent}, .replaced)"),),
        "split <;> exact (show state.attempts id = .spent from spent)")
    check_lean_theorems(ROOT, command, source, count=11)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
