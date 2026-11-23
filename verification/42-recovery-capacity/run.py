#!/usr/bin/env python3
"""Check exact recovery under ordinary pressure and persistent physical custody."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ("Bounds", "SealProtected", "ExactInstall", "RetainsPhysicalCharge", "AcceptedMediaStaysPinned")
TEMPORAL = {"SealedCompletes", "ReturnsOldWorkspace"}


def check(name, laws, *, normal=3, workspace=4, envelope=2, policy="exact",
          variant="reference", scenario="general", expected=None):
    constants = {"Normal": normal, "Workspace": workspace, "Envelope": envelope,
                 "Policy": f'"{policy}"', "Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}
    checks = tuple(("PROPERTY" if law in TEMPORAL else "INVARIANT", law) for law in laws)
    spec = "Fair" if any(law in TEMPORAL for law in laws) else "Spec"
    check_tla(ROOT, "RecoveryCapacity", name, spec, constants, checks, expected=expected)


def verify_tla():
    for variant, law in (
        ("accepted_over_envelope", "SealProtected"),
        ("learned_cut", "SealProtected"),
        ("install_wrong_cut", "ExactInstall"),
        ("drop_old_charge", "RetainsPhysicalCharge"),
        ("release_on_timeout", "RetainsPhysicalCharge"),
        ("forget_credit", "SealProtected"),
        ("erase_early", "AcceptedMediaStaysPinned"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    for policy in ("learned", "staging_only", "borrow"):
        check(f"control-{policy}", ("SealedCompletes",), policy=policy, expected="liveness")
    check("control-one_image", ("SealedCompletes",), policy="one_image", workspace=2, expected="liveness")
    check("control-charge_install_again", ("SealedCompletes",), variant="charge_install_again", expected="liveness")
    check("control-old-custodian-unreachable", ("ReturnsOldWorkspace",), scenario="provider_down",
          expected="liveness")

    for envelope in (2, 3):
        check(f"reserved-envelope-{envelope}", (*SAFETY, "SealedCompletes", "ReturnsOldWorkspace"),
              normal=envelope + 1, workspace=2 * envelope, envelope=envelope)
    check("install-with-old-custodian-down", (*SAFETY, "SealedCompletes"), scenario="provider_down")
    check("no-residency-room-waits-before-seal", (*SAFETY, "WaitsBeforeSeal"), scenario="no_residency_room")
    check("full-ordinary-loss-and-restart", ("NeverInstallsHiddenCutAtCapacity",), scenario="provider_down",
          expected="NeverInstallsHiddenCutAtCapacity")
    check("returns-space-on-stable-absence", ("NeverReleasesOldCustody",), expected="NeverReleasesOldCustody")


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "27-prefix-consensus/DurableAcceptor.lean",
        "28-ordered-application/OrderedApplication.lean",
        "32-configuration-closure/ConfigurationClosure.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
    ))
    source = ROOT / "RecoveryCapacity.lean"
    check_lean_mutation(ROOT, command, source, "accept-without-envelope",
        (("(fitsNew : ∀ vote, after.acceptor.votes vote → ¬ before.acceptor.votes vote →\n"
          "        context.footprint vote.history ≤ context.budget.envelope)",
          "(fitsNew : ∀ vote, after.acceptor.votes vote → ¬ before.acceptor.votes vote → True)"),),
        "exact ⟨.next prior.1 transition, preserveBound prior.2 fits⟩")
    check_lean_mutation(ROOT, command, source, "reserve-just-one-image",
        (("    2 * context.budget.envelope ≤ context.budget.workspace\n\ndef CanReleaseOld",
          "    context.budget.envelope ≤ context.budget.workspace\n\ndef CanReleaseOld"),),
        "fun _ => room.2")
    check_lean_mutation(ROOT, command, source, "install-different-recovered-history",
        (("  exact : family.basis = cut.history",
          "  exact : family.basis.length = cut.history.length"),), "exact installation.exact")
    check_lean_mutation(ROOT, command, source, "install-at-unrelated-family",
        (("  target : context.authorizedTarget family", "  target : True"),), "exact installation.target")
    check_lean_mutation(ROOT, command, source, "forget-required-incumbent",
        (("(retains : NeedsIncumbent state.phase → next.present = true)", "(retains : True)"),),
        "exact ⟨sound.ordinary, sound.workspace, ProviderIOClosure.sound_step sound.custody effect, retains⟩")
    check_lean_mutation(ROOT, command, source, "discard-custody-on-assertion",
        (("def CanReleaseOld (state : State context Ticket) : Prop :=\n  state.incumbent.erased = true",
          "def CanReleaseOld (_state : State context Ticket) : Prop := True"),), "exact sound.custody.erasure proof")
    check_lean_theorems(ROOT, command, source, count=14)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
