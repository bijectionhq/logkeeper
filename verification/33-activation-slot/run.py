#!/usr/bin/env python3
"""Check exact successor activation across coordinator changes and payload loss."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ("ChosenAgreement", "PublishedIsChosen", "EveryLiveAcceptedHasBytes", "ChosenIsRecoverable",
          "StagingIsBounded")


def check(name, laws, *, media="local", variant="reference", ballots=2,
          schedule="general", capacity=2, temporal=False, expected=None):
    constants = {"Media": f'"{media}"', "Variant": f'"{variant}"',
                 "Ballots": ballots, "Schedule": f'"{schedule}"', "Capacity": capacity}
    check_tla(ROOT, "Activation", name, "Fair" if temporal else "Spec", constants,
              tuple(("PROPERTY" if temporal else "INVARIANT", law) for law in laws),
              expected=expected)


def verify_tla():
    for variant, law in (
        ("ignore_accepted", "ChosenAgreement"),
        ("cached_ready", "EveryLiveAcceptedHasBytes"),
        ("promise_releases_vote", "EveryLiveAcceptedHasBytes"),
        ("publish_readiness", "PublishedIsChosen"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    check("control-metadata-decides-without-image", ("ChosenIsRecoverable",),
          media="metadata", expected="ChosenIsRecoverable")
    check("control-unbacked-retry-stalls", ("RecoversAfterFault",),
          media="metadata", schedule="partial", temporal=True, expected="liveness")
    check("control-fixed-prepared-ballot-stalls", ("RecoversAfterFault",),
          ballots=3, variant="no_new_ballot_after_loss", schedule="report_then_loss",
          temporal=True, expected="liveness")
    check("control-no-replacement-room", ("RecoversAfterFault",),
          ballots=3, schedule="divergent_holders", capacity=1, temporal=True, expected="liveness")

    check("local-general", SAFETY)
    check("referent-general", SAFETY, media="referent")
    for media in ("local", "referent"):
        check(f"{media}-hidden", SAFETY, media=media, schedule="hidden")
        check(f"{media}-hidden-progress", ("RecoversAfterFault",),
              media=media, schedule="hidden", temporal=True)
    check("local-partial", SAFETY, schedule="partial")
    check("local-partial-progress", ("RecoversAfterFault",), schedule="partial", temporal=True)
    check("local-report-then-loss", SAFETY, ballots=3, schedule="report_then_loss")
    check("local-report-then-loss-progress", ("RecoversAfterFault",),
          ballots=3, schedule="report_then_loss", temporal=True)
    check("local-divergent-holders", SAFETY, ballots=3, schedule="divergent_holders")
    check("local-divergent-holders-progress", ("RecoversAfterFault",),
          ballots=3, schedule="divergent_holders", temporal=True)

    for law, schedule, ballots in (
        ("NeverRelearnsHiddenChoice", "hidden", 2),
        ("NeverDiscardsLostSingleton", "partial", 2),
        ("NeverRetriesUnreadablePreparedValue", "report_then_loss", 3),
        ("NeverReleasesReplacedBinding", "divergent_holders", 3),
    ):
        check(f"witness-{schedule}", (law,), schedule=schedule, ballots=ballots, expected=law)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "27-prefix-consensus/DurableAcceptor.lean",
        "32-configuration-closure/ConfigurationClosure.lean",
    ))
    source = ROOT / "ActivationSlot.lean"
    check_lean_mutation(ROOT, command, source, "accept-an-image-without-backing",
        (("def MayAccept (state : Device Seed) (seed : Seed) : Prop := state.resident seed",
          "def MayAccept (_state : Device Seed) (_seed : Seed) : Prop := True"),),
        "exact backed")
    check_lean_mutation(ROOT, command, source, "collect-the-still-bound-image",
        (("  | collect {state} (seed : Seed) (allowed : MayCollect state seed) :",
          "  | collect {state} (seed : Seed) (allowed : True) :"),),
        "exact allowed")
    check_lean_mutation(ROOT, command, source, "publish-staging-without-choice",
        (("def CanPublish (ledger : Ledger Voter Seed) (ballot : Nat) (seed : Seed) : Prop :=\n"
          "  Decided ledger ballot seed",
          "def CanPublish (_ledger : Ledger Voter Seed) (_ballot : Nat) (_seed : Seed) : Prop := True"),),
        "exact accepted")
    check_lean_mutation(ROOT, command, source, "installed-image-matches-only-length",
        (("def ReplaysRecovered (decoded recovered : List Command) : Prop := decoded = recovered",
          "def ReplaysRecovered (decoded recovered : List Command) : Prop := decoded.length = recovered.length"),),
        "exact exactImage")
    check_lean_theorems(ROOT, command, source, count=10)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
