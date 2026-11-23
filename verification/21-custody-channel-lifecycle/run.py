#!/usr/bin/env python3
"""Compare drain-first and receiver-minted custody channel lifecycles."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = ("OnlyFreshChannelIsActive", "PublishedPinsSurvive", "EveryGrantWasPlanned",
        "LateAcquireDoesNotRecreateChannelInterest", "NoStaleClose", "NoStaleCredit", "Footprint")


def check(name, checks, *, variant="detach", expected=None, bound=2, observe=False):
    constants = {"Variant": f'"{variant}"', "MaxNonce": bound, "Observe": "TRUE" if observe else "FALSE"}
    check_tla(ROOT, "ChannelLifecycle", name, "FairSpec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
        "20-registration-recovery/RegistrationRecovery.lean",
    ))
    source = ROOT / "ChannelLifecycle.lean"
    check_lean_mutation(ROOT, command, source, "admit-on-stale-route",
        (("else .refuse\n      | none => .refuse", "else .admit\n      | none => .refuse"),),
        "| some channel =>\n      have different : channel.handle ≠ key.handle")
    check_lean_mutation(ROOT, command, source, "release-without-exact-authority",
        (("(closed : authority.mayRelease key binding)", "(closed : True)"),
         (".release key binding (.inr pin) releaseAuthorized",
          ".release key binding (.inr pin) (by have _ := releaseAuthorized; exact True.intro)")),
        "have certified")
    check_lean_mutation(ROOT, command, source, "open-outside-slot-budget",
        (("(room : route < authority.routeLimit)", "(room : True)"),
         (".mint route key.handle.issuer free room openAuthorized",
          ".mint route key.handle.issuer free (by have _ := room; exact True.intro) openAuthorized")),
        "have inside")
    check_lean_theorems(ROOT, command, source, count=15)


def main():
    verify_lean()
    for variant, law in (
        ("reuse_handle", "OnlyFreshChannelIsActive"),
        ("drop_live_pins", "PublishedPinsSurvive"),
        ("ignore_channel", "LateAcquireDoesNotRecreateChannelInterest"),
        ("rebind_to_route", "EveryGrantWasPlanned"),
        ("close_by_route", "NoStaleClose"),
        ("floor_by_route", "NoStaleCredit"),
        ("release_by_serial", "PublishedPinsSurvive"),
    ):
        check(f"control-{variant}", (("INVARIANT", law),), variant=variant, expected=law)
    check("control-release_requires_channel", (("PROPERTY", "OldReleaseProgress"),),
          variant="release_requires_channel", expected="liveness")
    checks = tuple(("INVARIANT", law) for law in LAWS) + (("PROPERTY", "OldReleaseProgress"),)
    for variant in ("detach", "drain_first"):
        for bound in (2, 3):
            check(f"baseline-{variant}-{bound}", checks, variant=variant, bound=bound)
    law = "NeverRotatesWithLivePublishedPin"
    check("drain-first-excludes-rollover", (("INVARIANT", law),), variant="drain_first", observe=True)
    for law in (law, "NeverReplaysOldAndThenReleases", "NeverRejectsDelayedOnSuccessor"):
        check(f"witness-{law}", (("INVARIANT", law),), expected=law, observe=True)


if __name__ == "__main__":
    main()
