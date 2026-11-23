#!/usr/bin/env python3
"""Check changing checkpoint dependencies against ongoing exact storage effects."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def compare(name, scenario, *, policy="registered", law=None, progress=None, expected=None):
    constants = {"Scenario": f'"{scenario}"', "Policy": f'"{policy}"'}
    laws = (law,) if law else ("HoldsNeverCountPending", "PublishedHasExactProtection",
                               "NoPublishAfterCancel", "KeepsOldSelector", "ClosedStaysClosed")
    checks = [("INVARIANT", key) for key in laws]
    if progress:
        checks.append(("PROPERTY", progress))
    check_tla(ROOT, "DynamicProtection", name, "Fair" if progress else "Spec",
              constants, checks, expected=expected)


def verify_tla():
    compare("admit-a-hold-after-withdrawal", "race", policy="pin-withdrawing",
            law="HoldsNeverCountPending", expected="HoldsNeverCountPending")
    compare("publish-with-bare-physical-observation", "race", policy="check-bytes",
            law="PublishedHasExactProtection", expected="PublishedHasExactProtection")
    compare("renew-then-publish-a-spent-only-plan", "renewal", policy="old-qualification",
            law="PublishedHasExactProtection", expected="PublishedHasExactProtection")
    compare("publish-after-durable-abort", "after-publication", policy="publish-after-cancel",
            law="NoPublishAfterCancel", expected="NoPublishAfterCancel")
    compare("timeout-cancels-already-published-root", "after-publication", policy="infer-abort",
            law="NoPublishAfterCancel", expected="NoPublishAfterCancel")
    compare("delayed-acquire-reopens-canceled-reference", "cancel", policy="ignore-cancel-fence",
            law="ClosedStaysClosed", expected="ClosedStaysClosed")
    compare("lose-old-selector-during-transition", "protect-old-selector", policy="visible-only",
            law="KeepsOldSelector", expected="KeepsOldSelector")
    compare("invalidate-still-covered-plan-after-renewal", "renewal-covered", policy="same-envelope-only",
            progress="EventuallyPublishes", expected="liveness")
    compare("publication-needs-custodian-control-link", "offline-publication", policy="contact-custodian",
            progress="EventuallyPublishes", expected="liveness")
    compare("abort-waits-for-lost-acquire-reply", "cancel", policy="need-acquire-reply",
            progress="EventuallyClosesCanceled", expected="liveness")

    compare("pin-and-withdraw-race", "race")
    compare("renewal-rechecks-protected-inputs", "renewal")
    compare("still-covered-plan-publishes-after-renewal", "renewal-covered", progress="EventuallyPublishes")
    compare("irreversible-logical-outcome", "after-publication")
    compare("old-root-retains-its-own-holds", "protect-old-selector")
    compare("durable-holds-publish-offline", "offline-publication", progress="EventuallyPublishes")
    compare("settle-canceled-without-replies", "cancel", progress="EventuallyClosesCanceled")
    compare("publish-before-stable-sync-witness", "protect-old-selector", law="NeverPublishesWithBothSelectors",
            expected="NeverPublishesWithBothSelectors")
    compare("retire-old-only-after-sync-witness", "protect-old-selector", law="NeverRetiresOldAfterSwitch",
            expected="NeverRetiresOldAfterSwitch")


def verify_lean():
    deps = (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
        "20-registration-recovery/RegistrationRecovery.lean",
        "26-journal-rotation/JournalRotation.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
        "105-service-scope-protection/ScopeProtection.lean",
        "108-withdrawal-recovery/WithdrawalRecovery.lean",
    )
    command = compile_lean_modules(ROOT, deps)
    source = ROOT / "DynamicProtection.lean"
    check_lean_mutation(ROOT, command, source, "ignore-exact-publication-holds",
                        [("  ∀ version, plan.needs root version → store.refs root version = .held\n\ndef CanPublish",
                          "  ∀ version, plan.needs root version → store.refs root version = store.refs root version\n\ndef CanPublish")],
                        "  exact ready.2.1")
    check_lean_theorems(ROOT, command, source, count=12)


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
