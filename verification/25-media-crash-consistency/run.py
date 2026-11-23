#!/usr/bin/env python3
"""Check durable acknowledgement, prefix decoding and journal generation replacement."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = (
    "AcknowledgedPrefixSurvives",
    "RecoveryNeverSkipsMissingFrame",
    "VisibilityRequiresCommitEvidence",
)


def check(name, laws, *, variant="shared_tail", expected=None, bound=2):
    constants = {"Variant": f'"{variant}"', "MaxRecords": bound}
    checks = tuple(("INVARIANT", law) for law in laws)
    check_tla(ROOT, "CrashMedia", name, "Spec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
    ))
    source = ROOT / "MediaCrash.lean"
    check_lean_mutation(ROOT, command, source, "skip-invalid-frame",
        (("| .none :: _ => []", "| .none :: rest => decodePrefix rest"),),
        "exact List.append_nil valid")
    check_lean_mutation(ROOT, command, source, "reclaim-before-durable-selector",
        (("def ReclaimAdmissible (rotation : Rotation) : Prop :=\n  rotation.phase = .selectorStable",
          "def ReclaimAdmissible (_rotation : Rotation) : Prop := True"),),
        "have stableSelector : _ = Phase.selectorStable := admitted")
    check_lean_mutation(ROOT, command, source, "ack-without-durable-bytes",
        (("  vote.bytesStable = true ∧ vote.nameStable = true", "  vote.nameStable = true"),
         ("exact And.right admitted", "exact admitted")),
        "exact And.left admitted")
    check_lean_mutation(ROOT, command, source, "ack-without-durable-name",
        (("  vote.bytesStable = true ∧ vote.nameStable = true", "  vote.bytesStable = true"),
         ("exact And.left admitted", "exact admitted")),
        "exact And.right admitted")
    check_lean_theorems(ROOT, command, source, count=9)


def main():
    verify_lean()
    for variant, law in (
        ("ack_before_bytes", "AcknowledgedPrefixSurvives"),
        ("ack_before_name", "AcknowledgedPrefixSurvives"),
        ("skip_gap", "RecoveryNeverSkipsMissingFrame"),
        ("intact_means_committed", "VisibilityRequiresCommitEvidence"),
        ("publish_incomplete_base", "AcknowledgedPrefixSurvives"),
        ("unlink_before_selector_sync", "AcknowledgedPrefixSurvives"),
        ("omit_intervening_tail", "AcknowledgedPrefixSurvives"),
        ("redirect_before_selector", "AcknowledgedPrefixSurvives"),
    ):
        check(f"control-{variant}", (law,), variant=variant, expected=law)
    for bound in (2, 3):
        check(f"shared-tail-{bound}", LAWS, bound=bound)
    check("head-match-3", (*LAWS, "NeverPublishesAfterAdvance"),
          variant="head_match", bound=3)
    for bound, law in (
        (2, "NeverPublishesAfterAdvance"),
        (3, "NeverRecoversVolatilePublishOnOld"),
        (3, "NeverReclaimsAndRecoversExactSuffix"),
        (2, "NeverKeepsUncertifiedBytes"),
    ):
        check(f"witness-{law}", (law,), expected=law, bound=bound)


if __name__ == "__main__":
    main()
