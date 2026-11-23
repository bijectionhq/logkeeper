#!/usr/bin/env python3
"""Check exact checkpoint rehome, inherited pins and source disposal."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

SAFETY = ("RootInExactScope", "RootHasExactClosure", "SourceProtection")


def check(name, checks, *, variant="registered", expected=None, refs=1, observe=False):
    constants = {"Variant": f'"{variant}"', "RefCount": refs,
                 "Observe": "TRUE" if observe else "FALSE"}
    check_tla(ROOT, "Residence", name, "FairSpec", constants, checks, expected=expected)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "16-checkpoint-reconstruction/CheckpointReconstruction.lean",
        "18-snapshot-admission/SnapshotAdmission.lean",
        "19-shared-object-custody/SharedCustody.lean",
    ))
    source = ROOT / "ResidenceTransfer.lean"
    check_lean_mutation(ROOT, command, source, "untrusted-source-manifest",
        (("captured : prepared.sourceManifest = manifests.captured prepared.plan.origin\n  installed",
          "captured : True\n  installed"),),
        "have captured")
    check_lean_mutation(ROOT, command, source, "proof-for-other-target",
        (("installed : prepared.targetManifest = manifests.installed prepared.plan.destination\n  exact",
          "installed : True\n  exact"),),
        "have installed")
    check_lean_mutation(ROOT, command, source, "missing-logical-equivalence",
        (("exact : EquivalentClosure required prepared.sourceManifest prepared.targetManifest", "exact : True"),),
        "have same : EquivalentClosure")
    check_lean_mutation(ROOT, command, source, "publish-without-live-custody",
        (("registered : holds prepared.plan.destination", "registered : True"),),
        "have liveGrant")
    check_lean_theorems(ROOT, command, source, count=14)


def main():
    verify_lean()
    for variant, law, refs in (
        ("skip_bytes", "RootHasExactClosure", 1),
        ("skip_closure", "RootHasExactClosure", 1),
        ("reclaim_verified", "RootHasExactClosure", 1),
        ("swap_verified_version", "RootHasExactClosure", 1),
        ("stale_catalog", "RootInExactScope", 1),
        ("stale_target", "RootInExactScope", 1),
        ("wrong_referrer", "RootInExactScope", 2),
        ("skip_referrer", "SourceProtection", 2),
        ("skip_snapshot", "SourceProtection", 1),
        ("skip_reader", "SourceProtection", 1),
    ):
        check(f"control-{variant}", (("INVARIANT", law),), variant=variant, expected=law, refs=refs)
    check("control-needs_source_link", (("PROPERTY", "StableReadyCanInstall"),),
          variant="needs_source_link", expected="liveness")
    check("source-link-unavailable", (("PROPERTY", "SettlesWithoutSource"),),
          variant="permanent_source_loss", expected="liveness")
    safety = tuple(("INVARIANT", law) for law in SAFETY)
    progress = (("PROPERTY", "StableReadyCanInstall"), ("PROPERTY", "SettlesWithSource"))
    for refs in (1, 2):
        check(f"baseline-{refs}", safety + progress, refs=refs)
    check("drain-first", safety + (("PROPERTY", "SettlesWithSource"),), variant="drain_first")
    check("drain-first-blocks-overlap", (("INVARIANT", "NeverServesBothThenErases"),),
          variant="drain_first", observe=True)
    check("physical-equality", safety + progress + (("INVARIANT", "NeverInstallsRepacked"),),
          variant="physical_equality")
    for law in ("NeverInstallsRepacked", "NeverInstallsOffline", "NeverUsesHeldSnapshotAfterSwap"):
        check(f"witness-{law}", (("INVARIANT", law),), expected=law, observe=True,
              refs=1)
    for law in ("NeverServesBothThenErases", "NeverTransfersOfflineThenFullySettles"):
        check(f"witness-{law}", (("INVARIANT", law),), expected=law, observe=True, refs=2)


if __name__ == "__main__":
    main()
