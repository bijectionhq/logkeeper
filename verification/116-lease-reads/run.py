#!/usr/bin/env python3
"""Check the barrier and local serving protocols, witnesses, and controls."""

import os
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LAWS = [
    "LatestLinearizable", "CommittedPrefix", "FreshAuthority", "ServingDeadline", "TrimPreservesHolds",
    "CollectionPreservesHolds", "ErasureDeadline", "SameBasisRetry", "CostAccounting",
]


def check(name, design, *, fault="none", expected=None, second_read=True, reconfigure=True):
    constants = {
        "Design": f'"{design}"',
        "Fault": f'"{fault}"',
        "Horizon": "6" if reconfigure else "3",
        "Term": "3",
        "Drift": "1",
        "OrphanTTL": "2",
        "KeyGrace": "2",
        "SecondRead": "TRUE" if second_read else "FALSE",
        "Reconfigure": "TRUE" if reconfigure else "FALSE",
    }
    laws = [expected] if expected else list(LAWS)
    if expected is None and design in ("barrier", "fallback"):
        laws.append("RetainedNamedAdmission")
    if expected is None and fault == "lagging-apply":
        laws.remove("LatestLinearizable")
    check_tla(
        ROOT, "LeaseReads", name, "Spec", constants,
        [("INVARIANT", law) for law in laws], expected=expected,
    )


def verify_tla():
    if "TLA_JAR" in os.environ:
        local_jar = ROOT / ".tools" / "tla2tools.jar"
        local_jar.parent.mkdir(exist_ok=True)
        pinned_jar = Path(os.environ["TLA_JAR"]).expanduser().resolve()
        if pinned_jar != local_jar.resolve():
            shutil.copyfile(pinned_jar, local_jar)

    for design in ("barrier", "lease"):
        check(f"{design}-reconfiguration-baseline", design, second_read=False)
    for design in ("barrier", "lease", "fallback"):
        check(f"{design}-two-read-baseline", design, reconfigure=False)
    check("lease-lagging-applied-prefix-baseline", "lease", fault="lagging-apply", second_read=False)

    for design in ("barrier", "lease"):
        for witness, invariant, second_read in (
            ("serve-release-collect", "ServedAndCollectedWitness", False),
            ("read-across-replacement", "AcrossReplacementWitness", True),
            ("held-view-before-key-deadline", "ViewBeforeErasureDeadlineWitness", False),
            ("held-view-erased-at-deadline", "ErasedHeldViewWitness", False),
            ("clean-successor-and-held-erasure", "CleanAndErasedWitness", True),
            ("retry-original-basis", "SameBasisRetryWitness", True),
            ("lost-reply-expires-and-collects", "OrphanExpiryWitness", False),
        ):
            check(f"{design}-{witness}", design, expected=invariant, second_read=second_read)

    for design, witness, invariant in (
        ("lease", "two-active-cuts", "ReportedMinimumWitness"),
        ("lease", "refused-below-report", "BelowReportRetryWitness"),
        ("lease", "two-reads-one-renewal", "RenewedBatchWitness"),
        ("fallback", "older-basis-with-ordered-hold", "OrderedFallbackWitness"),
    ):
        check(f"{design}-{witness}", design, expected=invariant, reconfigure=False)

    for design, fault, invariant, second_read in (
        ("barrier", "barrier-applied-cut", "LatestLinearizable", False),
        ("barrier", "stale-barrier", "FreshAuthority", False),
        ("barrier", "trim-held", "TrimPreservesHolds", False),
        ("barrier", "collect-held", "CollectionPreservesHolds", False),
        ("barrier", "resample-retry", "SameBasisRetry", True),
        ("barrier", "free-release", "CostAccounting", False),
        ("barrier", "revoke-on-rotation", "ErasureDeadline", False),
        ("lease", "admit-expired", "ServingDeadline", False),
        ("lease", "slow-clock", "ServingDeadline", False),
        ("lease", "early-install", "FreshAuthority", False),
        ("lease", "early-install", "LatestLinearizable", False),
        ("lease", "lagging-apply", "LatestLinearizable", False),
        ("lease", "speculative-cut", "CommittedPrefix", False),
        ("lease", "periodic-only", "TrimPreservesHolds", True),
        ("lease", "expire-floor", "TrimPreservesHolds", False),
        ("lease", "collect-held", "CollectionPreservesHolds", False),
        ("lease", "skip-key-fence", "ErasureDeadline", False),
        ("lease", "resample-retry", "SameBasisRetry", True),
        ("lease", "none", "RetainedNamedAdmission", True),
        ("lease", "charge-local", "CostAccounting", False),
        ("lease", "free-renewal", "CostAccounting", False),
        ("fallback", "resample-retry", "SameBasisRetry", True),
    ):
        check(f"{design}-{fault}-{invariant}", design, fault=fault,
              expected=invariant, second_read=second_read, reconfigure=not second_read)

    for name, mode, laws, expected in (
        ("exact-basis-baseline", "basis", ["ReplayRetained", "ObjectsRetained"], None),
        ("exact-basis-witness", "basis", ["FinishAndCollectWitness"], "FinishAndCollectWitness"),
        ("logical-cut-loses-replay", "cut", ["ReplayRetained"], "ReplayRetained"),
        ("logical-cut-collects-root", "cut", ["ObjectsRetained"], "ObjectsRetained"),
    ):
        check_tla(ROOT, "ExactBasis", name, "Spec", {"Mode": f'"{mode}"'},
                  [("INVARIANT", law) for law in laws], expected=expected)


def verify_lean():
    elan = Path.home() / ".elan" / "bin" / "lean"
    if elan.is_file():
        os.environ.setdefault("LEAN_BIN", str(elan))
    command = compile_lean_modules(ROOT, ())
    source = ROOT / "LeaseBounds.lean"
    check_lean_theorems(ROOT, command, source, count=3)
    check_lean_mutation(
        ROOT, command, source, "ignore-drift",
        [("worker + drift < leaseEnd", "worker + 0 * drift < leaseEnd")],
        "  omega\n\ndef ReportedFloor",
    )
    check_lean_mutation(
        ROOT, command, source, "ignore-active-minimum",
        [("  min oldestActive applied", "  applied + 0 * oldestActive")],
        "  exact Nat.le_trans",
    )
    check_lean_mutation(
        ROOT, command, source, "ignore-report-at-admission",
        [("  reported ≤ cut", "  cut ≤ cut + reported")],
        "  omega\n\n#print axioms",
    )


if __name__ == "__main__":
    modes = sys.argv[1:]
    if modes not in ([], ["tla"], ["lean"]):
        raise SystemExit("usage: run.py [tla|lean]")
    if modes in ([], ["tla"]):
        verify_tla()
    if modes in ([], ["lean"]):
        verify_lean()
