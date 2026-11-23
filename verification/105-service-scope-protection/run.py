#!/usr/bin/env python3
"""Check the difference between a service cut and an AZ durability promise."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules


def compare(name, world, *, policy="preserve", replicate=True, loss=False, inputs=True, requalify=False,
            eventually=None, laws=("OpenedWithExactInputs", "PromisesIntact",
                                   "SurvivesActualLoss", "RenewalHasFullCoverage"),
            expected=None):
    constants = {
        "World": f'"{world}"',
        "Policy": f'"{policy}"',
        "CanReplicate": str(replicate).upper(),
        "InjectLoss": str(loss).upper(),
        "ExactInputs": str(inputs).upper(),
        "CanRequalify": str(requalify).upper(),
    }
    checks = [("INVARIANT", law) for law in laws]
    if eventually:
        checks.append(("PROPERTY", eventually))
    check_tla(ROOT, "ScopeProtection", name, "Fair" if eventually else "Spec",
              constants, checks, expected=expected)


def main():
    compare("ack-without-new-input-coverage", "slow", policy="skip-ack-coverage",
            loss=True, expected="PromisesIntact")
    compare("timeout-narrows-the-promise", "slow", policy="timeout-is-failure",
            replicate=False, expected="PromisesIntact")
    compare("timeout-ack-physically-loses-write", "slow", policy="timeout-is-failure",
            replicate=False, loss=True, laws=("SurvivesActualLoss",), expected="SurvivesActualLoss")
    compare("withdraw-on-scope", "slow", policy="withdraw-on-scope", replicate=False, loss=True,
            laws=("SurvivesActualLoss",), expected="SurvivesActualLoss")
    compare("renew-on-heartbeats", "diagnosed", policy="renew-on-heartbeats", replicate=False,
            requalify=True, laws=("RenewalHasFullCoverage",), expected="RenewalHasFullCoverage")
    compare("skip-exact-inputs", "slow", policy="skip-inputs", inputs=False,
            expected="OpenedWithExactInputs")
    compare("cannot-ack-single-copy-under-uncertainty", "failed", replicate=False,
            eventually="EventuallyAck", expected="liveness")

    compare("slow-first-loss", "slow", loss=True)
    compare("slow-serve-and-replicate", "slow", eventually="EventuallyAck")
    compare("failed-but-unclassified", "failed", eventually="EventuallyAck")
    compare("serve-before-diagnosis", "failed", replicate=False, eventually="EventuallyOpen")
    compare("proven-loss-single-copy", "diagnosed", replicate=False, eventually="EventuallyAck")
    compare("repair-then-next-interval-loss", "diagnosed", loss=True, requalify=True)
    compare("refuse-missing-inputs", "slow", inputs=False)

    # Negated reachability properties give minimal acceptance traces.
    compare("ack-after-independent-replication-witness", "slow", loss=True,
            laws=("NeverAcksWithIndependentCopy",), expected="NeverAcksWithIndependentCopy")
    compare("replace-then-lose-an-az-witness", "slow", loss=True,
            laws=("PriorCopyNeverReplacedBeforeLoss",), expected="PriorCopyNeverReplacedBeforeLoss")
    compare("renew-then-lose-an-az-witness", "diagnosed", loss=True, requalify=True,
            laws=("NeverLoseAgainAfterQualifiedRenewal",), expected="NeverLoseAgainAfterQualifiedRenewal")

    command = compile_lean_modules(ROOT, ())
    source = ROOT / "ScopeProtection.lean"
    check_lean_mutation(ROOT, command, source, "ignore-new-promise",
                        [("  ready ∧ (∀ zone, credibleLoss zone → Coverage copies next zone)",
                          "  ready ∧ (∀ zone, credibleLoss zone → copies next zone → copies next zone)")],
                        "    exact allow.2 lost credible")
    check_lean_theorems(ROOT, command, source, count=10)


if __name__ == "__main__":
    main()
