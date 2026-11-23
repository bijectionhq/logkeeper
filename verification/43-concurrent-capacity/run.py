#!/usr/bin/env python3
"""Check per-domain capacity conservation and recoverable vector preparation."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, compile_lean_modules

LEDGER = ("BoundsEachZone", "UnreleasedSealIsFullyFunded", "RetainsExactCharges", "ReleaseStaysInScope")
PREPARE = ("Exclusive", "SealsOwnAll", "TerminalDecisionIsExact", "AbortedCannotReacquire")
TEMPORAL = {"SealsFinish", "BothFinish", "AbortedRestoresRoom"}


def check(module, name, laws, constants, *, expected=None):
    spec = "Fair" if any(law in TEMPORAL for law in laws) else "Spec"
    checks = tuple(("PROPERTY" if law in TEMPORAL else "INVARIANT", law) for law in laws)
    check_tla(ROOT, module, name, spec, constants, checks, expected=expected)


def ledger(name, laws, *, capacity=4, variant="reference", scenario="general", expected=None):
    check("ConcurrentLedger", name, laws,
          {"Capacity": capacity, "Variant": f'"{variant}"', "Scenario": f'"{scenario}"'},
          expected=expected)


def prepare(name, laws, *, policy="ordered", variant="reference", scenario="general", expected=None):
    check("PrepareVector", name, laws,
          {"Policy": f'"{policy}"', "Variant": f'"{variant}"', "Scenario": f'"{scenario}"'},
          expected=expected)


def verify_tla():
    for variant, law, scenario in (
        ("total_only", "BoundsEachZone", "skew"),
        ("timeout_revokes_sealed", "UnreleasedSealIsFullyFunded", "general"),
        ("drop_retained_charge", "RetainsExactCharges", "general"),
        ("release_by_route", "ReleaseStaysInScope", "general"),
        ("forget_charges", "UnreleasedSealIsFullyFunded", "general"),
    ):
        ledger(f"control-{variant}", (law,), variant=variant, scenario=scenario, expected=law)
    ledger("control-rebill-promotion", ("SealsFinish",), variant="rebill_promotion", expected="liveness")
    prepare("control-unordered-wait", ("BothFinish",), policy="arbitrary", expected="liveness")
    for variant, law, scenario in (
        ("seal_partial", "SealsOwnAll", "general"),
        ("timeout_reclaims", "SealsOwnAll", "general"),
        ("reopen_abort", "AbortedCannotReacquire", "abort_after_restart"),
    ):
        prepare(f"control-prepare-{variant}", (law,), variant=variant, scenario=scenario, expected=law)

    ledger("ledger-capacity-three", (*LEDGER, "SealsFinish"), capacity=3)
    ledger("ledger-capacity-four", (*LEDGER, "SealsFinish"))
    ledger("ledger-custodian-unreachable", (*LEDGER, "SealsFinish"), scenario="custodian_down")
    ledger("ledger-skewed-capacity", LEDGER, scenario="skew")
    for policy in ("atomic", "ordered"):
        prepare(f"prepare-{policy}", (*PREPARE, "BothFinish"), policy=policy)
    prepare("prepare-exact-abort", (*PREPARE, "AbortedRestoresRoom"), scenario="abort_after_restart")
    witness = "NeverInstallsBothAtCapacity"
    ledger("witness-two-moves-full", (witness,), scenario="custodian_down", expected=witness)
    witness = "NeverReleasesExactObsolete"
    ledger("witness-exact-disposal", (witness,), expected=witness)
    witness = "NeverRecoversAContendedPartialAbort"
    prepare("witness-recover-partial-abort", (witness,), scenario="abort_after_restart", expected=witness)


def verify_lean():
    command = compile_lean_modules(ROOT, (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "27-prefix-consensus/DurableAcceptor.lean",
        "28-ordered-application/OrderedApplication.lean",
        "32-configuration-closure/ConfigurationClosure.lean",
        "40-provider-io-closure/ProviderIOClosure.lean",
        "42-recovery-capacity/RecoveryCapacity.lean",
    ))
    ledger_source = ROOT / "CapacityLedger.lean"
    check_lean_mutation(ROOT, command, ledger_source, "ignore-admission-charge",
        (("(ledger : Ledger Scope Pool) (row : Entry Scope Pool) : Prop :=\n"
          "  ∀ pool, usage ledger pool + charge row pool ≤ limit pool",
          "(ledger : Ledger Scope Pool) (_row : Entry Scope Pool) : Prop :=\n"
          "  ∀ pool, usage ledger pool ≤ limit pool"),), "exact fits pool")
    check_lean_mutation(ROOT, command, ledger_source, "accept-foreign-disposition",
        (("(receipt : Scope) (entry : Entry Scope Pool) : Prop :=\n"
          "  receipt = entry.scope ∧ disposed receipt",
          "(receipt : Scope) (_entry : Entry Scope Pool) : Prop :=\n"
          "  True ∧ disposed receipt"),), "exact proof.1")
    prepare_source = ROOT / "OrderedPrepare.lean"
    check_lean_mutation(ROOT, command, prepare_source, "ignore-terminal-refusal",
        (("def AcceptsDelayedPrepare (state : Partial Pool) (pool : Pool) : Prop :=\n"
          "  ¬ state.fenced pool",
          "def AcceptsDelayedPrepare (_state : Partial Pool) (_pool : Pool) : Prop :=\n"
          "  True"),), "exact eligible")
    check_lean_theorems(ROOT, command, ledger_source, count=12)
    check_lean_theorems(ROOT, command, prepare_source, count=8)


if __name__ == "__main__":
    verify_tla()
    verify_lean()
