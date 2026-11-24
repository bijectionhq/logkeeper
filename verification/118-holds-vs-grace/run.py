#!/usr/bin/env python3
"""Run each reference, named control, and reachability check for Study 118."""

import argparse
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from study_tools import check_lean_mutation, check_lean_theorems, check_tla

CYCLE = Path.home() / "cycle3"


def tla_value(value):
    if isinstance(value, str):
        return f'"{value}"'
    if isinstance(value, bool):
        return str(value).upper()
    return str(value)


def check(module, name, constants, laws=(), *, spec="Spec", temporal=None, failure=None):
    values = {key: tla_value(value) for key, value in constants.items()}
    checks = [("INVARIANT", law) for law in laws]
    if temporal:
        checks.append(("PROPERTY", temporal))
    check_tla(ROOT, module, name, spec, values, checks, expected=failure)


def physical(mode, scenario, *, fault="none", g=5, d=2, e=1, bounded=True, failure=None,
             witness=None, progress=False):
    constants = dict(Mode=mode, Scenario=scenario, Fault=fault, G=g, D=d, Bounded=bounded, E=e,
                     Horizon=10, LeaseEnd=2)
    laws = ("LiveRootsBacked", "BorrowBacked", "StableAbsence", "ExactSettlement",
            "DisposalAfterAdmission", "NoWrongVersion")
    name = f"physical-{mode}-{scenario}"
    if (g, d, e) != (5, 2, 1):
        name += f"-g{g}-d{d}-e{e}"
    if not bounded:
        name += "-unbounded"
    if fault != "none":
        name += f"-{fault}"
    elif failure:
        name += f"-{failure}"
    check("Physical", name, constants, [failure] if failure and failure != "liveness" else laws,
          spec="WorkerFair" if progress else "Spec",
          temporal="WorkerReclaimed" if progress else None, failure=failure)
    if witness:
        check("Physical", f"{name}-witness", constants, [witness], failure=witness)


def verify_physical():
    physical("A", "write", bounded=False, witness="SawWriteClosure")
    physical("A", "write", bounded=False, fault="no-fence", failure="StableAbsence")
    physical("B", "write", witness="SawWriteClosure")
    physical("B", "write", g=1, d=2, e=0, failure="StableAbsence")
    physical("B", "write", g=3, d=2, e=1, failure="StableAbsence")
    physical("B", "write", g=4, d=2, e=1, failure="StableAbsence")
    physical("B", "write", g=5, bounded=False, failure="StableAbsence")
    physical("pin", "write", g=4, failure="StableAbsence")
    for mode in ("A", "B", "pin"):
        physical(mode, "borrow", witness="SawDetachedDrain")
        physical(mode, "worker", witness="SawWorkerReclaimed", progress=True)
    physical("A", "borrow", fault="drop-borrow", failure="BorrowBacked")
    physical("B", "borrow", g=4, failure="BorrowBacked")
    physical("pin", "borrow", g=1, e=0, witness="SawDetachedDrain")
    physical("A", "worker", fault="early-dispose", failure="DisposalAfterAdmission")
    physical("A", "worker", fault="no-dispose", progress=True, failure="liveness")
    physical("A", "worker-race", witness="SawLeasedBorrow")
    physical("A", "worker-race", fault="early-dispose", failure="BorrowBacked")
    physical("B", "worker-race", g=7, witness="SawLeasedBorrow")
    physical("B", "worker-race", g=6, failure="BorrowBacked")
    physical("B", "worker-race", g=5, failure="BorrowBacked")
    for mode in ("A", "B"):
        for scenario in ("fork", "selector", "preparation", "suffix"):
            physical(mode, scenario, witness="SawRootRelease")
            physical(mode, scenario, fault="ignore-root", failure="LiveRootsBacked")
        physical(mode, "register", witness="SawRegistrationWin")
        physical(mode, "register", fault="stale-mark", failure="LiveRootsBacked")
        physical(mode, "replace", witness="SawReplacementSurvive")
        physical(mode, "replace", fault="delete-latest", failure="LiveRootsBacked")
        physical(mode, "replace", fault="marker", failure="ExactSettlement")
    physical("B", "replace", fault="hash-only", witness="SawVerifiedRefusal")
    physical("B", "replace", fault="trust-latest", failure="NoWrongVersion")


def cuts(mode, request, *, fault="none", failure=None, witness=None):
    constants = dict(Mode=mode, Request=request, Fault=fault)
    laws = ["NoWrongData", "RetryRereadsRoot", "ForkBacked"]
    if mode != "B":
        laws.extend(["RequestedBasisBacked", "ExactNamedService"])
    name = f"cuts-{mode}-{request}" + (f"-{fault}" if fault != "none" else "")
    check("Cuts", name, constants, [failure] if failure else laws, failure=failure)
    if witness:
        check("Cuts", f"{name}-witness", constants, [witness], failure=witness)


def cadence(mode, operation, c, observe, work, *, pin_life=None, failure=None, witness=None):
    constants = dict(Mode=mode, C=c, Observe=observe, Work=work,
                     PinLife=work + 1 if pin_life is None else pin_life)
    name = f"cadence-{mode}-{operation}-c{c}-o{observe}-w{work}"
    if pin_life is not None:
        name += f"-pin{pin_life}"
    check("Cadence", name, constants, temporal="EventuallyServed", failure=failure)
    if witness:
        check("Cadence", f"{name}-witness", constants, [witness], failure=witness)


def verify_cuts():
    for mode in ("A", "pin"):
        for request in ("named", "fork", "recovery"):
            cuts(mode, request, witness="SawForkTransfer" if request == "fork" else "SawOldCutAfterPublish")
        cuts(mode, "named", fault="omit-suffix", failure="RequestedBasisBacked")
        cuts(mode, "named", fault="omit-root", failure="RequestedBasisBacked")
    for mode in ("A", "B", "pin"):
        cuts(mode, "fork", fault="ignore-child", failure="ForkBacked")
    for request in ("latest", "recovery"):
        cuts("B", request, witness="SawFreshRetry")
        cuts("B", request, fault="stale-retry", failure="RetryRereadsRoot")
        cuts("B", request, fault="retarget", failure="NoWrongData")
    for request in ("named", "fork"):
        cuts("B", request, witness="SawRefusal")
        for law in ("ExactNamedService", "RequestedBasisBacked"):
            check("Cuts", f"cuts-B-{request}-product-{law}",
                  dict(Mode="B", Request=request, Fault="none"), [law], failure=law)
    for operation, work in (("latest", 2), ("recovery", 3)):
        cadence("B", operation, work + 2, 1, work, witness="SawCompletion")
        cadence("B", operation, work + 1, 1, work, failure="liveness")
        cadence("B", operation, work, 1, work, failure="liveness")
        for mode in ("A", "pin"):
            cadence(mode, operation, 2, 1, work, witness="SawOvertakeAndFinish")
        cadence("pin", operation, 2, 1, work, pin_life=work, failure="liveness")


def erasure(*, fault="none", e=1, arm=4, failure=None, witnesses=()):
    constants = dict(Fault=fault, E=e, Deadline=6, Arm=arm, Horizon=8)
    laws = ["CleanRecovery", "DeadlineUnreadable", "NoLatePlaintext",
            "NoEarlyEraseAtCommit", "GuaranteedWindow", "HoldSurvives", "KeyDomainClosed"]
    if e == 0:
        laws.append("FullViewWindow")
    name = f"erasure-e{e}-arm{arm}-{fault}"
    if failure:
        name += f"-{failure}"
    check("Erasure", name, constants, [failure] if failure else laws, spec="Fair",
          temporal=None if failure else "EventuallyRecovers", failure=failure)
    for witness in witnesses:
        check("Erasure", f"{name}-{witness}", constants, [witness], failure=witness)


def verify_erasure():
    witnesses = ("SawRevocationAndRecovery", "SawPredeadlineRead")
    erasure(e=0, arm=6, witnesses=witnesses)
    erasure(witnesses=witnesses)
    erasure(failure="FullViewWindow")
    erasure(arm=6, failure="DeadlineUnreadable")
    for fault, law in (
        ("grace-only", "DeadlineUnreadable"),
        ("old-selector", "CleanRecovery"),
        ("old-append", "CleanRecovery"),
        ("early-revoke", "NoEarlyEraseAtCommit"),
        ("drop-hold", "HoldSurvives"),
        ("escape-copy", "KeyDomainClosed"),
        ("admit-only", "NoLatePlaintext"),
    ):
        erasure(fault=fault, failure=law)


def verify_lean():
    command = [os.environ.get("LAKE_BIN", str(Path.home() / ".elan/bin/lake")), "env", "lean"]
    version = subprocess.run([*command, "--version"], cwd=ROOT, text=True,
                             capture_output=True, check=True)
    if "version 4.35.0," not in version.stdout:
        raise SystemExit(f"Expected Lean 4.35.0, found {version.stdout.strip()}")
    source = ROOT / "Bounds.lean"
    check_lean_theorems(ROOT, command, source, count=6)
    check_lean_mutation(ROOT, command, source, "allow-effect-at-grace-boundary",
                        [("delay + 2 * epsilon < grace", "delay + 2 * epsilon ≤ grace")],
                        "  omega\n\ntheorem weak_grace")
    check_lean_mutation(ROOT, command, source, "ignore-pinned-root",
                        [("¬durableRoots victim ∧ ¬pinnedRoots victim", "¬durableRoots victim ∧ True")],
                        "  exact reached.elim allowed.1 allowed.2")
    check_lean_mutation(ROOT, command, source, "allow-completion-at-trim-boundary",
                        [("observe + work < cadence", "observe + work ≤ cadence")],
                        "  omega\n\ntheorem conservative")
    check_lean_mutation(ROOT, command, source, "arm-without-clock-margin",
                        [("arm + 2 * epsilon ≤ deadline", "arm ≤ deadline")],
                        "  omega\n\ntheorem one_threshold")


def configure_tlc():
    java = CYCLE / "jdk/Contents/Home/bin/java"
    if java.is_file():
        os.environ.setdefault("JAVA_BIN", str(java))
    override = os.environ.get("LOGKEEPER_TLA_JAR")
    jar = Path(override) if override else CYCLE / "tools/formal/tla-1.7.4/tla2tools.jar"
    if override and not jar.is_file():
        raise SystemExit(f"TLC jar does not exist at {jar}")
    if jar.is_file():
        cached = ROOT / ".tools/tla2tools.jar"
        cached.parent.mkdir(exist_ok=True)
        if not cached.exists():
            cached.symlink_to(jar.resolve())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("suite", choices=["all", "physical", "cuts", "erasure", "lean"],
                        nargs="?", default="all")
    suite = parser.parse_args().suite
    if suite != "lean":
        configure_tlc()
    for name, verify in (("physical", verify_physical), ("cuts", verify_cuts),
                         ("erasure", verify_erasure), ("lean", verify_lean)):
        if suite in ("all", name):
            verify()
