#!/usr/bin/env python3
"""Check the local installation effect and the separate ordered-use boundary."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
from ordered_source_modules import ORDERED_SOURCE_MODULES
from study_tools import check_lean_mutation, check_lean_theorems, check_tla, command_in, compile_lean_modules


def check(scenario, name, laws=(), *, progress=False, expected=None):
    checks = [("INVARIANT", law) for law in laws]
    specification = "Spec"
    if progress:
        if scenario == "reopen":
            specification = "FairReopen"
            checks.append(("PROPERTY", "ReopensCurrent"))
        else:
            specification = "FairOverlap"
            checks.append(("PROPERTY", "CompletesProtected"))
    variant = name if expected else "reference"
    check_tla(ROOT, "AtomicPublication", name, specification,
              {"Variant": f'"{variant}"', "Scenario": f'"{scenario}"'}, checks, expected=expected)


def verify_tla():
    check("advance", "reuse-check", ("ExactAtEffect",), expected="ExactAtEffect")
    check("replace", "skip-revision", ("ExactAtEffect",), expected="ExactAtEffect")
    check("restart", "skip-run", ("ExactAtEffect",), expected="ExactAtEffect")
    check("reuse-route", "skip-lineage", ("ExactAtEffect",), expected="ExactAtEffect")
    check("duplicate", "overwrite", ("SingleAttach",), expected="SingleAttach")
    check("uncertain", "image-authorizes", ("OnlyAuthorityAdmits",), expected="OnlyAuthorityAdmits")
    check("stopped", "ignore-stop", ("OnlyHeldCompletes",), expected="OnlyHeldCompletes")
    check("overlap", "require-online-at-delivery", progress=True, expected="liveness")

    laws = ("ExactAtEffect", "SingleAttach", "OnlyAuthorityAdmits", "OnlyHeldCompletes")
    for scenario in ("advance", "replace", "restart", "reuse-route", "duplicate", "uncertain", "stopped"):
        check(scenario, scenario, laws)
    check("overlap", "protected-completion", laws, progress=True)
    check("reopen", "reopen-current", laws, progress=True)


def verify_lean():
    command = compile_lean_modules(ROOT, (*ORDERED_SOURCE_MODULES,
                                        "33-activation-slot/ActivationSlot.lean",
                                        "75-joint-realized-replay/RankedJointReplay.lean",
                                        "76-stable-writer-handoff/StableGrant.lean",
                                        "79-rtdb-failover/RTDBFailover.lean",
                                        "80-applied-barrier-receipt/AppliedBarrierReceipt.lean",
                                        "81-recoverable-read-admission/RecoverableRead.lean",
                                        "82-joint-read-recovery/JointReadRecovery.lean",
                                        "83-ordered-read-replay/ReadInvocationFloor.lean",
                                        "83-ordered-read-replay/OrderedReadReplay.lean",
                                        "84-read-invocation-floor/InvocationFloorProof.lean",
                                        "85-ranked-named-recovery/RankedNamedRecovery.lean",
                                        "86-atomic-recovery-publication/AtomicPublication.lean"))
    source = ROOT / "AtomicPublication.lean"
    check_lean_mutation(ROOT, command, source, "omit-session",
                        [("endpoint.stamp = stamp ∧ endpoint.opened = none\n\ntheorem attachment",
                          "{endpoint.stamp with session := stamp.session} = stamp ∧ endpoint.opened = none\n\ntheorem attachment")],
                        "  exact Iff.rfl\n\nnoncomputable def attach")
    check_lean_mutation(ROOT, command, source, "cache-delegates-read-authority",
                        [("gate.authority stamp call ∧ gate.authenticate call\n\ntheorem starting",
                          "stamp.session = stamp.session ∧ gate.authenticate call\n\ntheorem starting")],
                        "  exact Iff.rfl\n\nstructure ReplyUse")

    harness = ROOT / "ReplyUsePrivacy.lean"
    code, log, _ = command_in(ROOT, ROOT / ".results" / "privacy-baseline", [*command, str(harness)])
    if code:
        raise SystemExit(f"Compile-fail baseline did not compile; see {log}")
    forged = """

def forge {capacity : Nat} {Borrow Signature : Type} (call : RTDBFailover.Invocation)
    (permit : RecoverableRead.Permit capacity) (basis : SnapshotAdmission.Basis)
    (borrow : Borrow) (packet : AppliedBarrierReceipt.Packet Signature) : ReplyUse capacity Borrow Signature :=
  ⟨call, permit, basis, borrow, packet⟩
"""
    check_lean_mutation(ROOT, command, harness, "forge-reply-use",
                        [("  finishReply use held\n", "  finishReply use held\n" + forged)],
                        "  ⟨call, permit, basis, borrow, packet⟩")
    redirected = """

def redirect {capacity : Nat} {Borrow Signature : Type} (original : ReplyUse capacity Borrow Signature)
    (replacement : Borrow) : ReplyUse capacity Borrow Signature :=
  {original with borrow := replacement}
"""
    check_lean_mutation(ROOT, command, harness, "redirect-reply-borrow",
                        [("  finishReply use held\n", "  finishReply use held\n" + redirected)],
                        "  {original with borrow := replacement}")
    for control, expected in (
        ("forge-reply-use", "Constructor for `AtomicPublication.ReplyUse` is marked as private"),
        ("redirect-reply-borrow", "constructor for `ReplyUse` is marked as private"),
    ):
        diagnostic = (ROOT / ".results" / f"lean-control-{control}" / "run.log").read_text()
        if expected not in diagnostic:
            raise SystemExit(f"{control} did not fail at the private ReplyUse constructor")
    check_lean_theorems(ROOT, command, source, count=19)


if __name__ == "__main__":
    if not sys.argv[1:] or sys.argv[1:] == ["tla"]:
        verify_tla()
    if not sys.argv[1:] or sys.argv[1:] == ["lean"]:
        verify_lean()
