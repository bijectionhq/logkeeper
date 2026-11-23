#!/usr/bin/env python3
"""Check RTDB-shaped checkpoint demands and exact held recovery receipts."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent))
import re

from study_tools import check_lean_mutation, check_lean_theorems, check_tla, command_in, compile_lean_modules


def closure(name, scenario, *, policy="exact", law=None, expected=None):
    constants = {"Scenario": f'"{scenario}"', "Policy": f'"{policy}"'}
    laws = (law,) if law else ("CompleteReadSet", "ExactCarrier", "ExactChildren", "DistinctDomains")
    check_tla(ROOT, "ClosureCertificate", name, "Spec", constants, [("INVARIANT", key) for key in laws],
              expected=expected)


def receipts(name, policy, *, law="ExactRecoverablePublication", progress=False, expected=None):
    checks = [("INVARIANT", law)]
    if progress:
        checks.append(("PROPERTY", "EventuallyRestores"))
    check_tla(ROOT, "RankedReceipts", name, "Fair" if progress else "Spec", {"Policy": f'"{policy}"'},
              checks, expected=expected)


def check_lean_weakening(command, source, name, edits, failing):
    """Require a weakened enumeration to break exactly the named declarations."""
    mutated = source.read_text(encoding="utf-8")
    for old, new in edits:
        if mutated.count(old) != 1:
            raise SystemExit(f"Lean control {name}: ambiguous mutation")
        mutated = mutated.replace(old, new)
    case = ROOT / ".results" / f"lean-control-{name}"
    case.mkdir(parents=True, exist_ok=True)
    file = case / source.name
    file.write_text(mutated, encoding="utf-8")
    code, log, output = command_in(ROOT, case, [*command, str(file)])
    lines = mutated.splitlines()
    owners = set()
    for match in re.finditer(rf"{re.escape(source.name)}:(\d+):\d+: error", output):
        line = int(match.group(1))
        owner = next((entry for entry in reversed(lines[:line])
                      if re.match(r"(theorem|def) ", entry)), "")
        owners.add(owner.split()[1] if owner else "")
    if code == 0 or owners != set(failing):
        raise SystemExit(f"Lean control {name}: failures in {sorted(owners)}; see {log}")
    print(f"lean-control-{name}: proof failed only in {', '.join(sorted(owners))}", flush=True)


def verify_tla():
    for scenario, policy in (
        ("suffix", "base-only"),
        ("retained", "exclude-retained-L0"),
        ("artefact", "exclude-artefacts"),
        ("other-selector", "visible-only"),
        ("inline-upload", "payloads-only"),
        ("oversized-upload", "payloads-only"),
    ):
        closure(f"{policy}-{scenario}" if policy == "payloads-only" else policy, scenario, policy=policy,
                law="CompleteReadSet", expected="CompleteReadSet")
    closure("reuse-original-hold-after-relocation", "relocation", policy="logical-path-only",
            law="ExactCarrier", expected="ExactCarrier")
    closure("legacy-catalog-has-a-different-table-body", "legacy", policy="legacy-root-alone",
            law="ExactChildren", expected="ExactChildren")
    closure("count-two-members-of-the-same-pack", "pack", policy="count-logical-members",
            law="DistinctDomains", expected="DistinctDomains")
    receipts("forget-receipts-during-voter-replacement", "carry-position-only", progress=True,
             expected="liveness")
    receipts("open-from-a-cut-without-the-receipts", "trust-cut-only",
             expected="ExactRecoverablePublication")
    receipts("require-the-previous-publisher", "require-old-publisher", progress=True,
             expected="liveness")

    for scenario in ("complete", "suffix", "retained", "artefact", "other-selector", "relocation",
                     "legacy", "pack", "inline-upload", "oversized-upload"):
        closure(f"exact-{scenario}", scenario)
    closure("serve-after-new-generation-grant-witness", "relocation",
            law="NeverServesRelocatedVersion", expected="NeverServesRelocatedVersion")
    receipts("recover-exact-receipts-with-old-publisher-offline", "reference", progress=True)
    receipts("older-selector-receipt-witness", "reference", law="NeverRestoresFromOlder",
             expected="NeverRestoresFromOlder")
    receipts("newer-selector-receipt-witness", "reference", law="NeverRestoresFromNewer",
             expected="NeverRestoresFromNewer")


def verify_lean():
    deps = (
        "07-reference/Kernel.lean",
        "12-quorum-membership/JournalRefinement.lean",
        "26-journal-rotation/JournalRotation.lean",
        "27-prefix-consensus/PrefixAgreement.lean",
        "27-prefix-consensus/DurableAcceptor.lean",
        "32-configuration-closure/ConfigurationClosure.lean",
        "105-service-scope-protection/ScopeProtection.lean",
    )
    command = compile_lean_modules(ROOT, deps)
    source = ROOT / "RecoveryClosure.lean"
    check_lean_mutation(ROOT, command, source, "ignore-containing-generation",
                        [("grant.key = key ∧ grant.physical = physical",
                          "grant.key = key ∧ physical = physical")],
                        "  exact bound.2.2")
    check_lean_weakening(command, source, "outer-envelope-only",
                         [("payloadKeys record ++ bodyKeys selected record.body",
                           "payloadKeys record ++ (bodyKeys selected record.body).filter (fun _ => false)")],
                         {"chosen_suffix_enumeration_keeps_payloads_and_decoded_bodies"})
    check_lean_weakening(command, source, "upload-root-without-catalog",
                         [(".root index :: catalogKeys selected index ++ addedKeys tries",
                           ".root index :: addedKeys tries")],
                         {"body_enumeration_matches_each_driver_branch"})
    check_lean_weakening(command, source, "ignore-added-tries",
                         [("| .triesAdded storage tries => if storage = selected.storage then addedKeys tries else []",
                           "| .triesAdded _ _ => []")],
                         {"body_enumeration_matches_each_driver_branch"})
    check_lean_weakening(command, source, "storage-free-inline-tail",
                         [("  | .blockUploaded storage index tries =>\n      if storage",
                           "  | .blockUploaded storage index tries =>\n      if False ∧ storage")],
                         {"body_enumeration_matches_each_driver_branch"})
    check_lean_theorems(ROOT, command, source, count=25)


if __name__ == "__main__":
    if sys.argv[1:] in ([], ["tla"]):
        verify_tla()
    if sys.argv[1:] in ([], ["lean"]):
        verify_lean()
