# Study 104 · Order read-policy verification and its rotation

2026-11-23

## Verdict

Use the verifier installed at each command's ordered position.
A new width offer carries a canonical signed statement of the exact lineage, successor writer, requested width and verifier version.
The proposal and its signature travel together in the chosen frame.
The existing grant reducer compares the authenticated statement with the exact applied successor.

Choose verifier replacement in the existing journal, with a strictly higher bounded version and exact administrative authorization.
Verification of that rotation uses its own administrative evidence.
It does not require a response from the retiring policy signer.
A late offer from the retired version cannot make another width change.

Each named checkpoint carries its active public verifier descriptor.
Replay starts with that descriptor and processes each chosen rotation as an inline state transition.
A new checkpoint can absorb those old frames only once the predecessor is no longer selectable and any independent use has released the required evidence.
There is no separate per-grant verification history to query.

## Evidence

Lean 4.35.0 checked fourteen theorems with standard axioms only.

| Guarantee | Evidence and premises |
| --- | --- |
| Exact signed bytes | `a_policy_message_round_trips_exactly`, `decoded_policy_bytes_have_one_canonical_encoding` and `each_policy_message_has_a_fixed_signed_size` check the domain tag and eight unsigned words. The signature itself and public key format are abstract. |
| Current authority | `a_verified_offer_returns_only_its_exact_signed_scope`, `a_fresh_changed_policy_must_use_its_current_exact_signed_message`, and `an_inline_offer_with_a_retired_version_cannot_change_the_current_width` use the inline signed bytes and the installed verifier at application. |
| Ordered rotation | `rotation_is_an_ordered_administrative_decision_without_a_policy_packet` and `every_decision_keeps_or_advances_the_verifier_version` require the independent administrative rule and the bounded format. |
| Named historical verifier and exact replay | `a_historical_verifier_is_named_in_the_authentic_checkpoint`, `rotated_policy_recovers_identically_from_either_certified_base` and `an_actual_crash_choice_replays_the_exact_inline_verifier_history` use the exact authenticated named body, certified applied base, chosen suffix and modeled media rules. |

The Lean control removes the exact current-version check.
The law that admits only the current version fails at the declared proof step.

TLC 2.19 exhausts five reference configurations.
The older-selector case has six distinct states and the newer-selector case seven.
The valid current, late retired and rival offer cases each have five.
Eligible local actions are weakly fair.
The signing service is unavailable throughout.

| Deliberate comparison | Evidence |
| --- | --- |
| Accept a retired version for new offers | Unauthorized fresh admission in two transitions. |
| Take grant fields from outside the signed statement | A changed request accepts in two transitions. |
| Collect public verification material at visible publication | The still-selectable predecessor loses its verifier in three transitions. |
| Skip an earlier decision once the current verifier rejects its offer | Recovery returns the wrong width in three transitions. |
| Verify all history with the current descriptor | The older selector remains blocked after rotation. |
| Require policy-service contact to verify history | The available historical verifier and exact bytes still cannot recover. |
| Require the retiring policy signer to replace itself | Rotation stalls during its outage even with administrative authorization. |

## Amendments

[A412–A416](../amendments.md#study-104--2026-11-23) bind policy offers to exact signed bytes, order the verifier transition, and keep historical material under the normal selector and suffix lifetime.

## Limits

The checked codec establishes the canonical message and its fixed byte count.
The proof models cryptographic verification and administrative authorization as stable predicates on exact evidence.
The deployed key and signature encodings, compromise and revocation policy, signer provisioning, and the full authenticated command, checkpoint and quorum certificate formats remain separate obligations.
A chosen historical outcome stays governed by its original evidence.
Revising the product behavior after a suspected compromise requires an explicit ordered policy.
Independent external receipts may retain additional public verifiers under their own lifetime contracts.

## Reproduction

```sh
JAVA_BIN=/path/to/jdk/bin/java LEAN_BIN=/path/to/elan/bin/lean \
  python3 verification/104-ordered-policy-verifiers/run.py
```

[run.py](run.py) records each command, finite comparison and proof diagnostic under .results/.
