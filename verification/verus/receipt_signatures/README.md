# Ordered receipt signatures and repair keys

PL12 checks the Rust functions imported from `src/ordered` by
[`production.rs`](production.rs). The manifest lists the application functions
and each control's required diagnostic. The checked functions run in the
normal application path and their Verus annotations erase in Rust builds.

```sh
tools=/Users/sachaichbiah/code/codesign-agents/tools
python3 verification/verus/run.py --verus "$tools/verus" receipt_signatures
cd verification/lean
~/.elan/bin/lake build
```

## Correspondence to the Lean reference

The definitions and theorems below are in
[`Logkeeper.Premises`](../../lean/Logkeeper/Premises.lean).
[`reference.rs`](reference.rs) projects the Rust types to those definitions
and [`laws.rs`](laws.rs) composes the checked decisions.

| Lean definition or theorem | Shipped code and correspondence |
| --- | --- |
| `SignatureScope.exactBarrierInvocation`, `canonicalStart`, `canonical_fields_bind_claim`, `accepted_barrier_binds_claim` | [`BarrierVerifier::verify`](../../../src/ordered/daemon/sign/verification.rs) checks the barrier command, both placements, the worker enrollment, and the complete invocation ID. [The claim encoder and decoder](../../../src/ordered/codec/signed.rs) bind the placement, enrollment, nonce and expiry, decision position, checkpoint and through cut. The decoder derives the start cut from the checkpoint. Fixed-width fields make the encoding injective for claims with that start cut. The issuer's claim has that form because `Command::Barrier` calls `State::protect` and `Chosen::barrier_claim` carries its hold. |
| `SignatureScope.exactBarrierReceipt`, `exactReceiptScope`, `accepted_barrier_receipt_is_exact` | [The wire guards](../../../src/ordered/service/wire/receipt.rs) require a signed claim for a successful barrier and equate the complete receipt hold, placement, principal, invocation, and decision position to the claim. [`Input::decision`](../../../src/ordered/codec/service.rs) checks this relation after decoding. [`Reply::matches`](../../../src/ordered/service/wire.rs) binds the receipt to the route and request. [`Client::call_cohort`](../../../src/ordered/daemon.rs) authenticates the claim before returning the reply. The composition law equates the receipt's hold and cut to the signed claim. Ordinary decision receipts carry their coordinates on the authenticated application channel. |
| `SignatureScope.verify`, `rotation_domain_is_distinct` | [`RotationSlots::signing_bytes`](../../../src/ordered/codec/signed.rs) prepends `logkeeper.ordered-rotation-slots.v1` to the exact decision and evidence encodings. [The server](../../../src/ordered/service/wire.rs) signs that preimage and [`BarrierVerifier::verify_rotation`](../../../src/ordered/daemon/sign/verification.rs) verifies the same construction at the installed placement and cohort, with the evidence coverage check. The Verus law shows its first byte differs from that of `LKBRAR04` and rejects an otherwise recognized barrier signature in the rotation verifier. |
| `BarrierKeys.verificationKeys`, `validSuccessorKeys`, `valid_successor_extends_rotations`, `retained_across_rotations` | [`ReceiptKeys`](../../../src/ordered/daemon/receipt_keys.rs) constructs the union of the active, predecessor, and retained key sets and checks that the successor includes the entire predecessor union. Lean projects the lists by membership and lifts the verified step to every finite rotation chain. [`Manifest::application_route` and `Client::new`](../../../src/ordered/daemon.rs) export the union and install it in the client verifier. |
| `BarrierKeys.repairAuthority`, `repair_authority_is_active` | [`Manifest::seal_repair`](../../../src/ordered/daemon/repair.rs) resolves the exact predecessor identity and checks the successor keys against that predecessor's active roster. [The installer authentication](../../../src/ordered/daemon/repair/authentication.rs) looks up the package issuer in the target's predecessor list and verifies the seed bytes using that key. The composed law shows that successful validation and package verification imply that the authenticating key belongs to the immediate predecessor's active roster. |

A barrier placement includes deployment, incarnation, group, and generation.
The physical cohort digest is a separate coordinate used for successor
authorization and rotation evidence. The invocation ID includes both the
nonce and its expiry. The hold includes the exact history digests for the
checkpoint, start and through cuts.

## Boundaries and evidence

- `signed_message(key, signature)` is uninterpreted and identifies the
  original message bytes under that key. Signature verification succeeds
  exactly for those bytes. Its Lean view separates domain and payload.
  The ring implementation and SHA-256 collision resistance are premises.
  Fingerprint lookup uses exact public-key identifiers. Preservation of every
  public key in the map additionally uses the absence of issuer hash
  collisions among installed keys.
- The harness models UUID bytes, exact structural equality, standard map
  and set operations, and buffer appends. The placement, invocation,
  checkpoint, and cut encoders are checked Rust. Decoder field readers can
  return arbitrary typed values for the start-cut normalization law.
  Rotation receipt and evidence body encoding stay abstract. The proof
  checks their exact inputs and prefix, and takes `RotationSlots::covers`
  as a boundary for L13.
- Trusted route distribution and consistent use of the same destination
  manifest for sealing and installation are installation premises. The
  proof covers the key projection and verification guards under those
  premises. It leaves transport authentication, key custody, and
  establishment of a live read hold to their respective layers.
- Lean is parametric in the coordinate types and proves retention for
  arbitrary finite rotation chains. Reachability witnesses include two
  rotations over three keys, one exact barrier and one rotation signature.
  The five named negative witnesses cover dropped history, historical
  repair authority, omitted invocation, changed receipt cut, and omitted
  domain.
