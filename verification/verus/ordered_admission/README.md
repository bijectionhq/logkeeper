# Logkeeper ordered admission in Verus

The harness includes `src/ordered/admission.rs`, which the production ordered reducer and compact-image decoder call. It specifies checked byte debits, suffix protection, receipt retention at the expiry boundary and exact fingerprint matching. The harness composes these decisions for a full ordinary window and independently funded maintenance.

Use an installed Verus release with the proof entry point `verification/verus/ordered_admission/proof.rs`. Keep admission contracts free of assumed function specifications, proof stubs and unchecked external bodies. The ordinary Cargo build uses the same function bodies and erases the annotations.

This proof slice covers those executable decisions. The full disk-image encode/decode round trip, receipt-map preservation, quorum protocol and RTDB deployment path have independent model and test obligations. Treat the hash as the externally implemented identity primitive and review the canonical encoding and provider assumptions separately.

Proof execution has yet to be authorized.
