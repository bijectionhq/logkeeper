# Study 42 · Compose ranked recovery, custody, and capacity

2026-11-23

## Question

Can an exact quorum handoff complete after its source seals when ordinary capacity is full and the old accepted image still has physical custody?

## Sources

Use the [requirements](../requirements.md), the [stream reducer](../28-ordered-application/OrderedApplication.lean), [ranked quorum handoff](../32-configuration-closure/ConfigurationClosure.lean), [activation slot recovery](../33-activation-slot/report.md), and [provider disposition](../40-provider-io-closure/ProviderIOClosure.lean).

## Model and comparison

Put the chosen stream prefix, final-residency reservation, replacement workspace, and old custody charge in the same model.
Compare reserving the recoverable envelope with reserving the currently learned bytes or staging bytes alone.
Exercise a hidden accepted cut, simultaneous old and replacement images, ordinary contention, provider outage, and settlement.
Treat footprint measurement, current quorum installation, and authentic physical evidence as explicit interfaces.

## Properties and acceptance

- Bind a capacity promise to the largest eligible ranked cut, including its fallback basis.
- Preserve prior chosen outcomes and the old physical charge while moving to an exact install.
- Use pre-reserved final residency and workspace to install with the ordinary pool full.
- Fail safely when ordinary work can borrow the progress reserve or when only one image fits.
- Keep an obsolete candidate charged during a custody outage and release it after exact stable absence.
- Check that a post-seal resource guarantee survives restart and that a different exact image cannot spend the reservation.

## Tools

Use TLC 2.19 with one worker, a 512 MiB heap, and 60 seconds per case.
Use Lean 4.35.0 for arbitrary finite traces and composition with the imported reference laws.
