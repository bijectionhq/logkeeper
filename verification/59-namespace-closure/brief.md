# Study 59 · Close the provisioning authority

2026-11-23

## Question

Which root state can certify complete disposition of a pool namespace while delayed guard-provisioning requests, old payload operations, and external copies may still exist?

## Sources

Use [bounded incarnation inventory](../55-pool-incarnations/report.md), [finite issuance](../56-finite-inventory/report.md), [ordered inventory recovery](../57-ordered-inventory-recovery/report.md), and [guarded provider slots](../58-storage-effect-boundary/report.md).

## Model

Place namespace and guard creation behind an already provisioned durable root that survives its subordinate namespaces.
Use a funded finite guard plan per namespace.
Compare exact scoped creation with an application precheck followed by raw create.
Compare sealed draining and atomic cancellation of an exactly empty bank with treating an empty observation as terminal evidence or waiting for all old creates to respond.
Use Lean to compose the root with the child guarded-slot reducer and incarnation settlement.

## Properties

- A guard can first materialize only in an exact live funded namespace and planned slot.
- A parent fence stops new guards and payload admission while already funded effects can settle.
- Terminal evidence covers every guard, original child payload, and independent effect in the retired scope.
- Retirement remains terminal through retries, root recovery, and a fresh namespace at the same address.
- The root's namespace high water survives retirement without retaining a row per closed namespace.

## Tools

Use TLC 2.19 with a single worker, a 512 MiB heap, and 60 seconds per case.
Use Lean 4.35.0 for scoped creation, guarded-slot composition, and exact terminal evidence.
