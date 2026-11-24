# Verus and Lean correspondence inventory

The harness rows cover every function in `verification/verus/*/laws.rs` and
`proof.rs` except each entry point `main`. The additional rows name imported
predicates and selected dependency helpers. `specs.json` resolves qualified Lean
names for the mechanically linked definitions. Short Lean names below refer to
the module named in each Verus area's README.

- **Equivalence** is checked by Lean against a definition generated from the named Rust source.
- **Predicate link** identifies the checked predicate or projection used by the
  law. The law's executable proof remains with Verus. Remaining aspects of the
  correspondence are described in the row or in the area README.
- **Open** identifies the untranslated construct or the missing projection.
- **Local** or **Translated helper** identifies a function with no independent Lean counterpart claimed.

| Rust source | Symbol | Lean counterpart | Coverage |
| --- | --- | --- | --- |
| `src/ordered/codec/frame.rs` | `bodyLengthBounded` | `Logkeeper.Codec.bodyLengthBounded` | Equivalence |
| `src/ordered/codec/frame.rs` | `commandVersion` | `Logkeeper.Codec.commandVersion` | Equivalence |
| `src/ordered/codec/frame.rs` | `decisionHeader` | `Logkeeper.Codec.decisionHeader` | Equivalence |
| `src/ordered/codec/frame.rs` | `decisionHeaderMatches` | `Logkeeper.Codec.decisionHeaderMatches` | Equivalence |
| `src/ordered/codec/frame.rs` | `decisionRequestBytes` | `Logkeeper.Codec.decisionRequestBytes` | Equivalence |
| `src/ordered/codec/frame.rs` | `flagByte` | `Logkeeper.Codec.flagByte` | Equivalence |
| `src/ordered/codec/frame.rs` | `objectNameCountFits` | `Logkeeper.CompactImage.objectNameCountFits` | Equivalence |
| `src/ordered/codec/frame.rs` | `readFixedField` | `Logkeeper.Codec.readFixedField` | Equivalence |
| `src/ordered/codec/frame.rs` | `readFlag` | `Logkeeper.Codec.readFlag` | Equivalence |
| `src/ordered/codec/frame.rs` | `withdrawalIdentityAdmissible` | `Logkeeper.Codec.withdrawalIdentityAdmissible` | Equivalence |
| `src/ordered/codec/frame.rs` | `withdrawnWorkerCountBounded` | `Logkeeper.Codec.withdrawnWorkerCountBounded` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `allSnapshotRowsValid` | `Logkeeper.CompactImage.allSnapshotRowsValid` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `boundedMap` | `Logkeeper.CompactImage.boundedMap` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `checksSnapshotRow` | — | Open — closure-call specification |
| `src/ordered/codec/snapshot_checks.rs` | `fenceRowValid` | `Logkeeper.CompactImage.fenceRowValid` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `generationInRange` | `Logkeeper.CompactImage.generationInRange` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `holdReceiptMatches` | `Logkeeper.CompactImage.holdReceiptMatches` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `lastSnapshotKey` | — | Local — maximal element of the native map |
| `src/ordered/codec/snapshot_checks.rs` | `leaseRowValid` | `Logkeeper.CompactImage.leaseRowValid` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `objectControlTrailerCanonical` | `Logkeeper.CompactImage.objectControlTrailerCanonical` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `oldRootKeyIncreases` | `Logkeeper.CompactImage.oldRootKeyIncreases` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `receiptExpiryPartition` | `Logkeeper.CompactImage.receiptExpiryPartition` | Open — stored receipt fields and map-to-retry-row projection |
| `src/ordered/codec/snapshot_checks.rs` | `receiptPartition` | `Logkeeper.CompactImage.receiptPartition` | Open — stored receipt fields and map-to-retry-row projection |
| `src/ordered/codec/snapshot_checks.rs` | `receiptPositionFresh` | `Logkeeper.CompactImage.receiptPositionFresh` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `receiptPositionsUnique` | `Logkeeper.CompactImage.receiptPositionsUnique` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `receiptRowValid` | `Logkeeper.CompactImage.receiptRowValid` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `reducerInvariant` | `Logkeeper.CompactImage.reducerInvariant` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `rootReferenceRowValid` | `Logkeeper.CompactImage.rootReferenceRowValid` | Equivalence |
| `src/ordered/codec/snapshot_checks.rs` | `strictlyIncreasingKeys` | `Logkeeper.CompactImage.strictlyIncreasingKeys` | Equivalence |
| `src/ordered/lease_reducer.rs` | `after_disposal` | `DisposalLease.OwnerStep.dispose` | Open — owner-scoped map and hold backing projection |
| `src/ordered/lease_reducer.rs` | `after_prune` | `DisposalLease.OwnerImage.prune` | Open — owner-scoped map and hold backing projection |
| `src/ordered/lease_reducer.rs` | `held_by` | `DisposalLease.OwnerImage.backed` | Open — owner-scoped map and hold backing projection |
| `src/ordered/lease_reducer.rs` | `interval_available` | `DisposalLease.interval_available` | Equivalence |
| `src/ordered/lease_reducer.rs` | `retired_rows` | `DisposalLease.OwnerStep.dispose` | Open — owner-scoped map and hold backing projection |
| `src/ordered/object_names.rs` | `objectNameBefore` | `Logkeeper.CompactImage.objectNameBefore` | Open — pivot-based comparison versus inductive list lexicographic order |
| `src/ordered/object_names.rs` | `objectNamesCanonical` | `Logkeeper.CompactImage.objectNamesCanonical` | Open — fixed-width and adjacency projection |
| `src/ordered/object_names.rs` | `orderAt` | `Logkeeper.CompactImage.objectNameBefore` | Open — pivot-based comparison versus inductive list lexicographic order |
| `src/ordered/object_names.rs` | `zeroName` | `Logkeeper.CompactImage.zeroName` | Equivalence |
| `src/ordered/object_withdrawal.rs` | `referenced` | `Logkeeper.ObjectWithdrawal.referenced` | Open — physical root and suffix ownership projection |
| `src/ordered/replication/rules.rs` | `ballot_lt` | `Logkeeper.PrefixAgreement.ballotRank` | Equivalence |
| `src/ordered/replication/slot_header.rs` | `big_endian_round_trips` | `Logkeeper.VoterSlotHeader.big_endian_round_trips` | Open — bitvector operations or nested descriptor projection |
| `src/ordered/replication/slot_header.rs` | `decodeBE` | `Logkeeper.VoterSlotHeader.decodeBE` | Open — bitvector operations or nested descriptor projection |
| `src/ordered/replication/slot_header.rs` | `encodeBE` | `Logkeeper.VoterSlotHeader.encodeBE` | Open — bitvector operations or nested descriptor projection |
| `src/ordered/replication/slot_header.rs` | `slotDescriptor` | `Logkeeper.VoterSlotHeader.slotDescriptor` | Open — bitvector operations or nested descriptor projection |
| `src/ordered/replication/slot_header.rs` | `slotHeaderLengthValid` | `Logkeeper.VoterSlotHeader.slotHeaderLengthValid` | Open — bitvector operations or nested descriptor projection |
| `src/ordered/replication/slot_header.rs` | `slotHeaderMatches` | `Logkeeper.VoterSlotHeader.slotHeaderMatches` | Open — bitvector operations or nested descriptor projection |
| `src/ordered/replication/slot_header.rs` | `voterSlotMagic` | `Logkeeper.VoterSlotHeader.voterSlotMagic` | Equivalence |
| `src/ordered/replication/transport_fields.rs` | `ballotBytes` | `Logkeeper.VoterTransport.ballotBytes` | Open — fixed-width word encoding and nested slot structures |
| `src/ordered/replication/transport_fields.rs` | `ballotValid` | `Logkeeper.VoterTransport.ballotValid` | Open — fixed-width word encoding and nested slot structures |
| `src/ordered/replication/transport_fields.rs` | `responseKind` | `Logkeeper.VoterTransport.responseKind` | Equivalence |
| `src/ordered/replication/transport_fields.rs` | `transportGroupMatches` | `Logkeeper.VoterTransport.transportGroupMatches` | Equivalence |
| `src/ordered/replication/transport_fields.rs` | `transportMagic` | `Logkeeper.VoterTransport.transportMagic` | Equivalence |
| `src/ordered/replication/transport_fields.rs` | `voteSlotsMatch` | `Logkeeper.VoterTransport.voteSlotsMatch` | Open — fixed-width word encoding and nested slot structures |
| `src/ordered/retention.rs` | `pinsSuffix` | `Logkeeper.Protocol.pinsSuffix` | Equivalence |
| `src/ordered/retention.rs` | `recordCredit` | `Logkeeper.Protocol.Credit.addDebit` | Equivalence |
| `src/ordered/retention.rs` | `trimCredit` | `Logkeeper.Protocol.trimCredit` | Equivalence |
| `verification/verus/compact_image/laws.rs` | `a_checked_hold_has_a_matching_receipt` | `CompactImage.holdReceiptMatches` | Predicate link via `link_holdReceiptMatches` |
| `verification/verus/compact_image/laws.rs` | `accepted_compact_image_bytes_reencode_exactly` | `CompactImage.accepted_compact_image_bytes_reencode_exactly` | Open — ordered map rebuild and full layout projection |
| `verification/verus/compact_image/laws.rs` | `accepted_fence_has_bounded_coordinates` | `CompactImage.fenceRowValid` | Predicate link via `link_fenceRowValid` |
| `verification/verus/compact_image/laws.rs` | `accepted_lease_has_retained_owner_and_bounds` | `CompactImage.leaseRowValid` | Predicate link via `link_leaseRowValid` |
| `verification/verus/compact_image/laws.rs` | `accepted_object_control_trailer_matches_encoder_presence` | `CompactImage.objectControlTrailerCanonical` | Predicate link via `link_objectControlTrailerCanonical` |
| `verification/verus/compact_image/laws.rs` | `accepted_old_root_rows_are_in_revision_order` | `CompactImage.oldRootKeyIncreases` | Predicate link via `link_oldRootKeyIncreases` |
| `verification/verus/compact_image/laws.rs` | `accepted_reference_has_known_root_and_increasing_key` | `CompactImage.rootReferenceRowValid` | Predicate link via `link_rootReferenceRowValid` |
| `verification/verus/compact_image/laws.rs` | `accepting_a_receipt_preserves_unique_decision_positions` | `CompactImage.receiptPositionFresh`, `receiptRowValid`, `receiptPartition`, `receiptExpiryPartition` | Predicate link via `link_receiptPositionFresh` (freshness and row guard. exact typed keys and expiry partition pending) |
| `verification/verus/compact_image/laws.rs` | `decoded_receipts_use_exact_retry_and_expiry_keys` | `CompactImage.receiptPositionFresh`, `receiptRowValid`, `receiptPartition`, `receiptExpiryPartition` | Predicate link via `link_receiptPositionFresh` (freshness and row guard. exact typed keys and expiry partition pending) |
| `verification/verus/compact_image/laws.rs` | `insertion_preserves_checked_snapshot_rows` | `CompactImage.allSnapshotRowsValid`, `boundedMap` | Predicate link via `link_allSnapshotRowsValid` (checked rows. map update and decoder construction pending) |
| `verification/verus/compact_image/laws.rs` | `one_invalid_hold_prevents_recovery` | `CompactImage.one_invalid_hold_prevents_recovery` | Predicate link via `link_allSnapshotRowsValid` (row predicate. closure-call specification and map traversal pending) |
| `verification/verus/compact_image/laws.rs` | `the_reducer_invariant_excludes_reused_receipt_positions` | `CompactImage.reducerInvariant`, `receiptPositionsUnique` | Predicate link via `link_reducerInvariant` (projected image. construction from native reducer state pending) |
| `verification/verus/compact_image/laws.rs` | `vacant_generation_obeys_epoch` | `CompactImage.generationInRange` | Predicate link via `link_generationInRange` |
| `verification/verus/compact_image/layout.rs` | `canonicalCompactImageLayout` | `Logkeeper.CompactImage.canonicalCompactImageLayout` | Open — typed admission conditions and exact consumed-byte layout projection |
| `verification/verus/compact_image/layout.rs` | `compactImageAdmissible` | `Logkeeper.CompactImage.compactImageAdmissible` | Open — typed admission conditions and exact consumed-byte layout projection |
| `verification/verus/compact_image/layout.rs` | `compactImageBytesAdmissible` | `Logkeeper.CompactImage.compactImageBytesAdmissible` | Open — typed admission conditions and exact consumed-byte layout projection |
| `verification/verus/compact_image/layout.rs` | `compactImageLayoutBytes` | `Logkeeper.CompactImage.compactImageLayoutBytes` | Open — typed admission conditions and exact consumed-byte layout projection |
| `verification/verus/compact_image/layout.rs` | `oldRootsInOrder` | `Logkeeper.CompactImage.strictlyIncreasingKeys` | Open — tuple row projection in the layout proof |
| `verification/verus/mirrored_voter_media/laws.rs` | `a_mismatched_digest_is_ineligible` | — | Local — digest comparison helper |
| `verification/verus/mirrored_voter_media/laws.rs` | `a_reply_requires_both_syncs` | `SelectionFence.SyncTrace`, `mirrored`, `reply_requires_both_syncs` | Open — guarded match and projection from physical write log to inductive trace |
| `verification/verus/mirrored_voter_media/laws.rs` | `a_sync_or_tear_keeps_the_acknowledged_rank` | `SelectionFence.Keeps`, `Step` | Predicate link via `link_keeps` (rank predicate) |
| `verification/verus/mirrored_voter_media/laws.rs` | `acknowledged` | `SelectionFence.SyncTrace`, `mirrored`, `reply_requires_both_syncs` | Open — guarded match and projection from physical write log to inductive trace |
| `verification/verus/mirrored_voter_media/laws.rs` | `any_surviving_slot_keeps_the_acknowledged_rank` | `SelectionFence.any_surviving_slot_keeps_the_acknowledged_rank`, `one_tear_leaves_the_mirrored_image` | Predicate link via `link_keeps` (rank predicate) |
| `verification/verus/mirrored_voter_media/laws.rs` | `ballot_le` | `Logkeeper.PrefixAgreement.ballotRank` | Equivalence |
| `verification/verus/mirrored_voter_media/laws.rs` | `dominates` | `Logkeeper.SelectionFence.Image.Dominates` | Equivalence |
| `verification/verus/mirrored_voter_media/laws.rs` | `keeps` | `Logkeeper.SelectionFence.Keeps` | Equivalence |
| `verification/verus/mirrored_voter_media/laws.rs` | `one_detectable_tear_after_ack_selects_the_acknowledged_image` | `SelectionFence.any_surviving_slot_keeps_the_acknowledged_rank`, `one_tear_leaves_the_mirrored_image` | Predicate link via `link_keeps` (rank predicate) |
| `verification/verus/mirrored_voter_media/laws.rs` | `promise_le` | — | Translated helper |
| `verification/verus/mirrored_voter_media/laws.rs` | `read_back_visits_both_physical_slots` | `SelectionFence.AtFence`, `MirrorsFence` | Open — physical read events, authenticated descriptors and external disk contracts |
| `verification/verus/mirrored_voter_media/laws.rs` | `selection_prefers_the_newer_generation` | `SelectionFence.selectSlot`, `selection_prefers_the_newer_generation` | Open — relation appears in the shipped selection contract, with error and slot-index projections |
| `verification/verus/mirrored_voter_media/laws.rs` | `state_of` | — | Translated helper |
| `verification/verus/mirrored_voter_media/laws.rs` | `sync_step` | `SelectionFence.SyncStep` | Open — guarded match and media-event projection |
| `verification/verus/mirrored_voter_media/laws.rs` | `sync_trace` | `SelectionFence.SyncTrace`, `mirrored`, `reply_requires_both_syncs` | Open — guarded match and projection from physical write log to inductive trace |
| `verification/verus/object_name_codec/laws.rs` | `admitted_object_names_are_bounded_sorted_unique_and_nonzero` | `CompactImage.objectNameBefore`, `objectNamesCanonical`, `admitted_object_names_are_bounded_sorted_unique_and_nonzero` | Open — fixed-width lexicographic and adjacent-list projections |
| `verification/verus/object_name_codec/laws.rs` | `increasing_names_are_pairwise_ordered` | `CompactImage.objectNameBefore`, `objectNamesCanonical`, `admitted_object_names_are_bounded_sorted_unique_and_nonzero` | Open — fixed-width lexicographic and adjacent-list projections |
| `verification/verus/object_name_codec/laws.rs` | `object_name_order_is_transitive` | `CompactImage.objectNameBefore`, `objectNamesCanonical`, `admitted_object_names_are_bounded_sorted_unique_and_nonzero` | Open — fixed-width lexicographic and adjacent-list projections |
| `verification/verus/object_withdrawal/laws.rs` | `canAdmitReferences` | `Logkeeper.ObjectWithdrawal.canAdmitReferences` | Equivalence |
| `verification/verus/object_withdrawal/laws.rs` | `canWithdraw` | `Logkeeper.ObjectWithdrawal.canWithdraw` | Equivalence |
| `verification/verus/object_withdrawal/laws.rs` | `fenced` | `Logkeeper.ObjectWithdrawal.fenced` | Equivalence |
| `verification/verus/object_withdrawal/laws.rs` | `fenced_refuses_opaque_references` | `ObjectWithdrawal.fenced`, `canAdmitReferences` | Predicate link via `link_fenced` (fence domain. opaque branch pending) |
| `verification/verus/object_withdrawal/laws.rs` | `fenced_refuses_reference` | `ObjectWithdrawal.fenced`, `canAdmitReferences` | Predicate link via `link_canAdmitReferences` (explicit names) |
| `verification/verus/object_withdrawal/laws.rs` | `referenced_refuses_withdrawal` | `ObjectWithdrawal.referenced`, `canWithdraw` | Predicate link via `link_canWithdraw` (given complete/live projections) |
| `verification/verus/object_withdrawal/laws.rs` | `retry_withdrawal_matches_version` | `ObjectWithdrawal.State.fence`, `order_preserves_fence` | Predicate link via `link_fenced` (membership. map update, exact version and trace composition pending) |
| `verification/verus/object_withdrawal/laws.rs` | `withdrawn_name_stays_fenced` | `ObjectWithdrawal.State.fence`, `order_preserves_fence` | Predicate link via `link_fenced` (membership. map update, exact version and trace composition pending) |
| `verification/verus/ordered_admission/laws.rs` | `debit` | `Logkeeper.OrderedAdmission.debit` | Equivalence |
| `verification/verus/ordered_admission/laws.rs` | `debit_matches_reference` | `OrderedAdmission.debit` | Predicate link via `link_debit` |
| `verification/verus/ordered_admission/laws.rs` | `debit_value` | — | Translated helper |
| `verification/verus/ordered_admission/laws.rs` | `fingerprint_equality_matches_reference` | `OrderedAdmission.matchesFingerprint` | Predicate link via `link_matchesFingerprint` |
| `verification/verus/ordered_admission/laws.rs` | `maintenance_at_data_ceiling` | `OrderedAdmission.maintenance_at_data_ceiling` | Predicate link via `link_debit` |
| `verification/verus/ordered_admission/laws.rs` | `matchesFingerprint` | `Logkeeper.OrderedAdmission.matchesFingerprint` | Equivalence |
| `verification/verus/ordered_admission/laws.rs` | `pinsSuffix` | `Logkeeper.OrderedAdmission.pinsSuffix` | Equivalence |
| `verification/verus/ordered_admission/laws.rs` | `pins_suffix_matches_reference` | `OrderedAdmission.pinsSuffix` | Predicate link via `link_pinsSuffix` |
| `verification/verus/ordered_admission/laws.rs` | `retainsReceipt` | `Logkeeper.OrderedAdmission.retainsReceipt` | Equivalence |
| `verification/verus/ordered_admission/laws.rs` | `retains_receipt_matches_reference` | `OrderedAdmission.retainsReceipt` | Predicate link via `link_retainsReceipt` |
| `verification/verus/ordered_budgets/laws.rs` | `admitted_ordinary_append_preserves_funding` | `OrderedBudgets.fundedBudget`, `appendBudget` | Predicate link via `link_fundedBudget` (invariant and charge. executable result projection pending) |
| `verification/verus/ordered_budgets/laws.rs` | `fundedBudget` | `Logkeeper.OrderedBudgets.fundedBudget` | Equivalence |
| `verification/verus/ordered_budgets/laws.rs` | `funded_window_implies_retained_room` | `OrderedBudgets.funded_window_implies_retained_room` | Predicate link via `link_fundedBudget` |
| `verification/verus/ordered_budgets/laws.rs` | `funding_new_window` | `OrderedBudgets.funding_new_window`, `trace_preserves_funding` | Predicate link via `link_fundedBudget` (funding predicate) |
| `verification/verus/ordered_budgets/laws.rs` | `maintenance_funding_is_independent` | `OrderedBudgets.fundedBudget`, `appendBudget` | Predicate link via `link_fundedBudget` (invariant and charge. executable result projection pending) |
| `verification/verus/ordered_budgets/laws.rs` | `recordCharge` | `Logkeeper.OrderedBudgets.recordCharge` | Equivalence |
| `verification/verus/ordered_budgets/laws.rs` | `record_charge_matches_reference` | `OrderedBudgets.referenceCharge`, `recordCharge` | Predicate link via `link_recordCharge` |
| `verification/verus/ordered_budgets/laws.rs` | `referenceCharge` | `Logkeeper.OrderedBudgets.referenceCharge` | Equivalence |
| `verification/verus/ordered_checkpoint/laws.rs` | `a_closed_checkpoint_refuses_new_acquisition` | `OrderedCheckpoint.a_closed_checkpoint_refuses_new_acquisition` | Predicate link via `link_may_acquire` |
| `verification/verus/ordered_checkpoint/laws.rs` | `a_held_checkpoint_cannot_close` | `OrderedCheckpoint.a_held_checkpoint_cannot_close` | Predicate link via `link_may_close` |
| `verification/verus/ordered_checkpoint/laws.rs` | `matches_preparation` | `Logkeeper.OrderedCheckpoint.matches_preparation` | Equivalence |
| `verification/verus/ordered_checkpoint/laws.rs` | `may_acquire` | `Logkeeper.OrderedCheckpoint.may_acquire` | Equivalence |
| `verification/verus/ordered_checkpoint/laws.rs` | `may_close` | `Logkeeper.OrderedCheckpoint.may_close` | Equivalence |
| `verification/verus/ordered_checkpoint/laws.rs` | `next_revision` | `Logkeeper.OrderedCheckpoint.next_revision` | Equivalence |
| `verification/verus/ordered_checkpoint/laws.rs` | `preparation_revision_advances` | `OrderedCheckpoint.preparation_revision_advances` | Predicate link via `link_next_revision` |
| `verification/verus/ordered_checkpoint/laws.rs` | `publication_keeps_prepared_custody` | `OrderedCheckpoint.publication_keeps_prepared_custody` | Predicate link via `link_matches_preparation` |
| `verification/verus/ordered_codec/domains.rs` | `commandAdmissible` | `Logkeeper.Codec.commandAdmissible` | Open — command and service domain projection through nested data-carrying variants |
| `verification/verus/ordered_codec/domains.rs` | `decisionBodyAdmissible` | `Logkeeper.Codec.decisionBodyAdmissible` | Open — command and service domain projection through nested data-carrying variants |
| `verification/verus/ordered_codec/domains.rs` | `optionalObjectNamesAdmissible` | `Logkeeper.Codec.optionalObjectNamesAdmissible` | Open — command and service domain projection through nested data-carrying variants |
| `verification/verus/ordered_codec/domains.rs` | `recordAdmissible` | `Logkeeper.Codec.recordAdmissible` | Open — command and service domain projection through nested data-carrying variants |
| `verification/verus/ordered_codec/domains.rs` | `serviceDecisionAdmissible` | `Logkeeper.Codec.serviceDecisionAdmissible` | Open — command and service domain projection through nested data-carrying variants |
| `verification/verus/ordered_codec/domains.rs` | `serviceOperationAdmissible` | `Logkeeper.Codec.serviceOperationAdmissible` | Open — command and service domain projection through nested data-carrying variants |
| `verification/verus/ordered_codec/domains.rs` | `serviceReplyAdmissible` | `Logkeeper.Codec.serviceReplyAdmissible` | Open — command and service domain projection through nested data-carrying variants |
| `verification/verus/ordered_codec/laws.rs` | `a_torn_object_name_is_rejected` | `CompactImage.objectNameCountFits` | Predicate link via `link_objectNameCountFits` |
| `verification/verus/ordered_codec/laws.rs` | `admitted_withdrawn_worker_count_round_trips` | `Codec.withdrawnWorkerCountBounded` | Predicate link via `link_withdrawnWorkerCountBounded` (count guard) |
| `verification/verus/ordered_codec/laws.rs` | `body_over_limit_is_rejected` | `Codec.bodyLengthBounded`, `boundedBodyLength` | Predicate link via `link_bodyLengthBounded` (decoder guard) |
| `verification/verus/ordered_codec/laws.rs` | `decision_request_bytes_round_trip` | `Codec.decisionRequestBytes`, `decision_body_round_trips_over_command_codec` | Predicate link via `link_decisionRequestBytes` (fixed header extent. supplied command codec remains independent) |
| `verification/verus/ordered_codec/laws.rs` | `decision_time_round_trips` | `Codec.decisionHeader`, `decisionHeaderMatches` | Predicate link via `link_decisionHeaderMatches` |
| `verification/verus/ordered_codec/laws.rs` | `fixed_field_round_trips_with_suffix` | `Codec.readFixedField` | Predicate link via `link_readFixedField` |
| `verification/verus/ordered_codec/laws.rs` | `flag_round_trips` | `Codec.flagByte`, `readFlag` | Predicate link via `link_readFlag` |
| `verification/verus/ordered_codec/laws.rs` | `noncanonical_flag_is_rejected` | `Codec.flagByte`, `readFlag` | Predicate link via `link_readFlag` |
| `verification/verus/ordered_codec/laws.rs` | `oversized_withdrawn_worker_count_is_rejected` | `Codec.withdrawnWorkerCountBounded` | Predicate link via `link_withdrawnWorkerCountBounded` (count guard) |
| `verification/verus/ordered_codec/laws.rs` | `referenced_commands_and_operations_share_the_name_domain` | `Codec.commandAdmissible`, `serviceOperationAdmissible` | Open — nested variant patterns and canonical name list projection |
| `verification/verus/ordered_codec/laws.rs` | `short_decision_header_is_rejected` | `Codec.decisionHeader`, `decisionHeaderMatches` | Predicate link via `link_decisionHeaderMatches` |
| `verification/verus/ordered_codec/laws.rs` | `withdrawal_command_admission_requires_both_nonzero_fields` | `Codec.withdrawalIdentityAdmissible` | Predicate link via `link_withdrawalIdentityAdmissible` |
| `verification/verus/ordered_codec/laws.rs` | `wrong_command_version_is_rejected` | `Codec.commandVersion` | Predicate link via `link_commandVersion` |
| `verification/verus/ordered_cohort/laws.rs` | `accept_quorum` | `Logkeeper.OrderedCohort.accept_quorum` | Equivalence |
| `verification/verus/ordered_cohort/laws.rs` | `accept_quorum_is_majority` | `OrderedCohort.accept_quorum_is_majority` | Predicate link via `link_accept_quorum` |
| `verification/verus/ordered_cohort/laws.rs` | `has_paid_repair_quorum` | `Logkeeper.OrderedCohort.has_paid_repair_quorum` | Equivalence |
| `verification/verus/ordered_cohort/laws.rs` | `matches_chosen_seal` | `Logkeeper.OrderedCohort.matches_chosen_seal` | Equivalence |
| `verification/verus/ordered_cohort/laws.rs` | `may_extend` | `Logkeeper.OrderedCohort.may_extend` | Equivalence |
| `verification/verus/ordered_cohort/laws.rs` | `repair_requires_the_chosen_destination` | `OrderedCohort.repair_requires_the_chosen_destination` | Predicate link via `link_matches_chosen_seal` |
| `verification/verus/ordered_cohort/laws.rs` | `seal_requires_paid_successor_quorum` | `OrderedCohort.seal_requires_paid_successor_quorum` | Predicate link via `link_has_paid_repair_quorum` |
| `verification/verus/ordered_cohort/laws.rs` | `sealed_cohort_refuses_new_decisions` | `OrderedCohort.sealed_cohort_refuses_new_decisions` | Predicate link via `link_may_extend` |
| `verification/verus/ordered_lease_reducer/laws.rs` | `expiry_disposal_clears_owner` | `DisposalLease.may_dispose`, `expiry_disposal_clears_owner`, `OwnerStep.dispose`, `unissued_disposal_is_noop` | Open — owner-scoped map updates and issued-history relation |
| `verification/verus/ordered_lease_reducer/laws.rs` | `old_root_cannot_renew` | `DisposalLease.checkpoint_open` | Open — inline checkpoint contract. compound guard checked in `link_read_lease_end` |
| `verification/verus/ordered_lease_reducer/laws.rs` | `pending_erasure_blocks_writer_changes` | `DisposalLease.writer_open`, `OwnerStep.vacate`, `ErasureCommit.generation_survives_vacancy` | Open — inline writer-open contract and mutable authority transition |
| `verification/verus/ordered_lease_reducer/laws.rs` | `read_lease_end` | `DisposalLease.read_lease_end` | Equivalence |
| `verification/verus/ordered_lease_reducer/laws.rs` | `read_lease_requires_exact_protected_basis` | `DisposalLease.read_lease_end`, `interval_available` | Predicate link via `link_read_lease_end` (access, exact owner, protected interval and end bound) |
| `verification/verus/ordered_lease_reducer/laws.rs` | `read_lease_retains_greatest_end` | `DisposalLease.retained_end`, `OwnerStep.leaseRead`, `OwnerStep.lease` | Open — mutation of the per-enrollment map and historical greatest-end projection |
| `verification/verus/ordered_lease_reducer/laws.rs` | `release_read_keeps_end_if_backed` | `DisposalLease.OwnerImage.prune`, `OwnerStep.release` | Open — hold/lease map mutation and backing projection |
| `verification/verus/ordered_lease_reducer/laws.rs` | `rotation_adds_recovery_without_dropping_existing_holds` | `DisposalLease.grant_holds`, `OwnerStep.rotate`, `ErasureCommit.erasure_floor` | Predicate link via `link_erasure_floor` (ordered rotation area. hold-map transition pending) |
| `verification/verus/ordered_lease_reducer/laws.rs` | `settlement_must_match_erasure_floor` | `DisposalLease.settlement_fence` | Open — inline settlement contract |
| `verification/verus/ordered_lease_reducer/laws.rs` | `vacancy_never_substitutes_for_enrollment` | `DisposalLease.read_lease_end`, `interval_available` | Predicate link via `link_read_lease_end` (access, exact owner, protected interval and end bound) |
| `verification/verus/ordered_lease_reducer/laws.rs` | `vacancy_preserves_epoch_and_generation` | `DisposalLease.writer_open`, `OwnerStep.vacate`, `ErasureCommit.generation_survives_vacancy` | Open — inline writer-open contract and mutable authority transition |
| `verification/verus/ordered_lease_reducer/laws.rs` | `withdrawal_preserves_pending_owners` | `DisposalLease.OwnerStep.enroll`, `OwnerStep.withdraw`, `OwnerImage.backed` | Open — exact ownership and held versus enrolled backing |
| `verification/verus/ordered_lease_reducer/laws.rs` | `writer_lease_does_not_regress_or_change_other_ends` | `DisposalLease.retained_end`, `OwnerStep.leaseRead`, `OwnerStep.lease` | Open — mutation of the per-enrollment map and historical greatest-end projection |
| `verification/verus/ordered_receipt/laws.rs` | `abstract_book` | `Logkeeper.Protocol.Ordered.abstract_book` | Equivalence |
| `verification/verus/ordered_receipt/laws.rs` | `barriers_never_replay` | `Protocol.Ordered.replay`, `replay_mutation`, `reissued_append_identifies_chosen_append` | Predicate link via `link_replay` (retry rule) |
| `verification/verus/ordered_receipt/laws.rs` | `expired_receipt_without_hold` | `Protocol.Ordered.retains_receipt` | Predicate link via `link_retains_receipt` (retention predicate. map update pending) |
| `verification/verus/ordered_receipt/laws.rs` | `expired_request_cannot_admit_fresh_work` | `Protocol.Ordered.fresh_request_expired` | Predicate link via `link_fresh_request_expired` |
| `verification/verus/ordered_receipt/laws.rs` | `expiry_preserves_recoverable_receipts` | `Protocol.Ordered.retains_receipt` | Predicate link via `link_retains_receipt` (retention predicate. map update pending) |
| `verification/verus/ordered_receipt/laws.rs` | `fresh_request_expired` | `Logkeeper.Protocol.Ordered.fresh_request_expired` | Equivalence |
| `verification/verus/ordered_receipt/laws.rs` | `mutation_receipt_within_horizon` | `Protocol.Ordered.retains_receipt` | Predicate link via `link_retains_receipt` (retention predicate. map update pending) |
| `verification/verus/ordered_receipt/laws.rs` | `mutation_retry_exact` | `Protocol.Ordered.replay`, `replay_mutation`, `reissued_append_identifies_chosen_append` | Predicate link via `link_replay` (retry rule) |
| `verification/verus/ordered_receipt/laws.rs` | `original_placement_matches` | `Logkeeper.Protocol.Ordered.original_placement_matches` | Equivalence |
| `verification/verus/ordered_receipt/laws.rs` | `reconciliation_requires_original_placement` | `Protocol.Ordered.original_placement_matches` | Predicate link via `link_original_placement_matches` |
| `verification/verus/ordered_receipt/laws.rs` | `record_after_apply` | `Logkeeper.Protocol.Ordered.record_after_apply` | Equivalence |
| `verification/verus/ordered_receipt/laws.rs` | `recording_uses_the_applied_outcome` | `Protocol.Ordered.abstract_book`, `positive_receipt_is_applied`, `refused_barrier_leaves_no_receipt` | Predicate link via `link_retain_applied` (lifecycle predicates and row projection) |
| `verification/verus/ordered_receipt/laws.rs` | `replay` | `Logkeeper.Protocol.Ordered.replay` | Equivalence |
| `verification/verus/ordered_receipt/laws.rs` | `replay_mutation` | `Logkeeper.Protocol.Ordered.replay_mutation` | Equivalence |
| `verification/verus/ordered_receipt/laws.rs` | `retain_applied` | `Logkeeper.Protocol.Ordered.retain_applied` | Equivalence |
| `verification/verus/ordered_receipt/laws.rs` | `retains_receipt` | `Logkeeper.Protocol.Ordered.retains_receipt` | Equivalence |
| `verification/verus/ordered_replay/laws.rs` | `included` | — | Local — ordered replay harness does not name a Lean counterpart |
| `verification/verus/ordered_replay/laws.rs` | `replay_head_and_page_charge_the_exact_successor` | — | Local — ordered replay harness does not name a Lean counterpart |
| `verification/verus/ordered_replay/laws.rs` | `resume_requires_exact_cut_in_original_interval` | — | Local — ordered replay harness does not name a Lean counterpart |
| `verification/verus/ordered_replay/laws.rs` | `selected_replay_indices_cover_exact_interval` | — | Local — ordered replay harness does not name a Lean counterpart |
| `verification/verus/ordered_rotation/laws.rs` | `admits_history` | `ErasureCommit.admits_history` | Equivalence |
| `verification/verus/ordered_rotation/laws.rs` | `erasure_floor` | `ErasureCommit.erasure_floor` | Equivalence |
| `verification/verus/ordered_rotation/laws.rs` | `exact_preparation` | `ErasureCommit.exact_preparation` | Equivalence |
| `verification/verus/ordered_rotation/laws.rs` | `generation_survives_vacancy` | `ErasureCommit.vacate`, `Step.grant` | Open — mutable authority projection through transition |
| `verification/verus/ordered_rotation/laws.rs` | `publication_closes_old_history` | `ErasureCommit.erasure_floor`, `admits_history` | Predicate link via `link_admits_history` (also links the floor calculation) |
| `verification/verus/ordered_rotation/laws.rs` | `rotated_suffix_refuses_superseded_grant` | `ErasureCommit.rotate`, `abstract_grant`, `rotated_suffix_refuses_superseded_grant` plus `Kernel.Ordered.authorize_writer` | Predicate link via `link_successor_generation` (separate writer authorization link. composition pending) |
| `verification/verus/ordered_rotation/laws.rs` | `rotation_head` | `ErasureCommit.rotation_head` | Equivalence |
| `verification/verus/ordered_rotation/laws.rs` | `rotation_installs_successor_generation` | `ErasureCommit.successor_generation` | Predicate link via `link_successor_generation` |
| `verification/verus/ordered_rotation/laws.rs` | `rotation_requires_exact_incumbent_and_head` | `ErasureCommit.rotation_head` | Predicate link via `link_rotation_head` |
| `verification/verus/ordered_rotation/laws.rs` | `rotation_requires_exact_preparation` | `ErasureCommit.exact_preparation` | Predicate link via `link_exact_preparation` |
| `verification/verus/ordered_rotation/laws.rs` | `successor_generation` | `ErasureCommit.successor_generation` | Equivalence |
| `verification/verus/ordered_serving_lease/laws.rs` | `absent_unleased_identity_is_disposable` | — | Local — concrete outcome witness |
| `verification/verus/ordered_serving_lease/laws.rs` | `admits` | `DisposalLease.Admits` | Equivalence |
| `verification/verus/ordered_serving_lease/laws.rs` | `decision_time` | `DisposalLease.decision_time` | Equivalence |
| `verification/verus/ordered_serving_lease/laws.rs` | `decision_time_is_monotone` | `DisposalLease.decision_time` | Predicate link via `link_decision_time` |
| `verification/verus/ordered_serving_lease/laws.rs` | `disposal_requires_withdrawal_and_drift` | `DisposalLease.withdrawn`, `may_dispose`, `MayDispose`, `Admits` | Predicate link via `link_may_dispose` (leased-time predicate. full disposal result composition pending) |
| `verification/verus/ordered_serving_lease/laws.rs` | `grant_change_preserves_holds` | `DisposalLease.grant_holds`, `Kernel.Ordered.ImageStep.fence` | Open — mutation of hold map and authority |
| `verification/verus/ordered_serving_lease/laws.rs` | `lease_end` | `DisposalLease.lease_end` | Equivalence |
| `verification/verus/ordered_serving_lease/laws.rs` | `lease_requires_current_enrolled_grant` | `DisposalLease.lease_end`, `Kernel.Ordered.authorize_writer` | Predicate link via `link_lease_end` |
| `verification/verus/ordered_serving_lease/laws.rs` | `may_dispose` | `DisposalLease.MayDispose` | Equivalence |
| `verification/verus/ordered_serving_lease/laws.rs` | `withdrawn` | `DisposalLease.withdrawn` | Equivalence |
| `verification/verus/ordered_serving_lease/laws.rs` | `withdrawn_owner_page_is_exact_and_bounded` | `DisposalLease.eligible_owner`, `qualifying_owners`, `owner_page` | Predicate link via `link_withdrawn_owners` (eligible set. page relation pending) |
| `verification/verus/ordered_serving_lease/laws.rs` | `withdrawn_owners` | `DisposalLease.qualifying_owners` | Equivalence |
| `verification/verus/ordered_trim/laws.rs` | `between` | — | Translated helper |
| `verification/verus/ordered_trim/laws.rs` | `trimPrefixSafe` | `Logkeeper.Protocol.trimPrefixSafe` | Equivalence |
| `verification/verus/ordered_trim/laws.rs` | `trim_credit_matches_removed_records` | `Protocol.trimCredit`, `trim_credit_matches_removed_records` | Predicate link via `link_trimCredit` (requires exact queue/debit projection) |
| `verification/verus/ordered_trim/laws.rs` | `trim_preserves_replay` | `Protocol.trimPrefixSafe`, `pinsSuffix` | Predicate link via `link_trimPrefixSafe` (single hold and interval predicate. multi-hold traversal pending) |
| `verification/verus/ordered_trim/laws.rs` | `trim_refuses_a_live_pin` | `Protocol.trimPrefixSafe`, `pinsSuffix` | Predicate link via `link_trimPrefixSafe` (single hold and interval predicate. multi-hold traversal pending) |
| `verification/verus/ordered_writer/laws.rs` | `a_displaced_enrollment_cannot_acquire_replay` | `Kernel.Ordered.is_current_enrollment` | Predicate link via `link_is_current_enrollment` |
| `verification/verus/ordered_writer/laws.rs` | `abstract_authority` | `Logkeeper.Kernel.Ordered.abstract_authority` | Equivalence |
| `verification/verus/ordered_writer/laws.rs` | `abstract_history` | `Logkeeper.Kernel.Ordered.abstract_history` | Equivalence |
| `verification/verus/ordered_writer/laws.rs` | `abstract_state` | `Logkeeper.Kernel.Ordered.abstract_state` | Equivalence |
| `verification/verus/ordered_writer/laws.rs` | `append_next_lsn` | `Logkeeper.Kernel.Ordered.append_next_lsn` | Equivalence |
| `verification/verus/ordered_writer/laws.rs` | `append_only_by_current_grant_at_next_lsn` | `Kernel.Ordered.authorize_writer`, `append_next_lsn`, `append_at_next_lsn` | Predicate link via `link_append_next_lsn` (also links authorization) |
| `verification/verus/ordered_writer/laws.rs` | `applied_append_extends_history` | `Kernel.Ordered.image_step_refines_kernel`, `trim_keeps_the_logical_history` | Predicate link via `link_abstract_state` (authority/history projection. step and trace refinement pending) |
| `verification/verus/ordered_writer/laws.rs` | `authorize_writer` | `Logkeeper.Kernel.Ordered.authorize_writer` | Equivalence |
| `verification/verus/ordered_writer/laws.rs` | `grant_installation_fences_older_epochs` | `Kernel.Step.fenceWriter`, `Kernel.Ordered.next_writer_epoch` | Predicate link via `link_next_writer_epoch` (epoch calculation) |
| `verification/verus/ordered_writer/laws.rs` | `is_current_enrollment` | `Logkeeper.Kernel.Ordered.is_current_enrollment` | Equivalence |
| `verification/verus/ordered_writer/laws.rs` | `next_writer_epoch` | `Logkeeper.Kernel.Ordered.next_writer_epoch` | Equivalence |
| `verification/verus/ordered_writer/laws.rs` | `trim_keeps_the_logical_history` | `Kernel.Ordered.image_step_refines_kernel`, `trim_keeps_the_logical_history` | Predicate link via `link_abstract_state` (authority/history projection. step and trace refinement pending) |
| `verification/verus/ordered_writer/laws.rs` | `vacancy_clears_the_grant` | `Kernel.Ordered.withdraw_grant`, `abstract_authority` | Predicate link via `link_withdraw_grant` |
| `verification/verus/ordered_writer/laws.rs` | `withdraw_grant` | `Logkeeper.Kernel.Ordered.withdraw_grant` | Equivalence |
| `verification/verus/ordered_writer/laws.rs` | `withdrawal_clears_only_the_matching_grant` | `Kernel.Ordered.withdraw_grant`, `abstract_authority` | Predicate link via `link_withdraw_grant` |
| `verification/verus/prefix_agreement/laws.rs` | `accept_at_or_above_promise` | `DurableAcceptor.PrepareAdmitted`, `AcceptAtPromise`, `prepare_or_retry_is_step`, `accept_at_promise_is_step` | Predicate link via `link_ballot_lt` (ballot order. transition contracts pending) |
| `verification/verus/prefix_agreement/laws.rs` | `chosen_votes_bind_ballot_voter_and_image` | `PrefixAgreement.Chosen`, `JournalRefinement.Majority`, `distinct_configured_votes_are_majority` | Open — certificate assembly, roster counting and exact prefix projection |
| `verification/verus/prefix_agreement/laws.rs` | `increasing_between` | — | Local — indexed-order proof helper |
| `verification/verus/prefix_agreement/laws.rs` | `installation_carries_exact_predecessor_image` | `JournalRefinement.ExactImage`, `Protocol.Transfer.exactImage` | Open — image returned from shipped option-valued contracts and authority projection |
| `verification/verus/prefix_agreement/laws.rs` | `majority_counts_each_voter_once` | `PrefixAgreement.Chosen`, `JournalRefinement.Majority`, `distinct_configured_votes_are_majority` | Open — certificate assembly, roster counting and exact prefix projection |
| `verification/verus/prefix_agreement/laws.rs` | `majority_counts_only_configured_voters` | `PrefixAgreement.Chosen`, `JournalRefinement.Majority`, `distinct_configured_votes_are_majority` | Open — certificate assembly, roster counting and exact prefix projection |
| `verification/verus/prefix_agreement/laws.rs` | `majority_is_strict` | `PrefixAgreement.Chosen`, `JournalRefinement.Majority`, `distinct_configured_votes_are_majority` | Open — certificate assembly, roster counting and exact prefix projection |
| `verification/verus/prefix_agreement/laws.rs` | `promise_only_advances_above_floor` | `DurableAcceptor.PrepareAdmitted`, `AcceptAtPromise`, `prepare_or_retry_is_step`, `accept_at_promise_is_step` | Predicate link via `link_ballot_lt` (ballot order. transition contracts pending) |
| `verification/verus/prefix_agreement/laws.rs` | `sealing_carries_exact_predecessor_image` | `JournalRefinement.ExactImage`, `Protocol.Transfer.exactImage` | Open — image returned from shipped option-valued contracts and authority projection |
| `verification/verus/prefix_agreement/laws.rs` | `winner_dominates_observed` | `PrefixAgreement.WinnerDominates`, `RankLE` | Predicate link via `link_ballot_lt` (primary rank. winner fold pending) |
| `verification/verus/receipt_signatures/laws.rs` | `accepted_barrier_binds_claim` | `Premises.SignatureScope.canonicalStart`, `exactBarrierInvocation`, `canonical_fields_bind_claim`, `accepted_barrier_binds_claim` | Open — nested claim and request structures, domain/preimage encoding and signature contract |
| `verification/verus/receipt_signatures/laws.rs` | `accepted_barrier_receipt_is_exact` | `Premises.SignatureScope.exactBarrierReceipt`, `exactReceiptScope`, `accepted_barrier_receipt_is_exact` | Open — nested Rust record and result patterns, receipt and signed claim projections |
| `verification/verus/receipt_signatures/laws.rs` | `authenticated_barrier_receipt_binds_signed_cut` | `Premises.SignatureScope.exactBarrierReceipt`, `exactReceiptScope`, `accepted_barrier_receipt_is_exact` | Open — nested Rust record and result patterns, receipt and signed claim projections |
| `verification/verus/receipt_signatures/laws.rs` | `canonical_fields_bind_claim` | `Premises.SignatureScope.canonicalStart`, `exactBarrierInvocation`, `canonical_fields_bind_claim`, `accepted_barrier_binds_claim` | Open — nested claim and request structures, domain/preimage encoding and signature contract |
| `verification/verus/receipt_signatures/laws.rs` | `decoded_claim_has_canonical_start` | `Premises.SignatureScope.canonicalStart`, `exactBarrierInvocation`, `canonical_fields_bind_claim`, `accepted_barrier_binds_claim` | Open — nested claim and request structures, domain/preimage encoding and signature contract |
| `verification/verus/receipt_signatures/laws.rs` | `equal_checkpoint` | — | Local — byte encoding/injectivity helpers |
| `verification/verus/receipt_signatures/laws.rs` | `equal_cut` | — | Local — byte encoding/injectivity helpers |
| `verification/verus/receipt_signatures/laws.rs` | `equal_parts` | — | Local — byte encoding/injectivity helpers |
| `verification/verus/receipt_signatures/laws.rs` | `equal_placement` | — | Local — byte encoding/injectivity helpers |
| `verification/verus/receipt_signatures/laws.rs` | `equal_u64` | — | Local — byte encoding/injectivity helpers |
| `verification/verus/receipt_signatures/laws.rs` | `equal_uuid` | — | Local — byte encoding/injectivity helpers |
| `verification/verus/receipt_signatures/laws.rs` | `first_ascii_byte` | — | Local — byte encoding/injectivity helpers |
| `verification/verus/receipt_signatures/laws.rs` | `repair_authority_is_active` | `Premises.BarrierKeys.valid_successor_extends_rotations`, `repair_authority_is_active`, `retained_across_rotations` | Predicate link via `link_validSuccessorKeys` (key set/authorization relations. signature authentication pending) |
| `verification/verus/receipt_signatures/laws.rs` | `rotation_domain_is_distinct` | `Premises.SignatureScope.verify`, `rotation_domain_is_distinct` | Open — external signature contract, UTF-8, exact receipt/evidence preimages |
| `verification/verus/receipt_signatures/laws.rs` | `rotation_signs_in_its_own_domain` | `Premises.SignatureScope.verify`, `rotation_domain_is_distinct` | Open — external signature contract, UTF-8, exact receipt/evidence preimages |
| `verification/verus/receipt_signatures/laws.rs` | `rotation_verification_uses_its_own_domain` | `Premises.SignatureScope.verify`, `rotation_domain_is_distinct` | Open — external signature contract, UTF-8, exact receipt/evidence preimages |
| `verification/verus/receipt_signatures/laws.rs` | `valid_successor_extends_rotations` | `Premises.BarrierKeys.valid_successor_extends_rotations`, `repair_authority_is_active`, `retained_across_rotations` | Predicate link via `link_validSuccessorKeys` (key set/authorization relations. signature authentication pending) |
| `verification/verus/receipt_signatures/reference.rs` | `authenticates` | `Logkeeper.Premises.SignatureScope.verify` | Open — nested claim structures, result patterns or external signature contract |
| `verification/verus/receipt_signatures/reference.rs` | `barrier_bytes` | — | Local — byte encoding helpers used under `SignatureScope` |
| `verification/verus/receipt_signatures/reference.rs` | `be64_width` | — | Local — byte encoding helpers used under `SignatureScope` |
| `verification/verus/receipt_signatures/reference.rs` | `canonicalStart` | `Logkeeper.Premises.SignatureScope.canonicalStart` | Open — nested claim structures, result patterns or external signature contract |
| `verification/verus/receipt_signatures/reference.rs` | `checkpoint_bytes` | — | Local — byte encoding helpers used under `SignatureScope` |
| `verification/verus/receipt_signatures/reference.rs` | `cut_bytes` | — | Local — byte encoding helpers used under `SignatureScope` |
| `verification/verus/receipt_signatures/reference.rs` | `domain_bytes` | — | Local — byte encoding helpers used under `SignatureScope` |
| `verification/verus/receipt_signatures/reference.rs` | `enrollment_bytes` | — | Local — byte encoding helpers used under `SignatureScope` |
| `verification/verus/receipt_signatures/reference.rs` | `exactBarrierInvocation` | `Logkeeper.Premises.SignatureScope.exactBarrierInvocation` | Open — nested claim structures, result patterns or external signature contract |
| `verification/verus/receipt_signatures/reference.rs` | `exactBarrierReceipt` | `Logkeeper.Premises.SignatureScope.exactBarrierReceipt` | Open — nested claim structures, result patterns or external signature contract |
| `verification/verus/receipt_signatures/reference.rs` | `exactReceiptScope` | `Logkeeper.Premises.SignatureScope.exactReceiptScope` | Open — nested claim structures, result patterns or external signature contract |
| `verification/verus/receipt_signatures/reference.rs` | `placement_bytes` | — | Local — byte encoding helpers used under `SignatureScope` |
| `verification/verus/receipt_signatures/reference.rs` | `repairAuthority` | `Logkeeper.Premises.BarrierKeys.repairAuthority` | Equivalence |
| `verification/verus/receipt_signatures/reference.rs` | `request_id_bytes` | — | Local — byte encoding helpers used under `SignatureScope` |
| `verification/verus/receipt_signatures/reference.rs` | `rotation_bytes` | — | Local — byte encoding helpers used under `SignatureScope` |
| `verification/verus/receipt_signatures/reference.rs` | `uuid_bytes` | — | Local — byte encoding helpers used under `SignatureScope` |
| `verification/verus/receipt_signatures/reference.rs` | `validSuccessorKeys` | `Logkeeper.Premises.BarrierKeys.validSuccessorKeys` | Equivalence |
| `verification/verus/receipt_signatures/reference.rs` | `verificationKeys` | `Logkeeper.Premises.BarrierKeys.verificationKeys` | Equivalence |
| `verification/verus/rotation_slot_evidence/laws.rs` | `at_fence` | `Logkeeper.SelectionFence.AtFence` | Equivalence |
| `verification/verus/rotation_slot_evidence/laws.rs` | `distinct_voters` | `List.Nodup` | Equivalence |
| `verification/verus/rotation_slot_evidence/laws.rs` | `exact_rows` | `SelectionFence.RotationEvidence`, `StrictMajority`, `rotation_evidence_names_a_majority_with_both_exact_reads` | Open — voter evidence and roster/selected prefix composition |
| `verification/verus/rotation_slot_evidence/laws.rs` | `mirrors_fence` | `SelectionFence.MirrorsFence` | Open — slot-pair and authenticated physical read projections |
| `verification/verus/rotation_slot_evidence/laws.rs` | `only_new_configured_peers_can_enter_the_round` | — | Local — wire ordering and peer registration helper laws |
| `verification/verus/rotation_slot_evidence/laws.rs` | `ordered_rows_are_distinct` | `SelectionFence.RotationEvidence` (voter uniqueness) | Predicate link via `link_distinct_voters` (distinctness predicate. sortedness implication stays in Verus/Lean) |
| `verification/verus/rotation_slot_evidence/laws.rs` | `published_evidence_preserves_the_exact_rotation_and_roster` | `SelectionFence.RotationEvidence`, `StrictMajority`, `rotation_evidence_names_a_majority_with_both_exact_reads` | Predicate link via `link_distinct_voters` (voter uniqueness and attested `AtFence`. physical reads and roster/selected prefix composition pending) |
| `verification/verus/rotation_slot_evidence/laws.rs` | `recording_a_rotation_vote_preserves_exact_configured_rows` | `SelectionFence.RotationEvidence`, `StrictMajority`, `rotation_evidence_names_a_majority_with_both_exact_reads` | Open — voter evidence and roster/selected prefix composition |
| `verification/verus/rotation_slot_evidence/laws.rs` | `rotation_evidence_names_a_majority_with_both_exact_reads` | `SelectionFence.RotationEvidence`, `StrictMajority`, `rotation_evidence_names_a_majority_with_both_exact_reads` | Predicate link via `link_distinct_voters` (voter uniqueness and attested `AtFence`. physical reads and roster/selected prefix composition pending) |
| `verification/verus/rotation_slot_evidence/laws.rs` | `the_wire_preserves_the_fence_and_both_images_in_physical_order` | — | Local — wire ordering and peer registration helper laws |
| `verification/verus/voter_slot_header/laws.rs` | `voter_slot_header_rejects_inexact_extent` | `VoterSlotHeader.slotHeaderLengthValid`, `voter_slot_header_rejects_inexact_extent` | Open — fixed-width bit shifts, OR and truncation in `decodeBE` |
| `verification/verus/voter_slot_header/laws.rs` | `voter_slot_header_round_trips` | `VoterSlotHeader.voter_slot_header_round_trips`, `voter_slot_scope_is_exact` | Predicate link via `link_voterSlotMagic` (magic bytes. headers and word encoding pending) |
| `verification/verus/voter_slot_header/laws.rs` | `voter_slot_scope_is_exact` | `VoterSlotHeader.voter_slot_header_round_trips`, `voter_slot_scope_is_exact` | Predicate link via `link_voterSlotMagic` (magic bytes. headers and word encoding pending) |
| `verification/verus/voter_transport/laws.rs` | `a_reply_cannot_change_witness_mode` | `VoterTransport.voteReadBackMatches` | Open — predicate is inline in a shipped function contract |
| `verification/verus/voter_transport/laws.rs` | `scope_requires_both_groups` | `VoterTransport.transportGroupMatches`, `scope_requires_both_groups` | Predicate link via `link_transportGroupMatches` |
| `verification/verus/voter_transport/laws.rs` | `transport_ballot_round_trips` | `VoterTransport.ballotBytes`, `ballotValid`, `voteSlotsMatch` | Open — fixed-width word encoding and nested physical slot structures |
| `verification/verus/voter_transport/laws.rs` | `vote_reads_the_two_physical_slots_in_order` | `VoterTransport.ballotBytes`, `ballotValid`, `voteSlotsMatch` | Open — fixed-width word encoding and nested physical slot structures |
