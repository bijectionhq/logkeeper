# Action inventory

Bijection locations are relative to `crates/native_store_runtime/src/rtdb/` unless marked otherwise. RTDB locations are relative to `rust/crates/`. Both sides refer to the pinned `origin/main` revisions in the [study](README.md). A location can be opened with `git show <revision>:<path>` and the indicated line. Flight rows cite the actual sending wrapper or action selection and the RTDB dispatch branch. The wrappers are used by the fact-point and restore workflows cited below. The PGWire table collapses repeated SQL templates under their statement form. Lifecycle and recovery count public request operations once, even if multiple local workflows use them.

`T` transact, `R` read, `S` subscribe, `H` hold, `F` forget. In a composition, the listed verbs participate in the same logical request unless the description calls out a sequence. A held read uses an existing hold where available. `E` expressed with the contract in the [study](README.md), with full refinement unproved. `E/L` also has a corresponding Lean abstraction. `A` accidental, with its layering choice named. `X` essential, with the required privileged verb named. A dash means the five verbs have no equivalent authority transition.

## Owned Flight

Action names below carry the `rtdb.owned.` prefix on the wire. RTDB dispatch is `flight-sql/src/actions.rs`, with the handlers in `flight-sql/src/owned_actions.rs` and siblings. At RTDB's `multi/src/flight_gateway.rs:419–545`, the gateway authenticates and routes the Flight session, then proxies the RPC. It does not decide the action.

| Action | Semantics | Bijection send site | RTDB dispatch / handler | Verbs | Verdict |
| --- | --- | --- | --- | --- | --- |
| `DecideHeldWorlds.v2` | Atomically choose one to eight held world publications with optional Root facts and checks. | `owned_flight.rs:3679`, `fact_points/landing_decision.rs:1354–1359` world_batch_action | 274–277 `decide_held_worlds_action` | T | E |
| `SwitchPreparedProposal.v2` | Decide a staged Proposal switch with its Root witness, clock target, derived effects and terminal receipt. | `owned_flight.rs:3679`, `fact_points/landing_decision.rs:1354–1359` world_batch_action | 274–277 `decide_held_worlds_action` | T | E |
| `ReadHeldExpiryCandidates.v1` | Page exact creation groups and issue signed expiry candidates, without granting removal. | `owned_flight/expiry.rs:35` sweep_expired_page | 211 `held_expiry_candidates_action` | R H | A: expiry nominations |
| `ApplyHeldExpiry.v1` | Compare the original creation, authorized replay horizon and deadline, then retire the lifetime, advance its sweep floor and emit one expiry touch. | `owned_flight/expiry.rs:129` apply_expiry | 212 `apply_held_expiry_action` | T F | A: expiry nominations |
| `SealHostedRanges.v1` | Seal exact held range observations as portable, authenticated transaction predicates. | `owned_flight.rs:4234` durable_hosted_ranges | 137 `seal_hosted_ranges_action` | R H | A: held witnesses |
| `ValidateFreshHosted.v1` | Check source positions, durable range predicates, fact groups and control rows at the ordered head without applying business writes. | `owned_flight.rs:4290` validate_fresh_hosted | 138 `validate_fresh_hosted_action` | T | A: split validation |
| `DecideHosted.v4` | Decide checked Root facts and hosted controls with final predicates, optional world evidence, disposition and original clock. | `owned_flight.rs:4388` commit_hosted_with_world_reads | 139 `decide_hosted_action` | T | E/L |
| `Commit.v2` | Commit one checked-deadline Arrow batch of groups across owned relations, returning the transaction key. | `owned_flight.rs:4188` commit_layout_readiness, `owned_flight.rs:4198` commit | 160–162 `commit_owned_action` | T | E/L |
| `OfferFundedMutationClock.v1` | Order a funded booking bound to the held Root and return its original offered clock and receipt. | `owned_flight.rs:2238` offer_funded_mutation | 158 `offer_funded_mutation_clock_action` | R H T | A: funded clock booking |
| `OfferClockSlot.v2` | Offer the bounded one-second grid target from an admitted receiver-clock observation. | `owned_flight.rs:2216` offered_clock | 159 `offer_clock_slot_action` | R H | A: clock slot |
| `OpenWorldRead.v6` | Open a scoped live world, selecting its frozen parents, overlay, mode and clock. | `owned_flight.rs:4106` open_world_read | 257 `open_world_read_action` | H R | A: held worlds |
| `ReadHeldWorldHead.v1` | Read the held world's exact local head and logical clock basis. | `owned_flight.rs:1588` held_head_revision | 258 `read_held_world_head_action` | R | E |
| `PrepareHeldWorldOverlay.v5` | Prepare the historical Held overlay archive at an admitted exact publication for a retained child. | `owned_flight.rs:1651` prepare_retained_overlay | 235 `prepare_held_world_overlay_action` | H R | A: staged held worlds |
| `PublishHeldWorldRetention.v5` | Publish the retained child fork with both its Root base and selected Held overlay pinned. | `owned_flight.rs:1689` child_fork_publication | 269 `publish_held_world_retention_action` | H T | E |
| `PublishWorldCut.v2` | Register an initial archived world cut or advance it by comparing the predecessor pin and protecting the replacement. | `owned_flight.rs:2420` prepare_world_cut | 270–273 `publish_world_cut_action` | H T | E |
| `DecideWorldCut.v2` | Decide an initial retained fork and associated Root publication at one ordered source position. | `owned_flight.rs:2416` prepare_world_cut | 270–273 `publish_world_cut_action` | H T | E |
| `ReadHeldWorldPoint.v2` | Project a held world point and optional compare witness, resolving parent, overlay or requested source. | `owned_flight.rs:1891` read_point | 264 `held_world_point_action` | H R | E/L |
| `PreflightHeldWorldAt.v2` | Admit the exact local publication key and return its history time, mode and logical clock. | `owned_flight.rs:1746` select_accepted_cut | 262 `held_world_at_preflight_action` | R H | A: held-world preflight |
| `SelectHeldWorldAsOf.v2` | Resolve a requested history time to the selected admissible local world publication and its clock. | `owned_flight.rs:1748` select_accepted_cut | 261 `held_world_at_preflight_action` | R H | E |
| `SelectHeldWorldParentAsOf.v1` | Resolve a history time against the frozen parent under the world hold. | `owned_flight.rs:1725` archived_parent_as_of | 259 `held_world_at_preflight_action` | R H | E |
| `ReadHeldWorldPointAt.v1` | Read an effective world point at the selected local historical publication. | `owned_flight.rs:1790` accepted_point | 263 `held_world_point_at_action` | H R | E/L |
| `ReadHeldWorldParentPointAt.v1` | Read a point in the pinned parent's admitted historical publication. | `owned_flight.rs:1808` archived_parent_point | 260 `held_world_point_at_action` | H R | E/L |
| `ReadHeldWorldValidDuring.v2` | Return valid-time slices of a held identity from the requested current world source. | `owned_flight.rs:1910` valid_schedule, `owned_flight.rs:1912` valid_schedule | 223 `held_world_valid_during_action` | H R | E |
| `ReadHeldWorldValidDuringAt.v1` | Return effective-world valid-time slices at an earlier local publication. | `owned_flight.rs:1914` valid_schedule | 222 `held_world_valid_during_action` | H R | E |
| `ReadHeldWorldParentValidDuringAt.v1` | Return archive-parent valid-time slices at the selected earlier parent publication. | `owned_flight.rs:1918` valid_schedule | 220 `held_world_valid_during_action` | H R | E |
| `ReadHeldWorldIdentityPage.v1` | Page typed identities of the current effective world in key order. | `owned_flight.rs:1969` identity_page | 225 `held_world_identities_action` | H R | E |
| `ReadHeldWorldIdentityPageAt.v1` | Page effective typed identities at an earlier local world publication. | `owned_flight.rs:1992` identities_earlier | 224 `held_world_identities_action` | H R | E |
| `ReadHeldWorldParentIdentityPageAt.v1` | Page typed identities of the pinned parent at the requested earlier publication. | `owned_flight.rs:2001` archived_parent_identities | 221 `held_world_identities_action` | H R | E |
| `ReadHeldWorldOverlayIdentityPage.v1` | Page identities addressed by the local overlay, including tombstone keys. | `owned_flight.rs:1981` overlay_identities | 227 `held_world_identities_action` | H R | E |
| `ReadHeldWorldOverlayIdentitiesAt.v1` | Page overlay identities at the selected earlier local publication. | `owned_flight.rs:1978` overlay_identities | 226 `held_world_identities_action` | H R | E |
| `ReadHeldWorldRange.v1` | Page ordered rows from the held parent range and optionally capture absence/range evidence. | `owned_flight.rs:2092` ordered_read | 190 `held_world_ordered_action` | H R | E |
| `ReadHeldWorldParentRangeAt.v1` | Page ordered rows in the archived parent at the selected earlier publication. | `owned_flight.rs:2111` archived_parent_range | 188 `held_world_ordered_action` | H R | E |
| `ReadHeldWorldAncestorChanges.v2` | Page retained Held ancestor groups above the pinned Root basis at the exact inherited Held position. | `owned_flight.rs:1540` archived_ancestor_changes | 237 `archived_world_changes_action` | H R | E |
| `ReadHeldWorldParentChangesAt.v2` | Page bounded ordered ancestor changes in the pinned archive parent at a selected cut. | `owned_flight.rs:1529` archived_parent_changes | 236 `archived_world_changes_action` | H R | E |
| `ReadHeldWorldParentTouchKeysAt.v1` | Page original parent path touch keys between the requested cuts, including removals. | `owned_flight.rs:1457` archived_parent_touch_keys | 234 `held_world_parent_touch_images_action` | H R | E |
| `ReadHeldWorldParentTouchImagesAt.v1` | Page original parent path touches with their selected images. | `owned_flight.rs:1467` archived_parent_touch_images | 233 `held_world_parent_touch_images_action` | H R | E |
| `ReadHeldWorldOverlayRange.v1` | Page ordered local overlay entries, including overriding tombstones. | `owned_flight.rs:2093` ordered_read | 194 `held_world_ordered_action` | H R | E |
| `ReadHeldWorldOverlayRangeAt.v1` | Page ordered local overlay entries at a selected previously accepted publication. | `owned_flight.rs:2028` accepted_overlay_range | 193 `held_world_ordered_action` | H R | E |
| `CountHeldWorldRange.v1` | Count the held parent ordered range with optional compare evidence. | `owned_flight.rs:2103` ordered_count | 191 `held_world_ordered_action` | H R | E |
| `CountHeldWorldParentRangeAt.v1` | Count an ordered range at the selected earlier parent publication. | `owned_flight.rs:2120` archived_parent_count | 189 `held_world_ordered_action` | H R | E |
| `MeasureHeldWorldRange.v1` | Measure held parent range cardinality and key bounds. | `owned_flight.rs:2138` ordered_measure | 192 `held_world_ordered_action` | H R | E |
| `CloseWorldRead.v1` | Release the original owner-local world read handle. | `owned_flight.rs:2174` close | 265–267 `close_world_read_action` | H | A: held worlds |
| `OpenRead.v3` | Admit one applied live owned read and return its handle and cut/present. | `owned_flight.rs:3818` open_read | 172 `open_owned_read_action` | H R | E/L |
| `OpenFreshRead.v2` | Admit a fresh cut under the exact deployment and source floors. | `owned_flight.rs:3888` open_scoped_fresh_read | 173 `open_fresh_owned_read_action` | H R | E/L |
| `PrepareAppliedRead.v3` | Prepare audience recovery transport with a bounded seat-bound admission and source floors. | `owned_flight.rs:3749` prepare_audience_transport | 182 `prepare_applied_read_action` | H R | A: split admission and seats |
| `OpenAppliedRead.v5` | Open the already-applied hosted cut with its prepared or scoped fresh evidence and answer custody. | `owned_flight.rs:3920` open_applied_read | 183 `open_applied_owned_read_action` | H R | A: split admission and seats |
| `OpenReadAsOf.v2` | Admit the historical Root publication at or before the requested system time under a live hold. | `owned_flight.rs:2495` open_historical_read | 170 `open_owned_read_as_of_action` | H R | E |
| `OpenReadAtPublication.v1` | Admit the exact authenticated Root publication position and history time under an original hold. | `owned_flight.rs:2495` open_historical_read | 171 `open_owned_read_as_of_action` | H R | E |
| `LookupHeldPublication.v1` | Resolve the preceding or following publication for a table within a held history. | `owned_flight.rs:2548` lookup_publication | 208 `held_lookup_publication_action` | H R | E |
| `OpenOwnedScopedRead.v2` | Admit one fresh cut and restrict the owned handle to the named relations. | `owned_flight.rs:2267` scope_relations | 169 `open_owned_scoped_read_action` | H R | E/L |
| `ReadHeldPoint.v2` | Read one typed identity at explicit business time or the held present. | `owned_flight.rs:2567` read_point | 218 `held_owned_point_action` | H R | E/L |
| `ReadHeldFixedPoint.v1` | Read one typed identity at a required explicit valid instant. | `owned_flight.rs:2571` read_fixed_point | 219 `held_owned_point_action` | H R | E/L |
| `ReadHeldStorageUsage.v1` | Project storage usage of a relation at the owned view with its accounted storage inputs. | `owned_flight.rs:2594` storage_usage | 206 `held_owned_storage_usage_action` | H R | E |
| `ReadHeldPathTouch.v2` | Page touched typed keys for an ordered Root path over a bounded history interval. | `owned_flight.rs:2718` path_touch_keys | 243 `held_owned_path_touch_action` | H R | E |
| `ReadHeldWorldVersion.v2` | Resolve an exact world event address to its version image over the archived base and overlay. | `owned_flight.rs:1382` version_image | 240 `held_world_version_action` | H R | E/L |
| `ReadHeldWorldTouchImages.v1` | Page world path touches with original positions and images resolved against the parent. | `owned_flight.rs:1447` touch_images | 241 `held_world_path_touch_action` | H R | E |
| `ReadHeldWorldPathTouch.v1` | Page the held world path's touched keys and their ordered sources. | `owned_flight.rs:1352` path_touch_keys | 242 `held_world_path_touch_action` | H R | E |
| `ReadHeldHistoricalPoint.v1` | Read a point at a bounded earlier system time within the original held Root. | `owned_flight.rs:2643` read_historical_point | 244 `held_owned_historical_point_action` | H R | E/L |
| `ReadHeldPositionPoint.v1` | Read a point at an exact assertion position relative to a masked commit. | `owned_flight.rs:2667` read_position_point | 245 `held_owned_position_point_action` | H R | E |
| `ReadHeldRootCutPoint.v1` | Read a clear Root point immediately before or inclusive of the exact publication position. | `owned_flight.rs:2691` read_root_cut_point | 246 `held_root_cut_point_action` | H R | E |
| `ReadHeldRange.v2` | Page a held typed ordered range and optionally issue a compare witness. | `owned_flight.rs:2751` read_range | 196 `held_owned_range_action` | H R | E/L |
| `ReadHeldRange.v3` | Page the held ordered range using an explicit fixed valid time. | `owned_flight.rs:2750` read_range | 197 `held_owned_range_action` | H R | E/L |
| `ReadHeldRange.v4` | Page the ordered range at an earlier system time and explicit valid instant. | `owned_flight.rs:2749` read_range | 198 `held_owned_range_action` | H R | E |
| `ReadHeldUniqueWindow.v1` | Page owners of unique entries overlapping the typed interval and return its evidence. | `owned_flight.rs:3224` unique_window | 216 `held_owned_unique_window_action` | H R | E |
| `ReadHeldValidDuring.v2` | Return visible valid interval slices of a typed identity at the held system basis. | `owned_flight.rs:3269` valid_during_at | 247 `held_owned_valid_during_action` | H R | E |
| `ReadHeldValidRegion.v1` | Return the visible constant-value or absence region around the requested valid time. | `owned_flight.rs:3267` valid_during_at | 248 `held_owned_valid_during_action` | H R | E |
| `ReadHeldPositionValidDuring.v1` | Return valid-time slices at an exact masked assertion position in held history. | `owned_flight.rs:3265` valid_during_at | 249 `held_owned_valid_during_action` | H R | E |
| `ReadHeldProtectedCarrierCoverage.v1` | Return covered protected carrier edges for an exact identity and replay coordinate. | `owned_flight.rs:3354` protected_carrier_coverage | 228 `held_protected_coverage_action` | H R | E |
| `ReadHeldRowCarrierExists.v1` | Check whether an exact protected row has a carrier at the held cut. | `owned_flight.rs:3338` protected_row_carrier_exists | 229 `held_row_carrier_exists_action` | H R | E |
| `ReadHeldProtectedCarrierPage.v1` | Page eligible protected carrier IDs with coverage and continuation. | `owned_flight.rs:3383` protected_carrier_page | 230 `held_protected_carriers_action` | H R | E |
| `ReadHeldIdentityPage.v1` | Page held Root identities at the selected valid instant in typed order. | `owned_flight.rs:3305` identity_page | 231 `held_owned_identities_action` | H R | E/L |
| `ReadHeldIdentityPageAllValid.v1` | Page identities with any current assertion across all valid time at a selected system cut. | `owned_flight.rs:3330` identity_page_all_valid | 232 `held_owned_identities_all_valid_action` | H R | E |
| `ReadHeldVersions.v2` | Page placed assertion versions with their original positions along the selected history axis. | `owned_flight.rs:3394` versions | 239 `held_owned_versions_action` | H R | E |
| `ReadHeldWorldParentVersionsAt.v1` | Page typed assertion versions at the selected archived parent cut. | `owned_flight.rs:2129` archived_parent_versions | 238 `held_world_parent_versions_action` | H R | E |
| `CountHeldRange.v1` | Count a held Root range and optionally issue its comparison evidence and expiry. | `owned_flight.rs:3146` count_range_observed | 199 `held_owned_count_action` | H R | E/L |
| `MeasureHeldRange.v1` | Return current held range cardinality and selected extrema. | `owned_flight.rs:3176` measure_range_observed | 201 `held_owned_count_action` | H R | E |
| `MeasureHeldRangeAt.v1` | Return range cardinality and extrema at the earlier selected system basis. | `owned_flight.rs:3176` measure_range_observed | 202 `held_owned_count_action` | H R | E |
| `CountHeldRange.v2` | Count the range at the selected earlier system time with optional evidence. | `owned_flight.rs:3144` count_range_observed | 200 `held_owned_count_action` | H R | E/L |
| `ReadHeldWorldChangesDescending.v2` | Page the held world overlay's merged changes in descending exact publication order. | `owned_flight.rs:1512` merged_changes_descending, `owned_flight.rs:3720` merged_changes | 203 `held_world_changes_action` | H R | E |
| `ReadHeldWorldChanges.v4` | Page merged local world changes after the requested edge through the held cap. | `owned_flight.rs:1520` merged_changes | 204 `held_world_changes_action` | H R S | E/L |
| `ReadHeldMergedChanges.v4` | Merge admitted relation changes by exact publication edges, with coverage and a next page. | `owned_flight.rs:3419` merged_changes | 210 `held_owned_merged_changes_action` | H R S | E/L |
| `ReadHeldMergedChangesDescending.v2` | Page merged admitted relation changes in descending publication order. | `owned_flight.rs:3431` merged_changes_descending, `owned_flight.rs:3720` merged_changes | 207 `held_owned_merged_changes_action` | H R | E |
| `ReadHeldTablePublicationSequence.v1` | Read the authenticated table-local journal sequence over the held range. | `owned_flight.rs:3406` table_publication_sequence | 209 `held_table_publication_sequence_action` | H R | E |
| `ObserveHeldHosted.v1` | Observe original held range and hosted checks through their deadline and report whether dependencies still match. | `owned_flight.rs:2808` observe_hosted_dependencies | 152 `observe_held_hosted_action` | H R S | A: dependency polling |
| `ConfirmAppliedHosted.v6` | Confirm that the admitted answer and scoped checks still bind the installed source at its original position. | `owned_flight.rs:2851` confirm_applied_hosted_read | 153 `confirm_applied_hosted_action` | H R | A: split admission and seats |
| `ReadHeldHostedControl.v3` | Project allowlisted hosted control state at the live held position. | `owned_flight.rs:2896` hosted_control | 155 `read_held_hosted_control_action` | H R | E |
| `ReadHeldHostedControlAtPublication.v1` | Project allowlisted hosted control at the exact prior public Root publication. | `owned_flight.rs:2894` hosted_control | 156 `read_held_hosted_control_action` | H R | E |
| `ReadHeldRootCatalog.v1` | Project the requested native Root catalog domain under the admitted held cut. | `owned_flight.rs:2199` read_root_catalog | 157 `read_held_root_catalog_action` | H R | E |
| `ConfirmHostedSource.v1` | Authenticate scoped source prefix against exact transaction and receiver floors before routing an owner. | `owned_flight.rs:3984` confirm_source_prefix | 154 `confirm_hosted_source_action` | H R | A: separate source confirmation |
| `ReadHeldUnique.v1` | Look up the unique owner of a typed value at the selected valid instant. | `owned_flight.rs:3093` lookup_unique | 215 `held_owned_unique_action` | H R | E |
| `DeclareSpatialPath.v1` | Declare a tagged spatial path and coordinates in the owned catalog. | `owned_flight.rs:4447` declare_spatial_path | 147 `declare_owned_path_action` | T | E |
| `SpatialOpen.v1` | Open a held spatial predicate and return its first projected page plus filter capability. | `owned_flight.rs:2957` spatial | 125, 133–134 `spatial_held_owned_action` | H R | A: stateful spatial cursor |
| `SpatialNext.v1` | Continue that filter from the exclusive typed identity and optionally return a witness. | `owned_flight.rs:2949` spatial | 174–176 `next_spatial_owned_action` | H R | A: stateful spatial cursor |
| `SpatialClose.v1` | Release the filter capability on its original held owner. | `owned_flight.rs:966` release | 178–180 `close_spatial_owned_action` | H | A: stateful spatial cursor |
| `DeclareSpatialPath.v2` | Declare spatial path using its encoded layout and coordinate policy. | `owned_flight.rs:4445` declare_spatial_path | 148 `declare_owned_path_action` | T | E |
| `SpatialPathReadiness.v1` | Read spatial path coverage and artifact readiness for the admitted catalog. | `owned_flight.rs:2918` spatial_path_ready | 149 `spatial_path_readiness_action` | H R | E |
| `SpatialHeld.v2` | Read held spatial matches with their documents. | `owned_flight.rs:2959` spatial | 129, 133–134 `spatial_held_owned_action` | H R | E |
| `SpatialHeld.v3` | Read held spatial matches projecting only the requested document columns. | `owned_flight.rs:2958` spatial | 130, 133–134 `spatial_held_owned_action` | H R | E |
| `SpatialRankOpen.v1` | Start the held exact nearest ranking with a distance/identity cursor capability. | `owned_flight.rs:2961` spatial | 126, 133–134 `spatial_held_owned_action` | H R | A: stateful spatial cursor |
| `SpatialRankOpen.v2` | Open the exact ranked window beyond an exclusive radius with projected documents. | `owned_flight.rs:2960` spatial | 127, 133–134 `spatial_held_owned_action` | H R | A: stateful spatial cursor |
| `SpatialRankNext.v1` | Continue nearest ranking after its exact distance and complete typed identity. | `owned_flight.rs:2952` spatial | 174–176 `next_spatial_owned_action` | H R | A: stateful spatial cursor |
| `SearchHeld.v5` | Rank a scoped held text corpus, optionally including staged overlay, with exact total and evidence. | `owned_flight.rs:3125` search | 184 `search_held_owned_action` | H R | E |
| `SearchHeldWorld.v2` | Rank the current effective world's merged corpus with overlay shadowing and complete corpus evidence. | `owned_flight.rs:2044` search | 187 `search_held_world_action` | H R | E |
| `SearchHeldWorldAt.v1` | Rank the effective world's corpus at an earlier selected local publication. | `owned_flight.rs:2059` search_earlier | 186 `search_held_world_action` | H R | E |
| `SearchHeldWorldParentAt.v1` | Rank the pinned parent's archived corpus at an earlier selected parent publication. | `owned_flight.rs:2073` archived_parent_search | 185 `search_held_world_action` | H R | E |
| `DeclarePath.v1` | Declare a typed ordered path and its key encoding transactionally in the relation catalog. | `owned_flight.rs:4422` declare_path | 150 `declare_owned_path_action` | T | E |
| `DeclareCapacity.v2` | Declare a prefix-partition capacity constraint used by ordered writes. | `owned_flight.rs:4397` declare_capacity | 141 `declare_owned_capacity_action` | T | E |
| `DeclareFixedRange.v1` | Declare a range path's supported fixed-valid schema and bound. | `owned_flight.rs:4406` declare_fixed_range | 140 `declare_owned_fixed_range_action` | T | E |
| `DeclareUniquePath.v1` | Declare ownership uniqueness for a typed column path. | `owned_flight.rs:4466` declare_unique_path | 142 `declare_owned_single_column_path_action` | T | E |
| `DeclareRelation.v1` | Declare the private relation's schema, columns and valid-time/lifetime shape. | `owned_flight.rs:4439` declare_owned_schema | 144 `declare_owned_relation_action` | T | E |
| `DeclareSearchPath.v1` | Declare the text-search column and path for owned indexing. | `owned_flight.rs:4457` declare_search_path | 143 `declare_owned_single_column_path_action` | T | E |
| `CloseRead.v1` | Release the original owner-local Root read handle. | `owned_flight.rs:2786` close, `owned_flight.rs:2790` close | 250–252 `close_owned_read_action` | H | A: held reads |
| `PrepareReplayParent.v1` | Prepare the exact archived parent source for replay under the held restore writer. | `owned_flight.rs:4036` prepare_replay_parent | 254 `prepare_replay_parent_action` | H R | A: held restore staging |
| `FinishReplayParents.v1` | Finish provisional parent admissions for the replay binding before retaining worlds. | `owned_flight.rs:4056` finish_replay_parents | 255 `finish_replay_parents_action` | H | A: held restore staging |
| `RetainReplayedWorld.v5` | Bind a replayed world's original parent and optional Held overlay positions to the provisional destination world. | `owned_flight.rs:4073` retain_replayed_world | 256 `retain_replayed_world_action` | H T | A: held restore staging |

## Owned PGWire and session operations

The installed gateway route and the directory route differ. RTDB `multi/src/gateway.rs:340–365` checks the installation identity and prefers the ordered installed route when enrolled. Bijection's frozen recovery-stage connection is a separate privileged route and its scope comes from the archive stage.

| Operation | Semantics | Bijection call site | RTDB entry / effect | Verbs | Verdict |
| --- | --- | --- | --- | --- | --- |
| Startup `name@UUID` and `rtdb_installation_id` | Bind the connection and its replacement route to exactly the requested installed authority. | `connection.rs:571–590` connect | `multi/src/gateway.rs:31, 340–365`, `pgwire/src/connection.rs:144–201` | H R T S F | A: session routing |
| `SHOW rtdb_source_barrier` | Wait for a live source barrier before using the connection. | `connection.rs:502` | `node/src/control.rs:235–245, 332` | R | A: separate source confirmation |
| `SHOW rtdb_hosted_source_owner` | Confirm the source owner from the retained read transaction before accepting its cut. | `connection.rs:536–556` | `node/src/control.rs:235–245, 333–338` | H R | A: separate source confirmation |
| `SHOW rtdb_hosted_source_barrier` | Fetch confirmed authority, applied transaction ID and ordered system time, including an empty cut. | `connection.rs:623–652` | `node/src/control.rs:235–245, 339–351` | R | A: separate source confirmation |
| `SET TIME ZONE 'UTC'` | Fix the session interpretation of timestamps. | `connection.rs:613` | `node/src/control.rs:192–197` | R T | A: SQL session defaults |
| `SET AWAIT_TOKEN` | Set the causal/session floor before the next SQL admission. | `world.rs:771` | `node/src/control.rs:198–205` | R H T | A: session-carried floor |
| `BEGIN READ ONLY` | Admit one consistent snapshot for several dependent queries. | `connection.rs:536` snapshot, `world.rs` transaction builders | `node/src/control.rs:169–184` | H | E/L |
| `BEGIN READ WRITE` | Build an ordered write request including assertions and DML. | `world/cell_catalog/publication.rs:541, 550, 646` | `node/src/control.rs:169–184` | T | A: SQL transaction framing |
| `ASSERT` | Evaluate an ordered predicate and refuse the transaction on false, including a deliberate terminal refusal. | `relations.rs:335, 495`, `world/cell_catalog/publication.rs:541, 550, 670, 683`, `placement_order.rs:97–142` | `tx/src/resolver.rs:925–931` | T | E/L |
| `SELECT` with a valid/system basis | Project history, current rows, absence or counts at a chosen source position. | `world/exact_table.rs:83–91, 230–237`, `relations.rs:589` | `pgwire/src/protocol.rs:501–532` | H R | E/L |
| `COPY (query) TO STDOUT WITH (FORMAT 'arrow-stream')` | Stream an Arrow encoding of a held query. | `world/scan/arrow.rs:67` | `pgwire/src/protocol.rs:525–531`, `pgwire/src/copy.rs` | H R | A: stream framing |
| `INSERT INTO` | Append temporal rows, including catalog writes and original position markers. | `relations.rs:270`, `world/cell_catalog/publication.rs:464` | `tx/src/resolver.rs:922, 960–998` | T | E/L |
| `DELETE FROM` | Record a logical removal under the selected temporal scope. | `world/root_fact_receipts/retirement.rs:202, 271`, `world/release_grant.rs:205`, `world/restore/tenant_continuation.rs:526` | `tx/src/resolver.rs:923, 999–1010` | T | E/L |
| `ERASE FROM` | Remove all history for matching identities, including cleanup of private custody or restore rows. | `world/custody.rs:81, 247`, `world/key_recovery.rs:186, 735`, `world/erase.rs:1759`, `world/restore.rs:1920`, `world/release_grant.rs:1773`, `world/unit_control.rs:1698` | `tx/src/resolver.rs:924, 1011–1025` | T F | E/L |
| `CREATE TABLE` | Declare native catalog or fact relation with its temporal shape. | `relations.rs:231`, `world.rs:351–372` | `pgwire/src/protocol.rs:501–574`, `tx/src/resolver.rs:930–934` | T | E |
| `CREATE OR ALTER TABLE` | Install compatible field definitions before writing rows. | `relations.rs:305` | `pgwire/src/protocol.rs:501–574`, `tx/src/resolver.rs:930–934` | T | E |
| `CREATE INDEX IF NOT EXISTS` | Declare an ordered candidate or lookup path over a relation. | `relations.rs:465, 488` | `pgwire/src/protocol.rs:501–574`, `tx/src/resolver.rs:951–972` | T | E |
| `COMMIT` | End a read snapshot or order the accumulated write request. | `connection.rs:543`, `world/cell_catalog/publication.rs:448` | `node/src/control.rs:185–189` | H T | E/L |
| `ROLLBACK` | Discard unsubmitted work and release the session snapshot. | `world.rs:2327` | `node/src/control.rs:190` | H | A: SQL transaction framing |
| `SHOW LATEST_SUBMITTED_TX` | Read the session's latest submitted transaction key, disposition and await token. | `world.rs:1407`, `world/cell_catalog/publication.rs:448` | `node/src/control.rs:352–372` | T | A: implicit receipt readback |

## Hosted lifecycle

| Operation | Semantics | Bijection call site | RTDB entry / effect | Verbs | Verdict |
| --- | --- | --- | --- | --- | --- |
| `install` | Reserve the name and deployment identity, install initial authority, or verify a matching subsequent incarnation. | `hosted.rs:320–334, 426–437` | `multi/src/install.rs:239–253` | — | X: install |
| `schedule_disposal` | Fence the exact incarnation and start asynchronous serving disposal with an original receipt. | `hosted.rs:479–493` | `multi/src/install.rs:254–259` | — | X: retire |
| `inspect_disposal` | Read pending or terminal serving disposal with inventory evidence under the exact authority and epoch. | `hosted.rs:479–527` | `multi/src/install.rs:260–297, 304–316` | R of retire status | A: separate polling wire |
| `schedule_recovery_disposal` | Start retirement of independent archive custody and return the next remote inventory or completion. | `hosted.rs:487–527` | `multi/src/install.rs:274–294` | — | X: retire |
| `confirm_recovery_archive` | Report exact remote absence against the archive operation and inventory digest. | `hosted.rs:336–415` | `multi/src/install.rs:262–272` | — | A: caller-mediated disposal evidence under retire |

## Recovery service

| Operation | Semantics | Bijection call site | RTDB entry / effect | Verbs | Verdict |
| --- | --- | --- | --- | --- | --- |
| `capture_checkpoint` | Produce an independent archive of a certified checkpoint and return its bound manifest digest. | `recovery.rs:316–354, 382–396` | `multi/src/recovery.rs:347–389` | H for input | X: archive |
| `capture_checkpoint_suffix` | Pin the specified basis and archive the exact retained continuation of the captured root until its expiry. | `recovery.rs:324–331, 354–356`, `fact_points/worlds.rs:1416–1434` | `multi/src/recovery.rs:402–423` | H for input | X: archive |
| `verify_checkpoint_capture` | Revalidate the named manifest and return the certified basis bound to a fresh observation. | `recovery.rs:332–341, 357–363, 410–437` | `multi/src/recovery.rs:424–449` | R of archive status | A: separate archive verification RPC |
| `discard_checkpoint_capture` | Retire an exact capture and wait for archive custody disposal evidence. | `recovery.rs:365–370, 460–478, 626–644` | `multi/src/recovery.rs:751–772, 863–868` | — | X: retire |
| `recover_checkpoint` | Select a verified manifest as a recovery basis and report the durable recovery epoch and completion. | `recovery.rs:342, 364, 438–459` | `multi/src/recovery.rs:456–486` | — | X: restore |
| `stage_checkpoint` | Bind and materialize an independently sealed destination stage, returning its exact manifest. | `recovery.rs:481–510, 538–560` | `multi/src/recovery.rs:487–568` | H for input | X: restore |
| `transfer_checkpoint` | Stage a transfer, seal source replay, activate the target, and bind completion to matching terminal evidence and exact cut. | `recovery.rs:511–521, 561–591` | `multi/src/recovery.rs:569–629` | H for input | X: restore |
| `discard_checkpoint_stage` | Close admissions to the exact destination stage and reconcile disposal. | `recovery.rs:522–536, 592–625` | `multi/src/recovery.rs:497–568` | — | X: retire |
| `open_checkpoint_stage` | Open the authenticated, frozen stage as a read-only archive stream. | `recovery/staged.rs:529–549`, `recovery/relay.rs:328–337` | `multi/src/recovery.rs:887–943, 1006–1008` | H R of archive | E |
| `open_checkpoint_stage_owned_event_files` | Stream original owned event files without giving the relay write or live routing authority. | `recovery/relay.rs:310–327` | `multi/src/recovery.rs:887–943, 1006–1008` | H R of archive | E |
| `inspect_checkpoint_stage_owned_relations` | Read verified staged owned-relation inventory bound to the exact source, target and stage digest. | `recovery/staged.rs:243–274, 325–344` | `multi/src/recovery.rs:710–742` | R of archive | E |

The archive status and frozen-stage reads require an admin-issued archive capability. They use the read shape and do not add an authority-changing verb. RTDB has additional server/CLI actions, including the component transfer steps and capture-discard phases at `multi/src/recovery.rs:48–138`. Bijection does not send their tags in the audited transport. `transfer_checkpoint` and `discard_checkpoint_capture` are their client-side entry points.

## Operations carried inside those requests

These rows trace policy-bearing local operations and multiplexed payloads. The counts above do not include them as separate wire actions.

| Operation | Semantics | Bijection call site | RTDB sink | Verbs | Verdict |
| --- | --- | --- | --- | --- | --- |
| Hosted control check / replace | Compare original row revision and scope, then replace the selected control only in the authorized decision. | `owned_flight.rs:5244`, `fact_points/store.rs:1281` | `flight-sql/src/owned_actions.rs:5152–5172` | T | E |
| Owned row check, write and logical removal | Carry per-row checks, puts and temporal tombstones in grouped Arrow requests. | `fact_points/commit.rs:661`, `fact_points/landing_wire.rs` | `flight-sql/src/owned_actions.rs:1450–1590`, `tx/src/resolver.rs:1164–1184` | T | E/L |
| Owned row all-history erasure | Carry explicit erasure scope in the ordered fact and control decision. | `fact_points/erasure.rs:90–217`, `fact_points/landing_wire.rs` | `tx/src/resolver.rs:1180, 2527–2610`, `multi/src/journal/hosted/erasure.rs` | T F | E/L |
| `retire-relation` | Close writes to one relation and retain its old data through the declared horizon. | `relations.rs:47–64` | `flight-sql/src/owned_actions.rs:1567`, `tx/src/resolver.rs:1122` | T | E |
| Audience Flight handshake and renewal | Verify deployment audience, logical turn, alternate and attempt, and allocate bounded answer capacity to the exact seat. | `owned_flight.rs:371–429, 4599–4645`, `hosted.rs:711–725` | `multi/src/flight_gateway.rs:419–545`, `flight-sql/src/service/audience_owner.rs` | H R | A: seat-bound transport |
| Attempt recovery and failure settlement | Look up the exact ordered attempt row under a fresh hold, verify fingerprint, then reuse the original result or preserve an unresolved outcome. | `fact_points/attempts.rs:233–333` | `flight-sql/src/actions.rs:218, 139` | T R | A: attempt markers |
| Source close and continuation handoff | Seal source admission and inventory, check original receipt and destination continuation, and resume terminal source retirement. | `world/restore/handoff.rs:399, 596, 681, 889` | `multi/src/recovery.rs:569–709` for physical transfer, `flight-sql/src/actions.rs:139` for ordered application fences | T H plus restore and retire | E for application rows, X for physical authority |
| Held archive replay and release | Compare the selected archive census, replay each exact Original transaction once, finish the replay seal, and expose or abandon the held destination. | `recovery/staged.rs:654, 952, 1214, 1251, 1322, 1337` | `flight-sql/src/actions.rs:139, 254–256`, `multi/src/recovery.rs:487–568` | H R T plus restore | A: application-authored replay under a held writer |
| External-key recovery close/read | Order exact capsule recovery closure, then read its original close receipt before clearing local work. | `hosted.rs:440–478`, `world/key_recovery.rs` | `tx/src/resolver.rs:922–931, 1011–1025` | T R F | E for order and observations |
| Retained dependency and source-frontier readback | Read exact published positions and admission fences before opening a replacement, including null applied position on an empty source. | `connection.rs:494–562`, `fact_points/archive_admission.rs:16–52`, `fact_points/point_readback.rs` | `node/src/control.rs:235–245`, `flight-sql/src/actions.rs:154–157, 208, 246` | H R | A: multiple authority readbacks |

The RTDB-only versioned owned actions in the dispatcher are `SpatialHeld.v1`, `DropSpatialPath.v1`, `DropSpatialPath.v2`, `Create.v1`, `Commit.v1`, `CommitOrdered.v1`, `Commit.v7`, `Commit.v4`, `Commit.v3`, `ReadPoint.v1`, `ReadHeldPoint.v1`, `ReadHeldRange.v1`, `ReadHeldWorldRegionChanges.v1`, `NominateHeldExpiry.v1` and `ReadHeldChanges.v3`. Bijection uses the checked or counted modes of its live actions where applicable. A protocol changelog mention or older README example alone does not establish a client send site.
