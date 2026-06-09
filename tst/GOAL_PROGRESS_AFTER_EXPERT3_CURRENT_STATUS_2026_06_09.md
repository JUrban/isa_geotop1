# GeoTop Sections 3-4 Progress Status After Expert3

Date: 2026-06-09

## Short Status

The zero-`sorry` goal is not finished. The current checked target hole inventory is still 8 `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:4329
dev34/GeoTop_3_4.thy:12434
dev34/GeoTop_3_4.thy:13652
```

This agrees with the latest expert3 audit: the remaining count is small, but the open items are package-sized Moise arguments rather than routine tactic cleanup.

## Verified Progress Since The Earlier Audits

The graph-prefix cycle split is no longer one of the open packages. The earlier difficult facts about non-adjacent reversed orbit edges and cut path carrier intersection have been closed and committed in the graph prefix layer.

The active Figure 4.10 theorem has also gained useful successor-orbit facts. In particular, the proof now exposes source listed-edge successor endpoint cases and current/next index uniqueness for both source and target successor orbits. These were checked with the focused `dev34-cycle-realization` slice before commit.

The working process is now using the full hole scan and targeted greps frequently, as recommended. `./check_dev34_fast.sh holes` gives the current 8-hole list quickly, and focused slices should remain the default for iteration.

## Current In-Progress Work

There is one tracked uncommitted edit:

```text
dev34_prefix_graph/GeoTop_3_4_Prefix_Graph.thy
```

It extracts the book proof that a closed degree-two oriented successor period visits each vertex at only one index:

```text
geotop_degree_two_oriented_edge_successor_period_vertex_index_unique_prefix
```

This is intended to support the active Figure 4.10 boundary-cycle realization by turning source/target successor orbits into ordered vertex listings, not merely arbitrary vertex bijections.

Important: this extraction has not yet been kernel-checked after insertion, so it should not be counted as completed progress until `./check_dev34_fast.sh focus dev34-cycle-realization` passes.

## Remaining Stable Packages

The stable open package names are:

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_decomposition_prefix
geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
```

The expert3 advice still looks right: treat the finite graph/Figure 4.10 work as the best near-term sprint, but do not confuse that with completion of the whole goal. The Section 3 fold/subdisk transfer, D42 arc separation, and D44 brick transfer remain high-risk topology packages.

## Recommended Next Steps

1. Verify the new graph-prefix extraction with:

   ```bash
   ./check_dev34_fast.sh focus dev34-cycle-realization
   ```

2. If it passes, use the extracted vertex-index uniqueness lemma inside `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34` to prove source/target successor vertex injectivity and period/cardinality matching.

3. Regenerate indexes after any verified theory change:

   ```bash
   bash gen_index.sh --force
   bash gen_stmt_index.sh --force
   ```

4. Recheck whether the two index-generation scripts cover all current split/session files. This was raised by the user and should be handled before relying on index completeness for the next sprint.

5. Commit only after focused verification, hole scan, marker scan, index regeneration, and `git diff --check`.

## Bottom Line

We are approaching the goal in the sense that the target is localized and the graph-cycle infrastructure has improved. We are not close in the sense of "a few tactics left": all 8 remaining holes still represent real formal proof packages, and the current graph extraction is promising but unverified.
