# Goal Progress Brief After Expert3 Followup

Date: 2026-06-08

## Status

The zero-sorry goal is not complete. The current local hole scan still reports 8 target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:1680
dev34/GeoTop_3_4.thy:9785
dev34/GeoTop_3_4.thy:11003
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
```

The older expert reports that mention 17, 14, or 10 holes are stale. Their strategic diagnosis remains useful, but the current work should be measured against the stable 8-package map below.

## Stable Open Packages

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_decomposition_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
```

Expert3 names the Figure 4.10 package as `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`. After the recent refactor, the remaining active hole is more precisely inside `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`, which is the target-realization subproblem used by the cyclic wrapper.

## Recent Progress

The active Figure 4.10 work has made real progress. The proof now has explicit source-side singleton and adjacent-edge facts, closing-edge facts, finite source vertex/edge bookkeeping, and a seed target boundary subdivision `F0` obtained from `geotop_2simplex_boundary_finite_points_subdivision_preserves_vertices_dev34`.

The graph-prefix cycle split that earlier expert reports treated as open is no longer the immediate blocker. The remaining Figure 4.10 task is to upgrade the seed standard-boundary subdivision into an exact cyclic listing with a source-target vertex bijection.

The semicircle package was also corrected to the collar/existential-radius shape. That removes the earlier statement-shape concern, but the actual local Euclidean separation proof is still open.

## Current Risk

This is not a "last few tactics" state. The 8 visible holes are package-sized Moise picture arguments:

- D44 brick / regular-neighborhood component transfer is still the largest risk.
- Section 3 still has the chord subdisk transfer and support-controlled fold normalization packages.
- D42 still needs the theta/arc-separation argument.
- The graph-cache branch-vertex lemma still needs a precise local-component bridge; do not try to prove a false general statement that degree greater than two implies cutpoint for arbitrary finite graphs.
- Figure 4.10 is now narrower but still needs exact standard-boundary cyclic realization.

## Recommended Next Milestone

1. Finish `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34` by using the existing `F0` subdivision and reducing `geotop_isomorphism` to listed singleton and adjacent-edge cases.
2. Reuse that boundary listing/subdivision machinery for `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.
3. Return to `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix` only with a sharpened local-component bridge that accounts for all three selected germs.

For iteration speed, keep using the focused checker first:

```bash
./check_dev34_fast.sh focus dev34-cycle-realization
./check_dev34_fast.sh focus dev34-fan
./check_dev34_fast.sh focus graph-branch-local
./check_dev34_fast.sh holes
```

Use whole-index search frequently before adding helpers:

```bash
rg -n "standard boundary|cyclic listing|boundary arc fan|branch vertex|local component" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

Regenerate the indexes after adding proof infrastructure or status files:

```bash
bash gen_index.sh
bash gen_stmt_index.sh
```

