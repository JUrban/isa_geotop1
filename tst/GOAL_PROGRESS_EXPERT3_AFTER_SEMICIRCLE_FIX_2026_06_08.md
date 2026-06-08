# GeoTop Sections 3-4 Progress After Expert3 And Semicircle Fix

Date: 2026-06-08

## Status

The zero-sorry goal is not complete. The checked target stack still has 8
target holes:

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

The current line scan is:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:1627
dev34/GeoTop_3_4.thy:9732
dev34/GeoTop_3_4.thy:10950
```

## Progress Since Expert3

Expert3's warning about the one-sided semicircle package was correct: the old
radius-level statement was too strong because it fixed an arbitrary radius.
The active statement now has the collar shape needed by the book argument:
given a local chart radius `s`, it concludes that there exists a smaller
radius `r < s` and crosscut `A = sphere p r Int sigma`.

This repair was verified by:

```text
./check_dev34_fast.sh focus dev34-semicircle
./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy geotop_edge_one_side_simplex_local_semicircle_radius_separates_domain_dev34
./check_dev34_fast.sh proc dev34/GeoTop_3_4.thy
```

The broad active-file check passed after the statement repair. The hole count
did not change because the remaining semicircle proof is now the real book
step: choose the sufficiently small one-sided semicircle and prove it separates
the local domain.

The index scripts are already caching the full searchable index over theory
files, advice/report markdown, and bounded transcript snippets. A fresh run
tracked 45 theories, 64 advice files, and 6 bounded session logs; the statement
index reused the session-log snippet cache.

## Expert3 Synthesis

The project is approaching the goal structurally, but not in the sense that the
remaining work is tactic cleanup. The remaining holes are still package-sized
Moise arguments.

The finite-graph/Figure 4.10 sprint remains the best next milestone:

1. Close `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`.
2. Reuse the boundary listing/subdivision machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.
3. Return to `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   only after strengthening the missing third-germ/local-component bridge.

For Figure 4.10, the live blocker is no longer theory order. The needed
boundary-subdivision helpers are available before the active theorem. The
remaining proof must upgrade the seed subdivision `F0` into an exact cyclic
standard-boundary listing with the required vertex bijection from the source
cycle.

## Verification Discipline

Use the full indexes frequently:

```bash
rg -n "keyword" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

For iteration speed, prefer focused checks first:

```bash
./check_dev34_fast.sh focus dev34-cycle-realization
./check_dev34_fast.sh focus dev34-fan
./check_dev34_fast.sh focus dev34-semicircle
./check_dev34_fast.sh focus graph-branch-local
```

Run broad `proc` checks after statement repairs or when a wrapper/caller chain
has been changed.
