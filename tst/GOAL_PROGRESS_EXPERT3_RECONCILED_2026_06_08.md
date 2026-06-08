# GeoTop Sections 3-4 Progress Report After Expert3, 2026-06-08

## Status

The zero-sorry goal is not complete. A fresh local scan with
`./check_dev34_fast.sh holes` reports 8 target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:1427
dev34/GeoTop_3_4.thy:9502
dev34/GeoTop_3_4.thy:10704
```

No `sledgehammer` or `try0` markers were found in the checked target layers.
This matches the expert3 conclusion: the remaining count is small, but these
are package-sized Moise picture arguments, not routine tactic cleanup.

## Stable Open Packages

Line numbers keep moving, so the useful inventory is the theorem/package names:

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

The active Figure 4.10 obligation is currently isolated as
`geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`. This
is the same cyclic boundary-subdivision package that earlier reports called
`geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`,
but after the recent refactor the remaining local hole is inside the stronger
target-realization lemma.

## Progress Assessment

The project is still moving in the right direction structurally:

- older audit snapshots had 17, then 14, then 10 target holes; the current
  checked target stack has 8;
- the graph-prefix cycle split is closed, so Figure 4.10 is no longer blocked
  by the old cycle-order split;
- the cyclic-listing isomorphism bookkeeping has been separated from the target
  boundary-subdivision construction;
- the active Figure 4.10 proof now obtains a finite standard-boundary seed
  subdivision `F0` from
  `geotop_2simplex_boundary_finite_points_subdivision_preserves_vertices_dev34`;
- the full indexes contain the current expert3 advice and the key helper names,
  including the boundary subdivision, cyclic isomorphism, and branch-vertex
  packages.

The project is not near final close-out in the sense of "only tactics remain."
The remaining hard packages are still:

- D44 brick / regular-neighborhood transfer;
- Section 3 chord subdisk transfer;
- Section 3 support-controlled fold normalization;
- D42 theta / opposite-boundary arc separation;
- graph-cache branch-vertex local cutpoint;
- Figure 4.10 standard-boundary cyclic realization;
- endpoint-chain boundary-arc fan realization;
- one-sided semicircle separation, whose statement still needs care.

## Iteration Speed

The current focused-cache status supports targeted work, but not broad checks on
every edit. The useful hot targets are:

```text
graph-branch-local
dev34-cycle-realization
```

Several other targets still have stale or missing split caches and should be
warmed only when actively working on them:

```text
mid-split-free
mid-fold
mid-d42
prefix-d44
dev34-fan
dev34-semicircle
```

The fastest loop is therefore:

1. search `THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt` before adding helpers;
2. edit one named package only;
3. run the focused checker target for that package;
4. regenerate both indexes after theory or report edits;
5. commit verified increments.

I do not see an immediate need to change the two index-generation scripts just
because of `PLAN_zero_sorry-expert3.md`; the current indexes already include
the expert3 advice and the relevant report files. The important operational
point is to regenerate them after new theory/report changes.

## Recommended Next Milestone

Follow expert3's finite-graph/Figure 4.10 sprint, adjusted for the latest local
state:

1. close `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`;
2. reuse the same boundary listing/subdivision machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`;
3. return to `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   or further isolate its local-component bridge.

Progress should be measured by closed named packages, not by moving `sorry`s to
new line numbers.
