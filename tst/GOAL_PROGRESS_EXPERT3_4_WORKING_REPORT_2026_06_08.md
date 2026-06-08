# GeoTop Sections 3-4 Progress Report After Expert3

Date: 2026-06-08

## Current Status

The zero-sorry goal is not complete.

A fresh local scan with `./check_dev34_fast.sh holes` reports 8 target holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:2210
dev34/GeoTop_3_4.thy:10315
dev34/GeoTop_3_4.thy:11533
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
```

The stable open packages are:

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

Older reports mentioning 17, 14, or 10 target holes are stale as counts, but
their diagnosis is still useful: the remaining holes are not routine tactic
cleanup. They are package-sized formalizations of Moise picture arguments.

## What The Expert Audits Clarify

Expert3's main point remains correct: progress should be measured by closing
named packages, not by moving line numbers. The best remaining structure is:

1. finite graph / Figure 4.10 boundary-cycle realization;
2. endpoint chain / boundary-arc fan realization;
3. one-sided semicircle separation;
4. Section 3 chord subdisk transfer and supported fold normalization;
5. D42 theta/arc separation;
6. D44 brick / regular-neighborhood component transfer.

Some expert3 details have changed locally. The old
`geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`
diagnosis now lands more precisely at
`geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`.
Recent work has also built substantial source and target boundary facts inside
that theorem, including triangle boundary side facts and the frontier side
cover. The current gap is the exact upgrade from the seed boundary subdivision
to a cyclic target listing and source-target vertex map.

The graph-cache branch-vertex package remains open, but the audit's warning is
important: do not try to prove a false general rule that degree greater than two
implies cutpoint for arbitrary finite graphs. The proof needs the
simple-closed-curve/local-star hypothesis and a precise local-component bridge.

## Recent Verified Direction

The active Figure 4.10 package is moving in the right direction. The current
proof has already packaged:

- three distinct source anchor vertices;
- a bijection from those source anchors to the three triangle boundary vertices;
- the three named triangle boundary edges as exact target boundary edges;
- distinctness and cardinality of the three boundary sides;
- the exact set of edge faces of the 2-simplex;
- the cover of `frontier sigma` by the three named sides.

The next small useful step is to record that this named frontier union lies in
the boundary carrier `geotop_polyhedron ?B`, then continue toward an exact
standard-boundary cyclic listing.

## Are We Approaching The Goal?

Yes structurally, but not yet in elapsed-time terms. The project is approaching
the goal because:

- the target hole count is stable at 8;
- the holes have stable theorem names;
- the generated full indexes can locate the relevant proof infrastructure and
  audit notes quickly;
- focused checks allow narrower iteration than full verification;
- active Figure 4.10 work is now a target-realization problem rather than an
  unstructured graph/isomorphism problem.

It is not close in the sense of "a few `by100 blast` calls remain." D44, D42,
Section 3 subdisk/fold work, the branch-vertex local cutpoint, endpoint fan
realization, and the semicircle separator are each real formalization packages.

## Recommended Next Move

Continue with the active Figure 4.10 target package:

1. Close `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`
   by upgrading the existing seed subdivision and boundary-side facts into an
   exact cyclic target listing and source-target bijection.
2. Reuse the same boundary-listing machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.
3. Return to `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   only after stating or proving the missing local-component bridge explicitly.

For speed, every iteration should grep the full indexes first:

```bash
rg -n "standard boundary|cyclic listing|boundary subdivision|boundary arc fan|branch vertex|local component" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

Use focused checks before broader verification:

```bash
./check_dev34_fast.sh focus dev34-cycle-realization
./check_dev34_fast.sh focus dev34-fan
./check_dev34_fast.sh focus graph-branch-local
./check_dev34_fast.sh holes
```

Regenerate both indexes after theory or report edits:

```bash
bash gen_index.sh
bash gen_stmt_index.sh
```
