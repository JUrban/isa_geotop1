# GeoTop Sections 3-4 Progress After Expert3 Open-Edge Step

Date: 2026-06-08

## Status

The zero-sorry goal is not complete. A fresh local
`./check_dev34_fast.sh holes` run still reports 8 target holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:2297
dev34/GeoTop_3_4.thy:10402
dev34/GeoTop_3_4.thy:11620
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
```

The stable open packages are unchanged:

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

## Expert3 Takeaway

Expert3's main diagnosis matches the current local state: the remaining work
must be closed package-by-package, not by chasing line numbers. The best next
package is still the Figure 4.10 boundary-cycle realization, followed by the
endpoint boundary-arc fan and the graph branch-vertex local cutpoint bridge.

The expert3 name `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`
is now represented locally by the more precise active target
`geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`.

## Latest Verified Step

Inside `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`,
the active proof now records that the open side `open_segment a_sigma b_sigma`
is a usable reservoir of boundary points:

- `open_segment a_sigma b_sigma` is contained in the boundary carrier
  `geotop_polyhedron ?B`;
- `open_segment a_sigma b_sigma` is infinite;
- the opposite vertex `c_sigma` is not in that open side.

This supports the next Figure 4.10 construction step: choose enough additional
points on one boundary edge to match the source vertex count, then feed that
finite boundary set into the existing boundary-subdivision helper.

## Verification

The focused target check passed:

```bash
./check_dev34_fast.sh focus dev34-cycle-realization
```

Additional scans:

```bash
./check_dev34_fast.sh holes
rg -n "sledgehammer|try0" dev34/GeoTop_3_4.thy dev34_prefix dev34_prefix_mid dev34_prefix_graph dev34_prefix_graph/cache dev34_core
git diff --check -- dev34/GeoTop_3_4.thy
```

The marker scan was empty and `git diff --check` was clean.
