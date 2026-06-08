# GeoTop Sections 3-4 Workspace Checkpoint, 2026-06-08

## Current Status

The zero-sorry goal is not complete.

A fresh local scan with `./check_dev34_fast.sh holes` reports 8 target holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:1627
dev34/GeoTop_3_4.thy:9732
dev34/GeoTop_3_4.thy:10964
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

This matches the expert3 audit in substance: the count is small, but the
remaining holes are package-sized Moise picture arguments, not routine tactic
cleanup.

## Progress Since The Expert Audits

The older 17-hole and 10-hole states are no longer current. The graph-prefix
cycle split is closed, and the active Figure 4.10 work has been narrowed to a
target standard-boundary realization problem.

Recent verified commits have improved the Figure 4.10 package without changing
the 8-hole count:

```text
b69694af Tighten cyclic listing verification proofs
d6f0832c Tighten cyclic source setup proofs
88fc44d2 Record semicircle collar containment
```

The active cycle-realization proof now has:

- source singleton and adjacent-edge cases staged explicitly;
- source vertex/cardinality decompositions recorded;
- a seed standard-boundary subdivision `F0` from
  `geotop_2simplex_boundary_finite_points_subdivision_preserves_vertices_dev34`;
- faster, more explicit verification proofs around the cyclic listing setup.

The remaining Figure 4.10 hole at
`geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34` is the
upgrade from the seed boundary subdivision to an exact cyclic listing and
source-target bijection.

## Current Blocker Diagnosis

The graph-cache branch-vertex hole is sharper than before, but it is not a
local tactic gap. Inside
`geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`, the proof
currently has a connected set `N` meeting two selected germs, with witnesses
`p` and `y`, and a third selected sphere point `z` on the remaining edge.

The missing bridge asks for one local component of
`ball w r - (e1 union e2 union e3)` whose closure meets all three selected
germs. The current assumptions visible at the hole give `p in N` and `y in N`,
but do not give `z in N`. So this should not be forced with automation. It
needs either a stronger upstream split-side package meeting all three germs, or
a more precise path/first-exit argument from the punctured connected carrier.

This agrees with expert3's local-star bridge diagnosis.

## Are We Approaching The Goal?

Yes structurally, but not in elapsed-time terms if we keep treating the holes
as one-line proof obligations.

The project is approaching the goal because the remaining work is now isolated
by name, the focused checker targets are usable, and the full indexes contain
the relevant helpers and audit notes. It is not close in the sense of "just
clean up tactics": D44, D42, Section 3 subdisk transfer, Section 3 supported
folding, the graph-cache local cutpoint, endpoint fan realization, and the
semicircle separator are each real formalization packages.

## Recommended Next Move

The best next milestone is still the finite graph / Figure 4.10 sprint, but
with the latest local state:

1. Close `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`
   by proving the exact standard-boundary cyclic listing from the existing seed
   subdivision.
2. Reuse the same boundary listing/subdivision machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.
3. Return to `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   only after either strengthening the upstream split-side package or stating a
   precise local-component bridge with the missing third-germ hypothesis.

For speed, every iteration should grep `THEOREMS_AND_DEFS.txt` and
`STMT_INDEX.txt` before adding helpers, use the focused checker for the active
package, and regenerate the indexes after theory or report changes.
