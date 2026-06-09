# Goal Progress Report - 2026-06-09

## Current status

The zero-target-`sorry` goal is not finished. The current local target scan still reports 8 `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:2510
dev34/GeoTop_3_4.thy:10615
dev34/GeoTop_3_4.thy:11833
```

The stable package names are:

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

There are no visible `sledgehammer` or `try0` markers in the target scan. The recently touched target files and generated indexes were clean after commit `1117ba8a Expose source cycle connectivity`.

## Recent concrete progress

The newest committed Figure 4.10 work added and verified:

```text
geotop_closed_indexed_edge_cycle_complex_connected_dev34
```

This helper turns a closed indexed edge cycle into `geotop_complex_connected K`. The active theorem `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34` now proves:

```text
hsource_connected: geotop_complex_connected L
hsource_successor_cycle_decomp: L equals the singleton/edge orbit of an oriented successor cycle
```

That is a real reduction in the Figure 4.10 proof: the source graph is now known connected and has an explicit oriented successor-cycle decomposition. The latest focused verification for the cycle-realization target passed after this change.

## Audit-adjusted assessment

The new expert audit `PLAN_zero_sorry-expert3.md` agrees with the earlier audits on the key point: the remaining 8 holes are package-sized Moise arguments, not isolated automation failures.

The graph-prefix cycle split is no longer an open target. That changes the immediate sprint: the active Figure 4.10 work should not restart graph-cycle splitting. The remaining gap is the exact standard-boundary realization and then reuse of that machinery for the endpoint fan.

The audit also gives two cautions that should steer the next steps:

```text
1. Do not use a weak "prescribed points become vertices" subdivision lemma
   as if it proved exact target vertices.
2. Check the one-sided semicircle statement before proof work; the
   radius-level version may be under-assumed unless a larger collar in U
   is available.
```

## Main active blocker

The active proof is stopped at:

```text
geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34
```

The existing target-side construction has:

```text
standard 2-simplex boundary complex ?B
named boundary vertices a_sigma, b_sigma, c_sigma
source anchor map to those three vertices
finite extra boundary points T_extra on open_segment a_sigma b_sigma
target finite set S_B with card S_B = card (geotop_complex_vertices L)
subdivision F_B whose vertices contain S_B and preserve old boundary vertices
```

The problem is exactness. The available subdivision helper proves prescribed boundary points become vertices, but the target predicate needs a cyclic listing of all target vertices:

```text
((lambda k. u k) ` {0..<p}) = geotop_complex_vertices F
```

So the next proof step needs either:

```text
an exact no-extra-vertices boundary subdivision lemma
```

or:

```text
a direct construction of the boundary cycle complex from an ordered boundary list
```

The new source successor-cycle decomposition should be used to transfer the source incidence pattern to the target cycle once exact target vertices/edges are available.

## Recommended next order

1. Finish the active Figure 4.10 exact boundary-cycle realization.
2. Reuse the boundary-cycle/listing machinery for the endpoint boundary-arc fan target.
3. Close the graph-cache branch-vertex local cutpoint bridge.
4. Recheck and then prove the one-sided semicircle/collar separator.
5. Finish Section 3 subdisk transfer.
6. Finish Section 3 support-controlled fold normalization.
7. Finish D42 via a reusable theta-separation lemma.
8. Finish D44 last as a regular-neighborhood / brick-transfer package.

## Process notes

Use the full indexes frequently:

```bash
rg -n "pattern" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

Use focused verification instead of broad rebuilds during iteration:

```bash
./check_dev34_fast.sh focus dev34-cycle-realization
./check_dev34_fast.sh focus dev34-fan
./check_dev34_fast.sh focus-status
```

When theorem statements or theory content change, regenerate the generated indexes before committing. This report-only update does not require index regeneration.
