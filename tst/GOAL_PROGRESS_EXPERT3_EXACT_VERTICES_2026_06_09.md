# Goal Progress Brief - 2026-06-09

## Status

The zero-target-`sorry` goal is still open. A fresh target scan reports the
same 8 remaining target holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:2691
dev34/GeoTop_3_4.thy:10796
dev34/GeoTop_3_4.thy:12014
```

The stable package names remain:

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

The hygiene scan found no `sledgehammer` or `try0` markers in the target
layers. `git diff --check` is clean.

## Recent progress

The active Figure 4.10 proof has made concrete source-side progress. Recent
commits established the source graph connectivity, exact oriented successor
vertex orbit, exact oriented edge orbit, source successor period bound, and
successor-state injectivity/cardinality facts inside
`geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`.

The newest local step adds:

```text
geotop_explicit_edge_subdivision_vertices_subset_dev34
```

This proves that the explicit operation replacing an edge by two subedges
through a new point `R` introduces no vertices outside
`insert R (geotop_complex_vertices K)`, provided the explicit replacement is a
complex and `R` is distinct from the two old endpoints. The focused
`dev34-cycle-realization` check is fresh/clean after this addition, and the
generated indexes now include the lemma.

## Audit-adjusted assessment

`PLAN_zero_sorry-expert3.md` agrees with the earlier audits: the remaining
holes are not small tactic gaps. They are isolated but still package-sized
Moise arguments.

The most important expert3 point for the current active proof is the
distinction between:

```text
prescribed boundary points become vertices
```

and the stronger requirement needed by the cyclic target model:

```text
the target subdivision has exactly the listed vertices and no extras
```

The current boundary helper only gives the first form. The new local helper is
the first step toward the second form: exact/no-extra-vertices preservation for
one explicit edge subdivision. The next useful lemmas are the corresponding
strong versions of edge subdivision, subdivision-at-a-point, finite point
subdivision, and finally the 2-simplex boundary finite-point subdivision.

## Current blocker

The active blocker is still Figure 4.10 exact target realization:

```text
geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34
```

The source cycle is now well controlled. The target side has a standard
2-simplex boundary, chosen boundary vertices, a finite prescribed set `S_B`,
and a subdivision whose vertices contain `S_B`. What is missing is the exact
vertex equality needed for a cyclic listing:

```text
((lambda k. u k) ` {0..<p}) = geotop_complex_vertices F
```

The fastest route is to keep proving no-extra-vertices subdivision
infrastructure and then use it to turn the current weak target subdivision
into an exact one.

## Recommended next work

1. Prove the strong interior-edge subdivision lemma with
   `geotop_complex_vertices K' <= insert R (geotop_complex_vertices K)`.
2. Lift that to a strong `subdivide_at` lemma.
3. Iterate it over finite point sets to get
   `geotop_complex_vertices K' <= S union geotop_complex_vertices K`.
4. Specialize to the 2-simplex boundary, where `S_B` already contains the old
   boundary vertices, and combine subset plus containment to get exact target
   vertices.
5. Finish the Figure 4.10 cyclic boundary-cycle realization, then reuse the
   machinery for the endpoint boundary-arc fan.

After that sprint, the remaining order should be branch-vertex local cutpoint,
semicircle/collar separator after checking the statement strength, Section 3
subdisk transfer, Section 3 support-controlled fold normalization, D42 theta
separation, and D44 regular-neighborhood/brick transfer last.

## Verification

Commands run for this status:

```bash
bash gen_index.sh
bash gen_stmt_index.sh
./check_dev34_fast.sh focus dev34-cycle-realization
rg -n "^[^#]*sorry\\b|sledgehammer|try0" \
  dev34/GeoTop_3_4.thy \
  dev34_prefix/GeoTop_3_4_Prefix.thy \
  dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy \
  dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy
git diff --check
./check_dev34_fast.sh index geotop_explicit_edge_subdivision_vertices_subset_dev34
```
