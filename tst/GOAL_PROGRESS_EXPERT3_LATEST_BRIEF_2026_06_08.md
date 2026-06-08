# GeoTop Sections 3-4 Latest Progress Brief, 2026-06-08

## Status

The zero-sorry goal is not complete.

The last stable audited baseline is 8 target holes, matching the expert3
assessment:

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_decomposition_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_standard_boundary_cycle_listing_data_with_source_bijection_dev34
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
```

A fresh local hole scan now reports 8 visible target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:1494
dev34/GeoTop_3_4.thy:9051
dev34/GeoTop_3_4.thy:10253
```

The temporary source-side holes from the in-progress Figure 4.10 refactor have
been closed. The active Figure 4.10 target-model package now has one remaining
hole again, now isolated as the source-to-target package
`geotop_standard_boundary_cycle_listing_data_with_source_bijection_dev34`.

## Progress Since Expert3

The expert3 audit said the graph-prefix cycle split was no longer the main
blocker and that the best near-term path was the finite graph / Figure 4.10
sprint. Local progress since then is aligned with that advice.

Recent committed work:

```text
16305b85 Isolate cyclic boundary target model
4f2e0949 Correct cyclic target parametrization contract
241de9e8 Prove cyclic listing isomorphism transfer
```

The most important new proved helper is
`geotop_cyclic_listing_isomorphism_from_matching_cases_dev34`. It isolates the
isomorphism proof for cyclic listings: once the source and target are both
reduced to singleton vertices and adjacent cyclic edges, `geotop_isomorphism`
is no longer the hard part.

The current work applies that helper inside
`geotop_cyclic_listing_standard_boundary_cycle_target_model_dev34`. It also
proves the source singleton and adjacent-edge convex-hull membership facts from
the cyclic listing decomposition and listed edge package. The focused active
theory check passed:

```bash
./check_dev34_fast.sh proc dev34/GeoTop_3_4.thy
```

The remaining Figure 4.10 burden is now mostly the target boundary subdivision
construction, not arbitrary isomorphism bookkeeping or source-side case
bookkeeping. The anonymous target-data hole has also been renamed as
`geotop_standard_boundary_cycle_listing_data_with_source_bijection_dev34`, and
the standard boundary cyclic listing contract is named by
`geotop_standard_boundary_cycle_listing_data_dev34`, so the missing book step is
searchable by theorem name and by target-data predicate.

Inside the source-to-target package, the source-side finite/nonempty vertex
facts, singleton membership facts, listed-edge membership facts, and listed-edge
endpoint distinctness facts have now been proved. It also proves the listed-edge
simplex-vertex facts, endpoint membership in the source vertex set, successor
membership in the listed source image, and source singleton/edge convex-hull
membership facts. The remaining local hole is the actual standard-boundary
cyclic subdivision and matching vertex map.

The same package now also records indexed source vertex membership, the closed
endpoint vertex membership, finiteness of the source singleton and edge images,
and nonemptiness of the source complex.

## Audit Synthesis

The direction is coherent: the active Figure 4.10 package has been split into
smaller obligations, and the full indexes confirm the relevant boundary
subdivision and cyclic-listing helpers are searchable in
`THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt`.

The project is still not close in the sense of "only tactics remain." The
remaining holes are package-sized formalizations of Moise picture arguments,
especially Section 3 subdisk/fold machinery, D42 theta separation, D44 bricks,
the graph-cache branch cutpoint package, endpoint fan realization, and
one-sided semicircle separation.

## Next Step

Continue the expert3 finite-graph sprint:

1. close `geotop_standard_boundary_cycle_listing_data_with_source_bijection_dev34`;
2. reuse the same listing/subdivision machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`;
3. return to `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   or further isolate its local-component bridge.

For iteration speed, keep grepping the full indexes before adding helpers, use
the focused checker targets, regenerate both indexes after report/theory edits,
and measure progress by closed named packages rather than raw line movement.
