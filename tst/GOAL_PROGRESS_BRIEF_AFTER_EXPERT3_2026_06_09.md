# GeoTop Sections 3-4 Progress Brief After Expert3 - 2026-06-09

## Status

The zero-target-`sorry` goal is still open. A fresh local scan with
`./check_dev34_fast.sh holes` reports 8 target holes and no visible
`sledgehammer` or `try0` markers in the checked target files.

Current visible hole locations:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:3209
dev34/GeoTop_3_4.thy:11314
dev34/GeoTop_3_4.thy:12532
```

Stable package names:

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

So the project is not in final tactic-cleanup. The remaining holes are still
package-sized book arguments, matching `PLAN_zero_sorry-expert3.md`.

## Recent Progress

The active Figure 4.10 / cyclic boundary realization sprint has made real
progress since the expert3 audit. Recent commits strengthened the target-side
boundary subdivision chain:

```text
133fe1a5 Bound explicit edge subdivision vertices
2c6f3855 Strengthen interior edge subdivision vertices
032a5384 Strengthen edge subdivision vertices
0435e403 Strengthen point subdivision vertices
dc8d3f82 Iterate point subdivision vertex bounds
b20eec8e Specialize boundary vertex bounds
292791b0 Expose exact boundary subdivision vertices
```

The current active theorem
`geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34` now
proves exact target vertex control for the constructed boundary subdivision:

```text
geotop_complex_vertices F_B = S_B
card (geotop_complex_vertices F_B) = card (geotop_complex_vertices L)
```

This addresses the expert3 warning that merely making prescribed boundary
points into vertices is too weak. The active proof now has exact target
vertices, not just containment.

## Remaining Active Gap

The remaining Figure 4.10 hole is now narrower: construct or expose the cyclic
ordering/listing of the exact target boundary subdivision and the bijection
matching the source listing. In other words, the current missing part is no
longer exact vertex count; it is target cyclic order and adjacent-edge
incidence on the subdivided standard boundary.

The most likely next useful lemma is still the expert3-style target model:

```text
standard_2simplex_boundary_cycle_subdivision_with_n_vertices
```

or an equivalent statement that gives a finite subdivision of the standard
2-simplex boundary with a cyclic vertex listing and exact adjacent-edge cases.
That should then feed the existing cyclic-listing isomorphism helper.

## Audit-Adjusted Priority

Best next milestone:

1. Finish `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`.
2. Reuse the same ordered boundary-subdivision machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.
3. Return to the graph-cache branch-vertex local-component bridge.
4. Treat semicircle, Section 3 subdisk/fold, D42, and D44 as separate named
   book packages rather than trying to solve them by local proof search.

For speed, keep the loop tight: grep `THEOREMS_AND_DEFS.txt` and
`STMT_INDEX.txt`, edit one package, run the focused checker target, then run
the hole scan. Broad verification should wait until a named package closes.

## Commands Used

```bash
sed -n '1,240p' CLAUDE.md
./check_dev34_fast.sh holes
rg -n "^[^#]*\\bsorry\\b|sledgehammer|try0" \
  dev34_prefix/GeoTop_3_4_Prefix.thy \
  dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy \
  dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy \
  dev34/GeoTop_3_4.thy
git log --oneline -12
```
