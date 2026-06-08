# GeoTop Sections 3-4 Goal Progress Status, 2026-06-08

## Current Status

The zero-sorry goal is not complete. A fresh local hole scan still reports 8
target holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106:    sorry
dev34/GeoTop_3_4.thy:1460:    sorry
dev34/GeoTop_3_4.thy:8040:    sorry
dev34/GeoTop_3_4.thy:9242:  sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047:    sorry
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610:        sorry
```

The stable open packages are unchanged:

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_decomposition_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
```

No `sledgehammer` or `try0` markers were found in the checked target layers.

## Progress Since Expert3

The expert3 audit identified the active Figure 4.10 package as blocked mainly
by theory order: the useful 2-simplex boundary-subdivision helpers existed, but
the theorem
`geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`
could not use them.

That blocker has been addressed incrementally. The relevant boundary helpers
have been moved above the active cycle theorem, including the final helper
`geotop_2simplex_boundary_finite_points_subdivision_preserves_vertices_dev34`.
Inside the active theorem, the proof now obtains a finite target boundary
subdivision witness `F0`, proves it is a complex, and proves its vertex set is
finite. The focused check passed after this edit:

```bash
./check_dev34_fast.sh focus dev34-cycle-realization
```

This is real structural progress, but it does not close a target hole yet. The
remaining local hole is still the Figure 4.10 model step:

```text
geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34
```

The missing content is now narrower: construct or expose a cyclic listing for
the target boundary subdivision and prove the `geotop_isomorphism` by reducing
source simplexes to singleton and adjacent-edge cases.

## Audit Synthesis

The previous audits and `PLAN_zero_sorry-expert3.md` agree on the main
assessment. The project is approaching the goal structurally, but the remaining
8 holes are still package-sized Moise arguments, not routine tactic cleanup.

Expert3 also supersedes one older work plan: the graph-prefix cycle split is no
longer an open prerequisite. The best near-term milestone is now:

1. close `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`;
2. reuse the same boundary listing/subdivision machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`;
3. close or further isolate
   `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`.

The Section 3 transfer/fold packages, D42 opposite-boundary arc decomposition,
D44 brick/regular-neighborhood transfer, and the one-sided semicircle separator
remain substantial independent proof packages.

## Workflow Notes

The full search indexes are useful and should be grepped frequently before
editing. After this checkpoint, the relevant searches are:

```bash
rg -n "geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34|geotop_2simplex_boundary_finite_points_subdivision_preserves_vertices_dev34" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
rg -n "Figure 4.10|boundary-subdivision|cyclic listing|expert3" STMT_INDEX.txt
```

The current efficient loop is: grep the full indexes, edit only one focused
package, run the focused checker, run the hole/hygiene scans, then regenerate
`THEOREMS_AND_DEFS.*` and `STMT_INDEX.txt`.
