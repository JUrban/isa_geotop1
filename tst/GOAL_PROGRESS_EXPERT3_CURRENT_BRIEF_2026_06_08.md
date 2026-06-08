# GeoTop Sections 3-4 Current Progress Brief After Expert3, 2026-06-08

## Status

The zero-sorry goal is not complete. A fresh local run of
`./check_dev34_fast.sh holes` reports 8 target holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106:    sorry
dev34/GeoTop_3_4.thy:749:    sorry
dev34/GeoTop_3_4.thy:8001:    sorry
dev34/GeoTop_3_4.thy:9203:  sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047:    sorry
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9576:        sorry
```

The stable open packages are still:

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

## What Changed Since The Previous Brief

The latest verified checkpoint is:

```text
88c0a48b Isolate selected closure facts in branch bridge
```

This did not reduce the 8-hole count, but it made real progress inside the
graph-cache branch-vertex package. The remaining hole in
`geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix` is now more
sharply isolated: after choosing the three selected incident edge germs, the
proof has established that the selected sphere points lie in the closures of
their corresponding inward punctured edge germs. The remaining missing step is
still the expert3 local-star bridge: construct one component of
`ball w r - (e1 union e2 union e3)` whose closure meets all three selected
germs, then apply the existing radial-sector contradiction.

Focused verification of the graph branch slice passed with:

```bash
./check_dev34_fast.sh focus graph-branch-local
```

The full theorem and statement indexes were regenerated after the theory
change, and the indexes currently contain both the open package names and the
expert audit advice. This supports the requested faster workflow: grep the full
indexes first, edit one focused package, verify only the focused slice, then
regenerate the indexes after theory/report changes.

## Audit Synthesis

The previous expert audits and `PLAN_zero_sorry-expert3.md` agree on the main
state: the project is structurally approaching the goal, but it is not in the
"only a few tactic calls remain" phase. The count is small, yet the remaining
holes are package-sized Moise arguments.

Expert3 supersedes the older graph-sprint ordering in one important way: the
graph-prefix cycle split is now closed, so the immediate finite-graph work is
not the old orbit/path-carrier split. The best next sprint is:

1. close or further isolate
   `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`;
2. close
   `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`;
3. reuse the same listing/subdivision machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.

The Section 3 transfer/fold packages, D42 theta separation, D44
brick/regular-neighborhood transfer, and the one-sided semicircle separator
remain substantial and should not be treated as routine cleanup.

## Bottom Line

Progress is coherent but slower than the hole count suggests. The current work
has improved the branch-vertex proof state and the verification workflow, but no
target hole has closed since the previous brief. The next meaningful milestone
is closing a whole finite-graph/Figure 4.10 package, not merely moving the
remaining `sorry` deeper into another helper.
