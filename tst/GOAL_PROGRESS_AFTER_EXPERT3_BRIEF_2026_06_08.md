# GeoTop Sections 3-4 Progress Brief After Expert3, 2026-06-08

## Current Status

The zero-sorry goal is not complete. A fresh local run of
`./check_dev34_fast.sh holes` reports 8 target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106:    sorry
dev34/GeoTop_3_4.thy:749:    sorry
dev34/GeoTop_3_4.thy:8001:    sorry
dev34/GeoTop_3_4.thy:9203:  sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047:    sorry
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9529:      sorry
```

The stable open package names remain:

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

## Progress Since The Previous Audit

The expert3 audit is directionally consistent with the local state. The
graph-prefix cycle split is no longer the bottleneck; the remaining finite graph
work is concentrated in the graph-cache branch-vertex local cutpoint package and
the two active realization packages in `dev34`.

The latest verified checkpoint is commit `84b5cd7b`:

```text
Expose selected germ closure
```

That commit adds a proved local helper
`hselected_sphere_germ_closure` inside the branch-vertex graph-cache package.
It shows that each selected sphere germ on one of the three incident edges lies
in the closure of the corresponding inward punctured edge germ. This does not
close the branch-vertex package, but it prepares the missing local-component
bridge that expert3 identified.

Focused verification used:

```bash
./check_dev34_fast.sh focus graph-branch-local
```

The graph slice had already been verified before commit, and the subsequent
focused check hit the fresh cache for the same slice. The index files were
regenerated and committed with the theory change.

## Assessment

The project is still approaching the goal structurally: the remaining work is
mapped to 8 named packages, the full indexes include the current reports and
theorem statements, and focused checker targets avoid multi-minute broad
verification on ordinary iterations.

It is not close in the sense of "only tactics remain." The visible count is
small, but several holes are still package-sized formalizations of Moise
arguments:

- the branch-vertex local cutpoint bridge;
- Figure 4.10 cyclic boundary subdivision;
- endpoint-chain boundary-arc fan realization;
- one-sided semicircle separation, whose statement still needs care;
- Section 3 chord/subdisk transfer and fold normalization;
- Theorem 4.2 theta/arc decomposition;
- Theorem 4.4 brick/regular-neighborhood transfer.

## Recommended Next Move

Continue the finite-graph sprint recommended by expert3:

1. Finish or further isolate
   `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`.
2. Use the existing boundary-subdivision helpers to close
   `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`.
3. Reuse the same listing/subdivision machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.

For speed, keep using the full text indexes with `rg` before adding facts, then
verify only the relevant focused slice. Regenerate both indexes after theory or
report changes and commit each verified increment.
