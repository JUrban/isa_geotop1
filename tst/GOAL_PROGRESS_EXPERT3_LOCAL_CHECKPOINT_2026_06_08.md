# GeoTop Sections 3-4 Local Checkpoint After Expert3, 2026-06-08

## Status

The zero-sorry goal is not complete. A fresh local scan with
`./check_dev34_fast.sh holes` reports 8 target holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106:    sorry
dev34/GeoTop_3_4.thy:1550:    sorry
dev34/GeoTop_3_4.thy:8133:    sorry
dev34/GeoTop_3_4.thy:9335:  sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047:    sorry
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610:        sorry
```

No `sledgehammer` or `try0` markers were found in the checked target layers.

The stable open packages are:

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

## Latest Verified Work

The active `dev34/GeoTop_3_4.thy` edits after the expert3 audit were verified
with:

```bash
./check_dev34_fast.sh proc dev34/GeoTop_3_4.thy
```

That check passed. The edits do not close a target hole, but they make the
Figure 4.10 cycle package more proof-ready:

- `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`
  now explicitly assumes the cyclic closure `v p = v 0`.
- The wrapper
  `geotop_cyclic_vertex_listing_standard_boundary_subdivision_model_dev34`
  and successor-orbit caller now pass that closure fact.
- Several brittle broad proof steps inside the active Figure 4.10 setup were
  split into explicit singleton/edge and convex-hull case facts.
- The source-side reduction now proves that any nonempty vertex subset whose
  convex hull is in `L` is either a listed singleton or a listed adjacent
  edge pair.

This is structural progress inside the active cycle-realization package, not a
hole-count reduction.

## Expert Audit Synthesis

The previous audits and `PLAN_zero_sorry-expert3.md` agree with the local
state: the project is much closer than it was, but the remaining 8 holes are
package-sized Moise arguments, not routine tactic cleanup.

Expert3 is especially useful for the next milestone. It says the graph-prefix
cycle split is no longer the main blocker; the immediate finite-graph work is
now:

1. close the active Figure 4.10 cyclic boundary-subdivision model;
2. reuse the same listing/subdivision machinery for the endpoint-chain
   boundary-arc fan target;
3. close or further isolate the branch-vertex local cutpoint package.

For the active Figure 4.10 package, the next missing mathematical step is still
to construct or expose a target cyclic boundary listing for the standard
2-simplex boundary subdivision, then prove `geotop_isomorphism` by the two
source cases already being isolated: singleton vertices and adjacent listed
edges. The current finite-points boundary subdivision helper is useful, but it
does not by itself provide the cyclic order/listing needed for the isomorphism.

## Workflow Notes

The full indexes were regenerated after the verified theory edits. They should
be used frequently with `rg`, especially before introducing new helper lemmas.
Relevant searches are:

```bash
rg -n "geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34|cyclic boundary|boundary subdivision" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
rg -n "geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34|boundary arc fan|endpoint chain" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
rg -n "geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix|local component|selected germs" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

The faster iteration loop should be: grep the full indexes, edit one focused
package, verify with the smallest reliable focus/proc target, run the hole and
hygiene scans, regenerate indexes after theory or report edits, and commit
small verified checkpoints.
