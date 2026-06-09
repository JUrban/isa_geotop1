# Live progress status after expert3 audit, 2026-06-09

This report is based on a fresh local hole scan:

```bash
cd /project/tst && ./check_dev34_fast.sh holes
```

Current target status: **7 executable target `sorry`s remain**.  This is
progress relative to expert3's 8-hole map.  The old Figure 4.10 cyclic boundary
subdivision package is no longer in the hole list; the remaining active
`dev34` graph work is now the endpoint boundary-arc fan model and the
one-sided semicircle/collar geometry.

## Current hole list

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:13967
dev34/GeoTop_3_4.thy:15944
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
```

## Stable remaining packages

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   - Moise Theorem 4.4 brick / regular-neighborhood component transfer.
   - Still the largest remaining package; treat as a named regular-neighborhood theorem, not local component algebra.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   - Section 3 chord subdisk induction transfer.
   - Needs side complexes proved to be smaller polygonal-disk triangulations, then transfer of free-triangle witnesses back to the parent disk.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   - Section 3 fold normalization with support.
   - This remains the engine behind Theorems 3.4 and 3.7; keep the support-parametric architecture.

4. `geotop_polygon_arc_opposite_boundary_decomposition_prefix`
   - Moise Theorem 4.2 theta / opposite-boundary arc separation.
   - Expert advice remains accurate: prove a theta or broken-line contradiction package instead of trying to solve it by raw component rewriting.

5. `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   - Graph-cache branch vertex local cutpoint package.
   - The remaining internal gap is the local-component bridge: from the connected split-side setup, obtain a component of `ball w r - (e1 union e2 union e3)` whose closure meets all three selected incident edge germs.
   - Do not replace this with a false general graph theorem. The simple-closed-curve/local-one-manifold hypothesis is essential.

6. `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
   - Endpoint chain to boundary-arc fan model.
   - The wrapper target package has been cleaned up; the remaining work is the model step: enumerate the endpoint chain, build a same-length boundary-arc target chain on one edge of a 2-simplex, and verify the cone/fan clauses.

7. `geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34`
   - One-sided semicircle crosscut separation.
   - The statement now has the stronger collar shape expert3 recommended. The remaining open step is metric simplex geometry: choose a small radius so `sphere p r inter sigma` is the standard one-sided arc and an outer witness in `U` remains outside the radius.

## What changed since expert3

Expert3's strategic diagnosis is still useful, but the finite-cycle part is partly
outdated locally.  The package
`geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34` is
indexed and no longer appears in `./check_dev34_fast.sh holes`.

The endpoint package also shifted: the visible hole is now the model theorem
`geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`, while
the target wrapper is checked in the focused fan slice.

Latest local inspection confirms that the later boundary-vertex fan wrappers are
downstream of this model hole.  In particular, the graph-only boundary-vertex
fan target theorems after the endpoint block prove the right final target shape,
but their proof chain currently calls the endpoint target wrapper, which calls
the model theorem.  They are therefore evidence that the statement shape is
right, not a shortcut that can be invoked to close the model theorem without
reordering or replacing that dependency chain.

## Current approach

The next useful proof work is the finite-graph/endpoint area.  The current best
route is:

1. Finish or isolate the graph-cache local-component bridge in
   `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`.
2. Use the no-branch / linear-chain consequences to support the endpoint source
   enumeration.
3. Close `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
   by reducing arbitrary finite vertex-set clauses to singleton and adjacent-edge
   cases, as expert3 recommended.

The broader Section 3 fold/subdisk packages, D42, and D44 are still real Moise
picture arguments. They should remain named packages with book-aligned helper
lemmas; moving them into deeper wrappers would not count as progress.

## Process notes

`CLAUDE.md` has been refreshed.  The important workflow constraints remain:

- grep `THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt` before adding lemmas;
- use focused checks rather than broad builds for each iteration;
- keep new proof structure `sorry`-first, then replace in small verified batches;
- regenerate indexes after theorem/cache changes.

Recent index grep confirms all seven stable packages are present in both the
name and statement indexes, and previous status reports are now also indexed.

Focused cache status after rereading expert3:

- `dev34-fan`: fresh core, fresh prefix cache, and fresh endpoint-fan slice.
- `graph-branch-local`: fresh prefix-base, fresh prefix cache, and fresh local
  branch slice.
- `dev34-semicircle`: core and earlier chained prefix are fresh, but the final
  semicircle prefix/slice around the remaining hole is stale and should only be
  refreshed when work returns to that package.
