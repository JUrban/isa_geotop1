# GeoTop Sections 3-4 latest progress after expert3 audit

Date: 2026-06-09

## Current status

The zero-target-`sorry` goal is not complete. A fresh target scan shows
7 remaining target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:13967
dev34/GeoTop_3_4.thy:15974
```

This is progress relative to the expert3 report's 8-hole map. The Figure 4.10
cyclic boundary-subdivision package
`geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`
is now closed locally. The remaining active `dev34` holes are the endpoint
boundary-arc fan model and the one-sided semicircle/collar separation package.

## Remaining proof packages

The remaining holes are still package-sized Moise arguments, not local tactic
cleanup:

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   - Theorem 4.4 brick / regular-neighborhood component-frontier transfer.
   - This remains the largest and highest-risk package.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   - Section 3 chord subdisk induction transfer.
   - Needs side-disk triangulation, strict smaller 2-simplex counts, and
     transfer of free-triangle witnesses back to the parent disk.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   - Section 3 support-parametric fold normalization.
   - Keep the support-parametric architecture; it serves both Theorem 3.4 and
     Theorem 3.7.

4. `geotop_polygon_arc_opposite_boundary_decomposition_prefix`
   - Theorem 4.2 opposite-boundary arc decomposition.
   - The expert audits are right that this should go through a theta/broken-line
     contradiction, not raw component algebra.

5. `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   - Branch-vertex local cutpoint package in the graph cache.
   - The missing bridge is still the local component meeting all three selected
     incident germs. Do not replace this with a false general graph theorem.

6. `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
   - Endpoint chain to boundary-arc fan model.
   - The source-chain listing infrastructure is mostly packaged. The remaining
     work is the same-length target boundary-arc subdivision plus cone/fan
     verification.

7. `geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34`
   - One-sided semicircle crosscut separation in a local collar.
   - Recent helpers now prove the crosscut is contained in `U`, provide an
     outer witness in `U`, and prove that such an outer witness disconnects
     `U - (sphere p r Int sigma)`. The remaining open step is the metric
     2-simplex geometry: choose a small radius for which
     `sphere p r Int sigma` is the standard one-sided semicircle arc while an
     edge-side point remains outside that radius.

## What changed since the expert audits

The expert3 assessment remains strategically useful, but its finite-cycle
diagnosis is now partly outdated. The old target
`geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`
is proved and indexed.

Since the last progress-report commit, the semicircle package was narrowed by:

```text
4143289f Add semicircle collar distance separation helpers
3c7d7985 Add semicircle outer witness separation helper
31ff4dee Narrow semicircle collar geometry to arc radius choice
```

The latest structure is better than the raw expert3 warning about an
under-assumed separator. The active statement uses the collar assumptions
`r < s`, local equality with the simplex, `geotop_polyhedron K Int ball p s <= U`,
and `U <= geotop_polyhedron K`. The remaining proof is not the radius-crossing
separation anymore; it is the small-sphere/2-simplex arc geometry needed to
produce a radius with the arc property.

## Verification and cache status

Commands checked for this update:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh focus-status dev34-semicircle dev34-fan graph-branch graph-branch-local
rg -n "geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34|..." \
  STMT_INDEX.txt THEOREMS_AND_DEFS.txt dev34/GeoTop_3_4.thy
```

Focused status:

```text
dev34-semicircle: fresh core, fresh prefix cache, fresh slice cache
dev34-fan: fresh core, fresh prefix cache, fresh slice cache
graph-branch: fresh prefix-base, stale/missing late prefix and slice cache
graph-branch-local: fresh prefix-base, fresh local prefix and slice cache
```

Fast iteration should therefore stay in `dev34-semicircle` or `dev34-fan`
unless there is a deliberate switch back to the graph branch. If returning to
the late branch-vertex proof, refresh the `graph-branch` cache first.

## Recommended next order

1. Continue with one hot active package: either close the endpoint fan model or
   prove/isolate the remaining semicircle small-radius arc geometry.
2. Keep using full-index greps before adding lemmas; no direct indexed lemma
   currently proves that `sphere p r Int sigma` is an arc for a small sphere at
   an edge-interior point of a 2-simplex.
3. Return to the graph branch only with the expert3 local-component bridge in
   mind; the current underpowered two-germ witness is not enough.
4. Keep the Section 3 and D42/D44 packages as named book-step packages rather
   than scattering their content into anonymous local claims.
5. Regenerate `THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt` after theory changes
   or when report content should be searchable by the full index.

The project is still approaching the goal: the hole count is lower, the old
Figure 4.10 cycle package is closed, and the active packages are better
isolated. The correct remaining measure is closed proof packages, not elapsed
days or raw `sorry` count alone.
