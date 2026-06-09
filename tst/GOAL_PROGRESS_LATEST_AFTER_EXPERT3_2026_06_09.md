# GeoTop Sections 3-4 latest progress after expert3 audit

Date: 2026-06-09

## Current status

The zero-target-`sorry` goal is not complete. The current target scan shows
7 remaining target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:13967
dev34/GeoTop_3_4.thy:15610
```

This is progress relative to the expert3 report, which described an 8-hole
state. The Figure 4.10 cyclic boundary-subdivision package is now closed. The
remaining active `dev34` work is the endpoint boundary-arc fan package and the
one-sided semicircle/collar separation package.

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
     work is the same-length boundary-arc target model and fan/cone verification.

7. `geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34`
   - One-sided semicircle crosscut separation in a local collar.
   - Recent helpers now prove the spherical crosscut is contained in `U` from
     the collar assumption and that the edge interior point lies in `U`.

## What changed since the expert audits

The expert3 assessment remains useful, but its 8-hole map is now outdated in
one important way: `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`
has been closed. That makes the next finite-graph target narrower than the
audit described.

Recent work also reduced the endpoint package by adding source-chain listing
helpers and splitting the endpoint fan proof into smaller model/target steps.
For the semicircle package, the work has moved toward the audit-recommended
collar/radius-crossing proof instead of a broad Jordan-style argument.

## Verification and cache status

Commands checked for this report:

```bash
./check_dev34_fast.sh holes
rg -n "geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix|..." \
  STMT_INDEX.txt THEOREMS_AND_DEFS.txt PLAN_zero_sorry-expert*.md GOAL_PROGRESS* GOAL_STATUS*
./check_dev34_fast.sh focus-status dev34-fan dev34-semicircle graph-branch graph-branch-local
```

Focused status:

```text
dev34-fan: fresh prefix and slice cache
dev34-semicircle: fresh prefix and slice cache
graph-branch: stale/missing late slice cache
graph-branch-local: fresh local slice cache
```

The fast iteration path is therefore to continue in `dev34-fan` or
`dev34-semicircle`, where the relevant caches are fresh. If returning to the
branch-vertex proof, refresh the late graph-branch slice first.

## Recommended next order

1. Continue with a narrow active package: endpoint target model or the next
   semicircle collar/radius-crossing helper.
2. Return to the graph branch package only with the expert3 local-component
   bridge in mind; the current underpowered two-germ witness is not enough.
3. Keep the Section 3 and D42/D44 packages as named book-step packages, not
   scattered local claims.
4. Continue using full-index greps before adding lemmas and regenerate the
   theorem/statement indexes after theory changes.

The project is still approaching the goal: the hole count is lower and the
active packages are better isolated. The correct measure of remaining work is
closed proof packages, not elapsed days or raw `sorry` count.
