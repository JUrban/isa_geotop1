# GeoTop Sections 3-4 current progress after expert audits

Date: 2026-06-09

This report supersedes the earlier June 9 seven-hole status files for the
current workspace.  It takes into account `PLAN_zero_sorry-expert.md`,
`PLAN_zero_sorry-expert1.md`, `PLAN_zero_sorry-expert2.md`, and
`PLAN_zero_sorry-expert3.md`, plus the latest local hole scan.

## Status

The zero-target-`sorry` goal is not complete.  A fresh check shows 8 target
holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:13967
dev34/GeoTop_3_4.thy:15918
dev34/GeoTop_3_4.thy:15935
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
```

This is not a regression in the mathematical package map.  The former single
one-sided semicircle package has been narrowed and split into two explicit
Euclidean geometry obligations:

```text
geotop_closed_halfspace_sphere_arc_R2_dev34
geotop_edge_face_2simplex_small_sphere_halfspace_model_exists_dev34
```

The downstream collar/radius separation wrapper is now structured and checked
against these named facts.  The live status is therefore best read as 7 stable
open packages, with the semicircle package exposed as two final geometry lemmas.

## Remaining packages

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   - Moise Theorem 4.4 brick / regular-neighborhood / component-frontier
     transfer.
   - This is still the largest remaining package and should stay a named
     regular-neighborhood theorem, not anonymous local component algebra.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   - Section 3 chord subdisk induction transfer.
   - Needs side complexes proved as smaller polygonal-disk triangulations and
     transfer of free-triangle witnesses back to the parent disk.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   - Section 3 fold normalization with support.
   - This remains the support-parametric engine for Theorems 3.4 and 3.7.

4. `geotop_polygon_arc_opposite_boundary_decomposition_prefix`
   - Moise Theorem 4.2 theta / opposite-boundary arc separation.
   - The expert audits are right: this needs a theta or broken-line
     contradiction package, not raw component rewriting.

5. `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   - Graph-cache branch vertex local cutpoint package.
   - The important missing bridge is still local: from the connected split-side
     setup, produce a component of `ball w r - (e1 union e2 union e3)` whose
     closure meets all three selected incident edge germs.  Do not replace this
     by the false general claim that degree greater than two always implies a
     graph cutpoint.

6. `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
   - Endpoint chain to boundary-arc fan model.
   - The remaining work is the model step: enumerate the endpoint chain, build a
     same-length boundary-arc target chain on a 2-simplex edge, then verify the
     cone/fan clauses by reducing arbitrary finite vertex subsets to singleton
     and adjacent-edge cases.

7. Semicircle geometry package
   - Open facts:
     `geotop_closed_halfspace_sphere_arc_R2_dev34` and
     `geotop_edge_face_2simplex_small_sphere_halfspace_model_exists_dev34`.
   - Recent commits already isolate the collar separation, outer witness, and
     radius-crossing contradiction.  What remains is pure metric geometry: a
     circle cut by a center half-plane is an arc, and a 2-simplex near an
     edge-interior point agrees with such a half-plane on sufficiently small
     spheres.

## Audit reconciliation

The expert audits remain useful, but some details are stale:

- The old Figure 4.10 cyclic boundary-subdivision target is closed locally and
  no longer appears in the hole list.
- The endpoint fan target was correctly retargeted to a boundary-arc fan; the
  visible hole is now the model theorem beneath the wrapper.
- Expert3's warning about the one-sided semicircle statement was acted on: the
  active collar statement has the stronger local assumptions.  The remaining
  gaps are now explicit geometric lemmas rather than an under-assumed
  separation theorem.

## Process and speed

The project is still approaching the goal, but the correct progress metric is
closed proof packages, not elapsed time or raw `sorry` count alone.  The
remaining holes are Moise picture arguments that have been localized into named
packages.

For faster iteration:

- keep using full-index greps over `THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt`
  before adding facts;
- use `./check_dev34_fast.sh focus ...` and hot slices instead of broad builds
  for every edit;
- preserve the `sorry`-first structure for new proof scaffolding, then replace
  in small verified batches;
- regenerate both indexes after theory or report changes.

Recommended next target: continue with the currently hot semicircle geometry if
the aim is to close the split just introduced; otherwise return to the endpoint
fan model, which is the next active graph package after the closed cycle model.
