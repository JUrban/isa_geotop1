# GeoTop Sections 3-4 Current Checkpoint After Expert3, 2026-06-09

## Status

The zero-sorry goal is still incomplete. After closing the affine semicircle
transfer lemma and the edge-face small-sphere half-plane model, a live
`./check_dev34_fast.sh holes` scan reports 6 target holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:13967
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
```

The active `dev34` line numbers have moved because of the current semicircle
work. The meaningful open package names are:

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_decomposition_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34
```

This is real progress from the expert-audit sequence, but it is not yet the
goal. The remaining holes are still named book-step packages or metric geometry
packages, not routine tactic cleanup.

## What Changed Since Expert3

The expert3 audit remains strategically useful, but some names in it are now
outdated locally.

The Figure 4.10 cyclic boundary-subdivision package that expert3 called
`geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34` is
no longer in the live hole list. Current indexed reports also record that this
cycle realization work has been closed locally. The finite-graph sprint is
therefore narrower now: the endpoint-chain fan package and the branch-vertex
local cutpoint package remain.

The semicircle work has now closed the local geometry package identified by
expert3. The current proof adds and verifies the standard upper semicircle arc
lemma:

```text
geotop_standard_upper_semicircle_arc_R2_dev34
```

It also proves the affine transfer lemma
`geotop_halfspace_sphere_affine_image_standard_upper_semicircle_exists_dev34`
using `orthogonal_transformation_exists`,
`orthogonal_transformation_surj`, and
`geotop_affine_linear_homeomorphism_UNIV`, then rewrites
`geotop_closed_halfspace_sphere_arc_R2_dev34` as a short homeomorphism-image
wrapper.

It then adds the one-sided probe-triangle helper
`geotop_probe_triangle_contains_small_halfball_dev34` and uses it to prove
`geotop_edge_face_2simplex_small_sphere_halfspace_model_exists_dev34`. That
closes the pure metric 2-simplex semicircle geometry: near an edge-interior
point, small spheres intersect the 2-simplex exactly as they intersect the
closed inward half-plane.

## Current Interpretation

We are approaching the goal in structure, not in elapsed-time certainty. The
proof state is much more localized than it was several days ago, and the raw
hole count is now 6, but several of those 6 are theorem-sized Moise
diagram arguments:

- D44 brick / regular-neighborhood transfer;
- Section 3 chord subdisk free-triangle transfer;
- Section 3 support-controlled fold normalization;
- D42 theta / opposite-boundary arc separation;
- graph branch-vertex local cutpoint;
- endpoint-chain boundary-arc fan model.

The main process lesson from the audits is still correct: do not spend days
trying to close these by local proof search at the final `sorry`. Each target
needs a small package of named lemmas, checked with focused slices.

## Current Follow-Up After Re-Reading Expert3

After re-reading `CLAUDE.md`, `PLAN_zero_sorry-expert3.md`, and the live
graph-cache proof, the endpoint-chain fan is not the best immediate next
target. The active endpoint model theorem can already call existing chain
listing machinery once a degree-one-or-two source graph hypothesis is
available, but deriving that degree bound from the current hypotheses depends
on ruling out branch vertices. The live branch-vertex package is therefore
upstream of the endpoint fan, not merely an adjacent cleanup.

The remaining graph-cache hole is exactly the expert3 local-star bridge inside
`geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`. The file
has already constructed:

```text
three selected incident edge germs e1 e2 e3 at w
canonical sphere points x1 x2 x3 on those germs
the simple-closed-curve arc-side split through w and q1
a selected split-side package with p,y connected in the punctured carrier
the radial-sector bound saying no one local component can touch all three germs
```

The only internal `sorry` is the bridge from the connected split-side package
to a component of `ball w r - (e1 union e2 union e3)` whose closure touches all
three selected germs. Immediately after that, the already-proved sector bound
derives the contradiction.

## Recommended Next Move

The immediate active semicircle package is closed. The next best target is now
the graph-cache branch local cutpoint bridge:

```text
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
```

The endpoint-chain fan package:

```text
geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34
```

should follow after this no-branch/degree-bound bridge is available. The
branch-vertex local cutpoint should still be attacked only through the expert3
local-component bridge for three selected germs, not by proving a false general
"degree greater than two implies cutpoint" graph statement. The larger
semicircle separation theorem should be revisited only after checking the
collar assumptions noted in expert3; the pure local half-plane model is no
longer the blocker.

## Verification Notes

Use the full indexes frequently:

```bash
rg -n "<topic>" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

After theory/report edits, rerun the two index generators and use focused
checks before committing. The checked semicircle commands for this checkpoint
were:

```bash
./check_dev34_fast.sh focus dev34-semicircle geotop_edge_face_2simplex_small_sphere_halfspace_model_exists_dev34
./check_dev34_fast.sh focus dev34-semicircle geotop_edge_simplex_small_sphere_arc_radius_bound_exists_dev34
./check_dev34_fast.sh holes
```

The current follow-up verification command was:

```bash
./check_dev34_fast.sh holes
```

It still reports the same 6 holes listed above.
