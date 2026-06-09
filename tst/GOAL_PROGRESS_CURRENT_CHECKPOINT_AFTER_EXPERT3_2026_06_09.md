# GeoTop Sections 3-4 Current Checkpoint After Expert3, 2026-06-09

## Status

The zero-sorry goal is still incomplete. After closing the affine semicircle
transfer lemma, a live `./check_dev34_fast.sh holes` scan reports 7 target
holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:13967
dev34/GeoTop_3_4.thy:16197
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
geotop_edge_face_2simplex_small_sphere_halfspace_model_exists_dev34
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

The semicircle work has improved structurally and has now reduced the live hole
count by one. The current proof adds and verifies the standard upper semicircle
arc lemma:

```text
geotop_standard_upper_semicircle_arc_R2_dev34
```

It also proves the affine transfer lemma
`geotop_halfspace_sphere_affine_image_standard_upper_semicircle_exists_dev34`
using `orthogonal_transformation_exists`,
`orthogonal_transformation_surj`, and
`geotop_affine_linear_homeomorphism_UNIV`, then rewrites
`geotop_closed_halfspace_sphere_arc_R2_dev34` as a short homeomorphism-image
wrapper. The remaining active semicircle hole is the local edge-face half-plane
model `geotop_edge_face_2simplex_small_sphere_halfspace_model_exists_dev34`.

This is a useful split: the analytic arc parametrization and affine
normalization are done, and the remaining open semicircle work is now exactly
the local 2-simplex half-plane geometry.

## Current Interpretation

We are approaching the goal in structure, not in elapsed-time certainty. The
proof state is much more localized than it was several days ago, and the raw
hole count is now 7, but several of those 7 are theorem-sized Moise
diagram arguments:

- D44 brick / regular-neighborhood transfer;
- Section 3 chord subdisk free-triangle transfer;
- Section 3 support-controlled fold normalization;
- D42 theta / opposite-boundary arc separation;
- graph branch-vertex local cutpoint;
- endpoint-chain boundary-arc fan model;
- small-sphere half-plane model for a 2-simplex at an edge-interior point.

The main process lesson from the audits is still correct: do not spend days
trying to close these by local proof search at the final `sorry`. Each target
needs a small package of named lemmas, checked with focused slices.

## Recommended Next Move

The immediate active thread can stay on the semicircle split if the next proof
is the book/local-geometry fact:

```text
geotop_edge_face_2simplex_small_sphere_halfspace_model_exists_dev34
```

That proof should choose a radius below the distances from the edge-interior
point to the two edge endpoints and to the opposite side of the 2-simplex, then
show small spheres see the simplex as the closed half-plane bounded by the edge
line. If that starts expanding into broad convex-geometry infrastructure,
switch back to the endpoint-chain fan package. It is now the best graph-side
target after the Figure 4.10 cycle realization was closed. The branch-vertex
local cutpoint should be attacked only through the expert3 local-component
bridge for three selected germs, not by proving a false general "degree greater
than two implies cutpoint" graph statement.

## Verification Notes

Use the full indexes frequently:

```bash
rg -n "<topic>" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

For the current semicircle thread, rerun the two index generators after each
theory/report edit and use focused checks before committing.
