# GeoTop Sections 3-4 Status

Date: 2026-06-05

Branch: `codex-dev34-cache`

This report summarizes the current state of the Section 3-4 formalization after
about 2.5 days of concentrated work on this goal.

## Executive Status

Sections 3 and 4 are not yet complete. The development is much better isolated,
the build is green, and a large amount of formerly active proof text has been
moved into cached sessions. The remaining target surface is now small by count:

- 17 executable `sorry`s remain in the Section 3-4 target stack.
- `tst/dev34_core/GeoTop_3_4_Core.thy` has 0 `sorry`s.
- `tst/dev34_prefix/GeoTop_3_4_Prefix.thy` has 12 `sorry`s.
- `tst/dev34/GeoTop_3_4.thy` has 5 `sorry`s.

The count is encouraging, but the remaining obligations are not small cleanup.
They are mostly the hard textbook construction steps: the Theorem 3.3
free-triangle induction, supported polygon straightening, Theorem 4.2/4.4
Jordan separation refinements, the Figure 4.10 cyclic boundary model, and the
local edge-chart semicircle/circle arguments used in Theorems 4.8-4.10.

So the honest completion assessment is:

- Statement/skeleton coverage: essentially complete for the current Section 3-4
  plan.
- Infrastructure/session engineering: in good shape.
- Proof completion by number of holes: close enough to track manually, 17
  remaining.
- Proof completion by difficulty/time: not near the end yet, because several
  remaining holes are full book subarguments rather than automation gaps.

## Current Session Layout

The active development is split as follows:

- `dev34_prefix`: Section 3 and early Section 4.
- `dev34_facts`, `dev34_workfacts`, `dev34_linkfacts`, `dev34_graphfacts`,
  `dev34_graphwork`, `dev34_openstar`: cached support layers.
- `dev34_core`: completed, sorry-free prefix of the former active
  `GeoTop_3_4.thy`.
- `dev34`: active remaining Section 4 manifold/local-model layer.

The newest cache split is:

- Commit `76e104d3`: `Cache completed GeoTop 3-4 core prefix`
- It moved the first 3866 lines of completed `GeoTop_3_4.thy` into
  `dev34_core/GeoTop_3_4_Core.thy`.
- Warm active verification improved from about `1:08` to about `0:58` on the
  measured local run.

Current warm-build command:

```bash
cd /project/tst
/project/bin/isabelle process_theories -d . -d dev34_pre -d dev34_prefix \
  -d dev34_facts -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
  -d dev34_graphwork -d dev34_openstar -d dev34_core -d dev34 \
  -l GeoTop34Dev -o quick_and_dirty -f dev34/GeoTop_3_4.thy
```

## Remaining Holes

Current evidence:

```bash
rg -n "\bsorry\b|sledgehammer" tst/dev34_prefix tst/dev34_core tst/dev34
```

### Section 3 / Prefix Holes

In `tst/dev34_prefix/GeoTop_3_4_Prefix.thy`:

- Line 1994:
  `geotop_two_triangle_boundary_contact_edges_cover_prefix`
  Base case for Theorem 3.3: in a two-triangle disk, the part of one triangle
  on the polygon boundary is covered by whole selected boundary edge faces.

- Line 2011:
  `geotop_two_triangle_not_all_boundary_edges_prefix`
  Base case for Theorem 3.3: one of two disk triangles cannot have all three
  edges on the polygon boundary.

- Line 2179:
  `geotop_polygon_disk_two_boundary_2simplexes_prefix`
  Induction prerequisite for Theorem 3.3: if there are more than two
  2-simplexes, at least two 2-simplexes have boundary edges.

- Line 3052:
  Inside the Theorem 3.3 induction proof.
  This is the book step that decomposes the polygonal disk at a non-free
  boundary triangle into two smaller polygonal disks, applies induction to both,
  and transfers the free 2-simplexes back.

- Line 3447:
  `ind_step` inside `Theorem_GT_3_4`.
  This is the reduction step using a free 2-simplex and a plane homeomorphism
  fold to reduce the number of 2-simplexes.

- Line 3906:
  `h_support_in_U` inside `Theorem_GT_3_7`.
  This is the supported version of Theorem 3.4, where each fold must be chosen
  fixed outside the prescribed open set `U`.

### Section 4 / Prefix Holes

In `tst/dev34_prefix/GeoTop_3_4_Prefix.thy`:

- Line 4237:
  `hD42_disjoint` inside `Theorem_GT_4_2`.
  This is the main arc-separation argument: the `Q`-side and `S`-side
  components of `I - A` are distinct and cover the complement.

- Line 4332:
  `hD44_bricks` inside `Theorem_GT_4_4`.
  Brick decomposition fine enough for the two disjoint arcs.

- Line 4340:
  `hD44_N'_manifold`.
  The union of bricks meeting `A1`, intersected with the polygonal disk, is a
  2-manifold with boundary.

- Line 4350:
  `hD44_frontier_broken_line`.
  The component of the frontier of that brick region gives the required
  1-sphere and broken-line subarc.

- Line 4361:
  `hD44_VW_component`.
  The broken-line endpoints are frontier points of one component of
  `I - (A1 union A2)`.

- Line 4371:
  `hD44_QS_component`.
  Cyclic-order transfer from the constructed endpoints `V,W` to the desired
  boundary points `Q,S`.

### Active `dev34` Holes

In `tst/dev34/GeoTop_3_4.thy`:

- Line 19:
  `geotop_connected_nonisolated_finite_linear_graph_boundary_cycle_model_dev34`
  Figure 4.10, first construction step: enumerate the finite polygonal linear
  graph as a cyclic edge chain and realize it as a subdivision of the boundary
  of a 2-simplex.

- Line 4982:
  Boundary-arc fan target for the broken-line link case.
  This is the boundary-vertex analogue of Figure 4.10: realize a finite
  broken-line graph as a subdivided boundary arc of a 2-simplex and cone from
  the adjacent boundary vertex.

- Line 5906:
  `geotop_edge_one_side_simplex_local_semicircle_separates_domain_radius_dev34`
  Moise Lemma 3 local geometry: in the unique incident 2-simplex case, choose a
  small semicircle in the local chart domain that separates.

- Line 9158:
  Remaining proof step inside
  `geotop_three_incident_2simplex_small_circle_domain_not_separates_chart_dev34`.
  Moise Lemma 4 local geometry: with three incident 2-simplexes, a small circle
  around the edge point does not separate the local domain because the third
  simplex gives a passage around the circle.

- Line 9989:
  Remaining side-containment premise inside the chart/Jordan contradiction.
  The 2-cell chart image of the selected small 1-sphere must contain the
  bounded Jordan side and meet the unbounded side, so that Jordan separation
  contradicts the local connectedness result.

## Recent Progress

The last several dozen commits have mostly been real proof/infrastructure
progress, not reshuffling. Recent themes:

- Built a cache chain for faster iteration through `dev34_prefix`,
  `dev34_facts`, `dev34_workfacts`, `dev34_linkfacts`, `dev34_graphfacts`,
  `dev34_graphwork`, `dev34_openstar`, and now `dev34_core`.

- Proved a long sequence of Theorem 3.3 boundary-triangle helpers:
  selected boundary edge shapes, named non-free triangle vertices, remaining
  edge faces in the complex, triangle side distinctness, selected edge count
  bounds, and full-boundary triangle contact.

- Narrowed the Figure 4.10 problem to the exact missing graph construction:
  the later cone/fan/isomorphism machinery is mostly present, but it still
  needs the cyclic boundary subdivision model.

- Factored the chart/Jordan contradiction into smaller pieces:
  open image of 2-cell charts, Jordan side split, and radius-explicit small
  circle existence are proved. The remaining issue is the actual local side
  containment/nonseparation geometry.

- Pulled/fetched colleague `main` repeatedly over HTTPS. As of the last check,
  colleague `main` was already an ancestor of this branch, so there was nothing
  new to merge.

## What “Completion” Still Requires

To mark the goal complete, all of the following must be true:

- `rg -n "\bsorry\b|sledgehammer" tst/dev34_prefix tst/dev34_core tst/dev34`
  returns no proof holes.
- The full Section 3-4 target session builds after removing all sorries.
- The indexes are regenerated and include the current theory split.
- The resulting work is committed.

The next best proof work should probably be one of these:

1. Continue Theorem 3.3 from the book proof:
   finish the boundary-triangle decomposition step at line 3052, since many
   helper lemmas for this path are already in place.

2. Work on Figure 4.10’s cyclic graph model:
   prove that a finite connected degree-two polygonal linear graph can be
   enumerated as a cycle and matched to a boundary subdivision.

3. Work on the local edge-chart geometry:
   expose the small circle/semicircle choices more explicitly so the final
   Jordan side-containment proof has concrete objects rather than opaque
   existential witnesses.

My recommendation is to continue with option 1 or 2. Option 1 advances Section
3 and may close several downstream Section 3 holes. Option 2 advances the core
local manifold model needed by Theorems 4.8-4.10. Both are faithful to the book;
neither is a quick automation cleanup.
