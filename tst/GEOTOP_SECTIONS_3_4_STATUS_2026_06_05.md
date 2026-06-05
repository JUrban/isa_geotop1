# GeoTop Sections 3-4 Status

Date: 2026-06-05

Branch: `codex-dev34-cache`

This report summarizes the state of the Sections 3-4 formalization after about
2.5 days of focused work on this goal.

## Executive Status

Sections 3 and 4 are not complete yet. The project is now in a controlled
proof-completion phase rather than an exploratory phase:

- The focused Section 3-4 target builds in the cached dirty sessions.
- The work is split into cache layers, so normal iteration is about one minute
  instead of repeatedly rebuilding the full GeoTop stack.
- The current target stack has 17 executable `sorry`s:
  12 in `dev34_prefix`, 0 in `dev34_core`, and 5 in active `dev34`.
- The remaining holes are localized and named. Most are real textbook
  subarguments, not incidental automation cleanup.

My current completion estimate is:

- Infrastructure and session layout: 85-90% complete.
- Statement coverage and book-faithful proof skeletons: 80-90% complete.
- Sorry-free mathematical completion: 40-55% complete.
- Overall goal completion, weighted by remaining difficulty: roughly 50%.

The raw hole count looks small, but the remaining 17 holes are not uniform.
Several are large Moise arguments: Theorem 3.3's disk-decomposition/free
triangle argument, Theorem 3.4/3.7 fold support, Theorem 4.2/4.4 arc and brick
decompositions, Figure 4.10's cyclic graph realization, and the local
semicircle/circle chart arguments for Theorems 4.8-4.10.

## Current Verification State

Last successful prefix build:

```bash
cd /project/tst
/project/bin/isabelle process_theories -d . -d dev34_pre -d dev34_prefix \
  -l GeoTop34PrefixDirty -o quick_and_dirty \
  -f dev34_prefix/GeoTop_3_4_Prefix.thy
```

Recorded timing:

```text
Finished GeoTop34PrefixDirty (0:00:21 elapsed time, 0:00:34 cpu time, factor 1.62)
Finished Draft (0:00:07 elapsed time, 0:00:21 cpu time, factor 2.74)
```

Last successful active build:

```bash
cd /project/tst
/project/bin/isabelle process_theories -d . -d dev34_pre -d dev34_prefix \
  -d dev34_facts -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
  -d dev34_graphwork -d dev34_openstar -d dev34_core -d dev34 \
  -l GeoTop34Dev -o quick_and_dirty -f dev34/GeoTop_3_4.thy
```

Recorded timing:

```text
Finished GeoTop34Dev (0:00:36 elapsed time, 0:01:27 cpu time, factor 2.37)
Finished Draft (0:00:18 elapsed time, 0:00:48 cpu time, factor 2.70)
```

The indexes were regenerated after the latest theory changes:

```bash
cd /project/tst
bash gen_index.sh
bash gen_stmt_index.sh
```

Current remaining-hole command:

```bash
rg -n "\bsorry\b|sledgehammer" tst/dev34_prefix tst/dev34_core tst/dev34
```

Current result: 17 `sorry`s and no `sledgehammer` text in the target stack.

Latest relevant commit at the time of this report:

- `ca2b93fe Expose two-triangle carrier inclusion facts`

## Session Layout

The active development is split as follows:

- `dev34_prefix`: Section 3 and early Section 4 material, cached dirty.
- `dev34_facts`, `dev34_workfacts`, `dev34_linkfacts`, `dev34_graphfacts`,
  `dev34_graphwork`, `dev34_openstar`: support cache layers.
- `dev34_core`: sorry-free completed prefix of the former active
  `GeoTop_3_4.thy`.
- `dev34`: current active Section 4 manifold/local-model layer.

Important cache commit:

- `76e104d3 Cache completed GeoTop 3-4 core prefix`

The branch includes the colleague's current `main` as of the latest fetch
check. The local branch is ahead of `origin/codex-dev34-cache`; pushing this
branch will publish both our work and any merged colleague history already in
the branch.

## Remaining Holes

### Prefix: Section 3

File: `tst/dev34_prefix/GeoTop_3_4_Prefix.thy`

- Line 1994:
  `geotop_two_triangle_boundary_contact_edges_cover_prefix`.
  In the two-triangle disk base case, the part of one triangle on the polygon
  boundary must be covered by selected whole boundary edge faces.

- Line 2062:
  `geotop_two_triangle_all_boundary_edges_force_other_subset_prefix`.
  This is the current hard topological step in the two-triangle base case. If
  all three edge faces of one triangle lie on the polygon boundary, the closed
  polygonal disk should be forced to be that triangle, so the other 2-simplex
  would be contained in it.

- Line 2258:
  `geotop_polygon_disk_two_boundary_2simplexes_prefix`.
  Induction prerequisite for Theorem 3.3. If there are more than two
  2-simplexes, at least two 2-simplexes have boundary edges.

- Line 3131:
  Main induction step inside Theorem 3.3.
  This is the book step where a non-free boundary triangle decomposes the
  polygonal disk into two smaller polygonal disks, induction is applied to both,
  and the resulting free 2-simplexes are transferred back.

- Line 3526:
  `ind_step` inside `Theorem_GT_3_4`.
  This is the reduction step using a free 2-simplex and a plane homeomorphism
  fold to reduce the number of 2-simplexes.

- Line 3985:
  `h_support_in_U` inside `Theorem_GT_3_7`.
  This is the supported version of Theorem 3.4, where the fold must be fixed
  outside the prescribed open set `U`.

### Prefix: Section 4

File: `tst/dev34_prefix/GeoTop_3_4_Prefix.thy`

- Line 4316:
  `hD42_disjoint` inside `Theorem_GT_4_2`.
  Main arc-separation argument: the `Q`-side and `S`-side components of
  `I - A` are distinct and cover the complement.

- Line 4411:
  `hD44_bricks` inside `Theorem_GT_4_4`.
  Brick decomposition fine enough for the two disjoint arcs.

- Line 4419:
  `hD44_N'_manifold`.
  The union of bricks meeting `A1`, intersected with the polygonal disk, is a
  2-manifold with boundary.

- Line 4429:
  `hD44_frontier_broken_line`.
  The component of the frontier of that brick region gives the required
  1-sphere and broken-line subarc.

- Line 4440:
  `hD44_VW_component`.
  The broken-line endpoints are frontier points of one component of
  `I - (A1 union A2)`.

- Line 4450:
  `hD44_QS_component`.
  Cyclic-order transfer from the constructed endpoints `V,W` to the desired
  boundary points `Q,S`.

### Active `dev34`

File: `tst/dev34/GeoTop_3_4.thy`

- Line 19:
  `geotop_connected_nonisolated_finite_linear_graph_boundary_cycle_model_dev34`.
  Figure 4.10's first construction step: enumerate the finite polygonal linear
  graph as a cyclic edge chain and realize it as a subdivision of the boundary
  of a 2-simplex.

- Line 4982:
  Boundary-arc fan target for the broken-line link case.
  This is the boundary-vertex analogue of Figure 4.10: realize a finite
  broken-line graph as a subdivided boundary arc of a 2-simplex and cone from
  the adjacent boundary vertex.

- Line 5906:
  `geotop_edge_one_side_simplex_local_semicircle_separates_domain_radius_dev34`.
  Moise Lemma 3 local geometry. In the unique incident 2-simplex case, choose a
  small semicircle in the local chart domain that separates.

- Line 8911:
  `geotop_three_incident_small_circle_complement_connected_explicit_dev34`.
  Moise Lemma 4 local geometry. With three incident 2-simplexes, a small circle
  around the edge point should not separate the local domain because the third
  simplex gives a passage around the circle.

- Line 10016:
  Remaining side-containment premise inside the chart/Jordan contradiction.
  The 2-cell chart image of the selected small 1-sphere must contain the
  bounded Jordan side and meet the unbounded side, so Jordan separation
  contradicts the local connectedness result.

## Work Completed During This Stretch

The last 2.5 days produced both build infrastructure and proof localization:

- Built the `dev34_*` cache chain, including the sorry-free `dev34_core` layer.
- Repeatedly pulled/fetched colleague `main`; as of the latest checks,
  colleague work had already been merged into this branch.
- Regenerated and used theorem/statement indexes instead of relying on raw log
  searches.
- Proved and packaged many Theorem 3.3 boundary-triangle helpers: selected edge
  shapes, named triangle-frontier facts, side distinctness, selected-edge
  counts, full-boundary contact lemmas, and the easy same-dimension containment
  contradiction for two 2-simplexes.
- Split the two-triangle base case further so the current difficult step is
  isolated as a clean carrier-inclusion/topological-disk obligation.
- Narrowed Figure 4.10 to the exact missing cyclic graph realization step.
- Split the Section 4 local chart/Jordan contradiction into smaller lemmas:
  chart image openness, Jordan side split, radius-explicit small circle choice,
  and the remaining local side-containment/nonseparation obligations.
- Removed tautological wrappers after the real obligations became visible.

## Current Best Next Step

The most book-faithful Section 3 continuation is to finish line 2062:

```text
all three boundary edges of sigma
=> the polygonal disk is forced to be sigma
=> tau subset sigma
=> contradiction with the same-dimension proper-subset lemma
```

That would close the currently exposed contradiction path for the two-triangle
base case and likely simplify the nearby line 1994/2258 obligations.

The most useful Section 4 continuation is line 8911, the explicit
three-incident small-circle nonseparation lemma. The recent radius-explicit
commits made the circle concrete as `sphere p eps`, which should make the
remaining Jordan-side contradiction at line 10016 more tractable.

My preference is to continue with the Section 3 two-triangle carrier-inclusion
step first, because it is the nearest open proof chain and directly supports
Theorem 3.3.

## Completion Criteria

The goal is complete only when:

- `rg -n "\bsorry\b|sledgehammer" tst/dev34_prefix tst/dev34_core tst/dev34`
  returns no holes.
- The active Section 3-4 build succeeds without relying on remaining sorries.
- The theorem and statement indexes are regenerated.
- The resulting state is committed on `codex-dev34-cache`.
