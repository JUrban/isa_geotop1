# GeoTop Sections 3-4 Status

Date: 2026-06-05

Branch: `codex-dev34-cache`

This report summarizes the state of the Sections 3-4 formalization after about
2.5 days of focused work on this goal.

## Executive Status

Sections 3 and 4 are not complete yet. The project is, however, in a much more
controlled state than at the start of this work:

- The Section 3-4 development builds in the dirty cached sessions.
- The active working target has been split into cache layers so iteration is
  now around a minute instead of repeatedly rebuilding the whole stack.
- The current Section 3-4 target stack has 17 executable `sorry`s:
  12 in `dev34_prefix`, 0 in `dev34_core`, and 5 in active `dev34`.
- The remaining holes are named and localized. They are not random cleanup
  failures; most correspond to real book subarguments.

The honest completion estimate is therefore mixed:

- By organization and scaffolding: high. The target surface is well isolated.
- By raw hole count: encouraging. There are only 17 executable holes left in
  the Section 3-4 stack.
- By mathematical difficulty: not close to done. Several of those 17 holes are
  substantial textbook constructions.

I would describe the work as past the exploratory phase and into the hard proof
completion phase. A numerical estimate is necessarily rough, but my best
engineering assessment is:

- Infrastructure/session work: about 80-90% complete for this goal.
- Statement coverage and proof skeleton coverage: about 80-90% complete.
- Sorry-free mathematical completion: about 40-55% complete.

The reason the last number is lower is that the remaining obligations include
Theorem 3.3's disk decomposition, Theorem 3.4/3.7 straightening steps, Figure
4.10's cyclic boundary model, Theorem 4.2/4.4 Jordan separation refinements,
and the local semicircle/circle chart arguments for Theorems 4.8-4.10.

## Current Verification State

Last successful active build command:

```bash
cd /project/tst
/project/bin/isabelle process_theories -d . -d dev34_pre -d dev34_prefix \
  -d dev34_facts -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts \
  -d dev34_graphwork -d dev34_openstar -d dev34_core -d dev34 \
  -l GeoTop34Dev -o quick_and_dirty -f dev34/GeoTop_3_4.thy
```

Last recorded successful timing for the active target:

```text
Finished GeoTop34Dev (0:00:35 elapsed time, 0:01:19 cpu time, factor 2.22)
Finished Draft (0:00:20 elapsed time, 0:00:55 cpu time, factor 2.71)
```

The theorem indexes have been regenerated after the latest theory changes:

```bash
cd /project/tst
bash gen_index.sh
bash gen_stmt_index.sh
```

The current remaining-hole check is:

```bash
rg -n "\bsorry\b|sledgehammer" tst/dev34_prefix tst/dev34_core tst/dev34
```

Current result: 17 `sorry`s and no `sledgehammer` text in the target stack.

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

Most recent proof-organization commit at the time of this report:

- `a9a11b11 Use radius-explicit circle in chart contradiction`

That latest step made the small circle in the final chart contradiction
concrete as `J = sphere p eps`, which should make the remaining Jordan-side
containment proof more tractable.

## Remaining Holes

### Prefix: Section 3

File: `tst/dev34_prefix/GeoTop_3_4_Prefix.thy`

- Line 1994:
  `geotop_two_triangle_boundary_contact_edges_cover_prefix`
  Base case for Theorem 3.3. In a two-triangle disk, the part of one triangle
  on the polygon boundary must be covered by selected whole boundary edge
  faces.

- Line 2011:
  `geotop_two_triangle_not_all_boundary_edges_prefix`
  Base case for Theorem 3.3. One of two disk triangles cannot have all three
  edges on the polygon boundary.

- Line 2179:
  `geotop_polygon_disk_two_boundary_2simplexes_prefix`
  Induction prerequisite for Theorem 3.3. If there are more than two
  2-simplexes, at least two 2-simplexes have boundary edges.

- Line 3052:
  The main induction step inside Theorem 3.3.
  This is the book step where a non-free boundary triangle decomposes the
  polygonal disk into two smaller polygonal disks, induction is applied to both,
  and the resulting free 2-simplexes are transferred back.

- Line 3447:
  `ind_step` inside `Theorem_GT_3_4`.
  This is the reduction step using a free 2-simplex and a plane homeomorphism
  fold to reduce the number of 2-simplexes.

- Line 3906:
  `h_support_in_U` inside `Theorem_GT_3_7`.
  This is the supported version of Theorem 3.4, where the fold must be fixed
  outside the prescribed open set `U`.

### Prefix: Section 4

File: `tst/dev34_prefix/GeoTop_3_4_Prefix.thy`

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

### Active `dev34`

File: `tst/dev34/GeoTop_3_4.thy`

- Line 19:
  `geotop_connected_nonisolated_finite_linear_graph_boundary_cycle_model_dev34`
  Figure 4.10's first construction step: enumerate the finite polygonal linear
  graph as a cyclic edge chain and realize it as a subdivision of the boundary
  of a 2-simplex.

- Line 4982:
  Boundary-arc fan target for the broken-line link case.
  This is the boundary-vertex analogue of Figure 4.10: realize a finite
  broken-line graph as a subdivided boundary arc of a 2-simplex and cone from
  the adjacent boundary vertex.

- Line 5906:
  `geotop_edge_one_side_simplex_local_semicircle_separates_domain_radius_dev34`
  Moise Lemma 3 local geometry. In the unique incident 2-simplex case, choose a
  small semicircle in the local chart domain that separates.

- Line 8911:
  `geotop_three_incident_small_circle_complement_connected_explicit_dev34`
  Moise Lemma 4 local geometry. With three incident 2-simplexes, a small circle
  around the edge point should not separate the local domain because the third
  simplex gives a passage around the circle.

- Line 10016:
  Remaining side-containment premise inside the chart/Jordan contradiction.
  The 2-cell chart image of the selected small 1-sphere must contain the
  bounded Jordan side and meet the unbounded side, so Jordan separation
  contradicts the local connectedness result.

## Work Completed During This Stretch

The work over the last 2.5 days has mainly produced reusable proof
infrastructure and reduced ambiguity:

- Built the `dev34_*` cache chain, including the newer sorry-free `dev34_core`
  layer.
- Repeatedly pulled/fetched colleague `main`; as of the latest checks, colleague
  work had already been merged into this branch.
- Regenerated and used the theorem/statement indexes instead of searching only
  raw session logs.
- Proved and packaged many Theorem 3.3 boundary-triangle helpers: selected edge
  shapes, named triangle-frontier facts, side distinctness, selected-edge
  counts, and full-boundary contact lemmas.
- Narrowed Figure 4.10 to the exact missing cyclic graph realization step.
- Split the Section 4 local chart/Jordan contradiction into smaller lemmas:
  chart image openness, Jordan side split, radius-explicit small circle choice,
  and the remaining local side-containment/nonseparation obligations.
- Removed some tautological or unhelpful wrappers after the real obligations
  became visible.

## Recommended Next Work

The best next target depends on whether we want Section 3 progress or Section 4
progress first.

Recommended Section 3 path:

1. Finish the Theorem 3.3 disk-decomposition hole at prefix line 3052.
2. Use that to close the nearby two-triangle/boundary-simplex helper holes if
   they become easier after the induction step is better structured.
3. Continue to Theorem 3.4 and 3.7 fold/support obligations.

Recommended Section 4 path:

1. Continue the explicit small-circle local geometry at active line 8911.
2. Use the now-concrete `J = sphere p eps` in the chart/Jordan contradiction at
   active line 10016.
3. Then return to Figure 4.10 and the boundary-arc fan model.

My preference is to continue either with Theorem 3.3 line 3052 or with the
small-circle geometry at active line 8911. Both are central, book-faithful
proof obligations. Neither looks like a one-command automation cleanup.

## Completion Criteria

The goal is complete only when:

- `rg -n "\bsorry\b|sledgehammer" tst/dev34_prefix tst/dev34_core tst/dev34`
  returns no holes.
- The active Section 3-4 build succeeds without relying on remaining sorries.
- The theorem and statement indexes are regenerated.
- The resulting state is committed on `codex-dev34-cache`.
