# Brief status report: GeoTop / Moise Sections 3-4 zero-sorry goal

Date: 2026-06-09
Branch: `codex-dev34-cache`
Scope: Sections 3 and 4 target stack under `tst/`.

## Current verified status

The goal is not complete.

A fresh focused hole scan reports 7 target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:13765
dev34/GeoTop_3_4.thy:15354
```

No `sledgehammer`, `try0`, or `oops` markers were found in the checked target
layers.

Stable open packages:

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_decomposition_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34
geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
```

The expert3 audit's 8-hole map is now one step stale: the Figure 4.10 standard
boundary-cycle realization package has been closed since that audit. The older
17/14/10-hole reports are also useful historically, but not current.

## Progress against the expert audits

The previous audits were right about the main risk: the remaining holes are not
routine tactic cleanup. They are package-sized Moise picture arguments.

Meaningful progress since those audits:

- The graph-prefix cycle split is closed.
- The active Figure 4.10 boundary-cycle realization is closed.
- The endpoint fan target has been corrected to a boundary-arc fan, not a full
  boundary cycle.
- The endpoint fan wrapper is checked; the remaining endpoint hole is now a
  named model step that must build the ordered endpoint chain target and cone it
  from the appropriate boundary vertex.

The project is therefore approaching the goal structurally: the holes are few,
stable, and named. It is not yet close in the sense of "a few lines of proof
search left". D44, Section 3 fold/subdisk transfer, Theorem 4.2 separation, the
branch local cutpoint, endpoint fan realization, and the semicircle separator
are all real formalization packages.

## Search and verification workflow

`CLAUDE.md` was reread. Its current guidance remains important:

- use the full indexes frequently (`THEOREMS_AND_DEFS.txt`, `STMT_INDEX.txt`);
- regenerate indexes after theory/report changes with:

```bash
bash gen_index.sh
bash gen_stmt_index.sh
```

The full-index searches were useful in confirming that the endpoint fan has
listing/isomorphism transfer helpers, but still lacks the final source/target
model construction.

Verification speed is currently uneven. `./check_dev34_fast.sh focus-status`
shows hot caches for:

```text
graph-branch-local
dev34-cycle-realization
dev34-fan
```

but stale or missing split caches for many mid/prefix packages, including the
Section 3 and D44 targets. That explains why some iterations feel like several
minutes: if we edit a cold mid/prefix target, the split cache needs to be
rebuilt. For fast progress, work should stay on a hot focused target when
possible, and caches should be deliberately warmed before a long proof sprint.

## Best next target

The best immediate target remains the endpoint fan model:

```text
geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34
```

Reason: the wrapper and transfer infrastructure are already checked in the hot
`dev34-fan` slice. The remaining proof is narrower than D44 or the Section 3
fold package.

The main caveat from the latest inspection is that the endpoint model depends
on source-side endpoint-chain listing facts that may ultimately need the
branch-vertex/no-branch graph package. If the endpoint target stalls on that
dependency, switch to:

```text
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
```

There the exact blocker is the local component bridge: from the connected
punctured simple-closed-curve carrier and three selected incident germs, produce
a component of `ball w r - (e1 union e2 union e3)` whose closure touches all
three germs, then apply the already-staged radial-sector contradiction.

## Bottom line

The project is moving toward the zero-sorry goal, but the remaining work should
be measured by closed packages, not raw `sorry` count. The current count is 7.
The most efficient path is to keep using full-index searches and hot focused
checks, close the endpoint/branch finite-graph packages first, then return to
the colder and larger Section 3/D44 packages with warmed caches.
