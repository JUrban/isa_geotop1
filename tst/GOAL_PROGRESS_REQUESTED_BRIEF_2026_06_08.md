# GeoTop Sections 3-4 Requested Progress Brief, 2026-06-08

## Current status

The zero-sorry goal is not complete. A fresh local run of
`./check_dev34_fast.sh holes` reports 8 target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106:    sorry
dev34/GeoTop_3_4.thy:749:    sorry
dev34/GeoTop_3_4.thy:8001:    sorry
dev34/GeoTop_3_4.thy:9203:  sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047:    sorry
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9410:      sorry
```

No `sledgehammer` or `try0` markers were found in the checked target layers
`dev34`, `dev34_prefix`, `dev34_prefix_mid`, `dev34_prefix_graph`, and
`dev34_core`.

## Stable open packages

Line numbers keep moving, so the useful status is the stable package list:

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_decomposition_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
```

## Progress assessment

The project is still approaching the goal in the structural sense: the target
stack is down from older audit snapshots of 17/14/10 holes to 8 verified target
holes, the graph-prefix cycle split is no longer open, and the remaining work is
concentrated in named packages with focused checker targets.

It is not approaching completion in the sense of "a few tactics remain." The
expert audits agree that the remaining holes are package-sized Moise picture
arguments: Section 3 subdisk transfer and fold normalization, D42 theta/arc
separation, D44 brick/regular-neighborhood transfer, finite graph branch
cutpoints, Figure 4.10 boundary-cycle realization, endpoint-chain fan
realization, and one-sided semicircle separation.

Expert3 is the most current audit and is consistent with the local scan. Its
main correction is that the old graph-prefix cycle split is now closed, so the
finite graph sprint should focus on the graph-cache branch local cutpoint, the
active Figure 4.10 boundary-subdivision model, and then the endpoint-chain fan.

## Verification and iteration speed

The fastest current targets are:

```text
dev34-cycle-realization: fresh core, fresh prefix cache, fresh slice cache
graph-branch-local: fresh prefix-base, fresh prefix cache, fresh slice cache
```

The following targets currently have stale or missing split caches and should be
warmed only when actively working on them:

```text
dev34-fan
dev34-semicircle
mid-d42
mid-fold
mid-split-free
prefix-d44
```

This means broad verification after every edit is still too expensive. The
practical loop should be: search the indexes, edit one package, run the focused
target, regenerate indexes after theory/report changes, and commit verified
progress.

## Index status

`CLAUDE.md` correctly emphasizes frequent full-index search via
`THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt`. The current index scripts already
track local advice/report notes and bounded session transcript inputs through
`index_theory_lib.py`, so I do not see an immediate script edit required just
because of the new expert/session files. The important operational rule is to
regenerate both indexes after adding reports or changing theory/cache files.

The current indexes already contain all eight stable package names and the
expert3 advice, so they should be used before adding any new helper lemma.

## Recommended next milestone

Use the hot focused caches to close one complete finite-graph/Figure 4.10
package rather than moving a `sorry` deeper:

1. finish or sharply isolate
   `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`;
2. close
   `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`;
3. reuse the listing/subdivision work for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.

The bottom line is that the direction is coherent and measurable, but the goal
is not yet near final close-out. Progress should be judged by closed packages,
not by raw line count.
