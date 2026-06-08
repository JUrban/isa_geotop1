# GeoTop Sections 3-4 Expert3 Progress Update, 2026-06-08

## Status

The zero-sorry goal is not complete. A fresh local run of
`./check_dev34_fast.sh holes` reports 8 target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106:    sorry
dev34/GeoTop_3_4.thy:495:    sorry
dev34/GeoTop_3_4.thy:7747:    sorry
dev34/GeoTop_3_4.thy:8949:  sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047:    sorry
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9410:      sorry
```

Line numbers have shifted from older reports, but the stable package names are
unchanged:

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

No `sledgehammer` or `try0` markers were found in the checked target layers
`dev34_prefix`, `dev34_prefix_mid`, `dev34_prefix_graph`, `dev34_core`, and
`dev34`.

## Audit Synthesis

The previous expert audits were directionally correct, and expert3 is now the
most current refinement. The project is still approaching the goal in the
structural sense: the remaining work is isolated into eight named packages, and
the checker can warm focused slices instead of paying broad verification cost
after every edit.

It is not approaching completion in the "just a few tactics left" sense. The
remaining holes are package-sized formalizations of Moise picture arguments:
finite graph local cutpoints, Figure 4.10 cycle realization, endpoint-chain fan
realization, one-sided semicircle separation, Section 3 subdisk transfer, Section
3 fold normalization, D42 theta separation, and D44 bricks/regular
neighborhoods.

Expert3 changes the immediate priority slightly. The earlier graph-prefix cycle
split is now closed, so the best next sprint is narrower:

1. Close or sharply isolate
   `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`.
2. Close
   `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`.
3. Reuse the same listing/subdivision machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.

This ordering is preferable because those three packages share finite graph
ordering, cyclic/path listing, and boundary-subdivision bookkeeping. Closing one
complete package is a better progress signal than moving a `sorry` deeper into a
wrapper.

## Current Verification Notes

`./check_dev34_fast.sh focus-status dev34-cycle-realization graph-branch-local
dev34-fan` reports hot caches for the cycle realization and graph-branch local
targets. The `dev34-fan` prefix and slice caches are stale or missing, so it
should be warmed only when work moves to the endpoint fan package.

The full indexes were searched for the eight package names using:

```bash
rg -n "<package names>" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

Both indexes contain the current package names and expert3 advice, so future
work should keep using the indexes before adding new facts.

## Immediate Recommendation

Continue with the finite graph / Figure 4.10 sprint. For each package, follow
`CLAUDE.md`: grep `THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt` first, add any
new proof structure with `sorry` first, compile a focused slice immediately,
replace only small batches with bounded methods, regenerate indexes after theory
or report changes, and commit verified progress frequently.

The status after expert3 is therefore: 8 target holes remain, the direction is
still coherent, but the next meaningful milestone is closing a whole finite
graph/Figure 4.10 package rather than merely reducing a local line count.
