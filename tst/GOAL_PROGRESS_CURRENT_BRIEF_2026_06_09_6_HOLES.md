# GeoTop Sections 3-4 Current Progress Brief, 2026-06-09

Snapshot: local branch `codex-dev34-cache` at `d2081aa4`, checked
2026-06-09T12:40:10Z.

## Status

The zero-`sorry` goal is not complete. The current focused hole scan reports
6 target holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:9915
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:14872
```

This is real progress from the expert-audit sequence. The older reports counted
17, then 14, then 10, then 8 holes, but those counts are now stale. The current
raw count is smaller because several graph/cycle/local packages have been
closed or moved into sharper named packages.

The remaining holes are still package-sized Moise arguments, not ordinary
tactic cleanup.

## What Changed Since The Expert3 Audit

The graph-prefix cycle split is no longer a visible target hole. The previous
cycle-realization and one-sided semicircle packages also no longer appear in
the focused hole scan.

Recent local progress added and checked reusable D42 infrastructure:

- `geotop_polygon_interior_minus_arc_open_prefix`
- `geotop_polygon_interior_minus_arc_component_open_prefix`
- `geotop_polygon_arc_opposite_boundary_theta_component_split_prefix`

The old anonymous D42 gap in the opposite-boundary decomposition is now a named
theta/component-split package. That does not solve D42, but it is the right
shape: the remaining proof should use the book's theta-graph contradiction,
not ad hoc component algebra.

The endpoint package has also been narrowed. The current hole is
`geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`, with
the finish-endpoint case already handled and the non-finish branch still open.

## Current Stable Packages

The current named open packages are:

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_theta_component_split_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34
```

They are also present in the generated indexes, so future work should search by
name in `THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt` instead of relying on line
numbers.

## Expert Audit Synthesis

The expert reports remain useful, but their raw hole maps are outdated. Their
main strategic warnings still apply:

1. Do not treat each remaining `sorry` as a local proof-search target.
2. Keep D44 as a named regular-neighborhood/brick transfer package.
3. Keep Section 3 fold normalization support-parametric; do not prove a weaker
   unsupported variant first.
4. For the branch-vertex graph cache, do not prove the false general claim that
   degree greater than two implies a cutpoint. The simple-closed-curve /
   local-one-manifold hypothesis is essential.
5. For D42, the missing bridge is a theta contradiction: same component in
   `polygon_interior J - A` should yield a forbidden broken-line/theta graph.
6. For endpoint fan, reduce arbitrary finite vertex-set clauses to endpoint
   chain singleton/adjacent-edge cases before trying to verify the fan target.

## Verification And Speed

The faster workflow is now essential. Use:

```bash
./check_dev34_fast.sh holes
rg -n "<name-or-concept>" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
rg -n "<name-or-concept>" dev34_prefix dev34_prefix_mid dev34_prefix_graph dev34
```

For focused checks, prefer the relevant slice rather than broad builds, for
example:

```bash
./check_dev34_fast.sh slice-hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy geotop_polygon_arc_opposite_boundary_theta_component_split_prefix
./check_dev34_fast.sh focus-full graph-branch-local geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
./check_dev34_fast.sh focus-full dev34-fan geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34
```

After theorem/cache edits, regenerate the indexes:

```bash
bash gen_index.sh
bash gen_stmt_index.sh
```

## Bottom Line

The project is still approaching the goal: the open work is now isolated to
6 stable packages, and recent commits reduced the target set while improving
reuse. It is not close in the sense of "a few tactics left." The remaining
work should be measured by closed named packages, with D42/endpoint/graph-cache
as plausible next packages and D44 likely the largest remaining topology block.
