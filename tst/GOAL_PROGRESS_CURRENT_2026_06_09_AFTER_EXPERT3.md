# Current GeoTop Sections 3-4 Progress Report After Expert3

Date: 2026-06-09
Branch: `codex-dev34-cache`
Scope: zero-target-`sorry` goal for Moise/GeoTop Sections 3 and 4.

## Status

The goal is not complete, but the local checkout is ahead of the older audit
counts. A fresh live scan with `./check_dev34_fast.sh holes` reports six target
`sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:9933
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9613
dev34/GeoTop_3_4.thy:14872
```

The previous expert reports remain useful for strategy, but their raw counts
are stale. The active cycle-realization and semicircle holes mentioned in some
older reports are not live in this scan. The remaining work is still
package-sized mathematical content, not routine tactic cleanup.

## Remaining Packages

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   - File: `dev34_prefix/GeoTop_3_4_Prefix.thy`
   - Live hole: `hD44_book_steps`.
   - Content: Moise Theorem 4.4 brick decomposition, regular neighborhood,
     frontier broken-line, component-frontier, and cyclic-order transfer.
   - Risk: highest remaining package.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   - File: `dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy`
   - Live hole: `hsubdisk_induction_transfer_book`.
   - Content: Figure 3.2 side-disk triangulations, strict smaller counts, and
     transfer of selected free-triangle witnesses back to the parent disk.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   - File: `dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy`
   - Live hole: `hfold_induction_book`.
   - Content: Moise Theorem 3.4/3.7 fold normalization with support control.
     This is the intended shared engine for the unrestricted and supported
     fold theorems.

4. `geotop_polygon_arc_opposite_boundary_theta_component_split_prefix`
   - File: `dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy`
   - Live hole: `hD42_theta_component_book_step`.
   - Content: D42/Theorem 4.2 theta separation. The elementary open-cut fact is
     now proved; the remaining step is to get the two side components or derive
     the forbidden theta graph from a same-component assumption.

5. `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   - File: `dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy`
   - Live hole: `hsplit_side_endpoint_local_branch_book_step`.
   - Content: graph-cache local branch contradiction. The proof must use the
     simple-closed-curve/local-one-manifold hypotheses; the expert warning is
     correct that a general "degree greater than two implies cutpoint" graph
     lemma would be false.

6. `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
   - File: `dev34/GeoTop_3_4.thy`
   - Live hole: the non-finish branch in the endpoint fan model.
   - Content: enumerate the endpoint chain from the broken-line arc order,
     realize it as a same-length boundary-arc subdivision, and cone it from the
     appropriate target boundary vertex. The older full-boundary-cycle shortcut
     is not the right target.

## Are We Approaching The Goal?

Yes, structurally: the target stack is down to six stable, named packages, and
recent work has already closed the cycle-realization path and narrowed D42 and
endpoint fan obligations. No current evidence suggests broad uncontrolled
sprawl.

No, in the sense of elapsed proof effort: the remaining six holes are theorem
packages. The right progress metric is "closed package", not raw `sorry` count
or line count. D44 and the Section 3 fold/subdisk packages may each require a
focused proof sprint.

## Workflow Notes

`CLAUDE.md` was reread. The relevant process constraints are:

- New proof structure should be introduced with `sorry` first, then compiled,
  then replaced in small batches.
- Search the full indexes before adding helpers:
  `THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt`.
- Regenerate indexes after theory/report/cache-relevant changes:

```bash
bash gen_index.sh
bash gen_stmt_index.sh
```

The speed issue is real. Current `./check_dev34_fast.sh focus-status` shows
fresh parent graph/base caches, but most split caches for mid/prefix/dev34
targets are stale or missing. To avoid multi-minute surprise checks, prime the
target cache before a sprint and stay on one focused target while it is hot.

## Recommended Next Work

Best immediate target: the endpoint non-finish fan model, because it is active,
localized, and the wrapper already handles the two-vertex finish case.

Fallback if endpoint stalls on no-branch/source-listing facts: switch to the
graph-cache branch package and close the local branch contradiction using the
simple-closed-curve/local-one-manifold assumptions.

Leave D44 for a dedicated sprint after the smaller graph/endpoint packages are
closed or further isolated.
