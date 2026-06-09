# GeoTop Sections 3-4 zero-sorry progress after expert3 audit

Date: 2026-06-09

## Current status

The goal is not complete yet, but it is measurably closer than the older expert reports indicate.
The live target scan now shows 7 target `sorry`s and no `sledgehammer`/`try0`/`oops`
markers in the checked target layers:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:13967
dev34/GeoTop_3_4.thy:15556
```

The important change from the earlier 8-hole audit is that the active cycle-realization
package has been closed. Recent work also split the endpoint fan package into smaller
source-chain and target-model wrappers. The remaining endpoint hole is narrower than the
original endpoint fan obligation, but still needs the boundary-arc fan construction.

Recent relevant commits:

```text
779661a4 Split endpoint fan model target package
532631fa Package endpoint source chain split
1cdb0166 Add endpoint chain source listing helpers
3c8ca7d9 Add current zero-sorry progress report
c94d35e4 Name endpoint fan model book step
474c0ad4 Refine endpoint fan model obligation
5181623e Add endpoint fan target model wrapper
8602149b Add live progress report after expert3 audit
```

## Remaining packages

The 7 holes are not routine tactic cleanup. They are still package-sized pieces of Moise
Sections 3 and 4:

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   - Moise Theorem 4.4 brick / regular-neighborhood / component-frontier transfer.
   - This is probably the largest remaining package.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   - Section 3 chord subdisk induction transfer.
   - Needs side disk triangulations, strict smaller counts, and transfer of free-triangle
     witnesses back to the parent disk.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   - Section 3 fold normalization with support control.
   - This is the engine behind Theorems 3.4 and 3.7.

4. `geotop_polygon_arc_opposite_boundary_decomposition_prefix`
   - Theorem 4.2 theta / opposite-boundary arc separation.
   - Needs a broken-line or theta contradiction package, not only component algebra.

5. `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   - Graph-cache branch vertex local cutpoint contradiction.
   - Expert3's warning is important: do not prove a false general "degree > 2 implies
     cutpoint" graph lemma. The simple-closed-curve/local-one-manifold hypothesis is
     essential.

6. `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
   - Endpoint chain to boundary-arc fan model.
   - Source chain helpers are now packaged; the remaining work is the same-length target
     boundary-arc subdivision plus cone/fan verification.

7. `geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34`
   - One-sided local semicircle crosscut separation.
   - The current collar statement is plausibly the right shape: prove `A = sphere p r ∩ σ`
     lies in `U`, then use a radius-crossing argument in the local collar.

## Assessment against the expert audits

The expert reports were directionally right: the project is well localized but not in the
"just replace a few tactics" phase. Since those audits, the graph cycle realization and
several endpoint-source helpers have been closed, so the best current description is:

```text
small hole count, large remaining mathematical content
```

The work is still approaching the goal, but the remaining time should be estimated by
closed proof packages, not by raw `sorry` count. The next meaningful milestones are:

1. Close one narrow active package, preferably the endpoint target-model wrapper or a
   small semicircle helper.
2. Keep the branch-vertex package honest by strengthening the upstream local-component
   bridge rather than forcing the currently underpowered component claim.
3. Save Theorem 4.4 bricks for a separate focused sprint; it is the highest-risk package.

## Process notes

The current fast workflow is the right one:

- Use `./check_dev34_fast.sh holes` for the live target hole inventory.
- Use full-index/source search frequently before stating helpers:
  `./check_dev34_fast.sh index PAT` or direct `rg` over `THEOREMS_AND_DEFS.txt`
  and `STMT_INDEX.txt`.
- Regenerate indexes after theory changes:
  `bash gen_index.sh` and `bash gen_stmt_index.sh`.
- The index scripts now have cache/signature logic over session files and generated
  session files; if session layout changes unexpectedly, run both with `--force` and
  inspect `INDEX_THEORIES.txt`.

The colleague branch should not be relied on for planning right now; local progress and
the expert audits are enough to continue.
