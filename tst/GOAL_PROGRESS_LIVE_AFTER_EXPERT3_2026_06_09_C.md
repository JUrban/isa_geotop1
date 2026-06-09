# Live GeoTop Sections 3-4 Progress Report After Expert3, 2026-06-09

This is a brief local status report written after rereading `CLAUDE.md`,
`PLAN_zero_sorry-expert.md` through `PLAN_zero_sorry-expert3.md`, the generated
indexes, and the live target files. The inactive colleague state is ignored; the
source of truth here is the local workspace on branch `codex-dev34-cache`.

## Current live status

The goal is not complete. A fresh local run of:

```bash
./check_dev34_fast.sh holes
```

reports seven raw target `sorry` lines:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:9933
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:3921
dev34/GeoTop_3_4.thy:14839
dev34/GeoTop_3_4.thy:14872
```

This is ahead of the expert3 audit's eight-hole map. The old Figure 4.10
cycle-subdivision package and the one-sided semicircle/collar package no longer
appear in the live hole scan. The remaining active `dev34` holes are now the
endpoint source-degree bound and the boundary-edge cone target-data step.

## Remaining proof packages

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   - Moise Theorem 4.4 brick / regular-neighborhood / component-frontier
     transfer.
   - This remains the largest visible topology package.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   - Section 3 chord-subdisk induction transfer.
   - Needs side complexes as smaller polygonal-disk triangulations and transfer
     of free-triangle witnesses back to the parent disk.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   - Section 3 support-parametric fold normalization.
   - This is still the common engine behind Theorems 3.4 and 3.7.

4. `geotop_polygon_arc_opposite_boundary_theta_component_split_prefix`
   - Moise Theorem 4.2 theta / opposite-boundary arc separation.
   - The expert advice is still accurate: close this with the broken-line /
     theta contradiction, not broad component rewriting.

5. `geotop_connected_split_side_three_germs_local_component_prefix` inside
   `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   - Graph-cache branch-vertex local cutpoint package.
   - The inner bridge is still under-specified as a standalone lemma: the proof
     has two selected germs directly in the connected set and the third only via
     closure data. The next useful edit is to rethread the upstream split-side
     information or strengthen the bridge with the exact third-germ relation.

6. `geotop_endpoint_nonfinish_degree_bound_book_step_dev34`
   - Source-side finite linear arc no-branch / degree bound.
   - Needed before the endpoint chain listing can be used as a source model.

7. `geotop_endpoint_chain_boundary_edge_cone_target_data_book_step_dev34`
   - Target-side same-length boundary-edge subdivision plus cone fan data.
   - This is the correct path analogue of the boundary-cycle construction and
     must not be replaced by a full boundary-cycle shortcut.

## Audit reconciliation

The expert3 report remains useful for strategy, but several named targets have
moved. In particular, `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`
is indexed but no longer open in `./check_dev34_fast.sh holes`, and the
semicircle target is also out of the live scan. The endpoint work has been split
more sharply than expert3 described: one hole is source-side degree control, the
other is target-side boundary-edge cone data.

The project is approaching the goal structurally: the remaining work is named,
localized, and searchable. It is not in final tactic-cleanup mode. D44, Section
3 fold normalization, D42, and the graph local-component bridge are still
mathematical book packages compressed into one `sorry` each.

## Index and iteration notes

The user's reminder about full-index grep is important. Use both generated
indexes and source search before adding helpers:

```bash
rg -n "pattern" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
rg -n "pattern" dev34 dev34_prefix dev34_prefix_mid dev34_prefix_graph
```

The index scripts do not currently need changes for `PLAN_zero_sorry-expert3.md`
or this report. `index_theory_lib.py` already includes
`PLAN_zero_sorry-expert*.md`, `*PROGRESS*.md`, `*REPORT*.md`, `*STATUS*.md`,
`CLAUDE*.md`, session files, generated session files, and bounded session logs.

For speed, stay on one package and use focused checks:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh focus-status
./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy TARGET_NAME
```

The best next proof target is the endpoint boundary-edge target-data step if the
goal is visible active-file progress, or the graph local-component bridge if the
goal is to unlock more no-branch source facts. D44 should remain a later target
unless it blocks a dependency.
