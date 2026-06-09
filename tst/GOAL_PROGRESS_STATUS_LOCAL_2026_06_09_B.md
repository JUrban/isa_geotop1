# GeoTop Sections 3-4 Zero-Sorry Goal: Progress Status

Date: 2026-06-09

This is a short local status report for `/project/tst`, written after reading
`CLAUDE.md`, the current checker output, the existing local brief
`GOAL_PROGRESS_BRIEF_LOCAL_2026_06_09.md`, and the expert audit reports through
`PLAN_zero_sorry-expert3.md`.

## Current status

The goal is not complete. The current local target scan reports 6 executable
`sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:13967
```

The same 6 lines are found by both:

```bash
./check_dev34_fast.sh holes
rg -n "sorry|sledgehammer|try0|admit" dev34_prefix dev34_prefix_mid dev34_prefix_graph/cache dev34
```

No current local scan shows the older 8-hole expert3 list exactly. In
particular, the cycle-boundary subdivision and one-sided semicircle packages
that expert3 still listed are not visible target holes in this checkout.

## What has improved

The expert audits describe a sequence of stale counts: 17, 14, 10, and then 8
target holes. The local tree is now below those reports at 6 target holes. That
is real progress, not just a renaming of files.

The most important resolved areas are:

- the graph-prefix cycle split is no longer a visible target hole;
- the active boundary-cycle realization is no longer a visible target hole;
- the one-sided semicircle separator is no longer a visible target hole;
- the endpoint work has moved to the remaining boundary-arc fan model step;
- the remaining graph issue is concentrated in the branch-vertex local
  cutpoint package.

This means the project is approaching the goal in the sense that the open
surface has narrowed substantially. It is not yet close in the sense of being
only minor tactic cleanup.

## Remaining packages

The 6 visible target holes are package-sized proof obligations:

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   - Moise Theorem 4.4 brick / regular-neighborhood / component transfer.
   - This is probably the largest remaining topology package.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   - Section 3 chord-subdisk induction transfer.
   - Needs side-disk triangulations, strict smaller counts, and transfer of
     free-triangle witnesses back to the parent disk.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   - Section 3 supported fold normalization.
   - This is the shared engine behind the later fold/support theorems.

4. `geotop_polygon_arc_opposite_boundary_decomposition_prefix`
   - Moise Theorem 4.2 opposite-boundary arc separation.
   - The missing content is a theta/broken-line contradiction argument.

5. `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   - Branch-vertex local cutpoint contradiction in the graph cache.
   - The expert3 warning is still relevant: do not prove the false general
     claim that degree greater than 2 implies cutpoint for arbitrary finite
     graphs. The simple-closed-curve/local-one-manifold hypothesis is essential.

6. `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
   - Endpoint chain to boundary-arc fan model.
   - This likely depends on source chain enumeration and degree/no-branch
     reasoning, so it is related to the branch-vertex package.

## Current bottleneck

The best near-term target remains the graph/endpoint dependency.

For the branch-vertex theorem, the proof has already staged the downstream
contradiction: no local component can meet all three selected incident edge
germs. The remaining missing bridge is to obtain such a component from the
connected split-side setup. The current local assumptions around that internal
step appear to identify points on two selected germs directly, but the third
germ still needs to be tied explicitly to the same local component or supplied
by a strengthened split-side lemma.

That is a mathematical statement-shape issue, not something likely to be fixed
by broad `auto` or repeated full builds.

## Process adjustments

The user concern about slow verification is valid. Iteration should use the
local cache and indexes aggressively:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh focus-full graph-branch-local geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
rg -n "concept_or_theorem_name" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
rg -n "concept_or_theorem_name" dev34_prefix dev34_prefix_mid dev34_prefix_graph dev34
```

The full generated indexes should be searched frequently, not only local file
neighborhoods. If new session files or target layers have been added since the
index scripts were written, the two index-generation scripts should be checked
before relying on the indexes as complete.

## Bottom line

The work is converging: the visible target count has fallen to 6, and several
expert3 risks are no longer open local holes. The remaining work is still hard
because each `sorry` represents a compacted book argument. The safest next
step is to close the branch-vertex local-component bridge, then use that graph
progress to finish the endpoint boundary-arc fan model.
