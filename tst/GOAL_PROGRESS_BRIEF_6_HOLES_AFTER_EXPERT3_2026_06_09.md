# GeoTop Sections 3-4 progress brief after expert audits

Date: 2026-06-09
Branch: `codex-dev34-cache`
Scope: local target stack under `tst/`

## Current status

The zero-target-`sorry` goal is not complete.

A fresh local scan with:

```bash
./check_dev34_fast.sh holes
```

currently reports 6 target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:9933
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9621
dev34/GeoTop_3_4.thy:14872
```

This is real progress from the expert-audit sequence.  The older audits mention
17, 14, 10, and then 8 target holes.  Those counts are stale locally, but the
experts' main diagnosis remains correct: the remaining holes are package-sized
Moise picture arguments, not final tactic cleanup.

## Remaining packages

The stable remaining packages are:

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   - Moise Theorem 4.4 brick / regular-neighborhood / component-frontier transfer.
   - This is still the largest visible topology package.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   - Section 3 chord-subdisk induction transfer.
   - Needs side complexes proved as smaller polygonal-disk triangulations and
     transfer of free-triangle witnesses back to the parent disk.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   - Section 3 support-parametric fold normalization.
   - This remains the common engine behind Theorems 3.4 and 3.7.

4. `geotop_polygon_arc_opposite_boundary_decomposition_prefix`
   - Moise Theorem 4.2 opposite-boundary arc separation.
   - The missing core is the theta / broken-line contradiction package.

5. `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   - Graph-cache branch-vertex local cutpoint package.
   - The current inner gap has been narrowed to the exact local-component bridge:
     from the simple-closed-curve split-side setup, produce a component of
     `ball w r - (e1 union e2 union e3)` whose closure meets all three selected
     incident edge germs.
   - The expert3 warning is essential here: do not replace this with the false
     general graph claim that degree greater than two implies a cutpoint.  The
     simple-closed-curve / local-one-manifold hypothesis is required.

6. `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
   - Active endpoint-chain boundary-arc fan model.
   - The finish case is handled by the two-vertex model.  The remaining
     non-finish branch still needs the endpoint chain enumeration and matching
     boundary-arc fan realization.

## Progress since expert3

Several expert3 items are now closed locally:

- the graph-prefix cycle split is closed;
- the Figure 4.10 standard boundary-cycle realization is closed;
- the one-sided semicircle/collar package no longer appears in the current
  target hole scan;
- the endpoint fan target has been corrected to a boundary-arc fan rather than
  a full boundary-cycle target.

The latest graph-cache edit also improves the proof structure without reducing
the hole count: it replaces a misleading `False` placeholder in the branch
local-disconnect proof by the precise component-existence statement needed by
the already-staged radial-sector contradiction.

## Process status

`CLAUDE.md` was reread.  The important working rules remain:

- search the full indexes frequently before adding or moving lemmas:
  `THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt`;
- use focused checker modes instead of broad rebuilds for normal iteration;
- keep new proof structure `sorry`-first, then replace small verified batches;
- regenerate indexes after theory/report/cache edits:

```bash
bash gen_index.sh
bash gen_stmt_index.sh
```

The current efficient targets are the hot graph-cache branch package and the
active endpoint-fan slice.  D44 and the Section 3/D42 packages should be treated
as larger named theorem packages, not as local proof-search cleanups.

## Bottom line

We are approaching the goal in the structural sense: the target count is down to
6 and the open items are stable, named packages.  We are not yet in final cleanup:
the remaining work still includes D44, Section 3 subdisk/fold transfer, D42
theta separation, the graph local-component bridge, and the endpoint fan model.
