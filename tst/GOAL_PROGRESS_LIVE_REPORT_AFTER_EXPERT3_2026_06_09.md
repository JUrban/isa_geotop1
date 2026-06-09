# Live progress report after expert3 audit

Date: 2026-06-09
Branch: `codex-dev34-cache`
Scope: GeoTop / Moise Sections 3 and 4 zero-target-sorry goal.

## Current verified status

The goal is not complete. A fresh target scan reports 7 target `sorry`s and no
`sledgehammer`, `try0`, or `oops` markers in the checked target layers.

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:13738
dev34/GeoTop_3_4.thy:14956
```

Stable open package names:

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_decomposition_prefix
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
```

The expert3 audit's 8-hole diagnosis is now slightly stale. Since that audit,
the active Figure 4.10 / standard boundary-cycle realization package has been
closed, and the endpoint-chain package has gained new checked helper lemmas.

## Progress since the audits

The graph-prefix cycle split is closed. The earlier hard orbit/cut-path facts
about non-adjacent reversed edges and carrier intersection no longer appear as
target holes.

The active boundary-cycle realization is closed and indexed:

```text
geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34
```

Recent endpoint-chain infrastructure is also now checked and indexed:

```text
geotop_endpoint_chain_listing_isomorphism_from_matching_dev34
geotop_endpoint_chain_fan_target_transfer_from_isomorphism_dev34
geotop_endpoint_chain_fan_target_from_matching_model_dev34
```

These helpers do not close the endpoint fan target yet, but they reduce the
remaining proof to constructing the correct target-side boundary-arc fan model
and applying the matching/isomorphism transfer.

## What the expert audits got right

The main expert conclusion remains correct: the remaining count is small, but
the holes are package-sized Moise picture arguments, not routine proof-search
cleanup.

The remaining work falls into these clusters:

- Theorem 4.4 brick / regular-neighborhood component transfer.
- Section 3 chord subdisk induction and free-triangle transfer.
- Section 3 support-controlled free-triangle fold normalization.
- Theorem 4.2 opposite-boundary arc decomposition via theta/separation.
- Graph-cache branch-vertex local cutpoint.
- Endpoint-chain boundary-arc fan realization.
- One-sided simplex semicircle/crosscut separation.

So we are approaching the goal structurally: the target list is short, named,
and much better isolated than it was in the older 17/14/10-hole reports. But we
are not yet close in the sense of "a few tactics left". The D44 and Section 3
fold packages are still large formalization tasks.

## Search and index status

`CLAUDE.md` was reread. Its current guidance is still to search both indexes
before adding lemmas and regenerate them after theorem/cache changes:

```bash
cd /project/tst && bash gen_index.sh
cd /project/tst && bash gen_stmt_index.sh
```

The index scripts already route through `index_theory_lib.py`, which includes:

```text
PLAN_zero_sorry-expert*.md
```

as advice inputs, and also tracks ROOT/session files plus bounded session logs
in the cache signature. The current expert3 report is therefore covered by the
existing advice-file pattern.

## Speed and verification status

The focused checker remains the right iteration tool:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh focus dev34-fan
./check_dev34_fast.sh focus-status
```

Recent endpoint helper work was checked through the focused `dev34-fan` slice
and committed. Broad rebuilds should be reserved for larger checkpoints or final
verification, because they are too slow for ordinary proof iteration.

I did not run a full Isabelle build for this report. The live facts above are
based on the focused hole scan, marker scan, git history, and index searches.

## Recommended next target

The best immediate target is still:

```text
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
```

Reason: the needed source-side listing and transfer helpers are now in place,
and the remaining work is narrower than D44 or the Section 3 fold package. The
next useful helper is a target-side construction for an ordered endpoint chain
realized as a subdivision of one boundary arc of a standard 2-simplex, coned
from the adjacent/opposite boundary vertex.

If that target stalls on geometry, the next fallback should be the graph-cache
branch-vertex local cutpoint, but only by isolating the local component bridge
described in expert3. D44 and the Section 3 fold/subdisk packages should be
treated as deliberate package work, not opportunistic tactic cleanup.
