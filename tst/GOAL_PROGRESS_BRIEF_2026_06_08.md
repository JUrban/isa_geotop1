# GeoTop Sections 3-4 Goal Progress Brief, 2026-06-08

## Status

The goal is not complete yet. The current local hole inventory reports 8 target
`sorry`s remaining:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106:    sorry
dev34/GeoTop_3_4.thy:556:      sorry
dev34/GeoTop_3_4.thy:7388:    sorry
dev34/GeoTop_3_4.thy:8550:  sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047:    sorry
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9109:    sorry
```

This is better than the oldest audit snapshot of 17 holes and better than the
newest expert audit snapshot of 10 holes. The numerical trend is positive, but
the remaining 8 holes are still package-sized Moise picture arguments, not
ordinary tactic cleanup.

## What Improved

The branch is now split into focused layers: graph cache/prefix, mid-prefix,
final prefix, and active `dev34`. The fast checker also has focused targets and
cache status commands. This directly addresses the earlier problem where every
iteration could take minutes.

The latest work also moved several obligations out of theorem bodies and into
named packages. That matches the expert advice: close reusable geometric and
finite-graph lemmas, then make theorem wrappers short.

## Expert Audit Synthesis

The three expert reports agree on the main point: the project is well localized
but not in final close-out. The remaining work is concentrated in these
mathematical packages:

1. finite graph local/cycle realization;
2. endpoint chain / boundary-arc fan realization;
3. one-sided semicircle separation;
4. Section 3 subdisk and free-triangle fold support;
5. Theorem 4.2 theta/arc separation;
6. Theorem 4.4 brick and regular-neighborhood transfer.

The newest audit recommends a finite-graph sprint first. That still looks like
the best next move because it connects the graph-cache branch-vertex hole with
the active Figure 4.10 boundary-cycle realization.

## Current Risk

The main risk is treating each remaining `sorry` as a local proof-search
problem. Several holes stand for whole book steps:

- the branch-vertex local cutpoint argument needs the simple-closed-curve local
  one-manifold restriction, not just graph degree counting;
- the cycle realization needs a clean cyclic listing/subdivision model;
- the endpoint fan needs the path analogue of that realization;
- the semicircle statement may be too strong unless the local hypotheses really
  prevent reconnection outside the small ball;
- D44 is probably the largest remaining conceptual package despite being one
  visible hole.

## Recommended Next Sprint

Start with the finite-graph package:

1. close `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`;
2. use that and the existing graph infrastructure to finish the boundary-cycle
   realization in active `dev34`;
3. immediately follow with the endpoint chain/fan realization while the graph
   cache is warm.

For each edit, follow `CLAUDE.md`: grep `THEOREMS_AND_DEFS.txt` and
`STMT_INDEX.txt` first, add any new proof structure with `sorry` first, compile
focused slices immediately, replace small batches only after successful
compilation, regenerate indexes after theorem/cache changes, and commit verified
progress frequently.

## Bottom Line

The project is still approaching the goal, but it is not close in the sense of
"only a few tactics left." It is close in the sense that the remaining work is
explicitly mapped and isolated. Visible progress should be judged by closed
packages, especially the finite-graph sprint, rather than by raw line count or
the number of files touched.
