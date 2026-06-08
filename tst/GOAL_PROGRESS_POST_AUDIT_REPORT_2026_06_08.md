# GeoTop Sections 3-4 Post-Audit Progress Report, 2026-06-08

## Status

The zero-sorry goal is not complete. A fresh local run of
`./check_dev34_fast.sh holes` reports 8 target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34/GeoTop_3_4.thy:378
dev34/GeoTop_3_4.thy:7555
dev34/GeoTop_3_4.thy:8757
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9109
```

This is progress relative to the previous expert audit sequence, which saw the
work move from stale counts around 17 and 14 to a credible 10-hole state. The
current count is 8, but the remaining items are still package-sized Moise
arguments, not final tactic cleanup.

## What Changed Recently

Recent commits improved the Figure 4.10 boundary-cycle path:

- `319677e2` simplified assumptions for the standard boundary subdivision
  package.
- `2f487fe3` added a helper putting finitely many boundary points into a finite
  1-complex with the same boundary carrier.
- `1db9f52c` added a helper producing a finite subdivision of the 2-simplex
  boundary with prescribed boundary points as vertices.

These helpers formalize part of the book sentence "subdivide the edges so as to
get a 1-dimensional complex with the same number of edges as L(v)." They do not
yet close the Figure 4.10 realization hole, partly because the helper facts live
after the current book-step theorem in theory order.

## Expert Audit Synthesis

The previous expert audit remains directionally correct. The project is
approaching the goal structurally: the remaining work is isolated into named
packages and the focused checker makes iteration cheaper. It is not approaching
completion in the sense that only routine automation remains.

The important remaining packages are:

- finite graph local cutpoint and boundary-cycle realization;
- Section 3 subdisk/free-triangle transfer;
- Section 3 support-controlled fold normalization;
- Theorem 4.2 theta/arc separation;
- Theorem 4.4 brick or regular-neighborhood transfer;
- endpoint-chain boundary-arc fan realization;
- one-sided semicircle separation.

The audit recommendation still stands: close whole packages by adding reusable
intermediate lemmas, instead of trying to solve each visible `sorry` in place.

## Best Next Milestone

The best near-term milestone is still the finite-graph/Figure 4.10 sprint:

1. Finish or sharply isolate
   `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`.
2. Close `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`.
3. Reuse the same graph-listing and boundary-subdivision infrastructure for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.

Before adding any more facts, grep both generated indexes:

```bash
rg -n "<topic>" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

After report, theory, or cache changes, regenerate the indexes with:

```bash
bash gen_index.sh
bash gen_stmt_index.sh
```

## Bottom Line

There has been real progress: the hole count is down to 8 and the Figure 4.10
boundary subdivision subproblem now has proved helper lemmas. The goal is still
not close in the "minutes of cleanup" sense. The next useful sign of progress
will be closing one complete package, preferably the finite-graph/Figure 4.10
package, and then reusing that machinery for the endpoint fan package.
