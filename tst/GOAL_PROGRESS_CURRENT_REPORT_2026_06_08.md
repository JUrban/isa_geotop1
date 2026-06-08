# GeoTop Sections 3-4 Current Progress Report, 2026-06-08

Snapshot: `codex-dev34-cache` at `d4010d04`, checked locally at
2026-06-08T10:59:31Z.

## Status

The zero-sorry goal is not complete yet. The current focused checker reports 8
target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:381
dev34/GeoTop_3_4.thy:7447
dev34/GeoTop_3_4.thy:8649
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9109
```

That is real progress from the expert-audit sequence, which saw stale snapshots
around 17, then 14, then 10 holes. The current number is smaller, but the
remaining holes are still package-sized Moise picture arguments rather than
small tactic cleanup.

## Expert Audit Synthesis

The previous expert reports remain useful. Their shared diagnosis is that the
project is structurally close but still has a few hard mathematical packages
left:

- finite graph local cutpoint and cycle realization;
- Section 3 subdisk/free-triangle transfer;
- Section 3 support-controlled fold normalization;
- Theorem 4.2 theta/arc separation;
- Theorem 4.4 brick or regular-neighborhood transfer;
- Figure 4.10 boundary-cycle subdivision;
- endpoint-chain boundary-arc fan realization;
- one-sided semicircle separation.

The important warning from the audits still applies: do not try to solve these
as isolated local `sorry`s. Most need named intermediate lemmas that formalize
Moise's diagrammatic steps.

## What Improved

The work is now split into focused layers instead of one large active theory:
graph cache, graph prefix, mid-prefix, final prefix, and active `dev34`. The
fast checker supports focused targets, and `dev34-cycle-realization` currently
has both a fresh prefix cache and a fresh slice cache.

The generated indexes are now central to the workflow. Before adding or
restating facts, search both:

```bash
rg -n "<topic>" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

This should prevent duplicate lemmas and wasted proof attempts. The indexes and
focus-cache status should be refreshed whenever theory or cache files change.

## Current Verification Picture

`./check_dev34_fast.sh holes` reports the 8 holes above.

`./check_dev34_fast.sh focus-status` shows the best hot target is currently
`dev34-cycle-realization`; many mid-prefix, D44, fan, semicircle, and graph
long-slice targets have stale or missing slice caches. That means the fastest
iteration path is to use hot focused targets first, and refresh stale slices
only for the active proof package.

## Recommended Next Milestone

The best next measurable milestone is still the finite-graph sprint:

1. Finish or sharply isolate
   `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`.
2. Close
   `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`
   / the Figure 4.10 boundary-cycle subdivision package.
3. Reuse the same graph-listing discipline for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.

This route connects multiple remaining holes and uses the freshest verification
setup. The Section 3 fold package and Theorem 4.4 brick package remain
necessary, but they are larger PL-topology packages and are less likely to give
quick iteration wins.

## Bottom Line

The project is approaching the goal in the sense that the remaining work is
explicitly mapped and isolated. It is not approaching the goal in the sense that
only a few automation calls remain. Progress should now be judged by closed
packages, especially the finite-graph package, not by raw line count or by
moving a `sorry` into a deeper wrapper.
