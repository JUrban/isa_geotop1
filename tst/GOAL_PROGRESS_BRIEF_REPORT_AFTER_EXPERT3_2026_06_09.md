# GeoTop Sections 3-4 Progress Brief After Expert3

Date: 2026-06-09

This is a brief local status report, taking `PLAN_zero_sorry-expert.md`,
`PLAN_zero_sorry-expert1.md`, `PLAN_zero_sorry-expert2.md`, and
`PLAN_zero_sorry-expert3.md` into account. I ignored the inactive colleague
state and checked the local branch directly.

## Current status

The zero-target-sorry goal is still open, but the project is moving toward it.
The latest local scan:

```bash
cd /project/tst && ./check_dev34_fast.sh holes
```

reports 7 target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:12872
dev34/GeoTop_3_4.thy:14090
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
```

The important change since `PLAN_zero_sorry-expert3.md` is that the active
Figure 4.10 boundary-cycle realization package is now closed:

```text
geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34
```

This was committed as:

```text
7012c356 Close standard boundary cycle realization
```

The previous supporting commit was:

```text
5ee5d2c5 Extract successor vertex index uniqueness
```

So the expert3 report is right about the nature of the remaining work, but its
8-hole inventory is now slightly stale: the boundary-cycle realization item has
been removed from the target hole list.

## Remaining packages

The stable remaining targets are:

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_decomposition_prefix
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
```

These are still package-sized Moise/PL-topology obligations, not final tactic
cleanup. The raw count is small, but the effort is not proportional to the raw
count.

## Expert audit reconciliation

The expert reports were directionally correct:

* Use theorem names rather than line numbers, because line numbers are moving.
* Search the full indexes frequently before adding facts.
* Keep closing whole packages rather than moving `sorry`s into wrappers.
* Use focused cache/checker modes for iteration.
* Treat the graph/Figure 4.10 work as the best near-term sprint.

The finite graph/Figure 4.10 sprint has made real progress: the graph-prefix
cycle split is closed, and the active boundary-cycle realization is now closed.
What remains from that cluster is the branch-vertex local-disconnect cache
package and the endpoint-chain boundary-arc fan package.

## Cache and index status

I reread the `CLAUDE.md` index instructions and checked the two index scripts.
`gen_index.sh` and `gen_stmt_index.sh` already delegate discovery to
`index_theory_lib.py`, whose patterns include theory files, ROOT/session files,
advice/progress/report markdown files, and bounded session transcripts such as
`*.cast`, `*.cast.gz`, and `session*.jsonl`. No immediate script update looks
needed just because of the new session/report files.

The full indexes should still be regenerated after theory/cache/report changes:

```bash
cd /project/tst && bash gen_index.sh && bash gen_stmt_index.sh
```

The focused cache status currently says:

```text
dev34-cycle-realization: fresh prefix cache and fresh slice cache
dev34-fan: stale/missing prefix and slice cache before/through the endpoint fan area
dev34-semicircle: stale/missing chained prefix/slice cache
prefix-d44 and mid packages: stale/missing focused slices
```

This means the next endpoint-fan iteration should start with a warm/focused pass
rather than broad verification.

## Recommended next step

The next best target is:

```text
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
```

Reason: it is the path analogue of the boundary-cycle package that just closed,
so it can reuse the same style of ordered-listing and finite-graph search work.
The first useful reduction is to extract a verified endpoint chain listing from
the existing broken-line/endpoint assumptions, then prove the fan realization
from that chain listing as a separate reusable package.

The branch-vertex local-disconnect cache package remains adjacent and important,
but the active endpoint fan is the most direct continuation of the just-closed
Figure 4.10 work.

## Bottom line

Yes, we are approaching the goal: the local target count has moved from the old
17-hole reports to 7, and a major active Figure 4.10 package has just been
closed and checked. No, the project is not in final cleanup yet: the remaining
7 holes are still real mathematical packages, especially D44 brick transfer,
Section 3 fold/subdisk transfer, D42 arc separation, branch local disconnect,
endpoint fan, and one-sided semicircle separation.

