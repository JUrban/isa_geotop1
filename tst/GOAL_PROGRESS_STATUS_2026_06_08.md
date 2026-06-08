# GeoTop Sections 3-4 Goal Progress Status, 2026-06-08

## Current Status

The goal is still incomplete. The current verified target inventory has 8
remaining `sorry`s:

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

This is real progress from the expert audit snapshots: the earlier reports saw
17 target holes, then roughly 14, then 10. The current local checker reports 8.
There are no `sledgehammer` or `try0` markers in the checked target set.

The latest committed proof work is `dda49b08 Retarget endpoint fan package to
boundary arc`. That fixed an important statement-shape problem: the endpoint fan
target is now a boundary-arc fan package, not an incorrect full-boundary-cycle
isomorphism requirement.

The Figure 4.10 cycle realization hole is now named as
`geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`.
The surrounding cyclic-listing proof calls this package instead of carrying an
anonymous inner `sorry`.

## What The Expert Audits Imply

The previous expert audits were right about the main diagnosis. This is not
blocked by ordinary tactic cleanup. The remaining holes are compressed Moise
picture arguments:

- finite graph local cutpoint and cycle realization;
- Section 3 subdisk/free-triangle transfer;
- Section 3 support-controlled fold normalization;
- Theorem 4.2 theta/arc separation;
- Theorem 4.4 brick or regular-neighborhood transfer;
- Figure 4.10 boundary-cycle realization;
- endpoint-chain boundary-arc fan realization;
- one-sided semicircle separation.

The current branch is therefore approaching the goal structurally, but not in
the sense that only a few `blast` calls remain. Progress should be measured by
closing these named packages, not by the small raw count of 8 holes.

## Verification And Speed

The focused checker/cache setup is now the right workflow. Current focus status:

```text
dev34-cycle-realization: fresh prefix and fresh slice cache
dev34-fan:               fresh prefix and fresh slice cache
graph-branch-local:      fresh prefix cache, stale/missing long slice
dev34-semicircle:        stale/missing prefix and slice near line 8591
```

This means the next iteration should not spend 2.5 minutes on every check.
Prefer the hot focused targets first, especially `dev34-cycle-realization` and
`dev34-fan`, and only refresh the stale semicircle/graph long slices when that
is the active target.

The index workflow from `CLAUDE.md` remains important: grep both
`THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt` before adding lemmas, and
regenerate the indexes after theorem/cache/report changes.

## Best Next Sprint

The best next sprint is still the finite-graph sprint recommended by the latest
expert audit:

1. Close the graph-cache branch/local cutpoint package, or at least isolate its
exact local simple-closed-curve obstruction.
2. Use the existing cyclic successor/orbit infrastructure to close the standard
boundary-cycle subdivision model in `dev34/GeoTop_3_4.thy:381`.
3. Then close the endpoint-chain boundary-arc fan package at
   `dev34/GeoTop_3_4.thy:7447`, reusing the same graph-listing discipline.

That route is preferred because it connects several remaining holes and uses
the freshest focus caches. The Section 3 fold and Theorem 4.4 brick package are
still necessary, but they are larger PL-topology packages and should not be
mistaken for quick local proof-search tasks.

## Bottom Line

The project is moving toward the goal, but the remaining work is still
substantive. The improved split, hot checks, regenerated indexes, and lower hole
count show real progress. The risk is spending more days treating theorem-sized
book steps as local verification problems. The next useful milestone is a
closed finite-graph package that removes both a graph-cache hole and the active
boundary-cycle/fan realization uncertainty.
