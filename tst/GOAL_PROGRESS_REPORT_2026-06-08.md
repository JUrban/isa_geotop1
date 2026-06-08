# Goal Progress Report, 2026-06-08

Objective: finish GeoTop / Moise Sections 3 and 4 with no target `sorry`s.

## Current Status

The goal is not complete, but the work is still moving toward it. The current
target stack has 8 visible `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:378
dev34/GeoTop_3_4.thy:7627
dev34/GeoTop_3_4.thy:8829
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9261
```

`rg` over the current target directories found no `sledgehammer` or `try0`
markers in the active target stack. The latest focused cache status is good for
the current graph target:

```text
graph-branch-local: fresh prefix-base, fresh prefix cache, fresh slice cache
dev34-cycle-realization: stale/missing
dev34-fan: stale/missing
```

So focused graph iteration is currently fast, while the active `dev34` cycle and
fan targets still need cache priming before they become similarly cheap.

## What Changed Since The Expert Audits

The expert audits were useful, but their hole counts are now stale. They
described earlier states with roughly 17, then about 14, then about 10 visible
target holes. The live count is now 8.

The audits' main diagnosis remains correct: the remaining holes are not simple
tactic cleanup. They are package-sized formalizations of Moise picture
arguments. The current 8 holes are concentrated into these themes:

1. Theorem 4.4 brick / regular-neighborhood package.
2. Section 3 Figure 3.2 subdisk induction transfer.
3. Section 3 Theorem 3.4 / 3.7 fold normalization with support control.
4. Theorem 4.2 theta separation / component split.
5. Figure 4.10 standard boundary cycle realization.
6. Endpoint-chain boundary-arc fan realization.
7. One-sided local semicircle separator.
8. Branch-vertex local-star bridge in the finite graph cache.

This matches the latest expert recommendation: treat the graph-cache
branch-vertex lemma, the finite graph realization lemmas, and the endpoint fan
lemma as a coherent finite-graph sprint rather than as unrelated holes.

## Recent Concrete Progress

Recent commits show real narrowing of the finite-graph branch problem:

```text
bcaecff2 Isolate graph split-side component bridge
46e92106 Isolate branch local star bridge
a68a08f5 Package selected edge sector contradiction
ba5a28ca Add local sector bound contradiction
d9e0dd2f Preserve boundary vertices in subdivision helper
1db9f52c Add boundary subdivision vertex preservation helper
2f487fe3 Add boundary finite-point vertex helper
319677e2 Simplify Figure 4.10 cycle package assumptions
1888c383 Name Figure 4.10 boundary cycle package
```

The current graph-cache hole is no longer the whole branch-vertex contradiction.
It has been reduced to a precise local-star bridge:

```text
Find one component of ball w r - (e1 union e2 union e3)
whose closure meets all three selected incident edge germs.
```

Once that component exists, the already-proved sector bound immediately gives
the contradiction. This is meaningful progress because the remaining gap is now
sharply stated instead of hidden inside a broad local-graph theorem.

The active `dev34` cycle package has also been made more explicit: recent helper
commits preserve boundary vertices in subdivision models, which is exactly the
kind of bookkeeping the expert audit said was needed for Figure 4.10.

## Main Risk

The remaining 8 holes are small in number but not small in mathematical content.
The largest unresolved packages are:

- Theorem 4.4 bricks and regular neighborhoods.
- Section 3 fold normalization with support control.
- Theorem 4.2 theta separation.

These are likely still multi-step proof packages. It would be misleading to say
the project is "almost done" merely because the raw hole count is 8.

The most important process risk is spending too much time on broad verification.
The cache split is helping: `graph-branch-local` now checks as a focused slice,
and this should be the default iteration style. Before moving back to
`dev34-cycle-realization` or `dev34-fan`, prime those focus caches so iteration
does not return to multi-minute checks.

## Recommended Next Step

Continue with the graph sprint while the cache is fresh:

1. Finish `hlocal_component_meets_selected_three_edges_book_step` in
   `dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy`.
2. Verify with `./check_dev34_fast.sh focus graph-branch-local`.
3. Regenerate indexes.
4. Commit.
5. Prime `dev34-cycle-realization` and use the graph work to attack the standard
   boundary subdivision model at `dev34/GeoTop_3_4.thy:378`.

This is the best route toward the goal because it uses the currently fresh cache
and follows the expert audit's recommendation to close the finite-graph package
as one coherent block.
