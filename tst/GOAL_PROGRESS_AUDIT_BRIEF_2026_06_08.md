# Goal Progress Audit Brief, 2026-06-08

Snapshot: local branch `codex-dev34-cache` at `d9e0dd2f`.

## Current Status

The zero-sorry goal for GeoTop/Moise Sections 3 and 4 is not complete.
A fresh local run of `./check_dev34_fast.sh holes` reports 8 target
`sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9109
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:378
dev34/GeoTop_3_4.thy:7627
dev34/GeoTop_3_4.thy:8829
```

No `sledgehammer` or `try0` markers are visible in the current target
directories.

## Expert Audit Takeaway

The previous expert reports are directionally right but their raw hole counts
are stale. The project has moved from the earlier 17/14/10-hole snapshots to
8 verified target holes. That is real progress, but the remaining holes are
still package-sized mathematical arguments rather than routine tactic cleanup.

The useful audit advice is:

- treat the remaining work as a small number of proof packages;
- add reusable intermediate lemmas instead of attacking each visible `sorry`
  only in place;
- use the generated indexes aggressively before adding facts;
- use focused cached checks for the active package, not broad verification for
  every iteration.

## Remaining Packages

The 8 holes currently group into these packages:

- finite graph local cutpoint: branch vertex local disconnects a finite linear
  graph with simple-closed-curve carrier;
- Theorem 4.4 brick / regular-neighborhood transfer;
- Section 3 subdisk/free-triangle transfer;
- Section 3 support-controlled fold normalization;
- Theorem 4.2 theta / arc separation;
- Figure 4.10 cyclic boundary-subdivision realization;
- endpoint-chain boundary-arc fan realization;
- one-sided local semicircle separation.

## Recent Progress

Recent commits added boundary-subdivision helpers that preserve prescribed
boundary points and original boundary vertices. These are useful for the
Figure 4.10 and endpoint-fan packages, but they do not yet close the active
book-step holes. One practical issue is theory order: some strong helpers live
after earlier open book-step theorems, so either earlier-compatible helpers or
careful reordering will be needed.

The latest committed proved helper is:

```text
geotop_2simplex_boundary_finite_points_subdivision_preserves_vertices_dev34
```

It was verified with the hot slice checker before commit.

## Verification and Speed

`./check_dev34_fast.sh focus-status` currently reports fresh coarse caches but
mostly stale or missing slice caches. That matches the slow iteration problem.
For the next proof sprint, refresh only the target slice being worked on, then
iterate with that hot slice. Avoid repeatedly paying for unrelated mid-prefix,
brick, fan, and semicircle slices.

Before introducing any new lemma or definition, search the full generated
indexes:

```bash
rg -n "<topic>" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

After theory, cache, or report changes, regenerate the indexes:

```bash
bash gen_index.sh
bash gen_stmt_index.sh
```

## Assessment

The work is approaching the goal structurally: the remaining obligations are
localized and named. It is not yet close in elapsed time terms, because several
remaining obligations formalize Moise diagram arguments that each need a real
lemma package.

The best next milestone is to close one complete reusable package, preferably
the finite-graph / Figure 4.10 realization package, then reuse that machinery
for the endpoint-chain fan package. Progress should be measured by completed
packages and verified target-hole reduction, not by moving a `sorry` deeper
into a wrapper.
