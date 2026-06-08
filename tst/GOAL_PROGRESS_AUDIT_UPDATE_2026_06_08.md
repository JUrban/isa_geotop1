# GeoTop Sections 3-4 Progress Audit Update, 2026-06-08

## Current Status

The goal is not complete. The current focused hole checker reports 8 target
`sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9109
dev34/GeoTop_3_4.thy:381
dev34/GeoTop_3_4.thy:7447
dev34/GeoTop_3_4.thy:8649
```

This is progress from the expert audit sequence: the audits observed roughly
17, then 14, then 10 visible target holes. The local count is now 8. The
important caveat is that the remaining holes are large formalized book steps,
not small tactic failures.

## What Has Improved

The branch is better organized than it was several days ago. The work is split
across focused prefix, graph-cache, mid-prefix, and active `dev34` layers, and
the fast checker has focused targets. This directly addresses the previous
problem where each verification iteration was too broad and expensive.

Several obligations have also been moved out of anonymous theorem-body holes
and into named packages. The latest committed example is the Figure 4.10
boundary-cycle package:

```text
geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34
```

The endpoint fan work was also corrected to target a boundary-arc fan rather
than an inappropriate full boundary-cycle model. That is a real statement-shape
fix, not just a local proof edit.

## Expert Audit Synthesis

The expert audits agree with the current evidence: the project is approaching
the goal structurally, but it is not in final cleanup. The remaining work is
concentrated in these packages:

- finite graph local cutpoint and cycle realization;
- Section 3 subdisk/free-triangle transfer;
- Section 3 support-controlled fold normalization;
- Theorem 4.2 theta/arc separation;
- Theorem 4.4 brick or regular-neighborhood transfer;
- Figure 4.10 standard boundary-cycle subdivision;
- endpoint-chain boundary-arc fan realization;
- one-sided semicircle separation.

The newest audit's main warning still applies: do not treat these as isolated
`sorry`s to be solved by local proof search. Most of them need reusable
intermediate lemmas that formalize Moise's picture arguments.

## Recommended Next Milestone

The best next milestone is a finite-graph sprint:

1. Close or sharply isolate the branch-vertex local cutpoint package in
   `dev34_prefix_graph/cache`.
2. Use the cyclic successor/orbit infrastructure to close the active Figure
   4.10 boundary-cycle realization at `dev34/GeoTop_3_4.thy:381`.
3. Reuse the same graph-listing discipline for the endpoint-chain boundary-arc
   fan package at `dev34/GeoTop_3_4.thy:7447`.

This path is recommended because it connects multiple remaining holes and uses
the freshest focused verification setup. The Section 3 fold package and Theorem
4.4 brick package remain necessary, but they are larger PL-topology packages
and are less likely to give quick iteration wins.

## Process Notes

Future work should continue to grep the full generated indexes frequently:

```bash
rg -n "<topic>" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

The `CLAUDE.md` workflow remains binding: new proof structure starts with
`sorry`, focused checks run immediately, proof replacements are done in small
batches, stale focus caches are refreshed only when they are the active target,
and indexes are regenerated after theory/cache/report changes.

## Bottom Line

The project is making real progress toward zero target `sorry`s, but the time
spent so far is understandable because the remaining holes are compressed
topology and finite-graph arguments from Moise, not ordinary Isabelle cleanup.
The clearest sign of forward movement from here will be closing one whole
package, preferably the finite-graph package, rather than only reducing line
count or moving a `sorry` deeper into another wrapper.
