# GeoTop Sections 3-4 Goal Status, 2026-06-08

## Current State

The goal is not complete. The current focused hole check reports 8 target
`sorry`s remaining:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34/GeoTop_3_4.thy:556
dev34/GeoTop_3_4.thy:7388
dev34/GeoTop_3_4.thy:8550
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9109
```

Latest local commits:

```text
f5b72201 Track newer session transcript formats
2c84b9dc Keep branch split witness cardinality
d341d831 Record branch sphere triple cardinality
```

The most recent committed tooling change updated the index generators to cover
newer session transcript formats. Both `THEOREMS_AND_DEFS.txt` and
`STMT_INDEX.txt` should continue to be grepped before adding or naming any new
lemma.

## Expert-Audit Synthesis

The expert audits agree with the current local evidence: the raw hole count is
small, but the remaining holes are theorem-sized Moise picture arguments, not
simple tactic cleanup.

The recommended ordering is:

1. Treat the graph-cache branch-vertex lemma, graph-cycle split facts, and
   active Figure 4.10 cycle realization as one finite-graph sprint.
2. Then close the endpoint chain / boundary-arc fan realization.
3. Then handle the one-sided semicircle separator.
4. Larger Section 3 fold normalization, Theorem 4.2 theta separation, and
   Theorem 4.4 brick/regular-neighborhood packages should be developed as
   named reusable book-step lemmas, not patched locally with ad hoc tactics.

The audits specifically warn not to invent alternate proof strategies. The
work should continue by following Moise/book steps and the existing local proof
comments.

## Remaining Packages

### Finite Graph Sprint

Relevant holes:

```text
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9109
dev34/GeoTop_3_4.thy:556
```

The graph-cache hole is the branch-vertex local disconnect/cutpoint package for
a finite linear graph with simple-closed-curve carrier. The audit warns this
must use the simple-closed-curve/local-one-manifold hypothesis; degree greater
than two does not imply a cutpoint for arbitrary finite graphs.

The active `dev34` hole at line 556 is the Figure 4.10 cycle realization:
construct a subdivision of the boundary of a standard 2-simplex matching the
already-enumerated cyclic vertex/edge listing, then define the simplicial
isomorphism. Existing code has already split enumeration from realization.

Useful current fact: `geotop_finite_polyhedron_points_as_vertices_dev34` can
make a finite subset of a finite 1-complex carrier into vertices while
preserving carrier and finiteness. It does not by itself produce the cyclic
standard-boundary isomorphism.

### Endpoint Chain / Fan

Relevant hole:

```text
dev34/GeoTop_3_4.thy:7388
```

The endpoint bookkeeping is mostly present. The remaining book step is the
path analogue of the cycle realization: enumerate the finite connected
broken-line graph from the endpoint through the first neighbor, realize it as a
subdivided boundary arc of a standard 2-simplex, choose the adjacent boundary
vertex, and verify the cone/fan membership clauses.

### One-Sided Semicircle

Relevant hole:

```text
dev34/GeoTop_3_4.thy:8550
```

The audit recommends an explicit local Euclidean proof: choose a small radius
inside the one-sided simplex model, define the crosscut as
`sphere p r intersect sigma`, prove it is an arc, and show the local domain
minus that crosscut is disconnected. The audit also warns that the current
`U - A` statement may be overstrong unless the surrounding hypotheses localize
`U` enough to prevent reconnection outside the small ball.

### Section 3 / Theorem 4.2 / Theorem 4.4 Prefix Packages

Relevant holes:

```text
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix/GeoTop_3_4_Prefix.thy:106
```

These are the larger book packages:

- Section 3 subdisk induction-transfer for free triangles.
- Section 3 fold normalization with support control.
- Theorem 4.2 theta-graph arc-separation contradiction.
- Theorem 4.4 brick decomposition / regular-neighborhood / frontier component
  transfer.

These should remain structured as book-step packages and be decomposed into
named helper lemmas only when the helper is genuinely part of the Moise proof.

## Verification / Speed Notes

Focused cache status from the last work session:

- `dev34-cycle-realization`: fresh and hot; normal focused slice processing
  rewarms to about a few seconds.
- `dev34-fan`: fresh.
- `dev34-semicircle`: stale/missing at the line-8552 prefix/slice level.
- `graph-branch-local`: prefix fresh, long slice stale/missing.

A one-off `sledgehammer` probe at the cycle realization hole took about
26 seconds elapsed / 58 seconds CPU and produced no `Try this`. That suggests
the productive loop is not repeated single-goal prover probes. Use:

1. grep both full indexes,
2. add a `sorry` skeleton for a book-aligned helper,
3. compile immediately with the focused slice,
4. then replace small batches of `sorry`s using batched prover markers.

Per `CLAUDE.md`, continue to reread the file periodically, keep the build green,
use `by100` for automation, remove all temporary `sledgehammer` / `try0`
markers, regenerate indexes after theorem/cache changes, and commit verified
progress frequently.
