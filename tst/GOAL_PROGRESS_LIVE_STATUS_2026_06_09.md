# Live GeoTop Sections 3-4 Goal Status - 2026-06-09

## Current status

The zero-target-`sorry` goal is not complete.  The current checked target
hole count is 6, not the 8 listed in the latest expert3 audit.  The audit is
still useful for strategy, but its line map is stale after the subsequent
cache work and endpoint helper additions.

Current `./check_dev34_fast.sh holes` output:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803:    sorry
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047:    sorry
dev34/GeoTop_3_4.thy:14855:  sorry
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610:        sorry
```

## Progress since the expert audits

The finite graph cycle-split work that expert3 identified as recently closed
remains closed.  The active graph-cache hole is now the branch-vertex local
cutpoint package, not the older cycle-orbit split.

The endpoint target is now correctly treated as a boundary-arc fan problem,
not a full boundary-cycle realization.  Recent work added verified two-vertex
endpoint/fan cache helpers, including a direct source-facing wrapper:

```text
geotop_named_2simplex_exists_dev34
geotop_two_vertex_endpoint_chain_fan_model_dev34
```

Both were checked with focused `slice-hot` verification.  The wrapper does
not close the endpoint theorem by itself; it prepares the finish-edge
`[w, q]` branch of the remaining endpoint package.

## Verification and indexing

Recent focused checks:

```text
./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy geotop_named_2simplex_exists_dev34
./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy geotop_two_vertex_endpoint_chain_fan_model_dev34
./check_dev34_fast.sh holes
```

The theorem and statement indexes were regenerated after the new helpers:

```text
THEOREMS_AND_DEFS.txt / .md: 4613 entries
STMT_INDEX.txt: 9820 entries
```

## Practical assessment

We are approaching the goal structurally, but not at the "routine cleanup"
stage.  The remaining 6 holes are package-level Moise arguments:

1. branch-vertex local cutpoint in the graph cache;
2. endpoint boundary-arc fan realization in active `dev34`;
3. three Section 3 mid-prefix transfer/normalization/theta packages;
4. final Section 4.4 prefix transfer package.

The fastest iteration pattern is now to keep using full-index `rg` searches
before adding lemmas, then verify local work with `slice-hot` or focused dirty
layers.  Rebuilding broad targets for every edit is too slow; the latest
endpoint wrapper iteration reused the prefix cache and checked only the local
slice.
