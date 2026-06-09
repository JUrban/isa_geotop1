# Brief progress report after expert audits

Date: 2026-06-09
Branch: `codex-dev34-cache`
Scope: GeoTop / Moise Sections 3 and 4 zero-target-sorry goal.

## Current status

The goal is not complete. A fresh focused hole scan currently reports 7 target
`sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:13568
dev34/GeoTop_3_4.thy:14786
```

Stable package names:

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_decomposition_prefix
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
```

This is real progress from the expert audits. The earlier expert reports
described 17, then about 14, then 10/8 target holes. Since the expert3-style
8-hole state, the boundary-cycle/Figure 4.10 standard realization package has
been closed. The active target count is now 7.

## Recent verified progress

The graph-prefix cycle split is no longer an open target. The non-adjacent
reverse orbit and two cut path carrier-intersection facts were already closed
before this report window.

The standard boundary-cycle realization target was closed and committed:

```text
7012c356 Close standard boundary cycle realization
```

Endpoint-chain infrastructure has also improved. The following normal-form
lemmas for endpoint listings were added and committed:

```text
geotop_endpoint_chain_listing_convex_hull_in_L_cases_dev34
geotop_endpoint_chain_listing_singleton_convex_hull_in_L_dev34
geotop_endpoint_chain_listing_adjacent_convex_hull_in_L_dev34
geotop_endpoint_chain_listing_convex_hull_in_L_cases_all_dev34
geotop_endpoint_chain_listing_complex_decomp_dev34
```

Commit:

```text
3e784527 Add endpoint chain normal form lemmas
```

One more endpoint helper was verified and committed:

```text
42aada49 Add endpoint chain matching isomorphism
```

That helper is:

```text
geotop_endpoint_chain_listing_isomorphism_from_matching_dev34
```

It is intended to support the remaining endpoint boundary-arc fan package by
reducing an endpoint chain isomorphism to matching ordered vertex lists.

After these changes, both generated indexes contain the new endpoint helper.
The current workflow is using `THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt`
regularly, as requested by `CLAUDE.md` and the user.

## What the expert audits got right

The experts' main diagnosis remains correct: the project is no longer blocked
by random local automation. The remaining holes are package-sized Moise picture
arguments:

- Section 3 subdisk induction/free-triangle transfer.
- Section 3 support-controlled fold normalization.
- Theorem 4.2 opposite-boundary arc decomposition via theta/separation.
- Theorem 4.4 brick or regular-neighborhood component transfer.
- Graph-cache branch-vertex local cutpoint.
- Endpoint-chain boundary-arc fan realization.
- One-sided simplex semicircle/crosscut separation.

The raw number 7 is therefore misleadingly small. Several remaining items are
whole book arguments hidden behind one `sorry`.

## Process and performance status

The focused checker is now the right iteration path:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh focus dev34-fan
./check_dev34_fast.sh focus-status
```

This is much faster than broad rebuilds for every edit. The current practice is:

1. Search both full indexes before adding lemmas.
2. Add small helper lemmas close to the current package.
3. Run a focused check for the slice.
4. Regenerate indexes after verified theory changes.
5. Commit small verified checkpoints.

The recent endpoint helper work followed this pattern. The focused `dev34-fan`
check completed successfully before the latest commit.

## Assessment

We are approaching the goal structurally, but not yet temporally close to done.
The work has moved from broad cleanup to a short list of hard formal packages.
The best evidence of progress is that the graph-prefix cycle machinery and the
active boundary-cycle realization are closed, and the endpoint path analogue now
has the listing/isomorphism infrastructure it was missing.

The largest remaining risks are still Theorem 4.4 and the Section 3 fold
normalization package. The next best local target is probably the endpoint
boundary-arc fan package, because it can reuse the newly committed endpoint
listing normal forms and matching-isomorphism helper.

## Recommended next steps

1. Continue with `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.
   Use the new endpoint listing decomposition and matching-isomorphism helper.
2. Keep arbitrary finite `W` clauses reduced to singleton/adjacent-edge cases
   early; this was the key lesson from the expert3 endpoint advice.
3. If endpoint fan stalls on target construction, switch briefly to the graph
   branch local cutpoint only if the existing local-component bridge can be
   isolated as a small lemma.
4. Leave Theorem 4.4 and Section 3 fold normalization for deliberate package
   work, not opportunistic tactic search.

