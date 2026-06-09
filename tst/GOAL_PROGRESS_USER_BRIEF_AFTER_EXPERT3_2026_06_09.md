# GeoTop Sections 3-4 zero-sorry progress brief after expert3

Date: 2026-06-09

This note is a local progress/status report for the current `/project/tst`
checkout after rereading `CLAUDE.md`, `PLAN_zero_sorry-expert3.md`, the existing
local status notes, the generated indexes, and the live checker output.

## Current verified status

The zero-sorry goal is not complete. The live target scan reports 6 executable
`sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:14093
```

This is better than the expert3 report's 8-hole map. Expert3 remains useful for
strategy, but two of its listed targets are no longer live holes in this local
checkout:

```text
geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34
geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
```

Those names still appear in the indexes as proved or staged facts, but not as
the current executable target holes.

## Remaining proof packages

The 6 live holes correspond to these package-sized obligations:

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   - Moise Theorem 4.4 brick / regular-neighborhood component transfer.
   - This is probably the largest remaining package.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   - Section 3 chord subdisk induction transfer.
   - Needs side-disk triangulations, smaller 2-simplex counts, and transfer of
     free-triangle witnesses back to the parent disk.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   - Section 3 supported fold normalization.
   - This should stay support-parametric; proving an unsupported variant first
     would duplicate the hard work.

4. `geotop_polygon_arc_opposite_boundary_decomposition_prefix`
   - Moise Theorem 4.2 opposite-boundary arc separation.
   - The missing core is the theta/broken-line contradiction.

5. `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   - Graph-cache branch-vertex local cutpoint package.
   - Expert3's warning still applies: do not replace this with the false
     general claim that degree greater than 2 implies a cutpoint for arbitrary
     finite graphs. The simple-closed-curve/local-one-manifold hypothesis is
     essential.

6. `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
   - Endpoint chain to boundary-arc fan model.
   - The remaining problem is now sharper: enumerate the endpoint chain and
     build a matching boundary-arc target chain on a standard 2-simplex
     boundary subdivision. The cone/fan clauses have been isolated behind a
     proved bridge.

## Main bottleneck

The best near-term target is still the graph/endpoint cluster, but the reason is
now more specific than in the expert3 audit.

The branch-vertex proof already stages the downstream contradiction: no local
component of the punctured small ball can meet all three selected incident edge
germs. The remaining bridge is upstream: the current split-side package ties a
connected witness to two selected germs, while the contradiction needs one local
component whose closure touches all three. That is a statement-shape gap, not a
routine automation gap.

The endpoint fan package is related. The source-side endpoint chain listing is
mostly packaged, but the theorem currently lacks an immediate global
degree/no-branch bridge from the broken-line hypotheses. On the target side,
two new proved helpers now cache the finished cone work:

```text
geotop_endpoint_chain_target_model_from_boundary_subdivision_and_matching_dev34
geotop_endpoint_oriented_chain_boundary_arc_fan_model_from_boundary_subdivision_target_dev34
```

So the endpoint target construction is reduced to producing a same-length
endpoint chain `F,w',q',us` that is a subdivision of the standard triangle
boundary, plus the indexwise vertex bijection.

## Verification and cache status

The user concern about slow iteration is valid. The current process should avoid
full builds for every proof attempt. The fast loop should be:

```bash
./check_dev34_fast.sh holes
rg -n "keyword" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
rg -n "keyword" dev34_prefix dev34_prefix_mid dev34_prefix_graph dev34
./check_dev34_fast.sh focus-full graph-branch-local geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
./check_dev34_fast.sh focus-full dev34-fan geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34
```

`CLAUDE.md` says to regenerate both generated indexes after caching or adding
theorems. The two index scripts already use `index_theory_lib.py` and include
active theories, local imports, advice/report notes, session/signature files,
and bounded session logs in their cache signatures. They should still be rerun
after this report so the new note becomes searchable.

The endpoint bridge was checked through the focused split prefix generated by:

```bash
./check_dev34_fast.sh focus-full dev34-fan geotop_endpoint_oriented_chain_boundary_arc_fan_model_from_boundary_subdivision_target_dev34
```

That prefix built successfully. The tail then failed in later pre-existing
semicircle/local-Euclidean obligations, so this should not be treated as a full
`dev34` tail certification.

## Bottom line

We are approaching the goal in the sense that the visible target surface has
narrowed to 6 named packages and several expert3 risks are now closed locally.
We are not at the "few tactics left" stage. The next useful progress is a
package closure or a sharper package-level lemma, especially for the
branch-vertex local-component bridge or the endpoint boundary-arc fan model.
