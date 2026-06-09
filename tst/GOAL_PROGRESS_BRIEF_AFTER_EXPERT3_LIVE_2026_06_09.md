# GeoTop Sections 3-4 zero-sorry live progress brief

Date: 2026-06-09

This note is a current handoff/status report for `/project/tst` after rereading
`CLAUDE.md`, the expert audit files through `PLAN_zero_sorry-expert3.md`, the
existing local progress notes, the generated indexes, and the live target-hole
scan.

## Current status

The zero-sorry goal is not complete.  The current checked target surface is down
to 6 visible executable `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:14872
```

This is real progress relative to the older expert audits.  The earlier 17-hole,
10-hole, and 8-hole reports are now stale as raw counts, although their
mathematical diagnosis remains useful.  In particular, the finite cycle split,
the Figure 4.10 cyclic boundary realization, and the one-sided semicircle
package are no longer visible live holes in this checkout.

## Remaining packages

The 6 remaining holes are still package-sized Moise arguments, not routine tactic
cleanup:

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   - Moise Theorem 4.4 brick / regular-neighborhood / component-frontier
     transfer.
   - This is still the largest visible package and should remain a named
     regular-neighborhood theorem.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   - Section 3 chord-subdisk induction transfer.
   - Needs side complexes proved as smaller polygonal-disk triangulations and
     transfer of free-triangle witnesses back to the parent disk.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   - Section 3 supported fold normalization.
   - This remains the support-parametric engine for Theorems 3.4 and 3.7.

4. `geotop_polygon_arc_opposite_boundary_decomposition_prefix`
   - Moise Theorem 4.2 opposite-boundary arc separation.
   - The expert advice is still right: this needs a theta or broken-line
     contradiction package, not just component-set rewriting.

5. `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   - Graph-cache branch-vertex local cutpoint package.
   - The current internal gap is the local-component bridge: from the connected
     split-side setup, obtain a component of
     `ball w r - (e1 union e2 union e3)` whose closure meets all three selected
     incident edge germs.
   - Do not replace this by the false general claim that degree greater than 2
     implies a cutpoint for arbitrary finite graphs.  The simple-closed-curve /
     local-one-manifold hypothesis is essential.

6. `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
   - Endpoint chain to boundary-arc fan model.
   - The finish-endpoint case is closed by the two-vertex helper.  The remaining
     non-finish branch must derive the source chain order from the broken-line
     arc, build a same-length standard boundary-arc target chain, and verify the
     cone/fan clauses.

## Audit reconciliation

The expert3 report remains useful for ordering and risk control, but two parts
are now outdated locally:

- `geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`
  is indexed, but it is not a current live hole.
- `geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34` is also
  indexed, but it is not a current live hole.

The graph-prefix cycle split that earlier audits treated as a major target has
also been closed.  The live graph risk is now narrower: the branch-vertex local
component bridge in the graph cache, plus its relation to endpoint-chain
enumeration.

## Process status

The fastest loop should continue to use focused checks and full-index greps:

```bash
./check_dev34_fast.sh holes
rg -n "keyword" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
rg -n "keyword" dev34_prefix dev34_prefix_mid dev34_prefix_graph dev34
./check_dev34_fast.sh focus-full graph-branch-local geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
./check_dev34_fast.sh focus-full dev34-fan geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34
```

The two index scripts already track advice/report files and session/signature
inputs.  I do not see a script edit needed for the current report files; the
important step is to rerun both scripts after adding new reports or theorem
cache facts.

## Bottom line

We are approaching the goal in the concrete sense that the visible target
surface has narrowed to 6 named packages and several expert-audit risks have
closed locally.  We are not yet in the final tactic-cleanup phase.  The next
meaningful milestone should be closure, or a sharply checked package lemma, for
either the graph-cache local-component bridge or the endpoint boundary-arc fan
model.
