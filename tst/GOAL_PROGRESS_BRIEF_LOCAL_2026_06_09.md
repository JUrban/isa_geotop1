# GeoTop Sections 3-4 Zero-Sorry Goal: Local Progress Brief

Date: 2026-06-09

This report reflects the current local checkout in `/project/tst`, the project
instructions in `CLAUDE.md`, the full generated indexes
`THEOREMS_AND_DEFS.txt` and `STMT_INDEX.txt`, and the expert audit files
`PLAN_zero_sorry-expert*.md`, including `PLAN_zero_sorry-expert3.md`.

## Current status

The goal is not complete. The current local target scan reports 6 executable
`sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:13967
```

The visible remaining packages are:

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   - Moise Theorem 4.4 brick / regular-neighborhood / component-frontier
     transfer.
   - This is still the largest visible package.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   - Section 3 chord-subdisk induction transfer.
   - Needs side-disk triangulations, strict smaller counts, and transfer of
     free-triangle witnesses back to the parent disk.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   - Section 3 fold normalization with support control.
   - This is the shared engine for Theorems 3.4 and 3.7.

4. `geotop_polygon_arc_opposite_boundary_decomposition_prefix`
   - Moise Theorem 4.2 theta / opposite-boundary arc separation.
   - The remaining content is a theta-contradiction / broken-line extraction
     argument, not component algebra alone.

5. `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   - Graph-cache branch-vertex local cutpoint contradiction.
   - Expert3's warning remains important: do not prove a false general
     "degree > 2 implies cutpoint" theorem for arbitrary finite graphs. The
     simple-closed-curve / local-one-manifold hypothesis is essential.

6. `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
   - Endpoint chain to boundary-arc fan model.
   - The remaining work is source chain enumeration plus same-length target
     boundary-arc subdivision and cone/fan verification.

No current local hole is shown for the older expert3 names
`geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`
or `geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34`. Those
may still be dependency-relevant, but they are not in the current local
`./check_dev34_fast.sh holes` output.

## Progress relative to the expert audits

The older audits described 17, then 14, then 10, then 8 remaining target holes.
Those counts are stale for the local tree. The useful part of the audits is not
the old line numbers; it is the dependency diagnosis:

- the graph-prefix cycle split that was earlier open has been absorbed locally;
- the active cycle-boundary package no longer appears in the current hole scan;
- the one-sided semicircle package no longer appears in the current hole scan;
- the endpoint package has shifted to the model theorem, not the target wrapper;
- the branch-vertex package remains upstream of endpoint/source-chain reasoning;
- D44, D42, Section 3 subdisk transfer, and Section 3 fold normalization remain
  package-sized Moise picture arguments.

So there has been real progress. The local tree is not in the same state as the
first expert reports. But the remaining 6 holes are not "just tactics"; several
are whole formalized topology arguments hidden behind one `sorry`.

## Current risk assessment

The most important dependency issue is the graph/endpoint pair.

The branch-vertex local cutpoint proof currently reaches a very specific open
step: from a connected split-side package, obtain a local component of
`ball w r - (e1 union e2 union e3)` whose closure meets all three selected
edge germs. The downstream radial-sector contradiction is already staged. A
temporary `sledgehammer` probe at this hole did not find a direct proof, which
supports the expert3 diagnosis that the current assumptions are probably
missing one explicit bridge tying the third germ to the same local component.

The endpoint fan model should not be treated as already solved by the visible
target wrapper: the wrapper depends transitively on the open model theorem.
The model still needs the ordered endpoint chain plus target boundary-arc fan
construction. If the source-chain enumeration needs a no-branch/degree bound,
then the branch package remains an upstream dependency.

## Recommended next order

1. Continue with `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`.
   The next useful edit is not broad automation, but a strengthened local
   component bridge that explicitly includes the third selected germ or proves
   the needed first-exit/last-entry fact from the split-side construction.

2. Then close `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`.
   Reduce arbitrary finite vertex-set fan clauses early to singleton and
   adjacent-edge cases, as expert3 recommended.

3. Keep the Section 3 subdisk and fold packages as named book packages.
   They should be split into helper lemmas for side-disk triangulations,
   strict smaller counts, witness transfer, supported fold construction, and
   supported composition.

4. Treat D42 as a reusable theta-separation theorem.
   Do not try to prove it by unfolding components and using broad automation.

5. Leave D44 until after smaller graph/endpoint/local packages unless it blocks
   another dependency. It is a regular-neighborhood theorem, not a single local
   proof obligation.

## Process notes

The fast checker and full indexes are now essential. Use:

```bash
./check_dev34_fast.sh holes
rg -n "name_or_concept" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
rg -n "name_or_concept" dev34_prefix dev34_prefix_mid dev34_prefix_graph dev34
```

Focused checks should be preferred over broad builds during iteration. After
theory edits, regenerate the indexes if statements or new session files change,
then commit verified progress.
