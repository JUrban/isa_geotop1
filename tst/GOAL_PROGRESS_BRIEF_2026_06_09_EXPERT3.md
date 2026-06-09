# GeoTop Sections 3-4 Progress Brief, 2026-06-09

## Current verified status

The zero-target-`sorry` goal is not finished. The live target scan now reports
six `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:9933
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:3921
dev34/GeoTop_3_4.thy:14859
```

This is better than the expert3 raw count of eight. Two expert3 targets have
since closed as target holes: the active standard-boundary cycle realization
and the one-sided semicircle/collar package. The expert diagnosis is still
right in substance: the remaining holes are package-sized Moise book arguments,
not isolated automation cleanups.

## Remaining packages

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   - Theorem 4.4 brick / regular-neighborhood / component transfer.
   - Still the largest remaining prefix package.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   - Section 3 chord-subdisk induction transfer.
   - Needs the book-faithful smaller-subdisk proof and boundary-witness
     transfer back to the parent disk.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   - Section 3 support-controlled free-triangle fold engine.
   - The support-parametric architecture is correct and should be kept, because
     it serves both the unrestricted and supported fold uses.

4. `geotop_polygon_arc_opposite_boundary_theta_component_split_prefix`
   - Theorem 4.2 / D42 theta-separation package.
   - The intended proof is the Moise theta contradiction, not component
     algebra by broad automation.

5. `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   - Graph-cache branch-vertex local cutpoint package.
   - Its remaining named bridge is
     `geotop_connected_split_side_three_germs_local_component_prefix`: from the
     simple-closed-curve/local split-side setup, produce a component of
     `ball w r - (e1 union e2 union e3)` whose closure meets all three selected
     incident edge germs.
   - Current diagnosis: the bridge is now named and isolated, but as an
     abstract lemma it appears under-specified. The hypotheses put `p` and `y`
     in the connected set `N`; the third point `z` is only known to lie in the
     closure of the third germ. The next useful edit is therefore to rethread
     the upstream arc-side split data, or add the exact third-germ relation
     needed by the local-component argument, rather than trying to prove the
     current abstract statement by automation.

6. `geotop_endpoint_nonfinish_degree_and_boundary_arc_target_book_step_dev34`
   - Active endpoint non-finish package. It now combines the endpoint degree
     bound with the endpoint boundary-arc fan target construction.
   - The downstream wrapper
     `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
     calls this named theorem; the visible hole is in the named package, not in
     the wrapper.

## Audit takeaways to keep

- Use the full indexes frequently:
  `rg -n "pattern" THEOREMS_AND_DEFS.txt STMT_INDEX.txt`.
- The graph-cache branch package must use the simple-closed-curve/local
  one-manifold hypothesis. A general "degree greater than two implies cutpoint"
  claim for arbitrary finite graphs would be false.
- The endpoint target is correctly a boundary-arc fan, not a full boundary-cycle
  model. Existing full-boundary Figure 4.10 helpers should not be used as a
  shortcut unless they really prove the endpoint arc clauses.
- The D42 and D44 packages are genuine separation / regular-neighborhood book
  steps. Moving them into weaker local wrappers will not complete the goal.
- Per `CLAUDE.md`, new proof structure should be written with `sorry` first,
  compiled, and only then replaced in small verified batches.

## Iteration and cache status

The current workflow is faster than broad Isabelle builds:

```bash
./check_dev34_fast.sh holes
rg -n "concept_or_theorem_name" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
./check_dev34_fast.sh focus-full graph-branch-local geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34
```

The last two proof changes introduced named packages and verified focused
slices:

```text
geotop_connected_split_side_three_germs_local_component_prefix
geotop_endpoint_nonfinish_degree_and_boundary_arc_target_book_step_dev34
```

The generated indexes include advice/report files, so this report update should
be followed by:

```bash
bash gen_index.sh
bash gen_stmt_index.sh
```

The two index generators already include `PLAN_zero_sorry-expert*.md`,
`*PROGRESS*.md`, `*REPORT*.md`, `*STATUS*.md`, `CLAUDE*.md`, and bounded
session transcript files through `index_theory_lib.py`. No script change is
needed for `PLAN_zero_sorry-expert3.md`; normal regeneration is enough.

## Recommended next move

The most actionable current target is still one complete package at a time.
There are two realistic near-term choices:

1. Finish the graph-cache local-component bridge, because the surrounding
   radial-sector contradiction is already staged.
2. Finish the endpoint non-finish package, using the existing endpoint chain
   listing and fan-transfer helpers, while avoiding the old full-boundary-cycle
   shortcut.

Either route should preserve the current six-hole map until a package is
actually closed.
