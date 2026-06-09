# GeoTop Sections 3-4 Progress Brief, 2026-06-09

## Current verified status

The live target scan is down to six `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:9915
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:14872
```

The older expert audits are therefore stale on raw counts. Their main
diagnosis remains correct: the remaining holes are package-sized Moise picture
arguments, not routine tactic cleanup.

## Remaining packages

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   - Theorem 4.4 brick/regular-neighborhood/component transfer.
   - Largest remaining prefix package.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   - Section 3 chord-subdisk induction transfer.
   - Needs book-faithful smaller-subdisk and boundary-witness transfer.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   - Section 3 support-controlled free-triangle fold engine.
   - Intended to serve both unrestricted and support-controlled fold uses.

4. `geotop_polygon_arc_opposite_boundary_theta_component_split_prefix`
   - Theorem 4.2/D42 theta separation package.
   - Needs the book step extracting a forbidden theta graph if opposite
     boundary sides lie in the same component.

5. `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   - Graph-cache local branch cutpoint package.
   - Current inner gap is the local three-germ bridge: from the simple-closed
     curve/local graph setup to a component of
     `ball w r - (e1 union e2 union e3)` whose closure meets all three selected
     incident edge germs.

6. `geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
   - Active endpoint-chain boundary-arc fan realization.
   - The current non-finish branch still lacks the endpoint chain to boundary
     arc model. The older full-boundary-cycle shortcut is not appropriate for
     this target.

## Audit takeaways to keep

- Use the full indexes frequently. `THEOREMS_AND_DEFS.txt` and
  `STMT_INDEX.txt` should be searched before inventing any helper.
- The graph-cache branch package must use the simple-closed-curve/local
  one-manifold hypothesis. A general "degree greater than two implies
  cutpoint" theorem for arbitrary finite graphs would be false.
- The endpoint fan target is now correctly a boundary-arc fan, not a whole
  boundary-cycle model.
- The D42 and D44 packages are genuine separation/regular-neighborhood book
  steps. Wrapping them in weaker local claims will not complete the goal.
- Per `CLAUDE.md`, any new proof structure should be written with `sorry`
  first and compiled before replacing holes in small batches.

## Iteration and caching status

The current workflow is faster than broad Isabelle builds:

- `./check_dev34_fast.sh holes` gives the live target hole map quickly.
- Focused targets should be used for local work, especially:
  - `focus-full graph-branch-local geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
  - `focus-full dev34-fan geotop_endpoint_oriented_chain_boundary_arc_fan_model_book_step_dev34`
  - `slice-hot dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy geotop_polygon_arc_opposite_boundary_theta_component_split_prefix`
- The index scripts already include local advice/report files in their cache
  signatures, so new reports should be followed by:
  - `bash gen_index.sh`
  - `bash gen_stmt_index.sh`

## Recommended next move

The most actionable current proof target is the graph-cache branch gap. The
surrounding proof has already staged the radial-sector contradiction; the open
step is specifically the book bridge that forces a local component to touch all
three selected germs. If the exact bridge cannot yet be proved directly, the
next useful change is to isolate that bridge as the single named missing book
step without increasing the total hole count, then continue replacing its
substeps from the existing local SCC and component infrastructure.
