# GeoTop Sections 3-4 Progress Follow-up, 2026-06-08

## Current Status

The zero-sorry goal is still open. The focused target scan after the latest
verified work still reports 8 target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34/GeoTop_3_4.thy:858
dev34/GeoTop_3_4.thy:8001
dev34/GeoTop_3_4.thy:9203
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
```

The count has not changed in this checkpoint, but the active Figure 4.10
cycle package is better positioned for proof work. Three already-proved helper
lemmas were moved above
`geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`:

```text
geotop_subdivision_source_is_complex_dev34
geotop_comb_boundary_subset_complex_dev34
geotop_2simplex_comb_boundary_member_proper_face_dev34
```

The move followed the project workflow: add earlier `sorry` skeletons, run the
focused cycle check, restore the existing proofs, and run the same focused
check again. The final focused check passed:

```text
./check_dev34_fast.sh focus dev34-cycle-realization
```

The target hygiene check found no `sledgehammer` or `try0` markers in the
checked target layers.

## Relation to Expert Audits

The previous audits and `PLAN_zero_sorry-expert3.md` agree that the best next
sprint is the finite graph / Figure 4.10 cluster:

1. the graph-cache branch-vertex local cutpoint package;
2. the active Figure 4.10 boundary-cycle subdivision model;
3. the endpoint-chain boundary-arc fan package.

Expert3 specifically identified a theory-order problem in the Figure 4.10
package: useful boundary-subdivision helpers exist, but they were below the
book-step theorem that needs them. The latest committed work addresses that
blocker incrementally by moving the first three reusable helpers earlier.

## Next Useful Steps

Continue the same small-batch reordering for the remaining 2-simplex boundary
helpers needed by the active cycle theorem. The likely next candidates are:

```text
geotop_2simplex_face_complex_edge_unique_top_2face_dev34
geotop_2simplex_edge_face_in_comb_boundary_dev34
geotop_2simplex_vertex_face_in_comb_boundary_dev34
geotop_2simplex_proper_face_in_comb_boundary_dev34
geotop_2simplex_comb_boundary_finite_dev34
geotop_2simplex_comb_boundary_is_complex_dev34
geotop_2simplex_boundary_finite_points_subdivision_preserves_vertices_dev34
```

Each move should keep using the same bounded loop: skeleton first, focused
cycle check, restore old proof, focused cycle check, then regenerate indexes.
This is slower than a blind block move, but it has kept the build green and
avoids losing time to a large unlocalized theory-order failure.
