# Goal Progress Recheck After Expert3 - 2026-06-09

## Status

The zero-target-`sorry` goal is still open. A fresh local scan with
`./check_dev34_fast.sh holes` reports 8 target holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34/GeoTop_3_4.thy:3322
dev34/GeoTop_3_4.thy:11427
dev34/GeoTop_3_4.thy:12645
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
```

Stable open packages:

```text
geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix
geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix
geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix
geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
geotop_polygon_arc_opposite_boundary_decomposition_prefix
geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34
geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34
geotop_one_side_simplex_semicircle_crosscut_separates_domain_dev34
```

No `sledgehammer` or `try0` markers appear in the target scan.

## Expert3 Reconciliation

`PLAN_zero_sorry-expert3.md` is still strategically useful, but some details
have moved. The old expert3 name
`geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`
now corresponds locally to the active hole inside
`geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`.

The audit's main warning remains correct: the last holes are package-sized
Moise picture arguments, not final tactic cleanup. The graph-prefix cycle split
is no longer the main blocker. The active Figure 4.10 blocker is now the exact
target boundary listing and source-target vertex map.

## Recent Progress

Recent commits:

```text
bbb6d7de Expose source successor edge orbit facts
e4aba0f8 Record boundary target bijection facts
f88a2d4a Record expert3 recheck progress report
39cb4297 Expose cyclic target boundary graph facts
6c1631a9 Record cyclic target boundary list facts
```

Inside `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`,
the proof now has the following target-side facts:

```text
geotop_complex_vertices F_B = S_B
set u_B_list = geotop_complex_vertices F_B
distinct u_B_list
length u_B_list = card (geotop_complex_vertices F_B)
geotop_is_linear_graph F_B
frontier sigma <= geotop_polyhedron F_B
open_segment a_sigma b_sigma <= geotop_polyhedron F_B
2 < card (geotop_complex_vertices F_B)
```

This is a real narrowing of the Figure 4.10 problem. The target subdivision no
longer merely contains the prescribed boundary points; its vertex set is now
controlled exactly. The remaining missing step is to turn that exact vertex
control into a cyclic boundary listing with adjacent-edge incidence, then build
the required source-target bijection satisfying `psi (v k) = u k`.

The latest two proof commits added two more pieces of infrastructure inside the
same active theorem:

```text
bij_betw psi_B (geotop_complex_vertices L) (geotop_complex_vertices F_B)
bij_betw ((!) u_B_list) {0..<length u_B_list} (geotop_complex_vertices F_B)
bij_betw ((!) u_B_list) {0..<card (geotop_complex_vertices L)}
  (geotop_complex_vertices F_B)
bij_betw ((!) u_B_list) {0..<card (geotop_complex_vertices F_B)}
  (geotop_complex_vertices F_B)
snd ((geotop_oriented_edge_successor L ^^ k) s_c)
  = closed_segment
      (fst ((geotop_oriented_edge_successor L ^^ k) s_c))
      (fst ((geotop_oriented_edge_successor L ^^ Suc k) s_c))
((lambda k. snd ((geotop_oriented_edge_successor L ^^ k) s_c)) ` {0..<p_c})
  = {e in L. geotop_is_edge e}
```

These facts expose both sides of the intended bijection, but they do not yet
solve the main incidence problem: `u_B_list` is still only an exact distinct
vertex list, not a proved cyclic boundary order.

## Current Blocker

The active theorem still stops before producing:

```text
exists F u psi.
  geotop_standard_boundary_cycle_listing_data_dev34 sigma p F u
  and bij_betw psi (geotop_complex_vertices L) (geotop_complex_vertices F)
  and (forall k<p. psi (v k) = u k)
```

The arbitrary list `u_B_list = [a_sigma] @ xs_B @ [b_sigma, c_sigma]` gives a
distinct exact vertex list, but it is not yet an ordered boundary-cycle proof.
The next useful proof step should either order the extra points along
`open_segment a_sigma b_sigma`, or prove a general finite linear boundary graph
cycle-listing lemma for `F_B` using the existing graph infrastructure.

The new source successor facts make the source side less opaque, but they also
confirm that the active obstacle is not source edge enumeration. The missing
piece is the target boundary adjacency/listing package, especially because the
current arbitrary ordering of `T_extra` along the open side has no adjacency
proof.

## Recommended Next Order

1. Finish `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`
   by deriving the cyclic target listing and matching bijection.
2. Reuse the same boundary-listing machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.
3. Return to `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   with the local-component bridge described by expert3.
4. Keep the semicircle, Section 3 subdisk/fold, D42, and D44 holes as named
   book packages; do not try to solve them by broad local proof search.

## Workflow Notes

Use the full indexes frequently:

```bash
rg -n "cyclic listing|boundary subdivision|bij_betw|finite_same_card_bij" \
  THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

Use focused checks for iteration:

```bash
./check_dev34_fast.sh focus dev34-cycle-realization
./check_dev34_fast.sh holes
```

The two index scripts already track local advice/report files and bounded
session logs. This report should be followed by:

```bash
bash gen_index.sh
bash gen_stmt_index.sh
```
