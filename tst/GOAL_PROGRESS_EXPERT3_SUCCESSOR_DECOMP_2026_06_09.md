# Goal Progress After Expert3 And Successor Decomposition - 2026-06-09

## Current status

The zero-target-`sorry` goal is still open. A fresh local scan with
`./check_dev34_fast.sh holes` reports 8 target holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:3407
dev34/GeoTop_3_4.thy:11512
dev34/GeoTop_3_4.thy:12730
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

## Expert3 reconciliation

`PLAN_zero_sorry-expert3.md` remains useful, but some details are now stale.
The graph-prefix cycle split is already closed; the active Figure 4.10 problem
is now the target-side cyclic boundary-listing package inside
`geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`.

The expert3 warning is still the key diagnosis: the remaining holes are
package-sized Moise picture arguments, not routine tactic cleanup. Progress
should be measured by closing named packages, not by adding local bookkeeping
facts that leave the same package hole unchanged.

## Recent concrete progress

The latest proof increments inside
`geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34` exposed
more of the source successor cycle:

```text
listed source vertices occur in the oriented successor vertex orbit
listed source edges occur in the oriented successor edge orbit
listed source edges equal closed successor-orbit edge segments
L = singleton successor-orbit vertices union successor-orbit edges
```

Together with the earlier target-side work, the active theorem now has exact
source vertex/edge decomposition, exact target vertex-set control for `F_B`,
and bijections between source vertices and target vertices. This is real
narrowing, but the hole count did not change.

## Main blocker

The current active blocker is still:

```text
geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34
```

The proof has an exact distinct list
`u_B_list = [a_sigma] @ xs_B @ [b_sigma, c_sigma]`, but `xs_B` is only an
arbitrary distinct listing of extra points on `open_segment a_sigma b_sigma`.
That list has not been proved to be the cyclic boundary order of `F_B`, so it
does not yet provide the adjacent-edge facts required by
`geotop_standard_boundary_cycle_listing_data_dev34`.

The next useful step is to avoid treating this as a generic bijection problem.
It needs an ordered boundary-subdivision/listing lemma, or an explicit
construction of ordered points on the boundary side with adjacency facts built
in from the start.

## Recommended next order

1. Close or sharply isolate the target boundary listing problem for
   `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`.
2. Reuse the same ordered boundary-listing machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.
3. Return to `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   with the expert3 local-component bridge for three selected germs.
4. Keep the semicircle, Section 3 subdisk/fold, D42, and D44 holes as named
   book packages.

## Workflow notes

Use the full indexes frequently, especially before adding lemmas:

```bash
rg -n "boundary listing|cyclic listing|vertex edge decomp|closed_segment.*edge" \
  THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

For iteration speed, prefer:

```bash
./check_dev34_fast.sh focus dev34-cycle-realization
./check_dev34_fast.sh holes
```

Avoid broad recursive searches outside `tst`; the indexes already cover the
theories and local session reports.
