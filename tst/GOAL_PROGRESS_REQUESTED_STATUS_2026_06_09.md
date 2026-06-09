# GeoTop Sections 3-4 Goal Progress Status - 2026-06-09

## Current status

The zero-target-`sorry` goal is still open. A fresh local scan with
`./check_dev34_fast.sh holes` reports 8 target holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:3779
dev34/GeoTop_3_4.thy:11884
dev34/GeoTop_3_4.thy:13102
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

This is real progress from the older 17-hole and 10-hole states described in
the previous audits. It is not yet the final cleanup phase: the remaining
holes are named Moise picture packages, not isolated tactic failures.

## What changed since the expert audits

The expert3 report is still useful and matches the local status: the
graph-prefix cycle split that older audits treated as open is already closed
locally. The active Figure 4.10 problem has moved to the stronger
target-realization theorem
`geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`, rather
than the older cyclic-listing wrapper name used in some reports.

Recent verified work inside that theorem has exposed much more structure:

```text
source successor-orbit vertex membership
source successor-orbit edge membership
source vertex/edge decomposition from the successor cycle
target boundary subdivision carrier equals the simplex frontier
target boundary subdivision carrier equals the three named sides
target vertex set equals the prescribed finite boundary set
target vertex/edge decomposition
target vertex containment in the frontier and named sides
target connected finite linear graph structure
target degree-two vertex structure
target oriented successor cycle starting at a_sigma
target successor-orbit vertex set equals the target vertex set
target successor-orbit edge set equals the target edge set
```

The current active proof also has exact cardinality/bijection facts between
source vertices and target vertices, plus matching source and target successor
cycle decompositions. That means the remaining Figure 4.10 gap is narrower than
before: it is the ordered cyclic correspondence and adjacent-edge incidence for
the target subdivision, not the existence of enough target vertices or edges.

## Main active blocker

The main blocker remains:

```text
geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34
```

The proof originally had a distinct list
`u_B_list = [a_sigma] @ xs_B @ [b_sigma, c_sigma]` with the exact target vertex
set. However, `xs_B` is an arbitrary distinct listing of extra points on
`open_segment a_sigma b_sigma`. It has not been proved to be the boundary order
of the subdivision `F_B`, so it should not be used directly for the adjacent
edge clauses required by
`geotop_standard_boundary_cycle_listing_data_dev34`.

The latest verified increment gives a better route: use the target oriented
successor orbit of `F_B` as the ordered target boundary cycle. The next missing
piece is to relate that ordered target orbit to the source successor orbit and
then back to the original source listing `v`.

The right next proof step is therefore not another generic bijection fact. It
is an ordered boundary-subdivision/listing lemma, or an explicit construction
whose target list is ordered by construction.

## Recommended next order

1. Finish or sharply isolate the source-target successor-orbit matching lemma
   needed by `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`.
2. Reuse that same listing machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.
3. Return to `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   with the expert3 local-component bridge for three selected germs.
4. Keep the semicircle, Section 3 subdisk/fold, D42, and D44 obligations as
   named book packages, not ad hoc local tactic searches.

## Workflow and speed

The faster loop is now available and should stay the default:

```bash
rg -n "boundary listing|cyclic listing|closed_segment.*edge|vertex edge decomp" \
  THEOREMS_AND_DEFS.txt STMT_INDEX.txt
./check_dev34_fast.sh focus dev34-cycle-realization
./check_dev34_fast.sh holes
```

The index scripts already track local advice/report notes and session artifacts.
They were regenerated after the report/theory edits, so no script change was
needed for this file type.

## Bottom line

The project is approaching the goal structurally: the open set is small, named,
and repeatedly verified. It is not approaching completion linearly by wall-clock
time because each remaining hole compresses a substantial formal topology
argument. The best measure of progress from here is closure of the 8 named
packages, with the ordered Figure 4.10 boundary-listing package first.
