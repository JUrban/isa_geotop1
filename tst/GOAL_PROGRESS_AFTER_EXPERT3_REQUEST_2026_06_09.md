# GeoTop Sections 3-4 Progress Report After Expert3

Date: 2026-06-09
Branch: codex-dev34-cache

## Current Status

The zero-target-sorry goal is still open. A fresh local scan with
`./check_dev34_fast.sh holes` reports 8 target holes:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34/GeoTop_3_4.thy:4258
dev34/GeoTop_3_4.thy:12363
dev34/GeoTop_3_4.thy:13581
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

This is real progress from the older 17-hole and 10-hole audit states. It is
not final cleanup: each remaining hole is a named Moise book package, not a
small failed automation step.

## Expert Audit Reconciliation

The expert reports remain useful, especially expert3, but some names are now
stale relative to the local branch.

The graph-prefix cycle split that older reports treated as open is closed
locally. The active Figure 4.10 work is no longer best described as
`geotop_cyclic_vertex_listing_standard_boundary_subdivision_book_step_dev34`.
The remaining local hole has moved into the stronger theorem:

```text
geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34
```

The expert3 warning about ordered boundary listings is still the key diagnosis.
An arbitrary exact vertex list for the target boundary subdivision is not enough
for the adjacent-edge clauses. The proof needs an ordered cycle, preferably the
oriented successor orbit of the target subdivision `F_B`, and then a bridge from
that target successor orbit back to the source successor orbit and the original
source listing.

## Recent Verified Progress

Recent committed work inside
`geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34` has
already established substantial source and target structure:

```text
source successor-cycle decomposition
source successor vertex and edge orbit equalities
source successor state injectivity/cardinality facts
target boundary subdivision carrier and vertex-set control
target finite connected linear-graph facts
target degree-two facts
target successor-cycle decomposition
target successor vertex and edge orbit equalities
target standard boundary cycle listing data for the target successor orbit
source/target successor vertex cardinality bridge
finite bijection between source and target successor vertex sets
```

In this working tree there is also a newly extracted graph-prefix helper:

```text
geotop_degree_two_oriented_edge_successor_current_next_index_unique_prefix
```

It states that, in a degree-two linear graph successor orbit, two indices in the
injective period are equal if they have the same current successor vertex and
the same next successor vertex. This was verified by:

```bash
./check_dev34_fast.sh focus dev34-cycle-realization
```

That check rebuilt the relevant graph/prefix/facts/core caches and then
processed the active cycle-realization slice successfully.

## Main Remaining Gap

The main active gap is still ordered source-target cycle matching in:

```text
geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34
```

The proof has enough target vertices, target edges, successor-cycle data, and
cardinality/bijection facts. What remains is stronger than a set bijection:
the source listing and target successor listing must be related in the cyclic
order needed to transfer singleton and adjacent-edge cases.

The latest helper is a useful local order fact, but it is not by itself the full
solution. The next useful extraction is likely the stronger vertex-index
uniqueness/order lemma from the already closed graph split proof, or a direct
ordered construction of the target boundary subdivision list.

## Speed And Caching

The fast checker is helping, but verification is still expensive when editing a
high import such as `dev34_prefix_graph/GeoTop_3_4_Prefix_Graph.thy`: the focus
check has to refresh downstream prefix, facts, graph, open-star, core, and split
active caches before reaching the small active slice.

For faster iteration:

```bash
rg -n "successor.*index|current.*next|cyclic listing|boundary subdivision" \
  THEOREMS_AND_DEFS.txt STMT_INDEX.txt dev34 dev34_prefix_graph
./check_dev34_fast.sh focus dev34-cycle-realization
./check_dev34_fast.sh holes
```

The current index files already include advice/report entries and the current
named theorem inventory. The scripts should still be regenerated after this
report and the graph-prefix theory edit.

## Recommended Next Order

1. Use the new current/next index-uniqueness helper inside
   `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`.
2. Extract or prove the stronger ordered successor-orbit matching lemma needed
   to transfer adjacent-edge cases from source to target.
3. Reuse the same ordered listing machinery for
   `geotop_endpoint_oriented_chain_boundary_arc_fan_target_book_step_dev34`.
4. Return to `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix`
   with the expert3 local-component bridge for the three selected germs.
5. Keep the semicircle, Section 3 subdisk/fold, D42, and D44 obligations as
   named book packages rather than local proof-search targets.

## Bottom Line

The project is approaching the goal structurally: the remaining target set is
small, named, and repeatedly checked. It is not yet close in the sense of
"only tactics remain." The best immediate milestone is to close the ordered
Figure 4.10 source-target boundary-listing package, because that should also
pay down the endpoint fan package.
