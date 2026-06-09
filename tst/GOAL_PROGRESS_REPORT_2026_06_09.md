# Goal Progress Report - 2026-06-09

## Current status

The zero-target-`sorry` goal is not finished. The current local hole scan reports 8 target `sorry`s:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:9610
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:10047
dev34/GeoTop_3_4.thy:2396
dev34/GeoTop_3_4.thy:10501
dev34/GeoTop_3_4.thy:11719
```

The corresponding stable package names are:

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

There are no visible `sledgehammer` or `try0` markers in the checked target scan. The working tree has many unrelated untracked files outside the target edits; the recently touched target files are clean after the last commit.

## What improved

The previous expert audits were right that this is no longer broad exploratory work. The target stack is now split into focused layers, the graph-prefix cycle split has been closed, and active Figure 4.10 work has progressed through several concrete commits:

```text
dccc4607 Bound cycle target vertex count
3e5fff5e Prescribe boundary subdivision vertices
85003e21 Record open boundary edge reservoir
dadae502 Relate source anchors to boundary vertices
de675911 Identify triangle boundary vertices
e30b89ae Place triangle frontier in boundary carrier
2d858a61 Record expert3 progress checkpoint
```

The active Figure 4.10 theorem now has a standard boundary triangle, named target boundary vertices, a source-to-boundary anchor map, a reservoir of extra points on an open boundary edge, a prescribed finite target set `S_B`, and a subdivision `F_B` whose vertex set contains `S_B`. This is real progress toward the cyclic boundary target.

## Main blocker in the current active proof

The current active proof is stopped at `geotop_standard_boundary_cycle_listing_target_from_source_cases_dev34`.

The important limitation is that the available subdivision helper only proves that prescribed boundary points become vertices and that old boundary vertices are preserved. It does not prove that the resulting subdivision has no extra vertices. The target predicate needs an exact cyclic listing of all vertices of `F`, and the final isomorphism needs a bijection between the source vertices and the target vertices.

So the current obstacle is not just a missing tactic. It is an exact-realization issue:

```text
prescribed points become vertices
```

is weaker than:

```text
the subdivision vertices are exactly the prescribed cyclic target vertices
```

The next useful local lemma is therefore either an exact no-extra-vertices subdivision lemma for finite boundary point insertion, or a direct construction of the standard boundary cycle complex from an ordered boundary list.

## Audit-adjusted assessment

The expert reports are consistent with the local state:

* The project is approaching the goal in the sense that the hole count is small, named, and localized.
* It is not approaching the goal in the sense of "a few automation calls remain."
* The remaining 8 holes are package-sized Moise picture arguments.
* Moving a `sorry` deeper into a wrapper is not progress unless the package obligation is actually proved.

The finite graph / Figure 4.10 sprint remains the best short-term milestone, but the exact target subdivision issue must be solved before the current active theorem can close cleanly.

## Recommended next order

1. Finish the active Figure 4.10 exact boundary-cycle realization by proving either exact finite boundary subdivision or direct cyclic boundary complex construction.
2. Reuse that machinery for the endpoint boundary-arc fan target.
3. Close the graph-cache branch-vertex local cutpoint package.
4. Revisit the one-sided semicircle lemma, first checking whether the statement needs the stronger collar assumptions noted by the expert audit.
5. Finish the Section 3 subdisk transfer and support-controlled fold normalization packages.
6. Finish D42 through a reusable theta-separation lemma.
7. Finish D44 last as a regular-neighborhood / brick-transfer package.

## Process notes

Use the full generated indexes frequently:

```bash
rg -n "pattern" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
```

Keep using focused verification through `check_dev34_fast.sh`; broad rebuilds are too expensive for every iteration. After theory or report edits, regenerate the generated indexes before committing if theorem statements or indexable content changed. This report did not change theory content, so it does not require index regeneration.
