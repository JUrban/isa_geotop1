# GeoTop Sections 3-4 Current Status After Expert Audits, 2026-06-09

This report is based on a fresh local status refresh in `/project/tst`, the
current `CLAUDE.md` instructions, `PLAN_zero_sorry-expert.md` through
`PLAN_zero_sorry-expert3.md`, the generated index setup, and the current proof
files. I ignored the inactive colleague branch/status and used live local checks
as the source of truth.

## Current status

The zero-target-`sorry` goal is not complete. A fresh
`./check_dev34_fast.sh holes` scan reports seven raw target `sorry` lines:

```text
dev34_prefix/GeoTop_3_4_Prefix.thy:106
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:6664
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:8803
dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy:9933
dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy:3921
dev34/GeoTop_3_4.thy:14839
dev34/GeoTop_3_4.thy:14871
```

This is better than the older expert3 count of eight, but the remaining work is
still mathematical package work, not final automation cleanup. The active
standard-boundary cycle realization and the one-sided semicircle/collar package
are no longer in the live hole scan. The endpoint nonfinish package was split
into two explicit substeps, so the raw scan has seven lines but the stable
remaining package map is best read as six buckets.

## Remaining package buckets

1. `geotop_polygon_two_disjoint_endpoint_arcs_brick_component_transfer_prefix`
   in `dev34_prefix/GeoTop_3_4_Prefix.thy`.
   This is the Theorem 4.4 brick / regular-neighborhood / component-transfer
   package and remains the largest open bucket.

2. `geotop_polygon_disk_chord_subdisk_induction_transfer_free_count_prefix`
   in `dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy`.
   This is the Moise Figure 3.2 subdisk induction transfer: form the two side
   complexes, apply the smaller-disk induction hypotheses, and transfer free
   triangle witnesses back to the parent disk.

3. `geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix`
   in `dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy`.
   This is the support-controlled Section 3 fold-normalization induction. The
   current support-parametric shape should be preserved because it serves both
   unrestricted and local-supported uses.

4. `geotop_polygon_arc_opposite_boundary_theta_component_split_prefix`
   in `dev34_prefix_mid/GeoTop_3_4_Prefix_Mid.thy`.
   This is the D42 theta-separation package. The expert advice remains correct:
   close it by the Moise theta contradiction, not by broad component algebra.

5. `geotop_connected_split_side_three_germs_local_component_prefix` /
   `geotop_branch_vertex_local_disconnects_finite_linear_graph_prefix` in
   `dev34_prefix_graph/cache/GeoTop_3_4_Prefix_Graph_Cache.thy`.
   The branch-vertex radial-sector contradiction is staged, but the local
   component bridge is still under-specified as an abstract lemma. The next
   useful edit is to rethread the upstream arc-side split data or add the exact
   third-germ relation needed to produce one local component whose closure
   touches all three selected incident edge germs.

6. Endpoint nonfinish / boundary-arc fan in `dev34/GeoTop_3_4.thy`.
   The wrapper
   `geotop_endpoint_nonfinish_degree_and_boundary_arc_target_book_step_dev34`
   is now proved from two named substeps:
   `geotop_endpoint_nonfinish_degree_bound_book_step_dev34` and
   `geotop_endpoint_chain_boundary_arc_target_model_from_listing_book_step_dev34`.
   The target side must remain a same-length boundary-arc fan construction, not
   a full boundary-cycle shortcut.

## Are we approaching the goal?

Structurally, yes: the open work is now localized, named, and searchable. The
project is not in "almost done" tactic-cleanup mode, though. A single remaining
`sorry` may still hide a whole Moise book argument, especially D44, Section 3
fold normalization, and D42. The most honest progress metric is completed
packages with focused verification, not raw elapsed time or only raw line count.

The most encouraging recent progress is that earlier graph-cycle and
semicircle/collar targets are gone from the live hole scan, and the endpoint
work has been split into source-degree and target-model obligations. That makes
the next proof edits much less opaque.

## Search, cache, and iteration speed

The user's concern about full-index search is valid. Before introducing or
moving helper lemmas, search the whole generated index and the live source:

```bash
rg -n "pattern" THEOREMS_AND_DEFS.txt STMT_INDEX.txt
rg -n "pattern" dev34 dev34_prefix dev34_prefix_mid dev34_prefix_graph
```

The current `./check_dev34_fast.sh focus-status` shows fresh parent caches for
the main layers, but many split/slice caches are stale. The fastest practical
workflow is:

```bash
./check_dev34_fast.sh holes
./check_dev34_fast.sh focus-status
./check_dev34_fast.sh slice-hot dev34/GeoTop_3_4.thy TARGET_NAME
```

Prime or refresh only the active target slice, then stay on that package until a
real sublemma or package closes. Running broad checks after every small edit is
too expensive.

The two index generators already include `PLAN_zero_sorry-expert*.md`,
`*PROGRESS*.md`, `*REPORT*.md`, `*STATUS*.md`, `CLAUDE*.md`, active session
files, generated session files, and bounded session transcript files through
`index_theory_lib.py`. No script edit is needed for
`PLAN_zero_sorry-expert3.md`; normal regeneration is enough after this report.

## Recommended next move

Pick one of two focused routes and avoid switching every iteration:

1. Endpoint route: sharpen
   `geotop_endpoint_chain_boundary_arc_target_model_from_listing_book_step_dev34`
   into a named boundary-edge subdivision plus cone-fan target construction.
   This directly follows the latest expert3 advice and uses the existing
   endpoint listing/matching helpers.

2. Graph-cache route: strengthen
   `geotop_connected_split_side_three_germs_local_component_prefix` by carrying
   the missing third-germ/arc-side split data from the surrounding branch proof,
   then use the already-staged radial-sector contradiction.

D44 should wait until after smaller graph/endpoint packages close unless it
blocks a required dependency.
