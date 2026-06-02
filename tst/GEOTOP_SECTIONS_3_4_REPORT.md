# GeoTop Formalization Report for Sections 3 and 4

Date: 2026-06-02

This report summarizes the current formalization status for Sections 3 and 4
of `geotop.tex` in the active section-specific development branch.

## Status

Sections 3 and 4 are not yet sorry-free.  They are, however, isolated in a
fast cached development stack and the current active session builds after the
latest merge from `main`.

Evidence checked locally:

- Pulled/merged colleague `main` at commit `3e463c3b` into
  `codex-dev34-cache`; the merge commit is `2b0745a0`.
- `/project/bin/isabelle build -d . -d dev34_pre -d dev34_prefix -d dev34_facts
  -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts -d dev34_graphwork
  -d dev34_openstar -d dev34 GeoTop34Dev` passed.
- Because the merge touched base files, that post-merge rebuild took
  `0:11:32` elapsed overall; the final `GeoTop34Dev` theory itself ran in
  `0:00:07` elapsed once the caches were rebuilt.
- A scan of the target section-specific theories, excluding the intentionally
  dirty `dev34_pre/GeoTop.thy` mirror, finds 18 remaining executable `sorry`s:
  10 in `dev34_prefix/GeoTop_3_4_Prefix.thy` and 8 in
  `dev34/GeoTop_3_4.thy`.

The practical consequence is that Sections 3 and 4 have a working, green
development session, but completion still requires eliminating the listed
proof holes.  The main open cluster is the book Lemma 5/Theorem 4.8-4.9
vertex-star argument and the boundary equality part of Theorem 4.9.

## Layout

The section 3-4 development is split across cached sessions:

- `dev34_pre/GeoTop.thy`: dirty cached import of the original `GeoTop` script;
  it still contains the original later-section sketches and is not used as the
  target sorry count for Sections 3 and 4.
- `dev34_prefix/GeoTop_3_4_Prefix.thy`: Section 3 and early Section 4
  statements and proofs.
- `dev34_facts/GeoTop_3_4_Facts.thy`: Section 4 Jordan-curve facts and local
  manifold helpers.
- `dev34_workfacts`, `dev34_linkfacts`, `dev34_graphfacts`,
  `dev34_graphwork`, and `dev34_openstar`: supporting cached work for links,
  graph/edge facts, and open-star neighborhoods.
- `dev34/GeoTop_3_4.thy`: active Section 4 manifold/star work and the final
  layer of the section-specific stack; it currently contains 8 executable
  `sorry`s.

## Section 3 Table

| Book item | Book statement, abbreviated | Isabelle counterpart | File |
| --- | --- | --- | --- |
| Theorem 3.1 | Simplexes with matched vertex sets admit a simplicial homeomorphism carrying each vertex to its assigned image. | `Theorem_GT_3_1` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 3.2 | In the equal-dimensional case, the simplex homeomorphism extends to a homeomorphism of the whole Euclidean space. | `Theorem_GT_3_2` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 3.3 | A triangulated polygonal disk with more than one 2-simplex has a free 2-simplex. | `Theorem_GT_3_3` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 3.4 | Every polygon in `R^2` is carried by a plane homeomorphism to the frontier of a 2-simplex. | `Theorem_GT_3_4` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 3.5 | Any two polygons in `R^2` are equivalent by a plane homeomorphism. | `Theorem_GT_3_5` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 3.6 | A polygon bounds a topological 2-cell. | `Theorem_GT_3_6` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 3.7 | The polygon-to-simplex homeomorphism can be chosen fixed outside a prescribed open neighborhood of the polygonal disk. | `Theorem_GT_3_7` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |

## Section 4 Table

| Book item | Book statement, abbreviated | Isabelle counterpart | File |
| --- | --- | --- | --- |
| Theorem 4.1 | Distinct components of an open Euclidean set are separated by disjoint open subsets containing the chosen points. | `Theorem_GT_4_1` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 4.2 | An arc across a polygonal disk separates the polygon interior into the two expected open sides. | `Theorem_GT_4_2` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 4.3 | A topological 1-sphere in `R^2` separates the plane. | `Theorem_GT_4_3` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 4.4 | Two disjoint arcs from opposite boundary points of a polygonal disk leave `Q` and `S` in the frontier of the same component. | `Theorem_GT_4_4` | `dev34_prefix/GeoTop_3_4_Prefix.thy` |
| Theorem 4.5 | No arc separates `R^2`. | `Theorem_GT_4_5` | `dev34_facts/GeoTop_3_4_Facts.thy` |
| Theorem 4.6 | For a 1-sphere `J` and a component `U` of `R^2 - J`, the frontier of `U` is `J`. | `Theorem_GT_4_6` | `dev34_facts/GeoTop_3_4_Facts.thy` |
| Theorem 4.7 | A 1-sphere in `R^2` has exactly one bounded complement component. | `Theorem_GT_4_7` | `dev34_facts/GeoTop_3_4_Facts.thy` |
| Theorem 4.8 | If `|K|` is a 2-manifold, then every vertex star of `K` is a combinatorial 2-cell. | `Theorem_GT_4_8` | `dev34/GeoTop_3_4.thy` |
| Theorem 4.9 | If `|K|` is a 2-manifold with boundary, then every vertex star is a combinatorial 2-cell and the manifold boundary is the union of edges incident to exactly one 2-simplex. | `Theorem_GT_4_9` | `dev34/GeoTop_3_4.thy` |
| Theorem 4.10 | For a closed 2-manifold with boundary in `R^2`, the manifold boundary equals the topological frontier. | `Theorem_GT_4_10` | `dev34/GeoTop_3_4.thy` |

## Current Open Proof Holes

The remaining target holes in `dev34_prefix/GeoTop_3_4_Prefix.thy` are:

- `Theorem_GT_3_3`: induction/strong free-simplex claim at line 844.
- `Theorem_GT_3_4`: base case and induction step for reducing a polygonal disk
  to one 2-simplex at lines 892 and 905.
- `Theorem_GT_3_7`: support-in-`U` version of the Section 3.4 induction at
  line 1362.
- `Theorem_GT_4_2`: final arc-separation disjointness/decomposition step at
  line 1715.
- `Theorem_GT_4_4`: brick-decomposition and frontier-component construction
  steps at lines 1810, 1818, 1828, 1839, and 1849.

The remaining target holes in `dev34/GeoTop_3_4.thy` are:

- `geotop_punctured_star_radial_endpoint_projection_dev34` at line 20.
- `geotop_2_manifold_vertex_star_punctured_connected_dev34` at line 620.
- `geotop_2_manifold_with_boundary_vertex_star_punctured_connected_dev34` at
  line 631.
- `geotop_vertex_star_cone_equiv_from_link_line_or_polygon_dev34` at line 749.
- `geotop_unique_incident_2simplex_semicircle_separates_chart_dev34` at line
  791.
- `geotop_three_incident_2simplex_sphere_not_separates_chart_dev34` at line
  813.
- `geotop_boundary_chart_three_incident_2simplex_contradiction_dev34` at line
  834.
- The boundary equality half of `Theorem_GT_4_9` at line 2588.

## Recent Progress

The active file now contains proved bridge lemmas for the book Lemma 5 route:

- `geotop_connected_punctured_neighborhood_cannot_cross_separation_dev34`
- `geotop_link_radial_segment_in_star_dev34`
- `geotop_link_point_ne_vertex_dev34`
- `geotop_radial_point_ne_vertex_dev34`
- `geotop_link_radial_tail_in_punctured_star_dev34`
- `geotop_punctured_star_separation_side_meets_vertex_neighborhood_dev34`

These formalize the radial part of Moise's argument: a separation side of the
punctured vertex star accumulates at the vertex along radial segments from the
link.  This is intended to feed into the remaining proof that a plane or
half-plane chart provides a connected punctured neighborhood, contradicting a
separation of the punctured star.

## Important Supporting Material

Important cached helpers include:

- `geotop_complex_vertex_star_neighborhood_dev34`
- `geotop_open_star_open_in_subspace_locally_finite_dev34`
- `geotop_star_punctured_point_radial_to_link_dev34`
- `geotop_link_radial_endpoint_unique_dev34`
- `geotop_link_polyhedron_subset_punctured_star_polyhedron`
- `geotop_star_polyhedron_subset_polyhedron`
- `geotop_plane_chart_open_subset_connected_punctured_neighborhood`
- `geotop_plane_chart_point_complement_connected`
- `geotop_2_cell_open_subset_connected_punctured_neighborhood`
- `geotop_2_manifold_no_open_edge_rel_interior`
- `geotop_2_manifold_with_boundary_no_open_edge_rel_interior`
- `geotop_2_manifold_no_open_singleton`
- `geotop_2_manifold_with_boundary_no_open_singleton`

## Notes For Future Work

- The next book-aligned step is to finish the two punctured-star connectedness
  lemmas at lines 620 and 631 using the new side-accumulation bridge plus the
  plane/2-cell punctured-neighborhood lemmas.
- After that, Lemma 5 gives connected links, and the cone-over-link bridge at
  line 749 should be the next bottleneck for turning link shape into
  `geotop_comb_n_cell (geotop_star K v) 2`.
- Keep using the cached `GeoTop34Dev` build command from `CLAUDE.md`/the
  development notes; warm-cache final theory time is currently about 7 seconds,
  while base changes can force a much longer cold rebuild.
- If more named helpers are added, regenerate `THEOREMS_AND_DEFS.txt` and
  `STMT_INDEX.txt`.
