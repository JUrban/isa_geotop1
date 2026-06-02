# GeoTop Formalization Report for Sections 3 and 4

Date: 2026-06-02

This report summarizes the current formalization status for Sections 3 and 4
of `geotop.tex`, following the same format as the current report through
Section 2.

## Status

Sections 3 and 4 are not yet sorry-free. They are isolated in a cached
development stack, and the current active section session has a successful
warm-cache build.

Evidence checked locally:

- A fetch of colleague `main` over HTTPS reached commit `eaaa9065` (`Export TFF
  problems for AlgTop sessions`). The relevant faster theorem-index
  generator commit, `0284ba9c` (`Speed up theorem index generation`), is already
  contained in the local branch.
- The fast `gen_index.sh` implementation is the Python single-pass version and
  still includes the local Section 3-4 theory stack. The refreshed theorem index
  ran in about half a second, while `gen_stmt_index.sh` ran in about two
  seconds.
- A warm-cache section build passed:
  `/project/bin/isabelle build -d . -d dev34_pre -d dev34_prefix -d dev34_facts
  -d dev34_workfacts -d dev34_linkfacts -d dev34_graphfacts -d dev34_graphwork
  -d dev34_openstar -d dev34 GeoTop34Dev`, with the outer command reporting
  `0:00:39 elapsed time`.
- The current committed branch tip before this report refresh is `b8edaea1`
  (`Prove GeoTop edge interior subsegment`).
- A scan of the target section-specific theories, excluding the intentionally
  dirty `dev34_pre/GeoTop.thy` mirror, finds 16 remaining executable `sorry`s:
  10 in `dev34_prefix/GeoTop_3_4_Prefix.thy` and 6 in
  `dev34/GeoTop_3_4.thy`.

The practical consequence is that Sections 3 and 4 have a working, green
development session with a much smaller local target surface than the original
monolithic script. Completion still requires eliminating the listed proof
holes. The compact cone-over-compact closedness lemma is proved, closing the
radial bad-endpoint closedness bottleneck. The broad vertex-star fan wrapper is
proved from a more explicit Figure 4.10 isomorphism helper. The one-sided and
three-sided chart contradictions are now narrowed to explicit domain-level
small semicircle/small circle construction lemmas plus a 2-cell/Jordan helper.
The major open clusters are the actual ordered Figure 4.10 construction, the
small semicircle/small circle domain constructions, the 2-cell/Jordan
contradiction, the remaining Theorem 4.9 converse plane-neighborhood
obligations, and several larger Section 3/early Section 4 prefix arguments.

## Layout

The Section 3-4 development is split across cached sessions:

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
  layer of the section-specific stack; it currently contains 6 executable
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
| Theorem 4.8 | If the underlying polyhedron of `K` is a 2-manifold, then every vertex star of `K` is a combinatorial 2-cell. | `Theorem_GT_4_8` | `dev34/GeoTop_3_4.thy` |
| Theorem 4.9 | If the underlying polyhedron of `K` is a 2-manifold with boundary, then every vertex star is a combinatorial 2-cell and the manifold boundary is the union of edges incident to exactly one 2-simplex. | `Theorem_GT_4_9` | `dev34/GeoTop_3_4.thy` |
| Theorem 4.10 | For a closed 2-manifold with boundary in `R^2`, the manifold boundary equals the topological frontier. | `Theorem_GT_4_10` | `dev34/GeoTop_3_4.thy` |

## Current Open Proof Holes

The remaining target holes in `dev34_prefix/GeoTop_3_4_Prefix.thy` are:

- `Theorem_GT_3_3`: induction/strong free-simplex claim at line 844.
- `Theorem_GT_3_4`: base case and induction step for reducing a polygonal disk
  to one 2-simplex at lines 892 and 905.
- `Theorem_GT_3_7`: supported polygon-to-simplex homeomorphism, fixed outside
  the prescribed open neighborhood, at line 1362.
- `Theorem_GT_4_2`: final arc-separation disjointness/decomposition step at
  line 1715.
- `Theorem_GT_4_4`: brick-decomposition and frontier-component construction
  steps at lines 1810, 1818, 1828, 1839, and 1849.

The remaining target holes in `dev34/GeoTop_3_4.thy` are:

- `geotop_vertex_star_standard_fan_isomorphism_from_finite_linear_link_line_or_polygon_dev34`
  at line 3201.
- `geotop_unique_incident_2simplex_small_semicircle_domain_separates_chart_dev34`
  at line 4001.
- `geotop_three_incident_2simplex_small_circle_domain_not_separates_chart_dev34`
  at line 4061.
- `geotop_2cell_chart_1sphere_complement_not_connected_dev34` at line 4197.
- `geotop_2simplex_opposite_side_shared_edge_rel_interior_subset_HOL_interior_union_dev34`
  at line 7910; this is the remaining analytic local-neighborhood step for
  the same-complex two-triangle shared-edge local disk model.
- `geotop_polygon_link_vertex_is_HOL_interior_polyhedron_dev34` at line 8266;
  this is the Figure 4.10 full-disk vertex-star local Euclidean-neighborhood
  branch of Theorem 4.9's boundary converse.

## Recent Progress

The active file now proves most of the radial and local connected-neighborhood
infrastructure used in Moise's Lemma 5 route. Recent proved helpers include:

- `geotop_connected_punctured_neighborhood_cannot_cross_separation_dev34`
- `geotop_link_radial_segment_in_star_dev34`
- `geotop_link_point_ne_vertex_dev34`
- `geotop_radial_point_ne_vertex_dev34`
- `geotop_link_radial_tail_in_punctured_star_dev34`
- `geotop_punctured_star_separation_side_meets_vertex_neighborhood_dev34`
- `geotop_2_manifold_open_subset_connected_punctured_neighborhood_dev34`
- `geotop_2_manifold_with_boundary_open_subset_connected_punctured_neighborhood_dev34`
- `geotop_2_manifold_vertex_star_punctured_connected_dev34`
- `geotop_2_manifold_with_boundary_vertex_star_punctured_connected_dev34`
- `geotop_punctured_star_radial_endpoint_choice_property_dev34`
- `geotop_radial_endpoint_choice_preimage_eq_cone_dev34`
- `geotop_punctured_star_radial_endpoint_projection_dev34`
- `geotop_link_open_radial_cone_open_in_punctured_star_dev34`
- `geotop_openin_norm_polyhedron_contains_relative_ball_dev34`
- `geotop_two_2simplex_shared_edge_vertices_affine_obtain_dev34`
- `geotop_edge_vertices_affine_hull_normal_form_dev34`
- `geotop_two_2simplex_shared_edge_vertices_normal_obtain_dev34`
- `geotop_2simplex_vertices_HOL_interior_explicit_dev34`
- `geotop_2simplex_positive_bary_in_HOL_interior_dev34`
- `geotop_2simplex_HOL_interior_positive_side_of_edge_line_dev34`
- `geotop_2simplex_HOL_interior_negative_side_of_edge_line_dev34`
- `geotop_2simplex_HOL_interior_subset_positive_side_of_edge_line_dev34`
- `geotop_2simplex_HOL_interior_subset_negative_side_of_edge_line_dev34`
- `geotop_two_2simplex_shared_edge_vertices_side_obtain_dev34`
- `geotop_edge_vertices_subset_affine_hull_dev34`
- `geotop_edge_vertices_subset_normal_line_dev34`
- `geotop_2simplex_HOL_interior_eq_rel_interior_dev34`
- `geotop_complex_distinct_2simplex_HOL_interiors_disjoint_dev34`
- `geotop_2simplex_vertices_affine_hull_UNIV_dev34`
- `geotop_2simplex_vertices_affine_coordinates_dev34`
- `geotop_2simplex_positive_side_affine_coordinate_positive_dev34`
- `geotop_2simplex_negative_side_affine_coordinate_positive_dev34`
- `geotop_real_positive_overlap_parameter_dev34`
- `geotop_2simplex_affine_coordinate_HOL_interiors_meet_dev34`

Since the previous report, the radial cone openness problem has been reduced
substantially. The current branch proves the subspace-open bridge, a finite
local carrier lemma for locally finite complexes, finite local-ball gluing, and
finite-carrier radial neighborhood reduction:

- `geotop_subspace_open_from_euclidean_ball_witness_dev34`
- `geotop_complex_point_finite_local_carrier_dev34`
- `geotop_finite_carrier_local_ball_glue_dev34`
- `geotop_finite_local_carrier_radial_cone_point_neighborhood_dev34`
- `geotop_euclidean_open_radial_cone_point_neighborhood_dev34`
- `geotop_euclidean_open_radial_cone_open_in_punctured_star_dev34`

The single-simplex radial obligation was split into the easy
off-simplex case and the harder on-simplex endpoint-control case. Current
helpers in that reduction include:

- `geotop_simplex_point_neighborhood_empty_if_notin_dev34`
- `geotop_radial_cone_simplex_point_neighborhood_at_member_dev34`
- `geotop_radial_endpoint_simplex_local_ball_control_dev34`
- `geotop_ball_avoids_closed_not_containing_allow_empty_dev34`
- `geotop_radial_bad_endpoint_cone_avoids_point_dev34`
- `geotop_radial_cone_over_compact_closed_dev34`
- `geotop_radial_bad_endpoint_cone_closed_dev34`

The compact cone-over-compact helper proves the general closedness of the image
of `{0..1} x C` under the affine cone map
`(s,y) |-> (1-s) *\<^sub>R v + s *\<^sub>R y`, assuming `compact C`, by reducing
to compactness of a continuous image.

The chart-local Section 4 statements have also been audited against the book
argument. The one-sided and three-sided chart contradictions first extract a
relative metric ball from the local chart neighborhood and then delegate to
explicit small semicircle/small circle construction lemmas:

- `geotop_unique_incident_2simplex_small_semicircle_domain_separates_chart_dev34`
- `geotop_three_incident_2simplex_small_circle_domain_not_separates_chart_dev34`
- `geotop_2cell_chart_1sphere_complement_not_connected_dev34`

Since the previous report, the image-side chart wrappers have been proved from
these narrower domain-level obligations. New proved helpers include:

- `top1_homeomorphism_on_subspace_image_dev34`
- `geotop_homeomorphism_image_arc_dev34`
- `geotop_homeomorphism_image_1sphere_dev34`
- `geotop_unique_incident_2simplex_small_semicircle_separates_chart_dev34`
- `geotop_three_incident_2simplex_small_circle_not_separates_chart_dev34`
- `geotop_boundary_2cell_chart_three_incident_2simplex_contradiction_dev34`

The cone-over-link bridge for Theorem 4.8 has likewise been narrowed. The
link-complex wrapper now proves the finite linear-graph hypotheses and delegates
the remaining book Figure 4.10 construction through focused helpers:

- `geotop_vertex_star_standard_fan_isomorphism_from_finite_linear_link_line_or_polygon_dev34`
- `geotop_vertex_star_standard_fan_model_from_finite_linear_link_line_or_polygon_dev34`
- `geotop_vertex_star_fan_model_from_finite_linear_link_line_or_polygon_dev34`

The last two wrappers are proved. The open content is the first helper: enumerate
the finite linear link as an ordered edge-chain or edge-cycle, subdivide the
frontier of a standard 2-simplex with the same ordered edge data, add the cone
vertex, and define the resulting simplicial isomorphism.

Since the previous report, the boundary-equality half of Theorem 4.9 has been
split further. The broad subset helper now proves its contradiction argument
from a carrier split, and the remaining content is named as two local chart
obligations: two distinct 2-simplexes of the same complex sharing an edge form
an ordinary Euclidean neighborhood along the edge interior, and a polygonal
link gives a full disk-star Euclidean neighborhood at the vertex. The
two-sided vertex-link branch is now proved: exact two-face incidence gives
degree two at every link vertex, connectedness from Lemma 5 makes the link a
single component, and the finite connected degree-two linear graph classifier
turns that component into a polygon. New proved helpers include
`geotop_link_vertices_face_count_two_incident_link_edge_card_dev34`,
`geotop_link_component_preserves_incident_edge_card_two_dev34`, and
`geotop_link_component_degree_two_polygon_witness_dev34`. The same-complex
two-triangle local model has also gained the proved face-lattice helper
`geotop_2simplex_face_containing_edge_eq_edge_or_simplex_dev34`: in a
2-simplex, a face containing an edge is either that edge or the full simplex.
Using it with `geotop_is_complex_intersection` now proves
`geotop_complex_two_2simplex_shared_edge_inter_eq_edge_dev34`, the exact
intersection statement for distinct same-complex 2-simplexes sharing an edge.
The next vertex-form step is also proved:
`geotop_two_2simplex_shared_edge_vertices_obtain_dev34` extracts common edge
vertices `a,b` and distinct opposite vertices `c,d` for the two 2-simplexes.
The affine prerequisite
`geotop_2simplex_opposite_vertex_notin_edge_affine_hull_dev34` is now proved:
the vertex opposite an edge in a 2-simplex is not on the affine line of that
edge. The edge-line containment helpers
`geotop_edge_vertices_subset_affine_hull_dev34` and
`geotop_edge_vertices_subset_normal_line_dev34` now record that the common edge
itself lies on the normal-form line used in the half-plane argument. The
ordinary-interior wrappers
`geotop_2simplex_HOL_interior_eq_rel_interior_dev34` and
`geotop_complex_distinct_2simplex_HOL_interiors_disjoint_dev34` convert the
standard complex relative-interior disjointness fact into the HOL-interior form
needed for the same-side contradiction. The coordinate helpers
`geotop_2simplex_vertices_affine_hull_UNIV_dev34` and
`geotop_2simplex_vertices_affine_coordinates_dev34` show that the first
triangle's vertices span the plane and give affine coordinates for arbitrary
points, setting up the same-side overlap construction. The sign-coordinate
helpers
`geotop_2simplex_positive_side_affine_coordinate_positive_dev34` and
`geotop_2simplex_negative_side_affine_coordinate_positive_dev34` prove that a
same-side opposite vertex has positive affine coordinate at the first
triangle's opposite vertex. The real helper
`geotop_real_positive_overlap_parameter_dev34` chooses the small positive
parameter needed to keep both triangle-interior barycentric coordinate systems
strictly positive in the overlap construction. The construction itself is now
proved in `geotop_2simplex_affine_coordinate_HOL_interiors_meet_dev34`: the
small segment point lies in both HOL interiors after substituting the affine
coordinates of the second opposite vertex. The positive- and negative-side
wrappers
`geotop_2simplex_positive_same_side_HOL_interiors_meet_dev34` and
`geotop_2simplex_negative_same_side_HOL_interiors_meet_dev34` now expose this
as a direct same-side interior-overlap contradiction for the shared-edge local
model. The same-complex package
`geotop_complex_two_2simplex_shared_edge_vertices_opposite_sides_dev34` is now
proved: after extracting the shared-edge normal-coordinate data, complex
relative-interior disjointness rules out both same-side cases and leaves the
two opposite-side alternatives. The same-complex wrapper
`geotop_complex_two_2simplex_shared_edge_rel_interior_subset_HOL_interior_union_dev34`
is also proved from the newly isolated analytic helper
`geotop_2simplex_opposite_side_shared_edge_rel_interior_subset_HOL_interior_union_dev34`;
the remaining content is exactly the book's local Euclidean ball construction
for two opposite-side triangles along their common edge. The edge-coordinate
helper `geotop_edge_rel_interior_parameter_dev34` is now proved, giving the
open-segment parameter `0<t<1` for points of the shared edge relative interior.
The real positivity helper `geotop_real_positive_edge_probe_parameter_dev34` is
also proved; it chooses a small positive probe parameter that preserves the two
positive edge barycentric coordinates while creating a positive normal-side
coordinate, which is the next ingredient for the analytic local-neighborhood
step. The normal-probe helpers
`geotop_2simplex_positive_side_edge_normal_probe_in_HOL_interior_dev34` and
`geotop_2simplex_negative_side_edge_normal_probe_in_HOL_interior_dev34` are now
proved: from a point in the relative interior of the shared edge, a sufficiently
small move along the chosen normal direction into either strict side lands in
the HOL interior of the corresponding incident triangle. The package helper
`geotop_2simplex_opposite_side_shared_edge_normal_probes_in_HOL_interiors_dev34`
now combines these two one-sided probes for the opposite-side shared-edge
configuration. The containment helper
`geotop_edge_subset_2simplex_vertices_dev34` is now proved, recording that the
edge spanned by two triangle vertices is contained in the triangle. Its
immediate shared-edge consequence
`geotop_shared_edge_rel_interior_subset_two_2simplexes_dev34` is also proved,
placing the common edge relative interior inside both incident triangles.
The new helper `geotop_edge_rel_interior_small_subsegment_dev34` proves the
book's horizontal base step for the local diamond: every relative-interior edge
point has a small edge-direction subsegment remaining in the relative interior.
The follow-up helper
`geotop_shared_edge_small_subsegment_in_two_2simplexes_dev34` records that this
small subsegment lies in both incident triangles.

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
- `geotop_plane_chart_arc_complement_connected`
- `geotop_plane_chart_1sphere_complement_not_connected`
- `geotop_2_cell_open_subset_connected_punctured_neighborhood`
- `geotop_2_manifold_no_open_edge_rel_interior`
- `geotop_2_manifold_with_boundary_no_open_edge_rel_interior`
- `geotop_2_manifold_no_open_singleton`
- `geotop_2_manifold_with_boundary_no_open_singleton`
- `geotop_complex_simplex_closed`
- `geotop_complex_simplex_nonempty`
- `geotop_ball_avoids_closed_not_containing`
- `geotop_radial_endpoint_simplex_local_ball_control_dev34`
- `geotop_radial_cone_over_compact_closed_dev34`
- `geotop_radial_bad_endpoint_cone_avoids_point_dev34`

## Notes For Future Work

- The next book-aligned bottleneck for Theorems 4.8 and 4.9 is
  `geotop_vertex_star_standard_fan_isomorphism_from_finite_linear_link_line_or_polygon_dev34`.
  This is the formal Figure 4.10 step: subdivide the boundary of a 2-simplex to
  match the finite polygonal or broken-line link, add one interior vertex, cone
  the boundary subdivision, and obtain a simplicial isomorphism with a
  subdivision of the vertex star.
- The local chart contradiction wrappers are proved. The next step there is to
  formalize the book's small semicircle/small circle constructions in the chart
  domain and the isolated 2-cell/Jordan contradiction.
- The prefix holes in Theorems 3.3, 3.4, 3.7, 4.2, and 4.4 remain larger
  book-level arguments and should be attacked with the `sorry`-first skeleton
  workflow from `CLAUDE.md`.
- Keep using the cached `GeoTop34Dev` build command from `CLAUDE.md` and the
  development notes.
- If more named helpers are added, regenerate `THEOREMS_AND_DEFS.txt` and
  `STMT_INDEX.txt`.
