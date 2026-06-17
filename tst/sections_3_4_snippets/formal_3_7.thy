(** from \<S>3 Theorem 7 (geotop.tex:824)
    LATEX VERSION: Let J be a polygon in R^2 with interior I, and let U be an open set
      containing \<bar>I\<close>. Then there is a homeomorphism h: R^2 \<leftrightarrow> R^2 such that
      (1) h(J) is the frontier of a 2-simplex, and (2) h|(R^2 - U) is the identity.
    Moise proof (geotop.tex:826): \"In the proof of Theorem 4, we choose our
    homeomorphisms so that each of them satisfies (2).\" I.e., the induction in
    3_4 can be run with each step's homeomorphism having support inside U. **)
theorem Theorem_GT_3_7:
  fixes J U :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  assumes hU_open: "U \<in> geotop_euclidean_topology"
  assumes hI_sub_U: "closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J) \<subseteq> U"
  shows "\<exists>h \<sigma>. top1_homeomorphism_on UNIV geotop_euclidean_topology
                 UNIV geotop_euclidean_topology h
          \<and> geotop_simplex_dim \<sigma> 2
          \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>
          \<and> (\<forall>P\<in>UNIV - U. h P = P)"
proof -
  (** (1) Re-run the induction of Theorem 3_4 (reducing the triangulation K to one 2-simplex)
         but at each folding step choose the supporting quadrilateral/ triangle to lie
         entirely inside U. Each such fold is a PLH with support in U. **)
  have h_support_in_U:
    "\<exists>h \<sigma>. top1_homeomorphism_on UNIV geotop_euclidean_topology
              UNIV geotop_euclidean_topology h
          \<and> geotop_simplex_dim \<sigma> 2
          \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>
          \<and> (\<forall>P\<in>UNIV - U. h P = P)"
  proof -
    obtain K where hK: "geotop_is_complex K" and hK_fin: "finite K"
      and hK_poly:
        "geotop_polyhedron K =
          closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
      using Theorem_GT_2_2[OF hJ] by (by100 blast)
    show ?thesis
      using geotop_polygon_disk_free_triangle_fold_normalization_supported_prefix
        [OF hJ hK hK_fin hK_poly hU_open hI_sub_U]
      by (by100 blast)
