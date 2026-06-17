(** from \<S>4 Theorem 2 (geotop.tex:869)
    LATEX VERSION: Let I be the interior of a polygon in R^2, and let P, Q, R, S be points of
      Fr I, in cyclic order. Let A be an arc from P to R, lying in \<bar>I\<close>, with A \<inter> Fr I = {P,R}.
      Then I - A is the union of two disjoint open sets U_Q, U_S containing Q and S in
      their frontiers. **)
theorem Theorem_GT_4_2:
  fixes J :: "(real^2) set" and A :: "(real^2) set" and P Q R S :: "real^2"
  assumes hJ: "geotop_is_polygon J"
  assumes hP: "P \<in> J" and hQ: "Q \<in> J" and hR: "R \<in> J" and hS: "S \<in> J"
  assumes hcyc: "geotop_polygon_cyclic_order J P Q R S"
  assumes hcard: "card {P, Q, R, S} = 4"
  assumes hA: "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  assumes hAsub: "A \<subseteq> closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hAJ: "A \<inter> J = {P, R}"
  shows "\<exists>U\<^sub>Q U\<^sub>S. geotop_polygon_interior J - A = U\<^sub>Q \<union> U\<^sub>S \<and>
           U\<^sub>Q \<inter> U\<^sub>S = {} \<and>
           U\<^sub>Q \<in> geotop_euclidean_topology \<and> U\<^sub>S \<in> geotop_euclidean_topology \<and>
           Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q \<and>
           S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S"
  (** Moise proof (geotop.tex:872): By 3.5 we may assume \<bar>I\<close> is rectangular and
      P,Q,R,S in standard cyclic positions. Proof by contradiction: if Q' \<in> I near Q
      and S' \<in> I near S are in the same component of I - A, then \<exists> a broken line
      from Q' to S' in I - A, hence a broken line B from Q to S in \<bar>I\<close> - A
      intersecting Fr I only at Q,S. But then P,R lie in the same component of
      \<bar>I\<close> - B (since A is connected and A \<subseteq> \<bar>I\<close> - B), contradicting 2.8. **)
proof -
  have hD42_decomposition:
    "\<exists>U\<^sub>Q U\<^sub>S. U\<^sub>Q \<in> geotop_euclidean_topology \<and>
              U\<^sub>S \<in> geotop_euclidean_topology \<and>
              Q \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>Q \<and>
              S \<in> geotop_frontier UNIV geotop_euclidean_topology U\<^sub>S \<and>
              U\<^sub>Q \<inter> U\<^sub>S = {} \<and>
              geotop_polygon_interior J - A = U\<^sub>Q \<union> U\<^sub>S"
    by (rule geotop_polygon_arc_opposite_boundary_decomposition_prefix
        [OF hJ hP hQ hR hS hcyc hcard hA hAsub hAJ])
  show ?thesis
    using hD42_decomposition by (by100 blast)
