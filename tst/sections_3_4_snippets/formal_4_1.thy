theorem Theorem_GT_4_1:
  fixes U :: "'a::real_normed_vector set"
  assumes hUopen: "U \<in> geotop_euclidean_topology"
  assumes hP: "P \<in> U" and hQ: "Q \<in> U"
  assumes hneq: "geotop_component_at UNIV geotop_euclidean_topology U P \<noteq>
                 geotop_component_at UNIV geotop_euclidean_topology U Q"
  shows "\<exists>V W. U = V \<union> W \<and> V \<inter> W = {} \<and>
           V \<in> geotop_euclidean_topology \<and> W \<in> geotop_euclidean_topology \<and>
           P \<in> V \<and> Q \<in> W"
  (** Moise proof (geotop.tex:867): V = C_P = comp_U(P); W = U - V. V is open by
      geotop_component_at_open_in_euclidean. W is open as the union of the open
      components comp_U(x) for x \<in> W. P \<in> V because {P} is connected in U. Q \<in> W
      because comp_U(Q) \<noteq> V forces disjointness by Theorem 1.16. **)
