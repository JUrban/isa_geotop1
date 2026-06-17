(** from \<S>3 Theorem 2 (geotop.tex:735)
    LATEX VERSION: In Theorem 1, if m = n, then there is a homeomorphism g: R^n \<leftrightarrow> R^n such
      that g|\<sigma>^n is a simplicial homeomorphism \<sigma>^n \<leftrightarrow> \<tau>^n. **)
theorem Theorem_GT_3_2:
  fixes V W :: "'a::euclidean_space set" and \<sigma> \<tau> :: "'a set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> n" and h\<tau>: "geotop_simplex_dim \<tau> n"
  assumes hV: "geotop_simplex_vertices \<sigma> V" and hW: "geotop_simplex_vertices \<tau> W"
  assumes h\<phi>_mem: "\<phi> \<in> V \<rightarrow>\<^sub>E W" and h\<phi>_bij: "bij_betw \<phi> V W"
  shows "\<exists>g. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology g
          \<and> g ` \<sigma> = \<tau>
          \<and> (\<forall>x\<in>\<sigma>. g x \<in> \<tau>) \<and> geotop_simplicial_on \<sigma> g \<tau>"
