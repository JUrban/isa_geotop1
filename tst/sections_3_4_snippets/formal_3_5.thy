(** from \<S>3 Theorem 5 (Schönflies for polygons) (geotop.tex:801)
    LATEX VERSION: Let J and J' be polygons in R^2. Then there is a homeomorphism h: R^2 \<leftrightarrow> R^2,
      J \<leftrightarrow> J'. **)
theorem Theorem_GT_3_5:
  fixes J J' :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J" and hJ': "geotop_is_polygon J'"
  shows "\<exists>h. top1_homeomorphism_on UNIV geotop_euclidean_topology
               UNIV geotop_euclidean_topology h
          \<and> h ` J = J'"
  (** Moise proof (geotop.tex:805): By Theorem 4, \<exists>f\<^sub>1 homeo R\<^sup>2 \<leftrightarrow> R\<^sup>2 with
      f\<^sub>1(J) = Fr \<sigma>\<^sup>2, and \<exists>f\<^sub>2 homeo R\<^sup>2 \<leftrightarrow> R\<^sup>2 with f\<^sub>2(J') = Fr \<tau>\<^sup>2.
      By Theorem 2 (simplicial homeo between 2-simplexes), \<exists>f\<^sub>3 homeo R\<^sup>2 \<leftrightarrow> R\<^sup>2
      with f\<^sub>3(\<sigma>\<^sup>2) = \<tau>\<^sup>2 (hence f\<^sub>3(Fr \<sigma>\<^sup>2) = Fr \<tau>\<^sup>2).
      Let h = f\<^sub>2\<^sup>-\<^sup>1 \<circ> f\<^sub>3 \<circ> f\<^sub>1. Then h(J) = J'. **)
