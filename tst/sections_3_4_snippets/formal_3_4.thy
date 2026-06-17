(** from \<S>3 Theorem 4 (geotop.tex:782)
    LATEX VERSION: Let J be a polygon in R^2. Then there is a homeomorphism h: R^2 \<leftrightarrow> R^2,
      such that h(J) is the frontier of a 2-simplex. **)
theorem Theorem_GT_3_4:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "\<exists>(h :: real^2 \<Rightarrow> real^2) (\<sigma> :: (real^2) set).
                 top1_homeomorphism_on UNIV geotop_euclidean_topology
                 UNIV geotop_euclidean_topology h
          \<and> geotop_simplex_dim \<sigma> 2
          \<and> h ` J = geotop_frontier UNIV geotop_euclidean_topology \<sigma>"
  (** Moise proof (geotop.tex:783): Let I = Int J; K = triangulation of \<bar>I\<close>.
      Any free 2-simplex of K can be removed by a homeomorphism R\<^sup>2 \<leftrightarrow> R\<^sup>2.
      Case 1: v\<^sub>0v\<^sub>1v\<^sub>2 free with intersection only edge v\<^sub>0v\<^sub>2 in Fr|K|; fold v\<^sub>1
              along an extended quadrilateral (Fig 3.3). Reduces #2-simplexes by 1.
      Case 2: v\<^sub>0v\<^sub>1v\<^sub>2 free with intersection = v\<^sub>0v\<^sub>1 \<union> v\<^sub>1v\<^sub>2 in Fr|K|; use inverse.
      By induction on #2-simplexes: eventually K reduces to a single 2-simplex \<sigma>
      whose frontier is the image of J. **)
