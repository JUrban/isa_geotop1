(** from \<S>3 Theorem 3 (geotop.tex:762)
    LATEX VERSION: Let J be a polygon in R^2, let I be the interior of J, and let K be a
      triangulation of \<bar>I\<close>. If K has more than one 2-simplex, then K has a free 2-simplex. **)
theorem Theorem_GT_3_3:
  fixes J :: "(real^2) set" and K :: "(real^2) set set"
  assumes hJ: "geotop_is_polygon J"
  assumes hK: "geotop_is_complex K"
  assumes hKI: "geotop_polyhedron K =
    closure_on UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
  assumes hcard: "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2} > 1"
  shows "\<exists>\<sigma>\<^sub>2. geotop_free_2_simplex K J \<sigma>\<^sub>2"
proof -
  have hcount:
    "card {\<sigma>\<^sub>2\<in>K. geotop_free_2_simplex K J \<sigma>\<^sub>2} \<ge> 2"
    by (rule geotop_polygon_disk_free_2simplex_count_ge2_prefix
        [OF hJ hK hKI hcard])
  have hnonempty:
    "{\<sigma>\<^sub>2\<in>K. geotop_free_2_simplex K J \<sigma>\<^sub>2} \<noteq> {}"
    using hcount by (by100 force)
  show ?thesis
    using hnonempty by (by100 blast)
