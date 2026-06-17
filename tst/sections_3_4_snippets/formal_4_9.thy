(** from \<S>4 Theorem 9 (geotop.tex:1052)
    LATEX VERSION: Let K be a complex such that M = |K| is a 2-manifold with boundary. Then
      K is a combinatorial 2-manifold with boundary, and Bd M is the union of the edges of K
      that lie in only one 2-simplex of K. **)
theorem Theorem_GT_4_9:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hKM: "geotop_n_manifold_with_boundary_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  shows "\<forall>v\<in>geotop_complex_vertices K. geotop_comb_n_cell (geotop_star K v) 2"
    and "geotop_manifold_boundary (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) =
         \<Union>{e\<in>K. geotop_is_edge e \<and> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1}"
  (** Moise proof (geotop.tex:1054): As in Theorem 8, #(2-simplexes containing
      an edge e) is 1 or 2 (L2-L4 reused). Hence each component of |L(v)| is
      a broken line (edges with 1 triangle) or a 1-sphere (all edges with 2).
      |L(v)| connected (L5). So |L(v)| is a single broken line or polygon. St v
      is a combinatorial 2-cell.
      For Bd |K| = \<Union>(edges in only 1 triangle): such edges are exactly the ones
      at the manifold boundary. **)
