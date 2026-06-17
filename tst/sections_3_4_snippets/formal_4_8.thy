(** from \<S>4 Theorem 8 (geotop.tex:1020)
    LATEX VERSION: Let K be a complex such that M = |K| is a 2-manifold. Then K is a
      combinatorial 2-manifold; i.e., every subcomplex St v is a combinatorial 2-cell. **)
theorem Theorem_GT_4_8:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hM: "geotop_n_manifold_on (geotop_polyhedron K) (\<lambda>x y. norm (x - y)) 2"
  shows "\<forall>v\<in>geotop_complex_vertices K. geotop_comb_n_cell (geotop_star K v) 2"
  (** Moise proof (geotop.tex:1022). Via five lemmas:
      L1: Every vertex lies in an edge (R\<^sup>2 has no isolated points).
      L2: Every edge lies in \<ge> 1 2-simplex (else interior point has a plane-nbhd
          inside Int(edge), contradicting \"no point separates plane\").
      L3: Every edge lies in \<ge> 2 2-simplexes (else a semicircle in the
          2-simplex separates a plane-nbhd, contradicting \"no arc separates R\<^sup>2\").
      L4: Every edge lies in \<le> 2 2-simplexes (else 2 semicircles form a
          1-sphere not separating its plane-nbhd, contradicting Jordan).
      L5: |L(v)| is connected (v does not separate its plane-nbhd |St v|).
      From L1: L(v) \<noteq> \<emptyset>. From L2-L4: each component of |L(v)| is a polygon.
      With L5: |L(v)| is a single polygon. Form simplicial homeomorphism
      between (St v, L(v)) and a standard cone over a polygon (Fig 4.10). **)
