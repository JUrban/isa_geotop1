(** from \<S>4 Theorem 6 (geotop.tex:996)
    LATEX VERSION: Let J be a 1-sphere in R^2, and let U be a component of R^2 - J. Then J = Fr U. **)
theorem Theorem_GT_4_6:
  fixes J U :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes hU: "\<exists>P\<in>UNIV - J. U = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
  shows "J = geotop_frontier UNIV geotop_euclidean_topology U"
  (** Moise proof (geotop.tex:996): J homeomorphic to unit sphere in real^2
      (via our bridges); U ∈ components(-J); apply HOL `Jordan_Brouwer_frontier`
      (DIM(real^2)=2); bridge back via `geotop_frontier_UNIV_eq_frontier`. **)
