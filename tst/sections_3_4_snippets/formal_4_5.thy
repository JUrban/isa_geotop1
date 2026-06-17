(** from \<S>4 Theorem 5 (geotop.tex:976)
    LATEX VERSION: No arc separates R^2. **)
theorem Theorem_GT_4_5:
  fixes A :: "(real^2) set"
  assumes hA: "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  shows "top1_connected_on (UNIV - A)
           (subspace_topology UNIV geotop_euclidean_topology (UNIV - A))"
  (** Moise proof (geotop.tex:976): complement of an arc in R^n (n\<ge>2) is connected;
      follows from `top1_connected_complement_of_geotop_arc` since DIM(real^2)=2. **)
  by (rule top1_connected_complement_of_geotop_arc[OF hA]) simp
