(** from Introduction: Theorem 4 - Invariance of domain (geotop.tex:206)
    LATEX VERSION: Let U be a subset of R^n, such that U is homeomorphic to R^n. Then U is open.
    Positioned here (rather than in the Introduction) so that the HOL-Analysis bridge lemmas
    \<open>geotop_euclidean_topology_eq_open_sets\<close>,
    \<open>top1_continuous_map_on_geotop_imp_continuous_on\<close>, and
    \<open>subspace_topology_self_carrier\<close> are in scope. The proof uses HOL's
    \<open>invariance_of_domain_gen\<close> on the inverse g = f\<^sup>-\<^sup>1: \<bbbR>\<^sup>n \<rightarrow> U. **)
theorem Theorem_GT_4_invariance_of_domain:
  fixes U :: "'a::euclidean_space set"
  assumes hhomeo: "top1_homeomorphism_on U
             (subspace_topology (UNIV::'a set) geotop_euclidean_topology U)
             (UNIV::'a set) geotop_euclidean_topology f"
  shows "U \<in> geotop_euclidean_topology"
proof -
