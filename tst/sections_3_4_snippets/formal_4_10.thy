(** from \<S>4 Theorem 10 (geotop.tex:1058)
    LATEX VERSION: Let M be a 2-manifold with boundary, lying in R^2. If M is closed, then
      Bd M = Fr M. **)
theorem Theorem_GT_4_10:
  fixes M :: "(real^2) set"
  assumes hM: "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes hMcl: "closedin_on UNIV geotop_euclidean_topology M"
  shows "geotop_manifold_boundary M (\<lambda>x y. norm (x - y)) =
         geotop_frontier UNIV geotop_euclidean_topology M"
  (** Moise proof (geotop.tex:1060): Two inclusions.
      (1) Since Fr M is closed, every point of M - Fr M has a locally Euclidean
          open neighborhood in M. Hence M - Fr M \<subseteq> Int M = M - Bd M, i.e. Bd M \<subseteq> Fr M.
      (2) M closed in R\<^sup>2 so Fr M \<subseteq> M. If P \<in> Fr M, then P does NOT have a locally
          Euclidean (plane-homeomorphic) open nbhd in M \<Rightarrow> by Invariance of Domain
          (Theorem 4 = our Theorem_GT_4_invariance_of_domain) would give such a nbhd
          open in R\<^sup>2, contradicting P \<in> Fr M. Hence Fr M \<subseteq> Bd M. **)
