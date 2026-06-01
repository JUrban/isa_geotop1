theory GeoTop_Prefix
  imports "GeoTopDeps.GeoTopDeps" "HOL-Analysis.Jordan_Curve"
begin

hide_const (open) AlgTopCached.frontier


(* CHUNK_OUT: §2+ chunked IN for full-file verification.
   To chunk §2+ back OUT, reinstate the block-comment wrapper on the
   CHUNK_OUT_START and CHUNK_OUT_END markers. *)
(* CHUNK_OUT_START *)

section \<open>\<S>2 Separation properties of polygons in $\mathbf{R}^2$\<close>

(** from \<S>2: standard n-ball (geotop.tex:490)
    LATEX VERSION: B^n = {P | P \<in> R^n and d(P_0, P) \<le> 1}, where P_0 is the origin. **)
definition geotop_std_ball :: "'a::real_normed_vector set" where
  "geotop_std_ball = {P. norm P \<le> 1}"

(** from \<S>2: standard n-sphere (geotop.tex:494)
    LATEX VERSION: S^n = {P | P \<in> R^n and d(P_0, P) = 1}. **)
definition geotop_std_sphere :: "'a::real_normed_vector set" where
  "geotop_std_sphere = {P. norm P = 1}"

(** from \<S>2: n-sphere as an abstract space (geotop.tex:500)
    LATEX VERSION: A space (or set) S^n is an n-sphere if S^n is homeomorphic to S^n (standard). **)
definition geotop_is_n_sphere :: "'a::real_normed_vector set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> bool" where
  "geotop_is_n_sphere X TX n \<longleftrightarrow>
    is_topology_on X TX \<and>
    (\<exists>f. top1_homeomorphism_on X TX
           (geotop_std_sphere::'a set)
           (subspace_topology UNIV geotop_euclidean_topology geotop_std_sphere) f)"

(** from \<S>2: polygon (geotop.tex:500)
    LATEX VERSION: A polygon is a polyhedral 1-sphere. **)
definition geotop_is_polygon :: "'a::real_normed_vector set \<Rightarrow> bool" where
  "geotop_is_polygon J \<longleftrightarrow>
    (\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = J
       \<and> geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1)"

(** from \<S>2: triangulation of a polyhedron (geotop.tex:500)
    LATEX VERSION: For each complex K, K is called a triangulation of |K|. **)
text \<open>A triangulation of a set $M$ is a complex $K$ with $|K| = M$.
  Formalized inline as \<open>geotop_polyhedron K = M\<close>.\<close>

subsection \<open>Bridge \<open>real^2\<close> \<leftrightarrow> \<open>complex\<close>\<close>

text \<open>HOL-Analysis's planar Jordan-curve theorem (\<open>Jordan_curve\<close>) is stated for
  \<open>real \<Rightarrow> complex\<close> paths, with the key dependency \<open>Janiszewski\<close> also
  \<open>complex\<close>-typed. To use it for our \<open>real^2\<close> polygons, we set up a canonical
  homeomorphism \<open>R2_to_C\<close> between \<open>real^2\<close> and \<open>complex\<close> that preserves all
  the Euclidean structure we need (norm, openness, paths, components).\<close>

definition R2_to_C :: "real^2 \<Rightarrow> complex" where
  "R2_to_C v = Complex (v $ 1) (v $ 2)"

definition C_to_R2 :: "complex \<Rightarrow> real^2" where
  "C_to_R2 z = vector [Re z, Im z]"

definition R2_to_pair :: "real^2 \<Rightarrow> real \<times> real" where
  "R2_to_pair v = (v $ 1, v $ 2)"

definition pair_to_R2 :: "real \<times> real \<Rightarrow> real^2" where
  "pair_to_R2 p = (\<chi> i. if i = 1 then fst p else snd p)"

definition R2_to_S2 :: "real^2 \<Rightarrow> real \<times> real \<times> real" where
  "R2_to_S2 =
     (inv_into (top1_S2 - {north_pole}) stereographic_proj) \<circ> R2_to_pair"

lemma C_to_R2_R2_to_C: "C_to_R2 (R2_to_C v) = v"
  unfolding C_to_R2_def R2_to_C_def
  by (simp add: vec_eq_iff forall_2)

lemma R2_to_C_C_to_R2: "R2_to_C (C_to_R2 z) = z"
  by (simp add: C_to_R2_def R2_to_C_def)

lemma pair_to_R2_R2_to_pair: "pair_to_R2 (R2_to_pair v) = v"
  unfolding pair_to_R2_def R2_to_pair_def
  by (simp add: vec_eq_iff forall_2)

lemma R2_to_pair_pair_to_R2: "R2_to_pair (pair_to_R2 p) = p"
  unfolding pair_to_R2_def R2_to_pair_def
  by (by100 simp)

lemma R2_to_C_inj: "inj R2_to_C"
  using C_to_R2_R2_to_C by (metis injI)

lemma C_to_R2_inj: "inj C_to_R2"
  using R2_to_C_C_to_R2 by (metis injI)

lemma R2_to_pair_inj: "inj R2_to_pair"
  using pair_to_R2_R2_to_pair by (metis injI)

lemma R2_to_pair_surj: "surj R2_to_pair"
  using R2_to_pair_pair_to_R2 by (metis surjI)

lemma R2_to_pair_bij: "bij R2_to_pair"
  using R2_to_pair_inj R2_to_pair_surj by (simp add: bij_def)

lemma continuous_on_R2_to_pair: "continuous_on (UNIV::(real^2) set) R2_to_pair"
  unfolding R2_to_pair_def by (intro continuous_intros)

lemma continuous_on_pair_to_R2: "continuous_on (UNIV::(real \<times> real) set) pair_to_R2"
  unfolding pair_to_R2_def
  apply (rule continuous_on_vec_lambda)
  apply (case_tac "i = 1")
   apply (simp add: continuous_intros)
  apply (simp add: continuous_intros)
  done

lemma R2_pair_homeomorphism_UNIV:
  "homeomorphism (UNIV::(real^2) set) (UNIV::(real \<times> real) set)
     R2_to_pair pair_to_R2"
proof -
  show ?thesis
  proof (rule homeomorphismI)
    show "continuous_on UNIV R2_to_pair" by (rule continuous_on_R2_to_pair)
    show "continuous_on UNIV pair_to_R2" by (rule continuous_on_pair_to_R2)
    show "R2_to_pair ` UNIV \<subseteq> UNIV" by simp
    show "pair_to_R2 ` UNIV \<subseteq> UNIV" by simp
    show "\<And>x. x \<in> UNIV \<Longrightarrow> pair_to_R2 (R2_to_pair x) = x"
      by (rule pair_to_R2_R2_to_pair)
    show "\<And>y. y \<in> UNIV \<Longrightarrow> R2_to_pair (pair_to_R2 y) = y"
      by (rule R2_to_pair_pair_to_R2)
  qed
qed

lemma R2_pair_top1_homeomorphism_UNIV:
  "top1_homeomorphism_on (UNIV::(real^2) set)
     (geotop_euclidean_topology::(real^2) set set)
     (UNIV::(real \<times> real) set)
     (product_topology_on top1_open_sets top1_open_sets)
     R2_to_pair"
proof -
  have h_src_top:
    "is_topology_on (UNIV::(real^2) set)
       (geotop_euclidean_topology::(real^2) set set)"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have h_tgt_top:
    "is_topology_on (UNIV::(real \<times> real) set)
       (product_topology_on top1_open_sets top1_open_sets)"
    using product_topology_on_open_sets_real2 top1_open_sets_is_topology_on_UNIV
    by (by100 simp)
  have h_bij: "bij_betw R2_to_pair (UNIV::(real^2) set) (UNIV::(real \<times> real) set)"
    using R2_to_pair_bij unfolding bij_betw_def by (by100 simp)
  have hf_geo:
    "top1_continuous_map_on (UNIV::(real^2) set)
       (subspace_topology UNIV geotop_euclidean_topology (UNIV::(real^2) set))
       (UNIV::(real \<times> real) set)
       (subspace_topology UNIV geotop_euclidean_topology (UNIV::(real \<times> real) set))
       R2_to_pair"
    by (rule geotop_continuous_on_imp_top1_continuous_map_on
        [OF continuous_on_R2_to_pair subset_UNIV])
  have hf_top:
    "top1_continuous_map_on (UNIV::(real^2) set)
       (geotop_euclidean_topology::(real^2) set set)
       (UNIV::(real \<times> real) set)
       (product_topology_on top1_open_sets top1_open_sets)
       R2_to_pair"
    using hf_geo
    by (simp add: subspace_topology_UNIV_UNIV
                  geotop_euclidean_topology_eq_open_sets
                  product_topology_on_open_sets_real2)
  have hinv_eq: "inv_into (UNIV::(real^2) set) R2_to_pair = pair_to_R2"
  proof
    fix y :: "real \<times> real"
    show "inv_into (UNIV::(real^2) set) R2_to_pair y = pair_to_R2 y"
      using R2_to_pair_inj R2_to_pair_pair_to_R2
      by (metis UNIV_I inv_into_f_eq)
  qed
  have hg_geo:
    "top1_continuous_map_on (UNIV::(real \<times> real) set)
       (subspace_topology UNIV geotop_euclidean_topology (UNIV::(real \<times> real) set))
       (UNIV::(real^2) set)
       (subspace_topology UNIV geotop_euclidean_topology (UNIV::(real^2) set))
       pair_to_R2"
    by (rule geotop_continuous_on_imp_top1_continuous_map_on
        [OF continuous_on_pair_to_R2 subset_UNIV])
  have hg_top:
    "top1_continuous_map_on (UNIV::(real \<times> real) set)
       (product_topology_on top1_open_sets top1_open_sets)
       (UNIV::(real^2) set)
       (geotop_euclidean_topology::(real^2) set set)
       (inv_into (UNIV::(real^2) set) R2_to_pair)"
    using hg_geo
    by (simp add: hinv_eq subspace_topology_UNIV_UNIV
                  geotop_euclidean_topology_eq_open_sets
                  product_topology_on_open_sets_real2)
  show ?thesis
    unfolding top1_homeomorphism_on_def
    using h_src_top h_tgt_top h_bij hf_top hg_top by (by100 blast)
qed

lemma R2_S2_minus_north_homeomorphism_UNIV:
  "top1_homeomorphism_on (UNIV::(real^2) set)
     (geotop_euclidean_topology::(real^2) set set)
     (top1_S2 - {north_pole})
     (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
     R2_to_S2"
  unfolding R2_to_S2_def
  by (rule homeomorphism_comp[
      OF R2_pair_top1_homeomorphism_UNIV
         homeomorphism_inverse[OF stereographic_proj_homeomorphism]])

lemma R2_to_S2_image_subset_S2_minus_north:
  "R2_to_S2 ` A \<subseteq> top1_S2 - {north_pole}"
proof -
  have hbij: "bij_betw R2_to_S2 (UNIV::(real^2) set) (top1_S2 - {north_pole})"
    using R2_S2_minus_north_homeomorphism_UNIV
    unfolding top1_homeomorphism_on_def by (by100 blast)
  show ?thesis using hbij unfolding bij_betw_def by (by100 blast)
qed

lemma subspace_topology_S2_minus_north_trans:
  assumes "A \<subseteq> top1_S2 - {north_pole}"
  shows "subspace_topology (top1_S2 - {north_pole})
           (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) A
       = subspace_topology top1_S2 top1_S2_topology A"
  by (rule subspace_topology_trans[OF assms])

lemma R2_to_S2_inj_on_UNIV:
  "inj_on R2_to_S2 (UNIV::(real^2) set)"
proof -
  have hbij: "bij_betw R2_to_S2 (UNIV::(real^2) set) (top1_S2 - {north_pole})"
    using R2_S2_minus_north_homeomorphism_UNIV
    unfolding top1_homeomorphism_on_def by (by100 blast)
  show ?thesis using hbij unfolding bij_betw_def by (by100 blast)
qed

lemma R2_to_S2_image_Int:
  "R2_to_S2 ` A \<inter> R2_to_S2 ` B = R2_to_S2 ` (A \<inter> B)"
  using inj_on_image_Int[OF R2_to_S2_inj_on_UNIV subset_UNIV subset_UNIV, of A B]
  by (by100 simp)

subsection \<open>GeoTop arcs as top1 arcs\<close>

lemma geotop_euclidean_topology_UNIV_strict:
  "is_topology_on_strict (UNIV::'a::real_normed_vector set)
     (geotop_euclidean_topology::'a set set)"
proof (rule is_topology_on_strictI)
  show "is_topology_on (UNIV::'a set) (geotop_euclidean_topology::'a set set)"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  show "(geotop_euclidean_topology::'a set set) \<subseteq> Pow (UNIV::'a set)"
    by (by100 simp)
qed

lemma geotop_subspace_topology_strict:
  "is_topology_on_strict A
     (subspace_topology (UNIV::'a::real_normed_vector set)
        (geotop_euclidean_topology::'a set set) A)"
  by (rule subspace_topology_is_strict[OF geotop_euclidean_topology_UNIV_strict subset_UNIV])

lemma geotop_euclidean_topology_UNIV_hausdorff:
  "is_hausdorff_on (UNIV::'a::real_normed_vector set)
     (geotop_euclidean_topology::'a set set)"
proof -
  have hT: "is_topology_on (UNIV::'a set) (geotop_euclidean_topology::'a set set)"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  show ?thesis
    unfolding is_hausdorff_on_def
  proof (intro conjI ballI impI)
    show "is_topology_on (UNIV::'a set) (geotop_euclidean_topology::'a set set)"
      by (rule hT)
  next
    fix x y :: 'a
    assume hne: "x \<noteq> y"
    define r where "r = dist x y / 2"
    have hr_pos: "r > 0" using hne unfolding r_def by (by100 simp)
    have hUx: "ball x r \<in> (geotop_euclidean_topology::'a set set)"
      unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def by (by100 simp)
    have hUy: "ball y r \<in> (geotop_euclidean_topology::'a set set)"
      unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def by (by100 simp)
    have hdisj: "ball x r \<inter> ball y r = {}"
    proof (rule ccontr)
      assume "ball x r \<inter> ball y r \<noteq> {}"
      then obtain z where hz: "z \<in> ball x r" "z \<in> ball y r" by (by100 blast)
      have hlt: "dist x z + dist z y < dist x y"
        using hz unfolding r_def by (simp add: dist_commute)
      have "dist x y \<le> dist x z + dist z y"
        by (rule dist_triangle)
      thus False using hlt by (by100 linarith)
    qed
    show "\<exists>U V. neighborhood_of x (UNIV::'a set) geotop_euclidean_topology U \<and>
        neighborhood_of y (UNIV::'a set) geotop_euclidean_topology V \<and> U \<inter> V = {}"
      apply (rule exI[of _ "ball x r"])
      apply (rule exI[of _ "ball y r"])
      unfolding neighborhood_of_def
      using hUx hUy hr_pos hdisj by simp
  qed
qed

lemma geotop_arc_endpoints_imp_top1_arc:
  assumes "geotop_arc_endpoints A E"
  shows "top1_is_arc_on A
     (subspace_topology (UNIV::'a::real_normed_vector set) geotop_euclidean_topology A)"
proof -
  obtain f :: "real \<Rightarrow> 'a" where hf:
      "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
        (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1}) A
        (subspace_topology UNIV geotop_euclidean_topology A) f"
    using assms unfolding geotop_arc_endpoints_def by (by100 blast)
  have hI_set: "{t::real. 0 \<le> t \<and> t \<le> 1} = I_set"
    unfolding top1_unit_interval_def by (by100 auto)
  have hI_top:
      "subspace_topology (UNIV::real set) geotop_euclidean_topology
        {t::real. 0 \<le> t \<and> t \<le> 1} = I_top"
    unfolding top1_unit_interval_topology_def
    using hI_set by (simp add: geotop_euclidean_topology_eq_open_sets)
  have hf_top:
      "top1_homeomorphism_on I_set I_top A
        (subspace_topology UNIV geotop_euclidean_topology A) f"
    using hf hI_set hI_top by (by100 simp)
  have hstrict:
      "is_topology_on_strict A
        (subspace_topology (UNIV::'a set) geotop_euclidean_topology A)"
    by (rule geotop_subspace_topology_strict)
  show ?thesis
    unfolding top1_is_arc_on_def using hstrict hf_top by (by100 blast)
qed

lemma geotop_arc_endpoints_imp_top1_arc_endpoints:
  assumes "geotop_arc_endpoints A E"
  shows "top1_arc_endpoints_on A
     (subspace_topology (UNIV::'a::real_normed_vector set) geotop_euclidean_topology A) = E"
proof -
  obtain f :: "real \<Rightarrow> 'a" where hf:
      "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
        (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1}) A
        (subspace_topology UNIV geotop_euclidean_topology A) f"
      and hE: "E = {f 0, f 1}"
    using assms unfolding geotop_arc_endpoints_def by (by100 blast)
  have hI_set: "{t::real. 0 \<le> t \<and> t \<le> 1} = I_set"
    unfolding top1_unit_interval_def by (by100 auto)
  have hI_top:
      "subspace_topology (UNIV::real set) geotop_euclidean_topology
        {t::real. 0 \<le> t \<and> t \<le> 1} = I_top"
    unfolding top1_unit_interval_topology_def
    using hI_set by (simp add: geotop_euclidean_topology_eq_open_sets)
  have hf_top:
      "top1_homeomorphism_on I_set I_top A
        (subspace_topology UNIV geotop_euclidean_topology A) f"
    using hf hI_set hI_top by (by100 simp)
  have harc:
      "top1_is_arc_on A
        (subspace_topology (UNIV::'a set) geotop_euclidean_topology A)"
    by (rule geotop_arc_endpoints_imp_top1_arc[OF assms])
  have "top1_arc_endpoints_on A
      (subspace_topology (UNIV::'a set) geotop_euclidean_topology A) = {f 0, f 1}"
    by (rule arc_endpoints_are_boundary[
        OF geotop_euclidean_topology_UNIV_strict
           geotop_euclidean_topology_UNIV_hausdorff subset_UNIV harc hf_top])
  thus ?thesis using hE by (by100 simp)
qed

lemma R2_to_S2_geotop_arc_top1_arc:
  fixes A E :: "(real^2) set"
  assumes hA: "geotop_arc_endpoints A E"
      and hE: "E = {a, b}"
      and hab: "a \<noteq> b"
  shows "top1_is_arc_on (R2_to_S2 ` A)
      (subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` A))"
proof -
  let ?Y = "top1_S2 - {north_pole}"
  let ?TY = "subspace_topology top1_S2 top1_S2_topology ?Y"
  have hYsub: "?Y \<subseteq> top1_S2" by (by100 blast)
  have hY_strict: "is_topology_on_strict ?Y ?TY"
    by (rule subspace_topology_is_strict[OF top1_S2_is_topology_on_strict hYsub])
  have hY_haus: "is_hausdorff_on ?Y ?TY"
    using Theorem_17_11 top1_S2_is_hausdorff hYsub by (by100 blast)
  have hArc: "top1_is_arc_on A
      (subspace_topology (UNIV::(real^2) set) geotop_euclidean_topology A)"
    by (rule geotop_arc_endpoints_imp_top1_arc[OF hA])
  have hEp: "top1_arc_endpoints_on A
      (subspace_topology (UNIV::(real^2) set) geotop_euclidean_topology A) = {a, b}"
    using geotop_arc_endpoints_imp_top1_arc_endpoints[OF hA] hE by (by100 simp)
  have htransport:
      "top1_is_arc_on (R2_to_S2 ` A) (subspace_topology ?Y ?TY (R2_to_S2 ` A)) \<and>
       top1_arc_endpoints_on (R2_to_S2 ` A) (subspace_topology ?Y ?TY (R2_to_S2 ` A))
          = {R2_to_S2 a, R2_to_S2 b}"
    by (rule arc_endpoints_under_homeomorphism[
        OF geotop_euclidean_topology_UNIV_strict hY_strict
           geotop_euclidean_topology_UNIV_hausdorff hY_haus
           R2_S2_minus_north_homeomorphism_UNIV subset_UNIV hArc hEp hab])
  have himg_sub: "R2_to_S2 ` A \<subseteq> ?Y"
    by (rule R2_to_S2_image_subset_S2_minus_north)
  have htop_eq:
      "subspace_topology ?Y ?TY (R2_to_S2 ` A)
       = subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` A)"
    by (rule subspace_topology_S2_minus_north_trans[OF himg_sub])
  show ?thesis using htransport htop_eq by (by100 simp)
qed

lemma R2_to_S2_geotop_arc_top1_arc_endpoints:
  fixes A E :: "(real^2) set"
  assumes hA: "geotop_arc_endpoints A E"
      and hE: "E = {a, b}"
      and hab: "a \<noteq> b"
  shows "top1_arc_endpoints_on (R2_to_S2 ` A)
      (subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` A))
       = {R2_to_S2 a, R2_to_S2 b}"
proof -
  let ?Y = "top1_S2 - {north_pole}"
  let ?TY = "subspace_topology top1_S2 top1_S2_topology ?Y"
  have hYsub: "?Y \<subseteq> top1_S2" by (by100 blast)
  have hY_strict: "is_topology_on_strict ?Y ?TY"
    by (rule subspace_topology_is_strict[OF top1_S2_is_topology_on_strict hYsub])
  have hY_haus: "is_hausdorff_on ?Y ?TY"
    using Theorem_17_11 top1_S2_is_hausdorff hYsub by (by100 blast)
  have hArc: "top1_is_arc_on A
      (subspace_topology (UNIV::(real^2) set) geotop_euclidean_topology A)"
    by (rule geotop_arc_endpoints_imp_top1_arc[OF hA])
  have hEp: "top1_arc_endpoints_on A
      (subspace_topology (UNIV::(real^2) set) geotop_euclidean_topology A) = {a, b}"
    using geotop_arc_endpoints_imp_top1_arc_endpoints[OF hA] hE by (by100 simp)
  have htransport:
      "top1_is_arc_on (R2_to_S2 ` A) (subspace_topology ?Y ?TY (R2_to_S2 ` A)) \<and>
       top1_arc_endpoints_on (R2_to_S2 ` A) (subspace_topology ?Y ?TY (R2_to_S2 ` A))
          = {R2_to_S2 a, R2_to_S2 b}"
    by (rule arc_endpoints_under_homeomorphism[
        OF geotop_euclidean_topology_UNIV_strict hY_strict
           geotop_euclidean_topology_UNIV_hausdorff hY_haus
           R2_S2_minus_north_homeomorphism_UNIV subset_UNIV hArc hEp hab])
  have himg_sub: "R2_to_S2 ` A \<subseteq> ?Y"
    by (rule R2_to_S2_image_subset_S2_minus_north)
  have htop_eq:
      "subspace_topology ?Y ?TY (R2_to_S2 ` A)
       = subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` A)"
    by (rule subspace_topology_S2_minus_north_trans[OF himg_sub])
  show ?thesis using htransport htop_eq by (by100 simp)
qed

lemma R2_to_C_surj: "surj R2_to_C"
  using R2_to_C_C_to_R2 by (metis surjI)

lemma C_to_R2_surj: "surj C_to_R2"
  using C_to_R2_R2_to_C by (metis surjI)

lemma R2_to_C_bij: "bij R2_to_C"
  using R2_to_C_inj R2_to_C_surj by (simp add: bijI)

lemma C_to_R2_bij: "bij C_to_R2"
  using C_to_R2_inj C_to_R2_surj by (simp add: bijI)

lemma R2_to_C_inv: "inv R2_to_C = C_to_R2"
  using R2_to_C_inj C_to_R2_R2_to_C by (metis inv_equality R2_to_C_C_to_R2)

lemma C_to_R2_inv: "inv C_to_R2 = R2_to_C"
  using C_to_R2_inj R2_to_C_C_to_R2 by (metis inv_equality C_to_R2_R2_to_C)

lemma R2_to_C_add: "R2_to_C (u + v) = R2_to_C u + R2_to_C v"
  unfolding R2_to_C_def by (simp add: complex_add)

lemma R2_to_C_scaleR: "R2_to_C (a *\<^sub>R v) = a *\<^sub>R R2_to_C v"
  by (simp add: R2_to_C_def complex_eq_iff)

lemma C_to_R2_add: "C_to_R2 (z + w) = C_to_R2 z + C_to_R2 w"
  unfolding C_to_R2_def
  by (simp add: vec_eq_iff forall_2)

lemma C_to_R2_scaleR: "C_to_R2 (a *\<^sub>R z) = a *\<^sub>R C_to_R2 z"
  unfolding C_to_R2_def
  by (simp add: vec_eq_iff forall_2)

lemma norm_vec2_sq: "(norm (v::real^2))\<^sup>2 = (v $ 1)\<^sup>2 + (v $ 2)\<^sup>2"
proof -
  have huniv: "(UNIV :: 2 set) = {1, 2}" using UNIV_2 by blast
  have hne: "(1::2) \<noteq> 2" by simp
  have hsum: "(\<Sum>i\<in>UNIV. (v $ i)\<^sup>2) = (v $ 1)\<^sup>2 + (v $ 2)\<^sup>2"
    by (simp add: huniv hne)
  show ?thesis using hsum by (simp add: norm_vec_def L2_set_def)
qed

lemma R2_to_C_norm: "norm (R2_to_C v) = norm v"
  unfolding R2_to_C_def
  by (simp add: norm_vec2_sq complex_norm real_sqrt_unique)

lemma C_to_R2_norm: "norm (C_to_R2 z) = norm z"
  by (metis C_to_R2_R2_to_C R2_to_C_C_to_R2 R2_to_C_norm)

lemma bounded_linear_R2_to_C: "bounded_linear R2_to_C"
proof (rule bounded_linearI')
  fix u v :: "real^2" show "R2_to_C (u + v) = R2_to_C u + R2_to_C v" by (rule R2_to_C_add)
next
  fix r :: real and v :: "real^2" show "R2_to_C (r *\<^sub>R v) = r *\<^sub>R R2_to_C v" by (rule R2_to_C_scaleR)
qed

lemma bounded_linear_C_to_R2: "bounded_linear C_to_R2"
proof (rule bounded_linearI')
  fix u v :: complex show "C_to_R2 (u + v) = C_to_R2 u + C_to_R2 v" by (rule C_to_R2_add)
next
  fix r :: real and v :: complex show "C_to_R2 (r *\<^sub>R v) = r *\<^sub>R C_to_R2 v" by (rule C_to_R2_scaleR)
qed

lemma continuous_on_R2_to_C: "continuous_on UNIV R2_to_C"
  using bounded_linear_R2_to_C linear_continuous_on bounded_linear.linear by blast

lemma continuous_on_C_to_R2: "continuous_on UNIV C_to_R2"
  using bounded_linear_C_to_R2 linear_continuous_on bounded_linear.linear by blast

lemma homeomorphism_R2_C: "homeomorphism UNIV UNIV R2_to_C C_to_R2"
proof (rule homeomorphismI)
  show "continuous_on UNIV R2_to_C" by (rule continuous_on_R2_to_C)
  show "continuous_on UNIV C_to_R2" by (rule continuous_on_C_to_R2)
  show "R2_to_C ` UNIV \<subseteq> UNIV" by simp
  show "C_to_R2 ` UNIV \<subseteq> UNIV" by simp
  show "\<And>x. x \<in> UNIV \<Longrightarrow> C_to_R2 (R2_to_C x) = x" by (rule C_to_R2_R2_to_C)
  show "\<And>y. y \<in> UNIV \<Longrightarrow> R2_to_C (C_to_R2 y) = y" by (rule R2_to_C_C_to_R2)
qed

lemma C_to_R2_continuous_at: "continuous (at z) C_to_R2"
  using continuous_on_C_to_R2 by (simp add: continuous_on_eq_continuous_at)

lemma R2_to_C_continuous_at: "continuous (at v) R2_to_C"
  using continuous_on_R2_to_C by (simp add: continuous_on_eq_continuous_at)

lemma C_to_R2_vimage_eq_R2_to_C_image: "C_to_R2 -` S = R2_to_C ` S"
proof
  show "C_to_R2 -` S \<subseteq> R2_to_C ` S"
  proof
    fix z assume "z \<in> C_to_R2 -` S"
    hence "C_to_R2 z \<in> S" by simp
    moreover have "z = R2_to_C (C_to_R2 z)" by (simp add: R2_to_C_C_to_R2)
    ultimately show "z \<in> R2_to_C ` S" by blast
  qed
next
  show "R2_to_C ` S \<subseteq> C_to_R2 -` S"
  proof
    fix z assume "z \<in> R2_to_C ` S"
    then obtain v where hv: "v \<in> S" "z = R2_to_C v" by blast
    hence "C_to_R2 z = v" by (simp add: C_to_R2_R2_to_C)
    thus "z \<in> C_to_R2 -` S" using hv by simp
  qed
qed

lemma R2_to_C_vimage_eq_C_to_R2_image: "R2_to_C -` S = C_to_R2 ` S"
proof
  show "R2_to_C -` S \<subseteq> C_to_R2 ` S"
  proof
    fix v assume "v \<in> R2_to_C -` S"
    hence "R2_to_C v \<in> S" by simp
    moreover have "v = C_to_R2 (R2_to_C v)" by (simp add: C_to_R2_R2_to_C)
    ultimately show "v \<in> C_to_R2 ` S" by blast
  qed
next
  show "C_to_R2 ` S \<subseteq> R2_to_C -` S"
  proof
    fix v assume "v \<in> C_to_R2 ` S"
    then obtain z where hz: "z \<in> S" "v = C_to_R2 z" by blast
    hence "R2_to_C v = z" by (simp add: R2_to_C_C_to_R2)
    thus "v \<in> R2_to_C -` S" using hz by simp
  qed
qed

lemma R2_to_C_image_open: "open S \<Longrightarrow> open (R2_to_C ` S)"
proof -
  assume hS: "open S"
  have "open (C_to_R2 -` S)"
    using hS C_to_R2_continuous_at by (rule continuous_open_vimage)
  thus "open (R2_to_C ` S)" by (simp add: C_to_R2_vimage_eq_R2_to_C_image)
qed

lemma C_to_R2_image_open: "open S \<Longrightarrow> open (C_to_R2 ` S)"
proof -
  assume hS: "open S"
  have "open (R2_to_C -` S)"
    using hS R2_to_C_continuous_at by (rule continuous_open_vimage)
  thus "open (C_to_R2 ` S)" by (simp add: R2_to_C_vimage_eq_C_to_R2_image)
qed

lemma R2_to_C_image_bounded: "bounded (R2_to_C ` S) \<longleftrightarrow> bounded S"
proof
  assume "bounded (R2_to_C ` S)"
  then obtain B where hB: "\<forall>x \<in> R2_to_C ` S. norm x \<le> B"
    by (auto simp: bounded_iff)
  have "\<forall>x \<in> S. norm x \<le> B"
    using hB R2_to_C_norm by force
  thus "bounded S" by (auto simp: bounded_iff)
next
  assume "bounded S"
  then obtain B where hB: "\<forall>x \<in> S. norm x \<le> B"
    by (auto simp: bounded_iff)
  have "\<forall>y \<in> R2_to_C ` S. norm y \<le> B"
    using hB R2_to_C_norm by force
  thus "bounded (R2_to_C ` S)" by (auto simp: bounded_iff)
qed

lemma R2_to_C_image_connected: "connected (R2_to_C ` S) \<longleftrightarrow> connected S"
proof
  assume "connected (R2_to_C ` S)"
  hence "connected (C_to_R2 ` (R2_to_C ` S))"
    by (rule connected_continuous_image[OF continuous_on_subset[OF continuous_on_C_to_R2 subset_UNIV]])
  moreover have "C_to_R2 ` (R2_to_C ` S) = S"
    by (auto simp: image_iff C_to_R2_R2_to_C)
  ultimately show "connected S" by simp
next
  assume "connected S"
  thus "connected (R2_to_C ` S)"
    by (rule connected_continuous_image[OF continuous_on_subset[OF continuous_on_R2_to_C subset_UNIV]])
qed

lemma R2_to_C_image_compl: "R2_to_C ` (- S) = - R2_to_C ` S"
  using R2_to_C_bij by (rule bij_image_Compl_eq)

lemma C_to_R2_image_closure: "C_to_R2 ` closure S = closure (C_to_R2 ` S)"
proof
  show "C_to_R2 ` closure S \<subseteq> closure (C_to_R2 ` S)"
    using continuous_image_closure_subset[OF continuous_on_C_to_R2, of S] by simp
next
  show "closure (C_to_R2 ` S) \<subseteq> C_to_R2 ` closure S"
  proof
    fix v assume hv: "v \<in> closure (C_to_R2 ` S)"
    have "R2_to_C v \<in> R2_to_C ` closure (C_to_R2 ` S)"
      using hv by simp
    moreover have "R2_to_C ` closure (C_to_R2 ` S) \<subseteq> closure (R2_to_C ` (C_to_R2 ` S))"
      using continuous_image_closure_subset[OF continuous_on_R2_to_C, of "C_to_R2 ` S"] by simp
    moreover have "R2_to_C ` (C_to_R2 ` S) = S"
      by (auto simp: image_iff R2_to_C_C_to_R2)
    ultimately have "R2_to_C v \<in> closure S" by auto
    hence "C_to_R2 (R2_to_C v) \<in> C_to_R2 ` closure S" by simp
    thus "v \<in> C_to_R2 ` closure S" by (simp add: C_to_R2_R2_to_C)
  qed
qed

lemma C_to_R2_image_frontier: "C_to_R2 ` frontier S = frontier (C_to_R2 ` S)"
	proof -
	  have "C_to_R2 ` frontier S = C_to_R2 ` (closure S - interior S)"
	    by (simp add: Elementary_Topology.frontier_def)
  also have "\<dots> = C_to_R2 ` closure S - C_to_R2 ` interior S"
    using C_to_R2_inj image_set_diff by metis
  also have "\<dots> = closure (C_to_R2 ` S) - C_to_R2 ` interior S"
    by (simp add: C_to_R2_image_closure)
  also have "C_to_R2 ` interior S = interior (C_to_R2 ` S)"
  proof
    show "C_to_R2 ` interior S \<subseteq> interior (C_to_R2 ` S)"
      using C_to_R2_image_open[OF open_interior] interior_subset
      by (meson image_mono interior_maximal)
    show "interior (C_to_R2 ` S) \<subseteq> C_to_R2 ` interior S"
    proof
      fix v assume hv: "v \<in> interior (C_to_R2 ` S)"
      then obtain U where hU_open: "open U" and hUv: "v \<in> U" and hU_sub: "U \<subseteq> C_to_R2 ` S"
        by (auto simp: interior_def)
      have "R2_to_C ` U \<subseteq> S"
        using hU_sub by (auto simp: image_iff R2_to_C_C_to_R2)
      moreover have "open (R2_to_C ` U)" using hU_open R2_to_C_image_open by blast
      moreover have "R2_to_C v \<in> R2_to_C ` U" using hUv by simp
      ultimately have "R2_to_C v \<in> interior S"
        by (auto simp: interior_def)
      hence "C_to_R2 (R2_to_C v) \<in> C_to_R2 ` interior S" by simp
      thus "v \<in> C_to_R2 ` interior S" by (simp add: C_to_R2_R2_to_C)
    qed
  qed
	  finally show ?thesis by (simp add: Elementary_Topology.frontier_def)
qed

lemma R2_to_C_image_closure: "R2_to_C ` closure S = closure (R2_to_C ` S)"
proof
  show "R2_to_C ` closure S \<subseteq> closure (R2_to_C ` S)"
    using continuous_image_closure_subset[OF continuous_on_R2_to_C, of S] by simp
next
  show "closure (R2_to_C ` S) \<subseteq> R2_to_C ` closure S"
  proof
    fix z assume hz: "z \<in> closure (R2_to_C ` S)"
    have "C_to_R2 z \<in> C_to_R2 ` closure (R2_to_C ` S)"
      using hz by simp
    moreover have "C_to_R2 ` closure (R2_to_C ` S) \<subseteq> closure (C_to_R2 ` (R2_to_C ` S))"
      using continuous_image_closure_subset[OF continuous_on_C_to_R2, of "R2_to_C ` S"] by simp
    moreover have "C_to_R2 ` (R2_to_C ` S) = S"
      by (auto simp: image_iff C_to_R2_R2_to_C)
    ultimately have "C_to_R2 z \<in> closure S" by auto
    hence "R2_to_C (C_to_R2 z) \<in> R2_to_C ` closure S" by simp
    thus "z \<in> R2_to_C ` closure S" by (simp add: R2_to_C_C_to_R2)
  qed
qed

lemma R2_to_C_image_frontier: "R2_to_C ` frontier S = frontier (R2_to_C ` S)"
	proof -
	  have "R2_to_C ` frontier S = R2_to_C ` (closure S - interior S)"
	    by (simp add: Elementary_Topology.frontier_def)
  also have "\<dots> = R2_to_C ` closure S - R2_to_C ` interior S"
    using R2_to_C_inj image_set_diff by metis
  also have "\<dots> = closure (R2_to_C ` S) - R2_to_C ` interior S"
    by (simp add: R2_to_C_image_closure)
  also have "R2_to_C ` interior S = interior (R2_to_C ` S)"
  proof
    show "R2_to_C ` interior S \<subseteq> interior (R2_to_C ` S)"
      using R2_to_C_image_open[OF open_interior] interior_subset
      by (meson image_mono interior_maximal)
    show "interior (R2_to_C ` S) \<subseteq> R2_to_C ` interior S"
    proof
      fix z assume hz: "z \<in> interior (R2_to_C ` S)"
      then obtain U where hU_open: "open U" and hUz: "z \<in> U" and hU_sub: "U \<subseteq> R2_to_C ` S"
        by (auto simp: interior_def)
      have "C_to_R2 ` U \<subseteq> S"
        using hU_sub by (auto simp: image_iff C_to_R2_R2_to_C)
      moreover have "open (C_to_R2 ` U)" using hU_open C_to_R2_image_open by blast
      moreover have "C_to_R2 z \<in> C_to_R2 ` U" using hUz by simp
      ultimately have "C_to_R2 z \<in> interior S"
        by (auto simp: interior_def)
      hence "R2_to_C (C_to_R2 z) \<in> R2_to_C ` interior S" by simp
      thus "z \<in> R2_to_C ` interior S" by (simp add: R2_to_C_C_to_R2)
    qed
  qed
	  finally show ?thesis by (simp add: Elementary_Topology.frontier_def)
qed

lemma R2_to_C_path:
  "path c \<longleftrightarrow> path (R2_to_C \<circ> c)"
proof
  assume "path c"
  thus "path (R2_to_C \<circ> c)"
    using continuous_on_R2_to_C continuous_on_compose continuous_on_subset
    unfolding path_def by blast
next
  assume "path (R2_to_C \<circ> c)"
  hence "path (C_to_R2 \<circ> (R2_to_C \<circ> c))"
    using continuous_on_C_to_R2 continuous_on_compose continuous_on_subset
    unfolding path_def by blast
  moreover have "C_to_R2 \<circ> (R2_to_C \<circ> c) = c"
    by (auto simp: fun_eq_iff C_to_R2_R2_to_C)
  ultimately show "path c" by simp
qed

lemma R2_to_C_path_image:
  "path_image (R2_to_C \<circ> c) = R2_to_C ` path_image c"
  unfolding path_image_def by (auto simp: image_iff)

lemma R2_to_C_pathstart:
  "pathstart (R2_to_C \<circ> c) = R2_to_C (pathstart c)"
  unfolding pathstart_def by simp

lemma R2_to_C_pathfinish:
  "pathfinish (R2_to_C \<circ> c) = R2_to_C (pathfinish c)"
  unfolding pathfinish_def by simp

lemma R2_to_C_simple_path:
  "simple_path c \<longleftrightarrow> simple_path (R2_to_C \<circ> c)"
proof -
  have hinj: "inj R2_to_C" by (rule R2_to_C_inj)
  have hpath: "path c \<longleftrightarrow> path (R2_to_C \<circ> c)" by (rule R2_to_C_path)
  have h_inj_eq: "\<And>x y. R2_to_C x = R2_to_C y \<longleftrightarrow> x = y"
    using hinj by (auto dest: injD)
  have hloop: "loop_free c \<longleftrightarrow> loop_free (R2_to_C \<circ> c)"
    unfolding loop_free_def o_def by (simp add: h_inj_eq)
  show ?thesis unfolding simple_path_def using hpath hloop by blast
qed

theorem Jordan_curve_real2:
  fixes c :: "real \<Rightarrow> real^2"
  assumes hsp: "simple_path c" and hloop: "pathfinish c = pathstart c"
  obtains inner outer where
                "inner \<noteq> {}" "open inner" "connected inner"
                "outer \<noteq> {}" "open outer" "connected outer"
                "bounded inner" "\<not> bounded outer" "inner \<inter> outer = {}"
                "inner \<union> outer = - path_image c"
                "frontier inner = path_image c"
                "frontier outer = path_image c"
proof -
  define cC :: "real \<Rightarrow> complex" where "cC = R2_to_C \<circ> c"
  have hsp_C: "simple_path cC"
    using hsp R2_to_C_simple_path unfolding cC_def by blast
  have hloop_C: "pathfinish cC = pathstart cC"
    using hloop unfolding cC_def by (simp add: R2_to_C_pathstart R2_to_C_pathfinish)
  obtain innerC outerC where
	    h1: "innerC \<noteq> {}" "open innerC" "connected innerC"
	        "outerC \<noteq> {}" "open outerC" "connected outerC"
	        "bounded innerC" "\<not> bounded outerC" "innerC \<inter> outerC = {}"
	        "innerC \<union> outerC = - path_image cC"
	        "frontier innerC = path_image cC"
	        "frontier outerC = path_image cC"
	    by (rule Jordan_curve[OF hsp_C hloop_C])
  define inner :: "(real^2) set" where "inner = C_to_R2 ` innerC"
  define outer :: "(real^2) set" where "outer = C_to_R2 ` outerC"
  have h_path_eq: "path_image cC = R2_to_C ` path_image c"
    unfolding cC_def by (rule R2_to_C_path_image)
  have h_inner_ne: "inner \<noteq> {}" using h1(1) unfolding inner_def by simp
  have h_outer_ne: "outer \<noteq> {}" using h1(4) unfolding outer_def by simp
  have h_inner_open: "open inner"
    using h1(2) unfolding inner_def by (rule C_to_R2_image_open)
  have h_outer_open: "open outer"
    using h1(5) unfolding outer_def by (rule C_to_R2_image_open)
  have h_inner_conn: "connected inner"
  proof -
    have "connected (R2_to_C ` (C_to_R2 ` innerC))"
      using h1(3) by (simp add: image_image R2_to_C_C_to_R2)
    thus ?thesis using R2_to_C_image_connected unfolding inner_def by blast
  qed
  have h_outer_conn: "connected outer"
  proof -
    have "connected (R2_to_C ` (C_to_R2 ` outerC))"
      using h1(6) by (simp add: image_image R2_to_C_C_to_R2)
    thus ?thesis using R2_to_C_image_connected unfolding outer_def by blast
  qed
  have h_inner_bd: "bounded inner"
  proof -
    have "bounded (R2_to_C ` (C_to_R2 ` innerC))"
      using h1(7) by (simp add: image_image R2_to_C_C_to_R2)
    thus ?thesis using R2_to_C_image_bounded unfolding inner_def by blast
  qed
  have h_outer_unbd: "\<not> bounded outer"
  proof
    assume hbd: "bounded outer"
    have "bounded (R2_to_C ` (C_to_R2 ` outerC))"
      using hbd unfolding outer_def using R2_to_C_image_bounded by blast
    hence "bounded outerC" by (simp add: image_image R2_to_C_C_to_R2)
    thus False using h1(8) by simp
  qed
  have h_disjoint: "inner \<inter> outer = {}"
    unfolding inner_def outer_def
    using h1(9) C_to_R2_inj by (auto simp: image_iff dest: injD)
  have h_path_C_R2_union: "C_to_R2 ` path_image cC = path_image c"
  proof -
    have "C_to_R2 ` (R2_to_C ` path_image c) = path_image c"
      by (auto simp: image_iff C_to_R2_R2_to_C)
    thus ?thesis by (simp add: h_path_eq)
  qed
  have h_union: "inner \<union> outer = - path_image c"
  proof -
    have h_C_inv: "C_to_R2 ` innerC \<union> C_to_R2 ` outerC = C_to_R2 ` (- path_image cC)"
      using h1(10) image_Un by (metis image_Un)
    have h_compl: "C_to_R2 ` (- path_image cC) = - C_to_R2 ` path_image cC"
      using C_to_R2_bij by (rule bij_image_Compl_eq)
    show ?thesis unfolding inner_def outer_def
      using h_C_inv h_compl h_path_C_R2_union by simp
  qed
  have h_path_C_R2: "C_to_R2 ` path_image cC = path_image c"
  proof -
    have "C_to_R2 ` (R2_to_C ` path_image c) = path_image c"
      by (auto simp: image_iff C_to_R2_R2_to_C)
    thus ?thesis by (simp add: h_path_eq)
  qed
  have h_inner_fr: "frontier inner = path_image c"
  proof -
    have "frontier inner = frontier (C_to_R2 ` innerC)" unfolding inner_def by simp
    also have "\<dots> = C_to_R2 ` frontier innerC"
      by (rule C_to_R2_image_frontier[symmetric])
    also have "\<dots> = C_to_R2 ` path_image cC" using h1(11) by simp
    also have "\<dots> = path_image c" by (rule h_path_C_R2)
    finally show ?thesis .
  qed
  have h_outer_fr: "frontier outer = path_image c"
  proof -
    have "frontier outer = frontier (C_to_R2 ` outerC)" unfolding outer_def by simp
    also have "\<dots> = C_to_R2 ` frontier outerC"
      by (rule C_to_R2_image_frontier[symmetric])
    also have "\<dots> = C_to_R2 ` path_image cC" using h1(12) by simp
    also have "\<dots> = path_image c" by (rule h_path_C_R2)
    finally show ?thesis .
  qed
  show ?thesis
    using h_inner_ne h_outer_ne h_inner_open h_outer_open h_inner_conn h_outer_conn
          h_inner_bd h_outer_unbd h_disjoint h_union h_inner_fr h_outer_fr that
    by blast
qed

subsection \<open>Parametrising the unit circle in \<open>real^2\<close>\<close>

definition circle_path_R2 :: "real \<Rightarrow> real^2" where
  "circle_path_R2 t = vector [cos (2 * pi * t), sin (2 * pi * t)]"

lemma continuous_on_circle_path_R2_components:
  "continuous_on UNIV (\<lambda>t::real. cos (2 * pi * t))"
  "continuous_on UNIV (\<lambda>t::real. sin (2 * pi * t))"
  by (auto intro!: continuous_intros)

definition cp_C :: "real \<Rightarrow> complex" where
  "cp_C t = Complex (cos (2 * pi * t)) (sin (2 * pi * t))"

lemma circle_path_R2_via_C: "circle_path_R2 = C_to_R2 \<circ> cp_C"
  by (auto simp: fun_eq_iff circle_path_R2_def cp_C_def C_to_R2_def)

lemma continuous_on_cp_C: "continuous_on UNIV cp_C"
proof -
  have h1: "continuous_on UNIV (\<lambda>t::real. cos (2 * pi * t))"
    by (rule continuous_on_circle_path_R2_components(1))
  have h2: "continuous_on UNIV (\<lambda>t::real. sin (2 * pi * t))"
    by (rule continuous_on_circle_path_R2_components(2))
  have h3: "continuous_on UNIV (\<lambda>t. complex_of_real (cos (2 * pi * t)) + \<i> * complex_of_real (sin (2 * pi * t)))"
    using h1 h2 by (auto intro!: continuous_intros)
  have h4: "(\<lambda>t. complex_of_real (cos (2 * pi * t)) + \<i> * complex_of_real (sin (2 * pi * t))) = cp_C"
    by (auto simp: fun_eq_iff cp_C_def complex_eq_iff)
  show ?thesis using h3 by (subst h4[symmetric]) simp
qed

lemma path_circle_path_R2: "path circle_path_R2"
proof -
  have h_path_C: "path cp_C"
    using continuous_on_cp_C continuous_on_subset
    by (auto simp: path_def)
  have h_C_to_R2_path: "path (C_to_R2 \<circ> cp_C)"
    using h_path_C continuous_on_C_to_R2 continuous_on_compose continuous_on_subset
    unfolding path_def by blast
  show ?thesis using h_C_to_R2_path circle_path_R2_via_C by simp
qed

lemma pathstart_circle_path_R2: "pathstart circle_path_R2 = vector [1, 0]"
  unfolding pathstart_def circle_path_R2_def by simp

lemma pathfinish_circle_path_R2: "pathfinish circle_path_R2 = vector [1, 0]"
  unfolding pathfinish_def circle_path_R2_def by simp

lemma loop_circle_path_R2: "pathfinish circle_path_R2 = pathstart circle_path_R2"
  by (simp add: pathstart_circle_path_R2 pathfinish_circle_path_R2)

text \<open>The complex parametrisation \<open>cp_C\<close> traces out the unit circle in \<open>complex\<close>:
  this is a standard fact (Pythagoras + surjectivity from \<open>arctan\<close>).\<close>

lemma path_image_cp_C: "path_image cp_C = sphere (0::complex) 1"
proof
  show "path_image cp_C \<subseteq> sphere 0 1"
  proof
    fix z assume "z \<in> path_image cp_C"
    then obtain t where ht: "t \<in> {0..1}" "z = cp_C t"
      unfolding path_image_def by auto
    have hnorm: "(cmod z)\<^sup>2 = (cos (2 * pi * t))\<^sup>2 + (sin (2 * pi * t))\<^sup>2"
      using ht(2) unfolding cp_C_def by (simp add: cmod_def)
    also have "\<dots> = 1" by simp
    finally have h_sq: "(cmod z)\<^sup>2 = 1" .
    have "cmod z \<ge> 0" by simp
    hence "cmod z = 1"
      using h_sq by (metis abs_of_nonneg power2_eq_1_iff real_sqrt_abs real_sqrt_one)
    thus "z \<in> sphere 0 1" by simp
  qed
next
  show "sphere 0 1 \<subseteq> path_image cp_C"
  proof
    fix z :: complex assume hz: "z \<in> sphere 0 1"
    hence hcmod: "cmod z = 1" by simp
    obtain \<theta> where h\<theta>_lo: "0 \<le> \<theta>" and h\<theta>_hi: "\<theta> < 2 * pi"
                and h\<theta>_eq: "z = Complex (cos \<theta>) (sin \<theta>)"
      using hcmod complex_unimodular_polar by metis
    define t where "t = \<theta> / (2 * pi)"
    have hpi_pos: "(2::real) * pi > 0" by simp
    have ht_lo: "0 \<le> t"
      unfolding t_def using h\<theta>_lo hpi_pos by simp
    have ht_hi: "t < 1"
      unfolding t_def using h\<theta>_hi hpi_pos by (simp add: divide_less_eq)
    have ht_in: "t \<in> {0..1}" using ht_lo ht_hi by auto
    have h_2pi_t: "2 * pi * t = \<theta>"
      unfolding t_def using hpi_pos by simp
    have hcos: "cos (2 * pi * t) = cos \<theta>" by (simp add: h_2pi_t)
    have hsin: "sin (2 * pi * t) = sin \<theta>" by (simp add: h_2pi_t)
    have "cp_C t = z" unfolding cp_C_def using h\<theta>_eq hcos hsin by simp
    thus "z \<in> path_image cp_C" using ht_in unfolding path_image_def by auto
  qed
qed

lemma path_image_circle_path_R2: "path_image circle_path_R2 = sphere (0::real^2) 1"
proof -
  have h1: "path_image circle_path_R2 = path_image (C_to_R2 \<circ> cp_C)"
    by (simp add: circle_path_R2_via_C)
  also have "\<dots> = C_to_R2 ` path_image cp_C"
    unfolding path_image_def by (auto simp: image_iff)
  also have "\<dots> = C_to_R2 ` sphere 0 1"
    by (simp add: path_image_cp_C)
  also have "\<dots> = sphere (0::real^2) 1"
  proof
    show "C_to_R2 ` sphere (0::complex) 1 \<subseteq> sphere (0::real^2) 1"
      using C_to_R2_norm by force
    show "sphere (0::real^2) 1 \<subseteq> C_to_R2 ` sphere 0 1"
    proof
      fix v :: "real^2" assume hv: "v \<in> sphere 0 1"
      have "norm (R2_to_C v) = 1" using R2_to_C_norm hv by force
      hence "R2_to_C v \<in> sphere 0 1" by simp
      moreover have "v = C_to_R2 (R2_to_C v)" by (simp add: C_to_R2_R2_to_C)
      ultimately show "v \<in> C_to_R2 ` sphere 0 1" by blast
    qed
  qed
  finally show ?thesis .
qed

lemma cp_C_eq_iff:
  assumes "x \<in> {0..1}" "y \<in> {0..1}"
  shows "cp_C x = cp_C y \<longleftrightarrow> x = y \<or> (x = 0 \<and> y = 1) \<or> (x = 1 \<and> y = 0)"
proof
  assume heq: "cp_C x = cp_C y"
  have hcos: "cos (2 * pi * x) = cos (2 * pi * y)"
    using heq unfolding cp_C_def complex_eq_iff by simp
  have hsin: "sin (2 * pi * x) = sin (2 * pi * y)"
    using heq unfolding cp_C_def complex_eq_iff by simp
  have hpi_pos': "(2::real) * pi > 0" by simp
  have hpi_geq: "(2::real) * pi \<ge> 0" by simp
  have h2pi_x_lo: "0 \<le> 2 * pi * x"
    using assms(1) hpi_geq by simp
  have h2pi_x_hi: "2 * pi * x \<le> 2 * pi"
    using assms(1) hpi_geq by (simp add: mult_left_le)
  have h2pi_y_lo: "0 \<le> 2 * pi * y"
    using assms(2) hpi_geq by simp
  have h2pi_y_hi: "2 * pi * y \<le> 2 * pi"
    using assms(2) hpi_geq by (simp add: mult_left_le)
  have h_diff_lo: "- (2 * pi) \<le> 2 * pi * x - 2 * pi * y"
    using h2pi_x_lo h2pi_y_hi by linarith
  have h_diff_hi: "2 * pi * x - 2 * pi * y \<le> 2 * pi"
    using h2pi_x_hi h2pi_y_lo by linarith
  obtain k :: int where hk_raw: "2 * pi * x = 2 * pi * y + 2 * pi * real_of_int k"
    using sin_cos_eq_iff[of "2*pi*x" "2*pi*y"] hcos hsin by blast
  hence hk: "2 * pi * x - 2 * pi * y = 2 * pi * real_of_int k" by simp
  have hpi_pos: "(2::real) * pi > 0" by simp
  have hk_lo: "-1 \<le> real_of_int k"
  proof -
    have "- (2 * pi) \<le> 2 * pi * real_of_int k" using hk h_diff_lo by simp
    hence "- 1 * (2 * pi) \<le> real_of_int k * (2 * pi)" by (simp add: mult.commute)
    thus ?thesis using hpi_pos by (rule mult_right_le_imp_le)
  qed
  have hk_hi: "real_of_int k \<le> 1"
  proof -
    have "2 * pi * real_of_int k \<le> 2 * pi" using hk h_diff_hi by simp
    hence "real_of_int k * (2 * pi) \<le> 1 * (2 * pi)" by (simp add: mult.commute)
    thus ?thesis using hpi_pos by (rule mult_right_le_imp_le)
  qed
  have hk_bound: "real_of_int k \<in> {-1..1}" using hk_lo hk_hi by simp
  have hk_int: "k = -1 \<or> k = 0 \<or> k = 1"
    using hk_bound by (auto simp: minus_le_iff)
  show "x = y \<or> (x = 0 \<and> y = 1) \<or> (x = 1 \<and> y = 0)"
  proof (cases "k = 0")
    case True
    hence "x = y" using hk hpi_pos by (auto simp: divide_simps)
    thus ?thesis by simp
  next
    case False
    hence hk_pm: "k = -1 \<or> k = 1" using hk_int by simp
    show ?thesis
    proof (cases "k = 1")
      case True
      hence h_diff: "2 * pi * x - 2 * pi * y = 2 * pi" using hk by simp
      hence h_eq: "2 * pi * (x - y) = 2 * pi * 1"
        by (simp add: algebra_simps)
      have hpi_ne: "(2 * pi :: real) \<noteq> 0" using hpi_pos by simp
      have h_xy: "x - y = 1"
        using h_eq hpi_ne mult_cancel_left[of "2 * pi" "x - y" 1] by simp
      have "x = 1" using h_xy assms by auto
      moreover have "y = 0" using h_xy assms by auto
      ultimately show ?thesis by simp
    next
      case False
      hence "k = -1" using hk_pm by simp
      hence h_diff: "2 * pi * x - 2 * pi * y = - (2 * pi)" using hk by simp
      hence h_eq: "2 * pi * (x - y) = 2 * pi * (-1)"
        by (simp add: algebra_simps)
      have hpi_ne: "(2 * pi :: real) \<noteq> 0" using hpi_pos by simp
      have h_xy: "x - y = -1"
        using h_eq hpi_ne mult_cancel_left[of "2 * pi" "x - y" "-1"] by simp
      have "x = 0" using h_xy assms by auto
      moreover have "y = 1" using h_xy assms by auto
      ultimately show ?thesis by simp
    qed
  qed
next
  assume "x = y \<or> (x = 0 \<and> y = 1) \<or> (x = 1 \<and> y = 0)"
  thus "cp_C x = cp_C y"
    unfolding cp_C_def by (auto simp: complex_eq_iff)
qed

lemma simple_path_cp_C: "simple_path cp_C"
proof -
  have h_path: "path cp_C"
    using continuous_on_cp_C continuous_on_subset
    by (auto simp: path_def)
  have h_loop_free: "loop_free cp_C"
    unfolding loop_free_def using cp_C_eq_iff by blast
  show ?thesis unfolding simple_path_def using h_path h_loop_free by blast
qed

lemma simple_path_circle_path_R2: "simple_path circle_path_R2"
proof -
  have "simple_path (C_to_R2 \<circ> cp_C)"
  proof -
    have h1: "simple_path cp_C" by (rule simple_path_cp_C)
    have h2: "inj C_to_R2" by (rule C_to_R2_inj)
    have h_inj_eq: "\<And>x y. C_to_R2 x = C_to_R2 y \<longleftrightarrow> x = y"
      using h2 by (auto dest: injD)
    have h_loop_free: "loop_free (C_to_R2 \<circ> cp_C) \<longleftrightarrow> loop_free cp_C"
      unfolding loop_free_def o_def by (simp add: h_inj_eq)
    have h_path: "path (C_to_R2 \<circ> cp_C)"
      using h1 continuous_on_C_to_R2 continuous_on_compose continuous_on_subset
      unfolding path_def simple_path_def by blast
    show ?thesis using h1 h_path h_loop_free unfolding simple_path_def by blast
  qed
  thus ?thesis by (simp add: circle_path_R2_via_C)
qed

subsection \<open>Polygon parametrisation: from \<open>geotop_is_polygon J\<close> to a simple closed path\<close>

text \<open>Key: composing a simple closed path with a homeomorphism on the image
  yields a simple closed path with the transported image.\<close>

lemma simple_path_compose_homeomorphism:
  fixes c :: "real \<Rightarrow> 'a::t2_space" and h :: "'a \<Rightarrow> 'b::t2_space"
  assumes hsp: "simple_path c"
      and hcont: "continuous_on (path_image c) h"
      and hinj: "inj_on h (path_image c)"
  shows "simple_path (h \<circ> c)"
proof -
  have h_path_c: "path c" using hsp by (simp add: simple_path_def)
  have h_image_sub: "c ` {0..1} = path_image c" by (simp add: path_image_def)
  have h_path_hc: "path (h \<circ> c)"
  proof -
    have hcont_c: "continuous_on {0..1} c" using h_path_c by (simp add: path_def)
    have hcont_h_on_c: "continuous_on (c ` {0..1}) h"
      using hcont h_image_sub by simp
    have "continuous_on {0..1} (h \<circ> c)"
      by (rule continuous_on_compose[OF hcont_c hcont_h_on_c])
    thus ?thesis by (simp add: path_def)
  qed
  have h_loop_free_c: "loop_free c"
    using hsp by (simp add: simple_path_def)
  have h_loop_free_hc: "loop_free (h \<circ> c)"
    unfolding loop_free_def
  proof (intro ballI impI)
    fix x y assume hx: "x \<in> {0..1}" and hy: "y \<in> {0..1}" and heq: "(h \<circ> c) x = (h \<circ> c) y"
    have hcx: "c x \<in> path_image c" using hx by (simp add: path_image_def)
    have hcy: "c y \<in> path_image c" using hy by (simp add: path_image_def)
    from heq have hheq: "h (c x) = h (c y)" by simp
    have hcxy: "c x = c y" using hinj inj_onD[OF hinj hheq hcx hcy] by simp
    show "x = y \<or> x = 0 \<and> y = 1 \<or> x = 1 \<and> y = 0"
      using h_loop_free_c hx hy hcxy unfolding loop_free_def by blast
  qed
  show ?thesis unfolding simple_path_def using h_path_hc h_loop_free_hc by blast
qed

lemma path_image_compose: "path_image (h \<circ> c) = h ` path_image c"
  by (auto simp: path_image_def image_iff)

lemma pathstart_compose: "pathstart (h \<circ> c) = h (pathstart c)"
  by (simp add: pathstart_def)

lemma pathfinish_compose: "pathfinish (h \<circ> c) = h (pathfinish c)"
  by (simp add: pathfinish_def)

text \<open>The polygon parametrisation: from \<open>geotop_is_polygon J\<close> we extract a
  simple closed path whose image is \<open>J\<close>.\<close>

lemma polygon_simple_closed_path:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  obtains c where "simple_path c" "pathfinish c = pathstart c" "path_image c = J"
proof -
  from hJ have h_n_sphere: "geotop_is_n_sphere J
        (subspace_topology UNIV geotop_euclidean_topology J) 1"
    unfolding geotop_is_polygon_def by blast
  then obtain f where hf: "top1_homeomorphism_on J
        (subspace_topology UNIV geotop_euclidean_topology J)
        (geotop_std_sphere::(real^2) set)
        (subspace_topology UNIV geotop_euclidean_topology
            (geotop_std_sphere::(real^2) set)) f"
    unfolding geotop_is_n_sphere_def by blast
  have hstd_sphere: "(geotop_std_sphere::(real^2) set) = sphere 0 1"
    unfolding geotop_std_sphere_def by (auto simp: norm_eq_sqrt_inner)
  have h_homeo_HOL: "J homeomorphic (geotop_std_sphere::(real^2) set)"
    using hf top1_homeomorphism_on_geotop_imp_HOL_homeomorphic by blast
  hence h_homeo_HOL_sph: "J homeomorphic (sphere (0::real^2) 1)"
    using hstd_sphere by simp
  from h_homeo_HOL_sph have h_sym: "(sphere (0::real^2) 1) homeomorphic J"
    using homeomorphic_sym by blast
  then obtain g g' where hg_homeo: "homeomorphism (sphere (0::real^2) 1) J g g'"
    using homeomorphic_def by blast
  define hg_g where "hg_g = g"
  have hg: "homeomorphism (sphere (0::real^2) 1) J g g'" using hg_homeo .
  hence hg_cont_sphere: "continuous_on (sphere (0::real^2) 1) g"
    by (simp add: homeomorphism_def)
  hence hg_image: "g ` (sphere (0::real^2) 1) = J"
    using hg by (simp add: homeomorphism_def)
  have hg_inv: "\<And>x. x \<in> sphere (0::real^2) 1 \<Longrightarrow> g' (g x) = x"
    using hg unfolding homeomorphism_def by blast
  have hg_inj: "inj_on g (sphere (0::real^2) 1)"
  proof (rule inj_onI)
    fix x y assume hx: "x \<in> sphere 0 1" and hy: "y \<in> sphere 0 1" and heq: "g x = g y"
    from heq have "g' (g x) = g' (g y)" by simp
    thus "x = y" using hg_inv hx hy by simp
  qed
  define c where "c = g \<circ> circle_path_R2"
  have h_path_image_c: "path_image c = J"
  proof -
    have "path_image c = path_image (g \<circ> circle_path_R2)" by (simp add: c_def)
    also have "\<dots> = g ` path_image circle_path_R2" by (rule path_image_compose)
    also have "\<dots> = g ` sphere 0 1" by (simp add: path_image_circle_path_R2)
    finally show ?thesis using hg_image by simp
  qed
  have h_pathstart_c: "pathstart c = g (vector [1, 0])"
    by (simp add: c_def pathstart_compose pathstart_circle_path_R2)
  have h_pathfinish_c: "pathfinish c = g (vector [1, 0])"
    by (simp add: c_def pathfinish_compose pathfinish_circle_path_R2)
  have h_loop_c: "pathfinish c = pathstart c"
    using h_pathstart_c h_pathfinish_c by simp
  have h_simple_c: "simple_path c"
  proof -
    have h_g_cont_image: "continuous_on (path_image circle_path_R2) g"
      using hg_cont_sphere path_image_circle_path_R2 by simp
    have h_g_inj_image: "inj_on g (path_image circle_path_R2)"
      using hg_inj path_image_circle_path_R2 by simp
    show ?thesis unfolding c_def
      by (rule simple_path_compose_homeomorphism[OF simple_path_circle_path_R2
                                                    h_g_cont_image h_g_inj_image])
  qed
  from h_simple_c h_loop_c h_path_image_c that show ?thesis by blast
qed

(** from \<S>2 Theorem 1 - Lemma 1 (geotop.tex:514)
    LATEX VERSION: R^2 - J has at most two components. **)
text \<open>The set of \<open>geotop_component_at\<close> components of \<open>UNIV - J\<close> equals the
  HOL-Analysis \<open>components (UNIV - J)\<close>.\<close>

lemma geotop_polygon_components_set_eq:
  fixes J :: "(real^2) set"
  shows "{C. \<exists>P. P \<in> UNIV - J \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P}
       = components (UNIV - J)"
proof -
  have h_bridge: "\<And>P. geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P
              = connected_component_set (UNIV - J) P"
    by (rule geotop_component_at_UNIV_eq_connected_component_set)
  show ?thesis
    using h_bridge unfolding components_def by auto
qed

text \<open>Jordan curve theorem for polygons: \<open>R^2 - J\<close> has exactly two components.\<close>

lemma polygon_components_card:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "card (components (UNIV - J)) = 2"
proof -
  obtain c where hsp: "simple_path c" and hloop: "pathfinish c = pathstart c"
              and h_image: "path_image c = J"
    using polygon_simple_closed_path[OF hJ] by blast
  obtain inner outer where
    h_inner_ne: "inner \<noteq> {}" and h_inner_open: "open inner" and h_inner_conn: "connected inner"
    and h_outer_ne: "outer \<noteq> {}" and h_outer_open: "open outer" and h_outer_conn: "connected outer"
    and h_inner_bd: "bounded inner" and h_outer_unbd: "\<not> bounded outer"
    and h_disjoint: "inner \<inter> outer = {}"
    and h_union: "inner \<union> outer = - path_image c"
    and h_inner_fr: "frontier inner = path_image c"
    and h_outer_fr: "frontier outer = path_image c"
    using Jordan_curve_real2[OF hsp hloop] by metis
  have h_inner_neq_outer: "inner \<noteq> outer"
    using h_inner_bd h_outer_unbd by auto
  have h_X: "UNIV - J = inner \<union> outer"
    using h_union h_image by auto
  have h_components_eq: "components (UNIV - J) = {inner, outer}"
  proof
    show "components (UNIV - J) \<subseteq> {inner, outer}"
    proof
      fix C assume hC: "C \<in> components (UNIV - J)"
      then obtain P where hP: "P \<in> UNIV - J" and hC_eq: "C = connected_component_set (UNIV - J) P"
        by (rule componentsE)
      have hP_in: "P \<in> inner \<or> P \<in> outer" using hP h_X by blast
      have h_conn_in_inner_or_outer:
        "connected_component_set (UNIV - J) P \<subseteq> inner \<or> connected_component_set (UNIV - J) P \<subseteq> outer"
      proof -
        define C0 where "C0 = connected_component_set (UNIV - J) P"
        have hC0_conn: "connected C0" unfolding C0_def by (rule connected_connected_component)
        have hC0_sub: "C0 \<subseteq> UNIV - J" unfolding C0_def by (rule connected_component_subset)
        hence hC0_in_union: "C0 \<subseteq> inner \<union> outer" using h_X by simp
        have hP_C0: "P \<in> C0"
          unfolding C0_def using hP connected_component_refl by simp
        have h_inter1: "C0 \<inter> inner \<noteq> {} \<or> C0 \<inter> outer \<noteq> {}"
          using hP_C0 hP_in by blast
        have h_inter2: "C0 \<inter> inner = {} \<or> C0 \<inter> outer = {}"
          using hC0_conn hC0_in_union h_inner_open h_outer_open h_disjoint
                connectedD[OF hC0_conn h_inner_open h_outer_open]
          by (metis Int_assoc inf_bot_right inf_commute)
        show ?thesis
        proof (cases "C0 \<inter> inner = {}")
          case True
          hence "C0 \<subseteq> outer" using hC0_in_union by blast
          thus ?thesis unfolding C0_def by simp
        next
          case False
          hence "C0 \<inter> outer = {}" using h_inter2 by blast
          hence "C0 \<subseteq> inner" using hC0_in_union by blast
          thus ?thesis unfolding C0_def by simp
        qed
      qed
      have h_conn_eq: "connected_component_set (UNIV - J) P = inner \<or>
                       connected_component_set (UNIV - J) P = outer"
      proof -
        consider (Inner) "P \<in> inner" | (Outer) "P \<in> outer" using hP_in by blast
        thus ?thesis
        proof cases
          case Inner
          have "inner \<subseteq> connected_component_set (UNIV - J) P"
            using Inner h_inner_conn connected_component_maximal[of P inner "UNIV - J"] h_X
            by blast
          moreover have "connected_component_set (UNIV - J) P \<subseteq> inner"
          proof -
            have "connected_component_set (UNIV - J) P \<subseteq> outer \<Longrightarrow> P \<in> outer"
              using hP connected_component_refl by auto
            hence "\<not> (connected_component_set (UNIV - J) P \<subseteq> outer)"
              using Inner h_disjoint by auto
            thus ?thesis using h_conn_in_inner_or_outer by blast
          qed
          ultimately show ?thesis by simp
        next
          case Outer
          have "outer \<subseteq> connected_component_set (UNIV - J) P"
            using Outer h_outer_conn connected_component_maximal[of P outer "UNIV - J"] h_X
            by blast
          moreover have "connected_component_set (UNIV - J) P \<subseteq> outer"
          proof -
            have "connected_component_set (UNIV - J) P \<subseteq> inner \<Longrightarrow> P \<in> inner"
              using hP connected_component_refl by auto
            hence "\<not> (connected_component_set (UNIV - J) P \<subseteq> inner)"
              using Outer h_disjoint by auto
            thus ?thesis using h_conn_in_inner_or_outer by blast
          qed
          ultimately show ?thesis by simp
        qed
      qed
      thus "C \<in> {inner, outer}" using hC_eq by blast
    qed
  next
    show "{inner, outer} \<subseteq> components (UNIV - J)"
    proof
      fix C assume hC: "C \<in> {inner, outer}"
      show "C \<in> components (UNIV - J)"
      proof (cases "C = inner")
        case True
        obtain P where hP: "P \<in> inner" using h_inner_ne by blast
        hence hP_X: "P \<in> UNIV - J" using h_X by auto
        have h1: "inner \<subseteq> connected_component_set (UNIV - J) P"
          using hP h_inner_conn h_X connected_component_maximal[of P inner "UNIV - J"] by blast
        define C0 where "C0 = connected_component_set (UNIV - J) P"
        have hC0_conn: "connected C0" unfolding C0_def by (rule connected_connected_component)
        have hC0_sub: "C0 \<subseteq> UNIV - J" unfolding C0_def by (rule connected_component_subset)
        hence hC0_in_union: "C0 \<subseteq> inner \<union> outer" using h_X by simp
        have hP_C0: "P \<in> C0"
          unfolding C0_def using hP_X connected_component_refl by simp
        have hC0_inter_inner: "C0 \<inter> inner \<noteq> {}" using hP_C0 hP by blast
        have hC0_or: "C0 \<inter> inner = {} \<or> C0 \<inter> outer = {}"
          using connectedD[OF hC0_conn h_inner_open h_outer_open]
                hC0_in_union h_disjoint
          by (metis Int_assoc inf_bot_right inf_commute)
        hence hC0_inter_outer: "C0 \<inter> outer = {}" using hC0_inter_inner by blast
        have hC0_in_inner: "C0 \<subseteq> inner" using hC0_in_union hC0_inter_outer by blast
        have h2: "connected_component_set (UNIV - J) P \<subseteq> inner"
          using hC0_in_inner unfolding C0_def by simp
        have "inner = connected_component_set (UNIV - J) P" using h1 h2 by simp
        hence "inner \<in> components (UNIV - J)" using hP_X componentsI by metis
        thus ?thesis using True by simp
      next
        case False
        hence hC_outer: "C = outer" using hC by simp
        obtain P where hP: "P \<in> outer" using h_outer_ne by blast
        hence hP_X: "P \<in> UNIV - J" using h_X by auto
        have h1: "outer \<subseteq> connected_component_set (UNIV - J) P"
          using hP h_outer_conn h_X connected_component_maximal[of P outer "UNIV - J"] by blast
        define C0 where "C0 = connected_component_set (UNIV - J) P"
        have hC0_conn: "connected C0" unfolding C0_def by (rule connected_connected_component)
        have hC0_sub: "C0 \<subseteq> UNIV - J" unfolding C0_def by (rule connected_component_subset)
        hence hC0_in_union: "C0 \<subseteq> inner \<union> outer" using h_X by simp
        have hP_C0: "P \<in> C0"
          unfolding C0_def using hP_X connected_component_refl by simp
        have hC0_inter_outer: "C0 \<inter> outer \<noteq> {}" using hP_C0 hP by blast
        have hC0_or: "C0 \<inter> inner = {} \<or> C0 \<inter> outer = {}"
          using connectedD[OF hC0_conn h_inner_open h_outer_open]
                hC0_in_union h_disjoint
          by (metis Int_assoc inf_bot_right inf_commute)
        hence hC0_inter_inner: "C0 \<inter> inner = {}" using hC0_inter_outer by blast
        have hC0_in_outer: "C0 \<subseteq> outer" using hC0_in_union hC0_inter_inner by blast
        have h2: "connected_component_set (UNIV - J) P \<subseteq> outer"
          using hC0_in_outer unfolding C0_def by simp
        have "outer = connected_component_set (UNIV - J) P" using h1 h2 by simp
        hence "outer \<in> components (UNIV - J)" using hP_X componentsI by metis
        thus ?thesis using hC_outer by simp
      qed
    qed
  qed
  have "card (components (UNIV - J)) = card {inner, outer}"
    using h_components_eq by simp
  also have "\<dots> = 2" using h_inner_neq_outer by simp
  finally show ?thesis .
qed

theorem Lemma_GT_2_1a:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "card {C. \<exists>P. P \<in> (UNIV::(real^2) set) - J \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology ((UNIV::(real^2) set) - J) P} \<le> 2"
  using polygon_components_card[OF hJ] geotop_polygon_components_set_eq[of J] by simp

theorem Lemma_GT_2_1b:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "card {C. \<exists>P. P \<in> (UNIV::(real^2) set) - J \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology ((UNIV::(real^2) set) - J) P} \<ge> 2"
  using polygon_components_card[OF hJ] geotop_polygon_components_set_eq[of J] by simp

(** from \<S>2 Theorem 1 (geotop.tex:502)
    LATEX VERSION: Let J be a polygon in R^2. Then R^2 - J has exactly two components. **)
theorem Theorem_GT_2_1:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "card {C. \<exists>P. P \<in> (UNIV::(real^2) set) - J \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology ((UNIV::(real^2) set) - J) P} = 2"
  (** Combine the upper bound (Lemma_GT_2_1a) and lower bound (Lemma_GT_2_1b). **)
  using Lemma_GT_2_1a[OF hJ] Lemma_GT_2_1b[OF hJ]
  by linarith

(** from \<S>2: interior and exterior of a polygon (geotop.tex:553)
    LATEX VERSION: The bounded component I of R^2 - J is called the interior of J, and the
      unbounded component E is called the exterior. **)
text \<open>A set $A \subseteq \mathbb{R}^2$ is \emph{bounded} if there exists $r > 0$ such that
  $A \subseteq N(\mathbf{0}, r)$. We define interior and exterior of a polygon accordingly.\<close>

definition geotop_bounded_R2 :: "(real^2) set \<Rightarrow> bool" where
  "geotop_bounded_R2 A \<longleftrightarrow> (\<exists>r>0. \<forall>P\<in>A. norm P < r)"

definition geotop_polygon_interior :: "(real^2) set \<Rightarrow> (real^2) set" where
  "geotop_polygon_interior J =
    (SOME I. I \<noteq> {} \<and> I \<subseteq> UNIV - J \<and> geotop_bounded_R2 I \<and>
       top1_connected_on I (subspace_topology UNIV geotop_euclidean_topology I) \<and>
       (\<forall>P\<in>I. geotop_component_at UNIV geotop_euclidean_topology
                   ((UNIV::(real^2) set) - J) P = I))"

definition geotop_polygon_exterior :: "(real^2) set \<Rightarrow> (real^2) set" where
  "geotop_polygon_exterior J =
    (SOME E. E \<noteq> {} \<and> E \<subseteq> UNIV - J \<and> \<not> geotop_bounded_R2 E \<and>
       top1_connected_on E (subspace_topology UNIV geotop_euclidean_topology E) \<and>
       (\<forall>P\<in>E. geotop_component_at UNIV geotop_euclidean_topology
                   ((UNIV::(real^2) set) - J) P = E))"

text \<open>\<open>geotop_simplex_dim_imp_hyperplane_dim\<close> moved to GeoTopBase.\<close>

text \<open>Prerequisite for Theorem_GT_2_2 (Moise's "finite polyhedron" content):
  any complex with compact polyhedron is finite. This is the standard
  compactness-plus-local-finiteness argument, modelled on
  \<open>geotop_subdivision_of_finite_is_finite\<close> in \<open>b0/GeoTopBase0.thy\<close>.\<close>

lemma compact_polyhedron_imp_finite_complex:
  fixes K :: "(real^2) set set"
  assumes hKcomp: "geotop_is_complex K"
      and hK_poly_comp: "compact (geotop_polyhedron K)"
  shows "finite K"
proof -
  (** K.3 (local finiteness): each \<tau> \<in> K has open nbhd touching only finitely many. **)
  have hK_locfin: "\<forall>\<tau>\<in>K. \<exists>U. open U \<and> \<tau> \<subseteq> U \<and> finite {\<tau>'\<in>K. \<tau>' \<inter> U \<noteq> {}}"
    using hKcomp unfolding geotop_is_complex_def by (by100 blast)
  define Uf :: "(real^2) set \<Rightarrow> (real^2) set" where
    "Uf \<tau> = (SOME U. open U \<and> \<tau> \<subseteq> U \<and> finite {\<tau>'\<in>K. \<tau>' \<inter> U \<noteq> {}})" for \<tau>
  have hUf_spec: "\<forall>\<tau>\<in>K. open (Uf \<tau>) \<and> \<tau> \<subseteq> Uf \<tau>
                          \<and> finite {\<tau>'\<in>K. \<tau>' \<inter> Uf \<tau> \<noteq> {}}"
  proof
    fix \<tau> assume h\<tau>K: "\<tau> \<in> K"
    have hex: "\<exists>U. open U \<and> \<tau> \<subseteq> U \<and> finite {\<tau>'\<in>K. \<tau>' \<inter> U \<noteq> {}}"
      using hK_locfin h\<tau>K by (by100 blast)
    show "open (Uf \<tau>) \<and> \<tau> \<subseteq> Uf \<tau> \<and> finite {\<tau>'\<in>K. \<tau>' \<inter> Uf \<tau> \<noteq> {}}"
      unfolding Uf_def using someI_ex[OF hex] by (by100 blast)
  qed
  (** The U_\<tau>'s cover |K|. **)
  have hcover: "geotop_polyhedron K \<subseteq> (\<Union>\<tau>\<in>K. Uf \<tau>)"
  proof
    fix x assume hx: "x \<in> geotop_polyhedron K"
    obtain \<tau> where h\<tau>K: "\<tau> \<in> K" and hx\<tau>: "x \<in> \<tau>"
      using hx unfolding geotop_polyhedron_def by (by100 blast)
    have hx_Uf: "x \<in> Uf \<tau>" using hx\<tau> h\<tau>K hUf_spec by (by100 blast)
    show "x \<in> (\<Union>\<tau>\<in>K. Uf \<tau>)" using h\<tau>K hx_Uf by (by100 blast)
  qed
  have hUf_open_img: "\<forall>B\<in>Uf ` K. open B"
    using hUf_spec by (by100 blast)
  have hcover_img: "geotop_polyhedron K \<subseteq> \<Union>(Uf ` K)"
    using hcover by (by100 blast)
  have hcover_fin: "\<exists>\<T>\<subseteq>Uf ` K. finite \<T> \<and> geotop_polyhedron K \<subseteq> \<Union>\<T>"
  proof (rule compactE[OF hK_poly_comp hcover_img])
    fix B assume "B \<in> Uf ` K"
    thus "open B" using hUf_open_img by (by100 blast)
  next
    fix \<T> assume "\<T> \<subseteq> Uf ` K" "finite \<T>" "geotop_polyhedron K \<subseteq> \<Union>\<T>"
    thus "\<exists>\<T>\<subseteq>Uf ` K. finite \<T> \<and> geotop_polyhedron K \<subseteq> \<Union>\<T>"
      by (by100 blast)
  qed
  obtain \<T> where h\<T>_sub: "\<T> \<subseteq> Uf ` K" and h\<T>fin: "finite \<T>"
              and h\<T>_cover: "geotop_polyhedron K \<subseteq> \<Union>\<T>"
    using hcover_fin by (by100 blast)
  define S where "S = (\<lambda>B. SOME \<tau>. \<tau> \<in> K \<and> B = Uf \<tau>) ` \<T>"
  have hSfin: "finite S" unfolding S_def using h\<T>fin by (by100 blast)
  have hS_sub: "S \<subseteq> K"
  proof
    fix \<tau> assume h\<tau>S: "\<tau> \<in> S"
    then obtain B where hBT: "B \<in> \<T>"
      and h\<tau>_some: "\<tau> = (SOME \<tau>'. \<tau>' \<in> K \<and> B = Uf \<tau>')"
      unfolding S_def by (by100 blast)
    have hB_img: "B \<in> Uf ` K" using hBT h\<T>_sub by (by100 blast)
    have hex_some: "\<exists>\<tau>'. \<tau>' \<in> K \<and> B = Uf \<tau>'" using hB_img by (by100 blast)
    show "\<tau> \<in> K" using h\<tau>_some someI_ex[OF hex_some] by (by100 blast)
  qed
  have hS_cover: "geotop_polyhedron K \<subseteq> (\<Union>\<tau>\<in>S. Uf \<tau>)"
  proof
    fix x assume hx: "x \<in> geotop_polyhedron K"
    obtain B where hBT: "B \<in> \<T>" and hxB: "x \<in> B"
      using hx h\<T>_cover by (by100 blast)
    have hB_img: "B \<in> Uf ` K" using hBT h\<T>_sub by (by100 blast)
    have hex_some: "\<exists>\<tau>'. \<tau>' \<in> K \<and> B = Uf \<tau>'" using hB_img by (by100 blast)
    define \<tau> where "\<tau> = (SOME \<tau>'. \<tau>' \<in> K \<and> B = Uf \<tau>')"
    have h\<tau>_props: "\<tau> \<in> K \<and> B = Uf \<tau>"
      unfolding \<tau>_def using someI_ex[OF hex_some] by (by100 blast)
    have h\<tau>S: "\<tau> \<in> S" unfolding S_def using hBT \<tau>_def by (by100 blast)
    show "x \<in> (\<Union>\<tau>\<in>S. Uf \<tau>)" using h\<tau>S h\<tau>_props hxB by (by100 blast)
  qed
  (** Every \<tau>' \<in> K meets some Uf \<tau> with \<tau> \<in> S. **)
  have h\<tau>'_S: "\<forall>\<tau>'\<in>K. \<exists>\<tau>\<in>S. \<tau>' \<inter> Uf \<tau> \<noteq> {}"
  proof
    fix \<tau>' assume h\<tau>'K: "\<tau>' \<in> K"
    have hK_simp_all: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
      using conjunct1[OF hKcomp[unfolded geotop_is_complex_def]] by (by100 blast)
    have h\<tau>'_simp: "geotop_is_simplex \<tau>'"
      using h\<tau>'K hK_simp_all by (by100 blast)
    have h\<tau>'ne: "\<tau>' \<noteq> {}"
    proof -
      obtain V m n where hV_fin: "finite V" and hVcard: "card V = n + 1"
                  and h\<tau>'_hull: "\<tau>' = geotop_convex_hull V"
        using h\<tau>'_simp unfolding geotop_is_simplex_def by (by100 blast)
      have hVne: "V \<noteq> {}"
        using hV_fin hVcard card_gt_0_iff by (by100 fastforce)
      obtain v where hv: "v \<in> V" using hVne by (by100 blast)
      have hvhull: "v \<in> convex hull V" using hv hull_inc[of v V] by (by100 simp)
      have h\<tau>'_hullHOL: "\<tau>' = convex hull V"
        using h\<tau>'_hull geotop_convex_hull_eq_HOL by (by100 simp)
      show "\<tau>' \<noteq> {}" using hvhull h\<tau>'_hullHOL by (by100 blast)
    qed
    obtain x where hx\<tau>': "x \<in> \<tau>'" using h\<tau>'ne by (by100 blast)
    have hx_Kpoly: "x \<in> geotop_polyhedron K"
      using h\<tau>'K hx\<tau>' unfolding geotop_polyhedron_def by (by100 blast)
    obtain \<tau> where h\<tau>S: "\<tau> \<in> S" and hx_Uf\<tau>: "x \<in> Uf \<tau>"
      using hS_cover hx_Kpoly by (by100 blast)
    have hmeet: "\<tau>' \<inter> Uf \<tau> \<noteq> {}" using hx\<tau>' hx_Uf\<tau> by (by100 blast)
    show "\<exists>\<tau>\<in>S. \<tau>' \<inter> Uf \<tau> \<noteq> {}" using h\<tau>S hmeet by (by100 blast)
  qed
  have hK_sub: "K \<subseteq> (\<Union>\<tau>\<in>S. {\<tau>'\<in>K. \<tau>' \<inter> Uf \<tau> \<noteq> {}})"
  proof
    fix \<tau>' assume h\<tau>'K: "\<tau>' \<in> K"
    have h\<tau>'_meet: "\<exists>\<tau>\<in>S. \<tau>' \<inter> Uf \<tau> \<noteq> {}"
      using h\<tau>'_S h\<tau>'K by (by100 blast)
    obtain \<tau> where h\<tau>S: "\<tau> \<in> S" and hmeet: "\<tau>' \<inter> Uf \<tau> \<noteq> {}"
      using h\<tau>'_meet by (by100 blast)
    show "\<tau>' \<in> (\<Union>\<tau>\<in>S. {\<tau>'\<in>K. \<tau>' \<inter> Uf \<tau> \<noteq> {}})"
      using h\<tau>S h\<tau>'K hmeet by (by100 blast)
  qed
  have hSfin_sub: "finite (\<Union>\<tau>\<in>S. {\<tau>'\<in>K. \<tau>' \<inter> Uf \<tau> \<noteq> {}})"
  proof (rule finite_UN_I[OF hSfin])
    fix \<tau> assume h\<tau>S: "\<tau> \<in> S"
    have h\<tau>K: "\<tau> \<in> K" using h\<tau>S hS_sub by (by100 blast)
    show "finite {\<tau>'\<in>K. \<tau>' \<inter> Uf \<tau> \<noteq> {}}" using hUf_spec h\<tau>K by (by100 blast)
  qed
  show "finite K"
    using hK_sub hSfin_sub finite_subset by (by100 blast)
qed

text \<open>Polygons admit a finite triangulating complex (Moise implicit fact: the
  polyhedron of a polygon is compact, so any complex realising it is finite by
  \<open>compact_polyhedron_imp_finite_complex\<close>).\<close>

lemma geotop_polygon_finite_triangulation:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "\<exists>K. geotop_is_complex K \<and> finite K \<and> geotop_polyhedron K = J"
proof -
  obtain K0 where hK0c: "geotop_is_complex K0"
              and hK0p: "geotop_polyhedron K0 = J"
              and hJsph: "geotop_is_n_sphere J
                            (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ unfolding geotop_is_polygon_def by (by100 blast)
  obtain f where hf: "top1_homeomorphism_on J
                        (subspace_topology UNIV geotop_euclidean_topology J)
                        (geotop_std_sphere::(real^2) set)
                        (subspace_topology UNIV geotop_euclidean_topology
                           (geotop_std_sphere::(real^2) set)) f"
    using hJsph unfolding geotop_is_n_sphere_def by (by100 blast)
  have h_homeo_HOL: "J homeomorphic (geotop_std_sphere::(real^2) set)"
    using hf top1_homeomorphism_on_geotop_imp_HOL_homeomorphic by (by100 blast)
  have h_std_eq: "(geotop_std_sphere::(real^2) set) = sphere (0::real^2) 1"
    unfolding geotop_std_sphere_def by (auto simp: norm_eq_sqrt_inner)
  have h_homeo_sph: "J homeomorphic sphere (0::real^2) 1"
    using h_homeo_HOL h_std_eq by (by100 simp)
  have h_compact_sph: "compact (sphere (0::real^2) 1)" by simp
  have hJ_compact: "compact J"
    using h_compact_sph h_homeo_sph homeomorphic_compactness by (by100 blast)
  have hK0_poly_comp: "compact (geotop_polyhedron K0)"
    using hJ_compact hK0p by (by100 simp)
  have hK0_fin: "finite K0"
    using compact_polyhedron_imp_finite_complex[OF hK0c hK0_poly_comp] by (by100 simp)
  show ?thesis using hK0c hK0_fin hK0p by (by100 blast)
qed

text \<open>Polygon \<open>J\<close> in \<open>real^2\<close> is homeomorphic to the unit sphere
  \<open>sphere 0 1\<close> (HOL homeomorphism, not the geotop topological version).\<close>

lemma polygon_homeomorphic_S1_helper:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "J homeomorphic sphere (0::real^2) 1"
proof -
  have hJsph: "geotop_is_n_sphere J
                (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ unfolding geotop_is_polygon_def by (by100 blast)
  obtain f0 where hf0: "top1_homeomorphism_on J
                          (subspace_topology UNIV geotop_euclidean_topology J)
                          (geotop_std_sphere::(real^2) set)
                          (subspace_topology UNIV geotop_euclidean_topology
                             (geotop_std_sphere::(real^2) set)) f0"
    using hJsph unfolding geotop_is_n_sphere_def by (by100 blast)
  have h_J_std: "J homeomorphic (geotop_std_sphere::(real^2) set)"
    using hf0 top1_homeomorphism_on_geotop_imp_HOL_homeomorphic by (by100 blast)
  have h_std_eq: "(geotop_std_sphere::(real^2) set) = sphere (0::real^2) 1"
    unfolding geotop_std_sphere_def by (auto simp: norm_eq_sqrt_inner)
  show ?thesis using h_J_std h_std_eq by (by100 simp)
qed

text \<open>A polygon \<open>J \<subseteq> real^2\<close> has empty topological interior. Proof: combine
  \<open>polygon_homeomorphic_S1_helper\<close>, \<open>homeomorphic_punctured_sphere_hyperplane\<close>, and
  \<open>invariance_of_dimension_affine_sets\<close> on a small ball missing one fixed point.\<close>

lemma polygon_set_interior_empty:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "interior J = {}"
proof (rule ccontr)
  assume "interior J \<noteq> {}"
  then obtain x0 where hx0: "x0 \<in> interior J" by (by100 blast)
  obtain f f' where hff': "homeomorphism J (sphere (0::real^2) 1) f f'"
    using polygon_homeomorphic_S1_helper[OF hJ] unfolding homeomorphic_def by (by100 blast)
  define b :: "real^2" where "b = vector [1, 0]"
  have hb_norm: "norm b = 1"
  proof -
    have h1: "b $ 1 = 1" unfolding b_def by simp
    have h2: "b $ 2 = 0" unfolding b_def by simp
    have hsum: "(\<Sum>i\<in>(UNIV::2 set). (b $ i)\<^sup>2) = 1"
      using h1 h2 by (simp add: UNIV_2)
    show ?thesis unfolding norm_vec_def L2_set_def using hsum by simp
  qed
  have hb_sph: "b \<in> sphere (0::real^2) 1"
    using hb_norm by (by100 simp)
  define q where "q = f' b"
  have hq_J: "q \<in> J"
    using hb_sph hff' unfolding homeomorphism_def q_def by (by100 blast)
  have hf_q: "f q = b"
    using hq_J hff' hb_sph unfolding homeomorphism_def q_def by (by100 metis)
  (** Open interior J non-empty hence has a ball; pick x \<in> interior J with x \<noteq> q. **)
  obtain r00 where hr00: "r00 > 0" and hball00: "ball x0 r00 \<subseteq> interior J"
    using hx0 by (metis interior_subset open_contains_ball open_interior)
  define x where "x = (if x0 = q then x0 + (r00/2) *\<^sub>R b else x0)"
  have hx_ne_q: "x \<noteq> q"
  proof (cases "x0 = q")
    case True
    have h_diff: "x - x0 = (r00/2) *\<^sub>R b" unfolding x_def using True by (by100 simp)
    have h_diff_norm: "norm (x - x0) = r00/2"
      using hb_norm h_diff hr00 by (auto simp: norm_scaleR)
    have h_ne: "x \<noteq> x0"
      using h_diff_norm hr00 by force
    show ?thesis using h_ne True x_def by (by100 simp)
  next
    case False
    show ?thesis unfolding x_def using False by (by100 simp)
  qed
  have hx_in_int: "x \<in> interior J"
  proof (cases "x0 = q")
    case True
    have h_dist: "dist x x0 = r00/2"
    proof -
      have "dist x x0 = norm (x - x0)" by (simp add: dist_norm)
      also have "x - x0 = (r00/2) *\<^sub>R b" unfolding x_def using True by (by100 simp)
      finally show ?thesis using hb_norm hr00 by (auto simp: norm_scaleR)
    qed
    have h_lt: "dist x x0 < r00" using h_dist hr00 by simp
    have hx_in: "x \<in> ball x0 r00" using h_lt by (simp add: dist_commute)
    show ?thesis using hx_in hball00 by (by100 blast)
  next
    case False
    show ?thesis unfolding x_def using False hx0 by (by100 simp)
  qed
  obtain r0 where hr0: "r0 > 0" and hball0: "ball x r0 \<subseteq> interior J"
    using hx_in_int by (metis interior_subset open_contains_ball open_interior)
  define r where "r = min r0 (dist x q / 2)"
  have hdxq: "dist x q > 0" using hx_ne_q by simp
  have hr_pos: "r > 0"
    unfolding r_def using hr0 hdxq by (by100 simp)
  have hr_le: "r \<le> r0" unfolding r_def by simp
  have hball_int: "ball x r \<subseteq> interior J" using hball0 hr_le by auto
  have hball_J: "ball x r \<subseteq> J" using hball_int interior_subset by (by100 blast)
  have hq_notin: "q \<notin> ball x r"
  proof
    assume hqb: "q \<in> ball x r"
    have hr_lt: "r \<le> dist x q / 2" unfolding r_def by (by100 simp)
    have "dist x q < r" using hqb by (simp add: dist_commute)
    thus False using hr_lt hdxq by (by100 simp)
  qed
  have hball_Jq: "ball x r \<subseteq> J - {q}" using hball_J hq_notin by (by100 blast)
  (** S^1 - {b} homeomorphic to 1-dim hyperplane H = {y. b \<bullet> y = 0}. **)
  define H :: "(real^2) set" where "H = {y::real^2. b \<bullet> y = 0}"
  have hb_ne0: "b \<noteq> 0"
    unfolding b_def by (simp add: vec_eq_iff forall_2)
  have hSb_hom: "(sphere (0::real^2) 1 - {b}) homeomorphic H"
    unfolding H_def
    using homeomorphic_punctured_sphere_hyperplane[of 1 b 0 b 0] hb_sph hb_ne0
    by (by100 simp)
  obtain g g' where hgg': "homeomorphism (sphere (0::real^2) 1 - {b}) H g g'"
    using hSb_hom unfolding homeomorphic_def by (by100 blast)
  (** f maps ball x r into S^1 - {b}. **)
  have hf_J: "f ` J = sphere (0::real^2) 1"
    using hff' unfolding homeomorphism_def by (by100 blast)
  have hf_inj_J: "inj_on f J"
    using hff' unfolding homeomorphism_def by (auto simp: inj_on_def)
  have hf_im_ball_in_S1: "f ` ball x r \<subseteq> sphere (0::real^2) 1"
    using hball_J hf_J by (by100 blast)
  have hf_im_ball: "f ` ball x r \<subseteq> sphere (0::real^2) 1 - {b}"
  proof
    fix y assume "y \<in> f ` ball x r"
    then obtain z where hz: "z \<in> ball x r" and hyz: "y = f z" by (by100 blast)
    have hzJ: "z \<in> J" using hz hball_J by (by100 blast)
    have hzq: "z \<noteq> q" using hz hq_notin by (by100 blast)
    have hy_S1: "y \<in> sphere (0::real^2) 1" using hf_im_ball_in_S1 hz hyz by (by100 blast)
    have hy_ne_b: "y \<noteq> b"
    proof
      assume "y = b"
      hence "f z = f q" using hyz hf_q by (by100 simp)
      hence "z = q" using hzJ hq_J hf_inj_J unfolding inj_on_def by (by100 blast)
      thus False using hzq by (by100 simp)
    qed
    show "y \<in> sphere (0::real^2) 1 - {b}" using hy_S1 hy_ne_b by (by100 blast)
  qed
  (** Define F = g \<circ> f, which is continuous and injective on ball x r, image in H. **)
  have hf_cont_J: "continuous_on J f"
    by (rule homeomorphism_cont1[OF hff'])
  have hf_cont_ball: "continuous_on (ball x r) f"
    using hf_cont_J hball_J continuous_on_subset by (by100 blast)
  have hg_cont: "continuous_on (sphere (0::real^2) 1 - {b}) g"
    by (rule homeomorphism_cont1[OF hgg'])
  have hg_cont_im: "continuous_on (f ` ball x r) g"
    using hg_cont hf_im_ball continuous_on_subset by (by100 blast)
  have hF_cont: "continuous_on (ball x r) (g \<circ> f)"
    using hf_cont_ball hg_cont_im continuous_on_compose by (by100 blast)
  have hf_inj_ball: "inj_on f (ball x r)"
    using hf_inj_J hball_J inj_on_subset by (by100 blast)
  have hg_inj: "inj_on g (sphere (0::real^2) 1 - {b})"
  proof (rule inj_onI)
    fix u v assume hu: "u \<in> sphere (0::real^2) 1 - {b}"
                and hv: "v \<in> sphere (0::real^2) 1 - {b}"
                and h_eq: "g u = g v"
    have hgu: "g' (g u) = u" by (rule homeomorphism_apply1[OF hgg' hu])
    have hgv: "g' (g v) = v" by (rule homeomorphism_apply1[OF hgg' hv])
    show "u = v" using h_eq hgu hgv by (by100 metis)
  qed
  have hF_inj: "inj_on (g \<circ> f) (ball x r)"
  proof (rule comp_inj_on)
    show "inj_on f (ball x r)" by (rule hf_inj_ball)
    show "inj_on g (f ` ball x r)"
      using hg_inj hf_im_ball inj_on_subset by (by100 blast)
  qed
  have hg_im: "g ` (sphere (0::real^2) 1 - {b}) \<subseteq> H"
  proof -
    have h_eq: "g ` (sphere (0::real^2) 1 - {b}) = H"
      by (rule homeomorphism_image1[OF hgg'])
    show ?thesis using h_eq by (by100 simp)
  qed
  have hF_im: "(g \<circ> f) \<in> ball x r \<rightarrow> H"
  proof
    fix y assume hy: "y \<in> ball x r"
    have "f y \<in> sphere (0::real^2) 1 - {b}" using hy hf_im_ball by (by100 blast)
    hence "g (f y) \<in> H" using hg_im by (by100 blast)
    thus "(g \<circ> f) y \<in> H" by (by100 simp)
  qed
  have hball_open: "openin (top_of_set (UNIV::(real^2) set)) (ball x r)" by (by100 simp)
  have hUNIV_aff: "affine (UNIV::(real^2) set)" by (by100 simp)
  have hH_aff: "affine H" unfolding H_def by (rule affine_hyperplane)
  have hball_ne: "ball x r \<noteq> {}" using hr_pos by (by100 simp)
  have h_aff_le: "aff_dim (UNIV::(real^2) set) \<le> aff_dim H"
    using invariance_of_dimension_affine_sets[OF hball_open hUNIV_aff hH_aff
            hF_cont hF_im hF_inj hball_ne] by (by100 simp)
  have h_aff_UNIV: "aff_dim (UNIV::(real^2) set) = 2" by (simp add: aff_dim_UNIV)
  have h_aff_H: "aff_dim H = 1"
    unfolding H_def using hb_ne0 aff_dim_hyperplane[of b 0] by (by100 simp)
  show False using h_aff_le h_aff_UNIV h_aff_H by (by100 simp)
qed

text \<open>Every simplex of a polygon's complex has dimension \<le> 1: a 2-cell would
  have non-empty interior in \<open>real^2\<close>, contradicting \<open>polygon_set_interior_empty\<close>.\<close>

lemma polygon_complex_dim_le_1:
  fixes K :: "(real^2) set set" and J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
      and hKc: "geotop_is_complex K"
      and hKp: "geotop_polyhedron K = J"
  shows "\<forall>\<sigma>\<in>K. \<forall>k. geotop_simplex_dim \<sigma> k \<longrightarrow> k \<le> 1"
proof (intro ballI allI impI)
  fix \<sigma> k assume h\<sigma>K: "\<sigma> \<in> K" and h\<sigma>k: "geotop_simplex_dim \<sigma> k"
  show "k \<le> 1"
  proof (rule ccontr)
    assume hcontra: "\<not> k \<le> 1"
    hence hk2: "k \<ge> 2" by (by100 simp)
    obtain V m where hVfin: "finite V" and hVcard: "card V = k + 1"
                 and hVgp: "geotop_general_position V m"
                 and hknm: "k \<le> m" and h\<sigma>V: "\<sigma> = geotop_convex_hull V"
      using h\<sigma>k unfolding geotop_simplex_dim_def by (by100 blast)
    have hVai: "\<not> affine_dependent V"
    proof -
      have h_simp_verts: "geotop_simplex_vertices \<sigma> V"
        unfolding geotop_simplex_vertices_def
        using hVfin hVcard hknm hVgp h\<sigma>V by (by100 blast)
      show ?thesis by (rule geotop_general_position_imp_aff_indep[OF h_simp_verts])
    qed
    have h\<sigma>HOL: "\<sigma> = convex hull V"
      using h\<sigma>V geotop_convex_hull_eq_HOL by (by100 simp)
    have h_aff_V: "aff_dim V = int (card V) - 1"
      using hVai affine_independent_iff_card hVfin by (by100 blast)
    have h_aff_\<sigma>: "aff_dim \<sigma> = int k"
      using h\<sigma>HOL aff_dim_convex_hull[of V] h_aff_V hVcard by (by100 simp)
    (** \<open>aff_dim \<sigma> = k \<ge> 2 = DIM(real^2)\<close>, but also \<open>aff_dim \<sigma> \<le> 2\<close>. **)
    have h_aff_\<sigma>_le: "aff_dim \<sigma> \<le> int (DIM(real^2))"
      by (rule aff_dim_le_DIM)
    have h_DIM: "DIM(real^2) = 2" by simp
    have h_aff_\<sigma>_eq: "aff_dim \<sigma> = int (DIM(real^2))"
      using h_aff_\<sigma> hk2 h_aff_\<sigma>_le h_DIM by (by100 simp)
    (** Hence interior \<sigma> = rel_interior \<sigma> in real^2. **)
    have h_int_eq: "interior \<sigma> = rel_interior \<sigma>"
      using h_aff_\<sigma>_eq interior_rel_interior_gen[of \<sigma>] by (by100 simp)
    (** \<sigma> is non-empty convex (convex hull of non-empty V); rel_interior \<sigma> non-empty. **)
    have hVne: "V \<noteq> {}"
      using hVcard hVfin card_gt_0_iff by (by100 fastforce)
    have h\<sigma>ne: "\<sigma> \<noteq> {}"
      using h\<sigma>HOL hVne by (by100 simp)
    have h\<sigma>_conv: "convex \<sigma>" using h\<sigma>HOL convex_convex_hull by (by100 simp)
    have h_relint_ne: "rel_interior \<sigma> \<noteq> {}"
      using h\<sigma>ne h\<sigma>_conv rel_interior_eq_empty by (by100 blast)
    have h_int_\<sigma>_ne: "interior \<sigma> \<noteq> {}"
      using h_int_eq h_relint_ne by (by100 simp)
    (** \<sigma> \<subseteq> J, so interior \<sigma> (open in real^2, in J) \<subseteq> interior J. **)
    have h\<sigma>_subJ: "\<sigma> \<subseteq> J"
      using h\<sigma>K hKp unfolding geotop_polyhedron_def by (by100 blast)
    have h_int_open: "open (interior \<sigma>)" by simp
    have h_int_subJ: "interior \<sigma> \<subseteq> J"
      using interior_subset h\<sigma>_subJ by (by100 blast)
    have h_int_subIntJ: "interior \<sigma> \<subseteq> interior J"
      using h_int_open h_int_subJ interior_maximal by (by100 blast)
    have hIntJ_ne: "interior J \<noteq> {}"
      using h_int_\<sigma>_ne h_int_subIntJ by (by100 blast)
    show False using hIntJ_ne polygon_set_interior_empty[OF hJ] by (by100 blast)
  qed
qed

text \<open>Polygon \<open>J\<close> in \<open>real^2\<close> is connected (homeomorphic image of connected
  \<open>sphere 0 1\<close>) and not a singleton; hence each \<open>v \<in> J\<close> is a limit point of
  \<open>J\<close> (no isolated points).\<close>

lemma polygon_islimpt:
  fixes J :: "(real^2) set" and v :: "real^2"
  assumes hJ: "geotop_is_polygon J" and hv: "v \<in> J"
  shows "v islimpt J"
proof -
  have h_homeo: "J homeomorphic sphere (0::real^2) 1"
    by (rule polygon_homeomorphic_S1_helper[OF hJ])
  have h_DIM: "(2::nat) \<le> DIM(real^2)" by simp
  have h_S1_conn: "connected (sphere (0::real^2) 1)"
    by (rule connected_sphere[OF h_DIM])
  have h_J_conn: "connected J"
    using h_homeo h_S1_conn homeomorphic_connectedness by (by100 blast)
  (** \<open>J\<close> has at least two points (homeomorphic image of \<open>S\<^sup>1\<close> in \<open>real^2\<close>). **)
  obtain ff ff' where hff': "homeomorphism J (sphere (0::real^2) 1) ff ff'"
    using h_homeo unfolding homeomorphic_def by (by100 blast)
  have hff_inv: "homeomorphism (sphere (0::real^2) 1) J ff' ff"
    by (rule homeomorphism_symD[OF hff'])
  define f where "f = ff'"
  define f' where "f' = ff"
  have hff_homeo: "homeomorphism (sphere (0::real^2) 1) J f f'"
    unfolding f_def f'_def by (rule hff_inv)
  define p :: "real^2" where "p = vector [1, 0]"
  define q :: "real^2" where "q = vector [-1, 0]"
  have hp_norm: "norm p = 1"
  proof -
    have h1: "p $ 1 = 1" unfolding p_def by simp
    have h2: "p $ 2 = 0" unfolding p_def by simp
    have hsum: "(\<Sum>i\<in>(UNIV::2 set). (p $ i)\<^sup>2) = 1"
      using h1 h2 by (simp add: UNIV_2)
    show ?thesis unfolding norm_vec_def L2_set_def using hsum by simp
  qed
  have hq_norm: "norm q = 1"
  proof -
    have h1: "q $ 1 = -1" unfolding q_def by simp
    have h2: "q $ 2 = 0" unfolding q_def by simp
    have hsum: "(\<Sum>i\<in>(UNIV::2 set). (q $ i)\<^sup>2) = 1"
      using h1 h2 by (simp add: UNIV_2)
    show ?thesis unfolding norm_vec_def L2_set_def using hsum by simp
  qed
  have hp_S1: "p \<in> sphere (0::real^2) 1" using hp_norm by (by100 simp)
  have hq_S1: "q \<in> sphere (0::real^2) 1" using hq_norm by (by100 simp)
  have hpq: "p \<noteq> q"
  proof
    assume "p = q"
    hence "p $ 1 = q $ 1" by simp
    thus False unfolding p_def q_def by simp
  qed
  have hf_im: "f ` (sphere (0::real^2) 1) = J"
    using hff_homeo homeomorphism_image1 by (by100 blast)
  have hfp_J: "f p \<in> J"
    using hp_S1 hf_im by (by100 blast)
  have hfq_J: "f q \<in> J"
    using hq_S1 hf_im by (by100 blast)
  have hfp_ne_fq: "f p \<noteq> f q"
  proof
    assume "f p = f q"
    hence "f' (f p) = f' (f q)" by (by100 simp)
    moreover have "f' (f p) = p" by (rule homeomorphism_apply1[OF hff_homeo hp_S1])
    moreover have "f' (f q) = q" by (rule homeomorphism_apply1[OF hff_homeo hq_S1])
    ultimately have "p = q" by (by100 simp)
    thus False using hpq by (by100 simp)
  qed
  have h_J_not_sing: "\<And>x. J \<noteq> {x}"
  proof -
    fix x
    show "J \<noteq> {x}"
    proof
      assume hJ_sing: "J = {x}"
      have "f p = x" using hfp_J hJ_sing by (by100 blast)
      moreover have "f q = x" using hfq_J hJ_sing by (by100 blast)
      ultimately have "f p = f q" by (by100 simp)
      thus False using hfp_ne_fq by (by100 simp)
    qed
  qed
  show "v islimpt J"
    by (rule connected_imp_perfect[OF h_J_conn hv h_J_not_sing])
qed
(** from \<S>2 Theorem 3 (geotop.tex:579)
    LATEX VERSION: No broken line separates R^2. That is, if B is a broken line in R^2,
      then R^2 - B is connected. **)
theorem Theorem_GT_2_3:
  fixes B :: "(real^2) set"
  assumes hB: "geotop_is_broken_line B"
  shows "top1_connected_on (UNIV - B)
           (subspace_topology UNIV geotop_euclidean_topology (UNIV - B))"
  (** Moise proof (geotop.tex:579): broken line = polyhedral arc; apply
      `top1_connected_complement_of_geotop_arc` with DIM(real^2)=2. **)
proof -
  have harc: "geotop_is_arc B (subspace_topology UNIV geotop_euclidean_topology B)"
    using hB unfolding geotop_is_broken_line_def by blast
  show ?thesis by (rule top1_connected_complement_of_geotop_arc[OF harc]) simp
qed

(** from \<S>2 Theorem 4 (geotop.tex:593)
    LATEX VERSION: Let X be a topological space and let U be an open set. Then Fr U = \<bar>U\<close> - U. **)
theorem Theorem_GT_2_4:
  assumes "is_topology_on X T"
  assumes "U \<in> T"
  assumes "U \<subseteq> X"
  shows "geotop_frontier X T U = closure_on X T U - U"
proof -
  have hXXU: "X - (X - U) = U"
    using assms(3) by (by100 blast)
  have hXU_in_T: "X - (X - U) \<in> T"
    using assms(2) hXXU by (by100 simp)
  have hXU_sub: "X - U \<subseteq> X" by (by100 blast)
  have hXU_closed: "closedin_on X T (X - U)"
    by (rule closedin_intro[OF hXU_sub hXU_in_T])
  have hcl_XU: "closure_on X T (X - U) = X - U"
    using closure_on_subset_of_closed[OF hXU_closed subset_refl]
          subset_closure_on[of "X - U" X T]
    by (by100 blast)
  have hcl_U_sub_X: "closure_on X T U \<subseteq> X"
    by (rule closure_on_subset_carrier[OF assms(1) assms(3)])
  show ?thesis
    unfolding geotop_frontier_def
    using hcl_XU hcl_U_sub_X by (by100 blast)
qed

(** Bridge: is_limit_point_of on UNIV with geotop_euclidean_topology equals
    HOL-Analysis `islimpt`. **)
lemma is_limit_point_of_UNIV_geotop_iff_islimpt:
  fixes P :: "'a::real_normed_vector" and A :: "'a set"
  shows "is_limit_point_of P A UNIV geotop_euclidean_topology \<longleftrightarrow> P islimpt A"
proof
  assume "is_limit_point_of P A UNIV geotop_euclidean_topology"
  hence hf: "\<forall>U\<in>geotop_euclidean_topology. P \<in> U \<longrightarrow> (U - {P}) \<inter> A \<noteq> {}"
    unfolding is_limit_point_of_def neighborhood_of_def intersects_def by blast
  show "P islimpt A"
    unfolding islimpt_def
  proof (intro allI impI)
    fix T assume hPT: "P \<in> T" and hopen: "open T"
    have hT_geotop: "T \<in> (geotop_euclidean_topology :: 'a set set)"
      using hopen geotop_euclidean_topology_eq_open_sets[where 'a='a]
      unfolding top1_open_sets_def by auto
    have "(T - {P}) \<inter> A \<noteq> {}"
      using hf hT_geotop hPT by blast
    thus "\<exists>y\<in>A. y \<in> T \<and> y \<noteq> P" by blast
  qed
next
  assume "P islimpt A"
  hence hlimpt: "\<forall>T. P \<in> T \<longrightarrow> open T \<longrightarrow> (\<exists>y\<in>A. y \<in> T \<and> y \<noteq> P)"
    unfolding islimpt_def by blast
  show "is_limit_point_of P A UNIV geotop_euclidean_topology"
    unfolding is_limit_point_of_def neighborhood_of_def intersects_def
  proof (intro conjI allI impI)
    show "P \<in> UNIV" by simp
    show "A \<subseteq> UNIV" by simp
    fix U assume "U \<in> geotop_euclidean_topology \<and> P \<in> U"
    then have hUopen: "open U" and hPU: "P \<in> U"
      using geotop_euclidean_topology_eq_open_sets
      unfolding top1_open_sets_def by auto
    then obtain y where "y \<in> A" "y \<in> U" "y \<noteq> P"
      using hlimpt by blast
    thus "(U - {P}) \<inter> A \<noteq> {}" by blast
  qed
qed

(** Helper: for a geotop-1-sphere J in euclidean_space with DIM \<ge> 2, every
    component of UNIV - J has J as its frontier. **)
lemma top1_frontier_component_of_geotop_1sphere:
  fixes J U :: "'a::euclidean_space set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes hU_ex: "\<exists>P\<in>UNIV - J. U = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
  assumes hdim: "2 \<le> DIM('a)"
  shows "J = geotop_frontier UNIV geotop_euclidean_topology U"
proof -
  obtain f where hhomeo: "top1_homeomorphism_on J
                           (subspace_topology UNIV geotop_euclidean_topology J)
                           (geotop_std_sphere::'a set)
                           (subspace_topology UNIV geotop_euclidean_topology
                              (geotop_std_sphere::'a set)) f"
    using hJ unfolding geotop_is_n_sphere_def by blast
  have hhomeo_HOL: "J homeomorphic (geotop_std_sphere::'a set)"
    by (rule top1_homeomorphism_on_geotop_imp_HOL_homeomorphic[OF hhomeo])
  have hstd_eq: "(geotop_std_sphere::'a set) = sphere 0 1"
    unfolding geotop_std_sphere_def sphere_def by simp
  have hJ_sphere: "J homeomorphic sphere (0::'a) 1"
    using hhomeo_HOL hstd_eq by simp
  obtain P where hP_notJ: "P \<in> UNIV - J"
             and hU_eq: "U = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    using hU_ex by blast
  have hU_comp: "U = connected_component_set (- J) P"
    using hU_eq geotop_component_at_UNIV_eq_connected_component_set
    by (simp add: Compl_eq_Diff_UNIV)
  have hP_compl: "P \<in> - J" using hP_notJ by (simp add: Compl_eq_Diff_UNIV)
  have hU_in_components: "U \<in> components (- J)"
    unfolding components_def using hU_comp hP_compl by blast
  have hfrontier: "frontier U = J"
    by (rule Jordan_Brouwer_frontier[OF hJ_sphere hU_in_components hdim])
  show ?thesis
    using hfrontier geotop_frontier_UNIV_eq_frontier by metis
qed

(** Helper: for a geotop-1-sphere J in euclidean_space with DIM \<ge> 2, there
    exists a bounded component and an unbounded component of UNIV - J. **)
lemma geotop_1sphere_has_bounded_unbounded_components:
  fixes J :: "'a::euclidean_space set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  assumes hdim: "2 \<le> DIM('a)"
  shows "(\<exists>c. c \<in> components (- J) \<and> bounded c) \<and>
         (\<exists>c. c \<in> components (- J) \<and> \<not> bounded c)"
proof -
  obtain f where hhomeo: "top1_homeomorphism_on J
                           (subspace_topology UNIV geotop_euclidean_topology J)
                           (geotop_std_sphere::'a set)
                           (subspace_topology UNIV geotop_euclidean_topology
                              (geotop_std_sphere::'a set)) f"
    using hJ unfolding geotop_is_n_sphere_def by blast
  have hhomeo_HOL: "J homeomorphic (geotop_std_sphere::'a set)"
    by (rule top1_homeomorphism_on_geotop_imp_HOL_homeomorphic[OF hhomeo])
  have hstd_eq: "(geotop_std_sphere::'a set) = sphere 0 1"
    unfolding geotop_std_sphere_def sphere_def by simp
  have hJ_sphere: "J homeomorphic sphere (0::'a) 1"
    using hhomeo_HOL hstd_eq by simp
  have hnot_conn: "\<not> connected (- J)"
    using Jordan_Brouwer_separation[OF hJ_sphere] by simp
  (** J is bounded (compact, as homeomorphic image of sphere which is compact). **)
  have hJ_compact: "compact J"
    by (metis compact_sphere hJ_sphere homeomorphic_compactness)
  have hJ_bounded: "bounded J"
    using hJ_compact compact_imp_bounded by blast
  have hbounded_neg: "bounded (- (- J))"
    by (simp add: hJ_bounded)
  have hbd_comp: "\<exists>c. c \<in> components (- J) \<and> bounded c"
    using cobounded_has_bounded_component[OF hbounded_neg hnot_conn] hdim by blast
  have hunbd_comp: "\<exists>c. c \<in> components (- J) \<and> \<not> bounded c"
    using cobounded_unbounded_components[OF hbounded_neg] by blast
  show ?thesis using hbd_comp hunbd_comp by blast
qed

(** Bridge: geotop_bounded_R2 equals HOL-Analysis `bounded` on real^2. **)
lemma geotop_bounded_R2_iff_bounded:
  fixes A :: "(real^2) set"
  shows "geotop_bounded_R2 A \<longleftrightarrow> bounded A"
proof
  assume "geotop_bounded_R2 A"
  then obtain r where hr: "r > 0" "\<forall>P\<in>A. norm P < r"
    unfolding geotop_bounded_R2_def by blast
  then show "bounded A"
    unfolding bounded_iff by (meson less_le_not_le nle_le)
next
  assume "bounded A"
  then obtain a where ha: "\<forall>x\<in>A. norm x \<le> a"
    unfolding bounded_iff by blast
  let ?r = "max a 0 + 1"
  have "?r > 0" by simp
  moreover have "\<forall>P\<in>A. norm P < ?r"
    using ha by (smt (verit) max.cobounded1)
  ultimately show "geotop_bounded_R2 A"
    unfolding geotop_bounded_R2_def by blast
qed

(** Helper: given a 1-sphere J in R^2, polygon_interior J is a bounded connected
    component of UNIV - J, and polygon_exterior J is an unbounded one. **)
lemma geotop_polygon_interior_is_bounded_component:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "\<exists>P\<in>UNIV - J.
           geotop_polygon_interior J
           = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
proof -
  have hdim: "(2::nat) \<le> DIM(real^2)" by simp
  have hexists_bd: "\<exists>c. c \<in> components (- J) \<and> bounded c"
    using geotop_1sphere_has_bounded_unbounded_components[OF hJ hdim] by blast
  then obtain C where hC_comp: "C \<in> components (- J)" and hC_bd: "bounded C" by blast
  (** Show C satisfies the polygon_interior predicate. **)
  obtain P where hP: "P \<in> -J" and hC_eq: "C = connected_component_set (- J) P"
    using hC_comp unfolding components_def by blast
  have hC_sub: "C \<subseteq> UNIV - J"
    using hC_eq connected_component_subset by (metis Compl_eq_Diff_UNIV)
  have hC_bdR2: "geotop_bounded_R2 C"
    using hC_bd geotop_bounded_R2_iff_bounded by blast
  have hC_conn_HOL: "connected C"
    using hC_comp in_components_connected by blast
  have hC_topconn: "top1_connected_on C
                     (subspace_topology UNIV geotop_euclidean_topology C)"
    using hC_conn_HOL top1_connected_on_geotop_iff_connected by blast
  have hC_comp_at: "\<forall>Q\<in>C. geotop_component_at UNIV geotop_euclidean_topology
                             ((UNIV::(real^2) set) - J) Q = C"
  proof
    fix Q assume hQC: "Q \<in> C"
    have hQ_compl: "Q \<in> -J"
      using hQC hC_eq connected_component_subset by blast
    have hC_comp_Q: "C = connected_component_set (- J) Q"
      using connected_component_eq hC_eq hQC by blast
    then have "connected_component_set (UNIV - J) Q = C"
      using Compl_eq_Diff_UNIV by metis
    thus "geotop_component_at UNIV geotop_euclidean_topology
            ((UNIV::(real^2) set) - J) Q = C"
      using geotop_component_at_UNIV_eq_connected_component_set by metis
  qed
  have hC_ne: "C \<noteq> {}" using hC_comp in_components_nonempty by blast
  have hpred_C: "C \<noteq> {} \<and> C \<subseteq> UNIV - J \<and> geotop_bounded_R2 C \<and>
                 top1_connected_on C (subspace_topology UNIV geotop_euclidean_topology C) \<and>
                 (\<forall>P\<in>C. geotop_component_at UNIV geotop_euclidean_topology
                           ((UNIV::(real^2) set) - J) P = C)"
    using hC_ne hC_sub hC_bdR2 hC_topconn hC_comp_at by blast
  have hpred_ex: "\<exists>I. I \<noteq> {} \<and> I \<subseteq> UNIV - J \<and> geotop_bounded_R2 I \<and>
                      top1_connected_on I (subspace_topology UNIV geotop_euclidean_topology I) \<and>
                      (\<forall>P\<in>I. geotop_component_at UNIV geotop_euclidean_topology
                                ((UNIV::(real^2) set) - J) P = I)"
    using hpred_C by blast
  (** SOME picks such an I. Let I = polygon_interior J. **)
  let ?I = "geotop_polygon_interior J"
  have hI_pred: "?I \<noteq> {} \<and> ?I \<subseteq> UNIV - J \<and> geotop_bounded_R2 ?I \<and>
                 top1_connected_on ?I (subspace_topology UNIV geotop_euclidean_topology ?I) \<and>
                 (\<forall>P\<in>?I. geotop_component_at UNIV geotop_euclidean_topology
                            ((UNIV::(real^2) set) - J) P = ?I)"
    unfolding geotop_polygon_interior_def
    by (rule someI_ex[OF hpred_ex])
  have hI_ne: "?I \<noteq> {}" using hI_pred by blast
  have hI_sub: "?I \<subseteq> UNIV - J" using hI_pred by blast
  obtain P where hP_I: "P \<in> ?I" using hI_ne by blast
  have hP_notJ: "P \<in> UNIV - J" using hP_I hI_sub by blast
  have hI_eq: "?I = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    using hI_pred hP_I by metis
  show ?thesis using hP_notJ hI_eq by blast
qed

lemma geotop_polygon_exterior_is_component:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "\<exists>P\<in>UNIV - J.
           geotop_polygon_exterior J
           = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
proof -
  have hdim: "(2::nat) \<le> DIM(real^2)" by simp
  have hexists_unbd: "\<exists>c. c \<in> components (- J) \<and> \<not> bounded c"
    using geotop_1sphere_has_bounded_unbounded_components[OF hJ hdim] by blast
  then obtain C where hC_comp: "C \<in> components (- J)" and hC_unbd: "\<not> bounded C" by blast
  obtain P where hP: "P \<in> -J" and hC_eq: "C = connected_component_set (- J) P"
    using hC_comp unfolding components_def by blast
  have hC_sub: "C \<subseteq> UNIV - J"
    using hC_eq connected_component_subset by (metis Compl_eq_Diff_UNIV)
  have hC_unbdR2: "\<not> geotop_bounded_R2 C"
    using hC_unbd geotop_bounded_R2_iff_bounded by blast
  have hC_conn_HOL: "connected C"
    using hC_comp in_components_connected by blast
  have hC_topconn: "top1_connected_on C
                     (subspace_topology UNIV geotop_euclidean_topology C)"
    using hC_conn_HOL top1_connected_on_geotop_iff_connected by blast
  have hC_comp_at: "\<forall>Q\<in>C. geotop_component_at UNIV geotop_euclidean_topology
                             ((UNIV::(real^2) set) - J) Q = C"
  proof
    fix Q assume hQC: "Q \<in> C"
    have hQ_compl: "Q \<in> -J"
      using hQC hC_eq connected_component_subset by blast
    have hC_comp_Q: "C = connected_component_set (- J) Q"
      using connected_component_eq hC_eq hQC by blast
    then have "connected_component_set (UNIV - J) Q = C"
      using Compl_eq_Diff_UNIV by metis
    thus "geotop_component_at UNIV geotop_euclidean_topology
            ((UNIV::(real^2) set) - J) Q = C"
      using geotop_component_at_UNIV_eq_connected_component_set by metis
  qed
  have hC_ne: "C \<noteq> {}" using hC_comp in_components_nonempty by blast
  have hpred_C: "C \<noteq> {} \<and> C \<subseteq> UNIV - J \<and> \<not> geotop_bounded_R2 C \<and>
                 top1_connected_on C (subspace_topology UNIV geotop_euclidean_topology C) \<and>
                 (\<forall>P\<in>C. geotop_component_at UNIV geotop_euclidean_topology
                           ((UNIV::(real^2) set) - J) P = C)"
    using hC_ne hC_sub hC_unbdR2 hC_topconn hC_comp_at by blast
  have hpred_ex: "\<exists>E. E \<noteq> {} \<and> E \<subseteq> UNIV - J \<and> \<not> geotop_bounded_R2 E \<and>
                      top1_connected_on E (subspace_topology UNIV geotop_euclidean_topology E) \<and>
                      (\<forall>P\<in>E. geotop_component_at UNIV geotop_euclidean_topology
                                ((UNIV::(real^2) set) - J) P = E)"
    using hpred_C by blast
  let ?E = "geotop_polygon_exterior J"
  have hE_pred: "?E \<noteq> {} \<and> ?E \<subseteq> UNIV - J \<and> \<not> geotop_bounded_R2 ?E \<and>
                 top1_connected_on ?E (subspace_topology UNIV geotop_euclidean_topology ?E) \<and>
                 (\<forall>P\<in>?E. geotop_component_at UNIV geotop_euclidean_topology
                            ((UNIV::(real^2) set) - J) P = ?E)"
    unfolding geotop_polygon_exterior_def
    by (rule someI_ex[OF hpred_ex])
  have hE_ne: "?E \<noteq> {}" using hE_pred by blast
  have hE_sub: "?E \<subseteq> UNIV - J" using hE_pred by blast
  obtain P where hP_E: "P \<in> ?E" using hE_ne by blast
  have hP_notJ: "P \<in> UNIV - J" using hP_E hE_sub by blast
  have hE_eq: "?E = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    using hE_pred hP_E by metis
  show ?thesis using hP_notJ hE_eq by blast
qed

(** from \<S>2 Theorem 6 (geotop.tex:611)
    LATEX VERSION: Let J, I, E be as in Theorem 5. Then J = Fr I = Fr E. **)
theorem Theorem_GT_2_6:
  fixes J :: "(real^2) set"
  assumes hJ_poly: "geotop_is_polygon J"
  shows "J = geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
    and "J = geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_exterior J)"
proof -
  have hJ_sphere: "geotop_is_n_sphere J
                     (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ_poly unfolding geotop_is_polygon_def by blast
  have hdim: "(2::nat) \<le> DIM(real^2)" by simp
  (** Part 1: polygon_interior J is a component of UNIV - J, apply helper. **)
  have hI_comp: "\<exists>P\<in>UNIV - J.
                   geotop_polygon_interior J
                   = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    by (rule geotop_polygon_interior_is_bounded_component[OF hJ_sphere])
  show "J = geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_interior J)"
    by (rule top1_frontier_component_of_geotop_1sphere[OF hJ_sphere hI_comp hdim])
next
  have hJ_sphere: "geotop_is_n_sphere J
                     (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ_poly unfolding geotop_is_polygon_def by blast
  have hdim: "(2::nat) \<le> DIM(real^2)" by simp
  have hE_comp: "\<exists>P\<in>UNIV - J.
                   geotop_polygon_exterior J
                   = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    by (rule geotop_polygon_exterior_is_component[OF hJ_sphere])
  show "J = geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_exterior J)"
    by (rule top1_frontier_component_of_geotop_1sphere[OF hJ_sphere hE_comp hdim])
qed

(** from \<S>2 Theorem 5 (geotop.tex:596)
    LATEX VERSION: Let J be a polygon in R^2, with interior I and exterior E. Then every point
      of J is a limit point both of I and of E.
    (Placed here, after Theorem_GT_2_6, to reuse the frontier equality.) **)
theorem Theorem_GT_2_5:
  fixes J :: "(real^2) set"
  assumes hJ_poly: "geotop_is_polygon J"
  shows "\<forall>P\<in>J. is_limit_point_of P (geotop_polygon_interior J) UNIV geotop_euclidean_topology
             \<and> is_limit_point_of P (geotop_polygon_exterior J) UNIV geotop_euclidean_topology"
  (** Moise proof (geotop.tex:596): J = Fr I = Fr E (Theorem 2.6). For P \<in> J,
      P \<in> Fr I = closure I \<inter> closure (UNIV - I). Since P \<in> J and I \<subseteq> UNIV - J,
      so P \<notin> I. P \<in> closure I and P \<notin> I means P is a limit point of I. Similarly E. **)
proof
  fix P assume hPJ: "P \<in> J"
  have hJ_sphere: "geotop_is_n_sphere J
                     (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ_poly unfolding geotop_is_polygon_def by blast
  (** Interior part. **)
  obtain Pi where hPi_notJ: "Pi \<in> UNIV - J"
            and hI_eq: "geotop_polygon_interior J
                        = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) Pi"
    using geotop_polygon_interior_is_bounded_component[OF hJ_sphere] by blast
  have hI_sub: "geotop_polygon_interior J \<subseteq> UNIV - J"
    using hI_eq connected_component_subset geotop_component_at_UNIV_eq_connected_component_set
    by metis
  have hdim: "(2::nat) \<le> DIM(real^2)" by simp
  have hI_front: "geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_interior J) = J"
    using Theorem_GT_2_6(1)[OF hJ_poly] by simp
  have hI_front_HOL: "frontier (geotop_polygon_interior J) = J"
    using hI_front geotop_frontier_UNIV_eq_frontier by metis
	  have hP_closureI: "P \<in> closure (geotop_polygon_interior J)"
	    using hPJ hI_front_HOL unfolding Elementary_Topology.frontier_def by blast
  have hP_notI: "P \<notin> geotop_polygon_interior J"
    using hPJ hI_sub by blast
  have hP_islimptI: "P islimpt (geotop_polygon_interior J)"
    by (simp add: islimpt_in_closure hP_closureI hP_notI)
  have hlim_I: "is_limit_point_of P (geotop_polygon_interior J) UNIV geotop_euclidean_topology"
    using hP_islimptI is_limit_point_of_UNIV_geotop_iff_islimpt by blast
  (** Exterior part, same structure. **)
  obtain Pe where hPe_notJ: "Pe \<in> UNIV - J"
            and hE_eq: "geotop_polygon_exterior J
                        = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) Pe"
    using geotop_polygon_exterior_is_component[OF hJ_sphere] by blast
  have hE_sub: "geotop_polygon_exterior J \<subseteq> UNIV - J"
    using hE_eq connected_component_subset geotop_component_at_UNIV_eq_connected_component_set
    by metis
  have hE_front: "geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_exterior J) = J"
    using Theorem_GT_2_6(2)[OF hJ_poly] by simp
  have hE_front_HOL: "frontier (geotop_polygon_exterior J) = J"
    using hE_front geotop_frontier_UNIV_eq_frontier by metis
  have hP_closureE: "P \<in> closure (geotop_polygon_exterior J)"
    using hPJ hE_front_HOL unfolding Elementary_Topology.frontier_def by blast
  have hP_notE: "P \<notin> geotop_polygon_exterior J"
    using hPJ hE_sub by blast
  have hP_islimptE: "P islimpt (geotop_polygon_exterior J)"
    by (simp add: hP_closureE hP_notE islimpt_in_closure)
  have hlim_E: "is_limit_point_of P (geotop_polygon_exterior J) UNIV geotop_euclidean_topology"
    using hP_islimptE is_limit_point_of_UNIV_geotop_iff_islimpt by blast
  show "is_limit_point_of P (geotop_polygon_interior J) UNIV geotop_euclidean_topology
      \<and> is_limit_point_of P (geotop_polygon_exterior J) UNIV geotop_euclidean_topology"
    using hlim_I hlim_E by blast
qed

(** from \<S>2: \<theta>-graph (geotop.tex:619)
    LATEX VERSION: Let M be the union of three arcs B_1, B_2, B_3 with the same end-points P, Q
      but with disjoint interiors. Then M is called a \<theta>-graph.
    The endpoint/interior primitives are defined in GeoTopBase because Section 1
    broken-line infrastructure already needs them. **)
definition geotop_is_theta_graph ::
  "'a::real_normed_vector set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_is_theta_graph M B1 B2 B3 E \<longleftrightarrow>
    M = B1 \<union> B2 \<union> B3 \<and>
    geotop_arc_endpoints B1 E \<and> geotop_arc_endpoints B2 E \<and> geotop_arc_endpoints B3 E \<and>
    geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = {} \<and>
    geotop_arc_interior B1 E \<inter> geotop_arc_interior B3 E = {} \<and>
    geotop_arc_interior B2 E \<inter> geotop_arc_interior B3 E = {}"

text \<open>A polyhedral \<theta>-graph is a \<theta>-graph whose arcs are broken lines.\<close>
definition geotop_is_polyhedral_theta_graph ::
  "'a::real_normed_vector set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "geotop_is_polyhedral_theta_graph M B1 B2 B3 E \<longleftrightarrow>
    geotop_is_theta_graph M B1 B2 B3 E \<and>
    geotop_is_broken_line B1 \<and> geotop_is_broken_line B2 \<and> geotop_is_broken_line B3"

text \<open>Direct accessor lemmas for the polyhedral-theta-graph predicate to avoid
  repeated unfolding-and-blast in proofs (which can flake under load).\<close>

lemma polyhedral_theta_graph_imp_theta:
  "geotop_is_polyhedral_theta_graph M B1 B2 B3 E \<Longrightarrow> geotop_is_theta_graph M B1 B2 B3 E"
  unfolding geotop_is_polyhedral_theta_graph_def by (rule conjunct1)


lemma polyhedral_theta_graph_imp_bl_1:
  "geotop_is_polyhedral_theta_graph M B1 B2 B3 E \<Longrightarrow> geotop_is_broken_line B1"
  unfolding geotop_is_polyhedral_theta_graph_def by (by100 simp)

lemma polyhedral_theta_graph_imp_bl_2:
  "geotop_is_polyhedral_theta_graph M B1 B2 B3 E \<Longrightarrow> geotop_is_broken_line B2"
  unfolding geotop_is_polyhedral_theta_graph_def by (by100 simp)

lemma polyhedral_theta_graph_imp_bl_3:
  "geotop_is_polyhedral_theta_graph M B1 B2 B3 E \<Longrightarrow> geotop_is_broken_line B3"
  unfolding geotop_is_polyhedral_theta_graph_def by (by100 simp)

subsection \<open>Pair of arcs sharing endpoints is a polygon\<close>

text \<open>Helper used by Theorem_GT_2_7 and Theorem_GT_2_8: if two broken lines
  share endpoints \<open>{P, Q}\<close> with disjoint open interiors, then their union is
  a polygon (i.e., a polyhedral 1-sphere).\<close>

lemma arc_join_image_eq:
  fixes f g :: "real \<Rightarrow> 'a::topological_space"
  assumes "pathfinish f = pathstart g"
  shows "path_image (f +++ g) = path_image f \<union> path_image g"
  using assms by (rule path_image_join)

lemma pair_of_arcs_image_homeomorphic_sphere:
  fixes B1 B2 :: "(real^2) set" and E :: "(real^2) set"
  assumes hE1: "geotop_arc_endpoints B1 E"
      and hE2: "geotop_arc_endpoints B2 E"
      and h_disj: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = {}"
      and h_distinct: "B1 \<noteq> B2"
  shows "B1 \<union> B2 homeomorphic sphere (0::real^2) 1"
proof -
  obtain f1 :: "real \<Rightarrow> real^2" where
    harc1: "arc f1" and himg1: "path_image f1 = B1" and hE1_eq: "E = {pathstart f1, pathfinish f1}"
    using arc_endpoints_imp_arc_HOL[OF hE1] by blast
  obtain f2 :: "real \<Rightarrow> real^2" where
    harc2: "arc f2" and himg2: "path_image f2 = B2" and hE2_eq: "E = {pathstart f2, pathfinish f2}"
    using arc_endpoints_imp_arc_HOL[OF hE2] by blast
  define P where "P = pathstart f1"
  define Q where "Q = pathfinish f1"
  have hPQ_E: "{P, Q} = E" using hE1_eq P_def Q_def by simp
  have hPQ_card: "card E = 2" using hE1 unfolding geotop_arc_endpoints_def by blast
  have hP_ne_Q: "P \<noteq> Q"
  proof
    assume "P = Q"
    hence "{P, Q} = {P}" by simp
    hence "card E = card {P}" using hPQ_E by simp
    hence "card E = 1" by simp
    thus False using hPQ_card by simp
  qed
  text \<open>Either f2 starts at P (forward) or starts at Q (reverse).\<close>
  define g2 :: "real \<Rightarrow> real^2"
    where "g2 = (if pathstart f2 = Q then f2 else reversepath f2)"
  have h_g2_arc: "arc g2"
  proof (cases "pathstart f2 = Q")
    case True thus ?thesis unfolding g2_def using harc2 by simp
  next
    case False thus ?thesis unfolding g2_def using harc2 arc_reversepath by simp
  qed
  have hPQ_set: "{pathstart f2, pathfinish f2} = {P, Q}" using hE2_eq hPQ_E by simp
  have h_g2_pathstart: "pathstart g2 = Q"
  proof (cases "pathstart f2 = Q")
    case True thus ?thesis unfolding g2_def by simp
	  next
	    case False
	    have "pathstart f2 \<in> {P, Q}" using hPQ_set by blast
	    hence h_ps: "pathstart f2 = P" using False by blast
	    hence h_pf: "pathfinish f2 = Q" using hPQ_set hP_ne_Q by (metis doubleton_eq_iff)
    show ?thesis unfolding g2_def using False h_pf by (simp add: pathstart_reversepath)
  qed
  have h_g2_pathfinish: "pathfinish g2 = P"
  proof (cases "pathstart f2 = Q")
    case True
    hence h_pf: "pathfinish f2 = P" using hPQ_set hP_ne_Q by (metis doubleton_eq_iff)
    show ?thesis unfolding g2_def using True h_pf by simp
	  next
	    case False
	    have "pathstart f2 \<in> {P, Q}" using hPQ_set by blast
	    hence h_ps: "pathstart f2 = P" using False by blast
	    show ?thesis unfolding g2_def using False h_ps by (simp add: pathfinish_reversepath)
	  qed
  have h_g2_image: "path_image g2 = B2"
    unfolding g2_def using himg2 path_image_reversepath by simp
  text \<open>Set up join.\<close>
  have h_pf1_eq_ps_g2: "pathfinish f1 = pathstart g2"
    using h_g2_pathstart Q_def by simp
  have h_pf2_eq_ps_f1: "pathfinish g2 = pathstart f1"
    using h_g2_pathfinish P_def by simp
  text \<open>The two path-images intersect only at \<open>{P, Q}\<close>.\<close>
  have h_inter_PQ: "path_image f1 \<inter> path_image g2 \<subseteq> {pathstart f1, pathstart g2}"
  proof -
    have h_inter: "B1 \<inter> B2 \<subseteq> E"
      using h_disj unfolding geotop_arc_interior_def by blast
    have h_subs: "{pathstart f1, pathstart g2} = {P, Q}"
      using P_def h_g2_pathstart by simp
    show ?thesis using h_inter himg1 h_g2_image hPQ_E h_subs by blast
  qed
  have h_simple_join: "simple_path (f1 +++ g2)"
    by (rule simple_path_join_loop[OF harc1 h_g2_arc h_pf1_eq_ps_g2 h_pf2_eq_ps_f1 h_inter_PQ])
  have h_loop: "pathfinish (f1 +++ g2) = pathstart (f1 +++ g2)"
    by (simp add: pathstart_join pathfinish_join h_pf2_eq_ps_f1)
  have h_join_image: "path_image (f1 +++ g2) = B1 \<union> B2"
    using h_pf1_eq_ps_g2 himg1 h_g2_image by (subst path_image_join) auto
  text \<open>Apply HOL-Analysis to get homeomorphism with the unit sphere in complex.\<close>
  have h_pi_pos: "(0::real) < 1" by simp
  have h_to_C_sphere: "B1 \<union> B2 homeomorphic sphere (0::complex) 1"
    using homeomorphic_simple_path_image_circle[OF h_simple_join h_loop h_pi_pos]
          h_join_image
    by simp
  have h_DIM: "DIM(complex) = DIM(real^2)" by simp
  have h_spheres_homeo: "sphere (0::complex) 1 homeomorphic sphere (0::real^2) 1"
    using homeomorphic_spheres_gen[of 1 1 "0::complex" "0::real^2"] h_DIM by simp
  show ?thesis using h_to_C_sphere h_spheres_homeo homeomorphic_trans by blast
qed

text \<open>Refine a broken-line complex so that a specific point on the line
  becomes a vertex of the complex.\<close>

lemma broken_line_make_vertex:
  fixes B :: "(real^2) set" and P :: "real^2"
  assumes hB: "geotop_is_broken_line B"
      and hP: "P \<in> B"
  shows "\<exists>K. geotop_is_complex K \<and> geotop_complex_is_1dim K
              \<and> geotop_polyhedron K = B \<and> {P} \<in> K"
proof -
  from hB obtain K0 where hK0_complex: "geotop_is_complex K0"
                       and hK0_1dim: "geotop_complex_is_1dim K0"
                       and hK0_poly: "geotop_polyhedron K0 = B"
    unfolding geotop_is_broken_line_def by blast
  have hP_in_union: "P \<in> \<Union>K0" using hP hK0_poly unfolding geotop_polyhedron_def by simp
  obtain \<sigma> where h\<sigma>_K0: "\<sigma> \<in> K0" and hP\<sigma>: "P \<in> \<sigma>" using hP_in_union by blast
  have h\<sigma>_simp: "geotop_is_simplex \<sigma>"
    using hK0_complex h\<sigma>_K0
    unfolding geotop_is_complex_def by simp
  have h\<sigma>_dim_le_1: "\<exists>n. n \<le> 1 \<and> geotop_simplex_dim \<sigma> n"
    using hK0_1dim h\<sigma>_K0 unfolding geotop_complex_is_1dim_def by blast
  obtain n where hn_le: "n \<le> 1" and h\<sigma>_dim: "geotop_simplex_dim \<sigma> n"
    using h\<sigma>_dim_le_1 by blast
  show ?thesis
  proof (cases n)
    case 0
    have h\<sigma>_dim0: "geotop_simplex_dim \<sigma> 0" using h\<sigma>_dim 0 by simp
    have h\<sigma>_singleton: "\<exists>v. \<sigma> = {v}"
      using h\<sigma>_dim0 unfolding geotop_simplex_dim_def
      by (auto simp: geotop_convex_hull_eq_HOL card_1_singleton_iff)
    then obtain v where h\<sigma>_eq: "\<sigma> = {v}" by blast
    have hP_eq_v: "P = v" using hP\<sigma> h\<sigma>_eq by simp
    have "{P} \<in> K0" using hP_eq_v h\<sigma>_K0 h\<sigma>_eq by simp
    thus ?thesis using hK0_complex hK0_1dim hK0_poly by blast
  next
    case (Suc k)
    hence hn_eq_1: "n = 1" using hn_le by simp
    have h\<sigma>_dim1: "geotop_simplex_dim \<sigma> 1" using h\<sigma>_dim hn_eq_1 by simp
    have h_ex: "\<exists>K. geotop_is_complex K \<and> geotop_complex_is_1dim K
              \<and> geotop_polyhedron K = geotop_polyhedron K0 \<and> {P} \<in> K
              \<and> K0 - {\<sigma>} \<subseteq> K
              \<and> (finite K0 \<longrightarrow> finite K)"
      by (rule geotop_complex_subdivide_edge[OF hK0_complex hK0_1dim h\<sigma>_K0 h\<sigma>_dim1 hP\<sigma>])
    then obtain K where hK_complex: "geotop_is_complex K"
                     and hK_1dim: "geotop_complex_is_1dim K"
                     and hK_poly: "geotop_polyhedron K = geotop_polyhedron K0"
                     and hPK: "{P} \<in> K" by blast
    have hK_polyB: "geotop_polyhedron K = B" using hK_poly hK0_poly by simp
    show ?thesis using hK_complex hK_1dim hK_polyB hPK by blast
  qed
qed

text \<open>Refining a complex preserves an existing vertex (subdivide_edge ensures
  K - {edge} \<subseteq> K').\<close>

lemma broken_line_make_two_vertices:
  fixes B :: "(real^2) set" and P Q :: "real^2"
  assumes hB: "geotop_is_broken_line B"
      and hP: "P \<in> B" and hQ: "Q \<in> B"
  shows "\<exists>K. geotop_is_complex K \<and> geotop_complex_is_1dim K
              \<and> geotop_polyhedron K = B \<and> {P} \<in> K \<and> {Q} \<in> K"
proof -
  text \<open>Step 1: refine to add P as vertex.\<close>
  obtain K1 where hK1_complex: "geotop_is_complex K1"
              and hK1_1dim: "geotop_complex_is_1dim K1"
              and hK1_poly: "geotop_polyhedron K1 = B"
              and hPK1: "{P} \<in> K1"
    using broken_line_make_vertex[OF hB hP] by blast
  text \<open>Step 2: re-cast \<open>K1\<close> as a broken line, then refine to add Q as vertex.\<close>
  have hQ_K1: "Q \<in> B" using hQ by simp
  have hQ_in_union: "Q \<in> \<Union>K1" using hQ_K1 hK1_poly unfolding geotop_polyhedron_def by simp
  obtain \<sigma> where h\<sigma>_K1: "\<sigma> \<in> K1" and hQ\<sigma>: "Q \<in> \<sigma>" using hQ_in_union by blast
  have h\<sigma>_dim_le_1: "\<exists>n. n \<le> 1 \<and> geotop_simplex_dim \<sigma> n"
    using hK1_1dim h\<sigma>_K1 unfolding geotop_complex_is_1dim_def by blast
  obtain n where hn_le: "n \<le> 1" and h\<sigma>_dim: "geotop_simplex_dim \<sigma> n"
    using h\<sigma>_dim_le_1 by blast
  show ?thesis
  proof (cases n)
    case 0
    have h\<sigma>_dim0: "geotop_simplex_dim \<sigma> 0" using h\<sigma>_dim 0 by simp
    have h\<sigma>_singleton: "\<exists>v. \<sigma> = {v}"
      using h\<sigma>_dim0 unfolding geotop_simplex_dim_def
      by (auto simp: geotop_convex_hull_eq_HOL card_1_singleton_iff)
    then obtain v where h\<sigma>_eq: "\<sigma> = {v}" by blast
    have hQ_eq_v: "Q = v" using hQ\<sigma> h\<sigma>_eq by simp
    have "{Q} \<in> K1" using hQ_eq_v h\<sigma>_K1 h\<sigma>_eq by simp
    thus ?thesis using hK1_complex hK1_1dim hK1_poly hPK1 by blast
  next
    case (Suc k)
    hence hn_eq_1: "n = 1" using hn_le by simp
    have h\<sigma>_dim1: "geotop_simplex_dim \<sigma> 1" using h\<sigma>_dim hn_eq_1 by simp
    have h_ex: "\<exists>K. geotop_is_complex K \<and> geotop_complex_is_1dim K
              \<and> geotop_polyhedron K = geotop_polyhedron K1 \<and> {Q} \<in> K
              \<and> K1 - {\<sigma>} \<subseteq> K
              \<and> (finite K1 \<longrightarrow> finite K)"
      by (rule geotop_complex_subdivide_edge[OF hK1_complex hK1_1dim h\<sigma>_K1 h\<sigma>_dim1 hQ\<sigma>])
    then obtain K where hK_complex: "geotop_is_complex K"
                     and hK_1dim: "geotop_complex_is_1dim K"
                     and hK_poly: "geotop_polyhedron K = geotop_polyhedron K1"
                     and hQK: "{Q} \<in> K"
                     and hK_super: "K1 - {\<sigma>} \<subseteq> K" by blast
    have hK_polyB: "geotop_polyhedron K = B" using hK_poly hK1_poly by simp
    text \<open>P stays a vertex: \<open>{P}\<close> is a 0-simplex \<open>\<noteq> \<sigma>\<close> (which is a 1-simplex), so it
      survives the subdivision in \<open>K1 - {\<sigma>} \<subseteq> K\<close>.\<close>
    have hP_ne_\<sigma>: "{P} \<noteq> \<sigma>"
    proof
      assume h_eq: "{P} = \<sigma>"
      have h_dim0: "geotop_simplex_dim {P} 0"
        unfolding geotop_simplex_dim_def
        apply (rule exI[of _ "{P}"])
        apply (rule exI[of _ 0])
        by (simp add: geotop_convex_hull_eq_HOL geotop_general_position_def)
      hence h_dim_eq: "geotop_simplex_dim \<sigma> 0" using h_eq by simp
      have "0 = (1::nat)" by (rule geotop_simplex_dim_unique[OF h_dim_eq h\<sigma>_dim1])
      thus False by simp
    qed
    have hPK: "{P} \<in> K" using hPK1 hP_ne_\<sigma> hK_super by blast
    show ?thesis using hK_complex hK_1dim hK_polyB hPK hQK by blast
  qed
qed

text \<open>For \<open>pair_of_arcs_polyhedron\<close>, we refine the two complexes so
  endpoints are vertices in both, then take the union. The cross-complex
  intersection axiom holds because any common simplex lies in
  \<open>B1 \<inter> B2 \<subseteq> E = {P, Q}\<close>, and \<open>P, Q\<close> are vertices of both refined
  complexes. The complete proof requires extensive case analysis on
  simplex dimensions; we leave the detailed write-out as a session-sized
  follow-up.\<close>

text \<open>If \<open>\<sigma>\<close> is a simplex in a 1-dim complex \<open>K\<close>, with two distinct vertices
  \<open>{P}, {Q} \<in> K\<close> both lying in \<open>\<sigma>\<close>, then \<open>\<sigma> = \<close>convex hull \<open>{P, Q}\<close>.\<close>

lemma onedim_simplex_with_two_endpoints_eq_hull:
  fixes \<sigma> :: "(real^2) set" and P Q :: "real^2"
  assumes h_complex: "geotop_is_complex K"
      and h_1dim: "geotop_complex_is_1dim K"
      and h_\<sigma>_K: "\<sigma> \<in> K"
      and hPK: "{P} \<in> K"
      and hQK: "{Q} \<in> K"
      and hP\<sigma>: "P \<in> \<sigma>"
      and hQ\<sigma>: "Q \<in> \<sigma>"
      and hP_ne_Q: "P \<noteq> Q"
  shows "\<sigma> = geotop_convex_hull {P, Q}"
proof -
  have hK_c: "\<forall>\<sigma>\<in>K. \<forall>\<tau>\<in>K. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using h_complex unfolding geotop_is_complex_def by simp
  text \<open>P is a vertex of \<sigma>.\<close>
  have h_P_face_\<sigma>: "geotop_is_face {P} \<sigma>"
  proof -
    have h_inter_eq: "{P} \<inter> \<sigma> = {P}" using hP\<sigma> by blast
    have h_inter_ne: "{P} \<inter> \<sigma> \<noteq> {}" by (simp add: h_inter_eq)
    have "geotop_is_face ({P} \<inter> \<sigma>) \<sigma>"
      using hK_c[rule_format, OF hPK h_\<sigma>_K] h_inter_ne by blast
    thus ?thesis using h_inter_eq by simp
  qed
  obtain V_P W_P where hV_P: "geotop_simplex_vertices \<sigma> V_P"
                   and hW_P_ne: "W_P \<noteq> {}" and hW_P_sub: "W_P \<subseteq> V_P"
                   and hP_hull: "{P} = geotop_convex_hull W_P"
    using h_P_face_\<sigma> unfolding geotop_is_face_def by blast
  text \<open>From \<open>{P} = convex_hull(W_P)\<close>, deduce \<open>W_P = {P}\<close>.\<close>
  have hW_P_eq: "W_P = {P}"
  proof -
    have hW_P_finite: "finite W_P"
      using hV_P hW_P_sub unfolding geotop_simplex_vertices_def
      by (auto intro: finite_subset)
    have hW_P_card1: "card W_P = 1"
    proof -
      have hW_P_sub_hull: "W_P \<subseteq> geotop_convex_hull W_P"
        by (auto simp: geotop_convex_hull_eq_HOL hull_inc)
      hence "W_P \<subseteq> {P}" using hP_hull by simp
      thus ?thesis using hW_P_ne by (auto simp: subset_singleton_iff)
    qed
    have "\<exists>v. W_P = {v}"
      using hW_P_card1 by (auto simp: card_1_singleton_iff)
    then obtain v where "W_P = {v}" by blast
    moreover have "v = P"
    proof -
      have "geotop_convex_hull {v} = {v}"
        by (simp add: geotop_convex_hull_eq_HOL)
      thus ?thesis using hP_hull \<open>W_P = {v}\<close> by simp
    qed
    ultimately show ?thesis by simp
  qed
  have hP_V_P: "P \<in> V_P"
    using hW_P_eq hW_P_sub by blast
  text \<open>Similarly Q is a vertex of \<sigma>; uniqueness gives same V.\<close>
  have h_Q_face_\<sigma>: "geotop_is_face {Q} \<sigma>"
  proof -
    have h_inter_eq: "{Q} \<inter> \<sigma> = {Q}" using hQ\<sigma> by blast
    have h_inter_ne: "{Q} \<inter> \<sigma> \<noteq> {}" by (simp add: h_inter_eq)
    have "geotop_is_face ({Q} \<inter> \<sigma>) \<sigma>"
      using hK_c[rule_format, OF hQK h_\<sigma>_K] h_inter_ne by blast
    thus ?thesis using h_inter_eq by simp
  qed
  obtain V_Q W_Q where hV_Q: "geotop_simplex_vertices \<sigma> V_Q"
                   and hW_Q_ne: "W_Q \<noteq> {}" and hW_Q_sub: "W_Q \<subseteq> V_Q"
                   and hQ_hull: "{Q} = geotop_convex_hull W_Q"
    using h_Q_face_\<sigma> unfolding geotop_is_face_def by blast
  have h_V_eq: "V_Q = V_P" using hV_P hV_Q geotop_simplex_vertices_unique by blast
  have hW_Q_eq: "W_Q = {Q}"
  proof -
    have hW_Q_finite: "finite W_Q"
      using hV_Q hW_Q_sub unfolding geotop_simplex_vertices_def
      by (auto intro: finite_subset)
    have hW_Q_card1: "card W_Q = 1"
    proof -
      have hW_Q_sub_hull: "W_Q \<subseteq> geotop_convex_hull W_Q"
        by (auto simp: geotop_convex_hull_eq_HOL hull_inc)
      hence "W_Q \<subseteq> {Q}" using hQ_hull by simp
      thus ?thesis using hW_Q_ne by (auto simp: subset_singleton_iff)
    qed
    have "\<exists>v. W_Q = {v}"
      using hW_Q_card1 by (auto simp: card_1_singleton_iff)
    then obtain v where "W_Q = {v}" by blast
    moreover have "v = Q"
    proof -
      have "geotop_convex_hull {v} = {v}"
        by (simp add: geotop_convex_hull_eq_HOL)
      thus ?thesis using hQ_hull \<open>W_Q = {v}\<close> by simp
    qed
    ultimately show ?thesis by simp
  qed
  have hQ_V_P: "Q \<in> V_P"
    using hW_Q_eq hW_Q_sub h_V_eq by blast
  text \<open>\<sigma> in 1-dim K, so |V_P| \<le> 2.\<close>
  have h\<sigma>_dim_le_1: "\<exists>n. n \<le> 1 \<and> geotop_simplex_dim \<sigma> n"
    using h_1dim h_\<sigma>_K unfolding geotop_complex_is_1dim_def by blast
  obtain n where hn_le: "n \<le> 1" and h\<sigma>_dim: "geotop_simplex_dim \<sigma> n"
    using h\<sigma>_dim_le_1 by blast
  obtain V' m' where hV'_fin: "finite V'" and hV'_card: "card V' = n + 1"
                 and hnm': "n \<le> m'" and hV'_gp: "geotop_general_position V' m'"
                 and h\<sigma>_eq_V': "\<sigma> = geotop_convex_hull V'"
    using h\<sigma>_dim unfolding geotop_simplex_dim_def by blast
  have hV': "geotop_simplex_vertices \<sigma> V'"
    unfolding geotop_simplex_vertices_def
    using hV'_fin hV'_card hnm' hV'_gp h\<sigma>_eq_V' by blast
  have hV'_eq_V_P: "V' = V_P"
    using hV' hV_P geotop_simplex_vertices_unique by blast
  have hV_P_card: "card V_P = n + 1"
    using hV'_card hV'_eq_V_P by simp
  text \<open>P, Q ∈ V_P with P ≠ Q gives card V_P ≥ 2 ⟹ n + 1 ≥ 2 ⟹ n ≥ 1.\<close>
  have h_VP_finite: "finite V_P" using hV'_fin hV'_eq_V_P by simp
  have h_2_in_VP: "{P, Q} \<subseteq> V_P" using hP_V_P hQ_V_P by blast
  have h_card_VP_geq2: "card V_P \<ge> 2"
  proof -
    have "card {P, Q} = 2" using hP_ne_Q by simp
    moreover have "card {P, Q} \<le> card V_P"
      using h_2_in_VP h_VP_finite card_mono by blast
    ultimately show ?thesis by simp
  qed
  have hn_ge_1: "n \<ge> 1" using h_card_VP_geq2 hV_P_card by simp
  have hn_eq_1: "n = 1" using hn_le hn_ge_1 by simp
  have h_card_VP: "card V_P = 2" using hV_P_card hn_eq_1 by simp
  have h_VP_eq_PQ: "V_P = {P, Q}"
  proof -
    have h_card_PQ: "card {P, Q} = card V_P" using hP_ne_Q h_card_VP by simp
    have h_PQ_sub: "{P, Q} \<subseteq> V_P" using h_2_in_VP .
    show ?thesis
      using card_subset_eq[OF h_VP_finite h_PQ_sub] h_card_PQ by simp
  qed
  have h\<sigma>_eq: "\<sigma> = geotop_convex_hull V_P"
    using h\<sigma>_eq_V' hV'_eq_V_P by simp
  show ?thesis using h\<sigma>_eq h_VP_eq_PQ by simp
qed

lemma pair_of_arcs_polyhedron:
  fixes B1 B2 :: "(real^2) set" and E :: "(real^2) set"
  assumes hB1: "geotop_is_broken_line B1"
      and hB2: "geotop_is_broken_line B2"
      and hE1: "geotop_arc_endpoints B1 E"
      and hE2: "geotop_arc_endpoints B2 E"
      and h_disj: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = {}"
  shows "\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = B1 \<union> B2"
proof -
  text \<open>Endpoints are in both broken lines.\<close>
  have hE_card: "card E = 2" using hE1 unfolding geotop_arc_endpoints_def by blast
  have hE_sub_B1: "E \<subseteq> B1" using hE1 unfolding geotop_arc_endpoints_def by blast
  have hE_sub_B2: "E \<subseteq> B2" using hE2 unfolding geotop_arc_endpoints_def by blast
  obtain P Q where hPQ_E: "E = {P, Q}" and hP_ne_Q: "P \<noteq> Q"
    using hE_card card_2_iff by metis
  have hP_B1: "P \<in> B1" using hPQ_E hE_sub_B1 by blast
  have hP_B2: "P \<in> B2" using hPQ_E hE_sub_B2 by blast
  have hQ_B1: "Q \<in> B1" using hPQ_E hE_sub_B1 by blast
  have hQ_B2: "Q \<in> B2" using hPQ_E hE_sub_B2 by blast
  text \<open>Refine the two complexes to have endpoints as vertices.\<close>
  obtain K1 where hK1_complex: "geotop_is_complex K1"
              and hK1_1dim: "geotop_complex_is_1dim K1"
              and hK1_poly: "geotop_polyhedron K1 = B1"
              and hPK1: "{P} \<in> K1" and hQK1: "{Q} \<in> K1"
    using broken_line_make_two_vertices[OF hB1 hP_B1 hQ_B1] by blast
  obtain K2 where hK2_complex: "geotop_is_complex K2"
              and hK2_1dim: "geotop_complex_is_1dim K2"
              and hK2_poly: "geotop_polyhedron K2 = B2"
              and hPK2: "{P} \<in> K2" and hQK2: "{Q} \<in> K2"
    using broken_line_make_two_vertices[OF hB2 hP_B2 hQ_B2] by blast
  define K where "K = K1 \<union> K2"
  text \<open>Standard fact: \<open>B1 \<inter> B2 = E\<close>.\<close>
  have hB1B2_inter: "B1 \<inter> B2 = E"
  proof
    show "B1 \<inter> B2 \<subseteq> E"
    proof
      fix x assume hx: "x \<in> B1 \<inter> B2"
      show "x \<in> E"
      proof (rule ccontr)
        assume "x \<notin> E"
        hence hxB1E: "x \<in> B1 - E" using hx by blast
        have hxB2E: "x \<in> B2 - E" using hx \<open>x \<notin> E\<close> by blast
        have "x \<in> geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E"
          unfolding geotop_arc_interior_def using hxB1E hxB2E by blast
        thus False using h_disj by blast
      qed
    qed
    show "E \<subseteq> B1 \<inter> B2" using hE_sub_B1 hE_sub_B2 by blast
  qed
  text \<open>Axiom (a): every element of K is a simplex.\<close>
  have hK1_a: "\<forall>\<sigma>\<in>K1. geotop_is_simplex \<sigma>"
   and hK1_b: "\<forall>\<sigma>\<in>K1. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K1"
   and hK1_c: "\<forall>\<sigma>\<in>K1. \<forall>\<tau>\<in>K1. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                  geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using hK1_complex unfolding geotop_is_complex_def by simp_all
  have hK2_a: "\<forall>\<sigma>\<in>K2. geotop_is_simplex \<sigma>"
   and hK2_b: "\<forall>\<sigma>\<in>K2. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K2"
   and hK2_c: "\<forall>\<sigma>\<in>K2. \<forall>\<tau>\<in>K2. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                  geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using hK2_complex unfolding geotop_is_complex_def by simp_all
  have hK_a: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
    using hK1_a hK2_a unfolding K_def by blast
  text \<open>Axiom (b): K is closed under face.\<close>
  have hK_b: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using hK1_b hK2_b unfolding K_def by blast
  text \<open>Helper: every K1-simplex lies in B1; every K2-simplex lies in B2.\<close>
  have hK1_subB1: "\<forall>\<sigma>\<in>K1. \<sigma> \<subseteq> B1"
    using hK1_poly unfolding geotop_polyhedron_def by blast
  have hK2_subB2: "\<forall>\<sigma>\<in>K2. \<sigma> \<subseteq> B2"
    using hK2_poly unfolding geotop_polyhedron_def by blast
  text \<open>Helper: \<open>{P, Q}\<close> cannot be the cross-intersection because that would
    force \<open>\<sigma>, \<tau>\<close> both equal to segment PQ, but segment PQ has uncountably
    many points and would force PQ \<subseteq> E (finite). So the cross-intersection,
    if non-empty, is exactly \<open>{P}\<close> or \<open>{Q}\<close>.\<close>
  have h_PQ_seg_not_in_E: "geotop_convex_hull {P, Q} \<noteq> {P, Q}"
  proof -
    text \<open>The convex hull of two distinct points contains the midpoint, which
      is neither of them.\<close>
    define M where "M = (1/2) *\<^sub>R P + (1/2) *\<^sub>R Q"
    have hM_in_hull: "M \<in> geotop_convex_hull {P, Q}"
    proof -
      have hM_HOL: "M \<in> convex hull {P, Q}"
      proof -
        have hMM: "M = (1/2 :: real) *\<^sub>R P + (1/2 :: real) *\<^sub>R Q" by (simp add: M_def)
        have hCH_eq: "convex hull {P, Q} =
              {u *\<^sub>R P + v *\<^sub>R Q | u v. 0 \<le> u \<and> 0 \<le> v \<and> u + v = 1}"
          by (rule convex_hull_2)
        show "M \<in> convex hull {P, Q}"
          unfolding hCH_eq using hMM
          by (intro CollectI exI[of _ "1/2 :: real"] exI[of _ "1/2 :: real"]) auto
      qed
      thus ?thesis by (simp add: geotop_convex_hull_eq_HOL)
    qed
    have hM_eq_simp: "M = (1/2) *\<^sub>R P + (1/2) *\<^sub>R Q" by (simp add: M_def)
    have h_2M_eq: "(2::real) *\<^sub>R M = P + Q"
      using hM_eq_simp by (simp add: algebra_simps)
    have h_2_scaleR: "\<And>v::real^2. (2::real) *\<^sub>R v = v + v"
      by (simp add: scaleR_2)
    have hM_ne_P: "M \<noteq> P"
    proof
      assume "M = P"
      hence "(2::real) *\<^sub>R P = P + Q" using h_2M_eq by simp
      hence "P + P = P + Q" by (simp add: h_2_scaleR)
      hence "P = Q" by simp
      thus False using hP_ne_Q by simp
    qed
    have hM_ne_Q: "M \<noteq> Q"
    proof
      assume "M = Q"
      hence "(2::real) *\<^sub>R Q = P + Q" using h_2M_eq by simp
      hence "Q + Q = P + Q" by (simp add: h_2_scaleR)
      hence "Q = P" by simp
      thus False using hP_ne_Q by simp
    qed
    have hM_not_in_PQ: "M \<notin> {P, Q}" using hM_ne_P hM_ne_Q by simp
    show ?thesis using hM_in_hull hM_not_in_PQ by blast
  qed
  text \<open>Axiom (c) — main case-split.\<close>
  have hK_c: "\<forall>\<sigma>\<in>K. \<forall>\<tau>\<in>K. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
  proof (intro ballI impI)
    fix \<sigma> \<tau> assume h\<sigma>: "\<sigma> \<in> K" and h\<tau>: "\<tau> \<in> K" and h_inter: "\<sigma> \<inter> \<tau> \<noteq> {}"
    have h\<sigma>_cases: "\<sigma> \<in> K1 \<or> \<sigma> \<in> K2" using h\<sigma> unfolding K_def by blast
    have h\<tau>_cases: "\<tau> \<in> K1 \<or> \<tau> \<in> K2" using h\<tau> unfolding K_def by blast
    show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    proof (cases "\<sigma> \<in> K1 \<and> \<tau> \<in> K1")
      case True thus ?thesis using hK1_c h_inter by blast
    next
      case False
      show ?thesis
      proof (cases "\<sigma> \<in> K2 \<and> \<tau> \<in> K2")
        case True thus ?thesis using hK2_c h_inter by blast
      next
        case False
        text \<open>So \<open>\<sigma>, \<tau>\<close> are in different complexes.\<close>
        have h_cross: "(\<sigma> \<in> K1 \<and> \<tau> \<in> K2) \<or> (\<sigma> \<in> K2 \<and> \<tau> \<in> K1)"
          using \<open>\<not> (\<sigma> \<in> K1 \<and> \<tau> \<in> K1)\<close> False h\<sigma>_cases h\<tau>_cases by blast
        have h_cross_inter_in_E: "\<sigma> \<inter> \<tau> \<subseteq> E"
        proof -
          have "\<sigma> \<inter> \<tau> \<subseteq> B1 \<inter> B2"
            using h_cross hK1_subB1 hK2_subB2 by blast
          thus ?thesis using hB1B2_inter by simp
        qed
        have h_cross_inter_sub: "\<sigma> \<inter> \<tau> \<subseteq> {P, Q}"
          using h_cross_inter_in_E hPQ_E by blast
        text \<open>Show \<open>\<sigma> \<inter> \<tau> = {P}\<close> or \<open>\<sigma> \<inter> \<tau> = {Q}\<close> (both endpoints case excluded).\<close>
        have h_inter_singleton: "\<sigma> \<inter> \<tau> = {P} \<or> \<sigma> \<inter> \<tau> = {Q}"
        proof -
          have h_inter_sub_PQ: "\<sigma> \<inter> \<tau> \<subseteq> {P, Q}" using h_cross_inter_sub .
          have h_subsets_of_PQ: "\<And>S::(real^2) set. S \<subseteq> {P, Q} \<Longrightarrow>
                                  S = {} \<or> S = {P} \<or> S = {Q} \<or> S = {P, Q}"
          proof -
            fix S :: "(real^2) set" assume hS: "S \<subseteq> {P, Q}"
            consider "P \<in> S \<and> Q \<in> S" | "P \<in> S \<and> Q \<notin> S"
                   | "P \<notin> S \<and> Q \<in> S" | "P \<notin> S \<and> Q \<notin> S" by blast
            thus "S = {} \<or> S = {P} \<or> S = {Q} \<or> S = {P, Q}"
            proof cases
              case 1 thus ?thesis using hS by blast
            next
              case 2 thus ?thesis using hS by blast
            next
              case 3 thus ?thesis using hS by blast
            next
              case 4 thus ?thesis using hS by blast
            qed
          qed
          have h_inter_options: "\<sigma> \<inter> \<tau> = {} \<or> \<sigma> \<inter> \<tau> = {P} \<or>
                                  \<sigma> \<inter> \<tau> = {Q} \<or> \<sigma> \<inter> \<tau> = {P, Q}"
            using h_subsets_of_PQ[OF h_inter_sub_PQ] .
          consider "\<sigma> \<inter> \<tau> = {P}" | "\<sigma> \<inter> \<tau> = {Q}" | "\<sigma> \<inter> \<tau> = {P, Q}"
            using h_inter_options h_inter by blast
          thus ?thesis
          proof cases
            case 1 thus ?thesis by simp
          next
            case 2 thus ?thesis by simp
          next
            case 3
            text \<open>Need to derive contradiction. Both \<open>\<sigma>\<close> and \<open>\<tau>\<close> contain
              \<open>{P, Q}\<close>, so they are 1-simplices with \<open>{P, Q}\<close> as vertex set.
              But then \<open>\<sigma> = \<tau> = \<close> segment PQ, hence segment PQ \<subseteq> B1 \<inter> B2 = E,
              contradicting that segment PQ has uncountably many points.\<close>
            have hP\<sigma>: "P \<in> \<sigma>" using 3 by blast
            have hQ\<sigma>: "Q \<in> \<sigma>" using 3 by blast
            have hP\<tau>: "P \<in> \<tau>" using 3 by blast
            have hQ\<tau>: "Q \<in> \<tau>" using 3 by blast
            have h\<sigma>_K: "\<sigma> \<in> K1 \<or> \<sigma> \<in> K2" using h_cross by blast
            text \<open>From \<open>{P} \<in> Ki, \<sigma> \<in> Ki\<close>, P is a vertex of \<sigma> (so \<sigma> contains P
              as a vertex; similarly Q). With \<open>\<sigma>\<close> in a 1-dim complex, \<sigma> is a
              1-simplex, hence \<open>\<sigma> = \<close> convex hull \<open>{P, Q}\<close>.\<close>
            have h\<sigma>_eq_PQ: "\<sigma> = geotop_convex_hull {P, Q}"
            proof (cases "\<sigma> \<in> K1")
              case True
              show ?thesis
                by (rule onedim_simplex_with_two_endpoints_eq_hull
                          [OF hK1_complex hK1_1dim True hPK1 hQK1 hP\<sigma> hQ\<sigma> hP_ne_Q])
            next
              case False
              hence "\<sigma> \<in> K2" using h_cross by blast
              show ?thesis
                by (rule onedim_simplex_with_two_endpoints_eq_hull
                          [OF hK2_complex hK2_1dim \<open>\<sigma> \<in> K2\<close> hPK2 hQK2 hP\<sigma> hQ\<sigma> hP_ne_Q])
            qed
            have h\<tau>_eq_PQ: "\<tau> = geotop_convex_hull {P, Q}"
            proof (cases "\<tau> \<in> K1")
              case True
              show ?thesis
                by (rule onedim_simplex_with_two_endpoints_eq_hull
                          [OF hK1_complex hK1_1dim True hPK1 hQK1 hP\<tau> hQ\<tau> hP_ne_Q])
            next
              case False
              hence "\<tau> \<in> K2" using h_cross by blast
              show ?thesis
                by (rule onedim_simplex_with_two_endpoints_eq_hull
                          [OF hK2_complex hK2_1dim \<open>\<tau> \<in> K2\<close> hPK2 hQK2 hP\<tau> hQ\<tau> hP_ne_Q])
            qed
            have h\<sigma>_subB1: "\<sigma> \<subseteq> B1 \<and> \<tau> \<subseteq> B2 \<or> \<sigma> \<subseteq> B2 \<and> \<tau> \<subseteq> B1"
              using h_cross hK1_subB1 hK2_subB2 by blast
            have h_seg_in_inter: "geotop_convex_hull {P, Q} \<subseteq> B1 \<inter> B2"
              using h\<sigma>_eq_PQ h\<tau>_eq_PQ h\<sigma>_subB1 by blast
            hence "geotop_convex_hull {P, Q} \<subseteq> {P, Q}"
              using hB1B2_inter hPQ_E by simp
            moreover have "{P, Q} \<subseteq> geotop_convex_hull {P, Q}"
              by (auto simp: geotop_convex_hull_eq_HOL hull_inc)
            ultimately have "geotop_convex_hull {P, Q} = {P, Q}" by blast
            thus ?thesis using h_PQ_seg_not_in_E by blast
          qed
        qed
        text \<open>The singleton intersection case: both \<open>\<sigma>\<close> and \<open>\<tau>\<close> have the
          singleton vertex (since the singleton is in both K1 and K2, and the
          complex axiom of either Ki forces the intersection with the
          singleton to be a face).\<close>
        have h_singleton_face_of_simplex:
          "\<And>v Kx \<rho>. \<lbrakk>v \<in> {P, Q}; {v} \<in> Kx; \<rho> \<in> Kx; v \<in> \<rho>;
                    \<forall>\<sigma>\<in>Kx. \<forall>\<tau>\<in>Kx. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                       geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>\<rbrakk>
                  \<Longrightarrow> geotop_is_face {v} \<rho>"
        proof -
          fix v Kx \<rho> assume hv_PQ: "v \<in> {P, Q}" and hvKx: "{v} \<in> Kx"
                       and h\<rho>_Kx: "\<rho> \<in> Kx" and hv\<rho>: "v \<in> \<rho>"
                       and hKx_c: "\<forall>\<sigma>\<in>Kx. \<forall>\<tau>\<in>Kx. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
                                     geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
          have h_inter_eq: "{v} \<inter> \<rho> = {v}" using hv\<rho> by blast
          have h_inter_ne: "{v} \<inter> \<rho> \<noteq> {}" using h_inter_eq by simp
          have "geotop_is_face ({v} \<inter> \<rho>) \<rho>"
            using hKx_c[rule_format, OF hvKx h\<rho>_Kx] h_inter_ne by blast
          thus "geotop_is_face {v} \<rho>" using h_inter_eq by simp
        qed
        consider (P_case) "\<sigma> \<inter> \<tau> = {P}" | (Q_case) "\<sigma> \<inter> \<tau> = {Q}"
          using h_inter_singleton by blast
        thus ?thesis
        proof cases
          case P_case
          have hP\<sigma>: "P \<in> \<sigma>" using P_case by blast
          have hP\<tau>: "P \<in> \<tau>" using P_case by blast
          have hP_PQ: "P \<in> {P, Q}" by simp
          have h_sf\<sigma>: "geotop_is_face {P} \<sigma>"
          proof (cases "\<sigma> \<in> K1")
            case True
            show ?thesis
              by (rule h_singleton_face_of_simplex[OF hP_PQ hPK1 True hP\<sigma> hK1_c])
          next
            case False
            hence "\<sigma> \<in> K2" using h_cross by blast
            show ?thesis
              by (rule h_singleton_face_of_simplex[OF hP_PQ hPK2 \<open>\<sigma> \<in> K2\<close> hP\<sigma> hK2_c])
          qed
          have h_sf\<tau>: "geotop_is_face {P} \<tau>"
          proof (cases "\<tau> \<in> K1")
            case True
            show ?thesis
              by (rule h_singleton_face_of_simplex[OF hP_PQ hPK1 True hP\<tau> hK1_c])
          next
            case False
            hence "\<tau> \<in> K2" using h_cross by blast
            show ?thesis
              by (rule h_singleton_face_of_simplex[OF hP_PQ hPK2 \<open>\<tau> \<in> K2\<close> hP\<tau> hK2_c])
          qed
          show ?thesis using P_case h_sf\<sigma> h_sf\<tau> by simp
        next
          case Q_case
          have hQ\<sigma>: "Q \<in> \<sigma>" using Q_case by blast
          have hQ\<tau>: "Q \<in> \<tau>" using Q_case by blast
          have hQ_PQ: "Q \<in> {P, Q}" by simp
          have h_sf\<sigma>: "geotop_is_face {Q} \<sigma>"
          proof (cases "\<sigma> \<in> K1")
            case True
            show ?thesis
              by (rule h_singleton_face_of_simplex[OF hQ_PQ hQK1 True hQ\<sigma> hK1_c])
          next
            case False
            hence "\<sigma> \<in> K2" using h_cross by blast
            show ?thesis
              by (rule h_singleton_face_of_simplex[OF hQ_PQ hQK2 \<open>\<sigma> \<in> K2\<close> hQ\<sigma> hK2_c])
          qed
          have h_sf\<tau>: "geotop_is_face {Q} \<tau>"
          proof (cases "\<tau> \<in> K1")
            case True
            show ?thesis
              by (rule h_singleton_face_of_simplex[OF hQ_PQ hQK1 True hQ\<tau> hK1_c])
          next
            case False
            hence "\<tau> \<in> K2" using h_cross by blast
            show ?thesis
              by (rule h_singleton_face_of_simplex[OF hQ_PQ hQK2 \<open>\<tau> \<in> K2\<close> hQ\<tau> hK2_c])
          qed
          show ?thesis using Q_case h_sf\<sigma> h_sf\<tau> by simp
        qed
      qed
    qed
  qed
  text \<open>For local finiteness we need \<open>B2\<close> closed. From \<open>geotop_arc_endpoints B2 E\<close>
    we extract a homeomorphism \<open>[0,1] \<to> B2\<close>, so \<open>B2\<close> is the continuous image of a
    compact set, hence compact, hence closed.\<close>
  have hB1_closed: "closed B1"
  proof -
    obtain f0 :: "real \<Rightarrow> real^2" where
      h_homeo: "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
          (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1}) B1
          (subspace_topology UNIV geotop_euclidean_topology B1) f0"
      using hE1 unfolding geotop_arc_endpoints_def by blast
    have h_unit_iv: "{t::real. 0 \<le> t \<and> t \<le> 1} = {0..1}" by auto
    have h_homeo_HOL: "{0..1::real} homeomorphic B1"
      using h_homeo top1_homeomorphism_on_geotop_imp_HOL_homeomorphic h_unit_iv by metis
    have h_compact_01: "compact {0..1::real}" by simp
    have h_compact_B1: "compact B1"
      using h_compact_01 h_homeo_HOL homeomorphic_compactness by blast
    show ?thesis using h_compact_B1 compact_imp_closed by blast
  qed
  have hB2_closed: "closed B2"
  proof -
    obtain f0 :: "real \<Rightarrow> real^2" where
      h_homeo: "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
          (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1}) B2
          (subspace_topology UNIV geotop_euclidean_topology B2) f0"
      using hE2 unfolding geotop_arc_endpoints_def by blast
    have h_unit_iv: "{t::real. 0 \<le> t \<and> t \<le> 1} = {0..1}" by auto
    have h_homeo_HOL: "{0..1::real} homeomorphic B2"
      using h_homeo top1_homeomorphism_on_geotop_imp_HOL_homeomorphic h_unit_iv by metis
    have h_compact_01: "compact {0..1::real}" by simp
    have h_compact_B2: "compact B2"
      using h_compact_01 h_homeo_HOL homeomorphic_compactness by blast
    show ?thesis using h_compact_B2 compact_imp_closed by blast
  qed
  text \<open>Axiom (d): local finiteness.\<close>
  have hK1_d: "\<forall>\<sigma>\<in>K1. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K1. \<tau> \<inter> U \<noteq> {}}"
    using hK1_complex unfolding geotop_is_complex_def by simp
  have hK2_d: "\<forall>\<sigma>\<in>K2. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K2. \<tau> \<inter> U \<noteq> {}}"
    using hK2_complex unfolding geotop_is_complex_def by simp
  have hK_d: "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma> assume h\<sigma>_K: "\<sigma> \<in> K"
    obtain U2_P where hU2_P_open: "open U2_P" and hPU2_P: "{P} \<subseteq> U2_P"
                 and hfin_K2_P: "finite {\<tau>\<in>K2. \<tau> \<inter> U2_P \<noteq> {}}"
      using hK2_d hPK2 by blast
    obtain U2_Q where hU2_Q_open: "open U2_Q" and hQU2_Q: "{Q} \<subseteq> U2_Q"
                 and hfin_K2_Q: "finite {\<tau>\<in>K2. \<tau> \<inter> U2_Q \<noteq> {}}"
      using hK2_d hQK2 by blast
    obtain U1_P where hU1_P_open: "open U1_P" and hPU1_P: "{P} \<subseteq> U1_P"
                 and hfin_K1_P: "finite {\<tau>\<in>K1. \<tau> \<inter> U1_P \<noteq> {}}"
      using hK1_d hPK1 by blast
    obtain U1_Q where hU1_Q_open: "open U1_Q" and hQU1_Q: "{Q} \<subseteq> U1_Q"
                 and hfin_K1_Q: "finite {\<tau>\<in>K1. \<tau> \<inter> U1_Q \<noteq> {}}"
      using hK1_d hQK1 by blast
    consider (Ks1) "\<sigma> \<in> K1" | (Ks2) "\<sigma> \<in> K2 \<and> \<sigma> \<notin> K1"
      using h\<sigma>_K unfolding K_def by blast
    thus "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    proof cases
      case Ks1
      obtain U1 where hU1_open: "open U1" and h\<sigma>_U1: "\<sigma> \<subseteq> U1"
                  and hfin_U1: "finite {\<tau>\<in>K1. \<tau> \<inter> U1 \<noteq> {}}"
        using hK1_d Ks1 by blast
      define V where "V = U1 \<inter> (UNIV - (B2 - U2_P - U2_Q))"
      have hV_open: "open V"
      proof -
        have h_closed_part: "closed (B2 - U2_P - U2_Q)"
          using hB2_closed hU2_P_open hU2_Q_open
          by (simp add: closed_Diff)
        have h_open_compl: "open (UNIV - (B2 - U2_P - U2_Q))"
        proof -
          have "open (- (B2 - U2_P - U2_Q))"
            using h_closed_part open_Compl by blast
          thus ?thesis by (simp add: Compl_eq_Diff_UNIV)
        qed
        show ?thesis unfolding V_def using hU1_open h_open_compl by blast
      qed
      have h\<sigma>_sub_B1: "\<sigma> \<subseteq> B1" using hK1_subB1 Ks1 by blast
      have h\<sigma>_inter_B2: "\<sigma> \<inter> B2 \<subseteq> {P, Q}"
        using h\<sigma>_sub_B1 hB1B2_inter hPQ_E by blast
      have h\<sigma>_V: "\<sigma> \<subseteq> V"
      proof
        fix x assume hx: "x \<in> \<sigma>"
        have hxU1: "x \<in> U1" using hx h\<sigma>_U1 by blast
        have "x \<notin> B2 - U2_P - U2_Q"
        proof
          assume hxB2: "x \<in> B2 - U2_P - U2_Q"
          hence "x \<in> B2" by blast
          hence "x \<in> \<sigma> \<inter> B2" using hx by blast
          hence "x \<in> {P, Q}" using h\<sigma>_inter_B2 by blast
          hence "x \<in> U2_P \<union> U2_Q" using hPU2_P hQU2_Q by blast
          thus False using hxB2 by blast
        qed
        thus "x \<in> V" unfolding V_def using hxU1 by blast
      qed
      have hfin_K_V: "finite {\<tau>\<in>K. \<tau> \<inter> V \<noteq> {}}"
      proof -
        have h_K1_part: "{\<tau>\<in>K1. \<tau> \<inter> V \<noteq> {}} \<subseteq> {\<tau>\<in>K1. \<tau> \<inter> U1 \<noteq> {}}"
          unfolding V_def by blast
        have hfin_K1_V: "finite {\<tau>\<in>K1. \<tau> \<inter> V \<noteq> {}}"
          using h_K1_part hfin_U1 by (rule finite_subset)
        have h_K2_part:
          "{\<tau>\<in>K2. \<tau> \<inter> V \<noteq> {}} \<subseteq>
            {\<tau>\<in>K2. \<tau> \<inter> U2_P \<noteq> {}} \<union> {\<tau>\<in>K2. \<tau> \<inter> U2_Q \<noteq> {}}"
        proof
          fix \<tau> assume h\<tau>: "\<tau> \<in> {\<tau>\<in>K2. \<tau> \<inter> V \<noteq> {}}"
          hence h\<tau>K2: "\<tau> \<in> K2" and h\<tau>V: "\<tau> \<inter> V \<noteq> {}" by blast+
          obtain x where hx_\<tau>: "x \<in> \<tau>" and hxV: "x \<in> V" using h\<tau>V by blast
          have hx_B2: "x \<in> B2" using hx_\<tau> hK2_subB2 h\<tau>K2 by blast
          have hxU1: "x \<in> U1" using hxV unfolding V_def by blast
          have hx_not_B2_minus: "x \<notin> B2 - U2_P - U2_Q" using hxV unfolding V_def by blast
          have "x \<in> U2_P \<or> x \<in> U2_Q" using hx_B2 hx_not_B2_minus by blast
          thus "\<tau> \<in> {\<tau>\<in>K2. \<tau> \<inter> U2_P \<noteq> {}} \<union> {\<tau>\<in>K2. \<tau> \<inter> U2_Q \<noteq> {}}"
            using h\<tau>K2 hx_\<tau> by blast
        qed
        have hfin_K2_V: "finite {\<tau>\<in>K2. \<tau> \<inter> V \<noteq> {}}"
          using h_K2_part hfin_K2_P hfin_K2_Q by (auto intro: finite_subset)
        have h_K_decomp: "{\<tau>\<in>K. \<tau> \<inter> V \<noteq> {}} = {\<tau>\<in>K1. \<tau> \<inter> V \<noteq> {}} \<union> {\<tau>\<in>K2. \<tau> \<inter> V \<noteq> {}}"
          unfolding K_def by blast
        show ?thesis using h_K_decomp hfin_K1_V hfin_K2_V by simp
      qed
      show ?thesis using hV_open h\<sigma>_V hfin_K_V by blast
    next
      case Ks2
      hence h\<sigma>_K2: "\<sigma> \<in> K2" by blast
      obtain U2 where hU2_open: "open U2" and h\<sigma>_U2: "\<sigma> \<subseteq> U2"
                  and hfin_U2: "finite {\<tau>\<in>K2. \<tau> \<inter> U2 \<noteq> {}}"
        using hK2_d h\<sigma>_K2 by blast
      define V where "V = U2 \<inter> (UNIV - (B1 - U1_P - U1_Q))"
      have hV_open: "open V"
      proof -
        have h_closed_part: "closed (B1 - U1_P - U1_Q)"
          using hB1_closed hU1_P_open hU1_Q_open
          by (simp add: closed_Diff)
        have h_open_compl: "open (UNIV - (B1 - U1_P - U1_Q))"
        proof -
          have "open (- (B1 - U1_P - U1_Q))"
            using h_closed_part open_Compl by blast
          thus ?thesis by (simp add: Compl_eq_Diff_UNIV)
        qed
        show ?thesis unfolding V_def using hU2_open h_open_compl by blast
      qed
      have h\<sigma>_sub_B2: "\<sigma> \<subseteq> B2" using hK2_subB2 h\<sigma>_K2 by blast
      have h\<sigma>_inter_B1: "\<sigma> \<inter> B1 \<subseteq> {P, Q}"
        using h\<sigma>_sub_B2 hB1B2_inter hPQ_E by blast
      have h\<sigma>_V: "\<sigma> \<subseteq> V"
      proof
        fix x assume hx: "x \<in> \<sigma>"
        have hxU2: "x \<in> U2" using hx h\<sigma>_U2 by blast
        have "x \<notin> B1 - U1_P - U1_Q"
        proof
          assume hxB1: "x \<in> B1 - U1_P - U1_Q"
          hence "x \<in> B1" by blast
          hence "x \<in> \<sigma> \<inter> B1" using hx by blast
          hence "x \<in> {P, Q}" using h\<sigma>_inter_B1 by blast
          hence "x \<in> U1_P \<union> U1_Q" using hPU1_P hQU1_Q by blast
          thus False using hxB1 by blast
        qed
        thus "x \<in> V" unfolding V_def using hxU2 by blast
      qed
      have hfin_K_V: "finite {\<tau>\<in>K. \<tau> \<inter> V \<noteq> {}}"
      proof -
        have h_K2_part: "{\<tau>\<in>K2. \<tau> \<inter> V \<noteq> {}} \<subseteq> {\<tau>\<in>K2. \<tau> \<inter> U2 \<noteq> {}}"
          unfolding V_def by blast
        have hfin_K2_V: "finite {\<tau>\<in>K2. \<tau> \<inter> V \<noteq> {}}"
          using h_K2_part hfin_U2 by (rule finite_subset)
        have h_K1_part:
          "{\<tau>\<in>K1. \<tau> \<inter> V \<noteq> {}} \<subseteq>
            {\<tau>\<in>K1. \<tau> \<inter> U1_P \<noteq> {}} \<union> {\<tau>\<in>K1. \<tau> \<inter> U1_Q \<noteq> {}}"
        proof
          fix \<tau> assume h\<tau>: "\<tau> \<in> {\<tau>\<in>K1. \<tau> \<inter> V \<noteq> {}}"
          hence h\<tau>K1: "\<tau> \<in> K1" and h\<tau>V: "\<tau> \<inter> V \<noteq> {}" by blast+
          obtain x where hx_\<tau>: "x \<in> \<tau>" and hxV: "x \<in> V" using h\<tau>V by blast
          have hx_B1: "x \<in> B1" using hx_\<tau> hK1_subB1 h\<tau>K1 by blast
          have hx_not_B1_minus: "x \<notin> B1 - U1_P - U1_Q" using hxV unfolding V_def by blast
          have "x \<in> U1_P \<or> x \<in> U1_Q" using hx_B1 hx_not_B1_minus by blast
          thus "\<tau> \<in> {\<tau>\<in>K1. \<tau> \<inter> U1_P \<noteq> {}} \<union> {\<tau>\<in>K1. \<tau> \<inter> U1_Q \<noteq> {}}"
            using h\<tau>K1 hx_\<tau> by blast
        qed
        have hfin_K1_V: "finite {\<tau>\<in>K1. \<tau> \<inter> V \<noteq> {}}"
          using h_K1_part hfin_K1_P hfin_K1_Q by (auto intro: finite_subset)
        have h_K_decomp: "{\<tau>\<in>K. \<tau> \<inter> V \<noteq> {}} = {\<tau>\<in>K1. \<tau> \<inter> V \<noteq> {}} \<union> {\<tau>\<in>K2. \<tau> \<inter> V \<noteq> {}}"
          unfolding K_def by blast
        show ?thesis using h_K_decomp hfin_K1_V hfin_K2_V by simp
      qed
      show ?thesis using hV_open h\<sigma>_V hfin_K_V by blast
    qed
  qed
  have hK_complex: "geotop_is_complex K"
    unfolding geotop_is_complex_def using hK_a hK_b hK_c hK_d by blast
  text \<open>Polyhedron equality.\<close>
  have hK_poly: "geotop_polyhedron K = B1 \<union> B2"
  proof -
    have "geotop_polyhedron K = \<Union>K" unfolding geotop_polyhedron_def by simp
    also have "\<dots> = \<Union>K1 \<union> \<Union>K2" unfolding K_def by blast
    also have "\<dots> = geotop_polyhedron K1 \<union> geotop_polyhedron K2"
      unfolding geotop_polyhedron_def by simp
    also have "\<dots> = B1 \<union> B2" using hK1_poly hK2_poly by simp
    finally show ?thesis .
  qed
  show "\<exists>K. geotop_is_complex K \<and> geotop_polyhedron K = B1 \<union> B2"
    using hK_complex hK_poly by blast
qed

lemma arc_interior_nonempty:
  fixes B :: "(real^2) set" and E :: "(real^2) set"
  assumes hE: "geotop_arc_endpoints B E"
  shows "geotop_arc_interior B E \<noteq> {}"
proof -
  from hE obtain f0 :: "real \<Rightarrow> real^2" where
    h_homeo: "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
        (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1}) B
        (subspace_topology UNIV geotop_euclidean_topology B) f0"
    and hE_eq: "E = {f0 0, f0 1}"
    unfolding geotop_arc_endpoints_def by blast
  have h_unit_iv: "{t::real. 0 \<le> t \<and> t \<le> 1} = {0..1}" by auto
  have h_bij: "bij_betw f0 {0..1::real} B"
    using h_homeo h_unit_iv unfolding top1_homeomorphism_on_def by simp
  have h_inj: "inj_on f0 {0..1::real}"
    using h_bij by (simp add: bij_betw_def)
  have h_half_in: "(1/2::real) \<in> {0..1}" by simp
  have h_f_half: "f0 (1/2) \<in> B"
    using h_bij h_half_in unfolding bij_betw_def by blast
  have h_half_ne_0: "(1/2::real) \<noteq> 0" by simp
  have h_half_ne_1: "(1/2::real) \<noteq> 1" by simp
  have h_0_in: "(0::real) \<in> {0..1}" by simp
  have h_1_in: "(1::real) \<in> {0..1}" by simp
  have h_f_half_ne_0: "f0 (1/2) \<noteq> f0 0"
    using h_inj h_half_ne_0 h_half_in h_0_in inj_onD by metis
  have h_f_half_ne_1: "f0 (1/2) \<noteq> f0 1"
    using h_inj h_half_ne_1 h_half_in h_1_in inj_onD by metis
  have h_not_in_E: "f0 (1/2) \<notin> E"
    using hE_eq h_f_half_ne_0 h_f_half_ne_1 by simp
  show ?thesis
    unfolding geotop_arc_interior_def
    using h_f_half h_not_in_E by blast
qed

lemma pair_of_arcs_is_polygon:
  fixes B1 B2 :: "(real^2) set" and E :: "(real^2) set"
  assumes hB1: "geotop_is_broken_line B1"
      and hB2: "geotop_is_broken_line B2"
      and hE1: "geotop_arc_endpoints B1 E"
      and hE2: "geotop_arc_endpoints B2 E"
      and h_disj: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = {}"
  shows "geotop_is_polygon (B1 \<union> B2)"
proof -
  have h_distinct: "B1 \<noteq> B2"
  proof
    assume "B1 = B2"
    hence "geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = geotop_arc_interior B1 E"
      by simp
    hence "geotop_arc_interior B1 E = {}" using h_disj by simp
    thus False using arc_interior_nonempty[OF hE1] by simp
  qed
  obtain K where hK_complex: "geotop_is_complex K"
              and hK_poly: "geotop_polyhedron K = B1 \<union> B2"
    using pair_of_arcs_polyhedron[OF hB1 hB2 hE1 hE2 h_disj] by blast
  have h_homeo: "B1 \<union> B2 homeomorphic sphere (0::real^2) 1"
    using pair_of_arcs_image_homeomorphic_sphere[OF hE1 hE2 h_disj h_distinct] by blast
  have h_std_sphere_eq: "(geotop_std_sphere::(real^2) set) = sphere 0 1"
    unfolding geotop_std_sphere_def by (auto simp: norm_eq_sqrt_inner)
  have h_homeo_std: "B1 \<union> B2 homeomorphic (geotop_std_sphere::(real^2) set)"
    using h_homeo h_std_sphere_eq by simp
  have h_n_sphere: "geotop_is_n_sphere (B1 \<union> B2)
        (subspace_topology UNIV geotop_euclidean_topology (B1 \<union> B2)) 1"
  proof -
    obtain f where h_top1_homeo: "top1_homeomorphism_on (B1 \<union> B2)
        (subspace_topology UNIV geotop_euclidean_topology (B1 \<union> B2))
        (geotop_std_sphere::(real^2) set)
        (subspace_topology UNIV geotop_euclidean_topology (geotop_std_sphere::(real^2) set)) f"
      using geotop_HOL_homeomorphic_imp_top1_homeomorphism_on[OF h_homeo_std] by blast
    have h_eucl_top: "is_topology_on UNIV (geotop_euclidean_topology::(real^2) set set)"
      using top1_open_sets_is_topology_on_UNIV
      by (simp add: geotop_euclidean_topology_eq_open_sets)
    have h_topology: "is_topology_on (B1 \<union> B2)
        (subspace_topology UNIV geotop_euclidean_topology (B1 \<union> B2))"
      using subspace_topology_is_topology_on h_eucl_top by blast
    show ?thesis
      unfolding geotop_is_n_sphere_def
      using h_top1_homeo h_topology by blast
  qed
  show ?thesis
    unfolding geotop_is_polygon_def
    using hK_complex hK_poly h_n_sphere by blast
qed

text \<open>A broken line is closed (compact arc).\<close>

lemma broken_line_closed:
  fixes B :: "(real^2) set" and E :: "(real^2) set"
  assumes hE: "geotop_arc_endpoints B E"
  shows "closed B"
proof -
  obtain f0 :: "real \<Rightarrow> real^2" where
    h_homeo: "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
        (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1}) B
        (subspace_topology UNIV geotop_euclidean_topology B) f0"
    using hE unfolding geotop_arc_endpoints_def by blast
  have h_unit_iv: "{t::real. 0 \<le> t \<and> t \<le> 1} = {0..1}" by auto
  have h_homeo_HOL: "{0..1::real} homeomorphic B"
    using h_homeo top1_homeomorphism_on_geotop_imp_HOL_homeomorphic h_unit_iv by metis
  have h_compact_01: "compact {0..1::real}" by simp
  have h_compact_B: "compact B"
    using h_compact_01 h_homeo_HOL homeomorphic_compactness by blast
  show ?thesis using h_compact_B compact_imp_closed by blast
qed

text \<open>Subclaim 4 of h_open_in_int (the deepest local-component-constancy step):
  if x is a frontier point of an open set U with U disjoint from broken line Bi,
  and y is sufficiently close to x along Int Bi, then y is also a frontier point
  of U. This requires that U "sticks" to the same local side of Bi across small
  Bi-displacements — a connectivity-of-complement argument tying back to
  components of UNIV - Bi.

  Target form (for future sessions to formalize):
  \<open>\<exists>\<delta>>0. \<forall>y \<in> ball x \<delta> \<inter> geotop_arc_interior Bi E. y \<in> frontier U\<close>
  given x \<in> frontier U, x \<in> Int Bi, U open, U disjoint from B1\<union>B2\<union>B3.

  Proof outline:
  (1) obtain the isolating \<epsilon> from `theta_arc_interior_isolated_ball`,
  (2) obtain half-balls H+, H- via `ball_minus_hyperplane_has_two_components`,
  (3) WLOG U meets H+ near x (since x \<in> frontier U),
  (4) for y close to x on Int Bi, the corresponding half-ball at y still meets U
      (via path-connectedness of U + arc-connectedness of Int Bi).\<close>

text \<open>At each interior point of an arc Bi of a theta-graph, an open ball around x
  isolates Bi from the other two arcs (since arc-interiors are pairwise disjoint
  and each Bj is closed).\<close>

text \<open>For a broken line B and a point x \<in> B, exists a finite complex K with
  |K| = B and a small ball around x contained in the union of K-simplices
  containing x. This bridges `finite_union_closed_local_isolation` to broken
  lines. It is the second piece needed for h_open_in_int's local geometry
  (after the theta-graph isolation step).\<close>

lemma broken_line_local_simplex_isolation:
  fixes B :: "(real^2) set" and x :: "real^2"
  assumes hB: "geotop_is_broken_line B"
      and hxB: "x \<in> B"
  shows "\<exists>K. geotop_is_complex K \<and> finite K \<and> geotop_polyhedron K = B \<and>
              geotop_complex_is_1dim K \<and>
              (\<exists>\<delta>>0. ball x \<delta> \<inter> B \<subseteq> \<Union>{\<sigma>\<in>K. x \<in> \<sigma>})"
proof -
  obtain K where hK_complex: "geotop_is_complex K"
              and hK_1dim: "geotop_complex_is_1dim K"
              and hK_poly: "geotop_polyhedron K = B"
              and hK_fin: "finite K"
    using geotop_broken_line_finite_witness[OF hB] by (by100 blast)
  have hK_simp_all: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
    by (rule conjunct1[OF hK_complex[unfolded geotop_is_complex_def]])
  have hK_closed_all: "\<forall>\<sigma>\<in>K. closed \<sigma>"
  proof
    fix \<sigma> assume h\<sigma>K: "\<sigma> \<in> K"
    have hsim: "geotop_is_simplex \<sigma>" using hK_simp_all h\<sigma>K by (by100 blast)
    obtain V m n where hVfin: "finite V" and h\<sigma>_hull: "\<sigma> = geotop_convex_hull V"
      using hsim unfolding geotop_is_simplex_def by (by100 blast)
    have h\<sigma>_HOL: "\<sigma> = convex hull V"
      using h\<sigma>_hull geotop_convex_hull_eq_HOL by (by100 simp)
    have h_compact: "compact (convex hull V)"
      using hVfin finite_imp_compact_convex_hull by (by100 blast)
    have h_closed_hull: "closed (convex hull V)"
      using h_compact compact_imp_closed by (by100 blast)
    show "closed \<sigma>" using h\<sigma>_HOL h_closed_hull by (by100 simp)
  qed
  have hB_union: "B = \<Union>K"
    using hK_poly unfolding geotop_polyhedron_def by (by100 simp)
  obtain \<delta> where h\<delta>_pos: "\<delta> > 0"
              and h\<delta>_sub: "ball x \<delta> \<inter> B \<subseteq> \<Union>{\<sigma>\<in>K. x \<in> \<sigma>}"
    using finite_union_closed_local_isolation[OF hK_fin hK_closed_all hB_union hxB]
    by (by100 blast)
  show ?thesis using hK_complex hK_fin hK_poly hK_1dim h\<delta>_pos h\<delta>_sub by (by100 blast)
qed

lemma theta_arc_interior_isolated_ball:
  fixes B1 B2 B3 E :: "(real^2) set" and x :: "real^2"
  assumes hcl_B2: "closed B2" and hcl_B3: "closed B3"
      and h_int12: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = {}"
      and h_int13: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B3 E = {}"
      and hx1: "x \<in> geotop_arc_interior B1 E"
  shows "\<exists>\<epsilon>>0. ball x \<epsilon> \<inter> (B1 \<union> B2 \<union> B3) \<subseteq> B1"
proof -
  have h_int12_diff: "(B1 - E) \<inter> (B2 - E) = {}"
    using h_int12 unfolding geotop_arc_interior_def by (by100 simp)
  have h_int13_diff: "(B1 - E) \<inter> (B3 - E) = {}"
    using h_int13 unfolding geotop_arc_interior_def by (by100 simp)
  have hx1_diff: "x \<in> B1 - E"
    using hx1 unfolding geotop_arc_interior_def by (by100 simp)
  have hxB1: "x \<in> B1" using hx1_diff by (by100 blast)
  have hxnE: "x \<notin> E" using hx1_diff by (by100 blast)
  have hxnB2: "x \<notin> B2"
  proof
    assume hxB2: "x \<in> B2"
    have h: "x \<in> (B1 - E) \<inter> (B2 - E)"
      using hx1_diff hxB2 hxnE by (by100 blast)
    thus False using h_int12_diff by (by100 blast)
  qed
  have hxnB3: "x \<notin> B3"
  proof
    assume hxB3: "x \<in> B3"
    have h: "x \<in> (B1 - E) \<inter> (B3 - E)"
      using hx1_diff hxB3 hxnE by (by100 blast)
    thus False using h_int13_diff by (by100 blast)
  qed
  have h_in_compl_B2: "x \<in> -B2" using hxnB2 by (by100 simp)
  have h_open_compl_B2: "open (-B2)" using hcl_B2 closed_def by (by100 blast)
  obtain \<epsilon>\<^sub>2 where h\<epsilon>2_pos: "\<epsilon>\<^sub>2 > 0" and h\<epsilon>2_sub: "ball x \<epsilon>\<^sub>2 \<subseteq> -B2"
    using h_in_compl_B2 h_open_compl_B2 open_contains_ball by (by100 metis)
  have h_in_compl_B3: "x \<in> -B3" using hxnB3 by (by100 simp)
  have h_open_compl_B3: "open (-B3)" using hcl_B3 closed_def by (by100 blast)
  obtain \<epsilon>\<^sub>3 where h\<epsilon>3_pos: "\<epsilon>\<^sub>3 > 0" and h\<epsilon>3_sub: "ball x \<epsilon>\<^sub>3 \<subseteq> -B3"
    using h_in_compl_B3 h_open_compl_B3 open_contains_ball by (by100 metis)
  define \<epsilon> where "\<epsilon> = min \<epsilon>\<^sub>2 \<epsilon>\<^sub>3"
  have h\<epsilon>_pos: "\<epsilon> > 0" using h\<epsilon>2_pos h\<epsilon>3_pos \<epsilon>_def by (by100 simp)
  have h\<epsilon>_sub2: "ball x \<epsilon> \<subseteq> ball x \<epsilon>\<^sub>2" using \<epsilon>_def by (by100 auto)
  have h\<epsilon>_sub3: "ball x \<epsilon> \<subseteq> ball x \<epsilon>\<^sub>3" using \<epsilon>_def by (by100 auto)
  have h_int2: "ball x \<epsilon> \<inter> B2 = {}" using h\<epsilon>_sub2 h\<epsilon>2_sub by (by100 blast)
  have h_int3: "ball x \<epsilon> \<inter> B3 = {}" using h\<epsilon>_sub3 h\<epsilon>3_sub by (by100 blast)
  have h_subset: "ball x \<epsilon> \<inter> (B1 \<union> B2 \<union> B3) \<subseteq> B1"
    using h_int2 h_int3 by (by100 blast)
  show ?thesis using h\<epsilon>_pos h_subset by (by100 blast)
qed

text \<open>Generic bridge: the geotop component-set on \<open>UNIV - X\<close> equals
  HOL-Analysis \<open>components (UNIV - X)\<close>.\<close>

lemma geotop_components_complement_eq:
  fixes X :: "(real^2) set"
  shows "{C. \<exists>P. P \<in> UNIV - X \<and>
           C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - X) P}
       = components (UNIV - X)"
proof -
  have h_bridge: "\<And>P. geotop_component_at UNIV geotop_euclidean_topology (UNIV - X) P
              = connected_component_set (UNIV - X) P"
    by (rule geotop_component_at_UNIV_eq_connected_component_set)
  show ?thesis using h_bridge unfolding components_def by auto
qed

text \<open>Extract a parametrising arc \<open>f0 : [0,1] \<to> B\<close> from
  \<open>geotop_arc_endpoints B E\<close>. This bundles the standard data we repeatedly
  need: continuity, bijection, injectivity, image, endpoint equality.\<close>

lemma arc_endpoints_imp_param:
  fixes B :: "(real^2) set" and E :: "(real^2) set"
  assumes hE: "geotop_arc_endpoints B E"
  obtains f0 :: "real \<Rightarrow> real^2"
    where "continuous_on {0..1::real} f0"
      and "bij_betw f0 {0..1::real} B"
      and "f0 ` {0..1} = B"
      and "inj_on f0 {0..1::real}"
      and "E = {f0 0, f0 1}"
proof -
  obtain f0 :: "real \<Rightarrow> real^2" where
    h_homeo: "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
        (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1}) B
        (subspace_topology UNIV geotop_euclidean_topology B) f0"
    and hE_eq: "E = {f0 0, f0 1}"
    using hE unfolding geotop_arc_endpoints_def by (by100 blast)
  have h_unit_iv: "{t::real. 0 \<le> t \<and> t \<le> 1} = {0..1}" by (by100 auto)
  have h_homeo_01: "top1_homeomorphism_on {0..1::real}
        (subspace_topology UNIV geotop_euclidean_topology {0..1}) B
        (subspace_topology UNIV geotop_euclidean_topology B) f0"
    using h_homeo h_unit_iv by (by100 simp)
  have h_cont_top1: "top1_continuous_map_on {0..1}
        (subspace_topology UNIV geotop_euclidean_topology {0..1}) B
        (subspace_topology UNIV geotop_euclidean_topology B) f0"
    by (rule top1_homeomorphism_on_imp_cont1[OF h_homeo_01])
  have h_f0_cont: "continuous_on {0..1::real} f0"
    using h_cont_top1 top1_continuous_map_on_geotop_imp_continuous_on by (by100 blast)
  have h_f0_bij_J: "bij_betw f0 {t::real. 0 \<le> t \<and> t \<le> 1} B"
    by (rule top1_homeomorphism_on_imp_bij[OF h_homeo])
  have h_f0_bij_betw: "bij_betw f0 {0..1::real} B"
    using h_f0_bij_J h_unit_iv by (by100 simp)
  have h_f0_image: "f0 ` {0..1} = B"
    using h_f0_bij_betw unfolding bij_betw_def by (by100 simp)
  have h_f0_inj: "inj_on f0 {0..1::real}"
    using h_f0_bij_betw unfolding bij_betw_def by (by100 simp)
  show ?thesis using h_f0_cont h_f0_bij_betw h_f0_image h_f0_inj hE_eq that by (by100 blast)
qed

text \<open>The open interior of an arc is connected (homeomorphic to \<open>(0,1)\<close>).\<close>

lemma arc_interior_connected:
  fixes B :: "(real^2) set" and E :: "(real^2) set"
  assumes hE: "geotop_arc_endpoints B E"
  shows "connected (geotop_arc_interior B E)"
proof -
  obtain f0 :: "real \<Rightarrow> real^2"
    where h_f0_cont: "continuous_on {0..1::real} f0"
      and h_f0_bij_betw: "bij_betw f0 {0..1::real} B"
      and h_f0_image: "f0 ` {0..1} = B"
      and h_f0_inj: "inj_on f0 {0..1::real}"
      and hE_eq: "E = {f0 0, f0 1}"
    using arc_endpoints_imp_param[OF hE] by (by100 blast)
  have h_open_iv_connected: "connected {0<..<(1::real)}" by simp
  have h_open_iv_sub: "{0<..<(1::real)} \<subseteq> {0..1}" by auto
  have h_f0_cont_on_open_iv: "continuous_on {0<..<1} f0"
    using h_f0_cont h_open_iv_sub continuous_on_subset by blast
  have h_image_connected: "connected (f0 ` {0<..<1})"
    using connected_continuous_image[OF h_f0_cont_on_open_iv h_open_iv_connected] .
  text \<open>Show \<open>f0 ` {0<..<1} = geotop_arc_interior B E\<close>.\<close>
  have h_image_eq: "f0 ` {0<..<1} = geotop_arc_interior B E"
  proof
    show "f0 ` {0<..<1} \<subseteq> geotop_arc_interior B E"
    proof
      fix x assume "x \<in> f0 ` {0<..<1}"
      then obtain t where ht: "t \<in> {0<..<1}" and hx_eq: "x = f0 t" by blast
      have ht_in: "t \<in> {0..1}" using ht by simp
      have ht_ne_0: "t \<noteq> 0" using ht by simp
      have ht_ne_1: "t \<noteq> 1" using ht by simp
      have hx_in_B: "x \<in> B" using hx_eq h_f0_image ht_in by blast
      have hx_ne_0: "x \<noteq> f0 0" using hx_eq ht_ne_0 ht_in h_f0_inj by (auto dest: inj_onD)
      have hx_ne_1: "x \<noteq> f0 1" using hx_eq ht_ne_1 ht_in h_f0_inj by (auto dest: inj_onD)
      have hx_notin_E: "x \<notin> E" using hE_eq hx_ne_0 hx_ne_1 by simp
      show "x \<in> geotop_arc_interior B E"
        unfolding geotop_arc_interior_def using hx_in_B hx_notin_E by blast
    qed
    show "geotop_arc_interior B E \<subseteq> f0 ` {0<..<1}"
    proof
      fix x assume hx: "x \<in> geotop_arc_interior B E"
      have hxB: "x \<in> B" using hx unfolding geotop_arc_interior_def by blast
      have hx_notin_E: "x \<notin> E" using hx unfolding geotop_arc_interior_def by blast
      then obtain t where ht_in: "t \<in> {0..1}" and hx_eq: "x = f0 t"
        using hxB h_f0_image by blast
      have ht_ne_0: "t \<noteq> 0" using hx_notin_E hE_eq hx_eq by blast
      have ht_ne_1: "t \<noteq> 1" using hx_notin_E hE_eq hx_eq by blast
      have ht_in_open: "t \<in> {0<..<1}"
        using ht_in ht_ne_0 ht_ne_1 by auto
      show "x \<in> f0 ` {0<..<1}" using ht_in_open hx_eq by blast
    qed
  qed
  show ?thesis using h_image_connected h_image_eq by simp
qed

text \<open>A broken line in \<open>real^2\<close> has empty topological interior (1-dim subset
  of 2-dim space, via invariance of dimension).\<close>

lemma broken_line_interior_empty:
  fixes B :: "(real^2) set" and E :: "(real^2) set"
  assumes hE: "geotop_arc_endpoints B E"
  shows "interior B = {}"
proof (rule ccontr)
  assume "interior B \<noteq> {}"
  then obtain x where hx_int: "x \<in> interior B" by blast
  text \<open>From the arc parametrisation, extract the inverse homeomorphism
    \<open>g : B \<to> [0,1]\<close> as a function \<open>real^2 \<to> real\<close>.\<close>
  obtain f0 :: "real \<Rightarrow> real^2" where
    h_homeo: "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
        (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1}) B
        (subspace_topology UNIV geotop_euclidean_topology B) f0"
    using hE unfolding geotop_arc_endpoints_def by blast
  have h_unit_iv: "{t::real. 0 \<le> t \<and> t \<le> 1} = {0..1}" by auto
  have h_homeo_HOL: "{0..1::real} homeomorphic B"
    using h_homeo top1_homeomorphism_on_geotop_imp_HOL_homeomorphic h_unit_iv by metis
  then obtain g g' where hgg': "homeomorphism {0..1::real} B g g'"
    using homeomorphic_def by blast
  text \<open>\<open>g'\<close> is continuous on \<open>B\<close> with image in \<open>{0..1}\<close>, injective on \<open>B\<close>.\<close>
  have hg'_cont_B: "continuous_on B g'"
    using hgg' unfolding homeomorphism_def by blast
  have hg'_inj_B: "inj_on g' B"
  proof (rule inj_onI)
    fix x y assume hx: "x \<in> B" and hy: "y \<in> B" and h_eq: "g' x = g' y"
    have hg_x: "g (g' x) = x" using hgg' hx unfolding homeomorphism_def by (by100 blast)
    have hg_y: "g (g' y) = y" using hgg' hy unfolding homeomorphism_def by (by100 blast)
    show "x = y" using h_eq hg_x hg_y by (by100 metis)
  qed
  have hO_open: "open (interior B)" by simp
  have hO_sub_B: "interior B \<subseteq> B" by (rule interior_subset)
  have hg'_cont_O: "continuous_on (interior B) g'"
    using hg'_cont_B hO_sub_B continuous_on_subset by blast
  have hg'_inj_O: "inj_on g' (interior B)"
    using hg'_inj_B hO_sub_B inj_on_subset by blast
  have hO_ne: "interior B \<noteq> {}" using hx_int by blast
  text \<open>Apply invariance_of_dimension: \<open>g' : real^2 \<to> real\<close> continuous,
    \<open>interior B\<close> open, injective on it, non-empty \<Longrightarrow> \<open>DIM(real^2) \<le> DIM(real)\<close>.\<close>
  have h_dim_le: "DIM(real^2) \<le> DIM(real)"
    by (rule invariance_of_dimension[OF hg'_cont_O hO_open hg'_inj_O hO_ne])
  have h_dim_R2: "DIM(real^2) = 2" by simp
  have h_dim_R: "DIM(real) = 1" by simp
  show False using h_dim_le h_dim_R2 h_dim_R by simp
qed


text \<open>The closure of the open interior of an arc (in \<open>real^2\<close>) is the whole arc.
  Endpoints are limits of interior points (continuous image of \<open>0\<close> and \<open>1\<close> as
  limits of \<open>(0,1)\<close>).\<close>

lemma arc_closure_interior_eq_arc:
  fixes B :: "(real^2) set" and E :: "(real^2) set"
  assumes hE: "geotop_arc_endpoints B E"
  shows "closure (geotop_arc_interior B E) = B"
proof
  text \<open>Forward: closure(B - E) ⊆ B.\<close>
  show "closure (geotop_arc_interior B E) \<subseteq> B"
  proof -
    have h_closed_B: "closed B" by (rule broken_line_closed[OF hE])
    have "geotop_arc_interior B E \<subseteq> B"
      unfolding geotop_arc_interior_def by blast
    thus ?thesis using h_closed_B closure_minimal by blast
  qed
next
  text \<open>Backward: B ⊆ closure(B - E). Suffices Int Bi ⊆ closure(Int Bi) (trivial)
    plus E ⊆ closure(Int Bi) (each endpoint is a limit of interior points).\<close>
  show "B \<subseteq> closure (geotop_arc_interior B E)"
  proof
    fix x assume hxB: "x \<in> B"
    show "x \<in> closure (geotop_arc_interior B E)"
    proof (cases "x \<in> E")
      case False
      hence "x \<in> geotop_arc_interior B E"
        unfolding geotop_arc_interior_def using hxB by (by100 blast)
      thus ?thesis using closure_subset by (by100 blast)
    next
      case True
      text \<open>x is one of the two endpoints. We show x is a limit of points in
        the interior using the arc homeomorphism with [0,1].\<close>
      obtain f0 :: "real \<Rightarrow> real^2"
        where h_f0_cont: "continuous_on {0..1::real} f0"
          and h_f0_bij_betw: "bij_betw f0 {0..1::real} B"
          and h_f0_image: "f0 ` {0..1} = B"
          and h_f0_inj: "inj_on f0 {0..1::real}"
          and hE_eq: "E = {f0 0, f0 1}"
        using arc_endpoints_imp_param[OF hE] by (by100 blast)
      have hx_eq: "x = f0 0 \<or> x = f0 1" using True hE_eq by blast
      show ?thesis
      proof (cases "x = f0 0")
        case True
        text \<open>Approach \<open>f0 0\<close> via \<open>f0 (1/Suc n)\<close>.\<close>
        define seq where "seq n = f0 (1 / real (Suc (Suc n)))" for n :: nat
        have h_t_in: "\<forall>n. (1 / real (Suc (Suc n))) \<in> {0..1}"
          by (auto simp: divide_le_eq)
        have h_t_pos: "\<forall>n. (1 / real (Suc (Suc n))) > 0"
          by simp
        have h_t_lt_1: "\<forall>n. (1 / real (Suc (Suc n))) < 1"
        proof
          fix n :: nat
          have "real (Suc (Suc n)) > 1" by simp
          thus "1 / real (Suc (Suc n)) < 1" by simp
        qed
        have h_seq_in_int: "\<forall>n. seq n \<in> geotop_arc_interior B E"
        proof
          fix n :: nat
          have h_t_ne_0: "(1 / real (Suc (Suc n))) \<noteq> 0" using h_t_pos by simp
          have h_t_ne_1: "(1 / real (Suc (Suc n))) \<noteq> 1" using h_t_lt_1 by force
          have h_in: "(1 / real (Suc (Suc n))) \<in> {0..1}" using h_t_in by simp
          have h_seq_in_B: "seq n \<in> B" using h_in h_f0_image unfolding seq_def by blast
          have h_seq_ne_f00: "seq n \<noteq> f0 0"
            unfolding seq_def
            using h_t_ne_0 h_in h_f0_inj inj_onD by fastforce
          have h_seq_ne_f01: "seq n \<noteq> f0 1"
            unfolding seq_def
            using h_t_ne_1 h_in h_f0_inj inj_onD by fastforce
          have h_seq_notin_E: "seq n \<notin> E" using hE_eq h_seq_ne_f00 h_seq_ne_f01 by blast
          show "seq n \<in> geotop_arc_interior B E"
            unfolding geotop_arc_interior_def using h_seq_in_B h_seq_notin_E by blast
        qed
        have h_seq_to_x: "seq \<longlonglongrightarrow> x"
        proof -
          have h_t_to_0: "(\<lambda>n. 1 / real (Suc (Suc n))) \<longlonglongrightarrow> 0"
          proof -
            have h_inv: "(\<lambda>n. inverse (real (Suc n))) \<longlonglongrightarrow> 0"
              by (rule LIMSEQ_inverse_real_of_nat)
            have h_s: "(\<lambda>n. inverse (real (Suc (Suc n)))) \<longlonglongrightarrow> 0"
              using h_inv LIMSEQ_Suc by blast
            have h_eq: "(\<lambda>n. 1 / real (Suc (Suc n))) = (\<lambda>n. inverse (real (Suc (Suc n))))"
              by (simp add: inverse_eq_divide)
            show ?thesis using h_s h_eq by simp
          qed
          have h_0_in: "(0::real) \<in> {0..1}" by simp
          have h_seq_lim: "(\<lambda>n. f0 (1 / real (Suc (Suc n)))) \<longlonglongrightarrow> f0 0"
            using continuous_on_tendsto_compose[OF h_f0_cont h_t_to_0 h_0_in] h_t_in
            by simp
          show ?thesis using h_seq_lim True unfolding seq_def by simp
        qed
        show ?thesis
          using h_seq_to_x h_seq_in_int closure_sequential by blast
      next
        case False
        hence hx_eq_f01: "x = f0 1" using hx_eq by blast
        define seq where "seq n = f0 (1 - 1 / real (Suc (Suc n)))" for n :: nat
        have h_t_in: "\<forall>n. (1 - 1 / real (Suc (Suc n))) \<in> {0..1}"
          by (auto simp: divide_le_eq)
        have h_t_lt_1: "\<forall>n. (1 - 1 / real (Suc (Suc n))) < 1"
          by simp
        have h_t_pos: "\<forall>n. (1 - 1 / real (Suc (Suc n))) > 0"
        proof
          fix n :: nat
          have "real (Suc (Suc n)) > 1" by simp
          hence "1 / real (Suc (Suc n)) < 1" by simp
          thus "(1 - 1 / real (Suc (Suc n))) > 0" by simp
        qed
        have h_seq_in_int: "\<forall>n. seq n \<in> geotop_arc_interior B E"
        proof
          fix n :: nat
          have h_t_ne_1: "(1 - 1 / real (Suc (Suc n))) \<noteq> 1" using h_t_lt_1 by force
          have h_t_ne_0: "(1 - 1 / real (Suc (Suc n))) \<noteq> 0" using h_t_pos by force
          have h_in: "(1 - 1 / real (Suc (Suc n))) \<in> {0..1}" using h_t_in by simp
          have h_seq_in_B: "seq n \<in> B" using h_in h_f0_image unfolding seq_def by blast
          have h_seq_ne_f00: "seq n \<noteq> f0 0"
            unfolding seq_def
            using h_t_ne_0 h_in h_f0_inj inj_onD by fastforce
          have h_seq_ne_f01: "seq n \<noteq> f0 1"
            unfolding seq_def
            using h_t_ne_1 h_in h_f0_inj inj_onD by fastforce
          have h_seq_notin_E: "seq n \<notin> E" using hE_eq h_seq_ne_f00 h_seq_ne_f01 by blast
          show "seq n \<in> geotop_arc_interior B E"
            unfolding geotop_arc_interior_def using h_seq_in_B h_seq_notin_E by blast
        qed
        have h_seq_to_x: "seq \<longlonglongrightarrow> x"
        proof -
          have h_t_to_1: "(\<lambda>n. 1 - 1 / real (Suc (Suc n))) \<longlonglongrightarrow> 1"
          proof -
            have "(\<lambda>n. 1 / real (Suc (Suc n))) \<longlonglongrightarrow> 0"
            proof -
              have h_inv: "(\<lambda>n. inverse (real (Suc n))) \<longlonglongrightarrow> 0"
                by (rule LIMSEQ_inverse_real_of_nat)
              have h_s: "(\<lambda>n. inverse (real (Suc (Suc n)))) \<longlonglongrightarrow> 0"
                using h_inv LIMSEQ_Suc by blast
              have h_eq: "(\<lambda>n. 1 / real (Suc (Suc n))) = (\<lambda>n. inverse (real (Suc (Suc n))))"
                by (simp add: inverse_eq_divide)
              show ?thesis using h_s h_eq by simp
            qed
            thus ?thesis by (auto intro: tendsto_eq_intros)
          qed
          have h_1_in: "(1::real) \<in> {0..1}" by simp
          have h_seq_lim: "(\<lambda>n. f0 (1 - 1 / real (Suc (Suc n)))) \<longlonglongrightarrow> f0 1"
            using continuous_on_tendsto_compose[OF h_f0_cont h_t_to_1 h_1_in] h_t_in
            by simp
          show ?thesis using h_seq_lim hx_eq_f01 unfolding seq_def by simp
        qed
        show ?thesis
          using h_seq_to_x h_seq_in_int closure_sequential by blast
      qed
    qed
  qed
qed

text \<open>A broken line is bounded (compact arc).\<close>

lemma broken_line_bounded:
  fixes B :: "(real^2) set" and E :: "(real^2) set"
  assumes hE: "geotop_arc_endpoints B E"
  shows "bounded B"
proof -
  obtain f0 :: "real \<Rightarrow> real^2" where
    h_homeo: "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
        (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1}) B
        (subspace_topology UNIV geotop_euclidean_topology B) f0"
    using hE unfolding geotop_arc_endpoints_def by blast
  have h_unit_iv: "{t::real. 0 \<le> t \<and> t \<le> 1} = {0..1}" by auto
  have h_homeo_HOL: "{0..1::real} homeomorphic B"
    using h_homeo top1_homeomorphism_on_geotop_imp_HOL_homeomorphic h_unit_iv by metis
  have h_compact_01: "compact {0..1::real}" by simp
  have h_compact_B: "compact B"
    using h_compact_01 h_homeo_HOL homeomorphic_compactness by blast
  show ?thesis using h_compact_B compact_imp_bounded by blast
qed

text \<open>The complement of a polyhedral \<theta>-graph has at least 2 components.\<close>

lemma theta_graph_complement_has_two_components:
  fixes M B1 B2 B3 E :: "(real^2) set"
  assumes h\<theta>: "geotop_is_polyhedral_theta_graph M B1 B2 B3 E"
  shows "\<exists>D1 D2. D1 \<in> components (UNIV - M) \<and> D2 \<in> components (UNIV - M) \<and> D1 \<noteq> D2"
proof -
  have h_theta: "geotop_is_theta_graph M B1 B2 B3 E"
    using h\<theta> unfolding geotop_is_polyhedral_theta_graph_def by blast
  have hM_eq: "M = B1 \<union> B2 \<union> B3"
    using h_theta unfolding geotop_is_theta_graph_def by blast
  have hB1_bl: "geotop_is_broken_line B1"
   and hB2_bl: "geotop_is_broken_line B2"
   and hB3_bl: "geotop_is_broken_line B3"
    using h\<theta> unfolding geotop_is_polyhedral_theta_graph_def by blast+
  have hE1: "geotop_arc_endpoints B1 E"
   and hE2: "geotop_arc_endpoints B2 E"
   and hE3: "geotop_arc_endpoints B3 E"
    using h_theta unfolding geotop_is_theta_graph_def by blast+
  have h_int12: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = {}"
    using h_theta unfolding geotop_is_theta_graph_def by blast
  have h_poly_12: "geotop_is_polygon (B1 \<union> B2)"
    by (rule pair_of_arcs_is_polygon[OF hB1_bl hB2_bl hE1 hE2 h_int12])
  text \<open>Polygon \<open>B1 \<union> B2\<close> separates \<open>R^2\<close> into 2 components.\<close>
  have h_card_12: "card (components (UNIV - (B1 \<union> B2))) = 2"
    by (rule polygon_components_card[OF h_poly_12])
  obtain C1 C2 where hC12_set: "components (UNIV - (B1 \<union> B2)) = {C1, C2}"
                and hC12_ne: "C1 \<noteq> C2"
    using h_card_12 card_2_iff by metis
  text \<open>Both \<open>C1\<close> and \<open>C2\<close> have a point not in M.\<close>
  have h_B3_int_empty: "interior B3 = {}" by (rule broken_line_interior_empty[OF hE3])
  have h_each_C_minus_M_ne: "\<forall>C\<in>components (UNIV - (B1 \<union> B2)). C - M \<noteq> {}"
  proof
    fix C assume hC: "C \<in> components (UNIV - (B1 \<union> B2))"
    have hcl_B12: "closed (B1 \<union> B2)"
      using broken_line_closed[OF hE1] broken_line_closed[OF hE2] closed_Un by blast
    have hC_open: "open C"
    proof -
      have "open (- (B1 \<union> B2))" using hcl_B12 open_Compl by blast
      hence "open (UNIV - (B1 \<union> B2))" by (simp add: Compl_eq_Diff_UNIV)
      thus ?thesis using open_components hC by blast
    qed
    have hC_ne: "C \<noteq> {}" using hC in_components_nonempty by blast
    text \<open>If \<open>C \<subseteq> M\<close>: \<open>C \<subseteq> M \<setminus> (B1 \<union> B2) \<subseteq> B3 \<setminus> (B1 \<union> B2)\<close>, so \<open>C \<subseteq> interior B3 = \<emptyset>\<close>.\<close>
    have h_not_C_sub_M: "\<not> C \<subseteq> M"
    proof
      assume hC_sub_M: "C \<subseteq> M"
      have hC_sub_compl: "C \<subseteq> UNIV - (B1 \<union> B2)"
        using hC in_components_subset by blast
      have hC_sub_M_minus: "C \<subseteq> M - (B1 \<union> B2)"
        using hC_sub_M hC_sub_compl by blast
      have h_M_minus: "M - (B1 \<union> B2) \<subseteq> B3"
        using hM_eq by blast
      have hC_sub_B3: "C \<subseteq> B3" using hC_sub_M_minus h_M_minus by blast
      have "C \<subseteq> interior B3"
        using hC_open hC_sub_B3 interior_maximal by blast
      hence "C = {}" using h_B3_int_empty by simp
      thus False using hC_ne by simp
    qed
    show "C - M \<noteq> {}" using h_not_C_sub_M by blast
  qed
  text \<open>Take points \<open>x_1 \<in> C1 - M\<close> and \<open>x_2 \<in> C2 - M\<close>.\<close>
  obtain x1 where hx1_C1: "x1 \<in> C1" and hx1_notM: "x1 \<notin> M"
    using h_each_C_minus_M_ne hC12_set by blast
  obtain x2 where hx2_C2: "x2 \<in> C2" and hx2_notM: "x2 \<notin> M"
    using h_each_C_minus_M_ne hC12_set by blast
  have hx1_in: "x1 \<in> UNIV - M" using hx1_notM by blast
  have hx2_in: "x2 \<in> UNIV - M" using hx2_notM by blast
  text \<open>The components of \<open>UNIV - M\<close> through \<open>x1, x2\<close>.\<close>
  define D1 where "D1 = connected_component_set (UNIV - M) x1"
  define D2 where "D2 = connected_component_set (UNIV - M) x2"
  have hD1_comp: "D1 \<in> components (UNIV - M)"
    unfolding D1_def using hx1_in componentsI by metis
  have hD2_comp: "D2 \<in> components (UNIV - M)"
    unfolding D2_def using hx2_in componentsI by metis
  text \<open>\<open>D1 \<subseteq> C1\<close> and \<open>D2 \<subseteq> C2\<close>.\<close>
  have hD1_sub_compl12: "D1 \<subseteq> UNIV - (B1 \<union> B2)"
    unfolding D1_def using connected_component_subset hM_eq by force
  have hD1_conn: "connected D1"
    unfolding D1_def by (rule connected_connected_component)
  have hD1_in_some: "\<exists>C \<in> components (UNIV - (B1 \<union> B2)). D1 \<subseteq> C"
  proof -
    have hx1_compl12: "x1 \<in> UNIV - (B1 \<union> B2)"
      using hx1_notM hM_eq by blast
    define D1' where "D1' = connected_component_set (UNIV - (B1 \<union> B2)) x1"
    have "D1' \<in> components (UNIV - (B1 \<union> B2))"
      unfolding D1'_def using hx1_compl12 componentsI by metis
    moreover have "D1 \<subseteq> D1'"
      unfolding D1_def D1'_def
      by (rule connected_component_mono) (use hM_eq in blast)
    ultimately show ?thesis by blast
  qed
  obtain D1' where hD1'_comp: "D1' \<in> components (UNIV - (B1 \<union> B2))"
                and hD1_sub_D1': "D1 \<subseteq> D1'"
    using hD1_in_some by blast
  have hD2_in_some: "\<exists>C \<in> components (UNIV - (B1 \<union> B2)). D2 \<subseteq> C"
  proof -
    have hx2_compl12: "x2 \<in> UNIV - (B1 \<union> B2)"
      using hx2_notM hM_eq by blast
    define D2' where "D2' = connected_component_set (UNIV - (B1 \<union> B2)) x2"
    have "D2' \<in> components (UNIV - (B1 \<union> B2))"
      unfolding D2'_def using hx2_compl12 componentsI by metis
    moreover have "D2 \<subseteq> D2'"
      unfolding D2_def D2'_def
      by (rule connected_component_mono) (use hM_eq in blast)
    ultimately show ?thesis by blast
  qed
  obtain D2' where hD2'_comp: "D2' \<in> components (UNIV - (B1 \<union> B2))"
                and hD2_sub_D2': "D2 \<subseteq> D2'"
    using hD2_in_some by blast
  text \<open>Show \<open>D1 \<noteq> D2\<close> by showing \<open>D1' = C1\<close> and \<open>D2' = C2\<close> (so disjoint).\<close>
  have hx1_in_D1': "x1 \<in> D1'"
    using hD1_sub_D1' connected_component_refl unfolding D1_def
    by (metis hx1_in mem_Collect_eq subset_iff)
  have hx2_in_D2': "x2 \<in> D2'"
    using hD2_sub_D2' connected_component_refl unfolding D2_def
    by (metis hx2_in mem_Collect_eq subset_iff)
  have hC1_C2_disj: "C1 \<inter> C2 = {}"
  proof -
    have hC1_in: "C1 \<in> components (UNIV - (B1 \<union> B2))" using hC12_set by simp
    have hC2_in: "C2 \<in> components (UNIV - (B1 \<union> B2))" using hC12_set by simp
    show ?thesis
      using components_nonoverlap[of C1 "UNIV - (B1 \<union> B2)" C2] hC1_in hC2_in hC12_ne
      by (by100 blast)
  qed
  have hD1'_eq: "D1' = C1"
  proof -
    have "D1' \<in> {C1, C2}" using hD1'_comp hC12_set by (by100 simp)
    moreover have "x1 \<notin> C2"
    proof
      assume "x1 \<in> C2"
      hence "x1 \<notin> C1" using hC1_C2_disj by (by100 blast)
      thus False using hx1_C1 by (by100 blast)
    qed
    ultimately show "D1' = C1" using hx1_in_D1' by (by100 blast)
  qed
  have hD2'_eq: "D2' = C2"
  proof -
    have "D2' \<in> {C1, C2}" using hD2'_comp hC12_set by (by100 simp)
    moreover have "x2 \<notin> C1"
    proof
      assume "x2 \<in> C1"
      hence "x2 \<notin> C2" using hC1_C2_disj by (by100 blast)
      thus False using hx2_C2 by (by100 blast)
    qed
    ultimately show "D2' = C2" using hx2_in_D2' by (by100 blast)
  qed
  have hD1_D2_disj: "D1 \<inter> D2 = {}"
  proof -
    have "D1 \<subseteq> C1" using hD1_sub_D1' hD1'_eq by (by100 simp)
    moreover have "D2 \<subseteq> C2" using hD2_sub_D2' hD2'_eq by (by100 simp)
    ultimately show ?thesis using hC1_C2_disj by (by100 blast)
  qed
  have hx1_in_D1: "x1 \<in> D1"
    unfolding D1_def using hx1_in connected_component_refl by simp
  have hD1_ne: "D1 \<noteq> {}" using hx1_in_D1 by blast
  have hD1_ne_D2: "D1 \<noteq> D2"
    using hD1_D2_disj hD1_ne by blast
  show "\<exists>D1 D2. D1 \<in> components (UNIV - M) \<and> D2 \<in> components (UNIV - M) \<and> D1 \<noteq> D2"
    using hD1_comp hD2_comp hD1_ne_D2 by blast
qed

text \<open>The \<theta>-graph M is bounded (union of 3 bounded arcs).\<close>

lemma theta_graph_bounded:
  fixes M B1 B2 B3 E :: "(real^2) set"
  assumes h\<theta>: "geotop_is_polyhedral_theta_graph M B1 B2 B3 E"
  shows "bounded M"
proof -
  have h_theta: "geotop_is_theta_graph M B1 B2 B3 E"
    using h\<theta> unfolding geotop_is_polyhedral_theta_graph_def by blast
  have hM_eq: "M = B1 \<union> B2 \<union> B3"
    using h_theta unfolding geotop_is_theta_graph_def by blast
  have hE1: "geotop_arc_endpoints B1 E"
   and hE2: "geotop_arc_endpoints B2 E"
   and hE3: "geotop_arc_endpoints B3 E"
    using h_theta unfolding geotop_is_theta_graph_def by blast+
  have hB1_bdd: "bounded B1" by (rule broken_line_bounded[OF hE1])
  have hB2_bdd: "bounded B2" by (rule broken_line_bounded[OF hE2])
  have hB3_bdd: "bounded B3" by (rule broken_line_bounded[OF hE3])
  show ?thesis using hM_eq hB1_bdd hB2_bdd hB3_bdd by simp
qed

text \<open>The polygon exterior is unbounded.\<close>

lemma polygon_exterior_unbounded:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "\<not> bounded (geotop_polygon_exterior J)"
proof -
  obtain P where hP_compl: "P \<in> UNIV - J"
            and hE_eq: "geotop_polygon_exterior J
                        = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    using geotop_polygon_exterior_is_component[OF hJ] by blast
  text \<open>The SOME predicate ensures the result is not \<open>geotop_bounded_R2\<close>.\<close>
  have h_dim: "(2::nat) \<le> DIM(real^2)" by simp
  have h_exists_unbd: "\<exists>c. c \<in> components (- J) \<and> \<not> bounded c"
    using geotop_1sphere_has_bounded_unbounded_components[OF hJ h_dim] by blast
  then obtain C where hC_comp: "C \<in> components (- J)" and hC_unbd: "\<not> bounded C"
    by blast
  obtain Q where hQ: "Q \<in> -J" and hC_eq_Q: "C = connected_component_set (- J) Q"
    using hC_comp unfolding components_def by blast
  have hC_sub: "C \<subseteq> UNIV - J"
    using hC_eq_Q connected_component_subset by (metis Compl_eq_Diff_UNIV)
  have hC_unbd_R2: "\<not> geotop_bounded_R2 C"
    using hC_unbd geotop_bounded_R2_iff_bounded by blast
  have hC_conn: "connected C" using hC_comp in_components_connected by blast
  have hC_topconn: "top1_connected_on C
                     (subspace_topology UNIV geotop_euclidean_topology C)"
    using hC_conn top1_connected_on_geotop_iff_connected by blast
  have hC_comp_at: "\<forall>R\<in>C. geotop_component_at UNIV geotop_euclidean_topology
                             ((UNIV::(real^2) set) - J) R = C"
  proof
    fix R assume hR_C: "R \<in> C"
    have "R \<in> -J" using hR_C hC_eq_Q connected_component_subset by blast
    have hC_eq_R: "C = connected_component_set (-J) R"
      using connected_component_eq hC_eq_Q hR_C by blast
    hence "connected_component_set (UNIV - J) R = C"
      using Compl_eq_Diff_UNIV by metis
    thus "geotop_component_at UNIV geotop_euclidean_topology
            ((UNIV::(real^2) set) - J) R = C"
      using geotop_component_at_UNIV_eq_connected_component_set by metis
  qed
  have hC_ne: "C \<noteq> {}" using hC_comp in_components_nonempty by blast
  have hpred_C: "C \<noteq> {} \<and> C \<subseteq> UNIV - J \<and> \<not> geotop_bounded_R2 C \<and>
                 top1_connected_on C (subspace_topology UNIV geotop_euclidean_topology C) \<and>
                 (\<forall>R\<in>C. geotop_component_at UNIV geotop_euclidean_topology
                            ((UNIV::(real^2) set) - J) R = C)"
    using hC_ne hC_sub hC_unbd_R2 hC_topconn hC_comp_at by blast
  have hpred_ex: "\<exists>E'. E' \<noteq> {} \<and> E' \<subseteq> UNIV - J \<and> \<not> geotop_bounded_R2 E' \<and>
                       top1_connected_on E' (subspace_topology UNIV geotop_euclidean_topology E') \<and>
                       (\<forall>R\<in>E'. geotop_component_at UNIV geotop_euclidean_topology
                                  ((UNIV::(real^2) set) - J) R = E')"
    using hpred_C by blast
  let ?E = "geotop_polygon_exterior J"
  have hE_pred: "?E \<noteq> {} \<and> ?E \<subseteq> UNIV - J \<and> \<not> geotop_bounded_R2 ?E \<and>
                 top1_connected_on ?E (subspace_topology UNIV geotop_euclidean_topology ?E) \<and>
                 (\<forall>R\<in>?E. geotop_component_at UNIV geotop_euclidean_topology
                            ((UNIV::(real^2) set) - J) R = ?E)"
    unfolding geotop_polygon_exterior_def
    by (rule someI_ex[OF hpred_ex])
  hence "\<not> geotop_bounded_R2 ?E" by blast
  thus ?thesis using geotop_bounded_R2_iff_bounded by blast
qed

text \<open>The polygon exterior is a HOL component of \<open>UNIV - J\<close>.\<close>

lemma polygon_exterior_is_HOL_component:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "geotop_polygon_exterior J \<in> components (UNIV - J)"
proof -
  obtain P where hP: "P \<in> UNIV - J"
            and hE_eq: "geotop_polygon_exterior J
                        = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    using geotop_polygon_exterior_is_component[OF hJ] by blast
  have h_bridge: "geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P
                  = connected_component_set (UNIV - J) P"
    by (rule geotop_component_at_UNIV_eq_connected_component_set)
  hence "geotop_polygon_exterior J = connected_component_set (UNIV - J) P"
    using hE_eq by simp
  thus ?thesis using hP componentsI by metis
qed

text \<open>A polygon (polyhedral 1-sphere) in \<open>real^2\<close> is bounded.\<close>

lemma polygon_bounded:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "bounded J"
proof -
  have h_n_sphere: "geotop_is_n_sphere J
        (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ unfolding geotop_is_polygon_def by blast
  have h_std_sphere_eq: "(geotop_std_sphere::(real^2) set) = sphere 0 1"
    unfolding geotop_std_sphere_def by (auto simp: norm_eq_sqrt_inner)
  obtain f where hf: "top1_homeomorphism_on J
        (subspace_topology UNIV geotop_euclidean_topology J)
        (geotop_std_sphere::(real^2) set)
        (subspace_topology UNIV geotop_euclidean_topology
           (geotop_std_sphere::(real^2) set)) f"
    using h_n_sphere unfolding geotop_is_n_sphere_def by blast
  have h_homeo_HOL: "J homeomorphic (geotop_std_sphere::(real^2) set)"
    using hf top1_homeomorphism_on_geotop_imp_HOL_homeomorphic by blast
  hence h_homeo_sph: "J homeomorphic sphere (0::real^2) 1"
    using h_std_sphere_eq by simp
  have h_compact_sph: "compact (sphere (0::real^2) 1)" by simp
  have h_compact_J: "compact J"
    using h_compact_sph h_homeo_sph homeomorphic_compactness by blast
  show ?thesis using h_compact_J compact_imp_bounded by blast
qed

text \<open>The polygon interior is a HOL component of \<open>UNIV - J\<close> (bridge from
  geotop-style component to HOL-Analysis form).\<close>

lemma polygon_interior_is_HOL_component:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "geotop_polygon_interior J \<in> components (UNIV - J)"
proof -
  obtain P where hP: "P \<in> UNIV - J"
            and hI_eq: "geotop_polygon_interior J
                        = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    using geotop_polygon_interior_is_bounded_component[OF hJ] by blast
  have h_bridge: "geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P
                  = connected_component_set (UNIV - J) P"
    by (rule geotop_component_at_UNIV_eq_connected_component_set)
  hence "geotop_polygon_interior J = connected_component_set (UNIV - J) P"
    using hI_eq by simp
  thus ?thesis using hP componentsI by metis
qed

text \<open>The polygon interior is bounded (extracts the bounded predicate from the
  SOME definition).\<close>

lemma polygon_interior_bounded:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "bounded (geotop_polygon_interior J)"
proof -
  have h_dim: "(2::nat) \<le> DIM(real^2)" by simp
  have h_exists_bd: "\<exists>c. c \<in> components (- J) \<and> bounded c"
    using geotop_1sphere_has_bounded_unbounded_components[OF hJ h_dim] by blast
  then obtain C where hC_comp: "C \<in> components (- J)" and hC_bd: "bounded C"
    by blast
  obtain Q where hQ: "Q \<in> -J" and hC_eq_Q: "C = connected_component_set (- J) Q"
    using hC_comp unfolding components_def by blast
  have hC_sub: "C \<subseteq> UNIV - J"
    using hC_eq_Q connected_component_subset by (metis Compl_eq_Diff_UNIV)
  have hC_bd_R2: "geotop_bounded_R2 C"
    using hC_bd geotop_bounded_R2_iff_bounded by blast
  have hC_conn: "connected C" using hC_comp in_components_connected by blast
  have hC_topconn: "top1_connected_on C
                     (subspace_topology UNIV geotop_euclidean_topology C)"
    using hC_conn top1_connected_on_geotop_iff_connected by blast
  have hC_comp_at: "\<forall>R\<in>C. geotop_component_at UNIV geotop_euclidean_topology
                             ((UNIV::(real^2) set) - J) R = C"
  proof
    fix R assume hR_C: "R \<in> C"
    have "R \<in> -J" using hR_C hC_eq_Q connected_component_subset by blast
    have hC_eq_R: "C = connected_component_set (-J) R"
      using connected_component_eq hC_eq_Q hR_C by blast
    hence "connected_component_set (UNIV - J) R = C"
      using Compl_eq_Diff_UNIV by metis
    thus "geotop_component_at UNIV geotop_euclidean_topology
            ((UNIV::(real^2) set) - J) R = C"
      using geotop_component_at_UNIV_eq_connected_component_set by metis
  qed
  have hC_ne: "C \<noteq> {}" using hC_comp in_components_nonempty by blast
  have hpred_C: "C \<noteq> {} \<and> C \<subseteq> UNIV - J \<and> geotop_bounded_R2 C \<and>
                 top1_connected_on C (subspace_topology UNIV geotop_euclidean_topology C) \<and>
                 (\<forall>R\<in>C. geotop_component_at UNIV geotop_euclidean_topology
                            ((UNIV::(real^2) set) - J) R = C)"
    using hC_ne hC_sub hC_bd_R2 hC_topconn hC_comp_at by blast
  have hpred_ex: "\<exists>I. I \<noteq> {} \<and> I \<subseteq> UNIV - J \<and> geotop_bounded_R2 I \<and>
                       top1_connected_on I (subspace_topology UNIV geotop_euclidean_topology I) \<and>
                       (\<forall>R\<in>I. geotop_component_at UNIV geotop_euclidean_topology
                                  ((UNIV::(real^2) set) - J) R = I)"
    using hpred_C by blast
  let ?I = "geotop_polygon_interior J"
  have hI_pred: "?I \<noteq> {} \<and> ?I \<subseteq> UNIV - J \<and> geotop_bounded_R2 ?I \<and>
                 top1_connected_on ?I (subspace_topology UNIV geotop_euclidean_topology ?I) \<and>
                 (\<forall>R\<in>?I. geotop_component_at UNIV geotop_euclidean_topology
                            ((UNIV::(real^2) set) - J) R = ?I)"
    unfolding geotop_polygon_interior_def
    by (rule someI_ex[OF hpred_ex])
  hence "geotop_bounded_R2 ?I" by blast
  thus ?thesis using geotop_bounded_R2_iff_bounded by blast
qed

text \<open>For a polygon J (with exactly 2 components), the polygon interior is
  the UNIQUE bounded component of \<open>UNIV - J\<close>.\<close>

lemma polygon_interior_unique:
  fixes J :: "(real^2) set"
  assumes hJ_poly: "geotop_is_polygon J"
  assumes hC: "C \<in> components (UNIV - J) \<and> bounded C"
  shows "C = geotop_polygon_interior J"
proof -
  have hJ_sph: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ_poly unfolding geotop_is_polygon_def by blast
  have h_card_2: "card (components (UNIV - J)) = 2"
    by (rule polygon_components_card[OF hJ_poly])
  have hI_in: "geotop_polygon_interior J \<in> components (UNIV - J)"
    by (rule polygon_interior_is_HOL_component[OF hJ_sph])
  have hE_in: "geotop_polygon_exterior J \<in> components (UNIV - J)"
    by (rule polygon_exterior_is_HOL_component[OF hJ_sph])
  have hI_bd: "bounded (geotop_polygon_interior J)"
    by (rule polygon_interior_bounded[OF hJ_sph])
  have hE_unbd: "\<not> bounded (geotop_polygon_exterior J)"
    by (rule polygon_exterior_unbounded[OF hJ_sph])
  have hIE_ne: "geotop_polygon_interior J \<noteq> geotop_polygon_exterior J"
  proof
    assume "geotop_polygon_interior J = geotop_polygon_exterior J"
    hence "bounded (geotop_polygon_exterior J)" using hI_bd by simp
    thus False using hE_unbd by simp
  qed
  have hIE_set: "{geotop_polygon_interior J, geotop_polygon_exterior J}
                  \<subseteq> components (UNIV - J)"
    using hI_in hE_in by simp
  have hIE_card: "card {geotop_polygon_interior J, geotop_polygon_exterior J} = 2"
    using hIE_ne by simp
  have h_finite_comps: "finite (components (UNIV - J))"
  proof (rule ccontr)
    assume "\<not> finite (components (UNIV - J))"
    hence "card (components (UNIV - J)) = 0" by simp
    thus False using h_card_2 by simp
  qed
  have hIE_eq: "{geotop_polygon_interior J, geotop_polygon_exterior J}
                  = components (UNIV - J)"
    using hIE_set hIE_card h_card_2 h_finite_comps card_subset_eq by metis
  text \<open>C is in components, so C is interior or exterior.\<close>
  have hC_comp: "C \<in> components (UNIV - J)" using hC by blast
  have hC_bd: "bounded C" using hC by blast
  have hC_in_set: "C \<in> {geotop_polygon_interior J, geotop_polygon_exterior J}"
    using hC_comp hIE_eq by simp
  have hC_ne_E: "C \<noteq> geotop_polygon_exterior J"
    using hC_bd hE_unbd by blast
  show "C = geotop_polygon_interior J"
    using hC_in_set hC_ne_E by blast
qed

text \<open>The polygon exterior is the UNIQUE unbounded component of \<open>UNIV - J\<close>.\<close>

lemma polygon_exterior_unique:
  fixes J :: "(real^2) set"
  assumes hJ_poly: "geotop_is_polygon J"
  assumes hC: "C \<in> components (UNIV - J) \<and> \<not> bounded C"
  shows "C = geotop_polygon_exterior J"
proof -
  have hJ_sph: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ_poly unfolding geotop_is_polygon_def by blast
  have hJ_bdd: "bounded J" by (rule polygon_bounded[OF hJ_poly])
  have hJ_compl_bdd: "bounded (- (UNIV - J))" using hJ_bdd by simp
  have hE_in: "geotop_polygon_exterior J \<in> components (UNIV - J)"
    by (rule polygon_exterior_is_HOL_component[OF hJ_sph])
  have hE_unbd: "\<not> bounded (geotop_polygon_exterior J)"
    by (rule polygon_exterior_unbounded[OF hJ_sph])
  have h_dim: "(2::nat) \<le> DIM(real^2)" by simp
  show ?thesis
    using cobounded_unique_unbounded_components
            [OF hJ_compl_bdd, of C "geotop_polygon_exterior J"]
          hC hE_in hE_unbd h_dim by blast
qed

text \<open>The closure of the polygon interior is the interior plus the polygon
  itself.\<close>

lemma polygon_interior_closure_eq:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "closure (geotop_polygon_interior J) = geotop_polygon_interior J \<union> J"
proof -
  have hI_front: "geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_interior J) = J"
    using Theorem_GT_2_6(1)[OF hJ] by simp
  have hI_front_HOL: "frontier (geotop_polygon_interior J) = J"
    using hI_front geotop_frontier_UNIV_eq_frontier by metis
  show ?thesis using hI_front_HOL closure_Un_frontier by metis
qed

text \<open>Similarly for the polygon exterior.\<close>

lemma polygon_exterior_closure_eq:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  shows "closure (geotop_polygon_exterior J) = geotop_polygon_exterior J \<union> J"
proof -
  have hE_front: "geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_exterior J) = J"
    using Theorem_GT_2_6(2)[OF hJ] by simp
  have hE_front_HOL: "frontier (geotop_polygon_exterior J) = J"
    using hE_front geotop_frontier_UNIV_eq_frontier by metis
  show ?thesis using hE_front_HOL closure_Un_frontier by metis
qed

text \<open>Two polygons with the same interior are equal (since the polygon is the
  frontier of its interior, by GT_2_6).\<close>

lemma polygon_interior_injective:
  fixes J1 J2 :: "(real^2) set"
  assumes hJ1: "geotop_is_polygon J1"
      and hJ2: "geotop_is_polygon J2"
      and heq: "geotop_polygon_interior J1 = geotop_polygon_interior J2"
  shows "J1 = J2"
proof -
  have h1: "J1 = geotop_frontier UNIV geotop_euclidean_topology
                  (geotop_polygon_interior J1)"
    using Theorem_GT_2_6(1)[OF hJ1] by (by100 simp)
  have h2: "J2 = geotop_frontier UNIV geotop_euclidean_topology
                  (geotop_polygon_interior J2)"
    using Theorem_GT_2_6(1)[OF hJ2] by (by100 simp)
  show ?thesis using h1 h2 heq by (by100 simp)
qed

text \<open>The polygon interior is disjoint from the polygon itself.\<close>

lemma polygon_interior_disjoint_polygon:
  fixes J :: "(real^2) set"
  assumes hJ_poly: "geotop_is_polygon J"
  shows "geotop_polygon_interior J \<inter> J = {}"
proof -
  have hJ_sph: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ_poly unfolding geotop_is_polygon_def by blast
  have hI_in: "geotop_polygon_interior J \<in> components (UNIV - J)"
    by (rule polygon_interior_is_HOL_component[OF hJ_sph])
  have hI_sub: "geotop_polygon_interior J \<subseteq> UNIV - J"
    using hI_in in_components_subset by blast
  thus ?thesis by blast
qed

text \<open>The polygon exterior is disjoint from the polygon itself.\<close>

lemma polygon_exterior_disjoint_polygon:
  fixes J :: "(real^2) set"
  assumes hJ_poly: "geotop_is_polygon J"
  shows "geotop_polygon_exterior J \<inter> J = {}"
proof -
  have hJ_sph: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ_poly unfolding geotop_is_polygon_def by blast
  have hE_in: "geotop_polygon_exterior J \<in> components (UNIV - J)"
    by (rule polygon_exterior_is_HOL_component[OF hJ_sph])
  have hE_sub: "geotop_polygon_exterior J \<subseteq> UNIV - J"
    using hE_in in_components_subset by blast
  thus ?thesis by blast
qed

text \<open>The polygon interior and exterior are disjoint from each other.\<close>

lemma polygon_interior_exterior_disjoint:
  fixes J :: "(real^2) set"
  assumes hJ_poly: "geotop_is_polygon J"
  shows "geotop_polygon_interior J \<inter> geotop_polygon_exterior J = {}"
proof -
  have hJ_sph: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ_poly unfolding geotop_is_polygon_def by blast
  have hI_in: "geotop_polygon_interior J \<in> components (UNIV - J)"
    by (rule polygon_interior_is_HOL_component[OF hJ_sph])
  have hE_in: "geotop_polygon_exterior J \<in> components (UNIV - J)"
    by (rule polygon_exterior_is_HOL_component[OF hJ_sph])
  have hI_bd: "bounded (geotop_polygon_interior J)"
    by (rule polygon_interior_bounded[OF hJ_sph])
  have hE_unbd: "\<not> bounded (geotop_polygon_exterior J)"
    by (rule polygon_exterior_unbounded[OF hJ_sph])
  have hIE_ne: "geotop_polygon_interior J \<noteq> geotop_polygon_exterior J"
  proof
    assume "geotop_polygon_interior J = geotop_polygon_exterior J"
    hence "bounded (geotop_polygon_exterior J)" using hI_bd by simp
    thus False using hE_unbd by simp
  qed
  show ?thesis using hI_in hE_in hIE_ne
    using components_nonoverlap by blast
qed

text \<open>For two arcs sharing only endpoints, their intersection is exactly the
  endpoint set E.\<close>

lemma pair_of_arcs_intersection:
  fixes B1 B2 :: "(real^2) set" and E :: "(real^2) set"
  assumes hE1: "geotop_arc_endpoints B1 E"
      and hE2: "geotop_arc_endpoints B2 E"
      and h_disj: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = {}"
  shows "B1 \<inter> B2 = E"
proof
  show "B1 \<inter> B2 \<subseteq> E"
  proof
    fix x assume hx: "x \<in> B1 \<inter> B2"
    show "x \<in> E"
    proof (rule ccontr)
      assume "x \<notin> E"
      hence "x \<in> geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E"
        unfolding geotop_arc_interior_def using hx by blast
      thus False using h_disj by blast
    qed
  qed
  show "E \<subseteq> B1 \<inter> B2"
  proof -
    have "E \<subseteq> B1" using hE1 unfolding geotop_arc_endpoints_def by blast
    moreover have "E \<subseteq> B2" using hE2 unfolding geotop_arc_endpoints_def by blast
    ultimately show ?thesis by blast
  qed
qed

lemma geotop_theta_graph_R2_to_S2_three_components:
  fixes M B1 B2 B3 E :: "(real^2) set"
  assumes htheta: "geotop_is_theta_graph M B1 B2 B3 E"
  shows "\<exists>U V W. U \<noteq> {} \<and> V \<noteq> {} \<and> W \<noteq> {}
      \<and> U \<inter> V = {} \<and> V \<inter> W = {} \<and> U \<inter> W = {}
      \<and> U \<union> V \<union> W = top1_S2 - (R2_to_S2 ` B1 \<union> R2_to_S2 ` B2 \<union> R2_to_S2 ` B3)
      \<and> top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U)
      \<and> top1_connected_on V (subspace_topology top1_S2 top1_S2_topology V)
      \<and> top1_connected_on W (subspace_topology top1_S2 top1_S2_topology W)
      \<and> U \<in> top1_S2_topology \<and> V \<in> top1_S2_topology \<and> W \<in> top1_S2_topology"
proof -
  have hE1: "geotop_arc_endpoints B1 E"
    and hE2: "geotop_arc_endpoints B2 E"
    and hE3: "geotop_arc_endpoints B3 E"
    using htheta unfolding geotop_is_theta_graph_def by (by100 blast)+
  have hI12: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = {}"
    and hI13: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B3 E = {}"
    and hI23: "geotop_arc_interior B2 E \<inter> geotop_arc_interior B3 E = {}"
    using htheta unfolding geotop_is_theta_graph_def by (by100 blast)+
  have hE_card: "card E = 2"
    using hE1 unfolding geotop_arc_endpoints_def by (by100 blast)
  obtain a b where hab: "a \<noteq> b" and hE_eq: "E = {a, b}"
    using hE_card card_2_iff by (by100 metis)
  have himg_ne: "R2_to_S2 a \<noteq> R2_to_S2 b"
    using R2_to_S2_inj_on_UNIV hab unfolding inj_on_def by (by100 blast)
  have hA1: "top1_is_arc_on (R2_to_S2 ` B1)
      (subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` B1))"
    by (rule R2_to_S2_geotop_arc_top1_arc[OF hE1 hE_eq hab])
  have hA2: "top1_is_arc_on (R2_to_S2 ` B2)
      (subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` B2))"
    by (rule R2_to_S2_geotop_arc_top1_arc[OF hE2 hE_eq hab])
  have hA3: "top1_is_arc_on (R2_to_S2 ` B3)
      (subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` B3))"
    by (rule R2_to_S2_geotop_arc_top1_arc[OF hE3 hE_eq hab])
  have hEP1: "top1_arc_endpoints_on (R2_to_S2 ` B1)
      (subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` B1))
       = {R2_to_S2 a, R2_to_S2 b}"
    by (rule R2_to_S2_geotop_arc_top1_arc_endpoints[OF hE1 hE_eq hab])
  have hEP2: "top1_arc_endpoints_on (R2_to_S2 ` B2)
      (subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` B2))
       = {R2_to_S2 a, R2_to_S2 b}"
    by (rule R2_to_S2_geotop_arc_top1_arc_endpoints[OF hE2 hE_eq hab])
  have hEP3: "top1_arc_endpoints_on (R2_to_S2 ` B3)
      (subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` B3))
       = {R2_to_S2 a, R2_to_S2 b}"
    by (rule R2_to_S2_geotop_arc_top1_arc_endpoints[OF hE3 hE_eq hab])
  have hsub1: "R2_to_S2 ` B1 \<subseteq> top1_S2"
    using R2_to_S2_image_subset_S2_minus_north[of B1] by (by100 blast)
  have hsub2: "R2_to_S2 ` B2 \<subseteq> top1_S2"
    using R2_to_S2_image_subset_S2_minus_north[of B2] by (by100 blast)
  have hsub3: "R2_to_S2 ` B3 \<subseteq> top1_S2"
    using R2_to_S2_image_subset_S2_minus_north[of B3] by (by100 blast)
  have hB12: "B1 \<inter> B2 = E"
    by (rule pair_of_arcs_intersection[OF hE1 hE2 hI12])
  have hB23: "B2 \<inter> B3 = E"
    by (rule pair_of_arcs_intersection[OF hE2 hE3 hI23])
  have hB13: "B1 \<inter> B3 = E"
    by (rule pair_of_arcs_intersection[OF hE1 hE3 hI13])
  have hImg12: "R2_to_S2 ` B1 \<inter> R2_to_S2 ` B2 = {R2_to_S2 a, R2_to_S2 b}"
    using R2_to_S2_image_Int[of B1 B2] hB12 hE_eq by (by100 simp)
  have hImg23: "R2_to_S2 ` B2 \<inter> R2_to_S2 ` B3 = {R2_to_S2 a, R2_to_S2 b}"
    using R2_to_S2_image_Int[of B2 B3] hB23 hE_eq by (by100 simp)
  have hImg13: "R2_to_S2 ` B1 \<inter> R2_to_S2 ` B3 = {R2_to_S2 a, R2_to_S2 b}"
    using R2_to_S2_image_Int[of B1 B3] hB13 hE_eq by (by100 simp)
  show ?thesis
    by (rule Lemma_64_1_theta_space_three_components[
        OF top1_S2_is_topology_on_strict hsub1 hsub2 hsub3
           hA1 hA2 hA3 himg_ne hImg12 hImg23 hImg13 hEP1 hEP2 hEP3])
qed

lemma geotop_polyhedral_theta_graph_R2_to_S2_three_components:
  fixes M B1 B2 B3 E :: "(real^2) set"
  assumes htheta: "geotop_is_polyhedral_theta_graph M B1 B2 B3 E"
  shows "\<exists>U V W. U \<noteq> {} \<and> V \<noteq> {} \<and> W \<noteq> {}
      \<and> U \<inter> V = {} \<and> V \<inter> W = {} \<and> U \<inter> W = {}
      \<and> U \<union> V \<union> W = top1_S2 - (R2_to_S2 ` B1 \<union> R2_to_S2 ` B2 \<union> R2_to_S2 ` B3)
      \<and> top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U)
      \<and> top1_connected_on V (subspace_topology top1_S2 top1_S2_topology V)
      \<and> top1_connected_on W (subspace_topology top1_S2 top1_S2_topology W)
      \<and> U \<in> top1_S2_topology \<and> V \<in> top1_S2_topology \<and> W \<in> top1_S2_topology"
proof -
  have "geotop_is_theta_graph M B1 B2 B3 E"
    by (rule polyhedral_theta_graph_imp_theta[OF htheta])
  thus ?thesis
    by (rule geotop_theta_graph_R2_to_S2_three_components)
qed

text \<open>Book-proof boundary helper on \<open>S\<^sup>2\<close>: for a simple closed curve,
  each complementary side has the curve in its closure.\<close>

lemma S2_simple_closed_curve_component_closure_eq:
  fixes SCC Q R :: "(real * real * real) set"
  assumes hSCC: "top1_simple_closed_curve_on top1_S2 top1_S2_topology SCC"
      and hQop: "Q \<in> top1_S2_topology"
      and hRop: "R \<in> top1_S2_topology"
      and hQne: "Q \<noteq> {}"
      and hRne: "R \<noteq> {}"
      and hQR: "Q \<inter> R = {}"
      and hQR_un: "Q \<union> R = top1_S2 - SCC"
      and hQc: "top1_connected_on Q (subspace_topology top1_S2 top1_S2_topology Q)"
      and hRc: "top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R)"
  shows "closure_on top1_S2 top1_S2_topology Q = Q \<union> SCC"
proof -
  have hS2: "is_topology_on_strict top1_S2 top1_S2_topology"
    by (rule top1_S2_is_topology_on_strict)
  \<comment> \<open>(\<supseteq>): \<open>Q\<close> is contained in its closure, and every point of
    the simple closed curve is a boundary point of the side \<open>Q\<close>.\<close>
  have hQ_sub_cl: "Q \<subseteq> closure_on top1_S2 top1_S2_topology Q"
    by (rule subset_closure_on)
  have hSCC_sub_cl: "SCC \<subseteq> closure_on top1_S2 top1_S2_topology Q"
  proof
    fix x assume hx: "x \<in> SCC"
    show "x \<in> closure_on top1_S2 top1_S2_topology Q"
      unfolding closure_on_def
    proof (rule InterI, clarsimp)
      fix C assume hCcl: "closedin_on top1_S2 top1_S2_topology C" and hQC: "Q \<subseteq> C"
      show "x \<in> C"
      proof (rule ccontr)
        assume "x \<notin> C"
        have hV: "top1_S2 - C \<in> top1_S2_topology"
          using hCcl unfolding closedin_on_def by (by100 blast)
        have hxV: "x \<in> top1_S2 - C"
          using \<open>x \<notin> C\<close> hx hSCC
          unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
          by (by100 blast)
        from simple_closed_curve_boundary_meets_component[
            OF hS2 hSCC hQc hRc hQR hQR_un hQne hRne hQop hRop hx hV hxV]
        have "(top1_S2 - C) \<inter> Q \<noteq> {}" .
        thus False using hQC by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>(\<subseteq>): \<open>Q \<union> SCC\<close> is closed because its complement in \<open>S\<^sup>2\<close> is
    the other open component \<open>R\<close>.\<close>
  have hQSCC_closed: "closedin_on top1_S2 top1_S2_topology (Q \<union> SCC)"
  proof -
    have "top1_S2 - (Q \<union> SCC) = R"
    proof -
      have "Q \<union> SCC \<union> R = top1_S2"
        using hQR_un hSCC
        unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
        by (by100 blast)
      thus ?thesis using hQR hQR_un by (by100 blast)
    qed
    moreover have "Q \<union> SCC \<subseteq> top1_S2"
    proof -
      have "Q \<subseteq> top1_S2"
        by (rule is_topology_on_strict_opens_sub[OF hS2 hQop])
      moreover have "SCC \<subseteq> top1_S2"
        using hSCC unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
        by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    ultimately show ?thesis unfolding closedin_on_def using hRop by (by100 blast)
  qed
  have hQ_sub_QSCC: "Q \<subseteq> Q \<union> SCC" by (by100 blast)
  have hcl_sub: "closure_on top1_S2 top1_S2_topology Q \<subseteq> Q \<union> SCC"
    unfolding closure_on_def using hQSCC_closed hQ_sub_QSCC by (by100 blast)
  show ?thesis
    using hQ_sub_cl hSCC_sub_cl hcl_sub by (by100 blast)
qed

lemma S2_simple_closed_curve_component_frontier_eq:
  fixes SCC Q R :: "(real * real * real) set"
  assumes hSCC: "top1_simple_closed_curve_on top1_S2 top1_S2_topology SCC"
      and hQop: "Q \<in> top1_S2_topology"
      and hRop: "R \<in> top1_S2_topology"
      and hQne: "Q \<noteq> {}"
      and hRne: "R \<noteq> {}"
      and hQR: "Q \<inter> R = {}"
      and hQR_un: "Q \<union> R = top1_S2 - SCC"
      and hQc: "top1_connected_on Q (subspace_topology top1_S2 top1_S2_topology Q)"
      and hRc: "top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R)"
  shows "geotop_frontier top1_S2 top1_S2_topology Q = SCC"
proof -
  have hS2: "is_topology_on_strict top1_S2 top1_S2_topology"
    by (rule top1_S2_is_topology_on_strict)
  have hTop: "is_topology_on top1_S2 top1_S2_topology"
    using hS2 unfolding is_topology_on_strict_def by (by100 blast)
  have hQ_sub: "Q \<subseteq> top1_S2"
    by (rule is_topology_on_strict_opens_sub[OF hS2 hQop])
  have hQ_cl: "closure_on top1_S2 top1_S2_topology Q = Q \<union> SCC"
    by (rule S2_simple_closed_curve_component_closure_eq[
        OF hSCC hQop hRop hQne hRne hQR hQR_un hQc hRc])
  have hQ_disj_SCC: "Q \<inter> SCC = {}"
    using hQR_un by (by100 blast)
  have hfront: "geotop_frontier top1_S2 top1_S2_topology Q =
        closure_on top1_S2 top1_S2_topology Q - Q"
    by (rule Theorem_GT_2_4[OF hTop hQop hQ_sub])
  show ?thesis
    using hfront hQ_cl hQ_disj_SCC by (by100 blast)
qed

lemma S2_simple_closed_curve_component_frontiers_eq:
  fixes SCC Q R :: "(real * real * real) set"
  assumes hSCC: "top1_simple_closed_curve_on top1_S2 top1_S2_topology SCC"
      and hQop: "Q \<in> top1_S2_topology"
      and hRop: "R \<in> top1_S2_topology"
      and hQne: "Q \<noteq> {}"
      and hRne: "R \<noteq> {}"
      and hQR: "Q \<inter> R = {}"
      and hQR_un: "Q \<union> R = top1_S2 - SCC"
      and hQc: "top1_connected_on Q (subspace_topology top1_S2 top1_S2_topology Q)"
      and hRc: "top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R)"
  shows "geotop_frontier top1_S2 top1_S2_topology Q = SCC"
    and "geotop_frontier top1_S2 top1_S2_topology R = SCC"
proof -
  show "geotop_frontier top1_S2 top1_S2_topology Q = SCC"
    by (rule S2_simple_closed_curve_component_frontier_eq[
        OF hSCC hQop hRop hQne hRne hQR hQR_un hQc hRc])
  have hRQ: "R \<inter> Q = {}"
    using hQR by (by100 blast)
  have hRQ_un: "R \<union> Q = top1_S2 - SCC"
    using hQR_un by (by100 blast)
  show "geotop_frontier top1_S2 top1_S2_topology R = SCC"
    by (rule S2_simple_closed_curve_component_frontier_eq[
        OF hSCC hRop hQop hRne hQne hRQ hRQ_un hRc hQc])
qed

lemma S2_two_arcs_frontier_components:
  fixes A B :: "(real * real * real) set"
  assumes hA_sub: "A \<subseteq> top1_S2"
      and hB_sub: "B \<subseteq> top1_S2"
      and hA_arc: "top1_is_arc_on A (subspace_topology top1_S2 top1_S2_topology A)"
      and hB_arc: "top1_is_arc_on B (subspace_topology top1_S2 top1_S2_topology B)"
      and hAB: "A \<inter> B = {a, b}"
      and hab: "a \<noteq> b"
      and hA_ep: "top1_arc_endpoints_on A (subspace_topology top1_S2 top1_S2_topology A) = {a, b}"
      and hB_ep: "top1_arc_endpoints_on B (subspace_topology top1_S2 top1_S2_topology B) = {a, b}"
  shows "\<exists>Q R. Q \<noteq> {} \<and> R \<noteq> {} \<and> Q \<inter> R = {}
      \<and> Q \<union> R = top1_S2 - (A \<union> B)
      \<and> top1_connected_on Q (subspace_topology top1_S2 top1_S2_topology Q)
      \<and> top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R)
      \<and> Q \<in> top1_S2_topology \<and> R \<in> top1_S2_topology
      \<and> geotop_frontier top1_S2 top1_S2_topology Q = A \<union> B
      \<and> geotop_frontier top1_S2 top1_S2_topology R = A \<union> B"
proof -
  have hS2: "is_topology_on_strict top1_S2 top1_S2_topology"
    by (rule top1_S2_is_topology_on_strict)
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using hS2 unfolding is_topology_on_strict_def by (by100 blast)
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology"
    by (rule top1_S2_is_hausdorff)
  have hAB_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (A \<union> B)"
    by (rule arcs_form_simple_closed_curve[
        OF hS2 hS2_haus hA_arc hA_sub hB_arc hB_sub hAB hab hA_ep hB_ep])
  have hA_closed: "closedin_on top1_S2 top1_S2_topology A"
    by (rule arc_in_S2_closed[OF hA_sub hA_arc])
  have hB_closed: "closedin_on top1_S2 top1_S2_topology B"
    by (rule arc_in_S2_closed[OF hB_sub hB_arc])
  have hAB_card: "card (A \<inter> B) = 2"
    using hAB hab by (by100 simp)
  obtain Q R where hQR: "Q \<noteq> {}" "R \<noteq> {}" "Q \<inter> R = {}"
      "Q \<union> R = top1_S2 - (A \<union> B)"
      "top1_connected_on Q (subspace_topology top1_S2 top1_S2_topology Q)"
      "top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R)"
    using Theorem_63_5_two_closed_connected[OF hS2 hA_closed hB_closed
        arc_connected[OF hA_arc] arc_connected[OF hB_arc] hAB_card
        Theorem_63_2_arc_no_separation[OF hS2 hA_sub hA_arc]
        Theorem_63_2_arc_no_separation[OF hS2 hB_sub hB_arc]]
    by (metis (no_types))
  have hAB_closed: "closedin_on top1_S2 top1_S2_topology (A \<union> B)"
    by (rule closedin_on_Un[OF hTopS2 hA_closed hB_closed])
  have hAB_open: "top1_S2 - (A \<union> B) \<in> top1_S2_topology"
    using hAB_closed unfolding closedin_on_def by (by100 blast)
  have hAB_not_conn: "\<not> top1_connected_on (top1_S2 - (A \<union> B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A \<union> B)))"
    using Theorem_61_3_JordanSeparation_S2[OF hS2 hAB_scc]
    unfolding top1_separates_on_def by (by100 simp)
  have hQR_open: "Q \<in> top1_S2_topology \<and> R \<in> top1_S2_topology"
    using S2_two_component_open[OF hAB_open _ hQR(1,2,3,4,5,6) hAB_not_conn]
    by (by100 blast)
  have hQ_open: "Q \<in> top1_S2_topology"
    using hQR_open by (by100 blast)
  have hR_open: "R \<in> top1_S2_topology"
    using hQR_open by (by100 blast)
  have hfronts: "geotop_frontier top1_S2 top1_S2_topology Q = A \<union> B"
      "geotop_frontier top1_S2 top1_S2_topology R = A \<union> B"
    by (rule S2_simple_closed_curve_component_frontiers_eq[
        OF hAB_scc hQ_open hR_open hQR(1,2,3,4,5,6)])+
  show ?thesis
    using hQR hQR_open hfronts by (by100 blast)
qed

lemma geotop_two_arcs_R2_to_S2_frontier_components:
  fixes B1 B2 E :: "(real^2) set"
  assumes hE1: "geotop_arc_endpoints B1 E"
      and hE2: "geotop_arc_endpoints B2 E"
      and h_disj: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = {}"
  shows "\<exists>Q R. Q \<noteq> {} \<and> R \<noteq> {} \<and> Q \<inter> R = {}
      \<and> Q \<union> R = top1_S2 - (R2_to_S2 ` B1 \<union> R2_to_S2 ` B2)
      \<and> top1_connected_on Q (subspace_topology top1_S2 top1_S2_topology Q)
      \<and> top1_connected_on R (subspace_topology top1_S2 top1_S2_topology R)
      \<and> Q \<in> top1_S2_topology \<and> R \<in> top1_S2_topology
      \<and> geotop_frontier top1_S2 top1_S2_topology Q = R2_to_S2 ` B1 \<union> R2_to_S2 ` B2
      \<and> geotop_frontier top1_S2 top1_S2_topology R = R2_to_S2 ` B1 \<union> R2_to_S2 ` B2"
proof -
  have hE_card: "card E = 2"
    using hE1 unfolding geotop_arc_endpoints_def by (by100 blast)
  obtain a b where hab: "a \<noteq> b" and hE_eq: "E = {a, b}"
    using hE_card card_2_iff by (by100 metis)
  have himg_ne: "R2_to_S2 a \<noteq> R2_to_S2 b"
    using R2_to_S2_inj_on_UNIV hab unfolding inj_on_def by (by100 blast)
  have hA1: "top1_is_arc_on (R2_to_S2 ` B1)
      (subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` B1))"
    by (rule R2_to_S2_geotop_arc_top1_arc[OF hE1 hE_eq hab])
  have hA2: "top1_is_arc_on (R2_to_S2 ` B2)
      (subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` B2))"
    by (rule R2_to_S2_geotop_arc_top1_arc[OF hE2 hE_eq hab])
  have hEP1: "top1_arc_endpoints_on (R2_to_S2 ` B1)
      (subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` B1))
       = {R2_to_S2 a, R2_to_S2 b}"
    by (rule R2_to_S2_geotop_arc_top1_arc_endpoints[OF hE1 hE_eq hab])
  have hEP2: "top1_arc_endpoints_on (R2_to_S2 ` B2)
      (subspace_topology top1_S2 top1_S2_topology (R2_to_S2 ` B2))
       = {R2_to_S2 a, R2_to_S2 b}"
    by (rule R2_to_S2_geotop_arc_top1_arc_endpoints[OF hE2 hE_eq hab])
  have hsub1: "R2_to_S2 ` B1 \<subseteq> top1_S2"
    using R2_to_S2_image_subset_S2_minus_north[of B1] by (by100 blast)
  have hsub2: "R2_to_S2 ` B2 \<subseteq> top1_S2"
    using R2_to_S2_image_subset_S2_minus_north[of B2] by (by100 blast)
  have hB12: "B1 \<inter> B2 = E"
    by (rule pair_of_arcs_intersection[OF hE1 hE2 h_disj])
  have hImg12:
    "R2_to_S2 ` B1 \<inter> R2_to_S2 ` B2 = {R2_to_S2 a, R2_to_S2 b}"
    using R2_to_S2_image_Int[of B1 B2] hB12 hE_eq by (by100 simp)
  show ?thesis
    by (rule S2_two_arcs_frontier_components[
        OF hsub1 hsub2 hA1 hA2 hImg12 himg_ne hEP1 hEP2])
qed

text \<open>For two arcs sharing only endpoints, the interior of one is disjoint
  from the other arc entirely (since the interior excludes E).\<close>

lemma arc_interior_disjoint_other_arc:
  fixes B1 B2 :: "(real^2) set" and E :: "(real^2) set"
  assumes hE1: "geotop_arc_endpoints B1 E"
      and hE2: "geotop_arc_endpoints B2 E"
      and h_disj: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = {}"
  shows "geotop_arc_interior B1 E \<inter> B2 = {}"
proof -
  have h_inter: "B1 \<inter> B2 = E"
    by (rule pair_of_arcs_intersection[OF hE1 hE2 h_disj])
  have hI1_sub_B1: "geotop_arc_interior B1 E \<subseteq> B1"
    unfolding geotop_arc_interior_def by blast
  have hI1_disj_E: "geotop_arc_interior B1 E \<inter> E = {}"
    unfolding geotop_arc_interior_def by blast
  have "geotop_arc_interior B1 E \<inter> B2
        = geotop_arc_interior B1 E \<inter> B1 \<inter> B2"
    using hI1_sub_B1 by blast
  also have "\<dots> = geotop_arc_interior B1 E \<inter> E"
    using h_inter by blast
  also have "\<dots> = {}" using hI1_disj_E .
  finally show ?thesis .
qed

text \<open>The components of the polygon's complement are exactly the polygon
  interior and polygon exterior.\<close>

lemma polygon_components_eq:
  fixes J :: "(real^2) set"
  assumes hJ_poly: "geotop_is_polygon J"
  shows "components (UNIV - J) = {geotop_polygon_interior J, geotop_polygon_exterior J}"
proof -
  have hJ_sph: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ_poly unfolding geotop_is_polygon_def by blast
  have h_card_2: "card (components (UNIV - J)) = 2"
    by (rule polygon_components_card[OF hJ_poly])
  have hI_in: "geotop_polygon_interior J \<in> components (UNIV - J)"
    by (rule polygon_interior_is_HOL_component[OF hJ_sph])
  have hE_in: "geotop_polygon_exterior J \<in> components (UNIV - J)"
    by (rule polygon_exterior_is_HOL_component[OF hJ_sph])
  have hI_bd: "bounded (geotop_polygon_interior J)"
    by (rule polygon_interior_bounded[OF hJ_sph])
  have hE_unbd: "\<not> bounded (geotop_polygon_exterior J)"
    by (rule polygon_exterior_unbounded[OF hJ_sph])
  have hIE_ne: "geotop_polygon_interior J \<noteq> geotop_polygon_exterior J"
  proof
    assume "geotop_polygon_interior J = geotop_polygon_exterior J"
    hence "bounded (geotop_polygon_exterior J)" using hI_bd by simp
    thus False using hE_unbd by simp
  qed
  have hIE_set: "{geotop_polygon_interior J, geotop_polygon_exterior J}
                  \<subseteq> components (UNIV - J)"
    using hI_in hE_in by simp
  have hIE_card: "card {geotop_polygon_interior J, geotop_polygon_exterior J} = 2"
    using hIE_ne by simp
  have h_finite_comps: "finite (components (UNIV - J))"
  proof (rule ccontr)
    assume "\<not> finite (components (UNIV - J))"
    hence "card (components (UNIV - J)) = 0" by simp
    thus False using h_card_2 by simp
  qed
  show ?thesis
    using hIE_set hIE_card h_card_2 h_finite_comps card_subset_eq
    by metis
qed

text \<open>The decomposition of a θ-graph M into 3 arc interiors + the endpoint set.\<close>

lemma theta_graph_M_decomposition:
  fixes M B1 B2 B3 E :: "(real^2) set"
  assumes h\<theta>: "geotop_is_polyhedral_theta_graph M B1 B2 B3 E"
  shows "M = geotop_arc_interior B1 E \<union> geotop_arc_interior B2 E \<union> geotop_arc_interior B3 E \<union> E"
proof -
  have h_theta: "geotop_is_theta_graph M B1 B2 B3 E"
    using h\<theta> unfolding geotop_is_polyhedral_theta_graph_def by blast
  have hM_eq: "M = B1 \<union> B2 \<union> B3"
    using h_theta unfolding geotop_is_theta_graph_def by blast
  have hE1: "geotop_arc_endpoints B1 E"
   and hE2: "geotop_arc_endpoints B2 E"
   and hE3: "geotop_arc_endpoints B3 E"
    using h_theta unfolding geotop_is_theta_graph_def by blast+
  have hE_sub_B1: "E \<subseteq> B1" using hE1 unfolding geotop_arc_endpoints_def by blast
  have h_B1_decomp: "B1 = geotop_arc_interior B1 E \<union> E"
    unfolding geotop_arc_interior_def using hE_sub_B1 by blast
  have hE_sub_B2: "E \<subseteq> B2" using hE2 unfolding geotop_arc_endpoints_def by blast
  have h_B2_decomp: "B2 = geotop_arc_interior B2 E \<union> E"
    unfolding geotop_arc_interior_def using hE_sub_B2 by blast
  have hE_sub_B3: "E \<subseteq> B3" using hE3 unfolding geotop_arc_endpoints_def by blast
  have h_B3_decomp: "B3 = geotop_arc_interior B3 E \<union> E"
    unfolding geotop_arc_interior_def using hE_sub_B3 by blast
  show ?thesis using hM_eq h_B1_decomp h_B2_decomp h_B3_decomp by blast
qed

text \<open>For a polyhedral θ-graph, every pair of arcs forms a polygon.\<close>

lemma theta_graph_pair_is_polygon:
  fixes M B1 B2 B3 E :: "(real^2) set"
  assumes h\<theta>: "geotop_is_polyhedral_theta_graph M B1 B2 B3 E"
      and hi: "i \<in> {B1, B2, B3}" and hj: "j \<in> {B1, B2, B3}" and hij_ne: "i \<noteq> j"
  shows "geotop_is_polygon (i \<union> j)"
proof -
  have h_theta: "geotop_is_theta_graph M B1 B2 B3 E"
    using h\<theta> unfolding geotop_is_polyhedral_theta_graph_def by blast
  have hB1_bl: "geotop_is_broken_line B1"
   and hB2_bl: "geotop_is_broken_line B2"
   and hB3_bl: "geotop_is_broken_line B3"
    using h\<theta> unfolding geotop_is_polyhedral_theta_graph_def by blast+
  have hE1: "geotop_arc_endpoints B1 E"
   and hE2: "geotop_arc_endpoints B2 E"
   and hE3: "geotop_arc_endpoints B3 E"
    using h_theta unfolding geotop_is_theta_graph_def by blast+
  have h_int12: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = {}"
   and h_int13: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B3 E = {}"
   and h_int23: "geotop_arc_interior B2 E \<inter> geotop_arc_interior B3 E = {}"
    using h_theta unfolding geotop_is_theta_graph_def by blast+
  have h_poly_12: "geotop_is_polygon (B1 \<union> B2)"
    by (rule pair_of_arcs_is_polygon[OF hB1_bl hB2_bl hE1 hE2 h_int12])
  have h_poly_13: "geotop_is_polygon (B1 \<union> B3)"
    by (rule pair_of_arcs_is_polygon[OF hB1_bl hB3_bl hE1 hE3 h_int13])
  have h_poly_23: "geotop_is_polygon (B2 \<union> B3)"
    by (rule pair_of_arcs_is_polygon[OF hB2_bl hB3_bl hE2 hE3 h_int23])
  have h_i: "i = B1 \<or> i = B2 \<or> i = B3" using hi by simp
  have h_j: "j = B1 \<or> j = B2 \<or> j = B3" using hj by simp
  show ?thesis
    using h_i h_j hij_ne h_poly_12 h_poly_13 h_poly_23
    by (elim disjE) (auto simp: Un_commute)
qed

text \<open>For three arcs sharing endpoints (θ-graph configuration), the interior
  of one arc is fully in either the polygon interior or polygon exterior of
  the other two arcs.\<close>

lemma theta_arc_in_one_side_of_pair_polygon:
  fixes Bi Bj Bk :: "(real^2) set" and E :: "(real^2) set"
  assumes hEi: "geotop_arc_endpoints Bi E"
      and hEj: "geotop_arc_endpoints Bj E"
      and hEk: "geotop_arc_endpoints Bk E"
      and hBj_bl: "geotop_is_broken_line Bj"
      and hBk_bl: "geotop_is_broken_line Bk"
      and h_disj_ij: "geotop_arc_interior Bi E \<inter> geotop_arc_interior Bj E = {}"
      and h_disj_ik: "geotop_arc_interior Bi E \<inter> geotop_arc_interior Bk E = {}"
      and h_disj_jk: "geotop_arc_interior Bj E \<inter> geotop_arc_interior Bk E = {}"
  shows "geotop_arc_interior Bi E \<subseteq> geotop_polygon_interior (Bj \<union> Bk)
       \<or> geotop_arc_interior Bi E \<subseteq> geotop_polygon_exterior (Bj \<union> Bk)"
proof -
  have h_poly_jk: "geotop_is_polygon (Bj \<union> Bk)"
    by (rule pair_of_arcs_is_polygon[OF hBj_bl hBk_bl hEj hEk h_disj_jk])
  have h_sph_jk: "geotop_is_n_sphere (Bj \<union> Bk)
        (subspace_topology UNIV geotop_euclidean_topology (Bj \<union> Bk)) 1"
    using h_poly_jk unfolding geotop_is_polygon_def by blast
  have hI_in: "geotop_polygon_interior (Bj \<union> Bk) \<in> components (UNIV - (Bj \<union> Bk))"
    by (rule polygon_interior_is_HOL_component[OF h_sph_jk])
  have hE_in: "geotop_polygon_exterior (Bj \<union> Bk) \<in> components (UNIV - (Bj \<union> Bk))"
    by (rule polygon_exterior_is_HOL_component[OF h_sph_jk])
  have h_card_2: "card (components (UNIV - (Bj \<union> Bk))) = 2"
    by (rule polygon_components_card[OF h_poly_jk])
  have h_Bi_disj_Bj: "geotop_arc_interior Bi E \<inter> Bj = {}"
    by (rule arc_interior_disjoint_other_arc[OF hEi hEj h_disj_ij])
  have h_Bi_disj_Bk: "geotop_arc_interior Bi E \<inter> Bk = {}"
    by (rule arc_interior_disjoint_other_arc[OF hEi hEk h_disj_ik])
  have h_Bi_sub_compl_jk: "geotop_arc_interior Bi E \<subseteq> UNIV - (Bj \<union> Bk)"
    using h_Bi_disj_Bj h_Bi_disj_Bk by blast
  have h_Bi_conn: "connected (geotop_arc_interior Bi E)"
    by (rule arc_interior_connected[OF hEi])
  show ?thesis
  proof (cases "geotop_arc_interior Bi E = {}")
    case True
    thus ?thesis by simp
  next
    case False
    obtain x where hx_int: "x \<in> geotop_arc_interior Bi E" using False by blast
    have hx_compl: "x \<in> UNIV - (Bj \<union> Bk)" using hx_int h_Bi_sub_compl_jk by blast
    define Cx where "Cx = connected_component_set (UNIV - (Bj \<union> Bk)) x"
    have hCx_in: "Cx \<in> components (UNIV - (Bj \<union> Bk))"
      unfolding Cx_def using hx_compl componentsI by metis
    have hBi_sub_Cx: "geotop_arc_interior Bi E \<subseteq> Cx"
      unfolding Cx_def
      using h_Bi_conn hx_int h_Bi_sub_compl_jk connected_component_maximal by blast
    have hI_bd: "bounded (geotop_polygon_interior (Bj \<union> Bk))"
      by (rule polygon_interior_bounded[OF h_sph_jk])
    have hE_unbd: "\<not> bounded (geotop_polygon_exterior (Bj \<union> Bk))"
      by (rule polygon_exterior_unbounded[OF h_sph_jk])
    have h_IE_ne: "geotop_polygon_interior (Bj \<union> Bk) \<noteq> geotop_polygon_exterior (Bj \<union> Bk)"
    proof
      assume "geotop_polygon_interior (Bj \<union> Bk) = geotop_polygon_exterior (Bj \<union> Bk)"
      hence "bounded (geotop_polygon_exterior (Bj \<union> Bk))" using hI_bd by simp
      thus False using hE_unbd by simp
    qed
    have h_IE_set: "{geotop_polygon_interior (Bj \<union> Bk), geotop_polygon_exterior (Bj \<union> Bk)}
                    \<subseteq> components (UNIV - (Bj \<union> Bk))"
      using hI_in hE_in by simp
    have h_IE_card: "card {geotop_polygon_interior (Bj \<union> Bk),
                            geotop_polygon_exterior (Bj \<union> Bk)} = 2"
      using h_IE_ne by simp
    have h_finite_comps: "finite (components (UNIV - (Bj \<union> Bk)))"
    proof (rule ccontr)
      assume "\<not> finite (components (UNIV - (Bj \<union> Bk)))"
      hence "card (components (UNIV - (Bj \<union> Bk))) = 0" by simp
      thus False using h_card_2 by simp
    qed
    have h_IE_eq: "{geotop_polygon_interior (Bj \<union> Bk),
                     geotop_polygon_exterior (Bj \<union> Bk)}
                    = components (UNIV - (Bj \<union> Bk))"
      using h_IE_set h_IE_card h_card_2 h_finite_comps card_subset_eq by metis
    have hCx_in_set: "Cx \<in> {geotop_polygon_interior (Bj \<union> Bk),
                              geotop_polygon_exterior (Bj \<union> Bk)}"
      using hCx_in h_IE_eq by simp
    show ?thesis
    proof (cases "Cx = geotop_polygon_interior (Bj \<union> Bk)")
      case True
      thus ?thesis using hBi_sub_Cx by simp
    next
      case False
      hence "Cx = geotop_polygon_exterior (Bj \<union> Bk)" using hCx_in_set by blast
      thus ?thesis using hBi_sub_Cx by simp
    qed
  qed
qed

text \<open>The polygon interior, plus any subset of the polygon (its frontier),
  remains connected. This is a useful structural lemma for arguments that
  glue parts of the polygon to its interior (e.g., GT_2_8 piece connectedness).\<close>

lemma polygon_interior_union_subset_connected:
  fixes J :: "(real^2) set" and S :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
      and hS_sub: "S \<subseteq> J"
  shows "connected (geotop_polygon_interior J \<union> S)"
proof -
  have hJ_sph: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
    using hJ unfolding geotop_is_polygon_def by blast
  have hI_in: "geotop_polygon_interior J \<in> components (UNIV - J)"
    by (rule polygon_interior_is_HOL_component[OF hJ_sph])
  have hI_conn: "connected (geotop_polygon_interior J)"
    using hI_in in_components_connected by blast
  have hI_front: "geotop_frontier UNIV geotop_euclidean_topology (geotop_polygon_interior J) = J"
    using Theorem_GT_2_6(1)[OF hJ] by simp
  have hI_front_HOL: "frontier (geotop_polygon_interior J) = J"
    using hI_front geotop_frontier_UNIV_eq_frontier by metis
  have hI_sub: "geotop_polygon_interior J \<subseteq> geotop_polygon_interior J \<union> S" by blast
  have h_cl_eq: "closure (geotop_polygon_interior J) = geotop_polygon_interior J \<union> J"
    using hI_front_HOL closure_Un_frontier by metis
  have hUnion_sub_cl: "geotop_polygon_interior J \<union> S \<subseteq> closure (geotop_polygon_interior J)"
    using h_cl_eq hS_sub by blast
  show ?thesis
    by (rule connected_intermediate_closure[OF hI_conn hI_sub hUnion_sub_cl])
qed

text \<open>For a θ-graph M, the unbounded component E_M of \<open>UNIV - M\<close> is
  contained in \<open>polygon_exterior(Bi \<union> Bj)\<close> for any pair \<open>i \<ne> j\<close>.\<close>

lemma theta_graph_unbounded_in_pair_exterior:
  fixes M B1 B2 B3 E :: "(real^2) set" and U :: "(real^2) set"
        and i j :: "(real^2) set"
  assumes h\<theta>: "geotop_is_polyhedral_theta_graph M B1 B2 B3 E"
      and hU_comp: "U \<in> components (UNIV - M)"
      and hU_unbd: "\<not> bounded U"
      and hi: "i \<in> {B1, B2, B3}" and hj: "j \<in> {B1, B2, B3}" and hij_ne: "i \<noteq> j"
  shows "U \<subseteq> geotop_polygon_exterior (i \<union> j)"
proof -
  have h_theta: "geotop_is_theta_graph M B1 B2 B3 E"
    using h\<theta> unfolding geotop_is_polyhedral_theta_graph_def by blast
  have hM_eq: "M = B1 \<union> B2 \<union> B3"
    using h_theta unfolding geotop_is_theta_graph_def by blast
  have hB1_bl: "geotop_is_broken_line B1"
   and hB2_bl: "geotop_is_broken_line B2"
   and hB3_bl: "geotop_is_broken_line B3"
    using h\<theta> unfolding geotop_is_polyhedral_theta_graph_def by blast+
  have hE1: "geotop_arc_endpoints B1 E"
   and hE2: "geotop_arc_endpoints B2 E"
   and hE3: "geotop_arc_endpoints B3 E"
    using h_theta unfolding geotop_is_theta_graph_def by blast+
  have h_int12: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B2 E = {}"
   and h_int13: "geotop_arc_interior B1 E \<inter> geotop_arc_interior B3 E = {}"
   and h_int23: "geotop_arc_interior B2 E \<inter> geotop_arc_interior B3 E = {}"
    using h_theta unfolding geotop_is_theta_graph_def by blast+
  text \<open>The pair \<open>i \<union> j\<close> is a polygon.\<close>
  have h_poly_ij: "geotop_is_polygon (i \<union> j)"
  proof -
    have h_i: "i = B1 \<or> i = B2 \<or> i = B3" using hi by simp
    have h_j: "j = B1 \<or> j = B2 \<or> j = B3" using hj by simp
    have h_poly_12: "geotop_is_polygon (B1 \<union> B2)"
      by (rule pair_of_arcs_is_polygon[OF hB1_bl hB2_bl hE1 hE2 h_int12])
    have h_poly_13: "geotop_is_polygon (B1 \<union> B3)"
      by (rule pair_of_arcs_is_polygon[OF hB1_bl hB3_bl hE1 hE3 h_int13])
    have h_poly_23: "geotop_is_polygon (B2 \<union> B3)"
      by (rule pair_of_arcs_is_polygon[OF hB2_bl hB3_bl hE2 hE3 h_int23])
    show ?thesis
      using h_i h_j hij_ne h_poly_12 h_poly_13 h_poly_23
      by (elim disjE) (auto simp: Un_commute)
  qed
  text \<open>U is contained in \<open>UNIV - (i \<union> j)\<close>.\<close>
  have hU_subM: "U \<subseteq> UNIV - M" using hU_comp in_components_subset by blast
  have h_ij_subM: "i \<union> j \<subseteq> M" using hi hj hM_eq by blast
  have hU_sub_compl_ij: "U \<subseteq> UNIV - (i \<union> j)" using hU_subM h_ij_subM by blast
  text \<open>U is connected, so contained in one component of \<open>UNIV - (i \<union> j)\<close>.\<close>
  have hU_conn: "connected U" using hU_comp in_components_connected by blast
  have hU_ne: "U \<noteq> {}" using hU_comp in_components_nonempty by blast
  obtain x where hxU: "x \<in> U" using hU_ne by blast
  have hx_compl_ij: "x \<in> UNIV - (i \<union> j)" using hxU hU_sub_compl_ij by blast
  define Cx where "Cx = connected_component_set (UNIV - (i \<union> j)) x"
  have hCx_in: "Cx \<in> components (UNIV - (i \<union> j))"
    unfolding Cx_def using hx_compl_ij componentsI by metis
  have hU_sub_Cx: "U \<subseteq> Cx"
    unfolding Cx_def
    using hU_conn hxU hU_sub_compl_ij connected_component_maximal by blast
  have hCx_unbd: "\<not> bounded Cx" using hU_sub_Cx hU_unbd bounded_subset by blast
  have hCx_eq: "Cx = geotop_polygon_exterior (i \<union> j)"
    using polygon_exterior_unique[OF h_poly_ij] hCx_in hCx_unbd by blast
  show ?thesis using hU_sub_Cx hCx_eq by simp
qed

lemma theta_graph_unbounded_and_exterior_arc_same_pair_component:
  fixes M B1 B2 B3 E :: "(real^2) set" and U k i j :: "(real^2) set"
  assumes h\<theta>: "geotop_is_polyhedral_theta_graph M B1 B2 B3 E"
      and hU_comp: "U \<in> components (UNIV - M)"
      and hU_unbd: "\<not> bounded U"
      and hi: "i \<in> {B1, B2, B3}" and hj: "j \<in> {B1, B2, B3}" and hij_ne: "i \<noteq> j"
      and hk_ext: "geotop_arc_interior k E \<subseteq> geotop_polygon_exterior (i \<union> j)"
  shows "\<exists>C \<in> components (UNIV - (i \<union> j)).
            U \<subseteq> C \<and> geotop_arc_interior k E \<subseteq> C"
proof -
  have hU_ext: "U \<subseteq> geotop_polygon_exterior (i \<union> j)"
    by (rule theta_graph_unbounded_in_pair_exterior
        [OF h\<theta> hU_comp hU_unbd hi hj hij_ne])
  have h_poly_ij: "geotop_is_polygon (i \<union> j)"
    by (rule theta_graph_pair_is_polygon[OF h\<theta> hi hj hij_ne])
  have h_sph_ij:
    "geotop_is_n_sphere (i \<union> j)
      (subspace_topology UNIV geotop_euclidean_topology (i \<union> j)) 1"
    using h_poly_ij unfolding geotop_is_polygon_def by blast
  have h_ext_comp:
    "geotop_polygon_exterior (i \<union> j) \<in> components (UNIV - (i \<union> j))"
    by (rule polygon_exterior_is_HOL_component[OF h_sph_ij])
  show ?thesis
    using h_ext_comp hU_ext hk_ext by blast
qed

text \<open>The complement of a polyhedral \<theta>-graph has both an unbounded
  component (since M is bounded) and at least one bounded component
  (since the complement is not connected, by ≥ 2 components).\<close>

lemma theta_graph_has_unbounded_component:
  fixes M B1 B2 B3 E :: "(real^2) set"
  assumes h\<theta>: "geotop_is_polyhedral_theta_graph M B1 B2 B3 E"
  shows "\<exists>U. U \<in> components (UNIV - M) \<and> \<not> bounded U"
proof -
  have h_bdd_M: "bounded M" by (rule theta_graph_bounded[OF h\<theta>])
  have h_bdd_compl_compl: "bounded (- (UNIV - M))"
    using h_bdd_M by simp
  show ?thesis
    using cobounded_unbounded_components[OF h_bdd_compl_compl] by simp
qed

lemma theta_graph_unique_unbounded_component:
  fixes M B1 B2 B3 E :: "(real^2) set"
  assumes h\<theta>: "geotop_is_polyhedral_theta_graph M B1 B2 B3 E"
  shows "\<exists>!U. U \<in> components (UNIV - M) \<and> \<not> bounded U"
proof -
  have h_bdd_M: "bounded M" by (rule theta_graph_bounded[OF h\<theta>])
  have h_bdd_compl_compl: "bounded (- (UNIV - M))"
    using h_bdd_M by simp
  obtain U where hU: "U \<in> components (UNIV - M)" and hU_unbdd: "\<not> bounded U"
    using theta_graph_has_unbounded_component[OF h\<theta>] by blast
  show ?thesis
  proof (rule ex1I[of _ U])
    show "U \<in> components (UNIV - M) \<and> \<not> bounded U" using hU hU_unbdd by blast
  next
    fix V assume hV: "V \<in> components (UNIV - M) \<and> \<not> bounded V"
    have h_DIM: "(2::nat) \<le> DIM(real^2)" by simp
    show "V = U"
      using cobounded_unique_unbounded_components
              [OF h_bdd_compl_compl, of V U] hV hU hU_unbdd h_DIM
      by blast
  qed
qed

lemma theta_graph_has_bounded_component:
  fixes M B1 B2 B3 E :: "(real^2) set"
  assumes h\<theta>: "geotop_is_polyhedral_theta_graph M B1 B2 B3 E"
  shows "\<exists>F. F \<in> components (UNIV - M) \<and> bounded F"
proof -
  have h_bdd_M: "bounded M" by (rule theta_graph_bounded[OF h\<theta>])
  have h_bdd_compl_compl: "bounded (- (UNIV - M))"
    using h_bdd_M by simp
  obtain D1 D2 where hD1: "D1 \<in> components (UNIV - M)"
                  and hD2: "D2 \<in> components (UNIV - M)" and hD12: "D1 \<noteq> D2"
    using theta_graph_complement_has_two_components[OF h\<theta>] by blast
  have h_not_conn: "\<not> connected (UNIV - M)"
  proof
    assume h_conn: "connected (UNIV - M)"
    have hD1_ne: "D1 \<noteq> {}" using hD1 in_components_nonempty by blast
    have hD1_eq: "D1 = UNIV - M"
      using h_conn hD1 hD1_ne
      by (metis components_iff in_components_subset
                connected_iff_eq_connected_component_set subset_antisym)
    have hD2_eq: "D2 = UNIV - M"
      using h_conn hD2 in_components_nonempty
      by (metis components_iff in_components_subset
                connected_iff_eq_connected_component_set subset_antisym)
    show False using hD12 hD1_eq hD2_eq by simp
  qed
  have h_DIM: "(2::nat) \<le> DIM(real^2)" by simp
  show ?thesis
    using cobounded_has_bounded_component[OF h_bdd_compl_compl h_not_conn h_DIM] by metis
qed

text \<open>The \<theta>-graph M is closed (union of 3 closed arcs).\<close>

lemma theta_graph_closed:
  fixes M B1 B2 B3 E :: "(real^2) set"
  assumes h\<theta>: "geotop_is_polyhedral_theta_graph M B1 B2 B3 E"
  shows "closed M"
proof -
  have h_theta: "geotop_is_theta_graph M B1 B2 B3 E"
    using h\<theta> unfolding geotop_is_polyhedral_theta_graph_def by blast
  have hM_eq: "M = B1 \<union> B2 \<union> B3"
    using h_theta unfolding geotop_is_theta_graph_def by blast
  have hE1: "geotop_arc_endpoints B1 E"
   and hE2: "geotop_arc_endpoints B2 E"
   and hE3: "geotop_arc_endpoints B3 E"
    using h_theta unfolding geotop_is_theta_graph_def by blast+
  have hcl_B1: "closed B1" by (rule broken_line_closed[OF hE1])
  have hcl_B2: "closed B2" by (rule broken_line_closed[OF hE2])
  have hcl_B3: "closed B3" by (rule broken_line_closed[OF hE3])
  have h_cl_B12: "closed (B1 \<union> B2)" using hcl_B1 hcl_B2 by (rule closed_Un)
  have h_cl_M: "closed (B1 \<union> B2 \<union> B3)" using h_cl_B12 hcl_B3 by (rule closed_Un)
  show ?thesis using hM_eq h_cl_M by simp
qed

text \<open>Book translation for the uniqueness paragraph in Theorem 2.7:
  if two different theta-arcs were both on the bounded side of the polygon
  formed by the other arc and the common third arc, then the second arc would
  be accessible from infinity through the exterior of the first polygon,
  contradicting its containment in the bounded interior.\<close>

lemma theta_two_middle_arcs_contradict:
  fixes A B C E :: "(real^2) set"
  assumes hA: "geotop_arc_endpoints A E"
      and hB: "geotop_arc_endpoints B E"
      and hC: "geotop_arc_endpoints C E"
      and hAB: "geotop_arc_interior A E \<inter> geotop_arc_interior B E = {}"
      and hAC: "geotop_arc_interior A E \<inter> geotop_arc_interior C E = {}"
      and hBC: "geotop_arc_interior B E \<inter> geotop_arc_interior C E = {}"
      and hBC_poly: "geotop_is_polygon (B \<union> C)"
      and hAC_poly: "geotop_is_polygon (A \<union> C)"
      and hA_mid: "geotop_arc_interior A E \<subseteq> geotop_polygon_interior (B \<union> C)"
      and hB_mid: "geotop_arc_interior B E \<subseteq> geotop_polygon_interior (A \<union> C)"
  shows False
proof -
  let ?EBC = "geotop_polygon_exterior (B \<union> C)"
  let ?EAC = "geotop_polygon_exterior (A \<union> C)"
  let ?IAC = "geotop_polygon_interior (A \<union> C)"
  have hEBC_sub_EAC: "?EBC \<subseteq> ?EAC"
  proof -
    have hBC_sph:
      "geotop_is_n_sphere (B \<union> C)
        (subspace_topology UNIV geotop_euclidean_topology (B \<union> C)) 1"
      using hBC_poly unfolding geotop_is_polygon_def by (by100 blast)
    have hEBC_comp: "?EBC \<in> components (UNIV - (B \<union> C))"
      by (rule polygon_exterior_is_HOL_component[OF hBC_sph])
    have hEBC_unbd: "\<not> bounded ?EBC"
      by (rule polygon_exterior_unbounded[OF hBC_sph])
    have hEBC_conn: "connected ?EBC"
      using hEBC_comp in_components_connected by (by100 blast)
    have hEBC_ne: "?EBC \<noteq> {}"
      using hEBC_comp in_components_nonempty by (by100 blast)
    have hEBC_sub_compl_BC: "?EBC \<subseteq> UNIV - (B \<union> C)"
      using hEBC_comp in_components_subset by (by100 blast)
    have hE_sub_C: "E \<subseteq> C"
      using hC unfolding geotop_arc_endpoints_def by (by100 blast)
    have hA_decomp: "A = geotop_arc_interior A E \<union> E"
    proof -
      have hE_sub_A: "E \<subseteq> A"
        using hA unfolding geotop_arc_endpoints_def by (by100 blast)
      show ?thesis
        unfolding geotop_arc_interior_def using hE_sub_A by (by100 blast)
    qed
    have hEBC_disj_intA: "?EBC \<inter> geotop_arc_interior A E = {}"
    proof -
      have h_disj:
        "geotop_polygon_interior (B \<union> C) \<inter> ?EBC = {}"
        by (rule polygon_interior_exterior_disjoint[OF hBC_poly])
      show ?thesis using hA_mid h_disj by (by100 blast)
    qed
    have hEBC_disj_E: "?EBC \<inter> E = {}"
      using hEBC_sub_compl_BC hE_sub_C by (by100 blast)
    have hEBC_disj_A: "?EBC \<inter> A = {}"
      using hA_decomp hEBC_disj_intA hEBC_disj_E by (by100 blast)
    have hEBC_sub_compl_AC: "?EBC \<subseteq> UNIV - (A \<union> C)"
      using hEBC_disj_A hEBC_sub_compl_BC by (by100 blast)
    obtain p where hp_EBC: "p \<in> ?EBC"
      using hEBC_ne by (by100 blast)
    define D where "D = connected_component_set (UNIV - (A \<union> C)) p"
    have hp_compl_AC: "p \<in> UNIV - (A \<union> C)"
      using hp_EBC hEBC_sub_compl_AC by (by100 blast)
    have hD_comp: "D \<in> components (UNIV - (A \<union> C))"
      unfolding D_def using hp_compl_AC componentsI by metis
    have hEBC_sub_D: "?EBC \<subseteq> D"
      unfolding D_def
      using connected_component_maximal[OF hp_EBC hEBC_conn hEBC_sub_compl_AC] .
    have hD_unbd: "\<not> bounded D"
      using hEBC_sub_D hEBC_unbd bounded_subset by (by100 blast)
    have hD_eq_EAC: "D = ?EAC"
      using polygon_exterior_unique[OF hAC_poly] hD_comp hD_unbd by (by100 blast)
    show ?thesis
      using hEBC_sub_D hD_eq_EAC by (by100 simp)
  qed
  obtain x where hx_intB: "x \<in> geotop_arc_interior B E"
    using arc_interior_nonempty[OF hB] by (by100 blast)
  have hx_BC: "x \<in> B \<union> C"
    using hx_intB unfolding geotop_arc_interior_def by (by100 blast)
  have hx_lim_EBC:
    "is_limit_point_of x ?EBC UNIV geotop_euclidean_topology"
    using Theorem_GT_2_5[OF hBC_poly] hx_BC by (by100 blast)
  have hx_cl_EBC: "x \<in> closure ?EBC"
  proof -
    have hx_islimpt: "x islimpt ?EBC"
      using hx_lim_EBC is_limit_point_of_UNIV_geotop_iff_islimpt by (by100 blast)
    have hx_islimpt_iff: "x islimpt ?EBC = (x \<in> closure (?EBC - {x}))"
      by (rule islimpt_in_closure)
    have hx_cl_minus: "x \<in> closure (?EBC - {x})"
      using hx_islimpt hx_islimpt_iff by (by100 simp)
    have h_cl_sub: "closure (?EBC - {x}) \<subseteq> closure ?EBC"
      using closure_mono[of "?EBC - {x}" ?EBC] by (by100 blast)
    show ?thesis
      using hx_cl_minus h_cl_sub by (by100 blast)
  qed
  have hx_cl_EAC: "x \<in> closure ?EAC"
    using hx_cl_EBC hEBC_sub_EAC closure_mono by (by100 blast)
  have hx_not_AC: "x \<notin> A \<union> C"
  proof
    assume hx_AC: "x \<in> A \<union> C"
    have hx_notE: "x \<notin> E"
      using hx_intB unfolding geotop_arc_interior_def by (by100 blast)
    have hx_not_C: "x \<notin> C"
    proof
      assume hxC: "x \<in> C"
      have h_disj: "geotop_arc_interior B E \<inter> C = {}"
        by (rule arc_interior_disjoint_other_arc[OF hB hC hBC])
      show False using hx_intB hxC h_disj by (by100 blast)
    qed
    have hx_not_A: "x \<notin> A"
    proof
      assume hxA: "x \<in> A"
      have hx_intA: "x \<in> geotop_arc_interior A E"
        using hxA hx_notE unfolding geotop_arc_interior_def by (by100 blast)
      show False using hx_intA hx_intB hAB by (by100 blast)
    qed
    show False using hx_AC hx_not_A hx_not_C by (by100 blast)
  qed
  have hx_EAC: "x \<in> ?EAC"
  proof -
    have h_cl: "closure ?EAC = ?EAC \<union> (A \<union> C)"
      by (rule polygon_exterior_closure_eq[OF hAC_poly])
    show ?thesis using hx_cl_EAC hx_not_AC h_cl by (by100 blast)
  qed
  have hx_IAC: "x \<in> ?IAC"
    using hx_intB hB_mid by (by100 blast)
  have hIAC_disj_EAC: "?IAC \<inter> ?EAC = {}"
    by (rule polygon_interior_exterior_disjoint[OF hAC_poly])
  show False
    using hx_IAC hx_EAC hIAC_disj_EAC by (by100 blast)
qed

lemma nondegenerate_segment_meets_ball:
  fixes P p :: "real^2"
  assumes hp_ne: "p \<noteq> P"
      and h\<delta>_pos: "\<delta> > 0"
  shows "\<exists>q. q \<in> (closed_segment P p - {P}) \<inter> ball P \<delta>"
proof -
  have hnorm_pos: "norm (p - P) > 0"
    using hp_ne by (by100 simp)
  define t where "t = min (1 / 2) (\<delta> / (2 * norm (p - P)))"
  have ht_pos: "t > 0"
    unfolding t_def using h\<delta>_pos hnorm_pos by (by100 simp)
  have ht_le1: "t \<le> 1"
  proof -
    have "t \<le> 1 / 2" unfolding t_def by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  have ht_nonneg: "0 \<le> t" using ht_pos by (by100 simp)
  have ht_norm_lt: "t * norm (p - P) < \<delta>"
  proof -
    have ht_le: "t \<le> \<delta> / (2 * norm (p - P))"
      unfolding t_def by (by100 simp)
    have hmul_le: "t * norm (p - P) \<le> \<delta> / 2"
    proof -
      have h1: "t * norm (p - P)
              \<le> (\<delta> / (2 * norm (p - P))) * norm (p - P)"
        by (rule mult_right_mono[OF ht_le norm_ge_zero])
      have h2: "(\<delta> / (2 * norm (p - P))) * norm (p - P) = \<delta> / 2"
        using hnorm_pos by (by100 simp)
      show ?thesis using h1 h2 by (by100 simp)
    qed
    have "\<delta> / 2 < \<delta>" using h\<delta>_pos by (by100 simp)
    show ?thesis using hmul_le \<open>\<delta> / 2 < \<delta>\<close> by (by100 linarith)
  qed
  define q where "q = P + t *\<^sub>R (p - P)"
  have hq_seg_form: "q = (1 - t) *\<^sub>R P + t *\<^sub>R p"
    unfolding q_def by (simp add: algebra_simps)
  have hq_seg: "q \<in> closed_segment P p"
    unfolding closed_segment_def using ht_nonneg ht_le1 hq_seg_form by (by100 blast)
  have hq_ne: "q \<noteq> P"
  proof
    assume "q = P"
    hence "t *\<^sub>R (p - P) = 0"
      unfolding q_def by (by100 simp)
    hence "t = 0 \<or> p - P = 0"
      by (by100 simp)
    thus False using ht_pos hp_ne by (by100 simp)
  qed
  have hq_ball: "q \<in> ball P \<delta>"
  proof -
    have hdist: "dist P q = norm (t *\<^sub>R (p - P))"
      unfolding q_def by (simp add: dist_norm)
    have ht_abs: "\<bar>t\<bar> = t" using ht_nonneg by (by100 simp)
    have hnorm_eq: "norm (t *\<^sub>R (p - P)) = t * norm (p - P)"
      using ht_abs by (by100 simp)
    have "dist P q = t * norm (p - P)" using hdist hnorm_eq by (by100 simp)
    hence "dist P q < \<delta>" using ht_norm_lt by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  show ?thesis using hq_seg hq_ne hq_ball by (by100 blast)
qed

lemma segment_face_with_endpoint_and_extra_eq:
  fixes F :: "(real^2) set" and P p z :: "real^2"
  assumes hface: "geotop_is_face F (closed_segment P p)"
      and hp_ne: "p \<noteq> P"
      and hP_F: "P \<in> F"
      and hz_F: "z \<in> F"
      and hz_ne: "z \<noteq> P"
  shows "F = closed_segment P p"
proof -
  have hseg_sv: "geotop_simplex_vertices (closed_segment P p) {P, p}"
    by (rule geotop_closed_segment_simplex_vertices[OF hp_ne[symmetric]])
  obtain V W where hV_sv: "geotop_simplex_vertices (closed_segment P p) V"
      and hW_ne: "W \<noteq> {}"
      and hW_sub: "W \<subseteq> V"
      and hF_hull: "F = geotop_convex_hull W"
    using hface unfolding geotop_is_face_def by (by100 blast)
  have hV_eq: "V = {P, p}"
    using geotop_simplex_vertices_unique[OF hV_sv hseg_sv] .
  have hW_sub_Pp: "W \<subseteq> {P, p}" using hW_sub hV_eq by (by100 simp)
  have hW_cases: "W = {P} \<or> W = {p} \<or> W = {P, p}"
    using hW_sub_Pp hW_ne by (by100 blast)
  have hF_HOL: "F = convex hull W"
    using hF_hull geotop_convex_hull_eq_HOL by (by100 simp)
  have hW_eq_Pp: "W = {P, p}"
  proof (rule disjE[OF hW_cases])
    assume hW_P: "W = {P}"
    have hF_P: "F = {P}" using hF_HOL hW_P by (by100 simp)
    have "z = P" using hz_F hF_P by (by100 blast)
    hence False using hz_ne by (by100 blast)
    thus ?thesis by (rule FalseE)
  next
    assume hrest: "W = {p} \<or> W = {P, p}"
    show ?thesis
    proof (rule disjE[OF hrest])
      assume hW_p: "W = {p}"
      have hF_p: "F = {p}" using hF_HOL hW_p by (by100 simp)
      have "P = p" using hP_F hF_p by (by100 blast)
      hence False using hp_ne by (by100 blast)
      thus ?thesis by (rule FalseE)
    next
      assume hW_Pp: "W = {P, p}"
      show ?thesis by (rule hW_Pp)
    qed
  qed
  have hF_seg: "F = convex hull {P, p}" using hF_HOL hW_eq_Pp by (by100 simp)
  also have "\<dots> = closed_segment P p" by (rule segment_convex_hull[symmetric])
  finally show ?thesis .
qed

text \<open>Endpoint version of the book's small circular-neighborhood step for a
  broken line: near an arc endpoint, only the first straight segment of the
  broken line is visible. The point determining the segment is not required
  to lie in the chosen ball; it is a direction point for the local ray.\<close>

lemma broken_line_endpoint_local_segment:
  fixes B E :: "(real^2) set" and P :: "real^2"
  assumes hB_bl: "geotop_is_broken_line B"
      and hB_endp: "geotop_arc_endpoints B E"
      and hP_E: "P \<in> E"
  shows "\<exists>\<delta>>0. \<exists>p.
            p \<noteq> P \<and>
            ball P \<delta> \<inter> B = ball P \<delta> \<inter> closed_segment P p \<and>
            ball P \<delta> \<inter> geotop_arc_interior B E \<subseteq> closed_segment P p - {P}"
proof -
  have hP_B: "P \<in> B"
    using hB_endp hP_E unfolding geotop_arc_endpoints_def by (by100 blast)
  obtain \<gamma> :: "real \<Rightarrow> real^2"
    where h\<gamma>_arc: "arc \<gamma>"
      and h\<gamma>_pim: "path_image \<gamma> = B"
      and hE_eq: "E = {pathstart \<gamma>, pathfinish \<gamma>}"
    using arc_endpoints_imp_arc_HOL[OF hB_endp] by (by100 blast)
  have hP_endpoint_param: "\<gamma> 0 = P \<or> \<gamma> 1 = P"
    using hP_E hE_eq unfolding pathstart_def pathfinish_def by (by100 blast)
  obtain K where hK_complex: "geotop_is_complex K"
      and hK_1dim: "geotop_complex_is_1dim K"
      and hK_poly: "geotop_polyhedron K = B"
      and hPK: "{P} \<in> K"
      and hK_fin: "finite K"
    using geotop_broken_line_vertex_at[OF hB_bl hP_B] by (by100 blast)
  define EdgesAtP where
    "EdgesAtP = {\<sigma>\<in>K. P \<in> \<sigma> \<and> geotop_simplex_dim \<sigma> 1}"
  have hEdges_fin: "finite EdgesAtP"
    unfolding EdgesAtP_def using hK_fin by (by100 simp)
  have hK_local_isolation:
    "\<exists>\<delta>>0. ball P \<delta> \<inter> B \<subseteq> \<Union>{\<tau>\<in>K. P \<in> \<tau>}"
  proof -
    have hK_simp_all: "\<forall>\<tau>\<in>K. geotop_is_simplex \<tau>"
      by (rule conjunct1[OF hK_complex[unfolded geotop_is_complex_def]])
    have hK_closed_all: "\<forall>\<tau>\<in>K. closed \<tau>"
    proof
      fix \<tau> assume h\<tau>K: "\<tau> \<in> K"
      have hsim: "geotop_is_simplex \<tau>"
        by (rule bspec[OF hK_simp_all h\<tau>K])
      obtain V m n where hVfin: "finite V" and h\<tau>_hull: "\<tau> = geotop_convex_hull V"
        using hsim unfolding geotop_is_simplex_def by (by100 blast)
      have h\<tau>_HOL: "\<tau> = convex hull V"
        using h\<tau>_hull geotop_convex_hull_eq_HOL by (by100 simp)
      have h_compact: "compact (convex hull V)"
        using hVfin finite_imp_compact_convex_hull by (by100 blast)
      have h_closed: "closed (convex hull V)"
        using h_compact compact_imp_closed by (by100 blast)
      show "closed \<tau>" using h\<tau>_HOL h_closed by (by100 simp)
    qed
    have hB_union: "B = \<Union>K"
      using hK_poly unfolding geotop_polyhedron_def by (by100 simp)
    show ?thesis
      using finite_union_closed_local_isolation[OF hK_fin hK_closed_all hB_union hP_B]
      by (by100 blast)
  qed
  have hEdges_nonempty: "EdgesAtP \<noteq> {}"
  proof
    assume hEdges_empty: "EdgesAtP = {}"
    obtain \<delta> where h\<delta>_pos: "\<delta> > 0"
        and h\<delta>_iso: "ball P \<delta> \<inter> B \<subseteq> \<Union>{\<tau>\<in>K. P \<in> \<tau>}"
      using hK_local_isolation by (by100 blast)
    have h_ball_only_P: "ball P \<delta> \<inter> B \<subseteq> {P}"
    proof
      fix x assume hx: "x \<in> ball P \<delta> \<inter> B"
      obtain \<tau> where h\<tau>K: "\<tau> \<in> K" and hP\<tau>: "P \<in> \<tau>" and hx\<tau>: "x \<in> \<tau>"
        using h\<delta>_iso hx by (by100 blast)
      have hdim: "\<exists>n\<le>1. geotop_simplex_dim \<tau> n"
        using hK_1dim h\<tau>K unfolding geotop_complex_is_1dim_def by (by100 blast)
      obtain n where hn_le: "n \<le> 1" and h\<tau>dim: "geotop_simplex_dim \<tau> n"
        using hdim by (by100 blast)
      have hcases: "n = 0 \<or> n = 1" using hn_le by (by100 linarith)
      show "x \<in> {P}"
      proof (rule disjE[OF hcases])
        assume hn0: "n = 0"
        have h\<tau>dim0: "geotop_simplex_dim \<tau> 0" using h\<tau>dim hn0 by (by100 simp)
        obtain V m where hVcard: "card V = 0 + 1" and h\<tau>_hull: "\<tau> = geotop_convex_hull V"
          using h\<tau>dim0 unfolding geotop_simplex_dim_def by (by100 blast)
        have hVcard1: "card V = 1" using hVcard by (by100 simp)
        obtain v where hV: "V = {v}"
          by (rule card_1_singletonE[OF hVcard1])
        have h\<tau>_HOL: "\<tau> = convex hull V"
          using h\<tau>_hull geotop_convex_hull_eq_HOL by (by100 simp)
        have h\<tau>_sing: "\<tau> = {v}" using h\<tau>_HOL hV by (by100 simp)
        have hP_v: "P = v" using hP\<tau> h\<tau>_sing by (by100 blast)
        have hxP: "x = P" using hx\<tau> h\<tau>_sing hP_v by (by100 blast)
        show ?thesis using hxP by (by100 simp)
      next
        assume hn1: "n = 1"
        have h\<tau>dim1: "geotop_simplex_dim \<tau> 1" using h\<tau>dim hn1 by (by100 simp)
        have "\<tau> \<in> EdgesAtP"
          unfolding EdgesAtP_def using h\<tau>K hP\<tau> h\<tau>dim1 by (by100 simp)
        hence False using hEdges_empty by (by100 simp)
        thus ?thesis by (rule FalseE)
      qed
    qed
    have hP_cl_int: "P \<in> closure (geotop_arc_interior B E)"
      using arc_closure_interior_eq_arc[OF hB_endp] hP_B by (by100 simp)
    have h_ball_open: "open (ball P \<delta>)" by (by100 simp)
    have hP_ball: "P \<in> ball P \<delta>" using h\<delta>_pos by (by100 simp)
    have h_int_meets: "geotop_arc_interior B E \<inter> ball P \<delta> \<noteq> {}"
      using hP_cl_int closure_iff_nhds_not_empty[of P "geotop_arc_interior B E"]
            h_ball_open hP_ball
      by (by100 blast)
    obtain y where hy_int: "y \<in> geotop_arc_interior B E" and hy_ball: "y \<in> ball P \<delta>"
      using h_int_meets by (by100 blast)
    have hyB: "y \<in> B" using hy_int unfolding geotop_arc_interior_def by (by100 blast)
    have hyP: "y = P" using h_ball_only_P hy_ball hyB by (by100 blast)
    have hy_notP: "y \<noteq> P" using hy_int hP_E unfolding geotop_arc_interior_def by (by100 blast)
    show False using hyP hy_notP by (by100 blast)
  qed
  have hEdges_at_most_one: "\<forall>\<tau>\<in>EdgesAtP. \<forall>\<rho>\<in>EdgesAtP. \<tau> = \<rho>"
  proof (intro ballI)
    fix \<tau> \<rho>
    assume h\<tau>E: "\<tau> \<in> EdgesAtP" and h\<rho>E: "\<rho> \<in> EdgesAtP"
    have h\<tau>K: "\<tau> \<in> K" and hP\<tau>: "P \<in> \<tau>" and h\<tau>dim: "geotop_simplex_dim \<tau> 1"
      using h\<tau>E unfolding EdgesAtP_def by (by100 blast)+
    have h\<rho>K: "\<rho> \<in> K" and hP\<rho>: "P \<in> \<rho>" and h\<rho>dim: "geotop_simplex_dim \<rho> 1"
      using h\<rho>E unfolding EdgesAtP_def by (by100 blast)+
    have h_edge_segment_at_P:
      "\<And>e. \<lbrakk>e \<in> K; P \<in> e; geotop_simplex_dim e 1\<rbrakk>
        \<Longrightarrow> \<exists>q. q \<noteq> P \<and> e = closed_segment P q"
    proof -
      fix e
      assume heK: "e \<in> K" and hPe: "P \<in> e" and hedim: "geotop_simplex_dim e 1"
      have hcases: "(\<exists>v. e = {v}) \<or> (\<exists>a b. a \<noteq> b \<and> e = closed_segment a b)"
        by (rule geotop_1dim_simplex_cases[OF hK_1dim heK])
      show "\<exists>q. q \<noteq> P \<and> e = closed_segment P q"
      proof (rule disjE[OF hcases])
        assume "\<exists>v. e = {v}"
        then obtain v where hev: "e = {v}" by (by100 blast)
        have hdim0: "geotop_simplex_dim e 0"
          using hev geotop_singleton_is_simplex by (by100 simp)
        have "0 = (1::nat)" by (rule geotop_simplex_dim_unique[OF hdim0 hedim])
        hence False by simp
        thus ?thesis by (rule FalseE)
      next
        assume "\<exists>a b. a \<noteq> b \<and> e = closed_segment a b"
        then obtain a b where hab: "a \<noteq> b" and heab: "e = closed_segment a b"
          by (by100 blast)
        have hP_endpoint: "P = a \<or> P = b"
          by (rule geotop_1dim_vertex_in_1simplex_is_endpoint
              [OF hK_complex hPK heK heab hab hPe])
        show ?thesis
        proof (rule disjE[OF hP_endpoint])
          assume hPa: "P = a"
          have hb_ne: "b \<noteq> P" using hab hPa by (by100 blast)
          have hseg: "e = closed_segment P b" using heab hPa by (by100 simp)
          show ?thesis using hb_ne hseg by (by100 blast)
        next
          assume hPb: "P = b"
          have ha_ne: "a \<noteq> P" using hab hPb by (by100 blast)
          have hcomm: "closed_segment a b = closed_segment b a"
            by (rule closed_segment_commute)
          have hseg: "e = closed_segment P a" using heab hPb hcomm by (by100 simp)
          show ?thesis using ha_ne hseg by (by100 blast)
        qed
      qed
    qed
    obtain q\<tau> where hq\<tau>_ne: "q\<tau> \<noteq> P" and h\<tau>_seg: "\<tau> = closed_segment P q\<tau>"
      using h_edge_segment_at_P[OF h\<tau>K hP\<tau> h\<tau>dim] by (by100 blast)
    obtain q\<rho> where hq\<rho>_ne: "q\<rho> \<noteq> P" and h\<rho>_seg: "\<rho> = closed_segment P q\<rho>"
      using h_edge_segment_at_P[OF h\<rho>K hP\<rho> h\<rho>dim] by (by100 blast)
    have h_overlap_nonendpoint: "\<exists>z. z \<in> \<tau> \<inter> \<rho> \<and> z \<noteq> P"
    proof -
      have hK_path: "geotop_polyhedron K = path_image \<gamma>"
        using hK_poly h\<gamma>_pim by (by100 simp)
      obtain s_tau t_tau where hst_tau_le: "s_tau \<le> t_tau"
          and hs_tau_01: "s_tau \<in> {0..1}"
          and ht_tau_01: "t_tau \<in> {0..1}"
          and hpre_tau: "{s\<in>{0..1}. \<gamma> s \<in> \<tau>} = {s_tau..t_tau}"
          and hends_tau: "{\<gamma> s_tau, \<gamma> t_tau} = {P, q\<tau>}"
        using geotop_arc_1simplex_preimage_structure
          [OF h\<gamma>_arc hK_1dim hK_path h\<tau>K h\<tau>_seg hq\<tau>_ne[symmetric]]
        by (by100 blast)
      obtain s_rho t_rho where hst_rho_le: "s_rho \<le> t_rho"
          and hs_rho_01: "s_rho \<in> {0..1}"
          and ht_rho_01: "t_rho \<in> {0..1}"
          and hpre_rho: "{s\<in>{0..1}. \<gamma> s \<in> \<rho>} = {s_rho..t_rho}"
          and hends_rho: "{\<gamma> s_rho, \<gamma> t_rho} = {P, q\<rho>}"
        using geotop_arc_1simplex_preimage_structure
          [OF h\<gamma>_arc hK_1dim hK_path h\<rho>K h\<rho>_seg hq\<rho>_ne[symmetric]]
        by (by100 blast)
      have h_ordered_endpoint_overlap:
        "\<exists>r\<in>{0..1}. \<gamma> r \<in> \<tau> \<and> \<gamma> r \<in> \<rho> \<and> \<gamma> r \<noteq> P"
      proof (rule disjE[OF hP_endpoint_param])
        assume h0P: "\<gamma> 0 = P"
        have hinj: "inj_on \<gamma> {0..1}"
          using h\<gamma>_arc unfolding arc_def by (by100 blast)
        have h0_pre_tau: "0 \<in> {s\<in>{0..1}. \<gamma> s \<in> \<tau>}"
          using h0P hP\<tau> by (by100 simp)
        have h0_tau_iv: "0 \<in> {s_tau..t_tau}"
          using h0_pre_tau hpre_tau by (by100 simp)
        have hs_tau_zero: "s_tau = 0"
          using h0_tau_iv hs_tau_01 by (by100 simp)
        have hq_tau_img: "\<gamma> t_tau = q\<tau>"
        proof -
          have "q\<tau> \<in> {\<gamma> s_tau, \<gamma> t_tau}"
            using hends_tau by (by100 blast)
          thus ?thesis using hs_tau_zero h0P hq\<tau>_ne by (by100 blast)
        qed
        have ht_tau_pos: "t_tau > 0"
        proof -
          have "t_tau \<noteq> 0"
          proof
            assume ht0: "t_tau = 0"
            have "\<gamma> t_tau = P" using ht0 h0P by (by100 simp)
            thus False using hq_tau_img hq\<tau>_ne by (by100 simp)
          qed
          thus ?thesis using ht_tau_01 by (by100 simp)
        qed
        have h0_pre_rho: "0 \<in> {s\<in>{0..1}. \<gamma> s \<in> \<rho>}"
          using h0P hP\<rho> by (by100 simp)
        have h0_rho_iv: "0 \<in> {s_rho..t_rho}"
          using h0_pre_rho hpre_rho by (by100 simp)
        have hs_rho_zero: "s_rho = 0"
          using h0_rho_iv hs_rho_01 by (by100 simp)
        have hq_rho_img: "\<gamma> t_rho = q\<rho>"
        proof -
          have "q\<rho> \<in> {\<gamma> s_rho, \<gamma> t_rho}"
            using hends_rho by (by100 blast)
          thus ?thesis using hs_rho_zero h0P hq\<rho>_ne by (by100 blast)
        qed
        have ht_rho_pos: "t_rho > 0"
        proof -
          have "t_rho \<noteq> 0"
          proof
            assume ht0: "t_rho = 0"
            have "\<gamma> t_rho = P" using ht0 h0P by (by100 simp)
            thus False using hq_rho_img hq\<rho>_ne by (by100 simp)
          qed
          thus ?thesis using ht_rho_01 by (by100 simp)
        qed
        define r where "r = min t_tau t_rho / 2"
        have hr_pos: "r > 0" unfolding r_def using ht_tau_pos ht_rho_pos by (by100 simp)
        have hr_le_tau: "r \<le> t_tau" unfolding r_def using ht_tau_pos by (by100 linarith)
        have hr_le_rho: "r \<le> t_rho" unfolding r_def using ht_rho_pos by (by100 linarith)
        have hr_01: "r \<in> {0..1}"
        proof -
          have ht_tau_le1: "t_tau \<le> 1" using ht_tau_01 by (by100 simp)
          have "r \<le> 1" unfolding r_def using ht_tau_le1 by (by100 linarith)
          thus ?thesis using hr_pos by (by100 simp)
        qed
        have hr_tau_iv: "r \<in> {s_tau..t_tau}"
          using hs_tau_zero hr_pos hr_le_tau by (by100 simp)
        have hr_rho_iv: "r \<in> {s_rho..t_rho}"
          using hs_rho_zero hr_pos hr_le_rho by (by100 simp)
        have hr_tau: "\<gamma> r \<in> \<tau>"
          using hpre_tau hr_01 hr_tau_iv by (by100 blast)
        have hr_rho: "\<gamma> r \<in> \<rho>"
          using hpre_rho hr_01 hr_rho_iv by (by100 blast)
        have hr_neP: "\<gamma> r \<noteq> P"
        proof
          assume hrP: "\<gamma> r = P"
          have h0_01: "(0::real) \<in> {0..1}" by (by100 simp)
          have "r = 0"
            using hinj hr_01 h0_01 hrP h0P unfolding inj_on_def by (by100 blast)
          thus False using hr_pos by (by100 simp)
        qed
        show ?thesis using hr_01 hr_tau hr_rho hr_neP by (by100 blast)
      next
        assume h1P: "\<gamma> 1 = P"
        have hinj: "inj_on \<gamma> {0..1}"
          using h\<gamma>_arc unfolding arc_def by (by100 blast)
        have h1_pre_tau: "1 \<in> {s\<in>{0..1}. \<gamma> s \<in> \<tau>}"
          using h1P hP\<tau> by (by100 simp)
        have h1_tau_iv: "1 \<in> {s_tau..t_tau}"
          using h1_pre_tau hpre_tau by (by100 simp)
        have ht_tau_one: "t_tau = 1"
          using h1_tau_iv ht_tau_01 by (by100 simp)
        have hq_tau_img: "\<gamma> s_tau = q\<tau>"
        proof -
          have "q\<tau> \<in> {\<gamma> s_tau, \<gamma> t_tau}"
            using hends_tau by (by100 blast)
          thus ?thesis using ht_tau_one h1P hq\<tau>_ne by (by100 blast)
        qed
        have hs_tau_lt1: "s_tau < 1"
        proof -
          have "s_tau \<noteq> 1"
          proof
            assume hs1: "s_tau = 1"
            have "\<gamma> s_tau = P" using hs1 h1P by (by100 simp)
            thus False using hq_tau_img hq\<tau>_ne by (by100 simp)
          qed
          thus ?thesis using hs_tau_01 by (by100 simp)
        qed
        have h1_pre_rho: "1 \<in> {s\<in>{0..1}. \<gamma> s \<in> \<rho>}"
          using h1P hP\<rho> by (by100 simp)
        have h1_rho_iv: "1 \<in> {s_rho..t_rho}"
          using h1_pre_rho hpre_rho by (by100 simp)
        have ht_rho_one: "t_rho = 1"
          using h1_rho_iv ht_rho_01 by (by100 simp)
        have hq_rho_img: "\<gamma> s_rho = q\<rho>"
        proof -
          have "q\<rho> \<in> {\<gamma> s_rho, \<gamma> t_rho}"
            using hends_rho by (by100 blast)
          thus ?thesis using ht_rho_one h1P hq\<rho>_ne by (by100 blast)
        qed
        have hs_rho_lt1: "s_rho < 1"
        proof -
          have "s_rho \<noteq> 1"
          proof
            assume hs1: "s_rho = 1"
            have "\<gamma> s_rho = P" using hs1 h1P by (by100 simp)
            thus False using hq_rho_img hq\<rho>_ne by (by100 simp)
          qed
          thus ?thesis using hs_rho_01 by (by100 simp)
        qed
        define eta where "eta = min (1 - s_tau) (1 - s_rho) / 2"
        define r where "r = 1 - eta"
        have heta_pos: "eta > 0" unfolding eta_def using hs_tau_lt1 hs_rho_lt1 by (by100 simp)
        have hmin_pos: "min (1 - s_tau) (1 - s_rho) > 0"
          using hs_tau_lt1 hs_rho_lt1 by (by100 simp)
        have heta_le_min: "eta \<le> min (1 - s_tau) (1 - s_rho)"
        proof -
          have hdiv: "min (1 - s_tau) (1 - s_rho) / 2
              \<le> min (1 - s_tau) (1 - s_rho) / 1"
          proof (rule divide_left_mono)
            show "(1::real) \<le> 2" by (by100 simp)
            show "0 \<le> min (1 - s_tau) (1 - s_rho)" using hmin_pos by (by100 simp)
            show "0 < (2::real) * 1" by (by100 simp)
          qed
          show ?thesis unfolding eta_def using hdiv by (by100 simp)
        qed
        have hmin_le_tau: "min (1 - s_tau) (1 - s_rho) \<le> 1 - s_tau"
          by (by100 simp)
        have hmin_le_rho: "min (1 - s_tau) (1 - s_rho) \<le> 1 - s_rho"
          by (by100 simp)
        have heta_le_tau: "eta \<le> 1 - s_tau"
          using heta_le_min hmin_le_tau by (by100 linarith)
        have heta_le_rho: "eta \<le> 1 - s_rho"
          using heta_le_min hmin_le_rho by (by100 linarith)
        have heta_le1: "eta \<le> 1"
        proof -
          have hs_tau_ge0: "0 \<le> s_tau" using hs_tau_01 by (by100 simp)
          have "1 - s_tau \<le> 1" using hs_tau_ge0 by (by100 simp)
          thus ?thesis using heta_le_tau by (by100 linarith)
        qed
        have hr_lt1: "r < 1" unfolding r_def using heta_pos by (by100 simp)
        have hr_ge0: "0 \<le> r" unfolding r_def using heta_le1 by (by100 simp)
        have hr_01: "r \<in> {0..1}" using hr_ge0 hr_lt1 by (by100 simp)
        have hr_ge_tau: "s_tau \<le> r" unfolding r_def using heta_le_tau by (by100 linarith)
        have hr_ge_rho: "s_rho \<le> r" unfolding r_def using heta_le_rho by (by100 linarith)
        have hr_tau_iv: "r \<in> {s_tau..t_tau}"
          using hr_ge_tau hr_lt1 ht_tau_one by (by100 simp)
        have hr_rho_iv: "r \<in> {s_rho..t_rho}"
          using hr_ge_rho hr_lt1 ht_rho_one by (by100 simp)
        have hr_tau: "\<gamma> r \<in> \<tau>"
          using hpre_tau hr_01 hr_tau_iv by (by100 blast)
        have hr_rho: "\<gamma> r \<in> \<rho>"
          using hpre_rho hr_01 hr_rho_iv by (by100 blast)
        have hr_neP: "\<gamma> r \<noteq> P"
        proof
          assume hrP: "\<gamma> r = P"
          have h1_01: "(1::real) \<in> {0..1}" by (by100 simp)
          have "r = 1"
            using hinj hr_01 h1_01 hrP h1P unfolding inj_on_def by (by100 blast)
          thus False using hr_lt1 by (by100 simp)
        qed
        show ?thesis using hr_01 hr_tau hr_rho hr_neP by (by100 blast)
      qed
      obtain r where hr_01: "r \<in> {0..1}"
          and hr_tau: "\<gamma> r \<in> \<tau>"
          and hr_rho: "\<gamma> r \<in> \<rho>"
          and hr_ne: "\<gamma> r \<noteq> P"
        using h_ordered_endpoint_overlap by (by100 blast)
      show ?thesis using hr_tau hr_rho hr_ne by (by100 blast)
    qed
    obtain z where hz_inter: "z \<in> \<tau> \<inter> \<rho>" and hz_ne: "z \<noteq> P"
      using h_overlap_nonendpoint by (by100 blast)
    have h_inter_ne: "\<tau> \<inter> \<rho> \<noteq> {}" using hP\<tau> hP\<rho> by (by100 blast)
    have hface_\<tau>: "geotop_is_face (\<tau> \<inter> \<rho>) \<tau>"
      using hK_complex h\<tau>K h\<rho>K h_inter_ne unfolding geotop_is_complex_def by (by100 blast)
    have hface_\<rho>: "geotop_is_face (\<tau> \<inter> \<rho>) \<rho>"
      using hK_complex h\<tau>K h\<rho>K h_inter_ne unfolding geotop_is_complex_def by (by100 blast)
    have hP_inter: "P \<in> \<tau> \<inter> \<rho>" using hP\<tau> hP\<rho> by (by100 blast)
    have h\<tau>eq: "\<tau> \<inter> \<rho> = \<tau>"
      using segment_face_with_endpoint_and_extra_eq[of "\<tau> \<inter> \<rho>" P q\<tau> z]
            hface_\<tau> hq\<tau>_ne hP_inter hz_inter hz_ne h\<tau>_seg
      by (by100 simp)
    have h\<rho>eq: "\<tau> \<inter> \<rho> = \<rho>"
      using segment_face_with_endpoint_and_extra_eq[of "\<tau> \<inter> \<rho>" P q\<rho> z]
            hface_\<rho> hq\<rho>_ne hP_inter hz_inter hz_ne h\<rho>_seg
      by (by100 simp)
    show "\<tau> = \<rho>" using h\<tau>eq h\<rho>eq by (by100 simp)
  qed
  have hEdges_unique: "\<exists>!\<sigma>. \<sigma> \<in> EdgesAtP"
  proof -
    obtain \<sigma> where h\<sigma>: "\<sigma> \<in> EdgesAtP" using hEdges_nonempty by (by100 blast)
    show ?thesis
    proof (rule ex1I[of _ \<sigma>])
      show "\<sigma> \<in> EdgesAtP" by (rule h\<sigma>)
      fix \<tau> assume h\<tau>: "\<tau> \<in> EdgesAtP"
      show "\<tau> = \<sigma>" using hEdges_at_most_one h\<tau> h\<sigma> by (by100 blast)
    qed
  qed
  obtain \<sigma> where h\<sigma>_edge: "\<sigma> \<in> EdgesAtP"
      and h\<sigma>_unique: "\<forall>\<tau>. \<tau> \<in> EdgesAtP \<longrightarrow> \<tau> = \<sigma>"
    using hEdges_unique unfolding Ex1_def by (by100 blast)
  have h\<sigma>_KP: "\<sigma> \<in> K \<and> P \<in> \<sigma> \<and> geotop_simplex_dim \<sigma> 1"
    using h\<sigma>_edge unfolding EdgesAtP_def by (by100 blast)
  obtain a b where hab_ne: "a \<noteq> b" and h\<sigma>_seg_ab: "\<sigma> = closed_segment a b"
  proof -
    have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma>_KP by (by100 blast)
    have h\<sigma>dim1: "geotop_simplex_dim \<sigma> 1" using h\<sigma>_KP by (by100 blast)
    have hcases: "(\<exists>v. \<sigma> = {v}) \<or> (\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b)"
      by (rule geotop_1dim_simplex_cases[OF hK_1dim h\<sigma>K])
    show ?thesis
    proof (rule disjE[OF hcases])
      assume "\<exists>v. \<sigma> = {v}"
      then obtain v where h\<sigma>v: "\<sigma> = {v}" by (by100 blast)
      have hdim0: "geotop_simplex_dim \<sigma> 0"
        using h\<sigma>v geotop_singleton_is_simplex by (by100 simp)
      have "0 = (1::nat)" by (rule geotop_simplex_dim_unique[OF hdim0 h\<sigma>dim1])
      hence False by simp
      thus ?thesis by (rule FalseE)
    next
      assume "\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b"
      thus ?thesis using that by (by100 blast)
    qed
  qed
  have hP_ab: "P = a \<or> P = b"
  proof -
    have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma>_KP by (by100 blast)
    have hP\<sigma>: "P \<in> \<sigma>" using h\<sigma>_KP by (by100 blast)
    show ?thesis
      by (rule geotop_1dim_vertex_in_1simplex_is_endpoint
          [OF hK_complex hPK h\<sigma>K h\<sigma>_seg_ab hab_ne hP\<sigma>])
  qed
  obtain p where hp_ne: "p \<noteq> P" and h\<sigma>_seg: "\<sigma> = closed_segment P p"
  proof (rule disjE[OF hP_ab])
    assume hPa: "P = a"
    have hb_ne: "b \<noteq> P" using hab_ne hPa by (by100 blast)
    have hseg: "\<sigma> = closed_segment P b" using h\<sigma>_seg_ab hPa by (by100 simp)
    show ?thesis using that hb_ne hseg by (by100 blast)
  next
    assume hPb: "P = b"
    have ha_ne: "a \<noteq> P" using hab_ne hPb by (by100 blast)
    have hcomm: "closed_segment a b = closed_segment b a"
      by (rule closed_segment_commute)
    have hseg: "\<sigma> = closed_segment P a"
      using h\<sigma>_seg_ab hPb hcomm by (by100 simp)
    show ?thesis using that ha_ne hseg by (by100 blast)
  qed
  obtain \<delta>\<^sub>0 where h\<delta>0_pos: "\<delta>\<^sub>0 > 0"
      and h\<delta>0_iso: "ball P \<delta>\<^sub>0 \<inter> B \<subseteq> \<Union>{\<tau>\<in>K. P \<in> \<tau>}"
    using hK_local_isolation by (by100 blast)
  have hlocal_unique_edge:
    "ball P \<delta>\<^sub>0 \<inter> B \<subseteq> \<sigma>"
  proof
    fix x assume hx: "x \<in> ball P \<delta>\<^sub>0 \<inter> B"
    obtain \<tau> where h\<tau>K: "\<tau> \<in> K" and hP\<tau>: "P \<in> \<tau>" and hx\<tau>: "x \<in> \<tau>"
      using h\<delta>0_iso hx by (by100 blast)
    have hdim: "\<exists>n\<le>1. geotop_simplex_dim \<tau> n"
      using hK_1dim h\<tau>K unfolding geotop_complex_is_1dim_def by (by100 blast)
    obtain n where hn_le: "n \<le> 1" and h\<tau>dim: "geotop_simplex_dim \<tau> n"
      using hdim by (by100 blast)
    have hcases: "n = 0 \<or> n = 1" using hn_le by (by100 linarith)
    show "x \<in> \<sigma>"
    proof (rule disjE[OF hcases])
      assume hn0: "n = 0"
      have h\<tau>dim0: "geotop_simplex_dim \<tau> 0" using h\<tau>dim hn0 by (by100 simp)
      obtain V m where hVcard: "card V = 0 + 1" and h\<tau>_hull: "\<tau> = geotop_convex_hull V"
        using h\<tau>dim0 unfolding geotop_simplex_dim_def by (by100 blast)
      have hVcard1: "card V = 1" using hVcard by (by100 simp)
      obtain v where hV: "V = {v}"
        by (rule card_1_singletonE[OF hVcard1])
      have h\<tau>_HOL: "\<tau> = convex hull V"
        using h\<tau>_hull geotop_convex_hull_eq_HOL by (by100 simp)
      have h\<tau>_sing: "\<tau> = {v}" using h\<tau>_HOL hV by (by100 simp)
      have hP_v: "P = v" using hP\<tau> h\<tau>_sing by (by100 blast)
      have hxP: "x = P" using hx\<tau> h\<tau>_sing hP_v by (by100 blast)
      have hP\<sigma>: "P \<in> \<sigma>" using h\<sigma>_KP by (by100 blast)
      show ?thesis using hxP hP\<sigma> by (by100 simp)
    next
      assume hn1: "n = 1"
      have h\<tau>dim1: "geotop_simplex_dim \<tau> 1" using h\<tau>dim hn1 by (by100 simp)
      have h\<tau>_edge: "\<tau> \<in> EdgesAtP"
        unfolding EdgesAtP_def using h\<tau>K hP\<tau> h\<tau>dim1 by (by100 simp)
      have h\<tau>eq: "\<tau> = \<sigma>" using h\<sigma>_unique h\<tau>_edge by (by100 blast)
      show ?thesis using hx\<tau> h\<tau>eq by (by100 simp)
    qed
  qed
  have hlocal_eq:
    "ball P \<delta>\<^sub>0 \<inter> B = ball P \<delta>\<^sub>0 \<inter> closed_segment P p"
  proof
    show "ball P \<delta>\<^sub>0 \<inter> B \<subseteq> ball P \<delta>\<^sub>0 \<inter> closed_segment P p"
      using hlocal_unique_edge h\<sigma>_seg by (by100 blast)
    show "ball P \<delta>\<^sub>0 \<inter> closed_segment P p \<subseteq> ball P \<delta>\<^sub>0 \<inter> B"
    proof
      fix x assume hx: "x \<in> ball P \<delta>\<^sub>0 \<inter> closed_segment P p"
      have hx\<sigma>: "x \<in> \<sigma>" using hx h\<sigma>_seg by (by100 simp)
      have h\<sigma>K: "\<sigma> \<in> K" using h\<sigma>_KP by (by100 blast)
      have hxB: "x \<in> B"
        using hx\<sigma> h\<sigma>K hK_poly unfolding geotop_polyhedron_def by (by100 blast)
      show "x \<in> ball P \<delta>\<^sub>0 \<inter> B" using hx hxB by (by100 blast)
    qed
  qed
  have hlocal_int:
    "ball P \<delta>\<^sub>0 \<inter> geotop_arc_interior B E \<subseteq> closed_segment P p - {P}"
  proof
    fix x assume hx: "x \<in> ball P \<delta>\<^sub>0 \<inter> geotop_arc_interior B E"
    have hx_ball: "x \<in> ball P \<delta>\<^sub>0" using hx by (by100 blast)
    have hxB: "x \<in> B" using hx unfolding geotop_arc_interior_def by (by100 blast)
    have hx_seg: "x \<in> closed_segment P p"
      using hlocal_eq hx_ball hxB by (by100 blast)
    have hx_notP: "x \<noteq> P"
      using hx hP_E unfolding geotop_arc_interior_def by (by100 blast)
    show "x \<in> closed_segment P p - {P}" using hx_seg hx_notP by (by100 blast)
  qed
  show ?thesis
    using h\<delta>0_pos hp_ne hlocal_eq hlocal_int by (by100 blast)
qed


end
