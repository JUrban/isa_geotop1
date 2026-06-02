theory GeoTop_3_4_Facts
  imports "GeoTop34PrefixDirty.GeoTop_3_4_Prefix"
begin

text \<open>\<open>geotop_diameter\<close> and \<open>geotop_mesh\<close> are defined earlier (before
Theorem_GT_1), since they are needed to state the mesh-shrinkage lemma for
iterated barycentric subdivision.\<close>

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
proof -
  obtain f where hhomeo: "top1_homeomorphism_on J
                           (subspace_topology UNIV geotop_euclidean_topology J)
                           (geotop_std_sphere::(real^2) set)
                           (subspace_topology UNIV geotop_euclidean_topology
                              (geotop_std_sphere::(real^2) set)) f"
    using hJ unfolding geotop_is_n_sphere_def by blast
  have hhomeo_HOL: "J homeomorphic (geotop_std_sphere::(real^2) set)"
    by (rule top1_homeomorphism_on_geotop_imp_HOL_homeomorphic[OF hhomeo])
  have hstd_eq: "(geotop_std_sphere::(real^2) set) = sphere 0 1"
    unfolding geotop_std_sphere_def sphere_def by simp
  have hJ_sphere: "J homeomorphic sphere (0::real^2) 1"
    using hhomeo_HOL hstd_eq by simp
  obtain P where hP_notJ: "P \<in> UNIV - J"
             and hU_eq: "U = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
    using hU by blast
  have hU_HOL: "U = connected_component_set (UNIV - J) P"
    using hU_eq geotop_component_at_UNIV_eq_connected_component_set by simp
  have hU_comp: "U = connected_component_set (- J) P"
    using hU_HOL by (simp add: Compl_eq_Diff_UNIV)
  have hP_compl: "P \<in> - J" using hP_notJ by (simp add: Compl_eq_Diff_UNIV)
  have hU_in_components: "U \<in> components (- J)"
    unfolding components_def using hU_comp hP_compl by blast
  have hdim: "(2::nat) \<le> DIM(real^2)" by simp
  have hfrontier: "frontier U = J"
    by (rule Jordan_Brouwer_frontier[OF hJ_sphere hU_in_components hdim])
  show ?thesis
    using hfrontier geotop_frontier_UNIV_eq_frontier by metis
qed

lemma geotop_1sphere_simple_closed_path_R2:
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  obtains c :: "real \<Rightarrow> real^2"
    where "simple_path c" "pathfinish c = pathstart c" "path_image c = J"
proof -
  obtain f where hf: "top1_homeomorphism_on J
        (subspace_topology UNIV geotop_euclidean_topology J)
        (geotop_std_sphere::(real^2) set)
        (subspace_topology UNIV geotop_euclidean_topology
            (geotop_std_sphere::(real^2) set)) f"
    using hJ unfolding geotop_is_n_sphere_def by (by100 blast)
  have hstd_sphere: "(geotop_std_sphere::(real^2) set) = sphere 0 1"
    unfolding geotop_std_sphere_def by (auto simp: norm_eq_sqrt_inner)
  have h_homeo_HOL: "J homeomorphic (geotop_std_sphere::(real^2) set)"
    using hf top1_homeomorphism_on_geotop_imp_HOL_homeomorphic by (by100 blast)
  hence h_homeo_HOL_sph: "J homeomorphic (sphere (0::real^2) 1)"
    using hstd_sphere by (by100 simp)
  from h_homeo_HOL_sph have h_sym: "(sphere (0::real^2) 1) homeomorphic J"
    using homeomorphic_sym by (by100 blast)
  then obtain g g' where hg_homeo: "homeomorphism (sphere (0::real^2) 1) J g g'"
    unfolding homeomorphic_def by (by100 blast)
  have hg_cont_sphere: "continuous_on (sphere (0::real^2) 1) g"
    using hg_homeo by (simp add: homeomorphism_def)
  have hg_image: "g ` (sphere (0::real^2) 1) = J"
    using hg_homeo by (simp add: homeomorphism_def)
  have hg_inv: "\<And>x. x \<in> sphere (0::real^2) 1 \<Longrightarrow> g' (g x) = x"
    using hg_homeo unfolding homeomorphism_def by (by100 blast)
  have hg_inj: "inj_on g (sphere (0::real^2) 1)"
  proof (rule inj_onI)
    fix x y assume hx: "x \<in> sphere 0 1" and hy: "y \<in> sphere 0 1" and heq: "g x = g y"
    from heq have "g' (g x) = g' (g y)" by (by100 simp)
    thus "x = y" using hg_inv hx hy by (by100 simp)
  qed
  define c where "c = g \<circ> circle_path_R2"
  have h_path_image_c: "path_image c = J"
  proof -
    have "path_image c = path_image (g \<circ> circle_path_R2)" by (simp add: c_def)
    also have "\<dots> = g ` path_image circle_path_R2" by (rule path_image_compose)
    also have "\<dots> = g ` sphere 0 1" by (simp add: path_image_circle_path_R2)
    finally show ?thesis using hg_image by (by100 simp)
  qed
  have h_pathstart_c: "pathstart c = g (vector [1, 0])"
    by (simp add: c_def pathstart_compose pathstart_circle_path_R2)
  have h_pathfinish_c: "pathfinish c = g (vector [1, 0])"
    by (simp add: c_def pathfinish_compose pathfinish_circle_path_R2)
  have h_loop_c: "pathfinish c = pathstart c"
    using h_pathstart_c h_pathfinish_c by (by100 simp)
  have h_simple_c: "simple_path c"
  proof -
    have h_g_cont_image: "continuous_on (path_image circle_path_R2) g"
      using hg_cont_sphere path_image_circle_path_R2 by (by100 simp)
    have h_g_inj_image: "inj_on g (path_image circle_path_R2)"
      using hg_inj path_image_circle_path_R2 by (by100 simp)
    show ?thesis unfolding c_def
      by (rule simple_path_compose_homeomorphism[OF simple_path_circle_path_R2
                                                    h_g_cont_image h_g_inj_image])
  qed
  show ?thesis by (rule that[OF h_simple_c h_loop_c h_path_image_c])
qed

lemma geotop_1sphere_components_from_Jordan_curve:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  obtains inner outer where
    "inner \<in> components (UNIV - J)"
    "outer \<in> components (UNIV - J)"
    "bounded inner"
    "\<not> bounded outer"
    "components (UNIV - J) = {inner, outer}"
proof -
  obtain c :: "real \<Rightarrow> real^2" where hc_simple: "simple_path c"
      and hc_loop: "pathfinish c = pathstart c"
      and hc_image: "path_image c = J"
    by (rule geotop_1sphere_simple_closed_path_R2[OF hJ])
  obtain inner outer where hinner_ne: "inner \<noteq> {}"
      and hinner_open: "open inner"
      and hinner_conn: "connected inner"
      and houter_ne: "outer \<noteq> {}"
      and houter_open: "open outer"
      and houter_conn: "connected outer"
      and hinner_bdd: "bounded inner"
      and houter_unbdd: "\<not> bounded outer"
      and hdisj: "inner \<inter> outer = {}"
      and hcover: "inner \<union> outer = - path_image c"
      and hfront_inner: "frontier inner = path_image c"
      and hfront_outer: "frontier outer = path_image c"
    by (rule Jordan_curve_real2[OF hc_simple hc_loop])
  have hcover_J: "inner \<union> outer = UNIV - J"
    using hcover hc_image by (simp add: Compl_eq_Diff_UNIV)
  have hinner_sub: "inner \<subseteq> UNIV - J"
    using hcover_J by (by100 blast)
  have houter_sub: "outer \<subseteq> UNIV - J"
    using hcover_J by (by100 blast)
  have hinner_comp: "inner \<in> components (UNIV - J)"
  proof -
    have hmax: "\<forall>D. D \<noteq> {} \<and> inner \<subseteq> D \<and> D \<subseteq> UNIV - J \<and> connected D \<longrightarrow> D = inner"
    proof (intro allI impI)
      fix D :: "(real^2) set"
      assume hD: "D \<noteq> {} \<and> inner \<subseteq> D \<and> D \<subseteq> UNIV - J \<and> connected D"
      have hinnerD_ne: "inner \<inter> D \<noteq> {}"
        using hD hinner_ne by (by100 blast)
      have hD_sub_union: "D \<subseteq> inner \<union> outer"
        using hD hcover_J by (by100 blast)
      have houterD_empty: "outer \<inter> D = {}"
      proof -
        have hsep: "inner \<inter> D = {} \<or> outer \<inter> D = {}"
        proof -
          have hdisjD: "inner \<inter> outer \<inter> D = {}"
            using hdisj by (by100 blast)
          show ?thesis
            using connectedD[OF _ hinner_open houter_open hdisjD hD_sub_union] hD
            by (by100 blast)
        qed
        thus ?thesis using hinnerD_ne by (by100 blast)
      qed
      have hD_sub_inner: "D \<subseteq> inner"
        using hD_sub_union houterD_empty by (by100 blast)
      show "D = inner"
        using hD hD_sub_inner by (by100 blast)
    qed
    show ?thesis
      unfolding in_components_maximal
      using hinner_ne hinner_sub hinner_conn hmax by (by100 blast)
  qed
  have houter_comp: "outer \<in> components (UNIV - J)"
  proof -
    have hmax: "\<forall>D. D \<noteq> {} \<and> outer \<subseteq> D \<and> D \<subseteq> UNIV - J \<and> connected D \<longrightarrow> D = outer"
    proof (intro allI impI)
      fix D :: "(real^2) set"
      assume hD: "D \<noteq> {} \<and> outer \<subseteq> D \<and> D \<subseteq> UNIV - J \<and> connected D"
      have houterD_ne: "outer \<inter> D \<noteq> {}"
        using hD houter_ne by (by100 blast)
      have hD_sub_union: "D \<subseteq> inner \<union> outer"
        using hD hcover_J by (by100 blast)
      have hinnerD_empty: "inner \<inter> D = {}"
      proof -
        have hsep: "inner \<inter> D = {} \<or> outer \<inter> D = {}"
        proof -
          have hdisjD: "inner \<inter> outer \<inter> D = {}"
            using hdisj by (by100 blast)
          show ?thesis
            using connectedD[OF _ hinner_open houter_open hdisjD hD_sub_union] hD
            by (by100 blast)
        qed
        thus ?thesis using houterD_ne by (by100 blast)
      qed
      have hD_sub_outer: "D \<subseteq> outer"
        using hD_sub_union hinnerD_empty by (by100 blast)
      show "D = outer"
        using hD hD_sub_outer by (by100 blast)
    qed
    show ?thesis
      unfolding in_components_maximal
      using houter_ne houter_sub houter_conn hmax by (by100 blast)
  qed
  have hcomponents_subset: "components (UNIV - J) \<subseteq> {inner, outer}"
  proof
    fix C assume hCcomp: "C \<in> components (UNIV - J)"
    have hC_ne: "C \<noteq> {}"
      using hCcomp in_components_nonempty by (by100 blast)
    have hC_sub: "C \<subseteq> UNIV - J"
      using hCcomp in_components_subset by (by100 blast)
    have hC_conn: "connected C"
      using hCcomp in_components_connected by (by100 blast)
    have hC_sub_union: "C \<subseteq> inner \<union> outer"
      using hC_sub hcover_J by (by100 blast)
    show "C \<in> {inner, outer}"
    proof (cases "inner \<inter> C = {}")
      case True
      have hC_sub_outer: "C \<subseteq> outer"
        using True hC_sub_union by (by100 blast)
      have "C = outer"
        using hCcomp hC_ne hC_sub_outer houter_sub houter_conn
        unfolding in_components_maximal by (by100 blast)
      thus ?thesis by (by100 simp)
    next
      case False
      have houterC_empty: "outer \<inter> C = {}"
      proof -
        have hsep: "inner \<inter> C = {} \<or> outer \<inter> C = {}"
        proof -
          have hdisjC: "inner \<inter> outer \<inter> C = {}"
            using hdisj by (by100 blast)
          show ?thesis
            using connectedD[OF hC_conn hinner_open houter_open hdisjC hC_sub_union]
            by (by100 blast)
        qed
        thus ?thesis using False by (by100 blast)
      qed
      have hC_sub_inner: "C \<subseteq> inner"
        using houterC_empty hC_sub_union by (by100 blast)
      have "C = inner"
        using hCcomp hC_ne hC_sub_inner hinner_sub hinner_conn
        unfolding in_components_maximal by (by100 blast)
      thus ?thesis by (by100 simp)
    qed
  qed
  have hcomponents_eq: "components (UNIV - J) = {inner, outer}"
    using hcomponents_subset hinner_comp houter_comp by (by100 blast)
  show ?thesis
    by (rule that[OF hinner_comp houter_comp hinner_bdd houter_unbdd hcomponents_eq])
qed

(** from \<S>4 Theorem 7 (geotop.tex:1002)
    LATEX VERSION: Let J be a 1-sphere in R^2. Then R^2 - J has only one bounded component. **)
theorem Theorem_GT_4_7:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "card {C. geotop_bounded_R2 C \<and>
            (\<exists>P\<in>UNIV - J.
               C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)} = 1"
  (** Moise proof (geotop.tex:1004): As in the proof of 4.3, embed J \<subset> \<bar>I\<close>
      polyhedral 2-cell with J \<inter> Fr I = {P,R}; decompose J = A\<^sub>1 \<union> A\<^sub>2 along P,R.
      Broken line B from S to Q in \<bar>I\<close> meeting Fr I only at endpoints.
      Define T, X, Y, Z, W as in Fig 4.9. Z lies in a bounded component of R\<^sup>2 - J.
      Let B\<^sub>1,\<dots>,B\<^sub>5 be the segments S-T-X-Y-W-Q, B' = \<Union>B\<^sub>i.
      P, R are limit points of different components of I - B'.
      If U is a bounded component of R\<^sup>2 - J distinct from Z's component, then
      U \<inter> B' = \<emptyset>, so Fr U cannot contain both P and R, hence Fr U \<subset> arc of J,
      contradicting Theorem 5 (every point of J is a limit point of both I and E). **)
proof -
  (** Step 1: Exists a \"bounded component\" (from Jordan_Brouwer_separation + bdd). **)
  have h_exists_bdd: "\<exists>C. geotop_bounded_R2 C \<and>
            (\<exists>P\<in>UNIV - J. C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)"
  proof -
    obtain P where hP: "P \<in> UNIV - J"
               and hI_eq: "geotop_polygon_interior J
                           = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
      using geotop_polygon_interior_is_bounded_component[OF hJ] by (by100 blast)
    have h_bdd: "bounded (geotop_polygon_interior J)"
      by (rule polygon_interior_bounded[OF hJ])
    have h_geotop_bdd: "geotop_bounded_R2 (geotop_polygon_interior J)"
      using h_bdd geotop_bounded_R2_iff_bounded by (by100 blast)
    show ?thesis using hP hI_eq h_geotop_bdd by (by100 blast)
  qed
  (** Step 2: At most one bounded component, by the Moise contradiction argument:
      any second bounded component U would give Fr U \<subset> arc of J, contradicting 2.5. **)
  \<comment> \<open>Sub-claim T4_7-A: any bounded component of UNIV - J equals geotop_polygon_interior J.\<close>
  have hT4_7_eq_polygon_interior:
    "\<forall>C. geotop_bounded_R2 C \<and>
         (\<exists>P\<in>UNIV - J. C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)
         \<longrightarrow> C = geotop_polygon_interior J"
  proof
    fix C
    show "geotop_bounded_R2 C \<and>
         (\<exists>P\<in>UNIV - J. C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)
         \<longrightarrow> C = geotop_polygon_interior J"
    proof
      assume hC: "geotop_bounded_R2 C \<and>
         (\<exists>P\<in>UNIV - J. C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)"
      obtain inner outer where hinner_comp: "inner \<in> components (UNIV - J)"
        and houter_comp: "outer \<in> components (UNIV - J)"
        and hinner_bdd: "bounded inner"
        and houter_unbdd: "\<not> bounded outer"
        and hcomponents: "components (UNIV - J) = {inner, outer}"
        by (rule geotop_1sphere_components_from_Jordan_curve[OF hJ])
      have hC_bdd: "bounded C"
        using hC geotop_bounded_R2_iff_bounded by (by100 blast)
      obtain P where hP: "P \<in> UNIV - J"
        and hC_eq: "C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
        using hC by (by100 blast)
      have hC_conn_eq: "C = connected_component_set (UNIV - J) P"
        using hC_eq geotop_component_at_UNIV_eq_connected_component_set by (by100 simp)
      have hC_comp: "C \<in> components (UNIV - J)"
        unfolding components_def using hP hC_conn_eq by (by100 blast)
      have hC_inner: "C = inner"
      proof -
        have "C = inner \<or> C = outer"
          using hC_comp hcomponents by (by100 simp)
        thus ?thesis using hC_bdd houter_unbdd by (by100 blast)
      qed
      obtain PI where hPI: "PI \<in> UNIV - J"
        and hI_eq: "geotop_polygon_interior J =
              geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) PI"
        using geotop_polygon_interior_is_bounded_component[OF hJ] by (by100 blast)
      have hI_conn_eq: "geotop_polygon_interior J =
              connected_component_set (UNIV - J) PI"
        using hI_eq geotop_component_at_UNIV_eq_connected_component_set by (by100 simp)
      have hI_comp: "geotop_polygon_interior J \<in> components (UNIV - J)"
        unfolding components_def using hPI hI_conn_eq by (by100 blast)
      have hI_bdd: "bounded (geotop_polygon_interior J)"
        by (rule polygon_interior_bounded[OF hJ])
      have hI_inner: "geotop_polygon_interior J = inner"
      proof -
        have "geotop_polygon_interior J = inner \<or> geotop_polygon_interior J = outer"
          using hI_comp hcomponents by (by100 simp)
        thus ?thesis using hI_bdd houter_unbdd by (by100 blast)
      qed
      show "C = geotop_polygon_interior J"
        using hC_inner hI_inner by (by100 simp)
    qed
  qed
  \<comment> \<open>Sub-claim T4_7-B: from T4_7-A, any two such components coincide.\<close>
  have hT4_7_unique:
    "\<forall>C1 C2.
          (geotop_bounded_R2 C1 \<and>
             (\<exists>P\<in>UNIV - J. C1 = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)) \<and>
          (geotop_bounded_R2 C2 \<and>
             (\<exists>P\<in>UNIV - J. C2 = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P))
          \<longrightarrow> C1 = C2"
    using hT4_7_eq_polygon_interior by (by100 blast)
  have h_atmost: "\<forall>C1 C2.
          (geotop_bounded_R2 C1 \<and>
             (\<exists>P\<in>UNIV - J. C1 = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)) \<and>
          (geotop_bounded_R2 C2 \<and>
             (\<exists>P\<in>UNIV - J. C2 = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P))
          \<longrightarrow> C1 = C2"
    using hT4_7_unique by (by100 blast)
  (** Conclude card = 1. **)
  define S where "S = {C. geotop_bounded_R2 C \<and>
            (\<exists>P\<in>UNIV - J.
               C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)}"
  have hS_ne: "S \<noteq> {}" using h_exists_bdd unfolding S_def by (by100 blast)
  have hS_singleton: "\<forall>x\<in>S. \<forall>y\<in>S. x = y"
    unfolding S_def using h_atmost by (by100 blast)
  obtain C where hC: "C \<in> S" using hS_ne by (by100 blast)
  have hS_eq: "S = {C}"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> S"
    thus "x \<in> {C}" using hC hS_singleton by (by100 blast)
  next
    fix x assume "x \<in> {C}"
    thus "x \<in> S" using hC by (by100 blast)
  qed
  have hS_card: "card S = 1" using hS_eq by (by100 simp)
  show "card {C. geotop_bounded_R2 C \<and>
            (\<exists>P\<in>UNIV - J.
               C = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P)} = 1"
    using hS_card unfolding S_def by (by100 simp)
qed

(** JORDAN CURVE THEOREM — combining the above
    LATEX VERSION: Let J be a topological 1-sphere in R^2. Then R^2 - J is the union of two
      disjoint connected sets I and E, such that J = Fr I = Fr E. **)
theorem Jordan_curve_theorem:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_n_sphere J (subspace_topology UNIV geotop_euclidean_topology J) 1"
  shows "\<exists>I E. UNIV - J = I \<union> E \<and> I \<inter> E = {} \<and>
           top1_connected_on I (subspace_topology UNIV geotop_euclidean_topology I) \<and>
           top1_connected_on E (subspace_topology UNIV geotop_euclidean_topology E) \<and>
           J = geotop_frontier UNIV geotop_euclidean_topology I \<and>
           J = geotop_frontier UNIV geotop_euclidean_topology E"
proof -
  obtain I E where hI_comp: "I \<in> components (UNIV - J)"
    and hE_comp: "E \<in> components (UNIV - J)"
    and hI_bdd: "bounded I"
    and hE_unbdd: "\<not> bounded E"
    and hcomponents: "components (UNIV - J) = {I, E}"
    by (rule geotop_1sphere_components_from_Jordan_curve[OF hJ])
  have hcover: "UNIV - J = I \<union> E"
  proof -
    have "\<Union>(components (UNIV - J)) = I \<union> E"
      using hcomponents by (by100 simp)
    thus ?thesis using Union_components[of "UNIV - J"] by (by100 simp)
  qed
  have hIE_ne: "I \<noteq> E"
    using hI_bdd hE_unbdd by (by100 blast)
  have hdisj: "I \<inter> E = {}"
    using components_nonoverlap[OF hI_comp hE_comp] hIE_ne by (by100 blast)
  have hI_conn_HOL: "connected I"
    using hI_comp in_components_connected by (by100 blast)
  have hE_conn_HOL: "connected E"
    using hE_comp in_components_connected by (by100 blast)
  have hI_conn: "top1_connected_on I (subspace_topology UNIV geotop_euclidean_topology I)"
    using hI_conn_HOL top1_connected_on_geotop_iff_connected[of I] by (by100 simp)
  have hE_conn: "top1_connected_on E (subspace_topology UNIV geotop_euclidean_topology E)"
    using hE_conn_HOL top1_connected_on_geotop_iff_connected[of E] by (by100 simp)
  have hI_witness:
    "\<exists>P\<in>UNIV - J. I = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
  proof -
    obtain P where hP: "P \<in> UNIV - J"
      and hI_eq: "I = connected_component_set (UNIV - J) P"
      using hI_comp unfolding components_def by (by100 blast)
    have hcomp_eq: "geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P =
        connected_component_set (UNIV - J) P"
      by (rule geotop_component_at_UNIV_eq_connected_component_set)
    have "I = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
      using hI_eq hcomp_eq by (by100 simp)
    thus ?thesis using hP by (by100 blast)
  qed
  have hE_witness:
    "\<exists>P\<in>UNIV - J. E = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
  proof -
    obtain P where hP: "P \<in> UNIV - J"
      and hE_eq: "E = connected_component_set (UNIV - J) P"
      using hE_comp unfolding components_def by (by100 blast)
    have hcomp_eq: "geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P =
        connected_component_set (UNIV - J) P"
      by (rule geotop_component_at_UNIV_eq_connected_component_set)
    have "E = geotop_component_at UNIV geotop_euclidean_topology (UNIV - J) P"
      using hE_eq hcomp_eq by (by100 simp)
    thus ?thesis using hP by (by100 blast)
  qed
  have hI_front: "J = geotop_frontier UNIV geotop_euclidean_topology I"
    by (rule Theorem_GT_4_6[OF hJ hI_witness])
  have hE_front: "J = geotop_frontier UNIV geotop_euclidean_topology E"
    by (rule Theorem_GT_4_6[OF hJ hE_witness])
  show ?thesis
    using hcover hdisj hI_conn hE_conn hI_front hE_front by (by100 blast)
qed

(** Local combinatorial helper for Theorems 4.8 and 4.9, L1. If a simplex has
    two distinct vertices, the segment on those vertices is a 1-face. **)
lemma geotop_simplex_vertices_pair_edge_face:
  fixes \<sigma> :: "(real^2) set" and V :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hv: "v \<in> V"
  assumes hw: "w \<in> V"
  assumes hvw: "v \<noteq> w"
  shows "\<exists>e. geotop_is_face e \<sigma> \<and> geotop_is_edge e \<and> v \<in> e"
proof -
  obtain m n where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hpair_sub: "{v, w} \<subseteq> V"
    using hv hw by (by100 blast)
  have hpair_fin: "finite {v, w}"
    by (by100 simp)
  have hpair_card: "card {v, w} = 2"
    using hvw by (by100 simp)
  have hpair_card_le: "card {v, w} \<le> card V"
    by (rule card_mono[OF hV_fin hpair_sub])
  have hn_ge1: "1 \<le> n"
    using hV_card hpair_card hpair_card_le by linarith
  have hm_ge1: "1 \<le> m"
    using hn_ge1 hn_le_m by linarith
  have hgp_pair: "geotop_general_position {v, w} m"
    by (rule geotop_general_position_subset[OF hgp hpair_sub])
  define e where "e = geotop_convex_hull {v, w}"
  have hedge_dim: "geotop_simplex_dim e 1"
    unfolding geotop_simplex_dim_def
  proof (intro exI conjI)
    show "finite {v, w}"
      by (rule hpair_fin)
    show "card {v, w} = 1 + 1"
      using hpair_card by (by100 simp)
    show "1 \<le> m"
      by (rule hm_ge1)
    show "geotop_general_position {v, w} m"
      by (rule hgp_pair)
    show "e = geotop_convex_hull {v, w}"
      unfolding e_def by (by100 simp)
  qed
  have hedge: "geotop_is_edge e"
    using hedge_dim unfolding geotop_is_edge_def by (by100 simp)
  have hface: "geotop_is_face e \<sigma>"
    unfolding geotop_is_face_def
  proof (intro exI conjI)
    show "geotop_simplex_vertices \<sigma> V"
      by (rule h\<sigma>V)
    show "{v, w} \<noteq> {}"
      by (by100 simp)
    show "{v, w} \<subseteq> V"
      by (rule hpair_sub)
    show "e = geotop_convex_hull {v, w}"
      unfolding e_def by (by100 simp)
  qed
  have hv_e: "v \<in> e"
  proof -
    have hv_hol: "v \<in> convex hull {v, w}"
      using hull_inc[of v "{v, w}"] by (by100 simp)
    have "geotop_convex_hull {v, w} = convex hull {v, w}"
      by (rule geotop_convex_hull_eq_HOL)
    thus ?thesis
      unfolding e_def using hv_hol by (by100 simp)
  qed
  show ?thesis
    using hface hedge hv_e by (by100 blast)
qed

(** Complex face-closure turns the preceding 1-face into an actual incident edge
    of the complex. **)
lemma geotop_complex_simplex_vertex_incident_edge:
  fixes K :: "(real^2) set set" and \<sigma> :: "(real^2) set" and V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hv: "v \<in> V"
  assumes hw: "w \<in> V"
  assumes hvw: "v \<noteq> w"
  shows "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e"
proof -
  obtain e where hface: "geotop_is_face e \<sigma>"
    and hedge: "geotop_is_edge e"
    and hv_e: "v \<in> e"
    using geotop_simplex_vertices_pair_edge_face[OF h\<sigma>V hv hw hvw]
    by (by100 blast)
  have hface_closed: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have heK: "e \<in> K"
    using hface_closed h\<sigma>K hface by (by100 blast)
  show ?thesis
    using heK hedge hv_e by (by100 blast)
qed

lemma geotop_simplex_vertices_pair_edge_face_between:
  fixes \<sigma> :: "(real^2) set" and V :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hv: "v \<in> V"
  assumes hw: "w \<in> V"
  assumes hvw: "v \<noteq> w"
  shows "\<exists>e. geotop_is_face e \<sigma> \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e"
proof -
  obtain m n where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hpair_sub: "{v, w} \<subseteq> V"
    using hv hw by (by100 blast)
  have hpair_fin: "finite {v, w}"
    by (by100 simp)
  have hpair_card: "card {v, w} = 2"
    using hvw by (by100 simp)
  have hpair_card_le: "card {v, w} \<le> card V"
    by (rule card_mono[OF hV_fin hpair_sub])
  have hn_ge1: "1 \<le> n"
    using hV_card hpair_card hpair_card_le by (by100 linarith)
  have hm_ge1: "1 \<le> m"
    using hn_ge1 hn_le_m by (by100 linarith)
  have hgp_pair: "geotop_general_position {v, w} m"
    by (rule geotop_general_position_subset[OF hgp hpair_sub])
  define e where "e = geotop_convex_hull {v, w}"
  have hedge_dim: "geotop_simplex_dim e 1"
    unfolding geotop_simplex_dim_def
  proof (intro exI conjI)
    show "finite {v, w}"
      by (rule hpair_fin)
    show "card {v, w} = 1 + 1"
      using hpair_card by (by100 simp)
    show "1 \<le> m"
      by (rule hm_ge1)
    show "geotop_general_position {v, w} m"
      by (rule hgp_pair)
    show "e = geotop_convex_hull {v, w}"
      unfolding e_def by (by100 simp)
  qed
  have hedge: "geotop_is_edge e"
    using hedge_dim unfolding geotop_is_edge_def by (by100 simp)
  have hface: "geotop_is_face e \<sigma>"
    unfolding geotop_is_face_def
  proof (intro exI conjI)
    show "geotop_simplex_vertices \<sigma> V"
      by (rule h\<sigma>V)
    show "{v, w} \<noteq> {}"
      by (by100 simp)
    show "{v, w} \<subseteq> V"
      by (rule hpair_sub)
    show "e = geotop_convex_hull {v, w}"
      unfolding e_def by (by100 simp)
  qed
  have hv_e: "v \<in> e"
  proof -
    have "v \<in> convex hull {v, w}"
      using hull_inc[of v "{v, w}"] by (by100 simp)
    moreover have "geotop_convex_hull {v, w} = convex hull {v, w}"
      by (rule geotop_convex_hull_eq_HOL)
    ultimately show ?thesis
      unfolding e_def by (by100 simp)
  qed
  have hw_e: "w \<in> e"
  proof -
    have "w \<in> convex hull {v, w}"
      using hull_inc[of w "{v, w}"] by (by100 simp)
    moreover have "geotop_convex_hull {v, w} = convex hull {v, w}"
      by (rule geotop_convex_hull_eq_HOL)
    ultimately show ?thesis
      unfolding e_def by (by100 simp)
  qed
  show ?thesis
    using hface hedge hv_e hw_e by (by100 blast)
qed

lemma geotop_complex_simplex_vertices_incident_edge_between:
  fixes K :: "(real^2) set set" and \<sigma> :: "(real^2) set" and V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hv: "v \<in> V"
  assumes hw: "w \<in> V"
  assumes hvw: "v \<noteq> w"
  shows "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e \<and> w \<in> e"
proof -
  obtain e where hface: "geotop_is_face e \<sigma>"
    and hedge: "geotop_is_edge e"
    and hv_e: "v \<in> e"
    and hw_e: "w \<in> e"
    using geotop_simplex_vertices_pair_edge_face_between[OF h\<sigma>V hv hw hvw]
    by (by100 blast)
  have hface_closed: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have heK: "e \<in> K"
    using hface_closed h\<sigma>K hface by (by100 blast)
  show ?thesis
    using heK hedge hv_e hw_e by (by100 blast)
qed

(** If no edge of \<open>K\<close> contains \<open>v\<close>, then any simplex of \<open>K\<close> that has
    \<open>v\<close> as a vertex has \<open>v\<close> as its only vertex. **)
lemma geotop_complex_no_incident_edge_simplex_vertices_singleton:
  fixes K :: "(real^2) set set" and \<sigma> :: "(real^2) set" and V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hno_edge: "\<not> (\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e)"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hv: "v \<in> V"
  shows "V = {v}"
proof -
  have hV_sub: "V \<subseteq> {v}"
  proof
    fix w assume hw: "w \<in> V"
    show "w \<in> {v}"
    proof (rule ccontr)
      assume hw_not: "w \<notin> {v}"
      have hvw: "v \<noteq> w"
        using hw_not by (by100 simp)
      have "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e"
        by (rule geotop_complex_simplex_vertex_incident_edge
            [OF hK h\<sigma>K h\<sigma>V hv hw hvw])
      thus False
        using hno_edge by (by100 blast)
    qed
  qed
  show ?thesis
    using hV_sub hv by (by100 blast)
qed

(** If \<open>{v}\<close> is a vertex simplex of a complex and another simplex contains
    \<open>v\<close> as a point, then \<open>v\<close> is among the vertices of that simplex. **)
lemma geotop_complex_singleton_point_is_simplex_vertex:
  fixes K :: "(real^2) set set" and \<tau> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes hv\<tau>: "v \<in> \<tau>"
  shows "\<exists>V. geotop_simplex_vertices \<tau> V \<and> v \<in> V"
proof -
  have hnonempty: "{v} \<inter> \<tau> \<noteq> {}"
    using hv\<tau> by (by100 simp)
  have hface_int: "geotop_is_face ({v} \<inter> \<tau>) \<tau>"
    using hK hvK h\<tau>K hnonempty unfolding geotop_is_complex_def by (by100 blast)
  have hface: "geotop_is_face {v} \<tau>"
    using hface_int hv\<tau> by (by100 simp)
  obtain V W where h\<tau>V: "geotop_simplex_vertices \<tau> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and hW_hull: "{v} = geotop_convex_hull W"
    using hface unfolding geotop_is_face_def by (by100 blast)
  obtain w where hw: "w \<in> W"
    using hW_ne by (by100 blast)
  have hw_hull: "w \<in> geotop_convex_hull W"
  proof -
    have "w \<in> convex hull W"
      using hw hull_inc[of w W] by (by100 simp)
    moreover have "geotop_convex_hull W = convex hull W"
      by (rule geotop_convex_hull_eq_HOL)
    ultimately show ?thesis by (by100 simp)
  qed
  have hw_v: "w = v"
    using hW_hull hw_hull by (by100 blast)
  have hvV: "v \<in> V"
    using hw hw_v hW_sub by (by100 blast)
  show ?thesis
    using h\<tau>V hvV by (by100 blast)
qed

(** Hence a no-incident-edge complex has an isolated vertex simplex: every
    simplex containing \<open>v\<close> is the singleton \<open>{v}\<close>. **)
lemma geotop_complex_no_incident_edge_simplex_containing_vertex_eq_singleton:
  fixes K :: "(real^2) set set" and \<tau> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hno_edge: "\<not> (\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e)"
  assumes hvK: "{v} \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes hv\<tau>: "v \<in> \<tau>"
  shows "\<tau> = {v}"
proof -
  obtain V where h\<tau>V: "geotop_simplex_vertices \<tau> V"
    and hvV: "v \<in> V"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK h\<tau>K hv\<tau>]
    by (by100 blast)
  have hV_eq: "V = {v}"
    by (rule geotop_complex_no_incident_edge_simplex_vertices_singleton
        [OF hK hno_edge h\<tau>K h\<tau>V hvV])
  obtain m n where h\<tau>_eq: "\<tau> = geotop_convex_hull V"
    using h\<tau>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hsing_hull: "geotop_convex_hull {v} = {v}"
    using geotop_convex_hull_eq_HOL[of "{v}"] by (by100 simp)
  show ?thesis
    using h\<tau>_eq hV_eq hsing_hull by (by100 simp)
qed

(** Moise 4.8 L1, combinatorial half: if a complex vertex has no incident edge,
    then it is isolated in the polyhedron. **)
lemma geotop_complex_no_incident_edge_vertex_open_singleton:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hno_edge: "\<not> (\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e)"
  shows "{v} \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
proof -
  have hvK: "{v} \<in> K"
    using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
  have hlocal_fin:
    "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]]])
  have hlocal_v: "\<exists>U. open U \<and> {v} \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule bspec[OF hlocal_fin hvK])
  obtain U where hU_open: "open U"
    and hvU: "{v} \<subseteq> U"
    and hU_fin: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    using hlocal_v by (elim exE conjE)
  let ?F = "{\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
  let ?Bad = "{\<tau>\<in>?F. v \<notin> \<tau>}"
  have hBad_fin: "finite ?Bad"
  proof -
    have "?Bad \<subseteq> ?F"
      by (by100 blast)
    show ?thesis
      by (rule finite_subset[OF \<open>?Bad \<subseteq> ?F\<close> hU_fin])
  qed
  have hBad_closed: "\<forall>\<tau>\<in>?Bad. closed \<tau>"
  proof
    fix \<tau> assume h\<tau>: "\<tau> \<in> ?Bad"
    have h\<tau>K: "\<tau> \<in> K"
      using h\<tau> by (by100 simp)
    show "closed \<tau>"
      by (rule geotop_complex_simplex_closed[OF hK h\<tau>K])
  qed
  have hB_closed: "closed (\<Union>?Bad)"
    by (rule closed_Union[OF hBad_fin hBad_closed])
  have hv_not_B: "v \<notin> \<Union>?Bad"
    by (by100 simp)
  define W where "W = U - \<Union>?Bad"
  have hW_open_HOL: "open W"
    unfolding W_def by (rule open_Diff[OF hU_open hB_closed])
  have hvW: "v \<in> W"
    unfolding W_def using hvU hv_not_B by (by100 simp)
  have hpoly_inter_W: "geotop_polyhedron K \<inter> W = {v}"
  proof
    show "geotop_polyhedron K \<inter> W \<subseteq> {v}"
    proof
      fix x assume hx: "x \<in> geotop_polyhedron K \<inter> W"
      have hx_poly: "x \<in> geotop_polyhedron K"
        using hx by (by100 simp)
      have hxW: "x \<in> W"
        using hx by (by100 simp)
      have hxU: "x \<in> U"
        using hxW unfolding W_def by (by100 simp)
      obtain \<tau> where h\<tau>K: "\<tau> \<in> K" and hx\<tau>: "x \<in> \<tau>"
        using hx_poly unfolding geotop_polyhedron_def by (by100 blast)
      have h\<tau>F: "\<tau> \<in> ?F"
        using h\<tau>K hx\<tau> hxU by (by100 blast)
      have hv\<tau>: "v \<in> \<tau>"
      proof (rule ccontr)
        assume hv_not: "v \<notin> \<tau>"
        have h\<tau>Bad: "\<tau> \<in> ?Bad"
          using h\<tau>F hv_not by (by100 simp)
        have "x \<in> \<Union>?Bad"
          using h\<tau>Bad hx\<tau> by (by100 blast)
        thus False
          using hxW unfolding W_def by (by100 simp)
      qed
      have h\<tau>_eq: "\<tau> = {v}"
        by (rule geotop_complex_no_incident_edge_simplex_containing_vertex_eq_singleton
            [OF hK hno_edge hvK h\<tau>K hv\<tau>])
      show "x \<in> {v}"
        using hx\<tau> h\<tau>_eq by (by100 simp)
    qed
    show "{v} \<subseteq> geotop_polyhedron K \<inter> W"
    proof
      fix x assume hx: "x \<in> {v}"
      have hxv: "x = v"
        using hx by (by100 simp)
      have hv_poly: "v \<in> geotop_polyhedron K"
        using hvK unfolding geotop_polyhedron_def by (by100 blast)
      show "x \<in> geotop_polyhedron K \<inter> W"
        using hxv hv_poly hvW by (by100 simp)
    qed
  qed
  have hW_top: "W \<in> geotop_euclidean_topology"
    by (metis hW_open_HOL geotop_euclidean_topology_eq_open_sets
        mem_Collect_eq top1_open_sets_def)
  show ?thesis
    unfolding subspace_topology_def
    using hW_top hpoly_inter_W by (by100 blast)
qed

(** Moise 4.8 L2, combinatorial support: an edge face of a simplex of
    dimension at least two is contained in a 2-face of that simplex. **)
lemma geotop_is_face_imp_subset:
  fixes \<tau> \<sigma> :: "(real^2) set"
  assumes hface: "geotop_is_face \<tau> \<sigma>"
  shows "\<tau> \<subseteq> \<sigma>"
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_sub: "W \<subseteq> V"
    and h\<tau>_eq: "\<tau> = geotop_convex_hull W"
    using hface unfolding geotop_is_face_def by (by100 blast)
  obtain m n where h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hmono: "convex hull W \<subseteq> convex hull V"
    by (rule hull_mono[OF hW_sub])
  show ?thesis
    using hmono h\<tau>_eq h\<sigma>_eq geotop_convex_hull_eq_HOL[of W]
      geotop_convex_hull_eq_HOL[of V]
    by (by100 simp)
qed

lemma geotop_complex_subset_simplex_face:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes hsub: "\<tau> \<subseteq> \<sigma>"
  shows "geotop_is_face \<tau> \<sigma>"
proof -
  have h\<tau>_ne: "\<tau> \<noteq> {}"
    by (rule geotop_complex_simplex_nonempty[OF hK h\<tau>K])
  have hcap: "\<tau> \<inter> \<sigma> = \<tau>"
    using hsub by (by100 blast)
  have hcap_ne: "\<tau> \<inter> \<sigma> \<noteq> {}"
    using hcap h\<tau>_ne by (by100 simp)
  have hK_inter: "\<forall>\<sigma>'\<in>K. \<forall>\<tau>'\<in>K. \<sigma>' \<inter> \<tau>' \<noteq> {} \<longrightarrow>
                  geotop_is_face (\<sigma>' \<inter> \<tau>') \<sigma>' \<and> geotop_is_face (\<sigma>' \<inter> \<tau>') \<tau>'"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have hface_cap: "geotop_is_face (\<tau> \<inter> \<sigma>) \<sigma>"
    using hK_inter h\<tau>K h\<sigma>K hcap_ne by (by100 blast)
  show ?thesis
    using hface_cap hcap by (by100 simp)
qed

lemma geotop_face_witness_simplex_vertices:
  fixes \<tau> \<sigma> :: "(real^2) set"
  assumes hface: "geotop_is_face \<tau> \<sigma>"
  obtains V W where "geotop_simplex_vertices \<sigma> V"
    and "W \<noteq> {}" and "W \<subseteq> V"
    and "\<tau> = geotop_convex_hull W"
    and "geotop_simplex_vertices \<tau> W"
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}" and hW_sub: "W \<subseteq> V"
    and h\<tau>_eq: "\<tau> = geotop_convex_hull W"
    using hface unfolding geotop_is_face_def by (by100 blast)
  obtain m n where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hW_fin: "finite W"
    using hW_sub hV_fin by (rule finite_subset)
  have hW_card_pos: "0 < card W"
    using hW_fin hW_ne by (by100 force)
  have hW_card_eq: "card W = (card W - 1) + 1"
    using hW_card_pos by (by100 simp)
  have hW_card_le: "card W \<le> card V"
    by (rule card_mono[OF hV_fin hW_sub])
  have hW_dim_le_m: "card W - 1 \<le> m"
    using hW_card_le hV_card hn_le_m by (by100 linarith)
  have hgp_W: "geotop_general_position W m"
    by (rule geotop_general_position_subset[OF hgp hW_sub])
  have h\<tau>W: "geotop_simplex_vertices \<tau> W"
    unfolding geotop_simplex_vertices_def
    using hW_fin hW_card_eq hW_dim_le_m hgp_W h\<tau>_eq by (by100 blast)
  show ?thesis
    by (rule that[OF h\<sigma>V hW_ne hW_sub h\<tau>_eq h\<tau>W])
qed

lemma geotop_is_face_trans:
  fixes \<rho> \<tau> \<sigma> :: "(real^2) set"
  assumes h\<rho>\<tau>: "geotop_is_face \<rho> \<tau>"
  assumes h\<tau>\<sigma>: "geotop_is_face \<tau> \<sigma>"
  shows "geotop_is_face \<rho> \<sigma>"
proof -
  obtain V\<^sub>\<tau> W\<^sub>\<rho> where h\<tau>V: "geotop_simplex_vertices \<tau> V\<^sub>\<tau>"
    and hW\<^sub>\<rho>_ne: "W\<^sub>\<rho> \<noteq> {}"
    and hW\<^sub>\<rho>_sub: "W\<^sub>\<rho> \<subseteq> V\<^sub>\<tau>"
    and h\<rho>_eq: "\<rho> = geotop_convex_hull W\<^sub>\<rho>"
    and h\<rho>W: "geotop_simplex_vertices \<rho> W\<^sub>\<rho>"
    by (rule geotop_face_witness_simplex_vertices[OF h\<rho>\<tau>])
  obtain V\<^sub>\<sigma> W\<^sub>\<tau> where h\<sigma>V: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>"
    and hW\<^sub>\<tau>_ne: "W\<^sub>\<tau> \<noteq> {}"
    and hW\<^sub>\<tau>_sub: "W\<^sub>\<tau> \<subseteq> V\<^sub>\<sigma>"
    and h\<tau>_eq: "\<tau> = geotop_convex_hull W\<^sub>\<tau>"
    and h\<tau>W: "geotop_simplex_vertices \<tau> W\<^sub>\<tau>"
    by (rule geotop_face_witness_simplex_vertices[OF h\<tau>\<sigma>])
  have hV_eq: "V\<^sub>\<tau> = W\<^sub>\<tau>"
    by (rule geotop_simplex_vertices_unique[OF h\<tau>V h\<tau>W])
  have hW\<^sub>\<rho>_sub_\<sigma>: "W\<^sub>\<rho> \<subseteq> V\<^sub>\<sigma>"
    using hW\<^sub>\<rho>_sub hV_eq hW\<^sub>\<tau>_sub by (by100 blast)
  show ?thesis
    unfolding geotop_is_face_def
    using h\<sigma>V hW\<^sub>\<rho>_ne hW\<^sub>\<rho>_sub_\<sigma> h\<rho>_eq by (by100 blast)
qed

lemma geotop_simplex_dim_le_2_R2:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> n"
  shows "n \<le> 2"
proof -
  obtain V m where hVfin: "finite V"
    and hVcard: "card V = n + 1"
    and hnm: "n \<le> m"
    and hVgp: "geotop_general_position V m"
    and h\<sigma>eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma> unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    unfolding geotop_simplex_vertices_def
    using hVfin hVcard hnm hVgp h\<sigma>eq by (by100 blast)
  have hVai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF h\<sigma>V])
  have h_aff_V: "aff_dim V = int (card V) - 1"
    using hVai affine_independent_iff_card hVfin by (by100 blast)
  have h_aff_le: "aff_dim V \<le> int (DIM(real^2))"
    by (rule aff_dim_le_DIM)
  have hDIM: "DIM(real^2) = 2"
    by (by100 simp)
  have "int n \<le> (2::int)"
    using h_aff_V h_aff_le hDIM hVcard by (by100 linarith)
  show ?thesis
    using \<open>int n \<le> (2::int)\<close> by (by100 linarith)
qed

lemma geotop_star_subset_complex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_star K v \<subseteq> K"
proof
  fix \<tau> assume h\<tau>: "\<tau> \<in> geotop_star K v"
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    and hcase: "geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>"
    using h\<tau> unfolding geotop_star_def by (by100 blast)
  have hfaces: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  show "\<tau> \<in> K"
    using hfaces h\<sigma>K hcase by (by100 blast)
qed

lemma geotop_link_subset_complex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_link K v \<subseteq> K"
proof -
  have hstar: "geotop_star K v \<subseteq> K"
    by (rule geotop_star_subset_complex[OF hK])
  show ?thesis
    unfolding geotop_link_def using hstar by (by100 blast)
qed

lemma geotop_star_is_complex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_is_complex (geotop_star K v)"
proof -
  let ?S = "geotop_star K v"
  have hS_sub_K: "?S \<subseteq> K"
    by (rule geotop_star_subset_complex[OF hK])
  have hK_simplex: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
    by (rule conjunct1[OF hK[unfolded geotop_is_complex_def]])
  have hK_faces: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    by (rule conjunct1[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]])
  have hK_inter: "\<forall>\<sigma>\<in>K. \<forall>\<tau>\<in>K. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
      geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]]])
  have hK_local: "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and>
      finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]]])
  have hsimplex: "\<forall>\<sigma>\<in>?S. geotop_is_simplex \<sigma>"
    using hS_sub_K hK_simplex by (by100 blast)
  have hfaces: "\<forall>\<sigma>\<in>?S. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> ?S"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau> assume h\<sigma>S: "\<sigma> \<in> ?S" and h\<tau>\<sigma>: "geotop_is_face \<tau> \<sigma>"
    obtain \<omega> where h\<omega>K: "\<omega> \<in> K"
      and hv\<omega>: "v \<in> \<omega>"
      and h\<sigma>\<omega>_case: "geotop_is_face \<sigma> \<omega> \<or> \<sigma> = \<omega>"
      using h\<sigma>S unfolding geotop_star_def by (by100 blast)
    have h\<tau>\<omega>: "geotop_is_face \<tau> \<omega>"
    proof (rule disjE[OF h\<sigma>\<omega>_case])
      assume h\<sigma>\<omega>: "geotop_is_face \<sigma> \<omega>"
      show ?thesis
        by (rule geotop_is_face_trans[OF h\<tau>\<sigma> h\<sigma>\<omega>])
    next
      assume h\<sigma>_eq: "\<sigma> = \<omega>"
      show ?thesis
        using h\<tau>\<sigma> h\<sigma>_eq by (by100 simp)
    qed
    show "\<tau> \<in> ?S"
      unfolding geotop_star_def using h\<omega>K hv\<omega> h\<tau>\<omega> by (by100 blast)
  qed
  have hinter: "\<forall>\<sigma>\<in>?S. \<forall>\<tau>\<in>?S. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
      geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using hS_sub_K hK_inter by (by100 blast)
  have hlocal: "\<forall>\<sigma>\<in>?S. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and>
      finite {\<tau>\<in>?S. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma> assume h\<sigma>S: "\<sigma> \<in> ?S"
    have h\<sigma>K: "\<sigma> \<in> K"
      using hS_sub_K h\<sigma>S by (by100 blast)
    have hlocal_\<sigma>: "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and>
        finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      by (rule bspec[OF hK_local h\<sigma>K])
    obtain U where hUopen: "open U"
      and h\<sigma>U: "\<sigma> \<subseteq> U"
      and hfin_K: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using hlocal_\<sigma> by (elim exE conjE)
    have hsub_fin: "{\<tau>\<in>?S. \<tau> \<inter> U \<noteq> {}} \<subseteq> {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using hS_sub_K by (by100 blast)
    have hfin_S: "finite {\<tau>\<in>?S. \<tau> \<inter> U \<noteq> {}}"
      by (rule finite_subset[OF hsub_fin hfin_K])
    show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>?S. \<tau> \<inter> U \<noteq> {}}"
      using hUopen h\<sigma>U hfin_S by (by100 blast)
  qed
  show ?thesis
    unfolding geotop_is_complex_def using hsimplex hfaces hinter hlocal by (by100 blast)
qed

lemma geotop_link_is_complex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_is_complex (geotop_link K v)"
proof -
  let ?S = "geotop_star K v"
  let ?L = "geotop_link K v"
  have hS_complex: "geotop_is_complex ?S"
    by (rule geotop_star_is_complex[OF hK])
  have hL_sub_S: "?L \<subseteq> ?S"
    unfolding geotop_link_def by (by100 blast)
  have hS_simplex: "\<forall>\<sigma>\<in>?S. geotop_is_simplex \<sigma>"
    by (rule conjunct1[OF hS_complex[unfolded geotop_is_complex_def]])
  have hS_faces: "\<forall>\<sigma>\<in>?S. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> ?S"
    by (rule conjunct1[OF conjunct2[OF hS_complex[unfolded geotop_is_complex_def]]])
  have hS_inter: "\<forall>\<sigma>\<in>?S. \<forall>\<tau>\<in>?S. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
      geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    by (rule conjunct1[OF conjunct2[OF conjunct2[OF hS_complex[unfolded geotop_is_complex_def]]]])
  have hS_local: "\<forall>\<sigma>\<in>?S. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and>
      finite {\<tau>\<in>?S. \<tau> \<inter> U \<noteq> {}}"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hS_complex[unfolded geotop_is_complex_def]]]])
  have hsimplex: "\<forall>\<sigma>\<in>?L. geotop_is_simplex \<sigma>"
    using hL_sub_S hS_simplex by (by100 blast)
  have hfaces: "\<forall>\<sigma>\<in>?L. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> ?L"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau> assume h\<sigma>L: "\<sigma> \<in> ?L" and h\<tau>\<sigma>: "geotop_is_face \<tau> \<sigma>"
    have h\<sigma>S: "\<sigma> \<in> ?S"
      using hL_sub_S h\<sigma>L by (by100 blast)
    have hv_not_\<sigma>: "v \<notin> \<sigma>"
      using h\<sigma>L unfolding geotop_link_def by (by100 blast)
    have h\<tau>S: "\<tau> \<in> ?S"
      using hS_faces h\<sigma>S h\<tau>\<sigma> by (by100 blast)
    have h\<tau>sub\<sigma>: "\<tau> \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset[OF h\<tau>\<sigma>])
    have hv_not_\<tau>: "v \<notin> \<tau>"
      using hv_not_\<sigma> h\<tau>sub\<sigma> by (by100 blast)
    show "\<tau> \<in> ?L"
      unfolding geotop_link_def using h\<tau>S hv_not_\<tau> by (by100 blast)
  qed
  have hinter: "\<forall>\<sigma>\<in>?L. \<forall>\<tau>\<in>?L. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
      geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using hL_sub_S hS_inter by (by100 blast)
  have hlocal: "\<forall>\<sigma>\<in>?L. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and>
      finite {\<tau>\<in>?L. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma> assume h\<sigma>L: "\<sigma> \<in> ?L"
    have h\<sigma>S: "\<sigma> \<in> ?S"
      using hL_sub_S h\<sigma>L by (by100 blast)
    have hlocal_\<sigma>: "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and>
        finite {\<tau>\<in>?S. \<tau> \<inter> U \<noteq> {}}"
      by (rule bspec[OF hS_local h\<sigma>S])
    obtain U where hUopen: "open U"
      and h\<sigma>U: "\<sigma> \<subseteq> U"
      and hfin_S: "finite {\<tau>\<in>?S. \<tau> \<inter> U \<noteq> {}}"
      using hlocal_\<sigma> by (elim exE conjE)
    have hsub_fin: "{\<tau>\<in>?L. \<tau> \<inter> U \<noteq> {}} \<subseteq> {\<tau>\<in>?S. \<tau> \<inter> U \<noteq> {}}"
      using hL_sub_S by (by100 blast)
    have hfin_L: "finite {\<tau>\<in>?L. \<tau> \<inter> U \<noteq> {}}"
      by (rule finite_subset[OF hsub_fin hfin_S])
    show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>?L. \<tau> \<inter> U \<noteq> {}}"
      using hUopen h\<sigma>U hfin_L by (by100 blast)
  qed
  show ?thesis
    unfolding geotop_is_complex_def using hsimplex hfaces hinter hlocal by (by100 blast)
qed

lemma geotop_link_complex_is_1dim_R2:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_complex_is_1dim (geotop_link K v)"
proof -
  have hlink_sub_K: "geotop_link K v \<subseteq> K"
    by (rule geotop_link_subset_complex[OF hK])
  have hK_simplex: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
    by (rule conjunct1[OF hK[unfolded geotop_is_complex_def]])
  show ?thesis
    unfolding geotop_complex_is_1dim_def
  proof
    fix \<tau> assume h\<tau>L: "\<tau> \<in> geotop_link K v"
    have h\<tau>K: "\<tau> \<in> K"
      using hlink_sub_K h\<tau>L by (by100 blast)
    have h\<tau>simplex: "geotop_is_simplex \<tau>"
      using hK_simplex h\<tau>K by (by100 blast)
    obtain n\<^sub>\<tau> where h\<tau>dim: "geotop_simplex_dim \<tau> n\<^sub>\<tau>"
      using h\<tau>simplex unfolding geotop_is_simplex_def geotop_simplex_dim_def
      by (by100 blast)
    obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
      and hv\<sigma>: "v \<in> \<sigma>"
      and h\<tau>\<sigma>_case: "geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>"
      using h\<tau>L unfolding geotop_link_def geotop_star_def by (by100 blast)
    have hv_not_\<tau>: "v \<notin> \<tau>"
      using h\<tau>L unfolding geotop_link_def by (by100 blast)
    have h\<tau>\<sigma>: "geotop_is_face \<tau> \<sigma>"
    proof (rule disjE[OF h\<tau>\<sigma>_case])
      assume "geotop_is_face \<tau> \<sigma>"
      thus ?thesis .
    next
      assume h_eq: "\<tau> = \<sigma>"
      have False
        using hv\<sigma> hv_not_\<tau> h_eq by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    have h\<tau>sub\<sigma>: "\<tau> \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset[OF h\<tau>\<sigma>])
    have hproper: "\<tau> \<subset> \<sigma>"
    proof -
      have "\<tau> \<noteq> \<sigma>"
        using hv\<sigma> hv_not_\<tau> by (by100 blast)
      show ?thesis
        using h\<tau>sub\<sigma> \<open>\<tau> \<noteq> \<sigma>\<close> by (by100 blast)
    qed
    have h\<sigma>simplex: "geotop_is_simplex \<sigma>"
      using hK_simplex h\<sigma>K by (by100 blast)
    obtain n\<^sub>\<sigma> where h\<sigma>dim: "geotop_simplex_dim \<sigma> n\<^sub>\<sigma>"
      using h\<sigma>simplex unfolding geotop_is_simplex_def geotop_simplex_dim_def
      by (by100 blast)
    have hdim_lt: "n\<^sub>\<tau> < n\<^sub>\<sigma>"
      by (rule geotop_complex_proper_subset_dim_less
          [OF hK h\<tau>K h\<sigma>K hproper h\<tau>dim h\<sigma>dim])
    have h\<sigma>le2: "n\<^sub>\<sigma> \<le> 2"
      by (rule geotop_simplex_dim_le_2_R2[OF h\<sigma>dim])
    have "n\<^sub>\<tau> \<le> 1"
      using hdim_lt h\<sigma>le2 by (by100 linarith)
    show "\<exists>n\<le>1. geotop_simplex_dim \<tau> n"
      using h\<tau>dim \<open>n\<^sub>\<tau> \<le> 1\<close> by (by100 blast)
  qed
qed

lemma geotop_complex_1dim_imp_linear_graph_dev34:
  assumes hK: "geotop_is_complex K"
  assumes hK1: "geotop_complex_is_1dim K"
  shows "geotop_is_linear_graph K"
proof -
  have hdim: "\<forall>\<sigma>\<in>K. \<exists>i\<le>1. geotop_simplex_dim \<sigma> i"
    using hK1 unfolding geotop_complex_is_1dim_def by (by100 simp)
  show ?thesis
    unfolding geotop_is_linear_graph_def using hK hdim by (by100 simp)
qed

lemma geotop_linear_graph_imp_complex_1dim_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_linear_graph K"
  shows "geotop_is_complex K \<and> geotop_complex_is_1dim K"
proof -
  have hK_complex: "geotop_is_complex K"
    using hK unfolding geotop_is_linear_graph_def by (by100 blast)
  have hdim: "\<forall>\<sigma>\<in>K. \<exists>i\<le>1. geotop_simplex_dim \<sigma> i"
    using hK unfolding geotop_is_linear_graph_def by (by100 blast)
  have hK_1dim: "geotop_complex_is_1dim K"
    unfolding geotop_complex_is_1dim_def using hdim by (by100 simp)
  show ?thesis
    using hK_complex hK_1dim by (by100 blast)
qed

lemma geotop_finite_complex_vertices_finite_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hfin: "finite K"
  shows "finite (geotop_complex_vertices K)"
proof -
  have hverts_eq: "geotop_complex_vertices K = {v. {v} \<in> K}"
    by (rule geotop_complex_vertices_eq_0_simplexes[OF hK])
  define S where "S = {\<sigma>\<in>K. \<exists>v. \<sigma> = {v}}"
  have hS_fin: "finite S"
    unfolding S_def using hfin by (by100 simp)
  have hS_each_fin: "\<forall>\<sigma>\<in>S. finite \<sigma>"
    unfolding S_def by (by100 blast)
  have hUnion_fin: "finite (\<Union>S)"
    by (rule finite_Union[OF hS_fin hS_each_fin])
  have hUnion_eq: "\<Union>S = {v. {v} \<in> K}"
  proof
    show "\<Union>S \<subseteq> {v. {v} \<in> K}"
    proof
      fix x
      assume hx: "x \<in> \<Union>S"
      obtain \<sigma> where h\<sigma>S: "\<sigma> \<in> S" and hx\<sigma>: "x \<in> \<sigma>"
        using hx by (by100 blast)
      obtain v where h\<sigma>eq: "\<sigma> = {v}"
        using h\<sigma>S unfolding S_def by (by100 blast)
      have "{x} \<in> K"
        using h\<sigma>S hx\<sigma> h\<sigma>eq unfolding S_def by (by100 blast)
      show "x \<in> {v. {v} \<in> K}"
        using \<open>{x} \<in> K\<close> by (by100 simp)
    qed
    show "{v. {v} \<in> K} \<subseteq> \<Union>S"
    proof
      fix x
      assume hx: "x \<in> {v. {v} \<in> K}"
      have hxK: "{x} \<in> K"
        using hx by (by100 simp)
      have "{x} \<in> S"
        unfolding S_def using hxK by (by100 blast)
      show "x \<in> \<Union>S"
        using \<open>{x} \<in> S\<close> by (by100 blast)
    qed
  qed
  show ?thesis
    using hverts_eq hUnion_eq hUnion_fin by (by100 simp)
qed

lemma geotop_simplex_face_complex_finite_R2:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_is_simplex \<sigma>"
  shows "finite {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
proof -
  have hfaces_fin: "finite {\<tau>. geotop_is_face \<tau> \<sigma>}"
    by (rule geotop_simplex_faces_finite[OF h\<sigma>])
  have "{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} =
        {\<tau>. geotop_is_face \<tau> \<sigma>} \<union> {\<sigma>}"
    by (by100 blast)
  thus ?thesis
    using hfaces_fin by (by100 simp)
qed

lemma geotop_simplex_dim_face_complex_finite_R2:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> n"
  shows "finite {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
proof -
  have hsimplex: "geotop_is_simplex \<sigma>"
    by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>])
  show ?thesis
    by (rule geotop_simplex_face_complex_finite_R2[OF hsimplex])
qed

lemma geotop_is_face_imp_HOL_face_of_R2:
  fixes \<tau> \<sigma> :: "(real^2) set"
  assumes hface: "geotop_is_face \<tau> \<sigma>"
  shows "\<tau> face_of \<sigma>"
proof -
  obtain V W where hV: "geotop_simplex_vertices \<sigma> V"
    and hWsub: "W \<subseteq> V"
    and h\<tau>eq: "\<tau> = geotop_convex_hull W"
    using hface unfolding geotop_is_face_def by (by100 blast)
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF hV])
  have h\<sigma>HOL: "\<sigma> = convex hull V"
  proof -
    have "\<sigma> = geotop_convex_hull V"
      using hV unfolding geotop_simplex_vertices_def by (by100 blast)
    thus ?thesis
      using geotop_convex_hull_eq_HOL[of V] by (by100 simp)
  qed
  have h\<tau>HOL: "\<tau> = convex hull W"
    using h\<tau>eq geotop_convex_hull_eq_HOL[of W] by (by100 simp)
  have "\<tau> face_of (convex hull V)"
    using face_of_convex_hull_affine_independent[OF hV_ai, of \<tau>] hWsub h\<tau>HOL
    by (by100 blast)
  thus ?thesis
    using h\<sigma>HOL by (by100 simp)
qed

lemma geotop_HOL_face_of_simplex_imp_geotop_is_face_R2:
  fixes F \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_is_simplex \<sigma>"
  assumes hface: "F face_of \<sigma>"
  assumes hFne: "F \<noteq> {}"
  shows "geotop_is_face F \<sigma>"
proof -
  obtain V m n where hVfin: "finite V" and hVcard: "card V = n + 1"
    and hnm: "n \<le> m" and hVgp: "geotop_general_position V m"
    and h\<sigma>eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma> unfolding geotop_is_simplex_def by (by100 blast)
  have h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    unfolding geotop_simplex_vertices_def
    using hVfin hVcard hnm hVgp h\<sigma>eq by (by100 blast)
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF h\<sigma>V])
  have h\<sigma>HOL: "\<sigma> = convex hull V"
    using h\<sigma>eq geotop_convex_hull_eq_HOL[of V] by (by100 simp)
  obtain W where hWsub: "W \<subseteq> V" and hFHOL: "F = convex hull W"
    using face_of_convex_hull_affine_independent[OF hV_ai, of F] hface h\<sigma>HOL
    by (by100 metis)
  have hWne: "W \<noteq> {}"
  proof
    assume "W = {}"
    hence "F = {}"
      using hFHOL by (by100 simp)
    thus False
      using hFne by (by100 blast)
  qed
  have hFgeo: "F = geotop_convex_hull W"
    using hFHOL geotop_convex_hull_eq_HOL[of W] by (by100 simp)
  show ?thesis
    unfolding geotop_is_face_def using h\<sigma>V hWne hWsub hFgeo by (by100 blast)
qed

lemma geotop_simplex_face_complex_is_complex_R2:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_is_simplex \<sigma>"
  shows "geotop_is_complex {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
proof -
  let ?L = "{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  have hfinite: "finite ?L"
    by (rule geotop_simplex_face_complex_finite_R2[OF h\<sigma>])
  have h\<sigma>conv: "convex \<sigma>"
    by (rule GeoTopBase0.geotop_simplex_is_convex[OF h\<sigma>])
  have hsimplex: "\<forall>\<tau>\<in>?L. geotop_is_simplex \<tau>"
  proof
    fix \<tau> assume h\<tau>L: "\<tau> \<in> ?L"
    have hcase: "geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>"
      using h\<tau>L by (by100 blast)
    show "geotop_is_simplex \<tau>"
    proof (rule disjE[OF hcase])
      assume hface: "geotop_is_face \<tau> \<sigma>"
      obtain V W where h\<tau>W: "geotop_simplex_vertices \<tau> W"
        by (rule geotop_face_witness_simplex_vertices[OF hface])
      show ?thesis
        using h\<tau>W unfolding geotop_is_simplex_def geotop_simplex_vertices_def
        by (by100 blast)
    next
      assume "\<tau> = \<sigma>"
      thus ?thesis using h\<sigma> by (by100 simp)
    qed
  qed
  have hfaces: "\<forall>\<tau>\<in>?L. \<forall>\<rho>. geotop_is_face \<rho> \<tau> \<longrightarrow> \<rho> \<in> ?L"
  proof (intro ballI allI impI)
    fix \<tau> \<rho>
    assume h\<tau>L: "\<tau> \<in> ?L"
    assume h\<rho>\<tau>: "geotop_is_face \<rho> \<tau>"
    have hcase: "geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>"
      using h\<tau>L by (by100 blast)
    have h\<rho>\<sigma>: "geotop_is_face \<rho> \<sigma>"
    proof (rule disjE[OF hcase])
      assume h\<tau>\<sigma>: "geotop_is_face \<tau> \<sigma>"
      show ?thesis
        by (rule geotop_is_face_trans[OF h\<rho>\<tau> h\<tau>\<sigma>])
    next
      assume "\<tau> = \<sigma>"
      thus ?thesis using h\<rho>\<tau> by (by100 simp)
    qed
    show "\<rho> \<in> ?L"
      using h\<rho>\<sigma> by (by100 blast)
  qed
  have hinter: "\<forall>\<tau>\<in>?L. \<forall>\<upsilon>\<in>?L. \<tau> \<inter> \<upsilon> \<noteq> {} \<longrightarrow>
      geotop_is_face (\<tau> \<inter> \<upsilon>) \<tau> \<and> geotop_is_face (\<tau> \<inter> \<upsilon>) \<upsilon>"
  proof (intro ballI impI)
    fix \<tau> \<upsilon>
    assume h\<tau>L: "\<tau> \<in> ?L"
    assume h\<upsilon>L: "\<upsilon> \<in> ?L"
    assume hne: "\<tau> \<inter> \<upsilon> \<noteq> {}"
    have h\<tau>simplex: "geotop_is_simplex \<tau>"
      using hsimplex h\<tau>L by (by100 blast)
    have h\<upsilon>simplex: "geotop_is_simplex \<upsilon>"
      using hsimplex h\<upsilon>L by (by100 blast)
    have h\<tau>case: "geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>"
      using h\<tau>L by (by100 blast)
    have h\<upsilon>case: "geotop_is_face \<upsilon> \<sigma> \<or> \<upsilon> = \<sigma>"
      using h\<upsilon>L by (by100 blast)
    have h\<tau>HOL: "\<tau> face_of \<sigma>"
    proof (rule disjE[OF h\<tau>case])
      assume hface: "geotop_is_face \<tau> \<sigma>"
      show ?thesis
        by (rule geotop_is_face_imp_HOL_face_of_R2[OF hface])
    next
      assume "\<tau> = \<sigma>"
      thus ?thesis
        using face_of_refl[OF h\<sigma>conv] by (by100 simp)
    qed
    have h\<upsilon>HOL: "\<upsilon> face_of \<sigma>"
    proof (rule disjE[OF h\<upsilon>case])
      assume hface: "geotop_is_face \<upsilon> \<sigma>"
      show ?thesis
        by (rule geotop_is_face_imp_HOL_face_of_R2[OF hface])
    next
      assume "\<upsilon> = \<sigma>"
      thus ?thesis
        using face_of_refl[OF h\<sigma>conv] by (by100 simp)
    qed
    have hinterHOL_\<sigma>: "(\<tau> \<inter> \<upsilon>) face_of \<sigma>"
      by (rule face_of_Int[OF h\<tau>HOL h\<upsilon>HOL])
    have hinterHOL_\<tau>: "(\<tau> \<inter> \<upsilon>) face_of \<tau>"
      using face_of_face[OF h\<tau>HOL, of "\<tau> \<inter> \<upsilon>"] hinterHOL_\<sigma> by (by100 blast)
    have hinterHOL_\<upsilon>: "(\<tau> \<inter> \<upsilon>) face_of \<upsilon>"
      using face_of_face[OF h\<upsilon>HOL, of "\<tau> \<inter> \<upsilon>"] hinterHOL_\<sigma> by (by100 blast)
    have hgeo_\<tau>: "geotop_is_face (\<tau> \<inter> \<upsilon>) \<tau>"
      by (rule geotop_HOL_face_of_simplex_imp_geotop_is_face_R2
          [OF h\<tau>simplex hinterHOL_\<tau> hne])
    have hgeo_\<upsilon>: "geotop_is_face (\<tau> \<inter> \<upsilon>) \<upsilon>"
      by (rule geotop_HOL_face_of_simplex_imp_geotop_is_face_R2
          [OF h\<upsilon>simplex hinterHOL_\<upsilon> hne])
    show "geotop_is_face (\<tau> \<inter> \<upsilon>) \<tau> \<and>
          geotop_is_face (\<tau> \<inter> \<upsilon>) \<upsilon>"
      using hgeo_\<tau> hgeo_\<upsilon> by (by100 blast)
  qed
  have hlocal: "\<forall>\<tau>\<in>?L. \<exists>U. open U \<and> \<tau> \<subseteq> U \<and>
      finite {\<rho>\<in>?L. \<rho> \<inter> U \<noteq> {}}"
  proof
    fix \<tau> assume h\<tau>L: "\<tau> \<in> ?L"
    have hopen: "open (UNIV::(real^2) set)"
      by (by100 simp)
    have hfin_filter: "finite {\<rho>\<in>?L. \<rho> \<inter> (UNIV::(real^2) set) \<noteq> {}}"
      using hfinite by (by100 simp)
    show "\<exists>U. open U \<and> \<tau> \<subseteq> U \<and> finite {\<rho>\<in>?L. \<rho> \<inter> U \<noteq> {}}"
      using hopen hfin_filter by (by100 blast)
  qed
  show ?thesis
    unfolding geotop_is_complex_def using hsimplex hfaces hinter hlocal by (by100 blast)
qed

lemma geotop_simplex_dim_face_complex_is_complex_R2:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> n"
  shows "geotop_is_complex {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
proof -
  have hsimplex: "geotop_is_simplex \<sigma>"
    by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>])
  show ?thesis
    by (rule geotop_simplex_face_complex_is_complex_R2[OF hsimplex])
qed

lemma geotop_isomorphic_refl_dev34:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  shows "geotop_isomorphic K K"
proof -
  have hbij: "bij_betw id (geotop_complex_vertices K) (geotop_complex_vertices K)"
    by (by100 simp)
  have hcond: "\<forall>V. V \<subseteq> geotop_complex_vertices K \<longrightarrow>
      (geotop_convex_hull V \<in> K \<longleftrightarrow> geotop_convex_hull (id ` V) \<in> K)"
    by (by100 simp)
  have hiso: "geotop_isomorphism K K id"
    unfolding geotop_isomorphism_def using hbij hcond by (by100 blast)
  show ?thesis
    unfolding geotop_isomorphic_def using hiso by (by100 blast)
qed

lemma geotop_comb_equiv_refl_finite_dev34:
  fixes K :: "'a::real_normed_vector set set"
  assumes hK: "geotop_is_complex K"
  assumes hfin: "finite K"
  shows "geotop_comb_equiv K K"
proof -
  have hsub: "geotop_is_subdivision K K"
    by (rule geotop_is_subdivision_refl[OF hK])
  have hiso: "geotop_isomorphic K K"
    by (rule geotop_isomorphic_refl_dev34[OF hK])
  show ?thesis
    unfolding geotop_comb_equiv_def using hfin hsub hiso by (by100 blast)
qed

lemma geotop_simplex_face_complex_comb_n_cell_R2:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> n"
  shows "geotop_comb_n_cell {\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>} n"
proof -
  let ?L = "{\<tau>. geotop_is_face \<tau> \<sigma> \<or> \<tau> = \<sigma>}"
  have hL_complex: "geotop_is_complex ?L"
    by (rule geotop_simplex_dim_face_complex_is_complex_R2[OF h\<sigma>])
  have hL_finite: "finite ?L"
    by (rule geotop_simplex_dim_face_complex_finite_R2[OF h\<sigma>])
  have hL_comb: "geotop_comb_equiv ?L ?L"
    by (rule geotop_comb_equiv_refl_finite_dev34[OF hL_complex hL_finite])
  show ?thesis
    unfolding geotop_comb_n_cell_def using hL_complex h\<sigma> hL_comb by (by100 blast)
qed

lemma geotop_star_finite_at_vertex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  shows "finite (geotop_star K v)"
proof -
  let ?I = "{\<sigma>\<in>K. v \<in> \<sigma>}"
  have hK_simplex: "\<forall>\<sigma>\<in>K. geotop_is_simplex \<sigma>"
    by (rule conjunct1[OF hK[unfolded geotop_is_complex_def]])
  have hK_local: "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and>
      finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]]])
  have hlocal_v: "\<exists>U. open U \<and> {v} \<subseteq> U \<and>
      finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule bspec[OF hK_local hvK])
  obtain U where hUopen: "open U" and hvUsub: "{v} \<subseteq> U"
    and hUfin: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    using hlocal_v by (by100 blast)
  have hvU: "v \<in> U"
    using hvUsub by (by100 blast)
  have hI_sub: "?I \<subseteq> {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma> assume h\<sigma>I: "\<sigma> \<in> ?I"
    have h\<sigma>K: "\<sigma> \<in> K"
      using h\<sigma>I by (by100 blast)
    have hv\<sigma>: "v \<in> \<sigma>"
      using h\<sigma>I by (by100 blast)
    have "\<sigma> \<inter> U \<noteq> {}"
      using hv\<sigma> hvU by (by100 blast)
    show "\<sigma> \<in> {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using h\<sigma>K \<open>\<sigma> \<inter> U \<noteq> {}\<close> by (by100 blast)
  qed
  have hI_fin: "finite ?I"
    by (rule finite_subset[OF hI_sub hUfin])
  have hstar_eq:
    "geotop_star K v =
      (\<Union>\<sigma>\<in>?I. {(\<tau>::(real^2) set). geotop_is_face \<tau> \<sigma>} \<union> {\<sigma>})"
    unfolding geotop_star_def by (by100 blast)
  have hfaces_fin:
    "finite (\<Union>\<sigma>\<in>?I. {(\<tau>::(real^2) set). geotop_is_face \<tau> \<sigma>} \<union> {\<sigma>})"
  proof (rule finite_UN_I[OF hI_fin])
    fix \<sigma> assume h\<sigma>I: "\<sigma> \<in> ?I"
    have h\<sigma>K: "\<sigma> \<in> K"
      using h\<sigma>I by (by100 blast)
    have h\<sigma>simplex: "geotop_is_simplex \<sigma>"
      using hK_simplex h\<sigma>K by (by100 blast)
    have "finite {(\<tau>::(real^2) set). geotop_is_face \<tau> \<sigma>}"
      by (rule geotop_simplex_faces_finite[OF h\<sigma>simplex])
    thus "finite ({(\<tau>::(real^2) set). geotop_is_face \<tau> \<sigma>} \<union> {\<sigma>})"
      by (by100 simp)
  qed
  show ?thesis
    using hstar_eq hfaces_fin by (by100 simp)
qed

lemma geotop_link_finite_at_vertex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  shows "finite (geotop_link K v)"
proof -
  have hstar_fin: "finite (geotop_star K v)"
    by (rule geotop_star_finite_at_vertex[OF hK hvK])
  have hlink_sub: "geotop_link K v \<subseteq> geotop_star K v"
    unfolding geotop_link_def by (by100 blast)
  show ?thesis
    by (rule finite_subset[OF hlink_sub hstar_fin])
qed

lemma geotop_star_finite_at_complex_vertex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "finite (geotop_star K v)"
proof -
  have hvK: "{v} \<in> K"
    using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
  show ?thesis
    by (rule geotop_star_finite_at_vertex[OF hK hvK])
qed

lemma geotop_link_finite_at_complex_vertex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "finite (geotop_link K v)"
proof -
  have hvK: "{v} \<in> K"
    using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
  show ?thesis
    by (rule geotop_link_finite_at_vertex[OF hK hvK])
qed

lemma geotop_link_polyhedron_finite_1dim_witness:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "\<exists>L. geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = \<Union>(geotop_link K v)"
proof -
  have hlink_complex: "geotop_is_complex (geotop_link K v)"
    by (rule geotop_link_is_complex[OF hK])
  have hlink_1dim: "geotop_complex_is_1dim (geotop_link K v)"
    by (rule geotop_link_complex_is_1dim_R2[OF hK])
  have hlink_fin: "finite (geotop_link K v)"
    by (rule geotop_link_finite_at_complex_vertex[OF hK hv])
  have hpoly_eq: "geotop_polyhedron (geotop_link K v) = \<Union>(geotop_link K v)"
    unfolding geotop_polyhedron_def by (by100 simp)
  show ?thesis
    using hlink_complex hlink_1dim hlink_fin hpoly_eq by (by100 blast)
qed

lemma geotop_link_polyhedron_subset_star_polyhedron:
  "\<Union>(geotop_link K v) \<subseteq> \<Union>(geotop_star K v)"
  unfolding geotop_link_def by (by100 blast)

lemma geotop_link_polyhedron_subset_punctured_star_polyhedron:
  "\<Union>(geotop_link K v) \<subseteq> \<Union>(geotop_star K v) - {v}"
  unfolding geotop_link_def by (by100 blast)

lemma geotop_star_polyhedron_subset_polyhedron:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  shows "\<Union>(geotop_star K v) \<subseteq> geotop_polyhedron K"
proof -
  have hsub: "geotop_star K v \<subseteq> K"
    by (rule geotop_star_subset_complex[OF hK])
  show ?thesis
    unfolding geotop_polyhedron_def using hsub by (by100 blast)
qed

lemma geotop_link_polyhedron_subset_polyhedron:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  shows "\<Union>(geotop_link K v) \<subseteq> geotop_polyhedron K"
proof -
  have hsub: "geotop_link K v \<subseteq> K"
    by (rule geotop_link_subset_complex[OF hK])
  show ?thesis
    unfolding geotop_polyhedron_def using hsub by (by100 blast)
qed

lemma geotop_star_polyhedron_compact_at_complex_vertex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "compact (\<Union>(geotop_star K v))"
proof -
  have hstar_complex: "geotop_is_complex (geotop_star K v)"
    by (rule geotop_star_is_complex[OF hK])
  have hstar_fin: "finite (geotop_star K v)"
    by (rule geotop_star_finite_at_complex_vertex[OF hK hv])
  have "compact (geotop_polyhedron (geotop_star K v))"
    by (rule geotop_complex_polyhedron_compact[OF hstar_complex hstar_fin])
  thus ?thesis
    unfolding geotop_polyhedron_def by (by100 simp)
qed

lemma geotop_star_polyhedron_closed_at_complex_vertex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "closed (\<Union>(geotop_star K v))"
proof -
  have hcompact: "compact (\<Union>(geotop_star K v))"
    by (rule geotop_star_polyhedron_compact_at_complex_vertex[OF hK hv])
  show ?thesis
    by (rule compact_imp_closed[OF hcompact])
qed

lemma geotop_star_polyhedron_contains_complex_vertex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "v \<in> \<Union>(geotop_star K v)"
proof -
  have hvK: "{v} \<in> K"
    using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
  have "{v} \<in> geotop_star K v"
    unfolding geotop_star_def using hvK by (by100 blast)
  show ?thesis
    using \<open>{v} \<in> geotop_star K v\<close> by (by100 blast)
qed

lemma geotop_link_polyhedron_avoids_vertex:
  "v \<notin> \<Union>(geotop_link K v)"
  unfolding geotop_link_def by (by100 blast)

lemma geotop_link_polyhedron_compact_at_complex_vertex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "compact (\<Union>(geotop_link K v))"
proof -
  have hlink_complex: "geotop_is_complex (geotop_link K v)"
    by (rule geotop_link_is_complex[OF hK])
  have hlink_fin: "finite (geotop_link K v)"
    by (rule geotop_link_finite_at_complex_vertex[OF hK hv])
  have "compact (geotop_polyhedron (geotop_link K v))"
    by (rule geotop_complex_polyhedron_compact[OF hlink_complex hlink_fin])
  thus ?thesis
    unfolding geotop_polyhedron_def by (by100 simp)
qed

lemma geotop_link_polyhedron_closed_at_complex_vertex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  shows "closed (\<Union>(geotop_link K v))"
proof -
  have hcompact: "compact (\<Union>(geotop_link K v))"
    by (rule geotop_link_polyhedron_compact_at_complex_vertex[OF hK hv])
  show ?thesis
    by (rule compact_imp_closed[OF hcompact])
qed

lemma geotop_nonempty_complex_polyhedron_nonempty:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hne: "K \<noteq> {}"
  shows "geotop_polyhedron K \<noteq> {}"
proof -
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    using hne by (by100 blast)
  have h\<sigma>ne: "\<sigma> \<noteq> {}"
    by (rule geotop_complex_simplex_nonempty[OF hK h\<sigma>K])
  show ?thesis
    unfolding geotop_polyhedron_def using h\<sigma>K h\<sigma>ne by (by100 blast)
qed

lemma geotop_nonempty_polyhedron_has_complex_vertex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hpoly: "geotop_polyhedron K \<noteq> {}"
  shows "\<exists>w. {w} \<in> K"
proof -
  obtain x where hx: "x \<in> geotop_polyhedron K"
    using hpoly by (by100 blast)
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K" and hx\<sigma>: "x \<in> \<sigma>"
    using hx unfolding geotop_polyhedron_def by (by100 blast)
  have hsimplex_all: "\<forall>\<tau>\<in>K. geotop_is_simplex \<tau>"
    by (rule conjunct1[OF hK[unfolded geotop_is_complex_def]])
  have h\<sigma>simplex: "geotop_is_simplex \<sigma>"
    using hsimplex_all h\<sigma>K by (by100 blast)
  obtain V m n where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>simplex unfolding geotop_is_simplex_def by (by100 blast)
  have hV_ne: "V \<noteq> {}"
    using hV_card by (by100 force)
  obtain w where hwV: "w \<in> V"
    using hV_ne by (by100 blast)
  have hsingle_hull: "{w} = geotop_convex_hull {w}"
    using geotop_convex_hull_eq_HOL[of "{w}"] by (by100 simp)
  have h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    unfolding geotop_simplex_vertices_def
    using hV_fin hV_card hn_le_m hgp h\<sigma>_eq by (by100 blast)
  have hface: "geotop_is_face {w} \<sigma>"
    unfolding geotop_is_face_def using h\<sigma>V hwV hsingle_hull by (by100 blast)
  have hface_closed: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    by (rule conjunct1[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]])
  have "{w} \<in> K"
    using hface_closed h\<sigma>K hface by (by100 blast)
  show ?thesis
    using \<open>{w} \<in> K\<close> by (by100 blast)
qed

lemma geotop_connected_component_at_eq_self:
  assumes hPM: "P \<in> M"
  assumes hconn: "top1_connected_on M (subspace_topology X T M)"
  shows "geotop_component_at X T M P = M"
proof
  show "geotop_component_at X T M P \<subseteq> M"
    unfolding geotop_component_at_def by (by100 blast)
next
  show "M \<subseteq> geotop_component_at X T M P"
    unfolding geotop_component_at_def using hPM hconn by (by100 blast)
qed

lemma geotop_component_at_UNIV_subset:
  fixes M :: "'a::real_normed_vector set"
  shows "geotop_component_at UNIV geotop_euclidean_topology M P \<subseteq> M"
proof -
  have h_eq: "geotop_component_at UNIV geotop_euclidean_topology M P =
      connected_component_set M P"
    by (rule geotop_component_at_UNIV_eq_connected_component_set)
  show ?thesis
    using h_eq connected_component_subset by (by100 simp)
qed

lemma geotop_component_at_UNIV_connected:
  fixes M :: "'a::real_normed_vector set"
  shows "top1_connected_on (geotop_component_at UNIV geotop_euclidean_topology M P)
           (subspace_topology UNIV geotop_euclidean_topology
              (geotop_component_at UNIV geotop_euclidean_topology M P))"
proof -
  have h_eq: "geotop_component_at UNIV geotop_euclidean_topology M P =
      connected_component_set M P"
    by (rule geotop_component_at_UNIV_eq_connected_component_set)
  have "connected (geotop_component_at UNIV geotop_euclidean_topology M P)"
    using h_eq connected_connected_component by (by100 simp)
  show ?thesis
    using \<open>connected (geotop_component_at UNIV geotop_euclidean_topology M P)\<close>
      top1_connected_on_geotop_iff_connected by (by100 blast)
qed

lemma geotop_component_at_UNIV_self:
  fixes M :: "'a::real_normed_vector set"
  assumes hP: "P \<in> M"
  shows "P \<in> geotop_component_at UNIV geotop_euclidean_topology M P"
proof -
  have h_eq: "geotop_component_at UNIV geotop_euclidean_topology M P =
      connected_component_set M P"
    by (rule geotop_component_at_UNIV_eq_connected_component_set)
  have "P \<in> connected_component_set M P"
    using hP connected_component_refl by (by100 simp)
  show ?thesis
    using h_eq \<open>P \<in> connected_component_set M P\<close> by (by100 simp)
qed

lemma geotop_component_at_UNIV_closedin_HOL:
  fixes M :: "'a::real_normed_vector set"
  shows "closedin (top_of_set M)
           (geotop_component_at UNIV geotop_euclidean_topology M P)"
proof -
  have h_eq: "geotop_component_at UNIV geotop_euclidean_topology M P =
      connected_component_set M P"
    by (rule geotop_component_at_UNIV_eq_connected_component_set)
  show ?thesis
    using h_eq closedin_connected_component by (by100 simp)
qed

lemma geotop_link_component_basic:
  fixes K :: "(real^2) set set"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  shows "C \<subseteq> \<Union>(geotop_link K v)
       \<and> P \<in> C
       \<and> top1_connected_on C (subspace_topology UNIV geotop_euclidean_topology C)"
proof -
  have hsub: "C \<subseteq> \<Union>(geotop_link K v)"
    using hC geotop_component_at_UNIV_subset[of "\<Union>(geotop_link K v)" P]
    by (by100 simp)
  have hself: "P \<in> C"
    using hC geotop_component_at_UNIV_self[OF hP] by (by100 simp)
  have hconn: "top1_connected_on C
      (subspace_topology UNIV geotop_euclidean_topology C)"
    using hC geotop_component_at_UNIV_connected[of "\<Union>(geotop_link K v)" P]
    by (by100 simp)
  show ?thesis
    using hsub hself hconn by (by100 blast)
qed

lemma geotop_link_component_compact:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  shows "compact C"
proof -
  have hlink_compact: "compact (\<Union>(geotop_link K v))"
    by (rule geotop_link_polyhedron_compact_at_complex_vertex[OF hK hv])
  have hC_closedin: "closedin (top_of_set (\<Union>(geotop_link K v))) C"
    using hC
      geotop_component_at_UNIV_closedin_HOL[of "\<Union>(geotop_link K v)" P]
    by (by100 simp)
  show ?thesis
    by (rule closedin_compact[OF hlink_compact hC_closedin])
qed

lemma geotop_link_component_closed:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  shows "closed C"
proof -
  have hcompact: "compact C"
    by (rule geotop_link_component_compact[OF hK hv hC])
  show ?thesis
    by (rule compact_imp_closed[OF hcompact])
qed

lemma geotop_link_component_summary:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  shows "C \<subseteq> \<Union>(geotop_link K v)
       \<and> P \<in> C
       \<and> top1_connected_on C (subspace_topology UNIV geotop_euclidean_topology C)
       \<and> compact C
       \<and> closed C"
proof -
  have hbasic:
    "C \<subseteq> \<Union>(geotop_link K v)
       \<and> P \<in> C
       \<and> top1_connected_on C (subspace_topology UNIV geotop_euclidean_topology C)"
    by (rule geotop_link_component_basic[OF hP hC])
  have hcompact: "compact C"
    by (rule geotop_link_component_compact[OF hK hv hC])
  have hclosed: "closed C"
    by (rule geotop_link_component_closed[OF hK hv hC])
  show ?thesis
    using hbasic hcompact hclosed by (by100 blast)
qed

lemma geotop_simplex_connected_HOL_dev34:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_is_simplex \<sigma>"
  shows "connected \<sigma>"
proof -
  have hpc: "top1_path_connected_on \<sigma>
      (subspace_topology UNIV geotop_euclidean_topology \<sigma>)"
    by (rule Theorem_GT_1_3[OF h\<sigma>])
  have hconn_top: "top1_connected_on \<sigma>
      (subspace_topology UNIV geotop_euclidean_topology \<sigma>)"
    by (rule top1_path_connected_on_geotop_imp_connected[OF hpc])
  show ?thesis
    using hconn_top top1_connected_on_geotop_iff_connected by (by100 blast)
qed

lemma geotop_link_component_contains_meeting_simplex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  assumes h\<sigma>: "\<sigma> \<in> geotop_link K v"
  assumes hmeet: "\<sigma> \<inter> C \<noteq> {}"
  shows "\<sigma> \<subseteq> C"
proof -
  let ?M = "\<Union>(geotop_link K v)"
  obtain x where hx\<sigma>: "x \<in> \<sigma>" and hxC: "x \<in> C"
    using hmeet by (by100 blast)
  have hlink_complex: "geotop_is_complex (geotop_link K v)"
    by (rule geotop_link_is_complex[OF hK])
  have h\<sigma>_simplex: "geotop_is_simplex \<sigma>"
    using geotop_is_complex_simplex[OF hlink_complex] h\<sigma> by (by100 blast)
  have h\<sigma>_conn: "connected \<sigma>"
    by (rule geotop_simplex_connected_HOL_dev34[OF h\<sigma>_simplex])
  have h\<sigma>_sub_M: "\<sigma> \<subseteq> ?M"
    using h\<sigma> unfolding geotop_polyhedron_def by (by100 blast)
  have hC_eq_P: "C = connected_component_set ?M P"
    using hC geotop_component_at_UNIV_eq_connected_component_set by (by100 simp)
  have hC_eq_x: "C = connected_component_set ?M x"
    using connected_component_eq hC_eq_P hxC by (by100 blast)
  have "\<sigma> \<subseteq> connected_component_set ?M x"
    by (rule connected_component_maximal[OF hx\<sigma> h\<sigma>_conn h\<sigma>_sub_M])
  show ?thesis
    using \<open>\<sigma> \<subseteq> connected_component_set ?M x\<close> hC_eq_x by (by100 simp)
qed

lemma geotop_link_component_inherits_incident_link_edges:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  assumes hvertices:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
        (\<exists>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l)"
  shows "\<forall>w. {w} \<in> {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C} \<longrightarrow>
        (\<exists>l\<in>{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}. geotop_is_edge l \<and> w \<in> l)"
proof (intro allI impI)
  fix w
  let ?L = "{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}"
  assume hwL: "{w} \<in> ?L"
  have hw_link: "{w} \<in> geotop_link K v"
    using hwL by (by100 simp)
  have hwC: "w \<in> C"
    using hwL by (by100 simp)
  obtain l where hl_link: "l \<in> geotop_link K v"
    and hledge: "geotop_is_edge l"
    and hwl: "w \<in> l"
    using hvertices hw_link by (by100 blast)
  have hmeet: "l \<inter> C \<noteq> {}"
    using hwl hwC by (by100 blast)
  have hl_sub_C: "l \<subseteq> C"
    by (rule geotop_link_component_contains_meeting_simplex
        [OF hK hP hC hl_link hmeet])
  have hl_L: "l \<in> ?L"
    using hl_link hl_sub_C by (by100 simp)
  show "\<exists>l\<in>?L. geotop_is_edge l \<and> w \<in> l"
    using hl_L hledge hwl by (by100 blast)
qed

lemma geotop_link_component_inherits_two_distinct_link_edges:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  assumes hvertices:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
        (\<exists>l\<^sub>1 l\<^sub>2. l\<^sub>1 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
          \<and> l\<^sub>2 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
          \<and> l\<^sub>1 \<noteq> l\<^sub>2)"
  shows "\<forall>w. {w} \<in> {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C} \<longrightarrow>
        (\<exists>l\<^sub>1\<in>{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}.
          \<exists>l\<^sub>2\<in>{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}.
            geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
            \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
            \<and> l\<^sub>1 \<noteq> l\<^sub>2)"
proof (intro allI impI)
  fix w
  let ?L = "{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}"
  assume hwL: "{w} \<in> ?L"
  have hw_link: "{w} \<in> geotop_link K v"
    using hwL by (by100 simp)
  have hwC: "w \<in> C"
    using hwL by (by100 simp)
  obtain l\<^sub>1 l\<^sub>2 where hl1_link: "l\<^sub>1 \<in> geotop_link K v"
    and hl1_edge: "geotop_is_edge l\<^sub>1"
    and hw_l1: "w \<in> l\<^sub>1"
    and hl2_link: "l\<^sub>2 \<in> geotop_link K v"
    and hl2_edge: "geotop_is_edge l\<^sub>2"
    and hw_l2: "w \<in> l\<^sub>2"
    and hl12: "l\<^sub>1 \<noteq> l\<^sub>2"
    using hvertices hw_link by (by100 blast)
  have hl1_meet: "l\<^sub>1 \<inter> C \<noteq> {}"
    using hw_l1 hwC by (by100 blast)
  have hl1_sub_C: "l\<^sub>1 \<subseteq> C"
    by (rule geotop_link_component_contains_meeting_simplex
        [OF hK hP hC hl1_link hl1_meet])
  have hl1_L: "l\<^sub>1 \<in> ?L"
    using hl1_link hl1_sub_C by (by100 simp)
  have hl2_meet: "l\<^sub>2 \<inter> C \<noteq> {}"
    using hw_l2 hwC by (by100 blast)
  have hl2_sub_C: "l\<^sub>2 \<subseteq> C"
    by (rule geotop_link_component_contains_meeting_simplex
        [OF hK hP hC hl2_link hl2_meet])
  have hl2_L: "l\<^sub>2 \<in> ?L"
    using hl2_link hl2_sub_C by (by100 simp)
  show "\<exists>l\<^sub>1\<in>?L. \<exists>l\<^sub>2\<in>?L.
      geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
      \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
      \<and> l\<^sub>1 \<noteq> l\<^sub>2"
    using hl1_L hl1_edge hw_l1 hl2_L hl2_edge hw_l2 hl12 by (by100 blast)
qed

lemma geotop_link_component_inherits_two_exact_link_edges:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  assumes hvertices:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
        (\<exists>l\<^sub>1 l\<^sub>2. l\<^sub>1 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
          \<and> l\<^sub>2 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
          \<and> l\<^sub>1 \<noteq> l\<^sub>2
          \<and> (\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
              \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2))"
  shows "\<forall>w. {w} \<in> {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C} \<longrightarrow>
        (\<exists>l\<^sub>1\<in>{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}.
          \<exists>l\<^sub>2\<in>{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}.
            geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
            \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
            \<and> l\<^sub>1 \<noteq> l\<^sub>2
            \<and> (\<forall>l. l \<in> {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}
                \<and> geotop_is_edge l \<and> w \<in> l
                \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2))"
proof (intro allI impI)
  fix w
  let ?L = "{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}"
  assume hwL: "{w} \<in> ?L"
  have hw_link: "{w} \<in> geotop_link K v"
    using hwL by (by100 simp)
  have hwC: "w \<in> C"
    using hwL by (by100 simp)
  obtain l\<^sub>1 l\<^sub>2 where hl1_link: "l\<^sub>1 \<in> geotop_link K v"
    and hl1_edge: "geotop_is_edge l\<^sub>1"
    and hw_l1: "w \<in> l\<^sub>1"
    and hl2_link: "l\<^sub>2 \<in> geotop_link K v"
    and hl2_edge: "geotop_is_edge l\<^sub>2"
    and hw_l2: "w \<in> l\<^sub>2"
    and hl12: "l\<^sub>1 \<noteq> l\<^sub>2"
    and hexact: "\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
              \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2"
    using hvertices hw_link by (by100 blast)
  have hl1_meet: "l\<^sub>1 \<inter> C \<noteq> {}"
    using hw_l1 hwC by (by100 blast)
  have hl1_sub_C: "l\<^sub>1 \<subseteq> C"
    by (rule geotop_link_component_contains_meeting_simplex
        [OF hK hP hC hl1_link hl1_meet])
  have hl1_L: "l\<^sub>1 \<in> ?L"
    using hl1_link hl1_sub_C by (by100 simp)
  have hl2_meet: "l\<^sub>2 \<inter> C \<noteq> {}"
    using hw_l2 hwC by (by100 blast)
  have hl2_sub_C: "l\<^sub>2 \<subseteq> C"
    by (rule geotop_link_component_contains_meeting_simplex
        [OF hK hP hC hl2_link hl2_meet])
  have hl2_L: "l\<^sub>2 \<in> ?L"
    using hl2_link hl2_sub_C by (by100 simp)
  have hexact_L: "\<forall>l. l \<in> ?L \<and> geotop_is_edge l \<and> w \<in> l
      \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2"
  proof (intro allI impI)
    fix l
    assume hl: "l \<in> ?L \<and> geotop_is_edge l \<and> w \<in> l"
    have hl_link: "l \<in> geotop_link K v"
      using hl by (by100 simp)
    have hl_edge: "geotop_is_edge l"
      using hl by (by100 blast)
    have hw_l: "w \<in> l"
      using hl by (by100 blast)
    show "l = l\<^sub>1 \<or> l = l\<^sub>2"
      using hexact hl_link hl_edge hw_l by (by100 blast)
  qed
  show "\<exists>l\<^sub>1\<in>?L. \<exists>l\<^sub>2\<in>?L.
      geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
      \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
      \<and> l\<^sub>1 \<noteq> l\<^sub>2
      \<and> (\<forall>l. l \<in> ?L \<and> geotop_is_edge l \<and> w \<in> l
          \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2)"
    using hl1_L hl1_edge hw_l1 hl2_L hl2_edge hw_l2 hl12 hexact_L
    by (by100 blast)
qed

lemma geotop_link_component_subcomplex_witness:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  shows "\<exists>L. L = {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}
          \<and> geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C"
proof -
  let ?L = "{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}"
  let ?M = "\<Union>(geotop_link K v)"
  have hlink_complex: "geotop_is_complex (geotop_link K v)"
    by (rule geotop_link_is_complex[OF hK])
  have hL_complex: "geotop_is_complex ?L"
    by (rule geotop_complex_restrict_subset_is_complex[OF hlink_complex])
  have hlink_1dim: "geotop_complex_is_1dim (geotop_link K v)"
    by (rule geotop_link_complex_is_1dim_R2[OF hK])
  have hL_1dim: "geotop_complex_is_1dim ?L"
    by (rule geotop_complex_restrict_preserves_1dim[OF hlink_1dim])
  have hlink_fin: "finite (geotop_link K v)"
    by (rule geotop_link_finite_at_complex_vertex[OF hK hv])
  have hL_sub_link: "?L \<subseteq> geotop_link K v"
    by (by100 blast)
  have hL_fin: "finite ?L"
    by (rule finite_subset[OF hL_sub_link hlink_fin])
  have hC_sub_M: "C \<subseteq> ?M"
    using geotop_link_component_summary[OF hK hv hP hC] by (by100 blast)
  have hpoly_eq: "geotop_polyhedron ?L = C"
  proof
    show "geotop_polyhedron ?L \<subseteq> C"
    proof
      fix x assume hx: "x \<in> geotop_polyhedron ?L"
      obtain \<sigma> where h\<sigma>L: "\<sigma> \<in> ?L" and hx\<sigma>: "x \<in> \<sigma>"
        using hx unfolding geotop_polyhedron_def by (by100 blast)
      have h\<sigma>subC: "\<sigma> \<subseteq> C"
        using h\<sigma>L by (by100 simp)
      show "x \<in> C"
        using h\<sigma>subC hx\<sigma> by (by100 blast)
    qed
  next
    show "C \<subseteq> geotop_polyhedron ?L"
    proof
      fix x assume hxC: "x \<in> C"
      have hxM: "x \<in> ?M"
        using hC_sub_M hxC by (by100 blast)
      obtain \<sigma> where h\<sigma>link: "\<sigma> \<in> geotop_link K v" and hx\<sigma>: "x \<in> \<sigma>"
        using hxM unfolding geotop_polyhedron_def by (by100 blast)
      have hmeet: "\<sigma> \<inter> C \<noteq> {}"
        using hxC hx\<sigma> by (by100 blast)
      have h\<sigma>subC: "\<sigma> \<subseteq> C"
        by (rule geotop_link_component_contains_meeting_simplex
            [OF hK hP hC h\<sigma>link hmeet])
      have h\<sigma>L: "\<sigma> \<in> ?L"
        using h\<sigma>link h\<sigma>subC by (by100 simp)
      show "x \<in> geotop_polyhedron ?L"
        unfolding geotop_polyhedron_def using h\<sigma>L hx\<sigma> by (by100 blast)
    qed
  qed
  show ?thesis
    using hL_complex hL_1dim hL_fin hpoly_eq by (by100 blast)
qed

lemma geotop_link_component_connected_subcomplex_witness:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  shows "\<exists>L. geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> geotop_complex_connected L"
proof -
  obtain L where hL_eq: "L = {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}"
    and hL_complex: "geotop_is_complex L"
    and hL_1dim: "geotop_complex_is_1dim L"
    and hL_fin: "finite L"
    and hL_poly: "geotop_polyhedron L = C"
    using geotop_link_component_subcomplex_witness[OF hK hv hP hC]
    by (by100 blast)
  have hC_conn: "top1_connected_on C
      (subspace_topology UNIV geotop_euclidean_topology C)"
    using geotop_link_component_summary[OF hK hv hP hC] by (by100 blast)
  have hpoly_conn: "top1_connected_on (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    using hC_conn hL_poly by (by100 simp)
  have hpath: "top1_path_connected_on (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    by (rule iffD2[OF Theorem_GT_1_12(2)[OF hL_complex] hpoly_conn])
  have hL_conn: "geotop_complex_connected L"
    by (rule iffD2[OF Theorem_GT_1_12(1)[OF hL_complex] hpath])
  show ?thesis
    using hL_complex hL_1dim hL_fin hL_poly hL_conn by (by100 blast)
qed

lemma geotop_link_component_nonisolated_subcomplex_witness:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  assumes hvertices:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
        (\<exists>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l)"
  shows "\<exists>L. geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> geotop_complex_connected L
          \<and> (\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>l\<in>L. geotop_is_edge l \<and> w \<in> l))"
proof -
  obtain L where hL_eq: "L = {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}"
    and hL_complex: "geotop_is_complex L"
    and hL_1dim: "geotop_complex_is_1dim L"
    and hL_fin: "finite L"
    and hL_poly: "geotop_polyhedron L = C"
    using geotop_link_component_subcomplex_witness[OF hK hv hP hC]
    by (by100 blast)
  have hC_conn: "top1_connected_on C
      (subspace_topology UNIV geotop_euclidean_topology C)"
    using geotop_link_component_summary[OF hK hv hP hC] by (by100 blast)
  have hpoly_conn: "top1_connected_on (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    using hC_conn hL_poly by (by100 simp)
  have hpath: "top1_path_connected_on (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    by (rule iffD2[OF Theorem_GT_1_12(2)[OF hL_complex] hpoly_conn])
  have hL_conn: "geotop_complex_connected L"
    by (rule iffD2[OF Theorem_GT_1_12(1)[OF hL_complex] hpath])
  have hinc_raw:
    "\<forall>w. {w} \<in> {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C} \<longrightarrow>
        (\<exists>l\<in>{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}. geotop_is_edge l \<and> w \<in> l)"
    by (rule geotop_link_component_inherits_incident_link_edges
        [OF hK hP hC hvertices])
  have hinc_L: "\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>l\<in>L. geotop_is_edge l \<and> w \<in> l)"
    using hinc_raw hL_eq by (by100 simp)
  show ?thesis
    using hL_complex hL_1dim hL_fin hL_poly hL_conn hinc_L by (by100 blast)
qed

lemma geotop_link_component_two_distinct_subcomplex_witness:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  assumes hvertices:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
        (\<exists>l\<^sub>1 l\<^sub>2. l\<^sub>1 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
          \<and> l\<^sub>2 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
          \<and> l\<^sub>1 \<noteq> l\<^sub>2)"
  shows "\<exists>L. geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> geotop_complex_connected L
          \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
              (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
                geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
                \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
                \<and> l\<^sub>1 \<noteq> l\<^sub>2))"
proof -
  obtain L where hL_eq: "L = {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}"
    and hL_complex: "geotop_is_complex L"
    and hL_1dim: "geotop_complex_is_1dim L"
    and hL_fin: "finite L"
    and hL_poly: "geotop_polyhedron L = C"
    using geotop_link_component_subcomplex_witness[OF hK hv hP hC]
    by (by100 blast)
  have hC_conn: "top1_connected_on C
      (subspace_topology UNIV geotop_euclidean_topology C)"
    using geotop_link_component_summary[OF hK hv hP hC] by (by100 blast)
  have hpoly_conn: "top1_connected_on (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    using hC_conn hL_poly by (by100 simp)
  have hpath: "top1_path_connected_on (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    by (rule iffD2[OF Theorem_GT_1_12(2)[OF hL_complex] hpoly_conn])
  have hL_conn: "geotop_complex_connected L"
    by (rule iffD2[OF Theorem_GT_1_12(1)[OF hL_complex] hpath])
  have htwo_raw:
    "\<forall>w. {w} \<in> {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C} \<longrightarrow>
        (\<exists>l\<^sub>1\<in>{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}.
          \<exists>l\<^sub>2\<in>{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}.
            geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
            \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
            \<and> l\<^sub>1 \<noteq> l\<^sub>2)"
    by (rule geotop_link_component_inherits_two_distinct_link_edges
        [OF hK hP hC hvertices])
  have htwo_L: "\<forall>w. {w} \<in> L \<longrightarrow>
      (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
        geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
        \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
        \<and> l\<^sub>1 \<noteq> l\<^sub>2)"
    using htwo_raw hL_eq by (by100 simp)
  show ?thesis
    using hL_complex hL_1dim hL_fin hL_poly hL_conn htwo_L by (by100 blast)
qed

lemma geotop_link_component_two_exact_subcomplex_witness:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  assumes hvertices:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
        (\<exists>l\<^sub>1 l\<^sub>2. l\<^sub>1 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
          \<and> l\<^sub>2 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
          \<and> l\<^sub>1 \<noteq> l\<^sub>2
          \<and> (\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
              \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2))"
  shows "\<exists>L. geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> geotop_complex_connected L
          \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
              (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
                geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
                \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
                \<and> l\<^sub>1 \<noteq> l\<^sub>2
                \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
                    \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2)))"
proof -
  obtain L where hL_eq: "L = {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}"
    and hL_complex: "geotop_is_complex L"
    and hL_1dim: "geotop_complex_is_1dim L"
    and hL_fin: "finite L"
    and hL_poly: "geotop_polyhedron L = C"
    using geotop_link_component_subcomplex_witness[OF hK hv hP hC]
    by (by100 blast)
  have hC_conn: "top1_connected_on C
      (subspace_topology UNIV geotop_euclidean_topology C)"
    using geotop_link_component_summary[OF hK hv hP hC] by (by100 blast)
  have hpoly_conn: "top1_connected_on (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    using hC_conn hL_poly by (by100 simp)
  have hpath: "top1_path_connected_on (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    by (rule iffD2[OF Theorem_GT_1_12(2)[OF hL_complex] hpoly_conn])
  have hL_conn: "geotop_complex_connected L"
    by (rule iffD2[OF Theorem_GT_1_12(1)[OF hL_complex] hpath])
  have htwo_raw:
    "\<forall>w. {w} \<in> {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C} \<longrightarrow>
        (\<exists>l\<^sub>1\<in>{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}.
          \<exists>l\<^sub>2\<in>{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}.
            geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
            \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
            \<and> l\<^sub>1 \<noteq> l\<^sub>2
            \<and> (\<forall>l. l \<in> {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}
                \<and> geotop_is_edge l \<and> w \<in> l
                \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2))"
    by (rule geotop_link_component_inherits_two_exact_link_edges
        [OF hK hP hC hvertices])
  have htwo_L: "\<forall>w. {w} \<in> L \<longrightarrow>
      (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
        geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
        \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
        \<and> l\<^sub>1 \<noteq> l\<^sub>2
        \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
            \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2))"
    using htwo_raw hL_eq by (by100 simp)
  show ?thesis
    using hL_complex hL_1dim hL_fin hL_poly hL_conn htwo_L by (by100 blast)
qed

lemma geotop_exact_two_incident_edges_no_graph_endpoint_dev34:
  fixes L :: "(real^2) set set"
  assumes hfin: "finite L"
  assumes htwo:
    "\<forall>w. {w} \<in> L \<longrightarrow>
      (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
        geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
        \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
        \<and> l\<^sub>1 \<noteq> l\<^sub>2
        \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
            \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2))"
  shows "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
proof (intro allI impI)
  fix w
  assume hwL: "{w} \<in> L"
  show "\<not> geotop_graph_endpoint L w"
  proof
    assume hend: "geotop_graph_endpoint L w"
    obtain l\<^sub>1 l\<^sub>2 where hl1L: "l\<^sub>1 \<in> L"
      and hl2L: "l\<^sub>2 \<in> L"
      and hl1edge: "geotop_is_edge l\<^sub>1"
      and hw_l1: "w \<in> l\<^sub>1"
      and hl2edge: "geotop_is_edge l\<^sub>2"
      and hw_l2: "w \<in> l\<^sub>2"
      and hl12: "l\<^sub>1 \<noteq> l\<^sub>2"
      using htwo hwL by (by100 blast)
    let ?S = "{e\<in>L. geotop_is_edge e \<and> w \<in> e}"
    have hS_fin: "finite ?S"
      by (rule finite_subset[OF _ hfin]) (by100 blast)
    have hl1S: "l\<^sub>1 \<in> ?S"
      using hl1L hl1edge hw_l1 by (by100 simp)
    have hl2S: "l\<^sub>2 \<in> ?S"
      using hl2L hl2edge hw_l2 by (by100 simp)
    have hpair_sub: "{l\<^sub>1, l\<^sub>2} \<subseteq> ?S"
      using hl1S hl2S by (by100 blast)
    have hpair_card: "card {l\<^sub>1, l\<^sub>2} = 2"
      using hl12 by (by100 simp)
    have hcard_le: "card {l\<^sub>1, l\<^sub>2} \<le> card ?S"
      by (rule card_mono[OF hS_fin hpair_sub])
    have hcard_ge2: "2 \<le> card ?S"
      using hpair_card hcard_le by (by100 linarith)
    have hcard1: "card ?S = 1"
      using hend unfolding geotop_graph_endpoint_def by (by100 blast)
    show False
      using hcard_ge2 hcard1 by (by100 simp)
  qed
qed

lemma geotop_exact_two_incident_edges_card_eq_two_dev34:
  fixes L :: "(real^2) set set"
  assumes hfin: "finite L"
  assumes htwo:
    "\<forall>w. {w} \<in> L \<longrightarrow>
      (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
        geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
        \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
        \<and> l\<^sub>1 \<noteq> l\<^sub>2
        \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
            \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2))"
  shows "\<forall>w. {w} \<in> L \<longrightarrow>
      card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2"
proof (intro allI impI)
  fix w
  assume hwL: "{w} \<in> L"
  obtain l\<^sub>1 l\<^sub>2 where hl1L: "l\<^sub>1 \<in> L"
    and hl2L: "l\<^sub>2 \<in> L"
    and hl1edge: "geotop_is_edge l\<^sub>1"
    and hw_l1: "w \<in> l\<^sub>1"
    and hl2edge: "geotop_is_edge l\<^sub>2"
    and hw_l2: "w \<in> l\<^sub>2"
    and hl12: "l\<^sub>1 \<noteq> l\<^sub>2"
    and hexact: "\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
        \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2"
    using htwo hwL by (by100 blast)
  let ?S = "{l\<in>L. geotop_is_edge l \<and> w \<in> l}"
  have hS_eq: "?S = {l\<^sub>1, l\<^sub>2}"
  proof
    show "?S \<subseteq> {l\<^sub>1, l\<^sub>2}"
      using hexact by (by100 blast)
    show "{l\<^sub>1, l\<^sub>2} \<subseteq> ?S"
      using hl1L hl2L hl1edge hl2edge hw_l1 hw_l2 by (by100 blast)
  qed
  show "card ?S = 2"
    using hS_eq hl12 by (by100 simp)
qed

lemma geotop_link_component_two_exact_no_endpoint_linear_graph_witness:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  assumes hvertices:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
        (\<exists>l\<^sub>1 l\<^sub>2. l\<^sub>1 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
          \<and> l\<^sub>2 \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
          \<and> l\<^sub>1 \<noteq> l\<^sub>2
          \<and> (\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
              \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2))"
  shows "\<exists>L. geotop_is_linear_graph L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> geotop_complex_connected L
          \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
              (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
                geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
                \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
                \<and> l\<^sub>1 \<noteq> l\<^sub>2
                \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
                    \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2)))
          \<and> (\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w)"
proof -
  obtain L where hL_complex: "geotop_is_complex L"
    and hL_1dim: "geotop_complex_is_1dim L"
    and hL_fin: "finite L"
    and hL_poly: "geotop_polyhedron L = C"
    and hL_conn: "geotop_complex_connected L"
    and hL_two: "\<forall>w. {w} \<in> L \<longrightarrow>
      (\<exists>l\<^sub>1\<in>L. \<exists>l\<^sub>2\<in>L.
        geotop_is_edge l\<^sub>1 \<and> w \<in> l\<^sub>1
        \<and> geotop_is_edge l\<^sub>2 \<and> w \<in> l\<^sub>2
        \<and> l\<^sub>1 \<noteq> l\<^sub>2
        \<and> (\<forall>l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l
            \<longrightarrow> l = l\<^sub>1 \<or> l = l\<^sub>2))"
    using geotop_link_component_two_exact_subcomplex_witness
      [OF hK hv hP hC hvertices]
    by (by100 blast)
  have hL_linear: "geotop_is_linear_graph L"
    by (rule geotop_complex_1dim_imp_linear_graph_dev34[OF hL_complex hL_1dim])
  have hL_noend: "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
    by (rule geotop_exact_two_incident_edges_no_graph_endpoint_dev34[OF hL_fin hL_two])
  show ?thesis
    using hL_linear hL_fin hL_poly hL_conn hL_two hL_noend by (by100 blast)
qed

lemma geotop_link_component_nonisolated_linear_graph_witness:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  assumes hvertices:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
        (\<exists>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l)"
  shows "\<exists>L. geotop_is_linear_graph L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> geotop_complex_connected L
          \<and> (\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>l\<in>L. geotop_is_edge l \<and> w \<in> l))"
proof -
  obtain L where hL_complex: "geotop_is_complex L"
    and hL_1dim: "geotop_complex_is_1dim L"
    and hL_fin: "finite L"
    and hL_poly: "geotop_polyhedron L = C"
    and hL_conn: "geotop_complex_connected L"
    and hL_noiso: "\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>l\<in>L. geotop_is_edge l \<and> w \<in> l)"
    using geotop_link_component_nonisolated_subcomplex_witness
      [OF hK hv hP hC hvertices]
    by (by100 blast)
  have hL_linear: "geotop_is_linear_graph L"
    by (rule geotop_complex_1dim_imp_linear_graph_dev34[OF hL_complex hL_1dim])
  show ?thesis
    using hL_linear hL_fin hL_poly hL_conn hL_noiso by (by100 blast)
qed

lemma geotop_link_components_nonisolated_subcomplex_witnesses:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hvertices:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
        (\<exists>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l)"
  shows "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
          C = geotop_component_at UNIV geotop_euclidean_topology
                (\<Union>(geotop_link K v)) P)
        \<longrightarrow> (\<exists>L. geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> geotop_complex_connected L
          \<and> (\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>l\<in>L. geotop_is_edge l \<and> w \<in> l)))"
proof (intro allI impI)
  fix C
  assume hC_ex: "\<exists>P\<in>\<Union>(geotop_link K v).
          C = geotop_component_at UNIV geotop_euclidean_topology
                (\<Union>(geotop_link K v)) P"
  obtain P where hP: "P \<in> \<Union>(geotop_link K v)"
    and hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                (\<Union>(geotop_link K v)) P"
    using hC_ex by (by100 blast)
  show "\<exists>L. geotop_is_complex L
          \<and> geotop_complex_is_1dim L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> geotop_complex_connected L
          \<and> (\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>l\<in>L. geotop_is_edge l \<and> w \<in> l))"
    by (rule geotop_link_component_nonisolated_subcomplex_witness
        [OF hK hv hP hC hvertices])
qed

lemma geotop_link_components_nonisolated_linear_graph_witnesses:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hvertices:
    "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
        (\<exists>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l)"
  shows "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
          C = geotop_component_at UNIV geotop_euclidean_topology
                (\<Union>(geotop_link K v)) P)
        \<longrightarrow> (\<exists>L. geotop_is_linear_graph L
          \<and> finite L
          \<and> geotop_polyhedron L = C
          \<and> geotop_complex_connected L
          \<and> (\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>l\<in>L. geotop_is_edge l \<and> w \<in> l)))"
proof (intro allI impI)
  fix C
  assume hC_ex: "\<exists>P\<in>\<Union>(geotop_link K v).
          C = geotop_component_at UNIV geotop_euclidean_topology
                (\<Union>(geotop_link K v)) P"
  obtain P where hP: "P \<in> \<Union>(geotop_link K v)"
    and hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                (\<Union>(geotop_link K v)) P"
    using hC_ex by (by100 blast)
  show "\<exists>L. geotop_is_linear_graph L \<and> finite L
      \<and> geotop_polyhedron L = C \<and> geotop_complex_connected L
      \<and> (\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>l\<in>L. geotop_is_edge l \<and> w \<in> l))"
    by (rule geotop_link_component_nonisolated_linear_graph_witness
        [OF hK hv hP hC hvertices])
qed

lemma geotop_finite_components_real_line_minus_two_dev34:
  fixes a b :: real
  shows "finite (components (UNIV - {a, b}))"
proof (cases "a = b")
  case True
  define A where "A = {{..<a}, {a<..}}"
  have hpair: "pairwise disjnt A"
    unfolding A_def by (auto simp: pairwise_insert disjnt_def)
  have hUnion: "\<Union>A = UNIV - {a, b}"
    unfolding A_def using True by (by100 auto)
  have hsets:
    "\<And>X. X \<in> A \<Longrightarrow> open X \<and> connected X \<and> X \<noteq> {}"
  proof -
    fix X assume hX: "X \<in> A"
    consider (L) "X = {..<a}" | (R) "X = {a<..}"
      using hX unfolding A_def by (by100 blast)
    thus "open X \<and> connected X \<and> X \<noteq> {}"
    proof cases
      case L
      have "(a - 1) \<in> {..<a}" by (by100 simp)
      thus ?thesis using L by (by100 simp)
    next
      case R
      have "(a + 1) \<in> {a<..}" by (by100 simp)
      thus ?thesis using R by (by100 simp)
    qed
  qed
  have hcomp: "components (UNIV - {a, b}) = A"
    by (rule components_open_unique[OF hpair hUnion hsets])
  show ?thesis unfolding hcomp A_def by (by100 simp)
next
  case False
  let ?l = "min a b"
  let ?u = "max a b"
  define A where "A = {{..< ?l}, {?l <..< ?u}, {?u <..}}"
  have hlu: "?l < ?u"
    using False by (by100 simp)
  have hpair: "pairwise disjnt A"
    unfolding A_def by (auto simp: pairwise_insert disjnt_def)
  have hUnion: "\<Union>A = UNIV - {a, b}"
    unfolding A_def using False by (by100 auto)
  have hsets:
    "\<And>X. X \<in> A \<Longrightarrow> open X \<and> connected X \<and> X \<noteq> {}"
  proof -
    fix X assume hX: "X \<in> A"
    consider (L) "X = {..< ?l}" | (M) "X = {?l <..< ?u}" | (R) "X = {?u <..}"
      using hX unfolding A_def by (by100 blast)
    thus "open X \<and> connected X \<and> X \<noteq> {}"
    proof cases
      case L
      have hla: "?l \<le> a" by (rule min.cobounded1)
      have hlb: "?l \<le> b" by (rule min.cobounded2)
      have hlt_a: "?l - 1 < a" using hla by (by100 linarith)
      have hlt_b: "?l - 1 < b" using hlb by (by100 linarith)
      have hmem: "(?l - 1) \<in> {..< ?l}"
        using hlt_a hlt_b by (by100 simp)
      have "open X" using L by (by100 simp)
      moreover have "connected X" using L by (by100 simp)
      moreover have "X \<noteq> {}" using L hmem by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    next
      case M
      have hmem: "((?l + ?u) / 2) \<in> {?l <..< ?u}"
        using hlu by (by100 simp)
      have "open X" using M by (by100 simp)
      moreover have "connected X" using M by (by100 simp)
      moreover have "X \<noteq> {}" using M hmem by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    next
      case R
      have hau: "a \<le> ?u" by (rule max.cobounded1)
      have hbu: "b \<le> ?u" by (rule max.cobounded2)
      have hlt_a: "a < ?u + 1" using hau by (by100 linarith)
      have hlt_b: "b < ?u + 1" using hbu by (by100 linarith)
      have hmem: "(?u + 1) \<in> {?u <..}"
        using hlt_a hlt_b by (by100 simp)
      have "open X" using R by (by100 simp)
      moreover have "connected X" using R by (by100 simp)
      moreover have "X \<noteq> {}" using R hmem by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
  qed
  have hcomp: "components (UNIV - {a, b}) = A"
    by (rule components_open_unique[OF hpair hUnion hsets])
  show ?thesis unfolding hcomp A_def by (by100 simp)
qed

lemma geotop_finite_components_homeomorphism_dev34:
  assumes hhom: "homeomorphism A B f g"
  assumes hfin: "finite (components B)"
  shows "finite (components A)"
proof -
  have hcomp_sub:
    "components A \<subseteq> (\<lambda>D. g ` D) ` components B"
  proof
    fix C assume hC: "C \<in> components A"
    obtain x where hxA: "x \<in> A"
      and hC_eq: "C = connected_component_set A x"
      using hC componentsE by (by100 blast)
    have hfxB: "f x \<in> B"
      using hhom hxA unfolding homeomorphism_def by (by100 blast)
    define D where "D = connected_component_set B (f x)"
    have hD_comp: "D \<in> components B"
      unfolding D_def by (rule componentsI[OF hfxB])
    have hBA: "homeomorphism B A g f"
      by (rule homeomorphism_symD[OF hhom])
    have hcc:
      "connected_component_set A (g (f x)) =
        g ` connected_component_set B (f x)"
      by (rule connected_component_set_homeomorphism[OF hBA hfxB])
    have hgf: "g (f x) = x"
      using hhom hxA by (rule homeomorphism_apply1)
    have "C = g ` D"
      using hC_eq hcc hgf unfolding D_def by (by100 simp)
    thus "C \<in> (\<lambda>D. g ` D) ` components B"
      using hD_comp by (by100 blast)
  qed
  have himage_fin: "finite ((\<lambda>D. g ` D) ` components B)"
    by (rule finite_imageI[OF hfin])
  show "finite (components A)"
    by (rule finite_subset[OF hcomp_sub himage_fin])
qed

lemma geotop_finite_components_punctured_circle_three_points_R2:
  fixes P q1 q2 q3 :: "real^2"
  assumes hr: "r > 0"
  assumes hq1: "q1 \<in> sphere P r"
  assumes hq2: "q2 \<in> sphere P r"
  assumes hq3: "q3 \<in> sphere P r"
  assumes hq12: "q1 \<noteq> q2"
  assumes hq13: "q1 \<noteq> q3"
  assumes hq23: "q2 \<noteq> q3"
  shows "finite (components (sphere P r - {q1, q2, q3}))"
proof -
  let ?S = "sphere P r"
  let ?A = "?S - {q1, q2, q3}"
  let ?L = "{x::real^2. (q2 - q1) \<bullet> x = 0}"
  have hc_nonzero: "q2 - q1 \<noteq> 0"
    using hq12 by (by100 auto)
  have hpunctured_homeo_line: "(?S - {q1}) homeomorphic ?L"
    by (rule homeomorphic_punctured_sphere_hyperplane
        [OF hr hq1 hc_nonzero])
  obtain f g where hfg: "homeomorphism (?S - {q1}) ?L f g"
    using hpunctured_homeo_line unfolding homeomorphic_def by (by100 blast)
  define a where "a = f q2"
  define b where "b = f q3"
  have hq2_dom: "q2 \<in> ?S - {q1}"
    using hq2 hq12 by (by100 blast)
  have hq3_dom: "q3 \<in> ?S - {q1}"
    using hq3 hq13 by (by100 blast)
  have hf_img: "f ` (?S - {q1}) = ?L"
    using hfg by (rule homeomorphism_image1)
  have hgf: "\<And>x. x \<in> ?S - {q1} \<Longrightarrow> g (f x) = x"
    using hfg by (rule homeomorphism_apply1)
  have hinj: "inj_on f (?S - {q1})"
  proof (unfold inj_on_def, intro ballI impI)
    fix x y
    assume hx: "x \<in> ?S - {q1}"
      and hy: "y \<in> ?S - {q1}"
      and hxy: "f x = f y"
    have "g (f x) = g (f y)" using hxy by (by100 simp)
    thus "x = y" using hgf[OF hx] hgf[OF hy] by (by100 simp)
  qed
  have hcircle_line_image:
    "f ` ?A = ?L - {a, b}"
  proof
    show "f ` ?A \<subseteq> ?L - {a, b}"
    proof
      fix y assume hy: "y \<in> f ` ?A"
      obtain x where hxA: "x \<in> ?A" and hy_eq: "y = f x"
        using hy by (by100 blast)
      have hx_dom: "x \<in> ?S - {q1}" using hxA by (by100 blast)
      have hx_ne_q2: "x \<noteq> q2" using hxA by (by100 blast)
      have hx_ne_q3: "x \<noteq> q3" using hxA by (by100 blast)
      have hy_L: "y \<in> ?L" using hy_eq hx_dom hf_img by (by100 blast)
      have hy_ne_a: "y \<noteq> a"
      proof
        assume hya: "y = a"
        have "f x = f q2" using hya hy_eq unfolding a_def by (by100 simp)
        hence "x = q2"
          using hinj hx_dom hq2_dom unfolding inj_on_def by (by100 blast)
        thus False using hx_ne_q2 by (by100 blast)
      qed
      have hy_ne_b: "y \<noteq> b"
      proof
        assume hyb: "y = b"
        have "f x = f q3" using hyb hy_eq unfolding b_def by (by100 simp)
        hence "x = q3"
          using hinj hx_dom hq3_dom unfolding inj_on_def by (by100 blast)
        thus False using hx_ne_q3 by (by100 blast)
      qed
      show "y \<in> ?L - {a, b}" using hy_L hy_ne_a hy_ne_b by (by100 blast)
    qed
    show "?L - {a, b} \<subseteq> f ` ?A"
    proof
      fix y assume hy: "y \<in> ?L - {a, b}"
      have hy_L: "y \<in> ?L" using hy by (by100 blast)
      have hy_ne_a: "y \<noteq> a" using hy by (by100 blast)
      have hy_ne_b: "y \<noteq> b" using hy by (by100 blast)
      have hy_img: "y \<in> f ` (?S - {q1})"
        using hf_img hy_L by (by100 simp)
      obtain x where hx_dom: "x \<in> ?S - {q1}" and hfx: "f x = y"
        using hy_img by (by100 blast)
      have hx_ne_q2: "x \<noteq> q2"
      proof
        assume hxq2: "x = q2"
        hence "y = a" using hfx unfolding a_def by (by100 simp)
        thus False using hy_ne_a by (by100 blast)
      qed
      have hx_ne_q3: "x \<noteq> q3"
      proof
        assume hxq3: "x = q3"
        hence "y = b" using hfx unfolding b_def by (by100 simp)
        thus False using hy_ne_b by (by100 blast)
      qed
      have "x \<in> ?A" using hx_dom hx_ne_q2 hx_ne_q3 by (by100 blast)
      thus "y \<in> f ` ?A" using hfx by (by100 blast)
    qed
  qed
  have hcircle_line_homeomorphism:
    "homeomorphism ?A (?L - {a, b}) f g"
  proof (rule homeomorphism_of_subsets[OF hfg])
    show "?A \<subseteq> ?S - {q1}" by (by100 blast)
    show "?L - {a, b} \<subseteq> ?L" by (by100 blast)
    show "f ` ?A = ?L - {a, b}" by (rule hcircle_line_image)
  qed
  have hline_components_finite: "finite (components (?L - {a, b}))"
  proof -
    have hL_dim: "aff_dim ?L = 1"
      using hc_nonzero aff_dim_hyperplane[of "q2 - q1" 0]
      by (by100 simp)
    have hreal_dim: "aff_dim (UNIV::real set) = 1"
      by (by100 simp)
    have hL_homeo_real: "?L homeomorphic (UNIV::real set)"
    proof (rule homeomorphic_affine_sets)
      show "affine ?L" by (rule affine_hyperplane)
      show "affine (UNIV::real set)" by (rule affine_UNIV)
      show "aff_dim ?L = aff_dim (UNIV::real set)"
        using hL_dim hreal_dim by (by100 simp)
    qed
    obtain h j where hhj: "homeomorphism ?L (UNIV::real set) h j"
      using hL_homeo_real unfolding homeomorphic_def by (by100 blast)
    have ha_L: "a \<in> ?L" unfolding a_def using hq2_dom hf_img by (by100 blast)
    have hb_L: "b \<in> ?L" unfolding b_def using hq3_dom hf_img by (by100 blast)
    have hjh: "\<And>x. x \<in> ?L \<Longrightarrow> j (h x) = x"
      using hhj by (rule homeomorphism_apply1)
    have h_line_real_image:
      "h ` (?L - {a, b}) = (UNIV::real set) - {h a, h b}"
    proof
      show "h ` (?L - {a, b}) \<subseteq> (UNIV::real set) - {h a, h b}"
      proof
        fix y assume hy: "y \<in> h ` (?L - {a, b})"
        obtain x where hx: "x \<in> ?L - {a, b}" and hy_eq: "y = h x"
          using hy by (by100 blast)
        have hxL: "x \<in> ?L" using hx by (by100 blast)
        have hx_ne_a: "x \<noteq> a" using hx by (by100 blast)
        have hx_ne_b: "x \<noteq> b" using hx by (by100 blast)
        have hy_ne_ha: "y \<noteq> h a"
        proof
          assume hya: "y = h a"
          have "j (h x) = j (h a)" using hya hy_eq by (by100 simp)
          hence "x = a" using hjh[OF hxL] hjh[OF ha_L] by (by100 simp)
          thus False using hx_ne_a by (by100 blast)
        qed
        have hy_ne_hb: "y \<noteq> h b"
        proof
          assume hyb: "y = h b"
          have "j (h x) = j (h b)" using hyb hy_eq by (by100 simp)
          hence "x = b" using hjh[OF hxL] hjh[OF hb_L] by (by100 simp)
          thus False using hx_ne_b by (by100 blast)
        qed
        show "y \<in> (UNIV::real set) - {h a, h b}"
          using hy_ne_ha hy_ne_hb by (by100 blast)
      qed
      show "(UNIV::real set) - {h a, h b} \<subseteq> h ` (?L - {a, b})"
      proof
        fix y assume hy: "y \<in> (UNIV::real set) - {h a, h b}"
        have hjy_L: "j y \<in> ?L"
          using hhj unfolding homeomorphism_def by (by100 blast)
        have hhy: "h (j y) = y"
          using hhj by (rule homeomorphism_apply2[of ?L "UNIV::real set" h j y, simplified])
        have hjy_ne_a: "j y \<noteq> a"
        proof
          assume hja: "j y = a"
          hence "y = h a" using hhy by (by100 simp)
          thus False using hy by (by100 blast)
        qed
        have hjy_ne_b: "j y \<noteq> b"
        proof
          assume hjb: "j y = b"
          hence "y = h b" using hhy by (by100 simp)
          thus False using hy by (by100 blast)
        qed
        have "j y \<in> ?L - {a, b}" using hjy_L hjy_ne_a hjy_ne_b by (by100 blast)
        hence "h (j y) \<in> h ` (?L - {a, b})" by (rule imageI)
        thus "y \<in> h ` (?L - {a, b})" using hhy by (by100 simp)
      qed
    qed
    have hline_real_homeomorphism:
      "homeomorphism (?L - {a, b}) ((UNIV::real set) - {h a, h b}) h j"
    proof (rule homeomorphism_of_subsets[OF hhj])
      show "?L - {a, b} \<subseteq> ?L" by (by100 blast)
      show "(UNIV::real set) - {h a, h b} \<subseteq> UNIV" by (by100 blast)
      show "h ` (?L - {a, b}) = (UNIV::real set) - {h a, h b}"
        by (rule h_line_real_image)
    qed
    have hreal_fin: "finite (components ((UNIV::real set) - {h a, h b}))"
      by (rule geotop_finite_components_real_line_minus_two_dev34)
    show ?thesis
      by (rule geotop_finite_components_homeomorphism_dev34
          [OF hline_real_homeomorphism hreal_fin])
  qed
  show ?thesis
    by (rule geotop_finite_components_homeomorphism_dev34
        [OF hcircle_line_homeomorphism hline_components_finite])
qed

lemma geotop_incident_edge_link_nonempty:
  fixes K :: "(real^2) set set" and e :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  shows "geotop_link K v \<noteq> {}"
proof -
  have he_dim: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  obtain V m where hV_fin: "finite V"
    and hV_card: "card V = 1 + 1"
    and h1_le_m: "1 \<le> m"
    and hgp_V: "geotop_general_position V m"
    and he_eq: "e = geotop_convex_hull V"
    using he_dim unfolding geotop_simplex_dim_def by (by100 blast)
  have heV: "geotop_simplex_vertices e V"
    unfolding geotop_simplex_vertices_def
    using hV_fin hV_card h1_le_m hgp_V he_eq by (by100 blast)
  obtain V' where heV': "geotop_simplex_vertices e V'"
    and hvV': "v \<in> V'"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK heK hv_e]
    by (by100 blast)
  have hV'_eq: "V' = V"
    by (rule geotop_simplex_vertices_unique[OF heV' heV])
  have hvV: "v \<in> V"
    using hvV' hV'_eq by (by100 simp)
  have hV_not_sub_singleton: "\<not> V \<subseteq> {v}"
  proof
    assume hsub: "V \<subseteq> {v}"
    have "card V \<le> card {v}"
      by (rule card_mono[OF finite.emptyI[THEN finite.insertI] hsub])
    hence "card V \<le> 1"
      by (by100 simp)
    thus False
      using hV_card by (by100 simp)
  qed
  obtain w where hwV: "w \<in> V" and hw_ne_v: "w \<noteq> v"
    using hV_not_sub_singleton by (by100 blast)
  let ?\<tau> = "geotop_convex_hull {w}"
  have hface: "geotop_is_face ?\<tau> e"
    unfolding geotop_is_face_def using heV hwV by (by100 blast)
  have h\<tau>_singleton: "?\<tau> = {w}"
    using geotop_convex_hull_eq_HOL[of "{w}"] by (by100 simp)
  have hv_not_\<tau>: "v \<notin> ?\<tau>"
    using h\<tau>_singleton hw_ne_v by (by100 simp)
  have h\<tau>_star: "?\<tau> \<in> geotop_star K v"
    unfolding geotop_star_def using heK hv_e hface by (by100 blast)
  have h\<tau>_link: "?\<tau> \<in> geotop_link K v"
    unfolding geotop_link_def using h\<tau>_star hv_not_\<tau> by (by100 blast)
  show ?thesis
    using h\<tau>_link by (by100 blast)
qed

lemma geotop_incident_edge_link_polyhedron_nonempty:
  fixes K :: "(real^2) set set" and e :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  shows "\<Union>(geotop_link K v) \<noteq> {}"
proof -
  have hlink_nonempty: "geotop_link K v \<noteq> {}"
    by (rule geotop_incident_edge_link_nonempty[OF hK hvK heK hedge hv_e])
  have hlink_complex: "geotop_is_complex (geotop_link K v)"
    by (rule geotop_link_is_complex[OF hK])
  have "geotop_polyhedron (geotop_link K v) \<noteq> {}"
    by (rule geotop_nonempty_complex_polyhedron_nonempty
        [OF hlink_complex hlink_nonempty])
  thus ?thesis
    unfolding geotop_polyhedron_def by (by100 simp)
qed

lemma geotop_incident_edge_link_vertex_witness:
  fixes K :: "(real^2) set set" and e :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  shows "\<exists>w. w \<noteq> v \<and> w \<in> e \<and> {w} \<in> geotop_link K v"
proof -
  have he_dim: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  obtain V m where hV_fin: "finite V"
    and hV_card: "card V = 1 + 1"
    and h1_le_m: "1 \<le> m"
    and hgp_V: "geotop_general_position V m"
    and he_eq: "e = geotop_convex_hull V"
    using he_dim unfolding geotop_simplex_dim_def by (by100 blast)
  have heV: "geotop_simplex_vertices e V"
    unfolding geotop_simplex_vertices_def
    using hV_fin hV_card h1_le_m hgp_V he_eq by (by100 blast)
  obtain V' where heV': "geotop_simplex_vertices e V'"
    and hvV': "v \<in> V'"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK heK hv_e]
    by (by100 blast)
  have hV'_eq: "V' = V"
    by (rule geotop_simplex_vertices_unique[OF heV' heV])
  have hvV: "v \<in> V"
    using hvV' hV'_eq by (by100 simp)
  have hV_not_sub_singleton: "\<not> V \<subseteq> {v}"
  proof
    assume hsub: "V \<subseteq> {v}"
    have "card V \<le> card {v}"
      by (rule card_mono[OF finite.emptyI[THEN finite.insertI] hsub])
    hence "card V \<le> 1"
      by (by100 simp)
    thus False
      using hV_card by (by100 simp)
  qed
  obtain w where hwV: "w \<in> V" and hw_ne_v: "w \<noteq> v"
    using hV_not_sub_singleton by (by100 blast)
  have hw_e: "w \<in> e"
  proof -
    have "w \<in> convex hull V"
      using hwV hull_inc[of w V] by (by100 simp)
    moreover have "geotop_convex_hull V = convex hull V"
      by (rule geotop_convex_hull_eq_HOL)
    ultimately show ?thesis
      using he_eq by (by100 simp)
  qed
  let ?\<tau> = "geotop_convex_hull {w}"
  have hface: "geotop_is_face ?\<tau> e"
    unfolding geotop_is_face_def using heV hwV by (by100 blast)
  have h\<tau>_singleton: "?\<tau> = {w}"
    using geotop_convex_hull_eq_HOL[of "{w}"] by (by100 simp)
  have hv_not_\<tau>: "v \<notin> ?\<tau>"
    using h\<tau>_singleton hw_ne_v by (by100 simp)
  have h\<tau>_star: "?\<tau> \<in> geotop_star K v"
    unfolding geotop_star_def using heK hv_e hface by (by100 blast)
  have h\<tau>_link: "?\<tau> \<in> geotop_link K v"
    unfolding geotop_link_def using h\<tau>_star hv_not_\<tau> by (by100 blast)
  have hw_link: "{w} \<in> geotop_link K v"
    using h\<tau>_singleton h\<tau>_link by (by100 simp)
  show ?thesis
  proof (intro exI conjI)
    show "w \<noteq> v"
      by (rule hw_ne_v)
    show "w \<in> e"
      by (rule hw_e)
    show "{w} \<in> geotop_link K v"
      by (rule hw_link)
  qed
qed

lemma geotop_link_vertex_incident_edge_witness:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwL: "{w} \<in> geotop_link K v"
  shows "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e \<and> w \<in> e"
proof -
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    and hv\<sigma>: "v \<in> \<sigma>"
    and hw_face_case: "geotop_is_face {w} \<sigma> \<or> {w} = \<sigma>"
    using hwL unfolding geotop_link_def geotop_star_def by (by100 blast)
  have hv_not_singleton: "v \<notin> {w}"
    using hwL unfolding geotop_link_def by (by100 blast)
  have hvw: "v \<noteq> w"
    using hv_not_singleton by (by100 simp)
  have hlink_sub: "geotop_link K v \<subseteq> K"
    by (rule geotop_link_subset_complex[OF hK])
  have hwK: "{w} \<in> K"
    using hlink_sub hwL by (by100 blast)
  have hw\<sigma>: "w \<in> \<sigma>"
  proof (rule disjE[OF hw_face_case])
    assume hface: "geotop_is_face {w} \<sigma>"
    have "{w} \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset[OF hface])
    thus ?thesis
      by (by100 simp)
  next
    assume hw_eq: "{w} = \<sigma>"
    have "w \<in> {w}"
      by (by100 simp)
    show ?thesis
      using hw_eq \<open>w \<in> {w}\<close> by (by100 blast)
  qed
  obtain V\<^sub>v where h\<sigma>Vv: "geotop_simplex_vertices \<sigma> V\<^sub>v"
    and hvVv: "v \<in> V\<^sub>v"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK h\<sigma>K hv\<sigma>]
    by (by100 blast)
  obtain V\<^sub>w where h\<sigma>Vw: "geotop_simplex_vertices \<sigma> V\<^sub>w"
    and hwVw: "w \<in> V\<^sub>w"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hwK h\<sigma>K hw\<sigma>]
    by (by100 blast)
  have hVw_eq: "V\<^sub>w = V\<^sub>v"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>Vw h\<sigma>Vv])
  have hwVv: "w \<in> V\<^sub>v"
    using hwVw hVw_eq by (by100 simp)
  show ?thesis
    by (rule geotop_complex_simplex_vertices_incident_edge_between
        [OF hK h\<sigma>K h\<sigma>Vv hvVv hwVv hvw])
qed

lemma geotop_link_polyhedron_nonempty_incident_edge_witness:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hlink_poly: "\<Union>(geotop_link K v) \<noteq> {}"
  shows "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e"
proof -
  have hlink_complex: "geotop_is_complex (geotop_link K v)"
    by (rule geotop_link_is_complex[OF hK])
  have hlink_poly_geotop: "geotop_polyhedron (geotop_link K v) \<noteq> {}"
    using hlink_poly unfolding geotop_polyhedron_def by (by100 simp)
  obtain w where hwL: "{w} \<in> geotop_link K v"
    using geotop_nonempty_polyhedron_has_complex_vertex
      [OF hlink_complex hlink_poly_geotop]
    by (by100 blast)
  obtain e where heK: "e \<in> K"
    and hedge: "geotop_is_edge e"
    and hv_e: "v \<in> e"
    using geotop_link_vertex_incident_edge_witness[OF hK hvK hwL]
    by (by100 blast)
  show ?thesis
    using heK hedge hv_e by (by100 blast)
qed

lemma geotop_link_polyhedron_nonempty_iff_incident_edge:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  shows "\<Union>(geotop_link K v) \<noteq> {}
    \<longleftrightarrow> (\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e)"
proof -
  show ?thesis
  proof
    assume hlink_poly: "\<Union>(geotop_link K v) \<noteq> {}"
    show "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e"
      by (rule geotop_link_polyhedron_nonempty_incident_edge_witness
          [OF hK hvK hlink_poly])
  next
    assume "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e"
    then obtain e where heK: "e \<in> K"
      and hedge: "geotop_is_edge e"
      and hv_e: "v \<in> e"
      by (by100 blast)
    show "\<Union>(geotop_link K v) \<noteq> {}"
      by (rule geotop_incident_edge_link_polyhedron_nonempty
          [OF hK hvK heK hedge hv_e])
  qed
qed

lemma geotop_simplex_vertex_notin_hull_of_other_vertices:
  fixes \<sigma> :: "(real^2) set" and V W :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hvV: "v \<in> V"
  assumes hW_sub: "W \<subseteq> V - {v}"
  shows "v \<notin> geotop_convex_hull W"
proof -
  have hV_ai: "\<not> affine_dependent V"
    by (rule geotop_general_position_imp_aff_indep[OF h\<sigma>V])
  have hW_sub_V: "W \<subseteq> V"
    using hW_sub by (by100 blast)
  have hW_ai: "\<not> affine_dependent W"
    by (rule affine_independent_subset[OF hV_ai hW_sub_V])
  have hinsert_sub: "insert v W \<subseteq> V"
    using hvV hW_sub by (by100 blast)
  have hinsert_ai: "\<not> affine_dependent (insert v W)"
    by (rule affine_independent_subset[OF hV_ai hinsert_sub])
  have hv_not_W: "v \<notin> W"
    using hW_sub by (by100 blast)
  have hv_not_aff: "v \<notin> affine hull W"
  proof
    assume hv_aff: "v \<in> affine hull W"
    have "affine_dependent (insert v W)"
      using affine_dependent_choose[OF hW_ai, of v] hv_not_W hv_aff
      by (by100 simp)
    thus False
      using hinsert_ai by (by100 blast)
  qed
  have hconv_sub_aff: "convex hull W \<subseteq> affine hull W"
    by (rule convex_hull_subset_affine_hull)
  show ?thesis
  proof
    assume hv_hull: "v \<in> geotop_convex_hull W"
    have "v \<in> convex hull W"
      using hv_hull geotop_convex_hull_eq_HOL[of W] by (by100 simp)
    hence "v \<in> affine hull W"
      using hconv_sub_aff by (by100 blast)
    thus False
      using hv_not_aff by (by100 blast)
  qed
qed

lemma geotop_simplex_point_radial_to_opposite_face_dev34:
  fixes \<sigma> :: "(real^2) set" and V :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hvV: "v \<in> V"
  assumes hx: "x \<in> \<sigma>"
  assumes hx_ne_v: "x \<noteq> v"
  shows "\<exists>y t. y \<in> geotop_convex_hull (V - {v})
      \<and> 0 < t \<and> t \<le> 1
      \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y"
proof -
  obtain m n where hV_fin: "finite V"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<sigma>_HOL: "\<sigma> = convex hull V"
    using h\<sigma>_eq geotop_convex_hull_eq_HOL[of V] by (by100 simp)
  obtain a where ha_nonneg: "\<forall>w\<in>V. 0 \<le> a w"
    and ha_sum: "(\<Sum>w\<in>V. a w) = 1"
    and hx_sum: "(\<Sum>w\<in>V. a w *\<^sub>R w) = x"
    using hx h\<sigma>_HOL convex_hull_finite[OF hV_fin] by (by100 blast)
  let ?W = "V - {v}"
  define t where "t = (\<Sum>w\<in>?W. a w)"
  have hW_fin: "finite ?W"
    using hV_fin by (by100 simp)
  have hsum_split: "(\<Sum>w\<in>V. a w) = a v + (\<Sum>w\<in>?W. a w)"
    using hV_fin hvV by (subst sum.remove) (by100 simp_all)
  have ht_eq: "t = 1 - a v"
    using ha_sum hsum_split unfolding t_def by (by100 simp)
  have ht_nonneg: "0 \<le> t"
    unfolding t_def using ha_nonneg by (by100 simp)
  have hav_nonneg: "0 \<le> a v"
    using ha_nonneg hvV by (by100 blast)
  have ht_le_1: "t \<le> 1"
    using ht_eq hav_nonneg by (by100 simp)
  have ht_pos: "0 < t"
  proof (rule ccontr)
    assume hnot: "\<not> 0 < t"
    have ht_zero: "t = 0"
      using ht_nonneg hnot by (by100 simp)
    have hzero_W: "\<forall>w\<in>?W. a w = 0"
    proof
      fix w assume hw: "w \<in> ?W"
      have hsum_zero: "(\<Sum>w\<in>?W. a w) = 0"
        using ht_zero unfolding t_def by (by100 simp)
      show "a w = 0"
        using sum_nonneg_eq_0_iff[OF hW_fin, of a] ha_nonneg hw hsum_zero
        by (by100 simp)
    qed
    have hav_one: "a v = 1"
      using ha_sum hsum_split ht_zero unfolding t_def by (by100 simp)
    have hvec_split: "(\<Sum>w\<in>V. a w *\<^sub>R w) =
        a v *\<^sub>R v + (\<Sum>w\<in>?W. a w *\<^sub>R w)"
      using hV_fin hvV by (subst sum.remove) (by100 simp_all)
    have hsum_zero_vec: "(\<Sum>w\<in>?W. a w *\<^sub>R w) = 0"
      by (rule sum.neutral) (use hzero_W in \<open>by100 simp\<close>)
    have "x = v"
      using hx_sum hvec_split hsum_zero_vec hav_one by (by100 simp)
    show False
      using hx_ne_v \<open>x = v\<close> by (by100 blast)
  qed
  define y where "y = (\<Sum>w\<in>?W. (a w / t) *\<^sub>R w)"
  have hy_hull_HOL: "y \<in> convex hull ?W"
  proof -
    have hcoeff_nonneg: "\<forall>w\<in>?W. 0 \<le> a w / t"
      using ha_nonneg ht_pos by (by100 simp)
    have hcoeff_sum: "(\<Sum>w\<in>?W. a w / t) = 1"
      using ht_pos unfolding t_def by (by100 simp)
    show ?thesis
      unfolding y_def convex_hull_finite[OF hW_fin]
      using hcoeff_nonneg hcoeff_sum by (by100 blast)
  qed
  have hy_hull: "y \<in> geotop_convex_hull ?W"
    using hy_hull_HOL geotop_convex_hull_eq_HOL[of ?W] by (by100 simp)
  have hvec_split: "(\<Sum>w\<in>V. a w *\<^sub>R w) =
      a v *\<^sub>R v + (\<Sum>w\<in>?W. a w *\<^sub>R w)"
    using hV_fin hvV by (subst sum.remove) (by100 simp_all)
  have ht_y: "t *\<^sub>R y = (\<Sum>w\<in>?W. a w *\<^sub>R w)"
    unfolding y_def
    using ht_pos
    by (by100 simp add: scaleR_right.sum scaleR_scaleR)
  have hx_decomp: "x = (1 - t) *\<^sub>R v + t *\<^sub>R y"
    using hx_sum hvec_split ht_y ht_eq by (by100 simp)
  show ?thesis
    using hy_hull ht_pos ht_le_1 hx_decomp by (by100 blast)
qed

lemma geotop_simplex_opposite_face_in_link_dev34:
  fixes K :: "(real^2) set set" and \<sigma> V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hvV: "v \<in> V"
  assumes hW_ne: "V - {v} \<noteq> {}"
  shows "geotop_convex_hull (V - {v}) \<in> geotop_link K v"
proof -
  let ?W = "V - {v}"
  let ?\<tau> = "geotop_convex_hull ?W"
  have hW_sub: "?W \<subseteq> V"
    by (by100 blast)
  have hface: "geotop_is_face ?\<tau> \<sigma>"
    unfolding geotop_is_face_def
    using h\<sigma>V hW_ne hW_sub by (by100 blast)
  have hv\<sigma>: "v \<in> \<sigma>"
  proof -
    have "v \<in> convex hull V"
      using hvV hull_inc[of v V] by (by100 simp)
    moreover have "\<sigma> = convex hull V"
    proof -
      obtain m n where "\<sigma> = geotop_convex_hull V"
        using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
      thus ?thesis using geotop_convex_hull_eq_HOL[of V] by (by100 simp)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  have hv_not_\<tau>: "v \<notin> ?\<tau>"
    by (rule geotop_simplex_vertex_notin_hull_of_other_vertices
        [OF h\<sigma>V hvV]) (by100 blast)
  have h\<tau>star: "?\<tau> \<in> geotop_star K v"
    unfolding geotop_star_def using h\<sigma>K hv\<sigma> hface by (by100 blast)
  show ?thesis
    unfolding geotop_link_def using h\<tau>star hv_not_\<tau> by (by100 blast)
qed

lemma geotop_complex_simplex_point_radial_to_link_dev34:
  fixes K :: "(real^2) set set" and \<sigma> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes hv\<sigma>: "v \<in> \<sigma>"
  assumes hx\<sigma>: "x \<in> \<sigma>"
  assumes hx_ne_v: "x \<noteq> v"
  shows "\<exists>y t. y \<in> \<Union>(geotop_link K v)
      \<and> 0 < t \<and> t \<le> 1
      \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y"
proof -
  obtain V where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hvV: "v \<in> V"
    by (rule geotop_complex_singleton_point_is_simplex_vertex
        [OF hK hvK h\<sigma>K hv\<sigma>])
  obtain y t where hy: "y \<in> geotop_convex_hull (V - {v})"
    and ht_pos: "0 < t"
    and ht_le: "t \<le> 1"
    and hx_decomp: "x = (1 - t) *\<^sub>R v + t *\<^sub>R y"
    using geotop_simplex_point_radial_to_opposite_face_dev34
      [OF h\<sigma>V hvV hx\<sigma> hx_ne_v]
    by (by100 blast)
  have hW_ne: "V - {v} \<noteq> {}"
  proof
    assume hW_empty: "V - {v} = {}"
    have "geotop_convex_hull (V - {v}) = {}"
      using hW_empty geotop_convex_hull_eq_HOL[of "V - {v}"] by (by100 simp)
    thus False using hy by (by100 blast)
  qed
  have hface_link: "geotop_convex_hull (V - {v}) \<in> geotop_link K v"
    by (rule geotop_simplex_opposite_face_in_link_dev34
        [OF hK h\<sigma>K h\<sigma>V hvV hW_ne])
  have hy_link: "y \<in> \<Union>(geotop_link K v)"
    using hy hface_link by (by100 blast)
  show ?thesis
    using hy_link ht_pos ht_le hx_decomp by (by100 blast)
qed

lemma geotop_star_punctured_point_radial_to_link_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hx: "x \<in> \<Union>(geotop_star K v) - {v}"
  shows "\<exists>y t. y \<in> \<Union>(geotop_link K v)
      \<and> 0 < t \<and> t \<le> 1
      \<and> x = (1 - t) *\<^sub>R v + t *\<^sub>R y"
proof -
  obtain \<tau> where h\<tau>star: "\<tau> \<in> geotop_star K v"
    and hx\<tau>: "x \<in> \<tau>"
    using hx by (by100 blast)
  have hx_ne_v: "x \<noteq> v"
    using hx by (by100 blast)
  have hvK: "{v} \<in> K"
    using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
  show ?thesis
  proof (cases "v \<in> \<tau>")
    case True
    have h\<tau>K: "\<tau> \<in> K"
    proof -
      have hstar_sub: "geotop_star K v \<subseteq> K"
        by (rule geotop_star_subset_complex[OF hK])
      show ?thesis using hstar_sub h\<tau>star by (by100 blast)
    qed
    show ?thesis
      by (rule geotop_complex_simplex_point_radial_to_link_dev34
          [OF hK hvK h\<tau>K True hx\<tau> hx_ne_v])
  next
    case False
    have h\<tau>link: "\<tau> \<in> geotop_link K v"
      unfolding geotop_link_def using h\<tau>star False by (by100 blast)
    have hx_link: "x \<in> \<Union>(geotop_link K v)"
      using h\<tau>link hx\<tau> by (by100 blast)
    have hx_decomp: "x = (1 - 1) *\<^sub>R v + 1 *\<^sub>R x"
      by (by100 simp)
    show ?thesis
      using hx_link hx_decomp by (intro exI[of _ x] exI[of _ 1]) (by100 simp)
  qed
qed

lemma geotop_simplex_opposite_edge_in_link:
  fixes K :: "(real^2) set set" and \<sigma> V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hvV: "v \<in> V"
  assumes hwV: "w \<in> V"
  assumes huV: "u \<in> V"
  assumes hvw: "v \<noteq> w"
  assumes hvu: "v \<noteq> u"
  assumes hwu: "w \<noteq> u"
  shows "geotop_convex_hull {w, u} \<in> geotop_link K v
      \<and> geotop_is_edge (geotop_convex_hull {w, u})
      \<and> w \<in> geotop_convex_hull {w, u}
      \<and> u \<in> geotop_convex_hull {w, u}"
proof -
  obtain m n where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  let ?\<tau> = "geotop_convex_hull {w, u}"
  have hpair_sub: "{w, u} \<subseteq> V"
    using hwV huV by (by100 blast)
  have hpair_fin: "finite {w, u}"
    by (by100 simp)
  have hpair_card: "card {w, u} = 2"
    using hwu by (by100 simp)
  have hpair_card_le: "card {w, u} \<le> card V"
    by (rule card_mono[OF hV_fin hpair_sub])
  have hn_ge1: "1 \<le> n"
    using hV_card hpair_card hpair_card_le by (by100 linarith)
  have hm_ge1: "1 \<le> m"
    using hn_ge1 hn_le_m by (by100 linarith)
  have hgp_pair: "geotop_general_position {w, u} m"
    by (rule geotop_general_position_subset[OF hgp hpair_sub])
  have h\<tau>dim: "geotop_simplex_dim ?\<tau> 1"
    unfolding geotop_simplex_dim_def
  proof (intro exI conjI)
    show "finite {w, u}"
      by (rule hpair_fin)
    show "card {w, u} = 1 + 1"
      using hpair_card by (by100 simp)
    show "1 \<le> m"
      by (rule hm_ge1)
    show "geotop_general_position {w, u} m"
      by (rule hgp_pair)
    show "?\<tau> = geotop_convex_hull {w, u}"
      by (by100 simp)
  qed
  have h\<tau>edge: "geotop_is_edge ?\<tau>"
    using h\<tau>dim unfolding geotop_is_edge_def by (by100 simp)
  have h\<tau>face: "geotop_is_face ?\<tau> \<sigma>"
    unfolding geotop_is_face_def
  proof (intro exI conjI)
    show "geotop_simplex_vertices \<sigma> V"
      by (rule h\<sigma>V)
    show "{w, u} \<noteq> {}"
      by (by100 simp)
    show "{w, u} \<subseteq> V"
      by (rule hpair_sub)
    show "?\<tau> = geotop_convex_hull {w, u}"
      by (by100 simp)
  qed
  have hv\<sigma>: "v \<in> \<sigma>"
  proof -
    have "v \<in> convex hull V"
      using hvV hull_inc[of v V] by (by100 simp)
    moreover have "\<sigma> = convex hull V"
      using h\<sigma>_eq geotop_convex_hull_eq_HOL[of V] by (by100 simp)
    ultimately show ?thesis
      by (by100 simp)
  qed
  have hpair_other: "{w, u} \<subseteq> V - {v}"
    using hwV huV hvw hvu by (by100 blast)
  have hv_not_\<tau>: "v \<notin> ?\<tau>"
    by (rule geotop_simplex_vertex_notin_hull_of_other_vertices
        [OF h\<sigma>V hvV hpair_other])
  have h\<tau>star: "?\<tau> \<in> geotop_star K v"
    unfolding geotop_star_def using h\<sigma>K hv\<sigma> h\<tau>face by (by100 blast)
  have h\<tau>link: "?\<tau> \<in> geotop_link K v"
    unfolding geotop_link_def using h\<tau>star hv_not_\<tau> by (by100 blast)
  have hw\<tau>: "w \<in> ?\<tau>"
  proof -
    have "w \<in> convex hull {w, u}"
      using hull_inc[of w "{w, u}"] by (by100 simp)
    thus ?thesis
      using geotop_convex_hull_eq_HOL[of "{w, u}"] by (by100 simp)
  qed
  have hu\<tau>: "u \<in> ?\<tau>"
  proof -
    have "u \<in> convex hull {w, u}"
      using hull_inc[of u "{w, u}"] by (by100 simp)
    thus ?thesis
      using geotop_convex_hull_eq_HOL[of "{w, u}"] by (by100 simp)
  qed
  show ?thesis
    using h\<tau>link h\<tau>edge hw\<tau> hu\<tau> by (by100 blast)
qed

lemma geotop_simplex_opposite_edge_face_in_link:
  fixes K :: "(real^2) set set" and \<sigma> V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hvV: "v \<in> V"
  assumes hwV: "w \<in> V"
  assumes huV: "u \<in> V"
  assumes hvw: "v \<noteq> w"
  assumes hvu: "v \<noteq> u"
  assumes hwu: "w \<noteq> u"
  shows "geotop_is_face (geotop_convex_hull {w, u}) \<sigma>
      \<and> geotop_convex_hull {w, u} \<in> geotop_link K v
      \<and> geotop_is_edge (geotop_convex_hull {w, u})
      \<and> w \<in> geotop_convex_hull {w, u}
      \<and> u \<in> geotop_convex_hull {w, u}"
proof -
  let ?\<tau> = "geotop_convex_hull {w, u}"
  have hpair_sub: "{w, u} \<subseteq> V"
    using hwV huV by (by100 blast)
  have hface: "geotop_is_face ?\<tau> \<sigma>"
    unfolding geotop_is_face_def
  proof (intro exI conjI)
    show "geotop_simplex_vertices \<sigma> V"
      by (rule h\<sigma>V)
    show "{w, u} \<noteq> {}"
      by (by100 simp)
    show "{w, u} \<subseteq> V"
      by (rule hpair_sub)
    show "?\<tau> = geotop_convex_hull {w, u}"
      by (by100 simp)
  qed
  have hopposite:
    "?\<tau> \<in> geotop_link K v
      \<and> geotop_is_edge ?\<tau>
      \<and> w \<in> ?\<tau>
      \<and> u \<in> ?\<tau>"
    by (rule geotop_simplex_opposite_edge_in_link
        [OF hK h\<sigma>K h\<sigma>V hvV hwV huV hvw hvu hwu])
  show ?thesis
    using hface hopposite by (by100 blast)
qed

lemma geotop_edge_face_witness_card_two:
  fixes e \<sigma> :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  assumes hface: "geotop_is_face e \<sigma>"
  obtains V W where "geotop_simplex_vertices \<sigma> V"
    and "W \<noteq> {}" and "W \<subseteq> V"
    and "e = geotop_convex_hull W"
    and "geotop_simplex_vertices e W"
    and "card W = 2"
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}" and hW_sub: "W \<subseteq> V"
    and he_eq: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    by (rule geotop_face_witness_simplex_vertices[OF hface])
  have he_dim: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  obtain V\<^sub>e m where hVe_fin: "finite V\<^sub>e"
    and hVe_card: "card V\<^sub>e = 1 + 1"
    and h1_le_m: "1 \<le> m"
    and hgp_Ve: "geotop_general_position V\<^sub>e m"
    and he_Ve: "e = geotop_convex_hull V\<^sub>e"
    using he_dim unfolding geotop_simplex_dim_def by (by100 blast)
  have heVe: "geotop_simplex_vertices e V\<^sub>e"
    unfolding geotop_simplex_vertices_def
    using hVe_fin hVe_card h1_le_m hgp_Ve he_Ve by (by100 blast)
  have hW_eq: "W = V\<^sub>e"
    by (rule geotop_simplex_vertices_unique[OF heW heVe])
  have hW_card: "card W = 2"
    using hW_eq hVe_card by (by100 simp)
  show ?thesis
    by (rule that[OF h\<sigma>V hW_ne hW_sub he_eq heW hW_card])
qed

lemma geotop_pair_convex_hull_simplex_vertices_dev34:
  fixes w u :: "real^2"
  assumes hwu: "w \<noteq> u"
  shows "geotop_simplex_vertices (geotop_convex_hull {w, u}) {w, u}"
proof -
  have hfin: "finite {w, u}"
    by (by100 simp)
  have hne: "{w, u} \<noteq> {}"
    by (by100 simp)
  have hai: "\<not> affine_dependent {w, u}"
    by (rule affine_independent_2)
  show ?thesis
    by (rule geotop_AI_finite_ne_is_simplex_vertices[OF hfin hne hai])
qed

lemma geotop_complex_edge_vertices_pair_dev34:
  fixes K :: "(real^2) set set" and e :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwK: "{w} \<in> K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  assumes hw_e: "w \<in> e"
  assumes hvw: "v \<noteq> w"
  shows "geotop_simplex_vertices e {v, w}"
proof -
  have he_dim: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  obtain V m where hV_fin: "finite V"
    and hV_card: "card V = 1 + 1"
    and h1_le_m: "1 \<le> m"
    and hgp_V: "geotop_general_position V m"
    and he_eq: "e = geotop_convex_hull V"
    using he_dim unfolding geotop_simplex_dim_def by (by100 blast)
  have heV: "geotop_simplex_vertices e V"
    unfolding geotop_simplex_vertices_def
    using hV_fin hV_card h1_le_m hgp_V he_eq by (by100 blast)
  obtain Vv where heVv: "geotop_simplex_vertices e Vv"
    and hvVv: "v \<in> Vv"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK heK hv_e]
    by (by100 blast)
  have hVv_eq: "Vv = V"
    by (rule geotop_simplex_vertices_unique[OF heVv heV])
  have hvV: "v \<in> V"
    using hvVv hVv_eq by (by100 simp)
  obtain Vw where heVw: "geotop_simplex_vertices e Vw"
    and hwVw: "w \<in> Vw"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hwK heK hw_e]
    by (by100 blast)
  have hVw_eq: "Vw = V"
    by (rule geotop_simplex_vertices_unique[OF heVw heV])
  have hwV: "w \<in> V"
    using hwVw hVw_eq by (by100 simp)
  have hV_sub: "V \<subseteq> {v, w}"
  proof
    fix x assume hxV: "x \<in> V"
    show "x \<in> {v, w}"
    proof (rule ccontr)
      assume hx_not: "x \<notin> {v, w}"
      have hthree_sub: "{v, w, x} \<subseteq> V"
        using hvV hwV hxV by (by100 blast)
      have hx_ne_v: "x \<noteq> v"
        using hx_not by (by100 simp)
      have hx_ne_w: "x \<noteq> w"
        using hx_not by (by100 simp)
      have hthree_card: "card {v, w, x} = 3"
        using hvw hx_ne_v hx_ne_w by (by100 simp)
      have "card {v, w, x} \<le> card V"
        by (rule card_mono[OF hV_fin hthree_sub])
      thus False
        using hthree_card hV_card by (by100 simp)
    qed
  qed
  have hV_eq_pair: "V = {v, w}"
    using hV_sub hvV hwV by (by100 blast)
  show ?thesis
    using heV hV_eq_pair by (by100 simp)
qed

lemma geotop_complex_edges_same_two_vertices_eq_dev34:
  fixes K :: "(real^2) set set" and e l :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwK: "{w} \<in> K"
  assumes heK: "e \<in> K"
  assumes hlK: "l \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hledge: "geotop_is_edge l"
  assumes hv_e: "v \<in> e"
  assumes hw_e: "w \<in> e"
  assumes hv_l: "v \<in> l"
  assumes hw_l: "w \<in> l"
  assumes hvw: "v \<noteq> w"
  shows "e = l"
proof -
  have heV: "geotop_simplex_vertices e {v, w}"
    by (rule geotop_complex_edge_vertices_pair_dev34
        [OF hK hvK hwK heK hedge hv_e hw_e hvw])
  have hlV: "geotop_simplex_vertices l {v, w}"
    by (rule geotop_complex_edge_vertices_pair_dev34
        [OF hK hvK hwK hlK hledge hv_l hw_l hvw])
  have he_eq: "e = geotop_convex_hull {v, w}"
    using heV unfolding geotop_simplex_vertices_def by (by100 blast)
  have hl_eq: "l = geotop_convex_hull {v, w}"
    using hlV unfolding geotop_simplex_vertices_def by (by100 blast)
  show ?thesis
    using he_eq hl_eq by (by100 simp)
qed

lemma geotop_2simplex_vertices_three_eq_dev34:
  fixes \<sigma> V :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hv: "v \<in> V"
  assumes hw: "w \<in> V"
  assumes hu: "u \<in> V"
  assumes hvw: "v \<noteq> w"
  assumes hvu: "v \<noteq> u"
  assumes hwu: "w \<noteq> u"
  shows "V = {v, w, u}"
proof -
  obtain V2 m where hV2_fin: "finite V2"
    and hV2_card: "card V2 = 2 + 1"
    and h2_le_m: "2 \<le> m"
    and hgp_V2: "geotop_general_position V2 m"
    and h\<sigma>_eq_V2: "\<sigma> = geotop_convex_hull V2"
    using h\<sigma>2 unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V2: "geotop_simplex_vertices \<sigma> V2"
    unfolding geotop_simplex_vertices_def
    using hV2_fin hV2_card h2_le_m hgp_V2 h\<sigma>_eq_V2 by (by100 blast)
  have hV_eq: "V = V2"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V2])
  have hV_card: "card V = 3"
    using hV_eq hV2_card by (by100 simp)
  have hV_fin: "finite V"
    using hV_eq hV2_fin by (by100 simp)
  have hthree_sub: "{v, w, u} \<subseteq> V"
    using hv hw hu by (by100 blast)
  have hthree_card: "card {v, w, u} = 3"
    using hvw hvu hwu by (by100 simp)
  have hthree_eq: "{v, w, u} = V"
    using hV_fin hthree_sub hthree_card hV_card by (by100 (metis card_seteq))
  show ?thesis
    using hthree_eq by (by100 simp)
qed

lemma geotop_two_2simplex_opposite_edges_distinct_dev34:
  fixes \<sigma> \<tau> V\<^sub>\<sigma> V\<^sub>\<tau> :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>"
  assumes h\<tau>V: "geotop_simplex_vertices \<tau> V\<^sub>\<tau>"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes hvw: "v \<noteq> w"
  assumes hvV\<sigma>: "v \<in> V\<^sub>\<sigma>"
  assumes hwV\<sigma>: "w \<in> V\<^sub>\<sigma>"
  assumes huV\<sigma>: "u\<^sub>\<sigma> \<in> V\<^sub>\<sigma>"
  assumes hvV\<tau>: "v \<in> V\<^sub>\<tau>"
  assumes hwV\<tau>: "w \<in> V\<^sub>\<tau>"
  assumes huV\<tau>: "u\<^sub>\<tau> \<in> V\<^sub>\<tau>"
  assumes hu\<sigma>_ne_v: "u\<^sub>\<sigma> \<noteq> v"
  assumes hu\<sigma>_ne_w: "u\<^sub>\<sigma> \<noteq> w"
  assumes hu\<tau>_ne_v: "u\<^sub>\<tau> \<noteq> v"
  assumes hu\<tau>_ne_w: "u\<^sub>\<tau> \<noteq> w"
  shows "geotop_convex_hull {w, u\<^sub>\<sigma>} \<noteq> geotop_convex_hull {w, u\<^sub>\<tau>}"
proof
  assume heq: "geotop_convex_hull {w, u\<^sub>\<sigma>} = geotop_convex_hull {w, u\<^sub>\<tau>}"
  have hw_ne_u\<sigma>: "w \<noteq> u\<^sub>\<sigma>"
    using hu\<sigma>_ne_w by (by100 blast)
  have hw_ne_u\<tau>: "w \<noteq> u\<^sub>\<tau>"
    using hu\<tau>_ne_w by (by100 blast)
  have hv_ne_u\<sigma>: "v \<noteq> u\<^sub>\<sigma>"
    using hu\<sigma>_ne_v by (by100 blast)
  have hv_ne_u\<tau>: "v \<noteq> u\<^sub>\<tau>"
    using hu\<tau>_ne_v by (by100 blast)
  have hL\<sigma>V: "geotop_simplex_vertices (geotop_convex_hull {w, u\<^sub>\<sigma>}) {w, u\<^sub>\<sigma>}"
    by (rule geotop_pair_convex_hull_simplex_vertices_dev34[OF hw_ne_u\<sigma>])
  have hL\<tau>V_raw: "geotop_simplex_vertices (geotop_convex_hull {w, u\<^sub>\<tau>}) {w, u\<^sub>\<tau>}"
    by (rule geotop_pair_convex_hull_simplex_vertices_dev34[OF hw_ne_u\<tau>])
  have hL\<tau>V: "geotop_simplex_vertices (geotop_convex_hull {w, u\<^sub>\<sigma>}) {w, u\<^sub>\<tau>}"
    using hL\<tau>V_raw heq by (by100 simp)
  have hpair_eq: "{w, u\<^sub>\<sigma>} = {w, u\<^sub>\<tau>}"
    by (rule geotop_simplex_vertices_unique[OF hL\<sigma>V hL\<tau>V])
  have hu_eq: "u\<^sub>\<sigma> = u\<^sub>\<tau>"
    using hpair_eq hu\<sigma>_ne_w hu\<tau>_ne_w by (by100 blast)
  have hV\<sigma>_eq: "V\<^sub>\<sigma> = {v, w, u\<^sub>\<sigma>}"
    by (rule geotop_2simplex_vertices_three_eq_dev34
        [OF h\<sigma>2 h\<sigma>V hvV\<sigma> hwV\<sigma> huV\<sigma> hvw hv_ne_u\<sigma> hw_ne_u\<sigma>])
  have hV\<tau>_eq: "V\<^sub>\<tau> = {v, w, u\<^sub>\<tau>}"
    by (rule geotop_2simplex_vertices_three_eq_dev34
        [OF h\<tau>2 h\<tau>V hvV\<tau> hwV\<tau> huV\<tau> hvw hv_ne_u\<tau> hw_ne_u\<tau>])
  have hV_eq: "V\<^sub>\<sigma> = V\<^sub>\<tau>"
    using hV\<sigma>_eq hV\<tau>_eq hu_eq by (by100 simp)
  have h\<sigma>_eq: "\<sigma> = geotop_convex_hull V\<^sub>\<sigma>"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have h\<tau>_eq: "\<tau> = geotop_convex_hull V\<^sub>\<tau>"
    using h\<tau>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have "\<sigma> = \<tau>"
    using h\<sigma>_eq h\<tau>_eq hV_eq by (by100 simp)
  thus False
    using h\<sigma>\<tau> by (by100 blast)
qed

lemma geotop_2simplex_edge_face_through_vertex_not_other_eq_opposite_dev34:
  fixes \<sigma> V l :: "(real^2) set"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hvV: "v \<in> V"
  assumes hwV: "w \<in> V"
  assumes huV: "u \<in> V"
  assumes hvw: "v \<noteq> w"
  assumes hvu: "v \<noteq> u"
  assumes hwu: "w \<noteq> u"
  assumes hface: "geotop_is_face l \<sigma>"
  assumes hledge: "geotop_is_edge l"
  assumes hw_l: "w \<in> l"
  assumes hv_not_l: "v \<notin> l"
  shows "l = geotop_convex_hull {w, u}"
proof -
  obtain V' W where h\<sigma>V': "geotop_simplex_vertices \<sigma> V'"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V'"
    and hl_eq: "l = geotop_convex_hull W"
    and hlW: "geotop_simplex_vertices l W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two[OF hledge hface])
  have hV'_eq: "V' = V"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>V' h\<sigma>V])
  have hW_sub_V: "W \<subseteq> V"
    using hW_sub hV'_eq by (by100 simp)
  have hV_eq_three: "V = {v, w, u}"
    by (rule geotop_2simplex_vertices_three_eq_dev34
        [OF h\<sigma>2 h\<sigma>V hvV hwV huV hvw hvu hwu])
  have hW_fin: "finite W"
    using hlW unfolding geotop_simplex_vertices_def by (by100 blast)
  have hwW: "w \<in> W"
  proof (rule ccontr)
    assume hw_not_W: "\<not> w \<in> W"
    have hW_sub_no_w: "W \<subseteq> V - {w}"
      using hW_sub_V hw_not_W by (by100 blast)
    have hw_not_hull: "w \<notin> geotop_convex_hull W"
      by (rule geotop_simplex_vertex_notin_hull_of_other_vertices
          [OF h\<sigma>V hwV hW_sub_no_w])
    have "w \<in> geotop_convex_hull W"
      using hw_l hl_eq by (by100 simp)
    thus False
      using hw_not_hull by (by100 blast)
  qed
  have hv_not_W: "v \<notin> W"
  proof
    assume hvW: "v \<in> W"
    have "v \<in> convex hull W"
      using hvW hull_inc[of v W] by (by100 simp)
    hence "v \<in> geotop_convex_hull W"
      using geotop_convex_hull_eq_HOL[of W] by (by100 simp)
    hence "v \<in> l"
      using hl_eq by (by100 simp)
    thus False
      using hv_not_l by (by100 blast)
  qed
  have hW_sub_wu: "W \<subseteq> {w, u}"
    using hW_sub_V hV_eq_three hv_not_W by (by100 blast)
  have hpair_card: "card {w, u} = 2"
    using hwu by (by100 simp)
  have hW_eq: "W = {w, u}"
    by (rule card_seteq[OF finite_insert hW_sub_wu])
       (use hW_card hpair_card in \<open>by (by100 simp)\<close>)
  show ?thesis
    using hl_eq hW_eq by (by100 simp)
qed

lemma geotop_incident_edge_2simplex_link_edge_witness:
  fixes K :: "(real^2) set set" and e \<sigma> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hface: "geotop_is_face e \<sigma>"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  shows "\<exists>w l. w \<noteq> v \<and> w \<in> e \<and> {w} \<in> geotop_link K v
      \<and> l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l"
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and he_eq: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two[OF hedge hface])
  obtain V2 m where hV2_fin: "finite V2"
    and hV2_card: "card V2 = 2 + 1"
    and h2_le_m: "2 \<le> m"
    and hgp_V2: "geotop_general_position V2 m"
    and h\<sigma>_eq_V2: "\<sigma> = geotop_convex_hull V2"
    using h\<sigma>2 unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V2: "geotop_simplex_vertices \<sigma> V2"
    unfolding geotop_simplex_vertices_def
    using hV2_fin hV2_card h2_le_m hgp_V2 h\<sigma>_eq_V2 by (by100 blast)
  have hV_eq: "V = V2"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V2])
  have hV_card: "card V = 3"
    using hV_eq hV2_card by (by100 simp)
  have hV_fin: "finite V"
    using hV_eq hV2_fin by (by100 simp)
  have hface_closed: "\<forall>\<rho>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<rho> \<longrightarrow> \<tau> \<in> K"
    by (rule conjunct1[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]])
  have heK: "e \<in> K"
    using hface_closed h\<sigma>K hface by (by100 blast)
  obtain Wv where heWv: "geotop_simplex_vertices e Wv"
    and hvWv: "v \<in> Wv"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK heK hv_e]
    by (by100 blast)
  have hWv_eq: "Wv = W"
    by (rule geotop_simplex_vertices_unique[OF heWv heW])
  have hvW: "v \<in> W"
    using hvWv hWv_eq by (by100 simp)
  have hvV: "v \<in> V"
    using hW_sub hvW by (by100 blast)
  have hW_not_sub_singleton: "\<not> W \<subseteq> {v}"
  proof
    assume hsub: "W \<subseteq> {v}"
    have hsingleton_fin: "finite {v}"
      by (by100 simp)
    have "card W \<le> card {v}"
      by (rule card_mono[OF hsingleton_fin hsub])
    thus False
      using hW_card by (by100 simp)
  qed
  obtain w where hwW: "w \<in> W" and hw_ne_v: "w \<noteq> v"
    using hW_not_sub_singleton by (by100 blast)
  have hwV: "w \<in> V"
    using hW_sub hwW by (by100 blast)
  have hv_ne_w: "v \<noteq> w"
    using hw_ne_v by (by100 blast)
  have hw_e: "w \<in> e"
  proof -
    have "w \<in> convex hull W"
      using hwW hull_inc[of w W] by (by100 simp)
    moreover have "geotop_convex_hull W = convex hull W"
      by (rule geotop_convex_hull_eq_HOL)
    ultimately show ?thesis
      using he_eq by (by100 simp)
  qed
  have hW_fin: "finite W"
    using hW_sub hV_fin by (rule finite_subset)
  have hV_not_sub_W: "\<not> V \<subseteq> W"
  proof
    assume hsub: "V \<subseteq> W"
    have "card V \<le> card W"
      by (rule card_mono[OF hW_fin hsub])
    thus False
      using hV_card hW_card by (by100 simp)
  qed
  obtain u where huV: "u \<in> V" and hu_not_W: "u \<notin> W"
    using hV_not_sub_W by (by100 blast)
  have hv_ne_u: "v \<noteq> u"
    using hvW hu_not_W by (by100 blast)
  have hw_ne_u: "w \<noteq> u"
    using hwW hu_not_W by (by100 blast)
  let ?sw = "geotop_convex_hull {w}"
  have hsw_face: "geotop_is_face ?sw e"
    unfolding geotop_is_face_def using heW hwW by (by100 blast)
  have hsw_singleton: "?sw = {w}"
    using geotop_convex_hull_eq_HOL[of "{w}"] by (by100 simp)
  have hv_not_sw: "v \<notin> ?sw"
    using hsw_singleton hw_ne_v by (by100 simp)
  have hsw_star: "?sw \<in> geotop_star K v"
    unfolding geotop_star_def using heK hv_e hsw_face by (by100 blast)
  have hsw_link: "?sw \<in> geotop_link K v"
    unfolding geotop_link_def using hsw_star hv_not_sw by (by100 blast)
  have hw_link: "{w} \<in> geotop_link K v"
    using hsw_singleton hsw_link by (by100 simp)
  have hopposite:
    "geotop_convex_hull {w, u} \<in> geotop_link K v
      \<and> geotop_is_edge (geotop_convex_hull {w, u})
      \<and> w \<in> geotop_convex_hull {w, u}
      \<and> u \<in> geotop_convex_hull {w, u}"
    by (rule geotop_simplex_opposite_edge_in_link
        [OF hK h\<sigma>K h\<sigma>V hvV hwV huV hv_ne_w hv_ne_u hw_ne_u])
  show ?thesis
    using hw_ne_v hw_e hw_link hopposite by (by100 blast)
qed

lemma geotop_link_vertex_incident_2simplex_opposite_link_edge:
  fixes K :: "(real^2) set set" and e \<sigma> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwL: "{w} \<in> geotop_link K v"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  assumes hw_e: "w \<in> e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hface: "geotop_is_face e \<sigma>"
  shows "\<exists>u. u \<in> \<sigma> \<and> u \<noteq> v \<and> u \<noteq> w
      \<and> geotop_convex_hull {w, u} \<in> geotop_link K v
      \<and> geotop_is_edge (geotop_convex_hull {w, u})
      \<and> w \<in> geotop_convex_hull {w, u}
      \<and> u \<in> geotop_convex_hull {w, u}"
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and he_eq: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two[OF hedge hface])
  obtain V2 m where hV2_fin: "finite V2"
    and hV2_card: "card V2 = 2 + 1"
    and h2_le_m: "2 \<le> m"
    and hgp_V2: "geotop_general_position V2 m"
    and h\<sigma>_eq_V2: "\<sigma> = geotop_convex_hull V2"
    using h\<sigma>2 unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V2: "geotop_simplex_vertices \<sigma> V2"
    unfolding geotop_simplex_vertices_def
    using hV2_fin hV2_card h2_le_m hgp_V2 h\<sigma>_eq_V2 by (by100 blast)
  have hV_eq: "V = V2"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V2])
  have hV_card: "card V = 3"
    using hV_eq hV2_card by (by100 simp)
  have hV_fin: "finite V"
    using hV_eq hV2_fin by (by100 simp)
  obtain Wv where heWv: "geotop_simplex_vertices e Wv"
    and hvWv: "v \<in> Wv"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK heK hv_e]
    by (by100 blast)
  have hWv_eq: "Wv = W"
    by (rule geotop_simplex_vertices_unique[OF heWv heW])
  have hvW: "v \<in> W"
    using hvWv hWv_eq by (by100 simp)
  have hvV: "v \<in> V"
    using hW_sub hvW by (by100 blast)
  have hlink_sub: "geotop_link K v \<subseteq> K"
    by (rule geotop_link_subset_complex[OF hK])
  have hwK: "{w} \<in> K"
    using hlink_sub hwL by (by100 blast)
  obtain Ww where heWw: "geotop_simplex_vertices e Ww"
    and hwWw: "w \<in> Ww"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hwK heK hw_e]
    by (by100 blast)
  have hWw_eq: "Ww = W"
    by (rule geotop_simplex_vertices_unique[OF heWw heW])
  have hwW: "w \<in> W"
    using hwWw hWw_eq by (by100 simp)
  have hwV: "w \<in> V"
    using hW_sub hwW by (by100 blast)
  have hW_fin: "finite W"
    using hW_sub hV_fin by (rule finite_subset)
  have hV_not_sub_W: "\<not> V \<subseteq> W"
  proof
    assume hsub: "V \<subseteq> W"
    have "card V \<le> card W"
      by (rule card_mono[OF hW_fin hsub])
    thus False
      using hV_card hW_card by (by100 simp)
  qed
  obtain u where huV: "u \<in> V" and hu_not_W: "u \<notin> W"
    using hV_not_sub_W by (by100 blast)
  have h\<sigma>_eq_V: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hu\<sigma>: "u \<in> \<sigma>"
  proof -
    have "u \<in> convex hull V"
      using huV hull_inc[of u V] by (by100 simp)
    moreover have "geotop_convex_hull V = convex hull V"
      by (rule geotop_convex_hull_eq_HOL)
    ultimately show ?thesis
      using h\<sigma>_eq_V by (by100 simp)
  qed
  have hv_ne_w: "v \<noteq> w"
    using hwL unfolding geotop_link_def by (by100 blast)
  have hv_ne_u: "v \<noteq> u"
    using hvW hu_not_W by (by100 blast)
  have hw_ne_u: "w \<noteq> u"
    using hwW hu_not_W by (by100 blast)
  have hopposite:
    "geotop_convex_hull {w, u} \<in> geotop_link K v
      \<and> geotop_is_edge (geotop_convex_hull {w, u})
      \<and> w \<in> geotop_convex_hull {w, u}
      \<and> u \<in> geotop_convex_hull {w, u}"
    by (rule geotop_simplex_opposite_edge_in_link
        [OF hK h\<sigma>K h\<sigma>V hvV hwV huV hv_ne_w hv_ne_u hw_ne_u])
  show ?thesis
    using hu\<sigma> hv_ne_u hw_ne_u hopposite by (by100 blast)
qed

lemma geotop_link_vertex_incident_2simplex_opposite_face_link_edge:
  fixes K :: "(real^2) set set" and e \<sigma> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwL: "{w} \<in> geotop_link K v"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  assumes hw_e: "w \<in> e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hface: "geotop_is_face e \<sigma>"
  shows "\<exists>u. u \<in> \<sigma> \<and> u \<noteq> v \<and> u \<noteq> w
      \<and> geotop_is_face (geotop_convex_hull {w, u}) \<sigma>
      \<and> geotop_convex_hull {w, u} \<in> geotop_link K v
      \<and> geotop_is_edge (geotop_convex_hull {w, u})
      \<and> w \<in> geotop_convex_hull {w, u}
      \<and> u \<in> geotop_convex_hull {w, u}"
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and he_eq: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two[OF hedge hface])
  obtain V2 m where hV2_fin: "finite V2"
    and hV2_card: "card V2 = 2 + 1"
    and h2_le_m: "2 \<le> m"
    and hgp_V2: "geotop_general_position V2 m"
    and h\<sigma>_eq_V2: "\<sigma> = geotop_convex_hull V2"
    using h\<sigma>2 unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V2: "geotop_simplex_vertices \<sigma> V2"
    unfolding geotop_simplex_vertices_def
    using hV2_fin hV2_card h2_le_m hgp_V2 h\<sigma>_eq_V2 by (by100 blast)
  have hV_eq: "V = V2"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V2])
  have hV_card: "card V = 3"
    using hV_eq hV2_card by (by100 simp)
  have hV_fin: "finite V"
    using hV_eq hV2_fin by (by100 simp)
  obtain Wv where heWv: "geotop_simplex_vertices e Wv"
    and hvWv: "v \<in> Wv"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK heK hv_e]
    by (by100 blast)
  have hWv_eq: "Wv = W"
    by (rule geotop_simplex_vertices_unique[OF heWv heW])
  have hvW: "v \<in> W"
    using hvWv hWv_eq by (by100 simp)
  have hvV: "v \<in> V"
    using hW_sub hvW by (by100 blast)
  have hlink_sub: "geotop_link K v \<subseteq> K"
    by (rule geotop_link_subset_complex[OF hK])
  have hwK: "{w} \<in> K"
    using hlink_sub hwL by (by100 blast)
  obtain Ww where heWw: "geotop_simplex_vertices e Ww"
    and hwWw: "w \<in> Ww"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hwK heK hw_e]
    by (by100 blast)
  have hWw_eq: "Ww = W"
    by (rule geotop_simplex_vertices_unique[OF heWw heW])
  have hwW: "w \<in> W"
    using hwWw hWw_eq by (by100 simp)
  have hwV: "w \<in> V"
    using hW_sub hwW by (by100 blast)
  have hW_fin: "finite W"
    using hW_sub hV_fin by (rule finite_subset)
  have hV_not_sub_W: "\<not> V \<subseteq> W"
  proof
    assume hsub: "V \<subseteq> W"
    have "card V \<le> card W"
      by (rule card_mono[OF hW_fin hsub])
    thus False
      using hV_card hW_card by (by100 simp)
  qed
  obtain u where huV: "u \<in> V" and hu_not_W: "u \<notin> W"
    using hV_not_sub_W by (by100 blast)
  have h\<sigma>_eq_V: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hu\<sigma>: "u \<in> \<sigma>"
  proof -
    have "u \<in> convex hull V"
      using huV hull_inc[of u V] by (by100 simp)
    moreover have "geotop_convex_hull V = convex hull V"
      by (rule geotop_convex_hull_eq_HOL)
    ultimately show ?thesis
      using h\<sigma>_eq_V by (by100 simp)
  qed
  have hv_ne_w: "v \<noteq> w"
    using hwL unfolding geotop_link_def by (by100 blast)
  have hv_ne_u: "v \<noteq> u"
    using hvW hu_not_W by (by100 blast)
  have hw_ne_u: "w \<noteq> u"
    using hwW hu_not_W by (by100 blast)
  have hopposite:
    "geotop_is_face (geotop_convex_hull {w, u}) \<sigma>
      \<and> geotop_convex_hull {w, u} \<in> geotop_link K v
      \<and> geotop_is_edge (geotop_convex_hull {w, u})
      \<and> w \<in> geotop_convex_hull {w, u}
      \<and> u \<in> geotop_convex_hull {w, u}"
    by (rule geotop_simplex_opposite_edge_face_in_link
        [OF hK h\<sigma>K h\<sigma>V hvV hwV huV hv_ne_w hv_ne_u hw_ne_u])
  show ?thesis
    using hu\<sigma> hv_ne_u hw_ne_u hopposite by (by100 blast)
qed

lemma geotop_link_vertex_incident_2simplex_opposite_vertex_face_link_edge:
  fixes K :: "(real^2) set set" and e \<sigma> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwL: "{w} \<in> geotop_link K v"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  assumes hw_e: "w \<in> e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hface: "geotop_is_face e \<sigma>"
  shows "\<exists>V u. geotop_simplex_vertices \<sigma> V
      \<and> v \<in> V \<and> w \<in> V \<and> u \<in> V
      \<and> u \<noteq> v \<and> u \<noteq> w
      \<and> u \<in> \<sigma>
      \<and> geotop_is_face (geotop_convex_hull {w, u}) \<sigma>
      \<and> geotop_convex_hull {w, u} \<in> geotop_link K v
      \<and> geotop_is_edge (geotop_convex_hull {w, u})
      \<and> w \<in> geotop_convex_hull {w, u}
      \<and> u \<in> geotop_convex_hull {w, u}"
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and he_eq: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two[OF hedge hface])
  obtain V2 m where hV2_fin: "finite V2"
    and hV2_card: "card V2 = 2 + 1"
    and h2_le_m: "2 \<le> m"
    and hgp_V2: "geotop_general_position V2 m"
    and h\<sigma>_eq_V2: "\<sigma> = geotop_convex_hull V2"
    using h\<sigma>2 unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V2: "geotop_simplex_vertices \<sigma> V2"
    unfolding geotop_simplex_vertices_def
    using hV2_fin hV2_card h2_le_m hgp_V2 h\<sigma>_eq_V2 by (by100 blast)
  have hV_eq: "V = V2"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V2])
  have hV_card: "card V = 3"
    using hV_eq hV2_card by (by100 simp)
  have hV_fin: "finite V"
    using hV_eq hV2_fin by (by100 simp)
  obtain Wv where heWv: "geotop_simplex_vertices e Wv"
    and hvWv: "v \<in> Wv"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK heK hv_e]
    by (by100 blast)
  have hWv_eq: "Wv = W"
    by (rule geotop_simplex_vertices_unique[OF heWv heW])
  have hvW: "v \<in> W"
    using hvWv hWv_eq by (by100 simp)
  have hvV: "v \<in> V"
    using hW_sub hvW by (by100 blast)
  have hlink_sub: "geotop_link K v \<subseteq> K"
    by (rule geotop_link_subset_complex[OF hK])
  have hwK: "{w} \<in> K"
    using hlink_sub hwL by (by100 blast)
  obtain Ww where heWw: "geotop_simplex_vertices e Ww"
    and hwWw: "w \<in> Ww"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hwK heK hw_e]
    by (by100 blast)
  have hWw_eq: "Ww = W"
    by (rule geotop_simplex_vertices_unique[OF heWw heW])
  have hwW: "w \<in> W"
    using hwWw hWw_eq by (by100 simp)
  have hwV: "w \<in> V"
    using hW_sub hwW by (by100 blast)
  have hW_fin: "finite W"
    using hW_sub hV_fin by (rule finite_subset)
  have hV_not_sub_W: "\<not> V \<subseteq> W"
  proof
    assume hsub: "V \<subseteq> W"
    have "card V \<le> card W"
      by (rule card_mono[OF hW_fin hsub])
    thus False
      using hV_card hW_card by (by100 simp)
  qed
  obtain u where huV: "u \<in> V" and hu_not_W: "u \<notin> W"
    using hV_not_sub_W by (by100 blast)
  have h\<sigma>_eq_V: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hu\<sigma>: "u \<in> \<sigma>"
  proof -
    have "u \<in> convex hull V"
      using huV hull_inc[of u V] by (by100 simp)
    moreover have "geotop_convex_hull V = convex hull V"
      by (rule geotop_convex_hull_eq_HOL)
    ultimately show ?thesis
      using h\<sigma>_eq_V by (by100 simp)
  qed
  have hv_ne_w: "v \<noteq> w"
    using hwL unfolding geotop_link_def by (by100 blast)
  have hv_ne_u: "v \<noteq> u"
    using hvW hu_not_W by (by100 blast)
  have hw_ne_u: "w \<noteq> u"
    using hwW hu_not_W by (by100 blast)
  have hopposite:
    "geotop_is_face (geotop_convex_hull {w, u}) \<sigma>
      \<and> geotop_convex_hull {w, u} \<in> geotop_link K v
      \<and> geotop_is_edge (geotop_convex_hull {w, u})
      \<and> w \<in> geotop_convex_hull {w, u}
      \<and> u \<in> geotop_convex_hull {w, u}"
    by (rule geotop_simplex_opposite_edge_face_in_link
        [OF hK h\<sigma>K h\<sigma>V hvV hwV huV hv_ne_w hv_ne_u hw_ne_u])
  show ?thesis
    using h\<sigma>V hvV hwV huV hv_ne_u hw_ne_u hu\<sigma> hopposite by (by100 blast)
qed

lemma geotop_incident_edge_adjacent_2simplex_link_edge_witness:
  fixes K :: "(real^2) set set" and e :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  assumes h2face: "\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  shows "\<exists>w l. w \<noteq> v \<and> w \<in> e \<and> {w} \<in> geotop_link K v
      \<and> l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l"
proof -
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and hface: "geotop_is_face e \<sigma>"
    using h2face by (by100 blast)
  show ?thesis
    by (rule geotop_incident_edge_2simplex_link_edge_witness
        [OF hK hvK h\<sigma>K h\<sigma>2 hface hedge hv_e])
qed

lemma geotop_incident_edge_face_count_ge_1_link_edge_witness:
  fixes K :: "(real^2) set set" and e :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  assumes hcount:
    "1 \<le> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  shows "\<exists>w l. w \<noteq> v \<and> w \<in> e \<and> {w} \<in> geotop_link K v
      \<and> l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l"
proof -
  let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  have hS_ne: "?S \<noteq> {}"
    using hcount by (by100 force)
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and hface: "geotop_is_face e \<sigma>"
    using hS_ne by (by100 blast)
  have h2face: "\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
    using h\<sigma>K h\<sigma>2 hface by (by100 blast)
  show ?thesis
    by (rule geotop_incident_edge_adjacent_2simplex_link_edge_witness
        [OF hK hvK heK hedge hv_e h2face])
qed

lemma geotop_link_vertex_incident_edge_count_ge_1_incident_link_edge:
  fixes K :: "(real^2) set set" and e :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwL: "{w} \<in> geotop_link K v"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  assumes hw_e: "w \<in> e"
  assumes hcount:
    "1 \<le> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  shows "\<exists>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l"
proof -
  have hlink_sub: "geotop_link K v \<subseteq> K"
    by (rule geotop_link_subset_complex[OF hK])
  have hwK: "{w} \<in> K"
    using hlink_sub hwL by (by100 blast)
  have hv_not_w: "v \<noteq> w"
    using hwL unfolding geotop_link_def by (by100 blast)
  obtain w' l where hw'_ne_v: "w' \<noteq> v"
    and hw'_e: "w' \<in> e"
    and hw'L: "{w'} \<in> geotop_link K v"
    and hlL: "l \<in> geotop_link K v"
    and hledge: "geotop_is_edge l"
    and hw'_l: "w' \<in> l"
    using geotop_incident_edge_face_count_ge_1_link_edge_witness
      [OF hK hvK heK hedge hv_e hcount]
    by (by100 blast)
  have hw'K: "{w'} \<in> K"
    using hlink_sub hw'L by (by100 blast)
  obtain V m where hV_fin: "finite V"
    and hV_card: "card V = 1 + 1"
    and h1_le_m: "1 \<le> m"
    and hgp_V: "geotop_general_position V m"
    and he_eq: "e = geotop_convex_hull V"
    using hedge unfolding geotop_is_edge_def geotop_simplex_dim_def
    by (by100 blast)
  have heV: "geotop_simplex_vertices e V"
    unfolding geotop_simplex_vertices_def
    using hV_fin hV_card h1_le_m hgp_V he_eq by (by100 blast)
  obtain Vv where heVv: "geotop_simplex_vertices e Vv"
    and hvVv: "v \<in> Vv"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK heK hv_e]
    by (by100 blast)
  have hVv_eq: "Vv = V"
    by (rule geotop_simplex_vertices_unique[OF heVv heV])
  have hvV: "v \<in> V"
    using hvVv hVv_eq by (by100 simp)
  obtain Vw where heVw: "geotop_simplex_vertices e Vw"
    and hwVw: "w \<in> Vw"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hwK heK hw_e]
    by (by100 blast)
  have hVw_eq: "Vw = V"
    by (rule geotop_simplex_vertices_unique[OF heVw heV])
  have hwV: "w \<in> V"
    using hwVw hVw_eq by (by100 simp)
  obtain Vw' where heVw': "geotop_simplex_vertices e Vw'"
    and hw'Vw': "w' \<in> Vw'"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hw'K heK hw'_e]
    by (by100 blast)
  have hVw'_eq: "Vw' = V"
    by (rule geotop_simplex_vertices_unique[OF heVw' heV])
  have hw'V: "w' \<in> V"
    using hw'Vw' hVw'_eq by (by100 simp)
  have hV_sub: "V \<subseteq> {v, w}"
  proof
    fix x assume hxV: "x \<in> V"
    show "x \<in> {v, w}"
    proof (rule ccontr)
      assume hx_not: "x \<notin> {v, w}"
      have hthree_sub: "{v, w, x} \<subseteq> V"
        using hvV hwV hxV by (by100 blast)
      have hx_ne_v: "x \<noteq> v"
        using hx_not by (by100 simp)
      have hx_ne_w: "x \<noteq> w"
        using hx_not by (by100 simp)
      have hthree_card: "card {v, w, x} = 3"
        using hv_not_w hx_ne_v hx_ne_w by (by100 simp)
      have "card {v, w, x} \<le> card V"
        by (rule card_mono[OF hV_fin hthree_sub])
      thus False
        using hthree_card hV_card by (by100 simp)
    qed
  qed
  have hw'_in_pair: "w' \<in> {v, w}"
    using hV_sub hw'V by (by100 blast)
  have hw'_eq_w: "w' = w"
    using hw'_in_pair hw'_ne_v by (by100 blast)
  show ?thesis
    using hlL hledge hw'_l hw'_eq_w by (by100 blast)
qed

lemma geotop_link_vertex_count_ge_1_incident_link_edge:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwL: "{w} \<in> geotop_link K v"
  assumes hcount:
    "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
      1 \<le> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  shows "\<exists>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l"
proof -
  obtain e where heK: "e \<in> K"
    and hedge: "geotop_is_edge e"
    and hv_e: "v \<in> e"
    and hw_e: "w \<in> e"
    using geotop_link_vertex_incident_edge_witness[OF hK hvK hwL]
    by (by100 blast)
  have hcount_e:
    "1 \<le> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
    using hcount heK hedge hv_e by (by100 blast)
  show ?thesis
    by (rule geotop_link_vertex_incident_edge_count_ge_1_incident_link_edge
        [OF hK hvK hwL heK hedge hv_e hw_e hcount_e])
qed

lemma geotop_link_vertices_count_ge_1_incident_link_edges:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hcount:
    "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
      1 \<le> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  shows "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
      (\<exists>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l)"
proof (intro allI impI)
  fix w assume hwL: "{w} \<in> geotop_link K v"
  show "\<exists>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l"
    by (rule geotop_link_vertex_count_ge_1_incident_link_edge
        [OF hK hvK hwL hcount])
qed

lemma geotop_edge_face_in_ge_2_simplex_has_2_face:
  fixes e \<sigma> :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  assumes hface: "geotop_is_face e \<sigma>"
  assumes h\<sigma>dim: "geotop_simplex_dim \<sigma> n"
  assumes hn: "2 \<le> n"
  shows "\<exists>\<tau>. geotop_is_face \<tau> \<sigma> \<and> geotop_simplex_dim \<tau> 2 \<and> e \<subseteq> \<tau>"
proof -
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}" and hW_sub: "W \<subseteq> V"
    and he_eq: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two[OF hedge hface])
  obtain V\<^sub>\<sigma> m where hV\<sigma>_fin: "finite V\<^sub>\<sigma>"
    and hV\<sigma>_card: "card V\<^sub>\<sigma> = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp_V\<sigma>: "geotop_general_position V\<^sub>\<sigma> m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V\<^sub>\<sigma>"
    using h\<sigma>dim unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<sigma>V\<sigma>: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>"
    unfolding geotop_simplex_vertices_def
    using hV\<sigma>_fin hV\<sigma>_card hn_le_m hgp_V\<sigma> h\<sigma>_eq by (by100 blast)
  have hV_eq: "V = V\<^sub>\<sigma>"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>V h\<sigma>V\<sigma>])
  have hW_sub_V\<sigma>: "W \<subseteq> V\<^sub>\<sigma>"
    using hW_sub hV_eq by (by100 simp)
  have hV\<sigma>_ge3: "3 \<le> card V\<^sub>\<sigma>"
    using hV\<sigma>_card hn by (by100 linarith)
  have hW_fin: "finite W"
    using hW_sub_V\<sigma> hV\<sigma>_fin by (rule finite_subset)
  have "\<not> V\<^sub>\<sigma> \<subseteq> W"
  proof
    assume hV_sub_W: "V\<^sub>\<sigma> \<subseteq> W"
    have "card V\<^sub>\<sigma> \<le> card W"
      by (rule card_mono[OF hW_fin hV_sub_W])
    thus False
      using hV\<sigma>_ge3 hW_card by (by100 linarith)
  qed
  then obtain u where huV: "u \<in> V\<^sub>\<sigma>" and huW: "u \<notin> W"
    by (by100 blast)
  let ?X = "W \<union> {u}"
  have hX_sub: "?X \<subseteq> V\<^sub>\<sigma>"
    using hW_sub_V\<sigma> huV by (by100 blast)
  have hX_ne: "?X \<noteq> {}"
    using huV by (by100 blast)
  have hX_fin: "finite ?X"
    using hW_fin by (by100 simp)
  have hX_card: "card ?X = 3"
    using hW_fin hW_card huW by (by100 simp)
  have hm_ge2: "2 \<le> m"
    using hn hn_le_m by (by100 linarith)
  have hgp_X: "geotop_general_position ?X m"
    by (rule geotop_general_position_subset[OF hgp_V\<sigma> hX_sub])
  define \<tau> where "\<tau> = geotop_convex_hull ?X"
  have h\<tau>face: "geotop_is_face \<tau> \<sigma>"
    unfolding \<tau>_def
    by (rule geotop_is_face_of_subset[OF h\<sigma>V\<sigma> hX_ne hX_sub])
  have h\<tau>dim: "geotop_simplex_dim \<tau> 2"
  proof -
    have hX_card_dim: "card ?X = 2 + 1"
      using hX_card by (by100 simp)
    show ?thesis
    unfolding geotop_simplex_dim_def \<tau>_def
      using hX_fin hX_card_dim hm_ge2 hgp_X by (by100 blast)
  qed
  have hesub: "e \<subseteq> \<tau>"
  proof -
    have hmono: "convex hull W \<subseteq> convex hull ?X"
      by (rule hull_mono) (by100 blast)
    show ?thesis
      using hmono he_eq \<tau>_def geotop_convex_hull_eq_HOL[of W]
        geotop_convex_hull_eq_HOL[of ?X]
      by (by100 simp)
  qed
  show ?thesis
    using h\<tau>face h\<tau>dim hesub by (by100 blast)
qed

lemma geotop_complex_edge_in_higher_simplex_has_2_simplex:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hsub: "e \<subseteq> \<sigma>"
  assumes h\<sigma>dim: "geotop_simplex_dim \<sigma> n"
  assumes hn: "2 \<le> n"
  shows "\<exists>\<tau>\<in>K. geotop_simplex_dim \<tau> 2 \<and> e \<subseteq> \<tau>"
proof -
  have hface: "geotop_is_face e \<sigma>"
    by (rule geotop_complex_subset_simplex_face[OF hK heK h\<sigma>K hsub])
  obtain \<tau> where h\<tau>face: "geotop_is_face \<tau> \<sigma>"
    and h\<tau>dim: "geotop_simplex_dim \<tau> 2"
    and he\<tau>: "e \<subseteq> \<tau>"
    using geotop_edge_face_in_ge_2_simplex_has_2_face[OF hedge hface h\<sigma>dim hn]
    by (by100 blast)
  have hface_closed: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have h\<tau>K: "\<tau> \<in> K"
    using hface_closed h\<sigma>K h\<tau>face by (by100 blast)
  show ?thesis
    using h\<tau>K h\<tau>dim he\<tau> by (by100 blast)
qed

lemma geotop_edge_closed_segment_obtain:
  fixes e :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  obtains a b where "a \<noteq> b" and "e = closed_segment a b"
proof -
  have he_dim: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  obtain V m where hV_fin: "finite V"
    and hV_card: "card V = 1 + 1"
    and hgp: "geotop_general_position V m"
    and he_eq: "e = geotop_convex_hull V"
    using he_dim unfolding geotop_simplex_dim_def by (by100 blast)
  have hV_card2: "card V = 2"
    using hV_card by (by100 simp)
  obtain a b where hab: "a \<noteq> b" and hV_eq: "V = {a, b}"
    using hV_card2 hV_fin by (auto simp: card_2_iff)
  have "e = geotop_convex_hull {a, b}"
    using he_eq hV_eq by (by100 simp)
  also have "\<dots> = convex hull {a, b}"
    by (rule geotop_convex_hull_eq_HOL)
  also have "\<dots> = closed_segment a b"
    by (rule segment_convex_hull[symmetric])
  finally have he_seg: "e = closed_segment a b" .
  show ?thesis
    by (rule that[OF hab he_seg])
qed

lemma geotop_edge_face_of_edge_eq:
  fixes e \<tau> :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  assumes h\<tau>edge: "geotop_is_edge \<tau>"
  assumes hface: "geotop_is_face e \<tau>"
  shows "e = \<tau>"
proof -
  obtain V W where h\<tau>V: "geotop_simplex_vertices \<tau> V"
    and hW_sub: "W \<subseteq> V"
    and he_eq: "e = geotop_convex_hull W"
    and heW: "geotop_simplex_vertices e W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two[OF hedge hface])
  have h\<tau>dim: "geotop_simplex_dim \<tau> 1"
    using h\<tau>edge unfolding geotop_is_edge_def by (by100 simp)
  obtain V\<^sub>\<tau> m where hV\<tau>_fin: "finite V\<^sub>\<tau>"
    and hV\<tau>_card: "card V\<^sub>\<tau> = 1 + 1"
    and h1_le_m: "1 \<le> m"
    and hgp_V\<tau>: "geotop_general_position V\<^sub>\<tau> m"
    and h\<tau>_eq: "\<tau> = geotop_convex_hull V\<^sub>\<tau>"
    using h\<tau>dim unfolding geotop_simplex_dim_def by (by100 blast)
  have h\<tau>V\<tau>: "geotop_simplex_vertices \<tau> V\<^sub>\<tau>"
    unfolding geotop_simplex_vertices_def
    using hV\<tau>_fin hV\<tau>_card h1_le_m hgp_V\<tau> h\<tau>_eq by (by100 blast)
  have hV_eq: "V = V\<^sub>\<tau>"
    by (rule geotop_simplex_vertices_unique[OF h\<tau>V h\<tau>V\<tau>])
  have hW_fin: "finite W"
    by (rule finite_subset[OF _ hV\<tau>_fin]) (use hW_sub hV_eq in \<open>by100 simp\<close>)
  have hW_eq: "W = V\<^sub>\<tau>"
  proof (rule card_subset_eq)
    show "finite V\<^sub>\<tau>"
      by (rule hV\<tau>_fin)
    show "W \<subseteq> V\<^sub>\<tau>"
      using hW_sub hV_eq by (by100 simp)
    show "card W = card V\<^sub>\<tau>"
      using hW_card hV\<tau>_card by (by100 simp)
  qed
  show ?thesis
    using he_eq h\<tau>_eq hW_eq by (by100 simp)
qed

lemma geotop_no_2_simplex_containing_edge_simplex_meeting_rel_interior_subset:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hmeet: "\<tau> \<inter> rel_interior e \<noteq> {}"
  assumes hno2: "\<not> (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)"
  shows "\<tau> \<subseteq> e"
proof -
  obtain x where hx\<tau>: "x \<in> \<tau>" and hxe_rel: "x \<in> rel_interior e"
    using hmeet by (by100 blast)
  have he_sub_\<tau>: "e \<subseteq> \<tau>"
    by (rule geotop_complex_rel_interior_imp_subset[OF hK heK h\<tau>K hxe_rel hx\<tau>])
  have h\<tau>simp: "geotop_is_simplex \<tau>"
    using geotop_is_complex_simplex[OF hK] h\<tau>K by (by100 blast)
  obtain n where h\<tau>dim: "geotop_simplex_dim \<tau> n"
    using h\<tau>simp unfolding geotop_is_simplex_def geotop_simplex_dim_def
    by (by100 blast)
  have hn_le1: "n \<le> 1"
  proof (rule ccontr)
    assume "\<not> n \<le> 1"
    hence hn_ge2: "2 \<le> n" by (by100 simp)
    have "\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>"
      by (rule geotop_complex_edge_in_higher_simplex_has_2_simplex
          [OF hK heK h\<tau>K hedge he_sub_\<tau> h\<tau>dim hn_ge2])
    thus False
      using hno2 by (by100 blast)
  qed
  have hn_cases: "n = 0 \<or> n = 1"
    using hn_le1 by (by100 linarith)
  show ?thesis
  proof (rule disjE[OF hn_cases])
    assume hn0: "n = 0"
    obtain a b where hab: "a \<noteq> b" and he_seg: "e = closed_segment a b"
      by (rule geotop_edge_closed_segment_obtain[OF hedge])
    obtain V m where hV_fin: "finite V"
      and hV_card: "card V = 0 + 1"
      and h\<tau>_eq: "\<tau> = geotop_convex_hull V"
      using h\<tau>dim hn0 unfolding geotop_simplex_dim_def by (by100 blast)
    have hV_card1: "card V = 1"
      using hV_card by (by100 simp)
    obtain c where hV_eq: "V = {c}"
      using hV_card1 by (rule card_1_singletonE)
    have h\<tau>_sing: "\<tau> = {c}"
      using h\<tau>_eq hV_eq geotop_convex_hull_eq_HOL[of "{c}"] by (by100 simp)
    have ha\<tau>: "a \<in> \<tau>"
    proof -
      have "a \<in> e"
        using he_seg by (by100 simp)
      thus ?thesis
        using he_sub_\<tau> by (by100 blast)
    qed
    have hb\<tau>: "b \<in> \<tau>"
    proof -
      have "b \<in> e"
        using he_seg by (by100 simp)
      thus ?thesis
        using he_sub_\<tau> by (by100 blast)
    qed
    have "a = b"
      using ha\<tau> hb\<tau> h\<tau>_sing by (by100 simp)
    thus ?thesis
      using hab by (by100 blast)
  next
    assume hn1: "n = 1"
    have h\<tau>edge: "geotop_is_edge \<tau>"
      using h\<tau>dim hn1 unfolding geotop_is_edge_def by (by100 simp)
    have hface: "geotop_is_face e \<tau>"
      by (rule geotop_complex_subset_simplex_face[OF hK heK h\<tau>K he_sub_\<tau>])
    have heq: "e = \<tau>"
      by (rule geotop_edge_face_of_edge_eq[OF hedge h\<tau>edge hface])
    show ?thesis
      using heq by (by100 simp)
  qed
qed

lemma geotop_complex_no_2_simplex_over_edge_rel_interior_open:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hno2: "\<not> (\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>)"
  shows "rel_interior e \<in>
    subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
proof -
  obtain a b where hab: "a \<noteq> b" and he_seg: "e = closed_segment a b"
    by (rule geotop_edge_closed_segment_obtain[OF hedge])
  have hrel_eq: "rel_interior e = open_segment a b"
    using he_seg hab rel_interior_closed_segment[of a b] by (by100 simp)
  have hrel_as_diff: "rel_interior e = e - {a, b}"
    using hrel_eq he_seg unfolding open_segment_def by (by100 simp)
  have hlocal_fin:
    "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]]])
  have hlocal_e: "\<exists>U. open U \<and> e \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule bspec[OF hlocal_fin heK])
  obtain U where hU_open: "open U"
    and heU: "e \<subseteq> U"
    and hU_fin: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    using hlocal_e by (elim exE conjE)
  let ?F = "{\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
  let ?Bad = "{\<tau>\<in>?F. \<tau> \<inter> rel_interior e = {}}"
  have hBad_fin: "finite ?Bad"
  proof -
    have "?Bad \<subseteq> ?F"
      by (by100 blast)
    show ?thesis
      by (rule finite_subset[OF \<open>?Bad \<subseteq> ?F\<close> hU_fin])
  qed
  have hBad_closed: "\<forall>\<tau>\<in>?Bad. closed \<tau>"
  proof
    fix \<tau> assume h\<tau>: "\<tau> \<in> ?Bad"
    have h\<tau>K: "\<tau> \<in> K"
      using h\<tau> by (by100 simp)
    show "closed \<tau>"
      by (rule geotop_complex_simplex_closed[OF hK h\<tau>K])
  qed
  have hB_closed: "closed (\<Union>?Bad)"
    by (rule closed_Union[OF hBad_fin hBad_closed])
  have hend_closed: "closed ({a, b}::(real^2) set)"
    by (by100 simp)
  define W where "W = U - \<Union>?Bad - {a, b}"
  have hW_open_HOL: "open W"
  proof -
    have hU_B_open: "open (U - \<Union>?Bad)"
      by (rule open_Diff[OF hU_open hB_closed])
    show ?thesis
      unfolding W_def by (rule open_Diff[OF hU_B_open hend_closed])
  qed
  have hpoly_inter_W: "geotop_polyhedron K \<inter> W = rel_interior e"
  proof
    show "geotop_polyhedron K \<inter> W \<subseteq> rel_interior e"
    proof
      fix x assume hx: "x \<in> geotop_polyhedron K \<inter> W"
      have hx_poly: "x \<in> geotop_polyhedron K"
        using hx by (by100 simp)
      have hxW: "x \<in> W"
        using hx by (by100 simp)
      have hxU: "x \<in> U"
        using hxW unfolding W_def by (by100 simp)
      have hx_not_end: "x \<notin> {a, b}"
        using hxW unfolding W_def by (by100 simp)
      obtain \<tau> where h\<tau>K: "\<tau> \<in> K" and hx\<tau>: "x \<in> \<tau>"
        using hx_poly unfolding geotop_polyhedron_def by (by100 blast)
      have h\<tau>F: "\<tau> \<in> ?F"
        using h\<tau>K hx\<tau> hxU by (by100 blast)
      have h\<tau>meet: "\<tau> \<inter> rel_interior e \<noteq> {}"
      proof (rule ccontr)
        assume "\<not> \<tau> \<inter> rel_interior e \<noteq> {}"
        hence h\<tau>bad: "\<tau> \<in> ?Bad"
          using h\<tau>F by (by100 simp)
        have "x \<in> \<Union>?Bad"
          using h\<tau>bad hx\<tau> by (by100 blast)
        thus False
          using hxW unfolding W_def by (by100 simp)
      qed
      have h\<tau>sube: "\<tau> \<subseteq> e"
        by (rule geotop_no_2_simplex_containing_edge_simplex_meeting_rel_interior_subset
            [OF hK heK h\<tau>K hedge h\<tau>meet hno2])
      have hxe: "x \<in> e"
        using h\<tau>sube hx\<tau> by (by100 blast)
      show "x \<in> rel_interior e"
        using hxe hx_not_end hrel_as_diff by (by100 blast)
    qed
  next
    show "rel_interior e \<subseteq> geotop_polyhedron K \<inter> W"
    proof
      fix x assume hxrel: "x \<in> rel_interior e"
      have hxe: "x \<in> e"
        using hxrel rel_interior_subset by (by100 blast)
      have hx_poly: "x \<in> geotop_polyhedron K"
        using heK hxe unfolding geotop_polyhedron_def by (by100 blast)
      have hxU: "x \<in> U"
        using heU hxe by (by100 blast)
      have hx_not_B: "x \<notin> \<Union>?Bad"
      proof
        assume "x \<in> \<Union>?Bad"
        then obtain \<tau> where h\<tau>bad: "\<tau> \<in> ?Bad" and hx\<tau>: "x \<in> \<tau>"
          by (by100 blast)
        have "\<tau> \<inter> rel_interior e \<noteq> {}"
          using hx\<tau> hxrel by (by100 blast)
        thus False
          using h\<tau>bad by (by100 simp)
      qed
      have hx_not_end: "x \<notin> {a, b}"
        using hxrel hrel_as_diff by (by100 blast)
      have hxW: "x \<in> W"
        unfolding W_def using hxU hx_not_B hx_not_end by (by100 simp)
      show "x \<in> geotop_polyhedron K \<inter> W"
        using hx_poly hxW by (by100 simp)
    qed
  qed
  have hW_top: "W \<in> geotop_euclidean_topology"
    by (metis hW_open_HOL geotop_euclidean_topology_eq_open_sets
        mem_Collect_eq top1_open_sets_def)
  show ?thesis
    unfolding subspace_topology_def
    using hW_top hpoly_inter_W by (by100 blast)
qed

lemma geotop_complex_2_faces_over_edge_finite:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  shows "finite {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
proof -
  have hlocal:
    "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule geotop_is_complex_locally_finite[OF hK])
  obtain U where hU_open: "open U" and heU: "e \<subseteq> U"
      and hU_fin: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    using bspec[OF hlocal heK] by (elim exE conjE)
  have he_dim: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  have he_simplex: "geotop_is_simplex e"
    by (rule geotop_simplex_dim_imp_is_simplex[OF he_dim])
  have he_ne: "e \<noteq> {}"
    by (rule geotop_simplex_nonempty[OF he_simplex])
  have hsub: "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}
      \<subseteq> {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma> assume h\<sigma>: "\<sigma> \<in> {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
    have h\<sigma>K: "\<sigma> \<in> K"
      using h\<sigma> by (by100 simp)
    have hface: "geotop_is_face e \<sigma>"
      using h\<sigma> by (by100 simp)
    have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset[OF hface])
    obtain x where hxe: "x \<in> e"
      using he_ne by (by100 blast)
    have "x \<in> \<sigma> \<inter> U"
      using hxe he_sub_\<sigma> heU by (by100 blast)
    thus "\<sigma> \<in> {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
      using h\<sigma>K by (by100 blast)
  qed
  show ?thesis
    by (rule finite_subset[OF hsub hU_fin])
qed

lemma geotop_complex_edge_in_2_simplex_imp_face_count_ge_1:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hex: "\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>"
  shows "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 1"
proof -
  let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  have hSfin: "finite ?S"
    by (rule geotop_complex_2_faces_over_edge_finite[OF hK heK hedge])
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K" and h\<sigma>dim: "geotop_simplex_dim \<sigma> 2"
      and he_sub_\<sigma>: "e \<subseteq> \<sigma>"
    using hex by (by100 blast)
  have hface: "geotop_is_face e \<sigma>"
    by (rule geotop_complex_subset_simplex_face[OF hK heK h\<sigma>K he_sub_\<sigma>])
  have h\<sigma>S: "\<sigma> \<in> ?S"
    using h\<sigma>K h\<sigma>dim hface by (by100 simp)
  have hSne: "?S \<noteq> {}"
    using h\<sigma>S by (by100 blast)
  have hcard_ne0: "card ?S \<noteq> 0"
  proof
    assume "card ?S = 0"
    hence "?S = {}"
      using hSfin by (by100 simp)
    thus False
      using hSne by (by100 blast)
  qed
  thus ?thesis
    by (by100 simp)
qed

lemma geotop_link_vertex_incident_2simplex_incident_link_edge:
  fixes K :: "(real^2) set set" and e \<sigma> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwL: "{w} \<in> geotop_link K v"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  assumes hw_e: "w \<in> e"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes hface: "geotop_is_face e \<sigma>"
  shows "\<exists>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l"
proof -
  have he_sub_\<sigma>: "e \<subseteq> \<sigma>"
    by (rule geotop_is_face_imp_subset[OF hface])
  have hex: "\<exists>\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> e \<subseteq> \<sigma>"
    using h\<sigma>K h\<sigma>2 he_sub_\<sigma> by (by100 blast)
  have hcount:
    "1 \<le> card {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
    by (rule geotop_complex_edge_in_2_simplex_imp_face_count_ge_1
        [OF hK heK hedge hex])
  show ?thesis
    by (rule geotop_link_vertex_incident_edge_count_ge_1_incident_link_edge
        [OF hK hvK hwL heK hedge hv_e hw_e hcount])
qed

lemma geotop_link_vertex_two_adjacent_faces_witness:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwL: "{w} \<in> geotop_link K v"
  assumes htwo:
    "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
      (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>})"
  shows "\<exists>e \<sigma> \<tau>. e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
      \<and> \<sigma> \<noteq> \<tau>
      \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
      \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
      \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
proof -
  obtain e where heK: "e \<in> K"
    and hedge: "geotop_is_edge e"
    and hv_e: "v \<in> e"
    and hw_e: "w \<in> e"
    using geotop_link_vertex_incident_edge_witness[OF hK hvK hwL]
    by (by100 blast)
  obtain \<sigma> \<tau> where h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
    and h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and h\<sigma>face: "geotop_is_face e \<sigma>"
    and h\<tau>K: "\<tau> \<in> K"
    and h\<tau>2: "geotop_simplex_dim \<tau> 2"
    and h\<tau>face: "geotop_is_face e \<tau>"
    and hfaces: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
    using htwo heK hedge hv_e by (by100 blast)
  show ?thesis
    using heK hedge hv_e hw_e h\<sigma>\<tau> h\<sigma>K h\<sigma>2 h\<sigma>face h\<tau>K h\<tau>2 h\<tau>face hfaces
    by (by100 blast)
qed

lemma geotop_link_vertex_two_adjacent_link_edge_witnesses:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwL: "{w} \<in> geotop_link K v"
  assumes htwo:
    "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
      (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>})"
  shows "\<exists>e \<sigma> \<tau> l\<^sub>\<sigma> l\<^sub>\<tau>. e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
      \<and> \<sigma> \<noteq> \<tau>
      \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
      \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
      \<and> l\<^sub>\<sigma> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<sigma> \<and> w \<in> l\<^sub>\<sigma>
      \<and> l\<^sub>\<tau> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<tau> \<and> w \<in> l\<^sub>\<tau>"
proof -
  obtain e \<sigma> \<tau> where heK: "e \<in> K"
    and hedge: "geotop_is_edge e"
    and hv_e: "v \<in> e"
    and hw_e: "w \<in> e"
    and h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
    and h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and h\<sigma>face: "geotop_is_face e \<sigma>"
    and h\<tau>K: "\<tau> \<in> K"
    and h\<tau>2: "geotop_simplex_dim \<tau> 2"
    and h\<tau>face: "geotop_is_face e \<tau>"
    and hfaces: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
    using geotop_link_vertex_two_adjacent_faces_witness[OF hK hvK hwL htwo]
    by (by100 blast)
  obtain l\<^sub>\<sigma> where hl\<sigma>L: "l\<^sub>\<sigma> \<in> geotop_link K v"
    and hl\<sigma>edge: "geotop_is_edge l\<^sub>\<sigma>"
    and hw_l\<sigma>: "w \<in> l\<^sub>\<sigma>"
    using geotop_link_vertex_incident_2simplex_incident_link_edge
      [OF hK hvK hwL heK hedge hv_e hw_e h\<sigma>K h\<sigma>2 h\<sigma>face]
    by (by100 blast)
  obtain l\<^sub>\<tau> where hl\<tau>L: "l\<^sub>\<tau> \<in> geotop_link K v"
    and hl\<tau>edge: "geotop_is_edge l\<^sub>\<tau>"
    and hw_l\<tau>: "w \<in> l\<^sub>\<tau>"
    using geotop_link_vertex_incident_2simplex_incident_link_edge
      [OF hK hvK hwL heK hedge hv_e hw_e h\<tau>K h\<tau>2 h\<tau>face]
    by (by100 blast)
  show ?thesis
    using heK hedge hv_e hw_e h\<sigma>\<tau> h\<sigma>K h\<sigma>2 h\<sigma>face h\<tau>K h\<tau>2 h\<tau>face
      hl\<sigma>L hl\<sigma>edge hw_l\<sigma> hl\<tau>L hl\<tau>edge hw_l\<tau>
    by (by100 blast)
qed

lemma geotop_link_edge_lies_in_2simplex_with_vertex:
  fixes K :: "(real^2) set set" and l :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hlL: "l \<in> geotop_link K v"
  assumes hledge: "geotop_is_edge l"
  shows "\<exists>\<rho>\<in>K. geotop_simplex_dim \<rho> 2
      \<and> geotop_is_face l \<rho>
      \<and> v \<in> \<rho>"
proof -
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    and hv\<sigma>: "v \<in> \<sigma>"
    and hl\<sigma>_case: "geotop_is_face l \<sigma> \<or> l = \<sigma>"
    using hlL unfolding geotop_link_def geotop_star_def by (by100 blast)
  have hv_not_l: "v \<notin> l"
    using hlL unfolding geotop_link_def by (by100 blast)
  have hl\<sigma>: "geotop_is_face l \<sigma>"
  proof (rule disjE[OF hl\<sigma>_case])
    assume "geotop_is_face l \<sigma>"
    thus ?thesis .
  next
    assume hl_eq: "l = \<sigma>"
    have False
      using hv\<sigma> hv_not_l hl_eq by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  obtain V W where h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and hl_eq: "l = geotop_convex_hull W"
    and hlW: "geotop_simplex_vertices l W"
    and hW_card: "card W = 2"
    by (rule geotop_edge_face_witness_card_two[OF hledge hl\<sigma>])
  obtain Vv where h\<sigma>Vv: "geotop_simplex_vertices \<sigma> Vv"
    and hvVv: "v \<in> Vv"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK h\<sigma>K hv\<sigma>]
    by (by100 blast)
  have hVv_eq: "Vv = V"
    by (rule geotop_simplex_vertices_unique[OF h\<sigma>Vv h\<sigma>V])
  have hvV: "v \<in> V"
    using hvVv hVv_eq by (by100 simp)
  have hW_fin: "finite W"
    using hlW unfolding geotop_simplex_vertices_def by (by100 blast)
  have hv_not_W: "v \<notin> W"
  proof
    assume hvW: "v \<in> W"
    have "v \<in> convex hull W"
      using hvW hull_inc[of v W] by (by100 simp)
    hence "v \<in> geotop_convex_hull W"
      using geotop_convex_hull_eq_HOL[of W] by (by100 simp)
    hence "v \<in> l"
      using hl_eq by (by100 simp)
    thus False
      using hv_not_l by (by100 blast)
  qed
  have hWV_sub: "W \<union> {v} \<subseteq> V"
    using hW_sub hvV by (by100 blast)
  have hWV_card: "card (W \<union> {v}) = 3"
    using hW_fin hW_card hv_not_W by (by100 simp)
  obtain n m where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp_V: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hcard_le: "card (W \<union> {v}) \<le> card V"
    by (rule card_mono[OF hV_fin hWV_sub])
  have hn_ge2: "2 \<le> n"
    using hV_card hWV_card hcard_le by (by100 linarith)
  have h\<sigma>dim_n: "geotop_simplex_dim \<sigma> n"
    unfolding geotop_simplex_dim_def
    using hV_fin hV_card hn_le_m hgp_V h\<sigma>_eq by (by100 blast)
  have hn_le2: "n \<le> 2"
    by (rule geotop_simplex_dim_le_2_R2[OF h\<sigma>dim_n])
  have hn_eq2: "n = 2"
    using hn_ge2 hn_le2 by (by100 linarith)
  have h\<sigma>dim2: "geotop_simplex_dim \<sigma> 2"
    using h\<sigma>dim_n hn_eq2 by (by100 simp)
  show ?thesis
    using h\<sigma>K h\<sigma>dim2 hl\<sigma> hv\<sigma> by (by100 blast)
qed

lemma geotop_link_edge_through_vertex_adjacent_2simplex_witness:
  fixes K :: "(real^2) set set" and e l :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwL: "{w} \<in> geotop_link K v"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  assumes hw_e: "w \<in> e"
  assumes hlL: "l \<in> geotop_link K v"
  assumes hledge: "geotop_is_edge l"
  assumes hw_l: "w \<in> l"
  shows "\<exists>\<rho>\<in>K. geotop_simplex_dim \<rho> 2
      \<and> geotop_is_face e \<rho>
      \<and> geotop_is_face l \<rho>"
proof -
  obtain \<rho> where h\<rho>K: "\<rho> \<in> K"
    and h\<rho>2: "geotop_simplex_dim \<rho> 2"
    and hl\<rho>: "geotop_is_face l \<rho>"
    and hv\<rho>: "v \<in> \<rho>"
    using geotop_link_edge_lies_in_2simplex_with_vertex[OF hK hvK hlL hledge]
    by (by100 blast)
  have hlink_sub: "geotop_link K v \<subseteq> K"
    by (rule geotop_link_subset_complex[OF hK])
  have hwK: "{w} \<in> K"
    using hlink_sub hwL by (by100 blast)
  have hv_not_w: "v \<noteq> w"
    using hwL unfolding geotop_link_def by (by100 blast)
  have hl_sub_\<rho>: "l \<subseteq> \<rho>"
    by (rule geotop_is_face_imp_subset[OF hl\<rho>])
  have hw\<rho>: "w \<in> \<rho>"
    using hw_l hl_sub_\<rho> by (by100 blast)
  obtain V\<^sub>v where h\<rho>Vv: "geotop_simplex_vertices \<rho> V\<^sub>v"
    and hvVv: "v \<in> V\<^sub>v"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hvK h\<rho>K hv\<rho>]
    by (by100 blast)
  obtain V\<^sub>w where h\<rho>Vw: "geotop_simplex_vertices \<rho> V\<^sub>w"
    and hwVw: "w \<in> V\<^sub>w"
    using geotop_complex_singleton_point_is_simplex_vertex[OF hK hwK h\<rho>K hw\<rho>]
    by (by100 blast)
  have hVw_eq: "V\<^sub>w = V\<^sub>v"
    by (rule geotop_simplex_vertices_unique[OF h\<rho>Vw h\<rho>Vv])
  have hwVv: "w \<in> V\<^sub>v"
    using hwVw hVw_eq by (by100 simp)
  obtain e' where he'\<rho>: "geotop_is_face e' \<rho>"
    and he'edge: "geotop_is_edge e'"
    and hv_e': "v \<in> e'"
    and hw_e': "w \<in> e'"
    using geotop_simplex_vertices_pair_edge_face_between
      [OF h\<rho>Vv hvVv hwVv hv_not_w]
    by (by100 blast)
  have hface_closed: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have he'K: "e' \<in> K"
    using hface_closed h\<rho>K he'\<rho> by (by100 blast)
  have he_eq: "e = e'"
    by (rule geotop_complex_edges_same_two_vertices_eq_dev34
        [OF hK hvK hwK heK he'K hedge he'edge hv_e hw_e hv_e' hw_e' hv_not_w])
  have he\<rho>: "geotop_is_face e \<rho>"
    using he'\<rho> he_eq by (by100 simp)
  show ?thesis
    using h\<rho>K h\<rho>2 he\<rho> hl\<rho> by (by100 blast)
qed

lemma geotop_link_vertex_two_incident_link_edges_exhaust:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwL: "{w} \<in> geotop_link K v"
  assumes htwo:
    "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
      (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
        \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
        \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
        \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>})"
  shows "\<exists>e \<sigma> \<tau> l\<^sub>\<sigma> l\<^sub>\<tau>.
      e \<in> K \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e
      \<and> \<sigma> \<noteq> \<tau>
      \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
      \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
      \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}
      \<and> l\<^sub>\<sigma> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<sigma> \<and> w \<in> l\<^sub>\<sigma>
      \<and> l\<^sub>\<tau> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<tau> \<and> w \<in> l\<^sub>\<tau>
      \<and> l\<^sub>\<sigma> \<noteq> l\<^sub>\<tau>
      \<and> (\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
            \<longrightarrow> l = l\<^sub>\<sigma> \<or> l = l\<^sub>\<tau>)"
proof -
  obtain e \<sigma> \<tau> where heK: "e \<in> K"
    and hedge: "geotop_is_edge e"
    and hv_e: "v \<in> e"
    and hw_e: "w \<in> e"
    and h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
    and h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and h\<sigma>face: "geotop_is_face e \<sigma>"
    and h\<tau>K: "\<tau> \<in> K"
    and h\<tau>2: "geotop_simplex_dim \<tau> 2"
    and h\<tau>face: "geotop_is_face e \<tau>"
    and hfaces: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
    using geotop_link_vertex_two_adjacent_faces_witness[OF hK hvK hwL htwo]
    by (by100 blast)
  obtain V\<^sub>\<sigma> u\<^sub>\<sigma> where hV\<sigma>: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>"
    and hvV\<sigma>: "v \<in> V\<^sub>\<sigma>"
    and hwV\<sigma>: "w \<in> V\<^sub>\<sigma>"
    and huV\<sigma>: "u\<^sub>\<sigma> \<in> V\<^sub>\<sigma>"
    and hu\<sigma>_ne_v: "u\<^sub>\<sigma> \<noteq> v"
    and hu\<sigma>_ne_w: "u\<^sub>\<sigma> \<noteq> w"
    and hface_l\<sigma>: "geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>"
    and hl\<sigma>L: "geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v"
    and hl\<sigma>edge: "geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})"
    and hw_l\<sigma>: "w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}"
    and hu\<sigma>_l\<sigma>: "u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}"
    using geotop_link_vertex_incident_2simplex_opposite_vertex_face_link_edge
      [OF hK hvK hwL heK hedge hv_e hw_e h\<sigma>K h\<sigma>2 h\<sigma>face]
    by (by100 blast)
  obtain V\<^sub>\<tau> u\<^sub>\<tau> where hV\<tau>: "geotop_simplex_vertices \<tau> V\<^sub>\<tau>"
    and hvV\<tau>: "v \<in> V\<^sub>\<tau>"
    and hwV\<tau>: "w \<in> V\<^sub>\<tau>"
    and huV\<tau>: "u\<^sub>\<tau> \<in> V\<^sub>\<tau>"
    and hu\<tau>_ne_v: "u\<^sub>\<tau> \<noteq> v"
    and hu\<tau>_ne_w: "u\<^sub>\<tau> \<noteq> w"
    and hface_l\<tau>: "geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>"
    and hl\<tau>L: "geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v"
    and hl\<tau>edge: "geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})"
    and hw_l\<tau>: "w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
    and hu\<tau>_l\<tau>: "u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
    using geotop_link_vertex_incident_2simplex_opposite_vertex_face_link_edge
      [OF hK hvK hwL heK hedge hv_e hw_e h\<tau>K h\<tau>2 h\<tau>face]
    by (by100 blast)
  let ?l\<^sub>\<sigma> = "geotop_convex_hull {w, u\<^sub>\<sigma>}"
  let ?l\<^sub>\<tau> = "geotop_convex_hull {w, u\<^sub>\<tau>}"
  have hv_ne_w: "v \<noteq> w"
    using hwL unfolding geotop_link_def by (by100 blast)
  have hv_ne_u\<sigma>: "v \<noteq> u\<^sub>\<sigma>"
    using hu\<sigma>_ne_v by (by100 blast)
  have hw_ne_u\<sigma>: "w \<noteq> u\<^sub>\<sigma>"
    using hu\<sigma>_ne_w by (by100 blast)
  have hv_ne_u\<tau>: "v \<noteq> u\<^sub>\<tau>"
    using hu\<tau>_ne_v by (by100 blast)
  have hw_ne_u\<tau>: "w \<noteq> u\<^sub>\<tau>"
    using hu\<tau>_ne_w by (by100 blast)
  have hl_distinct: "?l\<^sub>\<sigma> \<noteq> ?l\<^sub>\<tau>"
    by (rule geotop_two_2simplex_opposite_edges_distinct_dev34
        [OF h\<sigma>2 h\<tau>2 hV\<sigma> hV\<tau> h\<sigma>\<tau> hv_ne_w hvV\<sigma> hwV\<sigma> huV\<sigma>
            hvV\<tau> hwV\<tau> huV\<tau> hu\<sigma>_ne_v hu\<sigma>_ne_w hu\<tau>_ne_v hu\<tau>_ne_w])
  have hexhaust:
    "\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
      \<longrightarrow> l = ?l\<^sub>\<sigma> \<or> l = ?l\<^sub>\<tau>"
  proof (intro allI impI)
    fix l
    assume hl_inc: "l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l"
    have hlL: "l \<in> geotop_link K v"
      using hl_inc by (by100 blast)
    have hledge: "geotop_is_edge l"
      using hl_inc by (by100 blast)
    have hw_l: "w \<in> l"
      using hl_inc by (by100 blast)
    obtain \<rho> where h\<rho>K: "\<rho> \<in> K"
      and h\<rho>2: "geotop_simplex_dim \<rho> 2"
      and he\<rho>: "geotop_is_face e \<rho>"
      and hl\<rho>: "geotop_is_face l \<rho>"
      using geotop_link_edge_through_vertex_adjacent_2simplex_witness
        [OF hK hvK hwL heK hedge hv_e hw_e hlL hledge hw_l]
      by (by100 blast)
    have h\<rho>in_faces: "\<rho> \<in> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
      using h\<rho>K h\<rho>2 he\<rho> by (by100 simp)
    have h\<rho>case: "\<rho> = \<sigma> \<or> \<rho> = \<tau>"
      using h\<rho>in_faces hfaces by (by100 blast)
    have hv_not_l: "v \<notin> l"
      using hlL unfolding geotop_link_def by (by100 blast)
    show "l = ?l\<^sub>\<sigma> \<or> l = ?l\<^sub>\<tau>"
    proof (rule disjE[OF h\<rho>case])
      assume h\<rho>\<sigma>: "\<rho> = \<sigma>"
      have hl\<sigma>: "geotop_is_face l \<sigma>"
        using hl\<rho> h\<rho>\<sigma> by (by100 simp)
      have "l = ?l\<^sub>\<sigma>"
        by (rule geotop_2simplex_edge_face_through_vertex_not_other_eq_opposite_dev34
            [OF h\<sigma>2 hV\<sigma> hvV\<sigma> hwV\<sigma> huV\<sigma> hv_ne_w hv_ne_u\<sigma> hw_ne_u\<sigma>
                hl\<sigma> hledge hw_l hv_not_l])
      thus ?thesis
        by (by100 blast)
    next
      assume h\<rho>\<tau>: "\<rho> = \<tau>"
      have hl\<tau>: "geotop_is_face l \<tau>"
        using hl\<rho> h\<rho>\<tau> by (by100 simp)
      have "l = ?l\<^sub>\<tau>"
        by (rule geotop_2simplex_edge_face_through_vertex_not_other_eq_opposite_dev34
            [OF h\<tau>2 hV\<tau> hvV\<tau> hwV\<tau> huV\<tau> hv_ne_w hv_ne_u\<tau> hw_ne_u\<tau>
                hl\<tau> hledge hw_l hv_not_l])
      thus ?thesis
        by (by100 blast)
    qed
  qed
  show ?thesis
    using heK hedge hv_e hw_e h\<sigma>\<tau> h\<sigma>K h\<sigma>2 h\<sigma>face h\<tau>K h\<tau>2 h\<tau>face hfaces
      hl\<sigma>L hl\<sigma>edge hw_l\<sigma> hl\<tau>L hl\<tau>edge hw_l\<tau> hl_distinct hexhaust
    by (by100 blast)
qed

lemma geotop_complex_edge_face_count_eq_1_unique:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hcard: "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 1"
  shows "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
proof -
  let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  obtain \<sigma> where hSeq: "?S = {\<sigma>}"
    using hcard by (rule card_1_singletonE)
  show ?thesis
  proof (rule ex1I[where a=\<sigma>])
    have h\<sigma>S: "\<sigma> \<in> ?S"
      using hSeq by (by100 blast)
    show "\<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
      using h\<sigma>S by (by100 simp)
  next
    fix \<tau>
    assume h\<tau>: "\<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>"
    have "\<tau> \<in> ?S"
      using h\<tau> by (by100 simp)
    thus "\<tau> = \<sigma>"
      using hSeq by (by100 simp)
  qed
qed

lemma geotop_complex_edge_face_count_eq_2_obtain:
  fixes K :: "(real^2) set set"
  assumes hcard: "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} = 2"
  shows "\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
      \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
      \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
      \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
proof -
  let ?S = "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
  have hS2: "\<exists>\<sigma> \<tau>. ?S = {\<sigma>, \<tau>} \<and> \<sigma> \<noteq> \<tau>"
    using hcard
    apply (simp add: card_2_iff)
    done
  from hS2 obtain \<sigma> where hS2_\<sigma>: "\<exists>\<tau>. ?S = {\<sigma>, \<tau>} \<and> \<sigma> \<noteq> \<tau>" ..
  from hS2_\<sigma> obtain \<tau> where hS2w: "?S = {\<sigma>, \<tau>} \<and> \<sigma> \<noteq> \<tau>" ..
  have hSeq: "?S = {\<sigma>, \<tau>}"
    using hS2w by (by100 simp)
  have h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
    using hS2w by (by100 simp)
  have h\<sigma>S: "\<sigma> \<in> ?S"
    using hSeq by (by100 blast)
  have h\<tau>S: "\<tau> \<in> ?S"
    using hSeq by (by100 blast)
  show ?thesis
    using h\<sigma>\<tau> hSeq h\<sigma>S h\<tau>S by (by100 blast)
qed

lemma geotop_complex_edge_face_count_ge_3_obtain:
  fixes K :: "(real^2) set set"
  assumes hcard: "3 \<le> card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  shows "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
proof -
  let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  obtain W where hW_sub: "W \<subseteq> ?S" and hW_card: "card W = 3"
    using obtain_subset_with_card_n[OF hcard] by auto
  have hW_three:
    "\<exists>\<sigma>1 \<sigma>2 \<sigma>3. W = {\<sigma>1, \<sigma>2, \<sigma>3}
      \<and> \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3"
    using hW_card unfolding card_3_iff by (by100 simp)
  from hW_three obtain \<sigma>1 where hW1:
    "\<exists>\<sigma>2 \<sigma>3. W = {\<sigma>1, \<sigma>2, \<sigma>3}
      \<and> \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3" ..
  from hW1 obtain \<sigma>2 where hW2:
    "\<exists>\<sigma>3. W = {\<sigma>1, \<sigma>2, \<sigma>3}
      \<and> \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3" ..
  from hW2 obtain \<sigma>3 where hW3:
    "W = {\<sigma>1, \<sigma>2, \<sigma>3}
      \<and> \<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3" ..
  have hW_eq: "W = {\<sigma>1, \<sigma>2, \<sigma>3}"
    using hW3 by (by100 simp)
  have h12: "\<sigma>1 \<noteq> \<sigma>2"
    using hW3 by (by100 simp)
  have h23: "\<sigma>2 \<noteq> \<sigma>3"
    using hW3 by (by100 simp)
  have h13: "\<sigma>1 \<noteq> \<sigma>3"
    using hW3 by (by100 simp)
  have h\<sigma>1S: "\<sigma>1 \<in> ?S"
    using hW_eq hW_sub by (by100 blast)
  have h\<sigma>2S: "\<sigma>2 \<in> ?S"
    using hW_eq hW_sub by (by100 blast)
  have h\<sigma>3S: "\<sigma>3 \<in> ?S"
    using hW_eq hW_sub by (by100 blast)
  have hbody: "\<sigma>1 \<noteq> \<sigma>2 \<and> \<sigma>2 \<noteq> \<sigma>3 \<and> \<sigma>1 \<noteq> \<sigma>3
      \<and> \<sigma>1 \<in> K \<and> geotop_simplex_dim \<sigma>1 2 \<and> geotop_is_face e \<sigma>1
      \<and> \<sigma>2 \<in> K \<and> geotop_simplex_dim \<sigma>2 2 \<and> geotop_is_face e \<sigma>2
      \<and> \<sigma>3 \<in> K \<and> geotop_simplex_dim \<sigma>3 2 \<and> geotop_is_face e \<sigma>3"
  proof (intro conjI)
    show "\<sigma>1 \<noteq> \<sigma>2" by (rule h12)
    show "\<sigma>2 \<noteq> \<sigma>3" by (rule h23)
    show "\<sigma>1 \<noteq> \<sigma>3" by (rule h13)
    show "\<sigma>1 \<in> K" using h\<sigma>1S by (by100 simp)
    show "geotop_simplex_dim \<sigma>1 2" using h\<sigma>1S by (by100 simp)
    show "geotop_is_face e \<sigma>1" using h\<sigma>1S by (by100 simp)
    show "\<sigma>2 \<in> K" using h\<sigma>2S by (by100 simp)
    show "geotop_simplex_dim \<sigma>2 2" using h\<sigma>2S by (by100 simp)
    show "geotop_is_face e \<sigma>2" using h\<sigma>2S by (by100 simp)
    show "\<sigma>3 \<in> K" using h\<sigma>3S by (by100 simp)
    show "geotop_simplex_dim \<sigma>3 2" using h\<sigma>3S by (by100 simp)
    show "geotop_is_face e \<sigma>3" using h\<sigma>3S by (by100 simp)
  qed
  show ?thesis
    by (rule exI[where x=\<sigma>1], rule exI[where x=\<sigma>2],
        rule exI[where x=\<sigma>3], rule hbody)
qed

lemma geotop_complex_edge_face_count_between_1_2_cases:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hge: "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<ge> 1"
  assumes hle: "card {\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>} \<le> 2"
  shows "(\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>)
      \<or> (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
          \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
          \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
          \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>})"
proof -
  let ?S = "{\<sigma>\<in>K. geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>}"
  have hcase: "card ?S = 1 \<or> card ?S = 2"
    using hge hle by (by100 arith)
  show ?thesis
  proof (rule disjE[OF hcase])
    assume hcard1: "card ?S = 1"
    have "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
      by (rule geotop_complex_edge_face_count_eq_1_unique[OF hK heK hedge hcard1])
    thus ?thesis by (by100 blast)
  next
    assume hcard2: "card ?S = 2"
    have "\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
          \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
          \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
          \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
      by (rule geotop_complex_edge_face_count_eq_2_obtain[OF hcard2])
    thus ?thesis by (by100 blast)
  qed
qed

lemma geotop_edge_rel_interior_nonempty:
  fixes e :: "(real^2) set"
  assumes hedge: "geotop_is_edge e"
  shows "rel_interior e \<noteq> {}"
proof -
  have he_dim: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  have he_simplex: "geotop_is_simplex e"
    by (rule geotop_simplex_dim_imp_is_simplex[OF he_dim])
  show ?thesis
    by (rule geotop_simplex_rel_interior_nonempty[OF he_simplex])
qed

lemma geotop_edge_rel_interior_open_neighborhood_two_sides:
  fixes e N :: "(real^2) set" and p :: "real^2"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hNopen: "N \<in> subspace_topology UNIV geotop_euclidean_topology (rel_interior e)"
  assumes hpN: "p \<in> N"
  obtains a b x y where "a \<noteq> b" and "e = closed_segment a b"
    and "x \<in> N - {p}" and "y \<in> N - {p}"
    and "inner (b - a) x < inner (b - a) p"
    and "inner (b - a) p < inner (b - a) y"
    and "\<forall>z\<in>rel_interior e. z \<noteq> p \<longrightarrow>
          inner (b - a) z < inner (b - a) p \<or>
          inner (b - a) p < inner (b - a) z"
proof -
  obtain a b where hab: "a \<noteq> b" and he_seg: "e = closed_segment a b"
    by (rule geotop_edge_closed_segment_obtain[OF hedge])
  have hrel_eq: "rel_interior e = open_segment a b"
    using he_seg hab rel_interior_closed_segment[of a b] by (by100 simp)
  obtain U where hUtop: "U \<in> geotop_euclidean_topology"
    and hN_eq: "N = rel_interior e \<inter> U"
    using hNopen unfolding subspace_topology_def by (by100 blast)
  have hUopen: "open U"
    using hUtop unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hpU: "p \<in> U"
    using hpN hN_eq by (by100 blast)
  have hU_ball: "\<forall>q\<in>U. \<exists>\<epsilon>>0. ball q \<epsilon> \<subseteq> U"
    using hUopen unfolding open_contains_ball by (by100 simp)
  obtain \<delta> where h\<delta>pos: "\<delta> > 0" and hballU: "ball p \<delta> \<subseteq> U"
    using hU_ball hpU by (by100 blast)
  have hp_open: "p \<in> open_segment a b"
    using hp hrel_eq by (by100 simp)
  obtain t where ht0: "0 < t" and ht1: "t < 1"
    and hp_eq: "p = (1 - t) *\<^sub>R a + t *\<^sub>R b"
    using hp_open unfolding in_segment by (by100 auto)
  have hnorm_pos: "0 < norm (b - a)"
    using hab by (by100 simp)
  define s where "s = min (min t (1 - t)) (\<delta> / norm (b - a)) / 2"
  have hs_pos: "0 < s"
    unfolding s_def using ht0 ht1 h\<delta>pos hnorm_pos by (by100 simp)
  have hs_t: "s < t"
    unfolding s_def using ht0 ht1 h\<delta>pos hnorm_pos by (by100 simp)
  have hs_1t: "s < 1 - t"
    unfolding s_def using ht0 ht1 h\<delta>pos hnorm_pos by (by100 simp)
  have hs_delta: "s * norm (b - a) < \<delta>"
  proof -
    have hs_le: "s \<le> (\<delta> / norm (b - a)) / 2"
      unfolding s_def by (by100 simp)
    have "s * norm (b - a) \<le> ((\<delta> / norm (b - a)) / 2) * norm (b - a)"
      by (rule mult_right_mono[OF hs_le]) (use hnorm_pos in \<open>by100 simp\<close>)
    also have "\<dots> = \<delta> / 2"
      using hnorm_pos by (by100 simp)
    also have "\<dots> < \<delta>"
      using h\<delta>pos by (by100 simp)
    finally show ?thesis .
  qed
  define x where "x = (1 - (t - s)) *\<^sub>R a + (t - s) *\<^sub>R b"
  define y where "y = (1 - (t + s)) *\<^sub>R a + (t + s) *\<^sub>R b"
  have htms0: "0 < t - s"
    using hs_t by (by100 simp)
  have htms1: "t - s < 1"
    using ht1 hs_pos by (by100 simp)
  have htps0: "0 < t + s"
    using ht0 hs_pos by (by100 simp)
  have htps1: "t + s < 1"
    using hs_1t by (by100 simp)
  have hxrel: "x \<in> rel_interior e"
    unfolding hrel_eq x_def using hab htms0 htms1 in_segment(2) by (by100 blast)
  have hyrel: "y \<in> rel_interior e"
    unfolding hrel_eq y_def using hab htps0 htps1 in_segment(2) by (by100 blast)
  have hxp: "x = p - s *\<^sub>R (b - a)"
    unfolding x_def hp_eq by (simp add: algebra_simps)
  have hyp: "y = p + s *\<^sub>R (b - a)"
    unfolding y_def hp_eq by (simp add: algebra_simps)
  have hx_ball: "x \<in> ball p \<delta>"
  proof -
    have "dist p x = s * norm (b - a)"
      unfolding hxp dist_norm using hs_pos by (by100 simp)
    thus ?thesis
      using hs_delta by (by100 simp)
  qed
  have hy_ball: "y \<in> ball p \<delta>"
  proof -
    have "dist p y = s * norm (b - a)"
      unfolding hyp dist_norm using hs_pos by (by100 simp)
    thus ?thesis
      using hs_delta by (by100 simp)
  qed
  have hxU: "x \<in> U"
    using hballU hx_ball by (by100 blast)
  have hyU: "y \<in> U"
    using hballU hy_ball by (by100 blast)
  have hxN: "x \<in> N"
    using hN_eq hxrel hxU by (by100 blast)
  have hyN: "y \<in> N"
    using hN_eq hyrel hyU by (by100 blast)
  let ?d = "b - a"
  have hd_pos: "0 < inner ?d ?d"
    using hab by (by100 simp)
  have hxlt: "inner ?d x < inner ?d p"
  proof -
    have "inner ?d p - inner ?d x = s * inner ?d ?d"
      unfolding hxp by (simp add: algebra_simps inner_diff_right)
    moreover have "0 < s * inner ?d ?d"
      using hs_pos hd_pos by (by100 simp)
    ultimately show ?thesis by (by100 linarith)
  qed
  have hygt: "inner ?d p < inner ?d y"
  proof -
    have "inner ?d y - inner ?d p = s * inner ?d ?d"
      unfolding hyp by (simp add: algebra_simps)
    moreover have "0 < s * inner ?d ?d"
      using hs_pos hd_pos by (by100 simp)
    ultimately show ?thesis by (by100 linarith)
  qed
  have hx_ne: "x \<noteq> p"
    using hxlt by (by100 blast)
  have hy_ne: "y \<noteq> p"
    using hygt by (by100 blast)
  have hxNp: "x \<in> N - {p}"
    using hxN hx_ne by (by100 blast)
  have hyNp: "y \<in> N - {p}"
    using hyN hy_ne by (by100 blast)
  have hsplit:
    "\<forall>z\<in>rel_interior e. z \<noteq> p \<longrightarrow>
          inner ?d z < inner ?d p \<or> inner ?d p < inner ?d z"
  proof
    fix z assume hzrel: "z \<in> rel_interior e"
    show "z \<noteq> p \<longrightarrow> inner ?d z < inner ?d p \<or> inner ?d p < inner ?d z"
    proof
      assume hz_ne: "z \<noteq> p"
      have hzseg: "z \<in> closed_segment a b"
        using hzrel hrel_eq open_closed_segment by (by100 blast)
      have hpseg: "p \<in> closed_segment a b"
        using hp hrel_eq open_closed_segment by (by100 blast)
      have hinj: "inj_on (\<lambda>w. inner ?d w) (closed_segment a b)"
        by (rule geotop_inner_diff_inj_on_closed_segment[OF hab])
      have hneq: "inner ?d z \<noteq> inner ?d p"
        using hinj hzseg hpseg hz_ne unfolding inj_on_def by (by100 blast)
      show "inner ?d z < inner ?d p \<or> inner ?d p < inner ?d z"
        using hneq by (by100 linarith)
    qed
  qed
  show ?thesis
    by (rule that[OF hab he_seg hxNp hyNp hxlt hygt hsplit])
qed

lemma geotop_edge_rel_interior_punctured_open_neighborhood_disconnected:
  fixes e N :: "(real^2) set" and p :: "real^2"
  assumes hedge: "geotop_is_edge e"
  assumes hp: "p \<in> rel_interior e"
  assumes hNopen: "N \<in> subspace_topology UNIV geotop_euclidean_topology (rel_interior e)"
  assumes hpN: "p \<in> N"
  assumes hNsub: "N \<subseteq> rel_interior e"
  shows "\<not> top1_connected_on (N - {p})
    (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
proof -
  obtain a b x y where hab: "a \<noteq> b" and he_seg: "e = closed_segment a b"
    and hx: "x \<in> N - {p}" and hy: "y \<in> N - {p}"
    and hxlt: "inner (b - a) x < inner (b - a) p"
    and hygt: "inner (b - a) p < inner (b - a) y"
    and hsplit: "\<forall>z\<in>rel_interior e. z \<noteq> p \<longrightarrow>
          inner (b - a) z < inner (b - a) p \<or>
          inner (b - a) p < inner (b - a) z"
    by (rule geotop_edge_rel_interior_open_neighborhood_two_sides
        [OF hedge hp hNopen hpN])
  let ?d = "b - a"
  let ?c = "inner ?d p"
  define A where "A = {z \<in> N - {p}. inner ?d z < ?c}"
  define B where "B = {z \<in> N - {p}. ?c < inner ?d z}"
  have hlt_top: "{z::real^2. inner ?d z < ?c} \<in> geotop_euclidean_topology"
    using open_halfspace_lt[of ?d ?c]
    unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hgt_top: "{z::real^2. ?c < inner ?d z} \<in> geotop_euclidean_topology"
    using open_halfspace_gt[of ?c ?d]
    unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hAopen: "A \<in> subspace_topology UNIV geotop_euclidean_topology (N - {p})"
  proof -
    have hAeq: "A = (N - {p}) \<inter> {z::real^2. inner ?d z < ?c}"
      unfolding A_def by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hlt_top hAeq by (by100 blast)
  qed
  have hBopen: "B \<in> subspace_topology UNIV geotop_euclidean_topology (N - {p})"
  proof -
    have hBeq: "B = (N - {p}) \<inter> {z::real^2. ?c < inner ?d z}"
      unfolding B_def by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hgt_top hBeq by (by100 blast)
  qed
  have hAne: "A \<noteq> {}"
    using hx hxlt unfolding A_def by (by100 blast)
  have hBne: "B \<noteq> {}"
    using hy hygt unfolding B_def by (by100 blast)
  have hABdisj: "A \<inter> B = {}"
    unfolding A_def B_def by (by100 auto)
  have hABcover: "A \<union> B = N - {p}"
  proof
    show "A \<union> B \<subseteq> N - {p}"
      unfolding A_def B_def by (by100 blast)
  next
    show "N - {p} \<subseteq> A \<union> B"
    proof
      fix z assume hz: "z \<in> N - {p}"
      have hzN: "z \<in> N"
        using hz by (by100 simp)
      have hzrel: "z \<in> rel_interior e"
        using hNsub hzN by (by100 blast)
      have hzneq: "z \<noteq> p"
        using hz by (by100 simp)
      have "inner ?d z < ?c \<or> ?c < inner ?d z"
        using hsplit hzrel hzneq by (by100 blast)
      thus "z \<in> A \<union> B"
        using hz unfolding A_def B_def by (by100 blast)
    qed
  qed
  show ?thesis
    unfolding top1_connected_on_def
    using hAopen hBopen hAne hBne hABdisj hABcover by (by100 blast)
qed

lemma geotop_punctured_open_ball_connected:
  fixes p :: "real^2"
  assumes hr: "0 < r"
  shows "top1_connected_on (ball p r - {p})
      (subspace_topology UNIV geotop_euclidean_topology (ball p r - {p}))"
proof -
  have "connected (ball p r - {p})"
    using connected_punctured_ball[of p r] by (by100 simp)
  thus ?thesis
    using top1_connected_on_geotop_iff_connected[of "ball p r - {p}"]
    by (by100 simp)
qed

lemma geotop_plane_chart_open_subset_connected_punctured_neighborhood:
  fixes U A :: "(real^2) set" and p :: "real^2"
  assumes hhomeo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
  assumes hAopen: "A \<in> subspace_topology UNIV geotop_euclidean_topology U"
  assumes hAsub: "A \<subseteq> U"
  assumes hpA: "p \<in> A"
  shows "\<exists>N. p \<in> N \<and> N \<subseteq> A
      \<and> N \<in> subspace_topology UNIV geotop_euclidean_topology A
      \<and> top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
proof -
  let ?q = "f p"
  have hbij: "bij_betw f U (UNIV::(real^2) set)"
    by (rule top1_homeomorphism_on_imp_bij[OF hhomeo])
  have hinj: "inj_on f U"
    using hbij by (rule bij_betw_imp_inj_on)
  have hpU: "p \<in> U"
    using hpA hAsub by (by100 blast)
  have hfpA: "?q \<in> f ` A"
    using hpA by (by100 blast)
  have himg_open_top: "f ` A \<in> geotop_euclidean_topology"
    by (rule homeomorphism_image_open[OF hhomeo hAopen hAsub])
  have himg_open: "open (f ` A)"
    using himg_open_top
    unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  obtain r where hr: "0 < r" and hball_sub: "ball ?q r \<subseteq> f ` A"
    using himg_open hfpA unfolding open_contains_ball by (by100 blast)
  define N where "N = {x \<in> U. f x \<in> ball ?q r}"
  have hball_top: "ball ?q r \<in> geotop_euclidean_topology"
    using open_ball
    unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hcont_f: "top1_continuous_map_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
    by (rule top1_homeomorphism_on_imp_cont1[OF hhomeo])
  have hNopenU: "N \<in> subspace_topology UNIV geotop_euclidean_topology U"
    unfolding N_def
    by (rule continuous_map_preimage_open[OF hcont_f hball_top])
  have hNsubA: "N \<subseteq> A"
  proof
    fix x assume hxN: "x \<in> N"
    have hxU: "x \<in> U"
      using hxN unfolding N_def by (by100 simp)
    have hfxball: "f x \<in> ball ?q r"
      using hxN unfolding N_def by (by100 simp)
    have hfximg: "f x \<in> f ` A"
      using hball_sub hfxball by (by100 blast)
    then obtain a where hfxa: "f x = f a" and haA: "a \<in> A"
      by (rule imageE)
    have hfa: "f a = f x"
      using hfxa by (by100 simp)
    have haU: "a \<in> U"
      using haA hAsub by (by100 blast)
    have "a = x"
      using inj_onD[OF hinj hfa haU hxU] .
    thus "x \<in> A"
      using haA by (by100 simp)
  qed
  have hpN: "p \<in> N"
    unfolding N_def using hpU hr by (by100 simp)
  have hNopenA: "N \<in> subspace_topology UNIV geotop_euclidean_topology A"
  proof -
    obtain Oset where hOtop: "Oset \<in> geotop_euclidean_topology" and hNeq: "N = U \<inter> Oset"
      using hNopenU unfolding subspace_topology_def by (by100 blast)
    have hNeqA: "N = A \<inter> Oset"
    proof
      show "N \<subseteq> A \<inter> Oset"
        using hNsubA hNeq by (by100 blast)
    next
      show "A \<inter> Oset \<subseteq> N"
        using hAsub hNeq by (by100 blast)
    qed
    show ?thesis
      unfolding subspace_topology_def using hOtop hNeqA by (by100 blast)
  qed
  let ?W = "ball ?q r - {?q}"
  have hWconn: "top1_connected_on ?W
      (subspace_topology UNIV geotop_euclidean_topology ?W)"
    by (rule geotop_punctured_open_ball_connected[OF hr])
  have hcont_inv: "top1_continuous_map_on (UNIV::(real^2) set) geotop_euclidean_topology
      U (subspace_topology UNIV geotop_euclidean_topology U) (inv_into U f)"
    by (rule top1_homeomorphism_on_imp_cont2[OF hhomeo])
  have himage_eq: "(inv_into U f) ` ?W = N - {p}"
  proof
    show "(inv_into U f) ` ?W \<subseteq> N - {p}"
    proof
      fix y assume hy: "y \<in> (inv_into U f) ` ?W"
      then obtain z where hzW: "z \<in> ?W" and hyz: "y = inv_into U f z"
        by (by100 blast)
      have hzball: "z \<in> ball ?q r"
        using hzW by (by100 simp)
      have hzneq: "z \<noteq> ?q"
        using hzW by (by100 simp)
      have hzimg: "z \<in> f ` A"
        using hball_sub hzball by (by100 blast)
      then obtain a where haA: "a \<in> A" and hfaz: "f a = z"
        by (by100 blast)
      have haU: "a \<in> U"
        using haA hAsub by (by100 blast)
      have hy_a: "y = a"
        using hyz inv_into_f_eq[OF hinj haU hfaz] by (by100 simp)
      have hyN: "y \<in> N"
        unfolding N_def using hy_a haU hfaz hzball by (by100 simp)
      have "y \<noteq> p"
        using hy_a hfaz hzneq by (by100 blast)
      thus "y \<in> N - {p}"
        using hyN by (by100 simp)
    qed
  next
    show "N - {p} \<subseteq> (inv_into U f) ` ?W"
    proof
      fix y assume hy: "y \<in> N - {p}"
      have hyN: "y \<in> N"
        using hy by (by100 simp)
      have hyU: "y \<in> U"
        using hyN unfolding N_def by (by100 simp)
      have hfyball: "f y \<in> ball ?q r"
        using hyN unfolding N_def by (by100 simp)
      have hyneq: "y \<noteq> p"
        using hy by (by100 simp)
      have hfyneq: "f y \<noteq> ?q"
      proof
        assume hEq: "f y = ?q"
        have "y = p"
          using inj_onD[OF hinj hEq hyU hpU] .
        thus False
          using hyneq by (by100 simp)
      qed
      have hfyW: "f y \<in> ?W"
        using hfyball hfyneq by (by100 simp)
      have hinv_y0: "inv_into U f (f y) = y"
        using bij_betw_inv_into_left[OF hbij hyU] .
      have hinv_y: "y = inv_into U f (f y)"
        using hinv_y0 by (by100 simp)
      thus "y \<in> (inv_into U f) ` ?W"
        using image_eqI[of y "inv_into U f" "f y" ?W] hfyW by (by100 blast)
    qed
  qed
  have htop_UNIV: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
    unfolding geotop_euclidean_topology_eq_open_sets
    by (rule top1_open_sets_is_topology_on_UNIV)
  have htop_U: "is_topology_on U (subspace_topology UNIV geotop_euclidean_topology U)"
    by (rule subspace_topology_is_topology_on[OF htop_UNIV subset_UNIV])
  have hconn_U: "top1_connected_on (N - {p})
      (subspace_topology U (subspace_topology UNIV geotop_euclidean_topology U) (N - {p}))"
    by (rule Theorem_GT_1_8[OF htop_UNIV htop_U hcont_inv subset_UNIV himage_eq hWconn])
  have hNminus_subU: "N - {p} \<subseteq> U"
    unfolding N_def by (by100 blast)
  have hsub_eq: "subspace_topology U
        (subspace_topology UNIV geotop_euclidean_topology U) (N - {p}) =
      subspace_topology UNIV geotop_euclidean_topology (N - {p})"
    by (rule subspace_topology_trans[OF hNminus_subU])
  have hconn: "top1_connected_on (N - {p})
      (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
    using hconn_U hsub_eq by (by100 simp)
  show ?thesis
    using hpN hNsubA hNopenA hconn by (by100 blast)
qed

lemma geotop_plane_chart_arc_complement_connected:
  fixes U A :: "(real^2) set"
  assumes hhomeo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
  assumes hAsub: "A \<subseteq> U"
  assumes hAimg: "geotop_is_arc (f ` A)
      (subspace_topology UNIV geotop_euclidean_topology (f ` A))"
  shows "top1_connected_on (U - A)
      (subspace_topology UNIV geotop_euclidean_topology (U - A))"
proof -
  let ?B = "f ` A"
  have hconn_img: "top1_connected_on (UNIV - ?B)
      (subspace_topology UNIV geotop_euclidean_topology (UNIV - ?B))"
    by (rule Theorem_GT_4_5[OF hAimg])
  have hbij: "bij_betw f U (UNIV::(real^2) set)"
    by (rule top1_homeomorphism_on_imp_bij[OF hhomeo])
  have hinj: "inj_on f U"
    using hbij by (rule bij_betw_imp_inj_on)
  have hcont_inv: "top1_continuous_map_on (UNIV::(real^2) set) geotop_euclidean_topology
      U (subspace_topology UNIV geotop_euclidean_topology U) (inv_into U f)"
    by (rule top1_homeomorphism_on_imp_cont2[OF hhomeo])
  have himage_eq: "(inv_into U f) ` (UNIV - ?B) = U - A"
  proof
    show "(inv_into U f) ` (UNIV - ?B) \<subseteq> U - A"
    proof
      fix y assume hy: "y \<in> (inv_into U f) ` (UNIV - ?B)"
      then obtain z where hz: "z \<in> UNIV - ?B" and hyz: "y = inv_into U f z"
        by (by100 blast)
      have hznot: "z \<notin> ?B"
        using hz by (by100 simp)
      have hfyz: "f y = z"
        using hyz bij_betw_inv_into_right[OF hbij, of z] by (by100 simp)
      have hzin: "z \<in> f ` U"
        using hbij unfolding bij_betw_def by (by100 simp)
      obtain u where huU: "u \<in> U" and hfuz: "f u = z"
        using hzin by (by100 blast)
      have hyU: "y \<in> U"
        using hyz huU hfuz inv_into_f_eq[OF hinj huU hfuz] by (by100 simp)
      have hyA: "y \<notin> A"
      proof
        assume "y \<in> A"
        hence "z \<in> ?B"
          using hfyz by (by100 blast)
        thus False
          using hznot by (by100 blast)
      qed
      show "y \<in> U - A"
        using hyU hyA by (by100 simp)
    qed
  next
    show "U - A \<subseteq> (inv_into U f) ` (UNIV - ?B)"
    proof
      fix y assume hy: "y \<in> U - A"
      have hyU: "y \<in> U"
        using hy by (by100 simp)
      have hyA: "y \<notin> A"
        using hy by (by100 simp)
      have hfynot: "f y \<notin> ?B"
      proof
        assume "f y \<in> ?B"
        then obtain a where haA: "a \<in> A" and hfya: "f y = f a"
          by (by100 blast)
        have haU: "a \<in> U"
          using haA hAsub by (by100 blast)
        have "y = a"
          using inj_onD[OF hinj hfya hyU haU] .
        thus False
          using hyA haA by (by100 simp)
      qed
      have hfy: "f y \<in> UNIV - ?B"
        using hfynot by (by100 simp)
      have hy_inv: "y = inv_into U f (f y)"
        using bij_betw_inv_into_left[OF hbij hyU] by (by100 simp)
      show "y \<in> (inv_into U f) ` (UNIV - ?B)"
        using image_eqI[of y "inv_into U f" "f y" "UNIV - ?B"] hfy hy_inv
        by (by100 blast)
    qed
  qed
  have htop_UNIV: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
    unfolding geotop_euclidean_topology_eq_open_sets
    by (rule top1_open_sets_is_topology_on_UNIV)
  have htop_U: "is_topology_on U (subspace_topology UNIV geotop_euclidean_topology U)"
    by (rule subspace_topology_is_topology_on[OF htop_UNIV subset_UNIV])
  have hconn_U: "top1_connected_on (U - A)
      (subspace_topology U (subspace_topology UNIV geotop_euclidean_topology U) (U - A))"
    by (rule Theorem_GT_1_8[OF htop_UNIV htop_U hcont_inv subset_UNIV himage_eq hconn_img])
  have hsub_eq: "subspace_topology U
        (subspace_topology UNIV geotop_euclidean_topology U) (U - A) =
      subspace_topology UNIV geotop_euclidean_topology (U - A)"
    by (rule subspace_topology_trans[OF Diff_subset])
  show ?thesis
    using hconn_U hsub_eq by (by100 simp)
qed

lemma geotop_plane_chart_1sphere_complement_not_connected:
  fixes U J :: "(real^2) set"
  assumes hhomeo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
  assumes hJsub: "J \<subseteq> U"
  assumes hJimg: "geotop_is_n_sphere (f ` J)
      (subspace_topology UNIV geotop_euclidean_topology (f ` J)) 1"
  shows "\<not> top1_connected_on (U - J)
      (subspace_topology UNIV geotop_euclidean_topology (U - J))"
proof
  let ?B = "f ` J"
  assume hconn: "top1_connected_on (U - J)
      (subspace_topology UNIV geotop_euclidean_topology (U - J))"
  have hnot_img: "\<not> top1_connected_on (UNIV - ?B)
      (subspace_topology UNIV geotop_euclidean_topology (UNIV - ?B))"
    by (rule Theorem_GT_4_3[OF hJimg])
  have hbij: "bij_betw f U (UNIV::(real^2) set)"
    by (rule top1_homeomorphism_on_imp_bij[OF hhomeo])
  have hinj: "inj_on f U"
    using hbij by (rule bij_betw_imp_inj_on)
  have hcont_f: "top1_continuous_map_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
    by (rule top1_homeomorphism_on_imp_cont1[OF hhomeo])
  have himage_eq: "f ` (U - J) = UNIV - ?B"
  proof
    show "f ` (U - J) \<subseteq> UNIV - ?B"
    proof
      fix y assume hy: "y \<in> f ` (U - J)"
      then obtain x where hx: "x \<in> U - J" and hyx: "y = f x"
        by (by100 blast)
      have hxU: "x \<in> U"
        using hx by (by100 simp)
      have hxJ: "x \<notin> J"
        using hx by (by100 simp)
      have hy_not_B: "y \<notin> ?B"
      proof
        assume "y \<in> ?B"
        then obtain z where hzJ: "z \<in> J" and hyz: "y = f z"
          by (by100 blast)
        have hzU: "z \<in> U"
          using hzJ hJsub by (by100 blast)
        have "x = z"
          using inj_onD[OF hinj] hxU hzU hyx hyz by (by100 blast)
        thus False
          using hxJ hzJ by (by100 simp)
      qed
      show "y \<in> UNIV - ?B"
        using hy_not_B by (by100 simp)
    qed
  next
    show "UNIV - ?B \<subseteq> f ` (U - J)"
    proof
      fix y assume hy: "y \<in> UNIV - ?B"
      have hy_not_B: "y \<notin> ?B"
        using hy by (by100 simp)
      have hy_img_U: "y \<in> f ` U"
        using hbij unfolding bij_betw_def by (by100 simp)
      then obtain x where hxU: "x \<in> U" and hxy: "f x = y"
        by (by100 blast)
      have hx_not_J: "x \<notin> J"
      proof
        assume "x \<in> J"
        hence "y \<in> ?B"
          using hxy by (by100 blast)
        thus False
          using hy_not_B by (by100 blast)
      qed
      have hxUJ: "x \<in> U - J"
        using hxU hx_not_J by (by100 simp)
      show "y \<in> f ` (U - J)"
        using hxUJ hxy by (by100 blast)
    qed
  qed
  have htop_UNIV: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
    unfolding geotop_euclidean_topology_eq_open_sets
    by (rule top1_open_sets_is_topology_on_UNIV)
  have htop_U: "is_topology_on U (subspace_topology UNIV geotop_euclidean_topology U)"
    by (rule subspace_topology_is_topology_on[OF htop_UNIV subset_UNIV])
  have hsub_eq: "subspace_topology U
        (subspace_topology UNIV geotop_euclidean_topology U) (U - J) =
      subspace_topology UNIV geotop_euclidean_topology (U - J)"
    by (rule subspace_topology_trans[OF Diff_subset])
  have hconn_U: "top1_connected_on (U - J)
      (subspace_topology U (subspace_topology UNIV geotop_euclidean_topology U) (U - J))"
    using hconn hsub_eq by (by100 simp)
  have hconn_img: "top1_connected_on (UNIV - ?B)
      (subspace_topology UNIV geotop_euclidean_topology (UNIV - ?B))"
    by (rule Theorem_GT_1_8[OF htop_U htop_UNIV hcont_f Diff_subset himage_eq hconn_U])
  show False
    using hconn_img hnot_img by (by100 blast)
qed

lemma geotop_subspace_open_trans:
  fixes A B N :: "(real^2) set"
  assumes hA: "A \<in> subspace_topology UNIV geotop_euclidean_topology B"
  assumes hN: "N \<in> subspace_topology UNIV geotop_euclidean_topology A"
  shows "N \<in> subspace_topology UNIV geotop_euclidean_topology B"
proof -
  obtain U where hU: "U \<in> geotop_euclidean_topology" and hAeq: "A = B \<inter> U"
    using hA unfolding subspace_topology_def by (by100 blast)
  obtain V where hV: "V \<in> geotop_euclidean_topology" and hNeq: "N = A \<inter> V"
    using hN unfolding subspace_topology_def by (by100 blast)
  have hUopen: "open U"
    using hU unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hVopen: "open V"
    using hV unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hUV: "U \<inter> V \<in> geotop_euclidean_topology"
    using open_Int[OF hUopen hVopen]
    unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have "N = B \<inter> (U \<inter> V)"
    using hAeq hNeq by (by100 blast)
  thus ?thesis
    using hUV unfolding subspace_topology_def by (by100 blast)
qed

lemma top1_norm_metric_on_UNIV_R2_dev34:
  "top1_metric_on (UNIV::(real^2) set) (\<lambda>x y. norm (x - y))"
  unfolding top1_metric_on_def
  by (auto simp: dist_norm [symmetric] dist_commute intro: dist_triangle)

lemma top1_norm_metric_topology_on_eq_geotop_subspace_R2_dev34:
  fixes M :: "(real^2) set"
  shows "top1_metric_topology_on M (\<lambda>x y. norm (x - y)) =
         subspace_topology UNIV geotop_euclidean_topology M"
proof -
  have hsub:
    "subspace_topology UNIV
        (top1_metric_topology_on UNIV (\<lambda>x y. norm (x - y))) M =
     top1_metric_topology_on M (\<lambda>x y. norm (x - y))"
    by (rule subspace_metric_topology_eq_metric_topology[
        OF top1_norm_metric_on_UNIV_R2_dev34 subset_UNIV])
  show ?thesis
    using hsub unfolding geotop_euclidean_topology_def by (by100 simp)
qed

lemma geotop_2_manifold_open_edge_rel_interior_connected_punctured_neighborhood:
  fixes M e :: "(real^2) set" and p :: "real^2"
  assumes hM: "geotop_n_manifold_on M (\<lambda>x y. norm (x - y)) 2"
  assumes hedge: "geotop_is_edge e"
  assumes hopen: "rel_interior e \<in> subspace_topology UNIV geotop_euclidean_topology M"
  assumes hsub: "rel_interior e \<subseteq> M"
  assumes hp: "p \<in> rel_interior e"
  shows "\<exists>N. p \<in> N \<and> N \<subseteq> rel_interior e
      \<and> N \<in> subspace_topology UNIV geotop_euclidean_topology (rel_interior e)
      \<and> top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
proof -
  let ?d = "\<lambda>x y. norm (x - y)"
  let ?TM = "top1_metric_topology_on M ?d"
  let ?GM = "subspace_topology UNIV geotop_euclidean_topology M"
  have hpM: "p \<in> M"
    using hp hsub by (by100 blast)
  obtain U f where hUopen: "openin_on M ?TM U" and hpU: "p \<in> U"
      and hhomeo: "top1_homeomorphism_on U (subspace_topology M ?TM U)
          (UNIV::(real^2) set) geotop_euclidean_topology f"
    using hM hpM unfolding geotop_n_manifold_on_def by (by100 blast)
  have hUsubM: "U \<subseteq> M"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hUmemTM: "U \<in> ?TM"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hTM_eq: "?TM = ?GM"
    by (rule top1_norm_metric_topology_on_eq_geotop_subspace_R2_dev34)
  have hUmemG: "U \<in> ?GM"
    using hUmemTM hTM_eq by (by100 simp)
  have hsource_eq: "subspace_topology M ?TM U =
      subspace_topology UNIV geotop_euclidean_topology U"
  proof -
    have htrans: "subspace_topology M ?GM U =
        subspace_topology UNIV geotop_euclidean_topology U"
      by (rule subspace_topology_trans[OF hUsubM])
    show ?thesis
      using hTM_eq htrans by (by100 simp)
  qed
  have hhomeo_geo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
    using hhomeo hsource_eq by (by100 simp)
  define A where "A = U \<inter> rel_interior e"
  have hpA: "p \<in> A"
    unfolding A_def using hp hpU by (by100 blast)
  have hAsubU: "A \<subseteq> U"
    unfolding A_def by (by100 blast)
  have hAopenU: "A \<in> subspace_topology UNIV geotop_euclidean_topology U"
  proof -
    obtain W where hWtop: "W \<in> geotop_euclidean_topology"
        and hrel_eq: "rel_interior e = M \<inter> W"
      using hopen unfolding subspace_topology_def by (by100 blast)
    have hAeq: "A = U \<inter> W"
      unfolding A_def using hUsubM hrel_eq by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hWtop hAeq by (by100 blast)
  qed
  have hAopenRel: "A \<in> subspace_topology UNIV geotop_euclidean_topology (rel_interior e)"
  proof -
    obtain V where hVtop: "V \<in> geotop_euclidean_topology" and hUeq: "U = M \<inter> V"
      using hUmemG unfolding subspace_topology_def by (by100 blast)
    have hAeq: "A = rel_interior e \<inter> V"
      unfolding A_def using hsub hUeq by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hVtop hAeq by (by100 blast)
  qed
  obtain N where hpN: "p \<in> N" and hNsubA: "N \<subseteq> A"
      and hNopenA: "N \<in> subspace_topology UNIV geotop_euclidean_topology A"
      and hNconn: "top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
    using geotop_plane_chart_open_subset_connected_punctured_neighborhood
      [OF hhomeo_geo hAopenU hAsubU hpA]
    by (by100 blast)
  have hNsubRel: "N \<subseteq> rel_interior e"
    using hNsubA unfolding A_def by (by100 blast)
  have hNopenRel: "N \<in> subspace_topology UNIV geotop_euclidean_topology (rel_interior e)"
    by (rule geotop_subspace_open_trans[OF hAopenRel hNopenA])
  show ?thesis
    using hpN hNsubRel hNopenRel hNconn by (by100 blast)
qed

lemma geotop_2_manifold_no_open_edge_rel_interior:
  fixes M e :: "(real^2) set"
  assumes hM: "geotop_n_manifold_on M (\<lambda>x y. norm (x - y)) 2"
  assumes hedge: "geotop_is_edge e"
  assumes hopen: "rel_interior e \<in> subspace_topology UNIV geotop_euclidean_topology M"
  assumes hsub: "rel_interior e \<subseteq> M"
  shows False
proof -
  obtain p where hp: "p \<in> rel_interior e"
    using geotop_edge_rel_interior_nonempty[OF hedge] by (by100 blast)
  obtain N where hpN: "p \<in> N" and hNsub: "N \<subseteq> rel_interior e"
      and hNopen: "N \<in> subspace_topology UNIV geotop_euclidean_topology (rel_interior e)"
      and hNconn: "top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
    using geotop_2_manifold_open_edge_rel_interior_connected_punctured_neighborhood
      [OF hM hedge hopen hsub hp]
    by (by100 blast)
  have hNnotconn: "\<not> top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
    by (rule geotop_edge_rel_interior_punctured_open_neighborhood_disconnected
        [OF hedge hp hNopen hpN hNsub])
  show False
    using hNconn hNnotconn by (by100 blast)
qed

lemma geotop_punctured_plane_connected:
  fixes p :: "real^2"
  shows "top1_connected_on (UNIV - {p})
    (subspace_topology UNIV geotop_euclidean_topology (UNIV - {p}))"
proof -
  have hconn_compl: "connected (- {p})"
    by (rule connected_punctured_universe) (by100 simp)
  have hpunct_eq: "UNIV - {p} = - {p}"
    by (by100 blast)
  have hconn: "connected (UNIV - {p})"
    using hconn_compl hpunct_eq by (by100 simp)
  show ?thesis
    using hconn top1_connected_on_geotop_iff_connected[of "UNIV - {p}"]
    by (by100 simp)
qed

lemma geotop_plane_chart_point_complement_connected:
  fixes U :: "(real^2) set" and p :: "real^2"
  assumes hhomeo: "top1_homeomorphism_on U
      (subspace_topology UNIV geotop_euclidean_topology U)
      (UNIV::(real^2) set) geotop_euclidean_topology f"
  assumes hpU: "p \<in> U"
  shows "top1_connected_on (U - {p})
      (subspace_topology UNIV geotop_euclidean_topology (U - {p}))"
proof -
  let ?q = "f p"
  have hconn_img: "top1_connected_on (UNIV - {?q})
      (subspace_topology UNIV geotop_euclidean_topology (UNIV - {?q}))"
    by (rule geotop_punctured_plane_connected)
  have hbij: "bij_betw f U (UNIV::(real^2) set)"
    by (rule top1_homeomorphism_on_imp_bij[OF hhomeo])
  have hinj: "inj_on f U"
    using hbij by (rule bij_betw_imp_inj_on)
  have hcont_inv: "top1_continuous_map_on (UNIV::(real^2) set) geotop_euclidean_topology
      U (subspace_topology UNIV geotop_euclidean_topology U) (inv_into U f)"
    by (rule top1_homeomorphism_on_imp_cont2[OF hhomeo])
  have himage_eq: "(inv_into U f) ` (UNIV - {?q}) = U - {p}"
  proof
    show "(inv_into U f) ` (UNIV - {?q}) \<subseteq> U - {p}"
    proof
      fix y assume hy: "y \<in> (inv_into U f) ` (UNIV - {?q})"
      then obtain z where hz: "z \<in> UNIV - {?q}" and hyz: "y = inv_into U f z"
        by (by100 blast)
      have hzneq: "z \<noteq> ?q"
        using hz by (by100 simp)
      have hz_img_U: "z \<in> f ` U"
        using hbij unfolding bij_betw_def by (by100 simp)
      then obtain u where huU: "u \<in> U" and hfuz: "f u = z"
        by (by100 blast)
      have hy_u: "y = u"
        using hyz inv_into_f_eq[OF hinj huU hfuz] by (by100 simp)
      have hyU: "y \<in> U"
        using hy_u huU by (by100 simp)
      have hyp: "y \<noteq> p"
      proof
        assume "y = p"
        hence "z = ?q"
          using hy_u hfuz by (by100 simp)
        thus False
          using hzneq by (by100 blast)
      qed
      show "y \<in> U - {p}"
        using hyU hyp by (by100 simp)
    qed
  next
    show "U - {p} \<subseteq> (inv_into U f) ` (UNIV - {?q})"
    proof
      fix y assume hy: "y \<in> U - {p}"
      have hyU: "y \<in> U"
        using hy by (by100 simp)
      have hyp: "y \<noteq> p"
        using hy by (by100 simp)
      have hfyneq: "f y \<noteq> ?q"
      proof
        assume hEq: "f y = ?q"
        have "y = p"
          using inj_onD[OF hinj hEq hyU hpU] .
        thus False
          using hyp by (by100 simp)
      qed
      have hfy: "f y \<in> UNIV - {?q}"
        using hfyneq by (by100 simp)
      have hy_inv: "y = inv_into U f (f y)"
        using bij_betw_inv_into_left[OF hbij hyU] by (by100 simp)
      show "y \<in> (inv_into U f) ` (UNIV - {?q})"
        using image_eqI[of y "inv_into U f" "f y" "UNIV - {?q}"] hfy hy_inv
        by (by100 blast)
    qed
  qed
  have htop_UNIV: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
    unfolding geotop_euclidean_topology_eq_open_sets
    by (rule top1_open_sets_is_topology_on_UNIV)
  have htop_U: "is_topology_on U (subspace_topology UNIV geotop_euclidean_topology U)"
    by (rule subspace_topology_is_topology_on[OF htop_UNIV subset_UNIV])
  have hconn_U: "top1_connected_on (U - {p})
      (subspace_topology U (subspace_topology UNIV geotop_euclidean_topology U) (U - {p}))"
    by (rule Theorem_GT_1_8[OF htop_UNIV htop_U hcont_inv subset_UNIV himage_eq hconn_img])
  have hsub_eq: "subspace_topology U
        (subspace_topology UNIV geotop_euclidean_topology U) (U - {p}) =
      subspace_topology UNIV geotop_euclidean_topology (U - {p})"
    by (rule subspace_topology_trans[OF Diff_subset])
  show ?thesis
    using hconn_U hsub_eq by (by100 simp)
qed

lemma geotop_2_simplex_ball_inter_aff_dim:
  fixes \<sigma> :: "(real^2) set" and p :: "real^2"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hp: "p \<in> \<sigma>"
  assumes hr: "0 < r"
  shows "aff_dim (\<sigma> \<inter> ball p r) = 2"
proof -
  have hsimplex: "geotop_is_simplex \<sigma>"
    by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>])
  have hconv: "convex \<sigma>"
    by (rule GeoTopBase0.geotop_simplex_is_convex[OF hsimplex])
  have hhyper: "geotop_hyperplane_dim (affine hull \<sigma>) 2"
    by (rule geotop_simplex_dim_imp_hyperplane_dim[OF h\<sigma>])
  have hdim\<sigma>: "aff_dim \<sigma> = 2"
    using geotop_hyperplane_dim_imp_affine_aff_dim[OF hhyper] by (by100 simp)
  have hmeet: "\<sigma> \<inter> ball p r \<noteq> {}"
    using hp hr by (by100 force)
  have "aff_dim (\<sigma> \<inter> ball p r) = aff_dim \<sigma>"
    by (rule aff_dim_convex_Int_open[OF hconv open_ball hmeet])
  thus ?thesis
    using hdim\<sigma> by (by100 simp)
qed

lemma geotop_2_simplex_open_subset_connected_punctured_neighborhood:
  fixes \<sigma> A :: "(real^2) set" and p :: "real^2"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hAopen: "A \<in> subspace_topology UNIV geotop_euclidean_topology \<sigma>"
  assumes hAsub: "A \<subseteq> \<sigma>"
  assumes hpA: "p \<in> A"
  shows "\<exists>N. p \<in> N \<and> N \<subseteq> A
      \<and> N \<in> subspace_topology UNIV geotop_euclidean_topology A
      \<and> top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
proof -
  obtain W where hWtop: "W \<in> geotop_euclidean_topology"
      and hAeq: "A = \<sigma> \<inter> W"
    using hAopen unfolding subspace_topology_def by (by100 blast)
  have hWopen: "open W"
    using hWtop unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hp\<sigma>: "p \<in> \<sigma>"
    using hpA hAsub by (by100 blast)
  have hpW: "p \<in> W"
    using hpA hAeq by (by100 blast)
  have hWopenin: "openin (top_of_set UNIV) W"
    using hWopen by (by100 simp)
  obtain r where hr: "0 < r" and hball_sub_W: "ball p r \<subseteq> W"
    using hWopenin hpW unfolding openin_contains_ball by (by100 force)
  define N where "N = \<sigma> \<inter> ball p r"
  have hpN: "p \<in> N"
    unfolding N_def using hp\<sigma> hr by (by100 simp)
  have hNsubA: "N \<subseteq> A"
    unfolding N_def using hAeq hball_sub_W by (by100 blast)
  have hN_eq_A_ball: "N = A \<inter> ball p r"
    unfolding N_def using hAeq hball_sub_W by (by100 blast)
  have hballtop: "ball p r \<in> geotop_euclidean_topology"
    unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hNopenA: "N \<in> subspace_topology UNIV geotop_euclidean_topology A"
    unfolding subspace_topology_def using hballtop hN_eq_A_ball by (by100 blast)
  have hsimplex: "geotop_is_simplex \<sigma>"
    by (rule geotop_simplex_dim_imp_is_simplex[OF h\<sigma>])
  have hconv\<sigma>: "convex \<sigma>"
    by (rule GeoTopBase0.geotop_simplex_is_convex[OF hsimplex])
  have hconvN: "convex N"
    unfolding N_def by (rule convex_Int[OF hconv\<sigma> convex_ball])
  have hdimN: "aff_dim N = 2"
    unfolding N_def by (rule geotop_2_simplex_ball_inter_aff_dim[OF h\<sigma> hp\<sigma> hr])
  have hnot1: "aff_dim N \<noteq> 1"
    using hdimN by (by100 simp)
  have hconnHOL: "connected (N - {p})"
    by (rule connected_punctured_convex[OF hconvN hnot1])
  have hconn: "top1_connected_on (N - {p})
      (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
    using hconnHOL top1_connected_on_geotop_iff_connected[of "N - {p}"]
    by (by100 simp)
  show ?thesis
    using hpN hNsubA hNopenA hconn by (by100 blast)
qed

lemma geotop_2_cell_open_subset_connected_punctured_neighborhood:
  fixes C A :: "(real^2) set" and p :: "real^2"
  assumes hcell: "geotop_is_n_cell C
      (subspace_topology UNIV geotop_euclidean_topology C) 2"
  assumes hAopen: "A \<in> subspace_topology UNIV geotop_euclidean_topology C"
  assumes hAsub: "A \<subseteq> C"
  assumes hpA: "p \<in> A"
  shows "\<exists>N. p \<in> N \<and> N \<subseteq> A
      \<and> N \<in> subspace_topology UNIV geotop_euclidean_topology A
      \<and> top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
proof -
  obtain \<sigma> and f :: "real^2 \<Rightarrow> real^2"
    where h\<sigma>: "geotop_simplex_dim \<sigma> 2"
      and hhomeo: "top1_homeomorphism_on C
          (subspace_topology UNIV geotop_euclidean_topology C)
          \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) f"
    using geotop_is_n_cell_imp_homeo_ex[OF hcell] by (by100 blast)
  have hpC: "p \<in> C"
    using hpA hAsub by (by100 blast)
  have hbij: "bij_betw f C \<sigma>"
    by (rule top1_homeomorphism_on_imp_bij[OF hhomeo])
  have hinj: "inj_on f C"
    using hbij by (rule bij_betw_imp_inj_on)
  define B where "B = f ` A"
  have hBopen: "B \<in> subspace_topology UNIV geotop_euclidean_topology \<sigma>"
    unfolding B_def
    by (rule homeomorphism_image_open[OF hhomeo hAopen hAsub])
  have hBsub\<sigma>: "B \<subseteq> \<sigma>"
    using hbij hAsub unfolding B_def bij_betw_def by (by100 blast)
  have hfpB: "f p \<in> B"
    unfolding B_def using hpA by (by100 blast)
  obtain W where hfpW: "f p \<in> W" and hWsubB: "W \<subseteq> B"
      and hWopenB: "W \<in> subspace_topology UNIV geotop_euclidean_topology B"
      and hWconn: "top1_connected_on (W - {f p})
          (subspace_topology UNIV geotop_euclidean_topology (W - {f p}))"
    using geotop_2_simplex_open_subset_connected_punctured_neighborhood
      [OF h\<sigma> hBopen hBsub\<sigma> hfpB]
    by (by100 blast)
  have hWopen\<sigma>: "W \<in> subspace_topology UNIV geotop_euclidean_topology \<sigma>"
    by (rule geotop_subspace_open_trans[OF hBopen hWopenB])
  have hcont_f: "top1_continuous_map_on C
      (subspace_topology UNIV geotop_euclidean_topology C)
      \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) f"
    by (rule top1_homeomorphism_on_imp_cont1[OF hhomeo])
  define N where "N = {x \<in> A. f x \<in> W}"
  have hpreC: "{x \<in> C. f x \<in> W}
      \<in> subspace_topology UNIV geotop_euclidean_topology C"
    by (rule continuous_map_preimage_open[OF hcont_f hWopen\<sigma>])
  have hNopenA: "N \<in> subspace_topology UNIV geotop_euclidean_topology A"
  proof -
    obtain Oset where hOtop: "Oset \<in> geotop_euclidean_topology"
        and hpre_eq: "{x \<in> C. f x \<in> W} = C \<inter> Oset"
      using hpreC unfolding subspace_topology_def by (by100 blast)
    have hNeq: "N = A \<inter> Oset"
      unfolding N_def using hAsub hpre_eq by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hOtop hNeq by (by100 blast)
  qed
  have hpN: "p \<in> N"
    unfolding N_def using hpA hfpW by (by100 blast)
  have hNsubA: "N \<subseteq> A"
    unfolding N_def by (by100 blast)
  have hcont_inv: "top1_continuous_map_on \<sigma>
      (subspace_topology UNIV geotop_euclidean_topology \<sigma>)
      C (subspace_topology UNIV geotop_euclidean_topology C) (inv_into C f)"
    by (rule top1_homeomorphism_on_imp_cont2[OF hhomeo])
  have himage_eq: "(inv_into C f) ` (W - {f p}) = N - {p}"
  proof
    show "(inv_into C f) ` (W - {f p}) \<subseteq> N - {p}"
    proof
      fix y assume hy: "y \<in> (inv_into C f) ` (W - {f p})"
      then obtain z where hzW: "z \<in> W - {f p}" and hyz: "y = inv_into C f z"
        by (by100 blast)
      have hzW0: "z \<in> W"
        using hzW by (by100 simp)
      have hzneq: "z \<noteq> f p"
        using hzW by (by100 simp)
      have hzB: "z \<in> B"
        using hWsubB hzW0 by (by100 blast)
      then obtain a where hza: "z = f a" and haA: "a \<in> A"
        unfolding B_def by (rule imageE)
      have haC: "a \<in> C"
        using haA hAsub by (by100 blast)
      have hy_a: "y = a"
        using hyz hza bij_betw_inv_into_left[OF hbij haC] by (by100 simp)
      have hyN: "y \<in> N"
        unfolding N_def using hy_a haA hza hzW0 by (by100 simp)
      have "y \<noteq> p"
        using hy_a hza hzneq by (by100 blast)
      thus "y \<in> N - {p}"
        using hyN by (by100 simp)
    qed
  next
    show "N - {p} \<subseteq> (inv_into C f) ` (W - {f p})"
    proof
      fix y assume hy: "y \<in> N - {p}"
      have hyN: "y \<in> N"
        using hy by (by100 simp)
      have hyA: "y \<in> A"
        using hyN unfolding N_def by (by100 simp)
      have hyC: "y \<in> C"
        using hyA hAsub by (by100 blast)
      have hfyW: "f y \<in> W"
        using hyN unfolding N_def by (by100 simp)
      have hyneq: "y \<noteq> p"
        using hy by (by100 simp)
      have hfyneq: "f y \<noteq> f p"
      proof
        assume hEq: "f y = f p"
        have "y = p"
          using inj_onD[OF hinj hEq hyC hpC] .
        thus False
          using hyneq by (by100 simp)
      qed
      have hfyWdiff: "f y \<in> W - {f p}"
        using hfyW hfyneq by (by100 simp)
      have hinv_y0: "inv_into C f (f y) = y"
        using bij_betw_inv_into_left[OF hbij hyC] .
      have hinv_y: "y = inv_into C f (f y)"
        using hinv_y0 by (by100 simp)
      thus "y \<in> (inv_into C f) ` (W - {f p})"
        using image_eqI[of y "inv_into C f" "f y" "W - {f p}"] hfyWdiff
        by (by100 blast)
    qed
  qed
  have htop\<sigma>: "is_topology_on \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>)"
  proof -
    have htop_UNIV: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      unfolding geotop_euclidean_topology_eq_open_sets
      by (rule top1_open_sets_is_topology_on_UNIV)
    show ?thesis
      by (rule subspace_topology_is_topology_on[OF htop_UNIV subset_UNIV])
  qed
  have htopC: "is_topology_on C (subspace_topology UNIV geotop_euclidean_topology C)"
  proof -
    have htop_UNIV: "is_topology_on (UNIV::(real^2) set) geotop_euclidean_topology"
      unfolding geotop_euclidean_topology_eq_open_sets
      by (rule top1_open_sets_is_topology_on_UNIV)
    show ?thesis
      by (rule subspace_topology_is_topology_on[OF htop_UNIV subset_UNIV])
  qed
  have hWdiff_sub\<sigma>: "W - {f p} \<subseteq> \<sigma>"
    using hWsubB hBsub\<sigma> by (by100 blast)
  have hW_subspace_eq: "subspace_topology \<sigma>
        (subspace_topology UNIV geotop_euclidean_topology \<sigma>) (W - {f p}) =
      subspace_topology UNIV geotop_euclidean_topology (W - {f p})"
    by (rule subspace_topology_trans[OF hWdiff_sub\<sigma>])
  have hWconn\<sigma>: "top1_connected_on (W - {f p})
      (subspace_topology \<sigma> (subspace_topology UNIV geotop_euclidean_topology \<sigma>) (W - {f p}))"
    using hWconn hW_subspace_eq by (by100 simp)
  have hconnC: "top1_connected_on (N - {p})
      (subspace_topology C (subspace_topology UNIV geotop_euclidean_topology C) (N - {p}))"
    by (rule Theorem_GT_1_8[OF htop\<sigma> htopC hcont_inv hWdiff_sub\<sigma> himage_eq hWconn\<sigma>])
  have hNminus_subC: "N - {p} \<subseteq> C"
    using hNsubA hAsub by (by100 blast)
  have hsub_eq: "subspace_topology C
        (subspace_topology UNIV geotop_euclidean_topology C) (N - {p}) =
      subspace_topology UNIV geotop_euclidean_topology (N - {p})"
    by (rule subspace_topology_trans[OF hNminus_subC])
  have hconn: "top1_connected_on (N - {p})
      (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
    using hconnC hsub_eq by (by100 simp)
  show ?thesis
    using hpN hNsubA hNopenA hconn by (by100 blast)
qed

lemma geotop_2_manifold_with_boundary_open_edge_rel_interior_connected_punctured_neighborhood:
  fixes M e :: "(real^2) set" and p :: "real^2"
  assumes hM: "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes hedge: "geotop_is_edge e"
  assumes hopen: "rel_interior e \<in> subspace_topology UNIV geotop_euclidean_topology M"
  assumes hsub: "rel_interior e \<subseteq> M"
  assumes hp: "p \<in> rel_interior e"
  shows "\<exists>N. p \<in> N \<and> N \<subseteq> rel_interior e
      \<and> N \<in> subspace_topology UNIV geotop_euclidean_topology (rel_interior e)
      \<and> top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
proof -
  let ?d = "\<lambda>x y. norm (x - y)"
  let ?T = "top1_metric_topology_on M ?d"
  have hpM: "p \<in> M"
    using hp hsub by (by100 blast)
  have hmetric: "top1_metric_on M ?d"
    using hM unfolding geotop_n_manifold_with_boundary_on_def by (by100 blast)
  have htopT: "is_topology_on M ?T"
    by (rule top1_metric_topology_on_is_topology_on[OF hmetric])
  obtain U where hUopen: "openin_on M ?T U" and hpU: "p \<in> U"
      and hcell: "geotop_is_n_cell (closure_on M ?T U)
          (subspace_topology M ?T (closure_on M ?T U)) 2"
    using hM hpM unfolding geotop_n_manifold_with_boundary_on_def by (by100 blast)
  let ?C = "closure_on M ?T U"
  have hUsubM: "U \<subseteq> M"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hUmemT: "U \<in> ?T"
    using hUopen unfolding openin_on_def by (by100 blast)
  have hCsubM: "?C \<subseteq> M"
    by (rule closure_on_subset_carrier[OF htopT hUsubM])
  have hUsubC: "U \<subseteq> ?C"
    by (rule subset_closure_on)
  have hT_eq: "?T = subspace_topology UNIV geotop_euclidean_topology M"
    by (rule top1_norm_metric_topology_on_eq_geotop_subspace_R2_dev34)
  have hTC_eq: "subspace_topology M ?T ?C =
      subspace_topology UNIV geotop_euclidean_topology ?C"
  proof -
    have htrans: "subspace_topology M
        (subspace_topology UNIV geotop_euclidean_topology M) ?C =
        subspace_topology UNIV geotop_euclidean_topology ?C"
      by (rule subspace_topology_trans[OF hCsubM])
    show ?thesis
      using hT_eq htrans by (by100 simp)
  qed
  have hcell_geo: "geotop_is_n_cell ?C
      (subspace_topology UNIV geotop_euclidean_topology ?C) 2"
    using hcell hTC_eq by (by100 simp)
  have hUmemG: "U \<in> subspace_topology UNIV geotop_euclidean_topology M"
    using hUmemT hT_eq by (by100 simp)
  define A where "A = U \<inter> rel_interior e"
  have hpA: "p \<in> A"
    unfolding A_def using hp hpU by (by100 blast)
  have hAsubC: "A \<subseteq> ?C"
    unfolding A_def using hUsubC by (by100 blast)
  have hAsubRel: "A \<subseteq> rel_interior e"
    unfolding A_def by (by100 blast)
  have hAopenM: "A \<in> subspace_topology UNIV geotop_euclidean_topology M"
  proof -
    obtain V where hVtop: "V \<in> geotop_euclidean_topology" and hUeq: "U = M \<inter> V"
      using hUmemG unfolding subspace_topology_def by (by100 blast)
    obtain W where hWtop: "W \<in> geotop_euclidean_topology"
        and hrel_eq: "rel_interior e = M \<inter> W"
      using hopen unfolding subspace_topology_def by (by100 blast)
    have hVWtop: "V \<inter> W \<in> geotop_euclidean_topology"
    proof -
      have hVopen: "open V"
        using hVtop unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
        by (by100 simp)
      have hWopen: "open W"
        using hWtop unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
        by (by100 simp)
      show ?thesis
        using open_Int[OF hVopen hWopen]
        unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
        by (by100 simp)
    qed
    have hAeq: "A = M \<inter> (V \<inter> W)"
      unfolding A_def using hUeq hrel_eq by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hVWtop hAeq by (by100 blast)
  qed
  have hAopenC: "A \<in> subspace_topology UNIV geotop_euclidean_topology ?C"
  proof -
    obtain V where hVtop: "V \<in> geotop_euclidean_topology" and hAeqM: "A = M \<inter> V"
      using hAopenM unfolding subspace_topology_def by (by100 blast)
    have hAeqC: "A = ?C \<inter> V"
      using hAeqM hAsubC hCsubM by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hVtop hAeqC by (by100 blast)
  qed
  have hAopenRel: "A \<in> subspace_topology UNIV geotop_euclidean_topology (rel_interior e)"
  proof -
    obtain V where hVtop: "V \<in> geotop_euclidean_topology" and hUeq: "U = M \<inter> V"
      using hUmemG unfolding subspace_topology_def by (by100 blast)
    have hAeq: "A = rel_interior e \<inter> V"
      unfolding A_def using hsub hUeq by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def using hVtop hAeq by (by100 blast)
  qed
  obtain N where hpN: "p \<in> N" and hNsubA: "N \<subseteq> A"
      and hNopenA: "N \<in> subspace_topology UNIV geotop_euclidean_topology A"
      and hNconn: "top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
    using geotop_2_cell_open_subset_connected_punctured_neighborhood
      [OF hcell_geo hAopenC hAsubC hpA]
    by (by100 blast)
  have hNsubRel: "N \<subseteq> rel_interior e"
    using hNsubA hAsubRel by (by100 blast)
  have hNopenRel: "N \<in> subspace_topology UNIV geotop_euclidean_topology (rel_interior e)"
    by (rule geotop_subspace_open_trans[OF hAopenRel hNopenA])
  show ?thesis
    using hpN hNsubRel hNopenRel hNconn by (by100 blast)
qed

lemma geotop_2_manifold_with_boundary_no_open_edge_rel_interior:
  fixes M e :: "(real^2) set"
  assumes hM: "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes hedge: "geotop_is_edge e"
  assumes hopen: "rel_interior e \<in> subspace_topology UNIV geotop_euclidean_topology M"
  assumes hsub: "rel_interior e \<subseteq> M"
  shows False
proof -
  obtain p where hp: "p \<in> rel_interior e"
    using geotop_edge_rel_interior_nonempty[OF hedge] by (by100 blast)
  obtain N where hpN: "p \<in> N" and hNsub: "N \<subseteq> rel_interior e"
      and hNopen: "N \<in> subspace_topology UNIV geotop_euclidean_topology (rel_interior e)"
      and hNconn: "top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
    using geotop_2_manifold_with_boundary_open_edge_rel_interior_connected_punctured_neighborhood
      [OF hM hedge hopen hsub hp]
    by (by100 blast)
  have hNnotconn: "\<not> top1_connected_on (N - {p})
          (subspace_topology UNIV geotop_euclidean_topology (N - {p}))"
    by (rule geotop_edge_rel_interior_punctured_open_neighborhood_disconnected
        [OF hedge hp hNopen hpN hNsub])
  show False
    using hNconn hNnotconn by (by100 blast)
qed

lemma top1_norm_metric_on_UNIV_early:
  "top1_metric_on (UNIV::'a::real_normed_vector set) (\<lambda>x y. norm (x - y))"
  unfolding top1_metric_on_def
  by (auto simp: dist_norm [symmetric] dist_commute intro: dist_triangle)

lemma top1_norm_metric_topology_on_eq_geotop_subspace_early:
  fixes M :: "'a::real_normed_vector set"
  shows "top1_metric_topology_on M (\<lambda>x y. norm (x - y)) =
         subspace_topology UNIV geotop_euclidean_topology M"
proof -
  have hsub:
    "subspace_topology UNIV
        (top1_metric_topology_on UNIV (\<lambda>x y. norm (x - y))) M =
     top1_metric_topology_on M (\<lambda>x y. norm (x - y))"
    by (rule subspace_metric_topology_eq_metric_topology[
        OF top1_norm_metric_on_UNIV_early subset_UNIV])
  show ?thesis
    using hsub unfolding geotop_euclidean_topology_def by (by100 simp)
qed

lemma top1_homeomorphism_on_open_image:
  assumes hhomeo: "top1_homeomorphism_on X TX Y TY f"
  assumes hAopen: "A \<in> TX"
  assumes hAsub: "A \<subseteq> X"
  shows "f ` A \<in> TY"
proof -
  have hbij: "bij_betw f X Y"
    by (rule top1_homeomorphism_on_imp_bij[OF hhomeo])
  have hcont_inv: "top1_continuous_map_on Y TY X TX (inv_into X f)"
    by (rule top1_homeomorphism_on_imp_cont2[OF hhomeo])
  have hpre: "{y\<in>Y. inv_into X f y \<in> A} \<in> TY"
    by (rule continuous_map_preimage_open[OF hcont_inv hAopen])
  have hpre_eq: "{y\<in>Y. inv_into X f y \<in> A} = f ` A"
  proof
    show "{y \<in> Y. inv_into X f y \<in> A} \<subseteq> f ` A"
    proof
      fix y assume hy: "y \<in> {y \<in> Y. inv_into X f y \<in> A}"
      have hyY: "y \<in> Y"
        using hy by (by100 simp)
      have hinvA: "inv_into X f y \<in> A"
        using hy by (by100 simp)
      have "f (inv_into X f y) = y"
        by (rule bij_betw_inv_into_right[OF hbij hyY])
      hence hy_img_eq: "y = f (inv_into X f y)"
        by (by100 simp)
      thus "y \<in> f ` A"
        by (rule image_eqI[OF _ hinvA])
    qed
    show "f ` A \<subseteq> {y \<in> Y. inv_into X f y \<in> A}"
    proof
      fix y assume hy: "y \<in> f ` A"
      obtain x where hxA: "x \<in> A" and hy_eq: "y = f x"
        using hy by (by100 blast)
      have hxX: "x \<in> X"
        using hAsub hxA by (by100 blast)
      have hyY: "y \<in> Y"
        using hbij hxX hy_eq unfolding bij_betw_def by (by100 blast)
      have "inv_into X f y = x"
        unfolding hy_eq by (rule bij_betw_inv_into_left[OF hbij hxX])
      thus "y \<in> {y \<in> Y. inv_into X f y \<in> A}"
        using hyY hxA by (by100 simp)
    qed
  qed
  show ?thesis
    using hpre hpre_eq by (by100 simp)
qed

lemma geotop_2_manifold_no_open_singleton:
  fixes M :: "(real^2) set"
  assumes hM: "geotop_n_manifold_on M (\<lambda>x y. norm (x - y)) 2"
  assumes hvM: "v \<in> M"
  shows "{v} \<notin> subspace_topology UNIV geotop_euclidean_topology M"
proof
  let ?d = "(\<lambda>x y. norm (x - y))"
  let ?T = "top1_metric_topology_on M ?d"
  assume hs_geo: "{v} \<in> subspace_topology UNIV geotop_euclidean_topology M"
  have hT_eq: "?T = subspace_topology UNIV geotop_euclidean_topology M"
    by (rule top1_norm_metric_topology_on_eq_geotop_subspace_early)
  have hs_metric: "{v} \<in> ?T"
    using hs_geo hT_eq by (by100 simp)
  have hcharts:
    "\<forall>P\<in>M. \<exists>U. openin_on M ?T U \<and> P \<in> U \<and>
       (\<exists>f. top1_homeomorphism_on U (subspace_topology M ?T U)
             (UNIV::(real^2) set) geotop_euclidean_topology f)"
    using hM unfolding geotop_n_manifold_on_def by (by100 blast)
  obtain U f where hU_openin: "openin_on M ?T U"
    and hvU: "v \<in> U"
    and hhomeo: "top1_homeomorphism_on U (subspace_topology M ?T U)
             (UNIV::(real^2) set) geotop_euclidean_topology f"
    using hcharts hvM by (by100 blast)
  have hsingle_source: "{v} \<in> subspace_topology M ?T U"
  proof -
    have hUv: "U \<inter> {v} = {v}"
      using hvU by (by100 blast)
    show ?thesis
      unfolding subspace_topology_def
      using hs_metric hUv by (by100 blast)
  qed
  have hsingle_sub_U: "{v} \<subseteq> U"
    using hvU by (by100 blast)
  have h_image_open: "f ` {v} \<in> geotop_euclidean_topology"
    by (rule top1_homeomorphism_on_open_image[OF hhomeo hsingle_source hsingle_sub_U])
  have h_image_eq: "f ` {v} = {f v}"
    by (by100 simp)
  have hsingleton_top: "{f v} \<in> geotop_euclidean_topology"
    using h_image_open h_image_eq by (by100 simp)
  have hsingleton_open: "open {f v}"
    using hsingleton_top unfolding geotop_euclidean_topology_eq_open_sets
      top1_open_sets_def by (by100 simp)
  show False
    using not_open_singleton[of "f v"] hsingleton_open by (by100 blast)
qed

lemma geotop_2_simplex_no_open_singleton:
  fixes \<sigma> :: "(real^2) set"
  assumes h\<sigma>: "geotop_simplex_dim \<sigma> 2"
  assumes hp: "p \<in> \<sigma>"
  shows "{p} \<notin> subspace_topology UNIV geotop_euclidean_topology \<sigma>"
proof
  assume hsopen_top: "{p} \<in> subspace_topology UNIV geotop_euclidean_topology \<sigma>"
  obtain U where hUtop: "U \<in> geotop_euclidean_topology"
    and hpUeq: "{p} = \<sigma> \<inter> U"
    using hsopen_top unfolding subspace_topology_def by (by100 blast)
  have hUopen: "open U"
    using hUtop unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hopenin: "openin (top_of_set \<sigma>) {p}"
    unfolding openin_open using hUopen hpUeq by (by100 blast)
  have hclosedin: "closedin (top_of_set \<sigma>) {p}"
  proof -
    have hclosed: "closed ({p}::(real^2) set)"
      by (by100 simp)
    have "{p} = \<sigma> \<inter> {p}"
      using hp by (by100 blast)
    thus ?thesis
      unfolding closedin_closed using hclosed by (by100 blast)
  qed
  obtain V m where hV_fin: "finite V"
    and hV_card: "card V = 2 + 1"
    and h2m: "2 \<le> m"
    and hgp: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma> unfolding geotop_simplex_dim_def by (by100 blast)
  have hconv: "convex \<sigma>"
    unfolding h\<sigma>_eq geotop_convex_hull_eq_HOL by (rule convex_convex_hull)
  have hconn: "connected \<sigma>"
    by (rule convex_connected[OF hconv])
  have hcases: "{p} = {} \<or> {p} = \<sigma>"
    using connected_clopen[THEN iffD1, OF hconn] hopenin hclosedin by (by100 blast)
  have h\<sigma>_singleton: "\<sigma> = {p}"
    using hcases by (by100 simp)
  have hdim2: "geotop_simplex_dim {p} 2"
    using h\<sigma> h\<sigma>_singleton by (by100 simp)
  have hdim0: "geotop_simplex_dim {p} 0"
    by (rule geotop_singleton_is_simplex)
  have "2 = (0::nat)"
    by (rule geotop_simplex_dim_unique[OF hdim2 hdim0])
  thus False
    by (by100 simp)
qed

lemma geotop_2_cell_no_open_singleton:
  fixes C :: "(real^2) set"
  assumes hcell: "geotop_is_n_cell C TC 2"
  assumes hp: "p \<in> C"
  shows "{p} \<notin> TC"
proof
  assume hpopen: "{p} \<in> TC"
  have hcell_ex: "\<exists>(\<sigma>::(real^2) set) f. geotop_simplex_dim \<sigma> 2 \<and>
            top1_homeomorphism_on C TC \<sigma>
              (subspace_topology UNIV geotop_euclidean_topology \<sigma>) f"
    by (rule geotop_is_n_cell_imp_homeo_ex[OF hcell])
  obtain \<sigma> and f :: "real^2 \<Rightarrow> real^2" where h\<sigma>: "geotop_simplex_dim \<sigma> 2"
    and hhomeo: "top1_homeomorphism_on C TC \<sigma>
              (subspace_topology UNIV geotop_euclidean_topology \<sigma>) f"
    using hcell_ex by (by100 blast)
  have himage_open: "f ` {p} \<in> subspace_topology UNIV geotop_euclidean_topology \<sigma>"
    by (rule top1_homeomorphism_on_open_image[OF hhomeo hpopen]) (use hp in \<open>by100 blast\<close>)
  have hbij: "bij_betw f C \<sigma>"
    by (rule top1_homeomorphism_on_imp_bij[OF hhomeo])
  have hfp\<sigma>: "f p \<in> \<sigma>"
    using hbij hp unfolding bij_betw_def by (by100 blast)
  have himage_eq: "f ` {p} = {f p}"
    by (by100 simp)
  have hfp_open: "{f p} \<in> subspace_topology UNIV geotop_euclidean_topology \<sigma>"
    using himage_open himage_eq by (by100 simp)
  show False
    using geotop_2_simplex_no_open_singleton[OF h\<sigma> hfp\<sigma>] hfp_open
    by (by100 blast)
qed

lemma geotop_2_manifold_with_boundary_no_open_singleton:
  fixes M :: "(real^2) set"
  assumes hM: "geotop_n_manifold_with_boundary_on M (\<lambda>x y. norm (x - y)) 2"
  assumes hvM: "v \<in> M"
  shows "{v} \<notin> subspace_topology UNIV geotop_euclidean_topology M"
proof
  let ?d = "(\<lambda>x y. norm (x - y))"
  let ?T = "top1_metric_topology_on M ?d"
  assume hs_geo: "{v} \<in> subspace_topology UNIV geotop_euclidean_topology M"
  have hT_eq: "?T = subspace_topology UNIV geotop_euclidean_topology M"
    by (rule top1_norm_metric_topology_on_eq_geotop_subspace_early)
  have hs_metric: "{v} \<in> ?T"
    using hs_geo hT_eq by (by100 simp)
  have hcharts:
    "\<forall>P\<in>M. \<exists>U. openin_on M ?T U \<and> P \<in> U \<and>
       geotop_is_n_cell (closure_on M ?T U)
         (subspace_topology M ?T (closure_on M ?T U)) 2"
    using hM unfolding geotop_n_manifold_with_boundary_on_def by (by100 blast)
  obtain U where hU_openin: "openin_on M ?T U"
    and hvU: "v \<in> U"
    and hcell: "geotop_is_n_cell (closure_on M ?T U)
         (subspace_topology M ?T (closure_on M ?T U)) 2"
    using hcharts hvM by (by100 blast)
  let ?C = "closure_on M ?T U"
  have hU_sub_M: "U \<subseteq> M"
    using hU_openin unfolding openin_on_def by (by100 blast)
  have hvC: "v \<in> ?C"
    by (rule subsetD[OF subset_closure_on hvU])
  have hsingle_open_C: "{v} \<in> subspace_topology M ?T ?C"
  proof -
    have "?C \<inter> {v} = {v}"
      using hvC by (by100 blast)
    thus ?thesis
      unfolding subspace_topology_def using hs_metric by (by100 blast)
  qed
  show False
    using geotop_2_cell_no_open_singleton[OF hcell hvC] hsingle_open_C
    by (by100 blast)
qed


end
