theory GeoTop_3_4_GraphFacts
  imports "GeoTop34LinkFactsDirty.GeoTop_3_4_LinkFacts"
begin

text \<open>Moise \<S>4, Theorem 8: the graph-classification step used after
Lemmas 2--4.  A finite connected linear graph whose every vertex has
exactly two incident edges is a polygon.\<close>
lemma geotop_HOL_homeomorphism_imp_top1_homeomorphism_on_cross_dev34:
  fixes X :: "'a::real_normed_vector set" and Y :: "'b::real_normed_vector set"
  assumes hfg: "homeomorphism X Y f g"
  shows "top1_homeomorphism_on X
              (subspace_topology UNIV geotop_euclidean_topology X)
              Y (subspace_topology UNIV geotop_euclidean_topology Y) f"
proof -
  have hf_cont_HOL: "continuous_on X f"
    using hfg unfolding homeomorphism_def by (by100 blast)
  have hg_cont_HOL: "continuous_on Y g"
    using hfg unfolding homeomorphism_def by (by100 blast)
  have hf_img_eq: "f ` X = Y"
    using hfg unfolding homeomorphism_def by (by100 blast)
  have hg_img_eq: "g ` Y = X"
    using hfg unfolding homeomorphism_def by (by100 blast)
  have hfg_id: "\<forall>x\<in>X. g (f x) = x"
    using hfg unfolding homeomorphism_def by (by100 blast)
  have hgf_id: "\<forall>y\<in>Y. f (g y) = y"
    using hfg unfolding homeomorphism_def by (by100 blast)
  have hf_img: "f ` X \<subseteq> Y" using hf_img_eq by (by100 simp)
  have hg_img: "g ` Y \<subseteq> X" using hg_img_eq by (by100 simp)
  have hf_top1: "top1_continuous_map_on X
                    (subspace_topology UNIV geotop_euclidean_topology X)
                    Y (subspace_topology UNIV geotop_euclidean_topology Y) f"
    by (rule geotop_continuous_on_imp_top1_continuous_map_on[OF hf_cont_HOL hf_img])
  have hg_top1: "top1_continuous_map_on Y
                    (subspace_topology UNIV geotop_euclidean_topology Y)
                    X (subspace_topology UNIV geotop_euclidean_topology X) g"
    by (rule geotop_continuous_on_imp_top1_continuous_map_on[OF hg_cont_HOL hg_img])
  have hf_bij: "bij_betw f X Y"
    by (rule bij_betw_byWitness[where f' = g, OF hfg_id hgf_id hf_img hg_img])
  have hf_inj: "inj_on f X" using hf_bij unfolding bij_betw_def by (by100 blast)
  have hg_eq_inv: "\<forall>y\<in>Y. g y = inv_into X f y"
  proof
    fix y assume hy: "y \<in> Y"
    have hgy_in_X: "g y \<in> X" using hg_img_eq hy by (by100 blast)
    have hfgy: "f (g y) = y" using hgf_id hy by (by100 blast)
    have "inv_into X f y = g y" by (rule inv_into_f_eq[OF hf_inj hgy_in_X hfgy])
    thus "g y = inv_into X f y" by (by100 simp)
  qed
  have h_invf_top1: "top1_continuous_map_on Y
                    (subspace_topology UNIV geotop_euclidean_topology Y)
                    X (subspace_topology UNIV geotop_euclidean_topology X)
                    (inv_into X f)"
    using hg_top1 top1_continuous_map_on_cong[OF hg_eq_inv] by (by100 blast)
  have h_Teucl_X: "is_topology_on (UNIV::'a set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have h_Teucl_Y: "is_topology_on (UNIV::'b set) geotop_euclidean_topology"
    by (metis geotop_euclidean_topology_eq_open_sets top1_open_sets_is_topology_on_UNIV)
  have hTX: "is_topology_on X (subspace_topology UNIV geotop_euclidean_topology X)"
    by (rule subspace_topology_is_topology_on[OF h_Teucl_X subset_UNIV])
  have hTY: "is_topology_on Y (subspace_topology UNIV geotop_euclidean_topology Y)"
    by (rule subspace_topology_is_topology_on[OF h_Teucl_Y subset_UNIV])
  show ?thesis
    unfolding top1_homeomorphism_on_def
    using hTX hTY hf_bij hf_top1 h_invf_top1 by (by100 blast)
qed

lemma geotop_is_arc_has_arc_endpoints_dev34:
  fixes A :: "(real^2) set"
  assumes hA: "geotop_is_arc A (subspace_topology UNIV geotop_euclidean_topology A)"
  shows "\<exists>E. geotop_arc_endpoints A E"
proof -
  obtain \<gamma> :: "real \<Rightarrow> real^2" where h\<gamma>_arc: "arc \<gamma>" and h\<gamma>_pim: "path_image \<gamma> = A"
    using geotop_is_arc_imp_HOL_arc[OF hA] by (by100 blast)
  obtain h where hhomeo_HOL: "homeomorphism {0..1} (path_image \<gamma>) \<gamma> h"
    using geotop_arc_homeomorphism_image[OF h\<gamma>_arc] by (by100 blast)
  have hhomeo_top1_iv: "top1_homeomorphism_on {0..1}
              (subspace_topology UNIV geotop_euclidean_topology {0..1})
              (path_image \<gamma>) (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>)) \<gamma>"
    by (rule geotop_HOL_homeomorphism_imp_top1_homeomorphism_on_cross_dev34[OF hhomeo_HOL])
  have hunit: "{t::real. 0 \<le> t \<and> t \<le> 1} = {0..1}"
    by (by100 auto)
  have hhomeo_top1_A: "top1_homeomorphism_on {t::real. 0 \<le> t \<and> t \<le> 1}
              (subspace_topology UNIV geotop_euclidean_topology {t::real. 0 \<le> t \<and> t \<le> 1})
              A (subspace_topology UNIV geotop_euclidean_topology A) \<gamma>"
    using hhomeo_top1_iv hunit h\<gamma>_pim by (by100 simp)
  have h\<gamma>_inj: "inj_on \<gamma> {0..1}"
    using h\<gamma>_arc unfolding arc_def by (by100 blast)
  have h\<gamma>0_ne_\<gamma>1: "\<gamma> 0 \<noteq> \<gamma> 1"
    using h\<gamma>_inj unfolding inj_on_def by (by100 force)
  have hcard: "card {\<gamma> 0, \<gamma> 1} = 2"
    using h\<gamma>0_ne_\<gamma>1 by (by100 simp)
  have hsub: "{\<gamma> 0, \<gamma> 1} \<subseteq> A"
    using h\<gamma>_pim unfolding path_image_def by (by100 force)
  show ?thesis
    unfolding geotop_arc_endpoints_def
    using hA hcard hsub hhomeo_top1_A by (by100 blast)
qed

lemma geotop_broken_line_endpoint_vertex_incident_edge_card_one_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hpoly: "geotop_polyhedron L = B"
  assumes hB: "geotop_is_broken_line B"
  assumes hE: "geotop_arc_endpoints B E"
  assumes hP: "P \<in> E"
  assumes hPL: "{P} \<in> L"
  shows "card {e\<in>L. geotop_is_edge e \<and> P \<in> e} = 1"
proof -
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  have hL_1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_dev34[OF hL])
  have hP_B: "P \<in> B"
    using hE hP unfolding geotop_arc_endpoints_def by (by100 blast)
  obtain \<gamma> :: "real \<Rightarrow> real^2"
    where h\<gamma>_arc: "arc \<gamma>"
      and h\<gamma>_pim: "path_image \<gamma> = B"
      and hE_eq: "E = {pathstart \<gamma>, pathfinish \<gamma>}"
    using arc_endpoints_imp_arc_HOL[OF hE] by (by100 blast)
  have hP_endpoint_param: "\<gamma> 0 = P \<or> \<gamma> 1 = P"
    using hP hE_eq unfolding pathstart_def pathfinish_def by (by100 blast)
  define EdgesAtP where
    "EdgesAtP = {\<sigma>\<in>L. P \<in> \<sigma> \<and> geotop_simplex_dim \<sigma> 1}"
  have hEdges_fin: "finite EdgesAtP"
    unfolding EdgesAtP_def using hfin by (by100 simp)
  have hL_local_isolation:
    "\<exists>\<delta>>0. ball P \<delta> \<inter> B \<subseteq> \<Union>{\<tau>\<in>L. P \<in> \<tau>}"
  proof -
    have hL_simp_all: "\<forall>\<tau>\<in>L. geotop_is_simplex \<tau>"
      by (rule geotop_is_complex_simplex[OF hL_complex])
    have hL_closed_all: "\<forall>\<tau>\<in>L. closed \<tau>"
    proof
      fix \<tau> assume h\<tau>L: "\<tau> \<in> L"
      have hsim: "geotop_is_simplex \<tau>"
        by (rule bspec[OF hL_simp_all h\<tau>L])
      obtain V m n where hVfin: "finite V" and h\<tau>_hull: "\<tau> = geotop_convex_hull V"
        using hsim unfolding geotop_is_simplex_def by (by100 blast)
      have h\<tau>_HOL: "\<tau> = convex hull V"
        using h\<tau>_hull geotop_convex_hull_eq_HOL by (by100 simp)
      have h_compact: "compact (convex hull V)"
        using hVfin finite_imp_compact_convex_hull by (by100 blast)
      show "closed \<tau>"
        using h\<tau>_HOL compact_imp_closed[OF h_compact] by (by100 simp)
    qed
    have hB_union: "B = \<Union>L"
      using hpoly unfolding geotop_polyhedron_def by (by100 simp)
    show ?thesis
      using finite_union_closed_local_isolation[OF hfin hL_closed_all hB_union hP_B]
      by (by100 blast)
  qed
  have hEdges_nonempty: "EdgesAtP \<noteq> {}"
  proof
    assume hEdges_empty: "EdgesAtP = {}"
    obtain \<delta> where h\<delta>_pos: "\<delta> > 0"
        and h\<delta>_iso: "ball P \<delta> \<inter> B \<subseteq> \<Union>{\<tau>\<in>L. P \<in> \<tau>}"
      using hL_local_isolation by (by100 blast)
    have h_ball_only_P: "ball P \<delta> \<inter> B \<subseteq> {P}"
    proof
      fix x assume hx: "x \<in> ball P \<delta> \<inter> B"
      obtain \<tau> where h\<tau>L: "\<tau> \<in> L" and hP\<tau>: "P \<in> \<tau>" and hx\<tau>: "x \<in> \<tau>"
        using h\<delta>_iso hx by (by100 blast)
      have hdim: "\<exists>n\<le>1. geotop_simplex_dim \<tau> n"
        using hL_1dim h\<tau>L unfolding geotop_complex_is_1dim_def by (by100 blast)
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
          unfolding EdgesAtP_def using h\<tau>L hP\<tau> h\<tau>dim1 by (by100 simp)
        hence False using hEdges_empty by (by100 simp)
        thus ?thesis by (rule FalseE)
      qed
    qed
    have hP_cl_int: "P \<in> closure (geotop_arc_interior B E)"
      using arc_closure_interior_eq_arc[OF hE] hP_B by (by100 simp)
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
    have hy_notP: "y \<noteq> P" using hy_int hP unfolding geotop_arc_interior_def by (by100 blast)
    show False using hyP hy_notP by (by100 blast)
  qed
  have hEdges_at_most_one: "\<forall>\<tau>\<in>EdgesAtP. \<forall>\<rho>\<in>EdgesAtP. \<tau> = \<rho>"
  proof (intro ballI)
    fix \<tau> \<rho>
    assume h\<tau>E: "\<tau> \<in> EdgesAtP" and h\<rho>E: "\<rho> \<in> EdgesAtP"
    have h\<tau>L: "\<tau> \<in> L" and hP\<tau>: "P \<in> \<tau>" and h\<tau>dim: "geotop_simplex_dim \<tau> 1"
      using h\<tau>E unfolding EdgesAtP_def by (by100 blast)+
    have h\<rho>L: "\<rho> \<in> L" and hP\<rho>: "P \<in> \<rho>" and h\<rho>dim: "geotop_simplex_dim \<rho> 1"
      using h\<rho>E unfolding EdgesAtP_def by (by100 blast)+
    have h_edge_segment_at_P:
      "\<And>e. \<lbrakk>e \<in> L; P \<in> e; geotop_simplex_dim e 1\<rbrakk>
        \<Longrightarrow> \<exists>q. q \<noteq> P \<and> e = closed_segment P q"
    proof -
      fix e
      assume heL: "e \<in> L" and hPe: "P \<in> e" and hedim: "geotop_simplex_dim e 1"
      have hcases: "(\<exists>v. e = {v}) \<or> (\<exists>a b. a \<noteq> b \<and> e = closed_segment a b)"
        by (rule geotop_1dim_simplex_cases[OF hL_1dim heL])
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
              [OF hL_complex hPL heL heab hab hPe])
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
      using h_edge_segment_at_P[OF h\<tau>L hP\<tau> h\<tau>dim] by (by100 blast)
    obtain q\<rho> where hq\<rho>_ne: "q\<rho> \<noteq> P" and h\<rho>_seg: "\<rho> = closed_segment P q\<rho>"
      using h_edge_segment_at_P[OF h\<rho>L hP\<rho> h\<rho>dim] by (by100 blast)
    have h_overlap_nonendpoint: "\<exists>z. z \<in> \<tau> \<inter> \<rho> \<and> z \<noteq> P"
    proof -
      have hL_path: "geotop_polyhedron L = path_image \<gamma>"
        using hpoly h\<gamma>_pim by (by100 simp)
      obtain s_tau t_tau where hst_tau_le: "s_tau \<le> t_tau"
          and hs_tau_01: "s_tau \<in> {0..1}"
          and ht_tau_01: "t_tau \<in> {0..1}"
          and hpre_tau: "{s\<in>{0..1}. \<gamma> s \<in> \<tau>} = {s_tau..t_tau}"
          and hends_tau: "{\<gamma> s_tau, \<gamma> t_tau} = {P, q\<tau>}"
        using geotop_arc_1simplex_preimage_structure
          [OF h\<gamma>_arc hL_1dim hL_path h\<tau>L h\<tau>_seg hq\<tau>_ne[symmetric]]
        by (by100 blast)
      obtain s_rho t_rho where hst_rho_le: "s_rho \<le> t_rho"
          and hs_rho_01: "s_rho \<in> {0..1}"
          and ht_rho_01: "t_rho \<in> {0..1}"
          and hpre_rho: "{s\<in>{0..1}. \<gamma> s \<in> \<rho>} = {s_rho..t_rho}"
          and hends_rho: "{\<gamma> s_rho, \<gamma> t_rho} = {P, q\<rho>}"
        using geotop_arc_1simplex_preimage_structure
          [OF h\<gamma>_arc hL_1dim hL_path h\<rho>L h\<rho>_seg hq\<rho>_ne[symmetric]]
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
      using hL_complex h\<tau>L h\<rho>L h_inter_ne unfolding geotop_is_complex_def by (by100 blast)
    have hface_\<rho>: "geotop_is_face (\<tau> \<inter> \<rho>) \<rho>"
      using hL_complex h\<tau>L h\<rho>L h_inter_ne unfolding geotop_is_complex_def by (by100 blast)
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
  have htarget_eq: "{e\<in>L. geotop_is_edge e \<and> P \<in> e} = EdgesAtP"
    unfolding EdgesAtP_def geotop_is_edge_def by (by100 blast)
  obtain e where he: "EdgesAtP = {e}"
    using hEdges_unique by (by100 blast)
  show ?thesis
    using htarget_eq he by (by100 simp)
qed

lemma geotop_broken_line_endpoint_in_finite_linear_graph_vertex_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hpoly: "geotop_polyhedron L = B"
  assumes hB: "geotop_is_broken_line B"
  assumes hE: "geotop_arc_endpoints B E"
  assumes hP: "P \<in> E"
  shows "{P} \<in> L"
proof -
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  have hL_1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_dev34[OF hL])
  have hP_B: "P \<in> B"
    using hE hP unfolding geotop_arc_endpoints_def by (by100 blast)
  obtain \<gamma> :: "real \<Rightarrow> real^2"
    where h\<gamma>_arc: "arc \<gamma>"
      and h\<gamma>_pim: "path_image \<gamma> = B"
      and hE_eq: "E = {pathstart \<gamma>, pathfinish \<gamma>}"
    using arc_endpoints_imp_arc_HOL[OF hE] by (by100 blast)
  have hP_endpoint_param: "\<gamma> 0 = P \<or> \<gamma> 1 = P"
    using hP hE_eq unfolding pathstart_def pathfinish_def by (by100 blast)
  have hpoly_path: "geotop_polyhedron L = path_image \<gamma>"
    using hpoly h\<gamma>_pim by (by100 simp)
  have hP_poly: "P \<in> geotop_polyhedron L"
    using hP_B hpoly by (by100 simp)
  obtain \<sigma> where h\<sigma>L: "\<sigma> \<in> L" and hP\<sigma>: "P \<in> \<sigma>"
    using hP_poly unfolding geotop_polyhedron_def by (by100 blast)
  have hcases: "(\<exists>v. \<sigma> = {v}) \<or> (\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b)"
    by (rule geotop_1dim_simplex_cases[OF hL_1dim h\<sigma>L])
  show ?thesis
  proof (rule disjE[OF hcases])
    assume "\<exists>v. \<sigma> = {v}"
    then obtain v where h\<sigma>v: "\<sigma> = {v}" by (by100 blast)
    have hPv: "P = v" using hP\<sigma> h\<sigma>v by (by100 blast)
    show "{P} \<in> L" using h\<sigma>L h\<sigma>v hPv by (by100 simp)
  next
    assume "\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b"
    then obtain a b where hab: "a \<noteq> b" and h\<sigma>ab: "\<sigma> = closed_segment a b"
      by (by100 blast)
    have hP_ab: "P = a \<or> P = b"
    proof (rule ccontr)
      assume hnot: "\<not> (P = a \<or> P = b)"
      have hP_ne_a: "P \<noteq> a" and hP_ne_b: "P \<noteq> b"
        using hnot by (by100 blast)+
      obtain s t where hst_le: "s \<le> t"
          and hs_01: "s \<in> {0..1}"
          and ht_01: "t \<in> {0..1}"
          and hpre: "{r\<in>{0..1}. \<gamma> r \<in> \<sigma>} = {s..t}"
          and hends: "{\<gamma> s, \<gamma> t} = {a, b}"
        using geotop_arc_1simplex_preimage_structure
          [OF h\<gamma>_arc hL_1dim hpoly_path h\<sigma>L h\<sigma>ab hab]
        by (by100 blast)
      show False
      proof (rule disjE[OF hP_endpoint_param])
        assume h0P: "\<gamma> 0 = P"
        have h0_pre: "0 \<in> {r\<in>{0..1}. \<gamma> r \<in> \<sigma>}"
          using h0P hP\<sigma> by (by100 simp)
        have h0_iv: "0 \<in> {s..t}"
          using h0_pre hpre by (by100 simp)
        have hs0: "s = 0"
          using h0_iv hs_01 by (by100 simp)
        have "P \<in> {a, b}"
          using hends hs0 h0P by (by100 blast)
        thus False using hP_ne_a hP_ne_b by (by100 blast)
      next
        assume h1P: "\<gamma> 1 = P"
        have h1_pre: "1 \<in> {r\<in>{0..1}. \<gamma> r \<in> \<sigma>}"
          using h1P hP\<sigma> by (by100 simp)
        have h1_iv: "1 \<in> {s..t}"
          using h1_pre hpre by (by100 simp)
        have ht1: "t = 1"
          using h1_iv ht_01 by (by100 simp)
        have "P \<in> {a, b}"
          using hends ht1 h1P by (by100 blast)
        thus False using hP_ne_a hP_ne_b by (by100 blast)
      qed
    qed
    have hface_closed: "\<forall>\<rho>\<in>L. \<forall>\<tau>. geotop_is_face \<tau> \<rho> \<longrightarrow> \<tau> \<in> L"
      by (rule geotop_is_complex_face_closed[OF hL_complex])
    show "{P} \<in> L"
    proof (rule disjE[OF hP_ab])
      assume hPa: "P = a"
      have hface: "geotop_is_face {P} \<sigma>"
        using geotop_closed_segment_is_face_endpoint[OF hab, of P] hPa h\<sigma>ab by (by100 simp)
      show ?thesis using hface_closed h\<sigma>L hface by (by100 blast)
    next
      assume hPb: "P = b"
      have hba: "b \<noteq> a"
        using hab by (by100 blast)
      have hface: "geotop_is_face {P} \<sigma>"
        using geotop_closed_segment_is_face_endpoint[OF hba, of P] hPb h\<sigma>ab
          closed_segment_commute[of a b]
        by (by100 simp)
      show ?thesis using hface_closed h\<sigma>L hface by (by100 blast)
    qed
  qed
qed

lemma geotop_broken_line_polyhedron_finite_linear_graph_has_endpoint_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hB: "geotop_is_broken_line (geotop_polyhedron L)"
  shows "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
proof -
  obtain K where hB_arc:
      "geotop_is_arc (geotop_polyhedron L)
        (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    using hB unfolding geotop_is_broken_line_def by (by100 blast)
  obtain E where hE: "geotop_arc_endpoints (geotop_polyhedron L) E"
    using geotop_is_arc_has_arc_endpoints_dev34[OF hB_arc] by (by100 blast)
  have hcardE: "card E = 2"
    using hE unfolding geotop_arc_endpoints_def by (by100 blast)
  have hE_nonempty: "E \<noteq> {}"
  proof
    assume hE_empty: "E = {}"
    have "card E = 0" using hE_empty by (by100 simp)
    thus False using hcardE by (by100 simp)
  qed
  obtain P where hP: "P \<in> E" using hE_nonempty by (by100 blast)
  have hPL: "{P} \<in> L"
    by (rule geotop_broken_line_endpoint_in_finite_linear_graph_vertex_dev34
        [OF hL hfin refl hB hE hP])
  have hcard_edges: "card {e\<in>L. geotop_is_edge e \<and> P \<in> e} = 1"
    by (rule geotop_broken_line_endpoint_vertex_incident_edge_card_one_dev34
        [OF hL hfin refl hB hE hP hPL])
  have h_endpoint: "geotop_graph_endpoint L P"
    by (rule geotop_degree_one_vertex_graph_endpoint_dev34[OF hL hPL hcard_edges])
  show ?thesis using hPL h_endpoint by (by100 blast)
qed

lemma geotop_degree_two_linear_graph_polyhedron_not_broken_line_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "\<not> geotop_is_broken_line (geotop_polyhedron L)"
proof
  assume hB: "geotop_is_broken_line (geotop_polyhedron L)"
  obtain w where hwL: "{w} \<in> L" and hend: "geotop_graph_endpoint L w"
    using geotop_broken_line_polyhedron_finite_linear_graph_has_endpoint_dev34
      [OF hL hfin hB] by (by100 blast)
  have hnoend: "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
    by (rule geotop_degree_two_vertices_no_graph_endpoint_dev34[OF hdegree])
  show False
    using hnoend hwL hend by (by100 blast)
qed

lemma geotop_finite_connected_degree_two_linear_graph_polygon_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "geotop_is_polygon (geotop_polyhedron L)"
proof -
  have hnonisolated: "\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e)"
    by (rule geotop_degree_two_vertices_nonisolated_dev34[OF hdegree])
  have hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
    using hdegree by (by100 blast)
  have hshape: "geotop_is_broken_line (geotop_polyhedron L) \<or>
      geotop_is_polygon (geotop_polyhedron L)"
    by (rule geotop_finite_connected_degree_one_or_two_linear_graph_line_or_polygon_dev34
        [OF hL hfin hconn hdegree12])
  have hnot_line: "\<not> geotop_is_broken_line (geotop_polyhedron L)"
    by (rule geotop_degree_two_linear_graph_polyhedron_not_broken_line_dev34
        [OF hL hfin hdegree])
  show ?thesis
    using hshape hnot_line by (by100 blast)
qed

text \<open>Moise \<S>4, Theorem 9: the corresponding graph-classification step
for manifolds with boundary.  After Lemmas 2--4, every link vertex has
degree one or two; a finite connected linear graph with that local
degree bound is either a broken line or a polygon.\<close>
lemma geotop_graph_endpoint_singleton_and_card_one_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hend: "geotop_graph_endpoint L w"
  shows "{w} \<in> L \<and> card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  have hw_vertex: "w \<in> geotop_complex_vertices L"
    using hend unfolding geotop_graph_endpoint_def by (by100 blast)
  have hwL: "{w} \<in> L"
    using geotop_complex_vertices_eq_0_simplexes[OF hcomplex] hw_vertex by (by100 blast)
  have hcard: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1"
    using hend unfolding geotop_graph_endpoint_def by (by100 blast)
  show ?thesis using hwL hcard by (by100 blast)
qed

lemma geotop_graph_endpoint_unique_incident_edge_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  shows "\<exists>!e. e \<in> L \<and> geotop_is_edge e \<and> w \<in> e"
proof -
  let ?S = "{e\<in>L. geotop_is_edge e \<and> w \<in> e}"
  have hcard: "card ?S = 1"
    using geotop_graph_endpoint_singleton_and_card_one_dev34[OF hL hend]
    by (by100 blast)
  obtain e where hS: "?S = {e}"
    by (rule card_1_singletonE[OF hcard])
  show ?thesis
  proof (rule ex1I[of _ e])
    show "e \<in> L \<and> geotop_is_edge e \<and> w \<in> e"
      using hS by (by100 simp)
  next
    fix e'
    assume he': "e' \<in> L \<and> geotop_is_edge e' \<and> w \<in> e'"
    have "e' \<in> ?S" using he' by (by100 simp)
    thus "e' = e" using hS by (by100 simp)
  qed
qed

lemma geotop_graph_endpoint_unique_segment_neighbor_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  shows "\<exists>e q. e \<in> L \<and> geotop_is_edge e \<and> w \<in> e
      \<and> q \<noteq> w \<and> e = closed_segment w q \<and> {q} \<in> L"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  have h1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_dev34[OF hL])
  have hwL: "{w} \<in> L"
    using geotop_graph_endpoint_singleton_and_card_one_dev34[OF hL hend]
    by (by100 blast)
  obtain e where heL: "e \<in> L" and hedge: "geotop_is_edge e" and hw_e: "w \<in> e"
    using geotop_graph_endpoint_unique_incident_edge_dev34[OF hL hfin hend]
    by (by100 blast)
  have hedim: "geotop_simplex_dim e 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  have hcases: "(\<exists>v. e = {v}) \<or> (\<exists>a b. a \<noteq> b \<and> e = closed_segment a b)"
    by (rule geotop_1dim_simplex_cases[OF h1dim heL])
  show ?thesis
  proof (rule disjE[OF hcases])
    assume "\<exists>v. e = {v}"
    then obtain v where hev: "e = {v}" by (by100 blast)
    have hdim0: "geotop_simplex_dim e 0"
      using hev geotop_singleton_is_simplex by (by100 simp)
    have "0 = (1::nat)" by (rule geotop_simplex_dim_unique[OF hdim0 hedim])
    hence False by (by100 simp)
    thus ?thesis by (rule FalseE)
  next
    assume "\<exists>a b. a \<noteq> b \<and> e = closed_segment a b"
    then obtain a b where hab: "a \<noteq> b" and heab: "e = closed_segment a b"
      by (by100 blast)
    have hw_endpoint: "w = a \<or> w = b"
      by (rule geotop_1dim_vertex_in_1simplex_is_endpoint
          [OF hcomplex hwL heL heab hab hw_e])
    have hface_closed: "\<forall>\<rho>\<in>L. \<forall>\<tau>. geotop_is_face \<tau> \<rho> \<longrightarrow> \<tau> \<in> L"
      by (rule geotop_is_complex_face_closed[OF hcomplex])
    show ?thesis
    proof (rule disjE[OF hw_endpoint])
      assume hwa: "w = a"
      have hba: "b \<noteq> a" using hab by (by100 blast)
      have hface_b: "geotop_is_face {b} e"
        using geotop_closed_segment_is_face_endpoint[OF hba, of b]
          heab closed_segment_commute[of a b]
        by (by100 simp)
      have hbL: "{b} \<in> L"
        using hface_closed heL hface_b by (by100 blast)
      show ?thesis
        using heL hedge hw_e hwa hab heab hbL by (by100 blast)
    next
      assume hwb: "w = b"
      have hface_a: "geotop_is_face {a} e"
        using geotop_closed_segment_is_face_endpoint[OF hab, of a] heab
        by (by100 simp)
      have haL: "{a} \<in> L"
        using hface_closed heL hface_a by (by100 blast)
      show ?thesis
        using heL hedge hw_e hwb hab heab haL closed_segment_commute[of a b]
        by (by100 blast)
    qed
  qed
qed

lemma geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes h\<sigma>L: "\<sigma> \<in> L"
  assumes hw\<sigma>: "w \<in> \<sigma>"
  shows "\<sigma> = {w} \<or> \<sigma> = e"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  have h1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_dev34[OF hL])
  have hwL: "{w} \<in> L"
    using geotop_graph_endpoint_singleton_and_card_one_dev34[OF hL hend]
    by (by100 blast)
  have hunique: "\<exists>!l. l \<in> L \<and> geotop_is_edge l \<and> w \<in> l"
    by (rule geotop_graph_endpoint_unique_incident_edge_dev34[OF hL hfin hend])
  have hcases: "(\<exists>v. \<sigma> = {v}) \<or> (\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b)"
    by (rule geotop_1dim_simplex_cases[OF h1dim h\<sigma>L])
  show ?thesis
  proof (rule disjE[OF hcases])
    assume "\<exists>v. \<sigma> = {v}"
    then obtain v where h\<sigma>v: "\<sigma> = {v}" by (by100 blast)
    have "v = w" using h\<sigma>v hw\<sigma> by (by100 blast)
    show ?thesis using h\<sigma>v \<open>v = w\<close> by (by100 simp)
  next
    assume "\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b"
    then obtain a b where hab: "a \<noteq> b" and h\<sigma>ab: "\<sigma> = closed_segment a b"
      by (by100 blast)
    have h\<sigma>edge: "geotop_is_edge \<sigma>"
      using geotop_closed_segment_is_simplex[OF hab] h\<sigma>ab
      unfolding geotop_is_edge_def by (by100 simp)
    have h\<sigma>prop: "\<sigma> \<in> L \<and> geotop_is_edge \<sigma> \<and> w \<in> \<sigma>"
      using h\<sigma>L h\<sigma>edge hw\<sigma> by (by100 blast)
    have heprop: "e \<in> L \<and> geotop_is_edge e \<and> w \<in> e"
      using heL hedge hwe by (by100 blast)
    have "\<sigma> = e"
      using hunique h\<sigma>prop heprop by (by100 blast)
    show ?thesis using \<open>\<sigma> = e\<close> by (by100 blast)
  qed
qed

lemma geotop_graph_endpoint_delete_leaf_polyhedron_union_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "geotop_polyhedron L = e \<union> geotop_polyhedron (L - {{w}, e})"
proof -
  have honly: "\<And>\<sigma>. \<lbrakk>\<sigma> \<in> L; w \<in> \<sigma>\<rbrakk> \<Longrightarrow> \<sigma> = {w} \<or> \<sigma> = e"
    by (rule geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_dev34
        [OF hL hfin hend heL hedge hwe])
  have hsubset_w_e: "{w} \<subseteq> e"
    using hwe by (by100 blast)
  show ?thesis
  proof
    show "geotop_polyhedron L \<subseteq> e \<union> geotop_polyhedron (L - {{w}, e})"
    proof
      fix x
      assume hx: "x \<in> geotop_polyhedron L"
      obtain \<sigma> where h\<sigma>L: "\<sigma> \<in> L" and hx\<sigma>: "x \<in> \<sigma>"
        using hx unfolding geotop_polyhedron_def by (by100 blast)
      show "x \<in> e \<union> geotop_polyhedron (L - {{w}, e})"
      proof (cases "w \<in> \<sigma>")
        case True
        have hcase: "\<sigma> = {w} \<or> \<sigma> = e"
          by (rule honly[OF h\<sigma>L True])
        show ?thesis
        proof (rule disjE[OF hcase])
          assume "\<sigma> = {w}"
          have "x \<in> e" using hx\<sigma> \<open>\<sigma> = {w}\<close> hsubset_w_e by (by100 blast)
          thus ?thesis by (by100 blast)
        next
          assume "\<sigma> = e"
          have "x \<in> e" using hx\<sigma> \<open>\<sigma> = e\<close> by (by100 simp)
          thus ?thesis by (by100 blast)
        qed
      next
        case False
        have h\<sigma>rest: "\<sigma> \<in> L - {{w}, e}"
        proof -
          have "\<sigma> \<noteq> {w}" using False by (by100 blast)
          have "\<sigma> \<noteq> e" using False hwe by (by100 blast)
          show ?thesis using h\<sigma>L \<open>\<sigma> \<noteq> {w}\<close> \<open>\<sigma> \<noteq> e\<close> by (by100 simp)
        qed
        have "x \<in> geotop_polyhedron (L - {{w}, e})"
          unfolding geotop_polyhedron_def using h\<sigma>rest hx\<sigma> by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
    qed
  next
    show "e \<union> geotop_polyhedron (L - {{w}, e}) \<subseteq> geotop_polyhedron L"
    proof
      fix x
      assume hx: "x \<in> e \<union> geotop_polyhedron (L - {{w}, e})"
      show "x \<in> geotop_polyhedron L"
      proof (rule UnE[OF hx])
        assume "x \<in> e"
        show ?thesis
          unfolding geotop_polyhedron_def using heL \<open>x \<in> e\<close> by (by100 blast)
      next
        assume "x \<in> geotop_polyhedron (L - {{w}, e})"
        obtain \<sigma> where h\<sigma>rest: "\<sigma> \<in> L - {{w}, e}" and hx\<sigma>: "x \<in> \<sigma>"
          using \<open>x \<in> geotop_polyhedron (L - {{w}, e})\<close>
          unfolding geotop_polyhedron_def by (by100 blast)
        have h\<sigma>L: "\<sigma> \<in> L" using h\<sigma>rest by (by100 simp)
        show ?thesis
          unfolding geotop_polyhedron_def using h\<sigma>L hx\<sigma> by (by100 blast)
      qed
    qed
  qed
qed

lemma geotop_graph_endpoint_not_in_delete_leaf_polyhedron_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "w \<notin> geotop_polyhedron (L - {{w}, e})"
proof
  assume hwrest: "w \<in> geotop_polyhedron (L - {{w}, e})"
  obtain \<sigma> where h\<sigma>rest: "\<sigma> \<in> L - {{w}, e}" and hw\<sigma>: "w \<in> \<sigma>"
    using hwrest unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>L: "\<sigma> \<in> L"
    using h\<sigma>rest by (by100 simp)
  have hcase: "\<sigma> = {w} \<or> \<sigma> = e"
    by (rule geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_dev34
        [OF hL hfin hend heL hedge hwe h\<sigma>L hw\<sigma>])
  show False
  proof (rule disjE[OF hcase])
    assume "\<sigma> = {w}"
    show False using h\<sigma>rest \<open>\<sigma> = {w}\<close> by (by100 simp)
  next
    assume "\<sigma> = e"
    show False using h\<sigma>rest \<open>\<sigma> = e\<close> by (by100 simp)
  qed
qed

lemma geotop_graph_endpoint_delete_leaf_complex_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "geotop_is_complex (L - {{w}, e})"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  have hsub: "L - {{w}, e} \<subseteq> L"
    by (by100 simp)
  have hfaces:
      "\<forall>\<sigma>\<in>L - {{w}, e}. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> L - {{w}, e}"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau>
    assume h\<sigma>rest: "\<sigma> \<in> L - {{w}, e}"
    assume hface: "geotop_is_face \<tau> \<sigma>"
    have h\<sigma>L: "\<sigma> \<in> L"
      using h\<sigma>rest by (by100 simp)
    have h\<tau>L: "\<tau> \<in> L"
      using geotop_is_complex_face_closed[OF hcomplex] h\<sigma>L hface by (by100 blast)
    have h\<tau>sub\<sigma>: "\<tau> \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset[OF hface])
    have h\<sigma>ne_w: "\<sigma> \<noteq> {w}"
      using h\<sigma>rest by (by100 simp)
    have h\<sigma>ne_e: "\<sigma> \<noteq> e"
      using h\<sigma>rest by (by100 simp)
    have h\<tau>ne_w: "\<tau> \<noteq> {w}"
    proof
      assume h\<tau>w: "\<tau> = {w}"
      have hw\<sigma>: "w \<in> \<sigma>"
        using h\<tau>sub\<sigma> h\<tau>w by (by100 blast)
      have hcase: "\<sigma> = {w} \<or> \<sigma> = e"
        by (rule geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_dev34
            [OF hL hfin hend heL hedge hwe h\<sigma>L hw\<sigma>])
      show False using hcase h\<sigma>ne_w h\<sigma>ne_e by (by100 blast)
    qed
    have h\<tau>ne_e: "\<tau> \<noteq> e"
    proof
      assume h\<tau>e: "\<tau> = e"
      have hw\<sigma>: "w \<in> \<sigma>"
        using h\<tau>sub\<sigma> h\<tau>e hwe by (by100 blast)
      have hcase: "\<sigma> = {w} \<or> \<sigma> = e"
        by (rule geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_dev34
            [OF hL hfin hend heL hedge hwe h\<sigma>L hw\<sigma>])
      show False using hcase h\<sigma>ne_w h\<sigma>ne_e by (by100 blast)
    qed
    show "\<tau> \<in> L - {{w}, e}"
      using h\<tau>L h\<tau>ne_w h\<tau>ne_e by (by100 simp)
  qed
  show ?thesis
    by (rule geotop_complex_subset_is_complex[OF hcomplex hsub hfaces])
qed

lemma geotop_graph_endpoint_delete_leaf_linear_graph_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "geotop_is_linear_graph (L - {{w}, e})"
proof -
  have hcomplex: "geotop_is_complex (L - {{w}, e})"
    by (rule geotop_graph_endpoint_delete_leaf_complex_dev34
        [OF hL hfin hend heL hedge hwe])
  have hL1: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_dev34[OF hL])
  have hrest1: "geotop_complex_is_1dim (L - {{w}, e})"
  proof (unfold geotop_complex_is_1dim_def, rule ballI)
    fix \<sigma>
    assume h\<sigma>rest: "\<sigma> \<in> L - {{w}, e}"
    have h\<sigma>L: "\<sigma> \<in> L"
      using h\<sigma>rest by (by100 simp)
    show "\<exists>n::nat. n \<le> 1 \<and> geotop_simplex_dim \<sigma> n"
      using hL1 h\<sigma>L unfolding geotop_complex_is_1dim_def by (by100 blast)
  qed
  show ?thesis
    by (rule geotop_complex_1dim_imp_linear_graph_dev34[OF hcomplex hrest1])
qed

lemma geotop_graph_endpoint_delete_leaf_finite_dev34:
  fixes L :: "(real^2) set set"
  assumes hfin: "finite L"
  shows "finite (L - {{w}, e})"
  using hfin by (by100 simp)

lemma geotop_delete_leaf_incident_edges_neighbor_eq_dev34:
  fixes L :: "(real^2) set set"
  assumes hqw: "q \<noteq> w"
  shows "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l}
      = {l\<in>L. geotop_is_edge l \<and> q \<in> l} - {e}"
proof
  show "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l}
      \<subseteq> {l\<in>L. geotop_is_edge l \<and> q \<in> l} - {e}"
  proof
    fix l
    assume hl: "l \<in> {l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l}"
    have "l \<in> L \<and> geotop_is_edge l \<and> q \<in> l \<and> l \<noteq> e"
      using hl by (by100 simp)
    show "l \<in> {l\<in>L. geotop_is_edge l \<and> q \<in> l} - {e}"
      using \<open>l \<in> L \<and> geotop_is_edge l \<and> q \<in> l \<and> l \<noteq> e\<close> by (by100 simp)
  qed
next
  show "{l\<in>L. geotop_is_edge l \<and> q \<in> l} - {e}
      \<subseteq> {l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l}"
  proof
    fix l
    assume hl: "l \<in> {l\<in>L. geotop_is_edge l \<and> q \<in> l} - {e}"
    have hlL: "l \<in> L" and hledge: "geotop_is_edge l" and hql: "q \<in> l" and hlne: "l \<noteq> e"
      using hl by (by100 simp_all)
    have "l \<noteq> {w}"
    proof
      assume "l = {w}"
      hence "q = w" using hql by (by100 simp)
      thus False using hqw by (by100 blast)
    qed
    have "l \<in> L - {{w}, e}"
      using hlL hlne \<open>l \<noteq> {w}\<close> by (by100 simp)
    show "l \<in> {l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l}"
      using \<open>l \<in> L - {{w}, e}\<close> hledge hql by (by100 simp)
  qed
qed

lemma geotop_delete_leaf_incident_edges_away_eq_dev34:
  fixes L :: "(real^2) set set"
  assumes hwe: "w \<in> e"
  assumes hxe: "x \<notin> e"
  shows "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}
      = {l\<in>L. geotop_is_edge l \<and> x \<in> l}"
proof
  show "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}
      \<subseteq> {l\<in>L. geotop_is_edge l \<and> x \<in> l}"
  proof
    fix l
    assume hl: "l \<in> {l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}"
    show "l \<in> {l\<in>L. geotop_is_edge l \<and> x \<in> l}"
      using hl by (by100 simp)
  qed
next
  show "{l\<in>L. geotop_is_edge l \<and> x \<in> l}
      \<subseteq> {l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}"
  proof
    fix l
    assume hl: "l \<in> {l\<in>L. geotop_is_edge l \<and> x \<in> l}"
    have hlL: "l \<in> L" and hledge: "geotop_is_edge l" and hxl: "x \<in> l"
      using hl by (by100 simp_all)
    have hlne: "l \<noteq> e"
      using hxl hxe by (by100 blast)
    have "l \<noteq> {w}"
    proof
      assume "l = {w}"
      hence "x = w" using hxl by (by100 simp)
      hence "x \<in> e" using hwe by (by100 simp)
      thus False using hxe by (by100 blast)
    qed
    have "l \<in> L - {{w}, e}"
      using hlL hlne \<open>l \<noteq> {w}\<close> by (by100 simp)
    show "l \<in> {l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}"
      using \<open>l \<in> L - {{w}, e}\<close> hledge hxl by (by100 simp)
  qed
qed

lemma geotop_delete_leaf_rest_vertex_not_in_deleted_edge_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes heL: "e \<in> L"
  assumes hqw: "q \<noteq> w"
  assumes heq: "e = closed_segment w q"
  assumes hxrest: "{x} \<in> L - {{w}, e}"
  assumes hxq: "x \<noteq> q"
  shows "x \<notin> e"
proof
  assume hxe: "x \<in> e"
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  have hxL: "{x} \<in> L"
    using hxrest by (by100 simp)
  have hxw: "x \<noteq> w"
  proof
    assume "x = w"
    hence "{x} = {w}" by (by100 simp)
    thus False using hxrest by (by100 simp)
  qed
  have hwq: "w \<noteq> q"
    using hqw by (by100 blast)
  have hendpoint: "x = w \<or> x = q"
    by (rule geotop_1dim_vertex_in_1simplex_is_endpoint
        [OF hcomplex hxL heL heq hwq hxe])
  show False using hendpoint hxw hxq by (by100 blast)
qed

lemma geotop_delete_leaf_rest_vertex_degree_preserved_away_neighbor_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes heL: "e \<in> L"
  assumes hqw: "q \<noteq> w"
  assumes heq: "e = closed_segment w q"
  assumes hxrest: "{x} \<in> L - {{w}, e}"
  assumes hxq: "x \<noteq> q"
  shows "card {l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}
      = card {l\<in>L. geotop_is_edge l \<and> x \<in> l}"
proof -
  have hx_not_e: "x \<notin> e"
    by (rule geotop_delete_leaf_rest_vertex_not_in_deleted_edge_dev34
        [OF hL heL hqw heq hxrest hxq])
  have hwe: "w \<in> e"
    using heq by (by100 simp)
  have "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}
      = {l\<in>L. geotop_is_edge l \<and> x \<in> l}"
    by (rule geotop_delete_leaf_incident_edges_away_eq_dev34[OF hwe hx_not_e])
  show ?thesis
    using \<open>{l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}
      = {l\<in>L. geotop_is_edge l \<and> x \<in> l}\<close>
    by (by100 simp)
qed

lemma geotop_segment_face_with_nonendpoint_eq_dev34:
  fixes F :: "(real^2) set" and a b x :: "real^2"
  assumes hface: "geotop_is_face F (closed_segment a b)"
  assumes hab: "a \<noteq> b"
  assumes hxF: "x \<in> F"
  assumes hxa: "x \<noteq> a"
  assumes hxb: "x \<noteq> b"
  shows "F = closed_segment a b"
proof -
  have hseg_sv: "geotop_simplex_vertices (closed_segment a b) {a, b}"
    by (rule geotop_closed_segment_simplex_vertices[OF hab])
  obtain V W where hV_sv: "geotop_simplex_vertices (closed_segment a b) V"
      and hW_ne: "W \<noteq> {}"
      and hW_sub: "W \<subseteq> V"
      and hF_hull: "F = geotop_convex_hull W"
    using hface unfolding geotop_is_face_def by (by100 blast)
  have hV_eq: "V = {a, b}"
    using geotop_simplex_vertices_unique[OF hV_sv hseg_sv] .
  have hW_sub_ab: "W \<subseteq> {a, b}"
    using hW_sub hV_eq by (by100 simp)
  have hW_cases: "W = {a} \<or> W = {b} \<or> W = {a, b}"
    using hW_sub_ab hW_ne by (by100 blast)
  have hF_HOL: "F = convex hull W"
    using hF_hull geotop_convex_hull_eq_HOL by (by100 simp)
  have hW_eq_ab: "W = {a, b}"
  proof (rule disjE[OF hW_cases])
    assume hW_a: "W = {a}"
    have hF_a: "F = {a}"
      using hF_HOL hW_a by (by100 simp)
    have "x = a" using hxF hF_a by (by100 blast)
    thus ?thesis using hxa by (by100 blast)
  next
    assume hW_rest: "W = {b} \<or> W = {a, b}"
    show ?thesis
    proof (rule disjE[OF hW_rest])
      assume hW_b: "W = {b}"
      have hF_b: "F = {b}"
        using hF_HOL hW_b by (by100 simp)
      have "x = b" using hxF hF_b by (by100 blast)
      thus ?thesis using hxb by (by100 blast)
    next
      assume hW_ab: "W = {a, b}"
      show ?thesis using hW_ab .
    qed
  qed
  have "F = convex hull {a, b}"
    using hF_HOL hW_eq_ab by (by100 simp)
  also have "\<dots> = closed_segment a b"
    by (rule segment_convex_hull)
  finally show ?thesis .
qed

lemma geotop_delete_leaf_edge_inter_rest_polyhedron_subset_neighbor_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes hqw: "q \<noteq> w"
  assumes heq: "e = closed_segment w q"
  shows "e \<inter> geotop_polyhedron (L - {{w}, e}) \<subseteq> {q}"
proof
  fix x
  assume hx: "x \<in> e \<inter> geotop_polyhedron (L - {{w}, e})"
  have hxe: "x \<in> e"
    using hx by (by100 simp)
  obtain \<sigma> where h\<sigma>rest: "\<sigma> \<in> L - {{w}, e}" and hx\<sigma>: "x \<in> \<sigma>"
    using hx unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>L: "\<sigma> \<in> L"
    using h\<sigma>rest by (by100 simp)
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  have hnonempty: "e \<inter> \<sigma> \<noteq> {}"
    using hxe hx\<sigma> by (by100 blast)
  have hface_e: "geotop_is_face (e \<inter> \<sigma>) e"
    using geotop_is_complex_intersection[OF hcomplex] heL h\<sigma>L hnonempty by (by100 blast)
  show "x \<in> {q}"
  proof (cases "x = q")
    case True
    show ?thesis using True by (by100 simp)
  next
    case False
    have hwq: "w \<noteq> q"
      using hqw by (by100 blast)
    show ?thesis
    proof (cases "x = w")
      case True
      have hw\<sigma>: "w \<in> \<sigma>"
        using True hx\<sigma> by (by100 simp)
      have hcase: "\<sigma> = {w} \<or> \<sigma> = e"
        by (rule geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_dev34
            [OF hL hfin hend heL hedge hwe h\<sigma>L hw\<sigma>])
      have False using hcase h\<sigma>rest by (by100 simp)
      thus ?thesis by (rule FalseE)
    next
      case hxnw: False
      have hx_inter: "x \<in> e \<inter> \<sigma>"
        using hxe hx\<sigma> by (by100 blast)
      have hface_seg: "geotop_is_face (e \<inter> \<sigma>) (closed_segment w q)"
        using hface_e heq by (by100 simp)
      have hinter_eq: "e \<inter> \<sigma> = closed_segment w q"
        by (rule geotop_segment_face_with_nonendpoint_eq_dev34
            [OF hface_seg hwq hx_inter hxnw False])
      have "w \<in> \<sigma>"
        using hinter_eq hwe heq by (by100 blast)
      have hcase: "\<sigma> = {w} \<or> \<sigma> = e"
        by (rule geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_dev34
            [OF hL hfin hend heL hedge hwe h\<sigma>L \<open>w \<in> \<sigma>\<close>])
      have False using hcase h\<sigma>rest by (by100 simp)
      thus ?thesis by (rule FalseE)
    qed
  qed
qed

lemma geotop_delete_leaf_edge_inter_rest_polyhedron_eq_neighbor_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes hqL: "{q} \<in> L"
  assumes hqw: "q \<noteq> w"
  assumes heq: "e = closed_segment w q"
  shows "e \<inter> geotop_polyhedron (L - {{w}, e}) = {q}"
proof
  show "e \<inter> geotop_polyhedron (L - {{w}, e}) \<subseteq> {q}"
    by (rule geotop_delete_leaf_edge_inter_rest_polyhedron_subset_neighbor_dev34
        [OF hL hfin hend heL hedge hwe hqw heq])
next
  show "{q} \<subseteq> e \<inter> geotop_polyhedron (L - {{w}, e})"
  proof
    fix x
    assume hx: "x \<in> {q}"
    have hxq: "x = q"
      using hx by (by100 simp)
    have hqe: "q \<in> e"
      using heq by (by100 simp)
    have hq_ne_w: "{q} \<noteq> {w}"
      using hqw by (by100 blast)
    have hq_ne_e: "{q} \<noteq> e"
    proof
      assume "{q} = e"
      have "w \<in> {q}"
        using hwe \<open>{q} = e\<close> by (by100 simp)
      hence "w = q" by (by100 simp)
      thus False using hqw by (by100 blast)
    qed
    have hqrest: "{q} \<in> L - {{w}, e}"
      using hqL hq_ne_w hq_ne_e by (by100 simp)
    have "q \<in> geotop_polyhedron (L - {{w}, e})"
      unfolding geotop_polyhedron_def using hqrest by (by100 blast)
    show "x \<in> e \<inter> geotop_polyhedron (L - {{w}, e})"
      using hxq hqe \<open>q \<in> geotop_polyhedron (L - {{w}, e})\<close> by (by100 simp)
  qed
qed

lemma geotop_graph_endpoint_delete_leaf_neighbor_endpoint_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes hqL: "{q} \<in> L"
  assumes hqw: "q \<noteq> w"
  assumes hqe: "q \<in> e"
  assumes hqcard: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 2"
  shows "geotop_graph_endpoint (L - {{w}, e}) q"
proof -
  let ?S = "{l\<in>L. geotop_is_edge l \<and> q \<in> l}"
  let ?T = "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l}"
  have hrest_linear: "geotop_is_linear_graph (L - {{w}, e})"
    by (rule geotop_graph_endpoint_delete_leaf_linear_graph_dev34
        [OF hL hfin hend heL hedge hwe])
  have hq_ne_singleton: "{q} \<noteq> {w}"
    using hqw by (by100 blast)
  have hq_ne_e: "{q} \<noteq> e"
  proof
    assume hqe_single: "{q} = e"
    have "w \<in> {q}"
      using hwe hqe_single by (by100 simp)
    hence "w = q" by (by100 simp)
    thus False using hqw by (by100 blast)
  qed
  have hqrest: "{q} \<in> L - {{w}, e}"
    using hqL hq_ne_singleton hq_ne_e by (by100 simp)
  have heS: "e \<in> ?S"
    using heL hedge hqe by (by100 simp)
  have hfinS: "finite ?S"
    using hfin by (by100 simp)
  have hT_eq: "?T = ?S - {e}"
    by (rule geotop_delete_leaf_incident_edges_neighbor_eq_dev34[OF hqw])
  have hcard_minus: "card (?S - {e}) = card ?S - 1"
    using hfinS heS by (by100 simp)
  have hcard_T: "card ?T = 1"
    using hT_eq hcard_minus hqcard by (by100 simp)
  show ?thesis
    by (rule geotop_degree_one_vertex_graph_endpoint_dev34
        [OF hrest_linear hqrest hcard_T])
qed

lemma geotop_graph_endpoint_delete_leaf_degree_one_or_two_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes hqL: "{q} \<in> L"
  assumes hqw: "q \<noteq> w"
  assumes heq: "e = closed_segment w q"
  assumes hdegree12: "\<forall>x. {x} \<in> L \<longrightarrow>
      card {l\<in>L. geotop_is_edge l \<and> x \<in> l} = 1 \<or>
      card {l\<in>L. geotop_is_edge l \<and> x \<in> l} = 2"
  assumes hqcard: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 2"
  shows "\<forall>x. {x} \<in> L - {{w}, e} \<longrightarrow>
      card {l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l} = 1 \<or>
      card {l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l} = 2"
proof (intro allI impI)
  fix x
  assume hxrest: "{x} \<in> L - {{w}, e}"
  let ?Srest = "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}"
  let ?Sold = "{l\<in>L. geotop_is_edge l \<and> x \<in> l}"
  have hq_in_e: "q \<in> e"
    using heq by (by100 simp)
  show "card ?Srest = 1 \<or> card ?Srest = 2"
  proof (cases "x = q")
    case True
    have hrest_linear: "geotop_is_linear_graph (L - {{w}, e})"
      by (rule geotop_graph_endpoint_delete_leaf_linear_graph_dev34
          [OF hL hfin hend heL hedge hwe])
    have hq_endpoint: "geotop_graph_endpoint (L - {{w}, e}) q"
      by (rule geotop_graph_endpoint_delete_leaf_neighbor_endpoint_dev34
          [OF hL hfin hend heL hedge hwe hqL hqw hq_in_e hqcard])
    have hq_card: "card {l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l} = 1"
      using geotop_graph_endpoint_singleton_and_card_one_dev34[OF hrest_linear hq_endpoint]
      by (by100 blast)
    show ?thesis using True hq_card by (by100 simp)
  next
    case False
    have hcard_eq: "card ?Srest = card ?Sold"
      by (rule geotop_delete_leaf_rest_vertex_degree_preserved_away_neighbor_dev34
          [OF hL heL hqw heq hxrest False])
    have hxL: "{x} \<in> L"
      using hxrest by (by100 simp)
    have hdegree_x: "card ?Sold = 1 \<or> card ?Sold = 2"
      using hdegree12 hxL by (by100 blast)
    show ?thesis using hcard_eq hdegree_x by (by100 simp)
  qed
qed

lemma geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_HOL_arc_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hend: "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
  shows "\<exists>\<gamma>::real \<Rightarrow> real^2. arc \<gamma> \<and> path_image \<gamma> = geotop_polyhedron L"
  sorry

lemma geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_arc_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hend: "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
  shows "geotop_is_arc (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
proof -
  obtain \<gamma> :: "real \<Rightarrow> real^2"
    where h\<gamma>_arc: "arc \<gamma>" and h\<gamma>_pim: "path_image \<gamma> = geotop_polyhedron L"
    using geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_HOL_arc_dev34
      [OF hL hfin hconn hdegree12 hend]
    by (by100 blast)
  have hgeo_arc: "geotop_is_arc (path_image \<gamma>)
      (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>))"
    by (rule geotop_HOL_arc_imp_geotop_is_arc[OF h\<gamma>_arc])
  show ?thesis
    using hgeo_arc h\<gamma>_pim by (by100 simp)
qed

lemma geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_broken_line_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hend: "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
  shows "geotop_is_broken_line (geotop_polyhedron L)"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  have h1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_dev34[OF hL])
  have harc: "geotop_is_arc (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    by (rule geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_arc_dev34
        [OF hL hfin hconn hdegree12 hend])
  show ?thesis
    unfolding geotop_is_broken_line_def
    using hcomplex h1dim harc by (by100 blast)
qed

lemma geotop_finite_connected_degree_one_or_two_linear_graph_line_or_polygon_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "geotop_is_broken_line (geotop_polyhedron L) \<or>
      geotop_is_polygon (geotop_polyhedron L)"
proof -
  have hendpoint_or_noendpoint:
      "(\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w) \<or>
       (\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w)"
    by (by100 blast)
  show ?thesis
  proof (rule disjE[OF hendpoint_or_noendpoint])
    assume hend: "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
    have hline: "geotop_is_broken_line (geotop_polyhedron L)"
      by (rule geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_broken_line_dev34
          [OF hL hfin hconn hdegree12 hend])
    show ?thesis
      using hline by (by100 blast)
  next
    assume hnoend: "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
    have hdegree2: "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule geotop_degree_one_or_two_no_endpoint_degree_two_dev34
          [OF hL hdegree12 hnoend])
    have hpoly: "geotop_is_polygon (geotop_polyhedron L)"
      by (rule geotop_finite_connected_degree_two_linear_graph_polygon_dev34
          [OF hL hfin hconn hdegree2])
    show ?thesis
      using hpoly by (by100 blast)
  qed
qed

end
