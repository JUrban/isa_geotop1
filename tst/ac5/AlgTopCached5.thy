theory AlgTopCached5
  imports "AlgTopCached4.AlgTopCached4"
begin

text \<open>Helper: a convex subset of reals (with the standard subspace topology) is path-connected.
  This is needed for showing components of covering preimages over arcs are path-connected.\<close>
lemma convex_real_subspace_path_connected:
  assumes hS_ne: "S \<noteq> {}"
      and hS_conv: "\<And>x y t. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> 0 \<le> t \<Longrightarrow> t \<le> 1
          \<Longrightarrow> (1 - t) * x + t * (y::real) \<in> S"
  shows "top1_path_connected_on S (subspace_topology (UNIV::real set) top1_open_sets S)"
  unfolding top1_path_connected_on_def
proof (intro conjI ballI)
  show "is_topology_on S (subspace_topology (UNIV::real set) top1_open_sets S)"
    by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV subset_UNIV])
next
  fix x y assume hx: "x \<in> S" and hy: "y \<in> S"
  let ?f = "\<lambda>t::real. (1 - t) * x + t * y"
  have hf_range: "\<forall>t\<in>top1_unit_interval. ?f t \<in> S"
    using hS_conv[OF hx hy] unfolding top1_unit_interval_def by (by100 auto)
  have hf_cont: "continuous_on top1_unit_interval ?f"
    by (intro continuous_intros)
  from top1_continuous_map_on_subspace_open_sets_on[OF _ hf_cont] hf_range
  have hf_cont2: "top1_continuous_map_on top1_unit_interval
      (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval)
      S (subspace_topology (UNIV::real set) top1_open_sets S) ?f"
    by (by100 blast)
  have hf_top: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
      S (subspace_topology (UNIV::real set) top1_open_sets S) ?f"
    using hf_cont2 unfolding top1_unit_interval_topology_def by (by100 simp)
  have "?f 0 = x" by (by100 simp)
  moreover have "?f 1 = y" by (by100 simp)
  ultimately show "\<exists>f. top1_is_path_on S (subspace_topology (UNIV::real set) top1_open_sets S) x y f"
    unfolding top1_is_path_on_def using hf_top by (by100 blast)
qed

text \<open>Helper: the total space of a covering of an arc has path-connected evenly covered sheets.
  Specifically, every point in the preimage has a path-connected open neighborhood.\<close>
lemma covering_sheet_over_arc_path_connected:
  assumes hcov: "top1_covering_map_on E0 TE0 A TA p"
      and harc: "top1_is_arc_on A TA"
      and hTE0: "is_topology_on E0 TE0"
      and hTA: "is_topology_on A TA"
      and he: "e \<in> E0"
  shows "\<exists>W. W \<subseteq> E0 \<and> openin_on E0 TE0 W \<and> e \<in> W
      \<and> top1_path_connected_on W (subspace_topology E0 TE0 W)
      \<and> top1_homeomorphism_on W (subspace_topology E0 TE0 W) (p ` W) (subspace_topology A TA (p ` W)) p
      \<and> top1_evenly_covered_on E0 TE0 A TA p (p ` W)"
proof -
  \<comment> \<open>Step 1: Get arc homeomorphism h: [0,1] \<rightarrow> A.\<close>
  obtain h_arc where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology A TA h_arc"
    using harc unfolding top1_is_arc_on_def by (by100 blast)
  have hh_bij: "bij_betw h_arc top1_unit_interval A"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology A TA h_arc"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  let ?h_inv = "inv_into top1_unit_interval h_arc"
  have hh_inv_cont: "top1_continuous_map_on A TA top1_unit_interval top1_unit_interval_topology ?h_inv"
    using hh unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh_inv_bij: "bij_betw ?h_inv A top1_unit_interval"
    using bij_betw_inv_into[OF hh_bij] .
  \<comment> \<open>Step 2: p(e) \<in> A. Get evenly covered neighborhood U0 of p(e).\<close>
  have hpe: "p e \<in> A"
    using hcov he unfolding top1_covering_map_on_def by (by100 blast)
  obtain U0 where hU0_pe: "p e \<in> U0"
      and hU0_ev: "top1_evenly_covered_on E0 TE0 A TA p U0"
    using hcov hpe unfolding top1_covering_map_on_def by (by100 blast)
  \<comment> \<open>Get sheets.\<close>
  obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E0 TE0 V"
      and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
      and hV_union: "{x \<in> E0. p x \<in> U0} = \<Union>\<V>"
      and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E0 TE0 V) U0 (subspace_topology A TA U0) p"
    using hU0_ev unfolding top1_evenly_covered_on_def
    apply (elim conjE exE)
    apply (rule that)
    apply (by100 blast)+
    done
  \<comment> \<open>Get the sheet V containing e.\<close>
  have "e \<in> {x \<in> E0. p x \<in> U0}" using he hU0_pe by (by100 blast)
  hence "e \<in> \<Union>\<V>" using hV_union by (by100 simp)
  then obtain V where hV: "V \<in> \<V>" "e \<in> V" by (by100 blast)
  have hV_sub: "V \<subseteq> E0"
    using hV_open hV(1) unfolding openin_on_def by (by100 blast)
  \<comment> \<open>Step 3: Find path-connected open sub-neighborhood in A.\<close>
  \<comment> \<open>h\_inv(U0) is open in [0,1]. Take a convex interval around h\_inv(p(e)).\<close>
  have hU0_open_A: "openin_on A TA U0"
    using hU0_ev unfolding top1_evenly_covered_on_def by (by100 blast)
  have hU0_sub_A: "U0 \<subseteq> A"
    using hU0_open_A unfolding openin_on_def by (by100 blast)
  \<comment> \<open>h\_inv(p(e)) \<in> [0,1]. h\_inv(U0) is open in [0,1].\<close>
  let ?a0 = "?h_inv (p e)"
  have ha0_I: "?a0 \<in> top1_unit_interval"
    using bij_betw_apply[OF hh_inv_bij hpe] .
  \<comment> \<open>h\_inv is continuous, so preimage of U0 under h\_arc is open in [0,1].\<close>
  \<comment> \<open>Equivalently: h\_inv(U0) is open in [0,1] because h\_inv is continuous and U0 is open.\<close>
  \<comment> \<open>Actually: preimage of U0 under h\_arc = {t \<in> I. h\_arc t \<in> U0}.\<close>
  let ?pre_U0 = "{t \<in> top1_unit_interval. h_arc t \<in> U0}"
  have hpre_open: "?pre_U0 \<in> top1_unit_interval_topology"
  proof -
    have "U0 \<in> TA"
      using hU0_open_A unfolding openin_on_def by (by100 blast)
    from hh_cont this show ?thesis
      unfolding top1_continuous_map_on_def by (by100 blast)
  qed
  have ha0_pre: "?a0 \<in> ?pre_U0"
  proof -
    have "h_arc ` top1_unit_interval = A" using hh_bij unfolding bij_betw_def by (by100 blast)
    hence "p e \<in> h_arc ` top1_unit_interval" using hpe by (by100 simp)
    have "h_arc ?a0 = p e"
      by (rule f_inv_into_f[OF \<open>p e \<in> h_arc ` top1_unit_interval\<close>])
    hence "h_arc ?a0 \<in> U0" using hU0_pe by (by100 simp)
    thus ?thesis using ha0_I by (by100 blast)
  qed
  \<comment> \<open>?pre\_U0 is open in [0,1]. [0,1] has subspace topology from R.
     So ?pre\_U0 = V0 \<inter> [0,1] for some open V0 \<subseteq> R.
     Since V0 is open and ?a0 \<in> V0, there exists \<epsilon> > 0 with ball(?a0, \<epsilon>) \<subseteq> V0.\<close>
  have "\<exists>\<epsilon>::real. \<epsilon> > 0 \<and> (\<forall>t. \<bar>t - ?a0\<bar> < \<epsilon> \<and> t \<in> top1_unit_interval \<longrightarrow> t \<in> ?pre_U0)"
  proof -
    \<comment> \<open>?pre\_U0 \<in> top1\_unit\_interval\_topology = subspace\_topology UNIV top1\_open\_sets [0,1].\<close>
    \<comment> \<open>So ?pre\_U0 = V0 \<inter> [0,1] for some V0 with open V0.\<close>
    from hpre_open obtain V0 where hV0: "open V0" "?pre_U0 = V0 \<inter> top1_unit_interval"
      unfolding top1_unit_interval_topology_def subspace_topology_def top1_open_sets_def
      by (by5000 blast)
    have "?a0 \<in> V0" using ha0_pre hV0(2) by (by100 blast)
    from \<open>open V0\<close> have "\<forall>x\<in>V0. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> V0"
      unfolding open_dist by (by100 blast)
    from this[rule_format, OF \<open>?a0 \<in> V0\<close>]
    obtain \<epsilon> where heps: "\<epsilon> > 0" "\<forall>y. dist y ?a0 < \<epsilon> \<longrightarrow> y \<in> V0" by (by100 blast)
    have "\<forall>t. \<bar>t - ?a0\<bar> < \<epsilon> \<and> t \<in> top1_unit_interval \<longrightarrow> t \<in> ?pre_U0"
    proof (intro allI impI)
      fix t assume ht: "\<bar>t - ?a0\<bar> < \<epsilon> \<and> t \<in> top1_unit_interval"
      have "dist t ?a0 < \<epsilon>" using ht unfolding dist_real_def by (by100 simp)
      hence "t \<in> V0" using heps(2) by (by100 blast)
      thus "t \<in> ?pre_U0" using ht hV0(2) by (by100 blast)
    qed
    thus ?thesis using heps(1) by (by100 blast)
  qed
  then obtain \<epsilon> where heps: "\<epsilon> > 0"
      and heps_pre: "\<forall>t. \<bar>t - ?a0\<bar> < \<epsilon> \<and> t \<in> top1_unit_interval \<longrightarrow> t \<in> ?pre_U0"
    by (by100 blast)
  \<comment> \<open>Define the interval I = {t \<in> [0,1]. |t - a0| < \<epsilon>}. I is convex.\<close>
  let ?I_eps = "{t \<in> top1_unit_interval. \<bar>t - ?a0\<bar> < \<epsilon>}"
  have hI_sub_pre: "?I_eps \<subseteq> ?pre_U0" using heps_pre by (by100 blast)
  have hI_ne: "?I_eps \<noteq> {}" using ha0_I heps by (by100 auto)
  have hI_conv: "\<And>x y t. x \<in> ?I_eps \<Longrightarrow> y \<in> ?I_eps \<Longrightarrow> 0 \<le> t \<Longrightarrow> t \<le> 1
      \<Longrightarrow> (1 - t) * x + t * y \<in> ?I_eps"
  proof -
    fix x y t :: real
    assume hx: "x \<in> ?I_eps" and hy: "y \<in> ?I_eps" and ht0: "0 \<le> t" and ht1: "t \<le> 1"
    from hx have hx_I: "x \<in> top1_unit_interval" and hx_abs: "\<bar>x - ?a0\<bar> < \<epsilon>" by (by100 blast)+
    from hy have hy_I: "y \<in> top1_unit_interval" and hy_abs: "\<bar>y - ?a0\<bar> < \<epsilon>" by (by100 blast)+
    have hx01: "0 \<le> x" "x \<le> 1" using hx_I unfolding top1_unit_interval_def by (by100 auto)+
    have hy01: "0 \<le> y" "y \<le> 1" using hy_I unfolding top1_unit_interval_def by (by100 auto)+
    let ?z = "(1 - t) * x + t * y"
    have "0 \<le> (1 - t)" using ht1 by (by100 linarith)
    have hz_ge: "0 \<le> ?z"
      using mult_nonneg_nonneg[OF \<open>0 \<le> 1 - t\<close> hx01(1)] mult_nonneg_nonneg[OF ht0 hy01(1)]
      by (by100 linarith)
    have "(1 - t) * x \<le> (1 - t) * 1" using mult_left_mono[OF hx01(2) \<open>0 \<le> 1 - t\<close>] .
    have "t * y \<le> t * 1" using mult_left_mono[OF hy01(2) ht0] .
    have "(1 - t) * 1 + t * 1 = (1::real)" by (by100 algebra)
    have hz_le: "?z \<le> 1"
      using \<open>(1-t)*x \<le> (1-t)*1\<close> \<open>t*y \<le> t*1\<close> \<open>(1-t)*1 + t*1 = 1\<close> by (by100 linarith)
    have hz_I: "?z \<in> top1_unit_interval"
      unfolding top1_unit_interval_def using hz_ge hz_le by (by100 auto)
    have "?z - ?a0 = (1 - t) * (x - ?a0) + t * (y - ?a0)" by (by100 algebra)
    have "\<bar>?z - ?a0\<bar> \<le> (1 - t) * \<bar>x - ?a0\<bar> + t * \<bar>y - ?a0\<bar>"
    proof -
      have "\<bar>(1 - t) * (x - ?a0) + t * (y - ?a0)\<bar>
          \<le> \<bar>(1 - t) * (x - ?a0)\<bar> + \<bar>t * (y - ?a0)\<bar>"
        by (rule abs_triangle_ineq)
      also have "\<bar>(1 - t) * (x - ?a0)\<bar> = (1 - t) * \<bar>x - ?a0\<bar>"
      proof -
        have "\<bar>(1 - t) * (x - ?a0)\<bar> = \<bar>1 - t\<bar> * \<bar>x - ?a0\<bar>" by (rule abs_mult)
        also have "\<bar>1 - t\<bar> = 1 - t" using abs_of_nonneg[OF \<open>0 \<le> 1 - t\<close>] .
        finally show ?thesis .
      qed
      also have "\<bar>t * (y - ?a0)\<bar> = t * \<bar>y - ?a0\<bar>"
      proof -
        have "\<bar>t * (y - ?a0)\<bar> = \<bar>t\<bar> * \<bar>y - ?a0\<bar>" by (rule abs_mult)
        also have "\<bar>t\<bar> = t" using abs_of_nonneg[OF ht0] .
        finally show ?thesis .
      qed
      finally show ?thesis using \<open>?z - ?a0 = _\<close> by (by5000 linarith)
    qed
    also have "... < (1 - t) * \<epsilon> + t * \<epsilon>"
    proof (cases "t = 0")
      case True
      thus ?thesis using hx_abs by (by100 simp)
    next
      case False
      hence ht_pos: "0 < t" using ht0 by (by100 linarith)
      show ?thesis
      proof (cases "t = 1")
        case True
        thus ?thesis using hy_abs by (by100 simp)
      next
        case False
        hence "0 < 1 - t" using ht1 by (by100 linarith)
        have h1: "(1 - t) * \<bar>x - ?a0\<bar> < (1 - t) * \<epsilon>"
          using \<open>0 < 1 - t\<close> hx_abs by (by100 simp)
        have h2: "t * \<bar>y - ?a0\<bar> < t * \<epsilon>"
          using ht_pos hy_abs by (by100 simp)
        from h1 h2 show ?thesis by (by100 linarith)
      qed
    qed
    also have "... = \<epsilon>"
    proof -
      have "(1 - t) * \<epsilon> + t * \<epsilon> = (1 - t + t) * \<epsilon>"
        apply (simp only: distrib_right)
        done
      also have "1 - t + t = (1::real)" by (by100 simp)
      finally show ?thesis by (by100 simp)
    qed
    finally have "\<bar>?z - ?a0\<bar> < \<epsilon>" .
    show "?z \<in> ?I_eps" using hz_I \<open>\<bar>?z - ?a0\<bar> < \<epsilon>\<close> by (by100 blast)
  qed
  have hI_sub_I: "?I_eps \<subseteq> top1_unit_interval" by (by100 blast)
  \<comment> \<open>I is path-connected.\<close>
  have hI_pc: "top1_path_connected_on ?I_eps
      (subspace_topology (UNIV::real set) top1_open_sets ?I_eps)"
    by (rule convex_real_subspace_path_connected[OF hI_ne hI_conv])
  \<comment> \<open>Step 4: h\_arc(I) is the path-connected open sub-neighborhood of p(e) in U0.\<close>
  let ?U' = "h_arc ` ?I_eps"
  have hU'_pc: "top1_path_connected_on ?U' (subspace_topology A TA ?U')"
  proof -
    \<comment> \<open>I\_eps is path-connected. h\_arc restricted to I\_eps is continuous.
       Use top1\_path\_connected\_continuous\_image.\<close>
    have hI_sub_UI: "?I_eps \<subseteq> top1_unit_interval" by (by100 blast)
    have hI_top_eq: "subspace_topology (UNIV::real set) top1_open_sets ?I_eps
        = subspace_topology top1_unit_interval top1_unit_interval_topology ?I_eps"
      using subspace_topology_trans[OF hI_sub_UI] unfolding top1_unit_interval_topology_def by (by100 simp)
    have hI_pc2: "top1_path_connected_on ?I_eps
        (subspace_topology top1_unit_interval top1_unit_interval_topology ?I_eps)"
      using hI_pc hI_top_eq by (by100 simp)
    \<comment> \<open>h\_arc is continuous from [0,1] to A.\<close>
    \<comment> \<open>h\_arc maps ?I\_eps into A (since ?I\_eps \<subseteq> [0,1] and h\_arc: [0,1] \<rightarrow> A).\<close>
    have hh_range: "\<forall>t \<in> ?I_eps. h_arc t \<in> A"
      using bij_betw_apply[OF hh_bij] by (by100 blast)
    have hh_img: "h_arc ` ?I_eps = ?U'" by (by100 blast)
    have hU'_sub_A: "?U' \<subseteq> A" using hh_range by (by100 blast)
    have hh_cont_I: "top1_continuous_map_on ?I_eps
        (subspace_topology top1_unit_interval top1_unit_interval_topology ?I_eps) A TA h_arc"
      by (rule top1_continuous_map_on_subspace_restrict[OF hh_cont hI_sub_UI])
    have "subspace_topology A TA ?U' = subspace_topology A TA (h_arc ` ?I_eps)" by (by100 simp)
    from top1_path_connected_continuous_image[OF hI_pc2 hh_cont_I hh_range hh_img hU'_sub_A this hTA]
    show ?thesis .
  qed
  have hU'_sub_U0: "?U' \<subseteq> U0"
  proof (intro subsetI)
    fix a assume "a \<in> ?U'"
    then obtain t where ht: "t \<in> ?I_eps" "a = h_arc t" by (by100 blast)
    from ht(1) have "t \<in> ?pre_U0" using hI_sub_pre by (by100 blast)
    hence "h_arc t \<in> U0" by (by100 blast)
    thus "a \<in> U0" using ht(2) by (by100 simp)
  qed
  have hU'_open_A: "openin_on A TA ?U'"
  proof -
    \<comment> \<open>I\_eps is open in [0,1].\<close>
    have hI_open: "openin_on top1_unit_interval top1_unit_interval_topology ?I_eps"
    proof -
      \<comment> \<open>?I\_eps = ball(?a0, \<epsilon>) \<inter> [0,1]. ball is open in R. So ?I\_eps is open in [0,1].\<close>
      have "{t. \<bar>t - ?a0\<bar> < \<epsilon>} \<in> top1_open_sets"
      proof -
        have "open {t::real. \<bar>t - ?a0\<bar> < \<epsilon>}"
        proof -
          have "\<forall>x\<in>{t::real. \<bar>t - ?a0\<bar> < \<epsilon>}. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> {t. \<bar>t - ?a0\<bar> < \<epsilon>}"
          proof (intro ballI)
            fix x :: real assume "x \<in> {t. \<bar>t - ?a0\<bar> < \<epsilon>}"
            hence hx: "\<bar>x - ?a0\<bar> < \<epsilon>" by (by100 blast)
            let ?e = "\<epsilon> - \<bar>x - ?a0\<bar>"
            have "?e > 0" using hx by (by100 linarith)
            have "\<forall>y. dist y x < ?e \<longrightarrow> y \<in> {t::real. \<bar>t - ?a0\<bar> < \<epsilon>}"
            proof (intro allI impI)
              fix y :: real assume "dist y x < ?e"
              hence "\<bar>y - x\<bar> < ?e" unfolding dist_real_def by (by100 simp)
              have "\<bar>y - ?a0\<bar> \<le> \<bar>y - x\<bar> + \<bar>x - ?a0\<bar>" by (by100 linarith)
              have "\<bar>y - ?a0\<bar> < \<epsilon>" using \<open>\<bar>y - ?a0\<bar> \<le> _\<close> \<open>\<bar>y - x\<bar> < ?e\<close> by (by100 linarith)
              thus "y \<in> {t. \<bar>t - ?a0\<bar> < \<epsilon>}" by (by100 blast)
            qed
            thus "\<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> {t::real. \<bar>t - ?a0\<bar> < \<epsilon>}"
              using \<open>?e > 0\<close> by (by100 blast)
          qed
          thus ?thesis unfolding open_dist by (by100 blast)
        qed
        thus ?thesis unfolding top1_open_sets_def by (by100 blast)
      qed
      hence "{t. \<bar>t - ?a0\<bar> < \<epsilon>} \<inter> top1_unit_interval \<in> top1_unit_interval_topology"
        unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
      moreover have "?I_eps = {t. \<bar>t - ?a0\<bar> < \<epsilon>} \<inter> top1_unit_interval" by (by100 blast)
      ultimately have "?I_eps \<in> top1_unit_interval_topology" by (by100 simp)
      moreover have "?I_eps \<subseteq> top1_unit_interval" by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by (by100 blast)
    qed
    \<comment> \<open>h\_arc maps open sets in [0,1] to open sets in A (homeomorphism = open map).\<close>
    have "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology A TA h_arc"
      using hh .
    \<comment> \<open>The inverse of h\_arc is continuous from A to [0,1]. So h\_arc is an open map.\<close>
    \<comment> \<open>h\_arc(I\_eps) = {a \<in> A. h\_inv(a) \<in> I\_eps}.\<close>
    have "?U' = {a \<in> A. ?h_inv a \<in> ?I_eps}"
    proof (rule set_eqI, rule iffI)
      fix a assume "a \<in> ?U'"
      then obtain t where ht: "t \<in> ?I_eps" "a = h_arc t" by (by100 blast)
      have "t \<in> top1_unit_interval" using ht(1) by (by100 blast)
      have "a \<in> A" using ht(2) bij_betw_apply[OF hh_bij \<open>t \<in> top1_unit_interval\<close>] by (by100 simp)
      have "?h_inv a = t"
        using inv_into_f_f[OF bij_betw_imp_inj_on[OF hh_bij] \<open>t \<in> top1_unit_interval\<close>]
            ht(2) by (by100 simp)
      thus "a \<in> {a \<in> A. ?h_inv a \<in> ?I_eps}" using \<open>a \<in> A\<close> ht(1) by (by100 simp)
    next
      fix a assume "a \<in> {a \<in> A. ?h_inv a \<in> ?I_eps}"
      hence ha: "a \<in> A" "?h_inv a \<in> ?I_eps" by (by100 blast)+
      have "h_arc ` top1_unit_interval = A" using hh_bij unfolding bij_betw_def by (by100 blast)
      have "a \<in> h_arc ` top1_unit_interval" using ha(1) \<open>h_arc ` top1_unit_interval = A\<close> by (by100 simp)
      have "h_arc (?h_inv a) = a" by (rule f_inv_into_f[OF \<open>a \<in> h_arc ` top1_unit_interval\<close>])
      hence "a = h_arc (?h_inv a)" by (by100 simp)
      thus "a \<in> ?U'" using ha(2) by (by100 force)
    qed
    \<comment> \<open>The preimage of ?I\_eps under ?h\_inv is open in A (since ?h\_inv is continuous and ?I\_eps is open in [0,1]).\<close>
    have "{a \<in> A. ?h_inv a \<in> ?I_eps} \<in> TA"
    proof -
      have "?I_eps \<in> top1_unit_interval_topology" using hI_open unfolding openin_on_def by (by100 blast)
      from hh_inv_cont this show ?thesis
        unfolding top1_continuous_map_on_def by (by100 blast)
    qed
    have "?U' \<subseteq> A"
    proof (intro subsetI)
      fix a assume "a \<in> ?U'"
      then obtain t where ht: "t \<in> ?I_eps" "a = h_arc t" by (by100 blast)
      have "t \<in> top1_unit_interval" using ht(1) by (by100 blast)
      from bij_betw_apply[OF hh_bij this] show "a \<in> A" using ht(2) by (by100 simp)
    qed
    moreover have "?U' \<in> TA"
      using \<open>{a \<in> A. ?h_inv a \<in> ?I_eps} \<in> TA\<close> \<open>?U' = {a \<in> A. ?h_inv a \<in> ?I_eps}\<close> by (by100 simp)
    ultimately show ?thesis unfolding openin_on_def by (by100 blast)
  qed
  have hpe_U': "p e \<in> ?U'"
  proof -
    have "h_arc ` top1_unit_interval = A" using hh_bij unfolding bij_betw_def by (by100 blast)
    hence "p e \<in> h_arc ` top1_unit_interval" using hpe by (by100 simp)
    have "h_arc ?a0 = p e" by (rule f_inv_into_f[OF \<open>p e \<in> h_arc ` top1_unit_interval\<close>])
    moreover have "?a0 \<in> ?I_eps"
    proof -
      have "?a0 \<in> top1_unit_interval" using ha0_I .
      moreover have "\<bar>?a0 - ?a0\<bar> < \<epsilon>" using heps by (by100 simp)
      ultimately show ?thesis by (by100 blast)
    qed
    ultimately show "p e \<in> h_arc ` ?I_eps"
    proof -
      assume h1: "h_arc ?a0 = p e" and h2: "?a0 \<in> ?I_eps"
      from h2 have "h_arc ?a0 \<in> h_arc ` ?I_eps" by (rule imageI)
      thus "p e \<in> h_arc ` ?I_eps" using h1 by (by100 simp)
    qed
  qed
  \<comment> \<open>Step 5: Restrict evenly covered to U'. Get sheet W containing e.\<close>
  have hU'_ev: "top1_evenly_covered_on E0 TE0 A TA p ?U'"
    by (rule evenly_covered_open_subset[OF hU0_ev hU'_open_A hU'_sub_U0 hTE0 hTA])
  obtain \<W> where hW_open: "\<forall>W\<in>\<W>. openin_on E0 TE0 W"
      and hW_disj: "\<forall>W\<in>\<W>. \<forall>W'\<in>\<W>. W \<noteq> W' \<longrightarrow> W \<inter> W' = {}"
      and hW_union: "{x \<in> E0. p x \<in> ?U'} = \<Union>\<W>"
      and hW_homeo: "\<forall>W\<in>\<W>. top1_homeomorphism_on W (subspace_topology E0 TE0 W)
          ?U' (subspace_topology A TA ?U') p"
    using hU'_ev unfolding top1_evenly_covered_on_def
    apply (elim conjE exE)
    apply (rule that)
    apply (by100 blast)+
    done
  have "e \<in> {x \<in> E0. p x \<in> ?U'}" using he hpe_U' by (by100 blast)
  hence "e \<in> \<Union>\<W>" using hW_union by (by100 simp)
  then obtain W where hW: "W \<in> \<W>" "e \<in> W" by (by100 blast)
  have hW_sub: "W \<subseteq> E0" using hW_open hW(1) unfolding openin_on_def by (by100 blast)
  \<comment> \<open>Step 6: W is path-connected (homeomorphic to U').\<close>
  have hW_homeo_U': "top1_homeomorphism_on W (subspace_topology E0 TE0 W) ?U' (subspace_topology A TA ?U') p"
    using hW_homeo hW(1) by (by100 blast)
  \<comment> \<open>For homeomorphism_preserves_path_connected, we need the reverse direction:
     U' path-connected \<Rightarrow> W path-connected. Use inverse homeomorphism.\<close>
  have hW_pc: "top1_path_connected_on W (subspace_topology E0 TE0 W)"
  proof -
    \<comment> \<open>p|\_W: W \<rightarrow> U' is a homeomorphism, so inv\_into W p: U' \<rightarrow> W is also a homeomorphism.\<close>
    have "top1_homeomorphism_on ?U' (subspace_topology A TA ?U') W (subspace_topology E0 TE0 W) (inv_into W p)"
      by (rule homeomorphism_inverse[OF hW_homeo_U'])
    from homeomorphism_preserves_path_connected[OF this hU'_pc] show ?thesis .
  qed
  \<comment> \<open>Export: p maps W homeomorphically onto p(W) = ?U', and ?U' is evenly covered.\<close>
  have hpW_eq: "p ` W = ?U'"
    using hW_homeo_U' unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have hW_homeo_pW: "top1_homeomorphism_on W (subspace_topology E0 TE0 W) (p ` W) (subspace_topology A TA (p ` W)) p"
    using hW_homeo_U' hpW_eq by (by100 simp)
  have hpW_ev: "top1_evenly_covered_on E0 TE0 A TA p (p ` W)"
    using hU'_ev hpW_eq by (by100 simp)
  show ?thesis
    apply (rule exI[of _ W])
    using hW_sub hW_open hW(1) hW(2) hW_pc hW_homeo_pW hpW_ev unfolding openin_on_def by (by100 blast)
qed

text \<open>Helper: a maximal connected component of the covering preimage over an arc is path-connected.\<close>
lemma covering_component_over_arc_path_connected:
  assumes "top1_covering_map_on E0 TE0 A TA p"
      and "top1_is_arc_on A TA"
      and "is_topology_on E0 TE0"
      and "is_topology_on A TA"
      and "top1_max_conn_comp E0 TE0 B'"
  shows "top1_path_connected_on B' (subspace_topology E0 TE0 B')"
proof -
  have hB'_ne: "B' \<noteq> {}" using max_conn_comp_ne[OF assms(5)] .
  have hB'_sub: "B' \<subseteq> E0" using max_conn_comp_sub[OF assms(5)] .
  have hB'_conn: "top1_connected_on B' (subspace_topology E0 TE0 B')"
    using assms(5) unfolding top1_max_conn_comp_def by (by100 blast)
  have hB'_max: "\<And>C. C \<supseteq> B' \<Longrightarrow> C \<subseteq> E0 \<Longrightarrow> top1_connected_on C (subspace_topology E0 TE0 C) \<Longrightarrow> C = B'"
    using assms(5) unfolding top1_max_conn_comp_def by (by100 blast)
  \<comment> \<open>Clopen approach: define the path-reachable set from some e1 \<in> B'.
     Show it is both open and closed in E0. Then B' \<subseteq> reachable set.
     Every path from e1 to x stays in B' (connected image meets B' at e1, maximality).\<close>
  obtain e1 where he1: "e1 \<in> B'" using hB'_ne by (by100 blast)
  have he1_E0: "e1 \<in> E0" using he1 hB'_sub by (by100 blast)
  \<comment> \<open>Sheet-in-component: for any e \<in> B', the covering sheet W at e is contained in B'.\<close>
  have hsheet_in_B': "\<And>e. e \<in> B' \<Longrightarrow>
      \<exists>W. W \<subseteq> B' \<and> openin_on E0 TE0 W \<and> e \<in> W
        \<and> top1_path_connected_on W (subspace_topology E0 TE0 W)"
  proof -
    fix e assume he: "e \<in> B'"
    have he_E0: "e \<in> E0" using he hB'_sub by (by100 blast)
    from covering_sheet_over_arc_path_connected[OF assms(1) assms(2) assms(3) assms(4) he_E0]
    obtain W where hW_sub: "W \<subseteq> E0" and hW_open: "openin_on E0 TE0 W"
        and hW_e: "e \<in> W"
        and hW_pc: "top1_path_connected_on W (subspace_topology E0 TE0 W)"
      by (by100 blast)
    have hW_conn: "top1_connected_on W (subspace_topology E0 TE0 W)"
      by (rule path_connected_imp_connected[OF hW_pc])
    \<comment> \<open>W \<subseteq> B' by maximality of B' (W connected, meets B' at e).\<close>
    have "W \<subseteq> B'"
    proof -
      have hWB_sub: "W \<union> B' \<subseteq> E0" using hW_sub hB'_sub by (by100 blast)
      have hWB_conn: "top1_connected_on (W \<union> B') (subspace_topology E0 TE0 (W \<union> B'))"
      proof -
        let ?A = "\<lambda>b::bool. if b then W else B'"
        have hI_ne: "{True, False} \<noteq> ({}::bool set)" by (by100 blast)
        have hA_sub: "\<forall>i\<in>{True, False}. ?A i \<subseteq> E0"
          using hW_sub hB'_sub by (by100 auto)
        have hA_conn: "\<forall>i\<in>{True, False}. top1_connected_on (?A i) (subspace_topology E0 TE0 (?A i))"
          using hW_conn hB'_conn by (by100 auto)
        have hp: "e \<in> \<Inter>(?A ` {True, False})"
          using hW_e he by (by100 auto)
        have hY: "W \<union> B' = (\<Union>i\<in>{True, False}. ?A i)" by (by100 auto)
        from Theorem_23_3[OF assms(3) hI_ne hA_sub hA_conn hp]
        have "top1_connected_on (\<Union>i\<in>{True, False}. ?A i)
            (subspace_topology E0 TE0 (\<Union>i\<in>{True, False}. ?A i))" .
        thus ?thesis using hY by (by100 simp)
      qed
      from hB'_max[OF _ hWB_sub hWB_conn] show "W \<subseteq> B'" by (by100 blast)
    qed
    thus "\<exists>W. W \<subseteq> B' \<and> openin_on E0 TE0 W \<and> e \<in> W
        \<and> top1_path_connected_on W (subspace_topology E0 TE0 W)"
      using hW_open hW_e hW_pc by (by100 blast)
  qed
  \<comment> \<open>For any x \<in> B', there is a path from e1 to x in B'.\<close>
  show ?thesis unfolding top1_path_connected_on_def
  proof (intro conjI ballI)
    show "is_topology_on B' (subspace_topology E0 TE0 B')"
      by (rule subspace_topology_is_topology_on[OF assms(3) hB'_sub])
  next
    fix x y assume hx: "x \<in> B'" and hy: "y \<in> B'"
    \<comment> \<open>Show: \<exists>f. path from x to y in B'.
       Strategy: the set R = {e \<in> B'. \<exists> path from e1 to e in B'} is clopen in B'.
       Since B' is connected and R \<ni> e1 is nonempty: R = B'.
       Then x, y \<in> R, concatenate paths via e1.\<close>
    let ?R = "{e \<in> B'. \<exists>f. top1_is_path_on B' (subspace_topology E0 TE0 B') e1 e f}"
    have hB'_top: "is_topology_on B' (subspace_topology E0 TE0 B')"
      by (rule subspace_topology_is_topology_on[OF assms(3) hB'_sub])
    \<comment> \<open>e1 \<in> R (constant path).\<close>
    have he1_R: "e1 \<in> ?R"
    proof -
      have "top1_is_path_on B' (subspace_topology E0 TE0 B') e1 e1 (top1_constant_path e1)"
        by (rule top1_constant_path_is_path[OF hB'_top he1])
      thus ?thesis using he1 by (by100 blast)
    qed
    \<comment> \<open>For any e \<in> B', the sheet W at e is open in B', path-connected, and W \<subseteq> B'.
       If e \<in> R: all of W is in R (paths from e1 \<rightarrow> e \<rightarrow> w for w \<in> W).
       If e \<notin> R: all of W is not in R (if w \<in> W \<inter> R, path e1 \<rightarrow> w \<rightarrow> e puts e in R).\<close>
    have hR_eq_B': "?R = B'"
    proof (rule ccontr)
      assume hne: "?R \<noteq> B'"
      have hR_sub: "?R \<subseteq> B'" by (by100 blast)
      hence hR_strict: "B' - ?R \<noteq> {}" using hne by (by100 blast)
      \<comment> \<open>Take e0 \<in> B' \\ R.\<close>
      obtain e0 where he0: "e0 \<in> B'" "e0 \<notin> ?R" using hR_strict by (by100 blast)
      \<comment> \<open>Get a sheet W0 at e0.\<close>
      from hsheet_in_B'[OF he0(1)] obtain W0 where
          hW0_sub: "W0 \<subseteq> B'" and hW0_open: "openin_on E0 TE0 W0" and hW0_e0: "e0 \<in> W0"
          and hW0_pc: "top1_path_connected_on W0 (subspace_topology E0 TE0 W0)"
        by (by100 blast)
      \<comment> \<open>W0 \<inter> R = {}: if w \<in> W0 \<inter> R, then path e1 \<rightarrow> w in B' + path w \<rightarrow> e0 in W0 \<subseteq> B'
         gives path e1 \<rightarrow> e0 in B', contradicting e0 \<notin> R.\<close>
      have hW0_disj_R: "W0 \<inter> ?R = {}"
      proof (rule ccontr)
        assume "W0 \<inter> ?R \<noteq> {}"
        then obtain w where hw: "w \<in> W0" "w \<in> ?R" by (by100 blast)
        from hw(2) obtain fw where hfw: "w \<in> B'"
            "top1_is_path_on B' (subspace_topology E0 TE0 B') e1 w fw"
          by (by100 blast)
        \<comment> \<open>Path from w to e0 in W0 (W0 path-connected).\<close>
        have "w \<in> W0" "e0 \<in> W0" using hw(1) hW0_e0 by (by100 blast)+
        from hW0_pc have "\<exists>g. top1_is_path_on W0 (subspace_topology E0 TE0 W0) w e0 g"
          using \<open>w \<in> W0\<close> \<open>e0 \<in> W0\<close> unfolding top1_path_connected_on_def by (by100 blast)
        then obtain gw where hgw: "top1_is_path_on W0 (subspace_topology E0 TE0 W0) w e0 gw"
          by (by100 blast)
        \<comment> \<open>Lift path gw from W0 to B' (since W0 \<subseteq> B').\<close>
        have "top1_is_path_on B' (subspace_topology E0 TE0 B') w e0 gw"
        proof -
          have hgw_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              W0 (subspace_topology E0 TE0 W0) gw"
            using hgw unfolding top1_is_path_on_def by (by100 blast)
          from top1_continuous_map_on_codomain_enlarge[OF hgw_cont hW0_sub hB'_sub]
          have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              B' (subspace_topology E0 TE0 B') gw" .
          moreover have "gw 0 = w" "gw 1 = e0"
            using hgw unfolding top1_is_path_on_def by (by100 blast)+
          ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
        qed
        \<comment> \<open>Concatenate: e1 \<rightarrow> w \<rightarrow> e0 in B'.\<close>
        have "top1_is_path_on B' (subspace_topology E0 TE0 B') e1 e0
            (top1_path_product fw gw)"
          by (rule top1_path_product_is_path[OF hB'_top hfw(2)
              \<open>top1_is_path_on B' (subspace_topology E0 TE0 B') w e0 gw\<close>])
        hence "e0 \<in> ?R" using he0(1) by (by100 blast)
        thus False using he0(2) by (by100 blast)
      qed
      \<comment> \<open>W0 is open in B' (W0 \<in> TE0, W0 \<subseteq> B').\<close>
      have hW0_open_B': "W0 \<in> subspace_topology E0 TE0 B'"
      proof -
        have "W0 \<in> TE0" using hW0_open unfolding openin_on_def by (by100 blast)
        have "W0 \<inter> B' = W0" using hW0_sub by (by100 blast)
        have "W0 \<inter> B' \<in> subspace_topology E0 TE0 B'"
          unfolding subspace_topology_def using \<open>W0 \<in> TE0\<close> by (by100 blast)
        thus ?thesis using \<open>W0 \<inter> B' = W0\<close> by (by100 simp)
      qed
      \<comment> \<open>W0 \<subseteq> B' \\ R, W0 open in B', e0 \<in> W0.
         Now get a sheet W1 at e1 (which is in R). W1 \<subseteq> R similarly.
         Then: R is a nonempty open set, B' \\ R is a nonempty open set.
         Their union is B'. This contradicts B' connected.\<close>
      \<comment> \<open>Similarly show: R is open in B'.\<close>
      have hR_open_B': "openin_on B' (subspace_topology E0 TE0 B') ?R"
      proof -
        have "\<forall>e \<in> ?R. \<exists>W. W \<in> subspace_topology E0 TE0 B' \<and> e \<in> W \<and> W \<subseteq> ?R"
        proof (intro ballI)
          fix e assume he_R: "e \<in> ?R"
          hence he_B': "e \<in> B'" by (by100 blast)
          from hsheet_in_B'[OF he_B'] obtain W where
              hW_sub_B: "W \<subseteq> B'" and hW_open_E: "openin_on E0 TE0 W" and hW_e: "e \<in> W"
              and hW_pc_W: "top1_path_connected_on W (subspace_topology E0 TE0 W)"
            by (by100 blast)
          \<comment> \<open>All of W is in R: for w \<in> W, path e1 \<rightarrow> e (in B') + path e \<rightarrow> w (in W \<subseteq> B').\<close>
          have "W \<subseteq> ?R"
          proof (intro subsetI)
            fix w assume hw: "w \<in> W"
            have hw_B': "w \<in> B'" using hw hW_sub_B by (by100 blast)
            from he_R obtain fe where hfe: "top1_is_path_on B' (subspace_topology E0 TE0 B') e1 e fe"
              by (by100 blast)
            have "\<exists>g. top1_is_path_on W (subspace_topology E0 TE0 W) e w g"
              using hW_pc_W hW_e hw unfolding top1_path_connected_on_def by (by100 blast)
            then obtain ge where hge: "top1_is_path_on W (subspace_topology E0 TE0 W) e w ge"
              by (by100 blast)
            have hge_B': "top1_is_path_on B' (subspace_topology E0 TE0 B') e w ge"
            proof -
              have hge_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  W (subspace_topology E0 TE0 W) ge"
                using hge unfolding top1_is_path_on_def by (by100 blast)
              from top1_continuous_map_on_codomain_enlarge[OF hge_cont hW_sub_B hB'_sub]
              have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  B' (subspace_topology E0 TE0 B') ge" .
              moreover have "ge 0 = e" "ge 1 = w"
                using hge unfolding top1_is_path_on_def by (by100 blast)+
              ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
            qed
            have "top1_is_path_on B' (subspace_topology E0 TE0 B') e1 w
                (top1_path_product fe ge)"
              by (rule top1_path_product_is_path[OF hB'_top hfe hge_B'])
            thus "w \<in> ?R" using hw_B' by (by100 blast)
          qed
          \<comment> \<open>W is open in B'.\<close>
          have "W \<in> TE0" using hW_open_E unfolding openin_on_def by (by100 blast)
          have "W \<inter> B' = W" using hW_sub_B by (by100 blast)
          have "W \<inter> B' \<in> subspace_topology E0 TE0 B'"
            unfolding subspace_topology_def using \<open>W \<in> TE0\<close> by (by100 blast)
          hence "W \<in> subspace_topology E0 TE0 B'" using \<open>W \<inter> B' = W\<close> by (by100 simp)
          thus "\<exists>W. W \<in> subspace_topology E0 TE0 B' \<and> e \<in> W \<and> W \<subseteq> ?R"
            using hW_e \<open>W \<subseteq> ?R\<close> by (by100 blast)
        qed
        \<comment> \<open>R = union of its open sub-neighborhoods, hence open.\<close>
        hence "?R = \<Union>{W \<in> subspace_topology E0 TE0 B'. W \<subseteq> ?R}"
          by (by5000 blast)
        moreover have "\<Union>{W \<in> subspace_topology E0 TE0 B'. W \<subseteq> ?R} \<in> subspace_topology E0 TE0 B'"
        proof -
          have "{W \<in> subspace_topology E0 TE0 B'. W \<subseteq> ?R} \<subseteq> subspace_topology E0 TE0 B'"
            by (by100 blast)
          from hB'_top[unfolded is_topology_on_def, THEN conjunct2, THEN conjunct2, THEN conjunct1,
              rule_format, OF this]
          show ?thesis .
        qed
        ultimately have "?R \<in> subspace_topology E0 TE0 B'" by (by100 simp)
        moreover have "?R \<subseteq> B'" by (by100 blast)
        ultimately show ?thesis unfolding openin_on_def by (by100 blast)
      qed
      \<comment> \<open>R nonempty, B' \\ R nonempty, both open in B', union = B'. Contradicts connected.\<close>
      have "?R \<noteq> {}" using he1_R by (by100 blast)
      have "B' - ?R \<noteq> {}" using hR_strict .
      have "?R \<union> (B' - ?R) = B'" by (by100 blast)
      have "?R \<inter> (B' - ?R) = {}" by (by100 blast)
      \<comment> \<open>Both R and B'\\R are open in B'. This contradicts B' connected.\<close>
      have "openin_on B' (subspace_topology E0 TE0 B') (B' - ?R)"
      proof -
        have "B' - ?R \<subseteq> B' - ?R" by (by100 blast)
        have "\<forall>e\<in>B' - ?R. \<exists>W. W \<in> subspace_topology E0 TE0 B' \<and> e \<in> W \<and> W \<subseteq> B' - ?R"
        proof (intro ballI)
          fix e2 assume he2: "e2 \<in> B' - ?R"
          hence he2_B': "e2 \<in> B'" and he2_nR: "e2 \<notin> ?R" by (by100 blast)+
          from hsheet_in_B'[OF he2_B'] obtain W2 where
              hW2_sub: "W2 \<subseteq> B'" and hW2_open: "openin_on E0 TE0 W2" and hW2_e: "e2 \<in> W2"
              and hW2_pc: "top1_path_connected_on W2 (subspace_topology E0 TE0 W2)"
            by (by100 blast)
          have "W2 \<inter> ?R = {}"
          proof (rule ccontr)
            assume "W2 \<inter> ?R \<noteq> {}"
            then obtain w where hw: "w \<in> W2" "w \<in> ?R" by (by100 blast)
            from hw(2) obtain fw2 where hfw2: "w \<in> B'"
                "top1_is_path_on B' (subspace_topology E0 TE0 B') e1 w fw2" by (by100 blast)
            have "\<exists>g. top1_is_path_on W2 (subspace_topology E0 TE0 W2) w e2 g"
              using hW2_pc hw(1) hW2_e unfolding top1_path_connected_on_def by (by100 blast)
            then obtain gw2 where hgw2: "top1_is_path_on W2 (subspace_topology E0 TE0 W2) w e2 gw2"
              by (by100 blast)
            have hgw2_B': "top1_is_path_on B' (subspace_topology E0 TE0 B') w e2 gw2"
            proof -
              have hc: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  W2 (subspace_topology E0 TE0 W2) gw2"
                using hgw2 unfolding top1_is_path_on_def by (by100 blast)
              from top1_continuous_map_on_codomain_enlarge[OF hc hW2_sub hB'_sub]
              have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  B' (subspace_topology E0 TE0 B') gw2" .
              moreover have "gw2 0 = w" "gw2 1 = e2"
                using hgw2 unfolding top1_is_path_on_def by (by100 blast)+
              ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
            qed
            have "top1_is_path_on B' (subspace_topology E0 TE0 B') e1 e2
                (top1_path_product fw2 gw2)"
              by (rule top1_path_product_is_path[OF hB'_top hfw2(2) hgw2_B'])
            hence "e2 \<in> ?R" using he2_B' by (by100 blast)
            thus False using he2_nR by (by100 blast)
          qed
          have "W2 \<in> TE0" using hW2_open unfolding openin_on_def by (by100 blast)
          have "W2 \<inter> B' = W2" using hW2_sub by (by100 blast)
          have "W2 \<inter> B' \<in> subspace_topology E0 TE0 B'"
            unfolding subspace_topology_def using \<open>W2 \<in> TE0\<close> by (by100 blast)
          hence "W2 \<in> subspace_topology E0 TE0 B'" using \<open>W2 \<inter> B' = W2\<close> by (by100 simp)
          have "W2 \<subseteq> B' - ?R" using hW2_sub \<open>W2 \<inter> ?R = {}\<close> by (by100 blast)
          thus "\<exists>W. W \<in> subspace_topology E0 TE0 B' \<and> e2 \<in> W \<and> W \<subseteq> B' - ?R"
            using \<open>W2 \<in> subspace_topology E0 TE0 B'\<close> hW2_e \<open>W2 \<subseteq> B' - ?R\<close> by (by100 blast)
        qed
        hence "B' - ?R = \<Union>{W \<in> subspace_topology E0 TE0 B'. W \<subseteq> B' - ?R}"
          by (by5000 blast)
        moreover have "\<Union>{W \<in> subspace_topology E0 TE0 B'. W \<subseteq> B' - ?R} \<in> subspace_topology E0 TE0 B'"
        proof -
          have "{W \<in> subspace_topology E0 TE0 B'. W \<subseteq> B' - ?R} \<subseteq> subspace_topology E0 TE0 B'"
            by (by100 blast)
          from hB'_top[unfolded is_topology_on_def, THEN conjunct2, THEN conjunct2, THEN conjunct1,
              rule_format, OF this]
          show ?thesis .
        qed
        ultimately have "(B' - ?R) \<in> subspace_topology E0 TE0 B'" by (by100 simp)
        thus ?thesis unfolding openin_on_def by (by100 blast)
      qed
      have "?R \<in> subspace_topology E0 TE0 B'"
        using hR_open_B' unfolding openin_on_def by (by100 blast)
      have "(B' - ?R) \<in> subspace_topology E0 TE0 B'"
        using \<open>openin_on B' (subspace_topology E0 TE0 B') (B' - ?R)\<close> unfolding openin_on_def
        by (by100 blast)
      from hB'_conn[unfolded top1_connected_on_def]
      have "\<not> (\<exists>U V. U \<in> subspace_topology E0 TE0 B' \<and> V \<in> subspace_topology E0 TE0 B'
          \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = B')"
        by (by100 blast)
      thus False
        using \<open>?R \<in> subspace_topology E0 TE0 B'\<close>
            \<open>(B' - ?R) \<in> subspace_topology E0 TE0 B'\<close>
            \<open>?R \<noteq> {}\<close> \<open>B' - ?R \<noteq> {}\<close>
            \<open>?R \<inter> (B' - ?R) = {}\<close> \<open>?R \<union> (B' - ?R) = B'\<close>
        by (by100 blast)
    qed
    \<comment> \<open>x, y \<in> R. Get paths e1 \<rightarrow> x and e1 \<rightarrow> y in B'.\<close>
    have "x \<in> ?R" using hR_eq_B' hx by (by100 simp)
    then obtain fx where hfx: "top1_is_path_on B' (subspace_topology E0 TE0 B') e1 x fx" by (by100 blast)
    have "y \<in> ?R" using hR_eq_B' hy by (by100 simp)
    then obtain fy where hfy: "top1_is_path_on B' (subspace_topology E0 TE0 B') e1 y fy" by (by100 blast)
    \<comment> \<open>Reverse fx to get x \<rightarrow> e1, then concatenate with fy for x \<rightarrow> e1 \<rightarrow> y.\<close>
    have hfx_rev: "top1_is_path_on B' (subspace_topology E0 TE0 B') x e1 (top1_path_reverse fx)"
      by (rule top1_path_reverse_is_path[OF hfx])
    have hB'_top: "is_topology_on B' (subspace_topology E0 TE0 B')"
      by (rule subspace_topology_is_topology_on[OF assms(3) hB'_sub])
    have "top1_is_path_on B' (subspace_topology E0 TE0 B') x y
        (top1_path_product (top1_path_reverse fx) fy)"
      by (rule top1_path_product_is_path[OF hB'_top hfx_rev hfy])
    thus "\<exists>f. top1_is_path_on B' (subspace_topology E0 TE0 B') x y f"
      by (by100 blast)
  qed
qed

section \<open>Chapter 14: Applications to Group Theory\<close>

(** from \<S>83 Theorem 83.4 (Munkres numbering): any covering space of a graph is itself a graph. **)
theorem Theorem_83_4_covering_of_graph_is_graph:
  assumes "top1_is_graph_on B TB"
      and "top1_covering_map_on E TE B TB p"
      and "is_topology_on_strict E TE"
  shows "top1_is_graph_on E TE"
proof -
  \<comment> \<open>Munkres 83.2: Each arc A in B lifts to arcs in E (sheets over A).
     The covering map p is a local homeomorphism, so lifts of arcs are arcs.
     The intersection condition and weak topology lift from B to E.\<close>
  obtain \<A>B where hAB: "(\<forall>A\<in>\<A>B. A \<subseteq> B \<and> top1_is_arc_on A (subspace_topology B TB A))"
      and hcover: "(\<Union>\<A>B) = B"
      and hAB_inter: "\<forall>A\<in>\<A>B. \<forall>A'\<in>\<A>B. A \<noteq> A' \<longrightarrow>
           A \<inter> A' \<subseteq> top1_arc_endpoints_on A (subspace_topology B TB A)
         \<and> A \<inter> A' \<subseteq> top1_arc_endpoints_on A' (subspace_topology B TB A')
         \<and> finite (A \<inter> A') \<and> card (A \<inter> A') \<le> 2"
      and hAB_coh: "\<forall>C. C \<subseteq> B \<longrightarrow>
           (closedin_on B TB C \<longleftrightarrow>
            (\<forall>A\<in>\<A>B. closedin_on A (subspace_topology B TB A) (A \<inter> C)))"
    using assms(1) unfolding top1_is_graph_on_def by (by5000 auto)
  \<comment> \<open>E is Hausdorff (needed in arc proofs below).\<close>
  have hE_haus_top: "is_hausdorff_on E TE"
  proof -
    have hB_haus: "is_hausdorff_on B TB"
      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
    have hTB: "is_topology_on B TB"
      using hB_haus unfolding is_hausdorff_on_def by (by100 blast)
    have hTE: "is_topology_on E TE"
      using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
    have hp_surj: "p ` E = B"
      using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
    show ?thesis unfolding is_hausdorff_on_def neighborhood_of_def
    proof (intro conjI ballI impI)
      show "is_topology_on E TE" by (rule hTE)
    next
      fix x y assume hx: "x \<in> E" and hy: "y \<in> E" and hne: "x \<noteq> y"
      show "\<exists>U V. (U \<in> TE \<and> x \<in> U) \<and> (V \<in> TE \<and> y \<in> V) \<and> U \<inter> V = {}"
      proof (cases "p x = p y")
        case False
        have hpx: "p x \<in> B" using hp_surj hx by (by100 blast)
        have hpy: "p y \<in> B" using hp_surj hy by (by100 blast)
        obtain U1 V1 where hU1: "U1 \<in> TB" "p x \<in> U1" and hV1: "V1 \<in> TB" "p y \<in> V1"
            and hdisj: "U1 \<inter> V1 = {}"
          using hB_haus hpx hpy False unfolding is_hausdorff_on_def neighborhood_of_def
          by (by100 blast)
        have hpU: "{e \<in> E. p e \<in> U1} \<in> TE"
          using hp_cont hU1(1) unfolding top1_continuous_map_on_def by (by100 blast)
        have hpV: "{e \<in> E. p e \<in> V1} \<in> TE"
          using hp_cont hV1(1) unfolding top1_continuous_map_on_def by (by100 blast)
        have "x \<in> {e \<in> E. p e \<in> U1}" using hx hU1(2) by (by100 blast)
        moreover have "y \<in> {e \<in> E. p e \<in> V1}" using hy hV1(2) by (by100 blast)
        moreover have "{e \<in> E. p e \<in> U1} \<inter> {e \<in> E. p e \<in> V1} = {}"
          using hdisj by (by100 blast)
        ultimately show ?thesis using hpU hpV by (by100 blast)
      next
        case True
        have hb: "p x \<in> B" using hp_surj hx by (by100 blast)
        obtain U0 where hbU: "p x \<in> U0"
            and hev: "top1_evenly_covered_on E TE B TB p U0"
          using assms(2) hb unfolding top1_covering_map_on_def by (by100 blast)
        obtain \<V> where hV_all: "(\<forall>V\<in>\<V>. openin_on E TE V)
            \<and> (\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {})
            \<and> {e \<in> E. p e \<in> U0} = \<Union>\<V>
            \<and> (\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
                U0 (subspace_topology B TB U0) p)"
          using hev unfolding top1_evenly_covered_on_def
          apply (elim conjE exE)
          apply (rule that)
          apply (by100 blast)+
          done
        have hV_open: "\<forall>V\<in>\<V>. openin_on E TE V" using hV_all by (by100 blast)
        have hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}" using hV_all by (by100 blast)
        have hV_union: "{e \<in> E. p e \<in> U0} = \<Union>\<V>" using hV_all by (by100 blast)
        have hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
            U0 (subspace_topology B TB U0) p" using hV_all by (by100 blast)
        have hx_in_V: "x \<in> \<Union>\<V>" using hx hbU hV_union by (by100 blast)
        have "p y \<in> U0" using hbU True by (by100 simp)
        have hy_in_V: "y \<in> \<Union>\<V>" using hy \<open>p y \<in> U0\<close> hV_union by (by100 blast)
        obtain Vx where hVx: "Vx \<in> \<V>" "x \<in> Vx" using hx_in_V by (by100 blast)
        obtain Vy where hVy: "Vy \<in> \<V>" "y \<in> Vy" using hy_in_V by (by100 blast)
        have "Vx \<noteq> Vy"
        proof
          assume heq: "Vx = Vy"
          have "inj_on p Vx"
            using hV_homeo hVx(1) unfolding top1_homeomorphism_on_def bij_betw_def
            by (by100 blast)
          have "y \<in> Vx" using hVy(2) heq by (by100 simp)
          have "x = y" using inj_onD[OF \<open>inj_on p Vx\<close> True hVx(2) \<open>y \<in> Vx\<close>] .
          thus False using hne by (by100 simp)
        qed
        hence "Vx \<inter> Vy = {}" using hV_disj hVx(1) hVy(1) by (by100 blast)
        moreover have "Vx \<in> TE" using hV_open hVx(1) unfolding openin_on_def by (by100 blast)
        moreover have "Vy \<in> TE" using hV_open hVy(1) unfolding openin_on_def by (by100 blast)
        ultimately show ?thesis using hVx(2) hVy(2) by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Step 1: For each arc A \<in> \<A>B, the preimage p\<inverse>(A) splits into sheets.
     Each sheet is homeomorphic to A via p (local homeomorphism), hence an arc.\<close>
  have hAE: "\<exists>\<A>E. (\<forall>A'\<in>\<A>E. A' \<subseteq> E \<and> top1_is_arc_on A' (subspace_topology E TE A'))
      \<and> (\<Union>\<A>E) = E
      \<and> (\<forall>A'\<in>\<A>E. \<forall>B'\<in>\<A>E. A' \<noteq> B' \<longrightarrow>
           A' \<inter> B' \<subseteq> top1_arc_endpoints_on A' (subspace_topology E TE A')
         \<and> A' \<inter> B' \<subseteq> top1_arc_endpoints_on B' (subspace_topology E TE B')
         \<and> finite (A' \<inter> B') \<and> card (A' \<inter> B') \<le> 2)
      \<and> (\<forall>C. C \<subseteq> E \<longrightarrow>
           (closedin_on E TE C \<longleftrightarrow>
            (\<forall>A'\<in>\<A>E. closedin_on A' (subspace_topology E TE A') (A' \<inter> C))))"
  proof -
    \<comment> \<open>Munkres 83.4: Lift graph structure from B to E.
       Step 1: For each arc A \<in> \<A>B, the path components of p\<inverse>(A) are arcs in E.
       Since A is path-connected and simply connected (an arc), p restricted to each
       path component B is a homeomorphism B \<rightarrow> A (by Theorem 54.4: lifting
       correspondence is bijective for simply-connected base).
       Step 2: These lifted arcs cover E (since \<A>B covers B and p is surjective on arcs).
       Different lifted arcs from different base arcs intersect at most in endpoints
       (from the intersection property of the base graph + homeomorphism of sheets).
       Step 3: E has the coherent (weak) topology with respect to the lifted arcs
       (from the covering map property: open sets in E are determined by sheets).\<close>
    have hE_haus: "is_hausdorff_on E TE" using hE_haus_top .
    \<comment> \<open>Define \<A>E = maximal connected components of p\<inverse>(A) for each A \<in> \<A>B.\<close>
    \<comment> \<open>Using named predicate for better automation.\<close>
    let ?\<A>E = "\<Union>A\<in>\<A>B. {B'. top1_max_conn_comp {e \<in> E. p e \<in> A}
        (subspace_topology E TE {e \<in> E. p e \<in> A}) B'}"
    \<comment> \<open>Each B \<in> \<A>E is an arc (homeomorphic to A via p|_B).\<close>
    have hAE_arcs: "\<forall>B'\<in>?\<A>E. B' \<subseteq> E \<and> top1_is_arc_on B' (subspace_topology E TE B') \<and> inj_on p B'
        \<and> (\<exists>A0\<in>\<A>B. p ` B' = A0)"
    proof (intro ballI)
      fix B' assume "B' \<in> ?\<A>E"
      then obtain A where hA: "A \<in> \<A>B"
          and hB'_comp: "top1_max_conn_comp {e \<in> E. p e \<in> A}
              (subspace_topology E TE {e \<in> E. p e \<in> A}) B'"
        by (by100 blast)
      \<comment> \<open>B' \<subseteq> p\<inverse>(A) \<subseteq> E.\<close>
      have hB'_sub_pre: "B' \<subseteq> {e \<in> E. p e \<in> A}" using max_conn_comp_sub[OF hB'_comp] .
      have hB'_sub_E: "B' \<subseteq> E" using hB'_sub_pre by (by100 blast)
      \<comment> \<open>Step 1: Restrict covering to arc A. By Theorem 53.2, p: p\<inverse>(A) \<rightarrow> A is a covering.\<close>
      \<comment> \<open>Step 2: B' is a connected component of p\<inverse>(A), hence path-connected (in LPC space).
         p restricted to B' maps onto A (connected component covers connected base).
         Since A is simply connected, by Theorem 54.4, fiber has 1 point \<rightarrow> homeomorphism.
         B' \<cong> A (arc) \<rightarrow> B' is an arc.\<close>
      \<comment> \<open>Prove arc and injectivity together (injectivity is needed for the arc proof
         and should also be exported).\<close>
      have hB'_arc_and_inj: "top1_is_arc_on B' (subspace_topology E TE B') \<and> inj_on p B' \<and> p ` B' = A"
      proof -
        \<comment> \<open>A is an arc: simply connected, path connected.\<close>
        have hA_arc: "top1_is_arc_on A (subspace_topology B TB A)"
          using hAB hA by (by100 blast)
        have hA_sub: "A \<subseteq> B" using hAB hA by (by100 blast)
        have hA_sc: "top1_simply_connected_on A (subspace_topology B TB A)"
        proof -
          have "top1_is_arc_on A (subspace_topology B TB A)" using hA_arc .
          \<comment> \<open>Arc = homeomorphic to [0,1] which is simply connected.\<close>
          then obtain h_arc where "top1_homeomorphism_on top1_unit_interval
              top1_unit_interval_topology A (subspace_topology B TB A) h_arc"
            unfolding top1_is_arc_on_def by (by100 blast)
          \<comment> \<open>Choose an endpoint of A.\<close>
          have hA_strict: "is_topology_on_strict A (subspace_topology B TB A)"
            using hA_arc unfolding top1_is_arc_on_def by (by100 blast)
          have hA_ep: "top1_arc_endpoints_on A (subspace_topology B TB A) \<noteq> {}"
          proof -
            have hB_haus: "is_hausdorff_on B TB"
              using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
            have hBT_strict: "is_topology_on_strict B TB"
              using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
            from arc_endpoints_are_boundary[OF hBT_strict hB_haus hA_sub hA_arc
                \<open>top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology A (subspace_topology B TB A) h_arc\<close>]
            show ?thesis by (by100 blast)
          qed
          then obtain ep where hep: "ep \<in> top1_arc_endpoints_on A (subspace_topology B TB A)"
            by (by100 blast)
          \<comment> \<open>Arc deformation retracts to endpoint (from cached session).\<close>
          have hA_dr: "top1_deformation_retract_of_on A (subspace_topology B TB A) {ep}"
            by (rule arc_deformation_retract_to_endpoint[OF hA_arc hep])
          \<comment> \<open>Arc path-connected (from homeomorphism with [0,1]).\<close>
          have hA_pc: "top1_path_connected_on A (subspace_topology B TB A)"
          proof -
            have "top1_path_connected_on top1_unit_interval top1_unit_interval_topology"
              unfolding top1_path_connected_on_def
            proof (intro conjI ballI)
              show "is_topology_on top1_unit_interval top1_unit_interval_topology"
                by (rule top1_unit_interval_topology_is_topology_on)
            next
              fix x y assume hx: "x \<in> top1_unit_interval" and hy: "y \<in> top1_unit_interval"
              let ?f = "\<lambda>t::real. (1 - t) * x + t * y"
              have hf_cont: "continuous_on top1_unit_interval ?f"
                by (intro continuous_intros)
              have hf_range: "\<forall>t\<in>top1_unit_interval. ?f t \<in> top1_unit_interval"
              proof (intro ballI)
                fix t assume ht: "t \<in> top1_unit_interval"
                have "0 \<le> t" "t \<le> 1" "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1"
                  using ht hx hy unfolding top1_unit_interval_def by (by100 auto)+
                have "0 \<le> 1 - t" using \<open>t \<le> 1\<close> by (by100 linarith)
                have "0 \<le> (1-t)*x" using \<open>0 \<le> 1-t\<close> \<open>0 \<le> x\<close> by (by100 auto)
                moreover have "0 \<le> t*y" using \<open>0 \<le> t\<close> \<open>0 \<le> y\<close> by (by100 auto)
                ultimately have "0 \<le> ?f t" by (by100 linarith)
                have "(1-t)*x \<le> (1-t)*1" using mult_left_mono[OF \<open>x \<le> 1\<close> \<open>0 \<le> 1-t\<close>] .
                have "t*y \<le> t*1" using mult_left_mono[OF \<open>y \<le> 1\<close> \<open>0 \<le> t\<close>] .
                have "(1-t)*1 + t*1 = (1::real)" by (by100 simp)
                have "?f t \<le> 1" using \<open>(1-t)*x \<le> (1-t)*1\<close> \<open>t*y \<le> t*1\<close> \<open>(1-t)*1 + t*1 = 1\<close>
                  by (by100 linarith)
                show "?f t \<in> top1_unit_interval"
                  unfolding top1_unit_interval_def using \<open>0 \<le> ?f t\<close> \<open>?f t \<le> 1\<close> by (by100 auto)
              qed
              from top1_continuous_map_on_subspace_open_sets_on[OF _ hf_cont] hf_range
              have "top1_continuous_map_on top1_unit_interval
                  (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval)
                  top1_unit_interval
                  (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval) ?f"
                by (by100 blast)
              hence hf_top: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  top1_unit_interval top1_unit_interval_topology ?f"
                unfolding top1_unit_interval_topology_def by (by100 simp)
              have "?f 0 = x" by (by100 simp)
              moreover have "?f 1 = y" by (by100 simp)
              ultimately show "\<exists>f. top1_is_path_on top1_unit_interval top1_unit_interval_topology x y f"
                unfolding top1_is_path_on_def using hf_top by (by100 blast)
            qed
            from homeomorphism_preserves_path_connected[OF
                \<open>top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology A (subspace_topology B TB A) h_arc\<close>
                this]
            show ?thesis .
          qed
          have hA_top: "is_topology_on A (subspace_topology B TB A)"
            using hA_strict unfolding is_topology_on_strict_def by (by100 blast)
          have "ep \<in> A" using hep unfolding top1_arc_endpoints_on_def by (by100 blast)
          \<comment> \<open>DR to singleton + path connected \<Rightarrow> simply connected.\<close>
          from deformation_retract_to_singleton_imp_simply_connected[OF hA_top \<open>ep \<in> A\<close> hA_pc hA_dr]
          show ?thesis .
        qed
        \<comment> \<open>Step 1: Restrict covering p: E \<rightarrow> B to p\<inverse>(A) \<rightarrow> A via Theorem 53.2.\<close>
        let ?E0 = "{e \<in> E. p e \<in> A}"
        have hE0_sub: "?E0 \<subseteq> E" by (by100 blast)
        have hE0_eq: "?E0 = {e \<in> E. p e \<in> A}" by (by100 blast)
        have hcov_A: "top1_covering_map_on ?E0 (subspace_topology E TE ?E0) A (subspace_topology B TB A) p"
        proof -
          have hBT_strict: "is_topology_on_strict B TB"
            using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
          from Theorem_53_2[OF assms(2) assms(3) hBT_strict hA_sub hE0_eq]
          show ?thesis .
        qed
        \<comment> \<open>Step 2: B' is connected in E0. p maps B' into A (surjectively onto A since
           A is connected and p is a covering map restricted to B').
           B' is path-connected (connected component of locally path-connected space).\<close>
        \<comment> \<open>Step 3: By Theorem 54.4: since A is simply connected, the lifting correspondence
           is bijective \<Rightarrow> fiber of p|\_B' has exactly 1 point \<Rightarrow> p|\_B' is injective.
           p|\_B' is continuous + injective + onto A + A compact Hausdorff \<Rightarrow> homeomorphism.
           B' \<cong> A \<cong> [0,1] \<Rightarrow> B' is an arc.\<close>
        \<comment> \<open>Munkres Thm 83.4 Step 1: p0: B' \<rightarrow> A obtained by restricting p is a covering map.
           Because B' path-connected, lifting corr \<phi>: \<pi>\_1(A,a) \<rightarrow> p0\<inverse>(a) surjective.
           A simply connected \<Rightarrow> p0\<inverse>(a) = 1 point \<Rightarrow> p0 homeomorphism \<Rightarrow> B' is arc.\<close>
        \<comment> \<open>p0: B' \<rightarrow> A is a covering map (from Theorems 53.2 + path component restriction).\<close>
        have hB'_pc: "top1_path_connected_on B' (subspace_topology E TE B')"
        proof -
          have hTE: "is_topology_on E TE"
            using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
          have hTE0: "is_topology_on ?E0 (subspace_topology E TE ?E0)"
            by (rule subspace_topology_is_topology_on[OF hTE hE0_sub])
          have hTA: "is_topology_on A (subspace_topology B TB A)"
          proof -
            have "is_topology_on B TB"
              using assms(1) unfolding top1_is_graph_on_def is_hausdorff_on_def by (by100 blast)
            from subspace_topology_is_topology_on[OF this hA_sub] show ?thesis .
          qed
          from covering_component_over_arc_path_connected[OF hcov_A hA_arc hTE0 hTA hB'_comp]
          have "top1_path_connected_on B' (subspace_topology ?E0 (subspace_topology E TE ?E0) B')" .
          moreover have "subspace_topology ?E0 (subspace_topology E TE ?E0) B' = subspace_topology E TE B'"
            by (rule subspace_topology_trans[OF \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close>])
          ultimately show ?thesis by (by100 simp)
        qed
        \<comment> \<open>Direct approach: show p|\_B' is a homeomorphism B' \<rightarrow> A via:
           (a) injectivity: Theorem 54.3 + A simply connected
           (b) surjectivity: open/closed argument
           (c) continuous + open map (from covering sheets) + bijective = homeomorphism.\<close>
        have hTE: "is_topology_on E TE"
          using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
        have hTE0: "is_topology_on ?E0 (subspace_topology E TE ?E0)"
          by (rule subspace_topology_is_topology_on[OF hTE hE0_sub])
        have hTA: "is_topology_on A (subspace_topology B TB A)"
        proof -
          have "is_topology_on B TB"
            using assms(1) unfolding top1_is_graph_on_def is_hausdorff_on_def by (by100 blast)
          from subspace_topology_is_topology_on[OF this hA_sub] show ?thesis .
        qed
        \<comment> \<open>Injectivity: if e1, e2 \<in> B' with p(e1) = p(e2), then e1 = e2.\<close>
        have hp_inj_B': "inj_on p B'"
        proof (intro inj_onI)
          fix e1' e2' assume he1': "e1' \<in> B'" and he2': "e2' \<in> B'" and hpeq: "p e1' = p e2'"
          let ?a = "p e1'"
          \<comment> \<open>B' path-connected: get a path \<gamma>: e1' \<rightarrow> e2' in B'.\<close>
          from hB'_pc[unfolded top1_path_connected_on_def]
          have "\<exists>f. top1_is_path_on B' (subspace_topology E TE B') e1' e2' f"
            using he1' he2' by (by100 blast)
          then obtain \<gamma> where h\<gamma>: "top1_is_path_on B' (subspace_topology E TE B') e1' e2' \<gamma>"
            by (by100 blast)
          \<comment> \<open>Lift \<gamma> to E0: \<gamma> is already a path in E0 (B' \<subseteq> E0).\<close>
          have h\<gamma>_E0: "top1_is_path_on ?E0 (subspace_topology E TE ?E0) e1' e2' \<gamma>"
          proof -
            have h\<gamma>_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                B' (subspace_topology E TE B') \<gamma>"
              using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
            from top1_continuous_map_on_codomain_enlarge[OF h\<gamma>_cont \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> hE0_sub]
            have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                ?E0 (subspace_topology E TE ?E0) \<gamma>" .
            moreover have "\<gamma> 0 = e1'" "\<gamma> 1 = e2'"
              using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)+
            ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
          qed
          \<comment> \<open>p \<circ> \<gamma> is a loop at ?a in A.\<close>
          \<comment> \<open>A simply connected: p \<circ> \<gamma> is path-homotopic to the constant loop.\<close>
          \<comment> \<open>\<gamma> is a lift of p \<circ> \<gamma> starting at e1'. constant\_e1' is a lift of constant\_?a.
             By Theorem 54.3: e2' = e1'.\<close>
          \<comment> \<open>For now, sorry the details of extracting the right conditions for Theorem\_54\_3.\<close>
          \<comment> \<open>p \<circ> \<gamma> is a loop at ?a in A (p \<circ> \<gamma> goes from p(e1') to p(e2') = p(e1')).\<close>
          have h_pg: "top1_is_path_on A (subspace_topology B TB A) ?a ?a (p \<circ> \<gamma>)"
          proof -
            \<comment> \<open>p is continuous from E0 to A.\<close>
            have hp_cont_E0: "top1_continuous_map_on ?E0 (subspace_topology E TE ?E0) A (subspace_topology B TB A) p"
            proof -
              have hp_cont: "top1_continuous_map_on E TE B TB p"
                using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
              have "top1_continuous_map_on ?E0 (subspace_topology E TE ?E0) B TB p"
                by (rule top1_continuous_map_on_subspace_restrict[OF hp_cont hE0_sub])
              have hp_range_E0: "\<forall>e \<in> ?E0. p e \<in> A" by (by100 blast)
              from continuous_map_restrict_codomain[OF
                  \<open>top1_continuous_map_on ?E0 (subspace_topology E TE ?E0) B TB p\<close>
                  hp_range_E0 hA_sub]
              show ?thesis .
            qed
            \<comment> \<open>Compose \<gamma>: I \<rightarrow> E0 with p: E0 \<rightarrow> A.\<close>
            have h\<gamma>_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                ?E0 (subspace_topology E TE ?E0) \<gamma>"
              using h\<gamma>_E0 unfolding top1_is_path_on_def by (by100 blast)
            from top1_continuous_map_on_comp[OF h\<gamma>_cont hp_cont_E0]
            have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                A (subspace_topology B TB A) (p \<circ> \<gamma>)" .
            moreover have "(p \<circ> \<gamma>) 0 = ?a"
              using h\<gamma> unfolding top1_is_path_on_def by (by100 simp)
            moreover have "(p \<circ> \<gamma>) 1 = ?a"
              using h\<gamma> hpeq unfolding top1_is_path_on_def by (by100 simp)
            ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
          qed
          have h_const: "top1_is_path_on A (subspace_topology B TB A) ?a ?a (top1_constant_path ?a)"
          proof -
            have "?a \<in> A" using he1' \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
            from top1_constant_path_is_path[OF hTA this] show ?thesis .
          qed
          \<comment> \<open>A simply connected \<Rightarrow> loop p \<circ> \<gamma> is path-homotopic to constant.\<close>
          have h_loop_pg: "top1_is_loop_on A (subspace_topology B TB A) ?a (p \<circ> \<gamma>)"
            unfolding top1_is_loop_on_def using h_pg by (by100 blast)
          have h_htpy: "top1_path_homotopic_on A (subspace_topology B TB A) ?a ?a (p \<circ> \<gamma>) (top1_constant_path ?a)"
          proof -
            have "?a \<in> A" using he1' \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
            from hA_sc[unfolded top1_simply_connected_on_def, THEN conjunct2, rule_format,
                OF \<open>?a \<in> A\<close> h_loop_pg]
            show ?thesis .
          qed
          \<comment> \<open>\<gamma> is a lift of p \<circ> \<gamma> in E0.\<close>
          have h\<gamma>_lift: "\<forall>s\<in>I_set. p (\<gamma> s) = (p \<circ> \<gamma>) s" by (by100 simp)
          \<comment> \<open>constant\_e1' is a lift of constant\_?a in E0.\<close>
          have hconst_lift: "top1_is_path_on ?E0 (subspace_topology E TE ?E0) e1' e1'
              (top1_constant_path e1')"
          proof -
            have "e1' \<in> ?E0" using he1' \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
            from top1_constant_path_is_path[OF hTE0 this] show ?thesis .
          qed
          have hconst_proj: "\<forall>s\<in>I_set. p (top1_constant_path e1' s) = (top1_constant_path ?a) s"
            unfolding top1_constant_path_def by (by100 simp)
          \<comment> \<open>Apply Theorem 54.3.\<close>
          have he1'_E0: "e1' \<in> ?E0" using he1' \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
          have hpeq_refl: "p e1' = ?a" by (by100 simp)
          from Theorem_54_3[OF hcov_A hTE0 hTA he1'_E0 hpeq_refl h_pg h_const h_htpy
              h\<gamma>_E0 h\<gamma>_lift hconst_lift hconst_proj]
          have "e2' = e1'" by (by100 blast)
          thus "e1' = e2'" by (by100 simp)
        qed
        \<comment> \<open>Surjectivity: p(B') = A via open/closed.\<close>
        have hp_surj_B': "p ` B' = A"
        proof -
          \<comment> \<open>p(B') is nonempty (B' \<noteq> {}).\<close>
          have hB'_ne: "B' \<noteq> {}" using max_conn_comp_ne[OF hB'_comp] .
          have "p ` B' \<noteq> {}" using hB'_ne by (by100 blast)
          \<comment> \<open>p(B') \<subseteq> A.\<close>
          have "p ` B' \<subseteq> A" using \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
          \<comment> \<open>p(B') is open in A: for a \<in> p(B'), the sheet at p\<inverse>(a) \<inter> B' maps onto a nbhd of a.\<close>
          \<comment> \<open>p(B') is closed in A: A \\ p(B') is open (sheets not meeting B').\<close>
          \<comment> \<open>A connected \<Rightarrow> p(B') = A.\<close>
          \<comment> \<open>p(B') is open in A: for a \<in> p(B'), get sheet W at p\<inverse>(a) containing some e \<in> B'.
             W \<subseteq> B' (by maximality). p(W) = U (evenly covered nbhd). So a has nbhd in p(B').\<close>
          have hpB_open: "openin_on A (subspace_topology B TB A) (p ` B')"
          proof -
            \<comment> \<open>For each a \<in> p(B'), get a nbhd of a in A contained in p(B').
               Use covering\_sheet\_over\_arc\_path\_connected to get a PC sheet W \<subseteq> E0 at e.
               W \<subseteq> B' by maximality. p(W) is open in A (from covering homeomorphism).\<close>
            have "\<forall>a \<in> p ` B'. \<exists>U. U \<in> subspace_topology B TB A \<and> a \<in> U \<and> U \<subseteq> p ` B'"
            proof (intro ballI)
              fix a assume "a \<in> p ` B'"
              then obtain e where he_B': "e \<in> B'" and hpe: "p e = a" by (by100 blast)
              have he_E0: "e \<in> ?E0" using he_B' \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
              \<comment> \<open>Get PC sheet W at e from covering\_sheet lemma (applied to E0).\<close>
              from covering_sheet_over_arc_path_connected[OF hcov_A hA_arc hTE0 hTA he_E0]
              obtain W where hW_sub: "W \<subseteq> ?E0" and hW_open: "openin_on ?E0 (subspace_topology E TE ?E0) W"
                  and hW_e: "e \<in> W" and hW_pc: "top1_path_connected_on W (subspace_topology ?E0 (subspace_topology E TE ?E0) W)"
                by (by100 blast)
              \<comment> \<open>W \<subseteq> B' by maximality (W connected, meets B' at e).\<close>
              have hW_conn: "top1_connected_on W (subspace_topology ?E0 (subspace_topology E TE ?E0) W)"
                by (rule path_connected_imp_connected[OF hW_pc])
              have hW_sub_B': "W \<subseteq> B'"
              proof -
                have hWB_sub: "W \<union> B' \<subseteq> ?E0" using hW_sub \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
                let ?A2 = "\<lambda>b::bool. if b then W else B'"
                have hY: "W \<union> B' = (\<Union>i\<in>{True, False}. ?A2 i)" by (by100 auto)
                have hWB_conn: "top1_connected_on (W \<union> B') (subspace_topology ?E0 (subspace_topology E TE ?E0) (W \<union> B'))"
                proof -
                  have hA2_sub: "\<forall>i\<in>{True, False}. ?A2 i \<subseteq> ?E0"
                    using hW_sub \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 auto)
                  have hA2_conn: "\<forall>i\<in>{True, False}. top1_connected_on (?A2 i) (subspace_topology ?E0 (subspace_topology E TE ?E0) (?A2 i))"
                  proof (intro ballI)
                    fix i :: bool assume "i \<in> {True, False}"
                    show "top1_connected_on (?A2 i) (subspace_topology ?E0 (subspace_topology E TE ?E0) (?A2 i))"
                    proof (cases i)
                      case True thus ?thesis using hW_conn by (by100 simp)
                    next
                      case False
                      have "top1_connected_on B' (subspace_topology {e \<in> E. p e \<in> A}
                          (subspace_topology E TE {e \<in> E. p e \<in> A}) B')"
                        using hB'_comp unfolding top1_max_conn_comp_def by (by100 blast)
                      thus ?thesis using False by (by100 simp)
                    qed
                  qed
                  have hp2: "e \<in> \<Inter>(?A2 ` {True, False})" using hW_e he_B' by (by100 auto)
                  from Theorem_23_3[OF hTE0 _ hA2_sub hA2_conn hp2]
                  have "top1_connected_on (\<Union>i\<in>{True, False}. ?A2 i)
                      (subspace_topology ?E0 (subspace_topology E TE ?E0) (\<Union>i\<in>{True, False}. ?A2 i))"
                    by (by100 blast)
                  thus ?thesis using hY by (by100 simp)
                qed
                have hB'_max_E0: "\<And>C. C \<supseteq> B' \<Longrightarrow> C \<subseteq> ?E0
                    \<Longrightarrow> top1_connected_on C (subspace_topology ?E0 (subspace_topology E TE ?E0) C) \<Longrightarrow> C = B'"
                proof -
                  fix C assume hC1: "C \<supseteq> B'" and hC2: "C \<subseteq> ?E0"
                      and hC3: "top1_connected_on C (subspace_topology ?E0 (subspace_topology E TE ?E0) C)"
                  have "subspace_topology ?E0 (subspace_topology E TE ?E0) C = subspace_topology E TE C"
                    by (rule subspace_topology_trans[OF hC2])
                  hence "top1_connected_on C (subspace_topology E TE C)" using hC3 by (by100 simp)
                  have "C \<subseteq> E" using hC2 by (by100 blast)
                  \<comment> \<open>But max\_conn\_comp uses subspace\_topology E TE, not E0.\<close>
                  \<comment> \<open>We need: top1\_connected\_on C (subspace\_topology {e \<in> E. p e \<in> A} (subspace\_topology E TE {e \<in> E. p e \<in> A}) C).\<close>
                  have "subspace_topology E TE C = subspace_topology {e \<in> E. p e \<in> A} (subspace_topology E TE {e \<in> E. p e \<in> A}) C"
                    by (rule subspace_topology_trans[OF hC2, symmetric])
                  hence "top1_connected_on C (subspace_topology {e \<in> E. p e \<in> A} (subspace_topology E TE {e \<in> E. p e \<in> A}) C)"
                    using \<open>top1_connected_on C (subspace_topology E TE C)\<close> by (by100 simp)
                  from hB'_comp[unfolded top1_max_conn_comp_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
                      rule_format, OF hC1 hC2 this]
                  show "C = B'" .
                qed
                from hB'_max_E0[OF _ hWB_sub hWB_conn] show "W \<subseteq> B'" by (by100 blast)
              qed
              \<comment> \<open>p(W) is open in A. W is part of an evenly covered sheet, so p(W) is open.\<close>
              \<comment> \<open>p|\_W is a homeomorphism onto its image (from covering), so p(W) is open in A.\<close>
              have "p ` W \<subseteq> A" using hW_sub by (by100 blast)
              have "p ` W \<in> subspace_topology B TB A"
              proof -
                have hTE0_strict: "is_topology_on_strict ?E0 (subspace_topology E TE ?E0)"
                  by (rule subspace_topology_is_strict[OF assms(3) hE0_sub])
                have "W \<in> subspace_topology E TE ?E0"
                  using hW_open unfolding openin_on_def by (by100 blast)
                from covering_map_is_open_map[OF hcov_A hTE0_strict hTA this]
                show ?thesis .
              qed
              have "a \<in> p ` W" using hW_e hpe by (by100 blast)
              have "p ` W \<subseteq> p ` B'" using hW_sub_B' by (by100 blast)
              thus "\<exists>U. U \<in> subspace_topology B TB A \<and> a \<in> U \<and> U \<subseteq> p ` B'"
                using \<open>p ` W \<in> subspace_topology B TB A\<close> \<open>a \<in> p ` W\<close> \<open>p ` W \<subseteq> p ` B'\<close>
                by (by100 blast)
            qed
            hence "p ` B' = \<Union>{U \<in> subspace_topology B TB A. U \<subseteq> p ` B'}"
              by (by5000 blast)
            moreover have "\<Union>{U \<in> subspace_topology B TB A. U \<subseteq> p ` B'} \<in> subspace_topology B TB A"
            proof -
              have "{U \<in> subspace_topology B TB A. U \<subseteq> p ` B'} \<subseteq> subspace_topology B TB A"
                by (by100 blast)
              from hTA[unfolded is_topology_on_def, THEN conjunct2, THEN conjunct2, THEN conjunct1,
                  rule_format, OF this]
              show ?thesis .
            qed
            ultimately have "p ` B' \<in> subspace_topology B TB A" by (by100 simp)
            thus ?thesis unfolding openin_on_def using \<open>p ` B' \<subseteq> A\<close> by (by100 blast)
          qed
          \<comment> \<open>A \\ p(B') is open: for each a \<in> A \\ p(B'), sheets over a don't meet B'.\<close>
          have hpB_closed: "closedin_on A (subspace_topology B TB A) (p ` B')"
          proof -
            \<comment> \<open>Show A \\ p(B') is open: for a \<in> A \\ p(B'), the covering sheets at a don't meet B'.\<close>
            have hcomp_open: "openin_on A (subspace_topology B TB A) (A - p ` B')"
            proof -
              have "\<forall>a \<in> A - p ` B'. \<exists>U. U \<in> subspace_topology B TB A \<and> a \<in> U \<and> U \<subseteq> A - p ` B'"
              proof (intro ballI)
                fix a assume ha: "a \<in> A - p ` B'"
                hence ha_A: "a \<in> A" and ha_nB: "a \<notin> p ` B'" by (by100 blast)+
                \<comment> \<open>Get evenly covered U0 of a.\<close>
                obtain U0 where hU0a: "a \<in> U0"
                    and hU0ev: "top1_evenly_covered_on ?E0 (subspace_topology E TE ?E0) A (subspace_topology B TB A) p U0"
                  using hcov_A ha_A unfolding top1_covering_map_on_def by (by100 blast)
                \<comment> \<open>Key: p(B') is already proved open. Since a \<notin> p(B') and p(B') is open,
                   U0 \\ p(B') is a neighborhood of a. More directly:
                   A \\ p(B') is the complement of an open set, but we need A \\ p(B') open too.

                   Direct argument: the fiber of a in E0 is nonempty (from covering surjectivity onto A).
                   Each point e0 of the fiber is NOT in B' (since a \<notin> p(B')).
                   The covering sheet at e0 is a connected nbhd of e0 in E0.
                   For this sheet to not meet B': if it did meet B', then the sheet \<subseteq> B' by maximality,
                   so a = p(e0) \<in> p(sheet) = U' \<subseteq> p(B'), contradiction.
                   So the sheet does not meet B'.
                   So {e \<in> E0. p e \<in> U'} has no points of B' (where U' is the PC sub-nbhd).
                   Hence U' \<inter> p(B') = {}.\<close>
                \<comment> \<open>Get a point in the fiber of a in E0.\<close>
                have "a \<in> A" using ha_A .
                have hp_surj_E0: "p ` ?E0 = A"
                  using hcov_A unfolding top1_covering_map_on_def by (by100 blast)
                have "a \<in> p ` ?E0" using hp_surj_E0 ha_A by (by100 simp)
                then obtain e0 where he0_E0: "e0 \<in> ?E0" and hpe0: "p e0 = a"
                  by (by100 blast)
                have he0_nB: "e0 \<notin> B'"
                  using ha_nB hpe0 by (by100 blast)
                \<comment> \<open>Get PC sheet W0 at e0.\<close>
                from covering_sheet_over_arc_path_connected[OF hcov_A hA_arc hTE0 hTA he0_E0]
                obtain W0 where hW0_sub: "W0 \<subseteq> ?E0" and hW0_open: "openin_on ?E0 (subspace_topology E TE ?E0) W0"
                    and hW0_e0: "e0 \<in> W0" and hW0_pc: "top1_path_connected_on W0 (subspace_topology ?E0 (subspace_topology E TE ?E0) W0)"
                    and hW0_homeo: "top1_homeomorphism_on W0 (subspace_topology ?E0 (subspace_topology E TE ?E0) W0)
                        (p ` W0) (subspace_topology A (subspace_topology B TB A) (p ` W0)) p"
                    and hW0_ev: "top1_evenly_covered_on ?E0 (subspace_topology E TE ?E0) A (subspace_topology B TB A) p (p ` W0)"
                  by (by100 blast)
                \<comment> \<open>W0 does NOT meet B': if it did, W0 \<subseteq> B' (by maximality), so e0 \<in> B', contradiction.\<close>
                have "W0 \<inter> B' = {}"
                proof (rule ccontr)
                  assume "W0 \<inter> B' \<noteq> {}"
                  have hW0_conn: "top1_connected_on W0 (subspace_topology ?E0 (subspace_topology E TE ?E0) W0)"
                    by (rule path_connected_imp_connected[OF hW0_pc])
                  have hW0B_sub: "W0 \<union> B' \<subseteq> ?E0"
                    using hW0_sub \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
                  obtain e_meet where "e_meet \<in> W0" "e_meet \<in> B'"
                    using \<open>W0 \<inter> B' \<noteq> {}\<close> by (by100 blast)
                  let ?A3 = "\<lambda>b::bool. if b then W0 else B'"
                  have hA3_conn: "\<forall>i\<in>{True, False}. top1_connected_on (?A3 i) (subspace_topology ?E0 (subspace_topology E TE ?E0) (?A3 i))"
                  proof (intro ballI)
                    fix i :: bool assume "i \<in> {True, False}"
                    thus "top1_connected_on (?A3 i) (subspace_topology ?E0 (subspace_topology E TE ?E0) (?A3 i))"
                    proof (cases i)
                      case True thus ?thesis using hW0_conn by (by100 simp)
                    next
                      case False
                      have "top1_connected_on B' (subspace_topology {e \<in> E. p e \<in> A}
                          (subspace_topology E TE {e \<in> E. p e \<in> A}) B')"
                        using hB'_comp unfolding top1_max_conn_comp_def by (by100 blast)
                      thus ?thesis using False by (by100 simp)
                    qed
                  qed
                  have hI3: "{True, False} \<noteq> ({}::bool set)" by (by100 blast)
                  have hA3_sub: "\<forall>i\<in>{True, False}. ?A3 i \<subseteq> ?E0"
                    using hW0_sub \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 auto)
                  have hp3: "e_meet \<in> \<Inter>(?A3 ` {True, False})"
                    using \<open>e_meet \<in> W0\<close> \<open>e_meet \<in> B'\<close> by (by100 auto)
                  have hY3: "W0 \<union> B' = (\<Union>i\<in>{True, False}. ?A3 i)" by (by100 auto)
                  from Theorem_23_3[OF hTE0 hI3 hA3_sub hA3_conn hp3]
                  have "top1_connected_on (\<Union>i\<in>{True, False}. ?A3 i) (subspace_topology ?E0 (subspace_topology E TE ?E0) (\<Union>i\<in>{True, False}. ?A3 i))" .
                  hence "top1_connected_on (W0 \<union> B') (subspace_topology ?E0 (subspace_topology E TE ?E0) (W0 \<union> B'))"
                    using hY3 by (by100 simp)
                  from hB'_comp[unfolded top1_max_conn_comp_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
                      rule_format, OF _ hW0B_sub this]
                  have "W0 \<union> B' = B'" by (by100 blast)
                  hence "W0 \<subseteq> B'" by (by100 blast)
                  hence "e0 \<in> B'" using hW0_e0 by (by100 blast)
                  thus False using he0_nB by (by100 blast)
                qed
                \<comment> \<open>p(W0) is open in A. a \<in> p(W0). All sheets over p(W0) are disjoint from B'.\<close>
                let ?U' = "p ` W0"
                have hU'_open: "?U' \<in> subspace_topology B TB A"
                proof -
                  have hTE0_strict: "is_topology_on_strict ?E0 (subspace_topology E TE ?E0)"
                    by (rule subspace_topology_is_strict[OF assms(3) hE0_sub])
                  have "W0 \<in> subspace_topology E TE ?E0"
                    using hW0_open unfolding openin_on_def by (by100 blast)
                  from covering_map_is_open_map[OF hcov_A hTE0_strict hTA this]
                  show ?thesis .
                qed
                have "a \<in> ?U'" using hW0_e0 hpe0 by (by100 blast)
                \<comment> \<open>?U' \<inter> p(B') = {}: if a' \<in> ?U' \<inter> p(B'), then some b \<in> B' with p(b) = a' \<in> ?U'.
                   So b \<in> {e \<in> E0. p e \<in> ?U'}. Get evenly covered U0' \<ni> a' and find the sheet of b.
                   The covering sheet at b (in E0) gives W\_b \<subseteq> B' with a' \<in> p(W\_b) = U\_b.
                   But U\_b and ?U' overlap at a'. The sheet containing e0 (W0) maps onto ?U' \<ni> a'.
                   If the sheet containing b also maps onto ?U'... then it meets W0 in the fiber of a'.
                   But they're different sheets (W0 \<inter> B' = {} and b \<in> B').\<close>
                \<comment> \<open>Actually: ALL sheets of p\<inverse>(?U') are disjoint from B'. If any sheet V meets B',
                   then V \<subseteq> B' (connected + maximality), so p(V) = some evenly covered neighborhood
                   containing a. But p|V: V \<rightarrow> ?U' is a homeomorphism (since V is a sheet over ?U'),
                   so a \<in> ?U' = p(V) \<subseteq> p(B'), contradicting a \<notin> p(B').\<close>
                \<comment> \<open>For this to work, we need the evenly covered neighborhood to be ?U' or a subset.
                   We need to work with an evenly covered ?U'.\<close>
                \<comment> \<open>?U' = p(W0) is evenly covered (from the strengthened covering\_sheet lemma).\<close>
                have hU'_ev: "top1_evenly_covered_on ?E0 (subspace_topology E TE ?E0) A (subspace_topology B TB A) p ?U'"
                  using hW0_ev .
                \<comment> \<open>All sheets over ?U' that meet B' must be in B'. For each such sheet V:
                   p|V: V \<rightarrow> ?U' is bijective (homeomorphism). So p(V) = ?U' \<ni> a.
                   But a \<notin> p(B'). Contradiction.\<close>
                have "?U' \<inter> p ` B' = {}"
                proof (rule ccontr)
                  assume hne: "?U' \<inter> p ` B' \<noteq> {}"
                  then obtain z where hz: "z \<in> ?U'" "z \<in> p ` B'" by (by100 blast)
                  from hz(2) obtain b where hb_B': "b \<in> B'" and hpb: "p b = z"
                    by (by100 auto)
                  have hpb_U': "p b \<in> ?U'" using hpb hz(1) by (by100 simp)
                  have hb_E0: "b \<in> ?E0" using hb_B' \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
                  have "b \<in> {e \<in> ?E0. p e \<in> ?U'}" using hb_E0 hpb_U' by (by100 blast)
                  \<comment> \<open>b is in some sheet Vb over ?U'.\<close>
                  obtain \<V>' where hV'_sheets: "(\<forall>V\<in>\<V>'. openin_on ?E0 (subspace_topology E TE ?E0) V)
                      \<and> (\<forall>V\<in>\<V>'. \<forall>V'\<in>\<V>'. V \<noteq> V' \<longrightarrow> V \<inter> V' = {})
                      \<and> {e \<in> ?E0. p e \<in> ?U'} = \<Union>\<V>'
                      \<and> (\<forall>V\<in>\<V>'. top1_homeomorphism_on V (subspace_topology ?E0 (subspace_topology E TE ?E0) V)
                          ?U' (subspace_topology A (subspace_topology B TB A) ?U') p)"
                    using hU'_ev unfolding top1_evenly_covered_on_def
                    apply (elim conjE exE) apply (rule that) apply (by100 blast)+ done
                  have "b \<in> \<Union>\<V>'" using hV'_sheets \<open>b \<in> {e \<in> ?E0. p e \<in> ?U'}\<close> by (by100 blast)
                  then obtain Vb where hVb: "Vb \<in> \<V>'" "b \<in> Vb" by (by100 blast)
                  \<comment> \<open>Vb is homeomorphic to ?U' via p. So p(Vb) = ?U'.\<close>
                  have "p ` Vb = ?U'"
                    using hV'_sheets hVb(1) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
                  hence "a \<in> p ` Vb" using \<open>a \<in> ?U'\<close> by (by100 blast)
                  then obtain e_a where "e_a \<in> Vb" "p e_a = a" by (by100 blast)
                  \<comment> \<open>e\_a \<in> Vb \<subseteq> E0. p(e\_a) = a. If Vb meets B' (at b), then Vb connected \<Rightarrow> Vb \<subseteq> B'.
                     But then e\_a \<in> B' and p(e\_a) = a \<in> p(B'). Contradicts a \<notin> p(B').\<close>
                  \<comment> \<open>Vb connected: homeomorphic to ?U' which is PC (image of PC W0).\<close>
                  have hU'_pc2: "top1_path_connected_on ?U' (subspace_topology A (subspace_topology B TB A) ?U')"
                    by (rule homeomorphism_preserves_path_connected[OF hW0_homeo hW0_pc])
                  \<comment> \<open>Vb homeomorphic to PC set \<Rightarrow> Vb PC \<Rightarrow> Vb connected.\<close>
                  have hVb_homeo: "top1_homeomorphism_on Vb (subspace_topology ?E0 (subspace_topology E TE ?E0) Vb)
                      ?U' (subspace_topology A (subspace_topology B TB A) ?U') p"
                    using hV'_sheets hVb(1) by (by100 blast)
                  have hVb_pc: "top1_path_connected_on Vb (subspace_topology ?E0 (subspace_topology E TE ?E0) Vb)"
                  proof -
                    from homeomorphism_inverse[OF hVb_homeo]
                    have "top1_homeomorphism_on ?U' (subspace_topology A (subspace_topology B TB A) ?U')
                        Vb (subspace_topology ?E0 (subspace_topology E TE ?E0) Vb) (inv_into Vb p)" .
                    from homeomorphism_preserves_path_connected[OF this hU'_pc2] show ?thesis .
                  qed
                  have hVb_conn: "top1_connected_on Vb (subspace_topology ?E0 (subspace_topology E TE ?E0) Vb)"
                    by (rule path_connected_imp_connected[OF hVb_pc])
                  have hVb_sub: "Vb \<subseteq> ?E0"
                    using hV'_sheets hVb(1) unfolding openin_on_def by (by100 blast)
                  \<comment> \<open>Vb connected, meets B' at b, Vb \<subseteq> E0. By maximality: Vb \<subseteq> B'.\<close>
                  have "Vb \<subseteq> B'"
                  proof -
                    have hVbB_sub: "Vb \<union> B' \<subseteq> ?E0"
                      using hVb_sub \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
                    let ?A4 = "\<lambda>i::bool. if i then Vb else B'"
                    have hA4_conn: "\<forall>i\<in>{True, False}. top1_connected_on (?A4 i) (subspace_topology ?E0 (subspace_topology E TE ?E0) (?A4 i))"
                    proof (intro ballI)
                      fix i :: bool assume "i \<in> {True, False}"
                      thus "top1_connected_on (?A4 i) (subspace_topology ?E0 (subspace_topology E TE ?E0) (?A4 i))"
                      proof (cases i)
                        case True thus ?thesis using hVb_conn by (by100 simp)
                      next
                        case False
                        have "top1_connected_on B' (subspace_topology {e \<in> E. p e \<in> A}
                            (subspace_topology E TE {e \<in> E. p e \<in> A}) B')"
                          using hB'_comp unfolding top1_max_conn_comp_def by (by100 blast)
                        thus ?thesis using False by (by100 simp)
                      qed
                    qed
                    have hp4: "b \<in> \<Inter>(?A4 ` {True, False})" using hVb(2) hb_B' by (by100 auto)
                    have hA4_sub: "\<forall>i\<in>{True, False}. ?A4 i \<subseteq> ?E0"
                      using hVb_sub \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 auto)
                    from Theorem_23_3[OF hTE0 _ hA4_sub hA4_conn hp4]
                    have "top1_connected_on (\<Union>i\<in>{True, False}. ?A4 i) (subspace_topology ?E0 (subspace_topology E TE ?E0) (\<Union>i\<in>{True, False}. ?A4 i))"
                      by (by100 blast)
                    have "Vb \<union> B' = (\<Union>i\<in>{True, False}. ?A4 i)" by (by100 auto)
                    hence "top1_connected_on (Vb \<union> B') (subspace_topology ?E0 (subspace_topology E TE ?E0) (Vb \<union> B'))"
                      using \<open>top1_connected_on (\<Union>i\<in>{True, False}. ?A4 i) _\<close> by (by100 simp)
                    from hB'_comp[unfolded top1_max_conn_comp_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
                        rule_format, OF _ hVbB_sub this]
                    show "Vb \<subseteq> B'" by (by100 blast)
                  qed
                  hence "e_a \<in> B'" using \<open>e_a \<in> Vb\<close> by (by100 blast)
                  hence "a \<in> p ` B'" using \<open>p e_a = a\<close> by (by100 blast)
                  thus False using ha_nB by (by100 blast)
                qed
                have "?U' \<subseteq> A" using hW0_sub by (by100 blast)
                have "?U' \<subseteq> A - p ` B'" using \<open>?U' \<subseteq> A\<close> \<open>?U' \<inter> p ` B' = {}\<close> by (by100 blast)
                thus "\<exists>U. U \<in> subspace_topology B TB A \<and> a \<in> U \<and> U \<subseteq> A - p ` B'"
                  using hU'_open \<open>a \<in> ?U'\<close> \<open>?U' \<subseteq> A - p ` B'\<close> by (by100 blast)
              qed
              hence "A - p ` B' = \<Union>{U \<in> subspace_topology B TB A. U \<subseteq> A - p ` B'}"
                by (by5000 blast)
              moreover have "\<Union>{U \<in> subspace_topology B TB A. U \<subseteq> A - p ` B'} \<in> subspace_topology B TB A"
              proof -
                have "{U \<in> subspace_topology B TB A. U \<subseteq> A - p ` B'} \<subseteq> subspace_topology B TB A"
                  by (by100 blast)
                from hTA[unfolded is_topology_on_def, THEN conjunct2, THEN conjunct2, THEN conjunct1,
                    rule_format, OF this]
                show ?thesis .
              qed
              ultimately have "(A - p ` B') \<in> subspace_topology B TB A" by (by100 simp)
              thus ?thesis unfolding openin_on_def by (by100 blast)
            qed
            have "(A - p ` B') \<in> subspace_topology B TB A"
              using hcomp_open unfolding openin_on_def by (by100 blast)
            thus ?thesis unfolding closedin_on_def using \<open>p ` B' \<subseteq> A\<close> by (by100 blast)
          qed
          \<comment> \<open>A is connected and p(B') is clopen and nonempty \<Rightarrow> p(B') = A.\<close>
          have hA_conn: "top1_connected_on A (subspace_topology B TB A)"
          proof -
            have "top1_path_connected_on A (subspace_topology B TB A)"
              using hA_sc unfolding top1_simply_connected_on_def by (by100 blast)
            from path_connected_imp_connected[OF this] show ?thesis .
          qed
          \<comment> \<open>By connected\_iff\_clopen: if A connected and p(B') is both open and closed in A,
             and p(B') nonempty, then p(B') = A.\<close>
          have "p ` B' \<in> subspace_topology B TB A"
            using hpB_open unfolding openin_on_def by (by100 blast)
          have "closedin_on A (subspace_topology B TB A) (p ` B')" using hpB_closed .
          from hA_conn[unfolded connected_iff_clopen[OF hTA], THEN conjunct2,
              rule_format, OF conjI[OF \<open>p ` B' \<in> subspace_topology B TB A\<close> hpB_closed]]
          have "p ` B' = {} \<or> p ` B' = A" .
          thus ?thesis using \<open>p ` B' \<noteq> {}\<close> by (by100 blast)
        qed
        \<comment> \<open>p is continuous from B' to A.\<close>
        have hp_cont_B': "top1_continuous_map_on B' (subspace_topology E TE B')
            A (subspace_topology B TB A) p"
        proof -
          have hp_cont: "top1_continuous_map_on E TE B TB p"
            using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
          have "top1_continuous_map_on B' (subspace_topology E TE B') B TB p"
            by (rule top1_continuous_map_on_subspace_restrict[OF hp_cont \<open>B' \<subseteq> E\<close>])
          \<comment> \<open>Restrict codomain from B to A: since p maps B' into A.\<close>
          have hp_range: "\<forall>b \<in> B'. p b \<in> A"
            using \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
          \<comment> \<open>By continuous restriction to codomain subspace.\<close>
          from continuous_map_restrict_codomain[OF
              \<open>top1_continuous_map_on B' (subspace_topology E TE B') B TB p\<close>
              hp_range hA_sub]
          show ?thesis .
        qed
        \<comment> \<open>p is an open map from B' to A (from covering sheets in B').\<close>
        \<comment> \<open>Construct homeomorphism: p|\_B' is bijective continuous open = homeomorphism.\<close>
        have "\<exists>h. top1_homeomorphism_on A (subspace_topology B TB A) B' (subspace_topology E TE B') h"
        proof -
          \<comment> \<open>p: B' \<rightarrow> A is bijective continuous. Show p is homeomorphism.\<close>
          have hbij: "bij_betw p B' A"
            unfolding bij_betw_def using hp_inj_B' hp_surj_B' by (by100 blast)
          \<comment> \<open>p is an open map from B' to A: for V open in B', p(V) open in A.
             Proof: each point has a covering sheet homeomorphic to an open subset of A.\<close>
          have hB'_top: "is_topology_on B' (subspace_topology E TE B')"
            by (rule subspace_topology_is_topology_on[OF hTE \<open>B' \<subseteq> E\<close>])
          have hp_open_map: "\<forall>V \<in> subspace_topology E TE B'. p ` V \<in> subspace_topology B TB A"
          proof (intro ballI)
            fix V assume hV: "V \<in> subspace_topology E TE B'"
            \<comment> \<open>p(V) is open in A: for each a \<in> p(V), find open nbhd of a in A contained in p(V).\<close>
            have hV_sub: "V \<subseteq> B'"
            proof -
              from hV obtain U0 where "U0 \<in> TE" "V = U0 \<inter> B'"
                unfolding subspace_topology_def by (by100 blast)
              thus ?thesis by (by100 blast)
            qed
            have "p ` V \<subseteq> A" using hV_sub \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
            \<comment> \<open>For each e \<in> V: covering sheet W\_e at e gives W\_e \<subseteq> B' with p|\_W\_e homeomorphism.
               V \<inter> W\_e is open in W\_e (since V is open in B' \<supseteq> W\_e).
               p(V \<inter> W\_e) is open in p(W\_e) \<subseteq> A.\<close>
            have "\<forall>a \<in> p ` V. \<exists>U. U \<in> subspace_topology B TB A \<and> a \<in> U \<and> U \<subseteq> p ` V"
            proof (intro ballI)
              fix a assume "a \<in> p ` V"
              then obtain e where he_V: "e \<in> V" and hpe_a: "p e = a" by (by100 blast)
              have he_B': "e \<in> B'" using he_V hV_sub by (by100 blast)
              have he_E0: "e \<in> ?E0" using he_B' \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
              \<comment> \<open>Get covering sheet We at e.\<close>
              from covering_sheet_over_arc_path_connected[OF hcov_A hA_arc hTE0 hTA he_E0]
              obtain We where hWe_sub: "We \<subseteq> ?E0"
                  and hWe_open: "openin_on ?E0 (subspace_topology E TE ?E0) We" and hWe_e: "e \<in> We"
                  and hWe_pc: "top1_path_connected_on We (subspace_topology ?E0 (subspace_topology E TE ?E0) We)"
                  and hWe_homeo: "top1_homeomorphism_on We (subspace_topology ?E0 (subspace_topology E TE ?E0) We)
                      (p ` We) (subspace_topology A (subspace_topology B TB A) (p ` We)) p"
                  and hWe_ev: "top1_evenly_covered_on ?E0 (subspace_topology E TE ?E0) A (subspace_topology B TB A) p (p ` We)"
                by (by100 blast)
              \<comment> \<open>We \<subseteq> B' by maximality (We connected, meets B' at e).\<close>
              have hWe_conn: "top1_connected_on We (subspace_topology ?E0 (subspace_topology E TE ?E0) We)"
                by (rule path_connected_imp_connected[OF hWe_pc])
              have hWe_sub_B': "We \<subseteq> B'"
              proof -
                have hWeB_sub: "We \<union> B' \<subseteq> ?E0"
                  using hWe_sub \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 blast)
                let ?Ae = "\<lambda>i::bool. if i then We else B'"
                have hAe_conn: "\<forall>i\<in>{True, False}. top1_connected_on (?Ae i) (subspace_topology ?E0 (subspace_topology E TE ?E0) (?Ae i))"
                proof (intro ballI)
                  fix i :: bool assume "i \<in> {True, False}"
                  thus "top1_connected_on (?Ae i) (subspace_topology ?E0 (subspace_topology E TE ?E0) (?Ae i))"
                  proof (cases i)
                    case True thus ?thesis using hWe_conn by (by100 simp)
                  next
                    case False
                    have "top1_connected_on B' (subspace_topology {e \<in> E. p e \<in> A}
                        (subspace_topology E TE {e \<in> E. p e \<in> A}) B')"
                      using hB'_comp unfolding top1_max_conn_comp_def by (by100 blast)
                    thus ?thesis using False by (by100 simp)
                  qed
                qed
                have hpe: "e \<in> \<Inter>(?Ae ` {True, False})" using hWe_e he_B' by (by100 auto)
                have hAe_sub: "\<forall>i\<in>{True, False}. ?Ae i \<subseteq> ?E0"
                  using hWe_sub \<open>B' \<subseteq> {e \<in> E. p e \<in> A}\<close> by (by100 auto)
                from Theorem_23_3[OF hTE0 _ hAe_sub hAe_conn hpe]
                have "top1_connected_on (\<Union>i\<in>{True, False}. ?Ae i) (subspace_topology ?E0 (subspace_topology E TE ?E0) (\<Union>i\<in>{True, False}. ?Ae i))"
                  by (by100 blast)
                have "We \<union> B' = (\<Union>i\<in>{True, False}. ?Ae i)" by (by100 auto)
                hence "top1_connected_on (We \<union> B') (subspace_topology ?E0 (subspace_topology E TE ?E0) (We \<union> B'))"
                  using \<open>top1_connected_on (\<Union>i\<in>{True, False}. ?Ae i) _\<close> by (by100 simp)
                from hB'_comp[unfolded top1_max_conn_comp_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
                    rule_format, OF _ hWeB_sub this]
                show "We \<subseteq> B'" by (by100 blast)
              qed
              \<comment> \<open>V \<inter> We is open in We (V is open in B', We \<subseteq> B').\<close>
              \<comment> \<open>p(V \<inter> We) is open in p(We) (homeomorphism maps open to open).\<close>
              \<comment> \<open>p(We) is open in A.\<close>
              \<comment> \<open>So p(V \<inter> We) is open in A.\<close>
              have hpWe_open: "p ` We \<in> subspace_topology B TB A"
              proof -
                have hTE0_strict: "is_topology_on_strict ?E0 (subspace_topology E TE ?E0)"
                  by (rule subspace_topology_is_strict[OF assms(3) hE0_sub])
                have "We \<in> subspace_topology E TE ?E0"
                  using hWe_open unfolding openin_on_def by (by100 blast)
                from covering_map_is_open_map[OF hcov_A hTE0_strict hTA this] show ?thesis .
              qed
              \<comment> \<open>V \<inter> We open in We: V = U0 \<inter> B' for U0 \<in> TE. We \<subseteq> B'. So V \<inter> We = U0 \<inter> We.\<close>
              \<comment> \<open>U0 \<in> TE. U0 \<inter> ?E0 \<in> subspace. U0 \<inter> We = (U0 \<inter> ?E0) \<inter> We open in We.\<close>
              \<comment> \<open>p maps this open set in We to an open set in p(We) via homeomorphism.\<close>
              have "p ` (V \<inter> We) \<in> subspace_topology B TB A"
              proof -
                \<comment> \<open>V \<inter> We is open in E0 (V open in B', B' subspace of E0, We open in E0).\<close>
                from hV obtain U0 where hU0: "U0 \<in> TE" "V = U0 \<inter> B'"
                  unfolding subspace_topology_def by (by100 blast)
                have "V \<inter> We = U0 \<inter> We" using hU0(2) hWe_sub_B' by (by100 blast)
                have "U0 \<inter> ?E0 \<in> subspace_topology E TE ?E0"
                  unfolding subspace_topology_def using hU0(1) by (by100 blast)
                have "We \<in> subspace_topology E TE ?E0"
                  using hWe_open unfolding openin_on_def by (by100 blast)
                \<comment> \<open>(U0 \<inter> ?E0) \<inter> We = U0 \<inter> We (since We \<subseteq> ?E0).\<close>
                have "(U0 \<inter> ?E0) \<inter> We = U0 \<inter> We" using hWe_sub by (by100 blast)
                \<comment> \<open>Intersection of two open sets in E0 topology is open.\<close>
                have "U0 \<inter> We \<in> subspace_topology E TE ?E0"
                proof -
                  have hTE0_top: "is_topology_on ?E0 (subspace_topology E TE ?E0)" using hTE0 .
                  have "{U0 \<inter> ?E0, We} \<subseteq> subspace_topology E TE ?E0"
                    using \<open>U0 \<inter> ?E0 \<in> subspace_topology E TE ?E0\<close> \<open>We \<in> subspace_topology E TE ?E0\<close>
                    by (by100 blast)
                  moreover have "finite {U0 \<inter> ?E0, We}" by (by100 simp)
                  moreover have "{U0 \<inter> ?E0, We} \<noteq> {}" by (by100 blast)
                  ultimately have "\<Inter>{U0 \<inter> ?E0, We} \<in> subspace_topology E TE ?E0"
                    using hTE0[unfolded is_topology_on_def] by (by100 blast)
                  moreover have "\<Inter>{U0 \<inter> ?E0, We} = U0 \<inter> We" using hWe_sub by (by100 blast)
                  ultimately show ?thesis by (by100 simp)
                qed
                hence "V \<inter> We \<in> subspace_topology E TE ?E0" using \<open>V \<inter> We = U0 \<inter> We\<close> by (by100 simp)
                have hTE0_strict: "is_topology_on_strict ?E0 (subspace_topology E TE ?E0)"
                  by (rule subspace_topology_is_strict[OF assms(3) hE0_sub])
                from covering_map_is_open_map[OF hcov_A hTE0_strict hTA \<open>V \<inter> We \<in> subspace_topology E TE ?E0\<close>]
                show ?thesis .
              qed
              have "a \<in> p ` (V \<inter> We)" using he_V hWe_e hpe_a by (by100 blast)
              have "p ` (V \<inter> We) \<subseteq> p ` V" by (by100 blast)
              thus "\<exists>U. U \<in> subspace_topology B TB A \<and> a \<in> U \<and> U \<subseteq> p ` V"
                using \<open>p ` (V \<inter> We) \<in> subspace_topology B TB A\<close> \<open>a \<in> p ` (V \<inter> We)\<close>
                    \<open>p ` (V \<inter> We) \<subseteq> p ` V\<close> by (by100 blast)
            qed
            hence "p ` V = \<Union>{U \<in> subspace_topology B TB A. U \<subseteq> p ` V}" by (by5000 blast)
            moreover have "\<Union>{U \<in> subspace_topology B TB A. U \<subseteq> p ` V} \<in> subspace_topology B TB A"
            proof -
              have "{U \<in> subspace_topology B TB A. U \<subseteq> p ` V} \<subseteq> subspace_topology B TB A" by (by100 blast)
              from hTA[unfolded is_topology_on_def, THEN conjunct2, THEN conjunct2, THEN conjunct1,
                  rule_format, OF this]
              show ?thesis .
            qed
            ultimately show "p ` V \<in> subspace_topology B TB A" by (by100 simp)
          qed
          \<comment> \<open>inv\_into B' p is continuous from A to B'.\<close>
          have hp_inv_cont: "top1_continuous_map_on A (subspace_topology B TB A)
              B' (subspace_topology E TE B') (inv_into B' p)"
          proof -
            have "\<forall>U \<in> subspace_topology E TE B'. {a \<in> A. inv_into B' p a \<in> U} \<in> subspace_topology B TB A"
            proof (intro ballI)
              fix U assume hU: "U \<in> subspace_topology E TE B'"
              \<comment> \<open>{a \<in> A. inv\_into B' p a \<in> U} = p ` (U \<inter> B') = p ` U (since U \<subseteq> B').\<close>
              have "U \<subseteq> B'"
              proof -
                from hU obtain V where "V \<in> TE" "U = V \<inter> B'"
                  unfolding subspace_topology_def by (by100 blast)
                thus ?thesis by (by100 blast)
              qed
              have "{a \<in> A. inv_into B' p a \<in> U} = p ` U"
              proof (rule set_eqI, rule iffI)
                fix a assume "a \<in> {a \<in> A. inv_into B' p a \<in> U}"
                hence ha: "a \<in> A" "inv_into B' p a \<in> U" by (by100 blast)+
                have "inv_into B' p a \<in> B'" using ha(2) \<open>U \<subseteq> B'\<close> by (by100 blast)
                have "a \<in> p ` B'" using ha(1) hp_surj_B' by (by100 simp)
                have "p (inv_into B' p a) = a"
                  by (rule f_inv_into_f[OF \<open>a \<in> p ` B'\<close>])
                have "inv_into B' p a \<in> U" using ha(2) .
                hence "p (inv_into B' p a) \<in> p ` U" by (rule imageI)
                hence "a \<in> p ` U" using \<open>p (inv_into B' p a) = a\<close> by (by100 simp)
                thus "a \<in> p ` U" .
              next
                fix a assume "a \<in> p ` U"
                then obtain e where he: "e \<in> U" "p e = a" by (by100 blast)
                have he_B': "e \<in> B'" using he(1) \<open>U \<subseteq> B'\<close> by (by100 blast)
                have "a \<in> A" using he(2) hp_surj_B' he_B' by (by100 blast)
                have "inv_into B' p a = e"
                  using inv_into_f_f[OF hp_inj_B' he_B'] he(2) by (by100 simp)
                thus "a \<in> {a \<in> A. inv_into B' p a \<in> U}" using \<open>a \<in> A\<close> he(1) by (by100 simp)
              qed
              thus "{a \<in> A. inv_into B' p a \<in> U} \<in> subspace_topology B TB A"
                using hp_open_map hU by (by100 simp)
            qed
            moreover have "\<forall>a \<in> A. inv_into B' p a \<in> B'"
            proof (intro ballI)
              fix a assume "a \<in> A"
              have "a \<in> p ` B'" using \<open>a \<in> A\<close> hp_surj_B' by (by100 simp)
              thus "inv_into B' p a \<in> B'"
                by (rule inv_into_into[of a p B'])
            qed
            ultimately show ?thesis unfolding top1_continuous_map_on_def by (by5000 blast)
          qed
          \<comment> \<open>Assemble: p: B' \<rightarrow> A is a homeomorphism.\<close>
          have "top1_homeomorphism_on B' (subspace_topology E TE B') A (subspace_topology B TB A) p"
            unfolding top1_homeomorphism_on_def
            using hB'_top hTA hbij hp_cont_B' hp_inv_cont by (by5000 blast)
          \<comment> \<open>Take inverse to get A \<rightarrow> B'.\<close>
          from homeomorphism_inverse[OF this]
          show ?thesis by (by100 blast)
        qed
        then obtain h where hh: "top1_homeomorphism_on A (subspace_topology B TB A) B' (subspace_topology E TE B') h"
          by (by100 blast)
        \<comment> \<open>A is an arc. Homeomorphic image of arc = arc.\<close>
        have "top1_is_arc_on A (subspace_topology B TB A)" using hA_arc .
        then obtain h_arc0 where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
            A (subspace_topology B TB A) h_arc0"
          unfolding top1_is_arc_on_def by (by100 blast)
        \<comment> \<open>Compose: h \<circ> h_arc0: [0,1] \<rightarrow> B' is a homeomorphism.\<close>
        have hB'_strict: "is_topology_on_strict B' (subspace_topology E TE B')"
          by (rule subspace_topology_is_strict[OF assms(3) \<open>B' \<subseteq> E\<close>])
        \<comment> \<open>Compose: [0,1] \<rightarrow>^{h\_arc0} A \<rightarrow>^{h} B'.\<close>
        show ?thesis unfolding top1_is_arc_on_def
        proof (intro conjI)
          show "inj_on p B'" using hp_inj_B' .
          show "p ` B' = A" using hp_surj_B' .
          show "is_topology_on_strict B' (subspace_topology E TE B')" using hB'_strict .
          show "\<exists>h'. top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
              B' (subspace_topology E TE B') h'"
          proof -
            \<comment> \<open>h\_arc0: I \<rightarrow> A continuous.\<close>
            have h1: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                A (subspace_topology B TB A) h_arc0"
              using \<open>top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                  A (subspace_topology B TB A) h_arc0\<close>
              unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>h: A \<rightarrow> B' continuous.\<close>
            have h2: "top1_continuous_map_on A (subspace_topology B TB A)
                B' (subspace_topology E TE B') h"
              using hh unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>Composition h \<circ> h\_arc0 continuous.\<close>
            have hcomp_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                B' (subspace_topology E TE B') (h \<circ> h_arc0)"
              by (rule top1_continuous_map_on_comp[OF h1 h2])
            \<comment> \<open>Bijection: compose bijections.\<close>
            have hb1: "bij_betw h_arc0 top1_unit_interval A"
              using \<open>top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                  A (subspace_topology B TB A) h_arc0\<close>
              unfolding top1_homeomorphism_on_def by (by100 blast)
            have hb2: "bij_betw h A B'"
              using hh unfolding top1_homeomorphism_on_def by (by100 blast)
            have hcomp_bij: "bij_betw (h \<circ> h_arc0) top1_unit_interval B'"
              by (rule bij_betw_trans[OF hb1 hb2])
            \<comment> \<open>[0,1] compact, B' Hausdorff \<Rightarrow> continuous bijection = homeomorphism (Thm 26.6).\<close>
            have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
              unfolding top1_unit_interval_def top1_unit_interval_topology_def
              using Theorem_27_1[of "0::real" 1] by (by100 simp)
            have hB'_haus: "is_hausdorff_on B' (subspace_topology E TE B')"
            proof -
              have "is_hausdorff_on E TE" using hE_haus .
              from conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>B' \<subseteq> E\<close> this
              show ?thesis by (by100 blast)
            qed
            have hI_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
              by (rule top1_unit_interval_topology_is_topology_on)
            have hB'_top: "is_topology_on B' (subspace_topology E TE B')"
              using hB'_strict unfolding is_topology_on_strict_def by (by100 blast)
            from Theorem_26_6[OF hI_top hB'_top hI_compact hB'_haus hcomp_cont hcomp_bij]
            have "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                B' (subspace_topology E TE B') (h \<circ> h_arc0)" .
            thus ?thesis by (by100 blast)
          qed
        qed
      qed
      \<comment> \<open>Surjectivity is now part of hB'\_arc\_and\_inj.\<close>
      show "B' \<subseteq> E \<and> top1_is_arc_on B' (subspace_topology E TE B') \<and> inj_on p B'
          \<and> (\<exists>A0\<in>\<A>B. p ` B' = A0)"
        using hB'_sub_E hB'_arc_and_inj hA by (by100 blast)
    qed
    \<comment> \<open>Extract per-B' surjectivity as a separate fact.\<close>
    have hAE_surj: "\<forall>B'\<in>?\<A>E. \<exists>A0\<in>\<A>B. p ` B' = A0"
      using hAE_arcs by (by100 blast)
    have hAE_cover: "\<Union>?\<A>E = E"
    proof (rule set_eqI, rule iffI)
      fix e assume "e \<in> \<Union>?\<A>E"
      then obtain B' A where "A \<in> \<A>B" "top1_max_conn_comp {e' \<in> E. p e' \<in> A}
          (subspace_topology E TE {e' \<in> E. p e' \<in> A}) B'" "e \<in> B'"
        by (by100 blast)
      from max_conn_comp_mem[OF this(2) this(3)] show "e \<in> E" by (by100 blast)
    next
      fix e assume he: "e \<in> E"
      have "p e \<in> B" using he assms(2) unfolding top1_covering_map_on_def by (by100 blast)
      then obtain A where hA: "A \<in> \<A>B" "p e \<in> A" using hcover by (by100 blast)
      have "e \<in> {e' \<in> E. p e' \<in> A}" using he hA(2) by (by100 blast)
      \<comment> \<open>e is in a maximal connected component of p\<inverse>(A).\<close>
      have hTE: "is_topology_on E TE" using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
      have "{e' \<in> E. p e' \<in> A} \<subseteq> E" by (by100 blast)
      have hT_sub: "is_topology_on {e' \<in> E. p e' \<in> A}
          (subspace_topology E TE {e' \<in> E. p e' \<in> A})"
        by (rule subspace_topology_is_topology_on[OF hTE \<open>{e' \<in> E. p e' \<in> A} \<subseteq> E\<close>])
      from max_conn_comp_covers[OF hT_sub \<open>e \<in> {e' \<in> E. p e' \<in> A}\<close>]
      obtain B' where "top1_max_conn_comp {e' \<in> E. p e' \<in> A}
          (subspace_topology E TE {e' \<in> E. p e' \<in> A}) B'" "e \<in> B'" by (by100 blast)
      hence "B' \<in> {B'. top1_max_conn_comp {e' \<in> E. p e' \<in> A}
          (subspace_topology E TE {e' \<in> E. p e' \<in> A}) B'}" by (by100 blast)
      hence "B' \<in> ?\<A>E" using hA(1) by (by100 blast)
      thus "e \<in> \<Union>?\<A>E" using \<open>e \<in> B'\<close> by (by100 blast)
    qed
    have hAE_intersect: "\<forall>A'\<in>?\<A>E. \<forall>B'\<in>?\<A>E. A' \<noteq> B' \<longrightarrow>
         A' \<inter> B' \<subseteq> top1_arc_endpoints_on A' (subspace_topology E TE A')
       \<and> A' \<inter> B' \<subseteq> top1_arc_endpoints_on B' (subspace_topology E TE B')
       \<and> finite (A' \<inter> B') \<and> card (A' \<inter> B') \<le> 2"
    proof (intro ballI impI)
      fix A1' A2' assume hA1: "A1' \<in> ?\<A>E" and hA2: "A2' \<in> ?\<A>E" and hne: "A1' \<noteq> A2'"
      \<comment> \<open>A1' comes from base arc A1, A2' from A2.\<close>
      from hA1 obtain A1 where hA1_base: "A1 \<in> \<A>B"
          and hA1_comp: "top1_max_conn_comp {e \<in> E. p e \<in> A1} (subspace_topology E TE {e \<in> E. p e \<in> A1}) A1'"
        by (by100 blast)
      from hA2 obtain A2 where hA2_base: "A2 \<in> \<A>B"
          and hA2_comp: "top1_max_conn_comp {e \<in> E. p e \<in> A2} (subspace_topology E TE {e \<in> E. p e \<in> A2}) A2'"
        by (by100 blast)
      have hA1'_sub: "A1' \<subseteq> {e \<in> E. p e \<in> A1}" using max_conn_comp_sub[OF hA1_comp] .
      have hA2'_sub: "A2' \<subseteq> {e \<in> E. p e \<in> A2}" using max_conn_comp_sub[OF hA2_comp] .
      have hA1'_sub_E: "A1' \<subseteq> E" using hA1'_sub by (by100 blast)
      have hA2'_sub_E: "A2' \<subseteq> E" using hA2'_sub by (by100 blast)
      \<comment> \<open>The intersection A1' \<inter> A2' maps under p into A1 \<inter> A2.\<close>
      have hp_inter: "p ` (A1' \<inter> A2') \<subseteq> A1 \<inter> A2"
        using hA1'_sub hA2'_sub by (by100 blast)
      show "A1' \<inter> A2' \<subseteq> top1_arc_endpoints_on A1' (subspace_topology E TE A1')
         \<and> A1' \<inter> A2' \<subseteq> top1_arc_endpoints_on A2' (subspace_topology E TE A2')
         \<and> finite (A1' \<inter> A2') \<and> card (A1' \<inter> A2') \<le> 2"
      proof (cases "A1 = A2")
        case True
        \<comment> \<open>Same base arc: A1' and A2' are different components of p\<inverse>(A1). Hence disjoint.\<close>
        have "A1' \<inter> A2' = {}"
        proof (rule ccontr)
          assume "A1' \<inter> A2' \<noteq> {}"
          \<comment> \<open>A1' and A2' are max connected components of p\<inverse>(A1) = p\<inverse>(A2) (since A1=A2).\<close>
          have hA2_comp': "top1_max_conn_comp {e \<in> E. p e \<in> A1} (subspace_topology E TE {e \<in> E. p e \<in> A1}) A2'"
            using hA2_comp True by (by100 simp)
          \<comment> \<open>B1 \<inter> B2 \<noteq> {} \<Rightarrow> B1 \<union> B2 connected \<Rightarrow> B1 = B2 by maximality.\<close>
          obtain z where "z \<in> A1'" "z \<in> A2'" using \<open>A1' \<inter> A2' \<noteq> {}\<close> by (by100 blast)
          have hTE_loc: "is_topology_on E TE"
            using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
          have hTE_A1: "is_topology_on {e \<in> E. p e \<in> A1} (subspace_topology E TE {e \<in> E. p e \<in> A1})"
            by (rule subspace_topology_is_topology_on[OF hTE_loc, of "{e \<in> E. p e \<in> A1}"])
               (by100 blast)
          \<comment> \<open>A1' \<union> A2' connected (Theorem 23.3).\<close>
          let ?A12 = "\<lambda>i::bool. if i then A1' else A2'"
          have hA12_sub: "\<forall>i\<in>{True, False}. ?A12 i \<subseteq> {e \<in> E. p e \<in> A1}"
            using hA1'_sub hA2'_sub True by (by100 auto)
          have hA1'_conn: "top1_connected_on A1' (subspace_topology {e \<in> E. p e \<in> A1} (subspace_topology E TE {e \<in> E. p e \<in> A1}) A1')"
            using hA1_comp unfolding top1_max_conn_comp_def by (by100 blast)
          have hA2'_conn: "top1_connected_on A2' (subspace_topology {e \<in> E. p e \<in> A1} (subspace_topology E TE {e \<in> E. p e \<in> A1}) A2')"
            using hA2_comp' unfolding top1_max_conn_comp_def by (by100 blast)
          have hA12_conn: "\<forall>i\<in>{True, False}. top1_connected_on (?A12 i) (subspace_topology {e \<in> E. p e \<in> A1} (subspace_topology E TE {e \<in> E. p e \<in> A1}) (?A12 i))"
            using hA1'_conn hA2'_conn by (by100 auto)
          have "z \<in> \<Inter>(?A12 ` {True, False})" using \<open>z \<in> A1'\<close> \<open>z \<in> A2'\<close> by (by100 auto)
          from Theorem_23_3[OF hTE_A1 _ hA12_sub hA12_conn this]
          have "top1_connected_on (\<Union>i\<in>{True, False}. ?A12 i) (subspace_topology {e \<in> E. p e \<in> A1} (subspace_topology E TE {e \<in> E. p e \<in> A1}) (\<Union>i\<in>{True, False}. ?A12 i))"
            by (by100 blast)
          have "A1' \<union> A2' = (\<Union>i\<in>{True, False}. ?A12 i)" by (by100 auto)
          hence hU_conn: "top1_connected_on (A1' \<union> A2') (subspace_topology {e \<in> E. p e \<in> A1} (subspace_topology E TE {e \<in> E. p e \<in> A1}) (A1' \<union> A2'))"
            using \<open>top1_connected_on (\<Union>i\<in>{True, False}. ?A12 i) _\<close> by (by100 simp)
          have "A1' \<union> A2' \<subseteq> {e \<in> E. p e \<in> A1}" using hA1'_sub hA2'_sub True by (by100 blast)
          from hA1_comp[unfolded top1_max_conn_comp_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
              rule_format, OF _ this hU_conn]
          have "A1' \<union> A2' = A1'" by (by100 blast)
          hence "A2' \<subseteq> A1'" by (by100 blast)
          \<comment> \<open>Similarly A1' \<subseteq> A2'. So A1' = A2'.\<close>
          from hA2_comp'[unfolded top1_max_conn_comp_def, THEN conjunct2, THEN conjunct2, THEN conjunct2,
              rule_format, OF _ \<open>A1' \<union> A2' \<subseteq> {e \<in> E. p e \<in> A1}\<close> hU_conn]
          have "A1' \<union> A2' = A2'" by (by100 blast)
          hence "A1' \<subseteq> A2'" by (by100 blast)
          hence "A1' = A2'" using \<open>A2' \<subseteq> A1'\<close> by (by100 blast)
          thus False using hne by (by100 blast)
        qed
        thus ?thesis by (by100 simp)
      next
        case False
        \<comment> \<open>Different base arcs: A1 \<inter> A2 \<subseteq> endpoints (from base graph).\<close>
        have hbase_inter: "A1 \<inter> A2 \<subseteq> top1_arc_endpoints_on A1 (subspace_topology B TB A1)
            \<and> A1 \<inter> A2 \<subseteq> top1_arc_endpoints_on A2 (subspace_topology B TB A2)
            \<and> finite (A1 \<inter> A2) \<and> card (A1 \<inter> A2) \<le> 2"
          using hAB_inter[rule_format, OF hA1_base hA2_base False] by (by100 blast)
        \<comment> \<open>p maps A1' \<inter> A2' into A1 \<inter> A2 (at most 2 points).
           p is injective on A1' and on A2'. Each point of A1 \<inter> A2 has at most 1 preimage in A1'
           and at most 1 in A2'. So |A1' \<inter> A2'| \<le> |A1 \<inter> A2| \<le> 2.\<close>
        \<comment> \<open>Points of A1' \<inter> A2' are endpoints of A1' and A2' (pulled back from endpoints of A1, A2).\<close>
        \<comment> \<open>|A1' \<inter> A2'| \<le> |A1 \<inter> A2| \<le> 2 (p injective on A1', p maps A1'\<inter>A2' into A1\<inter>A2).\<close>
        \<comment> \<open>Endpoint property: p maps endpoints of A1' to endpoints of A1.\<close>
        have "finite (A1' \<inter> A2') \<and> card (A1' \<inter> A2') \<le> 2"
        proof -
          have "inj_on p A1'" using hAE_arcs hA1 by (by100 blast)
          have hA12_sub_A1: "A1' \<inter> A2' \<subseteq> A1'" by (by100 blast)
          have "inj_on p (A1' \<inter> A2')" by (rule inj_on_subset[OF \<open>inj_on p A1'\<close> hA12_sub_A1])
          have "p ` (A1' \<inter> A2') \<subseteq> A1 \<inter> A2" using hp_inter .
          have "finite (A1 \<inter> A2)" using hbase_inter by (by100 blast)
          have "card (A1 \<inter> A2) \<le> 2" using hbase_inter by (by100 blast)
          have "finite (A1' \<inter> A2')"
            using finite_imageD[OF finite_subset[OF \<open>p ` (A1' \<inter> A2') \<subseteq> A1 \<inter> A2\<close> \<open>finite (A1 \<inter> A2)\<close>]
                \<open>inj_on p (A1' \<inter> A2')\<close>] .
          moreover have "card (A1' \<inter> A2') \<le> 2"
          proof -
            have "card (A1' \<inter> A2') = card (p ` (A1' \<inter> A2'))"
              using card_image[OF \<open>inj_on p (A1' \<inter> A2')\<close>] by (by100 simp)
            also have "... \<le> card (A1 \<inter> A2)"
              by (rule card_mono[OF \<open>finite (A1 \<inter> A2)\<close> \<open>p ` (A1' \<inter> A2') \<subseteq> A1 \<inter> A2\<close>])
            also have "... \<le> 2" using \<open>card (A1 \<inter> A2) \<le> 2\<close> .
            finally show ?thesis .
          qed
          ultimately show ?thesis by (by100 blast)
        qed
        moreover have "A1' \<inter> A2' \<subseteq> top1_arc_endpoints_on A1' (subspace_topology E TE A1')"
        proof -
          \<comment> \<open>From hAE\_surj: p maps A1' onto A1. With inj\_on: p|A1' is a bijection A1' \<rightarrow> A1.
             With continuity + open map: homeomorphism. Then arc\_endpoints\_under\_homeomorphism
             gives: endpoints of A1' map to endpoints of A1 under p.
             For e \<in> A1'\<inter>A2': p(e) \<in> endpoints(A1). So e \<in> p\<inverse>(endpoints(A1)) \<inter> A1' = endpoints(A1').\<close>
          show ?thesis
          proof (intro subsetI)
            fix e assume he: "e \<in> A1' \<inter> A2'"
            have he_A1': "e \<in> A1'" using he by (by100 blast)
            have hpe_ep: "p e \<in> top1_arc_endpoints_on A1 (subspace_topology B TB A1)"
              using hp_inter he hbase_inter by (by100 blast)
            \<comment> \<open>Step 1: Construct homeomorphism p: A1' \<rightarrow> A1 via Theorem 26.6.\<close>
            have hp_A1_surj: "p ` A1' = A1"
            proof -
              \<comment> \<open>A1' \<subseteq> p\<inverse>(A1) (from hA1\_comp). So p(A1') \<subseteq> A1.\<close>
              have "p ` A1' \<subseteq> A1" using hA1'_sub by (by100 blast)
              \<comment> \<open>From hAE\_surj: p(A1') = some A0 \<in> \<A>B.\<close>
              from hAE_surj[rule_format, OF hA1] obtain A0 where
                "A0 \<in> \<A>B" "p ` A1' = A0" by (by100 blast)
              \<comment> \<open>A0 = p(A1') \<subseteq> A1. Both A0, A1 \<in> \<A>B. If A0 \<noteq> A1: |A0 \<inter> A1| \<le> 2.
                 But A0 \<subseteq> A1 means A0 = A0 \<inter> A1. Card(A0) \<le> 2. But A0 is an arc (infinite). \<bot>.\<close>
              have "A0 \<subseteq> A1" using \<open>p ` A1' = A0\<close> \<open>p ` A1' \<subseteq> A1\<close> by (by100 blast)
              have "A0 = A1"
              proof (rule ccontr)
                assume "A0 \<noteq> A1"
                from hAB_inter[rule_format, OF \<open>A0 \<in> \<A>B\<close> hA1_base this]
                have "finite (A0 \<inter> A1) \<and> card (A0 \<inter> A1) \<le> 2" by (by100 blast)
                have "A0 \<inter> A1 = A0" using \<open>A0 \<subseteq> A1\<close> by (by100 blast)
                hence "finite A0 \<and> card A0 \<le> 2" using \<open>finite (A0 \<inter> A1) \<and> _\<close> by (by100 simp)
                \<comment> \<open>But A0 is an arc (infinite). Contradiction.\<close>
                have "top1_is_arc_on A0 (subspace_topology B TB A0)"
                  using hAB \<open>A0 \<in> \<A>B\<close> by (by100 blast)
                hence "\<not> finite A0"
                proof -
                  obtain h0 where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                      A0 (subspace_topology B TB A0) h0"
                    using \<open>top1_is_arc_on A0 (subspace_topology B TB A0)\<close>
                    unfolding top1_is_arc_on_def by (by100 blast)
                  hence "bij_betw h0 top1_unit_interval A0"
                    unfolding top1_homeomorphism_on_def by (by100 blast)
                  have "infinite top1_unit_interval"
                  proof -
                    have "\<And>n::nat. 1 / (real n + 2) \<in> top1_unit_interval"
                      unfolding top1_unit_interval_def by (by100 auto)
                    have "inj (\<lambda>n::nat. 1 / (real n + 2))"
                    proof (rule injI)
                      fix m n :: nat assume "1 / (real m + 2) = 1 / (real n + 2)"
                      hence "real m + 2 = real n + 2" by (by100 auto)
                      thus "m = n" by (by100 auto)
                    qed
                    hence "infinite (range (\<lambda>n::nat. 1 / (real n + 2)))"
                      using finite_imageD by (by100 blast)
                    moreover have "range (\<lambda>n::nat. 1 / (real n + 2)) \<subseteq> top1_unit_interval"
                      using \<open>\<And>n. 1 / (real n + 2) \<in> top1_unit_interval\<close> by (by100 blast)
                    ultimately show ?thesis using infinite_super by (by100 blast)
                  qed
                  from bij_betw_finite[OF \<open>bij_betw h0 top1_unit_interval A0\<close>]
                  show ?thesis using \<open>infinite top1_unit_interval\<close> by (by100 blast)
                qed
                thus False using \<open>finite A0 \<and> card A0 \<le> 2\<close> by (by100 blast)
              qed
              thus ?thesis using \<open>p ` A1' = A0\<close> by (by100 simp)
            qed
            have hp_A1_inj: "inj_on p A1'" using hAE_arcs hA1 by (by5000 blast)
            have hp_A1_bij: "bij_betw p A1' A1"
              unfolding bij_betw_def using hp_A1_inj hp_A1_surj by (by100 blast)
            have hA1'_arc: "top1_is_arc_on A1' (subspace_topology E TE A1')"
              using hAE_arcs hA1 by (by100 blast)
            have hA1'_strict: "is_topology_on_strict A1' (subspace_topology E TE A1')"
              using hA1'_arc unfolding top1_is_arc_on_def by (by100 blast)
            have hA1_strict: "is_topology_on_strict A1 (subspace_topology B TB A1)"
            proof -
              have hA1_arc: "top1_is_arc_on A1 (subspace_topology B TB A1)"
                using hAB hA1_base by (by100 blast)
              thus ?thesis unfolding top1_is_arc_on_def by (by100 blast)
            qed
            have hA1'_compact: "top1_compact_on A1' (subspace_topology E TE A1')"
            proof -
              obtain h1' where hh1': "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                  A1' (subspace_topology E TE A1') h1'"
                using hA1'_arc unfolding top1_is_arc_on_def by (by100 blast)
              have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
                unfolding top1_unit_interval_def top1_unit_interval_topology_def
                using Theorem_27_1[of "0::real" 1] by (by100 simp)
              have hI_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
                using hh1' unfolding top1_homeomorphism_on_def by (by100 blast)
              have hA1'_top: "is_topology_on A1' (subspace_topology E TE A1')"
                using hA1'_strict unfolding is_topology_on_strict_def by (by100 blast)
              have hh1'_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  A1' (subspace_topology E TE A1') h1'"
                using hh1' unfolding top1_homeomorphism_on_def by (by100 blast)
              have "h1' ` top1_unit_interval = A1'"
                using hh1' unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              from top1_compact_on_continuous_image[OF hI_compact hA1'_top hh1'_cont]
              have "top1_compact_on (h1' ` top1_unit_interval) (subspace_topology A1' (subspace_topology E TE A1') (h1' ` top1_unit_interval))" .
              have "subspace_topology A1' (subspace_topology E TE A1') (h1' ` top1_unit_interval) = subspace_topology E TE A1'"
                using subspace_topology_trans[of A1' A1'] \<open>h1' ` top1_unit_interval = A1'\<close> by (by100 simp)
              thus ?thesis using \<open>top1_compact_on (h1' ` top1_unit_interval) _\<close>
                  \<open>h1' ` top1_unit_interval = A1'\<close> by (by100 simp)
            qed
            have hA1_haus: "is_hausdorff_on A1 (subspace_topology B TB A1)"
            proof -
              have "is_hausdorff_on B TB"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              have "A1 \<subseteq> B" using hAB hA1_base by (by100 blast)
              from conjunct2[OF conjunct2[OF Theorem_17_11]] this \<open>is_hausdorff_on B TB\<close>
              show ?thesis by (by100 blast)
            qed
            have hp_A1_cont: "top1_continuous_map_on A1' (subspace_topology E TE A1')
                A1 (subspace_topology B TB A1) p"
            proof -
              have hp_cont: "top1_continuous_map_on E TE B TB p"
                using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
              have "top1_continuous_map_on A1' (subspace_topology E TE A1') B TB p"
                by (rule top1_continuous_map_on_subspace_restrict[OF hp_cont hA1'_sub_E])
              have "\<forall>e \<in> A1'. p e \<in> A1" using hA1'_sub by (by100 blast)
              have "A1 \<subseteq> B" using hAB hA1_base by (by100 blast)
              from continuous_map_restrict_codomain[OF
                  \<open>top1_continuous_map_on A1' (subspace_topology E TE A1') B TB p\<close>
                  \<open>\<forall>e \<in> A1'. p e \<in> A1\<close> this]
              show ?thesis .
            qed
            have hp_A1_homeo: "top1_homeomorphism_on A1' (subspace_topology E TE A1')
                A1 (subspace_topology B TB A1) p"
            proof -
              have hA1'_top: "is_topology_on A1' (subspace_topology E TE A1')"
                using hA1'_strict unfolding is_topology_on_strict_def by (by100 blast)
              have hA1_top: "is_topology_on A1 (subspace_topology B TB A1)"
                using hA1_strict unfolding is_topology_on_strict_def by (by100 blast)
              from Theorem_26_6[OF hA1'_top hA1_top hA1'_compact hA1_haus hp_A1_cont hp_A1_bij]
              show ?thesis .
            qed
            \<comment> \<open>Step 2: p(e) endpoint of A1 \<Rightarrow> A1 - {p(e)} connected.\<close>
            have hA1_minus_connected: "top1_connected_on (A1 - {p e}) (subspace_topology A1 (subspace_topology B TB A1) (A1 - {p e}))"
              using hpe_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
            \<comment> \<open>Step 3: A1' - {e} \<cong> A1 - {p(e)} via p (restriction of homeomorphism).\<close>
            \<comment> \<open>Step 4: A1' - {e} connected (homeomorphic to connected).\<close>
            have "top1_connected_on (A1' - {e}) (subspace_topology A1' (subspace_topology E TE A1') (A1' - {e}))"
            proof -
              \<comment> \<open>inv\_into A1' p: A1 \<rightarrow> A1' is continuous (inverse of homeomorphism).\<close>
              let ?g = "inv_into A1' p"
              have hg_cont: "top1_continuous_map_on A1 (subspace_topology B TB A1) A1' (subspace_topology E TE A1') ?g"
                using hp_A1_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
              \<comment> \<open>A1 - {p(e)} is connected.\<close>
              have hA1_minus_conn: "top1_connected_on (A1 - {p e})
                  (subspace_topology A1 (subspace_topology B TB A1) (A1 - {p e}))"
                using hpe_ep unfolding top1_arc_endpoints_on_def by (by100 blast)
              \<comment> \<open>Restrict g to A1 - {p(e)}: continuous.\<close>
              have hg_restrict: "top1_continuous_map_on (A1 - {p e})
                  (subspace_topology A1 (subspace_topology B TB A1) (A1 - {p e}))
                  A1' (subspace_topology E TE A1') ?g"
                by (rule top1_continuous_map_on_subspace_restrict[OF hg_cont]) (by100 blast)
              \<comment> \<open>Image: g ` (A1 - {p(e)}) = A1' - {e}.\<close>
              have "?g ` (A1 - {p e}) = A1' - {e}"
              proof -
                have "bij_betw ?g A1 A1'" using bij_betw_inv_into[OF hp_A1_bij] .
                hence "?g ` A1 = A1'" unfolding bij_betw_def by (by100 blast)
                have "inj_on ?g A1" using \<open>bij_betw ?g A1 A1'\<close> unfolding bij_betw_def by (by100 blast)
                have "?g (p e) = e"
                  using inv_into_f_f[OF hp_A1_inj he_A1'] by (by100 simp)
                have "p e \<in> A1" using hA1'_sub he_A1' by (by100 blast)
                show ?thesis
                proof (rule set_eqI, rule iffI)
                  fix x assume "x \<in> ?g ` (A1 - {p e})"
                  then obtain a where ha: "a \<in> A1" "a \<noteq> p e" "?g a = x" by (by100 blast)
                  have "x \<in> A1'" using \<open>?g ` A1 = A1'\<close> ha(1) ha(3) by (by100 blast)
                  have "x \<noteq> e"
                  proof
                    assume "x = e"
                    hence "?g a = ?g (p e)" using ha(3) \<open>?g (p e) = e\<close> by (by100 simp)
                    from inj_onD[OF \<open>inj_on ?g A1\<close> this ha(1) \<open>p e \<in> A1\<close>]
                    show False using ha(2) by (by100 blast)
                  qed
                  thus "x \<in> A1' - {e}" using \<open>x \<in> A1'\<close> \<open>x \<noteq> e\<close> by (by100 blast)
                next
                  fix x assume "x \<in> A1' - {e}"
                  hence hx: "x \<in> A1'" "x \<noteq> e" by (by100 blast)+
                  have "x \<in> ?g ` A1" using \<open>?g ` A1 = A1'\<close> hx(1) by (by100 blast)
                  then obtain a where "a \<in> A1" "?g a = x" by (by100 blast)
                  have "a \<noteq> p e" using \<open>?g a = x\<close> \<open>?g (p e) = e\<close> hx(2) by (by100 blast)
                  thus "x \<in> ?g ` (A1 - {p e})" using \<open>a \<in> A1\<close> \<open>?g a = x\<close> \<open>a \<noteq> p e\<close> by (by100 blast)
                qed
              qed
              \<comment> \<open>By Theorem 23.5: g(A1-{pe}) connected in subspace of A1'.\<close>
              have hA1'_top: "is_topology_on A1' (subspace_topology E TE A1')"
                using hA1'_strict unfolding is_topology_on_strict_def by (by100 blast)
              have hA1_minus_top: "is_topology_on (A1 - {p e})
                  (subspace_topology A1 (subspace_topology B TB A1) (A1 - {p e}))"
              proof -
                have "is_topology_on A1 (subspace_topology B TB A1)"
                  using hA1_strict unfolding is_topology_on_strict_def by (by100 blast)
                have "A1 - {p e} \<subseteq> A1" by (by100 blast)
                from subspace_topology_is_topology_on[OF \<open>is_topology_on A1 _\<close> this] show ?thesis .
              qed
              from Theorem_23_5[OF hA1_minus_top hA1'_top hA1_minus_conn hg_restrict]
              have "top1_connected_on (?g ` (A1 - {p e}))
                  (subspace_topology A1' (subspace_topology E TE A1') (?g ` (A1 - {p e})))" .
              thus ?thesis using \<open>?g ` (A1 - {p e}) = A1' - {e}\<close> by (by100 simp)
            qed
            \<comment> \<open>Step 5: e is an endpoint of A1'.\<close>
            thus "e \<in> top1_arc_endpoints_on A1' (subspace_topology E TE A1')"
              unfolding top1_arc_endpoints_on_def using he_A1' by (by100 blast)
          qed
        qed
        moreover have "A1' \<inter> A2' \<subseteq> top1_arc_endpoints_on A2' (subspace_topology E TE A2')"
        proof -
          show ?thesis
          proof (intro subsetI)
            fix e assume he: "e \<in> A1' \<inter> A2'"
            have he_A2': "e \<in> A2'" using he by (by100 blast)
            have hpe_ep2: "p e \<in> top1_arc_endpoints_on A2 (subspace_topology B TB A2)"
              using hp_inter he hbase_inter by (by100 blast)
            \<comment> \<open>Same as A1': construct homeomorphism p|A2' \<rightarrow> A2, transport connectedness.\<close>
            have hp_A2_surj: "p ` A2' = A2"
            proof -
              have "p ` A2' \<subseteq> A2" using hA2'_sub by (by100 blast)
              from hAE_surj[rule_format, OF hA2] obtain A2_base where
                "A2_base \<in> \<A>B" "p ` A2' = A2_base" by (by100 blast)
              have "A2_base \<subseteq> A2" using \<open>p ` A2' = A2_base\<close> \<open>p ` A2' \<subseteq> A2\<close> by (by100 blast)
              have "A2_base = A2"
              proof (rule ccontr)
                assume "A2_base \<noteq> A2"
                have hfin_A2b: "finite (A2_base \<inter> A2) \<and> card (A2_base \<inter> A2) \<le> 2"
                  using hAB_inter[rule_format, OF \<open>A2_base \<in> \<A>B\<close> hA2_base \<open>A2_base \<noteq> A2\<close>] by (by100 blast)
                have "A2_base \<inter> A2 = A2_base" using \<open>A2_base \<subseteq> A2\<close> by (by100 blast)
                hence "finite A2_base \<and> card A2_base \<le> 2" using hfin_A2b by (by100 simp)
                have "top1_is_arc_on A2_base (subspace_topology B TB A2_base)"
                  using hAB \<open>A2_base \<in> \<A>B\<close> by (by100 blast)
                then obtain h0 where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                    A2_base (subspace_topology B TB A2_base) h0"
                  unfolding top1_is_arc_on_def by (by100 blast)
                hence "bij_betw h0 top1_unit_interval A2_base"
                  unfolding top1_homeomorphism_on_def by (by100 blast)
                have "infinite top1_unit_interval"
                proof -
                  have "inj (\<lambda>n::nat. 1 / (real n + 2))"
                  proof (rule injI)
                    fix m n :: nat assume "1 / (real m + 2) = 1 / (real n + 2)"
                    hence "real m + 2 = real n + 2" by (by100 auto)
                    thus "m = n" by (by100 auto)
                  qed
                  hence "infinite (range (\<lambda>n::nat. 1 / (real n + 2)))"
                    using finite_imageD by (by100 blast)
                  moreover have "range (\<lambda>n::nat. 1 / (real n + 2)) \<subseteq> top1_unit_interval"
                    unfolding top1_unit_interval_def by (by100 auto)
                  ultimately show ?thesis using infinite_super by (by100 blast)
                qed
                from bij_betw_finite[OF \<open>bij_betw h0 top1_unit_interval A2_base\<close>]
                have "\<not> finite A2_base" using \<open>infinite top1_unit_interval\<close> by (by100 blast)
                thus False using \<open>finite A2_base \<and> _\<close> by (by100 blast)
              qed
              thus ?thesis using \<open>p ` A2' = A2_base\<close> by (by100 simp)
            qed
            have hp_A2_inj: "inj_on p A2'" using hAE_arcs hA2 by (by5000 blast)
            have hp_A2_bij: "bij_betw p A2' A2"
              unfolding bij_betw_def using hp_A2_inj hp_A2_surj by (by100 blast)
            have hA2'_arc: "top1_is_arc_on A2' (subspace_topology E TE A2')"
              using hAE_arcs hA2 by (by5000 blast)
            have hA2'_strict: "is_topology_on_strict A2' (subspace_topology E TE A2')"
              using hA2'_arc unfolding top1_is_arc_on_def by (by100 blast)
            have hA2_strict: "is_topology_on_strict A2 (subspace_topology B TB A2)"
            proof -
              have "top1_is_arc_on A2 (subspace_topology B TB A2)"
                using hAB hA2_base by (by100 blast)
              thus ?thesis unfolding top1_is_arc_on_def by (by100 blast)
            qed
            have hA2'_compact: "top1_compact_on A2' (subspace_topology E TE A2')"
            proof -
              obtain h2' where hh2': "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                  A2' (subspace_topology E TE A2') h2'"
                using hA2'_arc unfolding top1_is_arc_on_def by (by100 blast)
              have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
                unfolding top1_unit_interval_def top1_unit_interval_topology_def
                using Theorem_27_1[of "0::real" 1] by (by100 simp)
              have hA2'_top: "is_topology_on A2' (subspace_topology E TE A2')"
                using hA2'_strict unfolding is_topology_on_strict_def by (by100 blast)
              have hh2'_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  A2' (subspace_topology E TE A2') h2'"
                using hh2' unfolding top1_homeomorphism_on_def by (by100 blast)
              have "h2' ` top1_unit_interval = A2'"
                using hh2' unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
              from top1_compact_on_continuous_image[OF hI_compact hA2'_top hh2'_cont]
              have "top1_compact_on (h2' ` top1_unit_interval) (subspace_topology A2' (subspace_topology E TE A2') (h2' ` top1_unit_interval))" .
              have "subspace_topology A2' (subspace_topology E TE A2') (h2' ` top1_unit_interval) = subspace_topology E TE A2'"
                using subspace_topology_trans[of A2' A2'] \<open>h2' ` top1_unit_interval = A2'\<close> by (by100 simp)
              thus ?thesis using \<open>top1_compact_on (h2' ` top1_unit_interval) _\<close> \<open>h2' ` top1_unit_interval = A2'\<close>
                by (by100 simp)
            qed
            have hA2_haus: "is_hausdorff_on A2 (subspace_topology B TB A2)"
            proof -
              have "is_hausdorff_on B TB"
                using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
              have "A2 \<subseteq> B" using hAB hA2_base by (by100 blast)
              from conjunct2[OF conjunct2[OF Theorem_17_11]] this \<open>is_hausdorff_on B TB\<close>
              show ?thesis by (by100 blast)
            qed
            have hp_A2_cont: "top1_continuous_map_on A2' (subspace_topology E TE A2')
                A2 (subspace_topology B TB A2) p"
            proof -
              have hp_cont: "top1_continuous_map_on E TE B TB p"
                using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
              have "top1_continuous_map_on A2' (subspace_topology E TE A2') B TB p"
                by (rule top1_continuous_map_on_subspace_restrict[OF hp_cont hA2'_sub_E])
              have "\<forall>e \<in> A2'. p e \<in> A2" using hA2'_sub by (by100 blast)
              have "A2 \<subseteq> B" using hAB hA2_base by (by100 blast)
              from continuous_map_restrict_codomain[OF
                  \<open>top1_continuous_map_on A2' (subspace_topology E TE A2') B TB p\<close>
                  \<open>\<forall>e \<in> A2'. p e \<in> A2\<close> this]
              show ?thesis .
            qed
            have hp_A2_homeo: "top1_homeomorphism_on A2' (subspace_topology E TE A2')
                A2 (subspace_topology B TB A2) p"
            proof -
              have hA2'_top: "is_topology_on A2' (subspace_topology E TE A2')"
                using hA2'_strict unfolding is_topology_on_strict_def by (by100 blast)
              have hA2_top: "is_topology_on A2 (subspace_topology B TB A2)"
                using hA2_strict unfolding is_topology_on_strict_def by (by100 blast)
              from Theorem_26_6[OF hA2'_top hA2_top hA2'_compact hA2_haus hp_A2_cont hp_A2_bij]
              show ?thesis .
            qed
            have hA2_minus_connected: "top1_connected_on (A2 - {p e})
                (subspace_topology A2 (subspace_topology B TB A2) (A2 - {p e}))"
              using hpe_ep2 unfolding top1_arc_endpoints_on_def by (by100 blast)
            have "top1_connected_on (A2' - {e})
                (subspace_topology A2' (subspace_topology E TE A2') (A2' - {e}))"
            proof -
              let ?g2 = "inv_into A2' p"
              have hg2_cont: "top1_continuous_map_on A2 (subspace_topology B TB A2) A2' (subspace_topology E TE A2') ?g2"
                using hp_A2_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
              have hg2_restrict: "top1_continuous_map_on (A2 - {p e})
                  (subspace_topology A2 (subspace_topology B TB A2) (A2 - {p e}))
                  A2' (subspace_topology E TE A2') ?g2"
                by (rule top1_continuous_map_on_subspace_restrict[OF hg2_cont]) (by100 blast)
              have hg2_bij: "bij_betw ?g2 A2 A2'" using bij_betw_inv_into[OF hp_A2_bij] .
              have "?g2 ` A2 = A2'" using hg2_bij unfolding bij_betw_def by (by100 blast)
              have "inj_on ?g2 A2" using hg2_bij unfolding bij_betw_def by (by100 blast)
              have "?g2 (p e) = e"
                using inv_into_f_f[OF hp_A2_inj he_A2'] by (by100 simp)
              have "p e \<in> A2" using hA2'_sub he_A2' by (by100 blast)
              have "?g2 ` (A2 - {p e}) = A2' - {e}"
              proof (rule set_eqI, rule iffI)
                fix x assume "x \<in> ?g2 ` (A2 - {p e})"
                then obtain a where ha: "a \<in> A2" "a \<noteq> p e" "?g2 a = x" by (by100 blast)
                have "x \<in> A2'" using \<open>?g2 ` A2 = A2'\<close> ha(1) ha(3) by (by100 blast)
                have "x \<noteq> e"
                proof assume "x = e"
                  hence "?g2 a = ?g2 (p e)" using ha(3) \<open>?g2 (p e) = e\<close> by (by100 simp)
                  from inj_onD[OF \<open>inj_on ?g2 A2\<close> this ha(1) \<open>p e \<in> A2\<close>]
                  show False using ha(2) by (by100 blast)
                qed
                thus "x \<in> A2' - {e}" using \<open>x \<in> A2'\<close> by (by100 blast)
              next
                fix x assume "x \<in> A2' - {e}"
                hence hx: "x \<in> A2'" "x \<noteq> e" by (by100 blast)+
                have "x \<in> ?g2 ` A2" using \<open>?g2 ` A2 = A2'\<close> hx(1) by (by100 blast)
                then obtain a where "a \<in> A2" "?g2 a = x" by (by100 blast)
                have "a \<noteq> p e" using \<open>?g2 a = x\<close> \<open>?g2 (p e) = e\<close> hx(2) by (by100 blast)
                thus "x \<in> ?g2 ` (A2 - {p e})" using \<open>a \<in> A2\<close> \<open>?g2 a = x\<close> by (by100 blast)
              qed
              have hA2_minus_top: "is_topology_on (A2 - {p e})
                  (subspace_topology A2 (subspace_topology B TB A2) (A2 - {p e}))"
              proof -
                have "is_topology_on A2 (subspace_topology B TB A2)"
                  using hA2_strict unfolding is_topology_on_strict_def by (by100 blast)
                have "A2 - {p e} \<subseteq> A2" by (by100 blast)
                from subspace_topology_is_topology_on[OF \<open>is_topology_on A2 _\<close> this] show ?thesis .
              qed
              have hA2'_top: "is_topology_on A2' (subspace_topology E TE A2')"
                using hA2'_strict unfolding is_topology_on_strict_def by (by100 blast)
              from Theorem_23_5[OF hA2_minus_top hA2'_top hA2_minus_connected hg2_restrict]
              have "top1_connected_on (?g2 ` (A2 - {p e}))
                  (subspace_topology A2' (subspace_topology E TE A2') (?g2 ` (A2 - {p e})))" .
              thus ?thesis using \<open>?g2 ` (A2 - {p e}) = A2' - {e}\<close> by (by100 simp)
            qed
            thus "e \<in> top1_arc_endpoints_on A2' (subspace_topology E TE A2')"
              unfolding top1_arc_endpoints_on_def using he_A2' by (by100 blast)
          qed
        qed
        ultimately show ?thesis by (by100 blast)
      qed
    qed
    have hAE_topology: "\<forall>C. C \<subseteq> E \<longrightarrow>
         (closedin_on E TE C \<longleftrightarrow>
          (\<forall>A'\<in>?\<A>E. closedin_on A' (subspace_topology E TE A') (A' \<inter> C)))"
    proof (intro allI impI)
      fix C assume hC_sub: "C \<subseteq> E"
      show "closedin_on E TE C \<longleftrightarrow>
          (\<forall>A'\<in>?\<A>E. closedin_on A' (subspace_topology E TE A') (A' \<inter> C))"
      proof (rule iffI)
        \<comment> \<open>Forward: C closed in E \<Rightarrow> C \<inter> A' closed in A' for all A'.\<close>
        assume hC_cl: "closedin_on E TE C"
        show "\<forall>A'\<in>?\<A>E. closedin_on A' (subspace_topology E TE A') (A' \<inter> C)"
        proof (intro ballI)
          fix A' assume "A' \<in> ?\<A>E"
          have "A' \<subseteq> E" using hAE_arcs \<open>A' \<in> ?\<A>E\<close> by (by100 blast)
          have hTE: "is_topology_on E TE"
            using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
          have "A' \<inter> C = C \<inter> A'" by (by100 blast)
          moreover have "closedin_on E TE C" using hC_cl .
          ultimately show "closedin_on A' (subspace_topology E TE A') (A' \<inter> C)"
            using Theorem_17_2[OF hTE \<open>A' \<subseteq> E\<close>] by (by100 blast)
        qed
      next
        \<comment> \<open>Backward: all A' \<inter> C closed in A' \<Rightarrow> C closed in E.\<close>
        assume hall: "\<forall>A'\<in>?\<A>E. closedin_on A' (subspace_topology E TE A') (A' \<inter> C)"
        \<comment> \<open>Munkres Step 3: Show E \\ C is open in E.
           Step 3a: p(E\\C) is open in B (using coherent topology of B).
           Step 3b: For each slice V, (E\\C) \<inter> V is open in E.
           Step 3c: E\\C = \<Union>{(E\\C) \<inter> V | V slice} is open in E.\<close>
        \<comment> \<open>Equivalently: E \\ C is open in E. We use Munkres's Step 3.\<close>
        let ?W = "E - C"
        have hW_sub: "?W \<subseteq> E" by (by100 blast)
        \<comment> \<open>Step 3a: p(?W) is open in B (using coherent topology of B, i.e., hAB\_coh).\<close>
        \<comment> \<open>For each A\<alpha> \<in> \<A>B: p(?W) \<inter> A\<alpha> is open in A\<alpha>.
           p(?W) \<inter> A\<alpha> = p(?W \<inter> p\<inverse>(A\<alpha>)). ?W \<inter> p\<inverse>(A\<alpha>) = \<Union>{?W \<inter> B' | B' component of p\<inverse>(A\<alpha>)}.
           p(?W \<inter> B') is open in A\<alpha> (p|B' homeomorphism, ?W \<inter> B' open in B' since
           B' \\ (?W \<inter> B') = B' \<inter> C which is closed in B' by assumption).\<close>
        \<comment> \<open>Note: p(?W) open in B is not needed directly; we work with individual slices.\<close>
        \<comment> \<open>Step 3b+3c: p(?W) open in B, covering slices, lift to E.\<close>
        \<comment> \<open>For each e \<in> ?W: p(e) \<in> p(?W) which is open in B.
           Get evenly covered U of p(e). The slice V containing e is open in E.
           p maps V homeomorphically to U. V \<inter> ?W = p|\_V\<inverse>(p(?W) \<inter> U).
           p(?W) \<inter> U is open in U (since p(?W) is open in B and U is open in B).
           So V \<inter> ?W is open in V (homeomorphism), hence open in E.
           Hence ?W = \<Union>{V \<inter> ?W | ...} is open in E.\<close>
        have "openin_on E TE ?W"
        proof -
          \<comment> \<open>For each e \<in> ?W, find an open nbhd of e in ?W.
             Get evenly covered U of p(e). Slice V containing e. V open in E.
             V \<inter> ?W is open in E: use the fact that p|V is a homeomorphism
             and p(V \<inter> ?W) is open in U.
             To show p(V \<inter> ?W) is open in U:
             V \<inter> ?W = V \<inter> (E - C). For each B' \<in> \<A>E: (E-C) \<inter> B' is open in B'.
             V \<inter> B' is open in B' (V is open in E, so V \<inter> B' is open in B').
             Hence V \<inter> ?W \<inter> B' = V \<inter> (E-C) \<inter> B' is open in B'.
             p maps V \<inter> B' homeomorphically to part of base arc A\<alpha>.
             p(V \<inter> ?W \<inter> B') is open in A\<alpha>.
             p(V \<inter> ?W) = \<Union>{p(V \<inter> ?W \<inter> B') | B'} is a union of sets open in their arcs.
             By coherent topology of B: p(V \<inter> ?W) is open in B.
             p(V \<inter> ?W) \<subseteq> U (since V maps into U). So p(V \<inter> ?W) is open in U.
             p|V homeomorphism, so V \<inter> ?W = (p|V)\<inverse>(p(V \<inter> ?W)) is open in V, hence open in E.\<close>
          \<comment> \<open>Every point of ?W has an open nbhd in ?W (by above).\<close>
          \<comment> \<open>?W = union of these nbhds, hence open.\<close>
          have "?W \<subseteq> E" by (by100 blast)
          moreover have "?W \<in> TE"
          proof -
            \<comment> \<open>For each e \<in> ?W, find an open V\_e \<in> TE with e \<in> V\_e \<subseteq> ?W.\<close>
            have "\<forall>e \<in> ?W. \<exists>V \<in> TE. e \<in> V \<and> V \<subseteq> ?W"
            proof (intro ballI)
              fix e assume he_W: "e \<in> ?W"
              hence he_E: "e \<in> E" and he_nC: "e \<notin> C" by (by100 blast)+
              have hpe: "p e \<in> B"
                using assms(2) he_E unfolding top1_covering_map_on_def by (by100 blast)
              obtain U \<V> where hU_pe: "p e \<in> U"
                  and hev: "top1_evenly_covered_on E TE B TB p U"
                using assms(2) hpe unfolding top1_covering_map_on_def by (by100 blast)
              \<comment> \<open>Extract the sheet V containing e from evenly covered U.\<close>
              obtain V where hV_e: "e \<in> V" and hV_open: "openin_on E TE V"
                  and hV_homeo: "top1_homeomorphism_on V (subspace_topology E TE V) U (subspace_topology B TB U) p"
              proof -
                obtain \<V> where hV_all: "(\<forall>V\<in>\<V>. openin_on E TE V)
                    \<and> (\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {})
                    \<and> {x \<in> E. p x \<in> U} = \<Union>\<V>
                    \<and> (\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U (subspace_topology B TB U) p)"
                  using hev unfolding top1_evenly_covered_on_def
                  apply (elim conjE exE) apply (rule that) apply (by100 blast)+ done
                have "e \<in> {x \<in> E. p x \<in> U}" using he_E hU_pe by (by100 blast)
                hence "e \<in> \<Union>\<V>" using hV_all by (by100 blast)
                then obtain V0 where "V0 \<in> \<V>" "e \<in> V0" by (by100 blast)
                show ?thesis
                  apply (rule that[of V0])
                  using \<open>V0 \<in> \<V>\<close> \<open>e \<in> V0\<close> hV_all by (by100 blast)+
              qed
              \<comment> \<open>p(V \<inter> ?W) is open in B (coherent topology of B).\<close>
              have hpVW_open: "openin_on B TB (p ` (V \<inter> ?W))"
              proof -
                \<comment> \<open>Use coherent topology (open version): S open in B iff S \<inter> A\<alpha> open in A\<alpha> for all A\<alpha>.\<close>
                \<comment> \<open>Derived from hAB\_coh by complementation.\<close>
                have hpVW_sub_B: "p ` (V \<inter> ?W) \<subseteq> B"
                proof -
                  have "V \<subseteq> E" using hV_open unfolding openin_on_def by (by100 blast)
                  have "p ` E = B" using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
                  thus ?thesis using \<open>V \<subseteq> E\<close> by (by100 blast)
                qed
                \<comment> \<open>B \\ p(V \<inter> ?W) is closed in B iff for each A\<alpha>, A\<alpha> \<inter> (B \\ p(V\<inter>?W)) closed in A\<alpha>.
                   Equivalently, A\<alpha> \\ p(V\<inter>?W) closed in A\<alpha>.
                   Equivalently, A\<alpha> \<inter> p(V\<inter>?W) open in A\<alpha>.\<close>
                have hcompl_sub: "B - p ` (V \<inter> ?W) \<subseteq> B" by (by100 blast)
                have "closedin_on B TB (B - p ` (V \<inter> ?W))
                    \<longleftrightarrow> (\<forall>A\<in>\<A>B. closedin_on A (subspace_topology B TB A) (A \<inter> (B - p ` (V \<inter> ?W))))"
                  using hAB_coh[rule_format, OF hcompl_sub] .
                \<comment> \<open>Show: for each A\<alpha> \<in> \<A>B, A\<alpha> \<inter> (B \\ p(V\<inter>?W)) is closed in A\<alpha>.
                   Equivalently, A\<alpha> \<inter> p(V\<inter>?W) is open in A\<alpha>.\<close>
                have "\<forall>A0\<in>\<A>B. closedin_on A0 (subspace_topology B TB A0) (A0 \<inter> (B - p ` (V \<inter> ?W)))"
                proof (intro ballI)
                  fix A0 assume hA0: "A0 \<in> \<A>B"
                  have hA0_sub: "A0 \<subseteq> B" using hAB hA0 by (by100 blast)
                  \<comment> \<open>A0 \<inter> (B \\ p(V\<inter>?W)) = A0 \\ p(V\<inter>?W).
                     Its complement in A0 is A0 \<inter> p(V\<inter>?W).
                     We show A0 \<inter> p(V\<inter>?W) is open in A0.\<close>
                  have "A0 \<inter> (B - p ` (V \<inter> ?W)) = A0 - p ` (V \<inter> ?W)" using hA0_sub by (by100 blast)
                  \<comment> \<open>A0 \<inter> p(V\<inter>?W) = p((V\<inter>?W) \<inter> p\<inverse>(A0)).\<close>
                  \<comment> \<open>The key: V \<inter> p\<inverse>(A0) meets at most one lifted arc B' over A0.
                     (V\<inter>?W) \<inter> p\<inverse>(A0) = V \<inter> (E-C) \<inter> p\<inverse>(A0).
                     This is open in B' (V open in E gives V\<inter>B' open in B';
                     (E-C)\<inter>B' open in B' from hall). Their intersection is open in B'.
                     p maps it to an open subset of A0.\<close>
                  have "openin_on A0 (subspace_topology B TB A0) (A0 \<inter> p ` (V \<inter> ?W))"
                  proof -
                    \<comment> \<open>Book argument (Munkres 83.4 Step 3): A0 \<inter> p(V\<inter>?W) is a union of sets
                       open in A0. For each arc B' of E over A0: V\<inter>?W\<inter>B' open in B'
                       (V\<inter>B' open, (E-C)\<inter>B' open from hall); p|B' homeomorphism \<rightarrow> image open.\<close>
                    have hV_sub_E: "V \<subseteq> E" using hV_open unfolding openin_on_def by (by100 blast)
                    have hTE_loc: "is_topology_on E TE"
                      using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
                    have hTB_loc: "is_topology_on B TB"
                      using assms(1) unfolding top1_is_graph_on_def is_hausdorff_on_def by (by100 blast)
                    have hTA0: "is_topology_on A0 (subspace_topology B TB A0)"
                      by (rule subspace_topology_is_topology_on[OF hTB_loc hA0_sub])
                    \<comment> \<open>Per-point open neighborhoods.\<close>
                    have hper_point: "\<forall>a\<in>A0 \<inter> p ` (V \<inter> ?W).
                        \<exists>S. S \<in> subspace_topology B TB A0 \<and> a \<in> S \<and> S \<subseteq> A0 \<inter> p ` (V \<inter> ?W)"
                    proof (intro ballI)
                      fix a assume ha: "a \<in> A0 \<inter> p ` (V \<inter> ?W)"
                      then obtain ea where hea: "ea \<in> V" "ea \<notin> C" "p ea = a" "a \<in> A0"
                        by (by100 blast)
                      have hea_E: "ea \<in> E" using hea(1) hV_sub_E by (by100 blast)
                      have hpea_A0: "p ea \<in> A0" using hea(3,4) by (by100 simp)
                      \<comment> \<open>Find arc B' \<in> \<A>E with ea \<in> B' and p(B') = A0.\<close>
                      have hea_preA0: "ea \<in> {e' \<in> E. p e' \<in> A0}" using hea_E hpea_A0 by (by100 blast)
                      have hTpreA0: "is_topology_on {e' \<in> E. p e' \<in> A0}
                          (subspace_topology E TE {e' \<in> E. p e' \<in> A0})"
                        by (rule subspace_topology_is_topology_on[OF hTE_loc]) (by100 blast)
                      from max_conn_comp_covers[OF hTpreA0 hea_preA0]
                      obtain B' where hB'_comp: "top1_max_conn_comp {e' \<in> E. p e' \<in> A0}
                          (subspace_topology E TE {e' \<in> E. p e' \<in> A0}) B'"
                          and hea_B': "ea \<in> B'" by (by100 blast)
                      have hB'_AE: "B' \<in> ?\<A>E" using hB'_comp hA0 by (by100 blast)
                      have hB'_sub_E: "B' \<subseteq> E" using hAE_arcs hB'_AE by (by100 blast)
                      have hB'_arc: "top1_is_arc_on B' (subspace_topology E TE B')"
                        using hAE_arcs hB'_AE by (by100 blast)
                      have hB'_inj: "inj_on p B'" using hAE_arcs hB'_AE by (by100 blast)
                      \<comment> \<open>p(B') = A0 (arc-infinite argument).\<close>
                      have hB'_surj: "p ` B' = A0"
                      proof -
                        from hAE_arcs hB'_AE obtain A_base where hAb: "A_base \<in> \<A>B" "p ` B' = A_base"
                          by (by100 blast)
                        have "B' \<subseteq> {e' \<in> E. p e' \<in> A0}" using max_conn_comp_sub[OF hB'_comp] .
                        hence "p ` B' \<subseteq> A0" by (by100 blast)
                        hence "A_base \<subseteq> A0" using hAb(2) by (by100 simp)
                        have "A_base = A0"
                        proof (rule ccontr)
                          assume "A_base \<noteq> A0"
                          from hAB_inter[rule_format, OF hAb(1) hA0 this]
                          have hfin: "finite (A_base \<inter> A0) \<and> card (A_base \<inter> A0) \<le> 2" by (by100 blast)
                          have "A_base \<inter> A0 = A_base" using \<open>A_base \<subseteq> A0\<close> by (by100 blast)
                          hence "finite A_base \<and> card A_base \<le> 2" using hfin by (by100 simp)
                          have "top1_is_arc_on A_base (subspace_topology B TB A_base)"
                            using hAB hAb(1) by (by100 blast)
                          then obtain h0 where "top1_homeomorphism_on top1_unit_interval
                              top1_unit_interval_topology A_base (subspace_topology B TB A_base) h0"
                            unfolding top1_is_arc_on_def by (by100 blast)
                          hence "bij_betw h0 top1_unit_interval A_base"
                            unfolding top1_homeomorphism_on_def by (by100 blast)
                          have "infinite top1_unit_interval"
                          proof -
                            have "inj (\<lambda>n::nat. 1 / (real n + 2))"
                            proof (rule injI)
                              fix m n :: nat assume "1 / (real m + 2) = 1 / (real n + 2)"
                              hence "real m + 2 = real n + 2" by (by100 auto)
                              thus "m = n" by (by100 auto)
                            qed
                            hence "infinite (range (\<lambda>n::nat. 1 / (real n + 2)))"
                              using finite_imageD by (by100 blast)
                            moreover have "range (\<lambda>n::nat. 1 / (real n + 2)) \<subseteq> top1_unit_interval"
                              unfolding top1_unit_interval_def by (by100 auto)
                            ultimately show ?thesis using infinite_super by (by100 blast)
                          qed
                          from bij_betw_finite[OF \<open>bij_betw h0 top1_unit_interval A_base\<close>]
                          have "\<not> finite A_base" using \<open>infinite top1_unit_interval\<close> by (by100 blast)
                          thus False using \<open>finite A_base \<and> _\<close> by (by100 blast)
                        qed
                        thus ?thesis using hAb(2) by (by100 simp)
                      qed
                      have hB'_bij: "bij_betw p B' A0"
                        unfolding bij_betw_def using hB'_inj hB'_surj by (by100 blast)
                      \<comment> \<open>V \<inter> ?W \<inter> B' is open in B'.\<close>
                      have hB'_strict: "is_topology_on_strict B' (subspace_topology E TE B')"
                        using hB'_arc unfolding top1_is_arc_on_def by (by100 blast)
                      have hTB': "is_topology_on B' (subspace_topology E TE B')"
                        using hB'_strict unfolding is_topology_on_strict_def by (by100 blast)
                      have hV_open_B': "V \<inter> B' \<in> subspace_topology E TE B'"
                      proof -
                        have "V \<in> TE" using hV_open unfolding openin_on_def by (by100 blast)
                        thus ?thesis unfolding subspace_topology_def by (by100 blast)
                      qed
                      have hW_open_B': "?W \<inter> B' \<in> subspace_topology E TE B'"
                      proof -
                        from hall[rule_format, OF hB'_AE]
                        have "closedin_on B' (subspace_topology E TE B') (B' \<inter> C)" .
                        hence "B' - (B' \<inter> C) \<in> subspace_topology E TE B'"
                          unfolding closedin_on_def by (by100 blast)
                        have "?W \<inter> B' = B' - (B' \<inter> C)" using hB'_sub_E by (by100 blast)
                        thus ?thesis using \<open>B' - (B' \<inter> C) \<in> _\<close> by (by100 simp)
                      qed
                      have hVWB'_open: "V \<inter> ?W \<inter> B' \<in> subspace_topology E TE B'"
                      proof -
                        have heq: "V \<inter> ?W \<inter> B' = (V \<inter> B') \<inter> (?W \<inter> B')" by (by100 blast)
                        have hF_sub: "{V \<inter> B', ?W \<inter> B'} \<subseteq> subspace_topology E TE B'"
                          using hV_open_B' hW_open_B' by (by100 blast)
                        have hF_fin: "finite {V \<inter> B', ?W \<inter> B'}" by (by100 simp)
                        have hF_ne: "{V \<inter> B', ?W \<inter> B'} \<noteq> {}" by (by100 blast)
                        have hconj: "finite {V \<inter> B', ?W \<inter> B'} \<and> {V \<inter> B', ?W \<inter> B'} \<noteq> {} \<and>
                            {V \<inter> B', ?W \<inter> B'} \<subseteq> subspace_topology E TE B'"
                          using hF_fin hF_ne hF_sub by (by100 blast)
                        from hTB'[unfolded is_topology_on_def, THEN conjunct2, THEN conjunct2,
                            THEN conjunct2, rule_format, OF hconj]
                        have "\<Inter>{V \<inter> B', ?W \<inter> B'} \<in> subspace_topology E TE B'" .
                        moreover have "\<Inter>{V \<inter> B', ?W \<inter> B'} = (V \<inter> B') \<inter> (?W \<inter> B')" by (by100 auto)
                        ultimately show ?thesis using heq by (by100 simp)
                      qed
                      \<comment> \<open>p|B' homeomorphism B' \<rightarrow> A0 (Theorem 26.6).\<close>
                      have hp_homeo_B': "top1_homeomorphism_on B' (subspace_topology E TE B')
                          A0 (subspace_topology B TB A0) p"
                      proof -
                        have hB'_compact: "top1_compact_on B' (subspace_topology E TE B')"
                        proof -
                          obtain hB where hhB: "top1_homeomorphism_on top1_unit_interval
                              top1_unit_interval_topology B' (subspace_topology E TE B') hB"
                            using hB'_arc unfolding top1_is_arc_on_def by (by100 blast)
                          have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
                            unfolding top1_unit_interval_def top1_unit_interval_topology_def
                            using Theorem_27_1[of "0::real" 1] by (by100 simp)
                          have "hB ` top1_unit_interval = B'"
                            using hhB unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
                          have hhB_cont: "top1_continuous_map_on top1_unit_interval
                              top1_unit_interval_topology B' (subspace_topology E TE B') hB"
                            using hhB unfolding top1_homeomorphism_on_def by (by100 blast)
                          from top1_compact_on_continuous_image[OF hI_compact hTB' hhB_cont]
                          have "top1_compact_on (hB ` top1_unit_interval)
                              (subspace_topology B' (subspace_topology E TE B') (hB ` top1_unit_interval))" .
                          have "subspace_topology B' (subspace_topology E TE B') (hB ` top1_unit_interval) =
                              subspace_topology E TE B'"
                            using subspace_topology_trans[of B' B'] \<open>hB ` top1_unit_interval = B'\<close>
                            by (by100 simp)
                          thus ?thesis using \<open>top1_compact_on (hB ` top1_unit_interval) _\<close>
                              \<open>hB ` top1_unit_interval = B'\<close> by (by100 simp)
                        qed
                        have hA0_haus: "is_hausdorff_on A0 (subspace_topology B TB A0)"
                        proof -
                          have "is_hausdorff_on B TB"
                            using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                          from conjunct2[OF conjunct2[OF Theorem_17_11]] hA0_sub this
                          show ?thesis by (by100 blast)
                        qed
                        have hp_cont_B': "top1_continuous_map_on B' (subspace_topology E TE B')
                            A0 (subspace_topology B TB A0) p"
                        proof -
                          have hp_cont: "top1_continuous_map_on E TE B TB p"
                            using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
                          have "top1_continuous_map_on B' (subspace_topology E TE B') B TB p"
                            by (rule top1_continuous_map_on_subspace_restrict[OF hp_cont hB'_sub_E])
                          have "\<forall>e \<in> B'. p e \<in> A0"
                            using max_conn_comp_sub[OF hB'_comp] by (by100 blast)
                          from continuous_map_restrict_codomain[OF
                              \<open>top1_continuous_map_on B' _ B TB p\<close> this hA0_sub]
                          show ?thesis .
                        qed
                        from Theorem_26_6[OF hTB' hTA0 hB'_compact hA0_haus hp_cont_B' hB'_bij]
                        show ?thesis .
                      qed
                      \<comment> \<open>p maps open subsets of B' to open subsets of A0.\<close>
                      have hp_inv_cont: "top1_continuous_map_on A0 (subspace_topology B TB A0)
                          B' (subspace_topology E TE B') (inv_into B' p)"
                        using hp_homeo_B' unfolding top1_homeomorphism_on_def by (by100 blast)
                      have hpVWB'_open_A0: "p ` (V \<inter> ?W \<inter> B') \<in> subspace_topology B TB A0"
                      proof -
                        have hinv_pre: "{a \<in> A0. inv_into B' p a \<in> V \<inter> ?W \<inter> B'} \<in>
                            subspace_topology B TB A0"
                          using hp_inv_cont hVWB'_open
                          unfolding top1_continuous_map_on_def by (by100 blast)
                        have "{a \<in> A0. inv_into B' p a \<in> V \<inter> ?W \<inter> B'} = p ` (V \<inter> ?W \<inter> B')"
                        proof (rule set_eqI, rule iffI)
                          fix a assume "a \<in> {a \<in> A0. inv_into B' p a \<in> V \<inter> ?W \<inter> B'}"
                          hence ha_loc: "a \<in> A0" "inv_into B' p a \<in> V \<inter> ?W \<inter> B'"
                            by (by100 blast)+
                          have "p (inv_into B' p a) = a"
                            using f_inv_into_f[of a p B'] hB'_surj ha_loc(1) by (by100 simp)
                          hence "a = p (inv_into B' p a)" by (by100 simp)
                          thus "a \<in> p ` (V \<inter> ?W \<inter> B')"
                            using ha_loc(2) image_eqI by (by100 blast)
                        next
                          fix a assume "a \<in> p ` (V \<inter> ?W \<inter> B')"
                          then obtain e' where he': "e' \<in> V \<inter> ?W \<inter> B'" "p e' = a" by (by100 blast)
                          have "a \<in> A0" using he'(2) hB'_surj he'(1) by (by100 blast)
                          have "inv_into B' p a = e'"
                          proof -
                            have "e' \<in> B'" using he'(1) by (by100 blast)
                            from inv_into_f_f[OF hB'_inj this]
                            show ?thesis using he'(2) by (by100 simp)
                          qed
                          thus "a \<in> {a \<in> A0. inv_into B' p a \<in> V \<inter> ?W \<inter> B'}"
                            using \<open>a \<in> A0\<close> he'(1) by (by100 simp)
                        qed
                        thus ?thesis using hinv_pre by (by100 simp)
                      qed
                      \<comment> \<open>Assembly: a \<in> p(V\<inter>?W\<inter>B') \<subseteq> A0 \<inter> p(V\<inter>?W).\<close>
                      have "ea \<in> V \<inter> ?W \<inter> B'" using hea hea_E hea_B' by (by100 blast)
                      have "a \<in> p ` (V \<inter> ?W \<inter> B')" using \<open>ea \<in> V \<inter> ?W \<inter> B'\<close> hea(3) by (by100 blast)
                      have "p ` (V \<inter> ?W \<inter> B') \<subseteq> A0 \<inter> p ` (V \<inter> ?W)"
                        using hB'_surj by (by100 blast)
                      show "\<exists>S. S \<in> subspace_topology B TB A0 \<and> a \<in> S \<and> S \<subseteq> A0 \<inter> p ` (V \<inter> ?W)"
                        using hpVWB'_open_A0 \<open>a \<in> p ` (V \<inter> ?W \<inter> B')\<close>
                            \<open>p ` (V \<inter> ?W \<inter> B') \<subseteq> _\<close> by (by100 blast)
                    qed
                    \<comment> \<open>Union of open neighborhoods is open.\<close>
                    have "A0 \<inter> p ` (V \<inter> ?W) \<subseteq> A0" by (by100 blast)
                    have "A0 \<inter> p ` (V \<inter> ?W) =
                        \<Union>{S \<in> subspace_topology B TB A0. S \<subseteq> A0 \<inter> p ` (V \<inter> ?W)}"
                    proof (rule set_eqI, rule iffI)
                      fix a assume "a \<in> A0 \<inter> p ` (V \<inter> ?W)"
                      from hper_point[rule_format, OF this]
                      obtain S where "S \<in> subspace_topology B TB A0" "a \<in> S"
                          "S \<subseteq> A0 \<inter> p ` (V \<inter> ?W)" by (by100 blast)
                      thus "a \<in> \<Union>{S \<in> subspace_topology B TB A0. S \<subseteq> A0 \<inter> p ` (V \<inter> ?W)}"
                        by (by100 blast)
                    next
                      fix a assume "a \<in> \<Union>{S \<in> subspace_topology B TB A0. S \<subseteq> A0 \<inter> p ` (V \<inter> ?W)}"
                      thus "a \<in> A0 \<inter> p ` (V \<inter> ?W)" by (by100 blast)
                    qed
                    have "{S \<in> subspace_topology B TB A0. S \<subseteq> A0 \<inter> p ` (V \<inter> ?W)} \<subseteq>
                        subspace_topology B TB A0" by (by100 blast)
                    from hTA0[unfolded is_topology_on_def, THEN conjunct2, THEN conjunct2,
                        THEN conjunct1, rule_format, OF this]
                    have "\<Union>{S \<in> subspace_topology B TB A0. S \<subseteq> A0 \<inter> p ` (V \<inter> ?W)} \<in>
                        subspace_topology B TB A0" .
                    hence "A0 \<inter> p ` (V \<inter> ?W) \<in> subspace_topology B TB A0"
                      using \<open>A0 \<inter> p ` (V \<inter> ?W) = \<Union>_\<close> by (by100 simp)
                    show ?thesis unfolding openin_on_def
                      using \<open>A0 \<inter> p ` (V \<inter> ?W) \<in> subspace_topology B TB A0\<close>
                          \<open>A0 \<inter> p ` (V \<inter> ?W) \<subseteq> A0\<close> by (by100 blast)
                  qed
                  \<comment> \<open>Decomposition approach replaces old per-point argument.\<close>
                  have "A0 \<inter> p ` (V \<inter> ?W) \<in> subspace_topology B TB A0"
                    using \<open>openin_on A0 _ (A0 \<inter> p ` (V \<inter> ?W))\<close> unfolding openin_on_def by (by100 blast)
                  have "A0 - (A0 \<inter> p ` (V \<inter> ?W)) \<subseteq> A0" by (by100 blast)
                  have "A0 - (A0 - (A0 \<inter> p ` (V \<inter> ?W))) = A0 \<inter> p ` (V \<inter> ?W)" by (by100 blast)
                  hence "A0 - (A0 - (A0 \<inter> p ` (V \<inter> ?W))) \<in> subspace_topology B TB A0"
                    using \<open>A0 \<inter> p ` (V \<inter> ?W) \<in> subspace_topology B TB A0\<close> by (by100 simp)
                  hence "closedin_on A0 (subspace_topology B TB A0) (A0 - (A0 \<inter> p ` (V \<inter> ?W)))"
                    unfolding closedin_on_def using \<open>A0 - (A0 \<inter> p ` (V \<inter> ?W)) \<subseteq> A0\<close> by (by100 blast)
                  have "A0 - (A0 \<inter> p ` (V \<inter> ?W)) = A0 - p ` (V \<inter> ?W)" by (by100 blast)
                  thus "closedin_on A0 (subspace_topology B TB A0) (A0 \<inter> (B - p ` (V \<inter> ?W)))"
                    using \<open>closedin_on A0 _ (A0 - (A0 \<inter> p ` (V \<inter> ?W)))\<close>
                        \<open>A0 \<inter> (B - p ` (V \<inter> ?W)) = A0 - p ` (V \<inter> ?W)\<close>
                        \<open>A0 - (A0 \<inter> p ` (V \<inter> ?W)) = A0 - p ` (V \<inter> ?W)\<close>
                    by (by100 simp)
                qed
                hence "closedin_on B TB (B - p ` (V \<inter> ?W))"
                  using \<open>closedin_on B TB (B - p ` (V \<inter> ?W)) \<longleftrightarrow> _\<close> by (by100 blast)
                hence "B - p ` (V \<inter> ?W) \<subseteq> B \<and> (B - (B - p ` (V \<inter> ?W))) \<in> TB"
                  unfolding closedin_on_def by (by100 blast)
                have "B - (B - p ` (V \<inter> ?W)) = p ` (V \<inter> ?W)" using hpVW_sub_B by (by100 blast)
                hence "p ` (V \<inter> ?W) \<in> TB" using \<open>_ \<and> (B - (B - p ` (V \<inter> ?W))) \<in> TB\<close> by (by100 simp)
                thus ?thesis unfolding openin_on_def using hpVW_sub_B by (by100 blast)
              qed
              \<comment> \<open>p(V \<inter> ?W) \<subseteq> U (since V maps into U). So p(V \<inter> ?W) open in U.\<close>
              \<comment> \<open>(p|V)\<inverse>(p(V \<inter> ?W)) = V \<inter> ?W (p injective on V). Open in V (homeomorphism).\<close>
              \<comment> \<open>V \<inter> ?W is open in V, V open in E, so V \<inter> ?W is open in E.\<close>
              have hVW_TE: "V \<inter> ?W \<in> TE"
              proof -
                \<comment> \<open>p(V \<inter> ?W) \<subseteq> U.\<close>
                have hpVW_sub_U: "p ` (V \<inter> ?W) \<subseteq> U"
                proof -
                  have "bij_betw p V U" using hV_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
                  hence "p ` V = U" unfolding bij_betw_def by (by100 blast)
                  thus ?thesis by (by100 blast)
                qed
                \<comment> \<open>p(V \<inter> ?W) \<in> subspace B TB U.\<close>
                have "p ` (V \<inter> ?W) \<in> subspace_topology B TB U"
                proof -
                  have "p ` (V \<inter> ?W) \<in> TB" using hpVW_open unfolding openin_on_def by (by100 blast)
                  have "p ` (V \<inter> ?W) = p ` (V \<inter> ?W) \<inter> U" using hpVW_sub_U by (by100 blast)
                  thus ?thesis unfolding subspace_topology_def using \<open>p ` (V \<inter> ?W) \<in> TB\<close> by (by100 blast)
                qed
                \<comment> \<open>p|V continuous inverse: preimage of open in U is open in V.\<close>
                have "{v \<in> V. p v \<in> p ` (V \<inter> ?W)} \<in> subspace_topology E TE V"
                proof -
                  have hV_cont_p: "top1_continuous_map_on V (subspace_topology E TE V)
                      U (subspace_topology B TB U) p"
                    using hV_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
                  from hV_cont_p \<open>p ` (V \<inter> ?W) \<in> subspace_topology B TB U\<close>
                  show ?thesis unfolding top1_continuous_map_on_def by (by100 blast)
                qed
                \<comment> \<open>{v \<in> V. p v \<in> p(V \<inter> ?W)} = V \<inter> ?W (p injective on V).\<close>
                have "{v \<in> V. p v \<in> p ` (V \<inter> ?W)} = V \<inter> ?W"
                proof (rule set_eqI, rule iffI)
                  fix v assume "v \<in> {v \<in> V. p v \<in> p ` (V \<inter> ?W)}"
                  hence hv: "v \<in> V" "p v \<in> p ` (V \<inter> ?W)" by (by100 blast)+
                  from hv(2) obtain w where hw: "w \<in> V \<inter> ?W" "p w = p v" by (by100 auto)
                  have "inj_on p V" using hV_homeo unfolding top1_homeomorphism_on_def bij_betw_def
                    by (by100 blast)
                  have "w \<in> V" using hw(1) by (by100 blast)
                  from inj_onD[OF \<open>inj_on p V\<close> hw(2) \<open>w \<in> V\<close> hv(1)]
                  have "w = v" .
                  thus "v \<in> V \<inter> ?W" using hw(1) by (by100 simp)
                next
                  fix v assume "v \<in> V \<inter> ?W"
                  hence "v \<in> V" "p v \<in> p ` (V \<inter> ?W)" by (by100 blast)+
                  thus "v \<in> {v \<in> V. p v \<in> p ` (V \<inter> ?W)}" by (by100 blast)
                qed
                hence "V \<inter> ?W \<in> subspace_topology E TE V"
                  using \<open>{v \<in> V. p v \<in> p ` (V \<inter> ?W)} \<in> subspace_topology E TE V\<close> by (by100 simp)
                \<comment> \<open>V \<inter> ?W open in V + V open in E \<Rightarrow> V \<inter> ?W open in E.\<close>
                from this obtain U0 where "U0 \<in> TE" "V \<inter> ?W = U0 \<inter> V"
                  unfolding subspace_topology_def by (by100 blast)
                have "V \<in> TE" using hV_open unfolding openin_on_def by (by100 blast)
                have hTE_loc: "is_topology_on E TE"
                  using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
                have "{U0, V} \<subseteq> TE" "finite {U0, V}" "{U0, V} \<noteq> {}"
                  using \<open>U0 \<in> TE\<close> \<open>V \<in> TE\<close> by (by100 blast, by100 simp, by100 blast)
                have "\<Inter>{U0, V} \<in> TE"
                  using hTE_loc[unfolded is_topology_on_def] \<open>{U0, V} \<subseteq> TE\<close> \<open>finite {U0, V}\<close> \<open>{U0, V} \<noteq> {}\<close>
                  by (by100 blast)
                have "\<Inter>{U0, V} = U0 \<inter> V" by (by100 blast)
                thus ?thesis using \<open>\<Inter>{U0, V} \<in> TE\<close> \<open>V \<inter> ?W = U0 \<inter> V\<close> by (by100 simp)
              qed
              have "e \<in> V \<inter> ?W" using hV_e he_W by (by100 blast)
              have "V \<inter> ?W \<subseteq> ?W" by (by100 blast)
              show "\<exists>V \<in> TE. e \<in> V \<and> V \<subseteq> ?W"
                apply (rule bexI[of _ "V \<inter> ?W"])
                using \<open>e \<in> V \<inter> ?W\<close> \<open>V \<inter> ?W \<subseteq> ?W\<close> apply (by100 blast)
                apply (rule hVW_TE)
                done
            qed
            \<comment> \<open>?W = union of open sets, hence open.\<close>
            hence "?W = \<Union>{V \<in> TE. V \<subseteq> ?W}" by (by5000 blast)
            moreover have "\<Union>{V \<in> TE. V \<subseteq> ?W} \<in> TE"
            proof -
              have hTE: "is_topology_on E TE"
                using assms(3) unfolding is_topology_on_strict_def by (by100 blast)
              have "{V \<in> TE. V \<subseteq> ?W} \<subseteq> TE" by (by100 blast)
              from hTE[unfolded is_topology_on_def, THEN conjunct2, THEN conjunct2, THEN conjunct1,
                  rule_format, OF this]
              show ?thesis .
            qed
            ultimately show ?thesis by (by100 simp)
          qed
          ultimately show ?thesis unfolding openin_on_def by (by100 blast)
        qed
        show "closedin_on E TE C"
          using \<open>openin_on E TE ?W\<close> hC_sub unfolding closedin_on_def openin_on_def
          by (by100 blast)
      qed
    qed
    show ?thesis
      apply (rule exI[of _ ?\<A>E])
      using hAE_arcs hAE_cover hAE_intersect hAE_topology by (by100 blast)
  qed
  \<comment> \<open>Step 2: E is Hausdorff (proved at top level as hE\_haus\_top).\<close>
  have hE_hausdorff: "is_hausdorff_on E TE" using hE_haus_top .
  \<comment> \<open>Step 3: Combine all conditions into top1_is_graph_on.\<close>
  show ?thesis unfolding top1_is_graph_on_def
    using assms(3) hE_hausdorff hAE by (by100 blast)
qed

subsection \<open>Reviewer-requested graph theory infrastructure lemmas\<close>

text \<open>A connected graph has a maximal tree (Munkres Lemma 84.3).\<close>
text \<open>A connected graph has a maximal tree (Munkres Lemma 84.3).
  Moved after top1\_is\_tree\_on definition in \<S>84.\<close>

text \<open>tree\_contractible (= tree\_simply\_connected) is defined after top1\_is\_tree\_on in \<S>84.\<close>

text \<open>Quotient of a graph by a maximal tree is a wedge of circles (Munkres Lemma 84.5).\<close>
text \<open>Quotient of a graph by a maximal tree is a wedge of circles (Munkres Lemma 84.5).
  Moved after top1\_is\_tree\_on definition in \<S>84.\<close>

text \<open>A subset of a graph covered by a sub-collection of arcs is itself a graph (subgraph).\<close>
lemma subgraph_union_of_arcs_is_graph:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes hgraph: "top1_is_graph_on X TX"
      and h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and hcover_X: "\<Union>\<A> \<subseteq> X"
      and h\<A>_inter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and h\<A>_coh: "\<forall>C. C \<subseteq> \<Union>\<A> \<longrightarrow>
           (closedin_on (\<Union>\<A>) (subspace_topology X TX (\<Union>\<A>)) C \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
  shows "top1_is_graph_on (\<Union>\<A>) (subspace_topology X TX (\<Union>\<A>))"
proof -
  let ?S = "\<Union>\<A>"
  let ?TS = "subspace_topology X TX ?S"
  have hS_sub: "?S \<subseteq> X" using hcover_X .
  have hTS_strict: "is_topology_on_strict ?S ?TS"
    by (rule subspace_topology_is_strict[OF _ hS_sub])
       (rule assms(1)[unfolded top1_is_graph_on_def, THEN conjunct1])
  have hS_haus: "is_hausdorff_on ?S ?TS"
  proof -
    have "is_hausdorff_on X TX" using hgraph unfolding top1_is_graph_on_def by (by100 blast)
    from conjunct2[OF conjunct2[OF Theorem_17_11]] hS_sub this
    show ?thesis by (by100 blast)
  qed
  \<comment> \<open>The arcs \<A> form the arc decomposition of ?S.\<close>
  \<comment> \<open>Need: arcs in subspace topology of ?S equal arcs in subspace of X.\<close>
  have h\<A>_sub: "\<forall>A\<in>\<A>. top1_is_arc_on A (subspace_topology ?S ?TS A)"
  proof (intro ballI)
    fix A assume "A \<in> \<A>"
    have "A \<subseteq> ?S" using \<open>A \<in> \<A>\<close> by (by100 blast)
    have "subspace_topology ?S ?TS A = subspace_topology X TX A"
      by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?S\<close>])
    thus "top1_is_arc_on A (subspace_topology ?S ?TS A)"
      using h\<A> \<open>A \<in> \<A>\<close> by (by100 simp)
  qed
  have h\<A>_sub2: "\<forall>A\<in>\<A>. A \<subseteq> ?S" by (by100 blast)
  have hcover: "\<Union>\<A> = ?S" by (by100 blast)
  have h_inter_sub: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
       A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?S ?TS A)
     \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?S ?TS B)
     \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
  proof (intro ballI impI)
    fix A B assume "A \<in> \<A>" "B \<in> \<A>" "A \<noteq> B"
    from h\<A>_inter[rule_format, OF this]
    have h1: "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
        \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
        \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" .
    have "subspace_topology ?S ?TS A = subspace_topology X TX A"
      using subspace_topology_trans[of A ?S] \<open>A \<in> \<A>\<close> by (by100 blast)
    moreover have "subspace_topology ?S ?TS B = subspace_topology X TX B"
      using subspace_topology_trans[of B ?S] \<open>B \<in> \<A>\<close> by (by100 blast)
    ultimately show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?S ?TS A)
        \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?S ?TS B)
        \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      using h1 by (by100 simp)
  qed
  have h_coh_sub: "\<forall>C. C \<subseteq> ?S \<longrightarrow>
       (closedin_on ?S ?TS C \<longleftrightarrow>
        (\<forall>A\<in>\<A>. closedin_on A (subspace_topology ?S ?TS A) (A \<inter> C)))"
  proof (intro allI impI)
    fix C assume "C \<subseteq> ?S"
    have "\<And>A. A \<in> \<A> \<Longrightarrow> subspace_topology ?S ?TS A = subspace_topology X TX A"
      by (rule subspace_topology_trans, blast)
    show "closedin_on ?S ?TS C \<longleftrightarrow>
        (\<forall>A\<in>\<A>. closedin_on A (subspace_topology ?S ?TS A) (A \<inter> C))"
      using h\<A>_coh[rule_format, OF \<open>C \<subseteq> ?S\<close>] \<open>\<And>A. A \<in> \<A> \<Longrightarrow> subspace_topology ?S ?TS A = subspace_topology X TX A\<close>
      by (by100 simp)
  qed
  show ?thesis unfolding top1_is_graph_on_def
  proof (intro conjI)
    show "is_topology_on_strict ?S ?TS" using hTS_strict .
    show "is_hausdorff_on ?S ?TS" using hS_haus .
    show "\<exists>\<A>'. (\<forall>A\<in>\<A>'. A \<subseteq> ?S \<and> top1_is_arc_on A (subspace_topology ?S ?TS A))
        \<and> \<Union>\<A>' = ?S
        \<and> (\<forall>A\<in>\<A>'. \<forall>B\<in>\<A>'. A \<noteq> B \<longrightarrow>
             A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?S ?TS A)
           \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?S ?TS B)
           \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2)
        \<and> (\<forall>C. C \<subseteq> ?S \<longrightarrow>
             (closedin_on ?S ?TS C \<longleftrightarrow>
              (\<forall>A\<in>\<A>'. closedin_on A (subspace_topology ?S ?TS A) (A \<inter> C))))"
      apply (rule exI[of _ \<A>])
      using h\<A>_sub h\<A>_sub2 hcover h_inter_sub h_coh_sub by (by100 blast)
  qed
qed

text \<open>The fundamental group of a wedge of circles is free.\<close>
lemma wedge_circles_pi1_free:
  assumes "top1_is_wedge_of_circles_on X TX {..<(n::nat)} p"
  shows "\<exists>(G::int set) mul e invg (\<iota>::nat \<Rightarrow> int).
      top1_is_free_group_full_on G mul e invg \<iota> {..<n}
    \<and> top1_groups_isomorphic_on G mul
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p)"
  using Theorem_71_1_wedge_of_circles_finite[OF assms]
  by (by100 blast)


end
