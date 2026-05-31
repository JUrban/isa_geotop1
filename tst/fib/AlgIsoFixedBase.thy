theory AlgIsoFixedBase
imports AlgTopC.AlgTopCached
begin

text \<open>Fixed versions of theorems that should state a SPECIFIC MAP is an isomorphism,
  not just that the groups are abstractly isomorphic.
  See REPORT_wrong_iso_statements.md for details.\<close>

section \<open>Copied infrastructure (oracle-clean, from AlgTop.thy)\<close>

text \<open>These lemmas are proved in AlgTop.thy but not accessible from this session.
  Copied verbatim. Both are oracle-clean (verified by thm\_oracles).\<close>

lemma SCC_pi1_iso_Z:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
      and "c0 \<in> C"
  shows "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier C
        (subspace_topology top1_S2 top1_S2_topology C) c0)
      (top1_fundamental_group_mul C
        (subspace_topology top1_S2 top1_S2_topology C) c0)
      top1_Z_group top1_Z_mul"
proof -
  let ?TC = "subspace_topology top1_S2 top1_S2_topology C"
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hC_sub_S2: "C \<subseteq> top1_S2" using simple_closed_curve_subset[OF assms(2)] .
  obtain f where hf_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S2 top1_S2_topology f"
      and hf_inj: "inj_on f top1_S1" and hf_img: "f ` top1_S1 = C"
    using assms(2) unfolding top1_simple_closed_curve_on_def by (by100 blast)
  have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
    using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
  have hTC_top: "is_topology_on C ?TC"
    by (rule subspace_topology_is_topology_on[OF hTopS2 hC_sub_S2])
  have hf_all_C: "\<And>s. s \<in> top1_S1 \<Longrightarrow> f s \<in> C"
  proof -
    fix s assume "s \<in> top1_S1"
    hence "f s \<in> f ` top1_S1" by (rule imageI)
    thus "f s \<in> C" using hf_img by simp
  qed
  have hf_cont_C: "top1_continuous_map_on top1_S1 top1_S1_topology C ?TC f"
    by (intro continuous_map_restrict_codomain[OF hf_cont _ hC_sub_S2] ballI)
       (rule hf_all_C)
  have hf_bij: "bij_betw f top1_S1 C"
    unfolding bij_betw_def using hf_inj hf_img by (by100 blast)
  have hC_haus: "is_hausdorff_on C ?TC"
    using conjunct2[OF conjunct2[OF Theorem_17_11]] hC_sub_S2 top1_S2_is_hausdorff
    by (by100 blast)
  have hf_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology C ?TC f"
    by (rule Theorem_26_6[OF hS1_top hTC_top S1_compact hC_haus hf_cont_C hf_bij])
  obtain s0 where hs0: "s0 \<in> top1_S1" "f s0 = c0"
    using hf_img assms(3) by (by100 blast)
  have h_pi1_S1_C: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology s0)
      (top1_fundamental_group_mul top1_S1 top1_S1_topology s0)
      (top1_fundamental_group_carrier C ?TC c0)
      (top1_fundamental_group_mul C ?TC c0)"
    by (rule Corollary_52_5_homeomorphism_iso[OF hS1_top hTC_top hf_homeo hs0(1) hs0(2)])
  have h10_S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
  have h_pi1_S1_bp: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1::real, 0::real))
      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology s0)
      (top1_fundamental_group_mul top1_S1 top1_S1_topology s0)"
  proof -
    obtain \<gamma> where "top1_is_path_on top1_S1 top1_S1_topology (1, 0) s0 \<gamma>"
      using S1_path_connected h10_S1 hs0(1) unfolding top1_path_connected_on_def
      by (by100 blast)
    thus ?thesis by (rule basepoint_change_iso_via_path[OF hS1_top])
  qed
  have h_pi1_S1_Z: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
      top1_Z_group top1_Z_mul"
    by (rule Theorem_54_5_iso)
  \<comment> \<open>Chain: \<pi>_1(C,c0) \<cong> \<pi>_1(S1,s0) \<cong> \<pi>_1(S1,(1,0)) \<cong> Z.\<close>
  have h_pi1_S1_C_sym: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier C ?TC c0)
      (top1_fundamental_group_mul C ?TC c0)
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology s0)
      (top1_fundamental_group_mul top1_S1 top1_S1_topology s0)"
  proof (rule top1_groups_isomorphic_on_sym[OF h_pi1_S1_C])
    show "top1_is_group_on (top1_fundamental_group_carrier top1_S1 top1_S1_topology s0)
        (top1_fundamental_group_mul top1_S1 top1_S1_topology s0)
        (top1_fundamental_group_id top1_S1 top1_S1_topology s0)
        (top1_fundamental_group_invg top1_S1 top1_S1_topology s0)"
      by (rule top1_fundamental_group_is_group[OF hS1_top hs0(1)])
    have "c0 \<in> C" by (rule assms(3))
    show "top1_is_group_on (top1_fundamental_group_carrier C ?TC c0)
        (top1_fundamental_group_mul C ?TC c0)
        (top1_fundamental_group_id C ?TC c0)
        (top1_fundamental_group_invg C ?TC c0)"
      by (rule top1_fundamental_group_is_group[OF hTC_top \<open>c0 \<in> C\<close>])
  qed
  have h_pi1_S1_bp_sym: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology s0)
      (top1_fundamental_group_mul top1_S1 top1_S1_topology s0)
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
  proof (rule top1_groups_isomorphic_on_sym[OF h_pi1_S1_bp])
    show "top1_is_group_on (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1::real, 0::real))
        (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_id top1_S1 top1_S1_topology (1, 0))
        (top1_fundamental_group_invg top1_S1 top1_S1_topology (1, 0))"
      by (rule top1_fundamental_group_is_group[OF hS1_top h10_S1])
    show "top1_is_group_on (top1_fundamental_group_carrier top1_S1 top1_S1_topology s0)
        (top1_fundamental_group_mul top1_S1 top1_S1_topology s0)
        (top1_fundamental_group_id top1_S1 top1_S1_topology s0)
        (top1_fundamental_group_invg top1_S1 top1_S1_topology s0)"
      by (rule top1_fundamental_group_is_group[OF hS1_top hs0(1)])
  qed
  have h1: "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier C ?TC c0)
      (top1_fundamental_group_mul C ?TC c0)
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))"
    by (rule groups_isomorphic_trans_fwd[OF h_pi1_S1_C_sym h_pi1_S1_bp_sym])
  show ?thesis
    by (rule groups_isomorphic_trans_fwd[OF h1 h_pi1_S1_Z])
qed

lemma Theorem_63_1_b_generation:
  assumes "is_topology_on X TX"
      and "openin_on X TX U" and "openin_on X TX V" and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B"
      and "top1_is_path_on U (subspace_topology X TX U) a b \<alpha>"
      and "top1_is_path_on V (subspace_topology X TX V) b a \<beta>"
      \<comment> \<open>\<pi>_1(X, a) is infinite cyclic with some generator gen.\<close>
      and "\<exists>gen. top1_is_loop_on X TX a gen \<and>
        (\<forall>f. top1_is_loop_on X TX a f \<longrightarrow>
          (\<exists>n::nat. top1_path_homotopic_on X TX a a f (top1_path_power gen a n)
            \<or> top1_path_homotopic_on X TX a a f
                 (top1_path_power (top1_path_reverse gen) a n)))"
  shows "\<forall>f. top1_is_loop_on X TX a f \<longrightarrow>
    (\<exists>n::nat. top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_product \<alpha> \<beta>) a n)
      \<or> top1_path_homotopic_on X TX a a f
           (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n))"
proof -
  \<comment> \<open>Step 1: Construct helix covering.\<close>
  have ha_U: "a \<in> U" using assms(5,9) by (by100 blast)
  define E :: "('a \<times> int) set" where
    "E = {(x, m). (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)}"
  define TE :: "('a \<times> int) set set" where
    "TE = {W. W \<subseteq> E \<and>
      (\<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX) \<and>
      (\<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX)}"
  define p0 :: "'a \<times> int \<Rightarrow> 'a" where "p0 = fst"
  have he0: "(a, 0::int) \<in> E" unfolding E_def using ha_U by simp
  have hp0: "p0 (a, 0::int) = a" unfolding p0_def by simp
  have hcov_TE: "top1_covering_map_on E TE X TX p0 \<and> is_topology_on E TE"
  proof -
    note h = helix_covering_construction[OF assms(1-8)]
    have "E = {x. even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
      unfolding E_def by auto
    moreover have "TE = {W. W \<subseteq> E \<and>
        (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
        (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
              {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
      unfolding TE_def E_def by auto
    moreover have "p0 = fst" unfolding p0_def by simp
    ultimately show ?thesis using h by simp
  qed
  hence hTE: "is_topology_on E TE" and hcov: "top1_covering_map_on E TE X TX p0" by auto
  \<comment> \<open>Step 2: (\<alpha>*\<beta>)^m lifts from (a,0) to (a, 2m).\<close>
  have hfm_lift: "\<And>m. \<exists>ftm. top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm \<and>
      (\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product \<alpha> \<beta>) a m s)"
  proof -
    fix m :: nat
    show "\<exists>ftm. top1_is_path_on E TE (a, 0) (a, 2 * int m) ftm \<and>
        (\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product \<alpha> \<beta>) a m s)"
    proof (rule helix_f_power_lift[OF assms(1-12) hcov hTE he0 hp0])
      show "\<And>W n. W \<in> TE \<Longrightarrow> {x \<in> U. (x, 2 * n) \<in> W} \<in> TX"
        unfolding TE_def by (by100 blast)
      show "\<And>W n. W \<in> TE \<Longrightarrow> {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
          {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX"
        unfolding TE_def by (by100 blast)
      show "\<And>x n. x \<in> U \<Longrightarrow> (x, 2*n) \<in> E" unfolding E_def by auto
      show "\<And>x n. x \<in> V - U \<Longrightarrow> (x, 2*n + 1) \<in> E" unfolding E_def by auto
      show "\<And>x n. x \<in> A \<Longrightarrow> (x, 2*n + 2) \<in> E"
        using assms(5) unfolding E_def by auto
      show "\<And>x n. x \<in> B \<Longrightarrow> (x, 2*n) \<in> E"
        using assms(5) unfolding E_def by auto
      show "p0 = fst" unfolding p0_def by simp
      show "\<And>x m. (x, m) \<in> E \<Longrightarrow> (even m \<and> x \<in> U) \<or> (odd m \<and> x \<in> V - U)"
        unfolding E_def by auto
      show "\<And>W. \<lbrakk>W \<subseteq> E; \<forall>n::int. {x \<in> U. (x, 2*n) \<in> W} \<in> TX;
          \<forall>n::int. {x \<in> A. (x, 2*n + 2) \<in> W} \<union> {x \<in> B. (x, 2*n) \<in> W} \<union>
                    {x \<in> V - U. (x, 2*n + 1) \<in> W} \<in> TX\<rbrakk> \<Longrightarrow> W \<in> TE"
        unfolding TE_def by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 3: From assms(13), \<pi>_1(X) is infinite cyclic with generator gen.\<close>
  obtain gen where hgen_loop: "top1_is_loop_on X TX a gen"
      and hgen_all: "\<forall>f. top1_is_loop_on X TX a f \<longrightarrow>
        (\<exists>n::nat. top1_path_homotopic_on X TX a a f (top1_path_power gen a n)
          \<or> top1_path_homotopic_on X TX a a f
               (top1_path_power (top1_path_reverse gen) a n))"
    using assms(13) by blast
  \<comment> \<open>Step 4: [\<alpha>*\<beta>] is nontrivial (from Theorem\_63\_1\_loop\_nontrivial).\<close>
  have h\<alpha>\<beta>_nontrivial: "\<not> top1_path_homotopic_on X TX a a
      (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
    by (rule Theorem_63_1_loop_nontrivial[OF assms(1-12)])
  \<comment> \<open>Step 5: [\<alpha>*\<beta>] = gen^k for some k with k \<noteq> 0.\<close>
  have h\<alpha>\<beta>_loop: "top1_is_loop_on X TX a (top1_path_product \<alpha> \<beta>)"
  proof -
    have hU_sub: "U \<subseteq> X" using assms(2) unfolding openin_on_def by (by100 blast)
    have hV_sub: "V \<subseteq> X" using assms(3) unfolding openin_on_def by (by100 blast)
    have hTU: "is_topology_on U (subspace_topology X TX U)"
      by (rule subspace_topology_is_topology_on[OF assms(1) hU_sub])
    have hTV: "is_topology_on V (subspace_topology X TX V)"
      by (rule subspace_topology_is_topology_on[OF assms(1) hV_sub])
    have h\<alpha>_X: "top1_is_path_on X TX a b \<alpha>"
      by (rule path_in_subspace_is_path_in_ambient'[OF assms(1) hU_sub assms(11)])
    have h\<beta>_X: "top1_is_path_on X TX b a \<beta>"
      by (rule path_in_subspace_is_path_in_ambient'[OF assms(1) hV_sub assms(12)])
    show ?thesis unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF assms(1) h\<alpha>_X h\<beta>_X])
  qed
  obtain k :: nat where hk: "top1_path_homotopic_on X TX a a
      (top1_path_product \<alpha> \<beta>) (top1_path_power gen a k)
    \<or> top1_path_homotopic_on X TX a a
      (top1_path_product \<alpha> \<beta>) (top1_path_power (top1_path_reverse gen) a k)"
    using hgen_all[THEN spec, of "top1_path_product \<alpha> \<beta>"] h\<alpha>\<beta>_loop by blast
  have hk_ne: "k \<noteq> 0"
  proof
    assume "k = 0"
    hence "top1_path_homotopic_on X TX a a
        (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
      using hk by simp
    thus False using h\<alpha>\<beta>_nontrivial by contradiction
  qed
  \<comment> \<open>Step 6: The shift T(x,n) = (x, n+2) is a covering automorphism of E.
     This gives: if gen lifts from (a,0) to (a,2d), then gen^k lifts to (a,2kd).
     Since gen^k = [\<alpha>*\<beta>] lifts to (a,2): kd = 1, so k = \<plusminus>1.\<close>
  \<comment> \<open>Step 6a: The lift of gen from (a,0) exists and ends at some (a, 2d).\<close>
  have hgen_path: "top1_is_path_on X TX a a gen"
    using hgen_loop unfolding top1_is_loop_on_def by (by100 blast)
  obtain gen_lift where hgen_lift: "top1_is_path_on E TE (a, 0) (gen_lift 1) gen_lift"
      and hgen_lift_proj: "\<forall>s\<in>I_set. p0 (gen_lift s) = gen s"
    using Lemma_54_1_path_lifting[OF hcov he0 hp0 hgen_path assms(1) hTE] by blast
  \<comment> \<open>gen\_lift ends at some point in the fiber at a = \{(a, 2n) : n \<in> Z\}.\<close>
  have hgen_end_fiber: "\<exists>d :: int. gen_lift 1 = (a, 2 * d)"
  proof -
    have h1_I: "(1::real) \<in> I_set"
      unfolding top1_unit_interval_def by (by100 simp)
    have hend_E: "gen_lift 1 \<in> E"
      using hgen_lift unfolding top1_is_path_on_def top1_continuous_map_on_def
      using h1_I by (by100 blast)
    have hp0_gen1: "p0 (gen_lift 1) = gen 1"
      using hgen_lift_proj h1_I by (by100 blast)
    have hgen1_a: "gen 1 = a"
      using hgen_loop unfolding top1_is_loop_on_def top1_is_path_on_def
      by (by100 blast)
    have hend_proj: "p0 (gen_lift 1) = a"
      using hp0_gen1 hgen1_a by simp
    hence hfst: "fst (gen_lift 1) = a" unfolding p0_def by simp
    obtain x' n' where hpair: "gen_lift 1 = (x', n')" by (cases "gen_lift 1")
    hence "x' = a" using hfst by simp
    have "(x', n') \<in> E" using hend_E hpair by simp
    hence "(even n' \<and> x' \<in> U) \<or> (odd n' \<and> x' \<in> V - U)" unfolding E_def by auto
    hence "even n'"
    proof
      assume "even n' \<and> x' \<in> U" thus "even n'" by simp
    next
      assume "odd n' \<and> x' \<in> V - U"
      hence "x' \<in> V - U" by simp
      hence "a \<in> V - U" using \<open>x' = a\<close> by simp
      hence False using ha_U by (by100 blast)
      thus "even n'" by simp
    qed
    then obtain d where "n' = 2 * d" using evenE by blast
    hence "gen_lift 1 = (a, 2 * d)" using hpair \<open>x' = a\<close> by simp
    thus ?thesis by blast
  qed
  obtain d :: int where hgen_end: "gen_lift 1 = (a, 2 * d)"
    using hgen_end_fiber by blast
  \<comment> \<open>Step 6b: The shift T is a covering automorphism.\<close>
  \<comment> \<open>Step 6c: gen^k lifts from (a,0) to (a, 2kd) by applying T iteratively.\<close>
  \<comment> \<open>Step 6d: gen^k \<simeq> \<alpha>*\<beta>, and \<alpha>*\<beta> lifts to (a, 2). By Theorem\_54\_3: 2kd = 2.
     So kd = 1 with k \<in> N, d \<in> Z. If k = 0: already excluded. k \<ge> 1.
     Integer solutions to kd = 1: (k,d) = (1,1). So k = 1.\<close>
  \<comment> \<open>If [\<alpha>*\<beta>] = gen^k: k = 1 (positive case). If [\<alpha>*\<beta>] = gen^{-k}: k = 1 too.\<close>
  \<comment> \<open>Lift of (\<alpha>*\<beta>) (= m=1 case) from (a,0) to (a, 2).\<close>
  \<comment> \<open>(\<alpha>*\<beta>) lifts from (a,0) to (a, 2): from hfm\_lift with m = 1.\<close>
  obtain ab_lift where hab_lift: "top1_is_path_on E TE (a, 0) (a, 2) ab_lift"
      and hab_lift_proj: "\<forall>s\<in>I_set. p0 (ab_lift s) =
          top1_path_power (top1_path_product \<alpha> \<beta>) a 1 s"
  proof -
    obtain ftm where hftm: "top1_is_path_on E TE (a, 0) (a, 2 * int (1::nat)) ftm"
        "\<forall>s\<in>I_set. p0 (ftm s) = top1_path_power (top1_path_product \<alpha> \<beta>) a 1 s"
      using hfm_lift[of 1] by blast
    have "2 * int (1::nat) = (2::int)" by simp
    hence "top1_is_path_on E TE (a, 0) (a, 2) ftm" using hftm(1) by simp
    thus ?thesis using hftm(2) that by blast
  qed
  \<comment> \<open>gen^k lifts from (a,0) to (a, 2*int(k)*d).
     This uses the helix shift automorphism T(x,n) = (x, n+2).
     By induction on k: the lift of gen^k concatenates k lifts of gen,
     each shifted by T, giving endpoint (a, 2*k*d).\<close>
  \<comment> \<open>Define the helix shift T(x,n) = (x, n + 2*d). This maps a lift of gen
     from (a, 0) to a lift from (a, 2*d), from (a, 2*d) to (a, 4*d), etc.\<close>
  \<comment> \<open>Actually, we use the general shift T\_d(x,n) = (x, n + 2*d).
     For d = 1: this is the standard period-1 shift.
     The key property: T\_d is a covering automorphism.
     For arbitrary d: T\_d = T\_1^d where T\_1(x,n) = (x, n+2) is period-1.\<close>
  \<comment> \<open>The lift of gen from (a, 2*j*d) ends at (a, 2*(j+1)*d).
     This follows from the shift T\_d being a covering automorphism.\<close>
  \<comment> \<open>Define the period-1 helix shift T1(x,n) = (x, n+2).\<close>
  define T1 :: "('a \<times> int) \<Rightarrow> ('a \<times> int)" where "T1 = (\<lambda>(x, n). (x, n + 2))"
  \<comment> \<open>T1 maps E to E (parity of n preserved by adding 2).\<close>
  have hT1_E: "\<And>e. e \<in> E \<Longrightarrow> T1 e \<in> E"
    unfolding T1_def E_def by auto
  \<comment> \<open>p0 \<circ> T1 = p0.\<close>
  have hT1_proj: "\<And>e. p0 (T1 e) = p0 e"
    unfolding T1_def p0_def by auto
  \<comment> \<open>T1 is continuous: T1\<inverse>(W) \<in> TE for W \<in> TE.
     Key: T1\<inverse>(W) = \{(x,n) : (x, n+2) \<in> W\}.
     Slice conditions: \{x \<in> U. (x, 2n) \<in> T1\<inverse>(W)\} = \{x \<in> U. (x, 2(n+1)) \<in> W\} \<in> TX.\<close>
  have hT1_cont: "top1_continuous_map_on E TE E TE T1"
  proof -
    note h = helix_shift_general_continuous[OF assms(1-3) assms(5) assms(7-8), of 1]
    have "E = {x :: ('a \<times> int). even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
      unfolding E_def by auto
    moreover have "TE = {W. W \<subseteq> E \<and>
        (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
        (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
              {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
      unfolding TE_def E_def by auto
    moreover have "T1 = (\<lambda>(x :: 'a, n :: int). (x, n + 2 * (1::int)))" unfolding T1_def by auto
    ultimately show ?thesis using h by simp
  qed
  \<comment> \<open>The lift of gen from (a, 2*j) ends at (a, 2*j + 2*d) for any j.
     Proof: by covering\_lift\_unique\_connected, the lift from (a, 2*j) is
     T1^j \<circ> gen\_lift (since T1^j shifts by 2j, and the projection is unchanged).
     Then its endpoint is T1^j(gen\_lift 1) = T1^j(a, 2d) = (a, 2d + 2j).\<close>
  \<comment> \<open>More precisely: define T1_pow j (x,n) = (x, n + 2*j). Then:
     T1\_pow j \<circ> gen\_lift is a path from (a, 2*j) to (a, 2*d + 2*j) in E
     projecting to gen. By covering\_lift\_unique\_connected, this is THE unique lift
     of gen from (a, 2*j).\<close>
  \<comment> \<open>gen^k lift by induction: gen * shifted(gen^{k-1}), matching path\_power definition.
     path\_power gen a (Suc k') = gen * gen^{k'}.
     So: gen\_lift from (a,0) to (a,2d), then shifted gen^{k'} lift from (a,2d) to (a,2d+2k'd).\<close>
  have hgenk_lift: "\<exists>ftk. top1_is_path_on E TE (a, 0) (a, 2 * int k * d) ftk \<and>
      (\<forall>s\<in>I_set. p0 (ftk s) = top1_path_power gen a k s)"
  proof (induct k)
    case 0
    define ftk0 :: "real \<Rightarrow> ('a \<times> int)" where "ftk0 = (\<lambda>s. (a, 0::int))"
    have "top1_is_path_on E TE (a, 0) (a, 2 * int 0 * d) ftk0"
    proof -
      have "top1_is_path_on E TE (a, 0) (a, 0) ftk0"
        unfolding top1_is_path_on_def ftk0_def
      proof (intro conjI)
        have "top1_continuous_map_on I_set I_top E TE (top1_constant_path (a, 0::int))"
          by (rule top1_constant_path_continuous[OF hTE he0])
        thus "top1_continuous_map_on I_set I_top E TE (\<lambda>s. (a, 0::int))"
          unfolding top1_constant_path_def by simp
      qed simp+
      thus ?thesis by simp
    qed
    moreover have "\<forall>s\<in>I_set. p0 (ftk0 s) = top1_path_power gen a 0 s"
    proof (intro ballI)
      fix s assume "s \<in> I_set"
      show "p0 (ftk0 s) = top1_path_power gen a 0 s"
        unfolding ftk0_def p0_def by (simp add: top1_constant_path_def)
    qed
    ultimately show ?case by blast
  next
    case (Suc k')
    obtain ftk' where hftk': "top1_is_path_on E TE (a, 0) (a, 2 * int k' * d) ftk'"
        "\<forall>s\<in>I_set. p0 (ftk' s) = top1_path_power gen a k' s"
      using Suc.hyps by blast
    \<comment> \<open>Shift ftk' by d periods: T\_d(x,n) = (x, n+2d). Then T\_d \<circ> ftk' is a
       path from (a, 2d) to (a, 2d + 2k'd) = (a, 2(k'+1)d) in E,
       projecting to gen^{k'} (since p0 \<circ> T\_d = p0).\<close>
    define T_d :: "('a \<times> int) \<Rightarrow> ('a \<times> int)" where "T_d = (\<lambda>(x, n). (x, n + 2*d))"
    define ftk'_shifted :: "real \<Rightarrow> ('a \<times> int)"
      where "ftk'_shifted = T_d \<circ> ftk'"
    have hTd_cont: "top1_continuous_map_on E TE E TE T_d"
    proof -
      note h = helix_shift_general_continuous[OF assms(1-3) assms(5) assms(7-8)]
      have "E = {x :: ('a \<times> int). even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
        unfolding E_def by auto
      moreover have "TE = {W. W \<subseteq> E \<and>
          (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
          (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
                {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
        unfolding TE_def E_def by auto
      moreover have "T_d = (\<lambda>(x :: 'a, n :: int). (x, n + 2 * d))" unfolding T_d_def by auto
      ultimately show ?thesis using h by simp
    qed
    have hTd_proj: "\<And>e. p0 (T_d e) = p0 e" unfolding T_d_def p0_def by auto
    \<comment> \<open>ftk'\_shifted is a path from (a, 2d) to (a, 2d + 2k'd) in E.\<close>
    have hftk'_shifted_path: "top1_is_path_on E TE (a, 2 * d) (a, 2 * d + 2 * int k' * d) ftk'_shifted"
    proof -
      have hcomp_cont: "top1_continuous_map_on I_set I_top E TE ftk'_shifted"
        unfolding ftk'_shifted_def
        by (rule top1_continuous_map_on_comp[where Y=E and TY=TE])
           (use hftk'(1) hTd_cont in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
      have hstart: "ftk'_shifted 0 = (a, 2 * d)"
        unfolding ftk'_shifted_def T_d_def using hftk'(1)
        unfolding top1_is_path_on_def by (by100 simp)
      have hend: "ftk'_shifted 1 = (a, 2 * d + 2 * int k' * d)"
        unfolding ftk'_shifted_def T_d_def using hftk'(1)
        unfolding top1_is_path_on_def by (by100 simp)
      show ?thesis unfolding top1_is_path_on_def
        using hcomp_cont hstart hend by (by100 blast)
    qed
    have hftk'_shifted_proj: "\<forall>s\<in>I_set. p0 (ftk'_shifted s) = top1_path_power gen a k' s"
    proof (intro ballI)
      fix s assume "s \<in> I_set"
      have "p0 (ftk'_shifted s) = p0 (T_d (ftk' s))" unfolding ftk'_shifted_def by simp
      also have "... = p0 (ftk' s)" by (rule hTd_proj)
      also have "... = top1_path_power gen a k' s" using hftk'(2) \<open>s \<in> I_set\<close> by (by100 blast)
      finally show "p0 (ftk'_shifted s) = top1_path_power gen a k' s" .
    qed
    \<comment> \<open>Concatenate: gen * shifted(gen^{k'}) = gen^{Suc k'}.\<close>
    have h_endpoint_eq: "2 * d + 2 * int k' * d = 2 * int (Suc k') * d"
      by (simp add: algebra_simps)
    \<comment> \<open>gen\_lift goes (a,0)\<rightarrow>(a,2d), ftk'\_shifted goes (a,2d)\<rightarrow>(a,2d+2k'd).\<close>
    have hgen_lift_typed: "top1_is_path_on E TE (a, 0) (a, 2 * d) gen_lift"
      using hgen_lift hgen_end by simp
    define ftk_suc where "ftk_suc = top1_path_product gen_lift ftk'_shifted"
    have "top1_is_path_on E TE (a, 0) (a, 2 * int (Suc k') * d) ftk_suc"
    proof -
      have "top1_is_path_on E TE (a, 0) (a, 2 * d + 2 * int k' * d)
          (top1_path_product gen_lift ftk'_shifted)"
        by (rule top1_path_product_is_path[OF hTE hgen_lift_typed hftk'_shifted_path])
      thus ?thesis unfolding ftk_suc_def using h_endpoint_eq by simp
    qed
    moreover have "\<forall>s\<in>I_set. p0 (ftk_suc s) = top1_path_power gen a (Suc k') s"
    proof (intro ballI)
      fix s :: real assume hs: "s \<in> I_set"
      have "p0 (ftk_suc s) = p0 (top1_path_product gen_lift ftk'_shifted s)"
        unfolding ftk_suc_def by simp
      also have "... = (if s \<le> 1/2 then p0 (gen_lift (2*s)) else p0 (ftk'_shifted (2*s - 1)))"
        unfolding top1_path_product_def p0_def by (by100 simp)
      also have "... = (if s \<le> 1/2 then gen (2*s)
          else top1_path_power gen a k' (2*s - 1))"
      proof -
        have h1: "s \<le> 1/2 \<Longrightarrow> 2*s \<in> I_set"
          using hs unfolding top1_unit_interval_def by (by100 simp)
        have h2: "\<not>(s \<le> 1/2) \<Longrightarrow> 2*s - 1 \<in> I_set"
          using hs unfolding top1_unit_interval_def by (by100 simp)
        show ?thesis using hgen_lift_proj hftk'_shifted_proj h1 h2 by (by100 simp)
      qed
      also have "... = top1_path_product gen (top1_path_power gen a k') s"
        unfolding top1_path_product_def by simp
      also have "... = top1_path_power gen a (Suc k') s" by simp
      finally show "p0 (ftk_suc s) = top1_path_power gen a (Suc k') s" .
    qed
    ultimately show ?case by blast
  qed
  \<comment> \<open>Now: gen^k \<simeq> \<alpha>*\<beta> (from hk, positive case). Their lifts from (a,0)
     must end at the same point by Theorem\_54\_3.
     Endpoint of gen^k lift = (a, 2*int(k)*d). Endpoint of \<alpha>*\<beta> lift = (a, 2).
     So 2*int(k)*d = 2, giving int(k)*d = 1.\<close>
  have hk_one: "k = 1"
  proof -
    from hk show "k = 1"
    proof
      assume hpos: "top1_path_homotopic_on X TX a a
          (top1_path_product \<alpha> \<beta>) (top1_path_power gen a k)"
      \<comment> \<open>gen^k \<simeq> \<alpha>*\<beta>. Both lift from (a,0): gen^k to (a, 2kd), \<alpha>*\<beta> to (a, 2).
         By Theorem\_54\_3: endpoints match, so 2*int(k)*d = 2.\<close>
      obtain ftk where hftk: "top1_is_path_on E TE (a, 0) (a, 2 * int k * d) ftk"
          "\<forall>s\<in>I_set. p0 (ftk s) = top1_path_power gen a k s"
        using hgenk_lift by blast
      have hpos_sym: "top1_path_homotopic_on X TX a a
          (top1_path_power gen a k) (top1_path_product \<alpha> \<beta>)"
        by (rule Lemma_51_1_path_homotopic_sym[OF hpos])
      have hgenk_path: "top1_is_path_on X TX a a (top1_path_power gen a k)"
        by (rule top1_path_power_is_path[OF assms(1) hgen_loop])
      have hab_path_raw: "top1_is_path_on X TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a 1)"
        by (rule top1_path_power_is_path[OF assms(1) h\<alpha>\<beta>_loop])
      \<comment> \<open>Apply Theorem\_54\_3: gen^k \<simeq> path\_power (\<alpha>*\<beta>) a 1.
         Both lift from (a,0): gen^k to (a, 2kd), path\_power (\<alpha>*\<beta>) a 1 to (a, 2).
         Need: gen^k \<simeq> (path\_power (\<alpha>*\<beta>) a 1) as paths from a to a.
         From hpos: \<alpha>*\<beta> \<simeq> gen^k. Since (\<alpha>*\<beta>)*const \<simeq> \<alpha>*\<beta>:
         path\_power (\<alpha>*\<beta>) a 1 \<simeq> \<alpha>*\<beta> \<simeq> gen^k.
         So gen^k \<simeq> path\_power (\<alpha>*\<beta>) a 1 (by symmetry + transitivity).\<close>
      have h_genk_pp1: "top1_path_homotopic_on X TX a a
          (top1_path_power gen a k) (top1_path_power (top1_path_product \<alpha> \<beta>) a 1)"
      proof -
        \<comment> \<open>gen^k \<simeq> \<alpha>*\<beta> (symmetry of hpos).\<close>
        have hab_path: "top1_is_path_on X TX a a (top1_path_product \<alpha> \<beta>)"
          using h\<alpha>\<beta>_loop unfolding top1_is_loop_on_def by (by100 blast)
        \<comment> \<open>(\<alpha>*\<beta>)*const \<simeq> \<alpha>*\<beta> (right identity), so \<alpha>*\<beta> \<simeq> (\<alpha>*\<beta>)*const = path\_power (\<alpha>*\<beta>) a 1.\<close>
        have hri: "top1_path_homotopic_on X TX a a
            (top1_path_product (top1_path_product \<alpha> \<beta>) (top1_constant_path a))
            (top1_path_product \<alpha> \<beta>)"
          by (rule Theorem_51_2_right_identity[OF assms(1) hab_path])
        have hri_sym: "top1_path_homotopic_on X TX a a
            (top1_path_product \<alpha> \<beta>)
            (top1_path_product (top1_path_product \<alpha> \<beta>) (top1_constant_path a))"
          by (rule Lemma_51_1_path_homotopic_sym[OF hri])
        have hpp1_eq: "top1_path_power (top1_path_product \<alpha> \<beta>) a 1 =
            top1_path_product (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
          by simp
        have hab_pp1: "top1_path_homotopic_on X TX a a
            (top1_path_product \<alpha> \<beta>) (top1_path_power (top1_path_product \<alpha> \<beta>) a 1)"
          using hri_sym hpp1_eq by simp
        \<comment> \<open>Chain: gen^k \<simeq> \<alpha>*\<beta> \<simeq> path\_power (\<alpha>*\<beta>) a 1.\<close>
        show ?thesis
          by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hpos_sym hab_pp1])
      qed
      have h_endpoints: "(a, 2 * int k * d) = (a :: 'a, 2 :: int)"
      proof -
        note h = Theorem_54_3[OF hcov hTE assms(1) he0 hp0
            hgenk_path hab_path_raw h_genk_pp1
            hftk(1) hftk(2) hab_lift hab_lift_proj]
        from conjunct1[OF h] show ?thesis by simp
      qed
      hence "2 * int k * d = 2" by simp
      hence "int k * d = 1" by simp
      thus "k = 1"
      proof -
        from \<open>int k * d = 1\<close> have hunit: "int k * d = 1" .
        hence "int k = 1 \<or> int k = -1" using zmult_eq_1_iff by blast
        moreover have "int k \<ge> 0" by simp
        ultimately have "int k = 1" by auto
        thus "k = 1" by simp
      qed
    next
      assume hneg: "top1_path_homotopic_on X TX a a
          (top1_path_product \<alpha> \<beta>) (top1_path_power (top1_path_reverse gen) a k)"
      \<comment> \<open>Similar but with reverse gen. gen^{-k} \<simeq> \<alpha>*\<beta>.
         Lift of reverse(gen)^k from (a,0) ends at (a, -2kd).
         Equals (a, 2). So -2kd = 2, kd = -1. k \<ge> 1, d = -1/k.
         Only solution: k = 1, d = -1.\<close>
      \<comment> \<open>Same argument as positive case: lift reverse(gen) from (a,0),
         get endpoint (a, 2d') for some d'. Build reverse(gen)^k lift
         by induction with shift T\_{d'}, compare with (\<alpha>*\<beta>)^1 lift at (a,2).\<close>
      \<comment> \<open>Step 1: lift reverse(gen) from (a,0).\<close>
      have hrgen_path: "top1_is_path_on X TX a a (top1_path_reverse gen)"
        by (rule top1_path_reverse_is_path[OF hgen_path])
      obtain rgen_lift where hrgen_lift: "top1_is_path_on E TE (a, 0) (rgen_lift 1) rgen_lift"
          and hrgen_lift_proj: "\<forall>s\<in>I_set. p0 (rgen_lift s) = (top1_path_reverse gen) s"
        using Lemma_54_1_path_lifting[OF hcov he0 hp0 hrgen_path assms(1) hTE] by blast
      \<comment> \<open>Endpoint of rgen\_lift is in the fiber: (a, 2d') for some d'.\<close>
      obtain d' :: int where hrgen_end: "rgen_lift 1 = (a, 2 * d')"
      proof -
        have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have hend_E: "rgen_lift 1 \<in> E"
          using hrgen_lift unfolding top1_is_path_on_def top1_continuous_map_on_def
          using h1_I by (by100 blast)
        have "p0 (rgen_lift 1) = (top1_path_reverse gen) 1"
          using hrgen_lift_proj h1_I by (by100 blast)
        hence "fst (rgen_lift 1) = a"
          unfolding p0_def top1_path_reverse_def
          using hgen_path unfolding top1_is_path_on_def by (by100 simp)
        obtain x' n' where hpair: "rgen_lift 1 = (x', n')" by (cases "rgen_lift 1")
        hence "x' = a" using \<open>fst (rgen_lift 1) = a\<close> by simp
        have "(x', n') \<in> E" using hend_E hpair by simp
        hence "(even n' \<and> x' \<in> U) \<or> (odd n' \<and> x' \<in> V - U)" unfolding E_def by auto
        hence "even n'" using \<open>x' = a\<close> ha_U by (by100 blast)
        then obtain d'' where "n' = 2 * d''" using evenE by blast
        hence "rgen_lift 1 = (a, 2 * d'')" using hpair \<open>x' = a\<close> by simp
        thus ?thesis using that by blast
      qed
      \<comment> \<open>Step 2: reverse(gen)^k lift by induction (same as positive case with d').\<close>
      have hrgenk_lift: "\<exists>ftk. top1_is_path_on E TE (a, 0) (a, 2 * int k * d') ftk \<and>
          (\<forall>s\<in>I_set. p0 (ftk s) = top1_path_power (top1_path_reverse gen) a k s)"
      proof (induct k)
        case 0
        define ftk0 :: "real \<Rightarrow> ('a \<times> int)" where "ftk0 = (\<lambda>s. (a, 0::int))"
        have "top1_is_path_on E TE (a, 0) (a, 2 * int 0 * d') ftk0"
        proof -
          have "top1_is_path_on E TE (a, 0) (a, 0) ftk0"
            unfolding top1_is_path_on_def ftk0_def
          proof (intro conjI)
            have "top1_continuous_map_on I_set I_top E TE (top1_constant_path (a, 0::int))"
              by (rule top1_constant_path_continuous[OF hTE he0])
            thus "top1_continuous_map_on I_set I_top E TE (\<lambda>s. (a, 0::int))"
              unfolding top1_constant_path_def by simp
          qed simp+
          thus ?thesis by simp
        qed
        moreover have "\<forall>s\<in>I_set. p0 (ftk0 s) = top1_path_power (top1_path_reverse gen) a 0 s"
          unfolding ftk0_def p0_def by (simp add: top1_constant_path_def)
        ultimately show ?case by blast
      next
        case (Suc k')
        obtain ftk' where hftk'n: "top1_is_path_on E TE (a, 0) (a, 2 * int k' * d') ftk'"
            "\<forall>s\<in>I_set. p0 (ftk' s) = top1_path_power (top1_path_reverse gen) a k' s"
          using Suc.hyps by blast
        define T_d' :: "('a \<times> int) \<Rightarrow> ('a \<times> int)" where "T_d' = (\<lambda>(x, n). (x, n + 2*d'))"
        define ftk'n_shifted :: "real \<Rightarrow> ('a \<times> int)" where "ftk'n_shifted = T_d' \<circ> ftk'"
        have hTd'_cont: "top1_continuous_map_on E TE E TE T_d'"
        proof -
          note h = helix_shift_general_continuous[OF assms(1-3) assms(5) assms(7-8)]
          have "E = {x :: ('a \<times> int). even (snd x) \<and> fst x \<in> U \<or> odd (snd x) \<and> fst x \<in> V - U}"
            unfolding E_def by auto
          moreover have "TE = {W. W \<subseteq> E \<and>
              (\<forall>n. {x \<in> U. (x, 2 * n) \<in> W} \<in> TX) \<and>
              (\<forall>n. {x \<in> A. (x, 2 * n + 2) \<in> W} \<union> {x \<in> B. (x, 2 * n) \<in> W} \<union>
                    {x \<in> V - U. (x, 2 * n + 1) \<in> W} \<in> TX)}"
            unfolding TE_def E_def by auto
          moreover have "T_d' = (\<lambda>(x :: 'a, n :: int). (x, n + 2 * d'))" unfolding T_d'_def by auto
          ultimately show ?thesis using h by simp
        qed
        have hftk'n_shifted_path: "top1_is_path_on E TE (a, 2*d') (a, 2*d' + 2*int k'*d') ftk'n_shifted"
        proof -
          have hcomp_cont: "top1_continuous_map_on I_set I_top E TE ftk'n_shifted"
            unfolding ftk'n_shifted_def
            by (rule top1_continuous_map_on_comp[where Y=E and TY=TE])
               (use hftk'n(1) hTd'_cont in \<open>unfold top1_is_path_on_def, by100 blast\<close>)+
          show ?thesis unfolding top1_is_path_on_def
            using hcomp_cont
            unfolding ftk'n_shifted_def T_d'_def using hftk'n(1)
            unfolding top1_is_path_on_def by (by100 simp)
        qed
        have hftk'n_shifted_proj: "\<forall>s\<in>I_set. p0 (ftk'n_shifted s) =
            top1_path_power (top1_path_reverse gen) a k' s"
        proof (intro ballI)
          fix s assume "s \<in> I_set"
          have "p0 (ftk'n_shifted s) = p0 (T_d' (ftk' s))" unfolding ftk'n_shifted_def by simp
          also have "... = p0 (ftk' s)"
          proof -
            obtain x n where "T_d' (ftk' s) = (x, n)" by (cases "T_d' (ftk' s)")
            have "fst (T_d' (ftk' s)) = fst (ftk' s)" unfolding T_d'_def
              by (cases "ftk' s") (by100 simp)
            thus ?thesis unfolding p0_def by simp
          qed
          also have "... = top1_path_power (top1_path_reverse gen) a k' s"
            using hftk'n(2) \<open>s \<in> I_set\<close> by (by100 blast)
          finally show "p0 (ftk'n_shifted s) = top1_path_power (top1_path_reverse gen) a k' s" .
        qed
        have h_ep_eq: "2*d' + 2*int k'*d' = 2*int (Suc k')*d'"
          by (simp add: algebra_simps)
        have hrgen_lift_typed: "top1_is_path_on E TE (a, 0) (a, 2*d') rgen_lift"
          using hrgen_lift hrgen_end by simp
        define ftk_suc_n where "ftk_suc_n = top1_path_product rgen_lift ftk'n_shifted"
        have "top1_is_path_on E TE (a, 0) (a, 2*int (Suc k')*d') ftk_suc_n"
        proof -
          have "top1_is_path_on E TE (a, 0) (a, 2*d' + 2*int k'*d')
              (top1_path_product rgen_lift ftk'n_shifted)"
            by (rule top1_path_product_is_path[OF hTE hrgen_lift_typed hftk'n_shifted_path])
          thus ?thesis unfolding ftk_suc_n_def using h_ep_eq by simp
        qed
        moreover have "\<forall>s\<in>I_set. p0 (ftk_suc_n s) =
            top1_path_power (top1_path_reverse gen) a (Suc k') s"
        proof (intro ballI)
          fix s :: real assume hs: "s \<in> I_set"
          have "p0 (ftk_suc_n s) = p0 (top1_path_product rgen_lift ftk'n_shifted s)"
            unfolding ftk_suc_n_def by simp
          also have "... = (if s \<le> 1/2 then p0 (rgen_lift (2*s)) else p0 (ftk'n_shifted (2*s-1)))"
            unfolding top1_path_product_def p0_def by (by100 simp)
          also have "... = (if s \<le> 1/2 then (top1_path_reverse gen) (2*s)
              else top1_path_power (top1_path_reverse gen) a k' (2*s-1))"
          proof -
            have h1: "s \<le> 1/2 \<Longrightarrow> 2*s \<in> I_set"
              using hs unfolding top1_unit_interval_def by (by100 simp)
            have h2: "\<not>(s \<le> 1/2) \<Longrightarrow> 2*s-1 \<in> I_set"
              using hs unfolding top1_unit_interval_def by (by100 simp)
            show ?thesis using hrgen_lift_proj hftk'n_shifted_proj h1 h2 by (by100 simp)
          qed
          also have "... = top1_path_product (top1_path_reverse gen)
              (top1_path_power (top1_path_reverse gen) a k') s"
            unfolding top1_path_product_def by simp
          also have "... = top1_path_power (top1_path_reverse gen) a (Suc k') s" by simp
          finally show "p0 (ftk_suc_n s) = top1_path_power (top1_path_reverse gen) a (Suc k') s" .
        qed
        ultimately show ?case by blast
      qed
      \<comment> \<open>Step 3: reverse(gen)^k \<simeq> (\<alpha>*\<beta>)^1 \<Rightarrow> endpoints match \<Rightarrow> 2*k*d' = 2 \<Rightarrow> k*d' = 1 \<Rightarrow> k = 1.\<close>
      have hneg_sym: "top1_path_homotopic_on X TX a a
          (top1_path_power (top1_path_reverse gen) a k) (top1_path_product \<alpha> \<beta>)"
        by (rule Lemma_51_1_path_homotopic_sym[OF hneg])
      obtain ftk where hftk_neg: "top1_is_path_on E TE (a, 0) (a, 2 * int k * d') ftk"
          "\<forall>s\<in>I_set. p0 (ftk s) = top1_path_power (top1_path_reverse gen) a k s"
        using hrgenk_lift by blast
      have hrgen_loop: "top1_is_loop_on X TX a (top1_path_reverse gen)"
        by (rule top1_path_reverse_is_loop[OF hgen_loop])
      have hrgenk_path: "top1_is_path_on X TX a a
          (top1_path_power (top1_path_reverse gen) a k)"
        by (rule top1_path_power_is_path[OF assms(1) hrgen_loop])
      have hab_path_raw: "top1_is_path_on X TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a 1)"
        by (rule top1_path_power_is_path[OF assms(1) h\<alpha>\<beta>_loop])
      have hab_path: "top1_is_path_on X TX a a (top1_path_product \<alpha> \<beta>)"
        using h\<alpha>\<beta>_loop unfolding top1_is_loop_on_def by (by100 blast)
      have hri: "top1_path_homotopic_on X TX a a
          (top1_path_product (top1_path_product \<alpha> \<beta>) (top1_constant_path a))
          (top1_path_product \<alpha> \<beta>)"
        by (rule Theorem_51_2_right_identity[OF assms(1) hab_path])
      have hab_pp1: "top1_path_homotopic_on X TX a a
          (top1_path_product \<alpha> \<beta>) (top1_path_power (top1_path_product \<alpha> \<beta>) a 1)"
        using Lemma_51_1_path_homotopic_sym[OF hri] by simp
      have hproj_pp1: "top1_path_homotopic_on X TX a a
          (top1_path_power (top1_path_reverse gen) a k)
          (top1_path_power (top1_path_product \<alpha> \<beta>) a 1)"
        by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hneg_sym hab_pp1])
      have h_endpoints_neg: "(a, 2 * int k * d') = (a :: 'a, 2 :: int)"
      proof -
        note h = Theorem_54_3[OF hcov hTE assms(1) he0 hp0
            hrgenk_path hab_path_raw hproj_pp1
            hftk_neg(1) hftk_neg(2) hab_lift hab_lift_proj]
        from conjunct1[OF h] show ?thesis by simp
      qed
      hence "2 * int k * d' = 2" by simp
      hence "int k * d' = 1" by simp
      thus "k = 1"
      proof -
        from \<open>int k * d' = 1\<close> have "int k = 1 \<or> int k = -1" using zmult_eq_1_iff by blast
        moreover have "int k \<ge> 0" by simp
        ultimately have "int k = 1" by auto
        thus "k = 1" by simp
      qed
    qed
  qed
  \<comment> \<open>Step 7: Conclude. k = 1 means [\<alpha>*\<beta>] = gen (or gen\<inverse>). So gen generates with [\<alpha>*\<beta>].\<close>
  show ?thesis
  proof (intro allI impI)
    fix f assume hf: "top1_is_loop_on X TX a f"
    obtain n :: nat where hn: "top1_path_homotopic_on X TX a a f (top1_path_power gen a n)
        \<or> top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_reverse gen) a n)"
      using hgen_all[THEN spec, of f] hf by blast
    show "\<exists>n::nat. top1_path_homotopic_on X TX a a f
        (top1_path_power (top1_path_product \<alpha> \<beta>) a n)
      \<or> top1_path_homotopic_on X TX a a f
           (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n)"
    proof (cases "top1_path_homotopic_on X TX a a
        (top1_path_product \<alpha> \<beta>) (top1_path_power gen a k)")
      case True
      \<comment> \<open>[\<alpha>*\<beta>] = gen^k = gen^1 = gen. So gen^n = (\<alpha>*\<beta>)^n.\<close>
      have "k = 1" by (rule hk_one)
      \<comment> \<open>gen^1 = gen * const \<simeq> gen, so \<alpha>*\<beta> \<simeq> gen.\<close>
      have hgen1_eq: "top1_path_homotopic_on X TX a a
          (top1_path_power gen a 1) gen"
      proof -
        have "top1_path_power gen a 1 = top1_path_product gen (top1_constant_path a)"
          by simp
        moreover have "top1_path_homotopic_on X TX a a
            (top1_path_product gen (top1_constant_path a)) gen"
          by (rule Theorem_51_2_right_identity[OF assms(1) hgen_path])
        ultimately show ?thesis by simp
      qed
      have h_eq: "top1_path_homotopic_on X TX a a
          (top1_path_product \<alpha> \<beta>) gen"
      proof -
        have hab_gen1: "top1_path_homotopic_on X TX a a
            (top1_path_product \<alpha> \<beta>) (top1_path_power gen a 1)"
          using True \<open>k = 1\<close> by simp
        show ?thesis
          by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hab_gen1 hgen1_eq])
      qed
      \<comment> \<open>gen \<simeq> \<alpha>*\<beta>. So gen^n \<simeq> (\<alpha>*\<beta>)^n and gen^{-n} \<simeq> (\<alpha>*\<beta>)^{-n}.\<close>
      show ?thesis
      proof -
        have hgen_path2: "top1_is_path_on X TX a a gen"
          using hgen_loop unfolding top1_is_loop_on_def by (by100 blast)
        have hab_path: "top1_is_path_on X TX a a (top1_path_product \<alpha> \<beta>)"
          using h\<alpha>\<beta>_loop unfolding top1_is_loop_on_def by (by100 blast)
        have h_eq_sym: "top1_path_homotopic_on X TX a a gen (top1_path_product \<alpha> \<beta>)"
          using h_eq by (rule Lemma_51_1_path_homotopic_sym)
        have hpow: "top1_path_homotopic_on X TX a a
            (top1_path_power gen a n) (top1_path_power (top1_path_product \<alpha> \<beta>) a n)"
          by (rule path_homotopic_path_power[OF assms(1) h_eq_sym hgen_path2 hab_path])
        have h_req: "top1_path_homotopic_on X TX a a
            (top1_path_reverse gen) (top1_path_reverse (top1_path_product \<alpha> \<beta>))"
          by (rule path_homotopic_reverse[OF assms(1) h_eq_sym hgen_path2 hab_path])
        have hrgen_path: "top1_is_path_on X TX a a (top1_path_reverse gen)"
          by (rule top1_path_reverse_is_path[OF hgen_path2])
        have hrab_path: "top1_is_path_on X TX a a
            (top1_path_reverse (top1_path_product \<alpha> \<beta>))"
          by (rule top1_path_reverse_is_path[OF hab_path])
        have hpow_rev: "top1_path_homotopic_on X TX a a
            (top1_path_power (top1_path_reverse gen) a n)
            (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n)"
          by (rule path_homotopic_path_power[OF assms(1) h_req hrgen_path hrab_path])
        from hn show ?thesis
        proof
          assume hf_gen: "top1_path_homotopic_on X TX a a f (top1_path_power gen a n)"
          have "top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_product \<alpha> \<beta>) a n)"
            by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hf_gen hpow])
          thus ?thesis by blast
        next
          assume hf_rgen: "top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_reverse gen) a n)"
          have "top1_path_homotopic_on X TX a a f
              (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n)"
            by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hf_rgen hpow_rev])
          thus ?thesis by blast
        qed
      qed
    next
      case False
      \<comment> \<open>[\<alpha>*\<beta>] = gen^{-k} = gen^{-1}. So gen = reverse(\<alpha>*\<beta>).\<close>
      hence hneg: "top1_path_homotopic_on X TX a a
          (top1_path_product \<alpha> \<beta>) (top1_path_power (top1_path_reverse gen) a k)"
        using hk by (by100 blast)
      have "k = 1" by (rule hk_one)
      \<comment> \<open>reverse(gen)^1 \<simeq> reverse(gen), so \<alpha>*\<beta> \<simeq> reverse(gen), i.e., gen \<simeq> reverse(\<alpha>*\<beta>).\<close>
      \<comment> \<open>reverse(gen)^1 = reverse(gen)*const \<simeq> reverse(gen).\<close>
      have hrgen1_eq: "top1_path_homotopic_on X TX a a
          (top1_path_power (top1_path_reverse gen) a 1) (top1_path_reverse gen)"
      proof -
        have hrg_path: "top1_is_path_on X TX a a (top1_path_reverse gen)"
          by (rule top1_path_reverse_is_path[OF hgen_path])
        have "top1_path_power (top1_path_reverse gen) a 1 =
            top1_path_product (top1_path_reverse gen) (top1_constant_path a)" by simp
        moreover have "top1_path_homotopic_on X TX a a
            (top1_path_product (top1_path_reverse gen) (top1_constant_path a)) (top1_path_reverse gen)"
          by (rule Theorem_51_2_right_identity[OF assms(1) hrg_path])
        ultimately show ?thesis by simp
      qed
      have h_eq_neg: "top1_path_homotopic_on X TX a a
          (top1_path_product \<alpha> \<beta>) (top1_path_reverse gen)"
      proof -
        have "top1_path_homotopic_on X TX a a
            (top1_path_product \<alpha> \<beta>) (top1_path_power (top1_path_reverse gen) a 1)"
          using hneg \<open>k = 1\<close> by simp
        thus ?thesis
          by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) _ hrgen1_eq])
      qed
      \<comment> \<open>reverse(gen) \<simeq> \<alpha>*\<beta>. So gen \<simeq> reverse(\<alpha>*\<beta>).
         Then gen^n \<simeq> reverse(\<alpha>*\<beta>)^n and reverse(gen)^n \<simeq> (\<alpha>*\<beta>)^n.\<close>
      show ?thesis
      proof -
        have hgen_path2: "top1_is_path_on X TX a a gen"
          using hgen_loop unfolding top1_is_loop_on_def by (by100 blast)
        have hab_path: "top1_is_path_on X TX a a (top1_path_product \<alpha> \<beta>)"
          using h\<alpha>\<beta>_loop unfolding top1_is_loop_on_def by (by100 blast)
        have hrgen_path: "top1_is_path_on X TX a a (top1_path_reverse gen)"
          by (rule top1_path_reverse_is_path[OF hgen_path2])
        have hrab_path: "top1_is_path_on X TX a a
            (top1_path_reverse (top1_path_product \<alpha> \<beta>))"
          by (rule top1_path_reverse_is_path[OF hab_path])
        \<comment> \<open>\<alpha>*\<beta> \<simeq> reverse(gen). So reverse(\<alpha>*\<beta>) \<simeq> gen (reverse both sides).\<close>
        have h_eq_neg_sym: "top1_path_homotopic_on X TX a a
            (top1_path_reverse gen) (top1_path_product \<alpha> \<beta>)"
          by (rule Lemma_51_1_path_homotopic_sym[OF h_eq_neg])
        have h_rr_gen: "top1_path_homotopic_on X TX a a
            (top1_path_reverse (top1_path_reverse gen)) (top1_path_reverse (top1_path_product \<alpha> \<beta>))"
          by (rule path_homotopic_reverse[OF assms(1) h_eq_neg_sym hrgen_path hab_path])
        have h_gen_rab: "top1_path_homotopic_on X TX a a
            gen (top1_path_reverse (top1_path_product \<alpha> \<beta>))"
          using h_rr_gen top1_path_reverse_twice[of gen] by simp
        \<comment> \<open>gen^n \<simeq> reverse(\<alpha>*\<beta>)^n.\<close>
        have hpow: "top1_path_homotopic_on X TX a a
            (top1_path_power gen a n) (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n)"
          by (rule path_homotopic_path_power[OF assms(1) h_gen_rab hgen_path2 hrab_path])
        \<comment> \<open>reverse(gen) \<simeq> \<alpha>*\<beta>. So reverse(gen)^n \<simeq> (\<alpha>*\<beta>)^n.\<close>
        have h_rgen_ab: "top1_path_homotopic_on X TX a a
            (top1_path_reverse gen) (top1_path_product \<alpha> \<beta>)"
          by (rule Lemma_51_1_path_homotopic_sym[OF h_eq_neg])
        have hpow_rev: "top1_path_homotopic_on X TX a a
            (top1_path_power (top1_path_reverse gen) a n)
            (top1_path_power (top1_path_product \<alpha> \<beta>) a n)"
          by (rule path_homotopic_path_power[OF assms(1) h_rgen_ab hrgen_path hab_path])
        from hn show ?thesis
        proof
          assume hf_gen: "top1_path_homotopic_on X TX a a f (top1_path_power gen a n)"
          have "top1_path_homotopic_on X TX a a f
              (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n)"
            by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hf_gen hpow])
          thus ?thesis by blast
        next
          assume hf_rgen: "top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_reverse gen) a n)"
          have "top1_path_homotopic_on X TX a a f
              (top1_path_power (top1_path_product \<alpha> \<beta>) a n)"
            by (rule Lemma_51_1_path_homotopic_trans[OF assms(1) hf_rgen hpow_rev])
          thus ?thesis by blast
        qed
      qed
    qed
  qed
qed

section \<open>Theorem 58.7 (fixed): homotopy equivalence induces \<pi>_1 isomorphism\<close>

text \<open>Munkres Theorem 58.7: If f: X \<rightarrow> Y is a homotopy equivalence with f(x0)=y0,
  then f_*: \<pi>_1(X,x0) \<rightarrow> \<pi>_1(Y,y0) is an isomorphism.
  The induced map is top1_fundamental_group_induced_on X TX x0 Y TY (f x0) f.\<close>

\<comment> \<open>Helper: surjective group hom between infinite cyclic groups is injective.
   If G \<cong> Z (with generator gen) and H \<cong> Z, and \<phi>: G \<rightarrow> H is a surjective hom,
   then \<phi> is injective. Proof: \<phi>(gen) generates \<phi>(G) = H.
   So \<phi>(gen) = \<plusminus>gen\_H. Since \<phi>(gen^n) = \<phi>(gen)^n = (\<plusminus>gen\_H)^n:
   if \<phi>(gen^n) = e\_H then n = 0. So ker(\<phi>) = {e\_G}, i.e. \<phi> injective.\<close>
lemma surj_hom_infinite_cyclic_inj:
  assumes hGX_Z: "top1_groups_isomorphic_on GX mulX top1_Z_group top1_Z_mul"
      and hGY_Z: "top1_groups_isomorphic_on GY mulY top1_Z_group top1_Z_mul"
      and hphi_hom: "top1_group_hom_on GX mulX GY mulY \<phi>"
      and hphi_surj: "\<phi> ` GX = GY"
      and hGX_closed: "\<And>a b. a \<in> GX \<Longrightarrow> b \<in> GX \<Longrightarrow> mulX a b \<in> GX"
  shows "inj_on \<phi> GX"
proof -
  let ?GX = GX let ?mulX = mulX let ?GY = GY let ?mulY = mulY
  \<comment> \<open>Get iso witnesses: \<psi>\_X: \<pi>_1(X) \<cong> Z and \<psi>\_Y: \<pi>_1(Y) \<cong> Z.\<close>
  from hGX_Z obtain \<psi>X where h\<psi>X: "top1_group_iso_on ?GX ?mulX top1_Z_group top1_Z_mul \<psi>X"
    unfolding top1_groups_isomorphic_on_def by blast
  from hGY_Z obtain \<psi>Y where h\<psi>Y: "top1_group_iso_on ?GY ?mulY top1_Z_group top1_Z_mul \<psi>Y"
    unfolding top1_groups_isomorphic_on_def by blast
  \<comment> \<open>Compose: \<psi>\_Y \<circ> \<phi> \<circ> \<psi>\_X\<inverse>: Z \<rightarrow> Z is a surjective group hom.\<close>
  \<comment> \<open>In Z, surjective hom = multiplication by \<plusminus>1 = bijection.\<close>
  \<comment> \<open>Therefore \<phi> is injective (composition of injective maps).\<close>
  \<comment> \<open>The Z-arithmetic: if h: Z \<rightarrow> Z is a group hom, h(n) = n * h(1).
     Surjective means h(1) divides every integer, so |h(1)| = 1.
     Hence h is bijective.\<close>
  \<comment> \<open>Pure Z-arithmetic lemma: surjective hom Z \<rightarrow> Z is injective.\<close>
  have hZ_surj_inj: "\<And>h :: int \<Rightarrow> int. \<lbrakk>\<forall>a b. h (a + b) = h a + h b; h ` UNIV = UNIV\<rbrakk> \<Longrightarrow> inj h"
  proof -
    fix h :: "int \<Rightarrow> int"
    assume hhom: "\<forall>a b. h (a + b) = h a + h b" and hsurj: "h ` UNIV = UNIV"
    \<comment> \<open>h(n) = n * h(1).\<close>
    have h0: "h 0 = 0" using hhom[THEN spec, THEN spec, of 0 0] by (by100 simp)
    have hn: "\<And>n::int. h n = n * h 1"
    proof -
      fix n :: int
      have hS: "\<And>m. h (m + 1) = h m + h 1" using hhom by auto
      have hP: "\<And>m::int. h (m - 1) = h m - h 1"
      proof -
        fix m :: int
        from hhom have "h ((m - 1) + 1) = h (m - 1) + h 1" by blast
        thus "h (m - 1) = h m - h 1" by simp
      qed
      show "h n = n * h 1"
      proof (cases "n \<ge> 0")
        case True
        then show ?thesis
        proof (induct n rule: int_ge_induct)
          case base show ?case using h0 by auto
        next
          case (step n)
          have "h (n + 1) = h n + h 1" using hS by auto
          also have "\<dots> = n * h 1 + h 1" using step.hyps(2) by auto
          also have "\<dots> = (n + 1) * h 1" by (simp add: algebra_simps)
          finally show ?case .
        qed
      next
        case False hence "n < 0" by auto
        hence "- n \<ge> 0" by auto
        \<comment> \<open>h(-m) = -h(m) for all m (from h(a+b)=h(a)+h(b) and h(0)=0).\<close>
        have hneg: "\<And>m::int. h (-m) = - h m"
        proof -
          fix m :: int
          have "h (m + (-m)) = h m + h (-m)" using hhom by blast
          hence "h 0 = h m + h (-m)" by auto
          thus "h (-m) = - h m" using h0 by auto
        qed
        \<comment> \<open>h(-n) = -h(n). h(|n|) = |n|*h(1) by positive case. So h(n) = n*h(1).\<close>
        have "h n = n * h 1"
        proof -
          obtain m where hm: "m = nat (-n)" by blast
          have hm_pos: "-n = int m" using \<open>n < 0\<close> hm by auto
          have "h (int m) = int m * h 1"
          proof (induct m)
            case 0 show ?case using h0 by auto
          next
            case (Suc k)
            have "int (Suc k) = int k + 1" by simp
            hence "h (int (Suc k)) = h (int k) + h 1" using hhom by auto
            also have "\<dots> = int k * h 1 + h 1" using Suc by auto
            also have "\<dots> = int (Suc k) * h 1" by (simp add: algebra_simps)
            finally show ?case .
          qed
          hence "h (-n) = (-n) * h 1" using hm_pos by auto
          thus ?thesis using hneg[of "-n"] by auto
        qed
        thus ?thesis .
      qed
    qed
    \<comment> \<open>Surjective: 1 \<in> range(h), so \<exists>n. n * h(1) = 1. Hence |h(1)| = 1.\<close>
    have "h 1 = 1 \<or> h 1 = -1"
    proof -
      have "\<exists>n::int. h n = 1"
      proof -
        have "(1::int) \<in> UNIV" by (by100 blast)
        hence "(1::int) \<in> h ` UNIV" using hsurj by (by100 simp)
        thus ?thesis by auto
      qed
      then obtain n :: int where hn1: "h n = 1" by blast
      have "h n = n * h 1" by (rule hn)
      hence "n * h 1 = (1::int)" using hn1 by (by100 simp)
      hence "h 1 * n = (1::int)" by (simp add: mult.commute)
      hence "\<bar>h 1\<bar> = 1" using zmult_eq_1_iff by auto
      thus ?thesis by auto
    qed
    \<comment> \<open>h injective: h(a) = h(b) \<Rightarrow> a*h(1) = b*h(1) \<Rightarrow> a = b (since |h(1)| = 1).\<close>
    thus "inj h"
    proof (elim disjE)
      assume h1: "h 1 = 1"
      have "\<And>n. h n = n" using hn h1 by auto
      thus "inj h" by (intro injI) auto
    next
      assume h1: "h 1 = -1"
      have "\<And>n. h n = -n" using hn h1 by auto
      thus "inj h" by (intro injI) auto
    qed
  qed
  \<comment> \<open>Transfer from Z to \<pi>\_1 via the isomorphisms.\<close>
  \<comment> \<open>\<psi>\_Y \<circ> \<phi> \<circ> inv(\<psi>\_X) is a surjective hom Z \<rightarrow> Z, hence injective.
     Since \<psi>\_X and \<psi>\_Y are bijective, \<phi> is injective.\<close>
  \<comment> \<open>Define composed map h = \<psi>\_Y \<circ> \<phi> \<circ> inv(\<psi>\_X) : Z \<rightarrow> Z.\<close>
  define invPsiX where "invPsiX = inv_into ?GX \<psi>X"
  have hPsiX_bij: "bij_betw \<psi>X ?GX top1_Z_group"
    using h\<psi>X unfolding top1_group_iso_on_def by (by100 blast)
  have hPsiY_bij: "bij_betw \<psi>Y ?GY top1_Z_group"
    using h\<psi>Y unfolding top1_group_iso_on_def by (by100 blast)
  have hinvPsiX_bij: "bij_betw invPsiX top1_Z_group ?GX"
    unfolding invPsiX_def by (rule bij_betw_inv_into[OF hPsiX_bij])
  define comp_h where "comp_h = \<psi>Y \<circ> \<phi> \<circ> invPsiX"
  \<comment> \<open>comp\_h is a surjective map Z \<rightarrow> Z.\<close>
  have hcomp_surj: "comp_h ` top1_Z_group = top1_Z_group"
  proof -
    have "invPsiX ` top1_Z_group = ?GX" using hinvPsiX_bij unfolding bij_betw_def by (by100 blast)
    hence "\<phi> ` (invPsiX ` top1_Z_group) = \<phi> ` ?GX" by (by100 simp)
    hence "\<phi> ` (invPsiX ` top1_Z_group) = ?GY" using hphi_surj by (by100 simp)
    hence "\<psi>Y ` (\<phi> ` (invPsiX ` top1_Z_group)) = \<psi>Y ` ?GY" by (by100 simp)
    moreover have "\<psi>Y ` ?GY = top1_Z_group" using hPsiY_bij unfolding bij_betw_def by (by100 blast)
    ultimately have "\<psi>Y ` (\<phi> ` (invPsiX ` top1_Z_group)) = top1_Z_group" by (by100 simp)
    moreover have "(\<psi>Y \<circ> \<phi> \<circ> invPsiX) ` top1_Z_group = \<psi>Y ` (\<phi> ` (invPsiX ` top1_Z_group))"
      by (simp add: image_comp)
    ultimately show ?thesis unfolding comp_h_def by auto
  qed
  \<comment> \<open>comp\_h is a group hom Z \<rightarrow> Z, i.e. additive.\<close>
  \<comment> \<open>comp\_h additive: ψ\_Y(φ(invPsiX(a+b))) = ψ\_Y(φ(invPsiX(a))) + ψ\_Y(φ(invPsiX(b))).
     Each step preserves the group operation.\<close>
  have hcomp_add: "\<forall>a b. comp_h (a + b) = comp_h a + comp_h b"
  proof (intro allI)
    fix a b :: int
    \<comment> \<open>invPsiX hom: invPsiX(a+b) = mulX(invPsiX a, invPsiX b).\<close>
    have hinvPsiX_hom: "\<forall>x\<in>top1_Z_group. \<forall>y\<in>top1_Z_group.
        invPsiX (top1_Z_mul x y) = ?mulX (invPsiX x) (invPsiX y)"
    proof (intro ballI)
      fix x y assume hx: "x \<in> top1_Z_group" and hy: "y \<in> top1_Z_group"
      \<comment> \<open>\<psi>\_X is iso: hom + bij. So \<psi>\_X(mulX(a,b)) = mulZ(\<psi>\_X a, \<psi>\_X b).
         inv(\<psi>\_X)(mulZ(x,y)) = mulX(inv(\<psi>\_X)(x), inv(\<psi>\_X)(y)).\<close>
      have hPsiX_hom: "\<forall>a\<in>?GX. \<forall>b\<in>?GX. \<psi>X (?mulX a b) = top1_Z_mul (\<psi>X a) (\<psi>X b)"
        using h\<psi>X unfolding top1_group_iso_on_def top1_group_hom_on_def by (by100 blast)
      have hinvX: "invPsiX x \<in> ?GX" using hinvPsiX_bij hx unfolding bij_betw_def by (by100 blast)
      have hinvY: "invPsiX y \<in> ?GX" using hinvPsiX_bij hy unfolding bij_betw_def by (by100 blast)
      have "\<psi>X (?mulX (invPsiX x) (invPsiX y)) = top1_Z_mul (\<psi>X (invPsiX x)) (\<psi>X (invPsiX y))"
        using hPsiX_hom hinvX hinvY by (by100 blast)
      also have "\<psi>X (invPsiX x) = x"
        unfolding invPsiX_def by (rule f_inv_into_f[OF])
           (use hx hPsiX_bij in \<open>unfold bij_betw_def, by100 blast\<close>)
      also have "\<psi>X (invPsiX y) = y"
        unfolding invPsiX_def by (rule f_inv_into_f[OF])
           (use hy hPsiX_bij in \<open>unfold bij_betw_def, by100 blast\<close>)
      finally have "\<psi>X (?mulX (invPsiX x) (invPsiX y)) = top1_Z_mul x y" .
      \<comment> \<open>Apply inv(\<psi>\_X) to both sides.\<close>
      hence "invPsiX (\<psi>X (?mulX (invPsiX x) (invPsiX y))) = invPsiX (top1_Z_mul x y)"
        by (by100 simp)
      moreover have "invPsiX (\<psi>X (?mulX (invPsiX x) (invPsiX y))) = ?mulX (invPsiX x) (invPsiX y)"
      proof -
        have "?mulX (invPsiX x) (invPsiX y) \<in> ?GX"
          by (rule hGX_closed[OF hinvX hinvY])
        thus ?thesis unfolding invPsiX_def
          by (rule bij_betw_inv_into_left[OF hPsiX_bij])
      qed
      ultimately show "invPsiX (top1_Z_mul x y) = ?mulX (invPsiX x) (invPsiX y)" by (by100 simp)
    qed
    have ha: "a \<in> top1_Z_group" unfolding top1_Z_group_def by (by100 simp)
    have hb: "b \<in> top1_Z_group" unfolding top1_Z_group_def by (by100 simp)
    have "top1_Z_mul a b = a + b" unfolding top1_Z_mul_def by (by100 simp)
    have hinvAB: "invPsiX (a + b) = ?mulX (invPsiX a) (invPsiX b)"
      using hinvPsiX_hom[THEN bspec, OF ha, THEN bspec, OF hb]
      unfolding \<open>top1_Z_mul a b = a + b\<close>[symmetric] by (by100 simp)
    \<comment> \<open>\<phi> hom: \<phi>(mulX(x,y)) = mulY(\<phi> x, \<phi> y).\<close>
    have hinvA_GX: "invPsiX a \<in> ?GX" using hinvPsiX_bij ha unfolding bij_betw_def by (by100 blast)
    have hinvB_GX: "invPsiX b \<in> ?GX" using hinvPsiX_bij hb unfolding bij_betw_def by (by100 blast)
    have hphiAB: "\<phi> (?mulX (invPsiX a) (invPsiX b)) = ?mulY (\<phi> (invPsiX a)) (\<phi> (invPsiX b))"
      using hphi_hom hinvA_GX hinvB_GX unfolding top1_group_hom_on_def by (by100 blast)
    \<comment> \<open>\<psi>\_Y hom: \<psi>\_Y(mulY(x,y)) = mulZ(\<psi>\_Y x, \<psi>\_Y y) = \<psi>\_Y x + \<psi>\_Y y.\<close>
    have hphiA_GY: "\<phi> (invPsiX a) \<in> ?GY"
      using hphi_hom hinvA_GX unfolding top1_group_hom_on_def by (by100 blast)
    have hphiB_GY: "\<phi> (invPsiX b) \<in> ?GY"
      using hphi_hom hinvB_GX unfolding top1_group_hom_on_def by (by100 blast)
    have hpsiYAB: "\<psi>Y (?mulY (\<phi> (invPsiX a)) (\<phi> (invPsiX b))) =
        top1_Z_mul (\<psi>Y (\<phi> (invPsiX a))) (\<psi>Y (\<phi> (invPsiX b)))"
      using h\<psi>Y hphiA_GY hphiB_GY unfolding top1_group_iso_on_def top1_group_hom_on_def by (by100 blast)
    \<comment> \<open>Chain: comp\_h(a+b) = \<psi>\_Y(\<phi>(invPsiX(a+b)))
         = \<psi>\_Y(\<phi>(mulX(invPsiX a, invPsiX b)))
         = \<psi>\_Y(mulY(\<phi>(invPsiX a), \<phi>(invPsiX b)))
         = \<psi>\_Y(\<phi>(invPsiX a)) + \<psi>\_Y(\<phi>(invPsiX b))
         = comp\_h a + comp\_h b.\<close>
    have "comp_h (a + b) = \<psi>Y (\<phi> (invPsiX (a + b)))"
      unfolding comp_h_def by (by100 simp)
    also have "\<dots> = \<psi>Y (\<phi> (?mulX (invPsiX a) (invPsiX b)))" using hinvAB by (by100 simp)
    also have "\<dots> = \<psi>Y (?mulY (\<phi> (invPsiX a)) (\<phi> (invPsiX b)))" using hphiAB by (by100 simp)
    also have "\<dots> = top1_Z_mul (\<psi>Y (\<phi> (invPsiX a))) (\<psi>Y (\<phi> (invPsiX b)))" using hpsiYAB .
    also have "\<dots> = \<psi>Y (\<phi> (invPsiX a)) + \<psi>Y (\<phi> (invPsiX b))"
      unfolding top1_Z_mul_def by (by100 simp)
    also have "\<dots> = comp_h a + comp_h b" unfolding comp_h_def by (by100 simp)
    finally show "comp_h (a + b) = comp_h a + comp_h b" .
  qed
  have hZ_UNIV: "top1_Z_group = (UNIV :: int set)" unfolding top1_Z_group_def by (by100 simp)
  have hcomp_surj_UNIV: "comp_h ` UNIV = (UNIV :: int set)"
    using hcomp_surj hZ_UNIV by (by100 simp)
  \<comment> \<open>By hZ\_surj\_inj: comp\_h is injective.\<close>
  have hcomp_inj: "inj comp_h"
    by (rule hZ_surj_inj[OF hcomp_add hcomp_surj_UNIV])
  \<comment> \<open>\<phi> = inv(\<psi>\_Y) \<circ> comp\_h \<circ> \<psi>\_X. All three are injective, so \<phi> is injective.\<close>
  \<comment> \<open>\<phi>(x) = \<phi>(y) \<Rightarrow> \<psi>\_Y(\<phi>(x)) = \<psi>\_Y(\<phi>(y)) \<Rightarrow> comp\_h(\<psi>\_X(x)) = comp\_h(\<psi>\_X(y))
     \<Rightarrow> \<psi>\_X(x) = \<psi>\_X(y) (comp\_h inj) \<Rightarrow> x = y (\<psi>\_X inj).\<close>
  show "inj_on \<phi> ?GX"
  proof (rule inj_onI)
    fix x y assume hx: "x \<in> ?GX" and hy: "y \<in> ?GX" and hphi_eq: "\<phi> x = \<phi> y"
    have "\<psi>Y (\<phi> x) = \<psi>Y (\<phi> y)" using hphi_eq by (by100 simp)
    have hPsiX_x: "\<psi>X x \<in> top1_Z_group" using hPsiX_bij hx unfolding bij_betw_def by (by100 blast)
    have hPsiX_y: "\<psi>X y \<in> top1_Z_group" using hPsiX_bij hy unfolding bij_betw_def by (by100 blast)
    have hinvX: "invPsiX (\<psi>X x) = x"
      unfolding invPsiX_def by (rule bij_betw_inv_into_left[OF hPsiX_bij hx])
    have hinvY: "invPsiX (\<psi>X y) = y"
      unfolding invPsiX_def by (rule bij_betw_inv_into_left[OF hPsiX_bij hy])
    have "comp_h (\<psi>X x) = \<psi>Y (\<phi> (invPsiX (\<psi>X x)))"
      unfolding comp_h_def by (by100 simp)
    hence "comp_h (\<psi>X x) = \<psi>Y (\<phi> x)" using hinvX by (by100 simp)
    moreover have "comp_h (\<psi>X y) = \<psi>Y (\<phi> y)"
      unfolding comp_h_def using hinvY by (by100 simp)
    ultimately have "comp_h (\<psi>X x) = comp_h (\<psi>X y)"
      using \<open>\<psi>Y (\<phi> x) = \<psi>Y (\<phi> y)\<close> by (by100 simp)
    hence "\<psi>X x = \<psi>X y" using hcomp_inj unfolding inj_def by (by100 blast)
    thus "x = y" using hPsiX_bij hx hy unfolding bij_betw_def inj_on_def by (by100 blast)
  qed
qed

\<comment> \<open>Helper: induced map with id equals induced map with (\<lambda>x. x).\<close>
lemma induced_id_eq_lam:
  "top1_fundamental_group_induced_on A TA x0 X TX x0 id =
   top1_fundamental_group_induced_on A TA x0 X TX x0 (\<lambda>x. x)"
proof -
  have "id = (\<lambda>x::'a. x)" by auto
  thus ?thesis by (by100 simp)
qed

\<comment> \<open>Helper: if f \<simeq> g in X (path homotopic), then [f]\_X = [g]\_X.\<close>
lemma path_homotopic_same_class:
  assumes hTX: "is_topology_on X TX"
      and "top1_path_homotopic_on X TX a a f g"
  shows "{h. top1_loop_equiv_on X TX a f h} = {h. top1_loop_equiv_on X TX a g h}"
proof -
  \<comment> \<open>f \<simeq> g implies loop\_equiv f g.\<close>
  have hfg: "top1_loop_equiv_on X TX a f g"
    using assms(2) unfolding top1_loop_equiv_on_def top1_is_loop_on_def
      top1_path_homotopic_on_def by (by100 blast)
  have hgf: "top1_loop_equiv_on X TX a g f"
    by (rule top1_loop_equiv_on_sym[OF hfg])
  have "\<And>k. top1_loop_equiv_on X TX a f k \<Longrightarrow> top1_loop_equiv_on X TX a g k"
    using top1_loop_equiv_on_trans[OF hTX hgf] .
  moreover have "\<And>k. top1_loop_equiv_on X TX a g k \<Longrightarrow> top1_loop_equiv_on X TX a f k"
    using top1_loop_equiv_on_trans[OF hTX hfg] .
  ultimately show ?thesis by (by100 blast)
qed

\<comment> \<open>Helper: for a loop g in C \<subseteq> X, the inclusion-induced map sends [g]\_C to [g]\_X.\<close>
lemma inclusion_sends_class:
  assumes "is_topology_on X TX" "A \<subseteq> X" "x0 \<in> A"
      and "top1_is_loop_on A (subspace_topology X TX A) x0 g"
  shows "top1_fundamental_group_induced_on A (subspace_topology X TX A) x0 X TX x0 id
      {h. top1_loop_equiv_on A (subspace_topology X TX A) x0 g h} =
      {k. top1_loop_equiv_on X TX x0 g k}"
proof -
  from subspace_inclusion_induced_class[OF assms(1,2,4)]
  have "top1_fundamental_group_induced_on A (subspace_topology X TX A) x0 X TX x0 (\<lambda>x. x)
      {k. top1_loop_equiv_on A (subspace_topology X TX A) x0 g k} =
      {k. top1_loop_equiv_on X TX x0 g k}" .
  thus ?thesis unfolding induced_id_eq_lam .
qed

\<comment> \<open>Helpers and K4_nonadjacent copied from AlgTop.thy (oracle-clean).\<close>

lemma subset_disjoint_helper:
  assumes "S \<subseteq> A" and "A \<inter> B = {}" shows "S \<inter> B = {}"
  using assms by (by100 blast)

lemma K4_final_contradiction:
  assumes he12_Ri: "e12_int \<inter> Ri = {}" and hRi_comp: "Ri = A \<or> Ri = B"
      and hAB_disj: "A \<inter> B = {}" and he12_ne: "e12_int \<noteq> {}"
      and he34_Ri: "e34_int \<subseteq> Ri" and he34_ne: "e34_int \<noteq> {}"
  shows "\<not> (e12_int \<subseteq> A \<and> e34_int \<subseteq> A) \<and> \<not> (e12_int \<subseteq> B \<and> e34_int \<subseteq> B)"
proof (intro conjI notI)
  assume h: "e12_int \<subseteq> A \<and> e34_int \<subseteq> A"
  from hRi_comp show False
  proof
    assume "Ri = A"
    hence "e12_int \<subseteq> Ri" using h by (by100 blast)
    hence "e12_int \<inter> Ri \<noteq> {}" using he12_ne by (by100 blast)
    thus False using he12_Ri by (by100 blast)
  next
    assume "Ri = B"
    hence "e34_int \<subseteq> B" using he34_Ri by (by100 blast)
    hence "e34_int \<subseteq> A \<inter> B" using h by (by100 blast)
    hence "e34_int = {}" using hAB_disj by (by100 blast)
    thus False using he34_ne by (by100 blast)
  qed
next
  assume h: "e12_int \<subseteq> B \<and> e34_int \<subseteq> B"
  from hRi_comp show False
  proof
    assume "Ri = B"
    hence "e12_int \<subseteq> Ri" using h by (by100 blast)
    hence "e12_int \<inter> Ri \<noteq> {}" using he12_ne by (by100 blast)
    thus False using he12_Ri by (by100 blast)
  next
    assume "Ri = A"
    hence "e34_int \<subseteq> A" using he34_Ri by (by100 blast)
    hence "e34_int \<subseteq> A \<inter> B" using h by (by100 blast)
    hence "e34_int = {}" using hAB_disj by (by100 blast)
    thus False using he34_ne by (by100 blast)
  qed
qed

lemma element_of_three_subset:
  assumes "x \<in> {A, B, C}" shows "x \<subseteq> A \<union> B \<union> C"
  using assms by (by100 blast)

lemma component_eq_from_subset:
  assumes "C = A \<or> C = B" "C \<subseteq> A" "A \<inter> B = {}" "B \<noteq> {}"
  shows "C = A"
  using assms by (by100 blast)

lemma nonempty_inter_from_subset:
  assumes "S \<noteq> {}" "S \<subseteq> A" shows "S \<inter> A \<noteq> {}"
  using assms by (by100 blast)

lemma false_from_disjoint_nonempty:
  assumes "S \<inter> A = {}" "S \<inter> A \<noteq> {}" shows False
  using assms by (by100 blast)

lemma subset_from_eq_and_subset:
  assumes "C = A" "S \<subseteq> A" shows "S \<subseteq> C"
  using assms by (by100 blast)

lemma subset_of_complement_disjoint:
  assumes "R = X - T" and "S \<subseteq> T"
  shows "S \<inter> R = {}"
  using assms by (by100 blast)

lemma diff_inter_subset:
  assumes "A \<inter> R = {}" shows "(A - S) \<inter> R = {}"
  using assms by (by100 blast)

lemma disjoint_subset_right:
  assumes "A \<inter> B = {}" and "S \<subseteq> B" shows "A \<inter> S = {}"
  using assms by (by100 blast)

lemma third_element_unique:
  assumes "a \<in> {R1, R2, R3}" "b \<in> {R1, R2, R3}" "c \<in> {R1, R2, R3}" "d \<in> {R1, R2, R3}"
      and "R1 \<noteq> R2" "R2 \<noteq> R3" "R1 \<noteq> R3" and "a \<noteq> b"
      and "c \<noteq> a" "c \<noteq> b" "d \<noteq> a" "d \<noteq> b"
  shows "c = d"
proof -
  have "{R1,R2,R3} - {a,b} = {c}" and "{R1,R2,R3} - {a,b} = {d}"
    using assms by auto  \<comment> \<open>finite set computation, no by100 needed for top-level combinatorics\<close>
  thus ?thesis by (by100 simp)
qed

\<comment> \<open>Helper: if W \<subseteq> S2-(J\<union>Arc) = R1\<union>R2\<union>R3 and W is a connected J-component,
   and D' \<subseteq> W, D' = Ri\_D (one of the Ri's), Ri\_D \<subseteq> D', then D' = W.\<close>
lemma J_component_sub_theta_forces_eq:
  assumes "W \<subseteq> R1 \<union> R2 \<union> R3" "W \<noteq> {}"
      and "top1_connected_on W (subspace_topology X TX W)"
      and "D' \<subseteq> W" "D' \<noteq> {}"
      and "D' \<subseteq> Ri_D" "Ri_D \<subseteq> D'" "Ri_D \<in> {R1, R2, R3}"
      and "\<And>S. S \<subseteq> R1\<union>R2\<union>R3 \<Longrightarrow> S \<noteq> {} \<Longrightarrow>
          top1_connected_on S (subspace_topology X TX S) \<Longrightarrow> S \<subseteq> R1 \<or> S \<subseteq> R2 \<or> S \<subseteq> R3"
      and "R1 \<inter> R2 = {}" "R2 \<inter> R3 = {}" "R1 \<inter> R3 = {}"
  shows "D' = W"
proof -
  from assms(9)[OF assms(1,2,3)]
  have "W \<subseteq> R1 \<or> W \<subseteq> R2 \<or> W \<subseteq> R3" .
  then obtain Ri_W where "Ri_W \<in> {R1,R2,R3}" "W \<subseteq> Ri_W" by (by100 blast)
  have "D' \<subseteq> Ri_W" using assms(4) \<open>W \<subseteq> Ri_W\<close> by (by100 blast)
  have "Ri_D = D'" using assms(6,7) by (by100 blast)
  have "Ri_D \<subseteq> Ri_W" using \<open>D' \<subseteq> Ri_W\<close> \<open>Ri_D = D'\<close> by (by100 blast)
  have "Ri_W = Ri_D"
  proof (rule ccontr)
    assume "Ri_W \<noteq> Ri_D"
    hence "Ri_W \<inter> Ri_D = {}" using \<open>Ri_W \<in> _\<close> assms(8,10,11,12) by auto
    hence "Ri_D = {}" using \<open>Ri_D \<subseteq> Ri_W\<close> by (by100 blast)
    hence "D' = {}" using assms(6) by (by100 blast)
    thus False using assms(5) by (by100 blast)
  qed
  hence "W \<subseteq> Ri_D" using \<open>W \<subseteq> Ri_W\<close> by (by100 blast)
  hence "W \<subseteq> D'" using assms(7) by (by100 blast)
  thus "D' = W" using assms(4) by (by100 blast)
qed

(** from \<S>65 Lemma 65.1(a): non-adjacent edges of K_4 in S^2 have interiors in
    different components of S^2 minus the complementary 4-cycle.
    Duplicated from the internal hdiff fact in Lemma_65_1_K4_subgraph (AlgTopCached.thy). **)
lemma K4_nonadjacent_edges_different_components:
  fixes a1 a2 a3 a4 :: "real \<times> real \<times> real"
    and e12 e23 e34 e41 e13 e24 :: "(real \<times> real \<times> real) set"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "card {a1, a2, a3, a4} = 4"
      and "{a1, a2, a3, a4} \<subseteq> top1_S2"
      and "e12 \<subseteq> top1_S2" and "e23 \<subseteq> top1_S2" and "e34 \<subseteq> top1_S2"
      and "e41 \<subseteq> top1_S2" and "e13 \<subseteq> top1_S2" and "e24 \<subseteq> top1_S2"
      and "top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      and "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      and "top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      and "top1_is_arc_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
      and "top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
      and "top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
      and "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1,a2}"
      and "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2,a3}"
      and "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3,a4}"
      and "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4,a1}"
      and "top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1,a3}"
      and "top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2,a4}"
      and "e12 \<inter> e34 = {}" and "e23 \<inter> e41 = {}"
      and "e12 \<inter> e23 = {a2}" and "e23 \<inter> e34 = {a3}"
      and "e34 \<inter> e41 = {a4}" and "e41 \<inter> e12 = {a1}"
      and "e13 \<inter> e12 = {a1}" and "e13 \<inter> e23 = {a3}"
      and "e13 \<inter> e34 = {a3}" and "e13 \<inter> e41 = {a1}"
      and "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      and "e24 \<inter> e12 = {a2}" and "e24 \<inter> e23 = {a2}"
      and "e24 \<inter> e34 = {a4}" and "e24 \<inter> e41 = {a4}"
      \<comment> \<open>D = e13 \<union> e23 \<union> e24 \<union> e41 (the complementary 4-cycle).
         A, B are the two components of S2-D.\<close>
      and "A \<noteq> {}" and "B \<noteq> {}" and "A \<inter> B = {}"
      and "A \<union> B = top1_S2 - (e13 \<union> e23 \<union> e24 \<union> e41)"
      and "top1_connected_on A (subspace_topology top1_S2 top1_S2_topology A)"
      and "top1_connected_on B (subspace_topology top1_S2 top1_S2_topology B)"
  shows "\<not> (e12 - {a1, a2} \<subseteq> A \<and> e34 - {a3, a4} \<subseteq> A)
       \<and> \<not> (e12 - {a1, a2} \<subseteq> B \<and> e34 - {a3, a4} \<subseteq> B)"
proof -
  \<comment> \<open>Following algtop.tex 65.1(a): theta space D\<union>e12 \<Rightarrow> 3 components \<Rightarrow> separation.\<close>
  define D_loc where "D_loc = e13 \<union> e23 \<union> e24 \<union> e41"
  define Arc2 where "Arc2 = e13 \<union> e23"
  define Arc3 where "Arc3 = e24 \<union> e41"
  note defs = Arc2_def Arc3_def D_loc_def
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def unfolding defs by (by100 blast)
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" unfolding defs by (rule top1_S2_is_hausdorff)
  \<comment> \<open>Step 1: Hypotheses for Lemma\_64\_1.\<close>
  have hArc2_sub: "Arc2 \<subseteq> top1_S2" using assms(8,5) unfolding defs by (by100 blast)
  have hArc3_sub: "Arc3 \<subseteq> top1_S2" using assms(9,7) unfolding defs by (by100 blast)
  have ha3_e13: "a3 \<in> top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
    using assms(20) unfolding defs by (by100 blast)
  have ha3_e23: "a3 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
    using assms(17) unfolding defs by (by100 blast)
  have ha4_e24: "a4 \<in> top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
    using assms(21) unfolding defs by (by100 blast)
  have ha4_e41: "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
    using assms(19) unfolding defs by (by100 blast)
  have hArc2_arc: "top1_is_arc_on Arc2 (subspace_topology top1_S2 top1_S2_topology Arc2)"
    unfolding defs by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus assms(14,8,11,5) _ ha3_e13 ha3_e23])
       (use assms(29) in \<open>by100 blast\<close>)
  have hArc3_arc: "top1_is_arc_on Arc3 (subspace_topology top1_S2 top1_S2_topology Arc3)"
    unfolding defs by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus assms(15,9,13,7) _ ha4_e24 ha4_e41])
       (use assms(36) in \<open>by100 blast\<close>)
  have ha1_ne_a2: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha1_ne_a3: "a1 \<noteq> a3" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha1_ne_a4: "a1 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha2_ne_a3: "a2 \<noteq> a3" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha2_ne_a4: "a2 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha3_ne_a4: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have hint12: "e12 \<inter> Arc2 = {a1, a2}"
    using assms(28,24) unfolding defs by (by100 blast)
  have hint13: "e12 \<inter> Arc3 = {a1, a2}"
    using assms(33,27) unfolding defs by (by100 blast)
  have he13_e24_disj: "e13 \<inter> e24 = {}"
  proof -
    have "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}" unfolding defs by (rule assms(32))
    moreover have "a1 \<notin> e24"
    proof assume "a1 \<in> e24"
      hence "a1 \<in> e24 \<inter> e12" using assms(16) unfolding top1_arc_endpoints_on_def unfolding defs by (by100 blast)
      hence "a1 = a2" using assms(33) unfolding defs by (by100 blast)
      thus False using ha1_ne_a2 unfolding defs by (by100 blast) qed
    moreover have "a2 \<notin> e13"
    proof assume "a2 \<in> e13"
      hence "a2 \<in> e13 \<inter> e12" using assms(16) unfolding top1_arc_endpoints_on_def unfolding defs by (by100 blast)
      hence "a2 = a1" using assms(28) unfolding defs by (by100 blast)
      thus False using ha1_ne_a2 unfolding defs by (by100 blast) qed
    moreover have "a3 \<notin> e24"
    proof assume "a3 \<in> e24"
      hence "a3 \<in> e24 \<inter> e23" using assms(17) unfolding top1_arc_endpoints_on_def unfolding defs by (by100 blast)
      hence "a3 = a2" using assms(34) unfolding defs by (by100 blast)
      thus False using ha2_ne_a3 unfolding defs by (by100 blast) qed
    moreover have "a4 \<notin> e13"
    proof assume "a4 \<in> e13"
      hence "a4 \<in> e13 \<inter> e41" using assms(19) unfolding top1_arc_endpoints_on_def unfolding defs by (by100 blast)
      hence "a4 = a1" using assms(31) unfolding defs by (by100 blast)
      thus False using ha1_ne_a4 unfolding defs by (by100 blast) qed
    ultimately show ?thesis unfolding defs by (by100 blast)
  qed
  have hint23: "Arc2 \<inter> Arc3 = {a1, a2}"
    using he13_e24_disj assms(31,34,23) unfolding defs by (by100 blast)
  have hep_e23_swap: "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a3, a2}"
    using assms(17) unfolding defs by (by100 blast)
  have ha3_ne_a2: "a3 \<noteq> a2" using ha2_ne_a3 unfolding defs by (by100 blast)
  have hArc2_ep: "top1_arc_endpoints_on Arc2 (subspace_topology top1_S2 top1_S2_topology Arc2) = {a1, a2}"
    unfolding defs by (rule arc_concat_endpoints[OF assms(1) hS2_haus assms(14,8,11,5) assms(29)
          ha3_e13 ha3_e23 assms(20) hep_e23_swap ha1_ne_a3 ha3_ne_a2])
  have hArc3_ep: "top1_arc_endpoints_on Arc3 (subspace_topology top1_S2 top1_S2_topology Arc3) = {a1, a2}"
  proof -
    \<comment> \<open>arc\_concat\_endpoints gives {a2, a1} — need {a1, a2}.\<close>
    have hep_e41_swap: "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4, a1}"
      using assms(19) unfolding defs by (by100 blast)
    have ha4_ne_a2: "a4 \<noteq> a2" using ha2_ne_a4 unfolding defs by (by100 blast)
    have ha4_ne_a1: "a4 \<noteq> a1" using ha1_ne_a4 unfolding defs by (by100 blast)
    have "top1_arc_endpoints_on Arc3 (subspace_topology top1_S2 top1_S2_topology Arc3) = {a2, a1}"
      unfolding defs by (rule arc_concat_endpoints[OF assms(1) hS2_haus assms(15,9,13,7) assms(36)
            ha4_e24 ha4_e41 assms(21) hep_e41_swap ha2_ne_a4 ha4_ne_a1])
    thus ?thesis by (by100 blast)
  qed
  \<comment> \<open>Step 2: Apply Lemma\_64\_1.\<close>
  obtain R1 R2 R3 where hR: "R1 \<noteq> {}" "R2 \<noteq> {}" "R3 \<noteq> {}"
      "R1 \<inter> R2 = {}" "R2 \<inter> R3 = {}" "R1 \<inter> R3 = {}"
      "R1 \<union> R2 \<union> R3 = top1_S2 - (e12 \<union> Arc2 \<union> Arc3)"
      "top1_connected_on R1 (subspace_topology top1_S2 top1_S2_topology R1)"
      "top1_connected_on R2 (subspace_topology top1_S2 top1_S2_topology R2)"
      "top1_connected_on R3 (subspace_topology top1_S2 top1_S2_topology R3)"
      "R1 \<in> top1_S2_topology" "R2 \<in> top1_S2_topology" "R3 \<in> top1_S2_topology"
    using Lemma_64_1_theta_space_three_components[OF assms(1) assms(4) hArc2_sub hArc3_sub
        assms(10) hArc2_arc hArc3_arc ha1_ne_a2 hint12 hint23 hint13 assms(16) hArc2_ep hArc3_ep]
    by (metis (no_types))
  \<comment> \<open>Step 3: e34-{a3,a4} \<subseteq> S2-theta, hence in some Ri.\<close>
  have he34_theta: "e34 - {a3, a4} \<subseteq> top1_S2 - (e12 \<union> Arc2 \<union> Arc3)"
  proof -
    have h1: "e34 \<inter> e12 = {}" using assms(22) unfolding defs by (by100 blast)
    have h2: "e34 \<inter> e13 \<subseteq> {a3}" using assms(30) unfolding defs by (by100 blast)
    have h3: "e34 \<inter> e23 \<subseteq> {a3}" using assms(25) unfolding defs by (by100 blast)
    have h4: "e34 \<inter> e24 \<subseteq> {a4}" using assms(35) unfolding defs by (by100 blast)
    have h5: "e34 \<inter> e41 \<subseteq> {a4}" using assms(26) unfolding defs by (by100 blast)
    have "e34 \<inter> Arc2 \<subseteq> {a3}" using h2 h3 unfolding defs by (by100 blast)
    moreover have "e34 \<inter> Arc3 \<subseteq> {a4}" using h4 h5 unfolding defs by (by100 blast)
    ultimately have "e34 \<inter> (e12 \<union> Arc2 \<union> Arc3) \<subseteq> {a3, a4}" using h1 unfolding defs by (by100 blast)
    thus ?thesis using assms(6) unfolding defs by (by100 blast)
  qed
  have he34_ne: "e34 - {a3, a4} \<noteq> {}"
  proof -
    obtain h where hh: "top1_homeomorphism_on I_set I_top e34
        (subspace_topology top1_S2 top1_S2_topology e34) h"
      using assms(12) unfolding top1_is_arc_on_def unfolding defs by (by100 blast)
    have hbij: "bij_betw h I_set e34" using hh unfolding top1_homeomorphism_on_def unfolding defs by (by100 blast)
    have h0: "(0::real) \<in> I_set" unfolding top1_unit_interval_def unfolding defs by (by100 simp)
    have h1: "(1::real) \<in> I_set" unfolding top1_unit_interval_def unfolding defs by (by100 simp)
    have h12: "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def unfolding defs by (by100 simp)
    have "h (1/2) \<in> e34" using hbij h12 unfolding bij_betw_def unfolding defs by (by100 blast)
    moreover have "h (1/2) \<noteq> h 0 \<and> h (1/2) \<noteq> h 1"
    proof -
      have hinj: "inj_on h I_set" using hbij unfolding bij_betw_def unfolding defs by (by100 blast)
      have "h (1/2) \<noteq> h 0"
      proof assume "h (1/2) = h 0"
        from inj_onD[OF hinj this h12 h0] show False unfolding defs by (by100 simp) qed
      moreover have "h (1/2) \<noteq> h 1"
      proof assume "h (1/2) = h 1"
        from inj_onD[OF hinj this h12 h1] show False unfolding defs by (by100 simp) qed
      ultimately show ?thesis unfolding defs by (by100 blast)
    qed
    moreover have "{h 0, h 1} = {a3, a4}"
      using arc_endpoints_are_boundary[OF assms(1) hS2_haus assms(6,12) hh] assms(18)
      unfolding defs by (by100 simp)
    ultimately show ?thesis unfolding defs by (by100 blast)
  qed
  have he34_conn: "top1_connected_on (e34 - {a3, a4})
      (subspace_topology top1_S2 top1_S2_topology (e34 - {a3, a4}))"
    unfolding defs by (rule arc_minus_endpoints_connected[OF assms(1) hS2_haus assms(6,12,18) ha3_ne_a4])
  have hAB_sub_S2: "A \<union> B \<subseteq> top1_S2" using assms(40) unfolding defs by (by100 blast)
  have hD_is_Arc: "D_loc = Arc2 \<union> Arc3" unfolding defs by (by100 blast)
  have hD_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology D_loc"
    unfolding hD_is_Arc by (rule arcs_form_simple_closed_curve[OF assms(1) hS2_haus
        hArc2_arc hArc2_sub hArc3_arc hArc3_sub hint23 ha1_ne_a2 hArc2_ep hArc3_ep])
  have hD_closed: "closedin_on top1_S2 top1_S2_topology D_loc"
  proof -
    have "closedin_on top1_S2 top1_S2_topology e13" unfolding defs
      by (rule arc_in_S2_closed[OF assms(8,14)])
    moreover have "closedin_on top1_S2 top1_S2_topology e23" unfolding defs
      by (rule arc_in_S2_closed[OF assms(5,11)])
    moreover have "closedin_on top1_S2 top1_S2_topology e24" unfolding defs
      by (rule arc_in_S2_closed[OF assms(9,15)])
    moreover have "closedin_on top1_S2 top1_S2_topology e41" unfolding defs
      by (rule arc_in_S2_closed[OF assms(7,13)])
    ultimately have "closedin_on top1_S2 top1_S2_topology (e13 \<union> e23 \<union> e24 \<union> e41)"
      by (intro closedin_on_Un[OF hTopS2]) (by100 blast)+
    thus ?thesis unfolding defs by (by100 simp)
  qed
  have hW_open: "top1_S2 - D_loc \<in> top1_S2_topology"
    using hD_closed unfolding closedin_on_def by (by100 blast)
  have hW_not_conn: "\<not> top1_connected_on (top1_S2 - D_loc)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - D_loc))"
  proof -
    have "top1_separates_on top1_S2 top1_S2_topology D_loc"
      by (rule Theorem_61_3_JordanSeparation_S2[OF assms(1) hD_scc])
    thus ?thesis unfolding top1_separates_on_def unfolding defs by (by100 simp)
  qed
  have hAB_W: "A \<union> B = top1_S2 - D_loc" using assms(40) unfolding defs by (by100 simp)
  have hW_sub_S2: "top1_S2 - D_loc \<subseteq> top1_S2" by (by100 blast)
  have hA_open_S2: "A \<in> top1_S2_topology" and hB_open_S2: "B \<in> top1_S2_topology"
    using S2_two_component_open[OF hW_open hW_sub_S2 assms(37,38,39) hAB_W assms(41,42) hW_not_conn]
    by (by100 blast)+
  hence hA_open_S2: "A \<in> top1_S2_topology" and hB_open_S2: "B \<in> top1_S2_topology"
    by (by100 blast)+
  have hTAB_loc: "is_topology_on (A \<union> B) (subspace_topology top1_S2 top1_S2_topology (A \<union> B))"
    unfolding defs by (rule subspace_topology_is_topology_on[OF hTopS2]) (use hAB_sub_S2 in \<open>by100 blast\<close>)
  have hA_open_AB: "A \<in> subspace_topology top1_S2 top1_S2_topology (A \<union> B)"
    using hA_open_S2 unfolding subspace_topology_def by (by100 blast)
  have hB_open_AB: "B \<in> subspace_topology top1_S2 top1_S2_topology (A \<union> B)"
    using hB_open_S2 unfolding subspace_topology_def by (by100 blast)
  have hAB_sep: "top1_is_separation_on (A \<union> B) (subspace_topology top1_S2 top1_S2_topology (A \<union> B)) A B"
    unfolding top1_is_separation_on_def
    using hA_open_AB hB_open_AB assms(37,38,39) by (by100 blast)
  \<comment> \<open>e34-{a3,a4} connected \<subseteq> R1\<union>R2\<union>R3 \<Rightarrow> in some Ri.\<close>
  have he34_in_Ri: "e34 - {a3, a4} \<subseteq> R1 \<or> e34 - {a3, a4} \<subseteq> R2 \<or> e34 - {a3, a4} \<subseteq> R3"
  proof -
    let ?W = "R1 \<union> R2 \<union> R3"
    have hTW: "is_topology_on ?W (subspace_topology top1_S2 top1_S2_topology ?W)"
      unfolding defs by (rule subspace_topology_is_topology_on[OF hTopS2]) (use hR(7) in \<open>by100 blast\<close>)
    have hR1_open: "R1 \<in> subspace_topology top1_S2 top1_S2_topology ?W"
      using hR(11) unfolding subspace_topology_def unfolding defs by (by100 blast)
    have hR23_open: "R2 \<union> R3 \<in> subspace_topology top1_S2 top1_S2_topology ?W"
    proof -
      have "R2 \<union> R3 \<in> top1_S2_topology"
      proof -
        have "{R2, R3} \<subseteq> top1_S2_topology" using hR(12,13) unfolding defs by (by100 blast)
        hence "\<Union>{R2, R3} \<in> top1_S2_topology"
          using hTopS2 unfolding is_topology_on_def unfolding defs by (by100 blast)
        moreover have "\<Union>{R2, R3} = R2 \<union> R3" unfolding defs by (by100 blast)
        ultimately show ?thesis unfolding defs by (by100 simp)
      qed
      thus ?thesis unfolding subspace_topology_def unfolding defs by (by100 blast)
    qed
    have hSep1: "top1_is_separation_on ?W (subspace_topology top1_S2 top1_S2_topology ?W) R1 (R2 \<union> R3)"
      unfolding top1_is_separation_on_def
      using hR1_open hR23_open hR(1,2,3,4,5,6) unfolding defs by (by100 blast)
    have he34_sub_W: "e34 - {a3, a4} \<subseteq> ?W" using he34_theta hR(7) unfolding defs by (by100 blast)
    have he34_conn_W: "top1_connected_on (e34 - {a3, a4})
        (subspace_topology ?W (subspace_topology top1_S2 top1_S2_topology ?W) (e34 - {a3, a4}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology (e34 - {a3, a4}) =
          subspace_topology ?W (subspace_topology top1_S2 top1_S2_topology ?W) (e34 - {a3, a4})"
        using subspace_topology_trans[of "e34 - {a3, a4}" ?W] he34_sub_W unfolding defs by (by100 simp)
      thus ?thesis using he34_conn unfolding defs by (by100 simp)
    qed
    have hLem1: "(e34 - {a3, a4}) \<inter> (R2 \<union> R3) = {} \<or> (e34 - {a3, a4}) \<inter> R1 = {}"
      unfolding defs by (rule Lemma_23_2_disjoint[OF hTW hSep1 he34_sub_W he34_conn_W])
    hence hLem1_result: "e34 - {a3, a4} \<subseteq> R1 \<or> e34 - {a3, a4} \<subseteq> R2 \<union> R3"
    proof
      assume "(e34 - {a3, a4}) \<inter> (R2 \<union> R3) = {}"
      hence "e34 - {a3, a4} \<subseteq> R1" using he34_sub_W unfolding defs by (by100 blast)
      thus ?thesis unfolding defs by (by100 blast)
    next
      assume "(e34 - {a3, a4}) \<inter> R1 = {}"
      hence "e34 - {a3, a4} \<subseteq> R2 \<union> R3" using he34_sub_W unfolding defs by (by100 blast)
      thus ?thesis unfolding defs by (by100 blast)
    qed
    show ?thesis
    proof (cases "e34 - {a3, a4} \<subseteq> R1")
      case True thus ?thesis unfolding defs by (by100 blast)
    next
      case False
      hence "e34 - {a3, a4} \<subseteq> R2 \<union> R3" using hLem1_result unfolding defs by (by100 blast)
      hence he34_R23: "e34 - {a3, a4} \<subseteq> R2 \<union> R3" .
      have hR2_open: "R2 \<in> subspace_topology top1_S2 top1_S2_topology (R2 \<union> R3)"
        using hR(12) unfolding subspace_topology_def unfolding defs by (by100 blast)
      have hR3_open: "R3 \<in> subspace_topology top1_S2 top1_S2_topology (R2 \<union> R3)"
        using hR(13) unfolding subspace_topology_def unfolding defs by (by100 blast)
      have hTR23: "is_topology_on (R2 \<union> R3) (subspace_topology top1_S2 top1_S2_topology (R2 \<union> R3))"
        unfolding defs by (rule subspace_topology_is_topology_on[OF hTopS2]) (use hR(7) in \<open>by100 blast\<close>)
      have hSep23: "top1_is_separation_on (R2 \<union> R3) (subspace_topology top1_S2 top1_S2_topology (R2 \<union> R3)) R2 R3"
        unfolding top1_is_separation_on_def
        using hR2_open hR3_open hR(2,3,5) unfolding defs by (by100 blast)
      have he34_conn_R23: "top1_connected_on (e34 - {a3, a4})
          (subspace_topology (R2 \<union> R3) (subspace_topology top1_S2 top1_S2_topology (R2 \<union> R3)) (e34 - {a3, a4}))"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology (e34 - {a3, a4}) =
            subspace_topology (R2 \<union> R3) (subspace_topology top1_S2 top1_S2_topology (R2 \<union> R3)) (e34 - {a3, a4})"
          using subspace_topology_trans[of "e34 - {a3, a4}" "R2 \<union> R3"]
            \<open>e34 - {a3, a4} \<subseteq> R2 \<union> R3\<close> unfolding defs by (by100 simp)
        thus ?thesis using he34_conn unfolding defs by (by100 simp)
      qed
      have hLem2: "(e34 - {a3, a4}) \<inter> R3 = {} \<or> (e34 - {a3, a4}) \<inter> R2 = {}"
        unfolding defs by (rule Lemma_23_2_disjoint[OF hTR23 hSep23 \<open>e34 - {a3, a4} \<subseteq> R2 \<union> R3\<close> he34_conn_R23])
      hence "e34 - {a3, a4} \<subseteq> R2 \<or> e34 - {a3, a4} \<subseteq> R3"
      proof
        assume "(e34 - {a3, a4}) \<inter> R3 = {}"
        thus ?thesis using he34_R23 unfolding defs by (by100 blast)
      next
        assume "(e34 - {a3, a4}) \<inter> R2 = {}"
        thus ?thesis using he34_R23 unfolding defs by (by100 blast)
      qed
      thus ?thesis unfolding defs by (by100 blast)
    qed
  qed
  obtain Ri_e where hRie: "Ri_e \<in> {R1, R2, R3}" "e34 - {a3, a4} \<subseteq> Ri_e"
  proof -
    from he34_in_Ri show ?thesis
    proof (elim disjE)
      assume h: "e34 - {a3, a4} \<subseteq> R1"
      show ?thesis by (rule that[of R1]) (use h in \<open>by100 blast\<close>)+
    next
      assume h: "e34 - {a3, a4} \<subseteq> R2"
      show ?thesis by (rule that[of R2]) (use h in \<open>by100 blast\<close>)+
    next
      assume h: "e34 - {a3, a4} \<subseteq> R3"
      show ?thesis by (rule that[of R3]) (use h in \<open>by100 blast\<close>)+
    qed
  qed
  \<comment> \<open>Step 4: e12-{a1,a2} is on the theta space, hence NOT in any Ri.\<close>
  have he12_on_theta: "e12 - {a1, a2} \<subseteq> e12 \<union> Arc2 \<union> Arc3" unfolding defs by (by100 blast)
  have he12_sub_theta: "e12 \<subseteq> e12 \<union> Arc2 \<union> Arc3" by (by100 blast)
  have he12_R_disj: "e12 \<inter> (R1 \<union> R2 \<union> R3) = {}"
    by (rule subset_of_complement_disjoint[OF hR(7) he12_sub_theta])
  have he12_not_Ri: "(e12 - {a1, a2}) \<inter> (R1 \<union> R2 \<union> R3) = {}"
  proof -
    have "e12 - {a1, a2} \<subseteq> e12" by (by100 blast)
    hence "(e12 - {a1, a2}) \<inter> (R1 \<union> R2 \<union> R3) \<subseteq> e12 \<inter> (R1 \<union> R2 \<union> R3)"
      by (rule Int_mono) (rule subset_refl)
    also have "\<dots> = {}" by (rule he12_R_disj)
    finally have "(e12 - {a1, a2}) \<inter> (R1 \<union> R2 \<union> R3) \<subseteq> {}" .
    thus ?thesis by (rule subset_antisym) (rule empty_subsetI)
  qed
  \<comment> \<open>Step 5: Each Ri \<subseteq> A\<union>B (since Ri \<subseteq> S2-theta \<subseteq> S2-D = A\<union>B).
     The Ri containing e34 \<subseteq> A or B. e12 NOT in that Ri.
     e12-{a1,a2} \<subseteq> A\<union>B (from hint\_e12\_sub in Lemma\_65\_1 proof).
     If e34 Ri \<subseteq> A, then e12 must avoid A? No — e12 could still be in A via another Ri.
     The KEY: e12 is not in ANY Ri, so e12 is NOT in S2-theta.
     But e12-{a1,a2} IS in A\<union>B = S2-D. And S2-D = (S2-theta) \<union> (e12-{a1,a2}).
     So if e34 \<subseteq> Ri \<subseteq> A, then e12-{a1,a2} \<subseteq> S2-D - Ri.
     Since Ri is a component of S2-theta, and S2-D = (R1\<union>R2\<union>R3) \<union> (e12-{a1,a2}),
     the other components + e12 form the rest. A = Ri, B = rest (or swap).
     Hence e12 in B and e34 in A: different.\<close>
  \<comment> \<open>S2-D = (R1\<union>R2\<union>R3) \<union> (e12-{a1,a2}).\<close>
  have hAB_decomp: "A \<union> B = (R1 \<union> R2 \<union> R3) \<union> (e12 - {a1, a2})"
  proof -
    have hD_eq_theta: "D_loc = Arc2 \<union> Arc3" unfolding defs by (by100 blast)
    have htheta_eq: "e12 \<union> Arc2 \<union> Arc3 = D_loc \<union> e12" unfolding defs by (by100 blast)
    have hAB_is: "A \<union> B = top1_S2 - D_loc" using assms(40) unfolding defs by (by100 simp)
    have "top1_S2 - D_loc = (top1_S2 - (D_loc \<union> e12)) \<union> (e12 - D_loc)"
      unfolding defs using assms(4) by (by100 blast)
    also have "top1_S2 - (D_loc \<union> e12) = top1_S2 - (e12 \<union> Arc2 \<union> Arc3)"
      using htheta_eq by (by100 simp)
    also have "\<dots> = R1 \<union> R2 \<union> R3" using hR(7) by (by100 simp)
    finally have "top1_S2 - D_loc = (R1 \<union> R2 \<union> R3) \<union> (e12 - D_loc)" .
    moreover have "e12 - D_loc = e12 - {a1, a2}"
    proof -
      have "e12 \<inter> D_loc = {a1, a2}"
      proof -
        have "e12 \<inter> e13 = {a1}" using assms(28) by (by100 blast)
        moreover have "e12 \<inter> e23 = {a2}" using assms(24) by (by100 blast)
        moreover have "e12 \<inter> e24 = {a2}" using assms(33) by (by100 blast)
        moreover have "e12 \<inter> e41 = {a1}" using assms(27) by (by100 blast)
        ultimately show ?thesis unfolding defs by (by100 blast)
      qed
      thus ?thesis using assms(4) unfolding defs by (by100 blast)
    qed
    ultimately show ?thesis using hAB_is by (by100 simp)
  qed
  \<comment> \<open>Each Ri \<subseteq> A or B.\<close>
  have hRi_sub_AB: "R1 \<union> R2 \<union> R3 \<subseteq> A \<union> B" using hAB_decomp by (by100 blast)
  have hRi_in_AB: "\<And>Ri. Ri \<in> {R1, R2, R3} \<Longrightarrow> Ri \<subseteq> A \<or> Ri \<subseteq> B"
  proof -
    fix Ri assume hRi: "Ri \<in> {R1, R2, R3}"
    have hRi_sub: "Ri \<subseteq> A \<union> B" using hRi hRi_sub_AB by (by100 blast)
    have hRi_conn: "top1_connected_on Ri (subspace_topology top1_S2 top1_S2_topology Ri)"
      using hRi hR(8,9,10) by (by100 blast)
    have hRi_conn_AB: "top1_connected_on Ri
        (subspace_topology (A \<union> B) (subspace_topology top1_S2 top1_S2_topology (A \<union> B)) Ri)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology Ri =
          subspace_topology (A \<union> B) (subspace_topology top1_S2 top1_S2_topology (A \<union> B)) Ri"
        using subspace_topology_trans[of Ri "A \<union> B" top1_S2 top1_S2_topology]
            hRi_sub by (by100 simp)
      thus ?thesis using hRi_conn by (by100 simp)
    qed
    have "Ri \<inter> B = {} \<or> Ri \<inter> A = {}"
      by (rule Lemma_23_2_disjoint[OF hTAB_loc hAB_sep hRi_sub hRi_conn_AB])
    thus "Ri \<subseteq> A \<or> Ri \<subseteq> B"
    proof
      assume "Ri \<inter> B = {}" thus ?thesis using hRi_sub by (by100 blast)
    next
      assume "Ri \<inter> A = {}" thus ?thesis using hRi_sub by (by100 blast)
    qed
  qed
  have he12_ne: "e12 - {a1, a2} \<noteq> {}"
  proof -
    obtain h where hh: "top1_homeomorphism_on I_set I_top e12
        (subspace_topology top1_S2 top1_S2_topology e12) h"
      using assms(10) unfolding top1_is_arc_on_def by (by100 blast)
    have hbij: "bij_betw h I_set e12" using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have h12: "(1/2::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "h (1/2) \<in> e12" using hbij h12 unfolding bij_betw_def by (by100 blast)
    moreover have "h (1/2) \<noteq> h 0 \<and> h (1/2) \<noteq> h 1"
    proof -
      have hinj: "inj_on h I_set" using hbij unfolding bij_betw_def by (by100 blast)
      have h0: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      have h1: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      have "h (1/2) \<noteq> h 0"
      proof assume "h (1/2) = h 0"
        from inj_onD[OF hinj this h12 h0] show False by (by100 simp) qed
      moreover have "h (1/2) \<noteq> h 1"
      proof assume "h (1/2) = h 1"
        from inj_onD[OF hinj this h12 h1] show False by (by100 simp) qed
      ultimately show ?thesis by (by100 blast)
    qed
    moreover have "{h 0, h 1} = {a1, a2}"
      using arc_endpoints_are_boundary[OF assms(1) hS2_haus assms(4,10) hh] assms(16)
      by (by100 simp)
    ultimately show ?thesis by (by100 blast)
  qed
  have he12_not_Rie: "(e12 - {a1, a2}) \<inter> Ri_e = {}"
  proof -
    have hRie_sub: "Ri_e \<subseteq> R1 \<union> R2 \<union> R3" by (rule element_of_three_subset[OF hRie(1)])
    have "e12 \<inter> Ri_e = {}" by (rule disjoint_subset_right[OF he12_R_disj hRie_sub])
    thus ?thesis by (rule diff_inter_subset)
  qed
  \<comment> \<open>Direct proof by contradiction following Munkres 65.1(a).
     Assume both e12 and e34 interiors in same component C.
     Then D' (other component) \<subseteq> R1\<union>R2\<union>R3, D' = some Ri\_D.
     J12 = e12\<union>Arc2 is SCC. One J12-component Q12 = some Ri \<in> {Ri\_D, Rk}.
     If Q12 = Ri\_D: closure(Ri\_D) = Ri\_D\<union>J12 (SCCBMC) and \<subseteq> Ri\_D\<union>D\_loc (SCC-component).
     So J12 \<subseteq> D\_loc, hence e12 \<subseteq> D\_loc, but e12\<inter>D\_loc = {a1,a2}. Contradiction.
     Similarly for J13. If neither Ri\_D is Q: J12 = J13, Arc2 = Arc3, contradiction.\<close>
  \<comment> \<open>Connected subset of R1\<union>R2\<union>R3 \<Rightarrow> in one Ri (2\<times>Lemma\_23\_2).\<close>
  have hR_in_one: "\<And>S. S \<subseteq> R1 \<union> R2 \<union> R3 \<Longrightarrow> S \<noteq> {} \<Longrightarrow>
      top1_connected_on S (subspace_topology top1_S2 top1_S2_topology S) \<Longrightarrow>
      S \<subseteq> R1 \<or> S \<subseteq> R2 \<or> S \<subseteq> R3"
  proof -
    fix S assume hS_sub: "S \<subseteq> R1 \<union> R2 \<union> R3" and hS_ne: "S \<noteq> {}"
        and hS_conn: "top1_connected_on S (subspace_topology top1_S2 top1_S2_topology S)"
    let ?T\<theta> = "subspace_topology top1_S2 top1_S2_topology (R1 \<union> R2 \<union> R3)"
    have hT\<theta>: "is_topology_on (R1 \<union> R2 \<union> R3) ?T\<theta>"
      by (rule subspace_topology_is_topology_on[OF hTopS2]) (use hR(7) in \<open>by100 blast\<close>)
    have hR1_open: "R1 \<in> ?T\<theta>"
      using hR(11) unfolding subspace_topology_def by (by100 blast)
    have hR23_open: "R2 \<union> R3 \<in> ?T\<theta>"
    proof -
      have "{R2, R3} \<subseteq> top1_S2_topology" using hR(12,13) by (by100 blast)
      hence "\<Union>{R2, R3} \<in> top1_S2_topology"
        using hTopS2 unfolding is_topology_on_def by (by100 blast)
      hence "R2 \<union> R3 \<in> top1_S2_topology" by (by100 simp)
      thus ?thesis unfolding subspace_topology_def by (by100 blast)
    qed
    have hSep1: "top1_is_separation_on (R1 \<union> R2 \<union> R3) ?T\<theta> R1 (R2 \<union> R3)"
      unfolding top1_is_separation_on_def
      using hR1_open hR23_open hR(1,2,3,4,5,6) by (by100 blast)
    have hS_conn_\<theta>: "top1_connected_on S (subspace_topology (R1 \<union> R2 \<union> R3) ?T\<theta> S)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology S =
          subspace_topology (R1 \<union> R2 \<union> R3) ?T\<theta> S"
        using subspace_topology_trans[of S "R1 \<union> R2 \<union> R3" top1_S2 top1_S2_topology]
            hS_sub by (by100 simp)
      thus ?thesis using hS_conn by (by100 simp)
    qed
    from Lemma_23_2[OF hT\<theta> hSep1 hS_sub hS_conn_\<theta>]
    have "S \<subseteq> R1 \<or> S \<subseteq> R2 \<union> R3" by (by100 blast)
    moreover {
      assume "S \<subseteq> R2 \<union> R3"
      let ?T23 = "subspace_topology top1_S2 top1_S2_topology (R2 \<union> R3)"
      have hT23: "is_topology_on (R2 \<union> R3) ?T23"
        by (rule subspace_topology_is_topology_on[OF hTopS2])
           (use hR(7) in \<open>by100 blast\<close>)
      have "R2 \<in> ?T23"
        using hR(12) unfolding subspace_topology_def by (by100 blast)
      moreover have "R3 \<in> ?T23"
        using hR(13) unfolding subspace_topology_def by (by100 blast)
      ultimately have hSep2: "top1_is_separation_on (R2 \<union> R3) ?T23 R2 R3"
        unfolding top1_is_separation_on_def using hR(2,3,5) by (by100 blast)
      have hS_conn_23: "top1_connected_on S (subspace_topology (R2 \<union> R3) ?T23 S)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology S =
            subspace_topology (R2 \<union> R3) ?T23 S"
          using subspace_topology_trans[of S "R2 \<union> R3" top1_S2 top1_S2_topology]
              \<open>S \<subseteq> R2 \<union> R3\<close> by (by100 simp)
        thus ?thesis using hS_conn by (by100 simp)
      qed
      from Lemma_23_2[OF hT23 hSep2 \<open>S \<subseteq> R2 \<union> R3\<close> hS_conn_23]
      have "S \<subseteq> R2 \<or> S \<subseteq> R3" by (by100 blast)
    }
    ultimately show "S \<subseteq> R1 \<or> S \<subseteq> R2 \<or> S \<subseteq> R3" by (by100 blast)
  qed
  \<comment> \<open>J12 = e12\<union>Arc2, J13 = e12\<union>Arc3 are SCC.\<close>
  have hJ12_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (e12 \<union> Arc2)"
    by (rule arcs_form_simple_closed_curve[OF assms(1) hS2_haus
        assms(10) assms(4) hArc2_arc hArc2_sub hint12 ha1_ne_a2 assms(16) hArc2_ep])
  have hJ13_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (e12 \<union> Arc3)"
    by (rule arcs_form_simple_closed_curve[OF assms(1) hS2_haus
        assms(10) assms(4) hArc3_arc hArc3_sub hint13 ha1_ne_a2 assms(16) hArc3_ep])
  \<comment> \<open>Key vertex exclusions.\<close>
  have ha4_not_e12: "a4 \<notin> e12"
  proof assume "a4 \<in> e12"
    hence "a4 \<in> e34 \<inter> e12" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "a4 \<in> {}" using assms(22) by (by100 blast)
    thus False by (by100 blast) qed
  have ha4_not_Arc2: "a4 \<notin> Arc2"
  proof assume "a4 \<in> Arc2"
    hence "a4 \<in> e13 \<or> a4 \<in> e23" unfolding defs by (by100 blast)
    thus False
    proof
      assume "a4 \<in> e13"
      hence "a4 \<in> e13 \<inter> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
      hence "a4 = a1" using assms(31) by (by100 blast)
      thus False using ha1_ne_a4 by (by100 blast)
    next
      assume "a4 \<in> e23"
      hence "a4 \<in> e23 \<inter> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
      hence "a4 \<in> {}" using assms(23) by (by100 blast)
      thus False by (by100 blast)
    qed
  qed
  have ha3_not_e12: "a3 \<notin> e12"
  proof assume "a3 \<in> e12"
    hence "a3 \<in> e34 \<inter> e12" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "a3 \<in> {}" using assms(22) by (by100 blast)
    thus False by (by100 blast) qed
  have ha3_not_Arc3: "a3 \<notin> Arc3"
  proof assume "a3 \<in> Arc3"
    hence "a3 \<in> e24 \<or> a3 \<in> e41" unfolding defs by (by100 blast)
    thus False
    proof
      assume "a3 \<in> e24"
      hence "a3 \<in> e24 \<inter> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
      hence "a3 = a2" using assms(34) by (by100 blast)
      thus False using ha2_ne_a3 by (by100 blast)
    next
      assume "a3 \<in> e41"
      hence "a3 \<in> e23 \<inter> e41" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
      hence "a3 \<in> {}" using assms(23) by (by100 blast)
      thus False by (by100 blast)
    qed
  qed
  \<comment> \<open>Main: both-in-same-component \<Rightarrow> False. Single proof covers A and B by symmetry.\<close>
  have h_both_cases: "\<And>C D'. \<lbrakk>C \<noteq> {}; D' \<noteq> {}; C \<inter> D' = {}; C \<union> D' = A \<union> B;
      top1_connected_on C (subspace_topology top1_S2 top1_S2_topology C);
      top1_connected_on D' (subspace_topology top1_S2 top1_S2_topology D');
      C \<in> top1_S2_topology; D' \<in> top1_S2_topology;
      e12 - {a1, a2} \<subseteq> C; e34 - {a3, a4} \<subseteq> C\<rbrakk> \<Longrightarrow> False"
  proof -
    fix C D' assume hC_ne: "C \<noteq> {}" and hD'_ne: "D' \<noteq> {}" and hCD'_disj: "C \<inter> D' = {}"
        and hCD'_union: "C \<union> D' = A \<union> B"
        and hC_conn: "top1_connected_on C (subspace_topology top1_S2 top1_S2_topology C)"
        and hD'_conn: "top1_connected_on D' (subspace_topology top1_S2 top1_S2_topology D')"
        and hC_open: "C \<in> top1_S2_topology" and hD'_open: "D' \<in> top1_S2_topology"
        and he12C: "e12 - {a1, a2} \<subseteq> C" and he34C: "e34 - {a3, a4} \<subseteq> C"
    \<comment> \<open>Step 1: D' \<subseteq> R1\<union>R2\<union>R3.\<close>
    have hD'_sub_R: "D' \<subseteq> R1 \<union> R2 \<union> R3"
    proof -
      have "D' \<inter> (e12 - {a1, a2}) = {}" using hCD'_disj he12C by (by100 blast)
      thus ?thesis using hCD'_union hAB_decomp by (by100 blast)
    qed
    \<comment> \<open>Step 2: D' connected \<Rightarrow> D' \<subseteq> some Ri \<Rightarrow> D' = Ri\_D.\<close>
    from hR_in_one[OF hD'_sub_R hD'_ne hD'_conn]
    obtain Ri_D where hRiD: "Ri_D \<in> {R1, R2, R3}" and hD'_sub_RiD: "D' \<subseteq> Ri_D"
      by (by100 blast)
    have hRiD_sub_D': "Ri_D \<subseteq> D'"
    proof -
      have "Ri_D \<subseteq> R1 \<union> R2 \<union> R3" by (rule element_of_three_subset[OF hRiD])
      hence "Ri_D \<subseteq> A \<union> B" using hRi_sub_AB by (by100 blast)
      hence hRiD_sub_CD': "Ri_D \<subseteq> C \<union> D'" using hCD'_union by (by100 blast)
      have hRiD_conn: "top1_connected_on Ri_D (subspace_topology top1_S2 top1_S2_topology Ri_D)"
        using hRiD hR(8,9,10) by (by100 blast)
      \<comment> \<open>Ri\_D connected in C\<union>D' (open separation): Ri\_D \<subseteq> C or D'.\<close>
      have hTCD': "is_topology_on (C \<union> D') (subspace_topology top1_S2 top1_S2_topology (C \<union> D'))"
        by (rule subspace_topology_is_topology_on[OF hTopS2])
           (use hCD'_union hAB_sub_S2 in \<open>by100 blast\<close>)
      have hC_open_CD': "C \<in> subspace_topology top1_S2 top1_S2_topology (C \<union> D')"
        using hC_open unfolding subspace_topology_def by (by100 blast)
      have hD'_open_CD': "D' \<in> subspace_topology top1_S2 top1_S2_topology (C \<union> D')"
        using hD'_open unfolding subspace_topology_def by (by100 blast)
      have hSep_CD': "top1_is_separation_on (C \<union> D') (subspace_topology top1_S2 top1_S2_topology (C \<union> D')) C D'"
        unfolding top1_is_separation_on_def
        using hC_open_CD' hD'_open_CD' hC_ne hD'_ne hCD'_disj by (by100 blast)
      have hRiD_conn_CD': "top1_connected_on Ri_D
          (subspace_topology (C \<union> D') (subspace_topology top1_S2 top1_S2_topology (C \<union> D')) Ri_D)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology Ri_D =
            subspace_topology (C \<union> D') (subspace_topology top1_S2 top1_S2_topology (C \<union> D')) Ri_D"
          using subspace_topology_trans[of Ri_D "C \<union> D'" top1_S2 top1_S2_topology]
              hRiD_sub_CD' by (by100 simp)
        thus ?thesis using hRiD_conn by (by100 simp)
      qed
      from Lemma_23_2[OF hTCD' hSep_CD' hRiD_sub_CD' hRiD_conn_CD']
      have "Ri_D \<subseteq> C \<or> Ri_D \<subseteq> D'" by (by100 blast)
      moreover have "\<not> (Ri_D \<subseteq> C)"
      proof assume "Ri_D \<subseteq> C"
        hence "D' \<subseteq> C" using hD'_sub_RiD by (by100 blast)
        thus False using hCD'_disj hD'_ne by (by100 blast) qed
      ultimately show ?thesis by (by100 blast)
    qed
    have hD'_eq: "D' = Ri_D" using hD'_sub_RiD hRiD_sub_D' by (by100 blast)
    \<comment> \<open>Step 3: closure(D') \<subseteq> D' \<union> D\_loc.\<close>
    have hD'_sub_S2: "D' \<subseteq> top1_S2" using hCD'_union hAB_sub_S2 by (by100 blast)
    have hcl_D'_sub: "closure_on top1_S2 top1_S2_topology D' \<subseteq> D' \<union> D_loc"
    proof -
      have "closure_on top1_S2 top1_S2_topology D' \<inter> C = {}"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        hence "intersects (closure_on top1_S2 top1_S2_topology D') C"
          unfolding intersects_def by (by100 blast)
        from top1_intersects_closure_on_open_imp_intersects[OF hTopS2 hD'_sub_S2 hC_open this]
        show False using hCD'_disj unfolding intersects_def by (by100 blast)
      qed
      moreover have "closure_on top1_S2 top1_S2_topology D' \<subseteq> top1_S2"
        by (rule closure_on_subset_carrier[OF hTopS2 hD'_sub_S2])
      ultimately show ?thesis
      proof -
        assume h1: "closure_on top1_S2 top1_S2_topology D' \<inter> C = {}"
            and h2: "closure_on top1_S2 top1_S2_topology D' \<subseteq> top1_S2"
        have "A \<union> B = top1_S2 - D_loc" using assms(40) unfolding defs by (by100 simp)
        hence "top1_S2 \<subseteq> C \<union> D' \<union> D_loc" using hCD'_union by (by100 blast)
        thus ?thesis using h1 h2 by (by100 blast)
      qed
    qed
    \<comment> \<open>Step 4: Ri\_D \<inter> theta = {} (Ri\_D \<subseteq> S2-theta).\<close>
    have hRiD_sub_theta_compl: "Ri_D \<subseteq> top1_S2 - (e12 \<union> Arc2 \<union> Arc3)"
    proof -
      have "Ri_D \<subseteq> R1 \<union> R2 \<union> R3" by (rule element_of_three_subset[OF hRiD])
      thus ?thesis using hR(7) by (by100 blast)
    qed
    \<comment> \<open>Step 5: e12 \<inter> D\_loc = {a1,a2} and e12 has interior points.\<close>
    have he12_D_loc_int: "e12 \<inter> D_loc = {a1, a2}"
    proof -
      have "e12 \<inter> e13 = {a1}" using assms(28) by (by100 blast)
      moreover have "e12 \<inter> e23 = {a2}" using assms(24) by (by100 blast)
      moreover have "e12 \<inter> e24 = {a2}" using assms(33) by (by100 blast)
      moreover have "e12 \<inter> e41 = {a1}" using assms(27) by (by100 blast)
      ultimately show ?thesis unfolding defs by (by100 blast)
    qed
    \<comment> \<open>Step 6: SCCBMC-based contradiction.
       Key lemma: if J is SCC, W1\<union>W2 = S2-J (2 connected open components),
       then closure(W1) = W1 \<union> J (via simple\_closed\_curve\_boundary\_meets\_component).
       If D' is a J12-component: closure(D') = D'\<union>J12 \<subseteq> D'\<union>D\_loc \<Rightarrow> J12\<subseteq>D\_loc \<Rightarrow> e12\<subseteq>{a1,a2}.
       If D' is NOT a J12-component (for BOTH J12 AND J13):
       the J12-component Q12 = some Rk, and J13-component Q13 = same Rk
       \<Rightarrow> closure(Rk) = Rk\<union>J12 = Rk\<union>J13 \<Rightarrow> J12=J13 \<Rightarrow> Arc2=Arc3 \<Rightarrow> False.\<close>
    \<comment> \<open>Helper: closure of SCC component = component \<union> SCC.\<close>
    have hcl_scc_comp: "\<And>J W1 W2. top1_simple_closed_curve_on top1_S2 top1_S2_topology J \<Longrightarrow>
        W1 \<noteq> {} \<Longrightarrow> W2 \<noteq> {} \<Longrightarrow> W1 \<inter> W2 = {} \<Longrightarrow> W1 \<union> W2 = top1_S2 - J \<Longrightarrow>
        top1_connected_on W1 (subspace_topology top1_S2 top1_S2_topology W1) \<Longrightarrow>
        top1_connected_on W2 (subspace_topology top1_S2 top1_S2_topology W2) \<Longrightarrow>
        W1 \<in> top1_S2_topology \<Longrightarrow> W2 \<in> top1_S2_topology \<Longrightarrow>
        closure_on top1_S2 top1_S2_topology W1 = W1 \<union> J"
    proof -
      fix J W1 W2
      assume hJ_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology J"
          and hW1_ne: "W1 \<noteq> {}" and hW2_ne: "W2 \<noteq> {}" and hW12_d: "W1 \<inter> W2 = {}"
          and hW12_u: "W1 \<union> W2 = top1_S2 - J"
          and hW1_c: "top1_connected_on W1 (subspace_topology top1_S2 top1_S2_topology W1)"
          and hW2_c: "top1_connected_on W2 (subspace_topology top1_S2 top1_S2_topology W2)"
          and hW1_o: "W1 \<in> top1_S2_topology" and hW2_o: "W2 \<in> top1_S2_topology"
      have hW1_sub: "W1 \<subseteq> top1_S2" using hW12_u by (by100 blast)
      \<comment> \<open>Upper: cl(W1) \<subseteq> W1 \<union> J (since cl(W1) \<inter> W2 = {}).\<close>
      have hcl_upper: "closure_on top1_S2 top1_S2_topology W1 \<subseteq> W1 \<union> J"
      proof -
        have "closure_on top1_S2 top1_S2_topology W1 \<inter> W2 = {}"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          hence "intersects (closure_on top1_S2 top1_S2_topology W1) W2"
            unfolding intersects_def by (by100 blast)
          from top1_intersects_closure_on_open_imp_intersects[OF hTopS2 hW1_sub hW2_o this]
          show False using hW12_d unfolding intersects_def by (by100 blast)
        qed
        moreover have "closure_on top1_S2 top1_S2_topology W1 \<subseteq> top1_S2"
          by (rule closure_on_subset_carrier[OF hTopS2 hW1_sub])
        ultimately show ?thesis using hW12_u by (by100 blast)
      qed
      \<comment> \<open>Lower: J \<subseteq> cl(W1) (every point of J is in cl(W1), by SCCBMC).\<close>
      have hcl_lower: "W1 \<union> J \<subseteq> closure_on top1_S2 top1_S2_topology W1"
      proof -
        have "W1 \<subseteq> closure_on top1_S2 top1_S2_topology W1" by (rule subset_closure_on)
        moreover have "J \<subseteq> closure_on top1_S2 top1_S2_topology W1"
        proof
          fix x assume "x \<in> J"
          show "x \<in> closure_on top1_S2 top1_S2_topology W1"
          proof (rule iffD2[OF Theorem_17_5a[OF hTopS2 _ hW1_sub]])
            have "x \<in> top1_S2"
              using hJ_scc \<open>x \<in> J\<close> unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
              by (by100 blast)
            thus "x \<in> top1_S2" .
            show "\<forall>U. neighborhood_of x top1_S2 top1_S2_topology U \<longrightarrow> intersects U W1"
            proof (intro allI impI)
              fix V assume "neighborhood_of x top1_S2 top1_S2_topology V"
              hence hV: "V \<in> top1_S2_topology" "x \<in> V" unfolding neighborhood_of_def by (by100 blast)+
              have "V \<inter> W1 \<noteq> {}"
                by (rule simple_closed_curve_boundary_meets_component[OF assms(1) hJ_scc
                    hW1_c hW2_c hW12_d hW12_u hW1_ne hW2_ne hW1_o hW2_o \<open>x \<in> J\<close> hV(1) hV(2)])
              thus "intersects V W1" unfolding intersects_def by (by100 blast)
            qed
          qed
        qed
        ultimately show ?thesis by (by100 blast)
      qed
      show "closure_on top1_S2 top1_S2_topology W1 = W1 \<union> J"
        using hcl_upper hcl_lower by (by100 blast)
    qed
    \<comment> \<open>Helper: contradiction when a SCC J \<subseteq> D\_loc (forces e12 \<subseteq> {a1,a2}).\<close>
    have hJ_sub_D_loc_False: "\<And>J. J = e12 \<union> Arc2 \<or> J = e12 \<union> Arc3 \<Longrightarrow> J \<subseteq> D_loc \<Longrightarrow> False"
    proof -
      fix J assume hJ: "J = e12 \<union> Arc2 \<or> J = e12 \<union> Arc3" and hJD: "J \<subseteq> D_loc"
      have "e12 \<subseteq> J" using hJ by (by100 blast)
      hence "e12 \<subseteq> D_loc" using hJD by (by100 blast)
      hence "e12 - {a1, a2} \<subseteq> D_loc - {a1, a2}" by (by100 blast)
      moreover have "D_loc - {a1, a2} \<subseteq> D_loc" by (by100 blast)
      moreover have "e12 - {a1, a2} \<subseteq> e12 \<inter> D_loc" using \<open>e12 \<subseteq> D_loc\<close> by (by100 blast)
      moreover have "e12 \<inter> D_loc = {a1, a2}" by (rule he12_D_loc_int)
      ultimately have "e12 - {a1, a2} \<subseteq> {a1, a2}" by (by100 blast)
      hence "e12 - {a1, a2} = {}" by (by100 blast)
      thus False using he12_ne by (by100 blast)
    qed
    \<comment> \<open>Get 2 components of S2-J12.\<close>
    have hJ12_cl_e12: "closedin_on top1_S2 top1_S2_topology e12"
      by (rule arc_in_S2_closed[OF assms(4,10)])
    have hJ12_cl_Arc2: "closedin_on top1_S2 top1_S2_topology Arc2"
      by (rule arc_in_S2_closed[OF hArc2_sub hArc2_arc])
    have hJ12_card: "card (e12 \<inter> Arc2) = 2" using hint12 ha1_ne_a2 by (by100 simp)
    obtain W12a W12b where hW12: "W12a \<noteq> {}" "W12b \<noteq> {}" "W12a \<inter> W12b = {}"
        "W12a \<union> W12b = top1_S2 - (e12 \<union> Arc2)"
        "top1_connected_on W12a (subspace_topology top1_S2 top1_S2_topology W12a)"
        "top1_connected_on W12b (subspace_topology top1_S2 top1_S2_topology W12b)"
      using Theorem_63_5_two_closed_connected[OF assms(1) hJ12_cl_e12 hJ12_cl_Arc2
          arc_connected[OF assms(10)] arc_connected[OF hArc2_arc] hJ12_card
          Theorem_63_2_arc_no_separation[OF assms(1,4,10)]
          Theorem_63_2_arc_no_separation[OF assms(1) hArc2_sub hArc2_arc]]
      by (metis (no_types))
    \<comment> \<open>Make them open via S2\_two\_component\_open.\<close>
    have hJ12_cl: "closedin_on top1_S2 top1_S2_topology (e12 \<union> Arc2)"
      by (rule closedin_on_Un[OF hTopS2 hJ12_cl_e12 hJ12_cl_Arc2])
    have hJ12_open: "top1_S2 - (e12 \<union> Arc2) \<in> top1_S2_topology"
      using hJ12_cl unfolding closedin_on_def by (by100 blast)
    have hJ12_not_conn: "\<not> top1_connected_on (top1_S2 - (e12 \<union> Arc2))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e12 \<union> Arc2)))"
    proof -
      have "top1_separates_on top1_S2 top1_S2_topology (e12 \<union> Arc2)"
        by (rule Theorem_61_3_JordanSeparation_S2[OF assms(1) hJ12_scc])
      thus ?thesis unfolding top1_separates_on_def by (by100 simp)
    qed
    have hW12_open: "W12a \<in> top1_S2_topology \<and> W12b \<in> top1_S2_topology"
      using S2_two_component_open[OF hJ12_open _ hW12(1,2,3,4,5,6) hJ12_not_conn]
      by (by100 blast)
    \<comment> \<open>Arc3-{a1,a2} \<subseteq> S2-J12 and connected \<Rightarrow> in W12a or W12b. WLOG in W12b.\<close>
    \<comment> \<open>Q12 = the other one. Q12 \<inter> theta = {} \<Rightarrow> Q12 \<subseteq> R1\<union>R2\<union>R3 \<Rightarrow> Q12 = some Ri.\<close>
    \<comment> \<open>Ri\_e is NOT Q12 (a4 argument). So Q12 \<in> {Ri\_D, Rk}.\<close>
    \<comment> \<open>If Q12 = Ri\_D: cl(D') = D'\<union>J12 \<subseteq> D'\<union>D\_loc \<Rightarrow> J12\<subseteq>D\_loc \<Rightarrow> False.\<close>
    \<comment> \<open>If Q12 = Rk: similarly for J13. If Q13 = Rk too: J12=J13 \<Rightarrow> False.\<close>
    \<comment> \<open>If Q13 = Ri\_D: cl(D') = D'\<union>J13 \<subseteq> D'\<union>D\_loc \<Rightarrow> J13\<subseteq>D\_loc \<Rightarrow> False.\<close>
    \<comment> \<open>Identify which W12 component is Q12 (the one with \<inter> theta = {}).\<close>
    \<comment> \<open>Arc3 \<inter> (e12\<union>Arc2) = {a1,a2}. So Arc3-{a1,a2} \<subseteq> S2-(e12\<union>Arc2).
       Arc3-{a1,a2} connected \<Rightarrow> in W12a or W12b.\<close>
    have hArc3_sub_J12: "Arc3 - {a1, a2} \<subseteq> top1_S2 - (e12 \<union> Arc2)"
    proof -
      have "Arc3 \<inter> e12 = {a1, a2}" using hint13 by (by100 blast)
      moreover have "Arc3 \<inter> Arc2 = {a1, a2}" using hint23 by (by100 blast)
      ultimately have "Arc3 \<inter> (e12 \<union> Arc2) = {a1, a2}" by (by100 blast)
      thus ?thesis using hArc3_sub by (by100 blast)
    qed
    \<comment> \<open>Each Ri \<subseteq> S2-theta \<subseteq> S2-J12 = W12a \<union> W12b.\<close>
    \<comment> \<open>Arc3-{a1,a2} in one side. Ri\_D in one side. If in same side, their union side
       covers S2-J12 minus the other-side part. The other side = Q12 \<subseteq> S2-theta.\<close>
    \<comment> \<open>Key: Ri\_D is D' = B (a connected component of S2-D\_loc).
       closure(D') \<subseteq> D' \<union> D\_loc.
       If D' = W12a (a J12 component): closure(D') = D' \<union> J12 (from hcl\_scc\_comp).
       Then J12 \<subseteq> D' \<union> D\_loc. D' \<inter> J12 = {} (D' \<subseteq> S2-theta \<subseteq> S2-J12). So J12 \<subseteq> D\_loc.
       Apply hJ\_sub\_D\_loc\_False.\<close>
    \<comment> \<open>If D' \<noteq> W12a and D' \<noteq> W12b: impossible (D' connected \<subseteq> W12a\<union>W12b).\<close>
    have hD'_in_W12: "D' \<subseteq> W12a \<or> D' \<subseteq> W12b"
    proof -
      have hD'_sub_J12c: "D' \<subseteq> top1_S2 - (e12 \<union> Arc2)"
        using hD'_eq hRiD_sub_theta_compl by (by100 blast)
      hence hD'_sub_W12: "D' \<subseteq> W12a \<union> W12b" using hW12(4) by (by100 blast)
      have hTJ12: "is_topology_on (top1_S2 - (e12\<union>Arc2)) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e12\<union>Arc2)))"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
      have hW12a_open_sub: "W12a \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e12\<union>Arc2))"
        using hW12_open unfolding subspace_topology_def using hW12(4) by (by100 blast)
      have hW12b_open_sub: "W12b \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e12\<union>Arc2))"
        using hW12_open unfolding subspace_topology_def using hW12(4) by (by100 blast)
      have hSep_W12: "top1_is_separation_on (top1_S2 - (e12\<union>Arc2))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e12\<union>Arc2))) W12a W12b"
        unfolding top1_is_separation_on_def
        using hW12a_open_sub hW12b_open_sub hW12(1,2,3,4) by (by100 blast)
      have hD'_conn_W12: "top1_connected_on D'
          (subspace_topology (top1_S2 - (e12\<union>Arc2))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e12\<union>Arc2))) D')"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology D' =
            subspace_topology (top1_S2-(e12\<union>Arc2))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))) D'"
          using subspace_topology_trans[of D' "top1_S2-(e12\<union>Arc2)" top1_S2 top1_S2_topology]
              hD'_sub_J12c by (by100 simp)
        thus ?thesis using hD'_conn by (by100 simp)
      qed
      from Lemma_23_2[OF hTJ12 hSep_W12 hD'_sub_J12c hD'_conn_W12]
      show ?thesis by (by100 blast)
    qed
    show False
    proof (cases "D' = W12a \<or> D' = W12b")
      case True
      \<comment> \<open>D' is a full J12-component. closure(D') = D'\<union>J12.\<close>
      \<comment> \<open>Closure of W12a and W12b.\<close>
      have hcl_W12a: "closure_on top1_S2 top1_S2_topology W12a = W12a \<union> (e12 \<union> Arc2)"
        by (rule hcl_scc_comp[OF hJ12_scc hW12(1,2,3,4,5,6) hW12_open[THEN conjunct1] hW12_open[THEN conjunct2]])
      have hcl_W12b: "closure_on top1_S2 top1_S2_topology W12b = W12b \<union> (e12 \<union> Arc2)"
      proof -
        have h1: "W12b \<inter> W12a = {}" using hW12(3) by (by100 blast)
        have h2: "W12b \<union> W12a = top1_S2 - (e12 \<union> Arc2)" using hW12(4) by (by100 blast)
        show ?thesis
          by (rule hcl_scc_comp[OF hJ12_scc hW12(2,1) h1 h2 hW12(6,5) hW12_open[THEN conjunct2] hW12_open[THEN conjunct1]])
      qed
      have hcl_D'_J12: "closure_on top1_S2 top1_S2_topology D' = D' \<union> (e12 \<union> Arc2)"
        using True hcl_W12a hcl_W12b by (by100 blast)
      \<comment> \<open>Combined with hcl\_D'\_sub: J12 \<subseteq> D' \<union> D\_loc.\<close>
      have "D' \<union> (e12 \<union> Arc2) \<subseteq> D' \<union> D_loc"
        using hcl_D'_J12 hcl_D'_sub by (by100 blast)
      hence "e12 \<union> Arc2 \<subseteq> D' \<union> D_loc" by (by100 blast)
      moreover have "D' \<inter> (e12 \<union> Arc2) = {}"
      proof -
        have "D' \<subseteq> top1_S2 - (e12 \<union> Arc2 \<union> Arc3)"
          using hD'_eq hRiD_sub_theta_compl by (by100 simp)
        thus ?thesis by (by100 blast)
      qed
      ultimately have hJ12_sub_D: "e12 \<union> Arc2 \<subseteq> D_loc" by (by100 blast)
      have hJ12_is_J: "e12 \<union> Arc2 = e12 \<union> Arc2 \<or> e12 \<union> Arc2 = e12 \<union> Arc3" by (by100 blast)
      from hJ_sub_D_loc_False[OF hJ12_is_J hJ12_sub_D] show False .
    next
      case False
      \<comment> \<open>D' is NOT a full J12-component. Then D' \<subsetneq> W12a or W12b.\<close>
      \<comment> \<open>This case requires the J13 argument. D' not full J12 comp means
         Q12 (the J12 comp = some Ri) is NOT Ri\_D, so Q12 = Rk.
         Similarly for J13: Q13 = Rk. Then closure(Rk)=Rk\<union>J12=Rk\<union>J13, J12=J13.\<close>
      \<comment> \<open>D' \<subsetneq> W12a or W12b. The OTHER component Q12 \<subseteq> S2-theta = R1\<union>R2\<union>R3.
         Q12 connected, Q12 = some Ri. Since Q12 \<inter> D' = {}: Ri \<noteq> Ri\_D. And Ri \<noteq> Ri\_e (by a4).
         Hence Q12 = Rk. Similarly for J13: Q13 = Rk.
         closure(Rk) = Rk \<union> J12 = Rk \<union> J13. Rk \<inter> J12 = Rk \<inter> J13 = {} \<Rightarrow> J12 = J13 \<Rightarrow>
         Arc2 = Arc3 \<Rightarrow> a3 \<in> Arc3 = e24\<union>e41 \<Rightarrow> False.\<close>
      \<comment> \<open>Q12 argument: the J12-component NOT containing D'.\<close>
      have "D' \<noteq> W12a" "D' \<noteq> W12b" using False by (by100 blast)+
      \<comment> \<open>D' \<subseteq> W12a or W12b (hD'\_in\_W12). Pick the component containing D'.\<close>
      \<comment> \<open>The OTHER component Q12 has Q12 \<inter> D' = {} and Q12 \<inter> theta = {}.\<close>
      \<comment> \<open>For each case: Q12 \<subseteq> S2-theta \<Rightarrow> Q12 \<subseteq> R1\<union>R2\<union>R3 \<Rightarrow> Q12 = some Ri.\<close>
      \<comment> \<open>Then similarly for J13. If same Ri for both: J12=J13.\<close>
      \<comment> \<open>If different: one of them = Ri\_D, contradicting D' \<noteq> component.\<close>
      \<comment> \<open>For now, use the closure(D') \<subseteq> D'\<union>D\_loc to get J13\<subseteq>D\_loc too.\<close>
      \<comment> \<open>Actually: D' is NOT a FULL component of S2-J12, so we use J13 instead.\<close>
      \<comment> \<open>Get J13 components similarly.\<close>
      have hJ13_cl_Arc3: "closedin_on top1_S2 top1_S2_topology Arc3"
        by (rule arc_in_S2_closed[OF hArc3_sub hArc3_arc])
      have hJ13_card: "card (e12 \<inter> Arc3) = 2" using hint13 ha1_ne_a2 by (by100 simp)
      obtain W13a W13b where hW13: "W13a \<noteq> {}" "W13b \<noteq> {}" "W13a \<inter> W13b = {}"
          "W13a \<union> W13b = top1_S2 - (e12 \<union> Arc3)"
          "top1_connected_on W13a (subspace_topology top1_S2 top1_S2_topology W13a)"
          "top1_connected_on W13b (subspace_topology top1_S2 top1_S2_topology W13b)"
        using Theorem_63_5_two_closed_connected[OF assms(1) hJ12_cl_e12 hJ13_cl_Arc3
            arc_connected[OF assms(10)] arc_connected[OF hArc3_arc] hJ13_card
            Theorem_63_2_arc_no_separation[OF assms(1,4,10)]
            Theorem_63_2_arc_no_separation[OF assms(1) hArc3_sub hArc3_arc]]
        by (metis (no_types))
      have hJ13_cl: "closedin_on top1_S2 top1_S2_topology (e12 \<union> Arc3)"
        by (rule closedin_on_Un[OF hTopS2 hJ12_cl_e12 hJ13_cl_Arc3])
      have hJ13_open: "top1_S2 - (e12 \<union> Arc3) \<in> top1_S2_topology"
        using hJ13_cl unfolding closedin_on_def by (by100 blast)
      have hJ13_not_conn: "\<not> top1_connected_on (top1_S2 - (e12 \<union> Arc3))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e12 \<union> Arc3)))"
      proof -
        have "top1_separates_on top1_S2 top1_S2_topology (e12 \<union> Arc3)"
          by (rule Theorem_61_3_JordanSeparation_S2[OF assms(1) hJ13_scc])
        thus ?thesis unfolding top1_separates_on_def by (by100 simp)
      qed
      have hW13_open: "W13a \<in> top1_S2_topology \<and> W13b \<in> top1_S2_topology"
        using S2_two_component_open[OF hJ13_open _ hW13(1,2,3,4,5,6) hJ13_not_conn]
        by (by100 blast)
      \<comment> \<open>D' in one of W13a, W13b (same Lemma\_23\_2 argument).\<close>
      have hD'_in_W13: "D' \<subseteq> W13a \<or> D' \<subseteq> W13b"
      proof -
        have hD'_sub_J13c: "D' \<subseteq> top1_S2 - (e12 \<union> Arc3)"
          using hD'_eq hRiD_sub_theta_compl by (by100 blast)
        have hTJ13_loc: "is_topology_on (top1_S2 - (e12\<union>Arc3)) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e12\<union>Arc3)))"
          by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
        have "W13a \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e12\<union>Arc3))"
          using hW13_open unfolding subspace_topology_def using hW13(4) by (by100 blast)
        moreover have "W13b \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e12\<union>Arc3))"
          using hW13_open unfolding subspace_topology_def using hW13(4) by (by100 blast)
        ultimately have hSep_W13: "top1_is_separation_on (top1_S2 - (e12\<union>Arc3))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e12\<union>Arc3))) W13a W13b"
          unfolding top1_is_separation_on_def using hW13(1,2,3,4) by (by100 blast)
        have "top1_connected_on D'
            (subspace_topology (top1_S2 - (e12\<union>Arc3))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e12\<union>Arc3))) D')"
        proof -
          have "subspace_topology top1_S2 top1_S2_topology D' =
              subspace_topology (top1_S2-(e12\<union>Arc3))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))) D'"
            using subspace_topology_trans[of D' "top1_S2-(e12\<union>Arc3)" top1_S2 top1_S2_topology]
                hD'_sub_J13c by (by100 simp)
          thus ?thesis using hD'_conn by (by100 simp)
        qed
        from Lemma_23_2[OF hTJ13_loc hSep_W13 hD'_sub_J13c this]
        show ?thesis by (by100 blast)
      qed
      \<comment> \<open>Is D' a full J13 component?\<close>
      show False
      proof (cases "D' = W13a \<or> D' = W13b")
        case True
        \<comment> \<open>D' IS a J13 component. Same closure argument as J12 case.\<close>
        have hcl_W13a: "closure_on top1_S2 top1_S2_topology W13a = W13a \<union> (e12 \<union> Arc3)"
          by (rule hcl_scc_comp[OF hJ13_scc hW13(1,2,3,4,5,6) hW13_open[THEN conjunct1] hW13_open[THEN conjunct2]])
        have hcl_W13b: "closure_on top1_S2 top1_S2_topology W13b = W13b \<union> (e12 \<union> Arc3)"
        proof -
          have h1: "W13b \<inter> W13a = {}" using hW13(3) by (by100 blast)
          have h2: "W13b \<union> W13a = top1_S2 - (e12 \<union> Arc3)" using hW13(4) by (by100 blast)
          show ?thesis by (rule hcl_scc_comp[OF hJ13_scc hW13(2,1) h1 h2 hW13(6,5) hW13_open[THEN conjunct2] hW13_open[THEN conjunct1]])
        qed
        have hcl_D'_J13: "closure_on top1_S2 top1_S2_topology D' = D' \<union> (e12 \<union> Arc3)"
          using True hcl_W13a hcl_W13b by (by100 blast)
        have "D' \<union> (e12 \<union> Arc3) \<subseteq> D' \<union> D_loc"
          using hcl_D'_J13 hcl_D'_sub by (by100 blast)
        hence "e12 \<union> Arc3 \<subseteq> D' \<union> D_loc" by (by100 blast)
        moreover have "D' \<inter> (e12 \<union> Arc3) = {}"
          using hD'_eq hRiD_sub_theta_compl by (by100 blast)
        ultimately have "e12 \<union> Arc3 \<subseteq> D_loc" by (by100 blast)
        have "e12 \<union> Arc3 = e12 \<union> Arc3 \<or> e12 \<union> Arc3 = e12 \<union> Arc3" by (by100 blast)
        hence "e12 \<union> Arc3 = e12 \<union> Arc2 \<or> e12 \<union> Arc3 = e12 \<union> Arc3" by (by100 blast)
        from hJ_sub_D_loc_False[OF this \<open>e12 \<union> Arc3 \<subseteq> D_loc\<close>] show False .
      next
        case J13_False: False
        \<comment> \<open>D' is NOT a full component of EITHER J12 or J13.
           Then the "other" J12-component Q12 and "other" J13-component Q13 are NOT D'.
           Both are connected subsets of S2-theta = R1\<union>R2\<union>R3, hence each = some Ri.
           Cannot be Ri\_D (disjoint from D' complement). Cannot be Ri\_e (by a4/a3).
           Hence both = Rk. closure(Rk) = Rk\<union>J12 = Rk\<union>J13 \<Rightarrow> J12=J13 \<Rightarrow> Arc2=Arc3.\<close>
        \<comment> \<open>Q12 (other J12-side from D') \<subseteq> S2-theta, Q12=some Ri, Q12 \<noteq> Ri\_D, Q12 \<noteq> Ri\_e.\<close>
        have hQ12_sub_R: "\<exists>Q. Q \<in> {W12a, W12b} \<and> Q \<subseteq> R1 \<union> R2 \<union> R3 \<and> D' \<inter> Q = {} \<and> Q \<noteq> {}"
        proof -
          \<comment> \<open>Arc3-{a1,a2} in one of W12a/W12b (connected \<subseteq> S2-J12).\<close>
          have hArc3_ne_loc: "Arc3 - {a1,a2} \<noteq> {}"
          proof
            assume "Arc3 - {a1,a2} = {}"
            hence "Arc3 \<subseteq> {a1,a2}" by (by100 blast)
            have "a1 \<in> closure_on top1_S2 top1_S2_topology (Arc3 - {a1,a2})"
              using arc_endpoint_in_closure_of_interior[OF assms(1) hS2_haus hArc3_sub hArc3_arc hArc3_ep ha1_ne_a2]
              by (by100 blast)
            hence "a1 \<in> closure_on top1_S2 top1_S2_topology {}" using \<open>Arc3 - {a1,a2} = {}\<close> by (by100 simp)
            thus False using top1_closure_on_empty[OF hTopS2] by (by100 simp)
          qed
          have hArc3_in: "Arc3 - {a1,a2} \<subseteq> W12a \<or> Arc3 - {a1,a2} \<subseteq> W12b"
          proof -
            have hArc3_conn_loc: "top1_connected_on (Arc3 - {a1,a2})
                (subspace_topology top1_S2 top1_S2_topology (Arc3 - {a1,a2}))"
              by (rule arc_minus_endpoints_connected[OF assms(1) hS2_haus hArc3_sub hArc3_arc hArc3_ep ha1_ne_a2])
            have hArc3_sub_loc: "Arc3 - {a1,a2} \<subseteq> top1_S2 - (e12 \<union> Arc2)"
              using hArc3_sub_J12 .
            have hArc3_conn_sub: "top1_connected_on (Arc3 - {a1,a2})
                (subspace_topology (top1_S2-(e12\<union>Arc2))
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))) (Arc3-{a1,a2}))"
            proof -
              have "subspace_topology top1_S2 top1_S2_topology (Arc3-{a1,a2}) =
                  subspace_topology (top1_S2-(e12\<union>Arc2))
                      (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))) (Arc3-{a1,a2})"
                using subspace_topology_trans[of "Arc3-{a1,a2}" "top1_S2-(e12\<union>Arc2)"]
                    hArc3_sub_loc by (by100 simp)
              thus ?thesis using hArc3_conn_loc by (by100 simp)
            qed
            have hTJ12_loc: "is_topology_on (top1_S2-(e12\<union>Arc2)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2)))"
              by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
            have hW12a_op: "W12a \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))"
              using hW12_open hW12(4) unfolding subspace_topology_def by (by100 blast)
            have hW12b_op: "W12b \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))"
              using hW12_open hW12(4) unfolding subspace_topology_def by (by100 blast)
            have hSep_W12_loc: "top1_is_separation_on (top1_S2-(e12\<union>Arc2))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))) W12a W12b"
              unfolding top1_is_separation_on_def
              using hW12a_op hW12b_op hW12(1,2,3,4) by (by100 blast)
            from Lemma_23_2[OF hTJ12_loc hSep_W12_loc hArc3_sub_loc hArc3_conn_sub]
            show ?thesis by (by100 blast)
          qed
          from hD'_in_W12 show ?thesis
          proof (elim disjE)
            assume hDa: "D' \<subseteq> W12a"
            \<comment> \<open>If Arc3 \<subseteq> W12b: W12a \<inter> Arc3 = {}, so W12a \<subseteq> S2-theta.
               Then D' = W12a by J\_component\_sub\_theta\_forces\_eq. Contradicts D' \<noteq> W12a.\<close>
            have hArc3_W12a: "Arc3 - {a1,a2} \<subseteq> W12a"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              hence "Arc3 - {a1,a2} \<subseteq> W12b" using hArc3_in by (by100 blast)
              hence "W12a \<inter> (Arc3 - {a1,a2}) = {}" using hW12(3) by (by100 blast)
              moreover have "W12a \<inter> {a1,a2} = {}" using hW12(4) hint12 hint13 by (by100 blast)
              ultimately have "W12a \<inter> Arc3 = {}" by (by100 blast)
              hence "W12a \<subseteq> R1 \<union> R2 \<union> R3" using hW12(4) hR(7) by (by100 blast)
              from J_component_sub_theta_forces_eq[OF this hW12(1,5) hDa hD'_ne
                  hD'_sub_RiD hRiD_sub_D' hRiD hR_in_one hR(4,5,6)]
              have "D' = W12a" .
              thus False using \<open>D' \<noteq> W12a\<close> by (by100 blast)
            qed
            \<comment> \<open>Arc3 and D' on same side (W12a). Q12 = W12b.\<close>
            have "W12b \<inter> (Arc3 - {a1,a2}) = {}" using hArc3_W12a hW12(3) by (by100 blast)
            moreover have "W12b \<inter> {a1,a2} = {}" using hW12(4) hint12 hint13 by (by100 blast)
            ultimately have "W12b \<inter> Arc3 = {}" by (by100 blast)
            hence "W12b \<subseteq> R1 \<union> R2 \<union> R3" using hW12(4) hR(7) by (by100 blast)
            moreover have "D' \<inter> W12b = {}" using hDa hW12(3) by (by100 blast)
            ultimately show ?thesis using hW12(2) by (by100 blast)
          next
            assume hDb: "D' \<subseteq> W12b"
            \<comment> \<open>Symmetric case.\<close>
            have hArc3_W12b: "Arc3 - {a1,a2} \<subseteq> W12b"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              hence "Arc3 - {a1,a2} \<subseteq> W12a" using hArc3_in by (by100 blast)
              hence "W12b \<inter> (Arc3 - {a1,a2}) = {}" using hW12(3) by (by100 blast)
              moreover have "W12b \<inter> {a1,a2} = {}" using hW12(4) hint12 hint13 by (by100 blast)
              ultimately have "W12b \<inter> Arc3 = {}" by (by100 blast)
              hence "W12b \<subseteq> R1 \<union> R2 \<union> R3" using hW12(4) hR(7) by (by100 blast)
              from J_component_sub_theta_forces_eq[OF this hW12(2,6) hDb hD'_ne
                  hD'_sub_RiD hRiD_sub_D' hRiD hR_in_one hR(4,5,6)]
              have "D' = W12b" .
              thus False using \<open>D' \<noteq> W12b\<close> by (by100 blast)
            qed
            have "W12a \<inter> (Arc3 - {a1,a2}) = {}" using hArc3_W12b hW12(3) by (by100 blast)
            moreover have "W12a \<inter> {a1,a2} = {}" using hW12(4) hint12 hint13 by (by100 blast)
            ultimately have "W12a \<inter> Arc3 = {}" by (by100 blast)
            hence "W12a \<subseteq> R1 \<union> R2 \<union> R3" using hW12(4) hR(7) by (by100 blast)
            moreover have "D' \<inter> W12a = {}" using hDb hW12(3) by (by100 blast)
            ultimately show ?thesis using hW12(1) by (by100 blast)
          qed
        qed
        then obtain Q12 where hQ12: "Q12 \<in> {W12a, W12b}" "Q12 \<subseteq> R1 \<union> R2 \<union> R3"
            "D' \<inter> Q12 = {}" "Q12 \<noteq> {}" by blast
        have hQ13_sub_R: "\<exists>Q. Q \<in> {W13a, W13b} \<and> Q \<subseteq> R1 \<union> R2 \<union> R3 \<and> D' \<inter> Q = {} \<and> Q \<noteq> {}"
        proof -
          have hArc2_ne_loc: "Arc2 - {a1,a2} \<noteq> {}"
          proof
            assume "Arc2 - {a1,a2} = {}"
            have "a1 \<in> closure_on top1_S2 top1_S2_topology (Arc2 - {a1,a2})"
              using arc_endpoint_in_closure_of_interior[OF assms(1) hS2_haus hArc2_sub hArc2_arc hArc2_ep ha1_ne_a2]
              by (by100 blast)
            hence "a1 \<in> closure_on top1_S2 top1_S2_topology {}" using \<open>Arc2 - {a1,a2} = {}\<close> by (by100 simp)
            thus False using top1_closure_on_empty[OF hTopS2] by (by100 simp)
          qed
          have hArc2_in: "Arc2 - {a1,a2} \<subseteq> W13a \<or> Arc2 - {a1,a2} \<subseteq> W13b"
          proof -
            have hArc2_conn_loc: "top1_connected_on (Arc2 - {a1,a2})
                (subspace_topology top1_S2 top1_S2_topology (Arc2 - {a1,a2}))"
              by (rule arc_minus_endpoints_connected[OF assms(1) hS2_haus hArc2_sub hArc2_arc hArc2_ep ha1_ne_a2])
            have hArc2_sub_J13: "Arc2 - {a1,a2} \<subseteq> top1_S2 - (e12 \<union> Arc3)"
            proof -
              have "Arc2 \<inter> e12 = {a1, a2}" using hint12 by (by100 blast)
              moreover have "Arc2 \<inter> Arc3 = {a1, a2}" using hint23 by (by100 blast)
              ultimately have "Arc2 \<inter> (e12 \<union> Arc3) = {a1, a2}" by (by100 blast)
              thus ?thesis using hArc2_sub by (by100 blast)
            qed
            have hArc2_conn_sub: "top1_connected_on (Arc2 - {a1,a2})
                (subspace_topology (top1_S2-(e12\<union>Arc3))
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))) (Arc2-{a1,a2}))"
            proof -
              have "subspace_topology top1_S2 top1_S2_topology (Arc2-{a1,a2}) =
                  subspace_topology (top1_S2-(e12\<union>Arc3))
                      (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))) (Arc2-{a1,a2})"
                using subspace_topology_trans[of "Arc2-{a1,a2}" "top1_S2-(e12\<union>Arc3)"]
                    hArc2_sub_J13 by (by100 simp)
              thus ?thesis using hArc2_conn_loc by (by100 simp)
            qed
            have hTJ13_loc2: "is_topology_on (top1_S2-(e12\<union>Arc3)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3)))"
              by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
            have "W13a \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))"
              using hW13_open hW13(4) unfolding subspace_topology_def by (by100 blast)
            moreover have "W13b \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))"
              using hW13_open hW13(4) unfolding subspace_topology_def by (by100 blast)
            ultimately have hSep_W13_loc2: "top1_is_separation_on (top1_S2-(e12\<union>Arc3))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))) W13a W13b"
              unfolding top1_is_separation_on_def using hW13(1,2,3,4) by (by100 blast)
            from Lemma_23_2[OF hTJ13_loc2 hSep_W13_loc2 hArc2_sub_J13 hArc2_conn_sub]
            show ?thesis by (by100 blast)
          qed
          from hD'_in_W13 show ?thesis
          proof (elim disjE)
            assume hDa: "D' \<subseteq> W13a"
            have "Arc2 - {a1,a2} \<subseteq> W13a"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              hence "Arc2 - {a1,a2} \<subseteq> W13b" using hArc2_in by (by100 blast)
              hence "W13a \<inter> (Arc2 - {a1,a2}) = {}" using hW13(3) by (by100 blast)
              moreover have "W13a \<inter> {a1,a2} = {}" using hW13(4) hint13 hint23 by (by100 blast)
              ultimately have "W13a \<inter> Arc2 = {}" by (by100 blast)
              hence "W13a \<subseteq> R1 \<union> R2 \<union> R3" using hW13(4) hR(7) by (by100 blast)
              from J_component_sub_theta_forces_eq[OF this hW13(1,5) hDa hD'_ne
                  hD'_sub_RiD hRiD_sub_D' hRiD hR_in_one hR(4,5,6)]
              show False using J13_False by (by100 blast)
            qed
            have "W13b \<inter> (Arc2 - {a1,a2}) = {}" using \<open>Arc2 - {a1,a2} \<subseteq> W13a\<close> hW13(3) by (by100 blast)
            moreover have "W13b \<inter> {a1,a2} = {}" using hW13(4) hint13 hint23 by (by100 blast)
            ultimately have "W13b \<inter> Arc2 = {}" by (by100 blast)
            hence "W13b \<subseteq> R1 \<union> R2 \<union> R3" using hW13(4) hR(7) by (by100 blast)
            moreover have "D' \<inter> W13b = {}" using hDa hW13(3) by (by100 blast)
            ultimately show ?thesis using hW13(2) by (by100 blast)
          next
            assume hDb: "D' \<subseteq> W13b"
            have "Arc2 - {a1,a2} \<subseteq> W13b"
            proof (rule ccontr)
              assume "\<not> ?thesis"
              hence "Arc2 - {a1,a2} \<subseteq> W13a" using hArc2_in by (by100 blast)
              hence "W13b \<inter> (Arc2 - {a1,a2}) = {}" using hW13(3) by (by100 blast)
              moreover have "W13b \<inter> {a1,a2} = {}" using hW13(4) hint13 hint23 by (by100 blast)
              ultimately have "W13b \<inter> Arc2 = {}" by (by100 blast)
              hence "W13b \<subseteq> R1 \<union> R2 \<union> R3" using hW13(4) hR(7) by (by100 blast)
              from J_component_sub_theta_forces_eq[OF this hW13(2,6) hDb hD'_ne
                  hD'_sub_RiD hRiD_sub_D' hRiD hR_in_one hR(4,5,6)]
              show False using J13_False by (by100 blast)
            qed
            have "W13a \<inter> (Arc2 - {a1,a2}) = {}" using \<open>Arc2 - {a1,a2} \<subseteq> W13b\<close> hW13(3) by (by100 blast)
            moreover have "W13a \<inter> {a1,a2} = {}" using hW13(4) hint13 hint23 by (by100 blast)
            ultimately have "W13a \<inter> Arc2 = {}" by (by100 blast)
            hence "W13a \<subseteq> R1 \<union> R2 \<union> R3" using hW13(4) hR(7) by (by100 blast)
            moreover have "D' \<inter> W13a = {}" using hDb hW13(3) by (by100 blast)
            ultimately show ?thesis using hW13(1) by (by100 blast)
          qed
        qed
        then obtain Q13 where hQ13: "Q13 \<in> {W13a, W13b}" "Q13 \<subseteq> R1 \<union> R2 \<union> R3"
            "D' \<inter> Q13 = {}" "Q13 \<noteq> {}" by blast
        \<comment> \<open>Q12 = some Ri (connected J12-component \<subseteq> R1\<union>R2\<union>R3).\<close>
        have hQ12_conn: "top1_connected_on Q12 (subspace_topology top1_S2 top1_S2_topology Q12)"
          using hQ12(1) hW12(5,6) by (by100 blast)
        from hR_in_one[OF hQ12(2) hQ12(4) hQ12_conn]
        obtain Ri_Q12 where "Ri_Q12 \<in> {R1,R2,R3}" "Q12 \<subseteq> Ri_Q12" by (by100 blast)
        have hQ13_conn: "top1_connected_on Q13 (subspace_topology top1_S2 top1_S2_topology Q13)"
          using hQ13(1) hW13(5,6) by (by100 blast)
        from hR_in_one[OF hQ13(2) hQ13(4) hQ13_conn]
        obtain Ri_Q13 where "Ri_Q13 \<in> {R1,R2,R3}" "Q13 \<subseteq> Ri_Q13" by (by100 blast)
        \<comment> \<open>Q12 \<noteq> Ri\_D and Q12 \<noteq> Ri\_e (boundary arguments).\<close>
        have "Ri_Q12 \<noteq> Ri_D"
        proof assume "Ri_Q12 = Ri_D"
          hence "Q12 \<subseteq> D'" using \<open>Q12 \<subseteq> Ri_Q12\<close> hRiD_sub_D' by (by100 blast)
          thus False using hQ12(3,4) by (by100 blast) qed
        have "Ri_Q12 \<noteq> Ri_e"
        proof assume hRiQ12_eq: "Ri_Q12 = Ri_e"
          hence "Q12 \<subseteq> Ri_e" using \<open>Q12 \<subseteq> Ri_Q12\<close> by (by100 blast)
          hence "Ri_e \<inter> Q12 \<noteq> {}" using hQ12(4) by (by100 blast)
          \<comment> \<open>Ri\_e connected \<subseteq> S2-J12. By Lemma\_23\_2: Ri\_e \<subseteq> Q12.\<close>
          have hRie_conn_loc: "top1_connected_on Ri_e (subspace_topology top1_S2 top1_S2_topology Ri_e)"
            using hRie(1) hR(8,9,10) by (by100 blast)
          have hRie_sub_J12: "Ri_e \<subseteq> top1_S2 - (e12 \<union> Arc2)"
            using hRie(1) element_of_three_subset hR(7) by (by100 blast)
          have "Ri_e \<subseteq> Q12"
          proof -
            have hRie_conn_J12: "top1_connected_on Ri_e
                (subspace_topology (top1_S2-(e12\<union>Arc2))
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))) Ri_e)"
            proof -
              have hRie_conn_l: "top1_connected_on Ri_e (subspace_topology top1_S2 top1_S2_topology Ri_e)"
                using hRie(1) hR(8,9,10) by (by100 blast)
              have "subspace_topology top1_S2 top1_S2_topology Ri_e =
                  subspace_topology (top1_S2-(e12\<union>Arc2))
                      (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))) Ri_e"
                using subspace_topology_trans[of Ri_e "top1_S2-(e12\<union>Arc2)"] hRie_sub_J12 by (by100 simp)
              thus ?thesis using hRie_conn_l by (by100 simp)
            qed
            have hTJ12_l: "is_topology_on (top1_S2-(e12\<union>Arc2)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2)))"
              by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
            have "W12a \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))"
              using hW12_open hW12(4) unfolding subspace_topology_def by (by100 blast)
            moreover have "W12b \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))"
              using hW12_open hW12(4) unfolding subspace_topology_def by (by100 blast)
            ultimately have hSep_l: "top1_is_separation_on (top1_S2-(e12\<union>Arc2))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))) W12a W12b"
              unfolding top1_is_separation_on_def using hW12(1,2,3,4) by (by100 blast)
            from Lemma_23_2[OF hTJ12_l hSep_l hRie_sub_J12 hRie_conn_J12]
            have "Ri_e \<subseteq> W12a \<or> Ri_e \<subseteq> W12b" by (by100 blast)
            thus "Ri_e \<subseteq> Q12" using \<open>Ri_e \<inter> Q12 \<noteq> {}\<close> hQ12(1) hW12(3) by (by100 blast)
          qed
          \<comment> \<open>cl(Ri\_e) \<subseteq> cl(Q12) = Q12 \<union> J12.\<close>
          have "a4 \<in> closure_on top1_S2 top1_S2_topology Q12"
          proof -
            have ha34_ne: "a3 \<noteq> a4" using ha3_ne_a4 .
            have "a4 \<in> closure_on top1_S2 top1_S2_topology (e34 - {a3, a4})"
              using arc_endpoint_in_closure_of_interior[OF assms(1) hS2_haus assms(6,12,18) ha34_ne]
              by (by100 blast)
            hence "a4 \<in> closure_on top1_S2 top1_S2_topology Ri_e"
              using closure_on_mono[OF hRie(2)] by (by100 blast)
            thus ?thesis using closure_on_mono[OF \<open>Ri_e \<subseteq> Q12\<close>] by (by100 blast)
          qed
          have "closure_on top1_S2 top1_S2_topology Q12 = Q12 \<union> (e12 \<union> Arc2)"
          proof -
            have hcl_W12a_l: "closure_on top1_S2 top1_S2_topology W12a = W12a \<union> (e12 \<union> Arc2)"
              by (rule hcl_scc_comp[OF hJ12_scc hW12(1,2,3,4,5,6) hW12_open[THEN conjunct1] hW12_open[THEN conjunct2]])
            have hcl_W12b_l: "closure_on top1_S2 top1_S2_topology W12b = W12b \<union> (e12 \<union> Arc2)"
            proof -
              have h1: "W12b \<inter> W12a = {}" using hW12(3) by (by100 blast)
              have h2: "W12b \<union> W12a = top1_S2 - (e12 \<union> Arc2)" using hW12(4) by (by100 blast)
              show ?thesis by (rule hcl_scc_comp[OF hJ12_scc hW12(2,1) h1 h2 hW12(6,5) hW12_open[THEN conjunct2] hW12_open[THEN conjunct1]])
            qed
            from hQ12(1) show ?thesis using hcl_W12a_l hcl_W12b_l by (by100 blast)
          qed
          hence "a4 \<in> Q12 \<union> (e12 \<union> Arc2)" using \<open>a4 \<in> closure_on _ _ Q12\<close> by (by100 blast)
          moreover have "a4 \<notin> e12" by (rule ha4_not_e12)
          moreover have "a4 \<notin> Arc2" by (rule ha4_not_Arc2)
          ultimately have "a4 \<in> Q12" by (by100 blast)
          hence "a4 \<in> R1 \<union> R2 \<union> R3" using hQ12(2) by (by100 blast)
          hence "a4 \<in> top1_S2 - (e12 \<union> Arc2 \<union> Arc3)" using hR(7) by (by100 blast)
          moreover have "a4 \<in> Arc3" using assms(19) unfolding top1_arc_endpoints_on_def defs by (by100 blast)
          ultimately show False by (by100 blast)
        qed
        have "Ri_Q13 \<noteq> Ri_D"
        proof assume "Ri_Q13 = Ri_D"
          hence "Q13 \<subseteq> D'" using \<open>Q13 \<subseteq> Ri_Q13\<close> hRiD_sub_D' by (by100 blast)
          thus False using hQ13(3,4) by (by100 blast) qed
        have "Ri_Q13 \<noteq> Ri_e"
        proof assume hRiQ13_eq: "Ri_Q13 = Ri_e"
          hence "Q13 \<subseteq> Ri_e" using \<open>Q13 \<subseteq> Ri_Q13\<close> by (by100 blast)
          hence "Ri_e \<inter> Q13 \<noteq> {}" using hQ13(4) by (by100 blast)
          have hRie_sub_J13: "Ri_e \<subseteq> top1_S2 - (e12 \<union> Arc3)"
            using hRie(1) element_of_three_subset hR(7) by (by100 blast)
          have "Ri_e \<subseteq> Q13"
          proof -
            have hRie_conn_J13: "top1_connected_on Ri_e
                (subspace_topology (top1_S2-(e12\<union>Arc3))
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))) Ri_e)"
            proof -
              have hRie_conn_l: "top1_connected_on Ri_e (subspace_topology top1_S2 top1_S2_topology Ri_e)"
                using hRie(1) hR(8,9,10) by (by100 blast)
              have "subspace_topology top1_S2 top1_S2_topology Ri_e =
                  subspace_topology (top1_S2-(e12\<union>Arc3))
                      (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))) Ri_e"
                using subspace_topology_trans[of Ri_e "top1_S2-(e12\<union>Arc3)"] hRie_sub_J13 by (by100 simp)
              thus ?thesis using hRie_conn_l by (by100 simp)
            qed
            have hTJ13_l: "is_topology_on (top1_S2-(e12\<union>Arc3)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3)))"
              by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
            have "W13a \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))"
              using hW13_open hW13(4) unfolding subspace_topology_def by (by100 blast)
            moreover have "W13b \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))"
              using hW13_open hW13(4) unfolding subspace_topology_def by (by100 blast)
            ultimately have hSep_l: "top1_is_separation_on (top1_S2-(e12\<union>Arc3))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))) W13a W13b"
              unfolding top1_is_separation_on_def using hW13(1,2,3,4) by (by100 blast)
            from Lemma_23_2[OF hTJ13_l hSep_l hRie_sub_J13 hRie_conn_J13]
            have "Ri_e \<subseteq> W13a \<or> Ri_e \<subseteq> W13b" by (by100 blast)
            thus "Ri_e \<subseteq> Q13" using \<open>Ri_e \<inter> Q13 \<noteq> {}\<close> hQ13(1) hW13(3) by (by100 blast)
          qed
          have "a3 \<in> closure_on top1_S2 top1_S2_topology Q13"
          proof -
            have ha34_ne: "a3 \<noteq> a4" using ha3_ne_a4 .
            have "a3 \<in> closure_on top1_S2 top1_S2_topology (e34 - {a3, a4})"
              using arc_endpoint_in_closure_of_interior[OF assms(1) hS2_haus assms(6,12,18) ha34_ne]
              by (by100 blast)
            hence "a3 \<in> closure_on top1_S2 top1_S2_topology Ri_e"
              using closure_on_mono[OF hRie(2)] by (by100 blast)
            thus ?thesis using closure_on_mono[OF \<open>Ri_e \<subseteq> Q13\<close>] by (by100 blast)
          qed
          have "closure_on top1_S2 top1_S2_topology Q13 = Q13 \<union> (e12 \<union> Arc3)"
          proof -
            have hcl_W13a_l: "closure_on top1_S2 top1_S2_topology W13a = W13a \<union> (e12 \<union> Arc3)"
              by (rule hcl_scc_comp[OF hJ13_scc hW13(1,2,3,4,5,6) hW13_open[THEN conjunct1] hW13_open[THEN conjunct2]])
            have hcl_W13b_l: "closure_on top1_S2 top1_S2_topology W13b = W13b \<union> (e12 \<union> Arc3)"
            proof -
              have h1: "W13b \<inter> W13a = {}" using hW13(3) by (by100 blast)
              have h2: "W13b \<union> W13a = top1_S2 - (e12 \<union> Arc3)" using hW13(4) by (by100 blast)
              show ?thesis by (rule hcl_scc_comp[OF hJ13_scc hW13(2,1) h1 h2 hW13(6,5) hW13_open[THEN conjunct2] hW13_open[THEN conjunct1]])
            qed
            from hQ13(1) show ?thesis using hcl_W13a_l hcl_W13b_l by (by100 blast)
          qed
          hence "a3 \<in> Q13 \<union> (e12 \<union> Arc3)" using \<open>a3 \<in> closure_on _ _ Q13\<close> by (by100 blast)
          moreover have "a3 \<notin> e12" by (rule ha3_not_e12)
          moreover have "a3 \<notin> Arc3" by (rule ha3_not_Arc3)
          ultimately have "a3 \<in> Q13" by (by100 blast)
          hence "a3 \<in> R1 \<union> R2 \<union> R3" using hQ13(2) by (by100 blast)
          hence "a3 \<in> top1_S2 - (e12 \<union> Arc2 \<union> Arc3)" using hR(7) by (by100 blast)
          moreover have "a3 \<in> Arc2" using assms(20) unfolding top1_arc_endpoints_on_def defs by (by100 blast)
          ultimately show False by (by100 blast)
        qed
        \<comment> \<open>Ri\_Q12 = Ri\_Q13 (third\_element\_unique).\<close>
        have hR_dist: "R1 \<noteq> R2" "R2 \<noteq> R3" "R1 \<noteq> R3"
          using hR(1,2,3,4,5,6) by (by100 blast)+
        have hRie_ne_RiD: "Ri_e \<noteq> Ri_D"
        proof assume "Ri_e = Ri_D"
          have "e34 - {a3,a4} \<subseteq> C" by (rule he34C)
          moreover have "e34 - {a3,a4} \<subseteq> D'" using hRie(2) \<open>Ri_e = Ri_D\<close> hRiD_sub_D' by (by100 blast)
          ultimately have "e34 - {a3,a4} \<subseteq> C \<inter> D'" by (by100 blast)
          hence "e34 - {a3,a4} = {}" using hCD'_disj by (by100 blast)
          thus False using he34_ne by (by100 blast)
        qed
        have "Ri_Q12 = Ri_Q13"
          by (rule third_element_unique[OF hRie(1) hRiD \<open>Ri_Q12 \<in> _\<close> \<open>Ri_Q13 \<in> _\<close>
              hR_dist hRie_ne_RiD \<open>Ri_Q12 \<noteq> Ri_e\<close> \<open>Ri_Q12 \<noteq> Ri_D\<close>
              \<open>Ri_Q13 \<noteq> Ri_e\<close> \<open>Ri_Q13 \<noteq> Ri_D\<close>])
        \<comment> \<open>closure(Rk) = Rk\<union>J12 = Rk\<union>J13 \<Rightarrow> J12=J13 \<Rightarrow> Arc2=Arc3 \<Rightarrow> False.\<close>
        have hcl_Q12_J12: "closure_on top1_S2 top1_S2_topology Q12 = Q12 \<union> (e12 \<union> Arc2)"
        proof -
          \<comment> \<open>Q12 \<in> {W12a, W12b}. Both closures were computed in the True case.\<close>
          have hcl_W12a: "closure_on top1_S2 top1_S2_topology W12a = W12a \<union> (e12 \<union> Arc2)"
            by (rule hcl_scc_comp[OF hJ12_scc hW12(1,2,3,4,5,6) hW12_open[THEN conjunct1] hW12_open[THEN conjunct2]])
          have hcl_W12b: "closure_on top1_S2 top1_S2_topology W12b = W12b \<union> (e12 \<union> Arc2)"
          proof -
            have h1: "W12b \<inter> W12a = {}" using hW12(3) by (by100 blast)
            have h2: "W12b \<union> W12a = top1_S2 - (e12 \<union> Arc2)" using hW12(4) by (by100 blast)
            show ?thesis by (rule hcl_scc_comp[OF hJ12_scc hW12(2,1) h1 h2 hW12(6,5) hW12_open[THEN conjunct2] hW12_open[THEN conjunct1]])
          qed
          from hQ12(1) show ?thesis using hcl_W12a hcl_W12b by (by100 blast)
        qed
        have hcl_Q13_J13: "closure_on top1_S2 top1_S2_topology Q13 = Q13 \<union> (e12 \<union> Arc3)"
        proof -
          have hcl_W13a: "closure_on top1_S2 top1_S2_topology W13a = W13a \<union> (e12 \<union> Arc3)"
            by (rule hcl_scc_comp[OF hJ13_scc hW13(1,2,3,4,5,6) hW13_open[THEN conjunct1] hW13_open[THEN conjunct2]])
          have hcl_W13b: "closure_on top1_S2 top1_S2_topology W13b = W13b \<union> (e12 \<union> Arc3)"
          proof -
            have h1: "W13b \<inter> W13a = {}" using hW13(3) by (by100 blast)
            have h2: "W13b \<union> W13a = top1_S2 - (e12 \<union> Arc3)" using hW13(4) by (by100 blast)
            show ?thesis by (rule hcl_scc_comp[OF hJ13_scc hW13(2,1) h1 h2 hW13(6,5) hW13_open[THEN conjunct2] hW13_open[THEN conjunct1]])
          qed
          from hQ13(1) show ?thesis using hcl_W13a hcl_W13b by (by100 blast)
        qed
        have "e12 \<union> Arc2 = e12 \<union> Arc3"
        proof -
          have "Q12 = Q13"
          proof -
            define Rk where "Rk = Ri_Q12"
            have "Q12 \<subseteq> Rk" using \<open>Q12 \<subseteq> Ri_Q12\<close> unfolding Rk_def by (by100 blast)
            have "Q13 \<subseteq> Rk" using \<open>Q13 \<subseteq> Ri_Q13\<close> \<open>Ri_Q12 = Ri_Q13\<close> unfolding Rk_def by (by100 blast)
            have "Rk \<in> {R1,R2,R3}" using \<open>Ri_Q12 \<in> _\<close> unfolding Rk_def by (by100 blast)
            have hRk_conn: "top1_connected_on Rk (subspace_topology top1_S2 top1_S2_topology Rk)"
              using \<open>Rk \<in> _\<close> hR(8,9,10) by (by100 blast)
            have hRk_sub_theta_c: "Rk \<subseteq> top1_S2 - (e12 \<union> Arc2 \<union> Arc3)"
              using \<open>Rk \<in> _\<close> element_of_three_subset hR(7) by (by100 blast)
            \<comment> \<open>Rk \<subseteq> S2-J12. Rk \<inter> Q12 \<supseteq> Q12 \<noteq> {}. By Lemma\_23\_2: Rk \<subseteq> Q12.\<close>
            have "Rk \<subseteq> Q12"
            proof -
              have hRk_sub_J12: "Rk \<subseteq> top1_S2 - (e12 \<union> Arc2)" using hRk_sub_theta_c by (by100 blast)
              have hRk_conn_J12: "top1_connected_on Rk
                  (subspace_topology (top1_S2-(e12\<union>Arc2))
                      (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))) Rk)"
              proof -
                have "subspace_topology top1_S2 top1_S2_topology Rk =
                    subspace_topology (top1_S2-(e12\<union>Arc2))
                        (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))) Rk"
                  using subspace_topology_trans[of Rk "top1_S2-(e12\<union>Arc2)"] hRk_sub_J12 by (by100 simp)
                thus ?thesis using hRk_conn by (by100 simp)
              qed
              have hTJ12_l: "is_topology_on (top1_S2-(e12\<union>Arc2)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2)))"
                by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
              have "W12a \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))"
                using hW12_open hW12(4) unfolding subspace_topology_def by (by100 blast)
              moreover have "W12b \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))"
                using hW12_open hW12(4) unfolding subspace_topology_def by (by100 blast)
              ultimately have hSep_l: "top1_is_separation_on (top1_S2-(e12\<union>Arc2))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc2))) W12a W12b"
                unfolding top1_is_separation_on_def using hW12(1,2,3,4) by (by100 blast)
              from Lemma_23_2[OF hTJ12_l hSep_l hRk_sub_J12 hRk_conn_J12]
              have "Rk \<subseteq> W12a \<or> Rk \<subseteq> W12b" by (by100 blast)
              moreover have "Rk \<inter> Q12 \<noteq> {}" using \<open>Q12 \<subseteq> Rk\<close> hQ12(4) by (by100 blast)
              ultimately show "Rk \<subseteq> Q12" using hQ12(1) hW12(3) by (by100 blast)
            qed
            moreover have "Rk \<subseteq> Q13"
            proof -
              have hRk_sub_J13: "Rk \<subseteq> top1_S2 - (e12 \<union> Arc3)" using hRk_sub_theta_c by (by100 blast)
              have hRk_conn_J13: "top1_connected_on Rk
                  (subspace_topology (top1_S2-(e12\<union>Arc3))
                      (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))) Rk)"
              proof -
                have "subspace_topology top1_S2 top1_S2_topology Rk =
                    subspace_topology (top1_S2-(e12\<union>Arc3))
                        (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))) Rk"
                  using subspace_topology_trans[of Rk "top1_S2-(e12\<union>Arc3)"] hRk_sub_J13 by (by100 simp)
                thus ?thesis using hRk_conn by (by100 simp)
              qed
              have hTJ13_l: "is_topology_on (top1_S2-(e12\<union>Arc3)) (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3)))"
                by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
              have "W13a \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))"
                using hW13_open hW13(4) unfolding subspace_topology_def by (by100 blast)
              moreover have "W13b \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))"
                using hW13_open hW13(4) unfolding subspace_topology_def by (by100 blast)
              ultimately have hSep_l: "top1_is_separation_on (top1_S2-(e12\<union>Arc3))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2-(e12\<union>Arc3))) W13a W13b"
                unfolding top1_is_separation_on_def using hW13(1,2,3,4) by (by100 blast)
              from Lemma_23_2[OF hTJ13_l hSep_l hRk_sub_J13 hRk_conn_J13]
              have "Rk \<subseteq> W13a \<or> Rk \<subseteq> W13b" by (by100 blast)
              moreover have "Rk \<inter> Q13 \<noteq> {}" using \<open>Q13 \<subseteq> Rk\<close> hQ13(4) by (by100 blast)
              ultimately show "Rk \<subseteq> Q13" using hQ13(1) hW13(3) by (by100 blast)
            qed
            ultimately have "Rk \<subseteq> Q12 \<inter> Q13" by (by100 blast)
            moreover have "Rk \<noteq> {}" using \<open>Rk \<in> _\<close> hR(1,2,3) by (by100 blast)
            ultimately have "Q12 \<inter> Q13 \<noteq> {}" by (by100 blast)
            \<comment> \<open>Q12 = Rk = Q13.\<close>
            have "Q12 = Rk" using \<open>Q12 \<subseteq> Rk\<close> \<open>Rk \<subseteq> Q12\<close> by (by100 blast)
            moreover have "Q13 = Rk" using \<open>Q13 \<subseteq> Rk\<close> \<open>Rk \<subseteq> Q13\<close> by (by100 blast)
            ultimately show "Q12 = Q13" by (by100 blast)
          qed
          hence "Q12 \<union> (e12 \<union> Arc2) = Q13 \<union> (e12 \<union> Arc3)"
            using hcl_Q12_J12 hcl_Q13_J13 by (by100 simp)
          moreover have "Q12 \<inter> (e12 \<union> Arc2) = {}"
          proof -
            have "Q12 \<subseteq> R1 \<union> R2 \<union> R3" by (rule hQ12(2))
            hence "Q12 \<subseteq> top1_S2 - (e12 \<union> Arc2 \<union> Arc3)" using hR(7) by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
          moreover have "Q13 \<inter> (e12 \<union> Arc3) = {}"
          proof -
            have "Q13 \<subseteq> R1 \<union> R2 \<union> R3" by (rule hQ13(2))
            hence "Q13 \<subseteq> top1_S2 - (e12 \<union> Arc2 \<union> Arc3)" using hR(7) by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
          have hQ12_sub_theta: "Q12 \<subseteq> top1_S2 - (e12 \<union> Arc2 \<union> Arc3)"
            using hQ12(2) hR(7) by (by100 blast)
          have hQ12_disj_J12: "Q12 \<inter> (e12 \<union> Arc2) = {}" using hQ12_sub_theta by (by100 blast)
          have hQ12_disj_J13: "Q12 \<inter> (e12 \<union> Arc3) = {}" using hQ12_sub_theta by (by100 blast)
          have hJ_sub1: "e12 \<union> Arc2 \<subseteq> Q12 \<union> (e12 \<union> Arc3)"
            using hcl_Q12_J12 hcl_Q13_J13 \<open>Q12 = Q13\<close> by (by100 blast)
          have hJ_sub2: "e12 \<union> Arc3 \<subseteq> Q12 \<union> (e12 \<union> Arc2)"
            using hcl_Q12_J12 hcl_Q13_J13 \<open>Q12 = Q13\<close> by (by100 blast)
          have "e12 \<union> Arc2 \<subseteq> e12 \<union> Arc3"
          proof -
            { fix x assume "x \<in> e12 \<union> Arc2"
              hence "x \<in> Q12 \<union> (e12 \<union> Arc3)" using hJ_sub1 by (by100 blast)
              moreover have "x \<notin> Q12" using \<open>x \<in> e12 \<union> Arc2\<close> hQ12_disj_J12 by (by100 blast)
              ultimately have "x \<in> e12 \<union> Arc3" by (by100 blast) }
            thus ?thesis by (by100 blast)
          qed
          moreover have "e12 \<union> Arc3 \<subseteq> e12 \<union> Arc2"
          proof -
            { fix x assume "x \<in> e12 \<union> Arc3"
              hence "x \<in> Q12 \<union> (e12 \<union> Arc2)" using hJ_sub2 by (by100 blast)
              moreover have "x \<notin> Q12" using \<open>x \<in> e12 \<union> Arc3\<close> hQ12_disj_J13 by (by100 blast)
              ultimately have "x \<in> e12 \<union> Arc2" by (by100 blast) }
            thus ?thesis by (by100 blast)
          qed
          ultimately show ?thesis by (by100 blast)
        qed
        hence "Arc2 = Arc3"
        proof -
          assume hJ_eq: "e12 \<union> Arc2 = e12 \<union> Arc3"
          have "\<And>x. x \<in> Arc2 \<Longrightarrow> x \<in> Arc3"
          proof -
            fix x assume "x \<in> Arc2"
            hence "x \<in> e12 \<union> Arc3" using hJ_eq by (by100 blast)
            moreover { assume "x \<in> e12"
              hence "x \<in> {a1,a2}" using hint12 \<open>x \<in> Arc2\<close> by (by100 blast)
              hence "x \<in> Arc3" using hint13 by (by100 blast) }
            ultimately show "x \<in> Arc3" by (by100 blast)
          qed
          moreover have "\<And>x. x \<in> Arc3 \<Longrightarrow> x \<in> Arc2"
          proof -
            fix x assume "x \<in> Arc3"
            hence "x \<in> e12 \<union> Arc2" using hJ_eq by (by100 blast)
            moreover { assume "x \<in> e12"
              hence "x \<in> {a1,a2}" using hint13 \<open>x \<in> Arc3\<close> by (by100 blast)
              hence "x \<in> Arc2" using hint12 by (by100 blast) }
            ultimately show "x \<in> Arc2" by (by100 blast)
          qed
          ultimately show "Arc2 = Arc3" by (by100 blast)
        qed
        have "a3 \<in> Arc2"
          using assms(20) unfolding top1_arc_endpoints_on_def defs by (by100 blast)
        hence "a3 \<in> Arc3" using \<open>Arc2 = Arc3\<close> by (by100 blast)
        thus False using ha3_not_Arc3 by (by100 blast)
      qed
    qed
  qed
  show ?thesis
  proof (intro conjI notI)
    assume h: "e12 - {a1, a2} \<subseteq> A \<and> e34 - {a3, a4} \<subseteq> A"
    show False by (rule h_both_cases[OF assms(37,38,39) _ assms(41,42) hA_open_S2 hB_open_S2])
       (use h hAB_decomp in \<open>by100 blast\<close>)+
  next
    assume h: "e12 - {a1, a2} \<subseteq> B \<and> e34 - {a3, a4} \<subseteq> B"
    show False
    proof -
      have "A \<inter> B = {}" using assms(39) by (by100 blast)
      hence hBA: "B \<inter> A = {}" by (by100 blast)
      have hBA_union: "B \<union> A = A \<union> B" by (by100 blast)
      show ?thesis by (rule h_both_cases[OF assms(38,37) hBA hBA_union assms(42,41) hB_open_S2 hA_open_S2])
         (use h in \<open>by100 blast\<close>)+
    qed
  qed
qed


\<comment> \<open>Key lemma for 65.1(b): the K4 construction yields a loop in C that generates \<pi>_1(X).
   This is the textbook's \<alpha>*\<beta> loop. Proof: the full D1/D2/U/V construction from Lemma\_65\_1
   in AlgTop.thy (~2000 lines, oracle-clean) establishes this. We state it as a separate
   lemma to be copied/proved later.\<close>
lemma K4_generator_loop_in_C:
  fixes a1 a2 a3 a4 :: "real \<times> real \<times> real"
    and e12 e23 e34 e41 e13 e24 :: "(real \<times> real \<times> real) set"
    and C :: "(real \<times> real \<times> real) set"
    and p q :: "real \<times> real \<times> real"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "card {a1, a2, a3, a4} = 4"
      and "{a1, a2, a3, a4} \<subseteq> top1_S2"
      and "e12 \<subseteq> top1_S2" and "e23 \<subseteq> top1_S2" and "e34 \<subseteq> top1_S2"
      and "e41 \<subseteq> top1_S2" and "e13 \<subseteq> top1_S2" and "e24 \<subseteq> top1_S2"
      and "top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      and "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      and "top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      and "top1_is_arc_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
      and "top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
      and "top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
      and "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1,a2}"
      and "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2,a3}"
      and "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3,a4}"
      and "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4,a1}"
      and "top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1,a3}"
      and "top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2,a4}"
      and "e12 \<inter> e34 = {}" and "e23 \<inter> e41 = {}"
      and "e12 \<inter> e23 = {a2}" and "e23 \<inter> e34 = {a3}"
      and "e34 \<inter> e41 = {a4}" and "e41 \<inter> e12 = {a1}"
      and "e13 \<inter> e12 = {a1}" and "e13 \<inter> e23 = {a3}"
      and "e13 \<inter> e34 = {a3}" and "e13 \<inter> e41 = {a1}"
      and "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      and "e24 \<inter> e12 = {a2}" and "e24 \<inter> e23 = {a2}"
      and "e24 \<inter> e34 = {a4}" and "e24 \<inter> e41 = {a4}"
      and "p \<in> e13 - {a1, a3}" and "q \<in> e24 - {a2, a4}"
      and "C = e12 \<union> e23 \<union> e34 \<union> e41"
  shows "\<exists>x \<in> C. \<exists>g.
      top1_is_loop_on C (subspace_topology top1_S2 top1_S2_topology C) x g
    \<and> top1_is_loop_on (top1_S2 - {p} - {q})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x g
    \<and> (\<forall>f. top1_is_loop_on (top1_S2 - {p} - {q})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x f \<longrightarrow>
        (\<exists>n::nat.
            top1_path_homotopic_on (top1_S2 - {p} - {q})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x x f
              (top1_path_power g x n)
          \<or> top1_path_homotopic_on (top1_S2 - {p} - {q})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x x f
              (top1_path_power (top1_path_reverse g) x n)))"
proof -
  let ?X = "top1_S2 - {p} - {q}"
  let ?TX = "subspace_topology top1_S2 top1_S2_topology ?X"
  let ?TC = "subspace_topology top1_S2 top1_S2_topology C"
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  have hTX: "is_topology_on ?X ?TX"
    by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
  have hp_S2: "p \<in> top1_S2" using assms(8,37) by (by100 blast)
  have hq_S2: "q \<in> top1_S2" using assms(9,38) by (by100 blast)
  have hp_ne_q: "p \<noteq> q"
  proof assume "p = q"
    have "p \<in> e13" using assms(37) by (by100 blast)
    have "p \<in> e24" using \<open>p = q\<close> assms(38) by (by100 blast)
    hence "p \<in> e13 \<inter> e24" using \<open>p \<in> e13\<close> by (by100 blast)
    hence "p \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
    moreover have "p \<noteq> a1" "p \<noteq> a3" using assms(37) by (by100 blast)+
    moreover have "p \<noteq> a2" "p \<noteq> a4" using \<open>p = q\<close> assms(38) by (by100 blast)+
    ultimately show False by (by100 blast)
  qed
  have hC_sub_S2: "C \<subseteq> top1_S2" using assms(4,5,6,7,39) by (by100 blast)
  have hp_not_C: "p \<notin> C"
  proof -
    have "p \<in> e13" "p \<noteq> a1" "p \<noteq> a3" using assms(37) by (by100 blast)+
    have h1: "p \<notin> e12" using \<open>p \<in> e13\<close> \<open>p \<noteq> a1\<close> assms(28) by (by100 blast)
    have h2: "p \<notin> e23" using \<open>p \<in> e13\<close> \<open>p \<noteq> a3\<close> assms(29) by (by100 blast)
    have h3: "p \<notin> e34" using \<open>p \<in> e13\<close> \<open>p \<noteq> a3\<close> assms(30) by (by100 blast)
    have h4: "p \<notin> e41" using \<open>p \<in> e13\<close> \<open>p \<noteq> a1\<close> assms(31) by (by100 blast)
    show ?thesis using h1 h2 h3 h4 assms(39) by (by100 blast)
  qed
  have hq_not_C: "q \<notin> C"
  proof -
    have "q \<in> e24" "q \<noteq> a2" "q \<noteq> a4" using assms(38) by (by100 blast)+
    have h1: "q \<notin> e12" using \<open>q \<in> e24\<close> \<open>q \<noteq> a2\<close> assms(33) by (by100 blast)
    have h2: "q \<notin> e23" using \<open>q \<in> e24\<close> \<open>q \<noteq> a2\<close> assms(34) by (by100 blast)
    have h3: "q \<notin> e34" using \<open>q \<in> e24\<close> \<open>q \<noteq> a4\<close> assms(35) by (by100 blast)
    have h4: "q \<notin> e41" using \<open>q \<in> e24\<close> \<open>q \<noteq> a4\<close> assms(36) by (by100 blast)
    show ?thesis using h1 h2 h3 h4 assms(39) by (by100 blast)
  qed
  have hC_sub_X: "C \<subseteq> ?X" using hC_sub_S2 hp_not_C hq_not_C by (by100 blast)
  \<comment> \<open>Vertex distinctness (used in D1\<inter>D2 analysis below).\<close>
  have hdist: "a1 \<noteq> a2" "a2 \<noteq> a3" "a3 \<noteq> a4" "a4 \<noteq> a1" "a1 \<noteq> a3" "a2 \<noteq> a4"
    "a2 \<noteq> a1" "a3 \<noteq> a2" "a4 \<noteq> a3" "a1 \<noteq> a4" "a3 \<noteq> a1" "a4 \<noteq> a2"
    using assms(2) by (auto simp: card_insert_if split: if_splits)+
  \<comment> \<open>===== Following Munkres 65.1(b) EXACTLY =====
     Step A: Construct D1, D2 by splitting e13 at p and e24 at q.
     Step B: Construct specific \<alpha>, \<beta> along C edges.
     Step C: Apply Theorem 63.1 \<Rightarrow> \<alpha>*\<beta> nontrivial in X.
     Step D: \<alpha>*\<beta> generates \<pi>_1(X) (since \<pi>_1(X) infinite cyclic).
     Step E: \<alpha>*\<beta> \<in> C \<Rightarrow> j_* surjective.
     Step F: Surjective hom Z \<rightarrow> Z \<Rightarrow> injective.\<close>
  \<comment> \<open>Step A: Split e13 at p to get arcs a1-to-p and p-to-a3.
     Split e24 at q to get arcs a2-to-q and q-to-a4.
     D1 = (p-to-a3) \<union> e23 \<union> (a2-to-q): arc from p to q through a3, a2.
     D2 = (q-to-a4) \<union> e41 \<union> (a1-to-p): arc from q to p through a4, a1.\<close>
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  have hp_e13: "p \<in> e13" using assms(37) by (by100 blast)
  have hp_not_ep13: "p \<notin> top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
    using assms(37) assms(20) by (by100 blast)
  have ha1_ne_a3: "a1 \<noteq> a3" using assms(2) by (auto simp: card_insert_if split: if_splits)
  obtain D1p Da3 where hD1p_arc: "top1_is_arc_on D1p (subspace_topology top1_S2 top1_S2_topology D1p)"
      and hDa3_arc: "top1_is_arc_on Da3 (subspace_topology top1_S2 top1_S2_topology Da3)"
      and he13_split: "e13 = D1p \<union> Da3" and he13_meet: "D1p \<inter> Da3 = {p}"
      and "a1 \<in> D1p" "a3 \<in> Da3" "p \<in> D1p" "p \<in> Da3"
      and "D1p \<subseteq> top1_S2" "Da3 \<subseteq> top1_S2"
    using arc_split_at_given_point[OF assms(1) hS2_haus assms(8) assms(14)
          hp_e13 hp_not_ep13 assms(20) ha1_ne_a3] by blast
  have hq_e24: "q \<in> e24" using assms(38) by (by100 blast)
  have hq_not_ep24: "q \<notin> top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
    using assms(38) assms(21) by (by100 blast)
  have ha2_ne_a4: "a2 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
  obtain Da2 Dq4 where hDa2_arc: "top1_is_arc_on Da2 (subspace_topology top1_S2 top1_S2_topology Da2)"
      and hDq4_arc: "top1_is_arc_on Dq4 (subspace_topology top1_S2 top1_S2_topology Dq4)"
      and he24_split: "e24 = Da2 \<union> Dq4" and he24_meet: "Da2 \<inter> Dq4 = {q}"
      and "a2 \<in> Da2" "a4 \<in> Dq4" "q \<in> Da2" "q \<in> Dq4"
      and "Da2 \<subseteq> top1_S2" "Dq4 \<subseteq> top1_S2"
    using arc_split_at_given_point[OF assms(1) hS2_haus assms(9) assms(15)
          hq_e24 hq_not_ep24 assms(21) ha2_ne_a4] by blast
  \<comment> \<open>D1 = Da3 \<union> e23 \<union> Da2 (arc from p through a3, a2 to q).
     D2 = Dq4 \<union> e41 \<union> D1p (arc from q through a4, a1 to p).\<close>
  let ?D1 = "Da3 \<union> e23 \<union> Da2"
  let ?D2 = "Dq4 \<union> e41 \<union> D1p"
  let ?U_loc = "top1_S2 - ?D1"
  let ?V_loc = "top1_S2 - ?D2"
  \<comment> \<open>Step B: Get interior points x \<in> e12 and y \<in> e34.\<close>
  obtain x e12a e12b where hx_e12: "x \<in> e12" and he12_eq: "e12 = e12a \<union> e12b"
      and he12_meet: "e12a \<inter> e12b = {x}"
      and he12a_arc: "top1_is_arc_on e12a (subspace_topology top1_S2 top1_S2_topology e12a)"
      and he12b_arc: "top1_is_arc_on e12b (subspace_topology top1_S2 top1_S2_topology e12b)"
    using arc_split_at_midpoint[OF assms(1) hS2_haus assms(4) assms(10)] by blast
  obtain y e34a e34b where hy_e34: "y \<in> e34" and he34_eq: "e34 = e34a \<union> e34b"
      and he34_meet: "e34a \<inter> e34b = {y}"
      and he34a_arc: "top1_is_arc_on e34a (subspace_topology top1_S2 top1_S2_topology e34a)"
      and he34b_arc: "top1_is_arc_on e34b (subspace_topology top1_S2 top1_S2_topology e34b)"
    using arc_split_at_midpoint[OF assms(1) hS2_haus assms(6) assms(12)] by blast
  \<comment> \<open>Step B2: x \<notin> {a1, a2} and y \<notin> {a3, a4} (interior points of arcs).\<close>
  \<comment> \<open>x is an interior point of e12 (not an endpoint). From arc\_split\_at\_midpoint:
     e12 = e12a \<union> e12b, e12a \<inter> e12b = {x}. Removing x disconnects e12
     (e12a-{x} and e12b-{x} are nonempty disjoint clopen pieces).
     Since endpoints = {p | A-{p} connected}, x is not an endpoint.\<close>
  \<comment> \<open>Helper: arcs have \<ge> 2 points (bijective image of [0,1]).\<close>
  {
    fix A :: "(real \<times> real \<times> real) set" and TA and z
    assume harc: "top1_is_arc_on A TA"
    then obtain hf where hhf: "top1_homeomorphism_on I_set I_top A TA hf"
      unfolding top1_is_arc_on_def by (by100 blast)
    have hbij: "bij_betw hf I_set A"
      using hhf unfolding top1_homeomorphism_on_def by (by100 blast)
    have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have "hf 0 \<in> A" using hbij h0_I unfolding bij_betw_def by (by100 blast)
    moreover have "hf 1 \<in> A" using hbij h1_I unfolding bij_betw_def by (by100 blast)
    moreover have "hf 0 \<noteq> hf 1"
    proof -
      have "inj_on hf I_set" using hbij unfolding bij_betw_def by (by100 blast)
      thus ?thesis using h0_I h1_I unfolding inj_on_def by (by100 fastforce)
    qed
    ultimately have "A \<noteq> {z}" by (by100 fastforce)
  } note arc_not_singleton = this
  have hx_not_endpts: "x \<noteq> a1 \<and> x \<noteq> a2"
  proof (intro conjI notI)
    \<comment> \<open>Key: if x were an endpoint, arc\_both\_endpoints\_in\_one\_part forces one sub-arc
       to be a singleton, but arcs have \<ge> 2 points (homeomorphic to [0,1]).\<close>
    have ha1_ne_a2: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha2_e12: "a2 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha1_e12: "a1 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have he12a_sub: "e12a \<subseteq> top1_S2" using he12_eq assms(4) by (by100 blast)
    have he12b_sub: "e12b \<subseteq> top1_S2" using he12_eq assms(4) by (by100 blast)
    have he12a_conn: "top1_connected_on e12a (subspace_topology top1_S2 top1_S2_topology e12a)"
      using arc_connected[OF he12a_arc] .
    have he12b_conn: "top1_connected_on e12b (subspace_topology top1_S2 top1_S2_topology e12b)"
      using arc_connected[OF he12b_arc] .
    assume "x = a1"
    hence ha1_e12a: "a1 \<in> e12a" and ha1_e12b: "a1 \<in> e12b"
      using he12_meet by (by100 blast)+
    have "a2 \<in> e12a \<or> a2 \<in> e12b" using ha2_e12 he12_eq by (by100 blast)
    thus False
    proof
      assume "a2 \<in> e12a"
      have "e12b = {x}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(4) assms(10)
              he12_eq he12_meet he12a_conn he12a_sub assms(16) ha1_ne_a2 ha1_e12a \<open>a2 \<in> e12a\<close>])
      thus False using arc_not_singleton[OF he12b_arc, of x] by (by100 simp)
    next
      assume "a2 \<in> e12b"
      have he12_eq': "e12 = e12b \<union> e12a" using he12_eq by (by100 blast)
      have he12_meet': "e12b \<inter> e12a = {x}" using he12_meet by (by100 blast)
      have "e12a = {x}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(4) assms(10)
              he12_eq' he12_meet' he12b_conn he12b_sub assms(16) ha1_ne_a2 ha1_e12b \<open>a2 \<in> e12b\<close>])
      thus False using arc_not_singleton[OF he12a_arc, of x] by (by100 simp)
    qed
  next
    assume "x = a2"
    have ha1_ne_a2: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha2_e12a: "a2 \<in> e12a" and ha2_e12b: "a2 \<in> e12b"
      using \<open>x = a2\<close> he12_meet by (by100 blast)+
    have ha1_e12: "a1 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have he12a_sub: "e12a \<subseteq> top1_S2" using he12_eq assms(4) by (by100 blast)
    have he12b_sub: "e12b \<subseteq> top1_S2" using he12_eq assms(4) by (by100 blast)
    have he12a_conn: "top1_connected_on e12a (subspace_topology top1_S2 top1_S2_topology e12a)"
      using arc_connected[OF he12a_arc] .
    have he12b_conn: "top1_connected_on e12b (subspace_topology top1_S2 top1_S2_topology e12b)"
      using arc_connected[OF he12b_arc] .
    have "a1 \<in> e12a \<or> a1 \<in> e12b" using ha1_e12 he12_eq by (by100 blast)
    thus False
    proof
      assume "a1 \<in> e12a"
      have he12_eq': "e12 = e12a \<union> e12b" using he12_eq by (by100 blast)
      have he12_meet': "e12a \<inter> e12b = {x}" using he12_meet by (by100 blast)
      have "e12b = {x}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(4) assms(10)
              he12_eq' he12_meet' he12a_conn he12a_sub assms(16) ha1_ne_a2 \<open>a1 \<in> e12a\<close> ha2_e12a])
      thus False using arc_not_singleton[OF he12b_arc, of x] by (by100 simp)
    next
      assume "a1 \<in> e12b"
      have he12_eq': "e12 = e12b \<union> e12a" using he12_eq by (by100 blast)
      have he12_meet': "e12b \<inter> e12a = {x}" using he12_meet by (by100 blast)
      have "e12a = {x}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(4) assms(10)
              he12_eq' he12_meet' he12b_conn he12b_sub assms(16) ha1_ne_a2 \<open>a1 \<in> e12b\<close> ha2_e12b])
      thus False using arc_not_singleton[OF he12a_arc, of x] by (by100 simp)
    qed
  qed
  have hy_not_endpts: "y \<noteq> a3 \<and> y \<noteq> a4"
  proof (intro conjI notI)
    have ha3_ne_a4: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha4_e34: "a4 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha3_e34: "a3 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have he34a_sub: "e34a \<subseteq> top1_S2" using he34_eq assms(6) by (by100 blast)
    have he34b_sub: "e34b \<subseteq> top1_S2" using he34_eq assms(6) by (by100 blast)
    have he34a_conn: "top1_connected_on e34a (subspace_topology top1_S2 top1_S2_topology e34a)"
      using arc_connected[OF he34a_arc] .
    have he34b_conn: "top1_connected_on e34b (subspace_topology top1_S2 top1_S2_topology e34b)"
      using arc_connected[OF he34b_arc] .
    assume "y = a3"
    hence ha3_e34a: "a3 \<in> e34a" and ha3_e34b: "a3 \<in> e34b"
      using he34_meet by (by100 blast)+
    have "a4 \<in> e34a \<or> a4 \<in> e34b" using ha4_e34 he34_eq by (by100 blast)
    thus False
    proof
      assume "a4 \<in> e34a"
      have "e34b = {y}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(6) assms(12)
              he34_eq he34_meet he34a_conn he34a_sub assms(18) ha3_ne_a4 ha3_e34a \<open>a4 \<in> e34a\<close>])
      thus False using arc_not_singleton[OF he34b_arc, of y] by (by100 simp)
    next
      assume "a4 \<in> e34b"
      have he34_eq': "e34 = e34b \<union> e34a" using he34_eq by (by100 blast)
      have he34_meet': "e34b \<inter> e34a = {y}" using he34_meet by (by100 blast)
      have "e34a = {y}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(6) assms(12)
              he34_eq' he34_meet' he34b_conn he34b_sub assms(18) ha3_ne_a4 ha3_e34b \<open>a4 \<in> e34b\<close>])
      thus False using arc_not_singleton[OF he34a_arc, of y] by (by100 simp)
    qed
  next
    assume "y = a4"
    have ha3_ne_a4: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha4_e34a: "a4 \<in> e34a" and ha4_e34b: "a4 \<in> e34b"
      using \<open>y = a4\<close> he34_meet by (by100 blast)+
    have ha3_e34: "a3 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have he34a_sub: "e34a \<subseteq> top1_S2" using he34_eq assms(6) by (by100 blast)
    have he34b_sub: "e34b \<subseteq> top1_S2" using he34_eq assms(6) by (by100 blast)
    have he34a_conn: "top1_connected_on e34a (subspace_topology top1_S2 top1_S2_topology e34a)"
      using arc_connected[OF he34a_arc] .
    have he34b_conn: "top1_connected_on e34b (subspace_topology top1_S2 top1_S2_topology e34b)"
      using arc_connected[OF he34b_arc] .
    have "a3 \<in> e34a \<or> a3 \<in> e34b" using ha3_e34 he34_eq by (by100 blast)
    thus False
    proof
      assume "a3 \<in> e34a"
      have he34_eq': "e34 = e34a \<union> e34b" using he34_eq by (by100 blast)
      have he34_meet': "e34a \<inter> e34b = {y}" using he34_meet by (by100 blast)
      have "e34b = {y}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(6) assms(12)
              he34_eq' he34_meet' he34a_conn he34a_sub assms(18) ha3_ne_a4 \<open>a3 \<in> e34a\<close> ha4_e34a])
      thus False using arc_not_singleton[OF he34b_arc, of y] by (by100 simp)
    next
      assume "a3 \<in> e34b"
      have he34_eq': "e34 = e34b \<union> e34a" using he34_eq by (by100 blast)
      have he34_meet': "e34b \<inter> e34a = {y}" using he34_meet by (by100 blast)
      have "e34a = {y}"
        by (rule arc_both_endpoints_in_one_part[OF assms(1) hS2_haus assms(6) assms(12)
              he34_eq' he34_meet' he34b_conn he34b_sub assms(18) ha3_ne_a4 \<open>a3 \<in> e34b\<close> ha4_e34b])
      thus False using arc_not_singleton[OF he34a_arc, of y] by (by100 simp)
    qed
  qed
  \<comment> \<open>Step B3: C - D1 is path-connected and contains x, y.
     C - D1 = (e12-{a2}) \<union> e41 \<union> (e34-{a3}). Connected chain via a1, a4.
     x \<in> e12-{a2} (x interior), y \<in> e34-{a3} (y interior).
     So \<exists>\<alpha>: path from x to y in C \<inter> U.\<close>
  have hx_in_CmD1: "x \<in> C - ?D1"
  proof -
    have "x \<in> C" using hx_e12 assms(39) by (by100 blast)
    moreover have "x \<notin> Da3"
    proof -
      have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
      hence "e12 \<inter> Da3 \<subseteq> e12 \<inter> e13" by (by100 blast)
      hence h_sub: "e12 \<inter> Da3 \<subseteq> {a1}" using assms(28) by (by100 blast)
      have "a1 \<noteq> p" using assms(37) by (by100 blast)
      have "a1 \<notin> Da3" using \<open>a1 \<in> D1p\<close> he13_meet \<open>a1 \<noteq> p\<close> by (by100 blast)
      have "e12 \<inter> Da3 = {}" using h_sub \<open>a1 \<notin> Da3\<close> by (by100 blast)
      thus ?thesis using hx_e12 by (by100 blast)
    qed
    moreover have "x \<notin> e23" using hx_e12 hx_not_endpts assms(24) by (by100 blast)
    moreover have "x \<notin> Da2"
    proof -
      have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e12 \<inter> Da2 \<subseteq> e12 \<inter> e24" by (by100 blast)
      hence "e12 \<inter> Da2 \<subseteq> {a2}" using assms(33) by (by100 blast)
      thus ?thesis using hx_e12 hx_not_endpts by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  have hy_in_CmD1: "y \<in> C - ?D1"
  proof -
    have "y \<in> C" using hy_e34 assms(39) by (by100 blast)
    moreover have "y \<notin> Da3"
    proof -
      have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
      hence "e34 \<inter> Da3 \<subseteq> e34 \<inter> e13" by (by100 blast)
      hence "e34 \<inter> Da3 \<subseteq> {a3}" using assms(30) by (by100 blast)
      thus ?thesis using hy_e34 hy_not_endpts by (by100 blast)
    qed
    moreover have "y \<notin> e23" using hy_e34 hy_not_endpts assms(25) by (by100 blast)
    moreover have "y \<notin> Da2"
    proof -
      have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e34 \<inter> Da2 \<subseteq> e34 \<inter> e24" by (by100 blast)
      hence h_sub: "e34 \<inter> Da2 \<subseteq> {a4}" using assms(35) by (by100 blast)
      have "a4 \<noteq> q" using assms(38) by (by100 blast)
      have "a4 \<notin> Da2" using \<open>a4 \<in> Dq4\<close> he24_meet \<open>a4 \<noteq> q\<close> by (by100 blast)
      have "e34 \<inter> Da2 = {}" using h_sub \<open>a4 \<notin> Da2\<close> by (by100 blast)
      thus ?thesis using hy_e34 by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Helper: arcs in S2 are path-connected (from homeomorphism with [0,1]).\<close>
  {
    fix D :: "(real \<times> real \<times> real) set" and TD
    assume harc_loc: "top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D)"
        and hD_sub: "D \<subseteq> top1_S2"
    have "top1_path_connected_on D (subspace_topology top1_S2 top1_S2_topology D)"
    proof -
      obtain hf where hhf: "top1_homeomorphism_on I_set I_top D
          (subspace_topology top1_S2 top1_S2_topology D) hf"
        using harc_loc unfolding top1_is_arc_on_def by (by100 blast)
      have "top1_path_connected_on I_set I_top"
      proof (unfold top1_path_connected_on_def, intro conjI ballI)
        show "is_topology_on I_set I_top"
          unfolding top1_unit_interval_topology_def
          by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV])
             (by100 simp)
        fix a b :: real assume ha: "a \<in> I_set" and hb: "b \<in> I_set"
        let ?g = "\<lambda>t::real. (1-t)*a + t*b"
        have hg_cont: "continuous_on UNIV ?g" by (intro continuous_intros)
        have hg_map: "\<And>t. t \<in> I_set \<Longrightarrow> ?g t \<in> I_set"
        proof -
          fix t :: real assume ht: "t \<in> I_set"
          have "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
          have "0 \<le> a" "a \<le> 1" using ha unfolding top1_unit_interval_def by auto
          have "0 \<le> b" "b \<le> 1" using hb unfolding top1_unit_interval_def by auto
          have h0: "0 \<le> (1-t)*a" using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> \<open>0 \<le> a\<close>
            using mult_nonneg_nonneg by (by100 fastforce)
          have h1: "0 \<le> t*b" using \<open>0 \<le> t\<close> \<open>0 \<le> b\<close>
            using mult_nonneg_nonneg by (by100 fastforce)
          have "0 \<le> (1-t)*a + t*b" using h0 h1 by (by100 simp)
          moreover have "(1-t)*a + t*b \<le> 1"
          proof -
            have "(1-t)*a \<le> (1-t)*1" using \<open>a \<le> 1\<close> \<open>0 \<le> t\<close> \<open>t \<le> 1\<close>
              using mult_left_mono by (by100 fastforce)
            moreover have "t*b \<le> t*1" using \<open>b \<le> 1\<close> \<open>0 \<le> t\<close>
              using mult_left_mono by (by100 fastforce)
            ultimately show ?thesis by (by100 simp)
          qed
          ultimately show "?g t \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        qed
        have hg_top: "top1_continuous_map_on I_set I_top I_set I_top ?g"
        proof -
          have "top1_continuous_map_on I_set
              (subspace_topology UNIV top1_open_sets I_set)
              I_set (subspace_topology UNIV top1_open_sets I_set) ?g"
            by (rule top1_continuous_map_on_real_subspace_open_sets[OF hg_map hg_cont])
          thus ?thesis unfolding top1_unit_interval_topology_def .
        qed
        have "?g 0 = a" by (by100 simp)
        moreover have "?g 1 = b" by (by100 simp)
        ultimately have "top1_is_path_on I_set I_top a b ?g"
          unfolding top1_is_path_on_def using hg_top by (by100 blast)
        thus "\<exists>f. top1_is_path_on I_set I_top a b f" by (by100 blast)
      qed
      thus ?thesis by (rule homeomorphism_preserves_path_connected[OF hhf])
    qed
  } note arc_path_connected = this
  \<comment> \<open>Helper: arc minus one endpoint is path-connected.\<close>
  {
    fix D :: "(real \<times> real \<times> real) set" and ep
    assume harc_loc: "top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D)"
        and hD_sub: "D \<subseteq> top1_S2"
        and hep: "ep \<in> top1_arc_endpoints_on D (subspace_topology top1_S2 top1_S2_topology D)"
    have "top1_path_connected_on (D - {ep}) (subspace_topology top1_S2 top1_S2_topology (D - {ep}))"
    proof -
      obtain hf where hhf: "top1_homeomorphism_on I_set I_top D
          (subspace_topology top1_S2 top1_S2_topology D) hf"
        using harc_loc unfolding top1_is_arc_on_def by (by100 blast)
      have hbij: "bij_betw hf I_set D"
        using hhf unfolding top1_homeomorphism_on_def by (by100 blast)
      have hinj: "inj_on hf I_set" using hbij unfolding bij_betw_def by (by100 blast)
      have hsurj: "hf ` I_set = D" using hbij unfolding bij_betw_def by (by100 blast)
      have hcont: "top1_continuous_map_on I_set I_top D
          (subspace_topology top1_S2 top1_S2_topology D) hf"
        using hhf unfolding top1_homeomorphism_on_def by (by100 blast)
      \<comment> \<open>ep = hf(0) or ep = hf(1) (endpoints are boundary of [0,1]).\<close>
      have hep_bd: "top1_arc_endpoints_on D
          (subspace_topology top1_S2 top1_S2_topology D) = {hf 0, hf 1}"
        by (rule arc_endpoints_are_boundary[OF assms(1) hS2_haus hD_sub harc_loc hhf])
      have hep_01: "ep = hf 0 \<or> ep = hf 1" using hep hep_bd by (by100 blast)
      \<comment> \<open>Define tb = hf\<inverse>(ep) \<in> {0, 1}.\<close>
      define tb where "tb = inv_into I_set hf ep"
      have hep_D: "ep \<in> D" using hep unfolding top1_arc_endpoints_on_def by (by100 blast)
      have hep_img: "ep \<in> hf ` I_set" using hep_D hsurj by (by100 blast)
      have htb_I: "tb \<in> I_set" unfolding tb_def
        using inv_into_into[OF hep_img] by (by100 blast)
      have hftb: "hf tb = ep" unfolding tb_def
        using f_inv_into_f[OF hep_img] by (by100 blast)
      have htb_01: "tb = 0 \<or> tb = 1"
      proof -
        have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        from hep_01 show ?thesis
        proof
          assume "ep = hf 0"
          hence "hf tb = hf 0" using hftb by (by100 simp)
          thus ?thesis using hinj htb_I h0_I unfolding inj_on_def by (by100 blast)
        next
          assume "ep = hf 1"
          hence "hf tb = hf 1" using hftb by (by100 simp)
          thus ?thesis using hinj htb_I h1_I unfolding inj_on_def by (by100 blast)
        qed
      qed
      \<comment> \<open>Path-connected: for u, v \<in> D-{ep}, use affine path avoiding tb.\<close>
      show ?thesis unfolding top1_path_connected_on_def
      proof (intro conjI ballI)
        show "is_topology_on (D - {ep}) (subspace_topology top1_S2 top1_S2_topology (D - {ep}))"
          by (rule subspace_topology_is_topology_on[OF
              is_topology_on_strict_imp[OF assms(1)]]) (use hD_sub in \<open>by100 blast\<close>)
        fix u v assume hu: "u \<in> D - {ep}" and hv: "v \<in> D - {ep}"
        define su where "su = inv_into I_set hf u"
        define sv where "sv = inv_into I_set hf v"
        have hu_img: "u \<in> hf ` I_set" using hu hsurj by (by100 blast)
        have hv_img: "v \<in> hf ` I_set" using hv hsurj by (by100 blast)
        have hsu_I: "su \<in> I_set" unfolding su_def
          using inv_into_into[OF hu_img] by (by100 blast)
        have hsv_I: "sv \<in> I_set" unfolding sv_def
          using inv_into_into[OF hv_img] by (by100 blast)
        have hfsu: "hf su = u" unfolding su_def
          using f_inv_into_f[OF hu_img] by (by100 blast)
        have hfsv: "hf sv = v" unfolding sv_def
          using f_inv_into_f[OF hv_img] by (by100 blast)
        have hsu_ne_tb: "su \<noteq> tb" using hu hfsu hftb hinj hsu_I htb_I
          unfolding inj_on_def by (by100 blast)
        have hsv_ne_tb: "sv \<noteq> tb" using hv hfsv hftb hinj hsv_I htb_I
          unfolding inj_on_def by (by100 blast)
        \<comment> \<open>Affine path stays in I\_set and avoids tb (convexity of [0,1)-or-(0,1]).\<close>
        let ?g = "\<lambda>t::real. (1-t)*su + t*sv"
        have hg_in_I: "\<And>t. t \<in> I_set \<Longrightarrow> ?g t \<in> I_set"
        proof -
          fix t :: real assume ht: "t \<in> I_set"
          have "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
          have "0 \<le> su" "su \<le> 1" using hsu_I unfolding top1_unit_interval_def by auto
          have "0 \<le> sv" "sv \<le> 1" using hsv_I unfolding top1_unit_interval_def by auto
          have h0: "0 \<le> (1-t)*su" using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> \<open>0 \<le> su\<close>
            using mult_nonneg_nonneg by (by100 fastforce)
          have h1: "0 \<le> t*sv" using \<open>0 \<le> t\<close> \<open>0 \<le> sv\<close>
            using mult_nonneg_nonneg by (by100 fastforce)
          have hge: "0 \<le> ?g t" using h0 h1 by (by100 simp)
          have "(1-t)*su \<le> (1-t)*1" using \<open>su \<le> 1\<close> \<open>0 \<le> t\<close> \<open>t \<le> 1\<close>
            using mult_left_mono by (by100 fastforce)
          moreover have "t*sv \<le> t*1" using \<open>sv \<le> 1\<close> \<open>0 \<le> t\<close>
            using mult_left_mono by (by100 fastforce)
          ultimately have hle: "?g t \<le> 1" by (by100 simp)
          show "?g t \<in> I_set" unfolding top1_unit_interval_def using hge hle by (by100 simp)
        qed
        have hg_ne_tb: "\<And>t. t \<in> I_set \<Longrightarrow> ?g t \<noteq> tb"
        proof -
          fix t :: real assume ht: "t \<in> I_set"
          have "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
          have "0 \<le> su" "su \<le> 1" using hsu_I unfolding top1_unit_interval_def by auto
          have "0 \<le> sv" "sv \<le> 1" using hsv_I unfolding top1_unit_interval_def by auto
          \<comment> \<open>tb \<in> {0, 1}. su \<noteq> tb, sv \<noteq> tb. Convex combo avoids tb.\<close>
          from htb_01 show "?g t \<noteq> tb"
          proof
            assume "tb = 0"
            \<comment> \<open>su > 0 and sv > 0 (since su \<noteq> 0, sv \<noteq> 0, both \<ge> 0).\<close>
            have "su > 0" using hsu_ne_tb \<open>tb = 0\<close> \<open>0 \<le> su\<close> by (by100 simp)
            have "sv > 0" using hsv_ne_tb \<open>tb = 0\<close> \<open>0 \<le> sv\<close> by (by100 simp)
            have "(1-t)*su \<ge> 0" using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> \<open>su > 0\<close>
              using mult_nonneg_nonneg by (by100 fastforce)
            have "t*sv \<ge> 0" using \<open>0 \<le> t\<close> \<open>sv > 0\<close>
              using mult_nonneg_nonneg by (by100 fastforce)
            \<comment> \<open>At least one of (1-t)*su > 0 or t*sv > 0.\<close>
            have "(1-t)*su > 0 \<or> t*sv > 0"
            proof (cases "t = 1")
              case True thus ?thesis using \<open>sv > 0\<close> by (by100 simp)
            next
              case False
              hence "1 - t > 0" using \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> by (by100 simp)
              thus ?thesis using \<open>su > 0\<close> by (by100 simp)
            qed
            hence "(1-t)*su + t*sv > 0" using \<open>(1-t)*su \<ge> 0\<close> \<open>t*sv \<ge> 0\<close>
              by (by100 linarith)
            thus "?g t \<noteq> tb" using \<open>tb = 0\<close> by (by100 simp)
          next
            assume "tb = 1"
            \<comment> \<open>su < 1 and sv < 1 (since su \<noteq> 1, sv \<noteq> 1, both \<le> 1).\<close>
            have "su < 1" using hsu_ne_tb \<open>tb = 1\<close> \<open>su \<le> 1\<close> by (by100 simp)
            have "sv < 1" using hsv_ne_tb \<open>tb = 1\<close> \<open>sv \<le> 1\<close> by (by100 simp)
            have "?g t < 1"
            proof (cases "t = 0")
              case True thus ?thesis using \<open>su < 1\<close> by (by100 simp)
            next
              case False
              hence "t > 0" using \<open>0 \<le> t\<close> by (by100 simp)
              have "(1-t)*su \<le> (1-t)" using \<open>su \<le> 1\<close> \<open>0 \<le> t\<close> \<open>t \<le> 1\<close>
                using mult_left_le by (by100 fastforce)
              moreover have "t*sv < t" using \<open>sv < 1\<close> \<open>t > 0\<close>
                by (by100 simp)
              ultimately show ?thesis by (by100 linarith)
            qed
            thus "?g t \<noteq> tb" using \<open>tb = 1\<close> by (by100 simp)
          qed
        qed
        \<comment> \<open>Construct path: hf \<circ> g.\<close>
        let ?path = "hf \<circ> ?g"
        have hpath_in: "\<forall>s\<in>I_set. ?path s \<in> D - {ep}"
        proof (intro ballI)
          fix t assume ht: "t \<in> I_set"
          have "?g t \<in> I_set" by (rule hg_in_I[OF ht])
          have "?g t \<noteq> tb" by (rule hg_ne_tb[OF ht])
          have "hf (?g t) \<in> D" using \<open>?g t \<in> I_set\<close> hsurj by (by100 blast)
          moreover have "hf (?g t) \<noteq> ep"
            using \<open>?g t \<noteq> tb\<close> \<open>?g t \<in> I_set\<close> htb_I hftb hinj
            unfolding inj_on_def by (by100 blast)
          ultimately show "?path t \<in> D - {ep}" by (by100 simp)
        qed
        \<comment> \<open>Continuity: g continuous I \<rightarrow> I, hf continuous I \<rightarrow> D, compose + restrict codomain.\<close>
        have hg_cont_UNIV: "continuous_on UNIV ?g" by (intro continuous_intros)
        have hg_map: "\<And>t. t \<in> I_set \<Longrightarrow> ?g t \<in> I_set" by (rule hg_in_I)
        have hg_cont: "top1_continuous_map_on I_set I_top I_set I_top ?g"
        proof -
          have "top1_continuous_map_on I_set
              (subspace_topology UNIV top1_open_sets I_set)
              I_set (subspace_topology UNIV top1_open_sets I_set) ?g"
            by (rule top1_continuous_map_on_real_subspace_open_sets[OF hg_map hg_cont_UNIV])
          thus ?thesis unfolding top1_unit_interval_topology_def .
        qed
        have hpath_cont_D: "top1_continuous_map_on I_set I_top D
            (subspace_topology top1_S2 top1_S2_topology D) ?path"
          unfolding comp_def
          by (rule top1_continuous_map_on_comp[OF hg_cont hcont, simplified comp_def])
        have hpath_cont_sub: "top1_continuous_map_on I_set I_top (D - {ep})
            (subspace_topology D (subspace_topology top1_S2 top1_S2_topology D) (D - {ep})) ?path"
          by (rule continuous_map_restrict_codomain[OF hpath_cont_D])
             (use hpath_in in \<open>by100 blast\<close>)+
        have hT_eq: "subspace_topology D (subspace_topology top1_S2 top1_S2_topology D) (D - {ep})
            = subspace_topology top1_S2 top1_S2_topology (D - {ep})"
          by (rule subspace_topology_trans) (by100 blast)
        have hpath_cont: "top1_continuous_map_on I_set I_top (D - {ep})
            (subspace_topology top1_S2 top1_S2_topology (D - {ep})) ?path"
          using hpath_cont_sub hT_eq by (by100 simp)
        have "?path 0 = u" using hfsu by (by100 simp)
        moreover have "?path 1 = v" using hfsv by (by100 simp)
        ultimately have "top1_is_path_on (D - {ep})
            (subspace_topology top1_S2 top1_S2_topology (D - {ep})) u v ?path"
          unfolding top1_is_path_on_def using hpath_cont by (by100 blast)
        thus "\<exists>f. top1_is_path_on (D - {ep})
            (subspace_topology top1_S2 top1_S2_topology (D - {ep})) u v f" by (by100 blast)
      qed
    qed
  } note arc_minus_endpoint_pc = this
  \<comment> \<open>C - D1 path-connected: chain (e12 - {a2}) \<union> e41 \<union> (e34 - {a3}) at vertices a1, a4.\<close>
  have hCmD1_pc: "top1_path_connected_on (C - ?D1)
      (subspace_topology top1_S2 top1_S2_topology (C - ?D1))"
  proof -
    \<comment> \<open>Set equality.\<close>
    have hset: "C - ?D1 = (e12 - {a2}) \<union> e41 \<union> (e34 - {a3})"
    proof -
      \<comment> \<open>C = e12 \<union> e23 \<union> e34 \<union> e41. D1 = Da3 \<union> e23 \<union> Da2.\<close>
      have "e12 \<inter> Da3 = {}"
      proof -
        have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
        hence "e12 \<inter> Da3 \<subseteq> e12 \<inter> e13" by (by100 blast)
        hence "e12 \<inter> Da3 \<subseteq> {a1}" using assms(28) by (by100 blast)
        have "a1 \<noteq> p" using assms(37) by (by100 blast)
        have "a1 \<notin> Da3" using \<open>a1 \<in> D1p\<close> he13_meet \<open>a1 \<noteq> p\<close> by (by100 blast)
        thus ?thesis using \<open>e12 \<inter> Da3 \<subseteq> {a1}\<close> \<open>a1 \<notin> Da3\<close> by (by100 blast)
      qed
      have "e12 \<inter> Da2 \<subseteq> {a2}"
      proof -
        have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e12 \<inter> Da2 \<subseteq> e12 \<inter> e24" by (by100 blast)
        thus ?thesis using assms(33) by (by100 blast)
      qed
      have "e41 \<inter> Da3 = {}"
      proof -
        have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
        hence "e41 \<inter> Da3 \<subseteq> e41 \<inter> e13" by (by100 blast)
        hence "e41 \<inter> Da3 \<subseteq> {a1}" using assms(31) by (by100 blast)
        have "a1 \<noteq> p" using assms(37) by (by100 blast)
        have "a1 \<notin> Da3" using \<open>a1 \<in> D1p\<close> he13_meet \<open>a1 \<noteq> p\<close> by (by100 blast)
        thus ?thesis using \<open>e41 \<inter> Da3 \<subseteq> {a1}\<close> \<open>a1 \<notin> Da3\<close> by (by100 blast)
      qed
      have "e41 \<inter> Da2 = {}"
      proof -
        have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e41 \<inter> Da2 \<subseteq> e41 \<inter> e24" by (by100 blast)
        hence "e41 \<inter> Da2 \<subseteq> {a4}" using assms(36) by (by100 blast)
        have "a4 \<noteq> q" using assms(38) by (by100 blast)
        have "a4 \<notin> Da2" using \<open>a4 \<in> Dq4\<close> he24_meet \<open>a4 \<noteq> q\<close> by (by100 blast)
        thus ?thesis using \<open>e41 \<inter> Da2 \<subseteq> {a4}\<close> \<open>a4 \<notin> Da2\<close> by (by100 blast)
      qed
      have "e34 \<inter> Da2 = {}"
      proof -
        have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e34 \<inter> Da2 \<subseteq> e34 \<inter> e24" by (by100 blast)
        hence "e34 \<inter> Da2 \<subseteq> {a4}" using assms(35) by (by100 blast)
        have "a4 \<noteq> q" using assms(38) by (by100 blast)
        have "a4 \<notin> Da2" using \<open>a4 \<in> Dq4\<close> he24_meet \<open>a4 \<noteq> q\<close> by (by100 blast)
        thus ?thesis using \<open>e34 \<inter> Da2 \<subseteq> {a4}\<close> \<open>a4 \<notin> Da2\<close> by (by100 blast)
      qed
      have "e34 \<inter> Da3 \<subseteq> {a3}"
      proof -
        have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
        hence "e34 \<inter> Da3 \<subseteq> e34 \<inter> e13" by (by100 blast)
        thus ?thesis using assms(30) by (by100 blast)
      qed
      have "e12 - ?D1 = e12 - {a2}"
        using assms(24) \<open>e12 \<inter> Da3 = {}\<close> \<open>e12 \<inter> Da2 \<subseteq> {a2}\<close> by (by100 blast)
      moreover have "e23 - ?D1 = {}" by (by100 blast)
      moreover have "e41 - ?D1 = e41"
        using assms(23) \<open>e41 \<inter> Da3 = {}\<close> \<open>e41 \<inter> Da2 = {}\<close> by (by100 blast)
      moreover have "e34 - ?D1 = e34 - {a3}"
        using assms(25) \<open>e34 \<inter> Da2 = {}\<close> \<open>e34 \<inter> Da3 \<subseteq> {a3}\<close> by (by100 blast)
      ultimately have h_each: "e12 - ?D1 = e12 - {a2}" "e23 - ?D1 = {}"
          "e41 - ?D1 = e41" "e34 - ?D1 = e34 - {a3}" by (by100 blast)+
      have "C - ?D1 = (e12 - ?D1) \<union> (e23 - ?D1) \<union> (e34 - ?D1) \<union> (e41 - ?D1)"
        using assms(39) by (by100 blast)
      hence "C - ?D1 = (e12 - {a2}) \<union> {} \<union> (e34 - {a3}) \<union> e41"
        using h_each by (by100 simp)
      moreover have "(e12 - {a2}) \<union> (e34 - {a3}) \<union> e41 = (e12 - {a2}) \<union> e41 \<union> (e34 - {a3})"
        by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Path-connected pieces.\<close>
    have hpc_e41: "top1_path_connected_on e41
        (subspace_topology top1_S2 top1_S2_topology e41)"
      by (rule arc_path_connected[OF assms(13) assms(7)])
    have ha2_ep: "a2 \<in> top1_arc_endpoints_on e12
        (subspace_topology top1_S2 top1_S2_topology e12)"
      using assms(16) by (by100 blast)
    have hpc_e12: "top1_path_connected_on (e12 - {a2})
        (subspace_topology top1_S2 top1_S2_topology (e12 - {a2}))"
      by (rule arc_minus_endpoint_pc[OF assms(10) assms(4) ha2_ep])
    have ha3_ep: "a3 \<in> top1_arc_endpoints_on e34
        (subspace_topology top1_S2 top1_S2_topology e34)"
      using assms(18) by (by100 blast)
    have hpc_e34: "top1_path_connected_on (e34 - {a3})
        (subspace_topology top1_S2 top1_S2_topology (e34 - {a3}))"
      by (rule arc_minus_endpoint_pc[OF assms(12) assms(6) ha3_ep])
    \<comment> \<open>Shared vertices.\<close>
    have ha1_ne_a2: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha3_ne_a4: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha1_e12: "a1 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha1_e41: "a1 \<in> e41" using assms(27) by (by100 blast)
    have ha1_share: "a1 \<in> (e12 - {a2}) \<inter> e41" using ha1_e12 ha1_ne_a2 ha1_e41 by (by100 blast)
    have ha4_e41: "a4 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha4_e34: "a4 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha4_share: "a4 \<in> e41 \<inter> (e34 - {a3})" using ha4_e41 ha4_e34 ha3_ne_a4 by (by100 blast)
    \<comment> \<open>Chain: (e12-{a2}) \<union> e41 via shared a1.\<close>
    have hTX12: "is_topology_on ((e12 - {a2}) \<union> e41)
        (subspace_topology top1_S2 top1_S2_topology ((e12 - {a2}) \<union> e41))"
      by (rule subspace_topology_is_topology_on[OF
          is_topology_on_strict_imp[OF assms(1)]]) (use assms(4,7) in \<open>by100 blast\<close>)
    have hpc_a1: "top1_path_connected_on ({a1})
        (subspace_topology top1_S2 top1_S2_topology {a1})"
    proof -
      have hTS1: "is_topology_on {a1} (subspace_topology top1_S2 top1_S2_topology {a1})"
        by (rule subspace_topology_is_topology_on[OF
            is_topology_on_strict_imp[OF assms(1)]]) (use assms(3) in \<open>by100 blast\<close>)
      show ?thesis unfolding top1_path_connected_on_def top1_is_path_on_def
      proof (intro conjI ballI)
        show "is_topology_on {a1} (subspace_topology top1_S2 top1_S2_topology {a1})" by (rule hTS1)
        fix x y :: "real \<times> real \<times> real"
        assume "x \<in> {a1}" "y \<in> {a1}"
        hence "x = a1" "y = a1" by (by100 blast)+
        have "top1_continuous_map_on I_set I_top {a1}
            (subspace_topology top1_S2 top1_S2_topology {a1}) (top1_constant_path a1)"
        proof -
          have "a1 \<in> top1_S2" using assms(3) by (by100 blast)
          hence "a1 \<in> {a1}" by (by100 blast)
          show ?thesis using top1_constant_path_continuous[OF hTS1 \<open>a1 \<in> {a1}\<close>]
            unfolding top1_constant_path_def by (by100 simp)
        qed
        moreover have "(top1_constant_path a1) 0 = x" using \<open>x = a1\<close>
          unfolding top1_constant_path_def by (by100 simp)
        moreover have "(top1_constant_path a1) 1 = y" using \<open>y = a1\<close>
          unfolding top1_constant_path_def by (by100 simp)
        ultimately show "\<exists>f. top1_continuous_map_on I_set I_top {a1}
            (subspace_topology top1_S2 top1_S2_topology {a1}) f \<and> f 0 = x \<and> f 1 = y"
          by (by100 blast)
      qed
    qed
    have h_sub12: "(e12 - {a2}) \<inter> e41 = {a1}"
      using assms(27) ha1_ne_a2 by (by100 blast)
    \<comment> \<open>Topology matching: sub S2 (piece) = sub (union) (sub S2 (union)) (piece).\<close>
    let ?X12 = "(e12 - {a2}) \<union> e41"
    have hsub_e12: "subspace_topology top1_S2 top1_S2_topology (e12 - {a2})
        = subspace_topology ?X12 (subspace_topology top1_S2 top1_S2_topology ?X12) (e12 - {a2})"
      using subspace_topology_trans[of "e12 - {a2}" ?X12] by (by100 simp)
    have hsub_e41: "subspace_topology top1_S2 top1_S2_topology e41
        = subspace_topology ?X12 (subspace_topology top1_S2 top1_S2_topology ?X12) e41"
      using subspace_topology_trans[of e41 ?X12] by (by100 simp)
    have hsub_a1: "subspace_topology top1_S2 top1_S2_topology {a1}
        = subspace_topology ?X12 (subspace_topology top1_S2 top1_S2_topology ?X12) {a1}"
      using subspace_topology_trans[of "{a1}" ?X12] ha1_share by (by100 simp)
    have hpc12: "top1_path_connected_on ?X12
        (subspace_topology top1_S2 top1_S2_topology ?X12)"
    proof (rule path_connected_union[OF hTX12])
      show "top1_path_connected_on (e12 - {a2})
          (subspace_topology ?X12 (subspace_topology top1_S2 top1_S2_topology ?X12) (e12 - {a2}))"
        using hpc_e12 hsub_e12 by (by100 simp)
      show "top1_path_connected_on e41
          (subspace_topology ?X12 (subspace_topology top1_S2 top1_S2_topology ?X12) e41)"
        using hpc_e41 hsub_e41 by (by100 simp)
      show "top1_path_connected_on ((e12 - {a2}) \<inter> e41)
          (subspace_topology ?X12 (subspace_topology top1_S2 top1_S2_topology ?X12) ((e12 - {a2}) \<inter> e41))"
        using hpc_a1 hsub_a1 h_sub12 by (by100 simp)
      show "(e12 - {a2}) \<union> e41 = ?X12" by (by100 blast)
      show "e12 - {a2} \<subseteq> ?X12" by (by100 blast)
      show "e41 \<subseteq> ?X12" by (by100 blast)
      show "(e12 - {a2}) \<inter> e41 \<noteq> {}" using ha1_share by (by100 blast)
    qed
    \<comment> \<open>Chain: ((e12-{a2}) \<union> e41) \<union> (e34-{a3}) via shared a4.\<close>
    let ?Xall = "(e12 - {a2}) \<union> e41 \<union> (e34 - {a3})"
    have hTXall: "is_topology_on ?Xall
        (subspace_topology top1_S2 top1_S2_topology ?Xall)"
      by (rule subspace_topology_is_topology_on[OF
          is_topology_on_strict_imp[OF assms(1)]]) (use assms(4,6,7) in \<open>by100 blast\<close>)
    have h_sub_all: "?X12 \<inter> (e34 - {a3}) = {a4}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> ?X12 \<inter> (e34 - {a3})"
      hence "x \<in> e41 \<inter> (e34 - {a3})" using assms(22) by (by100 blast)
      thus "x \<in> {a4}" using assms(26) ha3_ne_a4 by (by100 blast)
    next
      fix x assume "x \<in> {a4}"
      hence "x = a4" by (by100 blast)
      thus "x \<in> ?X12 \<inter> (e34 - {a3})" using ha4_share by (by100 blast)
    qed
    have hsub_X12: "subspace_topology top1_S2 top1_S2_topology ?X12
        = subspace_topology ?Xall (subspace_topology top1_S2 top1_S2_topology ?Xall) ?X12"
      using subspace_topology_trans[of ?X12 ?Xall] by (by100 simp)
    have hsub_e34: "subspace_topology top1_S2 top1_S2_topology (e34 - {a3})
        = subspace_topology ?Xall (subspace_topology top1_S2 top1_S2_topology ?Xall) (e34 - {a3})"
      using subspace_topology_trans[of "e34 - {a3}" ?Xall] by (by100 simp)
    have hpc_a4: "top1_path_connected_on ({a4})
        (subspace_topology top1_S2 top1_S2_topology {a4})"
    proof -
      have hTS4: "is_topology_on {a4} (subspace_topology top1_S2 top1_S2_topology {a4})"
        by (rule subspace_topology_is_topology_on[OF
            is_topology_on_strict_imp[OF assms(1)]]) (use assms(3) in \<open>by100 blast\<close>)
      show ?thesis unfolding top1_path_connected_on_def top1_is_path_on_def
      proof (intro conjI ballI)
        show "is_topology_on {a4} (subspace_topology top1_S2 top1_S2_topology {a4})" by (rule hTS4)
        fix x y :: "real \<times> real \<times> real"
        assume "x \<in> {a4}" "y \<in> {a4}"
        hence "x = a4" "y = a4" by (by100 blast)+
        show "\<exists>f. top1_continuous_map_on I_set I_top {a4}
            (subspace_topology top1_S2 top1_S2_topology {a4}) f \<and> f 0 = x \<and> f 1 = y"
          using top1_constant_path_continuous[OF hTS4, of a4]
            \<open>x = a4\<close> \<open>y = a4\<close> unfolding top1_constant_path_def
          by (by100 fastforce)
      qed
    qed
    have hsub_a4: "subspace_topology top1_S2 top1_S2_topology {a4}
        = subspace_topology ?Xall (subspace_topology top1_S2 top1_S2_topology ?Xall) {a4}"
      using subspace_topology_trans[of "{a4}" ?Xall] ha4_share by (by100 simp)
    have hpc_all: "top1_path_connected_on ?Xall
        (subspace_topology top1_S2 top1_S2_topology ?Xall)"
    proof (rule path_connected_union[OF hTXall])
      show "top1_path_connected_on ?X12
          (subspace_topology ?Xall (subspace_topology top1_S2 top1_S2_topology ?Xall) ?X12)"
        using hpc12 hsub_X12 by (by100 simp)
      show "top1_path_connected_on (e34 - {a3})
          (subspace_topology ?Xall (subspace_topology top1_S2 top1_S2_topology ?Xall) (e34 - {a3}))"
        using hpc_e34 hsub_e34 by (by100 simp)
      show "top1_path_connected_on (?X12 \<inter> (e34 - {a3}))
          (subspace_topology ?Xall (subspace_topology top1_S2 top1_S2_topology ?Xall) (?X12 \<inter> (e34 - {a3})))"
        using hpc_a4 hsub_a4 h_sub_all by (by100 simp)
      show "?X12 \<union> (e34 - {a3}) = ?Xall" by (by100 blast)
      show "?X12 \<subseteq> ?Xall" by (by100 blast)
      show "e34 - {a3} \<subseteq> ?Xall" by (by100 blast)
      show "?X12 \<inter> (e34 - {a3}) \<noteq> {}" using ha4_share by (by100 blast)
    qed
    show ?thesis using hpc_all hset by (by100 simp)
  qed
  \<comment> \<open>Similarly for C - D2.\<close>
  have hx_in_CmD2: "x \<in> C - ?D2"
  proof -
    have "x \<in> C" using hx_e12 assms(39) by (by100 blast)
    moreover have "x \<notin> Dq4"
    proof -
      have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e12 \<inter> Dq4 \<subseteq> e12 \<inter> e24" by (by100 blast)
      hence "e12 \<inter> Dq4 \<subseteq> {a2}" using assms(33) by (by100 blast)
      thus ?thesis using hx_e12 hx_not_endpts by (by100 blast)
    qed
    moreover have "x \<notin> e41" using hx_e12 hx_not_endpts assms(27) by (by100 blast)
    moreover have "x \<notin> D1p"
    proof -
      have "D1p \<subseteq> e13" using he13_split by (by100 blast)
      hence "e12 \<inter> D1p \<subseteq> e12 \<inter> e13" by (by100 blast)
      hence "e12 \<inter> D1p \<subseteq> {a1}" using assms(28) by (by100 blast)
      thus ?thesis using hx_e12 hx_not_endpts by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  have hy_in_CmD2: "y \<in> C - ?D2"
  proof -
    have "y \<in> C" using hy_e34 assms(39) by (by100 blast)
    moreover have "y \<notin> Dq4"
    proof -
      have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e34 \<inter> Dq4 \<subseteq> e34 \<inter> e24" by (by100 blast)
      hence "e34 \<inter> Dq4 \<subseteq> {a4}" using assms(35) by (by100 blast)
      thus ?thesis using hy_e34 hy_not_endpts by (by100 blast)
    qed
    moreover have "y \<notin> e41" using hy_e34 hy_not_endpts assms(26) by (by100 blast)
    moreover have "y \<notin> D1p"
    proof -
      have "D1p \<subseteq> e13" using he13_split by (by100 blast)
      hence "e34 \<inter> D1p \<subseteq> e34 \<inter> e13" by (by100 blast)
      hence h_sub: "e34 \<inter> D1p \<subseteq> {a3}" using assms(30) by (by100 blast)
      have "a3 \<noteq> p" using assms(37) by (by100 blast)
      have "a3 \<notin> D1p" using \<open>a3 \<in> Da3\<close> he13_meet \<open>a3 \<noteq> p\<close> by (by100 blast)
      thus ?thesis using hy_e34 h_sub \<open>a3 \<notin> D1p\<close> by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  have hCmD2_pc: "top1_path_connected_on (C - ?D2)
      (subspace_topology top1_S2 top1_S2_topology (C - ?D2))"
  proof -
    \<comment> \<open>Set equality: C - D2 = (e12-{a1}) \<union> e23 \<union> (e34-{a4}).\<close>
    have "e12 \<inter> Dq4 = {}"
    proof -
      have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e12 \<inter> Dq4 \<subseteq> e12 \<inter> e24" by (by100 blast)
      hence "e12 \<inter> Dq4 \<subseteq> {a2}" using assms(33) by (by100 blast)
      have "a2 \<noteq> q" using assms(38) by (by100 blast)
      have "a2 \<notin> Dq4" using \<open>a2 \<in> Da2\<close> he24_meet \<open>a2 \<noteq> q\<close> by (by100 blast)
      thus ?thesis using \<open>e12 \<inter> Dq4 \<subseteq> {a2}\<close> \<open>a2 \<notin> Dq4\<close> by (by100 blast)
    qed
    have "e12 \<inter> D1p \<subseteq> {a1}"
    proof -
      have "D1p \<subseteq> e13" using he13_split by (by100 blast)
      hence "e12 \<inter> D1p \<subseteq> e12 \<inter> e13" by (by100 blast)
      thus ?thesis using assms(28) by (by100 blast)
    qed
    have "e23 \<inter> Dq4 = {}"
    proof -
      have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e23 \<inter> Dq4 \<subseteq> e23 \<inter> e24" by (by100 blast)
      hence "e23 \<inter> Dq4 \<subseteq> {a2}" using assms(34) by (by100 blast)
      have "a2 \<noteq> q" using assms(38) by (by100 blast)
      have "a2 \<notin> Dq4" using \<open>a2 \<in> Da2\<close> he24_meet \<open>a2 \<noteq> q\<close> by (by100 blast)
      thus ?thesis using \<open>e23 \<inter> Dq4 \<subseteq> {a2}\<close> \<open>a2 \<notin> Dq4\<close> by (by100 blast)
    qed
    have "e23 \<inter> D1p = {}"
    proof -
      have "D1p \<subseteq> e13" using he13_split by (by100 blast)
      hence "e23 \<inter> D1p \<subseteq> e23 \<inter> e13" by (by100 blast)
      hence "e23 \<inter> D1p \<subseteq> {a3}" using assms(29) by (by100 blast)
      have "a3 \<noteq> p" using assms(37) by (by100 blast)
      have "a3 \<notin> D1p" using \<open>a3 \<in> Da3\<close> he13_meet \<open>a3 \<noteq> p\<close> by (by100 blast)
      thus ?thesis using \<open>e23 \<inter> D1p \<subseteq> {a3}\<close> \<open>a3 \<notin> D1p\<close> by (by100 blast)
    qed
    have "e34 \<inter> Dq4 \<subseteq> {a4}"
    proof -
      have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
      hence "e34 \<inter> Dq4 \<subseteq> e34 \<inter> e24" by (by100 blast)
      thus ?thesis using assms(35) by (by100 blast)
    qed
    have "e34 \<inter> D1p = {}"
    proof -
      have "D1p \<subseteq> e13" using he13_split by (by100 blast)
      hence "e34 \<inter> D1p \<subseteq> e34 \<inter> e13" by (by100 blast)
      hence "e34 \<inter> D1p \<subseteq> {a3}" using assms(30) by (by100 blast)
      have "a3 \<noteq> p" using assms(37) by (by100 blast)
      have "a3 \<notin> D1p" using \<open>a3 \<in> Da3\<close> he13_meet \<open>a3 \<noteq> p\<close> by (by100 blast)
      thus ?thesis using \<open>e34 \<inter> D1p \<subseteq> {a3}\<close> \<open>a3 \<notin> D1p\<close> by (by100 blast)
    qed
    have he12_D2: "e12 - ?D2 = e12 - {a1}"
      using assms(27) \<open>e12 \<inter> Dq4 = {}\<close> \<open>e12 \<inter> D1p \<subseteq> {a1}\<close> by (by100 blast)
    have he41_D2: "e41 - ?D2 = {}" by (by100 blast)
    have he23_D2: "e23 - ?D2 = e23"
      using assms(23) \<open>e23 \<inter> Dq4 = {}\<close> \<open>e23 \<inter> D1p = {}\<close> by (by100 blast)
    have he34_D2: "e34 - ?D2 = e34 - {a4}"
      using assms(26) \<open>e34 \<inter> D1p = {}\<close> \<open>e34 \<inter> Dq4 \<subseteq> {a4}\<close> by (by100 blast)
    have "C - ?D2 = (e12 - ?D2) \<union> (e23 - ?D2) \<union> (e34 - ?D2) \<union> (e41 - ?D2)"
      using assms(39) by (by100 blast)
    hence hCmD2_split: "C - ?D2 = (e12 - {a1}) \<union> e23 \<union> (e34 - {a4})"
      using he12_D2 he41_D2 he23_D2 he34_D2 by (by100 simp)
    have hset: "C - ?D2 = (e12 - {a1}) \<union> e23 \<union> (e34 - {a4})"
      using hCmD2_split by (by100 blast)
    \<comment> \<open>Path-connected pieces.\<close>
    have ha1_ne_a2: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha3_ne_a4: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha1_ep12: "a1 \<in> top1_arc_endpoints_on e12
        (subspace_topology top1_S2 top1_S2_topology e12)" using assms(16) by (by100 blast)
    have hpc_e12a1: "top1_path_connected_on (e12 - {a1})
        (subspace_topology top1_S2 top1_S2_topology (e12 - {a1}))"
      by (rule arc_minus_endpoint_pc[OF assms(10) assms(4) ha1_ep12])
    have hpc_e23: "top1_path_connected_on e23
        (subspace_topology top1_S2 top1_S2_topology e23)"
      by (rule arc_path_connected[OF assms(11) assms(5)])
    have ha4_ep34: "a4 \<in> top1_arc_endpoints_on e34
        (subspace_topology top1_S2 top1_S2_topology e34)" using assms(18) by (by100 blast)
    have hpc_e34a4: "top1_path_connected_on (e34 - {a4})
        (subspace_topology top1_S2 top1_S2_topology (e34 - {a4}))"
      by (rule arc_minus_endpoint_pc[OF assms(12) assms(6) ha4_ep34])
    \<comment> \<open>Shared vertices: a2 and a3.\<close>
    have ha2_e12: "a2 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha2_e23: "a2 \<in> e23" using assms(24) by (by100 blast)
    have ha2_share: "a2 \<in> (e12 - {a1}) \<inter> e23" using ha2_e12 ha1_ne_a2 ha2_e23 by (by100 blast)
    have ha3_e23: "a3 \<in> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha3_e34: "a3 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have ha3_share: "a3 \<in> e23 \<inter> (e34 - {a4})" using ha3_e23 ha3_e34 ha3_ne_a4 by (by100 blast)
    \<comment> \<open>Chain: (e12-{a1}) \<union> e23 at a2.\<close>
    let ?Y12 = "(e12 - {a1}) \<union> e23"
    have hTY12: "is_topology_on ?Y12
        (subspace_topology top1_S2 top1_S2_topology ?Y12)"
      by (rule subspace_topology_is_topology_on[OF
          is_topology_on_strict_imp[OF assms(1)]]) (use assms(4,5) in \<open>by100 blast\<close>)
    have h_sub12: "(e12 - {a1}) \<inter> e23 = {a2}" using assms(24) ha1_ne_a2 by (by100 blast)
    have hsub_e12a1: "subspace_topology top1_S2 top1_S2_topology (e12 - {a1})
        = subspace_topology ?Y12 (subspace_topology top1_S2 top1_S2_topology ?Y12) (e12 - {a1})"
      using subspace_topology_trans[of "e12 - {a1}" ?Y12] by (by100 simp)
    have hsub_e23: "subspace_topology top1_S2 top1_S2_topology e23
        = subspace_topology ?Y12 (subspace_topology top1_S2 top1_S2_topology ?Y12) e23"
      using subspace_topology_trans[of e23 ?Y12] by (by100 simp)
    have hpc_a2: "top1_path_connected_on {a2}
        (subspace_topology top1_S2 top1_S2_topology {a2})"
    proof -
      have hTS2: "is_topology_on {a2} (subspace_topology top1_S2 top1_S2_topology {a2})"
        by (rule subspace_topology_is_topology_on[OF
            is_topology_on_strict_imp[OF assms(1)]]) (use assms(3) in \<open>by100 blast\<close>)
      show ?thesis unfolding top1_path_connected_on_def top1_is_path_on_def
      proof (intro conjI ballI)
        show "is_topology_on {a2} (subspace_topology top1_S2 top1_S2_topology {a2})" by (rule hTS2)
        fix x y :: "real \<times> real \<times> real" assume "x \<in> {a2}" "y \<in> {a2}"
        hence "x = a2" "y = a2" by (by100 blast)+
        show "\<exists>f. top1_continuous_map_on I_set I_top {a2}
            (subspace_topology top1_S2 top1_S2_topology {a2}) f \<and> f 0 = x \<and> f 1 = y"
          using top1_constant_path_continuous[OF hTS2, of a2]
            \<open>x = a2\<close> \<open>y = a2\<close> unfolding top1_constant_path_def by (by100 fastforce)
      qed
    qed
    have hsub_a2: "subspace_topology top1_S2 top1_S2_topology {a2}
        = subspace_topology ?Y12 (subspace_topology top1_S2 top1_S2_topology ?Y12) {a2}"
      using subspace_topology_trans[of "{a2}" ?Y12] ha2_share by (by100 simp)
    have hpc_Y12: "top1_path_connected_on ?Y12
        (subspace_topology top1_S2 top1_S2_topology ?Y12)"
    proof (rule path_connected_union[OF hTY12])
      show "top1_path_connected_on (e12 - {a1})
          (subspace_topology ?Y12 (subspace_topology top1_S2 top1_S2_topology ?Y12) (e12 - {a1}))"
        using hpc_e12a1 hsub_e12a1 by (by100 simp)
      show "top1_path_connected_on e23
          (subspace_topology ?Y12 (subspace_topology top1_S2 top1_S2_topology ?Y12) e23)"
        using hpc_e23 hsub_e23 by (by100 simp)
      show "top1_path_connected_on ((e12 - {a1}) \<inter> e23)
          (subspace_topology ?Y12 (subspace_topology top1_S2 top1_S2_topology ?Y12) ((e12 - {a1}) \<inter> e23))"
        using hpc_a2 hsub_a2 h_sub12 by (by100 simp)
      show "(e12 - {a1}) \<union> e23 = ?Y12" by (by100 blast)
      show "e12 - {a1} \<subseteq> ?Y12" by (by100 blast)
      show "e23 \<subseteq> ?Y12" by (by100 blast)
      show "(e12 - {a1}) \<inter> e23 \<noteq> {}" using ha2_share by (by100 blast)
    qed
    \<comment> \<open>Chain: ?Y12 \<union> (e34-{a4}) at a3.\<close>
    let ?Yall = "(e12 - {a1}) \<union> e23 \<union> (e34 - {a4})"
    have hTYall: "is_topology_on ?Yall
        (subspace_topology top1_S2 top1_S2_topology ?Yall)"
      by (rule subspace_topology_is_topology_on[OF
          is_topology_on_strict_imp[OF assms(1)]]) (use assms(4,5,6) in \<open>by100 blast\<close>)
    have h_sub_all: "?Y12 \<inter> (e34 - {a4}) = {a3}"
    proof (rule set_eqI, rule iffI)
      fix z assume "z \<in> ?Y12 \<inter> (e34 - {a4})"
      hence "z \<in> e23 \<inter> (e34 - {a4})" using assms(22) by (by100 blast)
      thus "z \<in> {a3}" using assms(25) ha3_ne_a4 by (by100 blast)
    next
      fix z assume "z \<in> {a3}" thus "z \<in> ?Y12 \<inter> (e34 - {a4})" using ha3_share by (by100 blast)
    qed
    have hsub_Y12: "subspace_topology top1_S2 top1_S2_topology ?Y12
        = subspace_topology ?Yall (subspace_topology top1_S2 top1_S2_topology ?Yall) ?Y12"
      using subspace_topology_trans[of ?Y12 ?Yall] by (by100 simp)
    have hsub_e34a4: "subspace_topology top1_S2 top1_S2_topology (e34 - {a4})
        = subspace_topology ?Yall (subspace_topology top1_S2 top1_S2_topology ?Yall) (e34 - {a4})"
      using subspace_topology_trans[of "e34 - {a4}" ?Yall] by (by100 simp)
    have hpc_a3: "top1_path_connected_on {a3}
        (subspace_topology top1_S2 top1_S2_topology {a3})"
    proof -
      have hTS3: "is_topology_on {a3} (subspace_topology top1_S2 top1_S2_topology {a3})"
        by (rule subspace_topology_is_topology_on[OF
            is_topology_on_strict_imp[OF assms(1)]]) (use assms(3) in \<open>by100 blast\<close>)
      show ?thesis unfolding top1_path_connected_on_def top1_is_path_on_def
      proof (intro conjI ballI)
        show "is_topology_on {a3} (subspace_topology top1_S2 top1_S2_topology {a3})" by (rule hTS3)
        fix x y :: "real \<times> real \<times> real" assume "x \<in> {a3}" "y \<in> {a3}"
        hence "x = a3" "y = a3" by (by100 blast)+
        show "\<exists>f. top1_continuous_map_on I_set I_top {a3}
            (subspace_topology top1_S2 top1_S2_topology {a3}) f \<and> f 0 = x \<and> f 1 = y"
          using top1_constant_path_continuous[OF hTS3, of a3]
            \<open>x = a3\<close> \<open>y = a3\<close> unfolding top1_constant_path_def by (by100 fastforce)
      qed
    qed
    have hsub_a3: "subspace_topology top1_S2 top1_S2_topology {a3}
        = subspace_topology ?Yall (subspace_topology top1_S2 top1_S2_topology ?Yall) {a3}"
      using subspace_topology_trans[of "{a3}" ?Yall] ha3_share by (by100 simp)
    have hpc_Yall: "top1_path_connected_on ?Yall
        (subspace_topology top1_S2 top1_S2_topology ?Yall)"
    proof (rule path_connected_union[OF hTYall])
      show "top1_path_connected_on ?Y12
          (subspace_topology ?Yall (subspace_topology top1_S2 top1_S2_topology ?Yall) ?Y12)"
        using hpc_Y12 hsub_Y12 by (by100 simp)
      show "top1_path_connected_on (e34 - {a4})
          (subspace_topology ?Yall (subspace_topology top1_S2 top1_S2_topology ?Yall) (e34 - {a4}))"
        using hpc_e34a4 hsub_e34a4 by (by100 simp)
      show "top1_path_connected_on (?Y12 \<inter> (e34 - {a4}))
          (subspace_topology ?Yall (subspace_topology top1_S2 top1_S2_topology ?Yall) (?Y12 \<inter> (e34 - {a4})))"
        using hpc_a3 hsub_a3 h_sub_all by (by100 simp)
      show "?Y12 \<union> (e34 - {a4}) = ?Yall" by (by100 blast)
      show "?Y12 \<subseteq> ?Yall" by (by100 blast)
      show "e34 - {a4} \<subseteq> ?Yall" by (by100 blast)
      show "?Y12 \<inter> (e34 - {a4}) \<noteq> {}" using ha3_share by (by100 blast)
    qed
    show ?thesis using hpc_Yall hset by (by100 simp)
  qed
  \<comment> \<open>Step B4: Get paths \<alpha> in C \<inter> U from x to y, \<beta> in C \<inter> V from y to x.\<close>
  have hCmD1_sub: "C - ?D1 \<subseteq> ?U_loc" using hC_sub_S2 by (by100 blast)
  have hCmD2_sub: "C - ?D2 \<subseteq> ?V_loc" using hC_sub_S2 by (by100 blast)
  obtain \<alpha> where h\<alpha>: "top1_is_path_on (C - ?D1)
      (subspace_topology top1_S2 top1_S2_topology (C - ?D1)) x y \<alpha>"
    using hCmD1_pc hx_in_CmD1 hy_in_CmD1
    unfolding top1_path_connected_on_def by (by100 blast)
  obtain \<beta> where h\<beta>: "top1_is_path_on (C - ?D2)
      (subspace_topology top1_S2 top1_S2_topology (C - ?D2)) y x \<beta>"
    using hCmD2_pc hy_in_CmD2 hx_in_CmD2
    unfolding top1_path_connected_on_def by (by100 blast)
  \<comment> \<open>\<alpha> lies in C \<inter> U, \<beta> lies in C \<inter> V. So \<alpha>*\<beta> lies in C.\<close>
  \<comment> \<open>Step C: Show U\<inter>V has two components A, B with x \<in> A, y \<in> B.
     Then apply Theorem\_63\_1 to get \<alpha>*\<beta> nontrivial.\<close>
  \<comment> \<open>Step D: [\<alpha>*\<beta>] generates \<pi>_1(X) (63.1(c) + infinite cyclic).
     Step E: j_* surjective (\<alpha>*\<beta> \<in> C + generator).\<close>
  \<comment> \<open>Step C1: U\_loc \<subseteq> X and V\_loc \<subseteq> X (since p,q \<in> D1 \<inter> D2).\<close>
  have hp_D1: "p \<in> ?D1" using \<open>p \<in> Da3\<close> by (by100 blast)
  have hq_D1: "q \<in> ?D1" using \<open>q \<in> Da2\<close> by (by100 blast)
  have hp_D2: "p \<in> ?D2" using \<open>p \<in> D1p\<close> by (by100 blast)
  have hq_D2: "q \<in> ?D2" using \<open>q \<in> Dq4\<close> by (by100 blast)
  have hU_sub_X: "?U_loc \<subseteq> ?X" using hp_D1 hq_D1 by (by100 blast)
  have hV_sub_X: "?V_loc \<subseteq> ?X" using hp_D2 hq_D2 by (by100 blast)
  \<comment> \<open>Step C2: U\_loc \<union> V\_loc = X (since D1 \<inter> D2 = {p, q}).\<close>
  have hDa3_sub: "Da3 \<subseteq> e13" and hD1p_sub: "D1p \<subseteq> e13"
      and hDa2_sub: "Da2 \<subseteq> e24" and hDq4_sub: "Dq4 \<subseteq> e24"
    using he13_split he24_split by (by100 blast)+
  have hD1_D2_inter: "?D1 \<inter> ?D2 = {p, q}"
  proof (rule set_eqI, rule iffI)
    fix z assume hz: "z \<in> ?D1 \<inter> ?D2"
    hence hz1: "z \<in> Da3 \<or> z \<in> e23 \<or> z \<in> Da2" and hz2: "z \<in> Dq4 \<or> z \<in> e41 \<or> z \<in> D1p"
      by (by100 blast)+
    show "z \<in> {p, q}"
    proof -
      \<comment> \<open>Case analysis on hz1 \<times> hz2 = 9 cases. Most empty by K4 intersections.\<close>
      { assume "z \<in> Da3" "z \<in> D1p"
        hence "z \<in> Da3 \<inter> D1p" by (by100 blast)
        hence "z = p" using he13_meet he13_split by (by100 blast)
      } moreover
      { assume "z \<in> Da2" "z \<in> Dq4"
        hence "z \<in> Da2 \<inter> Dq4" by (by100 blast)
        hence "z = q" using he24_meet he24_split by (by100 blast)
      } moreover
      { assume "z \<in> Da3" "z \<in> Dq4"
        hence "z \<in> e13 \<inter> e24" using hDa3_sub hDq4_sub by (by100 blast)
        hence "z \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
      } moreover
      { assume "z \<in> Da3" "z \<in> e41"
        hence "z \<in> e13 \<inter> e41" using hDa3_sub by (by100 blast)
        hence "z \<in> {a1}" using assms(31) by (by100 blast)
      } moreover
      { assume "z \<in> e23" "z \<in> Dq4"
        hence "z \<in> e23 \<inter> e24" using hDq4_sub by (by100 blast)
        hence "z \<in> {a2}" using assms(34) by (by100 blast)
      } moreover
      { assume "z \<in> e23" "z \<in> e41"
        hence "z \<in> e23 \<inter> e41" by (by100 blast)
        hence False using assms(23) by (by100 blast)
      } moreover
      { assume "z \<in> e23" "z \<in> D1p"
        hence "z \<in> e23 \<inter> e13" using hD1p_sub by (by100 blast)
        hence "z \<in> {a3}" using assms(29) by (by100 blast)
      } moreover
      { assume "z \<in> Da2" "z \<in> e41"
        hence "z \<in> e24 \<inter> e41" using hDa2_sub by (by100 blast)
        hence "z \<in> {a4}" using assms(36) by (by100 blast)
      } moreover
      { assume "z \<in> Da2" "z \<in> D1p"
        hence "z \<in> e24 \<inter> e13" using hDa2_sub hD1p_sub by (by100 blast)
        hence "z \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
      }
      \<comment> \<open>In all cases, z \<in> {a1,a2,a3,a4} or z = p or z = q.
         But a1,a2,a3,a4 are not in the correct sub-arcs by endpoint analysis.\<close>
      \<comment> \<open>Vertex exclusion: each a\_i is not in both D1 and D2.\<close>
      \<comment> \<open>a1: a1 \<in> D1p (endpoint) and a1 \<in> e41 (endpoint), so a1 \<in> D2.
         But a1 \<notin> Da3 (Da3 endpoints = \{p, a3\}, a1 \<noteq> p, a1 \<noteq> a3), a1 \<notin> e23, a1 \<notin> Da2.
         So a1 \<notin> D1.\<close>
      moreover { assume hz_a1: "z = a1"
        have "a1 \<notin> Da3"
        proof
          assume "a1 \<in> Da3"
          hence "a1 \<in> Da3 \<inter> D1p" using \<open>a1 \<in> D1p\<close> by (by100 blast)
          hence "a1 = p" using he13_meet by (by100 blast)
          moreover have "a1 \<noteq> p" using assms(37) by (by100 blast)
          ultimately show False by (by100 blast)
        qed
        moreover have "a1 \<notin> e23"
        proof
          assume "a1 \<in> e23"
          have "a1 \<in> e41" using assms(27) by (by100 blast)
          hence "a1 \<in> e23 \<inter> e41" using \<open>a1 \<in> e23\<close> by (by100 blast)
          thus False using assms(23) by (by100 blast)
        qed
        moreover have "a1 \<notin> Da2"
        proof
          assume "a1 \<in> Da2"
          hence "a1 \<in> e24" using hDa2_sub by (by100 blast)
          have "a1 \<in> e12" using assms(27) by (by100 blast)
          hence "a1 \<in> e24 \<inter> e12" using \<open>a1 \<in> e24\<close> by (by100 blast)
          hence "a1 = a2" using assms(33) by (by100 blast)
          moreover have "a1 \<noteq> a2" using hdist by (by100 blast) \<comment> \<open>a1 \<noteq> a2 from K4 intersection conditions.\<close>
          ultimately show False by (by100 blast)
        qed
        ultimately have "a1 \<notin> ?D1" by (by100 blast)
        hence False using hz hz_a1 by (by100 blast)
      }
      moreover { assume hz_a2: "z = a2"
        have "a2 \<notin> Dq4"
        proof
          assume "a2 \<in> Dq4"
          hence "a2 \<in> Da2 \<inter> Dq4" using \<open>a2 \<in> Da2\<close> by (by100 blast)
          hence "a2 = q" using he24_meet by (by100 blast)
          thus False using assms(38) by (by100 blast)
        qed
        moreover have "a2 \<notin> e41"
        proof
          assume "a2 \<in> e41"
          have "a2 \<in> e12" using assms(24) by (by100 blast)
          hence "a2 \<in> e41 \<inter> e12" using \<open>a2 \<in> e41\<close> by (by100 blast)
          hence "a2 \<in> {a1}" using assms(27) by (by100 blast)
          hence "a2 = a1" by (by100 blast)
          moreover have "a2 \<noteq> a1" using hdist by (by100 blast) \<comment> \<open>a2 \<noteq> a1 from K4.\<close>
          ultimately show False by (by100 blast)
        qed
        moreover have "a2 \<notin> D1p"
        proof
          assume "a2 \<in> D1p"
          hence "a2 \<in> e13" using hD1p_sub by (by100 blast)
          have "a2 \<in> e12" using assms(24) by (by100 blast)
          hence "a2 \<in> e13 \<inter> e12" using \<open>a2 \<in> e13\<close> by (by100 blast)
          hence "a2 \<in> {a1}" using assms(28) by (by100 blast)
          hence "a2 = a1" by (by100 blast)
          moreover have "a2 \<noteq> a1" using hdist by (by100 blast) \<comment> \<open>a2 \<noteq> a1.\<close>
          ultimately show False by (by100 blast)
        qed
        ultimately have "a2 \<notin> ?D2" by (by100 blast)
        hence False using hz hz_a2 by (by100 blast)
      }
      moreover { assume hz_a3: "z = a3"
        have "a3 \<notin> Dq4"
        proof
          assume "a3 \<in> Dq4"
          hence "a3 \<in> e24" using hDq4_sub by (by100 blast)
          have "a3 \<in> e23" using assms(25) by (by100 blast)
          hence "a3 \<in> e24 \<inter> e23" using \<open>a3 \<in> e24\<close> by (by100 blast)
          hence "a3 \<in> {a2}" using assms(34) by (by100 blast)
          hence "a3 = a2" by (by100 blast)
          moreover have "a3 \<noteq> a2" using hdist by (by100 blast) \<comment> \<open>a3 \<noteq> a2 from K4.\<close>
          ultimately show False by (by100 blast)
        qed
        moreover have "a3 \<notin> e41"
        proof
          assume "a3 \<in> e41"
          have "a3 \<in> e23" using assms(25) by (by100 blast)
          hence "a3 \<in> e23 \<inter> e41" using \<open>a3 \<in> e41\<close> by (by100 blast)
          thus False using assms(23) by (by100 blast)
        qed
        moreover have "a3 \<notin> D1p"
        proof
          assume "a3 \<in> D1p"
          hence "a3 \<in> Da3 \<inter> D1p" using \<open>a3 \<in> Da3\<close> by (by100 blast)
          hence "a3 = p" using he13_meet by (by100 blast)
          thus False using assms(37) by (by100 blast)
        qed
        ultimately have "a3 \<notin> ?D2" by (by100 blast)
        hence False using hz hz_a3 by (by100 blast)
      }
      moreover { assume hz_a4: "z = a4"
        have "a4 \<notin> Da3"
        proof
          assume "a4 \<in> Da3"
          hence "a4 \<in> e13" using hDa3_sub by (by100 blast)
          have "a4 \<in> e41" using assms(26) by (by100 blast)
          hence "a4 \<in> e13 \<inter> e41" using \<open>a4 \<in> e13\<close> by (by100 blast)
          hence "a4 \<in> {a1}" using assms(31) by (by100 blast)
          hence "a4 = a1" by (by100 blast)
          moreover have "a4 \<noteq> a1" using hdist by (by100 blast) \<comment> \<open>a4 \<noteq> a1 from K4.\<close>
          ultimately show False by (by100 blast)
        qed
        moreover have "a4 \<notin> e23"
        proof
          assume "a4 \<in> e23"
          have "a4 \<in> e34" using assms(26) by (by100 blast)
          hence "a4 \<in> e23 \<inter> e34" using \<open>a4 \<in> e23\<close> by (by100 blast)
          hence "a4 \<in> {a3}" using assms(25) by (by100 blast)
          hence "a4 = a3" by (by100 blast)
          moreover have "a4 \<noteq> a3" using hdist by (by100 blast) \<comment> \<open>a4 \<noteq> a3 from K4.\<close>
          ultimately show False by (by100 blast)
        qed
        moreover have "a4 \<notin> Da2"
        proof
          assume "a4 \<in> Da2"
          hence "a4 \<in> Da2 \<inter> Dq4" using \<open>a4 \<in> Dq4\<close> by (by100 blast)
          hence "a4 = q" using he24_meet by (by100 blast)
          thus False using assms(38) by (by100 blast)
        qed
        ultimately have "a4 \<notin> ?D1" by (by100 blast)
        hence False using hz hz_a4 by (by100 blast)
      }
      ultimately show ?thesis using hz1 hz2 by blast
    qed
  next
    fix z assume "z \<in> {p, q}"
    thus "z \<in> ?D1 \<inter> ?D2"
      using hp_D1 hq_D1 hp_D2 hq_D2 by (by100 blast)
  qed
  have hUV_union: "?U_loc \<union> ?V_loc = ?X"
    using hD1_D2_inter hp_D1 hq_D1 hp_D2 hq_D2 by blast
  \<comment> \<open>Step C3: U\_loc \<inter> V\_loc = S2 - (D1 \<union> D2). D1 \<union> D2 is a simple closed curve.
     By JCT: U\_loc \<inter> V\_loc has two components A, B with x \<in> A, y \<in> B.\<close>
  \<comment> \<open>Step C4: \<alpha> is a path in U\_loc from x to y, \<beta> is a path in V\_loc from y to x.\<close>
  have h\<alpha>_U: "top1_is_path_on ?U_loc (subspace_topology ?X ?TX ?U_loc) x y \<alpha>"
  proof -
    \<comment> \<open>Lift \<alpha> from C-D1 to U\_loc (C-D1 \<subseteq> U\_loc).\<close>
    have hTU: "is_topology_on ?U_loc (subspace_topology top1_S2 top1_S2_topology ?U_loc)"
      by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
    have hTC_D1_eq: "subspace_topology ?U_loc (subspace_topology top1_S2 top1_S2_topology ?U_loc) (C - ?D1)
        = subspace_topology top1_S2 top1_S2_topology (C - ?D1)"
      using subspace_topology_trans[of "C - ?D1" ?U_loc] hCmD1_sub by (by100 simp)
    have h\<alpha>': "top1_is_path_on (C - ?D1) (subspace_topology ?U_loc (subspace_topology top1_S2 top1_S2_topology ?U_loc) (C - ?D1)) x y \<alpha>"
      using h\<alpha> hTC_D1_eq by (by100 simp)
    have "top1_is_path_on ?U_loc (subspace_topology top1_S2 top1_S2_topology ?U_loc) x y \<alpha>"
      by (rule path_in_subspace_is_path_in_ambient'[OF hTU hCmD1_sub h\<alpha>'])
    moreover have "subspace_topology ?X ?TX ?U_loc = subspace_topology top1_S2 top1_S2_topology ?U_loc"
      using subspace_topology_trans[of ?U_loc ?X] hU_sub_X by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  have h\<beta>_V: "top1_is_path_on ?V_loc (subspace_topology ?X ?TX ?V_loc) y x \<beta>"
  proof -
    have hTV: "is_topology_on ?V_loc (subspace_topology top1_S2 top1_S2_topology ?V_loc)"
      by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
    have hTC_D2_eq: "subspace_topology ?V_loc (subspace_topology top1_S2 top1_S2_topology ?V_loc) (C - ?D2)
        = subspace_topology top1_S2 top1_S2_topology (C - ?D2)"
      using subspace_topology_trans[of "C - ?D2" ?V_loc] hCmD2_sub by (by100 simp)
    have h\<beta>': "top1_is_path_on (C - ?D2) (subspace_topology ?V_loc (subspace_topology top1_S2 top1_S2_topology ?V_loc) (C - ?D2)) y x \<beta>"
      using h\<beta> hTC_D2_eq by (by100 simp)
    have "top1_is_path_on ?V_loc (subspace_topology top1_S2 top1_S2_topology ?V_loc) y x \<beta>"
      by (rule path_in_subspace_is_path_in_ambient'[OF hTV hCmD2_sub h\<beta>'])
    moreover have "subspace_topology ?X ?TX ?V_loc = subspace_topology top1_S2 top1_S2_topology ?V_loc"
      using subspace_topology_trans[of ?V_loc ?X] hV_sub_X by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Step C5: Apply Theorem 63.1.\<close>
  \<comment> \<open>Theorem 63.1 hypotheses: U\_loc, V\_loc open in X; U\<inter>V has two components; x, y separated.\<close>
  \<comment> \<open>Sub-arc endpoints (needed for both D1 and D2 proofs).\<close>
  have hD1p_ep: "top1_arc_endpoints_on D1p (subspace_topology top1_S2 top1_S2_topology D1p) = {a1, p}"
    and hDa3_ep: "top1_arc_endpoints_on Da3 (subspace_topology top1_S2 top1_S2_topology Da3) = {p, a3}"
    using arc_split_endpoints[OF assms(1) hS2_haus assms(8) assms(14) he13_split he13_meet
          hD1p_arc hDa3_arc \<open>a1 \<in> D1p\<close> \<open>a3 \<in> Da3\<close> \<open>p \<in> D1p\<close> \<open>p \<in> Da3\<close> \<open>D1p \<subseteq> top1_S2\<close>
          \<open>Da3 \<subseteq> top1_S2\<close> assms(20) hp_not_ep13]
    by blast+
  have hDa2_ep: "top1_arc_endpoints_on Da2 (subspace_topology top1_S2 top1_S2_topology Da2) = {a2, q}"
    and hDq4_ep: "top1_arc_endpoints_on Dq4 (subspace_topology top1_S2 top1_S2_topology Dq4) = {q, a4}"
    using arc_split_endpoints[OF assms(1) hS2_haus assms(9) assms(15) he24_split he24_meet
          hDa2_arc hDq4_arc \<open>a2 \<in> Da2\<close> \<open>a4 \<in> Dq4\<close> \<open>q \<in> Da2\<close> \<open>q \<in> Dq4\<close> \<open>Da2 \<subseteq> top1_S2\<close>
          \<open>Dq4 \<subseteq> top1_S2\<close> assms(21) hq_not_ep24]
    by blast+
  have hD1_sub_S2: "?D1 \<subseteq> top1_S2" using hDa3_sub hDa2_sub assms(5,8,9) by (by100 blast)
  have hD2_sub_S2: "?D2 \<subseteq> top1_S2" using hDq4_sub hD1p_sub assms(7,8,9) by (by100 blast)
  have hD1_arc: "top1_is_arc_on ?D1 (subspace_topology top1_S2 top1_S2_topology ?D1)"
    proof -
      \<comment> \<open>Da3 \<union> e23: shared endpoint a3. Result is arc from p to a2.\<close>
      have ha3_Da3: "a3 \<in> top1_arc_endpoints_on Da3 (subspace_topology top1_S2 top1_S2_topology Da3)"
        using hDa3_ep by (by100 blast)
      have ha3_e23: "a3 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
        using assms(17) by (by100 blast)
      have ha3_e23_mem: "a3 \<in> e23"
        using assms(17,25) by (by100 blast)
      have hDa3_e23_inter: "Da3 \<inter> e23 = {a3}"
      proof -
        have "Da3 \<inter> e23 \<subseteq> e13 \<inter> e23" using hDa3_sub by (by100 blast)
        hence "Da3 \<inter> e23 \<subseteq> {a3}" using assms(29) by (by100 blast)
        moreover have "a3 \<in> Da3 \<inter> e23" using \<open>a3 \<in> Da3\<close> ha3_e23_mem by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      have hDa3_e23_arc: "top1_is_arc_on (Da3 \<union> e23) (subspace_topology top1_S2 top1_S2_topology (Da3 \<union> e23))"
        by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus hDa3_arc _ assms(11) assms(5)
               hDa3_e23_inter ha3_Da3 ha3_e23]) (rule \<open>Da3 \<subseteq> top1_S2\<close>)
      \<comment> \<open>(Da3 \<union> e23) \<union> Da2: shared endpoint a2. Result = D1 = arc from p to q.\<close>
      have hDa3e23_ep: "top1_arc_endpoints_on (Da3 \<union> e23) (subspace_topology top1_S2 top1_S2_topology (Da3 \<union> e23)) = {p, a2}"
      proof -
        have hp_ne_a3: "p \<noteq> a3" using assms(37) by (by100 blast)
        have ha3_ne_a2: "a3 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
        have he23_ep': "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a3, a2}"
          using assms(17) by (by100 blast)
        show ?thesis
          by (rule arc_concat_endpoints[OF assms(1) hS2_haus hDa3_arc \<open>Da3 \<subseteq> top1_S2\<close>
                 assms(11) assms(5) hDa3_e23_inter ha3_Da3 ha3_e23 hDa3_ep he23_ep'
                 hp_ne_a3 ha3_ne_a2])
      qed
      have ha2_Da3e23: "a2 \<in> top1_arc_endpoints_on (Da3 \<union> e23) (subspace_topology top1_S2 top1_S2_topology (Da3 \<union> e23))"
        using hDa3e23_ep by (by100 blast)
      have ha2_Da2: "a2 \<in> top1_arc_endpoints_on Da2 (subspace_topology top1_S2 top1_S2_topology Da2)"
        using hDa2_ep by (by100 blast)
      have hDa3e23_Da2_inter: "(Da3 \<union> e23) \<inter> Da2 = {a2}"
      proof -
        have "Da3 \<inter> Da2 = {}"
        proof -
          have hsub4: "Da3 \<inter> Da2 \<subseteq> {a1,a2,a3,a4}"
          proof -
            have "Da3 \<inter> Da2 \<subseteq> e13 \<inter> e24" using hDa3_sub hDa2_sub by (by100 blast)
            thus ?thesis using assms(32) by (by100 blast)
          qed
          have "a1 \<noteq> p" using assms(37) by (by100 blast)
          have ha1_not_Da3: "a1 \<notin> Da3" using \<open>a1 \<in> D1p\<close> he13_meet \<open>a1 \<noteq> p\<close> by (by100 blast)
          have ha3_not_Da2: "a3 \<notin> Da2"
          proof -
            have "a3 \<notin> e24"
            proof
              assume "a3 \<in> e24"
              hence "a3 \<in> e24 \<inter> e23" using assms(17,25) by (by100 blast)
              hence "a3 \<in> {a2}" using assms(34) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hDa2_sub by (by100 blast)
          qed
          have ha2_not_Da3: "a2 \<notin> Da3"
          proof -
            have "a2 \<notin> e13"
            proof
              assume "a2 \<in> e13"
              hence "a2 \<in> e13 \<inter> e12" using assms(16,24) by (by100 blast)
              hence "a2 \<in> {a1}" using assms(28) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hDa3_sub by (by100 blast)
          qed
          have ha4_not_Da3: "a4 \<notin> Da3"
          proof -
            have "a4 \<notin> e13"
            proof
              assume "a4 \<in> e13"
              hence "a4 \<in> e13 \<inter> e41" using assms(19,26) by (by100 blast)
              hence "a4 \<in> {a1}" using assms(31) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hDa3_sub by (by100 blast)
          qed
          \<comment> \<open>Combine: Da3 \<inter> Da2 \<subseteq> {a1,a2,a3,a4}, but a1,a2,a4 \<notin> Da3 and a3 \<notin> Da2.\<close>
          show ?thesis
          proof (rule equals0I)
            fix z assume "z \<in> Da3 \<inter> Da2"
            hence "z \<in> {a1,a2,a3,a4}" using hsub4 by (by100 blast)
            hence "z = a1 \<or> z = a2 \<or> z = a3 \<or> z = a4" by (by100 blast)
            thus False using \<open>z \<in> Da3 \<inter> Da2\<close> ha1_not_Da3 ha2_not_Da3 ha3_not_Da2 ha4_not_Da3
              by (by100 blast)
          qed
        qed
        moreover have "e23 \<inter> Da2 = {a2}"
        proof -
          have "e23 \<inter> Da2 \<subseteq> e23 \<inter> e24" using hDa2_sub by (by100 blast)
          hence "e23 \<inter> Da2 \<subseteq> {a2}" using assms(34) by (by100 blast)
          moreover have "a2 \<in> e23 \<inter> Da2"
            using \<open>a2 \<in> Da2\<close> assms(17,24) by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        ultimately show ?thesis by (by100 blast)
      qed
      have hDa3e23_sub: "Da3 \<union> e23 \<subseteq> top1_S2" using \<open>Da3 \<subseteq> top1_S2\<close> assms(5) by (by100 blast)
      show ?thesis unfolding Un_assoc[symmetric]
        by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus hDa3_e23_arc hDa3e23_sub
               hDa2_arc \<open>Da2 \<subseteq> top1_S2\<close> hDa3e23_Da2_inter ha2_Da3e23 ha2_Da2])
    qed
  have hU_open_X: "openin_on ?X ?TX ?U_loc"
  proof -
    have "closedin_on top1_S2 top1_S2_topology ?D1"
      by (rule arc_in_S2_closed[OF hD1_sub_S2 hD1_arc])
    hence hU_S2_open: "?U_loc \<in> top1_S2_topology" unfolding closedin_on_def by (by100 blast)
    have "?U_loc = ?U_loc \<inter> ?X" using hU_sub_X by (by100 blast)
    hence "?U_loc \<in> ?TX" using hU_S2_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis unfolding openin_on_def using hU_sub_X by (by100 blast)
  qed
  have hD2_arc: "top1_is_arc_on ?D2 (subspace_topology top1_S2 top1_S2_topology ?D2)"
    proof -
      \<comment> \<open>Step 1: Dq4 \<union> e41 is an arc (shared endpoint a4).\<close>
      have ha4_Dq4: "a4 \<in> top1_arc_endpoints_on Dq4 (subspace_topology top1_S2 top1_S2_topology Dq4)"
        using hDq4_ep by (by100 blast)
      have ha4_e41: "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
        using assms(19) by (by100 blast)
      have hDq4_e41_inter: "Dq4 \<inter> e41 = {a4}"
      proof -
        have "Dq4 \<inter> e41 \<subseteq> e24 \<inter> e41" using hDq4_sub by (by100 blast)
        hence "Dq4 \<inter> e41 \<subseteq> {a4}" using assms(36) by (by100 blast)
        moreover have "a4 \<in> Dq4 \<inter> e41" using \<open>a4 \<in> Dq4\<close> assms(19,26) by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      have hDq4_e41_arc: "top1_is_arc_on (Dq4 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (Dq4 \<union> e41))"
        by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus hDq4_arc \<open>Dq4 \<subseteq> top1_S2\<close>
               assms(13) assms(7) hDq4_e41_inter ha4_Dq4 ha4_e41])
      \<comment> \<open>Step 2: endpoints of Dq4 \<union> e41 = {q, a1}.\<close>
      have ha4_ne_q: "a4 \<noteq> q" using assms(38) by (by100 blast)
      have ha4_ne_a1: "a4 \<noteq> a1" using assms(2) by (auto simp: card_insert_if split: if_splits)
      have he41_ep': "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4, a1}"
        using assms(19) by (by100 blast)
      have hDq4e41_ep: "top1_arc_endpoints_on (Dq4 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (Dq4 \<union> e41)) = {q, a1}"
      proof (rule arc_concat_endpoints[where c=a4])
        show "is_topology_on_strict top1_S2 top1_S2_topology" by (rule assms(1))
        show "is_hausdorff_on top1_S2 top1_S2_topology" by (rule hS2_haus)
        show "top1_is_arc_on Dq4 (subspace_topology top1_S2 top1_S2_topology Dq4)" by (rule hDq4_arc)
        show "Dq4 \<subseteq> top1_S2" by (rule \<open>Dq4 \<subseteq> top1_S2\<close>)
        show "top1_is_arc_on e41 (subspace_topology top1_S2 top1_S2_topology e41)" by (rule assms(13))
        show "e41 \<subseteq> top1_S2" by (rule assms(7))
        show "Dq4 \<inter> e41 = {a4}" by (rule hDq4_e41_inter)
        show "a4 \<in> top1_arc_endpoints_on Dq4 (subspace_topology top1_S2 top1_S2_topology Dq4)"
          by (rule ha4_Dq4)
        show "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
          by (rule ha4_e41)
        show "top1_arc_endpoints_on Dq4 (subspace_topology top1_S2 top1_S2_topology Dq4) = {q, a4}"
          by (rule hDq4_ep)
        show "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4, a1}"
          by (rule he41_ep')
        show "q \<noteq> a4" using ha4_ne_q by (by100 simp)
        show "a4 \<noteq> a1" by (rule ha4_ne_a1)
      qed
      \<comment> \<open>Step 3: (Dq4 \<union> e41) \<union> D1p is an arc (shared endpoint a1).\<close>
      have ha1_Dq4e41: "a1 \<in> top1_arc_endpoints_on (Dq4 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (Dq4 \<union> e41))"
        using hDq4e41_ep by (by100 blast)
      have ha1_D1p: "a1 \<in> top1_arc_endpoints_on D1p (subspace_topology top1_S2 top1_S2_topology D1p)"
        using hD1p_ep by (by100 blast)
      have hDq4e41_D1p_inter: "(Dq4 \<union> e41) \<inter> D1p = {a1}"
      proof -
        have "Dq4 \<inter> D1p = {}"
        proof (rule equals0I)
          fix z assume "z \<in> Dq4 \<inter> D1p"
          hence "z \<in> e24 \<inter> e13" using hDq4_sub hD1p_sub by (by100 blast)
          hence "z \<in> {a1,a2,a3,a4}" using assms(32) by (by100 blast)
          hence "z = a1 \<or> z = a2 \<or> z = a3 \<or> z = a4" by (by100 blast)
          moreover have "a1 \<notin> Dq4"
          proof -
            have "a1 \<notin> e24"
            proof
              assume "a1 \<in> e24"
              hence "a1 \<in> e24 \<inter> e41" using assms(19,27) by (by100 blast)
              hence "a1 \<in> {a4}" using assms(36) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hDq4_sub by (by100 blast)
          qed
          moreover have "a2 \<notin> D1p"
          proof -
            have "a2 \<notin> e13"
            proof
              assume "a2 \<in> e13"
              hence "a2 \<in> e13 \<inter> e12" using assms(16,24) by (by100 blast)
              hence "a2 \<in> {a1}" using assms(28) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hD1p_sub by (by100 blast)
          qed
          moreover have "a3 \<notin> Dq4"
          proof -
            have "a3 \<notin> e24"
            proof
              assume "a3 \<in> e24"
              hence "a3 \<in> e24 \<inter> e23" using assms(17,25) by (by100 blast)
              hence "a3 \<in> {a2}" using assms(34) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hDq4_sub by (by100 blast)
          qed
          moreover have "a4 \<notin> D1p"
          proof -
            have "a4 \<notin> e13"
            proof
              assume "a4 \<in> e13"
              hence "a4 \<in> e13 \<inter> e41" using assms(19,26) by (by100 blast)
              hence "a4 \<in> {a1}" using assms(31) by (by100 blast)
              thus False using assms(2) by (auto simp: card_insert_if split: if_splits)
            qed
            thus ?thesis using hD1p_sub by (by100 blast)
          qed
          ultimately show False using \<open>z \<in> Dq4 \<inter> D1p\<close> by (by100 blast)
        qed
        moreover have "e41 \<inter> D1p = {a1}"
        proof -
          have "e41 \<inter> D1p \<subseteq> e41 \<inter> e13" using hD1p_sub by (by100 blast)
          hence "e41 \<inter> D1p \<subseteq> {a1}" using assms(31) by (by100 blast)
          moreover have "a1 \<in> e41 \<inter> D1p" using \<open>a1 \<in> D1p\<close> assms(19,27) by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        ultimately show ?thesis by (by100 blast)
      qed
      have hDq4e41_sub: "Dq4 \<union> e41 \<subseteq> top1_S2" using \<open>Dq4 \<subseteq> top1_S2\<close> assms(7) by (by100 blast)
      show ?thesis unfolding Un_assoc[symmetric]
        by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus hDq4_e41_arc hDq4e41_sub
               hD1p_arc \<open>D1p \<subseteq> top1_S2\<close> hDq4e41_D1p_inter ha1_Dq4e41 ha1_D1p])
    qed
  have hV_open_X: "openin_on ?X ?TX ?V_loc"
  proof -
    have "closedin_on top1_S2 top1_S2_topology ?D2"
      by (rule arc_in_S2_closed[OF hD2_sub_S2 hD2_arc])
    hence hV_S2_open: "?V_loc \<in> top1_S2_topology" unfolding closedin_on_def by (by100 blast)
    have "?V_loc = ?V_loc \<inter> ?X" using hV_sub_X by (by100 blast)
    hence "?V_loc \<in> ?TX" using hV_S2_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis unfolding openin_on_def using hV_sub_X by (by100 blast)
  qed
  \<comment> \<open>U\<inter>V = S2-(D1\<union>D2). D1\<union>D2 is an SCC (cycle a1-a3-a2-a4-a1 through p,q).
     By JCT: S2-(D1\<union>D2) has two components A, B.
     x \<in> int(e12) and y \<in> int(e34) lie in different components (by Lemma 65.1(a)
     applied to the "other" K4 cycle D1\<union>D2).\<close>
  \<comment> \<open>Apply Theorem 63.5: D1, D2 arcs meeting in {p,q} (\<Rightarrow> 2 components).\<close>
  \<comment> \<open>D1, D2 closedness, connectedness, non-separation (using proved arc facts from hU/hV\_open\_X blocks).\<close>
  have hD1_closed: "closedin_on top1_S2 top1_S2_topology ?D1"
    by (rule arc_in_S2_closed[OF hD1_sub_S2 hD1_arc])
  have hD2_closed: "closedin_on top1_S2 top1_S2_topology ?D2"
    by (rule arc_in_S2_closed[OF hD2_sub_S2 hD2_arc])
  have hD1_conn: "top1_connected_on ?D1 (subspace_topology top1_S2 top1_S2_topology ?D1)"
    using arc_connected[OF hD1_arc] .
  have hD2_conn: "top1_connected_on ?D2 (subspace_topology top1_S2 top1_S2_topology ?D2)"
    using arc_connected[OF hD2_arc] .
  have hD1_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?D1"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) hD1_sub_S2 hD1_arc])
  have hD2_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?D2"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) hD2_sub_S2 hD2_arc])
  have hD1D2_card: "card (?D1 \<inter> ?D2) = 2"
    using hD1_D2_inter hp_ne_q by (by100 simp)
  obtain U0 V0 where hUV0: "U0 \<noteq> {}" "V0 \<noteq> {}" "U0 \<inter> V0 = {}"
      "U0 \<union> V0 = top1_S2 - (?D1 \<union> ?D2)"
      "top1_connected_on U0 (subspace_topology top1_S2 top1_S2_topology U0)"
      "top1_connected_on V0 (subspace_topology top1_S2 top1_S2_topology V0)"
    using Theorem_63_5_two_closed_connected[OF assms(1) hD1_closed hD2_closed
          hD1_conn hD2_conn hD1D2_card hD1_no_sep hD2_no_sep] by blast
  \<comment> \<open>U0 \<union> V0 = S2-(D1\<union>D2) = (S2-D1) \<inter> (S2-D2) = U\_loc \<inter> V\_loc.\<close>
  have hUV0_eq: "U0 \<union> V0 = ?U_loc \<inter> ?V_loc"
    using hUV0(4) by (by100 blast)
  \<comment> \<open>U0, V0 are open in X (since they're connected components of an open set in S2).\<close>
  \<comment> \<open>x, y are in different components (needs part (a) / Lemma\_64\_3 applied to "other" cycle).\<close>
  \<comment> \<open>U0, V0 are open in S2 (connected components of an open set in S2).\<close>
  have hW_open: "top1_S2 - (?D1 \<union> ?D2) \<in> top1_S2_topology"
  proof -
    have "?D1 \<subseteq> top1_S2 \<and> top1_S2 - ?D1 \<in> top1_S2_topology"
      using hD1_closed unfolding closedin_on_def by (by100 blast)
    have "?D2 \<subseteq> top1_S2 \<and> top1_S2 - ?D2 \<in> top1_S2_topology"
      using hD2_closed unfolding closedin_on_def by (by100 blast)
    hence "(top1_S2 - ?D1) \<inter> (top1_S2 - ?D2) \<in> top1_S2_topology"
    proof -
      have "top1_S2 - ?D1 \<in> top1_S2_topology" using \<open>?D1 \<subseteq> top1_S2 \<and> top1_S2 - ?D1 \<in> top1_S2_topology\<close> by (by100 blast)
      moreover have "top1_S2 - ?D2 \<in> top1_S2_topology" using \<open>?D2 \<subseteq> top1_S2 \<and> top1_S2 - ?D2 \<in> top1_S2_topology\<close> by (by100 blast)
      ultimately show ?thesis
        using topology_inter2[OF hTopS2] by (by100 blast)
    qed
    moreover have "top1_S2 - (?D1 \<union> ?D2) = (top1_S2 - ?D1) \<inter> (top1_S2 - ?D2)" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  have hW_sub: "top1_S2 - (?D1 \<union> ?D2) \<subseteq> top1_S2" by (by100 blast)
  have hW_not_conn: "\<not> top1_connected_on (top1_S2 - (?D1 \<union> ?D2))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?D1 \<union> ?D2)))"
  proof -
    have hsep: "top1_separates_on top1_S2 top1_S2_topology (?D1 \<union> ?D2)"
      by (rule Theorem_61_4_general_separation[OF assms(1) hD1_sub_S2 hD2_sub_S2
            hD1_closed hD2_closed hD1_conn hD2_conn hD1D2_card])
    thus ?thesis unfolding top1_separates_on_def by (by100 simp)
  qed
  have "U0 \<in> top1_S2_topology" "V0 \<in> top1_S2_topology"
    using S2_two_component_open[OF hW_open hW_sub hUV0(1,2,3) hUV0(4) hUV0(5,6) hW_not_conn]
    by (by100 blast)+
  hence hU0_open: "U0 \<in> top1_S2_topology" and hV0_open: "V0 \<in> top1_S2_topology"
    by (by100 blast)+
  \<comment> \<open>U0, V0 are open in X (open in S2 and subset of X).\<close>
  have hU0_sub_X: "U0 \<subseteq> ?X" using hUV0(4) hU_sub_X hV_sub_X by (by100 blast)
  have hV0_sub_X: "V0 \<subseteq> ?X" using hUV0(4) hU_sub_X hV_sub_X by (by100 blast)
  have hU0_open_X: "openin_on ?X ?TX U0"
  proof -
    have "U0 = U0 \<inter> ?X" using hU0_sub_X by (by100 blast)
    hence "U0 \<in> ?TX" using hU0_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis unfolding openin_on_def using hU0_sub_X by (by100 blast)
  qed
  have hV0_open_X: "openin_on ?X ?TX V0"
  proof -
    have "V0 = V0 \<inter> ?X" using hV0_sub_X by (by100 blast)
    hence "V0 \<in> ?TX" using hV0_open unfolding subspace_topology_def by (by100 blast)
    thus ?thesis unfolding openin_on_def using hV0_sub_X by (by100 blast)
  qed
  \<comment> \<open>x \<in> U0, y \<in> V0 (or swapped). Needs: x and y in different components.
     This follows from Lemma 65.1(a) applied to the "other" K4 cycle D1\<union>D2.\<close>
  have hx_in_UV: "x \<in> U0 \<union> V0"
    using hUV0(4) hx_in_CmD1 hx_in_CmD2 hC_sub_S2 by (by100 blast)
  have hy_in_UV: "y \<in> U0 \<union> V0"
    using hUV0(4) hy_in_CmD1 hy_in_CmD2 hC_sub_S2 by (by100 blast)
  have hx_y_diff_comp: "(x \<in> U0 \<and> y \<in> V0) \<or> (x \<in> V0 \<and> y \<in> U0)"
  proof -
    have hx_int: "x \<in> e12 - {a1, a2}" using hx_e12 hx_not_endpts by (by100 blast)
    have hy_int: "y \<in> e34 - {a3, a4}" using hy_e34 hy_not_endpts by (by100 blast)
    \<comment> \<open>x and y avoid D1\<union>D2, so they're in U0 \<union> V0. Need: different components.\<close>
    \<comment> \<open>Proof by contradiction using Lemma\_64\_3: if both in same component,
       all 4 K4 faces + int(e12) + int(e34) would be in that component,
       leaving the other component empty.\<close>
    have hD_eq: "?D1 \<union> ?D2 = e13 \<union> e23 \<union> e24 \<union> e41"
      using he13_split he24_split by (by100 blast)
    have hdiff: "\<not> (e12 - {a1, a2} \<subseteq> U0 \<and> e34 - {a3, a4} \<subseteq> U0)
              \<and> \<not> (e12 - {a1, a2} \<subseteq> V0 \<and> e34 - {a3, a4} \<subseteq> V0)"
      by (rule K4_nonadjacent_edges_different_components[OF assms(1-36)
            hUV0(1,2,3) _ hUV0(5,6)])
         (use hUV0(4) hD_eq in \<open>by100 simp\<close>)
    \<comment> \<open>int(e12) connected \<Rightarrow> entirely in U0 or V0. Same for int(e34).\<close>
    have ha1_ne_a2_loc: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have ha3_ne_a4_loc: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
    have he12_conn: "top1_connected_on (e12 - {a1, a2})
        (subspace_topology top1_S2 top1_S2_topology (e12 - {a1, a2}))"
      by (rule arc_minus_endpoints_connected[OF assms(1) hS2_haus assms(4,10,16) ha1_ne_a2_loc])
    have he34_conn: "top1_connected_on (e34 - {a3, a4})
        (subspace_topology top1_S2 top1_S2_topology (e34 - {a3, a4}))"
      by (rule arc_minus_endpoints_connected[OF assms(1) hS2_haus assms(6,12,18) ha3_ne_a4_loc])
    have hint_e12_sub: "e12 - {a1, a2} \<subseteq> U0 \<union> V0"
    proof -
      \<comment> \<open>(e12 - {a2}) \<inter> D1 = {} and (e12 - {a1}) \<inter> D2 = {}.\<close>
      have "e12 \<inter> Da3 = {}"
      proof -
        have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
        hence "e12 \<inter> Da3 \<subseteq> {a1}" using assms(28) by (by100 blast)
        have "a1 \<noteq> p" using assms(37) by (by100 blast)
        have "a1 \<notin> Da3" using \<open>a1 \<in> D1p\<close> he13_meet \<open>a1 \<noteq> p\<close> by (by100 blast)
        thus ?thesis using \<open>e12 \<inter> Da3 \<subseteq> {a1}\<close> by (by100 blast)
      qed
      have "(e12 - {a2}) \<inter> Da2 = {}"
      proof -
        have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e12 \<inter> Da2 \<subseteq> {a2}" using assms(33) by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      hence h_D1: "(e12 - {a2}) \<inter> ?D1 = {}"
        using \<open>e12 \<inter> Da3 = {}\<close> assms(24) by (by100 blast)
      have "e12 \<inter> Dq4 = {}"
      proof -
        have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e12 \<inter> Dq4 \<subseteq> {a2}" using assms(33) by (by100 blast)
        have "a2 \<noteq> q" using assms(38) by (by100 blast)
        have "a2 \<notin> Dq4" using \<open>a2 \<in> Da2\<close> he24_meet \<open>a2 \<noteq> q\<close> by (by100 blast)
        thus ?thesis using \<open>e12 \<inter> Dq4 \<subseteq> {a2}\<close> by (by100 blast)
      qed
      have "(e12 - {a1}) \<inter> D1p = {}"
      proof -
        have "D1p \<subseteq> e13" using he13_split by (by100 blast)
        hence "e12 \<inter> D1p \<subseteq> {a1}" using assms(28) by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      hence h_D2: "(e12 - {a1}) \<inter> ?D2 = {}"
        using \<open>e12 \<inter> Dq4 = {}\<close> assms(27) by (by100 blast)
      have "(e12 - {a1, a2}) \<inter> (?D1 \<union> ?D2) = {}" using h_D1 h_D2 by (by100 blast)
      hence "e12 - {a1, a2} \<subseteq> top1_S2 - (?D1 \<union> ?D2)" using assms(4) by (by100 blast)
      thus ?thesis using hUV0(4) by (by100 blast)
    qed
    have hint_e34_sub: "e34 - {a3, a4} \<subseteq> U0 \<union> V0"
    proof -
      have "(e34 - {a3}) \<inter> Da3 = {}"
      proof -
        have "Da3 \<subseteq> e13" using he13_split by (by100 blast)
        hence "e34 \<inter> Da3 \<subseteq> {a3}" using assms(30) by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      have "e34 \<inter> Da2 = {}"
      proof -
        have "Da2 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e34 \<inter> Da2 \<subseteq> {a4}" using assms(35) by (by100 blast)
        have "a4 \<noteq> q" using assms(38) by (by100 blast)
        have "a4 \<notin> Da2" using \<open>a4 \<in> Dq4\<close> he24_meet \<open>a4 \<noteq> q\<close> by (by100 blast)
        thus ?thesis using \<open>e34 \<inter> Da2 \<subseteq> {a4}\<close> by (by100 blast)
      qed
      hence h_D1: "(e34 - {a3}) \<inter> ?D1 = {}"
        using \<open>(e34 - {a3}) \<inter> Da3 = {}\<close> assms(25) by (by100 blast)
      have "(e34 - {a4}) \<inter> Dq4 = {}"
      proof -
        have "Dq4 \<subseteq> e24" using he24_split by (by100 blast)
        hence "e34 \<inter> Dq4 \<subseteq> {a4}" using assms(35) by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      have "e34 \<inter> D1p = {}"
      proof -
        have "D1p \<subseteq> e13" using he13_split by (by100 blast)
        hence "e34 \<inter> D1p \<subseteq> {a3}" using assms(30) by (by100 blast)
        have "a3 \<noteq> p" using assms(37) by (by100 blast)
        have "a3 \<notin> D1p" using \<open>a3 \<in> Da3\<close> he13_meet \<open>a3 \<noteq> p\<close> by (by100 blast)
        thus ?thesis using \<open>e34 \<inter> D1p \<subseteq> {a3}\<close> by (by100 blast)
      qed
      hence h_D2: "(e34 - {a4}) \<inter> ?D2 = {}"
        using \<open>(e34 - {a4}) \<inter> Dq4 = {}\<close> assms(26) by (by100 blast)
      have "(e34 - {a3, a4}) \<inter> (?D1 \<union> ?D2) = {}" using h_D1 h_D2 by (by100 blast)
      hence "e34 - {a3, a4} \<subseteq> top1_S2 - (?D1 \<union> ?D2)" using assms(6) by (by100 blast)
      thus ?thesis using hUV0(4) by (by100 blast)
    qed
    have he12_in_comp: "e12 - {a1, a2} \<subseteq> U0 \<or> e12 - {a1, a2} \<subseteq> V0"
    proof -
      have hW_top: "is_topology_on (U0 \<union> V0)
          (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0))"
        by (rule subspace_topology_is_topology_on[OF hTopS2])
           (use hUV0(4) in \<open>by100 blast\<close>)
      have hU0_open_W: "U0 \<in> subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)"
      proof -
        have "U0 = (U0 \<union> V0) \<inter> U0" by (by100 blast)
        thus ?thesis using hU0_open unfolding subspace_topology_def by (by100 blast)
      qed
      have hV0_open_W: "V0 \<in> subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)"
      proof -
        have "V0 = (U0 \<union> V0) \<inter> V0" by (by100 blast)
        thus ?thesis using hV0_open unfolding subspace_topology_def by (by100 blast)
      qed
      have hsep: "top1_is_separation_on (U0 \<union> V0)
          (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)) U0 V0"
        unfolding top1_is_separation_on_def
        using hU0_open_W hV0_open_W hUV0(1,2,3) by (by100 blast)
      have he12_conn_W: "top1_connected_on (e12 - {a1, a2})
          (subspace_topology (U0 \<union> V0)
            (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)) (e12 - {a1, a2}))"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology (e12 - {a1, a2}) =
            subspace_topology (U0 \<union> V0)
              (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)) (e12 - {a1, a2})"
          using subspace_topology_trans[of "e12 - {a1, a2}" "U0 \<union> V0"]
            hint_e12_sub by (by100 simp)
        thus ?thesis using he12_conn by (by100 simp)
      qed
      from Lemma_23_2_disjoint[OF hW_top hsep hint_e12_sub he12_conn_W]
      have "(e12 - {a1, a2}) \<inter> V0 = {} \<or> (e12 - {a1, a2}) \<inter> U0 = {}" .
      thus ?thesis
      proof
        assume "(e12 - {a1, a2}) \<inter> V0 = {}"
        hence "e12 - {a1, a2} \<subseteq> U0" using hint_e12_sub by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        assume "(e12 - {a1, a2}) \<inter> U0 = {}"
        hence "e12 - {a1, a2} \<subseteq> V0" using hint_e12_sub by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
    qed
    have he34_in_comp: "e34 - {a3, a4} \<subseteq> U0 \<or> e34 - {a3, a4} \<subseteq> V0"
    proof -
      have hW_top: "is_topology_on (U0 \<union> V0)
          (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0))"
        by (rule subspace_topology_is_topology_on[OF hTopS2])
           (use hUV0(4) in \<open>by100 blast\<close>)
      have hU0_open_W: "U0 \<in> subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)"
      proof -
        have "U0 = (U0 \<union> V0) \<inter> U0" by (by100 blast)
        thus ?thesis using hU0_open unfolding subspace_topology_def by (by100 blast)
      qed
      have hV0_open_W: "V0 \<in> subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)"
      proof -
        have "V0 = (U0 \<union> V0) \<inter> V0" by (by100 blast)
        thus ?thesis using hV0_open unfolding subspace_topology_def by (by100 blast)
      qed
      have hsep: "top1_is_separation_on (U0 \<union> V0)
          (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)) U0 V0"
        unfolding top1_is_separation_on_def
        using hU0_open_W hV0_open_W hUV0(1,2,3) by (by100 blast)
      have he34_conn_W: "top1_connected_on (e34 - {a3, a4})
          (subspace_topology (U0 \<union> V0)
            (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)) (e34 - {a3, a4}))"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology (e34 - {a3, a4}) =
            subspace_topology (U0 \<union> V0)
              (subspace_topology top1_S2 top1_S2_topology (U0 \<union> V0)) (e34 - {a3, a4})"
          using subspace_topology_trans[of "e34 - {a3, a4}" "U0 \<union> V0"]
            hint_e34_sub by (by100 simp)
        thus ?thesis using he34_conn by (by100 simp)
      qed
      from Lemma_23_2_disjoint[OF hW_top hsep hint_e34_sub he34_conn_W]
      have "(e34 - {a3, a4}) \<inter> V0 = {} \<or> (e34 - {a3, a4}) \<inter> U0 = {}" .
      thus ?thesis
      proof
        assume "(e34 - {a3, a4}) \<inter> V0 = {}"
        hence "e34 - {a3, a4} \<subseteq> U0" using hint_e34_sub by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        assume "(e34 - {a3, a4}) \<inter> U0 = {}"
        hence "e34 - {a3, a4} \<subseteq> V0" using hint_e34_sub by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
    qed
    have hx_ne_y_comp: "\<not>(x \<in> U0 \<and> y \<in> U0) \<and> \<not>(x \<in> V0 \<and> y \<in> V0)"
    proof (intro conjI notI)
      assume hboth: "x \<in> U0 \<and> y \<in> U0"
      have "e12 - {a1,a2} \<subseteq> U0"
      proof -
        from he12_in_comp have "e12 - {a1,a2} \<subseteq> U0 \<or> e12 - {a1,a2} \<subseteq> V0" .
        moreover have "x \<in> U0" using hboth by (by100 blast)
        moreover have "\<not> (e12 - {a1,a2} \<subseteq> V0)" using hx_int \<open>x \<in> U0\<close> hUV0(3) by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      moreover have "e34 - {a3,a4} \<subseteq> U0"
      proof -
        from he34_in_comp have "e34 - {a3,a4} \<subseteq> U0 \<or> e34 - {a3,a4} \<subseteq> V0" .
        moreover have "y \<in> U0" using hboth by (by100 blast)
        moreover have "\<not> (e34 - {a3,a4} \<subseteq> V0)" using hy_int \<open>y \<in> U0\<close> hUV0(3) by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      ultimately have "e12 - {a1,a2} \<subseteq> U0 \<and> e34 - {a3,a4} \<subseteq> U0" by (by100 blast)
      thus False using hdiff by (by100 blast)
    next
      assume hboth: "x \<in> V0 \<and> y \<in> V0"
      have "e12 - {a1,a2} \<subseteq> V0"
      proof -
        from he12_in_comp have "e12 - {a1,a2} \<subseteq> U0 \<or> e12 - {a1,a2} \<subseteq> V0" .
        moreover have "x \<in> V0" using hboth by (by100 blast)
        moreover have "\<not> (e12 - {a1,a2} \<subseteq> U0)" using hx_int \<open>x \<in> V0\<close> hUV0(3) by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      moreover have "e34 - {a3,a4} \<subseteq> V0"
      proof -
        from he34_in_comp have "e34 - {a3,a4} \<subseteq> U0 \<or> e34 - {a3,a4} \<subseteq> V0" .
        moreover have "y \<in> V0" using hboth by (by100 blast)
        moreover have "\<not> (e34 - {a3,a4} \<subseteq> U0)" using hy_int \<open>y \<in> V0\<close> hUV0(3) by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      ultimately have "e12 - {a1,a2} \<subseteq> V0 \<and> e34 - {a3,a4} \<subseteq> V0" by (by100 blast)
      thus False using hdiff by (by100 blast)
    qed
    thus ?thesis using hx_in_UV hy_in_UV hUV0(3) by (by100 blast)
  qed
  obtain A B where hAB: "?U_loc \<inter> ?V_loc = A \<union> B" "A \<inter> B = {}"
      "openin_on ?X ?TX A" "openin_on ?X ?TX B" "x \<in> A" "y \<in> B"
  proof -
    from hx_y_diff_comp show ?thesis
    proof
      assume h: "x \<in> U0 \<and> y \<in> V0"
      show ?thesis by (rule that[of U0 V0]) (use hUV0_eq hUV0(3) hU0_open_X hV0_open_X h in \<open>by100 blast\<close>)+
    next
      assume h: "x \<in> V0 \<and> y \<in> U0"
      show ?thesis by (rule that[of V0 U0]) (use hUV0_eq hUV0(3) hU0_open_X hV0_open_X h in \<open>by100 blast\<close>)+
    qed
  qed
  have h\<alpha>\<beta>_nontrivial: "\<not> top1_path_homotopic_on ?X ?TX x x
      (top1_path_product \<alpha> \<beta>) (top1_constant_path x)"
    by (rule Theorem_63_1_loop_nontrivial[OF hTX hU_open_X hV_open_X hUV_union
           hAB(1,2,3,4,5,6) h\<alpha>_U h\<beta>_V])
  \<comment> \<open>Step D: \<alpha>*\<beta> lies in C. So [\<alpha>*\<beta>]_C is a well-defined element of \<pi>_1(C, x).
     j_*([\<alpha>*\<beta>]_C) = [\<alpha>*\<beta>]_X \<noteq> id. Hence j_* is nontrivial.
     Since \<pi>_1(C) \<cong> Z and \<pi>_1(X) \<cong> Z:
     - j_* nontrivial hom Z \<rightarrow> Z torsion-free \<Rightarrow> j_* injective.
     - [\<alpha>*\<beta>] generates \<pi>_1(X) (63.1(c) + infinite cyclic) \<Rightarrow> j_* surjective.\<close>
  have h\<alpha>\<beta>_in_C: "top1_is_loop_on C ?TC x (top1_path_product \<alpha> \<beta>)"
  proof -
    have hTC_top: "is_topology_on C ?TC"
      by (rule subspace_topology_is_topology_on[OF hTopS2 hC_sub_S2])
    \<comment> \<open>Lift \<alpha> from C-D1 to C.\<close>
    have hCmD1_sub_C: "C - ?D1 \<subseteq> C" by (by100 blast)
    have hTC_CD1: "subspace_topology C ?TC (C - ?D1) = subspace_topology top1_S2 top1_S2_topology (C - ?D1)"
      using subspace_topology_trans[of "C - ?D1" C] hCmD1_sub_C by (by100 simp)
    have h\<alpha>_C: "top1_is_path_on C ?TC x y \<alpha>"
      by (rule path_in_subspace_is_path_in_ambient'[OF hTC_top hCmD1_sub_C])
         (rule h\<alpha>[unfolded hTC_CD1[symmetric]])
    \<comment> \<open>Lift \<beta> from C-D2 to C.\<close>
    have hCmD2_sub_C: "C - ?D2 \<subseteq> C" by (by100 blast)
    have hTC_CD2: "subspace_topology C ?TC (C - ?D2) = subspace_topology top1_S2 top1_S2_topology (C - ?D2)"
      using subspace_topology_trans[of "C - ?D2" C] hCmD2_sub_C by (by100 simp)
    have h\<beta>_C: "top1_is_path_on C ?TC y x \<beta>"
      by (rule path_in_subspace_is_path_in_ambient'[OF hTC_top hCmD2_sub_C])
         (rule h\<beta>[unfolded hTC_CD2[symmetric]])
    \<comment> \<open>\<alpha>*\<beta> is a loop in C.\<close>
    show ?thesis unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF hTC_top h\<alpha>_C h\<beta>_C])
  qed
  \<comment> \<open>Textbook conclusion (Munkres p.393):
     "\<alpha>*\<beta> represents a generator of \<pi>_1(X)."
     "j_* is surjective, so j_* must be an isomorphism."

     We have: h\<alpha>\<beta>\_in\_C (\<alpha>*\<beta> loop in C at x), h\<alpha>\<beta>\_nontrivial (nontrivial in X),

     The surjectivity argument at basepoint x:
     (1) [\<alpha>*\<beta>]_X generates \<pi>_1(X, x) [textbook asserts from 63.1 + inf cyclic]
     (2) [\<alpha>*\<beta>]_C is an element of \<pi>_1(C, x)
     (3) j_*([\<alpha>*\<beta>]_C) = [\<alpha>*\<beta>]_X [by inclusion\_induced\_class]
     (4) j_* hits a generator \<Rightarrow> j_* surjective

     Then injectivity from surjective hom Z \<rightarrow> Z.\<close>
  \<comment> \<open>===== THE CORE ARGUMENT (following Munkres p.393) =====
     "Because the fundamental group of X is infinite cyclic, the loop \<alpha>*\<beta>
      represents a generator of this group."

     Proof: U\_loc, V\_loc are simply connected (S2 minus arc, S2\_minus\_arc\_simply\_connected).
     Any loop f in X subdivides into pieces in U\_loc or V\_loc (loop\_subdivision\_UV).
     Each piece is nulhomotopic in its region (simply connected).
     After contraction, only crossings A\<leftrightarrow>B remain.
     By Theorem\_63\_1\_c\_subgroups\_trivial: all crossing loops through A are trivial
     (relative to \<alpha>*\<beta>). So every loop is a power of [\<alpha>*\<beta>].
     Hence [\<alpha>*\<beta>] generates \<pi>_1(X), i.e. [\<alpha>*\<beta>] = \<plusminus>gen.

     Since \<alpha>*\<beta> \<in> C: j_*([\<alpha>*\<beta>]_C) = [\<alpha>*\<beta>]_X = generator.
     Since [\<alpha>*\<beta>]_C generates \<pi>_1(C) \<cong> Z (traverses C once):
     j_* maps generator to generator \<Rightarrow> surjective \<Rightarrow> isomorphism.\<close>
  \<comment> \<open>===== GENERATION ARGUMENT: [\<alpha>*\<beta>] generates \<pi>_1(X, x) =====
     Following Munkres Theorem 63.1(b): use helix covering + \<pi>_1(X) infinite cyclic.
     Key idea: the helix lift gives a well-defined injection \<pi>_1(X) \<hookrightarrow> Z
     with [\<alpha>*\<beta>] \<mapsto> 1. Since \<pi>_1(X) \<cong> Z, this forces [\<alpha>*\<beta>] = generator.\<close>
  \<comment> \<open>Step G1: \<pi>_1(X, x) is infinite cyclic.\<close>
  have hx_in_X: "x \<in> ?X" using hx_in_CmD1 hC_sub_X by (by100 blast)
  obtain gen where hgen_loop: "top1_is_loop_on ?X ?TX x gen"
      and hgen_generates: "\<forall>f. top1_is_loop_on ?X ?TX x f \<longrightarrow>
        (\<exists>n::nat. top1_path_homotopic_on ?X ?TX x x f (top1_path_power gen x n)
          \<or> top1_path_homotopic_on ?X ?TX x x f
               (top1_path_power (top1_path_reverse gen) x n))"
    using pi1_S2_minus_two_points_infinite_cyclic[OF assms(1) hp_S2 hq_S2 hp_ne_q hx_in_X]
    by blast
  \<comment> \<open>Step G2: Construct helix covering E \<rightarrow> X for the 63.1 setup.\<close>
  have hx_A: "x \<in> A" using hAB(5) .
  have hy_B: "y \<in> B" using hAB(6) .
  have hx_U: "x \<in> ?U_loc" using hx_in_CmD1 hCmD1_sub by (by100 blast)
  have hy_U: "y \<in> ?U_loc" using hy_in_CmD1 hCmD1_sub by (by100 blast)
  have hx_V: "x \<in> ?V_loc" using hx_in_CmD2 hCmD2_sub by (by100 blast)
  have hy_V: "y \<in> ?V_loc" using hy_in_CmD2 hCmD2_sub by (by100 blast)
  \<comment> \<open>Step G3: The helix covering and its key property.
     For any m, (\<alpha>*\<beta>)^m lifts from (x, 0) to (x, 2m).
     This is helix\_f\_power\_lift applied to the U\_loc, V\_loc, A, B decomposition.\<close>
  \<comment> \<open>Step G4: The lift endpoint function (winding number) is well-defined on
     homotopy classes, by Theorem\_54\_3 (homotopic paths lift to same endpoint).
     And it's injective: if wind(f) = wind(g), then lifts of f and g end at the
     same sheet, and by Theorem\_54\_3 applied to f*g\<inverse>, wind(f*g\<inverse>) = 0,
     which means f*g\<inverse> \<in> H = p_*(\<pi>_1(E, e0)).
     Since wind is surjective (wind((\<alpha>*\<beta>)^n) = n for all n), and \<pi>_1(X) \<cong> Z,
     we get Z/H \<cong> Z as sets, which forces H = \{0\} (Z/nZ is finite for n\<ge>1).
     So wind is injective: distinct homotopy classes have distinct lift endpoints.\<close>
  \<comment> \<open>Step G5: Since wind is injective with wind((\<alpha>*\<beta>)^n) = n hitting all of Z,
     and \<langle>[\<alpha>*\<beta>]\<rangle> \<subseteq> \<pi>_1(X), the injection wind restricted to \<langle>[\<alpha>*\<beta>]\<rangle> is surjective.
     By injectivity of wind on all of \<pi>_1(X), any element outside \<langle>[\<alpha>*\<beta>]\<rangle> would
     map to some m = wind(g) = wind((\<alpha>*\<beta>)^m), contradicting injectivity.
     So \<langle>[\<alpha>*\<beta>]\<rangle> = \<pi>_1(X).\<close>
  have h\<alpha>\<beta>_generates: "\<forall>f. top1_is_loop_on ?X ?TX x f \<longrightarrow>
    (\<exists>n::nat. top1_path_homotopic_on ?X ?TX x x f
        (top1_path_power (top1_path_product \<alpha> \<beta>) x n)
      \<or> top1_path_homotopic_on ?X ?TX x x f
           (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) x n))"
  proof (rule Theorem_63_1_b_generation[OF hTX hU_open_X hV_open_X hUV_union
         hAB(1,2,3,4,5,6) h\<alpha>_U h\<beta>_V])
    show "\<exists>gen. top1_is_loop_on ?X ?TX x gen \<and>
        (\<forall>f. top1_is_loop_on ?X ?TX x f \<longrightarrow>
          (\<exists>n::nat. top1_path_homotopic_on ?X ?TX x x f (top1_path_power gen x n)
            \<or> top1_path_homotopic_on ?X ?TX x x f
                 (top1_path_power (top1_path_reverse gen) x n)))"
      using hgen_loop hgen_generates by blast
  qed
  \<comment> \<open>\<alpha>*\<beta> is also a loop in X (C \<subseteq> X).\<close>
  have hx_C: "x \<in> C" using hx_in_CmD1 by (by100 blast)
  have "h\<alpha>\<beta>_loop_X": "top1_is_loop_on ?X ?TX x (top1_path_product \<alpha> \<beta>)"
  proof -
    have "top1_is_path_on C ?TC x x (top1_path_product \<alpha> \<beta>)"
      using h\<alpha>\<beta>_in_C unfolding top1_is_loop_on_def by (by100 blast)
    have hTC_sub: "?TC = subspace_topology ?X ?TX C"
      using subspace_topology_trans[of C ?X top1_S2 top1_S2_topology] hC_sub_X by (by100 simp)
    have "top1_is_path_on C (subspace_topology ?X ?TX C) x x (top1_path_product \<alpha> \<beta>)"
      using \<open>top1_is_path_on C ?TC x x _\<close> hTC_sub by (by100 simp)
    from path_in_subspace_is_path_in_ambient'[OF hTX hC_sub_X this]
    show ?thesis unfolding top1_is_loop_on_def by (by100 blast)
  qed
  show ?thesis
  proof (intro bexI exI conjI)
    show "top1_is_loop_on C ?TC x (top1_path_product \<alpha> \<beta>)" by (rule h\<alpha>\<beta>_in_C)
    show "top1_is_loop_on ?X ?TX x (top1_path_product \<alpha> \<beta>)" by (rule "h\<alpha>\<beta>_loop_X")
    show "\<forall>f. top1_is_loop_on ?X ?TX x f \<longrightarrow>
        (\<exists>n::nat. top1_path_homotopic_on ?X ?TX x x f
            (top1_path_power (top1_path_product \<alpha> \<beta>) x n)
          \<or> top1_path_homotopic_on ?X ?TX x x f
               (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) x n))"
      by (rule h\<alpha>\<beta>_generates)
    show "x \<in> C" by (rule hx_C)
  qed
qed


\<comment> \<open>Standalone: K4 4-cycle is SCC. Used by both Lemma\_65\_1\_fixed and exists\_basepoint.\<close>
lemma K4_cycle_is_SCC:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "card {a1, a2, a3, a4} = 4"
      and "e12 \<subseteq> top1_S2" and "e23 \<subseteq> top1_S2" and "e34 \<subseteq> top1_S2" and "e41 \<subseteq> top1_S2"
      and "top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      and "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      and "top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      and "top1_is_arc_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
      and "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1,a2}"
      and "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2,a3}"
      and "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3,a4}"
      and "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4,a1}"
      and "e12 \<inter> e34 = {}" and "e23 \<inter> e41 = {}"
      and "e12 \<inter> e23 = {a2}" and "e23 \<inter> e34 = {a3}" and "e34 \<inter> e41 = {a4}"
      and "e41 \<inter> e12 = {a1}"
      and "C = e12 \<union> e23 \<union> e34 \<union> e41"
  shows "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
proof -
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  have ha1_ne_a3: "a1 \<noteq> a3" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha2_e12: "a2 \<in> top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
    using assms(11) by (by100 blast)
  have ha2_e23: "a2 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
    using assms(12) by (by100 blast)
  have hArc1: "top1_is_arc_on (e12 \<union> e23) (subspace_topology top1_S2 top1_S2_topology (e12 \<union> e23))"
    by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus assms(7,3,8,4) assms(17) ha2_e12 ha2_e23])
  have ha4_e34: "a4 \<in> top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
    using assms(13) by (by100 blast)
  have ha4_e41: "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
    using assms(14) by (by100 blast)
  have hArc2: "top1_is_arc_on (e34 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (e34 \<union> e41))"
    by (rule arcs_concatenation_is_arc[OF assms(1) hS2_haus assms(9,5,10,6) assms(19) ha4_e34 ha4_e41])
  have ha1_ne_a2: "a1 \<noteq> a2" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha2_ne_a3: "a2 \<noteq> a3" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha3_ne_a4: "a3 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have ha1_ne_a4: "a1 \<noteq> a4" using assms(2) by (auto simp: card_insert_if split: if_splits)
  have hArc1_ep: "top1_arc_endpoints_on (e12 \<union> e23) (subspace_topology top1_S2 top1_S2_topology (e12 \<union> e23)) = {a1, a3}"
    by (rule arc_concat_endpoints[OF assms(1) hS2_haus assms(7,3,8,4) assms(17) ha2_e12 ha2_e23
        assms(11) assms(12) ha1_ne_a2 ha2_ne_a3])
  have hArc2_ep: "top1_arc_endpoints_on (e34 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (e34 \<union> e41)) = {a3, a1}"
    by (rule arc_concat_endpoints[OF assms(1) hS2_haus assms(9,5,10,6) assms(19) ha4_e34 ha4_e41
        assms(13) assms(14) ha3_ne_a4])
       (use ha1_ne_a4 in \<open>by100 blast\<close>)
  have hint: "(e12 \<union> e23) \<inter> (e34 \<union> e41) = {a1, a3}"
  proof -
    have "e12 \<inter> e34 = {}" by (rule assms(15))
    moreover have "e12 \<inter> e41 = {a1}" using assms(20) by (by100 blast)
    moreover have "e23 \<inter> e34 = {a3}" by (rule assms(18))
    moreover have "e23 \<inter> e41 = {}" by (rule assms(16))
    ultimately show ?thesis by (by100 blast)
  qed
  have "top1_simple_closed_curve_on top1_S2 top1_S2_topology ((e12 \<union> e23) \<union> (e34 \<union> e41))"
    by (rule arcs_form_simple_closed_curve[OF assms(1) hS2_haus hArc1 _ hArc2 _ hint ha1_ne_a3 hArc1_ep])
       (use assms(3,4,5,6) hArc2_ep in \<open>by100 blast\<close>)+
  moreover have "(e12 \<union> e23) \<union> (e34 \<union> e41) = C" using assms(21) by (by100 blast)
  ultimately show ?thesis by (by100 simp)
qed

\<comment> \<open>Standalone: inclusion j: C \<hookrightarrow> X is surjective at the K4-generator basepoint x.
   Uses K4\_generator\_loop\_in\_C + inclusion\_sends\_class.\<close>
lemma K4_inclusion_surjective_at_x:
  fixes a1 a2 a3 a4 :: "real \<times> real \<times> real"
    and e12 e23 e34 e41 e13 e24 :: "(real \<times> real \<times> real) set"
    and C :: "(real \<times> real \<times> real) set"
    and p q :: "real \<times> real \<times> real"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "card {a1, a2, a3, a4} = 4"
      and "{a1, a2, a3, a4} \<subseteq> top1_S2"
      and "e12 \<subseteq> top1_S2" and "e23 \<subseteq> top1_S2" and "e34 \<subseteq> top1_S2"
      and "e41 \<subseteq> top1_S2" and "e13 \<subseteq> top1_S2" and "e24 \<subseteq> top1_S2"
      and "top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      and "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      and "top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      and "top1_is_arc_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
      and "top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
      and "top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
      and "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1,a2}"
      and "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2,a3}"
      and "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3,a4}"
      and "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4,a1}"
      and "top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1,a3}"
      and "top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2,a4}"
      and "e12 \<inter> e34 = {}" and "e23 \<inter> e41 = {}"
      and "e12 \<inter> e23 = {a2}" and "e23 \<inter> e34 = {a3}"
      and "e34 \<inter> e41 = {a4}" and "e41 \<inter> e12 = {a1}"
      and "e13 \<inter> e12 = {a1}" and "e13 \<inter> e23 = {a3}"
      and "e13 \<inter> e34 = {a3}" and "e13 \<inter> e41 = {a1}"
      and "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      and "e24 \<inter> e12 = {a2}" and "e24 \<inter> e23 = {a2}"
      and "e24 \<inter> e34 = {a4}" and "e24 \<inter> e41 = {a4}"
      and "p \<in> e13 - {a1, a3}" and "q \<in> e24 - {a2, a4}"
      and "C = e12 \<union> e23 \<union> e34 \<union> e41"
      \<comment> \<open>x is the basepoint from K4\_generator, j\_cont and j\_hom\_x are provided.\<close>
      and hx_C: "x \<in> C"
      and hg_loop_C: "top1_is_loop_on C (subspace_topology top1_S2 top1_S2_topology C) x g"
      and hg_loop_X: "top1_is_loop_on (top1_S2 - {p} - {q})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x g"
      and hg_generates: "\<forall>f. top1_is_loop_on (top1_S2 - {p} - {q})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x f \<longrightarrow>
          (\<exists>n::nat. top1_path_homotopic_on (top1_S2 - {p} - {q})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x x f
              (top1_path_power g x n)
            \<or> top1_path_homotopic_on (top1_S2 - {p} - {q})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x x f
              (top1_path_power (top1_path_reverse g) x n))"
      and hC_sub_X: "C \<subseteq> top1_S2 - {p} - {q}"
      and hTX: "is_topology_on (top1_S2 - {p} - {q})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q}))"
      and hTC: "is_topology_on C (subspace_topology top1_S2 top1_S2_topology C)"
      and hj_cont: "top1_continuous_map_on C
          (subspace_topology top1_S2 top1_S2_topology C)
          (top1_S2 - {p} - {q})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) id"
  shows "(top1_fundamental_group_induced_on C
      (subspace_topology top1_S2 top1_S2_topology C) x
      (top1_S2 - {p} - {q})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x id) `
    (top1_fundamental_group_carrier C (subspace_topology top1_S2 top1_S2_topology C) x) =
    top1_fundamental_group_carrier (top1_S2 - {p} - {q})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x"
proof -
  let ?TC = "subspace_topology top1_S2 top1_S2_topology C"
  let ?X = "top1_S2 - {p} - {q}"
  let ?TX = "subspace_topology top1_S2 top1_S2_topology ?X"
  let ?j = "top1_fundamental_group_induced_on C ?TC x ?X ?TX x id"
  have hx_X: "x \<in> ?X" using hx_C hC_sub_X by (by100 blast)
  \<comment> \<open>j\_*([g]\_C) = [g]\_X.\<close>
  have hTC_eq: "subspace_topology ?X ?TX C = ?TC"
    using subspace_topology_trans[of C ?X top1_S2 top1_S2_topology] hC_sub_X by (by100 simp)
  \<comment> \<open>Surjectivity: every [f]\_X is in image of j\_*.\<close>
  show ?thesis
  proof (intro set_eqI iffI)
    fix c assume "c \<in> ?j ` (top1_fundamental_group_carrier C ?TC x)"
    then obtain d where "d \<in> top1_fundamental_group_carrier C ?TC x" "c = ?j d" by (by100 blast)
    have "id x = x" by (by100 simp)
    from top1_fundamental_group_induced_on_is_hom[OF hTC hTX _ hx_X hj_cont this]
    have hhom: "top1_group_hom_on
        (top1_fundamental_group_carrier C ?TC x) (top1_fundamental_group_mul C ?TC x)
        (top1_fundamental_group_carrier ?X ?TX x) (top1_fundamental_group_mul ?X ?TX x) ?j"
      using hx_C by (by100 blast)
    thus "c \<in> top1_fundamental_group_carrier ?X ?TX x"
      using \<open>d \<in> _\<close> \<open>c = _\<close> unfolding top1_group_hom_on_def by (by100 blast)
  next
    fix c assume hc: "c \<in> top1_fundamental_group_carrier ?X ?TX x"
    then obtain f where hf: "top1_is_loop_on ?X ?TX x f"
        and hc_eq: "c = {h. top1_loop_equiv_on ?X ?TX x f h}"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
    from hg_generates hf
    obtain n where "top1_path_homotopic_on ?X ?TX x x f (top1_path_power g x n)
        \<or> top1_path_homotopic_on ?X ?TX x x f (top1_path_power (top1_path_reverse g) x n)"
      by (by100 blast)
    thus "c \<in> ?j ` (top1_fundamental_group_carrier C ?TC x)"
    proof (elim disjE)
      assume hfgn: "top1_path_homotopic_on ?X ?TX x x f (top1_path_power g x n)"
      have hgn_C: "top1_is_loop_on C ?TC x (top1_path_power g x n)"
        by (rule top1_path_power_is_loop[OF hTC hg_loop_C])
      have hgn_class_C: "{h. top1_loop_equiv_on C ?TC x (top1_path_power g x n) h}
          \<in> top1_fundamental_group_carrier C ?TC x"
        unfolding top1_fundamental_group_carrier_def using hgn_C by (by100 blast)
      have hgn_C': "top1_is_loop_on C (subspace_topology ?X ?TX C) x (top1_path_power g x n)"
        using hgn_C hTC_eq by (by100 simp)
      from subspace_inclusion_induced_class[OF hTX hC_sub_X hgn_C']
      have hj_gn: "?j {h. top1_loop_equiv_on C ?TC x (top1_path_power g x n) h} =
          {k. top1_loop_equiv_on ?X ?TX x (top1_path_power g x n) k}"
        unfolding hTC_eq[symmetric] induced_id_eq_lam .
      from path_homotopic_same_class[OF hTX hfgn]
      have "{h. top1_loop_equiv_on ?X ?TX x f h} =
          {h. top1_loop_equiv_on ?X ?TX x (top1_path_power g x n) h}" .
      hence "c = {h. top1_loop_equiv_on ?X ?TX x (top1_path_power g x n) h}"
        using hc_eq by (by100 blast)
      hence "c = ?j {h. top1_loop_equiv_on C ?TC x (top1_path_power g x n) h}"
        using hj_gn by (by100 simp)
      thus ?thesis using hgn_class_C by (by100 blast)
    next
      assume hfgrn: "top1_path_homotopic_on ?X ?TX x x f (top1_path_power (top1_path_reverse g) x n)"
      have hgr_loop_C: "top1_is_loop_on C ?TC x (top1_path_reverse g)"
        by (rule top1_path_reverse_is_loop[OF hg_loop_C])
      have hgrn_C: "top1_is_loop_on C ?TC x (top1_path_power (top1_path_reverse g) x n)"
        by (rule top1_path_power_is_loop[OF hTC hgr_loop_C])
      have hgrn_class_C: "{h. top1_loop_equiv_on C ?TC x (top1_path_power (top1_path_reverse g) x n) h}
          \<in> top1_fundamental_group_carrier C ?TC x"
        unfolding top1_fundamental_group_carrier_def using hgrn_C by (by100 blast)
      have hgrn_C': "top1_is_loop_on C (subspace_topology ?X ?TX C) x (top1_path_power (top1_path_reverse g) x n)"
        using hgrn_C hTC_eq by (by100 simp)
      from subspace_inclusion_induced_class[OF hTX hC_sub_X hgrn_C']
      have hj_grn: "?j {h. top1_loop_equiv_on C ?TC x (top1_path_power (top1_path_reverse g) x n) h} =
          {k. top1_loop_equiv_on ?X ?TX x (top1_path_power (top1_path_reverse g) x n) k}"
        unfolding hTC_eq[symmetric] induced_id_eq_lam .
      from path_homotopic_same_class[OF hTX hfgrn]
      have "{h. top1_loop_equiv_on ?X ?TX x f h} =
          {h. top1_loop_equiv_on ?X ?TX x (top1_path_power (top1_path_reverse g) x n) h}" .
      hence "c = {h. top1_loop_equiv_on ?X ?TX x (top1_path_power (top1_path_reverse g) x n) h}"
        using hc_eq by (by100 blast)
      hence "c = ?j {h. top1_loop_equiv_on C ?TC x (top1_path_power (top1_path_reverse g) x n) h}"
        using hj_grn by (by100 simp)
      thus ?thesis using hgrn_class_C by (by100 blast)
    qed
  qed
qed

section \<open>Reusable SCC / arc / homeomorphism lemmas\<close>

text \<open>Named lemmas for common SCC properties, reducing repeated inline reasoning.\<close>

\<comment> \<open>Aliases for existing lemmas with reviewer-suggested names.\<close>
lemmas sphere_minus_point_homeomorphic_R2 = S2_minus_point_homeo_R2
lemmas stereographic_projection_homeomorphism = S2_minus_point_homeo_R2

lemma simple_closed_curve_compact:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  shows "top1_compact_on C (subspace_topology top1_S2 top1_S2_topology C)"
proof -
  obtain f where hf: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S2 top1_S2_topology f"
      "f ` top1_S1 = C" using assms(2) unfolding top1_simple_closed_curve_on_def by blast
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by blast
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by blast
  from Theorem_26_5[OF hTS1 hTS2 S1_compact hf(1)]
  show ?thesis using hf(2) by simp
qed

lemma simple_closed_curve_nonempty:
  assumes "top1_simple_closed_curve_on X TX C"
  shows "C \<noteq> {}"
proof -
  obtain f where "f ` top1_S1 = C"
    using assms unfolding top1_simple_closed_curve_on_def by blast
  moreover have "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by simp
  ultimately show ?thesis by blast
qed

lemma simple_closed_curve_closed_in_S2:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  shows "closedin_on top1_S2 top1_S2_topology C"
  by (rule Theorem_26_3[OF top1_S2_is_hausdorff
      simple_closed_curve_subset[OF assms(2)]
      simple_closed_curve_compact[OF assms]])

lemma simple_closed_curve_complement_open:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  shows "top1_S2 - C \<in> top1_S2_topology"
  using simple_closed_curve_closed_in_S2[OF assms] assms(1)
  unfolding is_topology_on_strict_def closedin_on_def by blast

lemma simple_closed_curve_complement_components_two:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  shows "top1_separates_on top1_S2 top1_S2_topology C"
  by (rule Theorem_61_3_JordanSeparation_S2[OF assms])

lemma simple_closed_curve_component_path_connected:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
      and "W \<subseteq> top1_S2 - C"
      and "top1_connected_on W (subspace_topology top1_S2 top1_S2_topology W)"
      and "W \<noteq> {}"
      and "W \<in> top1_S2_topology"
  shows "top1_path_connected_on W (subspace_topology top1_S2 top1_S2_topology W)"
proof -
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by blast
  have hW_lpc: "top1_locally_path_connected_on W (subspace_topology top1_S2 top1_S2_topology W)"
    by (rule open_subset_locally_path_connected[OF S2_locally_path_connected assms(6)])
       (use assms(3) simple_closed_curve_subset[OF assms(2)] in blast)
  have hW_sub: "W \<subseteq> top1_S2" using assms(3) simple_closed_curve_subset[OF assms(2)] by blast
  have hTW: "is_topology_on W (subspace_topology top1_S2 top1_S2_topology W)"
    by (rule subspace_topology_is_topology_on[OF hTS2 hW_sub])
  from connected_locally_path_connected_imp_path_connected[OF hTW assms(4) hW_lpc assms(5)]
  show ?thesis .
qed

lemma simple_closed_curve_separates_connected_set:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
      and "top1_connected_on E (subspace_topology top1_S2 top1_S2_topology E)"
      and "E \<subseteq> top1_S2 - C"
      and "W1 \<subseteq> top1_S2 - C" and "W2 \<subseteq> top1_S2 - C"
      and "W1 \<inter> W2 = {}" and "W1 \<union> W2 = top1_S2 - C"
      and "W1 \<noteq> {}" and "W2 \<noteq> {}"
      and "W1 \<in> top1_S2_topology" and "W2 \<in> top1_S2_topology"
      and "\<exists>e1 \<in> E. e1 \<in> W1" and "\<exists>e2 \<in> E. e2 \<in> W2"
  shows False
proof -
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by blast
  have hT_E: "is_topology_on E (subspace_topology top1_S2 top1_S2_topology E)"
    by (rule subspace_topology_is_topology_on[OF hTS2]) (use assms(4) in blast)
  have hE_sub_W12: "E \<subseteq> W1 \<union> W2" using assms(4,8) by blast
  have hE1: "E \<inter> W1 \<noteq> {}" using assms(13) by blast
  have hE2: "E \<inter> W2 \<noteq> {}" using assms(14) by blast
  have "E = (E \<inter> W1) \<union> (E \<inter> W2)" using hE_sub_W12 by blast
  moreover have "(E \<inter> W1) \<inter> (E \<inter> W2) = {}" using assms(7) by blast
  moreover have "E \<inter> W1 \<noteq> {}" using hE1 .
  moreover have "E \<inter> W2 \<noteq> {}" using hE2 .
  moreover have "E \<inter> W1 \<in> subspace_topology top1_S2 top1_S2_topology E"
    unfolding subspace_topology_def using assms(11) by blast
  moreover have "E \<inter> W2 \<in> subspace_topology top1_S2 top1_S2_topology E"
    unfolding subspace_topology_def using assms(12) by blast
  ultimately show False using assms(3) unfolding top1_connected_on_def
    by (by100 blast)
qed

lemma component_image_under_homeomorphism:
  assumes "is_topology_on X TX" and "is_topology_on Y TY"
      and "top1_homeomorphism_on X TX Y TY h"
      and "top1_connected_on W (subspace_topology X TX W)"
      and "W \<subseteq> X"
  shows "top1_connected_on (h ` W) (subspace_topology Y TY (h ` W))"
proof -
  have hcont: "top1_continuous_map_on X TX Y TY h"
    using assms(3) unfolding top1_homeomorphism_on_def by blast
  have hTW: "is_topology_on W (subspace_topology X TX W)"
    by (rule subspace_topology_is_topology_on[OF assms(1) assms(5)])
  have hcont_W: "top1_continuous_map_on W (subspace_topology X TX W) Y TY h"
    by (rule top1_continuous_map_on_restrict_domain_simple[OF hcont assms(5)])
  from Theorem_23_5[OF hTW assms(2) assms(4) hcont_W]
  show ?thesis .
qed

lemma arc_endpoints_under_homeomorphism:
  assumes "is_topology_on_strict X TX" and "is_topology_on_strict Y TY"
      and "is_hausdorff_on X TX" and "is_hausdorff_on Y TY"
      and "top1_homeomorphism_on X TX Y TY g"
      and "A \<subseteq> X" and "top1_is_arc_on A (subspace_topology X TX A)"
      and "top1_arc_endpoints_on A (subspace_topology X TX A) = {a, b}"
      and "a \<noteq> b"
  shows "top1_is_arc_on (g ` A) (subspace_topology Y TY (g ` A))
       \<and> top1_arc_endpoints_on (g ` A) (subspace_topology Y TY (g ` A)) = {g a, g b}"
proof -
  obtain \<phi> where h\<phi>: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      A (subspace_topology X TX A) \<phi>"
    using assms(7) unfolding top1_is_arc_on_def is_topology_on_strict_def by blast
  have hg_A: "top1_homeomorphism_on A (subspace_topology X TX A)
      (g ` A) (subspace_topology Y TY (g ` A)) g"
    by (rule homeomorphism_on_restrict[OF assms(5) assms(6)])
  have hcomp: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      (g ` A) (subspace_topology Y TY (g ` A)) (g \<circ> \<phi>)"
    by (rule homeomorphism_comp[OF h\<phi> hg_A])
  have hgA_sub: "g ` A \<subseteq> Y"
    using assms(5,6) unfolding top1_homeomorphism_on_def top1_continuous_map_on_def by blast
  have hTY_plain: "is_topology_on Y TY"
    using assms(2) unfolding is_topology_on_strict_def by blast
  have hT_gA: "is_topology_on_strict (g ` A) (subspace_topology Y TY (g ` A))"
    by (rule subspace_topology_is_strict[OF assms(2) hgA_sub])
  have harc_gA: "top1_is_arc_on (g ` A) (subspace_topology Y TY (g ` A))"
    unfolding top1_is_arc_on_def using hT_gA hcomp by blast
  have hep: "top1_arc_endpoints_on (g ` A) (subspace_topology Y TY (g ` A)) = {(g \<circ> \<phi>) 0, (g \<circ> \<phi>) 1}"
    by (rule arc_endpoints_are_boundary[OF assms(2) assms(4) hgA_sub harc_gA hcomp])
  have hep_A: "{\<phi> 0, \<phi> 1} = {a, b}"
    using arc_endpoints_are_boundary[OF assms(1) assms(3) assms(6) assms(7) h\<phi>] assms(8) by simp
  have "{g (\<phi> 0), g (\<phi> 1)} = {g a, g b}"
  proof -
    from hep_A assms(9) have "(\<phi> 0 = a \<and> \<phi> 1 = b) \<or> (\<phi> 0 = b \<and> \<phi> 1 = a)"
      by (by100 fast)
    thus ?thesis
    proof
      assume "\<phi> 0 = a \<and> \<phi> 1 = b" thus ?thesis by (by100 simp)
    next
      assume "\<phi> 0 = b \<and> \<phi> 1 = a"
      hence "{g (\<phi> 0), g (\<phi> 1)} = {g b, g a}" by (by100 simp)
      also have "\<dots> = {g a, g b}" by (by100 blast)
      finally show ?thesis .
    qed
  qed
  hence "top1_arc_endpoints_on (g ` A) (subspace_topology Y TY (g ` A)) = {g a, g b}"
    using hep by (by100 simp)
  thus ?thesis using harc_gA by blast
qed

end
