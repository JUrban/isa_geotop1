theory AlgTopCached2
  imports "AlgTopChain.AlgTopChain"
begin

text \<open>Standard topology facts: B2 compact, S1 closed in B2, dunce cap Hausdorff.\<close>

lemma B2_compact: "top1_compact_on top1_B2 top1_B2_topology"
proof -
  have hB2_sub: "top1_B2 \<subseteq> {-1..1} \<times> {-1..1::real}"
  proof
    fix p :: "real \<times> real" assume "p \<in> top1_B2"
    hence h: "fst p ^ 2 + snd p ^ 2 \<le> 1" unfolding top1_B2_def by (by100 simp)
    have "0 \<le> snd p ^ 2" by (by100 simp)
    hence "fst p ^ 2 \<le> 1" using h by (by100 linarith)
    hence "\<bar>fst p\<bar> \<le> 1" using power2_le_imp_le[of "\<bar>fst p\<bar>" 1] by (by100 simp)
    moreover have "0 \<le> fst p ^ 2" by (by100 simp)
    moreover have "snd p ^ 2 \<le> 1" using h calculation by (by100 linarith)
    hence "\<bar>snd p\<bar> \<le> 1" using power2_le_imp_le[of "\<bar>snd p\<bar>" 1] by (by100 simp)
    hence "- 1 \<le> snd p \<and> snd p \<le> 1" by (by100 linarith)
    moreover from \<open>\<bar>fst p\<bar> \<le> 1\<close> have "- 1 \<le> fst p \<and> fst p \<le> 1" by (by100 linarith)
    ultimately have "fst p \<in> {-1..1} \<and> snd p \<in> {-1..1}" by (by100 simp)
    thus "p \<in> {-1..1} \<times> {-1..1}" by (simp add: mem_Times_iff)
  qed
  have "closed top1_B2"
  proof -
    have "top1_B2 = (\<lambda>p::real\<times>real. fst p ^ 2 + snd p ^ 2) -` {..1}"
      unfolding top1_B2_def by (by100 auto)
    moreover have "continuous_on UNIV (\<lambda>p::real\<times>real. fst p ^ 2 + snd p ^ 2)"
      by (intro continuous_intros)
    hence "closed ((\<lambda>p::real\<times>real. fst p ^ 2 + snd p ^ 2) -` {..1})"
      by (intro closed_vimage closed_atMost) (simp add: continuous_on_eq_continuous_at open_UNIV)
    ultimately show ?thesis by (by100 simp)
  qed
  hence "compact top1_B2"
    using closed_subset_compact[OF compact_Icc_Times _ hB2_sub] by (by100 blast)
  have "top1_B2_topology = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_B2"
    unfolding top1_B2_topology_def ..
  hence "top1_B2_topology = subspace_topology (UNIV::((real\<times>real) set)) (top1_open_sets::((real\<times>real) set set)) top1_B2"
    using product_topology_on_open_sets[where 'a=real and 'b=real] by simp
  hence "top1_compact_on top1_B2 top1_B2_topology \<longleftrightarrow> compact top1_B2"
    using top1_compact_on_subspace_UNIV_iff_compact[of top1_B2] by simp
  thus ?thesis using \<open>compact top1_B2\<close> by (by100 simp)
qed

lemma S1_closed_in_B2: "closedin_on top1_B2 top1_B2_topology top1_S1"
proof -
  have hS1_sub_B2: "top1_S1 \<subseteq> top1_B2"
    unfolding top1_S1_def top1_B2_def by (by100 auto)
  show ?thesis
  proof (rule closedin_intro[OF hS1_sub_B2])
    have hopen_disk: "open {z::real\<times>real. (fst z)^2 + (snd z)^2 < 1}"
    proof -
      have hcont_nsq: "continuous_on UNIV (\<lambda>z::real\<times>real. (fst z)^2 + (snd z)^2)"
        by (intro continuous_intros)
      have hopen_lt1: "open ({..<1}::real set)" by (by100 simp)
      have heq: "{z::real\<times>real. (fst z)^2 + (snd z)^2 < 1}
          = (\<lambda>z. (fst z)^2 + (snd z)^2) -` {..<1::real} \<inter> UNIV"
        by (by100 auto)
      have "open ((\<lambda>z::real\<times>real. (fst z)^2 + (snd z)^2) -` {..<1::real} \<inter> UNIV)"
        using continuous_on_open_vimage[of "UNIV::((real\<times>real) set)"
              "\<lambda>z. (fst z)^2 + (snd z)^2"] hcont_nsq hopen_lt1
        by (by5000 auto)
      thus ?thesis using heq by (by100 simp)
    qed
    have hdisk_in_PT: "{z::real\<times>real. (fst z)^2 + (snd z)^2 < 1}
        \<in> product_topology_on top1_open_sets top1_open_sets"
      using hopen_disk product_topology_on_open_sets_real2 unfolding top1_open_sets_def
      by (by100 blast)
    have hdiff_eq: "top1_B2 - top1_S1 = top1_B2 \<inter> {z. (fst z)^2 + (snd z)^2 < 1}"
      unfolding top1_B2_def top1_S1_def by (by100 auto)
    show "top1_B2 - top1_S1 \<in> top1_B2_topology"
      unfolding top1_B2_topology_def subspace_topology_def
      using hdisk_in_PT hdiff_eq by (by100 blast)
  qed
qed


text \<open>The dunce cap quotient space is Hausdorff. This is used in both
  m\_projective\_scheme\_CW\_data and Theorem 73.4.\<close>
lemma dunce_cap_hausdorff:
  assumes "top1_is_dunce_cap_on X TX n"
  shows "is_hausdorff_on X TX"
proof -
  \<comment> \<open>Extract data from dunce cap definition.\<close>
  have hX_strict: "is_topology_on_strict X TX"
    using assms unfolding top1_is_dunce_cap_on_def by (by100 blast)
  have hTX: "is_topology_on X TX"
    using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
  have hn_pos: "n > 0" using assms unfolding top1_is_dunce_cap_on_def by (by100 blast)
  obtain q where hq_quot: "top1_quotient_map_on top1_B2 top1_B2_topology X TX q"
      and hq_S1: "\<forall>z\<in>top1_S1. \<forall>z'\<in>top1_S1.
            q z = q z' \<longleftrightarrow>
            (\<exists>k::nat. k < n \<and>
               z' = (cos (2*pi*real k/real n) * fst z - sin (2*pi*real k/real n) * snd z,
                     sin (2*pi*real k/real n) * fst z + cos (2*pi*real k/real n) * snd z))"
      and hq_inj: "inj_on q (top1_B2 - top1_S1)"
      and hq_sep: "\<forall>z\<in>top1_B2 - top1_S1. \<forall>z'\<in>top1_S1. q z \<noteq> q z'"
    using assms unfolding top1_is_dunce_cap_on_def
    apply (elim exE conjE)
    apply (rule that)
    apply assumption+
    done
  have hq_cont: "top1_continuous_map_on top1_B2 top1_B2_topology X TX q"
    using hq_quot unfolding top1_quotient_map_on_def by (by100 blast)
  have hq_surj: "q ` top1_B2 = X"
    using hq_quot unfolding top1_quotient_map_on_def by (by100 blast)
  \<comment> \<open>B2 is compact Hausdorff, hence normal.\<close>
  have hB2_haus: "is_hausdorff_on top1_B2 top1_B2_topology"
  proof -
    have hTOS_eq: "(order_topology_on_UNIV :: real set set) = top1_open_sets"
      using order_topology_on_UNIV_eq_HOL_open unfolding top1_open_sets_def by (by100 auto)
    have hR_haus: "is_hausdorff_on (UNIV::real set) (top1_open_sets::real set set)"
      using conjunct1[OF Theorem_17_11[where 'a=real]] unfolding hTOS_eq .
    have "is_hausdorff_on ((UNIV::real set) \<times> (UNIV::real set))
        (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set))"
      using conjunct1[OF conjunct2[OF Theorem_17_11]] hR_haus by (by100 blast)
    hence "is_hausdorff_on (UNIV::(real\<times>real) set)
        (product_topology_on top1_open_sets top1_open_sets)" by (by100 simp)
    thus ?thesis using conjunct2[OF conjunct2[OF Theorem_17_11]]
      unfolding top1_B2_topology_def by (by100 blast)
  qed
  \<comment> \<open>B2 normal (compact Hausdorff \<Rightarrow> normal by Theorem 32.3).\<close>
  have hB2_normal: "top1_normal_on top1_B2 top1_B2_topology"
    by (rule Theorem_32_3[OF B2_compact hB2_haus])
  \<comment> \<open>Munkres: For distinct x, y \<in> X, fibers q\<inverse>(x) and q\<inverse>(y) are disjoint closed
     subsets of normal B2, hence separable. Push forward via quotient.\<close>
  \<comment> \<open>q is a closed map: saturated closed sets in B2 map to closed sets in X.
     For the dunce cap, the saturation of any closed set C is:
     - C itself on B2 \\ S1 (injective),
     - C \<union> \<Union>k<n. rot_k(C \<inter> S1) on S1 (orbit of C's circle part).
     Both are closed (finite union of rotations of closed sets).\<close>
  have hq_closed: "\<forall>C. closedin_on top1_B2 top1_B2_topology C \<longrightarrow> closedin_on X TX (q ` C)"
  proof (intro allI impI)
    fix C assume hC: "closedin_on top1_B2 top1_B2_topology C"
    have hC_sub: "C \<subseteq> top1_B2" using hC unfolding closedin_on_def by (by100 blast)
    \<comment> \<open>Define rotation: rot\_k(z) = rotation of z by 2\<pi>k/n.\<close>
    define rot where "rot k z = (cos (2*pi*real k/real n) * fst z - sin (2*pi*real k/real n) * snd z,
        sin (2*pi*real k/real n) * fst z + cos (2*pi*real k/real n) * snd z)" for k :: nat and z :: "real \<times> real"
    \<comment> \<open>Saturation: sat(C) = {z \<in> B2 | q(z) \<in> q(C)} = C \<union> \<Union>k<n. rot k ` (C \<inter> S1).\<close>
    define sat where "sat = {z \<in> top1_B2. q z \<in> q ` C}"
    \<comment> \<open>Step 1: sat = C \<union> \<Union>k<n. rot k ` (C \<inter> S1).\<close>
    have hS1_sub_B2: "top1_S1 \<subseteq> top1_B2"
      unfolding top1_S1_def top1_B2_def by (by100 auto)
    \<comment> \<open>General fact: rotation preserves S1 (for any k).\<close>
    have hrot_S1_gen: "\<And>k. rot k ` top1_S1 \<subseteq> top1_S1"
    proof
      fix k :: nat and w assume "w \<in> rot k ` top1_S1"
      then obtain z where hz: "z \<in> top1_S1" "w = rot k z" by (by100 blast)
      have "fst z ^ 2 + snd z ^ 2 = 1" using hz(1) unfolding top1_S1_def by (by100 simp)
      define c where "c = cos (2*pi*real k/real n)"
      define s where "s = sin (2*pi*real k/real n)"
      have "fst w = c * fst z - s * snd z" and "snd w = s * fst z + c * snd z"
        using hz(2) unfolding rot_def c_def s_def by (by100 simp)+
      hence "fst w ^ 2 + snd w ^ 2 = (c^2 + s^2) * ((fst z)^2 + (snd z)^2)"
        by (by5000 algebra)
      also have "\<dots> = 1" using sin_cos_squared_add[of "2*pi*real k/real n"]
          \<open>fst z ^ 2 + snd z ^ 2 = 1\<close> unfolding c_def s_def by (by5000 algebra)
      finally show "w \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    qed
    have hsat_eq: "sat = C \<union> (\<Union>k\<in>{..<n}. rot k ` (C \<inter> top1_S1))"
    proof (rule set_eqI, rule iffI)
      fix z assume "z \<in> sat"
      hence hz_B2: "z \<in> top1_B2" and hqz: "q z \<in> q ` C" unfolding sat_def by (by100 blast)+
      from hqz obtain w where hw_C: "w \<in> C" and hqeq: "q z = q w" by (by100 blast)
      have hw_B2: "w \<in> top1_B2" using hw_C hC_sub by (by100 blast)
      show "z \<in> C \<union> (\<Union>k\<in>{..<n}. rot k ` (C \<inter> top1_S1))"
      proof (cases "z \<in> top1_S1")
        case False
        \<comment> \<open>z \<in> B2 - S1. Then w must also be in B2 - S1 (by hq\_sep: interior \<noteq> boundary).\<close>
        hence hz_int: "z \<in> top1_B2 - top1_S1" using hz_B2 by (by100 blast)
        have hw_int: "w \<in> top1_B2 - top1_S1"
        proof (rule ccontr)
          assume "\<not> w \<in> top1_B2 - top1_S1"
          hence "w \<in> top1_S1" using hw_B2 by (by100 blast)
          from hq_sep hz_int \<open>w \<in> top1_S1\<close> have "q z \<noteq> q w" by (by100 blast)
          thus False using hqeq by (by100 blast)
        qed
        \<comment> \<open>Both in interior: q injective \<Rightarrow> z = w \<in> C.\<close>
        from hq_inj have "z = w" using hz_int hw_int hqeq unfolding inj_on_def by (by100 blast)
        thus ?thesis using hw_C by (by100 blast)
      next
        case True
        \<comment> \<open>z \<in> S1. Then w must also be in S1.\<close>
        have hw_S1: "w \<in> top1_S1"
        proof (rule ccontr)
          assume "\<not> w \<in> top1_S1"
          hence "w \<in> top1_B2 - top1_S1" using hw_B2 by (by100 blast)
          from hq_sep this True have "q w \<noteq> q z" by (by100 blast)
          thus False using hqeq by (by100 simp)
        qed
        \<comment> \<open>Both on S1: q z = q w means z is a rotation of w.\<close>
        from hq_S1[rule_format, OF hw_S1 True] hqeq
        have "\<exists>k::nat. k < n \<and> z = (cos (2*pi*real k/real n) * fst w - sin (2*pi*real k/real n) * snd w,
              sin (2*pi*real k/real n) * fst w + cos (2*pi*real k/real n) * snd w)"
          by (by100 simp)
        then obtain k where "k < n" "z = rot k w" unfolding rot_def by (by100 blast)
        hence "z \<in> rot k ` (C \<inter> top1_S1)" using hw_C hw_S1 by (by100 blast)
        thus ?thesis using \<open>k < n\<close> by (by100 blast)
      qed
    next
      fix z assume "z \<in> C \<union> (\<Union>k\<in>{..<n}. rot k ` (C \<inter> top1_S1))"
      thus "z \<in> sat"
      proof
        assume "z \<in> C"
        thus ?thesis unfolding sat_def using hC_sub by (by100 blast)
      next
        assume "z \<in> (\<Union>k\<in>{..<n}. rot k ` (C \<inter> top1_S1))"
        then obtain k w where hk: "k < n" and hw: "w \<in> C" "w \<in> top1_S1" and hzw: "z = rot k w"
          by (by100 blast)
        \<comment> \<open>z = rot k(w) \<in> S1 \<subseteq> B2.\<close>
        have "rot k w \<in> top1_S1"
        proof -
          have "rot k ` top1_S1 \<subseteq> top1_S1" by (rule hrot_S1_gen)
          thus ?thesis using hw(2) by (by100 blast)
        qed
        hence hz_B2: "z \<in> top1_B2" using hzw hS1_sub_B2 by (by100 blast)
        \<comment> \<open>q(z) = q(rot k(w)) = q(w) (by the identification on S1).\<close>
        have "q z = q w"
        proof -
          from hq_S1[rule_format, OF hw(2) \<open>rot k w \<in> top1_S1\<close>]
          have "q w = q (rot k w) \<longleftrightarrow> (\<exists>j::nat. j < n \<and>
              rot k w = (cos (2*pi*real j/real n) * fst w - sin (2*pi*real j/real n) * snd w,
                         sin (2*pi*real j/real n) * fst w + cos (2*pi*real j/real n) * snd w))"
            by (by100 simp)
          moreover have "rot k w = (cos (2*pi*real k/real n) * fst w - sin (2*pi*real k/real n) * snd w,
              sin (2*pi*real k/real n) * fst w + cos (2*pi*real k/real n) * snd w)"
            unfolding rot_def by (by100 simp)
          ultimately have "q w = q (rot k w)" using hk by (by100 blast)
          thus ?thesis using hzw by (by100 simp)
        qed
        hence "q z \<in> q ` C" using hw(1) by (by100 blast)
        thus ?thesis unfolding sat_def using hz_B2 by (by100 blast)
      qed
    qed
    \<comment> \<open>Step 2: Each rot k ` (C \<inter> S1) is closed in B2.
       rot k is a homeomorphism S1 \<rightarrow> S1 (rotation).
       C \<inter> S1 is closed in S1 (intersection of closed sets).
       Image of closed under homeomorphism is closed.
       Closed in S1 + S1 closed in B2 \<Rightarrow> closed in B2.\<close>
    have hrot_img_closed: "\<And>k. k < n \<Longrightarrow>
        closedin_on top1_B2 top1_B2_topology (rot k ` (C \<inter> top1_S1))"
    proof -
      fix k assume "k < n"
      \<comment> \<open>rot k maps S1 to S1 (rotation preserves norm).\<close>
      have hrot_S1: "rot k ` top1_S1 \<subseteq> top1_S1" by (rule hrot_S1_gen)
      \<comment> \<open>rot k is continuous on S1 (composition of continuous functions).\<close>
      \<comment> \<open>C \<inter> S1 is closed in S1 (C closed in B2, S1 \<subseteq> B2).\<close>
      have hCS1_closed_S1: "closedin_on top1_S1 top1_S1_topology (C \<inter> top1_S1)"
      proof -
        have "top1_S1 \<subseteq> top1_B2" unfolding top1_S1_def top1_B2_def by (by100 auto)
        have hB2_top: "is_topology_on top1_B2 top1_B2_topology"
          using hB2_haus unfolding is_hausdorff_on_def by (by100 blast)
        from Theorem_17_2[OF hB2_top \<open>top1_S1 \<subseteq> top1_B2\<close>, of "C \<inter> top1_S1"]
        have "closedin_on top1_S1 (subspace_topology top1_B2 top1_B2_topology top1_S1) (C \<inter> top1_S1)
            \<longleftrightarrow> (\<exists>D. closedin_on top1_B2 top1_B2_topology D \<and> C \<inter> top1_S1 = D \<inter> top1_S1)"
          by (by100 blast)
        moreover have "\<exists>D. closedin_on top1_B2 top1_B2_topology D \<and> C \<inter> top1_S1 = D \<inter> top1_S1"
          using hC by (rule_tac x=C in exI) (by100 blast)
        moreover have "subspace_topology top1_B2 top1_B2_topology top1_S1 = top1_S1_topology"
        proof -
          from subspace_topology_trans[OF \<open>top1_S1 \<subseteq> top1_B2\<close>]
          show ?thesis unfolding top1_S1_topology_def top1_B2_topology_def by (by100 simp)
        qed
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>rot k ` (C \<inter> S1) is closed in S1 (continuous image of compact in Hausdorff,
         or homeomorphism preserves closed).\<close>
      have "closedin_on top1_S1 top1_S1_topology (rot k ` (C \<inter> top1_S1))"
      proof -
        \<comment> \<open>rot k is continuous on S1 (composition of continuous functions).\<close>
        have hrot_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (rot k)"
        proof -
          \<comment> \<open>rot k is continuous on UNIV (linear map, hence continuous).\<close>
          have hrot_cont_UNIV: "continuous_on UNIV (rot k)"
            unfolding rot_def by (intro continuous_intros)
          \<comment> \<open>rot k maps S1 to S1.\<close>
          have hrot_img: "\<And>p. p \<in> top1_S1 \<Longrightarrow> rot k p \<in> top1_S1"
            using hrot_S1 by (by100 blast)
          \<comment> \<open>Apply the subspace continuity lemma.\<close>
          from top1_continuous_map_on_real2_subspace[OF hrot_img hrot_cont_UNIV]
          show ?thesis unfolding top1_S1_topology_def .
        qed
        \<comment> \<open>S1 is compact and Hausdorff.\<close>
        have hS1_haus: "is_hausdorff_on top1_S1 top1_S1_topology"
        proof -
          have hS1_sub: "top1_S1 \<subseteq> top1_B2" unfolding top1_S1_def top1_B2_def by (by100 auto)
          from conjunct2[OF conjunct2[OF Theorem_17_11]] hB2_haus hS1_sub
          have "is_hausdorff_on top1_S1 (subspace_topology top1_B2 top1_B2_topology top1_S1)"
            by (by100 blast)
          moreover have "subspace_topology top1_B2 top1_B2_topology top1_S1 = top1_S1_topology"
            using subspace_topology_trans[OF hS1_sub]
            unfolding top1_S1_topology_def top1_B2_topology_def by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        \<comment> \<open>Compact + Hausdorff + continuous + closed C∩S1 \<Rightarrow> image closed.\<close>
        show ?thesis
          by (rule compact_hausdorff_continuous_closed_map[OF S1_compact hS1_haus hrot_cont hCS1_closed_S1])
      qed
      \<comment> \<open>Closed in S1 + S1 closed in B2 \<Rightarrow> closed in B2.\<close>
      moreover have "closedin_on top1_B2 top1_B2_topology top1_S1"
        by (rule S1_closed_in_B2)
      ultimately show "closedin_on top1_B2 top1_B2_topology (rot k ` (C \<inter> top1_S1))"
      proof -
        assume hcl_S1: "closedin_on top1_S1 top1_S1_topology (rot k ` (C \<inter> top1_S1))"
            and hS1_cl: "closedin_on top1_B2 top1_B2_topology top1_S1"
        have hB2_top: "is_topology_on top1_B2 top1_B2_topology"
          using hB2_haus unfolding is_hausdorff_on_def by (by100 blast)
        have "top1_S1_topology = subspace_topology top1_B2 top1_B2_topology top1_S1"
        proof -
          have "top1_S1 \<subseteq> top1_B2" unfolding top1_S1_def top1_B2_def by (by100 auto)
          from subspace_topology_trans[OF this]
          show ?thesis unfolding top1_S1_topology_def top1_B2_topology_def by (by100 simp)
        qed
        hence "closedin_on top1_S1 (subspace_topology top1_B2 top1_B2_topology top1_S1)
            (rot k ` (C \<inter> top1_S1))" using hcl_S1 by (by100 simp)
        thus ?thesis by (rule Theorem_17_3[OF hB2_top hS1_cl])
      qed
    qed
    \<comment> \<open>Step 3: sat is closed (C closed + finite union of closed).\<close>
    have "closedin_on top1_B2 top1_B2_topology sat"
    proof -
      have "closedin_on top1_B2 top1_B2_topology (\<Union>k\<in>{..<n}. rot k ` (C \<inter> top1_S1))"
      proof -
        have hB2_top: "is_topology_on top1_B2 top1_B2_topology"
          using hB2_haus unfolding is_hausdorff_on_def by (by100 blast)
        have hfin: "finite ((\<lambda>k. rot k ` (C \<inter> top1_S1)) ` {..<n})" by (by100 simp)
        have "\<forall>A\<in>((\<lambda>k. rot k ` (C \<inter> top1_S1)) ` {..<n}). closedin_on top1_B2 top1_B2_topology A"
          using hrot_img_closed by (by100 blast)
        from closedin_Union_finite[OF hB2_top hfin this]
        have "closedin_on top1_B2 top1_B2_topology (\<Union>((\<lambda>k. rot k ` (C \<inter> top1_S1)) ` {..<n}))" .
        moreover have "\<Union>((\<lambda>k. rot k ` (C \<inter> top1_S1)) ` {..<n}) = (\<Union>k\<in>{..<n}. rot k ` (C \<inter> top1_S1))"
          by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      hence "closedin_on top1_B2 top1_B2_topology (C \<union> (\<Union>k\<in>{..<n}. rot k ` (C \<inter> top1_S1)))"
      proof -
        assume horbit_cl: "closedin_on top1_B2 top1_B2_topology (\<Union>k\<in>{..<n}. rot k ` (C \<inter> top1_S1))"
        have hB2_top: "is_topology_on top1_B2 top1_B2_topology"
          using hB2_haus unfolding is_hausdorff_on_def by (by100 blast)
        have "finite {C, \<Union>k\<in>{..<n}. rot k ` (C \<inter> top1_S1)}" by (by100 simp)
        moreover have hall: "\<forall>A\<in>{C, \<Union>k\<in>{..<n}. rot k ` (C \<inter> top1_S1)}.
            closedin_on top1_B2 top1_B2_topology A"
          using hC horbit_cl by (by100 blast)
        from closedin_Union_finite[OF hB2_top calculation hall]
        have "closedin_on top1_B2 top1_B2_topology (\<Union>{C, \<Union>k\<in>{..<n}. rot k ` (C \<inter> top1_S1)})" .
        moreover have "\<Union>{C, \<Union>k\<in>{..<n}. rot k ` (C \<inter> top1_S1)}
            = C \<union> (\<Union>k\<in>{..<n}. rot k ` (C \<inter> top1_S1))" by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      thus ?thesis using hsat_eq by (by100 simp)
    qed
    \<comment> \<open>Step 4: sat is saturated (q\<inverse>(q(C)) = sat by definition).\<close>
    have "q ` C \<subseteq> X" using hC_sub hq_surj by (by100 blast)
    moreover have "X - q ` C \<in> TX"
    proof -
      have "{z \<in> top1_B2. q z \<in> X - q ` C} = top1_B2 - sat"
        unfolding sat_def using hq_surj by (by5000 blast)
      moreover have "top1_B2 - sat \<in> top1_B2_topology"
        using \<open>closedin_on top1_B2 top1_B2_topology sat\<close> unfolding closedin_on_def by (by100 blast)
      ultimately have "{z \<in> top1_B2. q z \<in> X - q ` C} \<in> top1_B2_topology" by (by100 simp)
      moreover have "X - q ` C \<subseteq> X" by (by100 blast)
      ultimately show ?thesis using hq_quot unfolding top1_quotient_map_on_def by (by100 blast)
    qed
    ultimately show "closedin_on X TX (q ` C)" unfolding closedin_on_def by (by100 blast)
  qed
  \<comment> \<open>With q closed, X is Hausdorff by Lemma 73.3 (Munkres):
     closed quotient map from normal space gives Hausdorff target.\<close>
  show ?thesis
    unfolding is_hausdorff_on_def neighborhood_of_def
  proof (intro conjI ballI impI)
    show "is_topology_on X TX" by (rule hTX)
  next
    fix x y assume hx: "x \<in> X" and hy: "y \<in> X" and hne: "x \<noteq> y"
    \<comment> \<open>Fibers q\<inverse>({x}), q\<inverse>({y}) are closed in B2 (finite in Hausdorff).\<close>
    \<comment> \<open>Fibers are finite (at most n+1 points), hence closed in Hausdorff B2.\<close>
    have hfiber_finite: "\<And>p. p \<in> X \<Longrightarrow> finite {z \<in> top1_B2. q z = p}"
    proof -
      fix p assume hp: "p \<in> X"
      \<comment> \<open>Split fiber into interior and circle parts.\<close>
      have hS1_sub: "top1_S1 \<subseteq> top1_B2"
        unfolding top1_S1_def top1_B2_def by (by100 auto)
      have hsplit: "{z \<in> top1_B2. q z = p} =
          {z \<in> top1_B2 - top1_S1. q z = p} \<union> {z \<in> top1_S1. q z = p}"
        using hS1_sub by (by100 blast)
      \<comment> \<open>Interior part: at most 1 point (q injective on B2 - S1).\<close>
      have "finite {z \<in> top1_B2 - top1_S1. q z = p}"
      proof -
        have "{z \<in> top1_B2 - top1_S1. q z = p} = {z \<in> top1_B2 - top1_S1. q z \<in> {p}}"
          by (by100 blast)
        moreover have "finite {z \<in> top1_B2 - top1_S1. q z \<in> {p}}"
          by (rule finite_inverse_image_gen[OF _ hq_inj]) (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>Circle part: at most n points (orbit under n-fold rotation).\<close>
      moreover have "finite {z \<in> top1_S1. q z = p}"
      proof (cases "\<exists>z0 \<in> top1_S1. q z0 = p")
        case False
        hence hempty: "{z \<in> top1_S1. q z = p} = {}" by (by5000 blast)
        show ?thesis unfolding hempty by (by100 simp)
      next
        case True
        then obtain z0 where hz0: "z0 \<in> top1_S1" "q z0 = p" by (by100 blast)
        \<comment> \<open>Any z \<in> S1 with q(z) = p = q(z0) must be a rotation of z0.\<close>
        have "{z \<in> top1_S1. q z = p} \<subseteq>
            (\<lambda>k. (cos (2*pi*real k/real n) * fst z0 - sin (2*pi*real k/real n) * snd z0,
                  sin (2*pi*real k/real n) * fst z0 + cos (2*pi*real k/real n) * snd z0)) ` {..<n}"
        proof
          fix z assume "z \<in> {z \<in> top1_S1. q z = p}"
          hence "z \<in> top1_S1" "q z = p" by (by100 blast)+
          hence "q z = q z0" using hz0 by (by100 simp)
          from hq_S1[rule_format, OF hz0(1) \<open>z \<in> top1_S1\<close>]
          have "q z0 = q z \<longleftrightarrow> (\<exists>k::nat. k < n \<and>
              z = (cos (2*pi*real k/real n) * fst z0 - sin (2*pi*real k/real n) * snd z0,
                   sin (2*pi*real k/real n) * fst z0 + cos (2*pi*real k/real n) * snd z0))"
            by (by100 simp)
          with \<open>q z = q z0\<close> show "z \<in> (\<lambda>k. (cos (2*pi*real k/real n) * fst z0 - sin (2*pi*real k/real n) * snd z0,
              sin (2*pi*real k/real n) * fst z0 + cos (2*pi*real k/real n) * snd z0)) ` {..<n}"
            by (by5000 force)
        qed
        moreover have "finite ((\<lambda>k. (cos (2*pi*real k/real n) * fst z0 - sin (2*pi*real k/real n) * snd z0,
            sin (2*pi*real k/real n) * fst z0 + cos (2*pi*real k/real n) * snd z0)) ` {..<n})"
          by (by100 simp)
        ultimately show ?thesis using finite_subset by (by100 blast)
      qed
      ultimately show "finite {z \<in> top1_B2. q z = p}" using hsplit by (by100 simp)
    qed
    have hB2_T1: "top1_T1_on top1_B2 top1_B2_topology"
      by (rule hausdorff_imp_T1_on[OF hB2_haus])
    have hfiber_closed: "\<And>p. p \<in> X \<Longrightarrow> closedin_on top1_B2 top1_B2_topology {z \<in> top1_B2. q z = p}"
    proof -
      fix p assume "p \<in> X"
      have "{z \<in> top1_B2. q z = p} \<subseteq> top1_B2" by (by100 blast)
      have "finite {z \<in> top1_B2. q z = p}" by (rule hfiber_finite[OF \<open>p \<in> X\<close>])
      \<comment> \<open>Finite subset of T1 space is closed.\<close>
      \<comment> \<open>Finite set = finite union of singletons; each singleton closed in T1; union closed.\<close>
      have "{z \<in> top1_B2. q z = p} = \<Union>((\<lambda>z. {z}) ` {z \<in> top1_B2. q z = p})"
        by (by100 blast)
      moreover have "finite ((\<lambda>z. {z}) ` {z \<in> top1_B2. q z = p})"
        using \<open>finite {z \<in> top1_B2. q z = p}\<close> by (by100 simp)
      moreover have "\<forall>A\<in>((\<lambda>z. {z}) ` {z \<in> top1_B2. q z = p}).
          closedin_on top1_B2 top1_B2_topology A"
      proof (intro ballI)
        fix A assume "A \<in> (\<lambda>z. {z}) ` {z \<in> top1_B2. q z = p}"
        then obtain z where "z \<in> top1_B2" "A = {z}" by (by100 blast)
        thus "closedin_on top1_B2 top1_B2_topology A"
          using hB2_T1 unfolding top1_T1_on_def by (by100 blast)
      qed
      moreover have "is_topology_on top1_B2 top1_B2_topology"
        using hB2_haus unfolding is_hausdorff_on_def by (by100 blast)
      ultimately show "closedin_on top1_B2 top1_B2_topology {z \<in> top1_B2. q z = p}"
      proof -
        assume heq: "{z \<in> top1_B2. q z = p} = \<Union>((\<lambda>z. {z}) ` {z \<in> top1_B2. q z = p})"
            and hfin: "finite ((\<lambda>z. {z}) ` {z \<in> top1_B2. q z = p})"
            and hall: "\<forall>A\<in>((\<lambda>z. {z}) ` {z \<in> top1_B2. q z = p}). closedin_on top1_B2 top1_B2_topology A"
            and htop: "is_topology_on top1_B2 top1_B2_topology"
        from closedin_Union_finite[OF htop hfin hall]
        show ?thesis using heq by (by100 simp)
      qed
    qed
    have hFx_closed: "closedin_on top1_B2 top1_B2_topology {z \<in> top1_B2. q z = x}"
      by (rule hfiber_closed[OF hx])
    have hFy_closed: "closedin_on top1_B2 top1_B2_topology {z \<in> top1_B2. q z = y}"
      by (rule hfiber_closed[OF hy])
    have hF_disj: "{z \<in> top1_B2. q z = x} \<inter> {z \<in> top1_B2. q z = y} = {}"
      using hne by (by100 blast)
    \<comment> \<open>By normality: separate fibers, push forward through quotient.\<close>
    \<comment> \<open>Step 1: B2 normal, separate closed disjoint fibers by open U, V.\<close>
    obtain U V where hU_open: "U \<in> top1_B2_topology" and hV_open: "V \<in> top1_B2_topology"
        and hFx_U: "{z \<in> top1_B2. q z = x} \<subseteq> U" and hFy_V: "{z \<in> top1_B2. q z = y} \<subseteq> V"
        and hUV_disj: "U \<inter> V = {}"
    proof -
      from hB2_normal hFx_closed hFy_closed hF_disj
      have "\<exists>U V. U \<in> top1_B2_topology \<and> V \<in> top1_B2_topology
          \<and> {z \<in> top1_B2. q z = x} \<subseteq> U \<and> {z \<in> top1_B2. q z = y} \<subseteq> V \<and> U \<inter> V = {}"
        unfolding top1_normal_on_def by (by5000 blast)
      thus ?thesis using that by (by5000 blast)
    qed
    \<comment> \<open>Step 2: Define saturated open neighborhoods in X.
       Let U0 = X - q(B2 - U) and V0 = X - q(B2 - V).
       These are open in X (B2-U and B2-V are closed, q is closed map, so q(B2-U) closed in X).
       x \<in> U0 (because q\<inverse>(x) \<subseteq> U, so q\<inverse>(x) \<inter> (B2-U) = {}, so x \<notin> q(B2-U)).
       Similarly y \<in> V0. And U0 \<inter> V0 = {} (from U \<inter> V = {}).\<close>
    let ?U0 = "X - q ` (top1_B2 - U)"
    let ?V0 = "X - q ` (top1_B2 - V)"
    have hU_sub: "U \<subseteq> top1_B2"
    proof -
      from hU_open have "U \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_B2"
        unfolding top1_B2_topology_def .
      thus ?thesis unfolding subspace_topology_def by (by100 blast)
    qed
    have hV_sub: "V \<subseteq> top1_B2"
    proof -
      from hV_open have "V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_B2"
        unfolding top1_B2_topology_def .
      thus ?thesis unfolding subspace_topology_def by (by100 blast)
    qed
    have hB2U_closed: "closedin_on top1_B2 top1_B2_topology (top1_B2 - U)"
    proof -
      have "top1_B2 - U \<subseteq> top1_B2" by (by100 blast)
      moreover have "top1_B2 - (top1_B2 - U) = U" using hU_sub by (by100 blast)
      hence "top1_B2 - (top1_B2 - U) \<in> top1_B2_topology" using hU_open by (by100 simp)
      ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
    qed
    have hB2V_closed: "closedin_on top1_B2 top1_B2_topology (top1_B2 - V)"
    proof -
      have "top1_B2 - V \<subseteq> top1_B2" by (by100 blast)
      moreover have "top1_B2 - (top1_B2 - V) = V" using hV_sub by (by100 blast)
      hence "top1_B2 - (top1_B2 - V) \<in> top1_B2_topology" using hV_open by (by100 simp)
      ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
    qed
    have hqU_closed: "closedin_on X TX (q ` (top1_B2 - U))"
      using hq_closed hB2U_closed by (by100 blast)
    have hqV_closed: "closedin_on X TX (q ` (top1_B2 - V))"
      using hq_closed hB2V_closed by (by100 blast)
    have hU0_open: "?U0 \<in> TX"
      using hqU_closed unfolding closedin_on_def by (by100 blast)
    have hV0_open: "?V0 \<in> TX"
      using hqV_closed unfolding closedin_on_def by (by100 blast)
    have "x \<in> ?U0"
    proof -
      have "x \<in> X" by (rule hx)
      moreover have "x \<notin> q ` (top1_B2 - U)"
      proof
        assume "x \<in> q ` (top1_B2 - U)"
        then obtain z where "z \<in> top1_B2 - U" "q z = x" by (by100 blast)
        hence "z \<in> {z \<in> top1_B2. q z = x}" by (by100 blast)
        hence "z \<in> U" using hFx_U by (by100 blast)
        thus False using \<open>z \<in> top1_B2 - U\<close> by (by100 blast)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    have "y \<in> ?V0"
    proof -
      have "y \<in> X" by (rule hy)
      moreover have "y \<notin> q ` (top1_B2 - V)"
      proof
        assume "y \<in> q ` (top1_B2 - V)"
        then obtain z where "z \<in> top1_B2 - V" "q z = y" by (by100 blast)
        hence "z \<in> {z \<in> top1_B2. q z = y}" by (by100 blast)
        hence "z \<in> V" using hFy_V by (by100 blast)
        thus False using \<open>z \<in> top1_B2 - V\<close> by (by100 blast)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    have "?U0 \<inter> ?V0 = {}"
    proof -
      have "\<forall>w. w \<in> ?U0 \<longrightarrow> w \<notin> ?V0"
      proof (intro allI impI)
        fix w assume "w \<in> ?U0"
        hence hw: "w \<in> X" "w \<notin> q ` (top1_B2 - U)" by (by100 blast)+
        \<comment> \<open>w \<in> X = q(B2), so w = q(z) for some z. z \<notin> B2-U (since w \<notin> q(B2-U)), so z \<in> U.
           But U \<inter> V = {}, so z \<notin> V, so z \<in> B2-V, so w = q(z) \<in> q(B2-V), so w \<notin> V0.\<close>
        obtain z where hz: "z \<in> top1_B2" "q z = w" using hw(1) hq_surj by (by100 blast)
        have "z \<notin> top1_B2 - U" using hw(2) hz by (by100 blast)
        hence "z \<in> U" using hz(1) by (by100 blast)
        hence "z \<notin> V" using hUV_disj by (by100 blast)
        hence "z \<in> top1_B2 - V" using hz(1) by (by100 blast)
        hence "w \<in> q ` (top1_B2 - V)" using hz by (by100 blast)
        thus "w \<notin> ?V0" by (by100 blast)
      qed
      thus ?thesis by (by100 blast)
    qed
    show "\<exists>Ux Vy. (Ux \<in> TX \<and> x \<in> Ux) \<and> (Vy \<in> TX \<and> y \<in> Vy) \<and> Ux \<inter> Vy = {}"
      using hU0_open hV0_open \<open>x \<in> ?U0\<close> \<open>y \<in> ?V0\<close> \<open>?U0 \<inter> ?V0 = {}\<close> by (by100 blast)
  qed
qed
text \<open>The 1-skeleton q(S1) of the dunce cap is homeomorphic to S1.
  This follows from Munkres \<S>73: the map g(t) = q(cos(2\<pi>t/n), sin(2\<pi>t/n))
  factors through R\_to\_S1 to give a homeomorphism S1 \<rightarrow> q(S1).\<close>
lemma dunce_cap_skeleton_is_circle:
  assumes "top1_is_dunce_cap_on X TX n"
      and "top1_quotient_map_on top1_B2 top1_B2_topology X TX q"
      and "\<forall>z\<in>top1_S1. \<forall>z'\<in>top1_S1. q z = q z' \<longleftrightarrow>
            (\<exists>k::nat. k < n \<and>
               z' = (cos (2*pi*real k/real n) * fst z - sin (2*pi*real k/real n) * snd z,
                     sin (2*pi*real k/real n) * fst z + cos (2*pi*real k/real n) * snd z))"
  shows "\<exists>f. top1_homeomorphism_on top1_S1 top1_S1_topology
      (q ` top1_S1) (subspace_topology X TX (q ` top1_S1)) f"
proof -
  \<comment> \<open>Munkres \<S>73.4: h maps arc C from p to r(p) onto A = h(S1), injective except endpoints.
     Formal route: define g(t) = q(R\_to\_S1(t/n)). g is a loop. Factor through R\_to\_S1
     to get h: S1 \<rightarrow> q(S1). Prove h is a continuous bijection. Compact-to-Hausdorff.\<close>
  have hn_pos: "n > 0" using assms(1) unfolding top1_is_dunce_cap_on_def by (by100 blast)
  let ?A = "q ` top1_S1"
  let ?TA = "subspace_topology X TX ?A"
  have hTX_strict: "is_topology_on_strict X TX"
    using assms(1) unfolding top1_is_dunce_cap_on_def by (by100 blast)
  have hTX: "is_topology_on X TX"
    using hTX_strict unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>Step 1 (book): define g(t) = q(cos(2\<pi>t/n), sin(2\<pi>t/n)) = q(R\_to\_S1(t/n)).\<close>
  define g where "g \<equiv> \<lambda>t::real. q (top1_R_to_S1 (t / real n))"
  \<comment> \<open>g(0) = g(1) = q(1,0): g is a loop.\<close>
  have hg0: "g 0 = q (1, 0)"
    unfolding g_def top1_R_to_S1_def by (by100 simp)
  have hg1: "g 1 = q (1, 0)"
  proof -
    \<comment> \<open>g(1) = q(R\_to\_S1(1/n)). R\_to\_S1(1/n) is rotation of (1,0) by 2\<pi>/n.
       By quotient relation (k=1 when n>1, or k=0 when n=1), q identifies this with (1,0).\<close>
    have "top1_R_to_S1 (1 / real n) \<in> top1_S1"
      unfolding top1_R_to_S1_def top1_S1_def
      using sin_cos_squared_add[of "2 * pi * (1 / real n)"] by (by100 auto)
    have "(1::real, 0::real) \<in> top1_S1"
      unfolding top1_S1_def by (by100 simp)
    \<comment> \<open>R\_to\_S1(1/n) = (cos(2\<pi>/n), sin(2\<pi>/n)) = rotation of (1,0) by 2\<pi>/n.\<close>
    have hRn: "top1_R_to_S1 (1 / real n) = (cos (2*pi/real n), sin (2*pi/real n))"
      unfolding top1_R_to_S1_def by (by100 simp)
    \<comment> \<open>This is rotation by 2\<pi>/n of (1,0), i.e., the k=1 case (or k=0 for n=1).\<close>
    have "q (1, 0) = q (top1_R_to_S1 (1 / real n))"
    proof (cases "n = 1")
      case True
      \<comment> \<open>n=1: R\_to\_S1(1/1) = R\_to\_S1(1) = (cos 2\<pi>, sin 2\<pi>) = (1, 0).\<close>
      hence "top1_R_to_S1 (1 / real n) = top1_R_to_S1 1"
        by (by100 simp)
      also have "\<dots> = (1, 0)"
        unfolding top1_R_to_S1_def by (by100 simp)
      finally show ?thesis by (by100 simp)
    next
      case False
      hence h1n: "(1::nat) < n" using hn_pos by (by100 simp)
      \<comment> \<open>k=1: rotation of (1,0) by 2\<pi>\<cdot>1/n gives R\_to\_S1(1/n).\<close>
      have "top1_R_to_S1 (1 / real n) =
          (cos (2*pi*real (1::nat)/real n) * fst (1::real, 0::real) - sin (2*pi*real (1::nat)/real n) * snd (1::real, 0::real),
           sin (2*pi*real (1::nat)/real n) * fst (1::real, 0::real) + cos (2*pi*real (1::nat)/real n) * snd (1::real, 0::real))"
        using hRn by (by100 simp)
      hence "\<exists>k::nat. k < n \<and> top1_R_to_S1 (1 / real n) =
          (cos (2*pi*real k/real n) * fst (1::real, 0::real) - sin (2*pi*real k/real n) * snd (1::real, 0::real),
           sin (2*pi*real k/real n) * fst (1::real, 0::real) + cos (2*pi*real k/real n) * snd (1::real, 0::real))"
        using h1n by (rule_tac x=1 in exI, by100 blast)
      with assms(3)[rule_format, OF \<open>(1::real, 0) \<in> top1_S1\<close> \<open>top1_R_to_S1 (1 / real n) \<in> top1_S1\<close>]
      show ?thesis by (by100 blast)
    qed
    thus ?thesis unfolding g_def by (by100 simp)
  qed
  have hg_loop: "g 0 = g 1" using hg0 hg1 by (by100 simp)
  \<comment> \<open>g maps [0,1] into q(S1).\<close>
  have hg_range: "\<forall>t\<in>top1_unit_interval. g t \<in> ?A"
  proof (intro ballI)
    fix t assume "t \<in> top1_unit_interval"
    have "top1_R_to_S1 (t / real n) \<in> top1_S1"
      unfolding top1_R_to_S1_def top1_S1_def
      using sin_cos_squared_add[of "2 * pi * (t / real n)"] by (by100 auto)
    thus "g t \<in> ?A" unfolding g_def by (by100 blast)
  qed
  \<comment> \<open>g is continuous from [0,1] to X.\<close>
  have hg_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX g"
  proof -
    \<comment> \<open>g = q \<circ> R\_to\_S1 \<circ> (\<lambda>t. t/n). Each piece is continuous.\<close>
    have hq_cont: "top1_continuous_map_on top1_B2 top1_B2_topology X TX q"
      using assms(2) unfolding top1_quotient_map_on_def by (by100 blast)
    have hR_cont: "top1_continuous_map_on (UNIV::real set) top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
      using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
    have hS1_B2: "top1_S1 \<subseteq> top1_B2"
      unfolding top1_S1_def top1_B2_def by (by100 auto)
    \<comment> \<open>R\_to\_S1: R \<rightarrow> B2 (via S1 \<subseteq> B2).\<close>
    have hR_B2: "top1_continuous_map_on (UNIV::real set) top1_open_sets top1_B2 top1_B2_topology top1_R_to_S1"
    proof -
      let ?Z = "UNIV :: (real \<times> real) set"
      let ?TZ = "product_topology_on top1_open_sets top1_open_sets"
      have hS1_eq: "top1_S1_topology = subspace_topology ?Z ?TZ top1_S1"
        unfolding top1_S1_topology_def by (by100 simp)
      have hB2_eq: "top1_B2_topology = subspace_topology ?Z ?TZ top1_B2"
        unfolding top1_B2_topology_def by (by100 simp)
      have hB2_Z: "top1_B2 \<subseteq> ?Z" by (by100 blast)
      have "top1_continuous_map_on (UNIV::real set) top1_open_sets top1_S1
          (subspace_topology ?Z ?TZ top1_S1) top1_R_to_S1"
        using hR_cont hS1_eq by (by100 simp)
      from top1_continuous_map_on_codomain_enlarge[OF this hS1_B2 hB2_Z]
      show ?thesis using hB2_eq by (by100 simp)
    qed
    \<comment> \<open>Compose: q \<circ> R\_to\_S1: R \<rightarrow> X continuous.\<close>
    have hqR: "top1_continuous_map_on (UNIV::real set) top1_open_sets X TX (q \<circ> top1_R_to_S1)"
      by (rule top1_continuous_map_on_comp[OF hR_B2 hq_cont])
    \<comment> \<open>Division by n: [0,1] \<rightarrow> R continuous. Route: Theorem 18.2 restriction.\<close>
    have hI_sub: "top1_unit_interval \<subseteq> (UNIV :: real set)" by (by100 blast)
    have hI_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
      by (rule top1_unit_interval_topology_is_topology_on)
    have hR_top: "is_topology_on (UNIV :: real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    \<comment> \<open>Restriction: if f: X \<rightarrow> Y continuous and A \<subseteq> X, then f|\_A: A \<rightarrow> Y continuous.\<close>
    \<comment> \<open>t \<mapsto> t/n is continuous on [0,1]: use continuous\_on from HOL-Analysis + conversion.\<close>
    have h_div: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
        (UNIV::real set) top1_open_sets (\<lambda>t. t / real n)"
    proof -
      have hn_ne: "real n \<noteq> 0" using hn_pos by (by100 simp)
      have "continuous_on top1_unit_interval (\<lambda>t::real. t * (1 / real n))"
        by (intro continuous_intros)
      hence "continuous_on top1_unit_interval (\<lambda>t::real. t / real n)"
        by (by100 simp)
      from top1_continuous_map_on_subspace_open_sets_on[OF _ this]
      have "top1_continuous_map_on top1_unit_interval (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval)
          (UNIV::real set) (subspace_topology (UNIV::real set) top1_open_sets (UNIV::real set)) (\<lambda>t. t / real n)"
        by (by100 blast)
      moreover have "subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval = top1_unit_interval_topology"
        unfolding top1_unit_interval_topology_def by (by100 simp)
      moreover have "subspace_topology (UNIV::real set) top1_open_sets (UNIV::real set) = top1_open_sets"
        unfolding subspace_topology_def by (by100 auto)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Compose: (q \<circ> R\_to\_S1) \<circ> (\<cdot>/n): [0,1] \<rightarrow> X continuous.\<close>
    have hcomp: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX
        ((q \<circ> top1_R_to_S1) \<circ> (\<lambda>t. t / real n))"
      by (rule top1_continuous_map_on_comp[OF h_div hqR])
    \<comment> \<open>g = (q \<circ> R\_to\_S1) \<circ> (\<cdot>/n).\<close>
    have "g = (q \<circ> top1_R_to_S1) \<circ> (\<lambda>t. t / real n)" unfolding g_def by (by100 auto)
    thus ?thesis using hcomp by (by100 simp)
  qed
  \<comment> \<open>Step 2: g is a loop in q(S1), so factor through R\_to\_S1.\<close>
  have hg_is_loop: "top1_is_loop_on X TX (q (1, 0)) g"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hg_cont hg0 hg1 by (by100 blast)
  have hA_sub: "?A \<subseteq> X"
  proof -
    have "top1_S1 \<subseteq> top1_B2"
      unfolding top1_S1_def top1_B2_def by (by100 auto)
    moreover have "q ` top1_B2 \<subseteq> X"
      using assms(2) unfolding top1_quotient_map_on_def top1_continuous_map_on_def by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  have hTA_top: "is_topology_on ?A ?TA"
    by (rule subspace_topology_is_topology_on[OF hTX hA_sub])
  \<comment> \<open>Factor: \<exists>h: S1 \<rightarrow> X continuous with g = h \<circ> R\_to\_S1 on [0,1].\<close>
  from loop_factors_through_S1[OF hTX hg_is_loop]
  obtain h where hh_cont_X: "top1_continuous_map_on top1_S1 top1_S1_topology X TX h"
      and hh_base: "h (1, 0) = q (1, 0)"
      and hh_factor: "\<forall>s\<in>top1_unit_interval. g s = h (top1_R_to_S1 s)"
    by (by100 blast)
  \<comment> \<open>h maps S1 into q(S1) (since g maps into q(S1)).\<close>
  have hh_range: "h ` top1_S1 \<subseteq> ?A"
  proof
    fix y assume "y \<in> h ` top1_S1"
    then obtain p where "p \<in> top1_S1" "y = h p" by (by100 blast)
    from S1_point_to_angle[OF \<open>p \<in> top1_S1\<close>] obtain \<theta> where "top1_R_to_S1 \<theta> = p" by (by100 blast)
    \<comment> \<open>Choose representative \<theta>' \<in> [0,1) with R\_to\_S1(\<theta>') = p.\<close>
    have "\<exists>\<theta>'\<in>top1_unit_interval. top1_R_to_S1 \<theta>' = p"
    proof -
      let ?\<theta>' = "\<theta> - of_int \<lfloor>\<theta>\<rfloor>"
      have "0 \<le> ?\<theta>'" by (by100 simp)
      moreover have "?\<theta>' < 1" using floor_correct[of \<theta>] by (by100 linarith)
      ultimately have "?\<theta>' \<in> top1_unit_interval"
        unfolding top1_unit_interval_def by (by100 simp)
      moreover have "top1_R_to_S1 ?\<theta>' = top1_R_to_S1 \<theta>"
      proof -
        note top1_R_to_S1_int_shift_early[of \<theta> "- \<lfloor>\<theta>\<rfloor>"]
        thus ?thesis by (by100 simp)
      qed
      hence "top1_R_to_S1 ?\<theta>' = p" using \<open>top1_R_to_S1 \<theta> = p\<close> by (by100 simp)
      ultimately show ?thesis by (by100 blast)
    qed
    then obtain \<theta>' where h\<theta>': "\<theta>' \<in> top1_unit_interval" "top1_R_to_S1 \<theta>' = p" by (by100 blast)
    have "h p = h (top1_R_to_S1 \<theta>')" using h\<theta>'(2) by (by100 simp)
    also have "\<dots> = g \<theta>'"
      using hh_factor[rule_format, OF h\<theta>'(1)] by (by100 simp)
    finally have "h p = g \<theta>'" .
    also have "\<dots> \<in> ?A" using hg_range h\<theta>'(1) by (by100 blast)
    finally show "y \<in> ?A" using \<open>y = h p\<close> by (by100 simp)
  qed
  \<comment> \<open>h is continuous from S1 to q(S1) with subspace topology.\<close>
  have hh_range_all: "\<forall>p\<in>top1_S1. h p \<in> ?A" using hh_range by (by100 blast)
  have hh_cont: "top1_continuous_map_on top1_S1 top1_S1_topology ?A ?TA h"
    by (rule continuous_map_restrict_codomain[OF hh_cont_X hh_range_all hA_sub])
  \<comment> \<open>Step 3 (book): h is injective.
     If h(p1) = h(p2), take representatives \<theta>1, \<theta>2 \<in> [0,1).
     g(\<theta>1) = g(\<theta>2) means q(R\_to\_S1(\<theta>1/n)) = q(R\_to\_S1(\<theta>2/n)).
     By quotient relation: \<theta>2/n - \<theta>1/n = k/n + m, so \<theta>2 - \<theta>1 = k + mn \<in> Z.
     Since \<theta>1, \<theta>2 \<in> [0,1): |\<theta>2 - \<theta>1| < 1, so \<theta>1 = \<theta>2, so p1 = p2.\<close>
  have hh_inj: "inj_on h top1_S1"
  proof (rule inj_onI)
    fix p1 p2 assume hp1: "p1 \<in> top1_S1" and hp2: "p2 \<in> top1_S1" and heq: "h p1 = h p2"
    \<comment> \<open>Choose representatives \<theta>1, \<theta>2 \<in> [0,1) with R\_to\_S1(\<theta>i) = pi.\<close>
    obtain \<theta>1 where h\<theta>1: "\<theta>1 \<in> top1_unit_interval" "top1_R_to_S1 \<theta>1 = p1"
    proof -
      from S1_point_to_angle[OF hp1] obtain \<alpha> where "top1_R_to_S1 \<alpha> = p1" by (by100 blast)
      let ?\<theta> = "\<alpha> - of_int \<lfloor>\<alpha>\<rfloor>"
      have "0 \<le> ?\<theta>" by (by100 simp)
      moreover have "?\<theta> < 1" using floor_correct[of \<alpha>] by (by100 linarith)
      ultimately have "?\<theta> \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
      moreover have "top1_R_to_S1 ?\<theta> = p1"
        using top1_R_to_S1_int_shift_early[of \<alpha> "- \<lfloor>\<alpha>\<rfloor>"] \<open>top1_R_to_S1 \<alpha> = p1\<close> by (by100 simp)
      ultimately show ?thesis using that by (by100 blast)
    qed
    obtain \<theta>2 where h\<theta>2: "\<theta>2 \<in> top1_unit_interval" "top1_R_to_S1 \<theta>2 = p2"
    proof -
      from S1_point_to_angle[OF hp2] obtain \<alpha> where "top1_R_to_S1 \<alpha> = p2" by (by100 blast)
      let ?\<theta> = "\<alpha> - of_int \<lfloor>\<alpha>\<rfloor>"
      have "0 \<le> ?\<theta>" by (by100 simp)
      moreover have "?\<theta> < 1" using floor_correct[of \<alpha>] by (by100 linarith)
      ultimately have "?\<theta> \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
      moreover have "top1_R_to_S1 ?\<theta> = p2"
        using top1_R_to_S1_int_shift_early[of \<alpha> "- \<lfloor>\<alpha>\<rfloor>"] \<open>top1_R_to_S1 \<alpha> = p2\<close> by (by100 simp)
      ultimately show ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>h(pi) = g(\<theta>i) from the factoring.\<close>
    have "g \<theta>1 = h (top1_R_to_S1 \<theta>1)" using hh_factor h\<theta>1(1) by (by100 blast)
    hence "g \<theta>1 = h p1" using h\<theta>1(2) by (by100 simp)
    have "g \<theta>2 = h (top1_R_to_S1 \<theta>2)" using hh_factor h\<theta>2(1) by (by100 blast)
    hence "g \<theta>2 = h p2" using h\<theta>2(2) by (by100 simp)
    \<comment> \<open>h(p1) = h(p2) implies g(\<theta>1) = g(\<theta>2), i.e., q(R\_to\_S1(\<theta>1/n)) = q(R\_to\_S1(\<theta>2/n)).\<close>
    have "g \<theta>1 = g \<theta>2" using \<open>g \<theta>1 = h p1\<close> \<open>g \<theta>2 = h p2\<close> heq by (by100 simp)
    hence hq_eq: "q (top1_R_to_S1 (\<theta>1 / real n)) = q (top1_R_to_S1 (\<theta>2 / real n))"
      unfolding g_def by (by100 simp)
    \<comment> \<open>By quotient relation: \<theta>2/n - \<theta>1/n = k/n + m, so \<theta>2 - \<theta>1 = k + mn \<in> Z.
       Since \<theta>1, \<theta>2 \<in> [0,1]: |\<theta>2 - \<theta>1| \<le> 1. Integer with |k+mn| \<le> 1: k+mn \<in> {-1,0,1}.
       k+mn = 0 \<Rightarrow> \<theta>1 = \<theta>2. k+mn = \<pm>1 \<Rightarrow> one of \<theta>i = 0, other = 1, both map to (1,0).\<close>
    have "top1_R_to_S1 \<theta>1 = top1_R_to_S1 \<theta>2"
    proof -
      \<comment> \<open>R\_to\_S1(\<theta>i/n) \<in> S1.\<close>
      have h1_S1: "top1_R_to_S1 (\<theta>1 / real n) \<in> top1_S1"
        unfolding top1_R_to_S1_def top1_S1_def
        using sin_cos_squared_add by (by100 auto)
      have h2_S1: "top1_R_to_S1 (\<theta>2 / real n) \<in> top1_S1"
        unfolding top1_R_to_S1_def top1_S1_def
        using sin_cos_squared_add by (by100 auto)
      \<comment> \<open>By quotient relation: \<exists>k < n with R\_to\_S1(\<theta>2/n) = rot\_k(R\_to\_S1(\<theta>1/n)).\<close>
      from assms(3)[rule_format, OF h1_S1 h2_S1] hq_eq
      obtain k :: nat where hk: "k < n"
          "top1_R_to_S1 (\<theta>2 / real n) =
            (cos (2*pi*real k/real n) * fst (top1_R_to_S1 (\<theta>1 / real n)) -
             sin (2*pi*real k/real n) * snd (top1_R_to_S1 (\<theta>1 / real n)),
             sin (2*pi*real k/real n) * fst (top1_R_to_S1 (\<theta>1 / real n)) +
             cos (2*pi*real k/real n) * snd (top1_R_to_S1 (\<theta>1 / real n)))"
        by (by100 blast)
      \<comment> \<open>This means R\_to\_S1(\<theta>2/n) = R\_to\_S1(\<theta>1/n + k/n), i.e., \<theta>2/n - \<theta>1/n - k/n \<in> Z.\<close>
      have h\<theta>_diff: "\<exists>m::int. \<theta>2 - \<theta>1 = real k + real n * real_of_int m"
      proof -
        \<comment> \<open>The rotation formula equals R\_to\_S1((\<theta>1+k)/n) (by angle addition).\<close>
        have hrot_rts: "top1_R_to_S1 (\<theta>2 / real n) = top1_R_to_S1 ((\<theta>1 + real k) / real n)"
        proof -
          \<comment> \<open>RHS of hk(2) = R\_to\_S1((\<theta>1+k)/n) by angle addition.\<close>
          have h_add: "2 * pi * ((\<theta>1 + real k) / real n) = 2 * pi * (\<theta>1 / real n) + 2 * pi * (real k / real n)"
            using hn_pos by (by100 algebra)
          have "cos (2 * pi * ((\<theta>1 + real k) / real n))
              = cos (2 * pi * (\<theta>1 / real n)) * cos (2 * pi * (real k / real n))
              - sin (2 * pi * (\<theta>1 / real n)) * sin (2 * pi * (real k / real n))"
            using cos_add[of "2 * pi * (\<theta>1 / real n)" "2 * pi * (real k / real n)"]
                  h_add by (by100 simp)
          moreover have "sin (2 * pi * ((\<theta>1 + real k) / real n))
              = sin (2 * pi * (\<theta>1 / real n)) * cos (2 * pi * (real k / real n))
              + cos (2 * pi * (\<theta>1 / real n)) * sin (2 * pi * (real k / real n))"
            using sin_add[of "2 * pi * (\<theta>1 / real n)" "2 * pi * (real k / real n)"]
                  h_add by (by100 simp)
          ultimately have "top1_R_to_S1 ((\<theta>1 + real k) / real n) =
              (cos (2*pi*(real k / real n)) * fst (top1_R_to_S1 (\<theta>1 / real n))
             - sin (2*pi*(real k / real n)) * snd (top1_R_to_S1 (\<theta>1 / real n)),
               sin (2*pi*(real k / real n)) * fst (top1_R_to_S1 (\<theta>1 / real n))
             + cos (2*pi*(real k / real n)) * snd (top1_R_to_S1 (\<theta>1 / real n)))"
            unfolding top1_R_to_S1_def by (by100 auto)
          \<comment> \<open>Now match with hk(2): rewrite to same form.\<close>
          hence "top1_R_to_S1 ((\<theta>1 + real k) / real n) =
              (cos (2*pi*real k/real n) * fst (top1_R_to_S1 (\<theta>1 / real n))
             - sin (2*pi*real k/real n) * snd (top1_R_to_S1 (\<theta>1 / real n)),
               sin (2*pi*real k/real n) * fst (top1_R_to_S1 (\<theta>1 / real n))
             + cos (2*pi*real k/real n) * snd (top1_R_to_S1 (\<theta>1 / real n)))"
            by (by100 simp)
          with hk(2) show ?thesis by (by100 simp)
        qed
        \<comment> \<open>Unfold: cos(2\<pi>\<theta>2/n) = cos(2\<pi>(\<theta>1+k)/n) and sin(2\<pi>\<theta>2/n) = sin(2\<pi>(\<theta>1+k)/n).\<close>
        hence "cos (2 * pi * (\<theta>2 / real n)) = cos (2 * pi * ((\<theta>1 + real k) / real n))"
          and "sin (2 * pi * (\<theta>2 / real n)) = sin (2 * pi * ((\<theta>1 + real k) / real n))"
          unfolding top1_R_to_S1_def by (by100 auto)+
        \<comment> \<open>By cos\_sin\_eq\_imp: \<exists>m. 2\<pi>\<theta>2/n - 2\<pi>(\<theta>1+k)/n = m \<cdot> 2\<pi>.\<close>
        from cos_sin_eq_imp[OF this]
        obtain m :: int where hm_raw:
            "2 * pi * (\<theta>2 / real n) - 2 * pi * ((\<theta>1 + real k) / real n)
             = real_of_int m * 2 * pi" by (by100 blast)
        \<comment> \<open>Divide by 2\<pi> (nonzero): \<theta>2/n - (\<theta>1+k)/n = m.\<close>
        have "\<theta>2 / real n - (\<theta>1 + real k) / real n = real_of_int m"
        proof -
          have "pi \<noteq> 0" using pi_gt_zero by (by100 linarith)
          hence "2 * pi \<noteq> 0" by (by100 linarith)
          from hm_raw have "2 * pi * (\<theta>2 / real n - (\<theta>1 + real k) / real n) = real_of_int m * (2 * pi)"
            by (by100 algebra)
          thus ?thesis using \<open>2 * pi \<noteq> 0\<close> by (by100 algebra)
        qed
        \<comment> \<open>Multiply by n: \<theta>2 - \<theta>1 - k = n*m.\<close>
        hence "\<theta>2 - \<theta>1 - real k = real n * real_of_int m"
        proof -
          have "real n > 0" using hn_pos by (by100 simp)
          have "real n * (\<theta>2 / real n - (\<theta>1 + real k) / real n) = real n * real_of_int m"
            using \<open>\<theta>2 / real n - (\<theta>1 + real k) / real n = real_of_int m\<close> by (by100 simp)
          moreover have "real n * (\<theta>2 / real n - (\<theta>1 + real k) / real n) = \<theta>2 - \<theta>1 - real k"
          proof -
            have "real n * (\<theta>2 / real n) = \<theta>2" using \<open>real n > 0\<close> by (by100 simp)
            have "real n * ((\<theta>1 + real k) / real n) = \<theta>1 + real k" using \<open>real n > 0\<close> by (by100 simp)
            have "real n * (\<theta>2 / real n - (\<theta>1 + real k) / real n)
                = real n * (\<theta>2 / real n) - real n * ((\<theta>1 + real k) / real n)"
              by (by100 algebra)
            also have "\<dots> = \<theta>2 - (\<theta>1 + real k)"
              using \<open>real n * (\<theta>2 / real n) = \<theta>2\<close> \<open>real n * ((\<theta>1 + real k) / real n) = \<theta>1 + real k\<close>
              by (by100 simp)
            also have "\<dots> = \<theta>2 - \<theta>1 - real k" by (by100 algebra)
            finally show ?thesis .
          qed
          ultimately show ?thesis by (by100 simp)
        qed
        hence "\<theta>2 - \<theta>1 = real k + real n * real_of_int m" by (by100 linarith)
        thus ?thesis by (by100 blast)
      qed
      then obtain m :: int where hm: "\<theta>2 - \<theta>1 = real k + real n * real_of_int m" by (by100 blast)
      \<comment> \<open>\<theta>1, \<theta>2 \<in> [0,1], so |\<theta>2 - \<theta>1| \<le> 1. And k + n*m is an integer.\<close>
      have h\<theta>1_bnd: "0 \<le> \<theta>1 \<and> \<theta>1 \<le> 1"
        using h\<theta>1(1) unfolding top1_unit_interval_def by (by100 simp)
      have h\<theta>2_bnd: "0 \<le> \<theta>2 \<and> \<theta>2 \<le> 1"
        using h\<theta>2(1) unfolding top1_unit_interval_def by (by100 simp)
      have habs: "\<bar>\<theta>2 - \<theta>1\<bar> \<le> 1" using h\<theta>1_bnd h\<theta>2_bnd by (by100 linarith)
      \<comment> \<open>k + n*m is an integer with |k + n*m| \<le> 1. Cases: k+n*m \<in> {-1,0,1}.\<close>
      have hint: "\<bar>real k + real n * real_of_int m\<bar> \<le> 1" using hm habs by (by100 linarith)
      \<comment> \<open>In all three cases, R\_to\_S1(\<theta>1) = R\_to\_S1(\<theta>2).\<close>
      have "real k + real n * real_of_int m \<in> {-1, 0, 1}"
      proof -
        \<comment> \<open>k + n*m is an integer (of\_int representation).\<close>
        have "real k + real n * real_of_int m = real_of_int (int k + int n * m)"
          by (by100 simp)
        hence "\<exists>z::int. real k + real n * real_of_int m = real_of_int z"
          by (by100 blast)
        then obtain z :: int where hz: "real k + real n * real_of_int m = real_of_int z"
          by (by100 blast)
        have "\<bar>real_of_int z\<bar> \<le> 1" using hint hz by (by100 simp)
        hence "z \<in> {-1, 0, 1}" by (by100 auto)
        thus ?thesis using hz by (by100 auto)
      qed
      hence "\<theta>2 - \<theta>1 \<in> {-1, 0, 1}" using hm by (by100 auto)
      \<comment> \<open>\<theta>2 - \<theta>1 \<in> {-1,0,1} and both in [0,1]: if 0 then equal, if \<pm>1 then endpoints.\<close>
      hence "top1_R_to_S1 \<theta>1 = top1_R_to_S1 \<theta>2"
      proof -
        from \<open>\<theta>2 - \<theta>1 \<in> {-1, 0, 1}\<close> consider
            (eq) "\<theta>2 - \<theta>1 = 0" | (plus) "\<theta>2 - \<theta>1 = 1" | (minus) "\<theta>2 - \<theta>1 = -1"
          by (by100 blast)
        thus ?thesis
        proof cases
          case eq thus ?thesis by (by100 simp)
        next
          case plus
          \<comment> \<open>\<theta>2 = \<theta>1 + 1. R\_to\_S1(\<theta>1 + 1) = R\_to\_S1(\<theta>1) by integer shift.\<close>
          hence "\<theta>2 = \<theta>1 + 1" by (by100 simp)
          hence "top1_R_to_S1 \<theta>2 = top1_R_to_S1 (\<theta>1 + of_int 1)"
            by (by100 simp)
          also have "\<dots> = top1_R_to_S1 \<theta>1" by (rule top1_R_to_S1_int_shift)
          finally show ?thesis by (by100 simp)
        next
          case minus
          hence "\<theta>1 = \<theta>2 + 1" by (by100 simp)
          hence "top1_R_to_S1 \<theta>1 = top1_R_to_S1 (\<theta>2 + of_int 1)"
            by (by100 simp)
          also have "\<dots> = top1_R_to_S1 \<theta>2" by (rule top1_R_to_S1_int_shift)
          finally show ?thesis .
        qed
      qed
      thus ?thesis .
    qed
    thus "p1 = p2" using h\<theta>1(2) h\<theta>2(2) by (by100 simp)
  qed
  \<comment> \<open>Step 4 (book): h is surjective onto q(S1).
     For q(z) with z = R\_to\_S1(\<alpha>): h(R\_to\_S1(n\<alpha>)) = g(n\<alpha>) = q(R\_to\_S1(\<alpha>)) = q(z).
     And R\_to\_S1(n\<alpha>) \<in> S1.\<close>
  have hh_surj: "h ` top1_S1 = ?A"
  proof (rule set_eqI, rule iffI)
    fix y assume "y \<in> h ` top1_S1"
    thus "y \<in> ?A" using hh_range by (by100 blast)
  next
    fix y assume "y \<in> ?A"
    \<comment> \<open>y = q(z) for z = R\_to\_S1(\<alpha>). Then h(R\_to\_S1(n\<alpha>)) = g(n\<alpha>) = q(R\_to\_S1(\<alpha>)) = y.\<close>
    then obtain z where "z \<in> top1_S1" "y = q z" by (by100 blast)
    from S1_point_to_angle[OF \<open>z \<in> top1_S1\<close>] obtain \<alpha> where "top1_R_to_S1 \<alpha> = z" by (by100 blast)
    \<comment> \<open>R\_to\_S1(n\<alpha>) \<in> S1. And h(R\_to\_S1(n\<alpha>)) = g(n\<alpha>) = q(R\_to\_S1(\<alpha>)) = q(z) = y.\<close>
    have "top1_R_to_S1 (real n * \<alpha>) \<in> top1_S1"
      unfolding top1_R_to_S1_def top1_S1_def
      using sin_cos_squared_add by (by100 auto)
    moreover have "h (top1_R_to_S1 (real n * \<alpha>)) = y"
    proof -
      \<comment> \<open>Need n\<alpha> mod 1 representative in [0,1] to use hh\_factor. Or use periodicity.\<close>
      have "g (real n * \<alpha>) = q (top1_R_to_S1 (real n * \<alpha> / real n))" unfolding g_def by (by100 simp)
      also have "\<dots> = q (top1_R_to_S1 \<alpha>)" using hn_pos by (by100 simp)
      also have "\<dots> = q z" using \<open>top1_R_to_S1 \<alpha> = z\<close> by (by100 simp)
      also have "\<dots> = y" using \<open>y = q z\<close> by (by100 simp)
      finally have hg_na: "g (real n * \<alpha>) = y" .
      \<comment> \<open>h(R\_to\_S1(n\<alpha>)) = g(n\<alpha>) from the factoring (using periodicity).\<close>
      \<comment> \<open>Take n\<alpha>' = n\<alpha> - floor(n\<alpha>) \<in> [0,1). Then R\_to\_S1(n\<alpha>') = R\_to\_S1(n\<alpha>).\<close>
      let ?na' = "real n * \<alpha> - of_int \<lfloor>real n * \<alpha>\<rfloor>"
      have hna'_bnd: "0 \<le> ?na' \<and> ?na' < 1"
        using floor_correct[of "real n * \<alpha>"] by (by100 linarith)
      hence hna'_I: "?na' \<in> top1_unit_interval"
        unfolding top1_unit_interval_def by (by100 simp)
      have hna'_eq: "top1_R_to_S1 ?na' = top1_R_to_S1 (real n * \<alpha>)"
        using top1_R_to_S1_int_shift_early[of "real n * \<alpha>" "- \<lfloor>real n * \<alpha>\<rfloor>"]
        by (by100 simp)
      \<comment> \<open>g(n\<alpha>') = q(R\_to\_S1(n\<alpha>'/n)). And n\<alpha>'/n and \<alpha> differ by \<lfloor>n\<alpha>\<rfloor>/n.
         Since \<lfloor>n\<alpha>\<rfloor> is an integer, this is a rotation in the quotient \<Rightarrow> same q-class.\<close>
      have hg_na': "g ?na' = g (real n * \<alpha>)"
      proof -
        have "g ?na' = q (top1_R_to_S1 (?na' / real n))" unfolding g_def by (by100 simp)
        \<comment> \<open>n\<alpha>'/n = \<alpha> - \<lfloor>n\<alpha>\<rfloor>/n. The shift \<lfloor>n\<alpha>\<rfloor>/n corresponds to rotation by 2\<pi>\<lfloor>n\<alpha>\<rfloor>/n.\<close>
        also have "\<dots> = q (top1_R_to_S1 \<alpha>)"
        proof -
          \<comment> \<open>R\_to\_S1(\<alpha>) = rot\_k(R\_to\_S1(\<alpha> - \<lfloor>n\<alpha>\<rfloor>/n)) where k = nat(\<lfloor>n\<alpha>\<rfloor> mod n).
             Use the same angle addition argument as for hrot\_rts.\<close>
          let ?k = "nat (\<lfloor>real n * \<alpha>\<rfloor> mod int n)"
          have hk_lt: "?k < n"
          proof -
            have "int n > 0" using hn_pos by (by100 simp)
            hence "\<lfloor>real n * \<alpha>\<rfloor> mod int n \<ge> 0" by (by100 simp)
            moreover have "\<lfloor>real n * \<alpha>\<rfloor> mod int n < int n" using \<open>int n > 0\<close> by (by100 simp)
            ultimately show ?thesis by (by100 auto)
          qed
          \<comment> \<open>nα'/n + k/n = α (mod integers): nα'/n = α - ⌊nα⌋/n, k/n = (⌊nα⌋ mod n)/n.
             But ⌊nα⌋ = n*q + (⌊nα⌋ mod n) for some integer q. So ⌊nα⌋/n = q + k/n.
             Hence α = nα'/n + ⌊nα⌋/n = nα'/n + q + k/n. And R\_to\_S1(\<alpha>) = R\_to\_S1(nα'/n + k/n)
             (since q is integer, R\_to\_S1 shifts by integers). Then by angle addition,
             this = rot\_k(R\_to\_S1(nα'/n)).\<close>
          have "top1_R_to_S1 \<alpha> = top1_R_to_S1 (?na' / real n + real ?k / real n)"
          proof -
            \<comment> \<open>nα'/n + k/n = α - (⌊nα⌋ div n). R\_to\_S1 shifts by this integer.\<close>
            have hn_ne: "real n \<noteq> 0" using hn_pos by (by100 simp)
            have h_eq: "?na' / real n + real ?k / real n = \<alpha> - of_int (\<lfloor>real n * \<alpha>\<rfloor> div int n)"
            proof -
              have hint_n: "int n > 0" using hn_pos by (by100 simp)
              have hmod_nn: "\<lfloor>real n * \<alpha>\<rfloor> mod int n \<ge> 0" using hint_n by (by100 simp)
              \<comment> \<open>nat(floor mod n) = floor mod n as nat, and its real = of\_int.\<close>
              have hnat_eq: "real (nat (\<lfloor>real n * \<alpha>\<rfloor> mod int n)) = of_int (\<lfloor>real n * \<alpha>\<rfloor> mod int n)"
                using hmod_nn by (by100 auto)
              \<comment> \<open>Key identity: a = n * (a div n) + (a mod n) for integers.\<close>
              have hzmod: "\<lfloor>real n * \<alpha>\<rfloor> = int n * (\<lfloor>real n * \<alpha>\<rfloor> div int n) + \<lfloor>real n * \<alpha>\<rfloor> mod int n"
                by (by100 simp)
              \<comment> \<open>Convert to reals: of\_int(floor) = n * of\_int(div) + of\_int(mod).\<close>
              have hreal: "of_int \<lfloor>real n * \<alpha>\<rfloor> = real n * of_int (\<lfloor>real n * \<alpha>\<rfloor> div int n) + of_int (\<lfloor>real n * \<alpha>\<rfloor> mod int n)"
              proof -
                from hzmod have "of_int \<lfloor>real n * \<alpha>\<rfloor> = of_int (int n * (\<lfloor>real n * \<alpha>\<rfloor> div int n) + \<lfloor>real n * \<alpha>\<rfloor> mod int n)"
                  by (by100 simp)
                also have "\<dots> = real n * of_int (\<lfloor>real n * \<alpha>\<rfloor> div int n) + of_int (\<lfloor>real n * \<alpha>\<rfloor> mod int n)"
                  apply (simp only: of_int_add of_int_mult)
                  done
                finally show ?thesis .
              qed
              \<comment> \<open>Now compute: (nα - floor)/n + (mod)/n = (nα - n*div - mod)/n + mod/n = α - div.\<close>
              have "?na' / real n + real ?k / real n
                  = (real n * \<alpha> - of_int \<lfloor>real n * \<alpha>\<rfloor> + of_int (\<lfloor>real n * \<alpha>\<rfloor> mod int n)) / real n"
                using hnat_eq hn_ne
                using add_divide_distrib[of "real n * \<alpha> - of_int \<lfloor>real n * \<alpha>\<rfloor>" "of_int (\<lfloor>real n * \<alpha>\<rfloor> mod int n)" "real n"]
                by (by100 simp)
              also have "\<dots> = (real n * \<alpha> - real n * of_int (\<lfloor>real n * \<alpha>\<rfloor> div int n)) / real n"
              proof -
                have "real n * \<alpha> - of_int \<lfloor>real n * \<alpha>\<rfloor> + of_int (\<lfloor>real n * \<alpha>\<rfloor> mod int n)
                    = real n * \<alpha> - real n * of_int (\<lfloor>real n * \<alpha>\<rfloor> div int n)"
                  using hreal by (by100 linarith)
                thus ?thesis by (by100 simp)
              qed
              also have "\<dots> = \<alpha> - of_int (\<lfloor>real n * \<alpha>\<rfloor> div int n)"
              proof -
                have "real n * \<alpha> - real n * of_int (\<lfloor>real n * \<alpha>\<rfloor> div int n)
                    = real n * (\<alpha> - of_int (\<lfloor>real n * \<alpha>\<rfloor> div int n))"
                  by (by100 algebra)
                hence "(real n * \<alpha> - real n * of_int (\<lfloor>real n * \<alpha>\<rfloor> div int n)) / real n
                    = \<alpha> - of_int (\<lfloor>real n * \<alpha>\<rfloor> div int n)"
                  using hn_ne by (by100 simp)
                thus ?thesis .
              qed
              finally show ?thesis .
            qed
            have "top1_R_to_S1 (?na' / real n + real ?k / real n)
                = top1_R_to_S1 (\<alpha> + of_int (- (\<lfloor>real n * \<alpha>\<rfloor> div int n)))"
              using h_eq by (by100 simp)
            also have "\<dots> = top1_R_to_S1 \<alpha>"
              by (rule top1_R_to_S1_int_shift)
            finally show ?thesis by (by100 simp)
          qed
          \<comment> \<open>By angle addition: rot\_k(R\_to\_S1(nα'/n)) = R\_to\_S1(nα'/n + k/n).\<close>
          \<comment> \<open>Then q(R\_to\_S1(nα'/n)) = q(R\_to\_S1(\<alpha>)) by quotient relation.\<close>
          have h_na'_S1: "top1_R_to_S1 (?na' / real n) \<in> top1_S1"
            unfolding top1_R_to_S1_def top1_S1_def
            using sin_cos_squared_add by (by100 auto)
          have h_a_S1: "top1_R_to_S1 \<alpha> \<in> top1_S1"
            unfolding top1_R_to_S1_def top1_S1_def
            using sin_cos_squared_add by (by100 auto)
          \<comment> \<open>R\_to\_S1(\<alpha>) is a rotation of R\_to\_S1(nα'/n) by k, hence identified by q.\<close>
          have "\<exists>j::nat. j < n \<and> top1_R_to_S1 \<alpha> =
              (cos (2*pi*real j/real n) * fst (top1_R_to_S1 (?na' / real n)) -
               sin (2*pi*real j/real n) * snd (top1_R_to_S1 (?na' / real n)),
               sin (2*pi*real j/real n) * fst (top1_R_to_S1 (?na' / real n)) +
               cos (2*pi*real j/real n) * snd (top1_R_to_S1 (?na' / real n)))"
          proof -
            \<comment> \<open>By angle addition: R\_to\_S1(nα'/n + k/n) = rot\_k(R\_to\_S1(nα'/n)).\<close>
            have h_add': "2 * pi * (?na' / real n + real ?k / real n)
                = 2 * pi * (?na' / real n) + 2 * pi * (real ?k / real n)"
              using hn_pos by (by100 algebra)
            have hcos': "cos (2 * pi * (?na' / real n + real ?k / real n))
                = cos (2 * pi * (?na' / real n)) * cos (2 * pi * (real ?k / real n))
                - sin (2 * pi * (?na' / real n)) * sin (2 * pi * (real ?k / real n))"
              using cos_add[of "2 * pi * (?na' / real n)" "2 * pi * (real ?k / real n)"]
                    h_add' by (by100 simp)
            have hsin': "sin (2 * pi * (?na' / real n + real ?k / real n))
                = sin (2 * pi * (?na' / real n)) * cos (2 * pi * (real ?k / real n))
                + cos (2 * pi * (?na' / real n)) * sin (2 * pi * (real ?k / real n))"
              using sin_add[of "2 * pi * (?na' / real n)" "2 * pi * (real ?k / real n)"]
                    h_add' by (by100 simp)
            have "top1_R_to_S1 (?na' / real n + real ?k / real n) =
                (cos (2*pi*(real ?k / real n)) * fst (top1_R_to_S1 (?na' / real n))
               - sin (2*pi*(real ?k / real n)) * snd (top1_R_to_S1 (?na' / real n)),
                 sin (2*pi*(real ?k / real n)) * fst (top1_R_to_S1 (?na' / real n))
               + cos (2*pi*(real ?k / real n)) * snd (top1_R_to_S1 (?na' / real n)))"
              unfolding top1_R_to_S1_def using hcos' hsin' by (by5000 auto)
            hence "top1_R_to_S1 (?na' / real n + real ?k / real n) =
                (cos (2*pi*real ?k/real n) * fst (top1_R_to_S1 (?na' / real n))
               - sin (2*pi*real ?k/real n) * snd (top1_R_to_S1 (?na' / real n)),
                 sin (2*pi*real ?k/real n) * fst (top1_R_to_S1 (?na' / real n))
               + cos (2*pi*real ?k/real n) * snd (top1_R_to_S1 (?na' / real n)))"
              by (by100 simp)
            \<comment> \<open>R\_to\_S1(\<alpha>) = R\_to\_S1(nα'/n + k/n) from earlier.\<close>
            from \<open>top1_R_to_S1 \<alpha> = top1_R_to_S1 (?na' / real n + real ?k / real n)\<close> this
            have "top1_R_to_S1 \<alpha> =
                (cos (2*pi*real ?k/real n) * fst (top1_R_to_S1 (?na' / real n))
               - sin (2*pi*real ?k/real n) * snd (top1_R_to_S1 (?na' / real n)),
                 sin (2*pi*real ?k/real n) * fst (top1_R_to_S1 (?na' / real n))
               + cos (2*pi*real ?k/real n) * snd (top1_R_to_S1 (?na' / real n)))"
              by (by100 simp)
            with hk_lt show ?thesis by (rule_tac x="?k" in exI, by100 blast)
          qed
          with assms(3)[rule_format, OF h_na'_S1 h_a_S1]
          show "q (top1_R_to_S1 (?na' / real n)) = q (top1_R_to_S1 \<alpha>)" by (by100 blast)
        qed
        also have "\<dots> = g (real n * \<alpha>)" using hg_na \<open>y = q z\<close> \<open>top1_R_to_S1 \<alpha> = z\<close>
          unfolding g_def using hn_pos by (by100 simp)
        finally show ?thesis .
      qed
      \<comment> \<open>h(R\_to\_S1(n\<alpha>)) = h(R\_to\_S1(n\<alpha>')) = g(n\<alpha>') = g(n\<alpha>) = y.\<close>
      have "h (top1_R_to_S1 (real n * \<alpha>)) = h (top1_R_to_S1 ?na')"
        using hna'_eq by (by100 simp)
      also have "\<dots> = g ?na'"
        using hh_factor[rule_format, OF hna'_I] by (by100 simp)
      also have "\<dots> = g (real n * \<alpha>)" using hg_na' .
      also have "\<dots> = y" using hg_na .
      finally show ?thesis .
    qed
    ultimately show "y \<in> h ` top1_S1" by (by100 blast)
  qed
  \<comment> \<open>Step 5: compact S1 + Hausdorff q(S1) + continuous bijection \<Rightarrow> homeomorphism.\<close>
  have hh_bij: "bij_betw h top1_S1 ?A"
    unfolding bij_betw_def using hh_inj hh_surj by (by100 blast)
  have hS1_compact: "top1_compact_on top1_S1 top1_S1_topology" by (rule S1_compact)
  have hX_haus: "is_hausdorff_on X TX" by (rule dunce_cap_hausdorff[OF assms(1)])
  have hA_haus: "is_hausdorff_on ?A ?TA"
    using hX_haus hA_sub conjunct2[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
  have hS1_top: "is_topology_on top1_S1 top1_S1_topology"
    using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
  have hh_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology ?A ?TA h"
    by (rule Theorem_26_6[OF hS1_top hTA_top hS1_compact hA_haus hh_cont hh_bij])
  show ?thesis using hh_homeo by (by100 blast)
qed

text \<open>Helper: the projective scheme has length 2m and its elements are (k, True) for k = i div 2.\<close>

lemma projective_scheme_length:
  "length (top1_m_projective_scheme m) = 2 * m"
  unfolding top1_m_projective_scheme_def by (induction m, simp, simp)

lemma projective_scheme_nth:
  assumes "i < 2 * m"
  shows "top1_m_projective_scheme m ! i = (i div 2, True)"
  using assms
proof (induction m arbitrary: i)
  case 0 thus ?case by (by100 simp)
next
  case (Suc m)
  show ?case
  proof (cases "i < 2 * m")
    case True
    hence IH: "top1_m_projective_scheme m ! i = (i div 2, True)" using Suc.IH by (by100 blast)
    have hlen_m: "length (top1_m_projective_scheme m) = 2 * m"
      by (rule projective_scheme_length)
    have "top1_m_projective_scheme (Suc m) = top1_m_projective_scheme m @ [(m, True), (m, True)]"
      unfolding top1_m_projective_scheme_def by (by100 simp)
    have "i < length (top1_m_projective_scheme m)"
      using True hlen_m by (by100 simp)
    hence "top1_m_projective_scheme (Suc m) ! i = top1_m_projective_scheme m ! i"
      using \<open>top1_m_projective_scheme (Suc m) = top1_m_projective_scheme m @ [(m, True), (m, True)]\<close>
        \<open>i < length (top1_m_projective_scheme m)\<close>
    proof -
      have "(top1_m_projective_scheme m @ [(m, True), (m, True)]) ! i = top1_m_projective_scheme m ! i"
        using \<open>i < length (top1_m_projective_scheme m)\<close> by (simp add: nth_append)
      thus ?thesis
        using \<open>top1_m_projective_scheme (Suc m) = top1_m_projective_scheme m @ [(m, True), (m, True)]\<close>
        by (by100 simp)
    qed
    thus ?thesis using IH by (by100 simp)
  next
    case False
    hence hi: "i = 2*m \<or> i = 2*m+1" using Suc.prems by (by100 auto)
    show ?thesis
    proof (cases "i = 2*m")
      case True
      have happ: "top1_m_projective_scheme (Suc m) = top1_m_projective_scheme m @ [(m, True), (m, True)]"
        unfolding top1_m_projective_scheme_def by (by100 simp)
      have hlen_m: "length (top1_m_projective_scheme m) = 2 * m"
        by (rule projective_scheme_length)
      have "top1_m_projective_scheme (Suc m) ! (2*m) = [(m, True), (m, True)] ! 0"
        unfolding happ using hlen_m by (simp add: nth_append)
      hence "top1_m_projective_scheme (Suc m) ! (2*m) = (m, True)" by (by100 simp)
      thus ?thesis using True by (by100 simp)
    next
      case False
      hence hi2: "i = 2*m+1" using hi by (by100 blast)
      have happ: "top1_m_projective_scheme (Suc m) = top1_m_projective_scheme m @ [(m, True), (m, True)]"
        unfolding top1_m_projective_scheme_def by (by100 simp)
      have hlen_m: "length (top1_m_projective_scheme m) = 2 * m"
        by (rule projective_scheme_length)
      have "top1_m_projective_scheme (Suc m) ! (2*m+1) = [(m, True), (m, True)] ! 1"
        unfolding happ using hlen_m by (simp add: nth_append)
      hence "top1_m_projective_scheme (Suc m) ! (2*m+1) = (m, True)" by (by100 simp)
      thus ?thesis using hi2 by (by100 simp)
    qed
  qed
qed

lemma projective_scheme_vertex_connectivity:
  assumes "m \<ge> 2"
  shows "\<forall>(q::real\<times>real\<Rightarrow>'b) (vx::nat\<Rightarrow>real) (vy::nat\<Rightarrow>real).
      (\<forall>i<length (top1_m_projective_scheme m). \<forall>j<length (top1_m_projective_scheme m).
        fst ((top1_m_projective_scheme m)!i) = fst ((top1_m_projective_scheme m)!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length (top1_m_projective_scheme m)),
           (1-t) * vy i + t * vy (Suc i mod length (top1_m_projective_scheme m)))
         = (if snd ((top1_m_projective_scheme m)!i) = snd ((top1_m_projective_scheme m)!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length (top1_m_projective_scheme m)),
                    (1-t) * vy j + t * vy (Suc j mod length (top1_m_projective_scheme m)))
            else q (t * vx j + (1-t) * vx (Suc j mod length (top1_m_projective_scheme m)),
                    t * vy j + (1-t) * vy (Suc j mod length (top1_m_projective_scheme m))))))
      \<longrightarrow> (\<forall>i<length (top1_m_projective_scheme m). \<forall>j<length (top1_m_projective_scheme m).
            q (vx i, vy i) = q (vx j, vy j))"
proof -
  \<comment> \<open>For any q, vx, vy satisfying the edge identifications, all vertices are equal.\<close>
  {
    fix q :: "real \<times> real \<Rightarrow> 'b" and vx vy :: "nat \<Rightarrow> real"
    let ?scheme = "top1_m_projective_scheme m"
    let ?n = "length ?scheme"
    assume hedge: "\<forall>i<?n. \<forall>j<?n.
        fst (?scheme!i) = fst (?scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod ?n),
           (1-t) * vy i + t * vy (Suc i mod ?n))
         = (if snd (?scheme!i) = snd (?scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod ?n),
                    (1-t) * vy j + t * vy (Suc j mod ?n))
            else q (t * vx j + (1-t) * vx (Suc j mod ?n),
                    t * vy j + (1-t) * vy (Suc j mod ?n))))"
    have hlen: "?n = 2 * m" by (rule projective_scheme_length)
  have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
  \<comment> \<open>Key: edges 2k and 2k+1 share label k, both True direction.
     At t=0: q(vx(2k), vy(2k)) = q(vx(2k+1), vy(2k+1)).
     Chaining adjacent pairs: all vertices equal.\<close>
  have hadjacent: "\<forall>i<?n. q (vx i, vy i) = q (vx (Suc i mod ?n), vy (Suc i mod ?n))"
  proof (intro allI impI)
    fix i assume hi: "i < ?n"
    define k where "k = i div 2"
    have hk: "k < m" using hi hlen k_def by (by100 simp)
    have h2k: "2*k < ?n" using hk hlen by (by100 simp)
    have h2k1: "2*k+1 < ?n" using hk hlen by (by100 simp)
    \<comment> \<open>Both edges 2k and 2k+1 have the same label and direction.\<close>
    have hsch_2k: "?scheme!(2*k) = (k, True)" using projective_scheme_nth h2k hlen by (by100 simp)
    have hsch_2k1: "?scheme!(2*k+1) = (k, True)" using projective_scheme_nth h2k1 hlen by (by100 simp)
    have hlabel_eq: "fst (?scheme!(2*k)) = fst (?scheme!(2*k+1))"
      using hsch_2k hsch_2k1 by (by100 simp)
    have hdir_eq: "snd (?scheme!(2*k)) = snd (?scheme!(2*k+1))"
      using hsch_2k hsch_2k1 by (by100 simp)
    \<comment> \<open>From hedge with same label and same direction at t=0:
       q(vx(2k), vy(2k)) = q(vx(2k+1), vy(2k+1)).\<close>
    have hedge_inst: "q ((1-0) * vx (2*k) + 0 * vx (Suc (2*k) mod ?n),
           (1-0) * vy (2*k) + 0 * vy (Suc (2*k) mod ?n))
       = q ((1-0) * vx (2*k+1) + 0 * vx (Suc (2*k+1) mod ?n),
            (1-0) * vy (2*k+1) + 0 * vy (Suc (2*k+1) mod ?n))"
    proof -
      from hedge have
        "\<forall>t\<in>I_set. q ((1-t) * vx (2*k) + t * vx (Suc (2*k) mod ?n),
           (1-t) * vy (2*k) + t * vy (Suc (2*k) mod ?n))
         = (if snd (?scheme!(2*k)) = snd (?scheme!(2*k+1))
            then q ((1-t) * vx (2*k+1) + t * vx (Suc (2*k+1) mod ?n),
                    (1-t) * vy (2*k+1) + t * vy (Suc (2*k+1) mod ?n))
            else q (t * vx (2*k+1) + (1-t) * vx (Suc (2*k+1) mod ?n),
                    t * vy (2*k+1) + (1-t) * vy (Suc (2*k+1) mod ?n)))"
        using h2k h2k1 hlabel_eq by (by100 blast)
      hence "q ((1-0) * vx (2*k) + 0 * vx (Suc (2*k) mod ?n),
           (1-0) * vy (2*k) + 0 * vy (Suc (2*k) mod ?n))
         = (if snd (?scheme!(2*k)) = snd (?scheme!(2*k+1))
            then q ((1-0) * vx (2*k+1) + 0 * vx (Suc (2*k+1) mod ?n),
                    (1-0) * vy (2*k+1) + 0 * vy (Suc (2*k+1) mod ?n))
            else q (0 * vx (2*k+1) + (1-0) * vx (Suc (2*k+1) mod ?n),
                    0 * vy (2*k+1) + (1-0) * vy (Suc (2*k+1) mod ?n)))"
        using h0_I by (by100 blast)
      thus ?thesis using hdir_eq by (by100 simp)
    qed
    have hv_eq: "q (vx (2*k), vy (2*k)) = q (vx (2*k+1), vy (2*k+1))"
      using hedge_inst by (by100 simp)
    \<comment> \<open>Similarly at t=1: q(vx(Suc(2k) mod n), vy(...)) = q(vx(Suc(2k+1) mod n), vy(...)).\<close>
    have hSuc_2k: "Suc (2*k) mod ?n = 2*k+1" using h2k1 hlen by (by100 simp)
    show "q (vx i, vy i) = q (vx (Suc i mod ?n), vy (Suc i mod ?n))"
    proof (cases "i mod 2 = 0")
      case True
      hence "i = 2*k" using k_def by (by5000 auto)
      thus ?thesis using hv_eq hSuc_2k by (by100 simp)
    next
      case False
      hence "i mod 2 = 1" by (by100 simp)
      hence "i = 2*k+1" using k_def
        by (by5000 presburger)
      \<comment> \<open>From hedge at t=1 on (2k, 2k+1):
         q(vx(Suc 2k mod n), ...) = q(vx(Suc(2k+1) mod n), ...).
         I.e., q(vx(2k+1), ...) = q(vx(2k+2 mod n), ...).\<close>
      have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
      have hedge_2k_2k1: "\<forall>t\<in>I_set. q ((1-t) * vx (2*k) + t * vx (Suc (2*k) mod ?n),
           (1-t) * vy (2*k) + t * vy (Suc (2*k) mod ?n))
         = q ((1-t) * vx (2*k+1) + t * vx (Suc (2*k+1) mod ?n),
              (1-t) * vy (2*k+1) + t * vy (Suc (2*k+1) mod ?n))"
      proof -
        from hedge h2k h2k1 hlabel_eq
        have h_raw: "\<forall>t\<in>I_set. q ((1-t) * vx (2*k) + t * vx (Suc (2*k) mod ?n),
           (1-t) * vy (2*k) + t * vy (Suc (2*k) mod ?n))
         = (if snd (?scheme!(2*k)) = snd (?scheme!(2*k+1))
            then q ((1-t) * vx (2*k+1) + t * vx (Suc (2*k+1) mod ?n),
                    (1-t) * vy (2*k+1) + t * vy (Suc (2*k+1) mod ?n))
            else q (t * vx (2*k+1) + (1-t) * vx (Suc (2*k+1) mod ?n),
                    t * vy (2*k+1) + (1-t) * vy (Suc (2*k+1) mod ?n)))"
          by (by5000 blast)
        thus ?thesis using hdir_eq by (by100 simp)
      qed
      hence "q ((1-1) * vx (2*k) + 1 * vx (Suc (2*k) mod ?n),
           (1-1) * vy (2*k) + 1 * vy (Suc (2*k) mod ?n))
         = q ((1-1) * vx (2*k+1) + 1 * vx (Suc (2*k+1) mod ?n),
              (1-1) * vy (2*k+1) + 1 * vy (Suc (2*k+1) mod ?n))"
        using h1_I by (by100 blast)
      hence "q (vx (Suc (2*k) mod ?n), vy (Suc (2*k) mod ?n))
         = q (vx (Suc (2*k+1) mod ?n), vy (Suc (2*k+1) mod ?n))"
        by (by100 simp)
      hence "q (vx (2*k+1), vy (2*k+1)) = q (vx (Suc (2*k+1) mod ?n), vy (Suc (2*k+1) mod ?n))"
        using hSuc_2k by (by100 simp)
      thus ?thesis using \<open>i = 2*k+1\<close> by (by100 simp)
    qed
  qed
  \<comment> \<open>Chain adjacent equalities to get all vertices equal.\<close>
    have hchain: "\<And>k. k < ?n \<Longrightarrow> q (vx 0, vy 0) = q (vx k, vy k)"
    proof -
      fix k show "k < ?n \<Longrightarrow> q (vx 0, vy 0) = q (vx k, vy k)"
      proof (induction k)
        case 0 thus ?case by (by100 simp)
      next
        case (Suc k)
        have "k < ?n" using Suc.prems by (by100 simp)
        hence IH: "q (vx 0, vy 0) = q (vx k, vy k)" using Suc.IH by (by100 blast)
        have "q (vx k, vy k) = q (vx (Suc k mod ?n), vy (Suc k mod ?n))"
          using hadjacent \<open>k < ?n\<close> by (by100 blast)
        moreover have "Suc k mod ?n = Suc k" using Suc.prems by (by100 simp)
        ultimately show ?case using IH by (by100 simp)
      qed
    qed
    have "\<forall>i<?n. \<forall>j<?n. q (vx i, vy i) = q (vx j, vy j)"
    proof (intro allI impI)
      fix i j assume "i < ?n" "j < ?n"
      from hchain[OF \<open>i < ?n\<close>] hchain[OF \<open>j < ?n\<close>]
      show "q (vx i, vy i) = q (vx j, vy j)" by (by100 simp)
    qed
  }
  thus ?thesis by (by100 blast)
qed


end
