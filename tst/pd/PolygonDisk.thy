theory PolygonDisk
  imports "AlgTopGroups.AlgTopGroups"
begin

lemma compact_R2_bridge:
  assumes "compact (A :: (real \<times> real) set)"
  shows "top1_compact_on A (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) A)"
proof -
  let ?R2 = "UNIV :: (real \<times> real) set"
  let ?T = "product_topology_on top1_open_sets top1_open_sets"
  let ?TA = "subspace_topology ?R2 ?T A"
  \<comment> \<open>The subspace topology is a topology.\<close>
  have hA_sub: "A \<subseteq> ?R2" by (by100 blast)
  have hT_top: "is_topology_on ?R2 ?T"
  proof -
    have "is_topology_on (UNIV::real set) top1_open_sets"
      unfolding top1_open_sets_def is_topology_on_def
      using open_UNIV open_empty open_Un open_Int by (by5000 auto)
    hence "is_topology_on ((UNIV::real set) \<times> (UNIV::real set)) ?T"
      using product_topology_on_is_topology_on by (by100 blast)
    thus ?thesis by (by100 simp)
  qed
  have hTA_top: "is_topology_on A ?TA"
    by (rule subspace_topology_is_topology_on[OF hT_top hA_sub])
  \<comment> \<open>Every cover of A from ?TA has a finite subcover.\<close>
  have hcover: "\<And>Uc. Uc \<subseteq> ?TA \<Longrightarrow> A \<subseteq> \<Union>Uc \<Longrightarrow> \<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F"
  proof -
    fix Uc assume hUc: "Uc \<subseteq> ?TA" and hcover: "A \<subseteq> \<Union>Uc"
    \<comment> \<open>Each U \<in> Uc is A \<inter> V for some V \<in> ?T. The V's form an open cover of A.\<close>
    \<comment> \<open>Each V \<in> ?T corresponds to an open set (product topology = standard topology).\<close>
    \<comment> \<open>compact A gives a finite subcover of V's, hence of U's.\<close>
    \<comment> \<open>For each U \<in> Uc, extract V \<in> R^2\_top with U = A \<inter> V.\<close>
    define VV where "VV U = (SOME V. V \<in> ?T \<and> U = A \<inter> V)" for U
    have hVV: "\<And>U. U \<in> Uc \<Longrightarrow> VV U \<in> ?T \<and> U = A \<inter> VV U"
    proof -
      fix U assume "U \<in> Uc"
      hence "U \<in> ?TA" using hUc by (by100 blast)
      hence "\<exists>V. V \<in> ?T \<and> U = A \<inter> V"
        unfolding subspace_topology_def by (by5000 blast)
      thus "VV U \<in> ?T \<and> U = A \<inter> VV U" unfolding VV_def by (rule someI_ex)
    qed
    \<comment> \<open>The V's cover A.\<close>
    have hV_cover: "A \<subseteq> \<Union>(VV ` Uc)"
    proof (rule subsetI)
      fix x assume "x \<in> A"
      from hcover \<open>x \<in> A\<close> obtain U where "U \<in> Uc" "x \<in> U" by (by100 blast)
      hence "x \<in> A \<inter> VV U" using hVV by (by100 blast)
      hence "x \<in> VV U" by (by100 blast)
      thus "x \<in> \<Union>(VV ` Uc)" using \<open>U \<in> Uc\<close> by (by100 blast)
    qed
    \<comment> \<open>Each VV U is open (product topology = standard open sets).\<close>
    have hV_open: "\<And>U. U \<in> Uc \<Longrightarrow> open (VV U)"
    proof -
      fix U assume "U \<in> Uc"
      from hVV[OF this] have hvu: "VV U \<in> ?T" by (by100 blast)
      have "?T = top1_open_sets" by (rule product_topology_on_open_sets)
      hence "VV U \<in> top1_open_sets" using hvu by (by5000 fast)
      thus "open (VV U)" unfolding top1_open_sets_def by (by100 blast)
    qed
    \<comment> \<open>compact A gives a finite subcover.\<close>
    have "\<exists>F. finite F \<and> F \<subseteq> VV ` Uc \<and> A \<subseteq> \<Union>F"
    proof -
      have hopen: "\<forall>V \<in> VV ` Uc. open V" using hV_open by (by100 blast)
      from assms have hHB: "\<And>C. (\<forall>c\<in>C. open c) \<Longrightarrow> A \<subseteq> \<Union>C \<Longrightarrow> \<exists>D\<subseteq>C. finite D \<and> A \<subseteq> \<Union>D"
        unfolding compact_eq_Heine_Borel by (by100 blast)
      from hHB[OF hopen hV_cover]
      obtain D where "D \<subseteq> VV ` Uc" "finite D" "A \<subseteq> \<Union>D" by (by5000 blast)
      thus ?thesis by (by100 blast)
    qed
    then obtain FV where hFV_fin: "finite FV" and hFV_sub: "FV \<subseteq> VV ` Uc"
      and hFV_cover: "A \<subseteq> \<Union>FV" by (by5000 fast)
    \<comment> \<open>Map back: for each V \<in> FV, pick one representative U \<in> Uc with VV U = V.\<close>
    define rep where "rep V = (SOME U. U \<in> Uc \<and> VV U = V)" for V
    have hrep: "\<And>V. V \<in> FV \<Longrightarrow> rep V \<in> Uc \<and> VV (rep V) = V"
    proof -
      fix V assume "V \<in> FV"
      hence "V \<in> VV ` Uc" using hFV_sub by (by100 blast)
      hence "\<exists>U. U \<in> Uc \<and> VV U = V" by (by100 blast)
      thus "rep V \<in> Uc \<and> VV (rep V) = V" unfolding rep_def by (rule someI_ex)
    qed
    define FU where "FU = rep ` FV"
    have "finite FU" unfolding FU_def using hFV_fin by (by100 blast)
    have "FU \<subseteq> Uc" unfolding FU_def using hrep by (by100 blast)
    have "A \<subseteq> \<Union>FU"
    proof (rule subsetI)
      fix x assume "x \<in> A"
      from hFV_cover \<open>x \<in> A\<close> obtain V where "V \<in> FV" "x \<in> V" by (by100 blast)
      have "rep V \<in> FU" unfolding FU_def using \<open>V \<in> FV\<close> by (by100 blast)
      moreover have "x \<in> rep V"
        using hVV[OF conjunct1[OF hrep[OF \<open>V \<in> FV\<close>]]] \<open>x \<in> A\<close> \<open>x \<in> V\<close>
          conjunct2[OF hrep[OF \<open>V \<in> FV\<close>]] by (by100 blast)
      ultimately show "x \<in> \<Union>FU" by (by100 blast)
    qed
    show "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> A \<subseteq> \<Union>F"
      using \<open>finite FU\<close> \<open>FU \<subseteq> Uc\<close> \<open>A \<subseteq> \<Union>FU\<close> by (by100 blast)
  qed
  show ?thesis unfolding top1_compact_on_def using hTA_top hcover by (by100 blast)
qed

text \<open>Helper: 2D cross product (signed area of parallelogram).\<close>
definition cross2 :: "real \<times> real \<Rightarrow> real \<times> real \<Rightarrow> real" where
  "cross2 a b = fst a * snd b - snd a * fst b"

text \<open>For a convex polygon with centroid c, the cross products cross(v_i - c, d)
  sum to 0 for any direction d. This means there exists a sign change,
  giving the sector containing d.\<close>
lemma cross2_centroid_sum_zero:
  fixes vx vy :: "nat \<Rightarrow> real" and n :: nat and dx dy :: real
  assumes "n \<ge> 1"
  defines "cx \<equiv> (\<Sum>i<n. vx i) / real n" and "cy \<equiv> (\<Sum>i<n. vy i) / real n"
  shows "(\<Sum>i<n. cross2 (vx i - cx, vy i - cy) (dx, dy)) = 0"
proof -
  have hvx_sum: "(\<Sum>i<n. vx i) = real n * cx" unfolding cx_def using assms by (by100 simp)
  have hvy_sum: "(\<Sum>i<n. vy i) = real n * cy" unfolding cy_def using assms by (by100 simp)
  \<comment> \<open>The sum telescopes: cross2(v_i-c, d) = (vx_i-cx)*dy - (vy_i-cy)*dx.
     \<Sum> = dy*(\<Sum>vx_i - n*cx) - dx*(\<Sum>vy_i - n*cy) = dy*0 - dx*0 = 0.\<close>
  have hstep1: "\<And>i. (vx i - cx) * dy - (vy i - cy) * dx
      = vx i * dy - cx * dy - (vy i * dx - cy * dx)"
    by (simp add: algebra_simps)
  \<comment> \<open>Step 1: Expand cross2.\<close>
  have heq1: "(\<Sum>i<n. cross2 (vx i - cx, vy i - cy) (dx, dy))
      = (\<Sum>i<n. (vx i - cx) * dy - (vy i - cy) * dx)"
    unfolding cross2_def by (by100 simp)
  \<comment> \<open>Step 2: Split sum of differences.\<close>
  have heq2: "(\<Sum>i<n. (vx i - cx) * dy - (vy i - cy) * dx)
      = (\<Sum>i<n. (vx i - cx) * dy) - (\<Sum>i<n. (vy i - cy) * dx)"
    using sum_subtractf[of "\<lambda>i. (vx i - cx) * dy" "\<lambda>i. (vy i - cy) * dx" "{..<n}", symmetric]
    by (by5000 simp)
  \<comment> \<open>Step 3: Each sub-sum is zero because \<Sum>(vx_i - cx) = \<Sum>vx_i - n*cx = 0.\<close>
  have hvx_diff_sum: "(\<Sum>i<n. vx i - cx) = 0"
    using sum_subtractf[of vx "\<lambda>_. cx" "{..<n}"] hvx_sum by (by5000 simp)
  have hvy_diff_sum: "(\<Sum>i<n. vy i - cy) = 0"
    using sum_subtractf[of vy "\<lambda>_. cy" "{..<n}"] hvy_sum by (by5000 simp)
  have hx_zero: "(\<Sum>i<n. (vx i - cx) * dy) = 0"
  proof -
    have "(\<Sum>i<n. (vx i - cx) * dy) = (\<Sum>i<n. (vx i - cx)) * dy"
      using sum_distrib_right[of "\<lambda>i. vx i - cx" "{..<n}" dy, symmetric] by (by100 simp)
    thus ?thesis using hvx_diff_sum by (by100 simp)
  qed
  have hy_zero: "(\<Sum>i<n. (vy i - cy) * dx) = 0"
  proof -
    have "(\<Sum>i<n. (vy i - cy) * dx) = (\<Sum>i<n. (vy i - cy)) * dx"
      using sum_distrib_right[of "\<lambda>i. vy i - cy" "{..<n}" dx, symmetric] by (by100 simp)
    thus ?thesis using hvy_diff_sum by (by100 simp)
  qed
  show ?thesis using heq1 heq2 hx_zero hy_zero by (by100 simp)
qed

lemma cross2_antisym: "cross2 a b = - cross2 b a"
  unfolding cross2_def by (simp add: algebra_simps)

lemma cross2_self: "cross2 a a = 0"
  unfolding cross2_def by (simp add: algebra_simps)

lemma cross2_linear_left_add: "cross2 (fst a + fst b, snd a + snd b) c =
    cross2 a c + cross2 b c"
  unfolding cross2_def by (simp add: algebra_simps)

lemma cross2_linear_left_scale: "cross2 (r * fst a, r * snd a) b =
    r * cross2 a b"
  unfolding cross2_def by (simp add: algebra_simps)

lemma cross2_linear_right_add: "cross2 a (fst b + fst c, snd b + snd c) =
    cross2 a b + cross2 a c"
  unfolding cross2_def by (simp add: algebra_simps)

lemma cross2_linear_right_scale: "cross2 a (r * fst b, r * snd b) =
    r * cross2 a b"
  unfolding cross2_def by (simp add: algebra_simps)

text \<open>For a convex polygon where all vertices satisfy the half-plane condition
  (cross2(v_k - v_i, v_{i+1} - v_i) \<le> 0 for all k), every convex combination also satisfies it.\<close>
lemma ccw_polygon_half_plane:
  fixes vx vy :: "nat \<Rightarrow> real" and n :: nat and coeffs :: "nat \<Rightarrow> real"
  assumes hn: "n \<ge> 3"
      and hcoeffs_ge: "\<forall>j<n. coeffs j \<ge> (0::real)"
      and hcoeffs_sum: "(\<Sum>j<n. coeffs j) = 1"
      and hzx: "zx = (\<Sum>j<n. coeffs j * vx j)"
      and hzy: "zy = (\<Sum>j<n. coeffs j * vy j)"
      and hi: "i < n"
      and hvert_hp: "\<forall>k<n. cross2 (vx k - vx i, vy k - vy i)
          (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
  shows "cross2 (zx - vx i, zy - vy i)
      (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
proof -
  define dx where "dx = vx (Suc i mod n) - vx i"
  define dy where "dy = vy (Suc i mod n) - vy i"
  \<comment> \<open>Express z - v_i as weighted sum of v_k - v_i.\<close>
  have hzx_vi: "zx - vx i = (\<Sum>j<n. coeffs j * (vx j - vx i))"
  proof -
    have "(\<Sum>j<n. coeffs j * vx j) - (\<Sum>j<n. coeffs j) * vx i
        = (\<Sum>j<n. coeffs j * vx j) - (\<Sum>j<n. coeffs j * vx i)"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>j<n. coeffs j * vx j - coeffs j * vx i)"
      using sum_subtractf[of "\<lambda>j. coeffs j * vx j" "\<lambda>j. coeffs j * vx i" "{..<n}"]
      by (by100 simp)
    also have "\<dots> = (\<Sum>j<n. coeffs j * (vx j - vx i))"
      by (rule sum.cong) (simp_all add: algebra_simps)
    finally show ?thesis using hzx hcoeffs_sum by (by100 simp)
  qed
  have hzy_vi: "zy - vy i = (\<Sum>j<n. coeffs j * (vy j - vy i))"
  proof -
    have "(\<Sum>j<n. coeffs j * vy j) - (\<Sum>j<n. coeffs j) * vy i
        = (\<Sum>j<n. coeffs j * vy j) - (\<Sum>j<n. coeffs j * vy i)"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>j<n. coeffs j * vy j - coeffs j * vy i)"
      using sum_subtractf[of "\<lambda>j. coeffs j * vy j" "\<lambda>j. coeffs j * vy i" "{..<n}"]
      by (by100 simp)
    also have "\<dots> = (\<Sum>j<n. coeffs j * (vy j - vy i))"
      by (rule sum.cong) (simp_all add: algebra_simps)
    finally show ?thesis using hzy hcoeffs_sum by (by100 simp)
  qed
  \<comment> \<open>cross2(z - v_i, v_{i+1} - v_i) = \<Sum> coeffs_k * cross2(v_k - v_i, v_{i+1} - v_i).\<close>
  have "cross2 (zx - vx i, zy - vy i) (dx, dy) =
      (\<Sum>j<n. coeffs j * cross2 (vx j - vx i, vy j - vy i) (dx, dy))"
  proof -
    have "cross2 (zx - vx i, zy - vy i) (dx, dy) =
        (zx - vx i) * dy - (zy - vy i) * dx" unfolding cross2_def by (by100 simp)
    also have "\<dots> = (\<Sum>j<n. coeffs j * (vx j - vx i)) * dy -
        (\<Sum>j<n. coeffs j * (vy j - vy i)) * dx"
      using hzx_vi hzy_vi by (by100 simp)
    also have "\<dots> = (\<Sum>j<n. coeffs j * (vx j - vx i) * dy) -
        (\<Sum>j<n. coeffs j * (vy j - vy i) * dx)"
      by (simp add: sum_distrib_right)
    also have "\<dots> = (\<Sum>j<n. coeffs j * (vx j - vx i) * dy - coeffs j * (vy j - vy i) * dx)"
      using sum_subtractf[of "\<lambda>j. coeffs j * (vx j - vx i) * dy"
          "\<lambda>j. coeffs j * (vy j - vy i) * dx" "{..<n}"] by (by100 simp)
    also have "\<dots> = (\<Sum>j<n. coeffs j * ((vx j - vx i) * dy - (vy j - vy i) * dx))"
      by (rule sum.cong) (simp_all add: algebra_simps)
    also have "\<dots> = (\<Sum>j<n. coeffs j * cross2 (vx j - vx i, vy j - vy i) (dx, dy))"
      unfolding cross2_def by (by100 simp)
    finally show ?thesis .
  qed
  moreover have "(\<Sum>j<n. coeffs j * cross2 (vx j - vx i, vy j - vy i) (dx, dy)) \<le> 0"
  proof (rule sum_nonpos)
    fix j assume "j \<in> {..<n}"
    hence hj: "j < n" by (by100 simp)
    have "cross2 (vx j - vx i, vy j - vy i) (dx, dy) \<le> 0"
      using hvert_hp[rule_format, OF hj] unfolding dx_def dy_def .
    thus "coeffs j * cross2 (vx j - vx i, vy j - vy i) (dx, dy) \<le> 0"
      using mult_nonneg_nonpos[OF hcoeffs_ge[rule_format, OF hj]] by (by100 blast)
  qed
  ultimately show ?thesis unfolding dx_def dy_def by (by100 simp)
qed

text \<open>If a sequence of reals sums to 0 and is not all zero, there exists an index
  where consecutive elements have opposite signs (a sign change).\<close>
lemma cyclic_sign_change:
  fixes f :: "nat \<Rightarrow> real" and n :: nat
  assumes "n \<ge> 2" and "(\<Sum>i<n. f i) = 0" and "\<exists>i<n. f i \<noteq> 0"
  shows "\<exists>i<n. f i \<ge> 0 \<and> f ((i+1) mod n) \<le> 0"
proof -
  \<comment> \<open>Since \<Sum>f_i = 0 and not all zero, there exist positive and negative values.\<close>
  \<comment> \<open>If no f_i \<ge> 0 had successor f_{i+1} \<le> 0, then every f_i \<ge> 0 implies f_{i+1} \<ge> 0.
     This transitivity around the cycle would force all f_i \<ge> 0 (starting from any
     positive element). But \<Sum>f_i = 0 with all f_i \<ge> 0 forces all = 0, contradicting \<exists>f_i \<noteq> 0.\<close>
  show ?thesis
  proof (rule ccontr)
    assume hno: "\<not> (\<exists>i<n. f i \<ge> 0 \<and> f ((i+1) mod n) \<le> 0)"
    hence htrans: "\<forall>i<n. f i \<ge> 0 \<longrightarrow> f ((i+1) mod n) > 0" by (by100 force)
    \<comment> \<open>From htrans: any non-negative f_i implies f_{i+1} > 0 (hence \<ge> 0), which propagates.\<close>
    \<comment> \<open>Either all f_i < 0 (contradicts \<Sum>=0 + not all zero → some must be \<ge> 0),
       or some f_i \<ge> 0, which propagates to all f_j > 0, contradicting \<Sum>=0.\<close>
    \<comment> \<open>Case 1: All f_i < 0. Then \<Sum>f_i < 0 (n \<ge> 2), contradicting \<Sum>=0.\<close>
    \<comment> \<open>Case 2: Some f_k \<ge> 0. By htrans, f_{k+1} > 0 \<ge> 0, f_{k+2} > 0, etc.
       After n steps: all f_i > 0. But \<Sum>f_i > 0, contradicting \<Sum>=0.\<close>
    show False
    proof (cases "\<forall>i<n. f i < 0")
      case True
      have "(\<Sum>i<n. f i) < 0"
      proof -
        have "(\<Sum>i<n. f i) \<le> 0"
          using sum_nonpos[of "{..<n}" f] True by (by5000 force)
        moreover have "(\<Sum>i<n. f i) \<noteq> 0"
        proof
          assume "(\<Sum>i<n. f i) = 0"
          have "(\<Sum>i<n. - f i) = - (\<Sum>i<n. f i)"
            using sum_negf by (by100 blast)
          hence "(\<Sum>i<n. - f i) = 0" using \<open>(\<Sum>i<n. f i) = 0\<close> by (by100 simp)
          have hnn: "\<And>x. x \<in> {..<n} \<Longrightarrow> 0 \<le> - f x"
            using True by (by100 force)
          hence "\<forall>i\<in>{..<n}. - f i = 0"
            using sum_nonneg_eq_0_iff[of "{..<n}" "\<lambda>i. - f i"]
              \<open>(\<Sum>i<n. - f i) = 0\<close> hnn by (by100 blast)
          hence "\<forall>i<n. f i = 0" by (by100 force)
          thus False using assms(3) by (by100 blast)
        qed
        ultimately show ?thesis by (by100 linarith)
      qed
      thus False using assms(2) by (by100 simp)
    next
      case False
      then obtain k where hk: "k < n" "f k \<ge> 0" by (by100 force)
      \<comment> \<open>Propagate: f_k \<ge> 0 \<Rightarrow> f_{k+1} > 0 \<Rightarrow> f_{k+2} > 0 \<Rightarrow> ... \<Rightarrow> all > 0.\<close>
      have hprop: "\<And>j. j < n \<Longrightarrow> f ((k + j) mod n) \<ge> 0"
      proof -
        fix j show "j < n \<Longrightarrow> f ((k + j) mod n) \<ge> 0"
        proof (induction j)
          case 0 thus ?case using hk by (by100 simp)
        next
          case (Suc j)
          hence hj: "j < n" by (by100 simp)
          have hjmod: "(k + j) mod n < n" using assms(1) by (by100 simp)
          have hfj: "f ((k + j) mod n) \<ge> 0" using Suc.IH hj by (by100 blast)
          from htrans[rule_format, OF hjmod hfj]
          have "f (((k + j) mod n + 1) mod n) > 0" .
          moreover have "((k + j) mod n + 1) mod n = (k + Suc j) mod n"
          proof -
            have "((k + j) mod n + 1) mod n = (k + j + 1) mod n"
              using mod_add_left_eq[of "k+j" n 1] by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
          ultimately show ?case by (by100 simp)
        qed
      qed
      have "\<forall>i<n. f i \<ge> 0"
      proof (intro allI impI)
        fix i assume "i < n"
        \<comment> \<open>i = (k + ((i - k) mod n)) mod n, and (i - k) mod n < n.\<close>
        have "\<exists>j<n. (k + j) mod n = i"
        proof (cases "k \<le> i")
          case True
          show ?thesis
            apply (rule exI[of _ "i - k"])
            using True \<open>i < n\<close> hk(1) by (by100 simp)
        next
          case False
          hence hki: "k > i" by (by100 simp)
          show ?thesis
            apply (rule exI[of _ "n - k + i"])
            using hki \<open>i < n\<close> hk(1) by (by5000 simp)
        qed
        then obtain j where "j < n" "(k + j) mod n = i" by (by100 blast)
        thus "f i \<ge> 0" using hprop[of j] by (by100 simp)
      qed
      hence "\<forall>i<n. f i = 0"
        using sum_nonneg_eq_0_iff[of "{..<n}" f] assms(2)
        by (by5000 force)
      thus False using assms(3) by (by100 blast)
    qed
  qed
qed

text \<open>Strict version: there exists i where f(i) > 0 and f(i+1) \<le> 0.\<close>
lemma cyclic_strict_sign_change:
  fixes f :: "nat \<Rightarrow> real" and n :: nat
  assumes "n \<ge> 2" and "(\<Sum>i<n. f i) = 0" and "\<exists>i<n. f i > 0"
  shows "\<exists>i<n. f i > 0 \<and> f ((i+1) mod n) \<le> 0"
proof (rule ccontr)
  assume "\<not> (\<exists>i<n. f i > 0 \<and> f ((i+1) mod n) \<le> 0)"
  hence htrans: "\<forall>i<n. f i > 0 \<longrightarrow> f ((i+1) mod n) > 0" by (by100 force)
  \<comment> \<open>From assms(3): \<exists>k with f(k) > 0. By htrans, all successors > 0. After n steps: all > 0.\<close>
  from assms(3) obtain k where hk: "k < n" "f k > 0" by (by100 blast)
  have hprop: "\<And>j. j < n \<Longrightarrow> f ((k + j) mod n) > 0"
  proof -
    fix j show "j < n \<Longrightarrow> f ((k + j) mod n) > 0"
    proof (induction j)
      case 0 thus ?case using hk by (by100 simp)
    next
      case (Suc j)
      hence hj: "j < n" by (by100 simp)
      have hjmod: "(k + j) mod n < n" using assms(1) by (by100 simp)
      have "f ((k + j) mod n) > 0" using Suc.IH hj by (by100 blast)
      from htrans[rule_format, OF hjmod this]
      have "f (((k + j) mod n + 1) mod n) > 0" .
      moreover have "((k + j) mod n + 1) mod n = (k + Suc j) mod n"
        using mod_add_left_eq[of "k+j" n 1] by (by100 simp)
      ultimately show ?case by (by100 simp)
    qed
  qed
  have "\<forall>i<n. f i > 0"
  proof (intro allI impI)
    fix i assume "i < n"
    have "\<exists>j<n. (k + j) mod n = i"
    proof (cases "k \<le> i")
      case True show ?thesis apply (rule exI[of _ "i - k"])
        using True \<open>i < n\<close> hk(1) by (by100 simp)
    next
      case False show ?thesis apply (rule exI[of _ "n - k + i"])
        using False \<open>i < n\<close> hk(1) by (by5000 simp)
    qed
    then obtain j where "j < n" "(k + j) mod n = i" by (by100 blast)
    thus "f i > 0" using hprop[of j] by (by100 simp)
  qed
  hence "(\<Sum>i<n. f i) > 0"
  proof -
    have "(\<Sum>i<n. f i) \<ge> 0" using \<open>\<forall>i<n. f i > 0\<close>
      by (intro sum_nonneg) (by100 force)
    moreover have "f 0 > 0" using \<open>\<forall>i<n. f i > 0\<close> assms(1) by (by100 simp)
    moreover have "0 < n" using assms(1) by (by100 simp)
    ultimately show ?thesis
      using sum_pos[of "{..<n}" f] \<open>\<forall>i<n. f i > 0\<close> by (by5000 force)
  qed
  thus False using assms(2) by (by100 simp)
qed

text \<open>A convex polygon in R^2 is homeomorphic to B^2 (the closed unit disk).
  This is a standard topology fact (radial projection from centroid).\<close>
text \<open>Continuous image of path-connected is path-connected.\<close>
lemma top1_path_connected_continuous_image:
  assumes "top1_path_connected_on X TX"
      and "top1_continuous_map_on X TX Y TY f"
      and "\<forall>x \<in> X. f x \<in> Y"
      and "f ` X = Z" and "Z \<subseteq> Y"
      and "TZ = subspace_topology Y TY Z"
      and "is_topology_on Y TY"
  shows "top1_path_connected_on Z TZ"
proof -
  show ?thesis unfolding top1_path_connected_on_def
  proof (intro conjI)
    show "is_topology_on Z TZ" unfolding assms(6)
    proof (rule subspace_topology_is_topology_on)
      show "is_topology_on Y TY" by (rule assms(7))
      show "Z \<subseteq> Y" by (rule assms(5))
    qed
    show "\<forall>a\<in>Z. \<forall>b\<in>Z. \<exists>\<gamma>. top1_is_path_on Z TZ a b \<gamma>"
    proof (intro ballI)
      fix a b assume ha: "a \<in> Z" and hb: "b \<in> Z"
      \<comment> \<open>Pick preimages x, y \<in> X.\<close>
      from ha assms(4) obtain x where hx: "x \<in> X" "f x = a" by (by100 blast)
      from hb assms(4) obtain y where hy: "y \<in> X" "f y = b" by (by100 blast)
      \<comment> \<open>Path from x to y in X.\<close>
      from assms(1)[unfolded top1_path_connected_on_def] hx(1) hy(1)
      obtain \<gamma> where h\<gamma>: "top1_is_path_on X TX x y \<gamma>" by (by100 blast)
      \<comment> \<open>f \<circ> \<gamma> is a path from a to b in Z.\<close>
      show "\<exists>\<gamma>. top1_is_path_on Z TZ a b \<gamma>"
      proof (rule exI[of _ "f \<circ> \<gamma>"])
        show "top1_is_path_on Z TZ a b (f \<circ> \<gamma>)"
          unfolding top1_is_path_on_def
        proof (intro conjI)
          \<comment> \<open>f \<circ> \<gamma> continuous from I to Z.\<close>
          have h\<gamma>_cont: "top1_continuous_map_on I_set top1_unit_interval_topology X TX \<gamma>"
            using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
          have hf\<gamma>_cont_Y: "top1_continuous_map_on I_set top1_unit_interval_topology Y TY (f \<circ> \<gamma>)"
            using top1_continuous_map_on_comp[OF h\<gamma>_cont assms(2)] .
          \<comment> \<open>f\<circ>\<gamma> maps I to Z (since \<gamma> maps to X and f maps X to Z).\<close>
          have himg: "\<forall>t \<in> I_set. (f \<circ> \<gamma>) t \<in> Z"
          proof (intro ballI)
            fix t assume "t \<in> I_set"
            have "\<gamma> t \<in> X" using h\<gamma>_cont \<open>t \<in> I_set\<close>
              unfolding top1_continuous_map_on_def by (by100 blast)
            thus "(f \<circ> \<gamma>) t \<in> Z" using assms(4) by (by100 auto)
          qed
          \<comment> \<open>Continuous into Z = subspace of Y.\<close>
          show "top1_continuous_map_on I_set top1_unit_interval_topology Z TZ (f \<circ> \<gamma>)"
            unfolding assms(6)
            by (rule continuous_map_restrict_codomain[OF hf\<gamma>_cont_Y himg assms(5)])
          show "(f \<circ> \<gamma>) 0 = a" using h\<gamma>[unfolded top1_is_path_on_def] hx(2) by (by100 simp)
          show "(f \<circ> \<gamma>) 1 = b" using h\<gamma>[unfolded top1_is_path_on_def] hy(2) by (by100 simp)
        qed
      qed
    qed
  qed
qed

lemma polygonal_region_convex_combo:
  assumes "top1_is_polygonal_region_on P n" and "n \<ge> 3"
      and "x \<in> P" and "y \<in> P" and "0 \<le> t" and "t \<le> 1"
  shows "((1-t) * fst x + t * fst y, (1-t) * snd x + t * snd y) \<in> P"
proof -
  from assms(1)[unfolded top1_is_polygonal_region_on_def]
  obtain vx vy where
    hP_eq: "P = {(x, y) | x y. \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
          \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
    by (elim conjE exE) (rule that, assumption+)
  obtain xx xy where hx_eq: "x = (xx, xy)" by (cases x) (by100 blast)
  obtain yx yy where hy_eq: "y = (yx, yy)" by (cases y) (by100 blast)
  from assms(3) obtain a where ha: "\<forall>i<n. a i \<ge> 0" "(\<Sum>i<n. a i) = 1"
      "xx = (\<Sum>i<n. a i * vx i)" "xy = (\<Sum>i<n. a i * vy i)"
    unfolding hP_eq hx_eq by (by5000 auto)
  from assms(4) obtain b where hb: "\<forall>i<n. b i \<ge> 0" "(\<Sum>i<n. b i) = 1"
      "yx = (\<Sum>i<n. b i * vx i)" "yy = (\<Sum>i<n. b i * vy i)"
    unfolding hP_eq hy_eq by (by5000 auto)
  define c where "c i = (1-t) * a i + t * b i" for i
  have hcge: "\<forall>i<n. c i \<ge> 0" unfolding c_def using ha(1) hb(1) assms(5,6) by (by100 auto)
  have hcsum: "(\<Sum>i<n. c i) = 1"
  proof -
    have "(\<Sum>i<n. c i) = (\<Sum>i<n. (1-t) * a i) + (\<Sum>i<n. t * b i)"
      unfolding c_def using sum.distrib[of "\<lambda>i. (1-t)*a i" "\<lambda>i. t*b i" "{..<n}", symmetric]
      by (by100 simp)
    also have "(\<Sum>i<n. (1-t) * a i) = (1-t) * (\<Sum>i<n. a i)"
      using sum_distrib_left[of "1-t" a "{..<n}", symmetric] by (by100 simp)
    also have "(\<Sum>i<n. t * b i) = t * (\<Sum>i<n. b i)"
      using sum_distrib_left[of t b "{..<n}", symmetric] by (by100 simp)
    finally show ?thesis using ha(2) hb(2) by (by100 simp)
  qed
  have hcvx: "(1-t)*xx + t*yx = (\<Sum>i<n. c i * vx i)"
  proof -
    have "(\<Sum>i<n. c i * vx i) = (\<Sum>i<n. ((1-t)*a i + t*b i) * vx i)" unfolding c_def ..
    also have "\<dots> = (\<Sum>i<n. (1-t)*a i*vx i + t*b i*vx i)"
      by (rule sum.cong) (simp add: algebra_simps)+
    also have "\<dots> = (\<Sum>i<n. (1-t)*(a i*vx i)) + (\<Sum>i<n. t*(b i*vx i))"
      using sum.distrib[of "\<lambda>i. (1-t)*(a i*vx i)" "\<lambda>i. t*(b i*vx i)" "{..<n}", symmetric]
      by (simp add: mult.assoc)
    also have "(\<Sum>i<n. (1-t)*(a i*vx i)) = (1-t)*(\<Sum>i<n. a i*vx i)"
      using sum_distrib_left[of "1-t" "\<lambda>i. a i*vx i" "{..<n}", symmetric] by (by100 simp)
    also have "(\<Sum>i<n. t*(b i*vx i)) = t*(\<Sum>i<n. b i*vx i)"
      using sum_distrib_left[of t "\<lambda>i. b i*vx i" "{..<n}", symmetric] by (by100 simp)
    finally show ?thesis using ha(3) hb(3) by (by100 simp)
  qed
  have hcvy: "(1-t)*xy + t*yy = (\<Sum>i<n. c i * vy i)"
  proof -
    have "(\<Sum>i<n. c i * vy i) = (\<Sum>i<n. ((1-t)*a i + t*b i) * vy i)" unfolding c_def ..
    also have "\<dots> = (\<Sum>i<n. (1-t)*a i*vy i + t*b i*vy i)"
      by (rule sum.cong) (simp add: algebra_simps)+
    also have "\<dots> = (\<Sum>i<n. (1-t)*(a i*vy i)) + (\<Sum>i<n. t*(b i*vy i))"
      using sum.distrib[of "\<lambda>i. (1-t)*(a i*vy i)" "\<lambda>i. t*(b i*vy i)" "{..<n}", symmetric]
      by (simp add: mult.assoc)
    also have "(\<Sum>i<n. (1-t)*(a i*vy i)) = (1-t)*(\<Sum>i<n. a i*vy i)"
      using sum_distrib_left[of "1-t" "\<lambda>i. a i*vy i" "{..<n}", symmetric] by (by100 simp)
    also have "(\<Sum>i<n. t*(b i*vy i)) = t*(\<Sum>i<n. b i*vy i)"
      using sum_distrib_left[of t "\<lambda>i. b i*vy i" "{..<n}", symmetric] by (by100 simp)
    finally show ?thesis using ha(4) hb(4) by (by100 simp)
  qed
  show ?thesis unfolding hP_eq hx_eq hy_eq using hcge hcsum hcvx hcvy by (by5000 auto)
qed

lemma polygonal_region_compact:
  assumes "top1_is_polygonal_region_on P n" and "n \<ge> 3"
  shows "top1_compact_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P)"
proof -
  \<comment> \<open>P is the convex hull of finitely many points, hence compact.
     Proved by inductive hull construction (Pk k compact for all k).\<close>
  have "compact P"
  proof -
    from assms(1)[unfolded top1_is_polygonal_region_on_def]
    obtain vx vy where
      hP: "P = {(x, y) | x y. \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0) \<and> (\<Sum>i<n. coeffs i) = 1
            \<and> x = (\<Sum>i<n. coeffs i * vx i) \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
      by (elim conjE exE) (rule that, assumption+)
    \<comment> \<open>Inductive hull construction: Pk k = convex hull of first k vertices.\<close>
    define Pk where "Pk k = {(x, y) | x y. \<exists>coeffs. (\<forall>i<k. coeffs i \<ge> 0)
        \<and> (\<Sum>i<k. coeffs i) = 1 \<and> x = (\<Sum>i<k. coeffs i * vx i)
        \<and> y = (\<Sum>i<k. coeffs i * vy i)}" for k :: nat
    have hPk_compact: "n \<ge> 1 \<Longrightarrow> compact (Pk n)"
    proof (rule nat_induct_at_least[of 1 n "\<lambda>k. compact (Pk k)"])
      show "1 \<le> n" using assms(2) by (by100 simp)
    next
      \<comment> \<open>Base: Pk 1 = {(vx 0, vy 0)}, compact as singleton.\<close>
      show "compact (Pk 1)"
      proof -
        have "Pk 1 = {(vx 0, vy 0)}"
        proof (rule set_eqI)
          fix p :: "real \<times> real"
          show "p \<in> Pk 1 \<longleftrightarrow> p \<in> {(vx 0, vy 0)}"
          proof
            assume "p \<in> Pk 1"
            then obtain x y coeffs where hp: "p = (x, y)"
                and hcge: "\<forall>i<(1::nat). coeffs i \<ge> 0" and hcsum: "(\<Sum>i<1. coeffs i) = 1"
                and hx: "x = (\<Sum>i<1. coeffs i * vx i)" and hy: "y = (\<Sum>i<1. coeffs i * vy i)"
              unfolding Pk_def by (by5000 auto)
            have "coeffs 0 = 1" using hcsum by (by100 simp)
            hence "x = vx 0" "y = vy 0" using hx hy by (by100 simp)+
            thus "p \<in> {(vx 0, vy 0)}" using hp by (by100 simp)
          next
            assume "p \<in> {(vx 0, vy 0)}"
            hence hp: "p = (vx 0, vy 0)" by (by100 simp)
            have "(vx 0, vy 0) \<in> Pk 1" unfolding Pk_def
              using exI[of _ "\<lambda>_::nat. 1::real"] by (by5000 auto)
            thus "p \<in> Pk 1" using hp by (by100 simp)
          qed
        qed
        thus ?thesis using compact_singleton by (by100 simp)
      qed
    next
      \<comment> \<open>Step: Pk (Suc k) = continuous image of Pk k × [0,1], hence compact.\<close>
      fix k assume "1 \<le> k" "compact (Pk k)"
      have hdom_compact: "compact (Pk k \<times> {0..1::real})"
        by (rule compact_Times_general[OF \<open>compact (Pk k)\<close> compact_Icc])
      have hset: "Pk (Suc k) = (\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))
          ` (Pk k \<times> {0..1})"
      proof (rule equalityI)
        \<comment> \<open>(\<subseteq>): element of Pk(Suc k) is a convex combo with k+1 vertices;
           let t = c_k, normalize remaining c_i by (1-t) to get point in Pk k.\<close>
        show "Pk (Suc k) \<subseteq> (\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))
            ` (Pk k \<times> {0..1})"
        proof (rule subsetI)
          fix q assume "q \<in> Pk (Suc k)"
          then obtain qx qy c where hq: "q = (qx, qy)"
              and hcge: "\<forall>i<Suc k. c i \<ge> 0" and hcsum: "(\<Sum>i<Suc k. c i) = 1"
              and hqx: "qx = (\<Sum>i<Suc k. c i * vx i)" and hqy: "qy = (\<Sum>i<Suc k. c i * vy i)"
            unfolding Pk_def by (by5000 auto)
          let ?t = "c k"
          have ht_ge: "?t \<ge> 0" using hcge by (by100 simp)
          have hrest: "(\<Sum>i<k. c i) = 1 - ?t" using hcsum by (by100 simp)
          have ht_le: "?t \<le> 1"
          proof -
            have "(\<Sum>i<k. c i) \<ge> 0"
              using hcge by (intro sum_nonneg) (by100 simp)
            thus ?thesis using hrest by (by100 linarith)
          qed
          show "q \<in> (\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))
              ` (Pk k \<times> {0..1})"
          proof (cases "?t = 1")
            case True
            \<comment> \<open>All other c_i = 0, q = (vx k, vy k).\<close>
            have hrest0: "(\<Sum>i<k. c i) = 0" using hrest True by (by100 simp)
            have hci0: "\<And>i. i < k \<Longrightarrow> c i = 0"
            proof -
              fix i assume "i < k"
              have "c i \<ge> 0" using hcge \<open>i < k\<close> by (by100 simp)
              moreover have "c i \<le> (\<Sum>i<k. c i)"
                using hcge \<open>i < k\<close> by (intro member_le_sum) (by100 auto)
              ultimately show "c i = 0" using hrest0 by (by100 simp)
            qed
            have "qx = vx k" using hqx hci0 True by (by100 simp)
            moreover have "qy = vy k" using hqy hci0 True by (by100 simp)
            ultimately have hq_vk: "q = (vx k, vy k)" using hq by (by100 simp)
            \<comment> \<open>v_0 \<in> Pk k (since k \<ge> 1).\<close>
            have hv0: "(vx 0, vy 0) \<in> Pk k"
            proof -
              define c0 where "c0 = (\<lambda>i::nat. if i = 0 then (1::real) else 0)"
              have hc0ge: "\<forall>i<k. c0 i \<ge> 0" unfolding c0_def by (by100 simp)
              have hc0_eq: "\<And>f. (\<Sum>i<k. c0 i * f i) = f 0"
              proof -
                fix f :: "nat \<Rightarrow> real"
                from \<open>1 \<le> k\<close> obtain k' where hk': "k = Suc k'" by (cases k) (by100 auto)
                have "(\<Sum>i<k. c0 i * f i) = (\<Sum>i<Suc k'. c0 i * f i)" unfolding hk' ..
                also have "\<dots> = c0 0 * f 0 + (\<Sum>i<k'. c0 (Suc i) * f (Suc i))"
                  using sum.lessThan_Suc_shift[of "\<lambda>i. c0 i * f i" k'] by (by100 simp)
                also have "(\<Sum>i<k'. c0 (Suc i) * f (Suc i)) = 0"
                  unfolding c0_def by (by100 simp)
                finally show "(\<Sum>i<k. c0 i * f i) = f 0" unfolding c0_def by (by100 simp)
              qed
              have hc0sum: "(\<Sum>i<k. c0 i) = 1"
              proof -
                have "(\<Sum>i<k. c0 i) = (\<Sum>i<k. c0 i * 1)" by (by100 simp)
                also have "\<dots> = 1" using hc0_eq[of "\<lambda>_. 1"] by (by100 simp)
                finally show ?thesis .
              qed
              have hc0x: "(\<Sum>i<k. c0 i * vx i) = vx 0" by (rule hc0_eq)
              have hc0y: "(\<Sum>i<k. c0 i * vy i) = vy 0" by (rule hc0_eq)
              show ?thesis unfolding Pk_def using hc0ge hc0sum hc0x hc0y by (by5000 auto)
            qed
            have "q = ((1 - 1) * fst (vx 0, vy 0) + 1 * vx k,
                       (1 - 1) * snd (vx 0, vy 0) + 1 * vy k)"
              unfolding hq_vk by (by100 simp)
            hence "q = (case ((vx 0, vy 0), 1::real) of (p, t) \<Rightarrow>
                ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))"
              by (by100 simp)
            moreover have "((vx 0, vy 0), 1::real) \<in> Pk k \<times> {0..1}" using hv0 by (by100 simp)
            ultimately show ?thesis by (by100 blast)
          next
            case False
            hence hlt: "?t < 1" using ht_le by (by100 simp)
            hence h1t_pos: "1 - ?t > 0" by (by100 simp)
            \<comment> \<open>Normalize: c'_i = c_i / (1-t).\<close>
            define c' where "c' i = c i / (1 - ?t)" for i
            have hc'ge: "\<forall>i<k. c' i \<ge> 0" using hcge h1t_pos unfolding c'_def by (by100 simp)
            have hc'sum: "(\<Sum>i<k. c' i) = 1"
              using hrest h1t_pos unfolding c'_def
              using sum_divide_distrib[of c "{..<k}" "1 - ?t"] by (by100 simp)
            define px where "px = (\<Sum>i<k. c' i * vx i)"
            define py where "py = (\<Sum>i<k. c' i * vy i)"
            have hp_in: "(px, py) \<in> Pk k" unfolding Pk_def
              using hc'ge hc'sum unfolding px_def py_def by (by5000 auto)
            \<comment> \<open>Show q = (1-t)*p + t*v_k.\<close>
            have "(\<Sum>i<k. c i * vx i) = (1 - ?t) * px"
            proof -
              have "(1 - ?t) * px = (1 - ?t) * (\<Sum>i<k. c' i * vx i)" unfolding px_def ..
              also have "\<dots> = (\<Sum>i<k. (1 - ?t) * (c' i * vx i))"
                using sum_distrib_left[of "1-?t" "\<lambda>i. c' i * vx i" "{..<k}", symmetric]
                by (by100 simp)
              also have "\<dots> = (\<Sum>i<k. c i * vx i)"
              proof (rule sum.cong)
                fix i assume "i \<in> {..<k}"
                show "(1 - ?t) * (c' i * vx i) = c i * vx i"
                  unfolding c'_def using h1t_pos by (by100 simp)
              qed (by100 simp)
              finally show ?thesis by (by100 simp)
            qed
            hence hqx_eq: "qx = (1 - ?t) * px + ?t * vx k"
              using hqx by (by100 simp)
            have "(\<Sum>i<k. c i * vy i) = (1 - ?t) * py"
            proof -
              have "(1 - ?t) * py = (1 - ?t) * (\<Sum>i<k. c' i * vy i)" unfolding py_def ..
              also have "\<dots> = (\<Sum>i<k. (1 - ?t) * (c' i * vy i))"
                using sum_distrib_left[of "1-?t" "\<lambda>i. c' i * vy i" "{..<k}", symmetric]
                by (by100 simp)
              also have "\<dots> = (\<Sum>i<k. c i * vy i)"
              proof (rule sum.cong)
                fix i assume "i \<in> {..<k}"
                show "(1 - ?t) * (c' i * vy i) = c i * vy i"
                  unfolding c'_def using h1t_pos by (by100 simp)
              qed (by100 simp)
              finally show ?thesis by (by100 simp)
            qed
            hence hqy_eq: "qy = (1 - ?t) * py + ?t * vy k"
              using hqy by (by100 simp)
            have "q = ((1 - ?t) * fst (px, py) + ?t * vx k,
                       (1 - ?t) * snd (px, py) + ?t * vy k)"
              using hq hqx_eq hqy_eq by (by100 simp)
            hence "q = (case ((px, py), ?t) of (p, t) \<Rightarrow>
                ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))"
              by (by100 simp)
            moreover have "((px, py), ?t) \<in> Pk k \<times> {0..1}" using hp_in ht_ge ht_le by (by100 simp)
            ultimately show ?thesis by (by100 blast)
          qed
        qed
        \<comment> \<open>(\<supseteq>): given p \<in> Pk k with coeffs d_i, and t \<in> [0,1],
           define c_i = (1-t)*d_i for i<k, c_k = t. Then \<Sum> c_i = 1.\<close>
        show "(\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))
            ` (Pk k \<times> {0..1}) \<subseteq> Pk (Suc k)"
        proof (rule subsetI)
          fix q assume "q \<in> (\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))
              ` (Pk k \<times> {0..1})"
          then obtain pt where hpt_in: "pt \<in> Pk k \<times> {0..1::real}"
              and hq: "q = (case pt of (p, t) \<Rightarrow> ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))"
            by (by100 blast)
          obtain p t where hpt: "pt = (p, t)" by (cases pt) (by100 blast)
          have hp: "p \<in> Pk k" and ht: "t \<in> {0..1::real}" using hpt_in hpt by (by100 blast)+
          have hq2: "q = ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k)"
            using hq hpt by (by100 simp)
          from hp obtain px py d where hpp: "p = (px, py)"
              and hdge: "\<forall>i<k. d i \<ge> 0" and hdsum: "(\<Sum>i<k. d i) = 1"
              and hpx: "px = (\<Sum>i<k. d i * vx i)" and hpy: "py = (\<Sum>i<k. d i * vy i)"
            unfolding Pk_def by (by5000 auto)
          define c where "c i = (if i < k then (1-t) * d i else if i = k then t else 0)" for i
          have ht01: "0 \<le> t" "t \<le> 1" using ht by (by100 auto)+
          have hcge: "\<forall>i<Suc k. c i \<ge> 0"
          proof (intro allI impI)
            fix i assume "i < Suc k"
            show "c i \<ge> 0"
            proof (cases "i < k")
              case True thus ?thesis unfolding c_def using ht01 hdge by (by100 auto)
            next
              case False hence "i = k" using \<open>i < Suc k\<close> by (by100 simp)
              thus ?thesis unfolding c_def using ht01 by (by100 simp)
            qed
          qed
          have hcsum: "(\<Sum>i<Suc k. c i) = 1"
          proof -
            have "(\<Sum>i<Suc k. c i) = (\<Sum>i<k. c i) + c k" by (by100 simp)
            also have "(\<Sum>i<k. c i) = (\<Sum>i<k. (1 - t) * d i)" unfolding c_def by (by100 simp)
            also have "\<dots> = (1 - t) * (\<Sum>i<k. d i)"
              using sum_distrib_left[of "1-t" d "{..<k}", symmetric] by (by100 simp)
            also have "\<dots> = 1 - t" using hdsum by (by100 simp)
            finally show ?thesis unfolding c_def by (by100 simp)
          qed
          have hqx: "fst q = (\<Sum>i<Suc k. c i * vx i)"
          proof -
            have "fst q = (1-t) * px + t * vx k" using hq2 hpp by (by100 simp)
            also have "\<dots> = (1-t) * (\<Sum>i<k. d i * vx i) + t * vx k" unfolding hpx ..
            also have "(1-t) * (\<Sum>i<k. d i * vx i) = (\<Sum>i<k. (1-t) * (d i * vx i))"
              using sum_distrib_left[of "1-t" "\<lambda>i. d i * vx i" "{..<k}", symmetric]
              by (by100 simp)
            also have "\<dots> = (\<Sum>i<k. c i * vx i)" unfolding c_def
              by (rule sum.cong) (by100 simp)+
            finally show ?thesis unfolding c_def by (by100 simp)
          qed
          have hqy: "snd q = (\<Sum>i<Suc k. c i * vy i)"
          proof -
            have "snd q = (1-t) * py + t * vy k" using hq2 hpp by (by100 simp)
            also have "\<dots> = (1-t) * (\<Sum>i<k. d i * vy i) + t * vy k" unfolding hpy ..
            also have "(1-t) * (\<Sum>i<k. d i * vy i) = (\<Sum>i<k. (1-t) * (d i * vy i))"
              using sum_distrib_left[of "1-t" "\<lambda>i. d i * vy i" "{..<k}", symmetric]
              by (by100 simp)
            also have "\<dots> = (\<Sum>i<k. c i * vy i)" unfolding c_def
              by (rule sum.cong) (by100 simp)+
            finally show ?thesis unfolding c_def by (by100 simp)
          qed
          obtain qx qy where hqq: "q = (qx, qy)" by (cases q) (by100 blast)
          have "qx = (\<Sum>i<Suc k. c i * vx i)" using hqx hqq by (by100 simp)
          moreover have "qy = (\<Sum>i<Suc k. c i * vy i)" using hqy hqq by (by100 simp)
          moreover note hcge hcsum
          ultimately show "q \<in> Pk (Suc k)" unfolding Pk_def hqq
            by (by5000 auto)
        qed
      qed
      have hcont: "continuous_on (Pk k \<times> {0..1})
          (\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))"
      proof -
        have hcont_eq: "(\<lambda>(p, t). ((1-t) * fst p + t * vx k, (1-t) * snd p + t * vy k))
            = (\<lambda>pt. ((1 - snd pt) * fst (fst pt) + snd pt * vx k,
                      (1 - snd pt) * snd (fst pt) + snd pt * vy k))"
          by (by100 auto)
        show ?thesis unfolding hcont_eq
          by (intro continuous_on_Pair continuous_on_add continuous_on_mult
              continuous_on_fst continuous_on_snd continuous_on_const
              continuous_on_diff) (by100 auto)+
      qed
      show "compact (Pk (Suc k))"
        unfolding hset by (rule compact_continuous_image[OF hcont hdom_compact])
    qed
    have "Pk n = P" unfolding Pk_def hP by (by100 simp)
    have "n \<ge> 1" using assms(2) by (by100 simp)
    hence "compact P" using hPk_compact \<open>Pk n = P\<close> by (by100 simp)
    thus ?thesis .
  qed
  thus ?thesis by (rule compact_R2_bridge)
qed



text \<open>Helper: psi\_local agreement on cone overlaps.
  Given equal total Cramer weight s and one of four adjacency cases,
  the angle-based psi maps agree.\<close>
lemma psi_angle_cases_agree:
  fixes s bi gi bj gj :: real and i j n :: nat
  assumes hn: "n > 0" and hi: "i < n" and hj: "j < n"
      and hs: "bi + gi = s" and hsj: "bj + gj = s"
      and hcase: "s = 0
        \<or> (i = j \<and> gi = gj)
        \<or> (Suc i mod n = j \<and> bi = 0 \<and> gj = 0)
        \<or> (Suc j mod n = i \<and> gi = 0 \<and> bj = 0)"
  shows "(let ui = (if s = 0 then 0 else gi / s);
              \<theta>i = 2 * pi * (real i + ui) / real n
          in (s * cos \<theta>i, s * sin \<theta>i))
       = (let uj = (if s = 0 then 0 else gj / s);
              \<theta>j = 2 * pi * (real j + uj) / real n
          in (s * cos \<theta>j, s * sin \<theta>j))"
proof -
  define ui where "ui = (if s = 0 then 0 else gi / s)"
  define uj where "uj = (if s = 0 then 0 else gj / s)"
  define \<theta>i where "\<theta>i = 2 * pi * (real i + ui) / real n"
  define \<theta>j where "\<theta>j = 2 * pi * (real j + uj) / real n"
  have hgoal: "s * cos \<theta>i = s * cos \<theta>j \<and> s * sin \<theta>i = s * sin \<theta>j"
  proof -
    from hcase show ?thesis
    proof (elim disjE)
      assume "s = 0"
      thus ?thesis by (by100 simp)
    next
      assume hij: "i = j \<and> gi = gj"
      hence "ui = uj" unfolding ui_def uj_def by (by100 simp)
      hence "\<theta>i = \<theta>j" unfolding \<theta>i_def \<theta>j_def using hij by (by100 simp)
      thus ?thesis by (by100 simp)
    next
      assume hadj1: "Suc i mod n = j \<and> bi = 0 \<and> gj = 0"
      hence hbi0: "bi = 0" and hgj0: "gj = 0" and hj_eq: "j = Suc i mod n" by (by100 blast)+
      have hgi_s: "gi = s" using hs hbi0 by (by100 linarith)
      have hbj_s: "bj = s" using hsj hgj0 by (by100 linarith)
      show ?thesis
      proof (cases "s = 0")
        case True thus ?thesis by (by100 simp)
      next
        case hsnz: False
        have hui: "ui = 1" unfolding ui_def using hsnz hgi_s by (by100 simp)
        have huj: "uj = 0" unfolding uj_def using hsnz hgj0 by (by100 simp)
        have h\<theta>i: "\<theta>i = 2 * pi * (real i + 1) / real n"
          unfolding \<theta>i_def using hui by (by100 simp)
        have h\<theta>j: "\<theta>j = 2 * pi * real j / real n"
          unfolding \<theta>j_def using huj by (by100 simp)
        \<comment> \<open>j = Suc i mod n. If Suc i < n then j = Suc i and \<theta>i = \<theta>j.
           If Suc i = n then j = 0 and \<theta>i = 2\<pi> and \<theta>j = 0, same mod 2\<pi>.\<close>
        have "\<theta>i = \<theta>j \<or> (\<theta>i - \<theta>j = 2 * pi \<or> \<theta>j - \<theta>i = 2 * pi)"
        proof (cases "Suc i < n")
          case True
          hence "Suc i mod n = Suc i" by (by100 simp)
          hence "j = Suc i" using hj_eq by (by100 simp)
          hence "\<theta>j = 2 * pi * real (Suc i) / real n" using h\<theta>j by (by100 simp)
          also have "\<dots> = 2 * pi * (real i + 1) / real n"
            by (by100 simp)
          finally show ?thesis using h\<theta>i by (by100 simp)
        next
          case False
          hence "Suc i \<ge> n" by (by100 linarith)
          hence hSi_n: "Suc i = n" using hi by (by100 linarith)
          hence "j = 0" using hj_eq by (by100 simp)
          hence h\<theta>j_val: "\<theta>j = 0" using h\<theta>j by (by100 simp)
          have hri: "real i + 1 = real n" using hSi_n by (by100 simp)
          have h\<theta>i_val: "\<theta>i = 2 * pi * real n / real n" unfolding h\<theta>i hri by (by100 simp)
          have h\<theta>i_2pi: "\<theta>i = 2 * pi" using h\<theta>i_val hn by (by100 simp)
          thus ?thesis using h\<theta>j_val by (by100 simp)
        qed
        thus ?thesis
        proof (elim disjE)
          assume "\<theta>i = \<theta>j" thus ?thesis by (by100 simp)
        next
          assume hd: "\<theta>i - \<theta>j = 2 * pi"
          hence heq: "\<theta>i = \<theta>j + 2 * pi" by (by100 linarith)
          have "cos \<theta>i = cos \<theta>j" using heq cos_periodic[of \<theta>j] by (by100 simp)
          moreover have "sin \<theta>i = sin \<theta>j" using heq sin_periodic[of \<theta>j] by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        next
          assume hd: "\<theta>j - \<theta>i = 2 * pi"
          hence heq: "\<theta>j = \<theta>i + 2 * pi" by (by100 linarith)
          have "cos \<theta>j = cos \<theta>i" using heq cos_periodic[of \<theta>i] by (by100 simp)
          moreover have "sin \<theta>j = sin \<theta>i" using heq sin_periodic[of \<theta>i] by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
      qed
    next
      assume hadj2: "Suc j mod n = i \<and> gi = 0 \<and> bj = 0"
      hence hgi0: "gi = 0" and hbj0: "bj = 0" and hi_eq: "i = Suc j mod n" by (by100 blast)+
      have hbi_s: "bi = s" using hs hgi0 by (by100 linarith)
      have hgj_s: "gj = s" using hsj hbj0 by (by100 linarith)
      show ?thesis
      proof (cases "s = 0")
        case True thus ?thesis by (by100 simp)
      next
        case hsnz: False
        have hui: "ui = 0" unfolding ui_def using hsnz hgi0 by (by100 simp)
        have huj: "uj = 1" unfolding uj_def using hsnz hgj_s by (by100 simp)
        have h\<theta>i: "\<theta>i = 2 * pi * real i / real n"
          unfolding \<theta>i_def using hui by (by100 simp)
        have h\<theta>j: "\<theta>j = 2 * pi * (real j + 1) / real n"
          unfolding \<theta>j_def using huj by (by100 simp)
        have "\<theta>i = \<theta>j \<or> (\<theta>i - \<theta>j = 2 * pi \<or> \<theta>j - \<theta>i = 2 * pi)"
        proof (cases "Suc j < n")
          case True
          hence "Suc j mod n = Suc j" by (by100 simp)
          hence "i = Suc j" using hi_eq by (by100 simp)
          hence "\<theta>i = 2 * pi * real (Suc j) / real n" using h\<theta>i by (by100 simp)
          also have "\<dots> = 2 * pi * (real j + 1) / real n"
            by (by100 simp)
          finally show ?thesis using h\<theta>j by (by100 simp)
        next
          case False
          hence "Suc j \<ge> n" by (by100 linarith)
          hence hSj_n: "Suc j = n" using hj by (by100 linarith)
          hence "i = 0" using hi_eq by (by100 simp)
          hence h\<theta>i_val: "\<theta>i = 0" using h\<theta>i by (by100 simp)
          have hrj: "real j + 1 = real n" using hSj_n by (by100 simp)
          have h\<theta>j_val: "\<theta>j = 2 * pi * real n / real n" unfolding h\<theta>j hrj by (by100 simp)
          have h\<theta>j_2pi: "\<theta>j = 2 * pi" using h\<theta>j_val hn by (by100 simp)
          thus ?thesis using h\<theta>i_val by (by100 simp)
        qed
        thus ?thesis
        proof (elim disjE)
          assume "\<theta>i = \<theta>j" thus ?thesis by (by100 simp)
        next
          assume hd: "\<theta>i - \<theta>j = 2 * pi"
          hence heq: "\<theta>i = \<theta>j + 2 * pi" by (by100 linarith)
          have "cos \<theta>i = cos \<theta>j" using heq cos_periodic[of \<theta>j] by (by100 simp)
          moreover have "sin \<theta>i = sin \<theta>j" using heq sin_periodic[of \<theta>j] by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        next
          assume hd: "\<theta>j - \<theta>i = 2 * pi"
          hence heq: "\<theta>j = \<theta>i + 2 * pi" by (by100 linarith)
          have "cos \<theta>j = cos \<theta>i" using heq cos_periodic[of \<theta>i] by (by100 simp)
          moreover have "sin \<theta>j = sin \<theta>i" using heq sin_periodic[of \<theta>i] by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
      qed
    qed
  qed
  have hcos: "s * cos \<theta>i = s * cos \<theta>j" using hgoal by (by100 simp)
  have hsin: "s * sin \<theta>i = s * sin \<theta>j" using hgoal by (by100 simp)
  show ?thesis unfolding Let_def ui_def[symmetric] uj_def[symmetric]
      \<theta>i_def[symmetric] \<theta>j_def[symmetric]
    using hcos hsin by (by100 simp)
qed

text \<open>Helper: if f is continuous on S-{c} and |fst(f z)|,|snd(f z)| \<le> g(z) where
  g is continuous, g(c)=0, and f(c)=(0,0), then f is continuous on S.\<close>
lemma continuous_on_squeeze_at_point:
  fixes f :: "'a::t1_space \<Rightarrow> real \<times> real" and g :: "'a \<Rightarrow> real"
  assumes hS: "c \<in> S"
      and hfc: "f c = (0, 0)"
      and hg_cont: "continuous_on S g"
      and hgc: "g c = 0"
      and hbound: "\<And>z. z \<in> S \<Longrightarrow> \<bar>fst (f z)\<bar> \<le> g z \<and> \<bar>snd (f z)\<bar> \<le> g z"
      and hg_nn: "\<And>z. z \<in> S \<Longrightarrow> g z \<ge> 0"
      and hcont_away: "continuous_on (S - {c}) f"
  shows "continuous_on S f"
proof (unfold continuous_on_def, intro ballI)
  fix z0 assume hz0: "z0 \<in> S"
  show "(f \<longlongrightarrow> f z0) (at z0 within S)"
  proof (cases "z0 = c")
    case False
    hence hz0': "z0 \<in> S - {c}" using hz0 by (by100 blast)
    from hcont_away[unfolded continuous_on_def, rule_format, OF hz0']
    have h_lim: "(f \<longlongrightarrow> f z0) (at z0 within S - {c})" .
    \<comment> \<open>at z0 within (S - {c}) = at z0 within S since z0 \<noteq> c.\<close>
    \<comment> \<open>Transfer: convergence within S-{c} implies within S (for z0\<noteq>c).\<close>
    show ?thesis
    proof (rule filterlim_mono_eventually)
      show "eventually (\<lambda>x. f x = f x) (at z0 within S)" by (by100 simp)
      show "at z0 within S \<le> at z0 within (S - {c})"
      proof (rule filter_leI)
        fix P assume hP: "eventually P (at z0 within (S - {c}))"
        from hP[unfolded eventually_at_filter]
        have hev: "eventually (\<lambda>x. x \<noteq> z0 \<longrightarrow> x \<in> S - {c} \<longrightarrow> P x) (nhds z0)" .
        \<comment> \<open>Eventually x \<noteq> c near z0 (T1 separation, or for R\<times>R: open complement of {c}).\<close>
        have hev_nc: "eventually (\<lambda>x. x \<noteq> c) (nhds z0)"
          using False t1_space_nhds by (by100 blast)
        have "eventually (\<lambda>x. (x \<noteq> z0 \<longrightarrow> x \<in> S - {c} \<longrightarrow> P x) \<and> x \<noteq> c) (nhds z0)"
          using eventually_conj[OF hev hev_nc] .
        hence "eventually (\<lambda>x. x \<noteq> z0 \<longrightarrow> x \<in> S \<longrightarrow> P x) (nhds z0)"
          by (rule eventually_mono) (by100 blast)
        thus "eventually P (at z0 within S)"
          unfolding eventually_at_filter .
      qed
      show "(f \<longlongrightarrow> f z0) (at z0 within (S - {c}))" using h_lim .
      show "nhds (f z0) \<le> nhds (f z0)" by (by100 simp)
    qed
  next
    case True
    hence hfz0: "f z0 = (0, 0)" using hfc by (by100 simp)
    \<comment> \<open>Need: f \<longlongrightarrow> (0,0) at c within S.\<close>
    \<comment> \<open>Equivalently: fst \<circ> f \<longlongrightarrow> 0 and snd \<circ> f \<longlongrightarrow> 0.\<close>
    \<comment> \<open>By squeeze: |fst(f z)| \<le> g z and g \<longlongrightarrow> g(c) = 0.\<close>
    \<comment> \<open>Squeeze: |fst(f z)| \<le> g z \<longrightarrow> 0 and |snd(f z)| \<le> g z \<longrightarrow> 0.
       So f z \<longrightarrow> (0,0).\<close>
    have hg_lim: "(g \<longlongrightarrow> 0) (at c within S)"
      using hg_cont[unfolded continuous_on_def, rule_format, OF hS] hgc by (by100 simp)
    \<comment> \<open>fst(f z) is squeezed between -g(z) and g(z), both tending to 0.\<close>
    \<comment> \<open>Squeeze: -g(z) \<le> fst(f z) \<le> g(z) and g \<longrightarrow> 0, -g \<longrightarrow> 0. So fst(f) \<longrightarrow> 0.\<close>
    have hng_lim: "((\<lambda>z. -g z) \<longlongrightarrow> 0) (at c within S)"
      using tendsto_minus[OF hg_lim] by (by100 simp)
    have hfst_lim: "((\<lambda>z. fst (f z)) \<longlongrightarrow> 0) (at c within S)"
    proof (rule real_tendsto_sandwich)
      show "eventually (\<lambda>z. - g z \<le> fst (f z)) (at c within S)"
        unfolding eventually_at_filter
        apply (rule eventually_mono[OF eventually_True[of "nhds c"]])
        using hbound hg_nn by (by100 force)
      show "eventually (\<lambda>z. fst (f z) \<le> g z) (at c within S)"
        unfolding eventually_at_filter
        apply (rule eventually_mono[OF eventually_True[of "nhds c"]])
        using hbound by (by100 force)
      show "((\<lambda>z. -g z) \<longlongrightarrow> 0) (at c within S)" using hng_lim .
      show "(g \<longlongrightarrow> 0) (at c within S)" using hg_lim .
    qed
    have hsnd_lim: "((\<lambda>z. snd (f z)) \<longlongrightarrow> 0) (at c within S)"
    proof (rule real_tendsto_sandwich)
      show "eventually (\<lambda>z. - g z \<le> snd (f z)) (at c within S)"
        unfolding eventually_at_filter
        apply (rule eventually_mono[OF eventually_True[of "nhds c"]])
        using hbound hg_nn by (by100 force)
      show "eventually (\<lambda>z. snd (f z) \<le> g z) (at c within S)"
        unfolding eventually_at_filter
        apply (rule eventually_mono[OF eventually_True[of "nhds c"]])
        using hbound by (by100 force)
      show "((\<lambda>z. -g z) \<longlongrightarrow> 0) (at c within S)" using hng_lim .
      show "(g \<longlongrightarrow> 0) (at c within S)" using hg_lim .
    qed
    \<comment> \<open>Combine component limits into pair limit.\<close>
    have "(f \<longlongrightarrow> (0, 0)) (at c within S)"
    proof -
      have "((\<lambda>z. (fst (f z), snd (f z))) \<longlongrightarrow> (0, 0)) (at c within S)"
        using tendsto_Pair[OF hfst_lim hsnd_lim] by (by100 simp)
      moreover have "(\<lambda>z. (fst (f z), snd (f z))) = f" by (rule ext) (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    thus ?thesis using hfz0 True by (by100 simp)
  qed
qed

text \<open>Strengthened polygon-to-disk: following the book (Munkres \<S>74) exactly.
  Uses radial projection from the centroid, not cone decomposition.
  Returns both the homeomorphism AND boundary correspondence.\<close>
lemma polygon_homeomorphic_to_disk_with_boundary:
  assumes "top1_is_polygonal_region_on P n" and "n \<ge> 3"
      and hverts_in: "\<forall>i<n. (vx i, vy i) \<in> P"
      and hP_hull: "P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<n. coeffs i) = 1
                       \<and> x = (\<Sum>i<n. coeffs i * vx i)
                       \<and> y = (\<Sum>i<n. coeffs i * vy i)}"
      and hccw: "\<forall>i<n. let cx = (\<Sum>j<n. vx j) / real n; cy = (\<Sum>j<n. vy j) / real n
         in (vx i - cx) * (vy (Suc i mod n) - cy) - (vy i - cy) * (vx (Suc i mod n) - cx) > 0"
      and hvert_hp: "\<forall>i<n. \<forall>k<n. cross2 (vx k - vx i, vy k - vy i)
          (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
      and hno_collinear: "\<forall>i<n. \<forall>j<n. j \<noteq> i \<longrightarrow> Suc i mod n \<noteq> j \<longrightarrow>
          cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<noteq> 0"
  shows "\<exists>\<psi>.
    top1_homeomorphism_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P)
        top1_B2 top1_B2_topology \<psi>
    \<and> \<psi> ` (\<Union>i<n. {((1-t) * vx i + t * vx (Suc i mod n),
                     (1-t) * vy i + t * vy (Suc i mod n)) | t. t \<in> I_set})
        = top1_S1
    \<and> top1_homeomorphism_on
        (P - (\<Union>i<n. {((1-t) * vx i + t * vx (Suc i mod n),
                       (1-t) * vy i + t * vy (Suc i mod n)) | t. t \<in> I_set}))
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
           (P - (\<Union>i<n. {((1-t) * vx i + t * vx (Suc i mod n),
                          (1-t) * vy i + t * vy (Suc i mod n)) | t. t \<in> I_set})))
        (top1_B2 - top1_S1)
        (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
        \<psi>
    \<comment> \<open>Edge-to-arc: \<psi> maps edge i at parameter t to angle 2\<pi>(i+t)/n on S1.\<close>
    \<and> (\<forall>i<n. \<forall>t\<in>I_set. \<psi> ((1-t) * vx i + t * vx (Suc i mod n),
                              (1-t) * vy i + t * vy (Suc i mod n))
        = (cos (2 * pi * (real i + t) / real n), sin (2 * pi * (real i + t) / real n)))"
proof -
  \<comment> \<open>Following Munkres \<S>74 paragraph before Theorem 74.2:
     "If two polygonal regions P and Q have the same number of vertices...
      then there is an obvious homeomorphism h of Bd P with Bd Q that carries
      the line segment from p_{i-1} to p_i by a positive linear map onto the
      line segment from q_{i-1} to q_i."
     "If p and q are fixed points of Int P and Int Q, respectively, then this
      homeomorphism may be extended to a homeomorphism of P with Q by letting
      it map the line segment from p to the point x of Bd P linearly onto
      the line segment from q to h(x)."\<close>
  \<comment> \<open>Step 1: Extract vertices from the polygonal region.\<close>
  have hn: "n \<ge> 3" using assms(2) .
  have hP_eq: "P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<n. coeffs i) = 1
                       \<and> x = (\<Sum>i<n. coeffs i * vx i)
                       \<and> y = (\<Sum>i<n. coeffs i * vy i)}" by (rule hP_hull)
  have hverts: "\<forall>i<n. (vx i, vy i) \<in> P" by (rule hverts_in)
  \<comment> \<open>Step 2: Define centroid c = (1/n) \<Sum> vertices as interior point.\<close>
  let ?cx = "(\<Sum>i<n. vx i) / real n"
  let ?cy = "(\<Sum>i<n. vy i) / real n"
  let ?c = "(?cx, ?cy)"
  have hc_in_P: "?c \<in> P"
  proof -
    define coeffs where "coeffs (i::nat) = (1 / real n :: real)" for i
    have "(\<forall>i<n. coeffs i \<ge> 0)" unfolding coeffs_def by (by100 simp)
    moreover have "(\<Sum>i<n. coeffs i) = 1"
      unfolding coeffs_def using hn by (by100 simp)
    moreover have "?cx = (\<Sum>i<n. coeffs i * vx i)"
      unfolding coeffs_def using hn by (simp add: sum_divide_distrib[symmetric])
    moreover have "?cy = (\<Sum>i<n. coeffs i * vy i)"
      unfolding coeffs_def using hn by (simp add: sum_divide_distrib[symmetric])
    ultimately show ?thesis unfolding hP_eq by (by100 blast)
  qed
  have hc_interior: "?c \<in> P - (\<Union>i<n. {((1-t) * vx i + t * vx (Suc i mod n),
      (1-t) * vy i + t * vy (Suc i mod n)) | t. t \<in> I_set})"
  proof -
    \<comment> \<open>From CCW: for each edge i, the centroid is not on the line through v_i, v_{i+1}.
       A point on edge i at parameter t is a convex combo of v_i and v_{i+1},
       hence on the line through them. Since centroid is NOT on that line, it's not on the edge.\<close>
    have "?c \<notin> (\<Union>i<n. {((1-t) * vx i + t * vx (Suc i mod n),
        (1-t) * vy i + t * vy (Suc i mod n)) | t. t \<in> I_set})"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain i t where hi: "i < n" and ht: "t \<in> I_set" and
        hpt: "?c = ((1-t) * vx i + t * vx (Suc i mod n), (1-t) * vy i + t * vy (Suc i mod n))"
        by (by5000 force)
      \<comment> \<open>The point (1-t)*v_i + t*v_{i+1} is on the line through v_i, v_{i+1}.
         So cross2(point - v_i, v_{i+1} - v_i) = 0. But also cross2(c - v_i, v_{i+1} - v_i) = 0.
         However, CCW says cross2(v_i - c, v_{i+1} - c) > 0, contradicting c on the edge line.\<close>
      have hcx_eq: "?cx = (1-t) * vx i + t * vx (Suc i mod n)" using hpt by (by100 simp)
      have hcy_eq: "?cy = (1-t) * vy i + t * vy (Suc i mod n)" using hpt by (by100 simp)
      \<comment> \<open>From hccw: (vx i - cx)*(vy_{i+1} - cy) - (vy i - cy)*(vx_{i+1} - cx) > 0.\<close>
      from hccw[rule_format, OF hi]
      have hD_pos: "(vx i - ?cx) * (vy (Suc i mod n) - ?cy)
          - (vy i - ?cy) * (vx (Suc i mod n) - ?cx) > 0"
        by (by100 simp)
      \<comment> \<open>But substituting c on the edge line: vx i - cx = (1-t)*(vx i - vx i) + t*(vx i - v_{i+1})...\<close>
      have "vx i - ?cx = - t * (vx (Suc i mod n) - vx i)" using hcx_eq by (simp add: algebra_simps)
      moreover have "vy i - ?cy = - t * (vy (Suc i mod n) - vy i)" using hcy_eq by (simp add: algebra_simps)
      moreover have "vx (Suc i mod n) - ?cx = (1 - t) * (vx (Suc i mod n) - vx i)"
        using hcx_eq by (simp add: algebra_simps)
      moreover have "vy (Suc i mod n) - ?cy = (1 - t) * (vy (Suc i mod n) - vy i)"
        using hcy_eq by (simp add: algebra_simps)
      ultimately have "(vx i - ?cx) * (vy (Suc i mod n) - ?cy)
          - (vy i - ?cy) * (vx (Suc i mod n) - ?cx) =
          (-t) * (vx (Suc i mod n) - vx i) * ((1-t) * (vy (Suc i mod n) - vy i))
          - (-t) * (vy (Suc i mod n) - vy i) * ((1-t) * (vx (Suc i mod n) - vx i))"
        by (by100 simp)
      also have "\<dots> = 0" by (simp add: algebra_simps)
      finally show False using hD_pos by (by100 linarith)
    qed
    thus ?thesis using hc_in_P by (by100 blast)
  qed
  \<comment> \<open>Step 3: Define boundary map h: Bd P \<rightarrow> S1 by positive linear maps on edges.
     Take Q = regular n-gon inscribed in S1, with vertices q_i = (cos(2\<pi>i/n), sin(2\<pi>i/n)).
     Map edge [v_i, v_{i+1}] linearly to arc [q_i, q_{i+1}] on S1.\<close>
  \<comment> \<open>Step 4: Define \<psi> by radial extension.
     For z \<in> P: find unique x \<in> Bd P and t \<in> [0,1] with z = (1-t)\<cdot>c + t\<cdot>x.
     Then \<psi>(z) = t \<cdot> h(x). For z = c: \<psi>(c) = (0,0).
     This is a continuous bijection from compact P to Hausdorff B2.\<close>
  \<comment> \<open>Step 5: Apply Theorem 26.6 (continuous bijection compact \<rightarrow> Hausdorff = homeomorphism).\<close>
  \<comment> \<open>Step 6: By construction \<psi>(Bd P) = S1 and \<psi>(Int P) = Int B2.\<close>
  \<comment> \<open>Following Munkres \<S>74: cone decomposition homeomorphism P \<rightarrow> B2.
     For z \<in> P in cone i (triangle c, v_i, v_{i+1}):
       Cramer coordinates \<beta>' = cross2(z-c, v_{i+1}-c)/D_i, \<gamma>' = cross2(v_i-c, z-c)/D_i
       w = \<beta>'*q_i + \<gamma>'*q_{i+1}, r = |w|
       \<psi>(z) = (\<beta>'+\<gamma>') * w/r  (normalized cone map)
     This maps each cone to a sector of B2 and pastes to a homeomorphism P \<rightarrow> B2.\<close>
  let ?BdP = "\<Union>i<n. {((1-t) * vx i + t * vx (Suc i mod n),
                       (1-t) * vy i + t * vy (Suc i mod n)) | t. t \<in> I_set}"
  let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
  \<comment> \<open>Target regular n-gon vertices on S1.\<close>
  define qx where "qx i = cos (2 * pi * real i / real n)" for i :: nat
  define qy where "qy i = sin (2 * pi * real i / real n)" for i :: nat
  have "\<exists>\<psi>. top1_homeomorphism_on P ?TP top1_B2 top1_B2_topology \<psi>
      \<and> \<psi> ` ?BdP = top1_S1
      \<and> top1_homeomorphism_on (P - ?BdP)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (P - ?BdP))
          (top1_B2 - top1_S1)
          (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1)) \<psi>
      \<and> (\<forall>i<n. \<forall>t\<in>I_set. \<psi> ((1-t) * vx i + t * vx (Suc i mod n),
                                (1-t) * vy i + t * vy (Suc i mod n))
          = (cos (2 * pi * (real i + t) / real n), sin (2 * pi * (real i + t) / real n)))"
  proof -
    \<comment> \<open>Centroid abbreviations.\<close>
    define cx where "cx = (\<Sum>j<n. vx j) / real n"
    define cy where "cy = (\<Sum>j<n. vy j) / real n"
    have hcx_eq: "cx = ?cx" unfolding cx_def by (by100 simp)
    have hcy_eq: "cy = ?cy" unfolding cy_def by (by100 simp)
    have hc_eq: "(cx, cy) = ?c" using hcx_eq hcy_eq by (by100 simp)
    \<comment> \<open>D_i = cross2(v_i - c, v_{i+1} - c) > 0 from CCW.\<close>
    define Di where "Di i = (vx i - cx) * (vy (Suc i mod n) - cy)
        - (vy i - cy) * (vx (Suc i mod n) - cx)" for i :: nat
    have hDi_pos: "\<And>i. i < n \<Longrightarrow> Di i > 0"
    proof -
      fix i assume "i < n"
      from hccw[rule_format, OF this]
      show "Di i > 0" unfolding Di_def cx_def cy_def by (by100 simp)
    qed
    \<comment> \<open>Cramer coordinates.\<close>
    define beta_cr where "beta_cr i z = cross2 (fst z - cx, snd z - cy)
        (vx (Suc i mod n) - cx, vy (Suc i mod n) - cy) / Di i" for i :: nat and z :: "real \<times> real"
    define gamma_cr where "gamma_cr i z = cross2 (vx i - cx, vy i - cy)
        (fst z - cx, snd z - cy) / Di i" for i :: nat and z :: "real \<times> real"
    \<comment> \<open>Cone membership: \<beta> \<ge> 0, \<gamma> \<ge> 0, \<beta>+\<gamma> \<le> 1.\<close>
    define in_cone where "in_cone i z \<longleftrightarrow>
        beta_cr i z \<ge> 0 \<and> gamma_cr i z \<ge> 0 \<and> beta_cr i z + gamma_cr i z \<le> 1"
        for i :: nat and z :: "real \<times> real"
    \<comment> \<open>Local cone map (angle-based: avoids sqrt normalization).\<close>
    define psi_local where "psi_local i z = (
        let b = beta_cr i z; g = gamma_cr i z;
            s = b + g;
            u = (if s = 0 then 0 else g / s);
            \<theta> = 2 * pi * (real i + u) / real n
        in (s * cos \<theta>, s * sin \<theta>))" for i :: nat and z :: "real \<times> real"
    \<comment> \<open>Key Cramer property: z - c = \<beta>'*(v_i - c) + \<gamma>'*(v_{i+1} - c).\<close>
    have hCramer_x: "\<And>i z. Di i \<noteq> 0 \<Longrightarrow>
        fst z - cx = beta_cr i z * (vx i - cx) + gamma_cr i z * (vx (Suc i mod n) - cx)"
    proof -
      fix i :: nat and z :: "real \<times> real"
      assume hDne: "Di i \<noteq> 0"
      have "beta_cr i z * (vx i - cx) + gamma_cr i z * (vx (Suc i mod n) - cx) =
          (cross2 (fst z - cx, snd z - cy) (vx (Suc i mod n) - cx, vy (Suc i mod n) - cy) * (vx i - cx) +
           cross2 (vx i - cx, vy i - cy) (fst z - cx, snd z - cy) * (vx (Suc i mod n) - cx)) / Di i"
        unfolding beta_cr_def gamma_cr_def by (simp add: add_divide_distrib)
      also have "\<dots> = (fst z - cx) * Di i / Di i"
        unfolding cross2_def Di_def by (simp add: algebra_simps)
      also have "\<dots> = fst z - cx" using hDne by (by100 simp)
      finally show "fst z - cx = beta_cr i z * (vx i - cx) + gamma_cr i z * (vx (Suc i mod n) - cx)"
        by (by100 simp)
    qed
    have hCramer_y: "\<And>i z. Di i \<noteq> 0 \<Longrightarrow>
        snd z - cy = beta_cr i z * (vy i - cy) + gamma_cr i z * (vy (Suc i mod n) - cy)"
    proof -
      fix i :: nat and z :: "real \<times> real"
      assume hDne: "Di i \<noteq> 0"
      have "beta_cr i z * (vy i - cy) + gamma_cr i z * (vy (Suc i mod n) - cy) =
          (cross2 (fst z - cx, snd z - cy) (vx (Suc i mod n) - cx, vy (Suc i mod n) - cy) * (vy i - cy) +
           cross2 (vx i - cx, vy i - cy) (fst z - cx, snd z - cy) * (vy (Suc i mod n) - cy)) / Di i"
        unfolding beta_cr_def gamma_cr_def by (simp add: add_divide_distrib)
      also have "\<dots> = (snd z - cy) * Di i / Di i"
        unfolding cross2_def Di_def by (simp add: algebra_simps)
      also have "\<dots> = snd z - cy" using hDne by (by100 simp)
      finally show "snd z - cy = beta_cr i z * (vy i - cy) + gamma_cr i z * (vy (Suc i mod n) - cy)"
        by (by100 simp)
    qed
    \<comment> \<open>Centroid maps to origin.\<close>
    have hpsi_local_c: "\<And>i. psi_local i (cx, cy) = (0, 0)"
    proof -
      fix i :: nat
      have "beta_cr i (cx, cy) = 0" unfolding beta_cr_def cross2_def by (by100 simp)
      moreover have "gamma_cr i (cx, cy) = 0" unfolding gamma_cr_def cross2_def by (by100 simp)
      ultimately show "psi_local i (cx, cy) = (0, 0)" unfolding psi_local_def by (by100 simp)
    qed
    \<comment> \<open>Cone decomposition: every z \<in> P is in some cone.
       Uses cross2_centroid_sum_zero + cyclic_strict_sign_change for sector finding,
       Cramer's rule for barycentric coordinates, and CCW + convexity for \<beta>'+\<gamma>' \<le> 1.\<close>
    \<comment> \<open>Helper: Di = cross2(v_i-c, v_{i+1}-c) = cross2(v_i-c, v_{i+1}-v_i).\<close>
    have hDi_eq: "\<And>i. Di i = cross2 (vx i - cx, vy i - cy) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)"
      unfolding Di_def cross2_def by (simp add: algebra_simps)
    \<comment> \<open>Helper: beta_cr i z = -cross2(v_{i+1}-c, z-c) / Di i (antisymmetry).\<close>
    have hbeta_antisym: "\<And>i z. beta_cr i z =
        - cross2 (vx (Suc i mod n) - cx, vy (Suc i mod n) - cy) (fst z - cx, snd z - cy) / Di i"
      unfolding beta_cr_def cross2_def by (simp add: algebra_simps)
    \<comment> \<open>Helper: beta_cr + gamma_cr = cross2(z-c, v_{i+1}-v_i) / Di.\<close>
    have hbg_sum: "\<And>i z. i < n \<Longrightarrow>
        beta_cr i z + gamma_cr i z =
        cross2 (fst z - cx, snd z - cy) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) / Di i"
    proof -
      fix i :: nat and z :: "real \<times> real"
      assume hi: "i < n"
      have "beta_cr i z + gamma_cr i z =
          (cross2 (fst z - cx, snd z - cy) (vx (Suc i mod n) - cx, vy (Suc i mod n) - cy) +
           cross2 (vx i - cx, vy i - cy) (fst z - cx, snd z - cy)) / Di i"
        unfolding beta_cr_def gamma_cr_def by (simp add: add_divide_distrib)
      also have "\<dots> = cross2 (fst z - cx, snd z - cy)
          (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) / Di i"
        unfolding cross2_def by (simp add: algebra_simps)
      finally show "beta_cr i z + gamma_cr i z =
          cross2 (fst z - cx, snd z - cy)
              (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) / Di i" .
    qed
    \<comment> \<open>Helper: for z \<in> P, beta_cr + gamma_cr \<le> 1 for each cone i.\<close>
    have hbg_le1: "\<And>i z. i < n \<Longrightarrow> z \<in> P \<Longrightarrow>
        beta_cr i z + gamma_cr i z \<le> 1"
    proof -
      fix i :: nat and z :: "real \<times> real"
      assume hi: "i < n" and hz: "z \<in> P"
      from hz obtain coeffs where hcge: "\<forall>j<n. coeffs j \<ge> 0"
          and hcsum: "(\<Sum>j<n. coeffs j) = 1"
          and hfst: "fst z = (\<Sum>j<n. coeffs j * vx j)"
          and hsnd: "snd z = (\<Sum>j<n. coeffs j * vy j)"
        unfolding hP_hull mem_Collect_eq by (by5000 auto)
      \<comment> \<open>beta_cr + gamma_cr = cross2(z-c, v_{i+1}-v_i) / Di.
         cross2(z-c, v_{i+1}-v_i) = cross2(z - v_i, v_{i+1}-v_i) + cross2(v_i - c, v_{i+1}-v_i).
         Since Di = cross2(v_i-c, v_{i+1}-v_i), we have:
         beta_cr + gamma_cr = (cross2(z-v_i, v_{i+1}-v_i) + Di) / Di
                            = cross2(z-v_i, v_{i+1}-v_i)/Di + 1.\<close>
      have hhp_i: "\<forall>k<n. cross2 (vx k - vx i, vy k - vy i)
          (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
        using hvert_hp hi by (by100 blast)
      have hcross_z: "cross2 (fst z - vx i, snd z - vy i)
          (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
        using ccw_polygon_half_plane[OF assms(2) hcge hcsum hfst hsnd hi hhp_i] .
      have "cross2 (fst z - cx, snd z - cy)
          (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) =
          cross2 (fst z - vx i, snd z - vy i)
              (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) +
          cross2 (vx i - cx, vy i - cy)
              (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)"
        unfolding cross2_def by (simp add: algebra_simps)
      also have "\<dots> \<le> 0 + Di i"
      proof -
        have "cross2 (fst z - vx i, snd z - vy i)
            (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
          using hcross_z .
        moreover have "cross2 (vx i - cx, vy i - cy)
            (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) = Di i"
          using hDi_eq by (by100 simp)
        ultimately show ?thesis by (by100 linarith)
      qed
      finally have hnum: "cross2 (fst z - cx, snd z - cy)
          (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> Di i"
        by (by100 linarith)
      have hDi_pos': "Di i > 0" using hDi_pos[OF hi] .
      show "beta_cr i z + gamma_cr i z \<le> 1"
        using hbg_sum[OF hi, of z] hnum hDi_pos'
        by (simp add: divide_le_eq)
    qed
    have hP_cones: "\<forall>z \<in> P. \<exists>i<n. in_cone i z"
    proof (rule ballI)
      fix z assume hz: "z \<in> P"
      show "\<exists>i<n. in_cone i z"
      proof (cases "z = (cx, cy)")
        case True
        have "in_cone 0 (cx, cy)"
          unfolding in_cone_def beta_cr_def gamma_cr_def cross2_def by (by100 simp)
        moreover have "(0::nat) < n" using hn by (by100 linarith)
        ultimately show ?thesis using True by (by100 blast)
      next
        case hne: False
        \<comment> \<open>z \<noteq> c. Define f(j) = cross2(v_j - c, z - c) and use sign change.\<close>
        define f where "f j = cross2 (vx j - cx, vy j - cy) (fst z - cx, snd z - cy)" for j :: nat
        have hf_sum: "(\<Sum>j<n. f j) = 0"
        proof -
          have "(\<Sum>j<n. f j) = (\<Sum>j<n. cross2 (vx j - cx, vy j - cy) (fst z - cx, snd z - cy))"
            unfolding f_def by (by100 simp)
          also have "\<dots> = 0"
          proof -
            have "(\<Sum>j<n. cross2 (vx j - cx, vy j - cy) (fst z - cx, snd z - cy)) =
                (\<Sum>j<n. cross2 (vx j - (\<Sum>i<n. vx i) / real n, vy j - (\<Sum>i<n. vy i) / real n)
                    (fst z - cx, snd z - cy))"
              unfolding cx_def cy_def by (by100 simp)
            also have "\<dots> = 0"
              using cross2_centroid_sum_zero[of n vx vy "fst z - cx" "snd z - cy"]
                assms(2) by (by100 linarith)
            finally show ?thesis .
          qed
          finally show ?thesis .
        qed
        \<comment> \<open>Need: \<exists>j<n. f j > 0. Since z \<noteq> c, d = z-c \<noteq> 0.
           Σ cross2(v_j-c, d) = 0. If all are 0, then all v_j-c are parallel to d,
           meaning all vertices are on a line through c in direction d.
           But D_0 > 0 means v_0, v_1, c are not collinear. So not all f(j) = 0.\<close>
        have hex_pos: "\<exists>j<n. f j > 0"
        proof (rule ccontr)
          assume hno: "\<not> (\<exists>j<n. f j > 0)"
          hence hall_le0: "\<forall>j<n. f j \<le> 0" by (by100 force)
          have hall_0: "\<forall>j<n. f j = 0"
          proof (intro allI impI)
            fix j assume hj: "j < n"
            have hle: "(\<Sum>k<n. f k) \<le> 0"
              using sum_nonpos[of "{..<n}" f] hall_le0 by (by100 force)
            hence "(\<Sum>k<n. f k) = 0" using hf_sum by (by100 simp)
            have hnn: "\<And>k. k \<in> {..<n} \<Longrightarrow> 0 \<le> - f k"
              using hall_le0 by (by100 force)
            have "(\<Sum>k<n. - f k) = - (\<Sum>k<n. f k)"
              using sum_negf by (by100 blast)
            hence "(\<Sum>k<n. - f k) = 0" using hf_sum by (by100 simp)
            from sum_nonneg_eq_0_iff[of "{..<n}" "\<lambda>k. - f k"] hnn this
            have "\<forall>k\<in>{..<n}. - f k = 0" by (by100 blast)
            thus "f j = 0" using hj by (by100 force)
          qed
          \<comment> \<open>f(0) = 0 and f(1) = 0 means cross2(v_0-c, d) = 0 and cross2(v_1-c, d) = 0.
             This means v_0-c and v_1-c are both parallel to d.
             So v_0-c = a*d and v_1-c = b*d for some a, b.
             Then D_0 = cross2(v_0-c, v_1-c) = cross2(a*d, b*d) = a*b*cross2(d,d) = 0.
             But D_0 > 0. Contradiction.\<close>
          have h0n: "(0::nat) < n" using hn by (by100 linarith)
          have hf0: "f 0 = 0" using hall_0 h0n by (by100 blast)
          have hf1: "f 1 = 0"
          proof -
            have "1 < n" using hn by (by100 linarith)
            thus ?thesis using hall_0 by (by100 blast)
          qed
          \<comment> \<open>From f(0) = 0: (vx 0 - cx)*(snd z - cy) = (vy 0 - cy)*(fst z - cx).\<close>
          have hpar0: "(vx 0 - cx) * (snd z - cy) = (vy 0 - cy) * (fst z - cx)"
            using hf0 unfolding f_def cross2_def by (by100 simp)
          \<comment> \<open>From f(1) = 0: (vx 1 - cx)*(snd z - cy) = (vy 1 - cy)*(fst z - cx).\<close>
          have hpar1: "(vx 1 - cx) * (snd z - cy) = (vy 1 - cy) * (fst z - cx)"
            using hf1 unfolding f_def cross2_def by (by100 simp)
          \<comment> \<open>D_0 = cross2(v_0-c, v_1-c) = (vx0-cx)*(vy1-cy) - (vy0-cy)*(vx1-cx).
             From hpar0 and hpar1, we can show D_0 = 0.\<close>
          have "Di 0 = 0"
          proof (cases "fst z - cx = 0 \<and> snd z - cy = 0")
            case True thus ?thesis using hne hcx_eq hcy_eq by (cases z) (by100 simp)
          next
            case False
            show ?thesis
            proof (cases "fst z - cx = 0")
              case True
              hence "snd z - cy \<noteq> 0" using False by (by100 blast)
              from hpar0 True have hvx0: "vx 0 - cx = 0"
                using \<open>snd z - cy \<noteq> 0\<close> by (by100 simp)
              from hpar1 True have hvx1: "vx 1 - cx = 0"
                using \<open>snd z - cy \<noteq> 0\<close> by (by100 simp)
              have "Suc 0 mod n = 1" using hn by (by100 simp)
              thus ?thesis unfolding Di_def using hvx0 hvx1 by (by100 simp)
            next
              case hfnz: False
              \<comment> \<open>fst z - cx \<noteq> 0. From hpar0: (vx 0 - cx) = (vy 0 - cy)*(fst z - cx)/(snd z - cy)
                 if snd z - cy \<noteq> 0, or vy 0 - cy = 0 if snd z - cy = 0.
                 In either case: Di 0 = 0.\<close>
              show ?thesis
              proof (cases "snd z - cy = 0")
                case True
                from hpar0 True hfnz have hvy0: "vy 0 - cy = 0" by (by100 simp)
                from hpar1 True hfnz have hvy1: "vy 1 - cy = 0" by (by100 simp)
                have "Suc 0 mod n = 1" using hn by (by100 simp)
                thus ?thesis unfolding Di_def using hvy0 hvy1 by (by100 simp)
              next
                case hsnz: False
                \<comment> \<open>Both components nonzero. vx_j - cx = (vy_j - cy) * (fst z - cx)/(snd z - cy).\<close>
                define r where "r = (fst z - cx) / (snd z - cy)"
                have hr: "vx 0 - cx = (vy 0 - cy) * r"
                proof -
                  have "(vx 0 - cx) * (snd z - cy) = (vy 0 - cy) * (fst z - cx)"
                    using hpar0 .
                  hence "vx 0 - cx = (vy 0 - cy) * (fst z - cx) / (snd z - cy)"
                    using hsnz by (simp add: field_simps)
                  thus ?thesis unfolding r_def by (by100 simp)
                qed
                have hr1: "vx 1 - cx = (vy 1 - cy) * r"
                proof -
                  have "(vx 1 - cx) * (snd z - cy) = (vy 1 - cy) * (fst z - cx)"
                    using hpar1 .
                  hence "vx 1 - cx = (vy 1 - cy) * (fst z - cx) / (snd z - cy)"
                    using hsnz by (simp add: field_simps)
                  thus ?thesis unfolding r_def by (by100 simp)
                qed
                have "Suc 0 mod n = 1" using hn by (by100 simp)
                hence "Di 0 = (vx 0 - cx) * (vy 1 - cy) - (vy 0 - cy) * (vx 1 - cx)"
                  unfolding Di_def by (by100 simp)
                also have "\<dots> = (vy 0 - cy) * r * (vy 1 - cy) - (vy 0 - cy) * ((vy 1 - cy) * r)"
                  using hr hr1 by (by100 simp)
                also have "\<dots> = 0" by (simp add: algebra_simps)
                finally show ?thesis .
              qed
            qed
          qed
          moreover have "Di 0 > 0" using hDi_pos[of 0] hn by (by100 linarith)
          ultimately show False by (by100 linarith)
        qed
        \<comment> \<open>Now apply cyclic_strict_sign_change.\<close>
        from cyclic_strict_sign_change[of n f] assms(2) hf_sum hex_pos
        obtain i where hi: "i < n" and hfi_pos: "f i > 0"
            and hfi1_le0: "f ((i+1) mod n) \<le> 0"
          by (by100 force)
        \<comment> \<open>gamma_cr i z = f(i) / Di i \<ge> 0.\<close>
        have hgamma: "gamma_cr i z \<ge> 0"
        proof -
          have "gamma_cr i z = f i / Di i"
            unfolding gamma_cr_def f_def by (by100 simp)
          moreover have "f i > 0" using hfi_pos .
          moreover have "Di i > 0" using hDi_pos[OF hi] .
          ultimately show ?thesis by (by100 simp)
        qed
        \<comment> \<open>beta_cr i z = -cross2(v_{i+1}-c, z-c) / Di = -f(i+1 mod n) / Di \<ge> 0.\<close>
        have hbeta: "beta_cr i z \<ge> 0"
        proof -
          have hSuc: "Suc i mod n = (i + 1) mod n" by (by100 simp)
          have hbval: "beta_cr i z = - f ((i+1) mod n) / Di i"
            unfolding hbeta_antisym f_def hSuc by (by100 simp)
          have hfle: "f ((i+1) mod n) / Di i \<le> 0"
          proof -
            have "f ((i+1) mod n) \<le> 0" using hfi1_le0 .
            moreover have "Di i > 0" using hDi_pos[OF hi] .
            ultimately show ?thesis
              using divide_nonpos_nonneg[of "f ((i+1) mod n)" "Di i"]
              by (by100 linarith)
          qed
          have "- f ((i+1) mod n) / Di i \<ge> 0" using hfle
            by (by100 linarith)
          thus ?thesis using hbval by (by100 linarith)
        qed
        have hbg: "beta_cr i z + gamma_cr i z \<le> 1"
          using hbg_le1[OF hi hz] .
        have "in_cone i z" unfolding in_cone_def using hbeta hgamma hbg by (by100 blast)
        thus ?thesis using hi by (by100 blast)
      qed
    qed
    \<comment> \<open>Local maps agree on cone overlaps.\<close>
    have hpsi_agree_centroid: "\<And>i j. psi_local i (cx, cy) = psi_local j (cx, cy)"
      using hpsi_local_c by (by100 simp)
    \<comment> \<open>Helper: cross2(z - v_i, v_{i+1} - v_i) in terms of Cramer coordinates.\<close>
    have hcross_z_vi: "\<And>i z. i < n \<Longrightarrow>
        cross2 (fst z - vx i, snd z - vy i)
            (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) =
        (beta_cr i z + gamma_cr i z - 1) * Di i"
    proof -
      fix i :: nat and z :: "real \<times> real"
      assume hi: "i < n"
      have hDne: "Di i \<noteq> 0" using hDi_pos[OF hi] by (by100 linarith)
      \<comment> \<open>z - v_i = (z - c) - (v_i - c) = beta_i*(v_i-c) + gamma_i*(v_{i+1}-c) - (v_i-c)
         = (beta_i - 1)*(v_i-c) + gamma_i*(v_{i+1}-c).\<close>
      have hfst: "fst z - vx i = (beta_cr i z - 1) * (vx i - cx) + gamma_cr i z * (vx (Suc i mod n) - cx)"
      proof -
        have "fst z - vx i = (fst z - cx) - (vx i - cx)" by (by100 simp)
        also have "fst z - cx = beta_cr i z * (vx i - cx) + gamma_cr i z * (vx (Suc i mod n) - cx)"
          using hCramer_x[OF hDne] .
        finally show ?thesis by (simp add: algebra_simps)
      qed
      have hsnd: "snd z - vy i = (beta_cr i z - 1) * (vy i - cy) + gamma_cr i z * (vy (Suc i mod n) - cy)"
      proof -
        have "snd z - vy i = (snd z - cy) - (vy i - cy)" by (by100 simp)
        also have "snd z - cy = beta_cr i z * (vy i - cy) + gamma_cr i z * (vy (Suc i mod n) - cy)"
          using hCramer_y[OF hDne] .
        finally show ?thesis by (simp add: algebra_simps)
      qed
      \<comment> \<open>cross2((beta-1)*(v_i-c) + gamma*(v_{i+1}-c), v_{i+1}-v_i)
         = (beta-1)*cross2(v_i-c, v_{i+1}-v_i) + gamma*cross2(v_{i+1}-c, v_{i+1}-v_i)
         = (beta-1)*Di + gamma*Di = (beta+gamma-1)*Di.\<close>
      have "cross2 (fst z - vx i, snd z - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) =
          (beta_cr i z - 1) * ((vx i - cx) * (vy (Suc i mod n) - vy i) - (vy i - cy) * (vx (Suc i mod n) - vx i)) +
          gamma_cr i z * ((vx (Suc i mod n) - cx) * (vy (Suc i mod n) - vy i) - (vy (Suc i mod n) - cy) * (vx (Suc i mod n) - vx i))"
        unfolding cross2_def hfst hsnd by (simp add: algebra_simps)
      also have "(vx i - cx) * (vy (Suc i mod n) - vy i) - (vy i - cy) * (vx (Suc i mod n) - vx i) = Di i"
        using hDi_eq unfolding cross2_def by (by100 simp)
      also have "(vx (Suc i mod n) - cx) * (vy (Suc i mod n) - vy i) - (vy (Suc i mod n) - cy) * (vx (Suc i mod n) - vx i) = Di i"
      proof -
        have "(vx (Suc i mod n) - cx) * (vy (Suc i mod n) - vy i) - (vy (Suc i mod n) - cy) * (vx (Suc i mod n) - vx i) =
            ((vx i - cx) + (vx (Suc i mod n) - vx i)) * (vy (Suc i mod n) - vy i) -
            ((vy i - cy) + (vy (Suc i mod n) - vy i)) * (vx (Suc i mod n) - vx i)"
          by (simp add: algebra_simps)
        also have "\<dots> = (vx i - cx) * (vy (Suc i mod n) - vy i) - (vy i - cy) * (vx (Suc i mod n) - vx i)"
          by (simp add: algebra_simps)
        also have "\<dots> = Di i"
          using hDi_eq unfolding cross2_def by (by100 simp)
        finally show ?thesis .
      qed
      finally show "cross2 (fst z - vx i, snd z - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) =
          (beta_cr i z + gamma_cr i z - 1) * Di i"
        by (simp add: algebra_simps)
    qed
    \<comment> \<open>Helper: alpha_i >= alpha_j (centroid weight inequality).\<close>
    have halpha_le: "\<And>i j z. i < n \<Longrightarrow> j < n \<Longrightarrow> in_cone i z \<Longrightarrow> in_cone j z \<Longrightarrow>
        beta_cr i z + gamma_cr i z \<le> beta_cr j z + gamma_cr j z"
    proof -
      fix i j :: nat and z :: "real \<times> real"
      assume hi: "i < n" and hj: "j < n"
      assume hic: "in_cone i z" and hjc: "in_cone j z"
      \<comment> \<open>From in_cone j: z - v_i expressed via j-decomposition.
         cross2(z-v_i, v_{i+1}-v_i) = -(1-s_i)*Di (from i-decomp)
         = alpha_j*cross2(c-v_i, ...) + beta_j*cross2(v_j-v_i, ...) + gamma_j*cross2(v_{j+1}-v_i, ...)
         = -alpha_j*Di + beta_j*Xji + gamma_j*Yji
         where Xji, Yji <= 0.\<close>
      have hDi: "Di i > 0" using hDi_pos[OF hi] .
      have hDne: "Di i \<noteq> 0" using hDi by (by100 linarith)
      have hDjne: "Di j \<noteq> 0" using hDi_pos[OF hj] by (by100 linarith)
      have hbi: "beta_cr i z \<ge> 0" using hic unfolding in_cone_def by (by100 blast)
      have hgi: "gamma_cr i z \<ge> 0" using hic unfolding in_cone_def by (by100 blast)
      have hbgi: "beta_cr i z + gamma_cr i z \<le> 1" using hic unfolding in_cone_def by (by100 blast)
      have hbj: "beta_cr j z \<ge> 0" using hjc unfolding in_cone_def by (by100 blast)
      have hgj: "gamma_cr j z \<ge> 0" using hjc unfolding in_cone_def by (by100 blast)
      have hbgj: "beta_cr j z + gamma_cr j z \<le> 1" using hjc unfolding in_cone_def by (by100 blast)
      \<comment> \<open>cross2(z-v_i, v_{i+1}-v_i) via i-decomposition.\<close>
      have hcross_i: "cross2 (fst z - vx i, snd z - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) =
          (beta_cr i z + gamma_cr i z - 1) * Di i"
        using hcross_z_vi[OF hi] .
      \<comment> \<open>Same cross2 via j-decomposition: use Cramer for j.\<close>
      have hfst_j: "fst z - cx = beta_cr j z * (vx j - cx) + gamma_cr j z * (vx (Suc j mod n) - cx)"
        using hCramer_x[OF hDjne, of z] .
      have hsnd_j: "snd z - cy = beta_cr j z * (vy j - cy) + gamma_cr j z * (vy (Suc j mod n) - cy)"
        using hCramer_y[OF hDjne, of z] .
      \<comment> \<open>z - v_i = (z-c) + (c-v_i) = beta_j*(v_j-c) + gamma_j*(v_{j+1}-c) + (c-v_i)
         = (1-beta_j-gamma_j)*(c-v_i) + beta_j*(v_j-v_i) + gamma_j*(v_{j+1}-v_i).\<close>
      define alpha_j where "alpha_j = 1 - beta_cr j z - gamma_cr j z"
      have haj_ge: "alpha_j \<ge> 0" unfolding alpha_j_def using hbgj by (by100 linarith)
      have hXji: "cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
        using hvert_hp hi hj by (by100 blast)
      have hYji: "cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
      proof -
        have "Suc j mod n < n" using hn hj by (by100 simp)
        thus ?thesis using hvert_hp hi by (by100 blast)
      qed
      \<comment> \<open>cross2(z-v_i, v_{i+1}-v_i) = alpha_j*cross2(c-v_i, ...) + beta_j*Xji + gamma_j*Yji
         = -alpha_j*Di + beta_j*Xji + gamma_j*Yji.\<close>
      have hcross_j: "cross2 (fst z - vx i, snd z - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) =
          - alpha_j * Di i + beta_cr j z * cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)
          + gamma_cr j z * cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)"
      proof -
        \<comment> \<open>fst z - vx i = alpha_j*(cx - vx i) + beta_j*(vx j - vx i) + gamma_j*(vx(j+1) - vx i).\<close>
        have hfst_vi: "fst z - vx i = alpha_j * (cx - vx i) + beta_cr j z * (vx j - vx i) + gamma_cr j z * (vx (Suc j mod n) - vx i)"
        proof -
          have "fst z - vx i = (fst z - cx) + (cx - vx i)" by (by100 simp)
          also have "fst z - cx = beta_cr j z * (vx j - cx) + gamma_cr j z * (vx (Suc j mod n) - cx)"
            using hfst_j .
          finally have "fst z - vx i = beta_cr j z * (vx j - cx) + gamma_cr j z * (vx (Suc j mod n) - cx) + (cx - vx i)"
            by (by100 simp)
          also have "\<dots> = (1 - beta_cr j z - gamma_cr j z) * (cx - vx i) + beta_cr j z * (vx j - vx i) + gamma_cr j z * (vx (Suc j mod n) - vx i)"
            by (simp add: algebra_simps)
          finally show ?thesis unfolding alpha_j_def by (by100 simp)
        qed
        have hsnd_vi: "snd z - vy i = alpha_j * (cy - vy i) + beta_cr j z * (vy j - vy i) + gamma_cr j z * (vy (Suc j mod n) - vy i)"
        proof -
          have "snd z - vy i = (snd z - cy) + (cy - vy i)" by (by100 simp)
          also have "snd z - cy = beta_cr j z * (vy j - cy) + gamma_cr j z * (vy (Suc j mod n) - cy)"
            using hsnd_j .
          finally have "snd z - vy i = beta_cr j z * (vy j - cy) + gamma_cr j z * (vy (Suc j mod n) - cy) + (cy - vy i)"
            by (by100 simp)
          also have "\<dots> = (1 - beta_cr j z - gamma_cr j z) * (cy - vy i) + beta_cr j z * (vy j - vy i) + gamma_cr j z * (vy (Suc j mod n) - vy i)"
            by (simp add: algebra_simps)
          finally show ?thesis unfolding alpha_j_def by (by100 simp)
        qed
        \<comment> \<open>Now expand cross2(z-v_i, v_{i+1}-v_i) using hfst_vi and hsnd_vi.\<close>
        have "cross2 (fst z - vx i, snd z - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) =
            (fst z - vx i) * (vy (Suc i mod n) - vy i) - (snd z - vy i) * (vx (Suc i mod n) - vx i)"
          unfolding cross2_def by (by100 simp)
        also have "\<dots> = (alpha_j * (cx - vx i) + beta_cr j z * (vx j - vx i) + gamma_cr j z * (vx (Suc j mod n) - vx i)) * (vy (Suc i mod n) - vy i)
            - (alpha_j * (cy - vy i) + beta_cr j z * (vy j - vy i) + gamma_cr j z * (vy (Suc j mod n) - vy i)) * (vx (Suc i mod n) - vx i)"
          unfolding hfst_vi hsnd_vi by (by100 simp)
        also have "\<dots> = alpha_j * ((cx - vx i) * (vy (Suc i mod n) - vy i) - (cy - vy i) * (vx (Suc i mod n) - vx i))
            + beta_cr j z * ((vx j - vx i) * (vy (Suc i mod n) - vy i) - (vy j - vy i) * (vx (Suc i mod n) - vx i))
            + gamma_cr j z * ((vx (Suc j mod n) - vx i) * (vy (Suc i mod n) - vy i) - (vy (Suc j mod n) - vy i) * (vx (Suc i mod n) - vx i))"
          by (simp add: algebra_simps)
        also have "((cx - vx i) * (vy (Suc i mod n) - vy i) - (cy - vy i) * (vx (Suc i mod n) - vx i)) = - Di i"
          using hDi_eq unfolding cross2_def by (simp add: algebra_simps)
        finally show ?thesis unfolding cross2_def by (simp add: algebra_simps)
      qed
      \<comment> \<open>Equating the two expressions for cross2(z-v_i, ...).\<close>
      have hkey: "(beta_cr i z + gamma_cr i z - 1) * Di i =
          - alpha_j * Di i + beta_cr j z * cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)
          + gamma_cr j z * cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)"
        using hcross_i hcross_j by (by100 simp)
      \<comment> \<open>Rearrange: (s_i - s_j)*Di = beta_j*Xji + gamma_j*Yji \<le> 0.\<close>
      have hkey2: "(beta_cr i z + gamma_cr i z - (beta_cr j z + gamma_cr j z)) * Di i =
          beta_cr j z * cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)
          + gamma_cr j z * cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)"
        using hkey unfolding alpha_j_def by (simp add: algebra_simps)
      have hrhs_le0: "beta_cr j z * cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)
          + gamma_cr j z * cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
      proof -
        have "beta_cr j z * cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
          using mult_nonneg_nonpos[OF hbj hXji] .
        moreover have "gamma_cr j z * cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
          using mult_nonneg_nonpos[OF hgj hYji] .
        ultimately show ?thesis by (by100 linarith)
      qed
      \<comment> \<open>So (s_i - s_j)*Di \<le> 0, hence s_i \<le> s_j since Di > 0.\<close>
      have "(beta_cr i z + gamma_cr i z - (beta_cr j z + gamma_cr j z)) * Di i \<le> 0"
        using hkey2 hrhs_le0 by (by100 linarith)
      thus "beta_cr i z + gamma_cr i z \<le> beta_cr j z + gamma_cr j z"
        using hDi by (simp add: mult_le_0_iff)
    qed
    \<comment> \<open>Corollary: s_i = s_j.\<close>
    have hs_eq: "\<And>i j z. i < n \<Longrightarrow> j < n \<Longrightarrow> in_cone i z \<Longrightarrow> in_cone j z \<Longrightarrow>
        beta_cr i z + gamma_cr i z = beta_cr j z + gamma_cr j z"
    proof -
      fix i j :: nat and z :: "real \<times> real"
      assume hi: "i < n" and hj: "j < n" and hic: "in_cone i z" and hjc: "in_cone j z"
      have "beta_cr i z + gamma_cr i z \<le> beta_cr j z + gamma_cr j z"
        using halpha_le[OF hi hj hic hjc] .
      moreover have "beta_cr j z + gamma_cr j z \<le> beta_cr i z + gamma_cr i z"
        using halpha_le[OF hj hi hjc hic] .
      ultimately show "beta_cr i z + gamma_cr i z = beta_cr j z + gamma_cr j z"
        by (by100 linarith)
    qed
    \<comment> \<open>Corollary: vanishing cross2 products.\<close>
    have hvanish: "\<And>i j z. i < n \<Longrightarrow> j < n \<Longrightarrow> in_cone i z \<Longrightarrow> in_cone j z \<Longrightarrow>
        beta_cr j z * cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) = 0
      \<and> gamma_cr j z * cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) = 0"
    proof -
      fix i j :: nat and z :: "real \<times> real"
      assume hi: "i < n" and hj: "j < n" and hic: "in_cone i z" and hjc: "in_cone j z"
      have hDi: "Di i > 0" using hDi_pos[OF hi] .
      have hDne: "Di i \<noteq> 0" using hDi by (by100 linarith)
      have hDjne: "Di j \<noteq> 0" using hDi_pos[OF hj] by (by100 linarith)
      have hbj: "beta_cr j z \<ge> 0" using hjc unfolding in_cone_def by (by100 blast)
      have hgj: "gamma_cr j z \<ge> 0" using hjc unfolding in_cone_def by (by100 blast)
      have hXji: "cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
        using hvert_hp hi hj by (by100 blast)
      have hYji: "cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
      proof -
        have "Suc j mod n < n" using hn hj by (by100 simp)
        thus ?thesis using hvert_hp hi by (by100 blast)
      qed
      have hseq: "beta_cr i z + gamma_cr i z = beta_cr j z + gamma_cr j z"
        using hs_eq[OF hi hj hic hjc] .
      \<comment> \<open>From the key equation: (s_i - s_j)*Di = beta_j*Xji + gamma_j*Yji = 0.\<close>
      have hfst_j: "fst z - cx = beta_cr j z * (vx j - cx) + gamma_cr j z * (vx (Suc j mod n) - cx)"
        using hCramer_x[OF hDjne, of z] .
      have hsnd_j: "snd z - cy = beta_cr j z * (vy j - cy) + gamma_cr j z * (vy (Suc j mod n) - cy)"
        using hCramer_y[OF hDjne, of z] .
      have hcross_i: "cross2 (fst z - vx i, snd z - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) =
          (beta_cr i z + gamma_cr i z - 1) * Di i"
        using hcross_z_vi[OF hi] .
      define alpha_j where "alpha_j = 1 - beta_cr j z - gamma_cr j z"
      have hcross_j: "cross2 (fst z - vx i, snd z - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) =
          - alpha_j * Di i + beta_cr j z * cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)
          + gamma_cr j z * cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)"
      proof -
        have hfst_vi: "fst z - vx i = alpha_j * (cx - vx i) + beta_cr j z * (vx j - vx i) + gamma_cr j z * (vx (Suc j mod n) - vx i)"
        proof -
          have "fst z - vx i = (fst z - cx) + (cx - vx i)" by (by100 simp)
          also have "fst z - cx = beta_cr j z * (vx j - cx) + gamma_cr j z * (vx (Suc j mod n) - cx)"
            using hfst_j .
          finally show ?thesis unfolding alpha_j_def by (simp add: algebra_simps)
        qed
        have hsnd_vi: "snd z - vy i = alpha_j * (cy - vy i) + beta_cr j z * (vy j - vy i) + gamma_cr j z * (vy (Suc j mod n) - vy i)"
        proof -
          have "snd z - vy i = (snd z - cy) + (cy - vy i)" by (by100 simp)
          also have "snd z - cy = beta_cr j z * (vy j - cy) + gamma_cr j z * (vy (Suc j mod n) - cy)"
            using hsnd_j .
          finally show ?thesis unfolding alpha_j_def by (simp add: algebra_simps)
        qed
        show ?thesis
        proof -
          have "cross2 (fst z - vx i, snd z - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) =
              (fst z - vx i) * (vy (Suc i mod n) - vy i) - (snd z - vy i) * (vx (Suc i mod n) - vx i)"
            unfolding cross2_def by (by100 simp)
          also have "\<dots> = alpha_j * ((cx - vx i) * (vy (Suc i mod n) - vy i) - (cy - vy i) * (vx (Suc i mod n) - vx i))
              + beta_cr j z * ((vx j - vx i) * (vy (Suc i mod n) - vy i) - (vy j - vy i) * (vx (Suc i mod n) - vx i))
              + gamma_cr j z * ((vx (Suc j mod n) - vx i) * (vy (Suc i mod n) - vy i) - (vy (Suc j mod n) - vy i) * (vx (Suc i mod n) - vx i))"
            unfolding hfst_vi hsnd_vi by (simp add: algebra_simps)
          also have "((cx - vx i) * (vy (Suc i mod n) - vy i) - (cy - vy i) * (vx (Suc i mod n) - vx i)) = - Di i"
            using hDi_eq unfolding cross2_def by (simp add: algebra_simps)
          finally show ?thesis unfolding cross2_def by (simp add: algebra_simps)
        qed
      qed
      have hsum0: "beta_cr j z * cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)
          + gamma_cr j z * cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) = 0"
      proof -
        have h1: "(beta_cr i z + gamma_cr i z - 1) * Di i =
            - alpha_j * Di i + beta_cr j z * cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)
            + gamma_cr j z * cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i)"
          using hcross_i hcross_j by (by100 simp)
        have "alpha_j = 1 - (beta_cr j z + gamma_cr j z)" unfolding alpha_j_def by (by100 simp)
        hence halpha_eq: "alpha_j = 1 - (beta_cr i z + gamma_cr i z)" using hseq by (by100 simp)
        hence "(beta_cr i z + gamma_cr i z - 1) * Di i = - alpha_j * Di i"
          by (by5000 simp)
        hence "(beta_cr i z + gamma_cr i z - 1) * Di i =
            - alpha_j * Di i + 0" by (by100 simp)
        thus ?thesis using h1 by (by100 linarith)
      qed
      \<comment> \<open>Each term \<le> 0 and sum = 0, so each = 0.\<close>
      have ht1: "beta_cr j z * cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
        using mult_nonneg_nonpos[OF hbj hXji] .
      have ht2: "gamma_cr j z * cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
        using mult_nonneg_nonpos[OF hgj hYji] .
      show "beta_cr j z * cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) = 0
        \<and> gamma_cr j z * cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) = 0"
        using hsum0 ht1 ht2 by (by100 linarith)
    qed
    \<comment> \<open>No three collinear vertices (extreme-point property).\<close>
    have hno_collinear: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> j \<noteq> i \<Longrightarrow> Suc i mod n \<noteq> j \<Longrightarrow>
        cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<noteq> 0"
      using hno_collinear by (by100 blast)
    have hcollinear_adj: "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow>
        cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) = 0 \<Longrightarrow>
        j = i \<or> j = Suc i mod n"
    proof -
      fix i j :: nat
      assume hi: "i < n" and hj: "j < n"
        and hc: "cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) = 0"
      show "j = i \<or> j = Suc i mod n"
      proof (rule ccontr)
        assume "\<not> (j = i \<or> j = Suc i mod n)"
        hence "j \<noteq> i" "Suc i mod n \<noteq> j" by (by100 simp)+
        thus False using hno_collinear[OF hi hj] hc by (by100 simp)
      qed
    qed
    \<comment> \<open>From vanishing products + no-collinear + Cramer, derive the case disjunction.\<close>
    have hcases: "\<And>i j z. i < n \<Longrightarrow> j < n \<Longrightarrow> in_cone i z \<Longrightarrow> in_cone j z \<Longrightarrow>
        beta_cr i z + gamma_cr i z = 0
        \<or> (i = j \<and> gamma_cr i z = gamma_cr j z)
        \<or> (Suc i mod n = j \<and> beta_cr i z = 0 \<and> gamma_cr j z = 0)
        \<or> (Suc j mod n = i \<and> gamma_cr i z = 0 \<and> beta_cr j z = 0)"
    proof -
      fix i j :: nat and z :: "real \<times> real"
      assume hi: "i < n" and hj: "j < n" and hic: "in_cone i z" and hjc: "in_cone j z"
      have hDi: "Di i > 0" using hDi_pos[OF hi] .
      have hDj: "Di j > 0" using hDi_pos[OF hj] .
      have hDne: "Di i \<noteq> 0" using hDi by (by100 linarith)
      have hDjne: "Di j \<noteq> 0" using hDj by (by100 linarith)
      have hbi: "beta_cr i z \<ge> 0" using hic unfolding in_cone_def by (by100 blast)
      have hgi: "gamma_cr i z \<ge> 0" using hic unfolding in_cone_def by (by100 blast)
      have hbj: "beta_cr j z \<ge> 0" using hjc unfolding in_cone_def by (by100 blast)
      have hgj: "gamma_cr j z \<ge> 0" using hjc unfolding in_cone_def by (by100 blast)
      have hseq: "beta_cr i z + gamma_cr i z = beta_cr j z + gamma_cr j z"
        using hs_eq[OF hi hj hic hjc] .
      define s where "s = beta_cr i z + gamma_cr i z"
      have hsj: "beta_cr j z + gamma_cr j z = s" using hseq unfolding s_def by (by100 simp)
      have hvan: "beta_cr j z * cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) = 0
        \<and> gamma_cr j z * cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) = 0"
        using hvanish[OF hi hj hic hjc] .
      have hvan_i: "beta_cr i z * cross2 (vx i - vx j, vy i - vy j) (vx (Suc j mod n) - vx j, vy (Suc j mod n) - vy j) = 0
        \<and> gamma_cr i z * cross2 (vx (Suc i mod n) - vx j, vy (Suc i mod n) - vy j) (vx (Suc j mod n) - vx j, vy (Suc j mod n) - vy j) = 0"
        using hvanish[OF hj hi hjc hic] .
      show "s = 0 \<or> (i = j \<and> gamma_cr i z = gamma_cr j z)
        \<or> (Suc i mod n = j \<and> beta_cr i z = 0 \<and> gamma_cr j z = 0)
        \<or> (Suc j mod n = i \<and> gamma_cr i z = 0 \<and> beta_cr j z = 0)"
      proof (cases "s = 0")
        case True thus ?thesis by (by100 simp)
      next
        case hsnz: False
        show ?thesis
        proof (cases "beta_cr j z = 0")
          case hbj0: True
          hence hgj_pos: "gamma_cr j z > 0" using hsnz hsj hgj by (by100 linarith)
          have hYji0: "cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) = 0"
            using hvan hgj_pos by (by100 simp)
          have hSjn: "Suc j mod n < n" using hn hj by (by100 simp)
          have hadj: "Suc j mod n = i \<or> Suc j mod n = Suc i mod n"
            using hcollinear_adj[OF hi hSjn hYji0] .
          show ?thesis
          proof (cases "beta_cr i z = 0")
            case hbi0: True
            have hgi_s: "gamma_cr i z = s" using hbi0 s_def by (by100 linarith)
            have hgj_s: "gamma_cr j z = s" using hbj0 hsj by (by100 linarith)
            have hCx_i: "fst z - cx = s * (vx (Suc i mod n) - cx)" using hCramer_x[OF hDne] hbi0 hgi_s by (by100 simp)
            have hCx_j: "fst z - cx = s * (vx (Suc j mod n) - cx)" using hCramer_x[OF hDjne] hbj0 hgj_s by (by100 simp)
            have hvx: "vx (Suc i mod n) = vx (Suc j mod n)" using hCx_i hCx_j hsnz by (by100 simp)
            have hCy_i: "snd z - cy = s * (vy (Suc i mod n) - cy)" using hCramer_y[OF hDne] hbi0 hgi_s by (by100 simp)
            have hCy_j: "snd z - cy = s * (vy (Suc j mod n) - cy)" using hCramer_y[OF hDjne] hbj0 hgj_s by (by100 simp)
            have hvy: "vy (Suc i mod n) = vy (Suc j mod n)" using hCy_i hCy_j hsnz by (by100 simp)
            from hadj show ?thesis
            proof (elim disjE)
              assume "Suc j mod n = i"
              hence "vx (Suc i mod n) = vx i" and "vy (Suc i mod n) = vy i" using hvx hvy by (by100 simp)+
              hence "Di i = 0" unfolding Di_def by (by100 simp)
              thus ?thesis using hDi by (by100 linarith)
            next
              assume hmod_eq: "Suc j mod n = Suc i mod n"
              hence "i = j"
              proof -
                have "Suc i \<le> n" using hi by (by100 linarith)
                have "Suc j \<le> n" using hj by (by100 linarith)
                show ?thesis
                proof (cases "Suc i = n")
                  case True hence "Suc i mod n = 0" by (by100 simp)
                  hence hsjmod: "Suc j mod n = 0" using hmod_eq by (by100 simp)
                  hence "n dvd Suc j"
                  proof -
                    from hsjmod have "Suc j mod n = 0" .
                    thus "n dvd Suc j" using dvd_eq_mod_eq_0[of n "Suc j"] by (by100 simp)
                  qed
                  hence "Suc j = n" using \<open>Suc j \<le> n\<close>
                    using dvd_imp_le[of n "Suc j"] hn by (by100 linarith)
                  thus ?thesis using True by (by100 simp)
                next
                  case False hence "Suc i < n" using \<open>Suc i \<le> n\<close> by (by100 linarith)
                  hence hsi: "Suc i mod n = Suc i" by (by100 simp)
                  show ?thesis
                  proof (cases "Suc j = n")
                    case True hence "Suc j mod n = 0" by (by100 simp)
                    hence "Suc i = 0" using hmod_eq hsi by (by100 simp)
                    thus ?thesis by (by100 simp)
                  next
                    case False2: False
                    hence "Suc j < n" using \<open>Suc j \<le> n\<close> by (by100 linarith)
                    hence "Suc j mod n = Suc j" by (by100 simp)
                    hence "Suc j = Suc i" using hmod_eq hsi by (by100 simp)
                    thus ?thesis by (by100 simp)
                  qed
                qed
              qed
              thus ?thesis using hgi_s hgj_s by (by100 simp)
            qed
          next
            case hbi_pos: False
            hence hbi_pos': "beta_cr i z > 0" using hbi by (by100 linarith)
            show ?thesis
            proof (cases "gamma_cr i z = 0")
              case hgi0: True
              have hbi_s: "beta_cr i z = s" using hgi0 s_def by (by100 linarith)
              have hCx_i: "fst z - cx = s * (vx i - cx)" using hCramer_x[OF hDne] hgi0 hbi_s by (by100 simp)
              have hCx_j: "fst z - cx = s * (vx (Suc j mod n) - cx)" using hCramer_x[OF hDjne] hbj0 hsj by (by100 simp)
              have hvx: "vx i = vx (Suc j mod n)" using hCx_i hCx_j hsnz by (by100 simp)
              have hCy_i: "snd z - cy = s * (vy i - cy)" using hCramer_y[OF hDne] hgi0 hbi_s by (by100 simp)
              have hCy_j: "snd z - cy = s * (vy (Suc j mod n) - cy)" using hCramer_y[OF hDjne] hbj0 hsj by (by100 simp)
              have hvy: "vy i = vy (Suc j mod n)" using hCy_i hCy_j hsnz by (by100 simp)
              from hadj show ?thesis
              proof (elim disjE)
                assume "Suc j mod n = i" thus ?thesis using hgi0 hbj0 by (by100 blast)
              next
                assume "Suc j mod n = Suc i mod n"
                hence "vx (Suc i mod n) = vx i" and "vy (Suc i mod n) = vy i" using hvx hvy by (by100 simp)+
                hence "Di i = 0" unfolding Di_def by (by100 simp)
                thus ?thesis using hDi by (by100 linarith)
              qed
            next
              case hgi_pos: False
              hence hgi_pos': "gamma_cr i z > 0" using hgi by (by100 linarith)
              have hXij0_prod: "beta_cr i z * cross2 (vx i - vx j, vy i - vy j) (vx (Suc j mod n) - vx j, vy (Suc j mod n) - vy j) = 0"
                using hvan_i by (by100 blast)
              have hXij0: "cross2 (vx i - vx j, vy i - vy j) (vx (Suc j mod n) - vx j, vy (Suc j mod n) - vy j) = 0"
                using hXij0_prod hbi_pos' by (by100 simp)
              have hadj_ij: "i = j \<or> i = Suc j mod n"
                using hcollinear_adj[OF hj hi hXij0] .
              show ?thesis
              proof (cases "i = j")
                case True
                have "gamma_cr i z = gamma_cr j z" using True by (by100 simp)
                thus ?thesis using True by (by100 blast)
              next
                case False
                hence "i = Suc j mod n" using hadj_ij by (by100 simp)
                hence hSj_i: "Suc j mod n = i" by (by100 simp)
                have hCx_j: "fst z - cx = gamma_cr j z * (vx i - cx)" using hCramer_x[OF hDjne] hbj0 hSj_i by (by100 simp)
                have hCx_i: "fst z - cx = beta_cr i z * (vx i - cx) + gamma_cr i z * (vx (Suc i mod n) - cx)" using hCramer_x[OF hDne] .
                have heqx: "gamma_cr i z * (vx (Suc i mod n) - cx) = (gamma_cr j z - beta_cr i z) * (vx i - cx)"
                  using hCx_i hCx_j by (simp add: algebra_simps)
                have hCy_j: "snd z - cy = gamma_cr j z * (vy i - cy)" using hCramer_y[OF hDjne] hbj0 hSj_i by (by100 simp)
                have hCy_i: "snd z - cy = beta_cr i z * (vy i - cy) + gamma_cr i z * (vy (Suc i mod n) - cy)" using hCramer_y[OF hDne] .
                have heqy: "gamma_cr i z * (vy (Suc i mod n) - cy) = (gamma_cr j z - beta_cr i z) * (vy i - cy)"
                  using hCy_i hCy_j by (simp add: algebra_simps)
                define r where "r = (gamma_cr j z - beta_cr i z) / gamma_cr i z"
                have hvx_eq: "vx (Suc i mod n) - cx = r * (vx i - cx)" using heqx hgi_pos' unfolding r_def by (simp add: field_simps)
                have hvy_eq: "vy (Suc i mod n) - cy = r * (vy i - cy)" using heqy hgi_pos' unfolding r_def by (simp add: field_simps)
                have "Di i = r * (vx i - cx) * (vy i - cy) - r * (vy i - cy) * (vx i - cx)" unfolding Di_def using hvx_eq hvy_eq by (by100 simp)
                hence "Di i = 0" by (simp add: algebra_simps)
                thus ?thesis using hDi by (by100 linarith)
              qed
            qed
          qed
        next
          case hbj_pos: False
          hence hbj_pos': "beta_cr j z > 0" using hbj by (by100 linarith)
          have hXji0: "cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) = 0"
            using hvan hbj_pos' by (by100 simp)
          have hadj_ji: "j = i \<or> j = Suc i mod n" using hcollinear_adj[OF hi hj hXji0] .
          show ?thesis
          proof (cases "gamma_cr j z = 0")
            case hgj0: True
            have hbj_s: "beta_cr j z = s" using hgj0 hsj by (by100 linarith)
            show ?thesis
            proof (cases "gamma_cr i z = 0")
              case hgi0: True
              have hbi_s: "beta_cr i z = s" using hgi0 s_def by (by100 linarith)
              have hCx_i: "fst z - cx = s * (vx i - cx)" using hCramer_x[OF hDne] hgi0 hbi_s by (by100 simp)
              have hCx_j: "fst z - cx = s * (vx j - cx)" using hCramer_x[OF hDjne] hgj0 hbj_s by (by100 simp)
              have hvx: "vx i = vx j" using hCx_i hCx_j hsnz by (by100 simp)
              have hCy_i: "snd z - cy = s * (vy i - cy)" using hCramer_y[OF hDne] hgi0 hbi_s by (by100 simp)
              have hCy_j: "snd z - cy = s * (vy j - cy)" using hCramer_y[OF hDjne] hgj0 hbj_s by (by100 simp)
              have hvy: "vy i = vy j" using hCy_i hCy_j hsnz by (by100 simp)
              from hadj_ji show ?thesis
              proof (elim disjE)
                assume "j = i" thus ?thesis using hgi0 hgj0 by (by100 simp)
              next
                assume "j = Suc i mod n"
                hence "vx (Suc i mod n) = vx i" and "vy (Suc i mod n) = vy i" using hvx hvy by (by100 simp)+
                hence "Di i = 0" unfolding Di_def by (by100 simp)
                thus ?thesis using hDi by (by100 linarith)
              qed
            next
              case hgi_pos: False
              hence hgi_pos': "gamma_cr i z > 0" using hgi by (by100 linarith)
              from hadj_ji show ?thesis
              proof (elim disjE)
                assume "j = i" thus ?thesis using s_def hsj by (by100 simp)
              next
                assume hj_Si: "j = Suc i mod n"
                show ?thesis
                proof (cases "beta_cr i z = 0")
                  case True thus ?thesis using hj_Si hgj0 by (by100 blast)
                next
                  case False
                  hence hbi_pos': "beta_cr i z > 0" using hbi by (by100 linarith)
                  have hCx_j: "fst z - cx = s * (vx (Suc i mod n) - cx)" using hCramer_x[OF hDjne] hgj0 hbj_s hj_Si by (by100 simp)
                  have hCx_i: "fst z - cx = beta_cr i z * (vx i - cx) + gamma_cr i z * (vx (Suc i mod n) - cx)" using hCramer_x[OF hDne] .
                  have heqx: "beta_cr i z * (vx i - cx) = (s - gamma_cr i z) * (vx (Suc i mod n) - cx)" using hCx_i hCx_j by (simp add: algebra_simps)
                  have hCy_j: "snd z - cy = s * (vy (Suc i mod n) - cy)" using hCramer_y[OF hDjne] hgj0 hbj_s hj_Si by (by100 simp)
                  have hCy_i: "snd z - cy = beta_cr i z * (vy i - cy) + gamma_cr i z * (vy (Suc i mod n) - cy)" using hCramer_y[OF hDne] .
                  have heqy: "beta_cr i z * (vy i - cy) = (s - gamma_cr i z) * (vy (Suc i mod n) - cy)" using hCy_i hCy_j by (simp add: algebra_simps)
                  define r where "r = (s - gamma_cr i z) / beta_cr i z"
                  have hvx_eq: "vx i - cx = r * (vx (Suc i mod n) - cx)" using heqx hbi_pos' unfolding r_def by (simp add: field_simps)
                  have hvy_eq: "vy i - cy = r * (vy (Suc i mod n) - cy)" using heqy hbi_pos' unfolding r_def by (simp add: field_simps)
                  have "Di i = r * (vx (Suc i mod n) - cx) * (vy (Suc i mod n) - cy) - r * (vy (Suc i mod n) - cy) * (vx (Suc i mod n) - cx)"
                    unfolding Di_def using hvx_eq hvy_eq by (by100 simp)
                  hence "Di i = 0" by (simp add: algebra_simps)
                  thus ?thesis using hDi by (by100 linarith)
                qed
              qed
            qed
          next
            case hgj_pos: False
            hence hgj_pos': "gamma_cr j z > 0" using hgj by (by100 linarith)
            have hYji0: "cross2 (vx (Suc j mod n) - vx i, vy (Suc j mod n) - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) = 0"
              using hvan hgj_pos' by (by100 simp)
            have hSjn: "Suc j mod n < n" using hn hj by (by100 simp)
            have hadj_Sj: "Suc j mod n = i \<or> Suc j mod n = Suc i mod n" using hcollinear_adj[OF hi hSjn hYji0] .
            from hadj_ji show ?thesis
            proof (elim disjE)
              assume "j = i" thus ?thesis using s_def hsj by (by100 simp)
            next
              assume hj_Si: "j = Suc i mod n"
              from hadj_Sj show ?thesis
              proof (elim disjE)
                assume hSj_i: "Suc j mod n = i"
                \<comment> \<open>j = i+1 mod n and j+1 = i mod n. Impossible for n >= 3.\<close>
                \<comment> \<open>(i+2) mod n = i, so n | 2. But n >= 3.\<close>
                have "(i + 2) mod n = i"
                proof -
                  have "j = Suc i mod n" using hj_Si .
                  have "Suc j mod n = i" using hSj_i .
                  have "(Suc (Suc i)) mod n = Suc (Suc i mod n) mod n"
                    using mod_Suc_eq[of "Suc i" n, symmetric] by (by100 simp)
                  also have "Suc (Suc i mod n) mod n = Suc j mod n" using hj_Si by (by100 simp)
                  also have "\<dots> = i" using hSj_i .
                  finally show ?thesis by (by100 simp)
                qed
                hence "n dvd 2"
                proof -
                  have "i + 2 \<ge> i" by (by100 simp)
                  have "(i + 2) mod n = i mod n" using \<open>(i + 2) mod n = i\<close> hi
                    by (by100 simp)
                  hence "n dvd (i + 2 - i)" using \<open>i + 2 \<ge> i\<close>
                    using mod_eq_dvd_iff_nat by (by100 blast)
                  thus ?thesis by (by100 simp)
                qed
                hence "n \<le> 2"
                proof -
                  have "n > 0" using hn by (by100 linarith)
                  thus ?thesis using \<open>n dvd 2\<close> dvd_imp_le[of n 2] by (by100 simp)
                qed
                thus ?thesis using hn by (by100 linarith)
              next
                assume hmod_eq2: "Suc j mod n = Suc i mod n"
                hence "j = i"
                proof -
                  have "Suc i \<le> n" using hi by (by100 linarith)
                  have "Suc j \<le> n" using hj by (by100 linarith)
                  show ?thesis
                  proof (cases "Suc i = n")
                    case True hence "Suc i mod n = 0" by (by100 simp)
                    hence "Suc j mod n = 0" using hmod_eq2 by (by100 simp)
                    hence "Suc j = n" using \<open>Suc j \<le> n\<close>
                      using dvd_eq_mod_eq_0[of n "Suc j"] dvd_imp_le[of n "Suc j"] hn
                      by (by100 linarith)
                    thus ?thesis using True by (by100 simp)
                  next
                    case False hence "Suc i < n" using \<open>Suc i \<le> n\<close> by (by100 linarith)
                    hence hsi: "Suc i mod n = Suc i" by (by100 simp)
                    show ?thesis
                    proof (cases "Suc j = n")
                      case True hence "Suc j mod n = 0" by (by100 simp)
                      hence "Suc i = 0" using hmod_eq2 hsi by (by100 simp)
                      thus ?thesis by (by100 simp)
                    next
                      case False2: False
                      hence "Suc j < n" using \<open>Suc j \<le> n\<close> by (by100 linarith)
                      hence "Suc j mod n = Suc j" by (by100 simp)
                      hence "Suc j = Suc i" using hmod_eq2 hsi by (by100 simp)
                      thus ?thesis by (by100 simp)
                    qed
                  qed
                qed
                hence "Suc i mod n = i" using hj_Si by (by100 simp)
                hence "False"
                proof (cases "Suc i < n")
                  case True hence "Suc i mod n = Suc i" by (by100 simp)
                  hence "Suc i = i" using \<open>Suc i mod n = i\<close> by (by100 simp)
                  thus ?thesis by (by100 simp)
                next
                  case False hence "Suc i = n" using hi by (by100 linarith)
                  hence "Suc i mod n = 0" by (by100 simp)
                  hence "i = 0" using \<open>Suc i mod n = i\<close> by (by100 simp)
                  hence "n = 1" using \<open>Suc i = n\<close> by (by100 simp)
                  thus ?thesis using hn by (by100 linarith)
                qed
                thus ?thesis by (by100 simp)
              qed
            qed
          qed
        qed
      qed
    qed
    have hpsi_agree: "\<And>i j z. i < n \<Longrightarrow> j < n \<Longrightarrow> in_cone i z \<Longrightarrow> in_cone j z \<Longrightarrow>
        psi_local i z = psi_local j z"
    proof -
      fix i j :: nat and z :: "real \<times> real"
      assume hi: "i < n" and hj: "j < n" and hic: "in_cone i z" and hjc: "in_cone j z"
      have hseq: "beta_cr i z + gamma_cr i z = beta_cr j z + gamma_cr j z"
        using hs_eq[OF hi hj hic hjc] .
      define s where "s = beta_cr i z + gamma_cr i z"
      have hsj: "beta_cr j z + gamma_cr j z = s" using hseq unfolding s_def by (by100 simp)
      have hcase4: "s = 0 \<or> (i = j \<and> gamma_cr i z = gamma_cr j z)
          \<or> (Suc i mod n = j \<and> beta_cr i z = 0 \<and> gamma_cr j z = 0)
          \<or> (Suc j mod n = i \<and> gamma_cr i z = 0 \<and> beta_cr j z = 0)"
        using hcases[OF hi hj hic hjc] unfolding s_def by (by100 simp)
      have hn_pos: "n > 0" using hn by (by100 linarith)
      have hsi: "beta_cr i z + gamma_cr i z = s" unfolding s_def by (by100 simp)
      have hagree: "(let ui = (if s = 0 then 0 else gamma_cr i z / s);
              \<theta>i = 2 * pi * (real i + ui) / real n
          in (s * cos \<theta>i, s * sin \<theta>i))
       = (let uj = (if s = 0 then 0 else gamma_cr j z / s);
              \<theta>j = 2 * pi * (real j + uj) / real n
          in (s * cos \<theta>j, s * sin \<theta>j))"
        using psi_angle_cases_agree[OF hn_pos hi hj hsi hsj hcase4] .
      have hpsi_i: "psi_local i z = (let ui = (if s = 0 then 0 else gamma_cr i z / s);
              \<theta>i = 2 * pi * (real i + ui) / real n in (s * cos \<theta>i, s * sin \<theta>i))"
        unfolding psi_local_def Let_def using hsi by (by100 simp)
      have hpsi_j: "psi_local j z = (let uj = (if s = 0 then 0 else gamma_cr j z / s);
              \<theta>j = 2 * pi * (real j + uj) / real n in (s * cos \<theta>j, s * sin \<theta>j))"
        unfolding psi_local_def Let_def using hsj by (by100 simp)
      show "psi_local i z = psi_local j z"
        using hpsi_i hpsi_j hagree by (by100 simp)
    qed
    \<comment> \<open>Global \<psi>: well-defined by overlap agreement.\<close>
    define \<psi> where "\<psi> z = psi_local (SOME i. i < n \<and> in_cone i z) z" for z
    have hpsi_eq: "\<And>i z. i < n \<Longrightarrow> in_cone i z \<Longrightarrow> \<psi> z = psi_local i z"
    proof -
      fix i :: nat and z :: "real \<times> real"
      assume hi: "i < n" and hic: "in_cone i z"
      have "\<exists>j. j < n \<and> in_cone j z" using hi hic by (by100 blast)
      hence hsome: "(SOME j. j < n \<and> in_cone j z) < n \<and> in_cone (SOME j. j < n \<and> in_cone j z) z"
        by (rule someI_ex)
      thus "\<psi> z = psi_local i z"
        unfolding \<psi>_def using hpsi_agree[OF _ hi _ hic] by (by100 simp)
    qed
    \<comment> \<open>(c) \<psi> continuous on P.\<close>
    \<comment> \<open>Define cone sets.\<close>
    define cone_set where "cone_set i = {z. in_cone i z}" for i :: nat
    have hcone_closed: "\<And>i. i < n \<Longrightarrow> closed (cone_set i)"
    proof -
      fix i :: nat assume hi: "i < n"
      \<comment> \<open>beta_cr i is a continuous linear function of z.\<close>
      have hDi_ne: "Di i \<noteq> 0" using hDi_pos[OF hi] by (by100 linarith)
      have hb_eq: "beta_cr i = (\<lambda>z::real\<times>real. ((fst z - cx) * (vy (Suc i mod n) - cy)
          - (snd z - cy) * (vx (Suc i mod n) - cx)) / Di i)"
        unfolding beta_cr_def cross2_def by (rule ext) (by100 simp)
      have hg_eq: "gamma_cr i = (\<lambda>z::real\<times>real. ((vx i - cx) * (snd z - cy)
          - (vy i - cy) * (fst z - cx)) / Di i)"
        unfolding gamma_cr_def cross2_def by (rule ext) (by100 simp)
      \<comment> \<open>These are continuous as compositions of continuous functions.\<close>
      have hb_cont: "continuous_on UNIV (beta_cr i)" unfolding hb_eq
        using hDi_ne by (intro continuous_intros) (by100 simp)+
      have hg_cont: "continuous_on UNIV (gamma_cr i)" unfolding hg_eq
        using hDi_ne by (intro continuous_intros) (by100 simp)+
      have hbg_cont: "continuous_on UNIV (\<lambda>z. beta_cr i z + gamma_cr i z)"
        using hb_cont hg_cont by (intro continuous_intros)
      \<comment> \<open>cone_set i is the preimage of a closed set under a continuous function.\<close>
      have "cone_set i = (\<lambda>z. beta_cr i z) -` {0..} \<inter>
          (\<lambda>z. gamma_cr i z) -` {0..} \<inter>
          (\<lambda>z. beta_cr i z + gamma_cr i z) -` {..1}"
        unfolding cone_set_def in_cone_def by (by100 blast)
      moreover have "closed ((\<lambda>z::real\<times>real. beta_cr i z) -` {0..})"
        using closed_vimage[OF closed_atLeast hb_cont] by (by100 simp)
      moreover have "closed ((\<lambda>z::real\<times>real. gamma_cr i z) -` {0..})"
        using closed_vimage[OF closed_atLeast hg_cont] by (by100 simp)
      moreover have "closed ((\<lambda>z::real\<times>real. beta_cr i z + gamma_cr i z) -` {..1})"
        using closed_vimage[OF closed_atMost hbg_cont] by (by100 simp)
      ultimately have "closed ((\<lambda>z. beta_cr i z) -` {0..} \<inter>
          (\<lambda>z. gamma_cr i z) -` {0..} \<inter>
          (\<lambda>z. beta_cr i z + gamma_cr i z) -` {..1})"
        by (intro closed_Int) (by100 assumption)+
      moreover have "cone_set i = (\<lambda>z. beta_cr i z) -` {0..} \<inter>
          (\<lambda>z. gamma_cr i z) -` {0..} \<inter>
          (\<lambda>z. beta_cr i z + gamma_cr i z) -` {..1}"
        unfolding cone_set_def in_cone_def by (by100 blast)
      ultimately show "closed (cone_set i)" by (by100 simp)
    qed
    have hcone_cover: "P \<subseteq> (\<Union>i\<in>{..<n}. cone_set i)"
      using hP_cones unfolding cone_set_def by (by100 blast)
    have hpsi_local_cont: "\<And>i. i < n \<Longrightarrow> continuous_on (cone_set i) (psi_local i)"
    proof -
      fix i :: nat assume hi: "i < n"
      have hDi_ne: "Di i \<noteq> 0" using hDi_pos[OF hi] by (by100 linarith)
      \<comment> \<open>psi_local i z = (s*cos \<theta>, s*sin \<theta>) where s = beta+gamma, \<theta> depends on gamma/s.\<close>
      \<comment> \<open>Key: |psi\_local i z - psi\_local i (cx,cy)| = |psi\_local i z| = s = beta+gamma.\<close>
      \<comment> \<open>And s is continuous (as sum of continuous beta, gamma). So as z\<rightarrow>c, s\<rightarrow>0.\<close>
      \<comment> \<open>Since |psi\_local| = s for all z, and s is continuous, psi\_local is continuous.\<close>
      have hs_cont: "continuous_on (cone_set i) (\<lambda>z. beta_cr i z + gamma_cr i z)"
      proof -
        have hb_eq: "beta_cr i = (\<lambda>z::real\<times>real. ((fst z - cx) * (vy (Suc i mod n) - cy)
            - (snd z - cy) * (vx (Suc i mod n) - cx)) / Di i)"
          unfolding beta_cr_def cross2_def by (rule ext) (by100 simp)
        have hg_eq: "gamma_cr i = (\<lambda>z::real\<times>real. ((vx i - cx) * (snd z - cy)
            - (vy i - cy) * (fst z - cx)) / Di i)"
          unfolding gamma_cr_def cross2_def by (rule ext) (by100 simp)
        have "continuous_on UNIV (beta_cr i)" unfolding hb_eq
          using hDi_ne by (intro continuous_intros) (by100 simp)+
        moreover have "continuous_on UNIV (gamma_cr i)" unfolding hg_eq
          using hDi_ne by (intro continuous_intros) (by100 simp)+
        ultimately have "continuous_on UNIV (\<lambda>z. beta_cr i z + gamma_cr i z)"
          by (intro continuous_intros)
        thus ?thesis using continuous_on_subset by (by100 blast)
      qed
      \<comment> \<open>For any z in cone i: |psi\_local i z|^2 = s^2 (proved earlier as h1 pattern).\<close>
      \<comment> \<open>Each component of psi\_local i z is bounded by s = beta+gamma.\<close>
      have hcomp_bound: "\<And>z. z \<in> cone_set i \<Longrightarrow>
          \<bar>fst (psi_local i z)\<bar> \<le> beta_cr i z + gamma_cr i z \<and>
          \<bar>snd (psi_local i z)\<bar> \<le> beta_cr i z + gamma_cr i z"
      proof -
        fix z assume "z \<in> cone_set i"
        hence hic: "in_cone i z" unfolding cone_set_def by (by100 simp)
        define s where "s = beta_cr i z + gamma_cr i z"
        have hs0: "s \<ge> 0" using hic unfolding in_cone_def s_def by (by100 linarith)
        define u where "u = (if s = 0 then 0 else gamma_cr i z / s)"
        define \<theta> where "\<theta> = 2*pi*(real i + u)/real n"
        have hval: "psi_local i z = (s * cos \<theta>, s * sin \<theta>)"
          unfolding psi_local_def Let_def s_def u_def \<theta>_def by (by100 simp)
        have h1: "\<bar>fst (psi_local i z)\<bar> \<le> s"
        proof -
          have "\<bar>fst (psi_local i z)\<bar> = \<bar>s * cos \<theta>\<bar>" using hval by (by100 simp)
          also have "\<dots> = s * \<bar>cos \<theta>\<bar>"
            using abs_mult[of s "cos \<theta>"] hs0 by (by100 simp)
          also have "\<dots> \<le> s * 1"
            using mult_left_mono[OF abs_cos_le_one[of \<theta>] hs0] by (by100 simp)
          finally show ?thesis by (by100 simp)
        qed
        have h2: "\<bar>snd (psi_local i z)\<bar> \<le> s"
        proof -
          have "\<bar>snd (psi_local i z)\<bar> = \<bar>s * sin \<theta>\<bar>" using hval by (by100 simp)
          also have "\<dots> = s * \<bar>sin \<theta>\<bar>"
            using abs_mult[of s "sin \<theta>"] hs0 by (by100 simp)
          also have "\<dots> \<le> s * 1"
            using mult_left_mono[OF abs_sin_le_one[of \<theta>] hs0] by (by100 simp)
          finally show ?thesis by (by100 simp)
        qed
        show "\<bar>fst (psi_local i z)\<bar> \<le> beta_cr i z + gamma_cr i z \<and>
            \<bar>snd (psi_local i z)\<bar> \<le> beta_cr i z + gamma_cr i z"
          using h1 h2 unfolding s_def by (by100 blast)
      qed
      \<comment> \<open>psi\_local i is continuous by squeeze: dist(psi\_local z, 0) = s(z) and s is continuous.\<close>
      \<comment> \<open>Also psi\_local(c) = (0,0), so dist(psi\_local z, psi\_local c) = s(z).\<close>
      \<comment> \<open>For z0 \<in> cone: dist(psi\_local z, psi\_local z0) \<le> dist(psi\_local z, 0) + dist(psi\_local z0, 0)
         = s(z) + s(z0). And s is continuous. So psi\_local is continuous.\<close>
      \<comment> \<open>Actually simpler: psi\_local maps to R^2, and each component is bounded by s.
         fst(psi\_local z) = s*cos \<theta> with |s*cos \<theta>| \<le> s. Similarly for snd.
         And s is continuous. So each component is squeezed, hence continuous.\<close>
      \<comment> \<open>psi\_local is continuous because each component = s*cos/sin(\<theta>).
         Away from s=0: \<theta> = 2\<pi>(i + \<gamma>/s)/n depends continuously on \<gamma> and s.
         At s=0: |component| \<le> s \<rightarrow> 0, so component \<rightarrow> 0 = psi\_local(c).
         We use: continuous\_on\_cases to split at s=0.\<close>
      \<comment> \<open>Define s as a function.\<close>
      define sf where "sf z = beta_cr i z + gamma_cr i z" for z
      have hsf_cont: "continuous_on (cone_set i) sf" unfolding sf_def using hs_cont by (by100 simp)
      \<comment> \<open>On {z \<in> cone | s > 0}: psi\_local is a composition of continuous functions.\<close>
      \<comment> \<open>On {z \<in> cone | s = 0} = {c}: psi\_local = (0,0), trivially continuous.\<close>
      \<comment> \<open>Both are closed in cone\_set, and agree on overlap (empty, since s>0 and s=0 disjoint).\<close>
      \<comment> \<open>Define the explicit formula matching psi\_local.\<close>
      define psi_explicit where "psi_explicit z =
          (sf z * cos (2*pi*(real i + (if sf z = 0 then 0 else gamma_cr i z / sf z))/real n),
           sf z * sin (2*pi*(real i + (if sf z = 0 then 0 else gamma_cr i z / sf z))/real n))" for z
      have hpsi_eq_explicit: "\<And>z. z \<in> cone_set i \<Longrightarrow> psi_local i z = psi_explicit z"
        unfolding psi_local_def Let_def sf_def psi_explicit_def by (by100 simp)
      \<comment> \<open>Transfer: psi\_local continuous iff psi\_explicit continuous.\<close>
      have "continuous_on (cone_set i) (psi_local i) = continuous_on (cone_set i) psi_explicit"
        by (rule continuous_on_cong) (by100 simp, rule hpsi_eq_explicit, assumption)
      \<comment> \<open>Now prove psi\_explicit is continuous.\<close>
      moreover have "continuous_on (cone_set i) psi_explicit"
      proof -
        \<comment> \<open>psi\_explicit = (sf * cos(\<theta>(sf,\<gamma>)), sf * sin(\<theta>(sf,\<gamma>))).
           Key insight: sf*cos(\<theta>) and sf*sin(\<theta>) are continuous because:
           - Away from sf=0: \<theta> is continuous (rational in sf, \<gamma>), cos/sin continuous.
           - At sf=0: |sf*cos| \<le> |sf| \<rightarrow> 0 and |sf*sin| \<le> |sf| \<rightarrow> 0.
           We prove each component continuous via continuous\_on\_tendsto\_compose.\<close>
        \<comment> \<open>Step 1: gamma\_cr continuous on cone\_set.\<close>
        have hg_eq: "gamma_cr i = (\<lambda>z::real\<times>real. ((vx i - cx) * (snd z - cy)
            - (vy i - cy) * (fst z - cx)) / Di i)"
          unfolding gamma_cr_def cross2_def by (rule ext) (by100 simp)
        have hg_cont: "continuous_on (cone_set i) (gamma_cr i)"
        proof -
          have "continuous_on UNIV (gamma_cr i)" unfolding hg_eq
            using hDi_ne by (intro continuous_intros) (by100 simp)+
          thus ?thesis using continuous_on_subset by (by100 blast)
        qed
        \<comment> \<open>Step 2: fst component = sf * cos(2\<pi>(i + if sf=0 then 0 else \<gamma>/sf)/n).\<close>
        \<comment> \<open>This equals sf * cos(2\<pi>i/n + 2\<pi>\<gamma>/(sf*n)) when sf\<noteq>0, and 0 when sf=0.\<close>
        \<comment> \<open>Rewrite: sf*cos(a + b*\<gamma>/sf) = sf*(cos a * cos(b*\<gamma>/sf) - sin a * sin(b*\<gamma>/sf))
           where a = 2\<pi>i/n, b = 2\<pi>/n.\<close>
        \<comment> \<open>This is getting complex. Use a simpler approach: each component of psi\_explicit
           is squeezed between -sf and sf, with sf continuous and sf(c) = 0.
           Since psi\_explicit(c) = (0,0), this gives continuity at c.
           Away from c (sf > 0), psi\_explicit is a composition of continuous functions.\<close>
        \<comment> \<open>Approach: split cone\_set into {c} and cone\_set - {c}, prove continuous on each,
           use closed\_Un pasting.\<close>
        have hc_in: "(cx, cy) \<in> cone_set i"
          unfolding cone_set_def in_cone_def beta_cr_def gamma_cr_def cross2_def by (by100 simp)
        have hsf_c: "sf (cx, cy) = 0" unfolding sf_def
          beta_cr_def gamma_cr_def cross2_def by (by100 simp)
        have hpe_c: "psi_explicit (cx, cy) = (0, 0)"
          unfolding psi_explicit_def using hsf_c by (by100 simp)
        \<comment> \<open>On cone\_set - {(cx,cy)}: sf > 0, so \<gamma>/sf is well-defined and continuous.\<close>
        have hcont_away: "continuous_on (cone_set i - {(cx, cy)}) psi_explicit"
        proof -
          have "\<And>z. z \<in> cone_set i - {(cx, cy)} \<Longrightarrow> sf z > 0"
          proof -
            fix z assume hz: "z \<in> cone_set i - {(cx, cy)}"
            hence hic: "in_cone i z" and hne: "z \<noteq> (cx, cy)"
              unfolding cone_set_def by (by100 simp)+
            have hb0: "beta_cr i z \<ge> 0" and hg0: "gamma_cr i z \<ge> 0"
              using hic unfolding in_cone_def by (by100 blast)+
            show "sf z > 0"
            proof (rule ccontr)
              assume "\<not> sf z > 0"
              hence "sf z = 0" unfolding sf_def using hb0 hg0 by (by100 linarith)
              hence "beta_cr i z = 0" "gamma_cr i z = 0"
                unfolding sf_def using hb0 hg0 by (by100 linarith)+
              hence "fst z = cx" "snd z = cy"
                using hCramer_x[OF hDi_ne, of z] hCramer_y[OF hDi_ne, of z] by (by100 simp)+
              hence "z = (cx, cy)" by (cases z) (by100 simp)
              thus False using hne by (by100 blast)
            qed
          qed
          hence hsf_pos: "\<And>z. z \<in> cone_set i - {(cx, cy)} \<Longrightarrow> sf z \<noteq> 0"
            by (by100 force)
          \<comment> \<open>On this set, if sf=0 branch is never taken, so psi\_explicit simplifies.\<close>
          have hpe_eq: "\<And>z. z \<in> cone_set i - {(cx, cy)} \<Longrightarrow>
              psi_explicit z = (sf z * cos (2*pi*(real i + gamma_cr i z / sf z)/real n),
                                sf z * sin (2*pi*(real i + gamma_cr i z / sf z)/real n))"
            unfolding psi_explicit_def using hsf_pos by (by100 simp)
          \<comment> \<open>This is a composition of continuous functions (sf, gamma\_cr, /, cos, sin, *).\<close>
          have "continuous_on (cone_set i - {(cx, cy)})
              (\<lambda>z. (sf z * cos (2*pi*(real i + gamma_cr i z / sf z)/real n),
                    sf z * sin (2*pi*(real i + gamma_cr i z / sf z)/real n)))"
          proof -
            have hsf_cont': "continuous_on (cone_set i - {(cx, cy)}) sf"
              using hsf_cont continuous_on_subset by (by100 blast)
            have hg_cont': "continuous_on (cone_set i - {(cx, cy)}) (gamma_cr i)"
              using hg_cont continuous_on_subset by (by100 blast)
            have "continuous_on (cone_set i - {(cx, cy)}) (\<lambda>z. gamma_cr i z / sf z)"
              using hsf_cont' hg_cont' hsf_pos by (intro continuous_intros) (by100 simp)+
            define theta_f where "theta_f z = 2*pi*(real i + gamma_cr i z / sf z)/real n" for z
            have hn_ne: "real n \<noteq> (0::real)" using hn by (by100 simp)
            have hgu_cont: "continuous_on (cone_set i - {(cx, cy)}) (\<lambda>z. gamma_cr i z / sf z)"
              apply (intro continuous_intros)
              using hg_cont' apply assumption
              using hsf_cont' apply assumption
              using hsf_pos apply (by100 blast)
              done
            have "continuous_on (cone_set i - {(cx, cy)}) theta_f"
              unfolding theta_f_def
              apply (intro continuous_intros)
              using hg_cont' apply assumption
              using hsf_cont' apply assumption
              using hsf_pos apply (by100 blast)
              using hn apply (by100 simp)
              done
            note hthf = \<open>continuous_on (cone_set i - {(cx, cy)}) theta_f\<close>
            have hcos_cont: "continuous_on (cone_set i - {(cx, cy)}) (\<lambda>z. cos (theta_f z))"
              using continuous_on_cos[OF hthf] .
            have hsin_cont: "continuous_on (cone_set i - {(cx, cy)}) (\<lambda>z. sin (theta_f z))"
              using continuous_on_sin[OF hthf] .
            have hfst_cont: "continuous_on (cone_set i - {(cx, cy)}) (\<lambda>z. sf z * cos (theta_f z))"
              apply (rule continuous_on_mult)
              using hsf_cont' apply assumption
              using hcos_cont apply assumption
              done
            have hsnd_cont: "continuous_on (cone_set i - {(cx, cy)}) (\<lambda>z. sf z * sin (theta_f z))"
              apply (rule continuous_on_mult)
              using hsf_cont' apply assumption
              using hsin_cont apply assumption
              done
            have "continuous_on (cone_set i - {(cx, cy)})
                (\<lambda>z. (sf z * cos (theta_f z), sf z * sin (theta_f z)))"
              apply (rule continuous_on_Pair)
              using hfst_cont apply assumption
              using hsnd_cont apply assumption
              done
            moreover have "\<And>z. z \<in> cone_set i - {(cx, cy)} \<Longrightarrow>
                (sf z * cos (theta_f z), sf z * sin (theta_f z)) =
                (sf z * cos (2*pi*(real i + gamma_cr i z / sf z)/real n),
                 sf z * sin (2*pi*(real i + gamma_cr i z / sf z)/real n))"
              unfolding theta_f_def by (by100 simp)
            ultimately show ?thesis
            proof -
              assume h1: "continuous_on (cone_set i - {(cx, cy)})
                  (\<lambda>z. (sf z * cos (theta_f z), sf z * sin (theta_f z)))"
              assume h2: "\<And>z. z \<in> cone_set i - {(cx, cy)} \<Longrightarrow>
                  (sf z * cos (theta_f z), sf z * sin (theta_f z)) =
                  (sf z * cos (2*pi*(real i + gamma_cr i z / sf z)/real n),
                   sf z * sin (2*pi*(real i + gamma_cr i z / sf z)/real n))"
              show ?thesis
                using continuous_on_cong[of "cone_set i - {(cx,cy)}" "cone_set i - {(cx,cy)}"
                  "\<lambda>z. (sf z * cos (theta_f z), sf z * sin (theta_f z))"
                  "\<lambda>z. (sf z * cos (2*pi*(real i + gamma_cr i z / sf z)/real n),
                       sf z * sin (2*pi*(real i + gamma_cr i z / sf z)/real n))"]
                h1 h2 by (by100 simp)
            qed
          qed
          thus ?thesis
            using continuous_on_cong[of "cone_set i - {(cx,cy)}" "cone_set i - {(cx,cy)}"
              "\<lambda>z. (sf z * cos (2*pi*(real i + gamma_cr i z / sf z)/real n),
                    sf z * sin (2*pi*(real i + gamma_cr i z / sf z)/real n))"
              psi_explicit] hpe_eq by (by5000 simp)
        qed
        \<comment> \<open>At {(cx,cy)}: trivially continuous (constant on singleton).\<close>
        have hcont_c: "continuous_on {(cx, cy)} psi_explicit"
          using hpe_c by (by100 simp)
        \<comment> \<open>Paste: cone\_set = (cone\_set - {c}) \<union> {c}.\<close>
        have "cone_set i = (cone_set i - {(cx, cy)}) \<union> {(cx, cy)}"
          using hc_in by (by100 blast)
        \<comment> \<open>Both pieces are subsets of cone\_set, which is closed, so they
           may not be closed themselves. Use a different approach.\<close>
        \<comment> \<open>Actually: use the squeeze/metric approach directly.
           For continuity at (cx,cy): |fst(psi\_explicit z)| \<le> sf z and sf continuous,
           sf(cx,cy) = 0, psi\_explicit(cx,cy) = (0,0).
           For continuity at z0 \<noteq> c: already proved in hcont\_away.\<close>
        \<comment> \<open>Continuity of psi\_explicit on cone\_set i:
           Away from c: by hcont\_away.
           At c: squeeze using |component| \<le> sf and sf continuous with sf(c) = 0.\<close>
        \<comment> \<open>Apply squeeze lemma.\<close>
        have hbound': "\<And>z. z \<in> cone_set i \<Longrightarrow>
            \<bar>fst (psi_explicit z)\<bar> \<le> sf z \<and> \<bar>snd (psi_explicit z)\<bar> \<le> sf z"
        proof -
          fix z assume "z \<in> cone_set i"
          from hcomp_bound[OF this] hpsi_eq_explicit[OF this]
          show "\<bar>fst (psi_explicit z)\<bar> \<le> sf z \<and> \<bar>snd (psi_explicit z)\<bar> \<le> sf z"
            unfolding sf_def by (by100 simp)
        qed
        have hg_nn: "\<And>z. z \<in> cone_set i \<Longrightarrow> sf z \<ge> 0"
        proof -
          fix z assume "z \<in> cone_set i"
          hence "in_cone i z" unfolding cone_set_def by (by100 simp)
          thus "sf z \<ge> 0" unfolding sf_def in_cone_def by (by100 linarith)
        qed
        show ?thesis
          using continuous_on_squeeze_at_point[OF hc_in hpe_c hsf_cont hsf_c hbound' hg_nn hcont_away] .
      qed
      ultimately show "continuous_on (cone_set i) (psi_local i)" by (by100 simp)
    qed
    have h\<psi>_cont_cone: "\<And>i. i < n \<Longrightarrow> continuous_on (cone_set i) \<psi>"
    proof -
      fix i :: nat assume hi: "i < n"
      have hag: "\<And>z. z \<in> cone_set i \<Longrightarrow> \<psi> z = psi_local i z"
        using hpsi_eq[OF hi] unfolding cone_set_def by (by100 simp)
      have "continuous_on (cone_set i) (psi_local i)"
        using hpsi_local_cont[OF hi] .
      have hag': "\<And>z. z \<in> cone_set i \<Longrightarrow> psi_local i z = \<psi> z"
        using hag by (by100 simp)
      have "continuous_on (cone_set i) (psi_local i) = continuous_on (cone_set i) \<psi>"
        by (rule continuous_on_cong) (by100 simp, rule hag', assumption)
      thus "continuous_on (cone_set i) \<psi>"
        using \<open>continuous_on (cone_set i) (psi_local i)\<close> by (by100 simp)
    qed
    have h\<psi>_cont: "continuous_on P \<psi>"
    proof -
      have "continuous_on (\<Union>i\<in>{..<n}. cone_set i) \<psi>"
      proof (rule continuous_on_closed_Union)
        show "finite ({..<n}::nat set)" by (by100 simp)
      next
        fix i assume "i \<in> {..<n}" thus "closed (cone_set i)" using hcone_closed by (by100 simp)
      next
        fix i assume "i \<in> {..<n}" thus "continuous_on (cone_set i) \<psi>"
          using h\<psi>_cont_cone by (by100 simp)
      qed
      thus ?thesis using hcone_cover by (rule continuous_on_subset)
    qed
    \<comment> \<open>(d) \<psi> surjective: \<psi> ` P = B2.\<close>
    \<comment> \<open>Helper: psi_local image is in B2.\<close>
    have hpsi_local_B2: "\<And>i z. i < n \<Longrightarrow> in_cone i z \<Longrightarrow> psi_local i z \<in> top1_B2"
    proof -
      fix i :: nat and z :: "real \<times> real"
      assume hi: "i < n" and hic: "in_cone i z"
      have hb: "beta_cr i z \<ge> 0" and hg: "gamma_cr i z \<ge> 0"
          and hbg: "beta_cr i z + gamma_cr i z \<le> 1"
        using hic unfolding in_cone_def by (by100 blast)+
      define s where "s = beta_cr i z + gamma_cr i z"
      have hs0: "s \<ge> 0" unfolding s_def using hb hg by (by100 linarith)
      have hs1: "s \<le> 1" unfolding s_def using hbg .
      define u where "u = (if s = 0 then 0 else gamma_cr i z / s)"
      define \<theta> where "\<theta> = 2 * pi * (real i + u) / real n"
      have "psi_local i z = (s * cos \<theta>, s * sin \<theta>)"
        unfolding psi_local_def Let_def s_def u_def \<theta>_def by (by100 simp)
      moreover have "fst (s * cos \<theta>, s * sin \<theta>) ^ 2 + snd (s * cos \<theta>, s * sin \<theta>) ^ 2 \<le> 1"
      proof -
        have h1: "(s * cos \<theta>) ^ 2 + (s * sin \<theta>) ^ 2 = s ^ 2"
        proof -
          have "(s * cos \<theta>) ^ 2 = s ^ 2 * (cos \<theta>) ^ 2"
            using power_mult_distrib by (by100 blast)
          moreover have "(s * sin \<theta>) ^ 2 = s ^ 2 * (sin \<theta>) ^ 2"
            using power_mult_distrib by (by100 blast)
          moreover have "s ^ 2 * (cos \<theta>) ^ 2 + s ^ 2 * (sin \<theta>) ^ 2 = s ^ 2"
          proof -
            have "s ^ 2 * (cos \<theta>) ^ 2 + s ^ 2 * (sin \<theta>) ^ 2 =
                s ^ 2 * ((cos \<theta>) ^ 2 + (sin \<theta>) ^ 2)"
              using distrib_left[of "s^2" "(cos \<theta>)^2" "(sin \<theta>)^2"] by (by100 simp)
            thus ?thesis by (by100 simp)
          qed
          ultimately show ?thesis by (by100 simp)
        qed
        have "s * s \<le> 1 * 1"
          using mult_mono[of s 1 s 1] hs0 hs1 by (by100 linarith)
        hence "s ^ 2 \<le> 1" using power2_eq_square[of s] by (by100 simp)
        thus ?thesis using h1 by (by100 simp)
      qed
      ultimately show "psi_local i z \<in> top1_B2" unfolding top1_B2_def by (by100 simp)
    qed
    \<comment> \<open>Helper: Cramer coords of interior point (1-s)*c + \<beta>*v_i + \<gamma>*v_{i+1}.\<close>
    have hCramer_interior: "\<And>i \<beta> \<gamma>. i < n \<Longrightarrow> \<beta> \<ge> 0 \<Longrightarrow> \<gamma> \<ge> 0 \<Longrightarrow> \<beta> + \<gamma> \<le> 1 \<Longrightarrow>
        beta_cr i ((1-\<beta>-\<gamma>)*cx + \<beta>*vx i + \<gamma>*vx(Suc i mod n),
                   (1-\<beta>-\<gamma>)*cy + \<beta>*vy i + \<gamma>*vy(Suc i mod n)) = \<beta> \<and>
        gamma_cr i ((1-\<beta>-\<gamma>)*cx + \<beta>*vx i + \<gamma>*vx(Suc i mod n),
                    (1-\<beta>-\<gamma>)*cy + \<beta>*vy i + \<gamma>*vy(Suc i mod n)) = \<gamma>"
    proof -
      fix i :: nat and \<beta> \<gamma> :: real
      assume hi: "i < n" and hb0: "\<beta> \<ge> 0" and hg0: "\<gamma> \<ge> 0" and hbg: "\<beta> + \<gamma> \<le> 1"
      define x where "x = ((1-\<beta>-\<gamma>)*cx + \<beta>*vx i + \<gamma>*vx(Suc i mod n),
                           (1-\<beta>-\<gamma>)*cy + \<beta>*vy i + \<gamma>*vy(Suc i mod n))"
      have hDi: "Di i > 0" using hDi_pos[OF hi] .
      have hDi_ne: "Di i \<noteq> 0" using hDi by (by100 linarith)
      \<comment> \<open>x - c = \<beta>*(v_i - c) + \<gamma>*(v_{i+1} - c)\<close>
      have hfst: "fst x - cx = \<beta>*(vx i - cx) + \<gamma>*(vx(Suc i mod n) - cx)"
        unfolding x_def by (simp add: algebra_simps)
      have hsnd: "snd x - cy = \<beta>*(vy i - cy) + \<gamma>*(vy(Suc i mod n) - cy)"
        unfolding x_def by (simp add: algebra_simps)
      have hcross_Di: "cross2 (vx i - cx, vy i - cy) (vx(Suc i mod n) - cx, vy(Suc i mod n) - cy) = Di i"
        unfolding Di_def cross2_def by (by100 simp)
      have hcross_b: "cross2 (fst x - cx, snd x - cy) (vx(Suc i mod n) - cx, vy(Suc i mod n) - cy) = \<beta> * Di i"
      proof -
        have "cross2 (fst x - cx, snd x - cy) (vx(Suc i mod n) - cx, vy(Suc i mod n) - cy) =
            \<beta> * cross2 (vx i - cx, vy i - cy) (vx(Suc i mod n) - cx, vy(Suc i mod n) - cy)"
          unfolding cross2_def hfst hsnd by (simp add: algebra_simps)
        thus ?thesis using hcross_Di by (by100 simp)
      qed
      have hbeta: "beta_cr i x = \<beta>"
      proof -
        have "beta_cr i x = cross2 (fst x - cx, snd x - cy) (vx(Suc i mod n) - cx, vy(Suc i mod n) - cy) / Di i"
          unfolding beta_cr_def by (by100 simp)
        also have "\<dots> = \<beta> * Di i / Di i" using hcross_b by (by100 simp)
        also have "\<dots> = \<beta>" using hDi_ne by (by100 simp)
        finally show ?thesis .
      qed
      have hcross_g: "cross2 (vx i - cx, vy i - cy) (fst x - cx, snd x - cy) = \<gamma> * Di i"
      proof -
        have "cross2 (vx i - cx, vy i - cy) (fst x - cx, snd x - cy) =
            \<gamma> * cross2 (vx i - cx, vy i - cy) (vx(Suc i mod n) - cx, vy(Suc i mod n) - cy)"
          unfolding cross2_def hfst hsnd by (simp add: algebra_simps)
        thus ?thesis using hcross_Di by (by100 simp)
      qed
      have hgamma: "gamma_cr i x = \<gamma>"
      proof -
        have "gamma_cr i x = cross2 (vx i - cx, vy i - cy) (fst x - cx, snd x - cy) / Di i"
          unfolding gamma_cr_def by (by100 simp)
        also have "\<dots> = \<gamma> * Di i / Di i" using hcross_g by (by100 simp)
        also have "\<dots> = \<gamma>" using hDi_ne by (by100 simp)
        finally show ?thesis .
      qed
      show "beta_cr i x = \<beta> \<and> gamma_cr i x = \<gamma>"
        using hbeta hgamma by (by100 blast)
    qed
    have h\<psi>_surj: "\<psi> ` P = top1_B2"
    proof (rule set_eqI, rule iffI)
      \<comment> \<open>\<subseteq>: image in B2.\<close>
      fix y assume "y \<in> \<psi> ` P"
      then obtain z where hz: "z \<in> P" and hy: "y = \<psi> z" by (by100 blast)
      from hP_cones hz obtain i where hi: "i < n" and hic: "in_cone i z" by (by100 blast)
      have "\<psi> z = psi_local i z" using hpsi_eq[OF hi hic] .
      moreover have "psi_local i z \<in> top1_B2" using hpsi_local_B2[OF hi hic] .
      ultimately show "y \<in> top1_B2" using hy by (by100 simp)
    next
      \<comment> \<open>\<supseteq>: every point in B2 has a preimage.\<close>
      fix y assume hy_B2: "y \<in> top1_B2"
      hence hy_le: "fst y ^ 2 + snd y ^ 2 \<le> 1" unfolding top1_B2_def by (by100 simp)
      show "y \<in> \<psi> ` P"
      proof (cases "y = (0, 0)")
        case True
        have "\<psi> (cx, cy) = (0, 0)"
        proof -
          have "in_cone 0 (cx, cy)"
            unfolding in_cone_def beta_cr_def gamma_cr_def cross2_def by (by100 simp)
          moreover have "(0::nat) < n" using hn by (by100 linarith)
          ultimately have "\<psi> (cx, cy) = psi_local 0 (cx, cy)" using hpsi_eq by (by100 blast)
          also have "\<dots> = (0, 0)" using hpsi_local_c by (by100 simp)
          finally show ?thesis .
        qed
        moreover have "(cx, cy) \<in> P" using hc_in_P hc_eq by (by100 simp)
        ultimately have "\<psi> (cx, cy) = y \<and> (cx, cy) \<in> P" using True by (by100 simp)
        thus ?thesis by (by100 blast)
      next
        case hne: False
        \<comment> \<open>y \<noteq> 0. Use angle decomposition like boundary proof but with r = |y| \<le> 1.\<close>
        define r where "r = sqrt (fst y ^ 2 + snd y ^ 2)"
        have hr_pos: "r > 0" unfolding r_def
        proof -
          have "fst y ^ 2 + snd y ^ 2 > 0"
          proof (rule ccontr)
            assume "\<not> fst y ^ 2 + snd y ^ 2 > 0"
            hence hle: "fst y ^ 2 + snd y ^ 2 \<le> 0" by (by100 linarith)
            have "fst y ^ 2 \<ge> 0" by (by100 simp)
            moreover have "snd y ^ 2 \<ge> 0" by (by100 simp)
            ultimately have "fst y ^ 2 = 0" "snd y ^ 2 = 0" using hle by (by100 linarith)+
            hence "fst y * fst y = 0" "snd y * snd y = 0"
              using power2_eq_square by (by100 simp)+
            hence "fst y = 0 \<and> snd y = 0" by (by100 simp)
            hence "y = (0, 0)" by (cases y) (by100 simp)
            thus False using hne by (by100 blast)
          qed
          thus "sqrt (fst y ^ 2 + snd y ^ 2) > 0" by (by100 simp)
        qed
        have hr_le1: "r \<le> 1" unfolding r_def using hy_le by (by100 simp)
        \<comment> \<open>(fst y / r, snd y / r) is on S1.\<close>
        have hunit: "(fst y / r) ^ 2 + (snd y / r) ^ 2 = 1"
        proof -
          have hr2: "r ^ 2 = fst y ^ 2 + snd y ^ 2" unfolding r_def by (by5000 simp)
          have hrne: "r \<noteq> 0" using hr_pos by (by100 linarith)
          have "(fst y / r) ^ 2 = fst y ^ 2 / r ^ 2"
            using power_divide[of "fst y" r 2] by (by100 simp)
          moreover have "(snd y / r) ^ 2 = snd y ^ 2 / r ^ 2"
            using power_divide[of "snd y" r 2] by (by100 simp)
          ultimately have "(fst y / r) ^ 2 + (snd y / r) ^ 2 = fst y ^ 2 / r ^ 2 + snd y ^ 2 / r ^ 2"
            by (by100 simp)
          also have "\<dots> = (fst y ^ 2 + snd y ^ 2) / r ^ 2"
            using add_divide_distrib[of "fst y ^ 2" "snd y ^ 2" "r ^ 2"]
            by (by100 simp)
          also have "\<dots> = r ^ 2 / r ^ 2" using hr2 by (by100 simp)
          also have "\<dots> = 1" using hrne by (by100 simp)
          finally show ?thesis .
        qed
        \<comment> \<open>Find angle \<phi> for unit direction (fst y/r, snd y/r) and sector.\<close>
        define a where "a = fst y / r"
        define b where "b = snd y / r"
        have ha_bound: "-1 \<le> a" "a \<le> 1"
        proof -
          have "b ^ 2 \<ge> 0" by (by100 simp)
          hence "a ^ 2 \<le> 1" using hunit unfolding a_def b_def by (by100 linarith)
          hence "a * a \<le> 1" using power2_eq_square[of a] by (by100 simp)
          show "a \<le> 1"
          proof (rule ccontr)
            assume "\<not> a \<le> 1" hence "a > 1" by (by100 simp)
            have "a * 1 < a * a"
              using mult_strict_left_mono[of 1 a a] \<open>a > 1\<close> by (by100 linarith)
            thus False using \<open>a * a \<le> 1\<close> \<open>a > 1\<close> by (by100 linarith)
          qed
          show "-1 \<le> a"
          proof (rule ccontr)
            assume "\<not> -1 \<le> a" hence "a < -1" by (by100 simp)
            hence "(-a) > 1" by (by100 linarith)
            have "(-a) * 1 < (-a) * (-a)"
              using mult_strict_left_mono[of 1 "- a" "-a"] \<open>(-a) > 1\<close> by (by100 linarith)
            hence "- a < (- a) * (- a)" by (by100 simp)
            hence "a * a > 1" using \<open>(-a) > 1\<close> by (by100 linarith)
            thus False using \<open>a * a \<le> 1\<close> by (by100 linarith)
          qed
        qed
        \<comment> \<open>Find angle \<phi> with cos \<phi> = a, sin \<phi> = b.\<close>
        define \<phi> where "\<phi> = (if b \<ge> 0 then arccos a else 2*pi - arccos a)"
        have hcos_\<phi>: "cos \<phi> = a"
        proof (cases "b \<ge> 0")
          case True thus ?thesis unfolding \<phi>_def using cos_arccos[OF ha_bound(1) ha_bound(2)] by (by100 simp)
        next
          case False thus ?thesis unfolding \<phi>_def using cos_arccos[OF ha_bound(1) ha_bound(2)] by (by100 simp)
        qed
        have hab_unit: "a ^ 2 + b ^ 2 = 1"
          using hunit unfolding a_def b_def .
        have hsin_\<phi>: "sin \<phi> = b"
        proof (cases "b \<ge> 0")
          case True
          have "sin (arccos a) = sqrt (1 - a ^ 2)"
            using sin_arccos[OF ha_bound(1) ha_bound(2)] by (by100 simp)
          also have "\<dots> = sqrt (b ^ 2)"
          proof -
            have "1 - a ^ 2 = b ^ 2" using hab_unit by (by100 linarith)
            thus ?thesis by (by100 simp)
          qed
          also have "\<dots> = \<bar>b\<bar>" using real_sqrt_abs by (by100 blast)
          also have "\<dots> = b" using True by (by100 simp)
          finally show ?thesis unfolding \<phi>_def using True by (by100 simp)
        next
          case False
          have "sin (2*pi - arccos a) = - sin (arccos a)"
            using sin_diff by (by5000 simp)
          also have "sin (arccos a) = sqrt (1 - a ^ 2)"
            using sin_arccos[OF ha_bound(1) ha_bound(2)] by (by100 simp)
          also have "sqrt (1 - a ^ 2) = sqrt (b ^ 2)"
          proof -
            have "1 - a ^ 2 = b ^ 2" using hab_unit by (by100 linarith)
            thus ?thesis by (by100 simp)
          qed
          also have "\<dots> = \<bar>b\<bar>" using real_sqrt_abs by (by100 blast)
          finally have "sin (2*pi - arccos a) = - \<bar>b\<bar>" by (by100 simp)
          also have "- \<bar>b\<bar> = b" using False by (by100 simp)
          finally have "sin (2*pi - arccos a) = b" .
          moreover have "\<phi> = 2*pi - arccos a" unfolding \<phi>_def using False by (by100 simp)
          ultimately show ?thesis by (by100 simp)
        qed
        have h\<phi>_ge: "0 \<le> \<phi>"
        proof (cases "b \<ge> 0")
          case True thus ?thesis unfolding \<phi>_def using arccos_lbound[OF ha_bound(1) ha_bound(2)] by (by100 simp)
        next
          case False
          have "\<phi> = 2*pi - arccos a" unfolding \<phi>_def using False by (by100 simp)
          moreover have "arccos a \<le> pi" using arccos_ubound[OF ha_bound(1) ha_bound(2)] .
          ultimately show ?thesis using pi_gt_zero by (by100 linarith)
        qed
        have h\<phi>_lt: "\<phi> < 2*pi"
        proof (cases "b \<ge> 0")
          case True
          have "\<phi> = arccos a" unfolding \<phi>_def using True by (by100 simp)
          moreover have "arccos a \<le> pi" using arccos_ubound[OF ha_bound(1) ha_bound(2)] .
          ultimately show ?thesis using pi_gt_zero by (by100 linarith)
        next
          case False
          have "0 < arccos a"
          proof -
            have "a < 1"
            proof (rule ccontr)
              assume "\<not> a < 1" hence ha1: "a = 1" using ha_bound(2) by (by100 linarith)
              hence "a ^ 2 = 1" by (by100 simp)
              hence "b ^ 2 = 0" using hab_unit by (by100 linarith)
              hence "b * b = 0" using power2_eq_square[of b] by (by100 simp)
              hence "b = 0" by (by100 simp)
              thus False using False by (by100 linarith)
            qed
            moreover have "- 1 < a"
            proof (rule ccontr)
              assume "\<not> - 1 < a" hence "a = - 1" using ha_bound(1) by (by100 linarith)
              hence "a ^ 2 = 1" by (by100 simp)
              hence "b ^ 2 = 0" using hab_unit by (by100 linarith)
              hence "b * b = 0" using power2_eq_square[of b] by (by100 simp)
              hence "b = 0" by (by100 simp)
              thus False using False by (by100 linarith)
            qed
            ultimately show ?thesis using arccos_lt_bounded by (by100 blast)
          qed
          have "\<phi> = 2*pi - arccos a" unfolding \<phi>_def using False by (by100 simp)
          thus ?thesis using \<open>0 < arccos a\<close> by (by100 linarith)
        qed
        \<comment> \<open>Find sector i with \<phi> \<in> [2\<pi>i/n, 2\<pi>(i+1)/n).\<close>
        define i where "i = nat \<lfloor>\<phi> * real n / (2*pi)\<rfloor>"
        have hn_pos: "real n > 0" using hn by (by100 simp)
        have h2pi_pos: "2*pi > 0" using pi_gt_zero by (by100 linarith)
        have hi: "i < n"
        proof -
          have "\<phi> * real n / (2*pi) < real n" using h\<phi>_lt h2pi_pos hn_pos
            by (simp add: field_simps)
          hence "\<lfloor>\<phi> * real n / (2*pi)\<rfloor> < real n"
            by (by100 linarith)
          moreover have "0 \<le> \<phi> * real n / (2*pi)" using h\<phi>_ge hn_pos h2pi_pos
            by (by100 simp)
          hence "0 \<le> \<lfloor>\<phi> * real n / (2*pi)\<rfloor>" by (by100 linarith)
          ultimately show ?thesis unfolding i_def by (by100 linarith)
        qed
        define t where "t = \<phi> * real n / (2*pi) - real i"
        have ht0: "0 \<le> t"
        proof -
          have hval_ge: "\<phi> * real n / (2*pi) \<ge> 0" using h\<phi>_ge hn_pos h2pi_pos by (by100 simp)
          have "real i = real (nat \<lfloor>\<phi> * real n / (2*pi)\<rfloor>)" unfolding i_def by (by100 simp)
          also have "\<dots> = \<lfloor>\<phi> * real n / (2*pi)\<rfloor>"
            using hval_ge by (by100 simp)
          also have "\<dots> \<le> \<phi> * real n / (2*pi)" using of_int_floor_le by (by100 simp)
          finally have "real i \<le> \<phi> * real n / (2*pi)" .
          thus ?thesis unfolding t_def by (by100 linarith)
        qed
        have ht1: "t < 1"
        proof -
          have "\<phi> * real n / (2*pi) < real i + 1"
          proof -
            have "\<lfloor>\<phi> * real n / (2*pi)\<rfloor> < real i + 1"
            proof -
              have "0 \<le> \<phi> * real n / (2*pi)" using h\<phi>_ge hn_pos h2pi_pos by (by100 simp)
              hence "0 \<le> \<lfloor>\<phi> * real n / (2*pi)\<rfloor>" by (by100 linarith)
              hence "real (nat \<lfloor>\<phi> * real n / (2*pi)\<rfloor>) = \<lfloor>\<phi> * real n / (2*pi)\<rfloor>"
                by (by100 simp)
              thus ?thesis unfolding i_def by (by100 linarith)
            qed
            moreover have "\<phi> * real n / (2*pi) < \<lfloor>\<phi> * real n / (2*pi)\<rfloor> + 1"
              by linarith
            ultimately show ?thesis unfolding i_def
              by (by100 linarith)
          qed
          thus ?thesis unfolding t_def by (by100 linarith)
        qed
        have h\<phi>_eq: "\<phi> = 2*pi*(real i + t)/real n" unfolding t_def
          using h2pi_pos hn_pos by (simp add: field_simps)
        \<comment> \<open>Construct preimage: z = (1-r)*c + r*xb = (1-r)*c + r*((1-t)*v_i + t*v_{i+1}).\<close>
        define \<beta> where "\<beta> = r * (1 - t)"
        define \<gamma> where "\<gamma> = r * t"
        have hb0: "\<beta> \<ge> 0" unfolding \<beta>_def using hr_pos ht0 ht1
          using mult_nonneg_nonneg[of r "1-t"] by (by100 linarith)
        have hg0: "\<gamma> \<ge> 0" unfolding \<gamma>_def using hr_pos ht0 by (by100 simp)
        have hbg: "\<beta> + \<gamma> = r" unfolding \<beta>_def \<gamma>_def by (simp add: algebra_simps)
        have hbg1: "\<beta> + \<gamma> \<le> 1" using hbg hr_le1 by (by100 linarith)
        define z where "z = ((1-\<beta>-\<gamma>)*cx + \<beta>*vx i + \<gamma>*vx(Suc i mod n),
                             (1-\<beta>-\<gamma>)*cy + \<beta>*vy i + \<gamma>*vy(Suc i mod n))"
        have ht1': "t \<le> 1" using ht1 by (by100 linarith)
        \<comment> \<open>z \<in> P: z = (1-\<beta>-\<gamma>)*c + \<beta>*v_i + \<gamma>*v_{i+1} is a convex combination of vertices.\<close>
        have hz_P: "z \<in> P"
        proof -
          define coeffs where "coeffs = (\<lambda>j. (1 - \<beta> - \<gamma>) / real n
              + (if j = i then \<beta> else 0)
              + (if j = Suc i mod n then \<gamma> else 0))"
          have hi2: "Suc i mod n < n" using hi assms(2) by (by100 simp)
          have hi_ne: "i \<noteq> Suc i mod n"
          proof (cases "Suc i < n")
            case True thus ?thesis by (by100 simp)
          next
            case False
            hence "Suc i = n" using hi by (by100 linarith)
            hence "Suc i mod n = 0" by (by100 simp)
            moreover have "i > 0 \<or> i = 0" by (by100 linarith)
            ultimately show ?thesis using hi \<open>Suc i = n\<close> assms(2) by (by100 linarith)
          qed
          have hbg_le: "1 - \<beta> - \<gamma> \<ge> 0" using hbg1 by (by100 linarith)
          have hcge: "\<forall>j<n. coeffs j \<ge> 0"
          proof (intro allI impI)
            fix j assume "j < n"
            have "(1 - \<beta> - \<gamma>) / real n \<ge> 0" using hbg_le hn by (by100 simp)
            moreover have "(if j = i then \<beta> else 0) \<ge> 0" using hb0 by (by100 simp)
            moreover have "(if j = Suc i mod n then \<gamma> else 0) \<ge> 0" using hg0 by (by100 simp)
            ultimately show "coeffs j \<ge> 0" unfolding coeffs_def by (by100 linarith)
          qed
          have hfin: "finite ({..<n}::nat set)" by (by100 simp)
          have hi_in: "i \<in> {..<n}" using hi by (by100 simp)
          have hi2_in: "Suc i mod n \<in> {..<n}" using hi2 by (by100 simp)
          have hcsum: "(\<Sum>j<n. coeffs j) = 1"
          proof -
            have "(\<Sum>j<n. coeffs j) = (\<Sum>j<n. (1 - \<beta> - \<gamma>) / real n)
                + (\<Sum>j<n. (if j = i then \<beta> else 0))
                + (\<Sum>j<n. (if j = Suc i mod n then \<gamma> else 0))"
              unfolding coeffs_def by (simp add: sum.distrib)
            also have "(\<Sum>j<n. (1 - \<beta> - \<gamma>) / real n) = (1 - \<beta> - \<gamma>)"
              using hn by (by100 simp)
            also have "(\<Sum>j<n. (if j = i then \<beta> else 0)) = \<beta>"
              using hi by (by100 simp)
            also have "(\<Sum>j<n. (if j = Suc i mod n then \<gamma> else 0)) = \<gamma>"
              using hi2 by (by100 simp)
            finally show ?thesis by (by100 simp)
          qed
          have hcvx: "(\<Sum>j<n. coeffs j * vx j) = fst z"
          proof -
            have "(\<Sum>j<n. coeffs j * vx j) = (\<Sum>j<n. ((1 - \<beta> - \<gamma>) / real n) * vx j)
                + (\<Sum>j<n. (if j = i then \<beta> else 0) * vx j)
                + (\<Sum>j<n. (if j = Suc i mod n then \<gamma> else 0) * vx j)"
              unfolding coeffs_def by (simp add: sum.distrib algebra_simps)
            also have "(\<Sum>j<n. ((1 - \<beta> - \<gamma>) / real n) * vx j) = (1 - \<beta> - \<gamma>) / real n * (\<Sum>j<n. vx j)"
              by (simp add: sum_distrib_left)
            also have "\<dots> = (1 - \<beta> - \<gamma>) * cx"
              unfolding cx_def using hn by (simp add: field_simps)
            also have "(\<Sum>j<n. (if j = i then \<beta> else 0) * vx j) = \<beta> * vx i"
            proof -
              have "(\<Sum>j<n. (if j = i then \<beta> else 0) * vx j) = (\<Sum>j\<in>{..<n}. (if j = i then \<beta> * vx j else 0))"
                by (rule sum.cong) (by100 simp)+
              also have "\<dots> = \<beta> * vx i" using hi by (by100 simp)
              finally show ?thesis .
            qed
            also have "(\<Sum>j<n. (if j = Suc i mod n then \<gamma> else 0) * vx j) = \<gamma> * vx (Suc i mod n)"
            proof -
              have "(\<Sum>j<n. (if j = Suc i mod n then \<gamma> else 0) * vx j) = (\<Sum>j\<in>{..<n}. (if j = Suc i mod n then \<gamma> * vx j else 0))"
                by (rule sum.cong) (by100 simp)+
              also have "\<dots> = \<gamma> * vx (Suc i mod n)" using hi2 by (by100 simp)
              finally show ?thesis .
            qed
            finally show ?thesis unfolding z_def by (by100 simp)
          qed
          have hcvy: "(\<Sum>j<n. coeffs j * vy j) = snd z"
          proof -
            have hsplit: "(\<Sum>j<n. coeffs j * vy j) = (\<Sum>j<n. ((1 - \<beta> - \<gamma>) / real n) * vy j)
                + (\<Sum>j<n. (if j = i then \<beta> else 0) * vy j)
                + (\<Sum>j<n. (if j = Suc i mod n then \<gamma> else 0) * vy j)"
              unfolding coeffs_def by (simp add: sum.distrib algebra_simps)
            have hterm1: "(\<Sum>j<n. ((1 - \<beta> - \<gamma>) / real n) * vy j) = (1 - \<beta> - \<gamma>) * cy"
            proof -
              have "(\<Sum>j<n. ((1 - \<beta> - \<gamma>) / real n) * vy j) = (1 - \<beta> - \<gamma>) / real n * (\<Sum>j<n. vy j)"
                by (simp add: sum_distrib_left)
              thus ?thesis unfolding cy_def using hn by (simp add: field_simps)
            qed
            have hterm2: "(\<Sum>j<n. (if j = i then \<beta> else 0) * vy j) = \<beta> * vy i"
            proof -
              have "(\<Sum>j<n. (if j = i then \<beta> else 0) * vy j) = (\<Sum>j\<in>{..<n}. (if j = i then \<beta> * vy j else 0))"
                by (rule sum.cong) (by100 simp)+
              also have "\<dots> = \<beta> * vy i" using hi by (by100 simp)
              finally show ?thesis .
            qed
            have hterm3: "(\<Sum>j<n. (if j = Suc i mod n then \<gamma> else 0) * vy j) = \<gamma> * vy (Suc i mod n)"
            proof -
              have "(\<Sum>j<n. (if j = Suc i mod n then \<gamma> else 0) * vy j) = (\<Sum>j\<in>{..<n}. (if j = Suc i mod n then \<gamma> * vy j else 0))"
                by (rule sum.cong) (by100 simp)+
              also have "\<dots> = \<gamma> * vy (Suc i mod n)" using hi2 by (by100 simp)
              finally show ?thesis .
            qed
            show ?thesis using hsplit hterm1 hterm2 hterm3 unfolding z_def by (by100 simp)
          qed
          have hfst_z: "fst z = (\<Sum>j<n. coeffs j * vx j)" using hcvx by (by100 simp)
          have hsnd_z: "snd z = (\<Sum>j<n. coeffs j * vy j)" using hcvy by (by100 simp)
          obtain zx zy where hzxy: "z = (zx, zy)" by (cases z) (by100 blast)
          have hzx: "zx = (\<Sum>j<n. coeffs j * vx j)" using hfst_z hzxy by (by100 simp)
          have hzy: "zy = (\<Sum>j<n. coeffs j * vy j)" using hsnd_z hzxy by (by100 simp)
          have "(zx, zy) \<in> P" unfolding hP_hull mem_Collect_eq
          proof (intro exI conjI)
            show "(zx, zy) = ((\<Sum>j<n. coeffs j * vx j), (\<Sum>j<n. coeffs j * vy j))"
              using hzx hzy by (by100 simp)
            show "\<forall>j<n. (0::real) \<le> coeffs j" using hcge by (by100 blast)
            show "sum coeffs {..<n} = (1::real)" using hcsum by (by100 blast)
            show "(\<Sum>j<n. coeffs j * vx j) = (\<Sum>j<n. coeffs j * vx j)" by (by100 simp)
            show "(\<Sum>j<n. coeffs j * vy j) = (\<Sum>j<n. coeffs j * vy j)" by (by100 simp)
          qed
          thus ?thesis using hzxy by (by100 simp)
        qed
        \<comment> \<open>Cramer coords: beta_cr i z = \<beta>, gamma_cr i z = \<gamma>.\<close>
        from hCramer_interior[OF hi hb0 hg0 hbg1]
        have hbc: "beta_cr i z = \<beta>" and hgc: "gamma_cr i z = \<gamma>"
          unfolding z_def by (by100 blast)+
        have hic: "in_cone i z"
          unfolding in_cone_def using hbc hgc hb0 hg0 hbg1 by (by100 linarith)
        \<comment> \<open>Compute \<psi>(z).\<close>
        have hpsi_z: "\<psi> z = psi_local i z" using hpsi_eq[OF hi hic] .
        \<comment> \<open>psi_local i z = (r*cos \<phi>, r*sin \<phi>).\<close>
        have hpsi_z_eq: "psi_local i z = (r * cos \<phi>, r * sin \<phi>)"
        proof -
          have hs_val: "beta_cr i z + gamma_cr i z = r" using hbc hgc hbg by (by100 simp)
          have hrne: "r \<noteq> 0" using hr_pos by (by100 linarith)
          have hu_val: "(if r = 0 then 0 else \<gamma> / r) = t"
            unfolding \<gamma>_def using hrne by (by100 simp)
          have hgu: "gamma_cr i z / r = t" using hgc \<gamma>_def hrne by (by100 simp)
          have "psi_local i z = (r * cos (2*pi*(real i + t)/real n), r * sin (2*pi*(real i + t)/real n))"
            unfolding psi_local_def Let_def using hbc hgc hs_val hgu hrne by (by100 simp)
          thus ?thesis using h\<phi>_eq by (by100 simp)
        qed
        \<comment> \<open>\<psi>(z) = (r*cos \<phi>, r*sin \<phi>) = (r*a, r*b) = (fst y, snd y) = y.\<close>
        have "\<psi> z = (r * a, r * b)"
          using hpsi_z hpsi_z_eq hcos_\<phi> hsin_\<phi> by (by100 simp)
        also have "\<dots> = (fst y, snd y)" unfolding a_def b_def using hr_pos by (by100 simp)
        also have "\<dots> = y" by (by100 simp)
        finally have "\<psi> z = y" .
        thus ?thesis using hz_P by (by100 blast)
      qed
    qed
    \<comment> \<open>(e) \<psi> injective on P.\<close>
    have h\<psi>_inj: "inj_on \<psi> P"
    proof (rule inj_onI)
      fix z1 z2 assume hz1: "z1 \<in> P" and hz2: "z2 \<in> P" and hpsi_eq2: "\<psi> z1 = \<psi> z2"
      from hP_cones hz1 obtain i1 where hi1: "i1 < n" and hic1: "in_cone i1 z1" by (by100 blast)
      from hP_cones hz2 obtain i2 where hi2: "i2 < n" and hic2: "in_cone i2 z2" by (by100 blast)
      have hpsi1: "\<psi> z1 = psi_local i1 z1" using hpsi_eq[OF hi1 hic1] .
      have hpsi2: "\<psi> z2 = psi_local i2 z2" using hpsi_eq[OF hi2 hic2] .
      define s1 where "s1 = beta_cr i1 z1 + gamma_cr i1 z1"
      define s2 where "s2 = beta_cr i2 z2 + gamma_cr i2 z2"
      define u1 where "u1 = (if s1 = 0 then 0 else gamma_cr i1 z1 / s1)"
      define u2 where "u2 = (if s2 = 0 then 0 else gamma_cr i2 z2 / s2)"
      define \<theta>1 where "\<theta>1 = 2*pi*(real i1 + u1)/real n"
      define \<theta>2 where "\<theta>2 = 2*pi*(real i2 + u2)/real n"
      have hpsi1_val: "psi_local i1 z1 = (s1 * cos \<theta>1, s1 * sin \<theta>1)"
        unfolding psi_local_def Let_def s1_def u1_def \<theta>1_def by (by100 simp)
      have hpsi2_val: "psi_local i2 z2 = (s2 * cos \<theta>2, s2 * sin \<theta>2)"
        unfolding psi_local_def Let_def s2_def u2_def \<theta>2_def by (by100 simp)
      have hs1_ge: "s1 \<ge> 0" using hic1 unfolding in_cone_def s1_def by (by100 linarith)
      have hs2_ge: "s2 \<ge> 0" using hic2 unfolding in_cone_def s2_def by (by100 linarith)
      have heq: "s1 * cos \<theta>1 = s2 * cos \<theta>2 \<and> s1 * sin \<theta>1 = s2 * sin \<theta>2"
        using hpsi_eq2 hpsi1 hpsi2 hpsi1_val hpsi2_val by (by100 simp)
      show "z1 = z2"
      proof (cases "s1 = 0")
        case hs1_0: True
        hence "s2 = 0"
        proof -
          from hs1_0 heq have "s2 * cos \<theta>2 = 0" "s2 * sin \<theta>2 = 0" by (by100 simp)+
          show "s2 = 0"
          proof (rule ccontr)
            assume "s2 \<noteq> 0"
            hence "cos \<theta>2 = 0" "sin \<theta>2 = 0" using \<open>s2 * cos \<theta>2 = 0\<close> \<open>s2 * sin \<theta>2 = 0\<close>
              by (by100 simp)+
            hence "cos \<theta>2 * cos \<theta>2 + sin \<theta>2 * sin \<theta>2 = 0" by (by100 simp)
            thus False using sin_cos_squared_add3[of \<theta>2] by (by100 linarith)
          qed
        qed
        have hDi1: "Di i1 \<noteq> 0" using hDi_pos[OF hi1] by (by100 linarith)
        have hDi2: "Di i2 \<noteq> 0" using hDi_pos[OF hi2] by (by100 linarith)
        have hb1_0: "beta_cr i1 z1 = 0" and hg1_0: "gamma_cr i1 z1 = 0"
          using hs1_0 unfolding s1_def
          using hic1 unfolding in_cone_def by (by100 linarith)+
        have hb2_0: "beta_cr i2 z2 = 0" and hg2_0: "gamma_cr i2 z2 = 0"
          using \<open>s2 = 0\<close> unfolding s2_def
          using hic2 unfolding in_cone_def by (by100 linarith)+
        have "fst z1 = cx"
          using hCramer_x[OF hDi1, of z1] hb1_0 hg1_0 by (by100 simp)
        moreover have "snd z1 = cy"
          using hCramer_y[OF hDi1, of z1] hb1_0 hg1_0 by (by100 simp)
        moreover have "fst z2 = cx"
          using hCramer_x[OF hDi2, of z2] hb2_0 hg2_0 by (by100 simp)
        moreover have "snd z2 = cy"
          using hCramer_y[OF hDi2, of z2] hb2_0 hg2_0 by (by100 simp)
        ultimately show ?thesis by (cases z1, cases z2) (by100 simp)
      next
        case hs1_ne: False
        hence hs1_pos: "s1 > 0" using hs1_ge by (by100 linarith)
        have hs2_pos: "s2 > 0"
        proof (rule ccontr)
          assume "\<not> s2 > 0" hence "s2 = 0" using hs2_ge by (by100 linarith)
          hence "s1 * cos \<theta>1 = 0" "s1 * sin \<theta>1 = 0" using heq by (by100 simp)+
          hence "cos \<theta>1 = 0" "sin \<theta>1 = 0" using hs1_ne by (by100 simp)+
          hence "cos \<theta>1 * cos \<theta>1 + sin \<theta>1 * sin \<theta>1 = 0" by (by100 simp)
          thus False using sin_cos_squared_add3[of \<theta>1] by (by100 linarith)
        qed
        \<comment> \<open>cos \<theta>1 = cos \<theta>2 and sin \<theta>1 = sin \<theta>2 (from s1=s2 > 0).\<close>
        have hs_eq: "s1 = s2"
        proof -
          \<comment> \<open>|s1*cos,s1*sin|^2 = s1^2 and |s2*cos,s2*sin|^2 = s2^2.\<close>
          have "s1*s1 = s2*s2"
          proof -
            from heq have hc: "s1*cos \<theta>1 = s2*cos \<theta>2" and hs: "s1*sin \<theta>1 = s2*sin \<theta>2"
              by (by100 blast)+
            define cc1 where "cc1 = cos \<theta>1 * cos \<theta>1"
            define ss1 where "ss1 = sin \<theta>1 * sin \<theta>1"
            define cc2 where "cc2 = cos \<theta>2 * cos \<theta>2"
            define ss2 where "ss2 = sin \<theta>2 * sin \<theta>2"
            have eq1: "s1*s1*cc1 = s2*s2*cc2"
              using hc unfolding cc1_def cc2_def by (simp add: algebra_simps)
            have eq2: "s1*s1*ss1 = s2*s2*ss2"
              using hs unfolding ss1_def ss2_def by (simp add: algebra_simps)
            have "s1*s1*(cc1 + ss1) = s2*s2*(cc2 + ss2)"
              using eq1 eq2 by (simp add: algebra_simps)
            moreover have "cc1 + ss1 = 1"
              unfolding cc1_def ss1_def using sin_cos_squared_add3 by (by100 simp)
            moreover have "cc2 + ss2 = 1"
              unfolding cc2_def ss2_def using sin_cos_squared_add3 by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          hence "(s1 - s2) * (s1 + s2) = 0" by (simp add: algebra_simps)
          hence "s1 - s2 = 0 \<or> s1 + s2 = 0" by (by100 simp)
          thus "s1 = s2" using hs1_ge hs2_ge by (by100 linarith)
        qed
        have hcos: "cos \<theta>1 = cos \<theta>2" using heq hs_eq hs1_pos by (by100 simp)
        have hsin: "sin \<theta>1 = sin \<theta>2" using heq hs_eq hs1_pos by (by100 simp)
        \<comment> \<open>cos(\<theta>1-\<theta>2) = cos^2\<theta>2 + sin^2\<theta>2 = 1, so \<theta>1-\<theta>2 = 2\<pi>k.\<close>
        have "cos (\<theta>1 - \<theta>2) = cos \<theta>1 * cos \<theta>2 + sin \<theta>1 * sin \<theta>2"
          using cos_diff by (by100 blast)
        also have "\<dots> = cos \<theta>2 * cos \<theta>2 + sin \<theta>2 * sin \<theta>2" using hcos hsin by (by100 simp)
        also have "\<dots> = 1" using sin_cos_squared_add3 by (by100 simp)
        finally have hcos1: "cos (\<theta>1 - \<theta>2) = 1" .
        have "\<exists>k :: int. \<theta>1 - \<theta>2 = real_of_int k * 2 * pi"
          using cos_one_2pi_int[of "\<theta>1 - \<theta>2"] hcos1 by (by100 blast)
        then obtain k :: int where hk: "\<theta>1 - \<theta>2 = real_of_int k * 2 * pi" by (by100 blast)
        \<comment> \<open>|\<theta>1 - \<theta>2| < 2\<pi> since both in [0, 2\<pi>].\<close>
        have hu1_b: "0 \<le> u1 \<and> u1 \<le> 1" unfolding u1_def
          using hic1 unfolding in_cone_def s1_def by (by5000 force)
        have hu2_b: "0 \<le> u2 \<and> u2 \<le> 1" unfolding u2_def
          using hic2 unfolding in_cone_def s2_def by (by5000 force)
        have hn_pos: "real n > 0" using hn by (by100 simp)
        have h\<theta>1_ge: "\<theta>1 \<ge> 0" unfolding \<theta>1_def
          using hu1_b hi1 pi_gt_zero hn_pos
          using divide_nonneg_nonneg mult_nonneg_nonneg by (by100 simp)
        have h\<theta>1_le: "\<theta>1 \<le> 2*pi"
        proof -
          have hle: "real i1 + u1 \<le> real n" using hu1_b hi1 by (by100 linarith)
          have "\<theta>1 = 2*pi*(real i1 + u1)/real n" unfolding \<theta>1_def by (by100 simp)
          also have "\<dots> \<le> 2*pi*real n/real n"
            using hle pi_gt_zero hn_pos
            using divide_right_mono[of "2*pi*(real i1 + u1)" "2*pi*real n" "real n"]
            by (by100 simp)
          also have "\<dots> = 2*pi" using hn_pos by (by100 simp)
          finally show ?thesis .
        qed
        have h\<theta>2_ge: "\<theta>2 \<ge> 0" unfolding \<theta>2_def
          using hu2_b hi2 pi_gt_zero hn_pos
          using divide_nonneg_nonneg mult_nonneg_nonneg by (by100 simp)
        have h\<theta>2_le: "\<theta>2 \<le> 2*pi"
        proof -
          have hle: "real i2 + u2 \<le> real n" using hu2_b hi2 by (by100 linarith)
          have "\<theta>2 = 2*pi*(real i2 + u2)/real n" unfolding \<theta>2_def by (by100 simp)
          also have "\<dots> \<le> 2*pi*real n/real n"
            using hle pi_gt_zero hn_pos
            using divide_right_mono[of "2*pi*(real i2 + u2)" "2*pi*real n" "real n"]
            by (by100 simp)
          also have "\<dots> = 2*pi" using hn_pos by (by100 simp)
          finally show ?thesis .
        qed
        have hk_ineq: "real_of_int k * 2 * pi \<ge> -2*pi \<and> real_of_int k * 2 * pi \<le> 2*pi"
          using hk h\<theta>1_ge h\<theta>1_le h\<theta>2_ge h\<theta>2_le by (by100 linarith)
        hence "real_of_int k * (2 * pi) \<ge> -(2*pi) \<and> real_of_int k * (2 * pi) \<le> 2*pi"
          by (simp add: algebra_simps)
        hence hk_range: "k \<ge> -1 \<and> k \<le> 1"
        proof -
          assume h: "real_of_int k * (2 * pi) \<ge> -(2*pi) \<and> real_of_int k * (2 * pi) \<le> 2*pi"
          have hpi: "2 * pi > 0" using pi_gt_zero by (by100 linarith)
          have "real_of_int k \<ge> -1"
          proof (rule ccontr)
            assume "\<not> real_of_int k \<ge> -1"
            hence "real_of_int k < -1" by (by100 simp)
            hence "real_of_int k * (2 * pi) < (-1) * (2 * pi)"
              using mult_strict_right_mono[of "real_of_int k" "-1" "2*pi"] hpi by (by100 linarith)
            thus False using h by (by100 linarith)
          qed
          moreover have "real_of_int k \<le> 1"
          proof (rule ccontr)
            assume "\<not> real_of_int k \<le> 1"
            hence "real_of_int k > 1" by (by100 simp)
            hence "real_of_int k * (2 * pi) > 1 * (2 * pi)"
              using mult_strict_right_mono[of 1 "real_of_int k" "2*pi"] hpi by (by100 linarith)
            thus False using h by (by100 linarith)
          qed
          ultimately show ?thesis by (by100 linarith)
        qed
        \<comment> \<open>k \<in> {-1, 0, 1}. For k=0: \<theta>1=\<theta>2. For k=\<plusminus>1: boundary (one \<theta>=0, other=2\<pi>).\<close>
        have h\<theta>_eq_mod: "\<theta>1 = \<theta>2 \<or> \<theta>1 = \<theta>2 + 2*pi \<or> \<theta>1 = \<theta>2 - 2*pi"
        proof -
          from hk_range have "k = -1 \<or> k = 0 \<or> k = 1" by (by100 force)
          thus ?thesis using hk by (by100 force)
        qed
        \<comment> \<open>In all cases, cos \<theta>1 = cos \<theta>2 and sin \<theta>1 = sin \<theta>2, so the
           physical point z-c = s*((1-u)*(vi-c) + u*(vi+1-c)) is the same.\<close>
        \<comment> \<open>z1-c = s*((1-u1)*(vi1-c) + u1*(vi1+1-c)), similarly z2.
           From \<theta>1 = \<theta>2 mod 2\<pi> and s1=s2: the weighted vertex combination is the same.
           Key: Cramer reconstruction determines z from (\<beta>,\<gamma>,i).
           Since the angle determines the boundary point and s the distance from c,
           z1 and z2 must be the same point.\<close>
        have hDi1: "Di i1 \<noteq> 0" using hDi_pos[OF hi1] by (by100 linarith)
        have hDi2: "Di i2 \<noteq> 0" using hDi_pos[OF hi2] by (by100 linarith)
        \<comment> \<open>z1-c = (s1*cos \<theta>1 / cos \<theta>1) * something... No, use direct Cramer.\<close>
        \<comment> \<open>From heq: fst(z1) = fst(z2) follows from \<psi>(z1) = \<psi>(z2) and the
           bijection between \<psi>-values and z-values via Cramer reconstruction.\<close>
        \<comment> \<open>From \<theta>1 = \<theta>2 mod 2\<pi>: i1+u1 = i2+u2 (mod n).\<close>
        have hiu_mod: "real i1 + u1 = real i2 + u2 \<or>
            real i1 + u1 = real i2 + u2 + real n \<or>
            real i1 + u1 = real i2 + u2 - real n"
        proof -
          \<comment> \<open>\<theta>1 - \<theta>2 = k*2\<pi> implies (i1+u1) - (i2+u2) = k*n.\<close>
          have hiu_diff: "real i1 + u1 - (real i2 + u2) = real_of_int k * real n"
          proof -
            have h1: "\<theta>1 = 2*pi*(real i1 + u1)/real n" unfolding \<theta>1_def by (by100 simp)
            have h2: "\<theta>2 = 2*pi*(real i2 + u2)/real n" unfolding \<theta>2_def by (by100 simp)
            have hpi_ne: "(2*pi) \<noteq> (0::real)" using pi_gt_zero by (by100 linarith)
            have hnn: "real n \<noteq> (0::real)" using hn_pos by (by100 linarith)
            from hk h1 h2 have hdiff: "\<theta>1 - \<theta>2 = real_of_int k * 2 * pi" by (by100 linarith)
            \<comment> \<open>\<theta>1/(2\<pi>) = (i1+u1)/n and \<theta>2/(2\<pi>) = (i2+u2)/n.\<close>
            have h1': "(real i1 + u1)/real n = \<theta>1/(2*pi)"
              using h1 hpi_ne by (by100 simp)
            have h2': "(real i2 + u2)/real n = \<theta>2/(2*pi)"
              using h2 hpi_ne by (by100 simp)
            have "(real i1 + u1)/real n - (real i2 + u2)/real n = real_of_int k"
            proof -
              have "(\<theta>1 - \<theta>2)/(2*pi) = real_of_int k"
                using hdiff hpi_ne by (by100 simp)
              moreover have "(\<theta>1 - \<theta>2)/(2*pi) = \<theta>1/(2*pi) - \<theta>2/(2*pi)"
                by (simp add: diff_divide_distrib)
              ultimately show ?thesis using h1' h2' by (by100 linarith)
            qed
            hence "((real i1 + u1) - (real i2 + u2)) = real_of_int k * real n"
            proof -
              assume h: "(real i1 + u1)/real n - (real i2 + u2)/real n = real_of_int k"
              hence "((real i1 + u1) - (real i2 + u2))/real n = real_of_int k"
                by (simp add: diff_divide_distrib)
              hence "((real i1 + u1) - (real i2 + u2))/real n * real n = real_of_int k * real n"
                by (by100 simp)
              thus ?thesis using hnn by (by5000 simp)
            qed
            thus ?thesis by (by100 linarith)
          qed
          from hk_range have "k = -1 \<or> k = 0 \<or> k = 1" by (by100 force)
          thus ?thesis using hiu_diff by (by100 force)
        qed
        \<comment> \<open>Cramer: z-c = \<beta>*(vi-c) + \<gamma>*(vi+1-c) = (1-u)*s*(vi-c) + u*s*(vi+1-c).\<close>
        have hg1: "gamma_cr i1 z1 = u1 * s1" using hs1_ne unfolding u1_def s1_def by (by100 simp)
        have hg2: "gamma_cr i2 z2 = u2 * s2" using hs2_pos unfolding u2_def s2_def by (by100 simp)
        have hb1: "beta_cr i1 z1 = s1 - u1 * s1"
        proof -
          have "s1 = beta_cr i1 z1 + gamma_cr i1 z1" unfolding s1_def by (by100 simp)
          thus ?thesis using hg1 by (by100 linarith)
        qed
        have hb2: "beta_cr i2 z2 = s2 - u2 * s2"
        proof -
          have "s2 = beta_cr i2 z2 + gamma_cr i2 z2" unfolding s2_def by (by100 simp)
          thus ?thesis using hg2 by (by100 linarith)
        qed
        \<comment> \<open>fst(z1-c) = (1-u1)*s1*(vx i1 - cx) + u1*s1*(vx(i1+1)-cx), same for z2.\<close>
        have hfst1: "fst z1 - cx = (s1 - u1*s1)*(vx i1 - cx) + u1*s1*(vx (Suc i1 mod n) - cx)"
          using hCramer_x[OF hDi1, of z1] hb1 hg1 by (simp add: algebra_simps)
        have hfst2: "fst z2 - cx = (s2 - u2*s2)*(vx i2 - cx) + u2*s2*(vx (Suc i2 mod n) - cx)"
          using hCramer_x[OF hDi2, of z2] hb2 hg2 by (simp add: algebra_simps)
        have hsnd1: "snd z1 - cy = (s1 - u1*s1)*(vy i1 - cy) + u1*s1*(vy (Suc i1 mod n) - cy)"
          using hCramer_y[OF hDi1, of z1] hb1 hg1 by (simp add: algebra_simps)
        have hsnd2: "snd z2 - cy = (s2 - u2*s2)*(vy i2 - cy) + u2*s2*(vy (Suc i2 mod n) - cy)"
          using hCramer_y[OF hDi2, of z2] hb2 hg2 by (simp add: algebra_simps)
        \<comment> \<open>z-c = s*((1-u)*(vi-c) + u*(vi+1-c)). So fst(z-c)/s = (1-u)*(vx i-cx) + u*(vx(i+1)-cx).\<close>
        \<comment> \<open>This is the fst-coord of boundary point (1-u)*vi + u*vi+1, shifted by c.\<close>
        \<comment> \<open>From hiu_mod and s1=s2: the boundary points match, hence z1-c = z2-c.\<close>
        show "z1 = z2"
        proof -
          \<comment> \<open>The boundary point bx = (1-u)*vx_i + u*vx_{i+1} is determined by angle \<theta>.\<close>
          \<comment> \<open>Case analysis on hiu_mod.\<close>
          from hiu_mod show ?thesis
          proof (elim disjE)
            assume hiu: "real i1 + u1 = real i2 + u2"
            \<comment> \<open>i1+u1 = i2+u2 with u in [0,1], i integer. Either i1=i2,u1=u2 or boundary.\<close>
            have hi_eq: "i1 = i2 \<or> (i1 = i2 + 1 \<and> u1 = 0 \<and> u2 = 1) \<or> (i2 = i1 + 1 \<and> u2 = 0 \<and> u1 = 1)"
              using hiu hu1_b hu2_b by (by5000 force)
            from hi_eq show "z1 = z2"
            proof (elim disjE conjE)
              assume hi_eq: "i1 = i2"
              hence "u1 = u2" using hiu by (by100 linarith)
              hence hbeq: "beta_cr i1 z1 = beta_cr i1 z2"
                using hb1 hb2 hs_eq hi_eq by (by100 simp)
              have hgeq: "gamma_cr i1 z1 = gamma_cr i1 z2"
                using hg1 hg2 hs_eq \<open>u1 = u2\<close> hi_eq by (by100 simp)
              have hfx1: "fst z1 - cx = beta_cr i1 z1 * (vx i1 - cx) + gamma_cr i1 z1 * (vx (Suc i1 mod n) - cx)"
                using hCramer_x[OF hDi1, of z1] .
              have hfx2: "fst z2 - cx = beta_cr i1 z2 * (vx i1 - cx) + gamma_cr i1 z2 * (vx (Suc i1 mod n) - cx)"
                using hCramer_x[OF hDi1, of z2] .
              have hfst_eq: "fst z1 = fst z2" using hfx1 hfx2 hbeq hgeq by (by100 simp)
              have hfy1: "snd z1 - cy = beta_cr i1 z1 * (vy i1 - cy) + gamma_cr i1 z1 * (vy (Suc i1 mod n) - cy)"
                using hCramer_y[OF hDi1, of z1] .
              have hfy2: "snd z2 - cy = beta_cr i1 z2 * (vy i1 - cy) + gamma_cr i1 z2 * (vy (Suc i1 mod n) - cy)"
                using hCramer_y[OF hDi1, of z2] .
              have hsnd_eq: "snd z1 = snd z2" using hfy1 hfy2 hbeq hgeq by (by100 simp)
              show "z1 = z2" using hfst_eq hsnd_eq by (cases z1, cases z2) (by100 simp)
            next
              assume "i1 = i2 + 1" and "u1 = 0" and "u2 = 1"
              \<comment> \<open>z1: \<beta>1=(1-0)*s=s, \<gamma>1=0. z1-c = s*(vi1-c) = s*(v_{i2+1}-c).\<close>
              \<comment> \<open>z2: \<beta>2=0, \<gamma>2=s. z2-c = s*(v_{i2+1}-c). Same!\<close>
              have hmod12: "Suc i2 mod n = i1"
              proof -
                have "Suc i2 = i1" using \<open>i1 = i2 + 1\<close> by (by100 simp)
                thus ?thesis using hi1 by (by100 simp)
              qed
              have "fst z1 - cx = s1 * (vx i1 - cx)"
                using hfst1 \<open>u1 = 0\<close> by (by100 simp)
              moreover have "fst z2 - cx = s2 * (vx i1 - cx)"
                using hfst2 \<open>u2 = 1\<close> hmod12 by (by100 simp)
              ultimately have "fst z1 - cx = fst z2 - cx" using hs_eq by (by100 simp)
              hence hfst_eq: "fst z1 = fst z2" by (by100 linarith)
              have "snd z1 - cy = s1 * (vy i1 - cy)" using hsnd1 \<open>u1 = 0\<close> by (by100 simp)
              moreover have "snd z2 - cy = s2 * (vy i1 - cy)"
                using hsnd2 \<open>u2 = 1\<close> hmod12 by (by100 simp)
              ultimately have "snd z1 - cy = snd z2 - cy" using hs_eq by (by100 simp)
              hence "snd z1 = snd z2" by (by100 linarith)
              thus "z1 = z2" using hfst_eq by (cases z1, cases z2) (by100 simp)
            next
              assume "i2 = i1 + 1" and "u2 = 0" and "u1 = 1"
              \<comment> \<open>Symmetric case.\<close>
              have hmod21: "Suc i1 mod n = i2"
              proof -
                have "Suc i1 = i2" using \<open>i2 = i1 + 1\<close> by (by100 simp)
                thus ?thesis using hi2 by (by100 simp)
              qed
              have "fst z1 - cx = s1 * (vx i2 - cx)"
                using hfst1 \<open>u1 = 1\<close> hmod21 by (by100 simp)
              moreover have "fst z2 - cx = s2 * (vx i2 - cx)"
                using hfst2 \<open>u2 = 0\<close> by (by100 simp)
              ultimately have "fst z1 - cx = fst z2 - cx" using hs_eq by (by100 simp)
              hence hfst_eq: "fst z1 = fst z2" by (by100 linarith)
              have "snd z1 - cy = s1 * (vy i2 - cy)"
                using hsnd1 \<open>u1 = 1\<close> hmod21 by (by100 simp)
              moreover have "snd z2 - cy = s2 * (vy i2 - cy)" using hsnd2 \<open>u2 = 0\<close> by (by100 simp)
              ultimately have "snd z1 - cy = snd z2 - cy" using hs_eq by (by100 simp)
              hence "snd z1 = snd z2" by (by100 linarith)
              thus "z1 = z2" using hfst_eq by (cases z1, cases z2) (by100 simp)
            qed
          next
            assume hiu: "real i1 + u1 = real i2 + u2 + real n"
            \<comment> \<open>i1+u1 = i2+u2+n. Since i1 < n, u1 \<le> 1, i2 \<ge> 0, u2 \<ge> 0: i1+u1 < n+1, i2+u2+n \<ge> n.
               So n \<le> i2+u2+n < n+1, i.e., i2+u2 < 1, so i2=0 and u2 < 1.
               And i1+u1 = u2+n, with u1 \<le> 1 and i1 < n: i1 = n-1, u1 = u2.
               Actually, i1+u1 \<ge> n, so i1 \<ge> n-1. Since i1 < n: i1 = n-1.
               Then n-1+u1 = u2+n, so u1 = u2+1. Since u1 \<le> 1 and u2 \<ge> 0: u1 = 1, u2 = 0.\<close>
            have "i1 = n - 1" and "u1 = 1" and "i2 = 0" and "u2 = 0"
              using hiu hu1_b hu2_b hi1 hi2 by (by5000 force)+
            \<comment> \<open>z1: u1=1, i1=n-1. \<beta>1=0, \<gamma>1=s. z1-c = s*(v_n mod n - c) = s*(v_0 - c).\<close>
            \<comment> \<open>z2: u2=0, i2=0. \<beta>2=s, \<gamma>2=0. z2-c = s*(v_0 - c). Same!\<close>
            have "Suc (n-1) mod n = 0" using hn by (by100 simp)
            hence hmod: "Suc i1 mod n = 0" using \<open>i1 = n-1\<close> by (by100 simp)
            have "fst z1 - cx = s1 * (vx 0 - cx)"
              using hfst1 \<open>u1 = 1\<close> hmod by (by100 simp)
            moreover have "fst z2 - cx = s2 * (vx 0 - cx)"
              using hfst2 \<open>u2 = 0\<close> \<open>i2 = 0\<close> by (by100 simp)
            ultimately have "fst z1 - cx = fst z2 - cx" using hs_eq by (by100 simp)
            hence hfst_eq: "fst z1 = fst z2" by (by100 linarith)
            have "snd z1 - cy = s1 * (vy 0 - cy)" using hsnd1 \<open>u1 = 1\<close> hmod by (by100 simp)
            moreover have "snd z2 - cy = s2 * (vy 0 - cy)" using hsnd2 \<open>u2 = 0\<close> \<open>i2 = 0\<close> by (by100 simp)
            ultimately have "snd z1 - cy = snd z2 - cy" using hs_eq by (by100 simp)
            hence "snd z1 = snd z2" by (by100 linarith)
            thus "z1 = z2" using hfst_eq by (cases z1, cases z2) (by100 simp)
          next
            assume hiu: "real i1 + u1 = real i2 + u2 - real n"
            \<comment> \<open>Symmetric: i2 = n-1, u2 = 1, i1 = 0, u1 = 0.\<close>
            have "i2 = n - 1" and "u2 = 1" and "i1 = 0" and "u1 = 0"
              using hiu hu1_b hu2_b hi1 hi2 by (by5000 force)+
            have "Suc (n-1) mod n = 0" using hn by (by100 simp)
            hence hmod: "Suc i2 mod n = 0" using \<open>i2 = n-1\<close> by (by100 simp)
            have "fst z1 - cx = s1 * (vx 0 - cx)"
              using hfst1 \<open>u1 = 0\<close> \<open>i1 = 0\<close> by (by100 simp)
            moreover have "fst z2 - cx = s2 * (vx 0 - cx)"
              using hfst2 \<open>u2 = 1\<close> hmod by (by100 simp)
            ultimately have "fst z1 - cx = fst z2 - cx" using hs_eq by (by100 simp)
            hence hfst_eq: "fst z1 = fst z2" by (by100 linarith)
            have "snd z1 - cy = s1 * (vy 0 - cy)" using hsnd1 \<open>u1 = 0\<close> \<open>i1 = 0\<close> by (by100 simp)
            moreover have "snd z2 - cy = s2 * (vy 0 - cy)" using hsnd2 \<open>u2 = 1\<close> hmod by (by100 simp)
            ultimately have "snd z1 - cy = snd z2 - cy" using hs_eq by (by100 simp)
            hence "snd z1 = snd z2" by (by100 linarith)
            thus "z1 = z2" using hfst_eq by (cases z1, cases z2) (by100 simp)
          qed
        qed
      qed
    qed
    \<comment> \<open>(f) Apply Theorem 26.6: continuous bijection compact \<rightarrow> Hausdorff = homeomorphism.\<close>
    have h\<psi>_bij: "bij_betw \<psi> P top1_B2"
      unfolding bij_betw_def using h\<psi>_surj h\<psi>_inj by (by100 blast)
    have hP_compact: "top1_compact_on P ?TP"
      by (rule polygonal_region_compact[OF assms(1) assms(2)])
    have hB2_haus: "is_hausdorff_on top1_B2 top1_B2_topology"
    proof -
      have "top1_B2 \<subseteq> (UNIV :: (real \<times> real) set)" by (by100 blast)
      thus ?thesis using Theorem_17_11 top1_R2_is_hausdorff
        unfolding top1_B2_topology_def by (by5000 blast)
    qed
    have h\<psi>_top1: "top1_continuous_map_on P ?TP top1_B2 top1_B2_topology \<psi>"
    proof -
      have himg: "\<And>p. p \<in> P \<Longrightarrow> \<psi> p \<in> top1_B2"
        using h\<psi>_surj by (by100 blast)
      have "top1_B2_topology = subspace_topology UNIV
          (product_topology_on top1_open_sets top1_open_sets) top1_B2"
        unfolding top1_B2_topology_def ..
      thus ?thesis using top1_continuous_map_on_real2_subspace_general[OF himg h\<psi>_cont]
        by (by100 simp)
    qed
    have h\<psi>_homeo: "top1_homeomorphism_on P ?TP top1_B2 top1_B2_topology \<psi>"
    proof -
      have hR: "is_topology_on (UNIV::real set) top1_open_sets"
        unfolding top1_open_sets_def is_topology_on_def
        using open_UNIV open_empty open_Un open_Int by (by5000 auto)
      have hR2: "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
          (product_topology_on top1_open_sets top1_open_sets)"
        using hR product_topology_on_is_topology_on by (by100 blast)
      hence hR2': "is_topology_on (UNIV::(real \<times> real) set)
          (product_topology_on top1_open_sets top1_open_sets)" by (by100 simp)
      have hTP_top: "is_topology_on P ?TP"
      proof -
        have "P \<subseteq> (UNIV::(real \<times> real) set)" by (by100 blast)
        thus ?thesis by (rule subspace_topology_is_topology_on[OF hR2'])
      qed
      have hTB2: "is_topology_on top1_B2 top1_B2_topology"
        unfolding top1_B2_topology_def
        by (rule subspace_topology_is_topology_on[OF hR2']) (by100 blast)
      from Theorem_26_6[OF hTP_top hTB2 hP_compact hB2_haus h\<psi>_top1 h\<psi>_bij]
      show ?thesis .
    qed
    \<comment> \<open>(g) By construction: \<psi>(BdP) = S1 and \<psi>(IntP) = IntB2.\<close>
    \<comment> \<open>Helper: Cramer coords of boundary point (1-t)*v_i + t*v_{i+1}.\<close>
    have hCramer_bd: "\<And>i t. i < n \<Longrightarrow> 0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow>
        beta_cr i ((1-t)*vx i + t*vx(Suc i mod n), (1-t)*vy i + t*vy(Suc i mod n)) = 1 - t \<and>
        gamma_cr i ((1-t)*vx i + t*vx(Suc i mod n), (1-t)*vy i + t*vy(Suc i mod n)) = t"
    proof -
      fix i :: nat and t :: real
      assume hi: "i < n" and ht0: "0 \<le> t" and ht1: "t \<le> 1"
      define x where "x = ((1-t)*vx i + t*vx(Suc i mod n), (1-t)*vy i + t*vy(Suc i mod n))"
      have hDi: "Di i > 0" using hDi_pos[OF hi] .
      have hDi_ne: "Di i \<noteq> 0" using hDi by (by100 linarith)
      \<comment> \<open>x - c = (1-t)*(v_i - c) + t*(v_{i+1} - c)\<close>
      have hfst: "fst x - cx = (1-t)*(vx i - cx) + t*(vx(Suc i mod n) - cx)"
        unfolding x_def by (simp add: algebra_simps)
      have hsnd: "snd x - cy = (1-t)*(vy i - cy) + t*(vy(Suc i mod n) - cy)"
        unfolding x_def by (simp add: algebra_simps)
      \<comment> \<open>beta_cr = cross2(x-c, v_{i+1}-c)/Di = (1-t)*Di/Di = 1-t\<close>
      have hcross_Di: "cross2 (vx i - cx, vy i - cy) (vx(Suc i mod n) - cx, vy(Suc i mod n) - cy) = Di i"
        unfolding Di_def cross2_def by (by100 simp)
      have hcross_b: "cross2 (fst x - cx, snd x - cy) (vx(Suc i mod n) - cx, vy(Suc i mod n) - cy) =
          (1-t) * Di i"
      proof -
        have "cross2 (fst x - cx, snd x - cy) (vx(Suc i mod n) - cx, vy(Suc i mod n) - cy) =
            (1-t) * cross2 (vx i - cx, vy i - cy) (vx(Suc i mod n) - cx, vy(Suc i mod n) - cy)"
          unfolding cross2_def hfst hsnd by (simp add: algebra_simps)
        thus ?thesis using hcross_Di by (by100 simp)
      qed
      have hbeta: "beta_cr i x = 1 - t"
      proof -
        have "beta_cr i x = cross2 (fst x - cx, snd x - cy) (vx(Suc i mod n) - cx, vy(Suc i mod n) - cy) / Di i"
          unfolding beta_cr_def by (by100 simp)
        also have "\<dots> = (1-t) * Di i / Di i" using hcross_b by (by100 simp)
        also have "\<dots> = 1 - t" using hDi_ne by (by100 simp)
        finally show ?thesis .
      qed
      \<comment> \<open>gamma_cr = cross2(v_i-c, x-c)/Di = t*Di/Di = t\<close>
      have hcross_g: "cross2 (vx i - cx, vy i - cy) (fst x - cx, snd x - cy) = t * Di i"
      proof -
        have "cross2 (vx i - cx, vy i - cy) (fst x - cx, snd x - cy) =
            t * cross2 (vx i - cx, vy i - cy) (vx(Suc i mod n) - cx, vy(Suc i mod n) - cy)"
          unfolding cross2_def hfst hsnd by (simp add: algebra_simps)
        thus ?thesis using hcross_Di by (by100 simp)
      qed
      have hgamma: "gamma_cr i x = t"
      proof -
        have "gamma_cr i x = cross2 (vx i - cx, vy i - cy) (fst x - cx, snd x - cy) / Di i"
          unfolding gamma_cr_def by (by100 simp)
        also have "\<dots> = t * Di i / Di i" using hcross_g by (by100 simp)
        also have "\<dots> = t" using hDi_ne by (by100 simp)
        finally show ?thesis .
      qed
      show "beta_cr i x = 1 - t \<and> gamma_cr i x = t"
        using hbeta hgamma by (by100 blast)
    qed
    \<comment> \<open>Helper: psi_local on boundary point.\<close>
    have hpsi_local_bd: "\<And>i t. i < n \<Longrightarrow> 0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow>
        psi_local i ((1-t)*vx i + t*vx(Suc i mod n), (1-t)*vy i + t*vy(Suc i mod n)) =
        (cos (2*pi*(real i + t)/real n), sin (2*pi*(real i + t)/real n))"
    proof -
      fix i :: nat and t :: real
      assume hi: "i < n" and ht0: "0 \<le> t" and ht1: "t \<le> 1"
      define x where "x = ((1-t)*vx i + t*vx(Suc i mod n), (1-t)*vy i + t*vy(Suc i mod n))"
      from hCramer_bd[OF hi ht0 ht1]
      have hb: "beta_cr i x = 1 - t" and hg: "gamma_cr i x = t"
        unfolding x_def by (by100 blast)+
      show "psi_local i ((1-t)*vx i + t*vx(Suc i mod n), (1-t)*vy i + t*vy(Suc i mod n)) =
          (cos (2*pi*(real i + t)/real n), sin (2*pi*(real i + t)/real n))"
        using hb hg unfolding x_def[symmetric] psi_local_def Let_def by (by100 simp)
    qed
    have h\<psi>_bd: "\<psi> ` ?BdP = top1_S1"
    proof (rule set_eqI, rule iffI)
      \<comment> \<open>\<subseteq>: boundary maps into S1.\<close>
      fix y assume "y \<in> \<psi> ` ?BdP"
      then obtain x where hx_in: "x \<in> ?BdP" and hy: "y = \<psi> x" by (by100 blast)
      from hx_in obtain i t where hi: "i < n" and ht: "t \<in> I_set"
          and hx_eq: "x = ((1-t)*vx i + t*vx(Suc i mod n),
                          (1-t)*vy i + t*vy(Suc i mod n))"
        by (by5000 force)
      have ht0: "0 \<le> t" and ht1: "t \<le> 1" using ht
        unfolding top1_unit_interval_def by (by100 auto)+
      from hCramer_bd[OF hi ht0 ht1]
      have hb: "beta_cr i x = 1 - t" and hg: "gamma_cr i x = t"
        unfolding hx_eq by (by100 blast)+
      have hic: "in_cone i x"
        unfolding in_cone_def using hb hg ht0 ht1 by (by100 linarith)
      have "psi_local i x = (cos (2*pi*(real i + t)/real n), sin (2*pi*(real i + t)/real n))"
        using hpsi_local_bd[OF hi ht0 ht1] unfolding hx_eq .
      hence hy_eq: "y = (cos (2*pi*(real i + t)/real n), sin (2*pi*(real i + t)/real n))"
        using hy hpsi_eq[OF hi hic] unfolding hx_eq by (by100 simp)
      show "y \<in> top1_S1" unfolding top1_S1_def
      proof (by100 simp)
        define \<theta> where "\<theta> = 2*pi*(real i + t)/real n"
        have "fst y = cos \<theta>" and "snd y = sin \<theta>" unfolding \<theta>_def hy_eq by (by100 simp)+
        thus "fst y ^ 2 + snd y ^ 2 = 1"
          using sin_cos_squared_add3[of \<theta>] by (by100 simp)
      qed
    next
      \<comment> \<open>\<supseteq>: S1 maps back from boundary.\<close>
      fix y assume hy_S1: "y \<in> top1_S1"
      hence hy_eq: "fst y ^ 2 + snd y ^ 2 = 1" unfolding top1_S1_def by (by100 simp)
      \<comment> \<open>Find angle \<theta> \<in> [0, 2\<pi>) with cos \<theta> = fst y, sin \<theta> = snd y.\<close>
      define \<theta> where "\<theta> = (if snd y \<ge> 0 then arccos (fst y) else 2*pi - arccos (fst y))"
      have hfst_bound: "-1 \<le> fst y" "fst y \<le> 1"
      proof -
        have h0: "(0::real) \<le> snd y ^ 2" by (by100 simp)
        hence hsq: "fst y ^ 2 \<le> 1" using hy_eq by (by100 linarith)
        hence hsq': "fst y * fst y \<le> 1" using power2_eq_square[of "fst y"] by (by100 simp)
        show "fst y \<le> 1"
        proof (rule ccontr)
          assume "\<not> fst y \<le> 1"
          hence hgt: "fst y > 1" by (by100 simp)
          have "fst y * 1 < fst y * fst y"
            using mult_strict_left_mono[of 1 "fst y" "fst y"] hgt by (by100 linarith)
          thus False using hsq' hgt by (by100 linarith)
        qed
        show "-1 \<le> fst y"
        proof (rule ccontr)
          assume "\<not> -1 \<le> fst y"
          hence hlt: "fst y < -1" by (by100 simp)
          hence hlt': "- fst y > 1" by (by100 linarith)
          have "(- fst y) * 1 < (- fst y) * (- fst y)"
            using mult_strict_left_mono[of 1 "- fst y" "- fst y"] hlt' by (by100 linarith)
          hence "- fst y < fst y * fst y" by (by100 simp)
          hence "fst y * fst y > 1" using hlt' by (by100 linarith)
          thus False using hsq' by (by100 linarith)
        qed
      qed
      have hcos: "cos \<theta> = fst y"
      proof (cases "snd y \<ge> 0")
        case True thus ?thesis unfolding \<theta>_def using cos_arccos[OF hfst_bound(1) hfst_bound(2)] by (by100 simp)
      next
        case False thus ?thesis unfolding \<theta>_def using cos_arccos[OF hfst_bound(1) hfst_bound(2)] by (by100 simp)
      qed
      have hsin: "sin \<theta> = snd y"
      proof (cases "snd y \<ge> 0")
        case True
        have "sin (arccos (fst y)) = sqrt (1 - fst y ^ 2)"
          using sin_arccos[OF hfst_bound(1) hfst_bound(2)] by (by100 simp)
        also have "\<dots> = sqrt (snd y ^ 2)"
        proof -
          have "1 - fst y ^ 2 = snd y ^ 2" using hy_eq by (by100 linarith)
          thus ?thesis by (by100 simp)
        qed
        also have "\<dots> = \<bar>snd y\<bar>" using real_sqrt_abs by (by100 blast)
        also have "\<dots> = snd y" using True by (by100 simp)
        finally show ?thesis unfolding \<theta>_def using True by (by100 simp)
      next
        case False
        have "sin (2*pi - arccos (fst y)) = - sin (arccos (fst y))"
          using sin_diff by (by5000 simp)
        also have "sin (arccos (fst y)) = sqrt (1 - fst y ^ 2)"
          using sin_arccos[OF hfst_bound(1) hfst_bound(2)] by (by100 simp)
        also have "sqrt (1 - fst y ^ 2) = sqrt (snd y ^ 2)"
        proof -
          have "1 - fst y ^ 2 = snd y ^ 2" using hy_eq by (by100 linarith)
          thus ?thesis by (by100 simp)
        qed
        also have "\<dots> = \<bar>snd y\<bar>" using real_sqrt_abs by (by100 blast)
        finally have "sin (2*pi - arccos (fst y)) = - \<bar>snd y\<bar>" by (by100 simp)
        also have "- \<bar>snd y\<bar> = snd y" using False by (by100 simp)
        finally have "sin (2*pi - arccos (fst y)) = snd y" .
        moreover have "\<theta> = 2*pi - arccos (fst y)" unfolding \<theta>_def using False by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      have h\<theta>_ge: "0 \<le> \<theta>"
      proof (cases "snd y \<ge> 0")
        case True thus ?thesis unfolding \<theta>_def using arccos_lbound[OF hfst_bound(1) hfst_bound(2)] by (by100 simp)
      next
        case False
        have "\<theta> = 2*pi - arccos (fst y)" unfolding \<theta>_def using False by (by100 simp)
        moreover have "arccos (fst y) \<le> pi" using arccos_ubound[OF hfst_bound(1) hfst_bound(2)] .
        ultimately show ?thesis using pi_gt_zero by (by100 linarith)
      qed
      have h\<theta>_lt: "\<theta> < 2*pi"
      proof (cases "snd y \<ge> 0")
        case True
        have "\<theta> = arccos (fst y)" unfolding \<theta>_def using True by (by100 simp)
        moreover have "arccos (fst y) \<le> pi" using arccos_ubound[OF hfst_bound(1) hfst_bound(2)] .
        ultimately show ?thesis using pi_gt_zero by (by100 linarith)
      next
        case False
        have "0 < arccos (fst y)"
        proof -
          have "fst y < 1"
          proof (rule ccontr)
            assume "\<not> fst y < 1" hence hfy1: "fst y = 1" using hfst_bound(2) by (by100 linarith)
            hence "fst y ^ 2 = 1" by (by100 simp)
            hence "snd y ^ 2 = 0" using hy_eq by (by100 linarith)
            hence "snd y * snd y = 0" using power2_eq_square[of "snd y"] by (by100 simp)
            hence "snd y = 0" by (by100 simp)
            thus False using False by (by100 linarith)
          qed
          moreover have "- 1 < fst y"
          proof (rule ccontr)
            assume "\<not> - 1 < fst y" hence "fst y = - 1" using hfst_bound(1) by (by100 linarith)
            hence "fst y ^ 2 = 1" by (by100 simp)
            hence "snd y ^ 2 = 0" using hy_eq by (by100 linarith)
            hence "snd y * snd y = 0" using power2_eq_square[of "snd y"] by (by100 simp)
            hence "snd y = 0" by (by100 simp)
            thus False using False by (by100 linarith)
          qed
          ultimately show ?thesis using arccos_lt_bounded by (by100 blast)
        qed
        have "\<theta> = 2*pi - arccos (fst y)" unfolding \<theta>_def using False by (by100 simp)
        thus ?thesis using \<open>0 < arccos (fst y)\<close> by (by100 linarith)
      qed
      \<comment> \<open>Find sector i: \<theta> \<in> [2\<pi>i/n, 2\<pi>(i+1)/n).\<close>
      define k where "k = nat \<lfloor>\<theta> * real n / (2*pi)\<rfloor>"
      have hn_pos: "real n > 0" using hn by (by100 simp)
      have h2pi_pos: "2*pi > 0" using pi_gt_zero by (by100 linarith)
      have hk_lt: "k < n"
      proof -
        have "\<theta> * real n / (2*pi) < real n" using h\<theta>_lt h2pi_pos hn_pos
          by (simp add: field_simps)
        hence "\<lfloor>\<theta> * real n / (2*pi)\<rfloor> < real n"
          by (by100 linarith)
        moreover have "0 \<le> \<theta> * real n / (2*pi)" using h\<theta>_ge hn_pos h2pi_pos
          by (by100 simp)
        hence "0 \<le> \<lfloor>\<theta> * real n / (2*pi)\<rfloor>" by (by100 linarith)
        ultimately show ?thesis unfolding k_def by (by100 linarith)
      qed
      have hk_lo: "2*pi*real k/real n \<le> \<theta>"
      proof -
        have hval_ge: "\<theta> * real n / (2*pi) \<ge> 0" using h\<theta>_ge hn_pos h2pi_pos by (by100 simp)
        have "real k = real (nat \<lfloor>\<theta> * real n / (2*pi)\<rfloor>)" unfolding k_def by (by100 simp)
        also have "\<dots> = \<lfloor>\<theta> * real n / (2*pi)\<rfloor>"
          using hval_ge by (by100 simp)
        also have "\<dots> \<le> \<theta> * real n / (2*pi)" using of_int_floor_le by (by100 simp)
        finally have "real k \<le> \<theta> * real n / (2*pi)" .
        thus ?thesis using h2pi_pos hn_pos by (simp add: field_simps)
      qed
      have hk_hi: "\<theta> < 2*pi*(real k + 1)/real n"
      proof -
        have "\<theta> * real n / (2*pi) < real k + 1"
        proof -
          have "\<lfloor>\<theta> * real n / (2*pi)\<rfloor> < real k + 1"
          proof -
            have "0 \<le> \<theta> * real n / (2*pi)" using h\<theta>_ge hn_pos h2pi_pos by (by100 simp)
            hence "0 \<le> \<lfloor>\<theta> * real n / (2*pi)\<rfloor>" by (by100 linarith)
            hence "real (nat \<lfloor>\<theta> * real n / (2*pi)\<rfloor>) = \<lfloor>\<theta> * real n / (2*pi)\<rfloor>"
              by (by100 simp)
            thus ?thesis unfolding k_def by (by100 linarith)
          qed
          moreover have "\<theta> * real n / (2*pi) < \<lfloor>\<theta> * real n / (2*pi)\<rfloor> + 1"
            by linarith
          ultimately show ?thesis unfolding k_def
            by (by100 linarith)
        qed
        thus ?thesis using h2pi_pos hn_pos by (simp add: field_simps)
      qed
      \<comment> \<open>Compute parameter t from \<theta>.\<close>
      define t where "t = \<theta> * real n / (2*pi) - real k"
      have ht0: "0 \<le> t" using hk_lo h2pi_pos hn_pos unfolding t_def by (simp add: field_simps)
      have ht1: "t < 1" using hk_hi h2pi_pos hn_pos unfolding t_def by (simp add: field_simps)
      have ht_I: "t \<in> I_set" unfolding top1_unit_interval_def using ht0 ht1 by (by100 auto)
      have h\<theta>_eq: "\<theta> = 2*pi*(real k + t)/real n" unfolding t_def
        using h2pi_pos hn_pos by (simp add: field_simps)
      \<comment> \<open>Construct boundary point.\<close>
      define x where "x = ((1-t)*vx k + t*vx(Suc k mod n), (1-t)*vy k + t*vy(Suc k mod n))"
      have hx_bd: "x \<in> ?BdP" unfolding x_def using hk_lt ht_I by (by100 blast)
      from hCramer_bd[OF hk_lt ht0] ht1
      have hb: "beta_cr k x = 1 - t" and hg: "gamma_cr k x = t"
        unfolding x_def by (by100 linarith)+
      have hic: "in_cone k x"
        unfolding in_cone_def using hb hg ht0 ht1 by (by100 linarith)
      have "\<psi> x = psi_local k x" using hpsi_eq[OF hk_lt hic] .
      also have "\<dots> = (cos \<theta>, sin \<theta>)"
      proof -
        have ht1': "t \<le> 1" using ht1 by (by100 linarith)
        have "psi_local k x = (cos (2*pi*(real k + t)/real n), sin (2*pi*(real k + t)/real n))"
          using hpsi_local_bd[OF hk_lt ht0 ht1'] unfolding x_def by (by100 simp)
        thus ?thesis using h\<theta>_eq by (by100 simp)
      qed
      also have "\<dots> = (fst y, snd y)" using hcos hsin by (by100 simp)
      also have "\<dots> = y" by (by100 simp)
      finally have "\<psi> x = y" .
      thus "y \<in> \<psi> ` ?BdP" using hx_bd by (by100 blast)
    qed
    have h\<psi>_int: "top1_homeomorphism_on (P - ?BdP)
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (P - ?BdP))
        (top1_B2 - top1_S1)
        (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1)) \<psi>"
    proof -
      \<comment> \<open>BdP \<subseteq> P: each boundary point is a convex combination of two vertices.\<close>
      have hBdP_sub: "?BdP \<subseteq> P"
      proof (rule UN_least)
        fix i assume "i \<in> {..<n}"
        hence hi: "i < n" by (by100 simp)
        show "{((1-t) * vx i + t * vx (Suc i mod n),
               (1-t) * vy i + t * vy (Suc i mod n)) | t. t \<in> I_set} \<subseteq> P"
        proof (rule subsetI)
          fix p assume "p \<in> {((1-t) * vx i + t * vx (Suc i mod n),
                             (1-t) * vy i + t * vy (Suc i mod n)) | t. t \<in> I_set}"
          then obtain t where ht: "t \<in> I_set" and
            hp: "p = ((1-t) * vx i + t * vx (Suc i mod n),
                      (1-t) * vy i + t * vy (Suc i mod n))" by (by100 blast)
          \<comment> \<open>p is a convex combination of v_i and v_{i+1} with coefficients (1-t) and t.\<close>
          define coeffs where "coeffs = (\<lambda>j. if j = i then (1 - t)
              else if j = Suc i mod n then t else 0::real)"
          have ht01: "0 \<le> t" "t \<le> 1" using ht
            unfolding top1_unit_interval_def by (by100 auto)+
          have hcge: "\<forall>j<n. coeffs j \<ge> 0" unfolding coeffs_def
            using ht01 by (by5000 auto)
          have hi2: "Suc i mod n < n" using hi assms(2) by (by100 simp)
          have hi_ne: "i \<noteq> Suc i mod n"
          proof (cases "Suc i < n")
            case True thus ?thesis by (by100 simp)
          next
            case False
            hence "Suc i = n" using hi by (by100 linarith)
            hence "Suc i mod n = 0" by (by100 simp)
            moreover have "i > 0 \<or> i = 0" by (by100 linarith)
            ultimately show ?thesis using hi \<open>Suc i = n\<close> assms(2) by (by100 linarith)
          qed
          have hfin: "finite ({..<n}::nat set)" by (by100 simp)
          have hi_in: "i \<in> {..<n}" using hi by (by100 simp)
          have hi2_in: "Suc i mod n \<in> {..<n}" using hi2 by (by100 simp)
          have hcsum: "(\<Sum>j<n. coeffs j) = 1"
          proof -
            have "(\<Sum>j<n. coeffs j) = coeffs i + (\<Sum>j\<in>{..<n} - {i}. coeffs j)"
              using sum.remove[OF hfin hi_in] by (by100 simp)
            also have "(\<Sum>j\<in>{..<n} - {i}. coeffs j) =
                coeffs (Suc i mod n) + (\<Sum>j\<in>{..<n} - {i} - {Suc i mod n}. coeffs j)"
            proof -
              have "Suc i mod n \<in> {..<n} - {i}" using hi2_in hi_ne by (by5000 auto)
              thus ?thesis using sum.remove[of "{..<n} - {i}" "Suc i mod n" coeffs]
                by (by100 simp)
            qed
            also have "coeffs i = 1 - t" unfolding coeffs_def using hi_ne by (by100 simp)
            also have "coeffs (Suc i mod n) = t" unfolding coeffs_def using hi_ne by (by100 simp)
            also have "(\<Sum>j\<in>{..<n} - {i} - {Suc i mod n}. coeffs j) = 0"
              by (rule sum.neutral) (simp add: coeffs_def)
            finally show ?thesis by (by100 simp)
          qed
          have hcx: "(\<Sum>j<n. coeffs j * vx j) = fst p"
          proof -
            have "(\<Sum>j<n. coeffs j * vx j) = coeffs i * vx i
                + (\<Sum>j\<in>{..<n} - {i}. coeffs j * vx j)"
              using sum.remove[OF hfin hi_in, of "\<lambda>j. coeffs j * vx j"] by (by100 simp)
            also have "(\<Sum>j\<in>{..<n} - {i}. coeffs j * vx j) =
                coeffs (Suc i mod n) * vx (Suc i mod n)
                + (\<Sum>j\<in>{..<n} - {i} - {Suc i mod n}. coeffs j * vx j)"
              using sum.remove[of "{..<n} - {i}" "Suc i mod n" "\<lambda>j. coeffs j * vx j"]
                hi2_in hi_ne by (by5000 auto)
            also have "(\<Sum>j\<in>{..<n} - {i} - {Suc i mod n}. coeffs j * vx j) = 0"
              by (rule sum.neutral) (simp add: coeffs_def)
            finally show ?thesis unfolding coeffs_def using hi_ne hp
              by (by100 simp)
          qed
          have hcy: "(\<Sum>j<n. coeffs j * vy j) = snd p"
          proof -
            have "(\<Sum>j<n. coeffs j * vy j) = coeffs i * vy i
                + (\<Sum>j\<in>{..<n} - {i}. coeffs j * vy j)"
              using sum.remove[OF hfin hi_in, of "\<lambda>j. coeffs j * vy j"] by (by100 simp)
            also have "(\<Sum>j\<in>{..<n} - {i}. coeffs j * vy j) =
                coeffs (Suc i mod n) * vy (Suc i mod n)
                + (\<Sum>j\<in>{..<n} - {i} - {Suc i mod n}. coeffs j * vy j)"
              using sum.remove[of "{..<n} - {i}" "Suc i mod n" "\<lambda>j. coeffs j * vy j"]
                hi2_in hi_ne by (by5000 auto)
            also have "(\<Sum>j\<in>{..<n} - {i} - {Suc i mod n}. coeffs j * vy j) = 0"
              by (rule sum.neutral) (simp add: coeffs_def)
            finally show ?thesis unfolding coeffs_def using hi_ne hp
              by (by100 simp)
          qed
          show "p \<in> P"
          proof -
            have hfp: "fst p = (\<Sum>i<n. coeffs i * vx i)" using hcx by (by100 simp)
            have hsp: "snd p = (\<Sum>i<n. coeffs i * vy i)" using hcy by (by100 simp)
            obtain px py where hpxy: "p = (px, py)" by (cases p) (by100 blast)
            have hpx: "px = (\<Sum>i<n. coeffs i * vx i)" using hfp hpxy by (by100 simp)
            have hpy: "py = (\<Sum>i<n. coeffs i * vy i)" using hsp hpxy by (by100 simp)
            have hwitness: "(\<forall>i<n. 0 \<le> coeffs i) \<and> sum coeffs {..<n} = 1 \<and>
                px = (\<Sum>i<n. coeffs i * vx i) \<and> py = (\<Sum>i<n. coeffs i * vy i)"
              using hcge hcsum hpx hpy by (by100 blast)
            have "(px, py) \<in> P" unfolding hP_hull mem_Collect_eq
            proof (intro exI conjI)
              show "(px, py) = ((\<Sum>i<n. coeffs i * vx i), (\<Sum>i<n. coeffs i * vy i))"
                using hpx hpy by (by100 simp)
              show "\<forall>i<n. (0::real) \<le> coeffs i" using hcge by (by100 blast)
              show "sum coeffs {..<n} = (1::real)" using hcsum by (by100 blast)
              show "(\<Sum>i<n. coeffs i * vx i) = (\<Sum>i<n. coeffs i * vx i)" by (by100 simp)
              show "(\<Sum>i<n. coeffs i * vy i) = (\<Sum>i<n. coeffs i * vy i)" by (by100 simp)
            qed
            thus ?thesis using hpxy by (by100 simp)
          qed
        qed
      qed
      \<comment> \<open>P - BdP \<subseteq> P\<close>
      have hPBdP_sub: "P - ?BdP \<subseteq> P" by (by100 blast)
      \<comment> \<open>\<psi> ` (P - BdP) = B2 - S1 (from injectivity + surjectivity + boundary image).\<close>
      have h\<psi>_img: "\<psi> ` (P - ?BdP) = top1_B2 - top1_S1"
      proof (rule set_eqI)
        fix y show "y \<in> \<psi> ` (P - ?BdP) \<longleftrightarrow> y \<in> top1_B2 - top1_S1"
        proof
          assume "y \<in> \<psi> ` (P - ?BdP)"
          then obtain x where hx: "x \<in> P - ?BdP" and hy: "y = \<psi> x" by (by100 blast)
          have "x \<in> P" using hx by (by100 blast)
          hence "\<psi> x \<in> \<psi> ` P" by (by100 blast)
          hence "\<psi> x \<in> top1_B2" using h\<psi>_surj by (by100 blast)
          have "y \<in> top1_B2" using hy \<open>\<psi> x \<in> top1_B2\<close> by (by100 blast)
          moreover have "y \<notin> top1_S1"
          proof
            assume "y \<in> top1_S1"
            hence "y \<in> \<psi> ` ?BdP" using h\<psi>_bd by (by100 blast)
            then obtain x' where hx': "x' \<in> ?BdP" and hy': "\<psi> x' = y" by (by100 blast)
            have "x' \<in> P" using hx' hBdP_sub by (by100 blast)
            have "x \<in> P" using hx by (by100 blast)
            from h\<psi>_inj have "x = x'"
              using \<open>x \<in> P\<close> \<open>x' \<in> P\<close> hy hy' unfolding inj_on_def by (by100 blast)
            thus False using hx hx' by (by100 blast)
          qed
          ultimately show "y \<in> top1_B2 - top1_S1" by (by100 blast)
        next
          assume "y \<in> top1_B2 - top1_S1"
          hence hy_B2: "y \<in> top1_B2" and hy_nS1: "y \<notin> top1_S1" by (by100 blast)+
          have "y \<in> \<psi> ` P" using hy_B2 h\<psi>_surj by (by100 blast)
          then obtain x where hx: "x \<in> P" and hy: "\<psi> x = y" by (by100 blast)
          have "x \<notin> ?BdP"
          proof
            assume "x \<in> ?BdP"
            hence "y \<in> \<psi> ` ?BdP" using hy by (by100 blast)
            hence "y \<in> top1_S1" using h\<psi>_bd by (by100 blast)
            thus False using hy_nS1 by (by100 blast)
          qed
          hence "x \<in> P - ?BdP" using hx by (by100 blast)
          thus "y \<in> \<psi> ` (P - ?BdP)" using hy by (by100 blast)
        qed
      qed
      \<comment> \<open>Apply homeomorphism_on_restrict to get homeomorphism on P-BdP.\<close>
      from homeomorphism_on_restrict[OF h\<psi>_homeo hPBdP_sub]
      have hrestr: "top1_homeomorphism_on (P - ?BdP)
          (subspace_topology P ?TP (P - ?BdP))
          (\<psi> ` (P - ?BdP)) (subspace_topology top1_B2 top1_B2_topology (\<psi> ` (P - ?BdP))) \<psi>"
        .
      \<comment> \<open>Rewrite subspace_topology P ?TP (P-BdP) = subspace_topology UNIV R2top (P-BdP)
           using subspace_topology_trans.\<close>
      have hTP_eq: "subspace_topology P ?TP (P - ?BdP) =
          subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (P - ?BdP)"
        using subspace_topology_trans[of "P - ?BdP" P UNIV
            "product_topology_on top1_open_sets top1_open_sets"] hPBdP_sub
        by (by100 simp)
      show ?thesis using hrestr h\<psi>_img hTP_eq by (by100 simp)
    qed
    \<comment> \<open>Edge-to-arc: \<psi> maps edge i at parameter t to (cos(2\<pi>(i+t)/n), sin(2\<pi>(i+t)/n)).
       From the cone construction: z on edge i has \<beta>=1-t, \<gamma>=t, s=1, u=t.\<close>
    have h\<psi>_edge_arc: "\<forall>i<n. \<forall>t\<in>I_set. \<psi> ((1-t) * vx i + t * vx (Suc i mod n),
                                (1-t) * vy i + t * vy (Suc i mod n))
        = (cos (2 * pi * (real i + t) / real n), sin (2 * pi * (real i + t) / real n))"
    proof (intro allI impI ballI)
      fix i :: nat and t :: real
      assume hi: "i < n" and ht: "t \<in> I_set"
      let ?z = "((1-t) * vx i + t * vx (Suc i mod n), (1-t) * vy i + t * vy (Suc i mod n))"
      \<comment> \<open>z is on edge i, hence in cone i.\<close>
      have ht01: "0 \<le> t \<and> t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)
      \<comment> \<open>Cramer coordinates for z on edge i: \<beta> = 1-t, \<gamma> = t.\<close>
      have hDi_ne: "Di i \<noteq> 0" using hDi_pos[OF hi] by (by100 linarith)
      have h\<beta>: "beta_cr i ?z = 1 - t"
      proof -
        \<comment> \<open>fst ?z - cx = (1-t)*(vx i - cx) + t*(vx(i+1) - cx),
           snd ?z - cy = (1-t)*(vy i - cy) + t*(vy(i+1) - cy).
           cross2(fst z - cx, snd z - cy)(vx(i+1)-cx, vy(i+1)-cy)
           = ((1-t)*(vx i-cx) + t*(vx(i+1)-cx))*(vy(i+1)-cy)
             - ((1-t)*(vy i-cy) + t*(vy(i+1)-cy))*(vx(i+1)-cx)
           = (1-t)*((vx i-cx)*(vy(i+1)-cy) - (vy i-cy)*(vx(i+1)-cx)) + t*0
           = (1-t)*Di i.\<close>
        have "cross2 (fst ?z - cx, snd ?z - cy) (vx (Suc i mod n) - cx, vy (Suc i mod n) - cy)
            = (1 - t) * Di i"
          unfolding cross2_def Di_def by (simp add: algebra_simps)
        thus ?thesis unfolding beta_cr_def using hDi_ne by (by100 simp)
      qed
      have h\<gamma>: "gamma_cr i ?z = t"
      proof -
        \<comment> \<open>cross2(vx i - cx, vy i - cy)(fst z - cx, snd z - cy)
           = (vx i-cx)*((1-t)*(vy i-cy) + t*(vy(i+1)-cy))
             - (vy i-cy)*((1-t)*(vx i-cx) + t*(vx(i+1)-cx))
           = (1-t)*0 + t*((vx i-cx)*(vy(i+1)-cy) - (vy i-cy)*(vx(i+1)-cx))
           = t*Di i.\<close>
        have "cross2 (vx i - cx, vy i - cy) (fst ?z - cx, snd ?z - cy) = t * Di i"
          unfolding cross2_def Di_def by (simp add: algebra_simps)
        thus ?thesis unfolding gamma_cr_def using hDi_ne by (by100 simp)
      qed
      \<comment> \<open>s = \<beta> + \<gamma> = 1, u = \<gamma>/s = t.\<close>
      have hs: "beta_cr i ?z + gamma_cr i ?z = 1" using h\<beta> h\<gamma> by (by100 simp)
      have hu: "(if beta_cr i ?z + gamma_cr i ?z = 0 then 0
                 else gamma_cr i ?z / (beta_cr i ?z + gamma_cr i ?z)) = t"
        using h\<beta> h\<gamma> hs by (by100 simp)
      \<comment> \<open>\<theta> = 2\<pi>(i + t)/n.\<close>
      \<comment> \<open>psi\_local i z = (s * cos \<theta>, s * sin \<theta>) = (cos \<theta>, sin \<theta>) since s = 1.\<close>
      have hpsi_local: "psi_local i ?z = (cos (2 * pi * (real i + t) / real n),
          sin (2 * pi * (real i + t) / real n))"
        unfolding psi_local_def Let_def using hs hu by (by100 simp)
      \<comment> \<open>\<psi> z = psi\_local (SOME i'. in\_cone i' z) z.
         On edge i, z is in cone i (or cone (i-1)), and psi\_local agrees.\<close>
      have "\<psi> ?z = psi_local i ?z"
      proof -
        have "in_cone i ?z" unfolding in_cone_def using h\<beta> h\<gamma> ht01 by (by100 simp)
        thus ?thesis using hpsi_eq[OF hi] by (by100 simp)
      qed
      thus "\<psi> ?z = (cos (2 * pi * (real i + t) / real n), sin (2 * pi * (real i + t) / real n))"
        using hpsi_local by (by100 simp)
    qed
    show ?thesis
      apply (rule exI[of _ \<psi>])
      apply (intro conjI)
      using h\<psi>_homeo apply (by100 blast)
      using h\<psi>_bd apply (by100 blast)
      using h\<psi>_int apply (by100 blast)
      using h\<psi>_edge_arc apply (by100 blast)
      done
  qed
  then obtain \<psi> where h\<psi>1: "top1_homeomorphism_on P ?TP top1_B2 top1_B2_topology \<psi>"
      and h\<psi>2: "\<psi> ` ?BdP = top1_S1"
      and h\<psi>3: "top1_homeomorphism_on (P - ?BdP)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (P - ?BdP))
          (top1_B2 - top1_S1)
          (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1)) \<psi>"
      and h\<psi>4: "\<forall>i<n. \<forall>t\<in>I_set. \<psi> ((1-t) * vx i + t * vx (Suc i mod n),
                              (1-t) * vy i + t * vy (Suc i mod n))
          = (cos (2 * pi * (real i + t) / real n), sin (2 * pi * (real i + t) / real n))"
    by - (erule exE, (erule conjE)+, rule that, assumption+)
  show ?thesis
    apply (rule exI[of _ \<psi>])
    apply (intro conjI)
    using h\<psi>1 apply (by100 blast)
    using h\<psi>2 apply (by100 blast)
    using h\<psi>3 apply (by100 blast)
    using h\<psi>4 apply (by100 blast)
    done
qed

text \<open>Note: convex\_polygon\_vertex\_half\_plane and ccw\_polygon\_no\_collinear
  were removed per reviewer advice. These conditions are now derived from the
  strict edge-side condition added to top1\_quotient\_of\_scheme\_on, rather than
  proved from CCW + convex hull alone (which has a bootstrapping issue, and
  the non-strict half-plane does not imply no-collinearity for degenerate polygons).\<close>

text \<open>Lemma 3: Torus scheme vertex connectivity.
  In the torus scheme [(a1,+),(b1,+),(a1,-),(b1,-),...,(an,+),(bn,+),(an,-),(bn,-)],
  the edge identifications (same label, opposite orientation = reversed edge) imply
  that all vertices are identified under any quotient map respecting the scheme.\<close>
text \<open>Helper for torus vertex connectivity: all vertices identified with v\_0.\<close>
lemma torus_scheme_all_eq_v0:
  fixes n :: nat
  defines "scheme \<equiv> concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                                       (2*i, False), (2*i+1, False)]) [0..<n])"
  assumes hedge: "\<forall>i<length scheme. \<forall>j<length scheme.
      fst (scheme!i) = fst (scheme!j) \<longrightarrow>
      (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
         (1-t) * vy i + t * vy (Suc i mod length scheme))
       = (if snd (scheme!i) = snd (scheme!j)
          then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                  (1-t) * vy j + t * vy (Suc j mod length scheme))
          else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                  t * vy j + (1-t) * vy (Suc j mod length scheme))))"
  shows "\<And>i. i < length scheme \<Longrightarrow> q (vx i, vy i) = q (vx 0, vy 0)"
proof -
  have hlen: "length scheme = 4 * n" unfolding scheme_def
    by (induct n) (by100 simp)+
  \<comment> \<open>Scheme access: scheme!(4k+r) for block k.\<close>
  \<comment> \<open>Scheme access: scheme!(4k+r) for block k, offset r.\<close>
  define f where "f i = [(2*i, True), (2*i+1, True), (2*i, False), (2*i+1, False)]"
    for i :: nat
  have hf_len: "\<And>i. length (f i) = 4" unfolding f_def by (by100 simp)
  have hscheme_f: "scheme = concat (map f [0..<n])" unfolding scheme_def f_def by (by100 simp)
  \<comment> \<open>Key: concat(map f [0..<n]) ! (4k+r) = f(k) ! r when k < n and r < 4.\<close>
  have hnth: "\<And>k r. k < n \<Longrightarrow> r < 4 \<Longrightarrow> scheme ! (4*k+r) = f k ! r"
    unfolding hscheme_f
  proof (induct n)
    case 0 thus ?case by (by100 simp)
  next
    case (Suc n')
    have hconcat_app: "concat (map f [0..<Suc n']) = concat (map f [0..<n']) @ f n'"
      by (by100 simp)
    have hlen_prefix: "length (concat (map f [0..<n'])) = 4 * n'"
      using hf_len by (induct n') (by100 simp)+
    show ?case
    proof (cases "k < n'")
      case True
      have "4*k+r < 4*n'" using True Suc.prems(2) by (by100 linarith)
      hence "4*k+r < length (concat (map f [0..<n']))" using hlen_prefix by (by100 linarith)
      hence "concat (map f [0..<Suc n']) ! (4*k+r) = concat (map f [0..<n']) ! (4*k+r)"
        unfolding hconcat_app using nth_append[of "concat (map f [0..<n'])" "f n'" "4*k+r"]
        by (by100 simp)
      thus ?thesis using Suc.hyps[OF True Suc.prems(2)] by (by100 simp)
    next
      case False
      hence hk: "k = n'" using Suc.prems(1) by (by100 linarith)
      have "concat (map f [0..<Suc n']) ! (4*k+r) = (concat (map f [0..<n']) @ f n') ! (4*n'+r)"
        unfolding hconcat_app hk by (by100 simp)
      also have "\<dots> = f n' ! r"
        using nth_append_length_plus[of "concat (map f [0..<n'])" "f n'" r]
          hlen_prefix by (by100 simp)
      finally show ?thesis using hk by (by100 simp)
    qed
  qed
  have hscheme_0: "\<And>k. k < n \<Longrightarrow> scheme ! (4*k) = (2*k, True)"
    using hnth[of _ 0] unfolding f_def by (by100 simp)
  have hscheme_1: "\<And>k. k < n \<Longrightarrow> scheme ! (4*k+1) = (2*k+1, True)"
    using hnth[of _ 1] unfolding f_def by (by100 simp)
  have hscheme_2: "\<And>k. k < n \<Longrightarrow> scheme ! (4*k+2) = (2*k, False)"
    using hnth[of _ 2] unfolding f_def by (by100 simp)
  have hscheme_3: "\<And>k. k < n \<Longrightarrow> scheme ! (4*k+3) = (2*k+1, False)"
    using hnth[of _ 3] unfolding f_def by (by100 simp)
  \<comment> \<open>Index bounds.\<close>
  have hidx: "\<And>k r. k < n \<Longrightarrow> r < 4 \<Longrightarrow> 4*k+r < length scheme"
    using hlen by (by100 linarith)
  \<comment> \<open>Edge pairing: edges 4k and 4k+2 share label 2k, opposite orientation.
     At t=0: q(v_{4k}) = q(v_{4k+3}). At t=1: q(v_{4k+1}) = q(v_{4k+2}).\<close>
  have hpair_a: "\<And>k. k < n \<Longrightarrow>
      q (vx (4*k), vy (4*k)) = q (vx (4*k+3), vy (4*k+3))"
  proof -
    fix k assume hk: "k < n"
    \<comment> \<open>Edge 4k has label (2k,T), edge 4k+2 has label (2k,F). Same fst, different snd.\<close>
    have h_fst: "fst (scheme!(4*k)) = fst (scheme!(4*k+2))"
      using hscheme_0[OF hk] hscheme_2[OF hk] by (by100 simp)
    have h_snd: "snd (scheme!(4*k)) \<noteq> snd (scheme!(4*k+2))"
      using hscheme_0[OF hk] hscheme_2[OF hk] by (by100 simp)
    have hi: "4*k < length scheme" using hidx[OF hk, of 0] by (by100 simp)
    have hj: "4*k+2 < length scheme" using hidx[OF hk, of 2] by (by100 simp)
    \<comment> \<open>Apply hedge with i=4k, j=4k+2, t=0.\<close>
    have h0: "0 \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
    have hSuc_4k: "Suc (4*k) mod length scheme = 4*k+1"
      using hi hlen by (by100 simp)
    have hSuc_4k2: "Suc (4*k+2) mod length scheme = 4*k+3"
    proof -
      have "4*k+3 < 4*n" using hk by (by100 linarith)
      hence "4*k+3 < length scheme" using hlen by (by100 linarith)
      thus ?thesis using hlen by (by100 simp)
    qed
    from hedge[rule_format, OF hi hj h_fst, rule_format, OF h0]
    show "q (vx (4*k), vy (4*k)) = q (vx (4*k+3), vy (4*k+3))"
      using h_snd hSuc_4k hSuc_4k2 by (by100 simp)
  qed
  have hpair_b: "\<And>k. k < n \<Longrightarrow>
      q (vx (4*k+1), vy (4*k+1)) = q (vx (4*k+2), vy (4*k+2))"
  proof -
    fix k assume hk: "k < n"
    have h_fst: "fst (scheme!(4*k)) = fst (scheme!(4*k+2))"
      using hscheme_0[OF hk] hscheme_2[OF hk] by (by100 simp)
    have h_snd: "snd (scheme!(4*k)) \<noteq> snd (scheme!(4*k+2))"
      using hscheme_0[OF hk] hscheme_2[OF hk] by (by100 simp)
    have hi: "4*k < length scheme" using hidx[OF hk, of 0] by (by100 simp)
    have hj: "4*k+2 < length scheme" using hidx[OF hk, of 2] by (by100 simp)
    have h1: "1 \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
    have hSuc_4k: "Suc (4*k) mod length scheme = 4*k+1"
      using hi hlen by (by100 simp)
    have hSuc_4k2: "Suc (4*k+2) mod length scheme = 4*k+3"
    proof -
      have "4*k+3 < length scheme" using hk hlen by (by100 linarith)
      thus ?thesis using hlen by (by100 simp)
    qed
    from hedge[rule_format, OF hi hj h_fst, rule_format, OF h1]
    show "q (vx (4*k+1), vy (4*k+1)) = q (vx (4*k+2), vy (4*k+2))"
      using h_snd hSuc_4k hSuc_4k2 by (by100 simp)
  qed
  have hpair_c: "\<And>k. k < n \<Longrightarrow>
      q (vx (4*k+2), vy (4*k+2)) = q (vx (4*k+3), vy (4*k+3))"
  proof -
    fix k assume hk: "k < n"
    have h_fst: "fst (scheme!(4*k+1)) = fst (scheme!(4*k+3))"
      using hscheme_1[OF hk] hscheme_3[OF hk] by (by100 simp)
    have h_snd: "snd (scheme!(4*k+1)) \<noteq> snd (scheme!(4*k+3))"
      using hscheme_1[OF hk] hscheme_3[OF hk] by (by100 simp)
    have hi: "4*k+1 < length scheme" using hidx[OF hk, of 1] by (by100 simp)
    have hj: "4*k+3 < length scheme" using hidx[OF hk, of 3] by (by100 simp)
    have h1: "1 \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
    have hSuc_4k1: "Suc (4*k+1) mod length scheme = 4*k+2"
    proof -
      have "4*k+2 < length scheme" using hk hlen by (by100 linarith)
      thus ?thesis using hlen by (by100 simp)
    qed
    have hSuc_4k3: "Suc (4*k+3) mod length scheme = 4*((k+1) mod n)"
    proof -
      have "Suc (4*k+3) = 4*(k+1)" by (by100 simp)
      hence "Suc (4*k+3) mod length scheme = 4*(k+1) mod (4*n)" using hlen by (by100 simp)
      also have "\<dots> = 4 * ((k+1) mod n)"
        using mult_mod_right[of 4 "k+1" n, symmetric] by (by100 simp)
      finally show ?thesis .
    qed
    from hedge[rule_format, OF hi hj h_fst, rule_format, OF h1]
    show "q (vx (4*k+2), vy (4*k+2)) = q (vx (4*k+3), vy (4*k+3))"
      using h_snd hSuc_4k1 hSuc_4k3 by (by100 simp)
  qed
  \<comment> \<open>Link between blocks: edges 4k+1 and 4k+3, t=0:
     q(v_{4k+1}) = q(v_{Suc(4k+3) mod 4n}) = q(v_{4(k+1) mod n}).\<close>
  have hlink: "\<And>k. k < n \<Longrightarrow>
      q (vx (4*k+1), vy (4*k+1)) = q (vx (4*((k+1) mod n)), vy (4*((k+1) mod n)))"
  proof -
    fix k assume hk: "k < n"
    have h_fst: "fst (scheme!(4*k+1)) = fst (scheme!(4*k+3))"
      using hscheme_1[OF hk] hscheme_3[OF hk] by (by100 simp)
    have h_snd: "snd (scheme!(4*k+1)) \<noteq> snd (scheme!(4*k+3))"
      using hscheme_1[OF hk] hscheme_3[OF hk] by (by100 simp)
    have hi: "4*k+1 < length scheme" using hidx[OF hk, of 1] by (by100 simp)
    have hj: "4*k+3 < length scheme" using hidx[OF hk, of 3] by (by100 simp)
    have h0: "0 \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
    have hSuc_4k1: "Suc (4*k+1) mod length scheme = 4*k+2"
    proof -
      have "4*k+2 < length scheme" using hk hlen by (by100 linarith)
      thus ?thesis using hlen by (by100 simp)
    qed
    have hSuc_4k3: "Suc (4*k+3) mod length scheme = 4*((k+1) mod n)"
    proof -
      have "Suc (4*k+3) = 4*(k+1)" by (by100 simp)
      hence "Suc (4*k+3) mod length scheme = 4*(k+1) mod (4*n)" using hlen by (by100 simp)
      also have "\<dots> = 4 * ((k+1) mod n)"
        using mult_mod_right[of 4 "k+1" n, symmetric] by (by100 simp)
      finally show ?thesis .
    qed
    from hedge[rule_format, OF hi hj h_fst, rule_format, OF h0]
    show "q (vx (4*k+1), vy (4*k+1)) = q (vx (4*((k+1) mod n)), vy (4*((k+1) mod n)))"
      using h_snd hSuc_4k1 hSuc_4k3 by (by100 simp)
  qed
  \<comment> \<open>Chain within block k: q(v_{4k}) = q(v_{4k+3}) = q(v_{4k+2}) = q(v_{4k+1}).\<close>
  have hblock_eq: "\<And>k r. k < n \<Longrightarrow> r < 4 \<Longrightarrow>
      q (vx (4*k+r), vy (4*k+r)) = q (vx (4*k), vy (4*k))"
  proof -
    fix k r :: nat assume hk: "k < n" and hr: "r < 4"
    show "q (vx (4*k+r), vy (4*k+r)) = q (vx (4*k), vy (4*k))"
    proof -
      have ha: "q (vx (4*k), vy (4*k)) = q (vx (4*k+3), vy (4*k+3))" using hpair_a[OF hk] .
      have hb: "q (vx (4*k+1), vy (4*k+1)) = q (vx (4*k+2), vy (4*k+2))" using hpair_b[OF hk] .
      have hc: "q (vx (4*k+2), vy (4*k+2)) = q (vx (4*k+3), vy (4*k+3))" using hpair_c[OF hk] .
      from hr have "r = 0 \<or> r = 1 \<or> r = 2 \<or> r = 3" by (by100 linarith)
      thus ?thesis using ha hb hc by (by100 force)
    qed
  qed
  \<comment> \<open>Chain across blocks: q(v_{4k}) = q(v_0) by induction using hlink.\<close>
  have hblock_0: "\<And>k. k < n \<Longrightarrow> q (vx (4*k), vy (4*k)) = q (vx 0, vy 0)"
  proof -
    fix k show "k < n \<Longrightarrow> q (vx (4*k), vy (4*k)) = q (vx 0, vy 0)"
    proof (induct k)
      case 0 thus ?case by (by100 simp)
    next
      case (Suc k')
      hence hk': "k' < n" by (by100 linarith)
      have hIH: "q (vx (4*k'), vy (4*k')) = q (vx 0, vy 0)"
        using Suc.hyps hk' by (by100 simp)
      have "q (vx (4*k'+1), vy (4*k'+1)) = q (vx (4*k'), vy (4*k'))"
        using hblock_eq[OF hk', of 1] by (by100 simp)
      moreover have "q (vx (4*k'+1), vy (4*k'+1)) = q (vx (4*Suc k'), vy (4*Suc k'))"
      proof -
        have "(k'+1) mod n = Suc k'" using Suc.prems by (by100 simp)
        thus ?thesis using hlink[OF hk'] by (by100 simp)
      qed
      ultimately show ?case using hIH by (by100 simp)
    qed
  qed
  \<comment> \<open>Combine: any i < 4n decomposes as i = 4k+r, so q(v_i) = q(v_{4k}) = q(v_0).\<close>
  fix i :: nat assume hi: "i < length scheme"
  define k where "k = i div 4"
  define r where "r = i mod 4"
  have "i = 4*k + r" unfolding k_def r_def by (by100 simp)
  have "k < n" using hi hlen k_def by (by100 simp)
  have "r < 4" unfolding r_def by (by100 simp)
  have "q (vx i, vy i) = q (vx (4*k+r), vy (4*k+r))" using \<open>i = 4*k + r\<close> by (by100 simp)
  also have "\<dots> = q (vx (4*k), vy (4*k))" using hblock_eq[OF \<open>k < n\<close> \<open>r < 4\<close>] .
  also have "\<dots> = q (vx 0, vy 0)" using hblock_0[OF \<open>k < n\<close>] .
  finally show "q (vx i, vy i) = q (vx 0, vy 0)" .
qed

lemma torus_scheme_vertex_connectivity:
  fixes n :: nat
  defines "scheme \<equiv> concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                                       (2*i, False), (2*i+1, False)]) [0..<n])"
  shows "\<forall>q (vx::nat\<Rightarrow>real) (vy::nat\<Rightarrow>real).
      (\<forall>i<length scheme. \<forall>j<length scheme.
        fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
           (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme)))))
      \<longrightarrow> (\<forall>i<length scheme. \<forall>j<length scheme. q (vx i, vy i) = q (vx j, vy j))"
  apply (intro allI impI)
  subgoal for q vx vy
    using torus_scheme_all_eq_v0[of n q vx vy]
    unfolding scheme_def
    by (by5000 force)
  done

text \<open>Path splitting lemma: a loop f: [0,1] \<rightarrow> X that passes through x0 at
  s = k/n (for k = 0,...,n) is path-homotopic to the product of n sub-loops
  f\_k: [0,1] \<rightarrow> X defined by f\_k(s) = f((k+s)/n).
  This is the key infrastructure for Theorem 74.2s relator identification.\<close>
lemma foldr_path_product_loops_is_loop:
  assumes htop: "is_topology_on X TX"
      and hbase: "top1_is_loop_on X TX x0 base"
      and hloops: "\<forall>g \<in> set gs. top1_is_loop_on X TX x0 g"
  shows "top1_is_loop_on X TX x0 (foldr top1_path_product gs base)"
  using hloops
proof (induct gs)
  case Nil show ?case using hbase by (by100 simp)
next
  case (Cons g gs')
  hence hg: "top1_is_loop_on X TX x0 g" by (by100 simp)
  have hgs': "\<forall>g \<in> set gs'. top1_is_loop_on X TX x0 g" using Cons.prems by (by100 simp)
  have hIH: "top1_is_loop_on X TX x0 (foldr top1_path_product gs' base)"
    using Cons.hyps[OF hgs'] .
  show ?case unfolding top1_is_loop_on_def
    using top1_path_product_is_path[OF htop
        hg[unfolded top1_is_loop_on_def]
        hIH[unfolded top1_is_loop_on_def]] by (by100 simp)
qed

text \<open>Helper: splitting a loop at 1/n gives f \<simeq> sub\_0 * g
  where g(s) = f(1/n + s*(n-1)/n). Uses reparam\_path\_homotopy.\<close>
lemma loop_split_first:
  assumes htop: "is_topology_on X TX"
      and hloop: "top1_is_loop_on X TX x0 f"
      and hn: "n \<ge> 2"
      and hvertex: "f (1 / real n) = x0"
  defines "sub0 \<equiv> (\<lambda>s. f (s / real n))"
      and "g \<equiv> (\<lambda>s. f (1 / real n + s * (real n - 1) / real n))"
  shows "top1_loop_equiv_on X TX x0 f (top1_path_product sub0 g)"
proof -
  have hn_pos: "real n > 0" using hn by (by100 simp)
  have hf_cont: "top1_continuous_map_on I_set top1_unit_interval_topology X TX f"
    using hloop unfolding top1_is_loop_on_def top1_is_path_on_def top1_unit_interval_def
    by (by100 blast)
  have hf_range: "\<forall>s\<in>I_set. f s \<in> X"
    using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
  have hf0: "f 0 = x0" using hloop unfolding top1_is_loop_on_def top1_is_path_on_def
    by (by100 blast)
  have hf1: "f 1 = x0" using hloop unfolding top1_is_loop_on_def top1_is_path_on_def
    by (by100 blast)
  \<comment> \<open>Define \<psi>: the splitting reparametrization.\<close>
  define \<psi> where "\<psi> s = (if s \<le> 1/2 then 2*s / real n
      else 1 / real n + (2*s - 1) * (real n - 1) / real n)" for s :: real
  \<comment> \<open>\<psi>(0) = 0, \<psi>(1) = 1.\<close>
  have h\<psi>0: "\<psi> 0 = 0" unfolding \<psi>_def by (by100 simp)
  have h\<psi>1: "\<psi> 1 = 1"
  proof -
    have "1 / real n + (2*1 - 1) * (real n - 1) / real n = real n / real n"
      by (simp add: field_simps)
    thus ?thesis unfolding \<psi>_def using hn_pos by (by100 simp)
  qed
  \<comment> \<open>\<psi> maps I\_set to I\_set.\<close>
  have h\<psi>_range: "\<forall>s\<in>I_set. \<psi> s \<in> I_set"
  proof (intro ballI)
    fix s :: real assume hs: "s \<in> I_set"
    hence hs01: "0 \<le> s" "s \<le> 1" unfolding top1_unit_interval_def by (by100 auto)+
    show "\<psi> s \<in> I_set" unfolding top1_unit_interval_def
    proof (cases "s \<le> 1/2")
      case True
      hence "\<psi> s = 2*s / real n" unfolding \<psi>_def by (by100 simp)
      moreover have "0 \<le> 2*s / real n" using hs01 hn_pos by (by100 simp)
      moreover have "2*s / real n \<le> 1" using True hn by (by100 simp)
      ultimately show "\<psi> s \<in> {0..1}" by (by100 auto)
    next
      case False
      hence hs_gt: "s > 1/2" by (by100 simp)
      hence "\<psi> s = 1/real n + (2*s-1)*(real n-1)/real n" unfolding \<psi>_def by (by100 simp)
      moreover have "0 \<le> 1/real n + (2*s-1)*(real n-1)/real n"
        using hs01 hs_gt hn_pos by (by100 simp)
      moreover have "1/real n + (2*s-1)*(real n-1)/real n \<le> 1"
      proof -
        have "(2*s-1) \<le> 1" using hs01 by (by100 linarith)
        hence "(2*s-1)*(real n-1)/real n \<le> 1*(real n-1)/real n"
          using hn by (intro divide_right_mono mult_right_mono) (by100 simp)+
        also have "1*(real n-1)/real n = (real n - 1)/real n" by (by100 simp)
        finally have "(2*s-1)*(real n-1)/real n \<le> (real n-1)/real n" .
        moreover have "1/real n + (real n-1)/real n = real n / real n"
          by (simp add: field_simps)
        moreover have "real n / real n = 1" using hn_pos by (by100 simp)
        ultimately show ?thesis by (by100 linarith)
      qed
      ultimately show "\<psi> s \<in> {0..1}" by (by100 auto)
    qed
  qed
  \<comment> \<open>\<psi> is continuous on I\_set.\<close>
  have h\<psi>_cont: "top1_continuous_map_on I_set top1_unit_interval_topology
      I_set top1_unit_interval_topology \<psi>"
  proof -
    define f1 where "f1 s = 2 * s / real n" for s :: real
    define f2 where "f2 s = 1 / real n + (2*s - 1) * (real n - 1) / real n" for s :: real
    have hf1_cont: "continuous_on UNIV f1" unfolding f1_def
      using hn_pos by (intro continuous_intros) (by100 simp)+
    have hf2_cont: "continuous_on UNIV f2" unfolding f2_def
      using hn_pos by (intro continuous_intros) (by100 simp)+
    \<comment> \<open>At junction s=1/2: f1(1/2) = 1/n = f2(1/2).\<close>
    have hjunction1: "\<And>s::real. s \<le> 1/2 \<Longrightarrow> \<not> (s \<le> 1/2) \<Longrightarrow> f1 s = f2 s"
      by (by100 simp)
    have hjunction2: "\<And>s::real. \<not> (s \<le> 1/2) \<Longrightarrow> s \<le> 1/2 \<Longrightarrow> f1 s = f2 s"
      by (by100 simp)
    have h\<psi>_cont_univ: "continuous_on (UNIV :: real set) \<psi>"
    proof -
      have "continuous_on ({..1/2} \<union> {1/2..}) (\<lambda>s. if s \<le> 1/2 then f1 s else f2 s)"
      proof (rule continuous_on_If)
        show "closed ({..1/2::real})" by (by100 simp)
        show "closed ({1/2::real..})" by (by100 simp)
        show "continuous_on {..1/2} f1" using continuous_on_subset[OF hf1_cont] by (by100 blast)
        show "continuous_on {1/2..} f2" using continuous_on_subset[OF hf2_cont] by (by100 blast)
        fix s :: real assume "s \<in> {..1/2}" "\<not> s \<le> 1/2"
        thus "f1 s = f2 s" by (by100 simp)
      next
        fix s :: real assume "s \<in> {1/2::real..}" "s \<le> 1/2"
        hence hs: "s = 1/2" by (by100 simp)
        show "f1 s = f2 s" unfolding f1_def f2_def hs by (by100 simp)
      qed
      moreover have "{..1/2::real} \<union> {1/2..} = UNIV" by (by100 auto)
      moreover have "\<And>s. \<psi> s = (if s \<le> 1/2 then f1 s else f2 s)"
        unfolding \<psi>_def f1_def f2_def by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    show ?thesis unfolding top1_unit_interval_def
      using top1_continuous_map_on_real_subspace_open_sets[of "{0..1}" \<psi> "{0..1}"]
        h\<psi>_range h\<psi>_cont_univ
      unfolding top1_unit_interval_def
      using top1_unit_interval_def top1_unit_interval_topology_def by (by5000 simp)
  qed
  \<comment> \<open>id is continuous on I\_set.\<close>
  have hid_cont: "top1_continuous_map_on I_set top1_unit_interval_topology
      I_set top1_unit_interval_topology id"
    unfolding top1_continuous_map_on_def top1_unit_interval_topology_def
      subspace_topology_def by (by5000 auto)
  \<comment> \<open>f \<circ> \<psi> = sub0 * g (pointwise on I\_set).\<close>
  have hf_psi_eq: "\<forall>s\<in>I_set. (f \<circ> \<psi>) s = top1_path_product sub0 g s"
  proof (intro ballI)
    fix s :: real assume hs: "s \<in> I_set"
    show "(f \<circ> \<psi>) s = top1_path_product sub0 g s"
      unfolding \<psi>_def top1_path_product_def sub0_def g_def comp_def by (by100 simp)
  qed
  \<comment> \<open>Subspace topology X TX X = TX.\<close>
  have hX_sub: "is_topology_on X (subspace_topology X TX X)"
    using subspace_topology_is_topology_on[OF htop] by (by100 blast)
  \<comment> \<open>Apply reparam\_path\_homotopy.\<close>
  have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
  have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
  have hreparam: "top1_path_homotopic_on X (subspace_topology X TX X)
      (f 0) (f 1) (f \<circ> id) (f \<circ> \<psi>)"
    using reparam_path_homotopy[OF htop hf_cont hf_range _ hX_sub
        hid_cont h\<psi>_cont _ _ _ _ h0_I h1_I] h\<psi>0 h\<psi>1
    by (by100 simp)
  \<comment> \<open>f \<circ> id = f.\<close>
  have hf_id: "f \<circ> id = f" by (by100 simp)
  \<comment> \<open>Convert: path\_homotopic f (f \<circ> \<psi>) in subspace X.
     Since subspace X TX X = TX, this gives path\_homotopic in (X, TX).
     And f \<circ> \<psi> = sub0 * g pointwise, so path\_homotopic f (sub0 * g).\<close>
  have hpath_homot: "top1_path_homotopic_on X TX x0 x0 f (top1_path_product sub0 g)"
  proof -
    \<comment> \<open>From hreparam: path\_homotopic in subspace X TX X from f(0)=x0 to f(1)=x0
       between f \<circ> id = f and f \<circ> \<psi>.\<close>
    \<comment> \<open>f \<circ> \<psi> and sub0 * g agree on I\_set.\<close>
    have hf_psi_prod: "f \<circ> \<psi> = top1_path_product sub0 g"
    proof (rule ext)
      fix s :: real
      show "(f \<circ> \<psi>) s = top1_path_product sub0 g s"
        unfolding \<psi>_def top1_path_product_def sub0_def g_def comp_def by (by100 simp)
    qed
    \<comment> \<open>Rewrite hreparam using f \<circ> id = f and f \<circ> \<psi> = sub0 * g.\<close>
    have hreparam': "top1_path_homotopic_on X (subspace_topology X TX X) x0 x0
        f (top1_path_product sub0 g)"
      using hreparam hf0 hf1 hf_psi_prod by (by100 simp)
    \<comment> \<open>Convert from subspace topology to TX.
       Since the homotopy maps into X, continuity into (X, subspace X TX X)
       is equivalent to continuity into (X, TX).\<close>
    \<comment> \<open>Topology conversion: for functions into X, continuity into subspace X TX X
       \<longleftrightarrow> continuity into TX. So path\_homotopic in subspace = path\_homotopic in TX.\<close>
    show ?thesis
    proof -
      from hreparam' obtain F where
        hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X (subspace_topology X TX X) F"
        and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s"
        and hF1: "\<forall>s\<in>I_set. F (s, 1) = top1_path_product sub0 g s"
        and hF_x0: "\<forall>t\<in>I_set. F (0, t) = x0"
        and hF_x1: "\<forall>t\<in>I_set. F (1, t) = x0"
        unfolding top1_path_homotopic_on_def by (by100 blast)
      \<comment> \<open>Convert continuity from subspace to TX.\<close>
      have hF_cont_TX: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix p assume "p \<in> I_set \<times> I_set"
        thus "F p \<in> X" using hF_cont unfolding top1_continuous_map_on_def by (by100 blast)
      next
        fix U assume hU: "U \<in> TX"
        \<comment> \<open>X \<inter> U \<in> subspace\_topology X TX X.\<close>
        have "X \<inter> U \<in> subspace_topology X TX X"
          unfolding subspace_topology_def using hU by (by100 blast)
        hence "{p \<in> I_set \<times> I_set. F p \<in> X \<inter> U} \<in> II_topology"
          using hF_cont unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>F maps into X, so F\<inverse>(U) = F\<inverse>(X \<inter> U).\<close>
        moreover have "{p \<in> I_set \<times> I_set. F p \<in> U} = {p \<in> I_set \<times> I_set. F p \<in> X \<inter> U}"
        proof (rule set_eqI, rule iffI)
          fix p assume "p \<in> {p \<in> I_set \<times> I_set. F p \<in> U}"
          hence hp: "p \<in> I_set \<times> I_set" "F p \<in> U" by (by100 blast)+
          moreover have "F p \<in> X" using hF_cont hp(1) unfolding top1_continuous_map_on_def
            by (by100 blast)
          ultimately show "p \<in> {p \<in> I_set \<times> I_set. F p \<in> X \<inter> U}" by (by100 blast)
        next
          fix p assume "p \<in> {p \<in> I_set \<times> I_set. F p \<in> X \<inter> U}"
          thus "p \<in> {p \<in> I_set \<times> I_set. F p \<in> U}" by (by100 blast)
        qed
        ultimately show "{p \<in> I_set \<times> I_set. F p \<in> U} \<in> II_topology" by (by100 simp)
      qed
      have hf_path: "top1_is_path_on X TX x0 x0 f"
        using hloop unfolding top1_is_loop_on_def by (by100 blast)
      have hprod_path: "top1_is_path_on X TX x0 x0 (top1_path_product sub0 g)"
      proof -
        from hreparam' have hprod_sub: "top1_is_path_on X (subspace_topology X TX X) x0 x0
            (top1_path_product sub0 g)"
          unfolding top1_path_homotopic_on_def by (by100 blast)
        have hprod_cont: "top1_continuous_map_on I_set top1_unit_interval_topology X TX
            (top1_path_product sub0 g)"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s assume hs: "s \<in> I_set"
          show "top1_path_product sub0 g s \<in> X"
            using hprod_sub hs unfolding top1_is_path_on_def top1_continuous_map_on_def
            by (by100 blast)
        next
          fix U assume hU: "U \<in> TX"
          have "X \<inter> U \<in> subspace_topology X TX X"
            unfolding subspace_topology_def using hU by (by100 blast)
          hence "{s \<in> I_set. top1_path_product sub0 g s \<in> X \<inter> U} \<in> top1_unit_interval_topology"
            using hprod_sub unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          moreover have "{s \<in> I_set. top1_path_product sub0 g s \<in> U}
              = {s \<in> I_set. top1_path_product sub0 g s \<in> X \<inter> U}"
          proof (rule set_eqI, rule iffI)
            fix s assume "s \<in> {s \<in> I_set. top1_path_product sub0 g s \<in> U}"
            hence "s \<in> I_set" "top1_path_product sub0 g s \<in> U" by (by100 blast)+
            moreover have "top1_path_product sub0 g s \<in> X"
              using hprod_sub \<open>s \<in> I_set\<close> unfolding top1_is_path_on_def top1_continuous_map_on_def
              by (by100 blast)
            ultimately show "s \<in> {s \<in> I_set. top1_path_product sub0 g s \<in> X \<inter> U}" by (by100 blast)
          next
            fix s assume "s \<in> {s \<in> I_set. top1_path_product sub0 g s \<in> X \<inter> U}"
            thus "s \<in> {s \<in> I_set. top1_path_product sub0 g s \<in> U}" by (by100 blast)
          qed
          ultimately show "{s \<in> I_set. top1_path_product sub0 g s \<in> U} \<in> top1_unit_interval_topology"
            by (by100 simp)
        qed
        have "top1_path_product sub0 g 0 = x0"
          using hprod_sub unfolding top1_is_path_on_def by (by100 blast)
        moreover have "top1_path_product sub0 g 1 = x0"
          using hprod_sub unfolding top1_is_path_on_def by (by100 blast)
        ultimately show ?thesis unfolding top1_is_path_on_def
          using hprod_cont by (by5000 blast)
      qed
      show ?thesis unfolding top1_path_homotopic_on_def
        using hf_path hprod_path hF_cont_TX hF0 hF1 hF_x0 hF_x1 by (by100 blast)
    qed
  qed
  \<comment> \<open>Convert path\_homotopic to loop\_equiv.\<close>
  have hsub0_g_loop: "top1_is_loop_on X TX x0 (top1_path_product sub0 g)"
  proof -
    have hsub0_loop: "top1_is_loop_on X TX x0 sub0"
    proof -
      have hs0: "sub0 0 = x0" unfolding sub0_def using hf0 by (by100 simp)
      have hs1: "sub0 1 = x0" unfolding sub0_def
      proof -
        have "f (1 / real n) = x0" using hvertex .
        thus "f (1 / real n) = x0" .
      qed
      have hs_cont: "top1_continuous_map_on I_set top1_unit_interval_topology X TX sub0"
      proof -
        define r where "r s = s / real n" for s :: real
        have "continuous_on UNIV r" unfolding r_def using hn_pos
          by (intro continuous_intros) (by100 simp)+
        have hr_range: "\<And>s. s \<in> I_set \<Longrightarrow> r s \<in> I_set"
          unfolding r_def top1_unit_interval_def using hn by (by100 auto)
        have hr_top1: "top1_continuous_map_on I_set top1_unit_interval_topology
            I_set top1_unit_interval_topology r"
          unfolding top1_unit_interval_def
          using top1_continuous_map_on_real_subspace_open_sets[of "{0..1}" r "{0..1}"]
            hr_range \<open>continuous_on UNIV r\<close>
          unfolding top1_unit_interval_def
          using top1_unit_interval_def top1_unit_interval_topology_def by (by5000 simp)
        have "top1_continuous_map_on I_set top1_unit_interval_topology X TX (f \<circ> r)"
          using top1_continuous_map_on_comp[OF hr_top1 hf_cont] .
        moreover have "sub0 = f \<circ> r" unfolding sub0_def r_def comp_def by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
        using hs0 hs1 hs_cont by (by5000 blast)
    qed
    have hg_loop: "top1_is_loop_on X TX x0 g"
    proof -
      have hg0: "g 0 = x0" unfolding g_def using hvertex by (by100 simp)
      have hg1: "g 1 = x0"
      proof -
        have "g 1 = f (1 / real n + 1 * (real n - 1) / real n)" unfolding g_def by (by100 simp)
        moreover have "(1::real) / real n + 1 * (real n - 1) / real n = real n / real n"
          by (simp add: field_simps)
        moreover have "f (real n / real n) = x0" using hf1 hn_pos by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      have hg_cont: "top1_continuous_map_on I_set top1_unit_interval_topology X TX g"
      proof -
        define r where "r s = 1 / real n + s * (real n - 1) / real n" for s :: real
        have "continuous_on UNIV r" unfolding r_def using hn_pos
          by (intro continuous_intros) (by100 simp)+
        have hr_range: "\<And>s. s \<in> I_set \<Longrightarrow> r s \<in> I_set"
        proof -
          fix s :: real assume "s \<in> I_set"
          hence hs01: "0 \<le> s" "s \<le> 1" unfolding top1_unit_interval_def by (by100 auto)+
          have "0 \<le> r s" unfolding r_def using hs01 hn_pos by (by100 simp)
          moreover have "r s \<le> 1"
          proof -
            have "s * (real n - 1) / real n \<le> 1 * (real n - 1) / real n"
              using hs01 hn by (intro divide_right_mono mult_right_mono) (by100 simp)+
            also have "1 * (real n - 1) / real n = (real n - 1) / real n" by (by100 simp)
            finally have "r s \<le> 1/real n + (real n-1)/real n" unfolding r_def by (by100 linarith)
            also have "1/real n + (real n-1)/real n = real n / real n" by (simp add: field_simps)
            also have "\<dots> = 1" using hn_pos by (by100 simp)
            finally show ?thesis .
          qed
          ultimately show "r s \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
        qed
        have hr_top1: "top1_continuous_map_on I_set top1_unit_interval_topology
            I_set top1_unit_interval_topology r"
          unfolding top1_unit_interval_def
          using top1_continuous_map_on_real_subspace_open_sets[of "{0..1}" r "{0..1}"]
            hr_range \<open>continuous_on UNIV r\<close>
          unfolding top1_unit_interval_def
          using top1_unit_interval_def top1_unit_interval_topology_def by (by5000 simp)
        have "top1_continuous_map_on I_set top1_unit_interval_topology X TX (f \<circ> r)"
          using top1_continuous_map_on_comp[OF hr_top1 hf_cont] .
        moreover have "g = f \<circ> r" unfolding g_def r_def comp_def by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
        using hg0 hg1 hg_cont by (by5000 blast)
    qed
    show ?thesis unfolding top1_is_loop_on_def
      using top1_path_product_is_path[OF htop
        hsub0_loop[unfolded top1_is_loop_on_def]
        hg_loop[unfolded top1_is_loop_on_def]] by (by100 simp)
  qed
  show ?thesis unfolding top1_loop_equiv_on_def
    using hloop hsub0_g_loop hpath_homot by (by100 blast)
qed

text \<open>Inductive helper: loop split at multiple vertices by induction on n.
  Proves: f \<simeq> foldr [sub\_0,...,sub\_{n-1}] const, where sub\_k(s) = f((k+s)/n).\<close>
lemma loop_split_inductive:
  assumes htop: "is_topology_on X TX"
      and hloop: "top1_is_loop_on X TX x0 f"
      and hn: "n \<ge> 1"
      and hvertex: "\<forall>k\<le>n. f (real k / real n) = x0"
  shows "top1_loop_equiv_on X TX x0 f
      (foldr top1_path_product
        (map (\<lambda>k. \<lambda>s. f ((real k + s) / real n)) [0..<n])
        (top1_constant_path x0))"
  using assms
proof (induction n arbitrary: f rule: nat_less_induct)
  case (1 n)
  hence htop: "is_topology_on X TX" and hloop: "top1_is_loop_on X TX x0 f"
    and hn: "n \<ge> 1" and hvertex: "\<forall>k\<le>n. f (real k / real n) = x0"
    by (by100 blast)+
  note hIH = 1(1)
  define sub where "sub k s = f ((real k + s) / real n)" for k :: nat and s :: real
  show ?case
  proof (cases "n = 1")
    case True
    \<comment> \<open>Base: sub 0 = f, foldr [sub 0] const = f * const \<simeq> f.\<close>
    have "sub 0 = f" unfolding sub_def using True by (by100 simp)
    hence hfoldr_1: "foldr top1_path_product
        (map (\<lambda>k. \<lambda>s. f ((real k + s) / real n)) [0..<n]) (top1_constant_path x0)
      = top1_path_product f (top1_constant_path x0)"
      using True unfolding sub_def by (by100 simp)
    have hf_path: "top1_is_path_on X TX x0 x0 f"
      using hloop unfolding top1_is_loop_on_def by (by100 blast)
    have hident: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product f (top1_constant_path x0)) f"
      using Theorem_51_2_right_identity[OF htop hf_path] .
    have hident_sym: "top1_path_homotopic_on X TX x0 x0
        f (top1_path_product f (top1_constant_path x0))"
      using Lemma_51_1_path_homotopic_sym[OF hident] .
    have hprod_loop_1: "top1_is_loop_on X TX x0
        (top1_path_product f (top1_constant_path x0))"
    proof -
      have hx0_X: "x0 \<in> X"
      proof -
        have "0 \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
        hence "f 0 \<in> X"
          using hloop unfolding top1_is_loop_on_def top1_is_path_on_def
            top1_continuous_map_on_def by (by100 blast)
        moreover have "f 0 = x0"
          using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      have hconst: "top1_is_loop_on X TX x0 (top1_constant_path x0)"
        using top1_constant_path_is_loop[OF htop hx0_X] .
      show ?thesis unfolding top1_is_loop_on_def
        using top1_path_product_is_path[OF htop
            hloop[unfolded top1_is_loop_on_def]
            hconst[unfolded top1_is_loop_on_def]] by (by100 simp)
    qed
    show ?thesis unfolding top1_loop_equiv_on_def
      using hloop hprod_loop_1 hident_sym hfoldr_1 by (by5000 simp)
  next
    case False
    hence hn2: "n \<ge> 2" using hn by (by100 linarith)
    \<comment> \<open>Step: split f at 1/n, apply IH to g with n-1.\<close>
    define g where "g s = f (1 / real n + s * (real n - 1) / real n)" for s
    \<comment> \<open>f \<simeq> sub 0 * g (from loop\_split\_first).\<close>
    have hvertex_1n: "f (1 / real n) = x0" using hvertex[rule_format, of 1] hn by (by100 simp)
    have hf_split: "top1_loop_equiv_on X TX x0 f (top1_path_product (sub 0) g)"
      using loop_split_first[OF htop hloop hn2 hvertex_1n] unfolding sub_def g_def
      by (by100 simp)
    \<comment> \<open>g is a loop satisfying IH hypotheses with n-1.\<close>
    have hn_pos: "real n > 0" using hn by (by100 simp)
    have hg_loop: "top1_is_loop_on X TX x0 g"
    proof -
      \<comment> \<open>g(0) = f(1/n) = x0, g(1) = f(1/n + (n-1)/n) = f(1) = x0.\<close>
      have hg0: "g 0 = x0" unfolding g_def using hvertex[rule_format, of 1] hn by (by100 simp)
      have hg1: "g 1 = x0"
      proof -
        have "g 1 = f (1 / real n + 1 * (real n - 1) / real n)" unfolding g_def by (by100 simp)
        moreover have "(1::real) / real n + 1 * (real n - 1) / real n = real n / real n"
          by (simp add: field_simps)
        moreover have "f (real n / real n) = x0"
          using hvertex[rule_format, of n] hn by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>g is continuous (composition of f with affine rescaling).\<close>
      have hg_cont: "top1_continuous_map_on I_set top1_unit_interval_topology X TX g"
      proof -
        \<comment> \<open>g = f \<circ> (affine rescaling). Rescaling maps [0,1] \<rightarrow> [0,1] continuously.\<close>
        have hf_cont: "top1_continuous_map_on I_set top1_unit_interval_topology X TX f"
          using hloop unfolding top1_is_loop_on_def top1_is_path_on_def top1_unit_interval_def
          by (by100 blast)
        define r where "r s = 1 / real n + s * (real n - 1) / real n" for s :: real
        have hr_range: "\<And>s. s \<in> I_set \<Longrightarrow> r s \<in> I_set"
        proof -
          fix s :: real assume hs: "s \<in> I_set"
          hence hs01: "0 \<le> s \<and> s \<le> 1" unfolding top1_unit_interval_def by (by100 auto)
          have "0 \<le> r s" unfolding r_def using hs01 hn_pos by (by100 simp)
          moreover have "r s \<le> 1"
          proof -
            have "r s = 1 / real n + s * (real n - 1) / real n" unfolding r_def by (by100 simp)
            also have "\<dots> \<le> 1 / real n + 1 * (real n - 1) / real n"
            proof -
              have "s * (real n - 1) / real n \<le> 1 * (real n - 1) / real n"
                using hs01 hn2 by (intro divide_right_mono mult_right_mono) (by100 simp)+
              thus ?thesis by (by100 simp)
            qed
            also have "\<dots> = real n / real n" by (simp add: field_simps)
            also have "\<dots> = 1" using hn_pos by (by100 simp)
            finally show ?thesis .
          qed
          ultimately show "r s \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
        qed
        have hr_cont_univ: "continuous_on (UNIV::real set) r"
          unfolding r_def using hn_pos by (intro continuous_intros) (by100 simp)+
        have hr_top1: "top1_continuous_map_on I_set top1_unit_interval_topology
            I_set top1_unit_interval_topology r"
          unfolding top1_unit_interval_def
          using top1_continuous_map_on_real_subspace_open_sets[of "{0..1}" r "{0..1}"]
            hr_range hr_cont_univ
          unfolding top1_unit_interval_def
          using top1_unit_interval_def top1_unit_interval_topology_def by (by5000 simp)
        have "top1_continuous_map_on I_set top1_unit_interval_topology X TX (f \<circ> r)"
          using top1_continuous_map_on_comp[OF hr_top1 hf_cont] .
        moreover have "g = f \<circ> r" unfolding g_def r_def comp_def by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
        using hg0 hg1 hg_cont by (by5000 blast)
    qed
    have hg_vertex: "\<forall>k\<le>n-1. g (real k / real (n-1)) = x0"
    proof (intro allI impI)
      fix k assume hk: "k \<le> n - 1"
      show "g (real k / real (n-1)) = x0"
      proof (cases "n = 2")
        case True
        hence "n - 1 = 1" by (by100 simp)
        hence "k = 0 \<or> k = 1" using hk True by (by100 auto)
        thus ?thesis
        proof
          assume "k = 0" thus ?thesis unfolding g_def
            using hvertex[rule_format, of 1] hn by (by100 simp)
        next
          assume "k = 1"
          have "g 1 = x0"
          proof -
            have "g 1 = f (1 / real n + 1 * (real n - 1) / real n)" unfolding g_def by (by100 simp)
            moreover have "(1::real) / real n + 1 * (real n - 1) / real n = real n / real n"
              by (simp add: field_simps)
            moreover have "f (real n / real n) = x0"
              using hvertex[rule_format, of n] hn by (by100 simp)
            ultimately show ?thesis by (by100 simp)
          qed
          thus ?thesis using \<open>k = 1\<close> True by (by100 simp)
        qed
      next
        case False
        hence hn3: "n \<ge> 3" using hn2 by (by100 linarith)
        have hnm1_pos: "real (n-1) > 0" using hn2 by (by100 simp)
        \<comment> \<open>g(k/(n-1)) = f(1/n + k/(n-1) * (n-1)/n) = f((k+1)/n).\<close>
        have "g (real k / real (n-1)) = f (1/real n + (real k / real (n-1)) * (real n - 1) / real n)"
          unfolding g_def by (by100 simp)
        also have "1/real n + (real k / real (n-1)) * (real n - 1) / real n
            = real (k+1) / real n"
          using hnm1_pos hn_pos by (simp add: field_simps)
        also have "f (real (k+1) / real n) = x0"
          using hvertex[rule_format, of "k+1"] hk hn2 by (by100 force)
        finally show ?thesis .
      qed
    qed
    \<comment> \<open>Apply IH: g \<simeq> foldr [g\_sub 0,...,g\_sub (n-2)] const.\<close>
    have hn1_ge1: "n - 1 \<ge> 1" using hn2 by (by100 linarith)
    have hn1_lt_n: "n - 1 < n" using hn2 by (by100 linarith)
    have hIH_g: "top1_loop_equiv_on X TX x0 g
        (foldr top1_path_product
          (map (\<lambda>k. \<lambda>s. g ((real k + s) / real (n-1))) [0..<n-1])
          (top1_constant_path x0))"
      using hIH[rule_format, of "n-1" g] hn1_lt_n htop hg_loop hn1_ge1 hg_vertex
      by (by100 blast)
    \<comment> \<open>Key: g\_sub k = sub (k+1).\<close>
    have hg_sub_eq: "map (\<lambda>k. \<lambda>s. g ((real k + s) / real (n-1))) [0..<n-1]
        = map (\<lambda>k. \<lambda>s. f ((real k + s) / real n)) [Suc 0..<n]"
    proof -
      have hnm1_pos: "real (n-1) > 0" using hn2 by (by100 simp)
      \<comment> \<open>Pointwise: g((k+s)/(n-1)) = f(((Suc k)+s)/n).\<close>
      have hpw: "\<And>k s. g ((real k + s) / real (n-1)) = f ((real (Suc k) + s) / real n)"
      proof -
        fix k :: nat and s :: real
        have "g ((real k + s) / real (n-1)) =
            f (1/real n + ((real k + s) / real (n-1)) * (real n - 1) / real n)"
          unfolding g_def by (by100 simp)
        moreover have "1/real n + ((real k + s) / real (n-1)) * (real n - 1) / real n
            = (real (Suc k) + s) / real n"
          using hn_pos hnm1_pos by (simp add: field_simps)
        ultimately show "g ((real k + s) / real (n-1)) = f ((real (Suc k) + s) / real n)"
          by (by100 simp)
      qed
      \<comment> \<open>[Suc 0..<n] = map Suc [0..<n-1].\<close>
      have hmap_suc: "[Suc 0..<n] = map Suc [0..<n-1]"
        using map_Suc_upt[of 0 "n-1", symmetric] hn2 by (by100 simp)
      show ?thesis unfolding hmap_suc
        using hpw by (by100 auto)
    qed
    \<comment> \<open>Combine: f \<simeq> sub\_0 * g \<simeq> sub\_0 * foldr [sub\_1,...] const = foldr [sub\_0,...] const.\<close>
    \<comment> \<open>Step 1: g \<simeq> foldr [sub Suc 0,...,sub (n-1)] const (from hIH\_g + hg\_sub\_eq).\<close>
    have hg_foldr: "top1_loop_equiv_on X TX x0 g
        (foldr top1_path_product (map (\<lambda>k. \<lambda>s. f ((real k + s) / real n)) [Suc 0..<n])
          (top1_constant_path x0))"
      using hIH_g hg_sub_eq by (by100 simp)
    \<comment> \<open>Step 2: f \<simeq> sub 0 * g (from hf\_split).\<close>
    \<comment> \<open>Step 3: sub 0 * g \<simeq> sub 0 * foldr [...] const (product congruence on right).\<close>
    \<comment> \<open>Step 4: = foldr [sub 0,...,sub (n-1)] const (from hfoldr\_cons).\<close>
    \<comment> \<open>Step 5: Transitivity.\<close>
    \<comment> \<open>Step 3: Product congruence: sub\_0 * g \<simeq> sub\_0 * foldr [sub\_1,...] const.\<close>
    define rest where "rest = foldr top1_path_product
        (map (\<lambda>k. \<lambda>s. f ((real k + s) / real n)) [Suc 0..<n]) (top1_constant_path x0)"
    have hg_ph_rest: "top1_path_homotopic_on X TX x0 x0 g rest"
      using hg_foldr unfolding top1_loop_equiv_on_def rest_def by (by100 blast)
    have hsub0_loop: "top1_is_loop_on X TX x0 (sub 0)"
    proof -
      have "sub 0 0 = x0" unfolding sub_def
        using hvertex[rule_format, of 0] hn by (by100 simp)
      moreover have "sub 0 1 = x0" unfolding sub_def
        using hvertex[rule_format, of 1] hn by (by100 simp)
      moreover have "top1_continuous_map_on I_set top1_unit_interval_topology X TX (sub 0)"
      proof -
        have hf_cont: "top1_continuous_map_on I_set top1_unit_interval_topology X TX f"
          using hloop unfolding top1_is_loop_on_def top1_is_path_on_def top1_unit_interval_def
          by (by100 blast)
        define r where "r s = s / real n" for s :: real
        have "continuous_on UNIV r" unfolding r_def
          using hn_pos by (intro continuous_intros) (by100 simp)+
        have hr_range: "\<And>s. s \<in> I_set \<Longrightarrow> r s \<in> I_set"
          unfolding r_def top1_unit_interval_def using hn by (by100 auto)
        have hr_top1: "top1_continuous_map_on I_set top1_unit_interval_topology
            I_set top1_unit_interval_topology r"
          unfolding top1_unit_interval_def
          using top1_continuous_map_on_real_subspace_open_sets[of "{0..1}" r "{0..1}"]
            hr_range \<open>continuous_on UNIV r\<close>
          unfolding top1_unit_interval_def
          using top1_unit_interval_def top1_unit_interval_topology_def by (by5000 simp)
        have "top1_continuous_map_on I_set top1_unit_interval_topology X TX (f \<circ> r)"
          using top1_continuous_map_on_comp[OF hr_top1 hf_cont] .
        moreover have "sub 0 = f \<circ> r" unfolding sub_def r_def comp_def by (by100 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      ultimately show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by5000 blast)
    qed
    have hsub0_path: "top1_is_path_on X TX x0 x0 (sub 0)"
      using hsub0_loop unfolding top1_is_loop_on_def by (by100 blast)
    have hprod_cong: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product (sub 0) g) (top1_path_product (sub 0) rest)"
    proof -
      from path_homotopic_product_right[OF htop hg_ph_rest hsub0_path]
      show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Step 4: foldr cons = sub\_0 * rest.\<close>
    have hcons: "foldr top1_path_product
        (map (\<lambda>k. \<lambda>s. f ((real k + s) / real n)) [0..<n]) (top1_constant_path x0)
      = top1_path_product (sub 0) rest"
    proof -
      have "n > 0" using hn by (by100 linarith)
      hence "[0..<n] = 0 # [Suc 0..<n]" using upt_rec[of 0 n] by (by100 simp)
      thus ?thesis unfolding rest_def sub_def by (by100 simp)
    qed
    \<comment> \<open>Step 5: f \<simeq> sub\_0 * g (hf\_split), sub\_0 * g \<simeq> sub\_0 * rest (hprod\_cong),
       sub\_0 * rest = foldr [sub\_0,...] (hcons). Transitivity.\<close>
    have hf_ph_prod: "top1_path_homotopic_on X TX x0 x0 f (top1_path_product (sub 0) g)"
      using hf_split unfolding top1_loop_equiv_on_def by (by100 blast)
    have hf_ph_rest: "top1_path_homotopic_on X TX x0 x0
        f (top1_path_product (sub 0) rest)"
      using Lemma_51_1_path_homotopic_trans[OF htop hf_ph_prod hprod_cong] .
    have hrest_loop: "top1_is_loop_on X TX x0 rest"
      using hg_foldr unfolding top1_loop_equiv_on_def rest_def by (by100 blast)
    have hprod_rest_loop: "top1_is_loop_on X TX x0 (top1_path_product (sub 0) rest)"
    proof -
      have "top1_is_loop_on X TX x0 (sub 0)"
        using hsub0_loop .
      thus ?thesis unfolding top1_is_loop_on_def
        using top1_path_product_is_path[OF htop
            \<open>top1_is_loop_on X TX x0 (sub 0)\<close>[unfolded top1_is_loop_on_def]
            hrest_loop[unfolded top1_is_loop_on_def]] by (by100 simp)
    qed
    show ?thesis unfolding top1_loop_equiv_on_def hcons
      using hloop hprod_rest_loop hf_ph_rest by (by100 blast)
  qed
qed

lemma loop_split_at_vertices:
  assumes htop: "is_topology_on X TX"
      and hloop: "top1_is_loop_on X TX x0 f"
      and hn: "n \<ge> 1"
      and hvertex: "\<forall>k\<le>n. f (real k / real n) = x0"
  defines "sub k \<equiv> (\<lambda>s. f ((real k + s) / real n))"
  shows "top1_loop_equiv_on X TX x0 f
      (foldr top1_path_product (map sub [0..<n]) (top1_constant_path x0))"
proof -
  \<comment> \<open>The loop f passes through x0 at s=0, s=1/n, ..., s=1.
     Split f into n sub-paths, each reparametrized to [0,1].
     The path product of these sub-paths is homotopic to f by reparametrization.\<close>
  \<comment> \<open>Each sub path is a path from x0 to x0.\<close>
  have hsub_loop: "\<And>k. k < n \<Longrightarrow> top1_is_loop_on X TX x0 (sub k)"
  proof -
    fix k assume hk: "k < n"
    \<comment> \<open>sub k 0 = f(k/n) = x0, sub k 1 = f((k+1)/n) = x0.\<close>
    have hsub0: "sub k 0 = x0"
      unfolding sub_def using hvertex[rule_format, of k] hk hn by (by100 simp)
    have hsub1: "sub k 1 = x0"
    proof -
      have "sub k 1 = f ((real k + 1) / real n)" unfolding sub_def by (by100 simp)
      also have "(real k + 1) / real n = real (Suc k) / real n" by (by100 simp)
      also have "f (real (Suc k) / real n) = x0"
      proof -
        have "Suc k \<le> n" using hk by (by100 linarith)
        thus ?thesis using hvertex by (by100 blast)
      qed
      finally show ?thesis .
    qed
    \<comment> \<open>sub k is continuous (f continuous, linear rescaling continuous).\<close>
    have hsub_cont: "top1_continuous_map_on I_set top1_unit_interval_topology X TX (sub k)"
    proof -
      \<comment> \<open>f is continuous from hloop.\<close>
      have hf_cont: "top1_continuous_map_on I_set top1_unit_interval_topology X TX f"
        using hloop unfolding top1_is_loop_on_def top1_is_path_on_def top1_unit_interval_def
        by (by100 blast)
      \<comment> \<open>The linear rescaling s \<mapsto> (k+s)/n maps I\_set to I\_set.\<close>
      have hrescale_range: "\<And>s. s \<in> I_set \<Longrightarrow> (real k + s) / real n \<in> I_set"
      proof -
        fix s :: real assume hs: "s \<in> I_set"
        hence hs01: "0 \<le> s \<and> s \<le> 1" unfolding top1_unit_interval_def by (by100 auto)
        have "0 \<le> (real k + s) / real n" using hs01 hn by (by100 simp)
        moreover have "(real k + s) / real n \<le> 1"
        proof -
          have "real k + s \<le> real k + 1" using hs01 by (by100 linarith)
          also have "\<dots> \<le> real n" using hk by (by100 simp)
          finally show ?thesis using hn by (by100 simp)
        qed
        ultimately show "(real k + s) / real n \<in> I_set"
          unfolding top1_unit_interval_def by (by100 auto)
      qed
      \<comment> \<open>Rescaling is continuous.\<close>
      have hrescale_cont: "continuous_on I_set (\<lambda>s. (real k + s) / real n)"
        using hn by (intro continuous_intros) (by100 simp)+
      \<comment> \<open>Composition f \<circ> rescale is continuous.\<close>
      \<comment> \<open>Bridge: rescaling as top1\_continuous\_map\_on.\<close>
      have hrescale_univ: "continuous_on (UNIV::real set) (\<lambda>s. (real k + s) / real n)"
        using hn by (intro continuous_intros) (by100 simp)+
      have hrescale_top1: "top1_continuous_map_on I_set top1_unit_interval_topology
          I_set top1_unit_interval_topology (\<lambda>s. (real k + s) / real n)"
        unfolding top1_unit_interval_def
        using top1_continuous_map_on_real_subspace_open_sets[of "{0..1}"
          "\<lambda>s. (real k + s) / real n" "{0..1}"]
          hrescale_range hrescale_univ
        unfolding top1_unit_interval_def
        using top1_unit_interval_def top1_unit_interval_topology_def by (by5000 simp)
      have "top1_continuous_map_on I_set top1_unit_interval_topology X TX
          (f \<circ> (\<lambda>s. (real k + s) / real n))"
        using top1_continuous_map_on_comp[OF hrescale_top1 hf_cont] .
      moreover have "(\<lambda>s. f ((real k + s) / real n)) = f \<circ> (\<lambda>s. (real k + s) / real n)"
        unfolding comp_def by (by100 simp)
      ultimately show ?thesis unfolding sub_def by (by100 simp)
    qed
    \<comment> \<open>sub k is a path from x0 to x0 = loop.\<close>
    show "top1_is_loop_on X TX x0 (sub k)"
      unfolding top1_is_loop_on_def top1_is_path_on_def
      using hsub0 hsub1 hsub_cont by (by5000 blast)
  qed
  \<comment> \<open>The foldr product is a loop from x0 to x0.\<close>
  have hprod_loop: "top1_is_loop_on X TX x0
      (foldr top1_path_product (map sub [0..<n]) (top1_constant_path x0))"
  proof -
    have hx0_X: "x0 \<in> X"
    proof -
      have "f 0 = x0" using top1_is_loop_on_start[OF hloop] .
      moreover have "f 0 \<in> X"
      proof -
        have "0 \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
        thus ?thesis using hloop[unfolded top1_is_loop_on_def top1_is_path_on_def
            top1_continuous_map_on_def] by (by100 blast)
      qed
      ultimately show ?thesis by (by100 simp)
    qed
    have hconst: "top1_is_loop_on X TX x0 (top1_constant_path x0)"
      using top1_constant_path_is_loop[OF htop hx0_X] .
    have hloops_set: "\<forall>g \<in> set (map sub [0..<n]). top1_is_loop_on X TX x0 g"
      using hsub_loop by (by100 force)
    show ?thesis using foldr_path_product_loops_is_loop[OF htop hconst hloops_set] .
  qed
  \<comment> \<open>f is homotopic to the product (by reparametrization).\<close>
  \<comment> \<open>Use reparam\_path\_homotopy: the reparametrization that maps
     the binary product timing to the linear timing gives homotopy.\<close>
  \<comment> \<open>Proof by induction on n.
     For n=1: sub 0 = f, so foldr [f] const = f * const \<simeq> f (right identity).
     For n>1: split f at 1/n, then f \<simeq> sub\_0 * g (reparametrization).
     g has n-1 sub-loops equal to sub\_1,...,sub\_{n-1}.
     By IH, g \<simeq> foldr [sub\_1,...,sub\_{n-1}] const.
     Product congruence: sub\_0 * g \<simeq> sub\_0 * foldr [...] const = foldr [sub\_0,...] const.\<close>
  \<comment> \<open>Define the reparametrization for the splitting step.\<close>
  define \<psi> where "\<psi> s \<equiv> (if s \<le> 1/2 then 2*s / real n else 1 / real n + (2*s - 1) * (real n - 1) / real n)"
  \<comment> \<open>Key: sub 0 * g = f \<circ> \<psi> where g(s) = f(1/n + s*(n-1)/n).\<close>
  define g where "g s \<equiv> f (1 / real n + s * (real n - 1) / real n)"
  \<comment> \<open>The foldr product decomposes as sub\_0 * foldr [sub\_1,...,sub\_{n-1}] const.\<close>
  have hfoldr_cons: "foldr top1_path_product (map sub [0..<n]) (top1_constant_path x0)
      = top1_path_product (sub 0) (foldr top1_path_product (map sub [Suc 0..<n]) (top1_constant_path x0))"
  proof -
    have "n > 0" using hn by (by100 linarith)
    hence "[0..<n] = 0 # [Suc 0..<n]" using upt_rec[of 0 n] by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  \<comment> \<open>Proof by strong induction on n (following Munkres: concatenation of edge traversals).
     Base n=1: sub 0 = f, foldr = f * const, right identity gives f \<simeq> f * const.
     Step n\<ge>2: Split f at 1/n using reparam\_path\_homotopy.
       f \<simeq> sub\_0 * g where g(s) = f(1/n + s*(n-1)/n).
       g has n-1 sub-loops equal to sub\_1,...,sub\_{n-1}.
       By IH, g \<simeq> foldr [sub\_1,...,sub\_{n-1}] const.
       Product congruence: sub\_0 * g \<simeq> sub\_0 * foldr [...].
       = foldr [sub\_0,...,sub\_{n-1}] const.\<close>
  \<comment> \<open>Use the inductive helper: sub k = (\<lambda>s. f((k+s)/n)), so the map is correct.\<close>
  have hsub_eq: "map sub [0..<n] = map (\<lambda>k. \<lambda>s. f ((real k + s) / real n)) [0..<n]"
    unfolding sub_def by (by100 simp)
  have hresult: "top1_loop_equiv_on X TX x0 f
      (foldr top1_path_product
        (map (\<lambda>k. \<lambda>s. f ((real k + s) / real n)) [0..<n])
        (top1_constant_path x0))"
    using loop_split_inductive[OF htop hloop hn hvertex] .
  show ?thesis using hresult unfolding hsub_eq .
qed

end
