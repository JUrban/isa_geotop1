theory AlgTop_JCT_Base0
  imports "Top0.Top1_Ch9_13" "AlgTopH.AlgTopHelpers"
begin


text \<open>The squaring map q(z) = z^2 on S^1 is a covering map (Munkres §53 exercise, used in §57).
  In real coordinates: q(x,y) = (x^2-y^2, 2xy).
  Cover S^1 by 4 open semicircles (upper/lower/left/right half-planes).
  For each, the preimage under q consists of 2 disjoint arcs, and q maps each
  homeomorphically onto the semicircle.\<close>

lemma squaring_map_covering:
  "top1_covering_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology
    (\<lambda>(x, y). (x\<^sup>2 - y\<^sup>2, 2*x*y))"
proof -
  define q :: "real \<times> real \<Rightarrow> real \<times> real" where "q p = (fst p ^ 2 - snd p ^ 2, 2 * fst p * snd p)" for p
  have hq_alt: "q = (\<lambda>(x, y). (x\<^sup>2 - y\<^sup>2, 2*x*y))" unfolding q_def by (intro ext) auto
  \<comment> \<open>q maps S^1 to S^1: if x^2+y^2=1 then (x^2-y^2)^2+(2xy)^2 = (x^2+y^2)^2 = 1.\<close>
  have hq_S1: "\<And>p. p \<in> top1_S1 \<Longrightarrow> q p \<in> top1_S1"
  proof -
    fix p assume hp: "p \<in> top1_S1"
    obtain x y where hxy: "p = (x, y)" by (cases p) auto
    have hS1: "x\<^sup>2 + y\<^sup>2 = 1" using hp unfolding top1_S1_def hxy by simp
    have "(x\<^sup>2 - y\<^sup>2)\<^sup>2 + (2*x*y)\<^sup>2 = x^4 - 2*x\<^sup>2*y\<^sup>2 + y^4 + 4*x\<^sup>2*y\<^sup>2"
      by (simp add: power2_eq_square power4_eq_xxxx algebra_simps)
    also have "\<dots> = x^4 + 2*x\<^sup>2*y\<^sup>2 + y^4" by simp
    also have "\<dots> = (x\<^sup>2 + y\<^sup>2)\<^sup>2"
      by (simp add: power2_eq_square power4_eq_xxxx algebra_simps)
    also have "\<dots> = 1" using hS1 by simp
    finally show "q p \<in> top1_S1" unfolding top1_S1_def q_def hxy by simp
  qed
  \<comment> \<open>q is surjective on S^1: for any (a,b) \<in> S^1, find (x,y) with q(x,y) = (a,b).\<close>
  have hq_surj: "q ` top1_S1 = top1_S1"
  proof (intro set_eqI iffI)
    fix w assume "w \<in> q ` top1_S1"
    then obtain p where hp: "p \<in> top1_S1" and hw: "w = q p" by (by100 blast)
    show "w \<in> top1_S1" using hq_S1[OF hp] hw by simp
  next
    fix w assume hw: "w \<in> top1_S1"
    obtain a b where hab: "w = (a, b)" by (cases w) auto
    have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" using hw unfolding top1_S1_def hab by simp
    \<comment> \<open>Use complex square root: z = Complex a b has |z|=1, so csqrt z has |csqrt z|=1.\<close>
    define z where "z = Complex a b"
    have hznorm: "cmod z = 1" unfolding z_def cmod_def using hS1w by simp
    define w' where "w' = csqrt z"
    have hw'norm: "cmod w' = 1" unfolding w'_def using hznorm by (simp add: norm_csqrt)
    have hw'sq: "w' * w' = z"
      using power2_csqrt[of z] unfolding w'_def power2_eq_square by simp
    define x where "x = Re w'"
    define y where "y = Im w'"
    have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1"
      using hw'norm unfolding x_def y_def cmod_def
      by (simp add: power2_eq_square real_sqrt_eq_1_iff)
    have "w' * w' = Complex (x\<^sup>2 - y\<^sup>2) (2*x*y)"
      unfolding x_def y_def
      by (intro complex_eqI) (simp_all add: power2_eq_square algebra_simps)
    hence "Complex (x\<^sup>2 - y\<^sup>2) (2*x*y) = z" using hw'sq by simp
    hence hqa: "x\<^sup>2 - y\<^sup>2 = a" and hqb: "2*x*y = b"
      unfolding z_def by (simp_all add: complex_eq_iff)
    have "(x, y) \<in> top1_S1" unfolding top1_S1_def using hxy_S1 by simp
    moreover have "q (x, y) = w" unfolding q_def hab using hqa hqb by simp
    ultimately show "w \<in> q ` top1_S1" by (by100 blast)
  qed
  \<comment> \<open>q is continuous (polynomial).\<close>
  have hq_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q"
  proof -
    \<comment> \<open>q is continuous as a map R^2 \<rightarrow> R^2 (polynomial), then restrict to S^1.\<close>
    have hcont_univ: "continuous_on UNIV (\<lambda>p::real\<times>real. (fst p ^ 2 - snd p ^ 2, 2 * fst p * snd p))"
      by (intro continuous_intros)
    have hcont_S1: "continuous_on top1_S1 (\<lambda>p. (fst p ^ 2 - snd p ^ 2, 2 * fst p * snd p))"
      using continuous_on_subset[OF hcont_univ] by (by100 blast)
    have hq_eq: "\<And>p. p \<in> top1_S1 \<Longrightarrow> q p = (fst p ^ 2 - snd p ^ 2, 2 * fst p * snd p)"
      unfolding q_def by simp
    \<comment> \<open>Bridge from continuous_on to top1_continuous_map_on via subspace topology.\<close>
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix p assume "p \<in> top1_S1" thus "q p \<in> top1_S1" by (rule hq_S1)
    next
      fix V assume hV: "V \<in> top1_S1_topology"
      obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
          and hVeq': "V = top1_S1 \<inter> W'"
        using hV unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      have hW'_open: "open W'" using hW'
        by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
      define W where "W = W'"
      have hW: "open W" and hVeq: "V = top1_S1 \<inter> W"
        using hW'_open hVeq' unfolding W_def by auto
      have "{p \<in> top1_S1. q p \<in> V} = {p \<in> top1_S1. q p \<in> W}"
        using hq_S1 hVeq by (by100 blast)
      also have "\<dots> = {p \<in> top1_S1. (fst p^2 - snd p^2, 2*fst p*snd p) \<in> W}"
        using hq_eq by (intro Collect_cong conj_cong refl) auto
      finally have hpre_eq: "{p \<in> top1_S1. q p \<in> V} =
          {p \<in> top1_S1. (fst p^2 - snd p^2, 2*fst p*snd p) \<in> W}" .
      obtain U where hU: "open U" and hfW: "U \<inter> top1_S1 =
          (\<lambda>p. (fst p^2 - snd p^2, 2*fst p*snd p)) -` W \<inter> top1_S1"
        using hcont_S1 hW unfolding continuous_on_open_invariant by blast
      have "{p \<in> top1_S1. (fst p^2 - snd p^2, 2*fst p*snd p) \<in> W} = U \<inter> top1_S1"
        using hfW by (by100 blast)
      hence "{p \<in> top1_S1. q p \<in> V} = U \<inter> top1_S1" using hpre_eq by simp
      moreover have "U \<inter> top1_S1 \<in> top1_S1_topology"
      proof -
        have "U \<in> (top1_open_sets :: (real \<times> real) set set)"
          using hU unfolding top1_open_sets_def by simp
        hence "U \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
          using product_topology_on_open_sets_real2 by (by100 metis)
        thus ?thesis unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      qed
      ultimately show "{p \<in> top1_S1. q p \<in> V} \<in> top1_S1_topology" by simp
    qed
  qed
  \<comment> \<open>Every point of S^1 has an evenly covered neighborhood.
     Use 4 open semicircles: U_top = {(a,b) \<in> S^1 | b > 0}, etc.\<close>
  \<comment> \<open>4 open semicircles covering S^1.\<close>
  define U_top where "U_top = {p \<in> top1_S1. snd p > 0}"
  define U_bot where "U_bot = {p \<in> top1_S1. snd p < 0}"
  define U_right where "U_right = {p \<in> top1_S1. fst p > 0}"
  define U_left where "U_left = {p \<in> top1_S1. fst p < 0}"
  \<comment> \<open>Every point of S^1 is in at least one semicircle.\<close>
  have hcover: "\<And>p. p \<in> top1_S1 \<Longrightarrow> p \<in> U_top \<or> p \<in> U_bot \<or> p \<in> U_right \<or> p \<in> U_left"
  proof -
    fix p assume hp: "p \<in> top1_S1"
    obtain a b where hab: "p = (a, b)" by (cases p) auto
    have hS1: "a\<^sup>2 + b\<^sup>2 = 1" using hp unfolding top1_S1_def hab by simp
    show "p \<in> U_top \<or> p \<in> U_bot \<or> p \<in> U_right \<or> p \<in> U_left"
    proof (cases "b > 0")
      case True thus ?thesis unfolding U_top_def using hp hab by simp
    next
      case False
      show ?thesis
      proof (cases "b < 0")
        case True thus ?thesis unfolding U_bot_def using hp hab by simp
      next
        case False
        hence "b = 0" using \<open>\<not> b > 0\<close> by simp
        hence "a\<^sup>2 = 1" using hS1 by simp
        hence "a = 1 \<or> a = -1" by (metis power2_eq_1_iff)
        thus ?thesis unfolding U_right_def U_left_def using hp hab by auto
      qed
    qed
  qed
  \<comment> \<open>Each semicircle is evenly covered. We prove this for U_top; the others are analogous.\<close>
  have hevenly_top: "top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U_top"
  proof -
    \<comment> \<open>U_top is open in S^1: intersection with open upper half-plane.\<close>
    have hU_top_open: "openin_on top1_S1 top1_S1_topology U_top"
    proof -
      have "open {p :: real \<times> real. snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      hence "{p :: real \<times> real. snd p > 0} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
      hence "{p :: real \<times> real. snd p > 0} \<in> product_topology_on top1_open_sets top1_open_sets"
        using product_topology_on_open_sets_real2 by (by100 metis)
      hence "top1_S1 \<inter> {p. snd p > 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "U_top = top1_S1 \<inter> {p. snd p > 0}" unfolding U_top_def by (by100 blast)
      moreover have "U_top \<subseteq> top1_S1" unfolding U_top_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    \<comment> \<open>V1 = first quadrant, V2 = third quadrant of S^1.\<close>
    define V1 where "V1 = {p \<in> top1_S1. fst p > 0 \<and> snd p > 0}"
    define V2 where "V2 = {p \<in> top1_S1. fst p < 0 \<and> snd p < 0}"
    \<comment> \<open>V1, V2 are open in S^1, disjoint, and q^{-1}(U_top) = V1 \<union> V2.\<close>
    have hV1_open: "openin_on top1_S1 top1_S1_topology V1"
    proof -
      have h1: "open {p :: real \<times> real. fst p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p > 0 \<and> snd p > 0}"
      proof -
        have "{p :: real \<times> real. fst p > 0 \<and> snd p > 0} = {p. fst p > 0} \<inter> {p. snd p > 0}" by auto
        thus ?thesis using open_Int[OF h1 h2] by simp
      qed
      hence "{p :: real \<times> real. fst p > 0 \<and> snd p > 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p > 0 \<and> snd p > 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p > 0 \<and> snd p > 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p > 0 \<and> snd p > 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V1 = top1_S1 \<inter> {p. fst p > 0 \<and> snd p > 0}" unfolding V1_def by (by100 blast)
      moreover have "V1 \<subseteq> top1_S1" unfolding V1_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV2_open: "openin_on top1_S1 top1_S1_topology V2"
    proof -
      have h1: "open {p :: real \<times> real. fst p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p < 0 \<and> snd p < 0}"
      proof -
        have "{p :: real \<times> real. fst p < 0 \<and> snd p < 0} = {p. fst p < 0} \<inter> {p. snd p < 0}" by auto
        thus ?thesis using open_Int[OF h1 h2] by simp
      qed
      hence "{p :: real \<times> real. fst p < 0 \<and> snd p < 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p < 0 \<and> snd p < 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p < 0 \<and> snd p < 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p < 0 \<and> snd p < 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V2 = top1_S1 \<inter> {p. fst p < 0 \<and> snd p < 0}" unfolding V2_def by (by100 blast)
      moreover have "V2 \<subseteq> top1_S1" unfolding V2_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV_disj: "V1 \<inter> V2 = {}" unfolding V1_def V2_def by auto
    have hpreimage: "{p \<in> top1_S1. q p \<in> U_top} = V1 \<union> V2"
    proof (intro set_eqI iffI)
      fix p assume hp: "p \<in> {p \<in> top1_S1. q p \<in> U_top}"
      hence hpS1: "p \<in> top1_S1" and hqp: "q p \<in> U_top" by auto
      obtain x y where hxy: "p = (x, y)" by (cases p) auto
      have hS1: "x\<^sup>2 + y\<^sup>2 = 1" using hpS1 unfolding top1_S1_def hxy by simp
      have "snd (q p) > 0" using hqp unfolding U_top_def by (by100 blast)
      hence "2*x*y > 0" unfolding q_def hxy by simp
      hence "x*y > 0" by simp
      hence "(x > 0 \<and> y > 0) \<or> (x < 0 \<and> y < 0)" using zero_less_mult_iff by force
      thus "p \<in> V1 \<union> V2" unfolding V1_def V2_def using hpS1 hxy by auto
    next
      fix p assume "p \<in> V1 \<union> V2"
      hence hpS1: "p \<in> top1_S1" and hq: "fst p * snd p > 0"
        unfolding V1_def V2_def by (auto intro: mult_pos_pos mult_neg_neg)
      have "snd (q p) = 2 * fst p * snd p" unfolding q_def by simp
      hence "snd (q p) > 0" using hq by simp
      moreover have "q p \<in> top1_S1" by (rule hq_S1[OF hpS1])
      ultimately show "p \<in> {p \<in> top1_S1. q p \<in> U_top}" unfolding U_top_def using hpS1 by auto
    qed
    \<comment> \<open>q is a homeomorphism from V1 to U_top and from V2 to U_top.\<close>
    \<comment> \<open>q is a homeomorphism V1 \<rightarrow> U_top. Inverse: (a,b) \<mapsto> (sqrt((1+a)/2), sqrt((1-a)/2)).\<close>
    have hhomeo1: "top1_homeomorphism_on V1 (subspace_topology top1_S1 top1_S1_topology V1)
        U_top (subspace_topology top1_S1 top1_S1_topology U_top) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V1 (subspace_topology top1_S1 top1_S1_topology V1)"
        by (rule subspace_topology_is_topology_on[OF hTS1]) (use V1_def in blast)
      show "is_topology_on U_top (subspace_topology top1_S1 top1_S1_topology U_top)"
        by (rule subspace_topology_is_topology_on[OF hTS1]) (use U_top_def in blast)
      show "bij_betw q V1 U_top"
      proof (rule bij_betw_imageI)
        \<comment> \<open>Injectivity of q on V1.\<close>
        show "inj_on q V1"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V1" and hp2: "p2 \<in> V1" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1 > 0" "y1 > 0" "x1\<^sup>2 + y1\<^sup>2 = 1"
            using hp1 unfolding V1_def top1_S1_def h1 by auto
          have hx2: "x2 > 0" "y2 > 0" "x2\<^sup>2 + y2\<^sup>2 = 1"
            using hp2 unfolding V1_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2"
            using heq unfolding q_def h1 h2 by auto
          have "x1\<^sup>2 = (1 + (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
          also have "\<dots> = (1 + (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
          also have "\<dots> = x2\<^sup>2" using hx2(3) by (simp add: field_simps)
          finally have "x1\<^sup>2 = x2\<^sup>2" .
          hence "x1 = x2" using hx1(1) hx2(1) by (simp add: power2_eq_iff_nonneg)
          moreover have "y1\<^sup>2 = y2\<^sup>2" using \<open>x1\<^sup>2 = x2\<^sup>2\<close> hx1(3) hx2(3) by linarith
          hence "y1 = y2" using hx1(2) hx2(2) by (simp add: power2_eq_iff_nonneg)
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        \<comment> \<open>q maps V1 onto U_top.\<close>
        show "q ` V1 = U_top"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V1"
          then obtain p where hp: "p \<in> V1" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" "fst p > 0" "snd p > 0" using hp unfolding V1_def by auto
          have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          moreover have "snd (q p) = 2 * fst p * snd p" unfolding q_def by simp
          hence "snd (q p) > 0" using \<open>fst p > 0\<close> \<open>snd p > 0\<close> by simp
          ultimately show "w \<in> U_top" unfolding U_top_def using hw by simp
        next
          fix w assume hw: "w \<in> U_top"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b > 0"
            using hw unfolding U_top_def top1_S1_def hab by auto
          define x where "x = sqrt ((1+a)/2)"
          define y where "y = sqrt ((1-a)/2)"
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square zero_less_mult_iff)
          hence "a\<^sup>2 < 1" using hS1w by linarith
          hence "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)"
            proof
              assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using \<open>a\<^sup>2 < 1\<close> by (simp add: power2_eq_square)
            qed
            moreover have "\<not> (a \<le> -1)"
            proof
              assume "a \<le> -1"
              hence "(-a) \<ge> 1" by linarith
              hence "1 \<le> (-a) * (-a)" using mult_mono[of 1 "-a" 1 "-a"] by simp
              hence "1 \<le> a * a" by simp
              thus False using \<open>a\<^sup>2 < 1\<close> by (simp add: power2_eq_square)
            qed
            ultimately show ?thesis by linarith
          qed
          hence ha_lt: "a < 1" and ha_gt: "-1 < a" by linarith+
          have ha_le: "a \<le> 1" and ha_ge: "-1 \<le> a" using ha_lt ha_gt by linarith+
          have hx_pos: "x > 0" unfolding x_def using ha_gt by simp
          have hy_nonneg: "y \<ge> 0" unfolding y_def using ha_le by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square
            using ha_ge by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square
            using ha_le by (simp add: real_sqrt_mult_self)
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2"
          proof -
            have "2 * x\<^sup>2 = 1 + a" using hx2 by auto
            have "2 * y\<^sup>2 = 1 - a" using hy2 by auto
            have "(2*x*y)\<^sup>2 = 4 * (x\<^sup>2 * y\<^sup>2)"
              by (simp add: power2_eq_square algebra_simps)
            also have "4 * (x\<^sup>2 * y\<^sup>2) = (2 * x\<^sup>2) * (2 * y\<^sup>2)"
              by (simp add: algebra_simps)
            also have "\<dots> = (1+a) * (1-a)" using \<open>2*x\<^sup>2 = 1+a\<close> \<open>2*y\<^sup>2 = 1-a\<close> by simp
            also have "\<dots> = 1 - a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
            also have "\<dots> = b\<^sup>2" using hS1w by linarith
            finally show ?thesis .
          qed
          have hxy_nonneg: "2*x*y \<ge> 0" using hx_pos hy_nonneg by simp
          have hqb: "2*x*y = b" using h2xy_eq_b2 hxy_nonneg hb by (simp add: power2_eq_iff_nonneg)
          have hy_pos: "y > 0"
          proof -
            have "2*x*y > 0" using hqb hb by simp
            hence "x*y > 0" by simp
            thus "y > 0" using hx_pos by (simp add: zero_less_mult_iff)
          qed
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have "(x, y) \<in> V1" unfolding V1_def top1_S1_def using hxy_S1 hx_pos hy_pos by simp
          moreover have "q (x, y) = w" unfolding q_def hab using hqa hqb by simp
          ultimately show "w \<in> q ` V1" by (by100 blast)
        qed
      qed
      show "top1_continuous_map_on V1 (subspace_topology top1_S1 top1_S1_topology V1)
          U_top (subspace_topology top1_S1 top1_S1_topology U_top) q"
      proof -
        have hV1_sub: "V1 \<subseteq> top1_S1" unfolding V1_def by (by100 blast)
        have hU_sub: "U_top \<subseteq> top1_S1" unfolding U_top_def by (by100 blast)
        have hq_V1: "top1_continuous_map_on V1 (subspace_topology top1_S1 top1_S1_topology V1)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV1_sub])
        have hq_img: "q ` V1 \<subseteq> U_top" using \<open>bij_betw q V1 U_top\<close> unfolding bij_betw_def by (by100 blast)
        \<comment> \<open>Restrict range: V \<in> subspace(S^1, U_top) means V = U_top \<inter> W, W \<in> top_S1.
           q^{-1}(V) \<inter> V1 = q^{-1}(W) \<inter> V1 \<in> subspace(S^1, V1).\<close>
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V1" thus "q p \<in> U_top" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_top"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_top \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V1. q p \<in> V} = {p \<in> V1. q p \<in> W}"
            using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V1. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V1"
            using hq_V1 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V1. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V1" by simp
        qed
      qed
      show "top1_continuous_map_on U_top (subspace_topology top1_S1 top1_S1_topology U_top)
          V1 (subspace_topology top1_S1 top1_S1_topology V1) (inv_into V1 q)"
      proof -
        \<comment> \<open>The inverse is (a,b) \<mapsto> (sqrt((1+a)/2), sqrt((1-a)/2)).
           This is continuous as a real-valued function on U_top.\<close>
        define qi where "qi = (\<lambda>(a::real, b::real). (sqrt ((1+a)/2), sqrt ((1-a)/2)))"
        \<comment> \<open>qi agrees with inv_into V1 q on U_top.\<close>
        have hqi_eq: "\<And>w. w \<in> U_top \<Longrightarrow> qi w = inv_into V1 q w"
        proof -
          fix w assume hw: "w \<in> U_top"
          \<comment> \<open>qi w \<in> V1 and q(qi w) = w, so inv_into gives qi w.\<close>
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b > 0"
            using hw unfolding U_top_def top1_S1_def hab by auto
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square zero_less_mult_iff)
          hence "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using \<open>a\<^sup>2 < 1\<close> by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "(-a) \<ge> 1" by linarith
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by simp
              hence "1 \<le> a*a" by simp
              thus False using \<open>a\<^sup>2 < 1\<close> by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = sqrt ((1+a)/2)"
          define y where "y = sqrt ((1-a)/2)"
          have "qi w = (x, y)" unfolding qi_def hab x_def y_def by simp
          moreover have "(x, y) \<in> V1"
          proof -
            have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
            have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
            have "x > 0" unfolding x_def using ha_bounds by simp
            have "y > 0"
            proof -
              have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2"
              proof -
                have "2*x\<^sup>2 = 1+a" using hx2 by auto
                have "2*y\<^sup>2 = 1-a" using hy2 by auto
                have "(2*x*y)\<^sup>2 = 4*(x\<^sup>2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
                also have "\<dots> = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: algebra_simps)
                also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2 = 1+a\<close> \<open>2*y\<^sup>2 = 1-a\<close> by simp
                also have "\<dots> = 1 - a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
                also have "\<dots> = b\<^sup>2" using hS1w by linarith
                finally show ?thesis .
              qed
              have "2*x*y \<ge> 0" using \<open>x > 0\<close> ha_bounds unfolding y_def
                by (intro mult_nonneg_nonneg) auto
              have "2*x*y = b" using h2xy_eq_b2 \<open>2*x*y \<ge> 0\<close> hb by (simp add: power2_eq_iff_nonneg)
              hence "x*y > 0" using hb by simp
              thus "y > 0" using \<open>x > 0\<close> by (simp add: zero_less_mult_iff)
            qed
            have "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
            show ?thesis unfolding V1_def top1_S1_def using \<open>x > 0\<close> \<open>y > 0\<close> \<open>x\<^sup>2+y\<^sup>2=1\<close> by simp
          qed
          moreover have "q (x, y) = w"
          proof -
            have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
            have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
            have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2"
            proof -
              have "(2*x*y)\<^sup>2 = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
              also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
              also have "\<dots> = 1-a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
              also have "\<dots> = b\<^sup>2" using hS1w by linarith
              finally show ?thesis .
            qed
            have "x > 0" unfolding x_def using ha_bounds by simp
            have "2*x*y \<ge> 0" using \<open>x > 0\<close> ha_bounds unfolding y_def
              by (intro mult_nonneg_nonneg) auto
            have hqb: "2*x*y = b"
              using h2xy_eq_b2 \<open>2*x*y \<ge> 0\<close> hb by (simp add: power2_eq_iff_nonneg)
            show ?thesis unfolding q_def hab using hqa hqb by simp
          qed
          ultimately show "qi w = inv_into V1 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF \<open>bij_betw q V1 U_top\<close>]]])
        qed
        \<comment> \<open>qi maps U_top into V1.\<close>
        have hqi_V1: "\<And>w. w \<in> U_top \<Longrightarrow> qi w \<in> V1"
        proof -
          fix w assume hw: "w \<in> U_top"
          have "qi w = inv_into V1 q w" by (rule hqi_eq[OF hw])
          moreover have "inv_into V1 q w \<in> V1"
          proof -
            have "q ` V1 = U_top" using \<open>bij_betw q V1 U_top\<close> unfolding bij_betw_def by (by100 blast)
            hence "w \<in> q ` V1" using hw by simp
            thus ?thesis by (rule inv_into_into)
          qed
          ultimately show "qi w \<in> V1" by simp
        qed
        \<comment> \<open>qi is continuous on U_top (sqrt composed with continuous affine maps).\<close>
        have hqi_cont: "continuous_on U_top qi"
        proof -
          have "continuous_on U_top (\<lambda>(a, b). (sqrt ((1+a)/2), sqrt ((1-a)/2)))"
            unfolding split_def by (intro continuous_intros) auto
          thus ?thesis unfolding qi_def by simp
        qed
        \<comment> \<open>Bridge: since qi = inv_into on U_top, and qi is continuous + maps into V1,
           we get inv_into continuous from U_top to V1.\<close>
        have hU_sub: "U_top \<subseteq> top1_S1" unfolding U_top_def by (by100 blast)
        have hV1_sub: "V1 \<subseteq> top1_S1" unfolding V1_def by (by100 blast)
        \<comment> \<open>U_top \<subseteq> UNIV (as pairs of reals), so continuous_on U_top qi gives
           preimages of open sets are relatively open.\<close>
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_top"
          show "inv_into V1 q w \<in> V1" using hqi_eq[OF \<open>w \<in> U_top\<close>] hqi_V1[OF \<open>w \<in> U_top\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V1"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V1 \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "W = top1_S1 \<inter> W''"
            using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
          have hW'_open: "open W''" using hW''
            by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          define W' where "W' = W''"
          have hW': "open W'" and hW'eq: "W = top1_S1 \<inter> W'"
            using hW'_open hWeq unfolding W'_def by auto
          \<comment> \<open>{w \<in> U_top. inv_into w \<in> V} = {w \<in> U_top. qi w \<in> W'} (since qi maps into V1 \<subseteq> S^1).\<close>
          have "{w \<in> U_top. inv_into V1 q w \<in> V} = {w \<in> U_top. qi w \<in> W'}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_top"
            have "inv_into V1 q w = qi w" using hqi_eq[OF hw] by simp
            moreover have "qi w \<in> V1" using hqi_V1[OF hw] .
            moreover have "V1 \<subseteq> top1_S1" using hV1_sub .
            ultimately show "(inv_into V1 q w \<in> V) = (qi w \<in> W')"
              using hVeq hW'eq by auto
          qed
          \<comment> \<open>qi^{-1}(W') \<inter> U_top is open in U_top (by continuous_on).\<close>
          moreover have "{w \<in> U_top. qi w \<in> W'} \<in> subspace_topology top1_S1 top1_S1_topology U_top"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_top = qi -` W' \<inter> U_top"
              using hqi_cont hW' unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_top. qi w \<in> W'} = U \<inter> U_top" using hUeq by (by100 blast)
            moreover have "U \<inter> U_top \<in> subspace_topology top1_S1 top1_S1_topology U_top"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_top = U_top \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_top. inv_into V1 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_top" by simp
        qed
      qed
    qed
    \<comment> \<open>q is a homeomorphism V2 \<rightarrow> U_top. Inverse: (a,b) \<mapsto> (-sqrt((1+a)/2), -sqrt((1-a)/2)).\<close>
    have hhomeo2: "top1_homeomorphism_on V2 (subspace_topology top1_S1 top1_S1_topology V2)
        U_top (subspace_topology top1_S1 top1_S1_topology U_top) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1': "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V2 (subspace_topology top1_S1 top1_S1_topology V2)"
        by (rule subspace_topology_is_topology_on[OF hTS1']) (use V2_def in blast)
      show "is_topology_on U_top (subspace_topology top1_S1 top1_S1_topology U_top)"
        by (rule subspace_topology_is_topology_on[OF hTS1']) (use U_top_def in blast)
      show "bij_betw q V2 U_top"
      proof (rule bij_betw_imageI)
        show "inj_on q V2"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V2" and hp2: "p2 \<in> V2" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1 < 0" "y1 < 0" "x1\<^sup>2 + y1\<^sup>2 = 1"
            using hp1 unfolding V2_def top1_S1_def h1 by auto
          have hx2: "x2 < 0" "y2 < 0" "x2\<^sup>2 + y2\<^sup>2 = 1"
            using hp2 unfolding V2_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2"
            using heq unfolding q_def h1 h2 by auto
          have "x1\<^sup>2 = (1 + (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
          also have "\<dots> = (1 + (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
          also have "\<dots> = x2\<^sup>2" using hx2(3) by (simp add: field_simps)
          finally have "x1\<^sup>2 = x2\<^sup>2" .
          hence "x1 = x2 \<or> x1 = -x2" using power2_eq_iff by (by100 blast)
          hence "x1 = x2" using hx1(1) hx2(1) by linarith
          moreover have "y1\<^sup>2 = y2\<^sup>2" using \<open>x1\<^sup>2 = x2\<^sup>2\<close> hx1(3) hx2(3) by linarith
          hence "y1 = y2 \<or> y1 = -y2" using power2_eq_iff by (by100 blast)
          hence "y1 = y2" using hx1(2) hx2(2) by linarith
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V2 = U_top"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V2"
          then obtain p where hp: "p \<in> V2" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" "fst p < 0" "snd p < 0" using hp unfolding V2_def by auto
          have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          moreover have "snd (q p) = 2 * fst p * snd p" unfolding q_def by simp
          hence "snd (q p) > 0" using \<open>fst p < 0\<close> \<open>snd p < 0\<close> by (simp add: mult_neg_neg)
          ultimately show "w \<in> U_top" unfolding U_top_def using hw by simp
        next
          fix w assume hw: "w \<in> U_top"
          \<comment> \<open>Inverse: (a,b) \<mapsto> (-sqrt((1+a)/2), -sqrt((1-a)/2)).\<close>
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b > 0"
            using hw unfolding U_top_def top1_S1_def hab by auto
          \<comment> \<open>Reuse the V1 inverse but negate.\<close>
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square zero_less_mult_iff)
          hence "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using \<open>a\<^sup>2 < 1\<close> by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "(-a) \<ge> 1" by linarith
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by simp
              hence "1 \<le> a*a" by simp
              thus False using \<open>a\<^sup>2 < 1\<close> by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = -sqrt ((1+a)/2)"
          define y where "y = -sqrt ((1-a)/2)"
          have hx_neg: "x < 0" unfolding x_def using ha_bounds by simp
          have hy_neg: "y < 0" proof -
            have "sqrt ((1-a)/2) > 0" using ha_bounds by simp
            thus ?thesis unfolding y_def by simp
          qed
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square
            using ha_bounds by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square
            using ha_bounds by (simp add: real_sqrt_mult_self)
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have "2*x\<^sup>2 = 1+a" using hx2 by auto
          have "2*y\<^sup>2 = 1-a" using hy2 by auto
          have "(2*x*y)\<^sup>2 = 4*(x\<^sup>2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: algebra_simps)
          also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
          also have "\<dots> = 1 - a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2" using hS1w by linarith
          finally have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2" .
          have "2*x*y \<ge> 0" using hx_neg hy_neg by (simp add: mult_nonpos_nonpos)
          have hqb: "2*x*y = b" using h2xy_eq_b2 \<open>2*x*y \<ge> 0\<close> hb by (simp add: power2_eq_iff_nonneg)
          have "(x, y) \<in> V2" unfolding V2_def top1_S1_def using hxy_S1 hx_neg hy_neg by simp
          moreover have "q (x, y) = w" unfolding q_def hab using hqa hqb by simp
          ultimately show "w \<in> q ` V2" by (by100 blast)
        qed
      qed
      \<comment> \<open>Continuity: same pattern as V1.\<close>
      show "top1_continuous_map_on V2 (subspace_topology top1_S1 top1_S1_topology V2)
          U_top (subspace_topology top1_S1 top1_S1_topology U_top) q"
      proof -
        have hV2_sub: "V2 \<subseteq> top1_S1" unfolding V2_def by (by100 blast)
        have hU_sub: "U_top \<subseteq> top1_S1" unfolding U_top_def by (by100 blast)
        have hq_V2: "top1_continuous_map_on V2 (subspace_topology top1_S1 top1_S1_topology V2)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV2_sub])
        have hq_img: "q ` V2 \<subseteq> U_top"
          using \<open>bij_betw q V2 U_top\<close> unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V2" thus "q p \<in> U_top" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_top"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_top \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V2. q p \<in> V} = {p \<in> V2. q p \<in> W}"
            using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V2. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V2"
            using hq_V2 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V2. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V2" by simp
        qed
      qed
      show "top1_continuous_map_on U_top (subspace_topology top1_S1 top1_S1_topology U_top)
          V2 (subspace_topology top1_S1 top1_S1_topology V2) (inv_into V2 q)"
      proof -
        define qi2 where "qi2 = (\<lambda>(a::real, b::real). (-sqrt ((1+a)/2), -sqrt ((1-a)/2)))"
        \<comment> \<open>qi2 maps U_top into V2 and q \<circ> qi2 = id on U_top.\<close>
        have hqi2_props: "\<And>w. w \<in> U_top \<Longrightarrow> qi2 w \<in> V2 \<and> q (qi2 w) = w"
        proof -
          fix w assume hw: "w \<in> U_top"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b > 0"
            using hw unfolding U_top_def top1_S1_def hab by auto
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square zero_less_mult_iff)
          hence ha2: "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by linarith
              thus False using ha2 by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = -sqrt ((1+a)/2)"
          define y where "y = -sqrt ((1-a)/2)"
          have hqi2_w: "qi2 w = (x, y)" unfolding qi2_def hab x_def y_def by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hx_neg: "x < 0" unfolding x_def using ha_bounds by simp
          have hy_neg: "y < 0" unfolding y_def using ha_bounds by simp
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have "2*x\<^sup>2 = 1+a" using hx2 by auto
          have "2*y\<^sup>2 = 1-a" using hy2 by auto
          have "(2*x*y)\<^sup>2 = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
          also have "\<dots> = 1-a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2" using hS1w by linarith
          finally have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2" .
          have "2*x*y \<ge> 0" using hx_neg hy_neg by (simp add: mult_nonpos_nonpos)
          have hqb: "2*x*y = b" using h2xy_eq_b2 \<open>2*x*y \<ge> 0\<close> hb by (simp add: power2_eq_iff_nonneg)
          have "qi2 w \<in> V2" unfolding hqi2_w V2_def top1_S1_def using hxy_S1 hx_neg hy_neg by simp
          moreover have "q (qi2 w) = w"
          proof -
            have "fst (q (x, y)) = x\<^sup>2 - y\<^sup>2" unfolding q_def by simp
            hence "fst (q (x, y)) = a" using hqa by simp
            moreover have "snd (q (x, y)) = 2*x*y" unfolding q_def by simp
            hence "snd (q (x, y)) = b" using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi2_w hab by simp
          qed
          ultimately show "qi2 w \<in> V2 \<and> q (qi2 w) = w" by (by100 blast)
        qed
        have hqi2_eq: "\<And>w. w \<in> U_top \<Longrightarrow> qi2 w = inv_into V2 q w"
        proof -
          fix w assume hw: "w \<in> U_top"
          have "qi2 w \<in> V2" and "q (qi2 w) = w" using hqi2_props[OF hw] by auto
          thus "qi2 w = inv_into V2 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF \<open>bij_betw q V2 U_top\<close>]]])
        qed
        have hqi2_V2: "\<And>w. w \<in> U_top \<Longrightarrow> qi2 w \<in> V2"
          using hqi2_props by (by100 blast)
        have hqi2_cont: "continuous_on U_top qi2"
          unfolding qi2_def split_def by (intro continuous_intros) auto
        have hU_sub: "U_top \<subseteq> top1_S1" unfolding U_top_def by (by100 blast)
        have hV2_sub: "V2 \<subseteq> top1_S1" unfolding V2_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_top"
          show "inv_into V2 q w \<in> V2" using hqi2_eq[OF \<open>w \<in> U_top\<close>] hqi2_V2[OF \<open>w \<in> U_top\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V2"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V2 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V2 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_top. inv_into V2 q w \<in> V} = {w \<in> U_top. qi2 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_top"
            have "inv_into V2 q w = qi2 w" using hqi2_eq[OF hw] by simp
            moreover have "qi2 w \<in> V2" using hqi2_V2[OF hw] .
            moreover have "V2 \<subseteq> top1_S1" using hV2_sub .
            ultimately show "(inv_into V2 q w \<in> V) = (qi2 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_top. qi2 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_top"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_top = qi2 -` W'' \<inter> U_top"
              using hqi2_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_top. qi2 w \<in> W''} = U \<inter> U_top" using hUeq by (by100 blast)
            moreover have "U \<inter> U_top \<in> subspace_topology top1_S1 top1_S1_topology U_top"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_top = U_top \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_top. inv_into V2 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_top" by simp
        qed
      qed
    qed
    show ?thesis unfolding top1_evenly_covered_on_def
    proof (intro conjI exI[of _ "{V1, V2}"])
      show "openin_on top1_S1 top1_S1_topology U_top" by (rule hU_top_open)
      show "\<forall>V\<in>{V1, V2}. openin_on top1_S1 top1_S1_topology V"
        using hV1_open hV2_open by (by100 blast)
      show "\<forall>V\<in>{V1, V2}. \<forall>V'\<in>{V1, V2}. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
        using hV_disj by (by100 blast)
      show "{x \<in> top1_S1. q x \<in> U_top} = \<Union> {V1, V2}" using hpreimage by simp
      show "\<forall>V\<in>{V1, V2}. top1_homeomorphism_on V (subspace_topology top1_S1 top1_S1_topology V)
          U_top (subspace_topology top1_S1 top1_S1_topology U_top) q"
        using hhomeo1 hhomeo2 by (by100 blast)
    qed
  qed
  \<comment> \<open>The remaining 3 semicircle cases are analogous to U_top.
     U_bot: preimage splits into Q2 \<union> Q4, inverse uses mixed signs.
     U_right/U_left: preimage splits using fst > 0 / fst < 0 condition.
     Each follows the exact same proof pattern as hevenly_top.\<close>
  have hevenly_bot: "top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U_bot"
  proof -
    have hU_bot_open: "openin_on top1_S1 top1_S1_topology U_bot"
    proof -
      have "open {p :: real \<times> real. snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      hence "{p :: real \<times> real. snd p < 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. snd p < 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. snd p < 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. snd p < 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "U_bot = top1_S1 \<inter> {p. snd p < 0}" unfolding U_bot_def by (by100 blast)
      moreover have "U_bot \<subseteq> top1_S1" unfolding U_bot_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    define V3 where "V3 = {p \<in> top1_S1. fst p < 0 \<and> snd p > 0}"
    define V4 where "V4 = {p \<in> top1_S1. fst p > 0 \<and> snd p < 0}"
    have hV3_open: "openin_on top1_S1 top1_S1_topology V3"
    proof -
      have h1: "open {p :: real \<times> real. fst p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p < 0 \<and> snd p > 0}"
        using open_Int[OF h1 h2] by (auto simp: Int_def)
      hence "{p :: real \<times> real. fst p < 0 \<and> snd p > 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p < 0 \<and> snd p > 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p < 0 \<and> snd p > 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p < 0 \<and> snd p > 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V3 = top1_S1 \<inter> {p. fst p < 0 \<and> snd p > 0}" unfolding V3_def by (by100 blast)
      moreover have "V3 \<subseteq> top1_S1" unfolding V3_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV4_open: "openin_on top1_S1 top1_S1_topology V4"
    proof -
      have h1: "open {p :: real \<times> real. fst p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p > 0 \<and> snd p < 0}"
        using open_Int[OF h1 h2] by (auto simp: Int_def)
      hence "{p :: real \<times> real. fst p > 0 \<and> snd p < 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p > 0 \<and> snd p < 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p > 0 \<and> snd p < 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p > 0 \<and> snd p < 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V4 = top1_S1 \<inter> {p. fst p > 0 \<and> snd p < 0}" unfolding V4_def by (by100 blast)
      moreover have "V4 \<subseteq> top1_S1" unfolding V4_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV_disj: "V3 \<inter> V4 = {}" unfolding V3_def V4_def by auto
    have hpreimage: "{p \<in> top1_S1. q p \<in> U_bot} = V3 \<union> V4"
    proof (intro set_eqI iffI)
      fix p assume hp: "p \<in> {p \<in> top1_S1. q p \<in> U_bot}"
      hence hpS1: "p \<in> top1_S1" and hqp: "q p \<in> U_bot" by auto
      obtain x y where hxy: "p = (x, y)" by (cases p) auto
      have "snd (q p) < 0" using hqp unfolding U_bot_def by (by100 blast)
      hence "2*x*y < 0" unfolding q_def hxy by simp
      hence "x*y < 0" by simp
      hence "(x < 0 \<and> y > 0) \<or> (x > 0 \<and> y < 0)" using mult_less_0_iff by force
      thus "p \<in> V3 \<union> V4" unfolding V3_def V4_def using hpS1 hxy by auto
    next
      fix p assume "p \<in> V3 \<union> V4"
      hence hpS1: "p \<in> top1_S1" and hq: "fst p * snd p < 0"
        unfolding V3_def V4_def by (auto intro: mult_neg_pos mult_pos_neg)
      have "snd (q p) = 2 * fst p * snd p" unfolding q_def by simp
      hence "snd (q p) < 0" using hq by simp
      moreover have "q p \<in> top1_S1" by (rule hq_S1[OF hpS1])
      ultimately show "p \<in> {p \<in> top1_S1. q p \<in> U_bot}" unfolding U_bot_def using hpS1 by auto
    qed
    \<comment> \<open>Homeomorphisms V3 \<rightarrow> U_bot and V4 \<rightarrow> U_bot: same structure as hhomeo1/hhomeo2.
       V3 inverse: (a,b) \<mapsto> (-sqrt((1+a)/2), sqrt((1-a)/2)) with b < 0.
       V4 inverse: (a,b) \<mapsto> (sqrt((1+a)/2), -sqrt((1-a)/2)) with b < 0.\<close>
    have hhomeo3: "top1_homeomorphism_on V3 (subspace_topology top1_S1 top1_S1_topology V3)
        U_bot (subspace_topology top1_S1 top1_S1_topology U_bot) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V3 (subspace_topology top1_S1 top1_S1_topology V3)"
        by (rule subspace_topology_is_topology_on[OF hTS1]) (use V3_def in blast)
      show "is_topology_on U_bot (subspace_topology top1_S1 top1_S1_topology U_bot)"
        by (rule subspace_topology_is_topology_on[OF hTS1]) (use U_bot_def in blast)
      show "bij_betw q V3 U_bot"
      proof (rule bij_betw_imageI)
        show "inj_on q V3"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V3" and hp2: "p2 \<in> V3" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1 < 0" "y1 > 0" "x1\<^sup>2 + y1\<^sup>2 = 1" using hp1 unfolding V3_def top1_S1_def h1 by auto
          have hx2: "x2 < 0" "y2 > 0" "x2\<^sup>2 + y2\<^sup>2 = 1" using hp2 unfolding V3_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2" using heq unfolding q_def h1 h2 by auto
          have "x1\<^sup>2 = (1 + (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
          also have "\<dots> = (1 + (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
          also have "\<dots> = x2\<^sup>2" using hx2(3) by (simp add: field_simps)
          finally have "x1\<^sup>2 = x2\<^sup>2" .
          hence "x1 = x2 \<or> x1 = -x2" using power2_eq_iff by (by100 blast)
          hence "x1 = x2" using hx1(1) hx2(1) by linarith
          moreover have "y1\<^sup>2 = y2\<^sup>2" using \<open>x1\<^sup>2 = x2\<^sup>2\<close> hx1(3) hx2(3) by linarith
          hence "y1 = y2 \<or> y1 = -y2" using power2_eq_iff by (by100 blast)
          hence "y1 = y2" using hx1(2) hx2(2) by linarith
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V3 = U_bot"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V3"
          then obtain p where hp: "p \<in> V3" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" "fst p < 0" "snd p > 0" using hp unfolding V3_def by auto
          have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          moreover have "snd (q p) = 2 * fst p * snd p" unfolding q_def by simp
          hence "snd (q p) < 0" using \<open>fst p < 0\<close> \<open>snd p > 0\<close> by (simp add: mult_neg_pos)
          ultimately show "w \<in> U_bot" unfolding U_bot_def using hw by simp
        next
          fix w assume hw: "w \<in> U_bot"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b < 0" using hw unfolding U_bot_def top1_S1_def hab by auto
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square) (simp add: mult_neg_neg)
          hence ha2: "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by linarith
              hence "1 \<le> a*a" by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = -sqrt ((1+a)/2)"
          define y where "y = sqrt ((1-a)/2)"
          have hx_neg: "x < 0" unfolding x_def using ha_bounds by simp
          have hy_pos: "y > 0" unfolding y_def using ha_bounds by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have "2*x\<^sup>2 = 1+a" using hx2 by auto
          have "2*y\<^sup>2 = 1-a" using hy2 by auto
          have "(2*x*y)\<^sup>2 = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
          also have "\<dots> = 1-a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2" using hS1w by linarith
          finally have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2" .
          have "2*x*y \<le> 0" using hx_neg hy_pos by (simp add: mult_nonpos_nonneg)
          have hqb: "2*x*y = b"
          proof -
            have "2*x*y = b \<or> 2*x*y = -b" using h2xy_eq_b2 power2_eq_iff by (by100 blast)
            thus ?thesis using \<open>2*x*y \<le> 0\<close> hb by linarith
          qed
          have "(x, y) \<in> V3" unfolding V3_def top1_S1_def using hxy_S1 hx_neg hy_pos by simp
          moreover have "q (x, y) = w"
          proof -
            have "fst (q (x, y)) = x\<^sup>2 - y\<^sup>2" unfolding q_def by simp
            hence "fst (q (x, y)) = a" using hqa by simp
            moreover have "snd (q (x, y)) = 2*x*y" unfolding q_def by simp
            hence "snd (q (x, y)) = b" using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hab by simp
          qed
          ultimately show "w \<in> q ` V3" by (by100 blast)
        qed
      qed
      show "top1_continuous_map_on V3 (subspace_topology top1_S1 top1_S1_topology V3)
          U_bot (subspace_topology top1_S1 top1_S1_topology U_bot) q"
      proof -
        have hV3_sub: "V3 \<subseteq> top1_S1" unfolding V3_def by (by100 blast)
        have hU_sub: "U_bot \<subseteq> top1_S1" unfolding U_bot_def by (by100 blast)
        have hq_V3: "top1_continuous_map_on V3 (subspace_topology top1_S1 top1_S1_topology V3)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV3_sub])
        have hq_img: "q ` V3 \<subseteq> U_bot"
          using \<open>bij_betw q V3 U_bot\<close> unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V3" thus "q p \<in> U_bot" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_bot"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_bot \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V3. q p \<in> V} = {p \<in> V3. q p \<in> W}"
            using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V3. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V3"
            using hq_V3 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V3. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V3" by simp
        qed
      qed
      show "top1_continuous_map_on U_bot (subspace_topology top1_S1 top1_S1_topology U_bot)
          V3 (subspace_topology top1_S1 top1_S1_topology V3) (inv_into V3 q)"
      proof -
        define qi3 where "qi3 = (\<lambda>(a::real, b::real). (-sqrt ((1+a)/2), sqrt ((1-a)/2)))"
        have hqi3_props: "\<And>w. w \<in> U_bot \<Longrightarrow> qi3 w \<in> V3 \<and> q (qi3 w) = w"
        proof -
          fix w assume hw: "w \<in> U_bot"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b < 0" using hw unfolding U_bot_def top1_S1_def hab by auto
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square) (simp add: mult_neg_neg)
          hence ha2: "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by linarith
              hence "1 \<le> a*a" by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = -sqrt ((1+a)/2)" define y where "y = sqrt ((1-a)/2)"
          have hqi3_w: "qi3 w = (x, y)" unfolding qi3_def hab x_def y_def by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hx_neg: "x < 0" unfolding x_def using ha_bounds by simp
          have hy_pos: "y > 0" unfolding y_def using ha_bounds by simp
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have "2*x\<^sup>2 = 1+a" using hx2 by auto
          have "2*y\<^sup>2 = 1-a" using hy2 by auto
          have "(2*x*y)\<^sup>2 = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
          also have "\<dots> = 1-a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2" using hS1w by linarith
          finally have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2" .
          have hqb: "2*x*y = b"
          proof -
            have "2*x*y = b \<or> 2*x*y = -b" using h2xy_eq_b2 power2_eq_iff by (by100 blast)
            moreover have "2*x*y \<le> 0" using hx_neg hy_pos by (simp add: mult_nonpos_nonneg)
            ultimately show ?thesis using hb by linarith
          qed
          have "qi3 w \<in> V3" unfolding hqi3_w V3_def top1_S1_def using hxy_S1 hx_neg hy_pos by simp
          moreover have "q (qi3 w) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi3_w hab by simp
          qed
          ultimately show "qi3 w \<in> V3 \<and> q (qi3 w) = w" by (by100 blast)
        qed
        have hqi3_eq: "\<And>w. w \<in> U_bot \<Longrightarrow> qi3 w = inv_into V3 q w"
        proof -
          fix w assume hw: "w \<in> U_bot"
          have "qi3 w \<in> V3" and "q (qi3 w) = w" using hqi3_props[OF hw] by auto
          thus "qi3 w = inv_into V3 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF \<open>bij_betw q V3 U_bot\<close>]]])
        qed
        have hqi3_V3: "\<And>w. w \<in> U_bot \<Longrightarrow> qi3 w \<in> V3" using hqi3_props by (by100 blast)
        have hqi3_cont: "continuous_on U_bot qi3"
          unfolding qi3_def split_def by (intro continuous_intros) auto
        have hU_sub: "U_bot \<subseteq> top1_S1" unfolding U_bot_def by (by100 blast)
        have hV3_sub: "V3 \<subseteq> top1_S1" unfolding V3_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_bot"
          show "inv_into V3 q w \<in> V3" using hqi3_eq[OF \<open>w \<in> U_bot\<close>] hqi3_V3[OF \<open>w \<in> U_bot\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V3"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V3 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V3 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_bot. inv_into V3 q w \<in> V} = {w \<in> U_bot. qi3 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_bot"
            have "inv_into V3 q w = qi3 w" using hqi3_eq[OF hw] by simp
            moreover have "qi3 w \<in> V3" using hqi3_V3[OF hw] .
            moreover have "V3 \<subseteq> top1_S1" using hV3_sub .
            ultimately show "(inv_into V3 q w \<in> V) = (qi3 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_bot. qi3 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_bot"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_bot = qi3 -` W'' \<inter> U_bot"
              using hqi3_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_bot. qi3 w \<in> W''} = U \<inter> U_bot" using hUeq by (by100 blast)
            moreover have "U \<inter> U_bot \<in> subspace_topology top1_S1 top1_S1_topology U_bot"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_bot = U_bot \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_bot. inv_into V3 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_bot" by simp
        qed
      qed
    qed
    have hhomeo4: "top1_homeomorphism_on V4 (subspace_topology top1_S1 top1_S1_topology V4)
        U_bot (subspace_topology top1_S1 top1_S1_topology U_bot) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1'': "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V4 (subspace_topology top1_S1 top1_S1_topology V4)"
        by (rule subspace_topology_is_topology_on[OF hTS1'']) (use V4_def in blast)
      show "is_topology_on U_bot (subspace_topology top1_S1 top1_S1_topology U_bot)"
        by (rule subspace_topology_is_topology_on[OF hTS1'']) (use U_bot_def in blast)
      show hbij4: "bij_betw q V4 U_bot"
      proof (rule bij_betw_imageI)
        show "inj_on q V4"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V4" and hp2: "p2 \<in> V4" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1 > 0" "y1 < 0" "x1\<^sup>2 + y1\<^sup>2 = 1" using hp1 unfolding V4_def top1_S1_def h1 by auto
          have hx2: "x2 > 0" "y2 < 0" "x2\<^sup>2 + y2\<^sup>2 = 1" using hp2 unfolding V4_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2" using heq unfolding q_def h1 h2 by auto
          have "x1\<^sup>2 = x2\<^sup>2"
          proof -
            have "x1\<^sup>2 = (1 + (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
            also have "\<dots> = (1 + (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
            also have "\<dots> = x2\<^sup>2" using hx2(3) by (simp add: field_simps)
            finally show ?thesis .
          qed
          hence "x1 = x2" using hx1(1) hx2(1) by (simp add: power2_eq_iff_nonneg)
          moreover have "y1\<^sup>2 = y2\<^sup>2" using \<open>x1\<^sup>2 = x2\<^sup>2\<close> hx1(3) hx2(3) by linarith
          hence "y1 = y2 \<or> y1 = -y2" using power2_eq_iff by (by100 blast)
          hence "y1 = y2" using hx1(2) hx2(2) by linarith
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V4 = U_bot"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V4"
          then obtain p where hp: "p \<in> V4" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" "fst p > 0" "snd p < 0" using hp unfolding V4_def by auto
          have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          moreover have "snd (q p) = 2 * fst p * snd p" unfolding q_def by simp
          hence "snd (q p) < 0" using \<open>fst p > 0\<close> \<open>snd p < 0\<close> by (simp add: mult_pos_neg)
          ultimately show "w \<in> U_bot" unfolding U_bot_def using hw by simp
        next
          fix w assume hw: "w \<in> U_bot"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b < 0" using hw unfolding U_bot_def top1_S1_def hab by auto
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square) (simp add: mult_neg_neg)
          hence ha2: "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by linarith
              hence "1 \<le> a*a" by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = sqrt ((1+a)/2)" define y where "y = -sqrt ((1-a)/2)"
          have hx_pos: "x > 0" unfolding x_def using ha_bounds by simp
          have hy_neg: "y < 0" unfolding y_def using ha_bounds by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have "2*x\<^sup>2 = 1+a" using hx2 by auto
          have "2*y\<^sup>2 = 1-a" using hy2 by auto
          have "(2*x*y)\<^sup>2 = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
          also have "\<dots> = 1-a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2" using hS1w by linarith
          finally have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2" .
          have hqb: "2*x*y = b"
          proof -
            have "2*x*y = b \<or> 2*x*y = -b" using h2xy_eq_b2 power2_eq_iff by (by100 blast)
            moreover have "2*x*y \<le> 0" using hx_pos hy_neg by (simp add: mult_nonneg_nonpos)
            ultimately show ?thesis using hb by linarith
          qed
          have "(x, y) \<in> V4" unfolding V4_def top1_S1_def using hxy_S1 hx_pos hy_neg by simp
          moreover have "q (x, y) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hab by simp
          qed
          ultimately show "w \<in> q ` V4" by (by100 blast)
        qed
      qed
      show "top1_continuous_map_on V4 (subspace_topology top1_S1 top1_S1_topology V4)
          U_bot (subspace_topology top1_S1 top1_S1_topology U_bot) q"
      proof -
        have hV4_sub: "V4 \<subseteq> top1_S1" unfolding V4_def by (by100 blast)
        have hU_sub: "U_bot \<subseteq> top1_S1" unfolding U_bot_def by (by100 blast)
        have hq_V4: "top1_continuous_map_on V4 (subspace_topology top1_S1 top1_S1_topology V4)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV4_sub])
        have hq_img: "q ` V4 \<subseteq> U_bot" using hbij4 unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V4" thus "q p \<in> U_bot" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_bot"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_bot \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V4. q p \<in> V} = {p \<in> V4. q p \<in> W}" using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V4. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V4"
            using hq_V4 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V4. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V4" by simp
        qed
      qed
      show "top1_continuous_map_on U_bot (subspace_topology top1_S1 top1_S1_topology U_bot)
          V4 (subspace_topology top1_S1 top1_S1_topology V4) (inv_into V4 q)"
      proof -
        define qi4 where "qi4 = (\<lambda>(a::real, b::real). (sqrt ((1+a)/2), -sqrt ((1-a)/2)))"
        have hqi4_props: "\<And>w. w \<in> U_bot \<Longrightarrow> qi4 w \<in> V4 \<and> q (qi4 w) = w"
        proof -
          fix w assume hw: "w \<in> U_bot"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and hb: "b < 0" using hw unfolding U_bot_def top1_S1_def hab by auto
          have "b\<^sup>2 > 0" using hb by (simp add: power2_eq_square) (simp add: mult_neg_neg)
          hence ha2: "a\<^sup>2 < 1" using hS1w by linarith
          hence ha_bounds: "a < 1 \<and> -1 < a"
          proof -
            have "\<not> (a \<ge> 1)" proof assume "1 \<le> a"
              hence "1 \<le> a * a" using mult_mono[of 1 a 1 a] by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            moreover have "\<not> (a \<le> -1)" proof assume "a \<le> -1"
              hence "1 \<le> (-a)*(-a)" using mult_mono[of 1 "-a" 1 "-a"] by linarith
              hence "1 \<le> a*a" by simp
              thus False using ha2 by (simp add: power2_eq_square) qed
            ultimately show ?thesis by linarith
          qed
          define x where "x = sqrt ((1+a)/2)" define y where "y = -sqrt ((1-a)/2)"
          have hqi4_w: "qi4 w = (x, y)" unfolding qi4_def hab x_def y_def by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha_bounds by (simp add: real_sqrt_mult_self)
          have hx_pos: "x > 0" unfolding x_def using ha_bounds by simp
          have hy_neg: "y < 0" unfolding y_def using ha_bounds by simp
          have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx2 hy2 by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a" using hx2 hy2 by simp
          have "2*x\<^sup>2 = 1+a" using hx2 by auto
          have "2*y\<^sup>2 = 1-a" using hy2 by auto
          have "(2*x*y)\<^sup>2 = (2*x\<^sup>2)*(2*y\<^sup>2)" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)*(1-a)" using \<open>2*x\<^sup>2=1+a\<close> \<open>2*y\<^sup>2=1-a\<close> by simp
          also have "\<dots> = 1-a\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2" using hS1w by linarith
          finally have h2xy_eq_b2: "(2*x*y)\<^sup>2 = b\<^sup>2" .
          have hqb: "2*x*y = b"
          proof -
            have "2*x*y = b \<or> 2*x*y = -b" using h2xy_eq_b2 power2_eq_iff by (by100 blast)
            moreover have "2*x*y \<le> 0" using hx_pos hy_neg by (simp add: mult_nonneg_nonpos)
            ultimately show ?thesis using hb by linarith
          qed
          have "qi4 w \<in> V4" unfolding hqi4_w V4_def top1_S1_def using hxy_S1 hx_pos hy_neg by simp
          moreover have "q (qi4 w) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi4_w hab by simp
          qed
          ultimately show "qi4 w \<in> V4 \<and> q (qi4 w) = w" by (by100 blast)
        qed
        have hqi4_eq: "\<And>w. w \<in> U_bot \<Longrightarrow> qi4 w = inv_into V4 q w"
        proof -
          fix w assume hw: "w \<in> U_bot"
          have "qi4 w \<in> V4" and "q (qi4 w) = w" using hqi4_props[OF hw] by auto
          thus "qi4 w = inv_into V4 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF hbij4]]])
        qed
        have hqi4_V4: "\<And>w. w \<in> U_bot \<Longrightarrow> qi4 w \<in> V4" using hqi4_props by (by100 blast)
        have hqi4_cont: "continuous_on U_bot qi4"
          unfolding qi4_def split_def by (intro continuous_intros) auto
        have hU_sub: "U_bot \<subseteq> top1_S1" unfolding U_bot_def by (by100 blast)
        have hV4_sub: "V4 \<subseteq> top1_S1" unfolding V4_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_bot"
          show "inv_into V4 q w \<in> V4" using hqi4_eq[OF \<open>w \<in> U_bot\<close>] hqi4_V4[OF \<open>w \<in> U_bot\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V4"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V4 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V4 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_bot. inv_into V4 q w \<in> V} = {w \<in> U_bot. qi4 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_bot"
            have "inv_into V4 q w = qi4 w" using hqi4_eq[OF hw] by simp
            moreover have "qi4 w \<in> V4" using hqi4_V4[OF hw] .
            moreover have "V4 \<subseteq> top1_S1" using hV4_sub .
            ultimately show "(inv_into V4 q w \<in> V) = (qi4 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_bot. qi4 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_bot"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_bot = qi4 -` W'' \<inter> U_bot"
              using hqi4_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_bot. qi4 w \<in> W''} = U \<inter> U_bot" using hUeq by (by100 blast)
            moreover have "U \<inter> U_bot \<in> subspace_topology top1_S1 top1_S1_topology U_bot"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_bot = U_bot \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_bot. inv_into V4 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_bot" by simp
        qed
      qed
    qed
    show ?thesis unfolding top1_evenly_covered_on_def
    proof (intro conjI exI[of _ "{V3, V4}"])
      show "openin_on top1_S1 top1_S1_topology U_bot" by (rule hU_bot_open)
      show "\<forall>V\<in>{V3, V4}. openin_on top1_S1 top1_S1_topology V" using hV3_open hV4_open by (by100 blast)
      show "\<forall>V\<in>{V3, V4}. \<forall>V'\<in>{V3, V4}. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}" using hV_disj by (by100 blast)
      show "{x \<in> top1_S1. q x \<in> U_bot} = \<Union> {V3, V4}" using hpreimage by simp
      show "\<forall>V\<in>{V3, V4}. top1_homeomorphism_on V (subspace_topology top1_S1 top1_S1_topology V)
          U_bot (subspace_topology top1_S1 top1_S1_topology U_bot) q"
        using hhomeo3 hhomeo4 by (by100 blast)
    qed
  qed
  have hevenly_right: "top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U_right"
  proof -
    have hU_right_open: "openin_on top1_S1 top1_S1_topology U_right"
    proof -
      have "open {p :: real \<times> real. fst p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      hence "{p :: real \<times> real. fst p > 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p > 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p > 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p > 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "U_right = top1_S1 \<inter> {p. fst p > 0}" unfolding U_right_def by (by100 blast)
      moreover have "U_right \<subseteq> top1_S1" unfolding U_right_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    \<comment> \<open>V5 = {x+y>0, x-y>0} \<inter> S^1 (arc near (1,0)), V6 = {x+y<0, x-y<0} \<inter> S^1 (arc near (-1,0)).\<close>
    define V5 where "V5 = {p \<in> top1_S1. fst p + snd p > 0 \<and> fst p - snd p > 0}"
    define V6 where "V6 = {p \<in> top1_S1. fst p + snd p < 0 \<and> fst p - snd p < 0}"
    have hV5_open: "openin_on top1_S1 top1_S1_topology V5"
    proof -
      have h1: "open {p :: real \<times> real. fst p + snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. fst p - snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p > 0}"
        using open_Int[OF h1 h2] by (auto simp: Int_def)
      hence "{p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p > 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p > 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p > 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p + snd p > 0 \<and> fst p - snd p > 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V5 = top1_S1 \<inter> {p. fst p + snd p > 0 \<and> fst p - snd p > 0}" unfolding V5_def by (by100 blast)
      moreover have "V5 \<subseteq> top1_S1" unfolding V5_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV6_open: "openin_on top1_S1 top1_S1_topology V6"
    proof -
      have h1: "open {p :: real \<times> real. fst p + snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. fst p - snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p < 0}"
        using open_Int[OF h1 h2] by (auto simp: Int_def)
      hence "{p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p < 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p < 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p < 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p + snd p < 0 \<and> fst p - snd p < 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V6 = top1_S1 \<inter> {p. fst p + snd p < 0 \<and> fst p - snd p < 0}" unfolding V6_def by (by100 blast)
      moreover have "V6 \<subseteq> top1_S1" unfolding V6_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV_disj: "V5 \<inter> V6 = {}" unfolding V5_def V6_def by auto
    have hpreimage: "{p \<in> top1_S1. q p \<in> U_right} = V5 \<union> V6"
    proof (intro set_eqI iffI)
      fix p assume hp: "p \<in> {p \<in> top1_S1. q p \<in> U_right}"
      hence hpS1: "p \<in> top1_S1" and hqp: "q p \<in> U_right" by auto
      obtain x y where hxy: "p = (x, y)" by (cases p) auto
      have hS1: "x\<^sup>2 + y\<^sup>2 = 1" using hpS1 unfolding top1_S1_def hxy by simp
      have "fst (q p) > 0" using hqp unfolding U_right_def by (by100 blast)
      hence "x\<^sup>2 - y\<^sup>2 > 0" unfolding q_def hxy by (simp add: power2_eq_square)
      \<comment> \<open>x^2-y^2 = (x+y)(x-y) > 0 iff both same sign.\<close>
      hence "(x+y)*(x-y) > 0" by (simp add: power2_eq_square algebra_simps)
      hence "(x+y > 0 \<and> x-y > 0) \<or> (x+y < 0 \<and> x-y < 0)" using zero_less_mult_iff by force
      thus "p \<in> V5 \<union> V6" unfolding V5_def V6_def using hpS1 hxy by auto
    next
      fix p assume "p \<in> V5 \<union> V6"
      hence hpS1: "p \<in> top1_S1" and hq: "(fst p + snd p) * (fst p - snd p) > 0"
        unfolding V5_def V6_def by (auto intro: mult_pos_pos mult_neg_neg)
      have "fst (q p) = fst p ^ 2 - snd p ^ 2" unfolding q_def by simp
      also have "\<dots> = (fst p + snd p) * (fst p - snd p)" by (simp add: power2_eq_square algebra_simps)
      finally have "fst (q p) > 0" using hq by simp
      moreover have "q p \<in> top1_S1" by (rule hq_S1[OF hpS1])
      ultimately show "p \<in> {p \<in> top1_S1. q p \<in> U_right}" unfolding U_right_def using hpS1 by auto
    qed
    \<comment> \<open>Homeomorphisms V5 \<rightarrow> U_right and V6 \<rightarrow> U_right.\<close>
    \<comment> \<open>Homeomorphisms: same pattern as previous cases. Inverse for V5: (a,b) \<mapsto> (sqrt((1+a)/2), b/(2*sqrt((1+a)/2))).
       For V6: negate both components.\<close>
    have hhomeo5: "top1_homeomorphism_on V5 (subspace_topology top1_S1 top1_S1_topology V5)
        U_right (subspace_topology top1_S1 top1_S1_topology U_right) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1r: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V5 (subspace_topology top1_S1 top1_S1_topology V5)"
        by (rule subspace_topology_is_topology_on[OF hTS1r]) (use V5_def in blast)
      show "is_topology_on U_right (subspace_topology top1_S1 top1_S1_topology U_right)"
        by (rule subspace_topology_is_topology_on[OF hTS1r]) (use U_right_def in blast)
      show hbij5: "bij_betw q V5 U_right"
      proof (rule bij_betw_imageI)
        show "inj_on q V5"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V5" and hp2: "p2 \<in> V5" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1 + y1 > 0" "x1 - y1 > 0" "x1\<^sup>2 + y1\<^sup>2 = 1"
            using hp1 unfolding V5_def top1_S1_def h1 by auto
          have hx2: "x2 + y2 > 0" "x2 - y2 > 0" "x2\<^sup>2 + y2\<^sup>2 = 1"
            using hp2 unfolding V5_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2" using heq unfolding q_def h1 h2 by auto
          have "x1\<^sup>2 = x2\<^sup>2"
          proof -
            have "x1\<^sup>2 = (1 + (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
            also have "\<dots> = (1 + (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
            also have "\<dots> = x2\<^sup>2" using hx2(3) by (simp add: field_simps)
            finally show ?thesis .
          qed
          moreover have "2*x1*y1 = 2*x2*y2" using heq unfolding q_def h1 h2 by auto
          hence "x1*y1 = x2*y2" by simp
          \<comment> \<open>x1^2 = x2^2 and x1 > 0 (since x1+y1>0 and x1-y1>0 imply x1>0).\<close>
          moreover have "x1 > 0" using hx1(1) hx1(2) by linarith
          moreover have "x2 > 0" using hx2(1) hx2(2) by linarith
          ultimately have "x1 = x2" by (simp add: power2_eq_iff_nonneg)
          moreover have "y1 = y2"
          proof -
            have "y1\<^sup>2 = y2\<^sup>2" using \<open>x1\<^sup>2 = x2\<^sup>2\<close> hx1(3) hx2(3) by linarith
            moreover have "x1*y1 = x1*y2" using \<open>x1*y1 = x2*y2\<close> \<open>x1 = x2\<close> by simp
            hence "y1 = y2" using \<open>x1 > 0\<close> by simp
            thus ?thesis .
          qed
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V5 = U_right"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V5"
          then obtain p where hp: "p \<in> V5" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" using hp unfolding V5_def by auto
          obtain x y where hxy: "p = (x, y)" by (cases p) auto
          have "x + y > 0" "x - y > 0" using hp unfolding V5_def hxy by auto
          hence "(x+y)*(x-y) > 0" by (simp add: mult_pos_pos)
          hence "x\<^sup>2 - y\<^sup>2 > 0" by (simp add: power2_eq_square algebra_simps)
          hence "fst (q p) > 0" unfolding q_def hxy by (simp add: power2_eq_square)
          moreover have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          ultimately show "w \<in> U_right" unfolding U_right_def using hw by simp
        next
          fix w assume hw: "w \<in> U_right"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a > 0" using hw unfolding U_right_def top1_S1_def hab by auto
          define x where "x = sqrt ((1+a)/2)" define y where "y = b / (2 * sqrt ((1+a)/2))"
          have hx_pos: "x > 0" unfolding x_def using ha by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          \<comment> \<open>y = b/(2x). Then 2xy = b. And x^2+y^2 = (1+a)/2 + b^2/(4*(1+a)/2) = (1+a)/2 + b^2/(2(1+a)).\<close>
          have hx_eq: "2*x = 2*sqrt((1+a)/2)" unfolding x_def by simp
          have h2x_pos: "2*x > 0" using hx_pos by simp
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1+a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1+a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding y_def x_def by simp
          qed
          \<comment> \<open>x^2+y^2=1: from (2xy)^2=b^2 and x^2=(1+a)/2.\<close>
          have "4*x\<^sup>2*(x\<^sup>2 + y\<^sup>2) = 4*x\<^sup>2*x\<^sup>2 + (2*x*y)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (2*x\<^sup>2)\<^sup>2 + b\<^sup>2" using hqb by (simp add: power2_eq_square algebra_simps)
          also have "2*x\<^sup>2 = 1+a" using hx2 by auto
          also have "(1+a)\<^sup>2 + b\<^sup>2 = 1 + 2*a + a\<^sup>2 + b\<^sup>2" by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 2 + 2*a" using hS1w by linarith
          also have "\<dots> = 2*(1+a)" by simp
          also have "\<dots> = 4*x\<^sup>2" using hx2 by auto
          finally have "4*x\<^sup>2*(x\<^sup>2+y\<^sup>2) = 4*x\<^sup>2" .
          hence hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx_pos by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            hence "x\<^sup>2 - y\<^sup>2 = 2*x\<^sup>2 - 1" using hxy_S1 by linarith
            also have "\<dots> = a" using \<open>2*x\<^sup>2 = 1+a\<close> by linarith
            finally show ?thesis .
          qed
          \<comment> \<open>(x,y) \<in> V5: need x+y > 0 and x-y > 0.\<close>
          have "x + y > 0 \<and> x - y > 0"
          proof -
            have "(x+y)*(x-y) = x\<^sup>2 - y\<^sup>2" by (simp add: power2_eq_square algebra_simps)
            hence "(x+y)*(x-y) = a" using hqa by simp
            hence "(x+y)*(x-y) > 0" using ha by simp
            hence "(x+y > 0 \<and> x-y > 0) \<or> (x+y < 0 \<and> x-y < 0)"
              using zero_less_mult_iff by force
            moreover have "x + y > 0 \<or> x - y > 0" using hx_pos by linarith
            ultimately show ?thesis by linarith
          qed
          hence "(x, y) \<in> V5" unfolding V5_def top1_S1_def using hxy_S1 by simp
          moreover have "q (x, y) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hab by simp
          qed
          ultimately show "w \<in> q ` V5" by (by100 blast)
        qed
      qed
      \<comment> \<open>Forward and inverse continuity: same pattern as previous cases.\<close>
      show "top1_continuous_map_on V5 (subspace_topology top1_S1 top1_S1_topology V5)
          U_right (subspace_topology top1_S1 top1_S1_topology U_right) q"
      proof -
        have hV5_sub: "V5 \<subseteq> top1_S1" unfolding V5_def by (by100 blast)
        have hU_sub: "U_right \<subseteq> top1_S1" unfolding U_right_def by (by100 blast)
        have hq_V5: "top1_continuous_map_on V5 (subspace_topology top1_S1 top1_S1_topology V5)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV5_sub])
        have hq_img: "q ` V5 \<subseteq> U_right" using hbij5 unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V5" thus "q p \<in> U_right" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_right"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_right \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V5. q p \<in> V} = {p \<in> V5. q p \<in> W}" using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V5. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V5"
            using hq_V5 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V5. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V5" by simp
        qed
      qed
      show "top1_continuous_map_on U_right (subspace_topology top1_S1 top1_S1_topology U_right)
          V5 (subspace_topology top1_S1 top1_S1_topology V5) (inv_into V5 q)"
      proof -
        define qi5 where "qi5 = (\<lambda>(a::real, b::real). (sqrt ((1+a)/2), b / (2 * sqrt ((1+a)/2))))"
        have hqi5_props: "\<And>w. w \<in> U_right \<Longrightarrow> qi5 w \<in> V5 \<and> q (qi5 w) = w"
        proof -
          fix w assume hw: "w \<in> U_right"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a > 0" using hw unfolding U_right_def top1_S1_def hab by auto
          define x where "x = sqrt ((1+a)/2)" define y where "y = b / (2 * sqrt ((1+a)/2))"
          have hqi5_w: "qi5 w = (x, y)" unfolding qi5_def hab x_def y_def by simp
          have hx_pos: "x > 0" unfolding x_def using ha by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1+a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1+a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding y_def x_def by simp
          qed
          have "4*x\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x\<^sup>2)\<^sup>2 + (2*x*y)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)\<^sup>2 + b\<^sup>2"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 + 2*a"
            using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*x\<^sup>2"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx_pos by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y > 0 \<and> x - y > 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps) (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) > 0" using ha by simp
            hence "(x+y > 0 \<and> x-y > 0) \<or> (x+y < 0 \<and> x-y < 0)"
              using zero_less_mult_iff by force
            moreover have "x + y > 0 \<or> x - y > 0" using hx_pos by linarith
            ultimately show ?thesis by linarith
          qed
          have "qi5 w \<in> V5" unfolding hqi5_w V5_def top1_S1_def using hxy_S1 \<open>x+y>0 \<and> x-y>0\<close> by simp
          moreover have "q (qi5 w) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi5_w hab by simp
          qed
          ultimately show "qi5 w \<in> V5 \<and> q (qi5 w) = w" by (by100 blast)
        qed
        have hqi5_eq: "\<And>w. w \<in> U_right \<Longrightarrow> qi5 w = inv_into V5 q w"
        proof -
          fix w assume hw: "w \<in> U_right"
          have "qi5 w \<in> V5" and "q (qi5 w) = w" using hqi5_props[OF hw] by auto
          thus "qi5 w = inv_into V5 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF hbij5]]])
        qed
        have hqi5_V5: "\<And>w. w \<in> U_right \<Longrightarrow> qi5 w \<in> V5" using hqi5_props by (by100 blast)
        have hqi5_cont: "continuous_on U_right qi5"
          unfolding qi5_def split_def
          by (intro continuous_intros continuous_on_divide)
             (auto simp: U_right_def top1_S1_def)
        have hU_sub: "U_right \<subseteq> top1_S1" unfolding U_right_def by (by100 blast)
        have hV5_sub: "V5 \<subseteq> top1_S1" unfolding V5_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_right"
          show "inv_into V5 q w \<in> V5" using hqi5_eq[OF \<open>w \<in> U_right\<close>] hqi5_V5[OF \<open>w \<in> U_right\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V5"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V5 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V5 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_right. inv_into V5 q w \<in> V} = {w \<in> U_right. qi5 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_right"
            have "inv_into V5 q w = qi5 w" using hqi5_eq[OF hw] by simp
            moreover have "qi5 w \<in> V5" using hqi5_V5[OF hw] .
            moreover have "V5 \<subseteq> top1_S1" using hV5_sub .
            ultimately show "(inv_into V5 q w \<in> V) = (qi5 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_right. qi5 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_right"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_right = qi5 -` W'' \<inter> U_right"
              using hqi5_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_right. qi5 w \<in> W''} = U \<inter> U_right" using hUeq by (by100 blast)
            moreover have "U \<inter> U_right \<in> subspace_topology top1_S1 top1_S1_topology U_right"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_right = U_right \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_right. inv_into V5 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_right" by simp
        qed
      qed
    qed
    have hhomeo6: "top1_homeomorphism_on V6 (subspace_topology top1_S1 top1_S1_topology V6)
        U_right (subspace_topology top1_S1 top1_S1_topology U_right) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1rr: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V6 (subspace_topology top1_S1 top1_S1_topology V6)"
        by (rule subspace_topology_is_topology_on[OF hTS1rr]) (use V6_def in blast)
      show "is_topology_on U_right (subspace_topology top1_S1 top1_S1_topology U_right)"
        by (rule subspace_topology_is_topology_on[OF hTS1rr]) (use U_right_def in blast)
      show hbij6: "bij_betw q V6 U_right"
      proof (rule bij_betw_imageI)
        show "inj_on q V6"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V6" and hp2: "p2 \<in> V6" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1 + y1 < 0" "x1 - y1 < 0" "x1\<^sup>2 + y1\<^sup>2 = 1" using hp1 unfolding V6_def top1_S1_def h1 by auto
          have hx2: "x2 + y2 < 0" "x2 - y2 < 0" "x2\<^sup>2 + y2\<^sup>2 = 1" using hp2 unfolding V6_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2" using heq unfolding q_def h1 h2 by auto
          have "x1\<^sup>2 = x2\<^sup>2"
          proof -
            have "x1\<^sup>2 = (1 + (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
            also have "\<dots> = (1 + (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
            also have "\<dots> = x2\<^sup>2" using hx2(3) by (simp add: field_simps)
            finally show ?thesis .
          qed
          have "2*x1*y1 = 2*x2*y2" using heq unfolding q_def h1 h2 by auto
          hence "x1*y1 = x2*y2" by simp
          have "x1 < 0" using hx1(1) hx1(2) by linarith
          have "x2 < 0" using hx2(1) hx2(2) by linarith
          hence "x1 = x2 \<or> x1 = -x2" using \<open>x1\<^sup>2 = x2\<^sup>2\<close> power2_eq_iff by (by100 blast)
          hence "x1 = x2" using \<open>x1 < 0\<close> \<open>x2 < 0\<close> by linarith
          moreover have "y1 = y2" using \<open>x1*y1 = x2*y2\<close> \<open>x1 = x2\<close> \<open>x1 < 0\<close> by simp
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V6 = U_right"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V6"
          then obtain p where hp: "p \<in> V6" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" using hp unfolding V6_def by auto
          obtain x y where hxy: "p = (x, y)" by (cases p) auto
          have "x + y < 0" "x - y < 0" using hp unfolding V6_def hxy by auto
          hence "(x+y)*(x-y) > 0" by (simp add: mult_neg_neg)
          hence "x\<^sup>2 - y\<^sup>2 > 0" by (simp add: power2_eq_square algebra_simps)
          hence "fst (q p) > 0" unfolding q_def hxy by (simp add: power2_eq_square)
          moreover have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          ultimately show "w \<in> U_right" unfolding U_right_def using hw by simp
        next
          fix w assume hw: "w \<in> U_right"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a > 0" using hw unfolding U_right_def top1_S1_def hab by auto
          define x where "x = -sqrt ((1+a)/2)" define y where "y = -b / (2 * sqrt ((1+a)/2))"
          have hx_neg: "x < 0" unfolding x_def using ha by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1+a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1+a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding y_def x_def by (simp add: field_simps)
          qed
          have "4*x\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x\<^sup>2)\<^sup>2 + (2*x*y)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)\<^sup>2 + b\<^sup>2"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 + 2*a" using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*x\<^sup>2"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx_neg by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y < 0 \<and> x - y < 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps) (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) > 0" using ha by simp
            hence "(x+y > 0 \<and> x-y > 0) \<or> (x+y < 0 \<and> x-y < 0)" using zero_less_mult_iff by force
            moreover have "x + y < 0 \<or> x - y < 0" using hx_neg by linarith
            ultimately show ?thesis by linarith
          qed
          have "(x, y) \<in> V6" unfolding V6_def top1_S1_def using hxy_S1 \<open>x+y<0 \<and> x-y<0\<close> by simp
          moreover have "q (x, y) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hab by simp
          qed
          ultimately show "w \<in> q ` V6" by (by100 blast)
        qed
      qed
      show "top1_continuous_map_on V6 (subspace_topology top1_S1 top1_S1_topology V6)
          U_right (subspace_topology top1_S1 top1_S1_topology U_right) q"
      proof -
        have hV6_sub: "V6 \<subseteq> top1_S1" unfolding V6_def by (by100 blast)
        have hU_sub: "U_right \<subseteq> top1_S1" unfolding U_right_def by (by100 blast)
        have hq_V6: "top1_continuous_map_on V6 (subspace_topology top1_S1 top1_S1_topology V6)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV6_sub])
        have hq_img: "q ` V6 \<subseteq> U_right" using hbij6 unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V6" thus "q p \<in> U_right" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_right"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_right \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V6. q p \<in> V} = {p \<in> V6. q p \<in> W}" using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V6. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V6"
            using hq_V6 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V6. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V6" by simp
        qed
      qed
      show "top1_continuous_map_on U_right (subspace_topology top1_S1 top1_S1_topology U_right)
          V6 (subspace_topology top1_S1 top1_S1_topology V6) (inv_into V6 q)"
      proof -
        define qi6 where "qi6 = (\<lambda>(a::real, b::real). (-sqrt ((1+a)/2), -b / (2 * sqrt ((1+a)/2))))"
        have hqi6_props: "\<And>w. w \<in> U_right \<Longrightarrow> qi6 w \<in> V6 \<and> q (qi6 w) = w"
        proof -
          fix w assume hw: "w \<in> U_right"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a > 0" using hw unfolding U_right_def top1_S1_def hab by auto
          define x where "x = -sqrt ((1+a)/2)" define y where "y = -b / (2 * sqrt ((1+a)/2))"
          have hqi6_w: "qi6 w = (x, y)" unfolding qi6_def hab x_def y_def by simp
          have hx_neg: "x < 0" unfolding x_def using ha by simp
          have hx2: "x\<^sup>2 = (1+a)/2" unfolding x_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1+a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1+a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding y_def x_def by (simp add: field_simps)
          qed
          have "4*x\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x\<^sup>2)\<^sup>2 + (2*x*y)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = (1+a)\<^sup>2 + b\<^sup>2"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 + 2*a" using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*x\<^sup>2"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hx_neg by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*x\<^sup>2 = 1+a" using hx2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y < 0 \<and> x - y < 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps)
              (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) > 0" using ha by simp
            hence "(x+y > 0 \<and> x-y > 0) \<or> (x+y < 0 \<and> x-y < 0)" using zero_less_mult_iff by force
            moreover have "x + y < 0 \<or> x - y < 0" using hx_neg by linarith
            ultimately show ?thesis by linarith
          qed
          have "qi6 w \<in> V6" unfolding hqi6_w V6_def top1_S1_def using hxy_S1 \<open>x+y<0 \<and> x-y<0\<close> by simp
          moreover have "q (qi6 w) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi6_w hab by simp
          qed
          ultimately show "qi6 w \<in> V6 \<and> q (qi6 w) = w" by (by100 blast)
        qed
        have hqi6_eq: "\<And>w. w \<in> U_right \<Longrightarrow> qi6 w = inv_into V6 q w"
        proof -
          fix w assume hw: "w \<in> U_right"
          have "qi6 w \<in> V6" and "q (qi6 w) = w" using hqi6_props[OF hw] by auto
          thus "qi6 w = inv_into V6 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF hbij6]]])
        qed
        have hqi6_V6: "\<And>w. w \<in> U_right \<Longrightarrow> qi6 w \<in> V6" using hqi6_props by (by100 blast)
        have hqi6_cont: "continuous_on U_right qi6"
          unfolding qi6_def split_def
          by (intro continuous_intros continuous_on_divide)
             (auto simp: U_right_def top1_S1_def)
        have hU_sub: "U_right \<subseteq> top1_S1" unfolding U_right_def by (by100 blast)
        have hV6_sub: "V6 \<subseteq> top1_S1" unfolding V6_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_right"
          show "inv_into V6 q w \<in> V6" using hqi6_eq[OF \<open>w \<in> U_right\<close>] hqi6_V6[OF \<open>w \<in> U_right\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V6"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V6 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V6 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_right. inv_into V6 q w \<in> V} = {w \<in> U_right. qi6 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_right"
            have "inv_into V6 q w = qi6 w" using hqi6_eq[OF hw] by simp
            moreover have "qi6 w \<in> V6" using hqi6_V6[OF hw] .
            moreover have "V6 \<subseteq> top1_S1" using hV6_sub .
            ultimately show "(inv_into V6 q w \<in> V) = (qi6 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_right. qi6 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_right"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_right = qi6 -` W'' \<inter> U_right"
              using hqi6_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_right. qi6 w \<in> W''} = U \<inter> U_right" using hUeq by (by100 blast)
            moreover have "U \<inter> U_right \<in> subspace_topology top1_S1 top1_S1_topology U_right"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_right = U_right \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_right. inv_into V6 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_right" by simp
        qed
      qed
    qed
    show ?thesis unfolding top1_evenly_covered_on_def
    proof (intro conjI exI[of _ "{V5, V6}"])
      show "openin_on top1_S1 top1_S1_topology U_right" by (rule hU_right_open)
      show "\<forall>V\<in>{V5, V6}. openin_on top1_S1 top1_S1_topology V" using hV5_open hV6_open by (by100 blast)
      show "\<forall>V\<in>{V5, V6}. \<forall>V'\<in>{V5, V6}. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}" using hV_disj by (by100 blast)
      show "{x \<in> top1_S1. q x \<in> U_right} = \<Union> {V5, V6}" using hpreimage by simp
      show "\<forall>V\<in>{V5, V6}. top1_homeomorphism_on V (subspace_topology top1_S1 top1_S1_topology V)
          U_right (subspace_topology top1_S1 top1_S1_topology U_right) q"
        using hhomeo5 hhomeo6 by (by100 blast)
    qed
  qed
  have hevenly_left: "top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U_left"
  proof -
    have hU_left_open: "openin_on top1_S1 top1_S1_topology U_left"
    proof -
      have "open {p :: real \<times> real. fst p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      hence "{p :: real \<times> real. fst p < 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p < 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p < 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p < 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "U_left = top1_S1 \<inter> {p. fst p < 0}" unfolding U_left_def by (by100 blast)
      moreover have "U_left \<subseteq> top1_S1" unfolding U_left_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    define V7 where "V7 = {p \<in> top1_S1. fst p + snd p > 0 \<and> fst p - snd p < 0}"
    define V8 where "V8 = {p \<in> top1_S1. fst p + snd p < 0 \<and> fst p - snd p > 0}"
    have hV7_open: "openin_on top1_S1 top1_S1_topology V7"
    proof -
      have h1: "open {p :: real \<times> real. fst p + snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. fst p - snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p < 0}"
        using open_Int[OF h1 h2] by (auto simp: Int_def)
      hence "{p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p < 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p < 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p + snd p > 0 \<and> fst p - snd p < 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p + snd p > 0 \<and> fst p - snd p < 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V7 = top1_S1 \<inter> {p. fst p + snd p > 0 \<and> fst p - snd p < 0}" unfolding V7_def by (by100 blast)
      moreover have "V7 \<subseteq> top1_S1" unfolding V7_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV8_open: "openin_on top1_S1 top1_S1_topology V8"
    proof -
      have h1: "open {p :: real \<times> real. fst p + snd p < 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have h2: "open {p :: real \<times> real. fst p - snd p > 0}" by (intro open_Collect_less) (intro continuous_intros)+
      have "open {p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p > 0}"
        using open_Int[OF h1 h2] by (auto simp: Int_def)
      hence "{p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p > 0} \<in> product_topology_on top1_open_sets top1_open_sets"
      proof -
        have "{p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p > 0} \<in> top1_open_sets"
          using \<open>open {p :: real \<times> real. fst p + snd p < 0 \<and> fst p - snd p > 0}\<close> unfolding top1_open_sets_def by simp
        thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
      qed
      hence "top1_S1 \<inter> {p. fst p + snd p < 0 \<and> fst p - snd p > 0} \<in> top1_S1_topology"
        unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      moreover have "V8 = top1_S1 \<inter> {p. fst p + snd p < 0 \<and> fst p - snd p > 0}" unfolding V8_def by (by100 blast)
      moreover have "V8 \<subseteq> top1_S1" unfolding V8_def by (by100 blast)
      ultimately show ?thesis unfolding openin_on_def by simp
    qed
    have hV_disj: "V7 \<inter> V8 = {}" unfolding V7_def V8_def by auto
    have hpreimage: "{p \<in> top1_S1. q p \<in> U_left} = V7 \<union> V8"
    proof (intro set_eqI iffI)
      fix p assume hp: "p \<in> {p \<in> top1_S1. q p \<in> U_left}"
      hence hpS1: "p \<in> top1_S1" and hqp: "q p \<in> U_left" by auto
      obtain x y where hxy: "p = (x, y)" by (cases p) auto
      have "fst (q p) < 0" using hqp unfolding U_left_def by (by100 blast)
      hence "x\<^sup>2 - y\<^sup>2 < 0" unfolding q_def hxy by (simp add: power2_eq_square)
      hence "(x+y)*(x-y) < 0" by (simp add: power2_eq_square algebra_simps)
      hence "(x+y > 0 \<and> x-y < 0) \<or> (x+y < 0 \<and> x-y > 0)" using mult_less_0_iff by force
      thus "p \<in> V7 \<union> V8" unfolding V7_def V8_def using hpS1 hxy by auto
    next
      fix p assume "p \<in> V7 \<union> V8"
      hence hpS1: "p \<in> top1_S1" and hq: "(fst p + snd p) * (fst p - snd p) < 0"
        unfolding V7_def V8_def by (auto intro: mult_pos_neg mult_neg_pos)
      have "fst (q p) = fst p ^ 2 - snd p ^ 2" unfolding q_def by simp
      also have "\<dots> = (fst p + snd p) * (fst p - snd p)" by (simp add: power2_eq_square algebra_simps)
      finally have "fst (q p) < 0" using hq by simp
      moreover have "q p \<in> top1_S1" by (rule hq_S1[OF hpS1])
      ultimately show "p \<in> {p \<in> top1_S1. q p \<in> U_left}" unfolding U_left_def using hpS1 by auto
    qed
    \<comment> \<open>Homeomorphisms V7 \<rightarrow> U_left and V8 \<rightarrow> U_left. Same pattern.\<close>
    \<comment> \<open>hhomeo7/hhomeo8: same pattern as hhomeo5/hhomeo6 but using b/(2y) inverse.\<close>
    have hhomeo7: "top1_homeomorphism_on V7 (subspace_topology top1_S1 top1_S1_topology V7)
        U_left (subspace_topology top1_S1 top1_S1_topology U_left) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1l: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V7 (subspace_topology top1_S1 top1_S1_topology V7)"
        by (rule subspace_topology_is_topology_on[OF hTS1l]) (use V7_def in blast)
      show "is_topology_on U_left (subspace_topology top1_S1 top1_S1_topology U_left)"
        by (rule subspace_topology_is_topology_on[OF hTS1l]) (use U_left_def in blast)
      show hbij7: "bij_betw q V7 U_left"
      proof (rule bij_betw_imageI)
        show "inj_on q V7"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V7" and hp2: "p2 \<in> V7" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1+y1 > 0" "x1-y1 < 0" "x1\<^sup>2+y1\<^sup>2 = 1" using hp1 unfolding V7_def top1_S1_def h1 by auto
          have hx2: "x2+y2 > 0" "x2-y2 < 0" "x2\<^sup>2+y2\<^sup>2 = 1" using hp2 unfolding V7_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2" using heq unfolding q_def h1 h2 by auto
          have "y1\<^sup>2 = (1 - (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
          also have "\<dots> = (1 - (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
          also have "\<dots> = y2\<^sup>2" using hx2(3) by (simp add: field_simps)
          finally have "y1\<^sup>2 = y2\<^sup>2" .
          have "2*x1*y1 = 2*x2*y2" using heq unfolding q_def h1 h2 by auto
          hence "x1*y1 = x2*y2" by simp
          have "y1 > 0" using hx1(1) hx1(2) by linarith
          have "y2 > 0" using hx2(1) hx2(2) by linarith
          hence "y1 = y2" using \<open>y1\<^sup>2 = y2\<^sup>2\<close> \<open>y1 > 0\<close> by (simp add: power2_eq_iff_nonneg)
          moreover have "x1 = x2" using \<open>x1*y1 = x2*y2\<close> \<open>y1 = y2\<close> \<open>y1 > 0\<close> by simp
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V7 = U_left"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V7"
          then obtain p where hp: "p \<in> V7" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" using hp unfolding V7_def by auto
          obtain x y where hxy: "p = (x, y)" by (cases p) auto
          have "x + y > 0" "x - y < 0" using hp unfolding V7_def hxy by auto
          hence "(x+y)*(x-y) < 0" by (simp add: mult_pos_neg)
          hence "x\<^sup>2 - y\<^sup>2 < 0" by (simp add: power2_eq_square algebra_simps)
          hence "fst (q p) < 0" unfolding q_def hxy by (simp add: power2_eq_square)
          moreover have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          ultimately show "w \<in> U_left" unfolding U_left_def using hw by simp
        next
          fix w assume hw: "w \<in> U_left"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a < 0" using hw unfolding U_left_def top1_S1_def hab by auto
          define y where "y = sqrt ((1-a)/2)" define x where "x = b / (2 * sqrt ((1-a)/2))"
          have hy_pos: "y > 0" unfolding y_def using ha by simp
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1-a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1-a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding x_def y_def by simp
          qed
          have "4*y\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x*y)\<^sup>2 + (2*y\<^sup>2)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2 + (1-a)\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 - 2*a" using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*y\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hy_pos by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y > 0 \<and> x - y < 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps)
              (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) < 0" using ha by simp
            hence "(x+y > 0 \<and> x-y < 0) \<or> (x+y < 0 \<and> x-y > 0)" using mult_less_0_iff by force
            moreover have "x + y > 0 \<or> x - y < 0" using hy_pos by linarith
            ultimately show ?thesis by linarith
          qed
          have "(x, y) \<in> V7" unfolding V7_def top1_S1_def using hxy_S1 \<open>x+y>0 \<and> x-y<0\<close> by simp
          moreover have "q (x, y) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hab by simp
          qed
          ultimately show "w \<in> q ` V7" by (by100 blast)
        qed
      qed
      show "top1_continuous_map_on V7 (subspace_topology top1_S1 top1_S1_topology V7)
          U_left (subspace_topology top1_S1 top1_S1_topology U_left) q"
      proof -
        have hV7_sub: "V7 \<subseteq> top1_S1" unfolding V7_def by (by100 blast)
        have hU_sub: "U_left \<subseteq> top1_S1" unfolding U_left_def by (by100 blast)
        have hq_V7: "top1_continuous_map_on V7 (subspace_topology top1_S1 top1_S1_topology V7)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV7_sub])
        have hq_img: "q ` V7 \<subseteq> U_left" using hbij7 unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V7" thus "q p \<in> U_left" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_left"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_left \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V7. q p \<in> V} = {p \<in> V7. q p \<in> W}" using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V7. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V7"
            using hq_V7 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V7. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V7" by simp
        qed
      qed
      show "top1_continuous_map_on U_left (subspace_topology top1_S1 top1_S1_topology U_left)
          V7 (subspace_topology top1_S1 top1_S1_topology V7) (inv_into V7 q)"
      proof -
        define qi7 where "qi7 = (\<lambda>(a::real, b::real). (b / (2 * sqrt ((1-a)/2)), sqrt ((1-a)/2)))"
        have hqi7_props: "\<And>w. w \<in> U_left \<Longrightarrow> qi7 w \<in> V7 \<and> q (qi7 w) = w"
        proof -
          fix w assume hw: "w \<in> U_left"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a < 0" using hw unfolding U_left_def top1_S1_def hab by auto
          define y where "y = sqrt ((1-a)/2)" define x where "x = b / (2 * sqrt ((1-a)/2))"
          have hqi7_w: "qi7 w = (x, y)" unfolding qi7_def hab x_def y_def by simp
          have hy_pos: "y > 0" unfolding y_def using ha by simp
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1-a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1-a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding x_def y_def by simp
          qed
          have "4*y\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x*y)\<^sup>2 + (2*y\<^sup>2)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2 + (1-a)\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 - 2*a" using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*y\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hy_pos by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y > 0 \<and> x - y < 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps)
              (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) < 0" using ha by simp
            hence "(x+y > 0 \<and> x-y < 0) \<or> (x+y < 0 \<and> x-y > 0)" using mult_less_0_iff by force
            moreover have "x + y > 0 \<or> x - y < 0" using hy_pos by linarith
            ultimately show ?thesis by linarith
          qed
          have "qi7 w \<in> V7" unfolding hqi7_w V7_def top1_S1_def using hxy_S1 \<open>x+y>0 \<and> x-y<0\<close> by simp
          moreover have "q (qi7 w) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi7_w hab by simp
          qed
          ultimately show "qi7 w \<in> V7 \<and> q (qi7 w) = w" by (by100 blast)
        qed
        have hqi7_eq: "\<And>w. w \<in> U_left \<Longrightarrow> qi7 w = inv_into V7 q w"
        proof -
          fix w assume hw: "w \<in> U_left"
          have "qi7 w \<in> V7" and "q (qi7 w) = w" using hqi7_props[OF hw] by auto
          thus "qi7 w = inv_into V7 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF hbij7]]])
        qed
        have hqi7_V7: "\<And>w. w \<in> U_left \<Longrightarrow> qi7 w \<in> V7" using hqi7_props by (by100 blast)
        have hqi7_cont: "continuous_on U_left qi7"
          unfolding qi7_def split_def
          by (intro continuous_intros continuous_on_divide)
             (auto simp: U_left_def top1_S1_def)
        have hU_sub: "U_left \<subseteq> top1_S1" unfolding U_left_def by (by100 blast)
        have hV7_sub: "V7 \<subseteq> top1_S1" unfolding V7_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_left"
          show "inv_into V7 q w \<in> V7" using hqi7_eq[OF \<open>w \<in> U_left\<close>] hqi7_V7[OF \<open>w \<in> U_left\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V7"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V7 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V7 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_left. inv_into V7 q w \<in> V} = {w \<in> U_left. qi7 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_left"
            have "inv_into V7 q w = qi7 w" using hqi7_eq[OF hw] by simp
            moreover have "qi7 w \<in> V7" using hqi7_V7[OF hw] .
            moreover have "V7 \<subseteq> top1_S1" using hV7_sub .
            ultimately show "(inv_into V7 q w \<in> V) = (qi7 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_left. qi7 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_left"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_left = qi7 -` W'' \<inter> U_left"
              using hqi7_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_left. qi7 w \<in> W''} = U \<inter> U_left" using hUeq by (by100 blast)
            moreover have "U \<inter> U_left \<in> subspace_topology top1_S1 top1_S1_topology U_left"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_left = U_left \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_left. inv_into V7 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_left" by simp
        qed
      qed
    qed
    have hhomeo8: "top1_homeomorphism_on V8 (subspace_topology top1_S1 top1_S1_topology V8)
        U_left (subspace_topology top1_S1 top1_S1_topology U_left) q"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      have hTS1ll: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      show "is_topology_on V8 (subspace_topology top1_S1 top1_S1_topology V8)"
        by (rule subspace_topology_is_topology_on[OF hTS1ll]) (use V8_def in blast)
      show "is_topology_on U_left (subspace_topology top1_S1 top1_S1_topology U_left)"
        by (rule subspace_topology_is_topology_on[OF hTS1ll]) (use U_left_def in blast)
      show hbij8: "bij_betw q V8 U_left"
      proof (rule bij_betw_imageI)
        show "inj_on q V8"
        proof (rule inj_onI)
          fix p1 p2 assume hp1: "p1 \<in> V8" and hp2: "p2 \<in> V8" and heq: "q p1 = q p2"
          obtain x1 y1 where h1: "p1 = (x1, y1)" by (cases p1) auto
          obtain x2 y2 where h2: "p2 = (x2, y2)" by (cases p2) auto
          have hx1: "x1+y1 < 0" "x1-y1 > 0" "x1\<^sup>2+y1\<^sup>2 = 1" using hp1 unfolding V8_def top1_S1_def h1 by auto
          have hx2: "x2+y2 < 0" "x2-y2 > 0" "x2\<^sup>2+y2\<^sup>2 = 1" using hp2 unfolding V8_def top1_S1_def h2 by auto
          have "x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2" using heq unfolding q_def h1 h2 by auto
          have "y1\<^sup>2 = y2\<^sup>2"
          proof -
            have "y1\<^sup>2 = (1 - (x1\<^sup>2 - y1\<^sup>2))/2" using hx1(3) by (simp add: field_simps)
            also have "\<dots> = (1 - (x2\<^sup>2 - y2\<^sup>2))/2" using \<open>x1\<^sup>2 - y1\<^sup>2 = x2\<^sup>2 - y2\<^sup>2\<close> by simp
            also have "\<dots> = y2\<^sup>2" using hx2(3) by (simp add: field_simps)
            finally show ?thesis .
          qed
          have "2*x1*y1 = 2*x2*y2" using heq unfolding q_def h1 h2 by auto
          hence "x1*y1 = x2*y2" by simp
          have "y1 < 0" using hx1(1) hx1(2) by linarith
          have "y2 < 0" using hx2(1) hx2(2) by linarith
          hence "y1 = y2 \<or> y1 = -y2" using \<open>y1\<^sup>2 = y2\<^sup>2\<close> power2_eq_iff by (by100 blast)
          hence "y1 = y2" using \<open>y1 < 0\<close> \<open>y2 < 0\<close> by linarith
          moreover have "x1 = x2" using \<open>x1*y1 = x2*y2\<close> \<open>y1 = y2\<close> \<open>y1 < 0\<close> by simp
          ultimately show "p1 = p2" unfolding h1 h2 by simp
        qed
      next
        show "q ` V8 = U_left"
        proof (intro set_eqI iffI)
          fix w assume "w \<in> q ` V8"
          then obtain p where hp: "p \<in> V8" and hw: "w = q p" by (by100 blast)
          have "p \<in> top1_S1" using hp unfolding V8_def by auto
          obtain x y where hxy: "p = (x, y)" by (cases p) auto
          have "x + y < 0" "x - y > 0" using hp unfolding V8_def hxy by auto
          hence "(x+y)*(x-y) < 0" by (simp add: mult_neg_pos)
          hence "x\<^sup>2 - y\<^sup>2 < 0" by (simp add: power2_eq_square algebra_simps)
          hence "fst (q p) < 0" unfolding q_def hxy by (simp add: power2_eq_square)
          moreover have "q p \<in> top1_S1" by (rule hq_S1[OF \<open>p \<in> top1_S1\<close>])
          ultimately show "w \<in> U_left" unfolding U_left_def using hw by simp
        next
          fix w assume hw: "w \<in> U_left"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a < 0" using hw unfolding U_left_def top1_S1_def hab by auto
          define y where "y = -sqrt ((1-a)/2)" define x where "x = -b / (2 * sqrt ((1-a)/2))"
          have hy_neg: "y < 0" unfolding y_def using ha by simp
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1-a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1-a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding x_def y_def by (simp add: field_simps)
          qed
          have "4*y\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x*y)\<^sup>2 + (2*y\<^sup>2)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2 + (1-a)\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 - 2*a" using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*y\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hy_neg by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y < 0 \<and> x - y > 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps)
              (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) < 0" using ha by simp
            hence "(x+y > 0 \<and> x-y < 0) \<or> (x+y < 0 \<and> x-y > 0)" using mult_less_0_iff by force
            moreover have "x + y < 0 \<or> x - y > 0" using hy_neg by linarith
            ultimately show ?thesis by linarith
          qed
          have "(x, y) \<in> V8" unfolding V8_def top1_S1_def using hxy_S1 \<open>x+y<0 \<and> x-y>0\<close> by simp
          moreover have "q (x, y) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hab by simp
          qed
          ultimately show "w \<in> q ` V8" by (by100 blast)
        qed
      qed
      show "top1_continuous_map_on V8 (subspace_topology top1_S1 top1_S1_topology V8)
          U_left (subspace_topology top1_S1 top1_S1_topology U_left) q"
      proof -
        have hV8_sub: "V8 \<subseteq> top1_S1" unfolding V8_def by (by100 blast)
        have hU_sub: "U_left \<subseteq> top1_S1" unfolding U_left_def by (by100 blast)
        have hq_V8: "top1_continuous_map_on V8 (subspace_topology top1_S1 top1_S1_topology V8)
            top1_S1 top1_S1_topology q"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hq_cont hV8_sub])
        have hq_img: "q ` V8 \<subseteq> U_left" using hbij8 unfolding bij_betw_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> V8" thus "q p \<in> U_left" using hq_img by (by100 blast)
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology U_left"
          obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = U_left \<inter> W"
            using hV unfolding subspace_topology_def by (by100 blast)
          have "{p \<in> V8. q p \<in> V} = {p \<in> V8. q p \<in> W}" using hq_img hVeq by (by100 blast)
          moreover have "{p \<in> V8. q p \<in> W} \<in> subspace_topology top1_S1 top1_S1_topology V8"
            using hq_V8 hW unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "{p \<in> V8. q p \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology V8" by simp
        qed
      qed
      show "top1_continuous_map_on U_left (subspace_topology top1_S1 top1_S1_topology U_left)
          V8 (subspace_topology top1_S1 top1_S1_topology V8) (inv_into V8 q)"
      proof -
        define qi8 where "qi8 = (\<lambda>(a::real, b::real). (-b / (2 * sqrt ((1-a)/2)), -sqrt ((1-a)/2)))"
        have hqi8_props: "\<And>w. w \<in> U_left \<Longrightarrow> qi8 w \<in> V8 \<and> q (qi8 w) = w"
        proof -
          fix w assume hw: "w \<in> U_left"
          obtain a b where hab: "w = (a, b)" by (cases w) auto
          have hS1w: "a\<^sup>2 + b\<^sup>2 = 1" and ha: "a < 0" using hw unfolding U_left_def top1_S1_def hab by auto
          define y where "y = -sqrt ((1-a)/2)" define x where "x = -b / (2 * sqrt ((1-a)/2))"
          have hqi8_w: "qi8 w = (x, y)" unfolding qi8_def hab x_def y_def by simp
          have hy_neg: "y < 0" unfolding y_def using ha by simp
          have hy2: "y\<^sup>2 = (1-a)/2" unfolding y_def power2_eq_square using ha by (simp add: real_sqrt_mult_self)
          have hqb: "2*x*y = b"
          proof -
            have "sqrt ((1-a)/2) > 0" using ha by simp
            hence "2 * sqrt ((1-a)/2) \<noteq> 0" by simp
            thus ?thesis unfolding x_def y_def by (simp add: field_simps)
          qed
          have "4*y\<^sup>2*(x\<^sup>2 + y\<^sup>2) = (2*x*y)\<^sup>2 + (2*y\<^sup>2)\<^sup>2"
            by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = b\<^sup>2 + (1-a)\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hqb by simp
          qed
          also have "\<dots> = 2 - 2*a" using hS1w by (simp add: power2_eq_square algebra_simps)
          also have "\<dots> = 4*y\<^sup>2"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis by linarith
          qed
          finally have hxy_S1: "x\<^sup>2 + y\<^sup>2 = 1" using hy_neg by simp
          have hqa: "x\<^sup>2 - y\<^sup>2 = a"
          proof -
            have "2*y\<^sup>2 = 1-a" using hy2 by auto
            thus ?thesis using hxy_S1 by linarith
          qed
          have "x + y < 0 \<and> x - y > 0"
          proof -
            have "(x+y)*(x-y) = a" by (simp add: power2_eq_square algebra_simps)
              (use hqa in \<open>simp add: power2_eq_square algebra_simps\<close>)
            hence "(x+y)*(x-y) < 0" using ha by simp
            hence "(x+y > 0 \<and> x-y < 0) \<or> (x+y < 0 \<and> x-y > 0)" using mult_less_0_iff by force
            moreover have "x + y < 0 \<or> x - y > 0" using hy_neg by linarith
            ultimately show ?thesis by linarith
          qed
          have "qi8 w \<in> V8" unfolding hqi8_w V8_def top1_S1_def using hxy_S1 \<open>x+y<0 \<and> x-y>0\<close> by simp
          moreover have "q (qi8 w) = w"
          proof -
            have "fst (q (x, y)) = a" unfolding q_def using hqa by simp
            moreover have "snd (q (x, y)) = b" unfolding q_def using hqb by simp
            ultimately have "q (x, y) = (a, b)" by (simp add: prod_eq_iff)
            thus ?thesis using hqi8_w hab by simp
          qed
          ultimately show "qi8 w \<in> V8 \<and> q (qi8 w) = w" by (by100 blast)
        qed
        have hqi8_eq: "\<And>w. w \<in> U_left \<Longrightarrow> qi8 w = inv_into V8 q w"
        proof -
          fix w assume hw: "w \<in> U_left"
          have "qi8 w \<in> V8" and "q (qi8 w) = w" using hqi8_props[OF hw] by auto
          thus "qi8 w = inv_into V8 q w"
            by (simp add: inv_into_f_eq[OF inj_on_subset[OF bij_betw_imp_inj_on[OF hbij8]]])
        qed
        have hqi8_V8: "\<And>w. w \<in> U_left \<Longrightarrow> qi8 w \<in> V8" using hqi8_props by (by100 blast)
        have hqi8_cont: "continuous_on U_left qi8"
          unfolding qi8_def split_def
          by (intro continuous_intros continuous_on_divide)
             (auto simp: U_left_def top1_S1_def)
        have hU_sub: "U_left \<subseteq> top1_S1" unfolding U_left_def by (by100 blast)
        have hV8_sub: "V8 \<subseteq> top1_S1" unfolding V8_def by (by100 blast)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix w assume "w \<in> U_left"
          show "inv_into V8 q w \<in> V8" using hqi8_eq[OF \<open>w \<in> U_left\<close>] hqi8_V8[OF \<open>w \<in> U_left\<close>] by simp
        next
          fix V assume hV: "V \<in> subspace_topology top1_S1 top1_S1_topology V8"
          obtain W'' where hW'': "W'' \<in> product_topology_on top1_open_sets top1_open_sets"
              and hWeq: "V = V8 \<inter> (top1_S1 \<inter> W'')"
          proof -
            obtain W where hW: "W \<in> top1_S1_topology" and hVeq: "V = V8 \<inter> W"
              using hV unfolding subspace_topology_def by (by100 blast)
            obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
                and hWW': "W = top1_S1 \<inter> W'"
              using hW unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
            show ?thesis using that[OF hW'] hVeq hWW' by simp
          qed
          have hW''_open: "open W''"
            using hW'' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
          have "{w \<in> U_left. inv_into V8 q w \<in> V} = {w \<in> U_left. qi8 w \<in> W''}"
          proof (intro Collect_cong conj_cong refl)
            fix w assume hw: "w \<in> U_left"
            have "inv_into V8 q w = qi8 w" using hqi8_eq[OF hw] by simp
            moreover have "qi8 w \<in> V8" using hqi8_V8[OF hw] .
            moreover have "V8 \<subseteq> top1_S1" using hV8_sub .
            ultimately show "(inv_into V8 q w \<in> V) = (qi8 w \<in> W'')" using hWeq by auto
          qed
          moreover have "{w \<in> U_left. qi8 w \<in> W''} \<in> subspace_topology top1_S1 top1_S1_topology U_left"
          proof -
            obtain U where hU: "open U" and hUeq: "U \<inter> U_left = qi8 -` W'' \<inter> U_left"
              using hqi8_cont hW''_open unfolding continuous_on_open_invariant by blast
            have "{w \<in> U_left. qi8 w \<in> W''} = U \<inter> U_left" using hUeq by (by100 blast)
            moreover have "U \<inter> U_left \<in> subspace_topology top1_S1 top1_S1_topology U_left"
            proof -
              have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
              hence "U \<in> product_topology_on top1_open_sets top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              hence "top1_S1 \<inter> U \<in> top1_S1_topology"
                unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
              moreover have "U \<inter> U_left = U_left \<inter> (top1_S1 \<inter> U)" using hU_sub by blast
              ultimately show ?thesis unfolding subspace_topology_def by blast
            qed
            ultimately show ?thesis by simp
          qed
          ultimately show "{w \<in> U_left. inv_into V8 q w \<in> V}
              \<in> subspace_topology top1_S1 top1_S1_topology U_left" by simp
        qed
      qed
    qed
    show ?thesis unfolding top1_evenly_covered_on_def
    proof (intro conjI exI[of _ "{V7, V8}"])
      show "openin_on top1_S1 top1_S1_topology U_left" by (rule hU_left_open)
      show "\<forall>V\<in>{V7, V8}. openin_on top1_S1 top1_S1_topology V" using hV7_open hV8_open by (by100 blast)
      show "\<forall>V\<in>{V7, V8}. \<forall>V'\<in>{V7, V8}. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}" using hV_disj by (by100 blast)
      show "{x \<in> top1_S1. q x \<in> U_left} = \<Union> {V7, V8}" using hpreimage by simp
      show "\<forall>V\<in>{V7, V8}. top1_homeomorphism_on V (subspace_topology top1_S1 top1_S1_topology V)
          U_left (subspace_topology top1_S1 top1_S1_topology U_left) q"
        using hhomeo7 hhomeo8 by (by100 blast)
    qed
  qed
  have hq_evenly: "\<And>b. b \<in> top1_S1 \<Longrightarrow>
      \<exists>U. b \<in> U \<and> top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U"
  proof -
    fix b assume hb: "b \<in> top1_S1"
    from hcover[OF hb] show "\<exists>U. b \<in> U \<and> top1_evenly_covered_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q U"
      using hevenly_top hevenly_bot hevenly_right hevenly_left by (by100 blast)
  qed
  show ?thesis unfolding hq_alt[symmetric] top1_covering_map_on_def
    using hq_cont hq_surj hq_evenly by (by100 blast)
qed



lemma squaring_map_factorization:
  assumes hh: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h"
      and hanti: "top1_antipode_preserving_S1 h"
  obtains k where "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology k"
      and "\<forall>z\<in>top1_S1. k ((\<lambda>(x,y). (x^2-y^2, 2*x*y)) z) = (\<lambda>(x,y). (x^2-y^2, 2*x*y)) (h z)"
proof -
  define q :: "real \<times> real \<Rightarrow> real \<times> real" where
    "q p = (fst p ^ 2 - snd p ^ 2, 2 * fst p * snd p)" for p
  have hq_alt: "q = (\<lambda>(x, y). (x^2-y^2, 2*x*y))" unfolding q_def by (intro ext) auto
  \<comment> \<open>q(-z) = q(z) and h(-z) = -h(z) imply q(h(-z)) = q(h(z)).\<close>
  have hq_neg: "\<And>p. q (- fst p, - snd p) = q p"
    unfolding q_def by (simp add: power2_eq_square algebra_simps)
  have hanti': "\<And>x y. h (-x, -y) = (- fst (h (x, y)), - snd (h (x, y)))"
    using hanti unfolding top1_antipode_preserving_S1_def by (by100 blast)
  have hqh_fiber: "\<And>z. z \<in> top1_S1 \<Longrightarrow> q (h (- fst z, - snd z)) = q (h z)"
  proof -
    fix z assume "z \<in> top1_S1"
    obtain x y where hxy: "z = (x, y)" by (cases z) auto
    have "q (h (-x, -y)) = q (- fst (h (x, y)), - snd (h (x, y)))" using hanti' by simp
    also have "\<dots> = q (h (x, y))" using hq_neg[of "h (x, y)"] by simp
    finally show "q (h (- fst z, - snd z)) = q (h z)" using hxy by simp
  qed
  \<comment> \<open>q∘h is constant on fibers {z, -z}, so it factors through q.
     Define k(w) = q(h(z)) where z is any preimage of w under q.\<close>
  \<comment> \<open>Define k: for each w, pick z with q(z)=w (using surjectivity), set k(w) = q(h(z)).\<close>
  have hq_surj: "q ` top1_S1 = top1_S1"
    using squaring_map_covering unfolding top1_covering_map_on_def hq_alt[symmetric] by (by100 blast)
  define k where "k w = q (h (SOME z. z \<in> top1_S1 \<and> q z = w))" for w
  \<comment> \<open>Fibers of q on S^1: q(z')=q(z) iff z'=z or z'=-z.\<close>
  have hq_fiber: "\<And>z z'. z \<in> top1_S1 \<Longrightarrow> z' \<in> top1_S1 \<Longrightarrow> q z' = q z \<Longrightarrow>
      z' = z \<or> z' = (- fst z, - snd z)"
  proof -
    fix z z' assume hz: "z \<in> top1_S1" and hz': "z' \<in> top1_S1" and hqeq: "q z' = q z"
    obtain x y where hxy: "z = (x, y)" by (cases z) auto
    obtain x' y' where hxy': "z' = (x', y')" by (cases z') auto
    have hS1: "x\<^sup>2 + y\<^sup>2 = 1" using hz unfolding top1_S1_def hxy by simp
    have hS1': "x'\<^sup>2 + y'\<^sup>2 = 1" using hz' unfolding top1_S1_def hxy' by simp
    have heq1: "x'\<^sup>2 - y'\<^sup>2 = x\<^sup>2 - y\<^sup>2" using hqeq unfolding q_def hxy hxy' by auto
    have heq2: "x'*y' = x*y" using hqeq unfolding q_def hxy hxy' by auto
    \<comment> \<open>From S^1 equations: x'^2 = x^2 and y'^2 = y^2.\<close>
    have hx2: "x'\<^sup>2 = x\<^sup>2"
    proof -
      have "x'\<^sup>2 = (1 + (x'\<^sup>2 - y'\<^sup>2))/2" using hS1' by (simp add: field_simps)
      also have "\<dots> = (1 + (x\<^sup>2 - y\<^sup>2))/2" using heq1 by simp
      also have "\<dots> = x\<^sup>2" using hS1 by (simp add: field_simps)
      finally show ?thesis .
    qed
    have hy2: "y'\<^sup>2 = y\<^sup>2" using hx2 hS1 hS1' by linarith
    \<comment> \<open>x' = \<pm>x, y' = \<pm>y. Combined with x'y' = xy:\<close>
    have "x' = x \<or> x' = -x" using hx2 power2_eq_iff by (by100 blast)
    moreover have "y' = y \<or> y' = -y" using hy2 power2_eq_iff by (by100 blast)
    ultimately consider "x' = x \<and> y' = y" | "x' = -x \<and> y' = -y"
        | "x' = x \<and> y' = -y" | "x' = -x \<and> y' = y" by blast
    thus "z' = z \<or> z' = (- fst z, - snd z)"
    proof cases
      case 1 thus ?thesis using hxy hxy' by simp
    next
      case 2 thus ?thesis using hxy hxy' by simp
    next
      case 3 \<comment> \<open>x'=x, y'=-y. Then x'y' = -xy = xy, so 2xy=0, x=0 or y=0.\<close>
      hence "x*(-y) = x*y" using heq2 by simp
      hence "x*y = 0" by simp
      hence "x = 0 \<or> y = 0" by simp
      thus ?thesis
      proof
        assume "x = 0" thus ?thesis using 3 hxy hxy' by simp
      next
        assume "y = 0" thus ?thesis using 3 hxy hxy' by simp
      qed
    next
      case 4 \<comment> \<open>x'=-x, y'=y. Then x'y' = -xy = xy, so 2xy=0.\<close>
      hence "(-x)*y = x*y" using heq2 by simp
      hence "x*y = 0" by simp
      hence "x = 0 \<or> y = 0" by simp
      thus ?thesis
      proof
        assume "x = 0" thus ?thesis using 4 hxy hxy' by simp
      next
        assume "y = 0" thus ?thesis using 4 hxy hxy' by simp
      qed
    qed
  qed
  have hk_eq: "\<And>z. z \<in> top1_S1 \<Longrightarrow> k (q z) = q (h z)"
  proof -
    fix z assume hz: "z \<in> top1_S1"
    define z' where "z' = (SOME z'. z' \<in> top1_S1 \<and> q z' = q z)"
    have "z' \<in> top1_S1 \<and> q z' = q z"
      unfolding z'_def by (rule someI[of "\<lambda>z'. z' \<in> top1_S1 \<and> q z' = q z"]) (use hz in auto)
    hence hz'S1: "z' \<in> top1_S1" and hqz': "q z' = q z" by auto
    have "z' = z \<or> z' = (- fst z, - snd z)" by (rule hq_fiber[OF hz hz'S1 hqz'])
    hence "q (h z') = q (h z)"
    proof
      assume "z' = z" thus ?thesis by simp
    next
      assume "z' = (- fst z, - snd z)"
      thus ?thesis using hqh_fiber[OF hz] by simp
    qed
    thus "k (q z) = q (h z)" unfolding k_def z'_def by simp
  qed
  have hk_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology k"
  proof -
    \<comment> \<open>k is continuous because q is a quotient map and k∘q = q∘h is continuous.\<close>
    \<comment> \<open>First: q∘h is continuous S^1 \<rightarrow> S^1.\<close>
    have hq_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q"
      using squaring_map_covering unfolding top1_covering_map_on_def hq_alt[symmetric] by (by100 blast)
    have hqh_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (q \<circ> h)"
      by (rule top1_continuous_map_on_comp[OF hh hq_cont])
    \<comment> \<open>q is a quotient map (covering \<Rightarrow> open surjection \<Rightarrow> preimages of open=open characterize topology).\<close>
    \<comment> \<open>For V open in S^1: q^{-1}(k^{-1}(V)) = (q\<circ>h)^{-1}(V) is open (since q\<circ>h continuous).
       Since q is a quotient map, k^{-1}(V) is open.\<close>
    \<comment> \<open>Instead of proving q is a quotient map in general, we use Theorem_22_2 directly.\<close>
    have hg_const: "\<forall>z\<in>top1_S1. \<forall>z'\<in>top1_S1. q z = q z' \<longrightarrow> (q \<circ> h) z = (q \<circ> h) z'"
    proof (intro ballI impI)
      fix z z' assume hz: "z \<in> top1_S1" and hz': "z' \<in> top1_S1" and hqeq: "q z = q z'"
      have "z' = z \<or> z' = (- fst z, - snd z)" by (rule hq_fiber[OF hz hz' hqeq[symmetric]])
      thus "(q \<circ> h) z = (q \<circ> h) z'"
      proof
        assume "z' = z" thus ?thesis by simp
      next
        assume "z' = (- fst z, - snd z)"
        hence "(q \<circ> h) z' = q (h (- fst z, - snd z))" by simp
        also have "\<dots> = q (h z)" using hqh_fiber[OF hz] by simp
        finally show ?thesis by simp
      qed
    qed
    \<comment> \<open>q is a quotient map. Covering maps are quotient maps.\<close>
    have hq_quotient: "top1_quotient_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q"
    proof -
      have hTS1q: "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
                top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
      qed
      have hq_cover: "top1_covering_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology q"
        using squaring_map_covering unfolding hq_alt[symmetric] by simp
      \<comment> \<open>q is an open map: for U open in S^1, q(U) is open in S^1.
         This follows from q being a local homeomorphism (covering map).
         For each w \<in> q(U), pick evenly covered V \<ni> w. On the sheet containing the
         preimage point in U, q restricts to a homeomorphism, so q(sheet \<inter> U) is open.
         Hence q(U) is a union of opens = open.\<close>
      \<comment> \<open>Proving q is an open map is substantial. Instead, we prove the quotient
         condition directly: if q^{-1}(V) is open and V \<subseteq> S^1, then V is open.
         For each w \<in> V, pick evenly covered U \<ni> w. The preimage q^{-1}(U) = \<Union>V_i
         with q|V_i homeomorphisms. V_i \<inter> q^{-1}(V) is open in V_i (since q^{-1}(V) open).
         q(V_i \<inter> q^{-1}(V)) = U \<inter> V is open in S^1 (homeomorphism maps open to open).
         So w has open neighborhood U \<inter> V \<subseteq> V. Hence V is open.\<close>
      have hquot_cond: "\<forall>V. V \<subseteq> top1_S1 \<longrightarrow>
          ({z \<in> top1_S1. q z \<in> V} \<in> top1_S1_topology \<longrightarrow> V \<in> top1_S1_topology)"
      proof (intro allI impI)
        fix V assume hVsub: "V \<subseteq> top1_S1" and hpreopen: "{z \<in> top1_S1. q z \<in> V} \<in> top1_S1_topology"
        have "\<forall>w \<in> V. \<exists>U \<in> top1_S1_topology. w \<in> U \<and> U \<subseteq> V"
        proof
          fix w assume hw: "w \<in> V"
          hence hwS1: "w \<in> top1_S1" using hVsub by (by100 blast)
          obtain W where hwW: "w \<in> W" and hevenly: "top1_evenly_covered_on top1_S1 top1_S1_topology
              top1_S1 top1_S1_topology q W"
            using hq_cover hwS1 unfolding top1_covering_map_on_def by (by100 blast)
          obtain \<V> where hVi_open: "\<forall>Vi\<in>\<V>. openin_on top1_S1 top1_S1_topology Vi"
              and hVi_union: "{x \<in> top1_S1. q x \<in> W} = \<Union>\<V>"
              and hVi_homeo: "\<forall>Vi\<in>\<V>. top1_homeomorphism_on Vi (subspace_topology top1_S1 top1_S1_topology Vi)
                  W (subspace_topology top1_S1 top1_S1_topology W) q"
            using hevenly unfolding top1_evenly_covered_on_def by auto
          have "w \<in> q ` top1_S1" using hq_surj hwS1 by simp
          then obtain z where hz: "z \<in> top1_S1" and hqz: "q z = w" by (by100 auto)
          have "z \<in> \<Union>\<V>" using hVi_union hz hqz hwW by (by100 auto)
          then obtain Vj where hVjV: "Vj \<in> \<V>" and hzVj: "z \<in> Vj" by (by100 blast)
          have hVj_sub: "Vj \<subseteq> top1_S1" using hVi_open hVjV unfolding openin_on_def by (by100 blast)
          \<comment> \<open>q|Vj: Vj \<rightarrow> W is a homeomorphism.\<close>
          have hhomeo: "top1_homeomorphism_on Vj (subspace_topology top1_S1 top1_S1_topology Vj)
              W (subspace_topology top1_S1 top1_S1_topology W) q"
            using hVi_homeo hVjV by (by100 blast)
          \<comment> \<open>q|Vj is bijective, so q(Vj \<inter> q^{-1}(V)) = W \<inter> V.\<close>
          \<comment> \<open>Vj \<inter> q^{-1}(V) is open in Vj. q maps it to an open subset of W.\<close>
          \<comment> \<open>Open in W + W open in S^1 \<Rightarrow> open in S^1.\<close>
          \<comment> \<open>Vj \<inter> q^{-1}(V) is open in Vj (intersection of opens in S^1, intersect with Vj).\<close>
          have hVj_open: "openin_on top1_S1 top1_S1_topology Vj"
            using hVi_open hVjV by (by100 blast)
          have hW_open: "openin_on top1_S1 top1_S1_topology W"
            using hevenly unfolding top1_evenly_covered_on_def by (by100 blast)
          \<comment> \<open>W is open in S^1.\<close>
          have hW_in_T: "W \<in> top1_S1_topology"
            using hW_open unfolding openin_on_def by (by100 blast)
          \<comment> \<open>q^{-1}(V) \<inter> Vj is open in S^1.\<close>
          have hVj_in_T: "Vj \<in> top1_S1_topology"
            using hVj_open unfolding openin_on_def by (by100 blast)
          have hpre_Vj: "Vj \<inter> {z \<in> top1_S1. q z \<in> V} \<in> top1_S1_topology"
          proof -
            have hfin_inter: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> top1_S1_topology \<longrightarrow> \<Inter>F \<in> top1_S1_topology"
              using hTS1q unfolding is_topology_on_def by (by100 blast)
            have "{Vj, {z \<in> top1_S1. q z \<in> V}} \<subseteq> top1_S1_topology"
              using hVj_in_T hpreopen by (by100 auto)
            moreover have "finite {Vj, {z \<in> top1_S1. q z \<in> V}}" by simp
            moreover have "{Vj, {z \<in> top1_S1. q z \<in> V}} \<noteq> {}" by simp
            ultimately have "\<Inter>{Vj, {z \<in> top1_S1. q z \<in> V}} \<in> top1_S1_topology"
              using hfin_inter by (by100 blast)
            moreover have "\<Inter>{Vj, {z \<in> top1_S1. q z \<in> V}} = Vj \<inter> {z \<in> top1_S1. q z \<in> V}" by (by100 auto)
            ultimately show ?thesis by simp
          qed
          \<comment> \<open>This is open in subspace Vj: Vj \<inter> q^{-1}(V) = Vj \<inter> (Vj \<inter> q^{-1}(V)).\<close>
          have hpre_in_Vj: "Vj \<inter> {z \<in> top1_S1. q z \<in> V} \<in> subspace_topology top1_S1 top1_S1_topology Vj"
            unfolding subspace_topology_def using hpre_Vj by (by100 blast)
          \<comment> \<open>q|Vj is a homeomorphism, so it maps open subsets of Vj to open subsets of W.
             The inverse (inv_into Vj q) is continuous W \<rightarrow> Vj, so preimages of open-in-Vj are open-in-W.\<close>
          have hinv_cont: "top1_continuous_map_on W (subspace_topology top1_S1 top1_S1_topology W)
              Vj (subspace_topology top1_S1 top1_S1_topology Vj) (inv_into Vj q)"
            using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have himg_open_W: "{w' \<in> W. inv_into Vj q w' \<in> Vj \<inter> {z \<in> top1_S1. q z \<in> V}}
              \<in> subspace_topology top1_S1 top1_S1_topology W"
            using hinv_cont hpre_in_Vj unfolding top1_continuous_map_on_def by (by100 blast)
          \<comment> \<open>This set = W \<inter> V (since inv_into Vj q w' \<in> q^{-1}(V) iff w' \<in> V, using bijection).\<close>
          have hbij: "bij_betw q Vj W" using hhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hset_eq: "{w' \<in> W. inv_into Vj q w' \<in> Vj \<inter> {z \<in> top1_S1. q z \<in> V}} = W \<inter> V"
          proof (intro set_eqI iffI)
            fix w' assume hw': "w' \<in> {w' \<in> W. inv_into Vj q w' \<in> Vj \<inter> {z \<in> top1_S1. q z \<in> V}}"
            hence "w' \<in> W" and "inv_into Vj q w' \<in> Vj" and "q (inv_into Vj q w') \<in> V" by auto
            have "w' \<in> q ` Vj" using \<open>w' \<in> W\<close> hbij unfolding bij_betw_def by (by100 blast)
            hence "q (inv_into Vj q w') = w'" by (simp add: f_inv_into_f)
            thus "w' \<in> W \<inter> V" using \<open>w' \<in> W\<close> \<open>q (inv_into Vj q w') \<in> V\<close> by simp
          next
            fix w' assume hw': "w' \<in> W \<inter> V"
            hence "w' \<in> W" and "w' \<in> V" by auto
            have "w' \<in> q ` Vj" using \<open>w' \<in> W\<close> hbij unfolding bij_betw_def by (by100 blast)
            hence hinv_Vj: "inv_into Vj q w' \<in> Vj" by (rule inv_into_into)
            hence hinv_S1: "inv_into Vj q w' \<in> top1_S1" using hVj_sub by (by100 blast)
            have "q (inv_into Vj q w') = w'" using \<open>w' \<in> q ` Vj\<close> by (simp add: f_inv_into_f)
            hence "q (inv_into Vj q w') \<in> V" using \<open>w' \<in> V\<close> by simp
            thus "w' \<in> {w' \<in> W. inv_into Vj q w' \<in> Vj \<inter> {z \<in> top1_S1. q z \<in> V}}"
              using \<open>w' \<in> W\<close> hinv_Vj hinv_S1 by (by100 auto)
          qed
          \<comment> \<open>W \<inter> V is open in subspace W, and W is open in S^1, so W \<inter> V is open in S^1.\<close>
          have "W \<inter> V \<in> subspace_topology top1_S1 top1_S1_topology W"
            using himg_open_W hset_eq by simp
          then obtain W' where hW': "W' \<in> top1_S1_topology" and hWV_eq: "W \<inter> V = W \<inter> W'"
            unfolding subspace_topology_def by (by100 blast)
          have "W \<inter> V \<in> top1_S1_topology"
          proof -
            have hfin_inter2: "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> top1_S1_topology \<longrightarrow> \<Inter>F \<in> top1_S1_topology"
              using hTS1q unfolding is_topology_on_def by (by100 blast)
            have "{W, W'} \<subseteq> top1_S1_topology" using hW_in_T hW' by (by100 auto)
            moreover have "finite {W, W'}" by simp
            moreover have "{W, W'} \<noteq> ({}::(real\<times>real) set set)" by simp
            ultimately have "\<Inter>{W, W'} \<in> top1_S1_topology" using hfin_inter2 by (by100 blast)
            moreover have "\<Inter>{W, W'} = W \<inter> W'" by (by100 auto)
            ultimately show ?thesis using hWV_eq by simp
          qed
          moreover have "w \<in> W \<inter> V" using hwW hw by simp
          moreover have "W \<inter> V \<subseteq> V" by (by100 blast)
          ultimately show "\<exists>U \<in> top1_S1_topology. w \<in> U \<and> U \<subseteq> V"
            by (intro bexI[of _ "W \<inter> V"]) simp_all
        qed
        hence "V = \<Union>{U \<in> top1_S1_topology. U \<subseteq> V}" by (by100 blast)
        moreover have "\<Union>{U \<in> top1_S1_topology. U \<subseteq> V} \<in> top1_S1_topology"
          using hTS1q unfolding is_topology_on_def by (by100 auto)
        ultimately show "V \<in> top1_S1_topology" by simp
      qed
      show ?thesis unfolding top1_quotient_map_on_def
        using hTS1q hq_cont hq_surj hquot_cond by (by100 blast)
    qed
    \<comment> \<open>By Theorem 22.2: g = q∘h constant on fibers, so \<exists>f with f∘q=g and f continuous iff g continuous.\<close>
    have hg_range: "\<forall>z\<in>top1_S1. (q \<circ> h) z \<in> top1_S1"
      using hqh_cont unfolding top1_continuous_map_on_def by (by100 blast)
    obtain f where hf_range: "\<forall>w\<in>top1_S1. f w \<in> top1_S1"
        and hf_eq: "\<forall>z\<in>top1_S1. f (q z) = (q \<circ> h) z"
        and hf_cont_iff: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology f
            \<longleftrightarrow> top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (q \<circ> h)"
      using Theorem_22_2[OF hq_quotient hg_range hg_const] by blast
    have hf_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology f"
      using hf_cont_iff hqh_cont by simp
    \<comment> \<open>f = k on S^1 (both satisfy f(q(z)) = q(h(z))).\<close>
    have hfk_eq: "\<And>w. w \<in> top1_S1 \<Longrightarrow> f w = k w"
    proof -
      fix w assume hw: "w \<in> top1_S1"
      have "w \<in> q ` top1_S1" using hq_surj hw by simp
      then obtain z where hz: "z \<in> top1_S1" and hqz: "q z = w" by (by100 auto)
      have "f w = f (q z)" using hqz by simp
      also have "\<dots> = (q \<circ> h) z" using hf_eq hz by simp
      also have "\<dots> = q (h z)" by simp
      also have "\<dots> = k (q z)" using hk_eq[OF hz] by simp
      also have "\<dots> = k w" using hqz by simp
      finally show "f w = k w" .
    qed
    \<comment> \<open>k is continuous (= f on S^1, and f is continuous).\<close>
    show ?thesis
      using iffD1[OF top1_continuous_map_on_cong[of top1_S1 f k] hf_cont]
      using hfk_eq by (by100 blast)
  qed
  show ?thesis
  proof (rule that[of k])
    show "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology k" by (rule hk_cont)
    show "\<forall>z\<in>top1_S1. k ((\<lambda>(x,y). (x^2-y^2, 2*x*y)) z) = (\<lambda>(x,y). (x^2-y^2, 2*x*y)) (h z)"
      using hk_eq unfolding hq_alt q_def by simp
  qed
qed


text \<open>Helper for Theorem 57.1: if g: S^1 \<rightarrow> S^1 is continuous, antipode-preserving,
  and g(1,0) = (1,0), then g_* is nontrivial (i.e. NOT every loop maps to the trivial class).
  Proof: Steps 2+3 of Munkres' proof of Theorem 57.1.\<close>

lemma antipode_preserving_basepoint_nontrivial:
  assumes hg: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology g"
      and hanti: "top1_antipode_preserving_S1 g"
      and hg10: "g (1, 0) = (1, 0)"
  shows "\<not> (\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
      \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
            (g \<circ> f) (top1_constant_path (1, 0)))"
proof
  assume hall: "\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
      \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
            (g \<circ> f) (top1_constant_path (1, 0))"
  let ?q = "\<lambda>(x, y). (x^2 - y^2 :: real, 2*x*y)"
  \<comment> \<open>Step 1: Construct f\<tilde> = upper semicircle from (1,0) to (-1,0).\<close>
  define ftilde where "ftilde t = (cos (pi * t), sin (pi * t))" for t :: real
  have hft_S1: "\<And>t. ftilde t \<in> top1_S1" unfolding ftilde_def top1_S1_def by (by100 simp)
  have hft0: "ftilde 0 = (1, 0)" unfolding ftilde_def by simp
  have hft1: "ftilde 1 = (-1, 0)" unfolding ftilde_def by simp
  have hft_cont: "continuous_on I_set ftilde"
    unfolding ftilde_def by (intro continuous_intros)
  have hft_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (-1, 0) ftilde"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology ftilde"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix t assume "t \<in> I_set" show "ftilde t \<in> top1_S1" by (rule hft_S1)
    next
      fix V assume hV: "V \<in> top1_S1_topology"
      obtain W' where hW': "W' \<in> product_topology_on top1_open_sets top1_open_sets"
          and hVeq: "V = top1_S1 \<inter> W'"
        using hV unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      have hW'_open: "open W'"
        using hW' by (metis product_topology_on_open_sets_real2 top1_open_sets_def mem_Collect_eq)
      have "{t \<in> I_set. ftilde t \<in> V} = {t \<in> I_set. ftilde t \<in> W'}"
        using hft_S1 hVeq by (by100 blast)
      moreover have "{t \<in> I_set. ftilde t \<in> W'} \<in> I_top"
      proof -
        obtain U where hU: "open U" and hUeq: "U \<inter> I_set = ftilde -` W' \<inter> I_set"
          using hft_cont hW'_open unfolding continuous_on_open_invariant by auto
        have "{t \<in> I_set. ftilde t \<in> W'} = U \<inter> I_set" using hUeq by (by100 blast)
        moreover have "U \<in> top1_open_sets" using hU unfolding top1_open_sets_def by simp
        hence "I_set \<inter> U \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
        moreover have "U \<inter> I_set = I_set \<inter> U" by (by100 blast)
        ultimately show ?thesis by simp
      qed
      ultimately show "{t \<in> I_set. ftilde t \<in> V} \<in> I_top" by simp
    qed
    show "ftilde 0 = (1, 0)" by (rule hft0)
    show "ftilde 1 = (-1, 0)" by (rule hft1)
  qed
  \<comment> \<open>Step 2: f = q \<circ> ftilde is a loop at (1,0).\<close>
  define f where "f = ?q \<circ> ftilde"
  have hq_cont_loc: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology ?q"
    using squaring_map_covering unfolding top1_covering_map_on_def by (by100 blast)
  have hft_cont_top: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology ftilde"
    using hft_path unfolding top1_is_path_on_def by (by100 blast)
  have hf_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology f"
    unfolding f_def using top1_continuous_map_on_comp[OF hft_cont_top hq_cont_loc]
    by (simp add: comp_assoc)
  have hf0: "f 0 = (1, 0)" unfolding f_def comp_def using hft0 by simp
  have hf1: "f 1 = (1, 0)" unfolding f_def comp_def using hft1 by simp
  have hf_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f"
    unfolding top1_is_loop_on_def top1_is_path_on_def using hf_cont hf0 hf1 by (by100 blast)
  \<comment> \<open>Step 3: g \<circ> f is assumed trivial. So g \<circ> q \<circ> ftilde \<simeq> const.\<close>
  have hgf_triv: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
      (g \<circ> f) (top1_constant_path (1, 0))"
    using hall hf_loop by (by100 blast)
  \<comment> \<open>Step 4: g \<circ> ftilde is a path from (1,0) to (-1,0) (since g(1,0)=(1,0), g(-1,0)=(-1,0)).\<close>
  have hg_minus10: "g (-1, 0) = (-1, 0)"
  proof -
    have "g (-(1::real), -(0::real)) = (- fst (g (1, 0)), - snd (g (1, 0)))"
      using hanti unfolding top1_antipode_preserving_S1_def
      by (rule allE[of _ 1]) (rule allE[of _ 0], simp)
    thus ?thesis using hg10 by simp
  qed
  have hgft_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology (g \<circ> ftilde)"
    using top1_continuous_map_on_comp[OF hft_cont_top hg] by (simp add: comp_assoc)
  have hgft0: "(g \<circ> ftilde) 0 = (1, 0)" using hft0 hg10 by simp
  have hgft1: "(g \<circ> ftilde) 1 = (-1, 0)" using hft1 hg_minus10 by simp
  have hgft_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (-1, 0) (g \<circ> ftilde)"
    unfolding top1_is_path_on_def using hgft_cont hgft0 hgft1 by (by100 blast)
  \<comment> \<open>Step 5: q \<circ> (g \<circ> ftilde) = (g \<circ> f) (since q \<circ> g = k \<circ> q for some k, but more directly:
     k \<circ> q \<circ> ftilde = k \<circ> f = ?, and q \<circ> g \<circ> ftilde = g \<circ> f? No: g \<circ> q \<noteq> q \<circ> g in general.
     Actually: g \<circ> f = g \<circ> (q \<circ> ftilde) \<noteq> q \<circ> (g \<circ> ftilde) in general.
     We need: q \<circ> (g \<circ> ftilde) is a loop at (1,0) that is ALSO trivial if g \<circ> f is trivial.

     The correct argument: q \<circ> (g \<circ> ftilde) is a loop at q(g(1,0)) = q(1,0) = (1,0).
     g \<circ> ftilde is a LIFTING of q \<circ> (g \<circ> ftilde) (since q \<circ> (g \<circ> ftilde) = q \<circ> g \<circ> ftilde).
     If q \<circ> (g \<circ> ftilde) were trivial, then by Theorem 54.3 (unique lifting),
     the lift g \<circ> ftilde would end at (1,0). But g \<circ> ftilde ends at (-1,0). Contradiction.

     But we need q \<circ> (g \<circ> ftilde) to be trivial. We know g \<circ> f = g \<circ> (q \<circ> ftilde) is trivial.
     And k \<circ> q = q \<circ> g, so q \<circ> g \<circ> ftilde = k \<circ> q \<circ> ftilde = k \<circ> f.
     If g \<circ> f is trivial, is k \<circ> f trivial? Not necessarily directly.

     Actually the textbook argument is different: it shows k_* is nontrivial, then q_* injective,
     then k_* \<circ> q_* injective, then since q_* \<circ> g_* = k_* \<circ> q_* and k_* \<circ> q_* is injective,
     g_* is injective (hence nontrivial).

     Let me follow that approach instead.\<close>
  \<comment> \<open>Direct approach: q \<circ> (g \<circ> ftilde) has lift g \<circ> ftilde ending at (-1,0) \<noteq> (1,0).
     By covering theory, this loop is nontrivial. But q \<circ> (g \<circ> ftilde) = k \<circ> f.
     And k \<circ> f is trivial iff g \<circ> f is trivial (since k_* is injective on π_1... wait, no).

     Simpler: if g_* is trivial, then for ALL loops L, g \<circ> L \<simeq> const. In particular,
     g \<circ> (q \<circ> ftilde) \<simeq> const. So q \<circ> g \<circ> (q \<circ> ftilde) \<simeq> q \<circ> const = const.
     But q \<circ> g \<circ> (q \<circ> ftilde) = k \<circ> q \<circ> (q \<circ> ftilde) = k \<circ> (q \<circ> q \<circ> ftilde).
     This doesn't simplify nicely.

     Even simpler: q \<circ> (g \<circ> ftilde) = (q \<circ> g) \<circ> ftilde = (k \<circ> q) \<circ> ftilde = k \<circ> f.
     So q \<circ> (g \<circ> ftilde) = k \<circ> f.

     g \<circ> ftilde is a lift of k \<circ> f (since q \<circ> (g \<circ> ftilde) = k \<circ> f).
     g \<circ> ftilde starts at (1,0) and ends at (-1,0).

     If k \<circ> f were trivial, then by Theorem 54.3 the lift g \<circ> ftilde would be homotopic to
     the constant lift at (1,0), hence end at (1,0). Contradiction.

     Now: from g_* trivial, we get g \<circ> f \<simeq> const. Then k \<circ> (g \<circ> f) \<simeq> k \<circ> const = const.
     But k \<circ> (g \<circ> f) = k \<circ> g \<circ> f = ??? We don't have k \<circ> g = anything useful.

     OK, the correct path: we need k \<circ> f nontrivial.
     k \<circ> f = q \<circ> (g \<circ> ftilde).
     g \<circ> ftilde lifts k \<circ> f, starts at (1,0), ends at (-1,0).
     If k \<circ> f were trivial, Theorem 54.3 gives g \<circ> ftilde ends at (1,0). Contradiction.
     So k \<circ> f is nontrivial. Hence k_* nontrivial.

     Now if g_* is trivial (the assumption), then g \<circ> L \<simeq> const for all L.
     In particular g \<circ> f \<simeq> const. Then q_* \<circ> g_*([f]) = q_*([const]) = [const].
     But q_* \<circ> g_* = k_* \<circ> q_*. So k_*(q_*([f])) = [const].
     Since q_*([f]) = [q \<circ> f] = [q \<circ> q \<circ> ftilde]. Hmm, not useful.

     THE KEY: q_* \<circ> g_* = k_* \<circ> q_* as homomorphisms.
     g_* trivial \<Rightarrow> q_* \<circ> g_* trivial \<Rightarrow> k_* \<circ> q_* trivial.
     But k_* nontrivial and q_* nontrivial (maps generator to double).
     k_* \<circ> q_* maps generator [gen] to k_*(q_*([gen])) = k_*([gen^2]).
     If k_* is injective (nontrivial on Z means injective), k_*([gen^2]) \<noteq> [const].
     So k_* \<circ> q_* is nontrivial. Contradiction.\<close>
  \<comment> \<open>Let's just use the direct lifting argument: k\<circ>f is nontrivial.\<close>
  obtain k where hk_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology k"
      and hk_eq: "\<forall>z\<in>top1_S1. k (?q z) = ?q (g z)"
    by (rule squaring_map_factorization[OF hg hanti])
  \<comment> \<open>k \<circ> f = q \<circ> (g \<circ> ftilde).\<close>
  have hkf_eq: "\<And>t. t \<in> I_set \<Longrightarrow> (k \<circ> f) t = (?q \<circ> (g \<circ> ftilde)) t"
  proof -
    fix t assume ht: "t \<in> I_set"
    have "ftilde t \<in> top1_S1" by (rule hft_S1)
    hence "(k \<circ> f) t = k (?q (ftilde t))" unfolding f_def comp_def by simp
    also have "\<dots> = ?q (g (ftilde t))" using hk_eq \<open>ftilde t \<in> top1_S1\<close> by (by100 blast)
    finally show "(k \<circ> f) t = (?q \<circ> (g \<circ> ftilde)) t" by (simp add: comp_def)
  qed
  \<comment> \<open>g \<circ> ftilde is a lift of k \<circ> f under q, starting at (1,0), ending at (-1,0).\<close>
  \<comment> \<open>If k \<circ> f were trivial, Theorem 54.3 would force the lift to end at (1,0). Contradiction.\<close>
  \<comment> \<open>So k \<circ> f is nontrivial.\<close>
  \<comment> \<open>But from g_* trivial: g \<circ> f \<simeq> const. Then q \<circ> g = k \<circ> q means
     q_*(g_*([f])) = k_*(q_*([f])). g_*([f]) = [const], so q_*([const]) = [const].
     Hence k_*(q_*([f])) = [const]. But q_*([f]) = [q \<circ> f] and we showed
     k \<circ> (q \<circ> ftilde) = k \<circ> f is nontrivial. Since q \<circ> ftilde = f,
     k_*([f]) is nontrivial. So k_*(q_*([ftilde'])) where q \<circ> ftilde' = f...
     This is getting circular. Let me just use the lifting argument directly.\<close>
  \<comment> \<open>The key fact: q \<circ> (g \<circ> ftilde) = k \<circ> f, and g \<circ> ftilde lifts this loop,
     starting at (1,0) and ending at (-1,0). If this loop were trivial (constant),
     the lift would end at (1,0) by Theorem 54.3. Contradiction.\<close>
  \<comment> \<open>Key: q \<circ> (g \<circ> ftilde) = k \<circ> f (from hkf_eq). g \<circ> ftilde is a lift of this loop,
     starting at (1,0) and ending at (-1,0). By Theorem 54.3, if k \<circ> f were trivial,
     the lift would end at (1,0). Contradiction. So k \<circ> f is nontrivial.

     From g_* trivial: g \<circ> f \<simeq> const. Then q \<circ> g \<circ> f = k \<circ> q \<circ> f.
     q \<circ> (g \<circ> f) \<simeq> q \<circ> const = const. So k \<circ> (q \<circ> f) \<simeq> const.
     But q \<circ> f = q \<circ> (q \<circ> ftilde). This is a different loop from f.
     The key: k_* maps [q \<circ> f] = k_*( q_*([f]) ) to const. Since k \<circ> f is nontrivial,
     and [q \<circ> f] \<noteq> [f], this doesn't immediately contradict.

     The textbook resolves this by showing k_* injective (Step 3) + q_* injective,
     hence k_* \<circ> q_* injective, hence g_* injective (since q_* \<circ> g_* = k_* \<circ> q_*).

     Proof via standard covering p: R \<rightarrow> S^1.
     k \<circ> f nontrivial (lift ends at n \<noteq> 0).
     k \<circ> (q \<circ> f) trivial (from g_* trivial + chain).
     q \<circ> f = f * f, so k \<circ> (f*f) = (k\<circ>f)*(k\<circ>f), lift ends at 2n.
     2n = 0 and n \<noteq> 0 impossible in Z.\<close>
  \<comment> \<open>Step A: k \<circ> f is nontrivial (lift of k\<circ>f under q has endpoint (-1,0) via g\<circ>ftilde).\<close>
  have hkf_nontrivial: "\<not> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
      (k \<circ> f) (top1_constant_path (1, 0))"
  proof
    assume hkf_triv: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
        (k \<circ> f) (top1_constant_path (1, 0))"
    \<comment> \<open>g \<circ> ftilde lifts k \<circ> f: q \<circ> (g \<circ> ftilde) = k \<circ> f on I_set.\<close>
    \<comment> \<open>The constant path at (1,0) lifts const: q(1,0) = (1,0), const at (1,0).\<close>
    \<comment> \<open>By Theorem 54.3: endpoints of lifts must agree. But g\<circ>ftilde ends at (-1,0),
       const ends at (1,0). So (-1,0) = (1,0), contradiction.\<close>
    have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    proof -
      have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV] by simp
      thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
    qed
    have h10S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    have hm10S1: "(-1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    \<comment> \<open>k \<circ> f is a loop at (1,0).\<close>
    have hkf_loop: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (k \<circ> f)"
      using hkf_triv unfolding top1_path_homotopic_on_def by (by100 blast)
    \<comment> \<open>const is a path from (1,0) to (1,0).\<close>
    have hconst_loop: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0)
        (top1_constant_path (1, 0))"
      by (rule top1_constant_path_is_path[OF hTS1 h10S1])
    \<comment> \<open>g \<circ> ftilde lifts k \<circ> f under q, from (1,0) to (-1,0).\<close>
    \<comment> \<open>const at (1,0) lifts const at (1,0) under q.\<close>
    \<comment> \<open>By Theorem 54.3: (-1,0) = (1,0). Contradiction.\<close>
    \<comment> \<open>Lift 1: g \<circ> ftilde lifts k \<circ> f (from hkf_eq). Starts at (1,0), ends at (-1,0).\<close>
    have hlift1: "\<forall>s\<in>I_set. ?q ((g \<circ> ftilde) s) = (k \<circ> f) s"
      using hkf_eq by simp
    \<comment> \<open>Lift 2: const_(1,0) lifts const_(1,0) since q(1,0) = (1,0).\<close>
    have hq10: "?q (1, 0) = (1, 0)" by simp
    have hlift2: "\<forall>s\<in>I_set. ?q (top1_constant_path (1, 0) s) = top1_constant_path (1, 0) s"
      unfolding top1_constant_path_def using hq10 by simp
    \<comment> \<open>By Theorem 54.3: lifts with same start and homotopic base paths have same endpoint.\<close>
    have "(-1::real, 0::real) = (1::real, 0::real)"
      using conjunct1[OF Theorem_54_3[OF squaring_map_covering hTS1 hTS1 h10S1 _
          hkf_loop hconst_loop hkf_triv hgft_path hlift1 hconst_loop hlift2]]
      by simp
    thus False by simp
  qed
  \<comment> \<open>Steps B-E use the standard covering p: R \<rightarrow> S^1 and Theorem 54.4.\<close>
  \<comment> \<open>Step B: q \<circ> f = f * f (path product of f with itself).\<close>
  \<comment> \<open>q \<circ> f = f * f: f(t) = q(ftilde(t)) = (cos 2\<pi>t, sin 2\<pi>t).
     f*f(t) = f(2t) for t \<le> 1/2, f(2t-1) for t > 1/2.
     f(2t) = (cos 4\<pi>t, sin 4\<pi>t). f(2t-1) = (cos(4\<pi>t-2\<pi>), sin(4\<pi>t-2\<pi>)) = (cos 4\<pi>t, sin 4\<pi>t).
     q(f(t)) = q(cos 2\<pi>t, sin 2\<pi>t) = (cos^2 2\<pi>t - sin^2 2\<pi>t, 2 cos 2\<pi>t sin 2\<pi>t)
             = (cos 4\<pi>t, sin 4\<pi>t). So both equal (cos 4\<pi>t, sin 4\<pi>t).\<close>
  \<comment> \<open>Key identity: f(t) = (cos 2\<pi>t, sin 2\<pi>t) via double angle formulas.\<close>
  have hf_trig: "\<And>t. f t = (cos (2*pi*t), sin (2*pi*t))"
  proof -
    fix t :: real
    have hft_q: "f t = ((cos (pi*t))^2 - (sin (pi*t))^2, 2 * cos (pi*t) * sin (pi*t))"
      unfolding f_def comp_def ftilde_def by (simp add: mult.commute)
    have hcos: "(cos (pi*t))^2 - (sin (pi*t))^2 = cos (2*pi*t)"
      using cos_double[of "pi*t"] by (simp add: algebra_simps)
    have hsin: "2 * cos (pi*t) * sin (pi*t) = sin (2*pi*t)"
      using sin_double[of "pi*t"] by (simp add: algebra_simps)
    show "f t = (cos (2*pi*t), sin (2*pi*t))" using hft_q hcos hsin by simp
  qed
  have hqf_eq: "\<And>t. ?q (f t) = top1_path_product f f t"
  proof -
    fix t :: real
    \<comment> \<open>LHS: q(f(t)) = (cos 4\<pi>t, sin 4\<pi>t) by double angle on f(t)=(cos 2\<pi>t, sin 2\<pi>t).\<close>
    have hqf: "?q (f t) = (cos (4*pi*t), sin (4*pi*t))"
    proof -
      have "?q (f t) = ((cos (2*pi*t))^2 - (sin (2*pi*t))^2, 2 * cos (2*pi*t) * sin (2*pi*t))"
        using hf_trig[of t] by simp
      moreover have "(cos (2*pi*t))^2 - (sin (2*pi*t))^2 = cos (2*(2*pi*t))"
        using cos_double[of "2*pi*t"] by simp
      moreover have "2 * cos (2*pi*t) * sin (2*pi*t) = sin (2*(2*pi*t))"
        using sin_double[of "2*pi*t"] by (simp add: mult.commute)
      moreover have "2*(2*pi*t) = 4*pi*t" by simp
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>RHS: (f*f)(t) = f(2t) or f(2t-1), both = (cos 4\<pi>t, sin 4\<pi>t).\<close>
    have hff: "top1_path_product f f t = (cos (4*pi*t), sin (4*pi*t))"
    proof (cases "t \<le> 1/2")
      case True
      have "top1_path_product f f t = f (2*t)" unfolding top1_path_product_def using True by simp
      also have "\<dots> = (cos (2*pi*(2*t)), sin (2*pi*(2*t)))" using hf_trig by simp
      also have "2*pi*(2*t) = 4*pi*t" by simp
      finally show ?thesis by simp
    next
      case False
      have "top1_path_product f f t = f (2*t - 1)" unfolding top1_path_product_def using False by simp
      hence "top1_path_product f f t = (cos (2*pi*(2*t - 1)), sin (2*pi*(2*t - 1)))"
        using hf_trig[of "2*t-1"] by simp
      moreover have "2*pi*(2*t - 1) = 4*pi*t - 2*pi" by (simp add: algebra_simps)
      moreover have "cos (4*pi*t - 2*pi) = cos (4*pi*t)" by (simp add: cos_diff)
      moreover have "sin (4*pi*t - 2*pi) = sin (4*pi*t)" by (simp add: sin_diff)
      ultimately show ?thesis by simp
    qed
    show "?q (f t) = top1_path_product f f t" using hqf hff by simp
  qed
  \<comment> \<open>Step C: k \<circ> (f*f) = (k\<circ>f) * (k\<circ>f).\<close>
  have hk_prod: "\<And>t. (k \<circ> (top1_path_product f f)) t = top1_path_product (k \<circ> f) (k \<circ> f) t"
    unfolding top1_path_product_def comp_def by simp
  \<comment> \<open>Step D: k \<circ> (q \<circ> f) = k \<circ> (f*f) = (k\<circ>f)*(k\<circ>f).\<close>
  \<comment> \<open>From g_* trivial: g \<circ> f \<simeq> const. q \<circ> (g \<circ> f) = k \<circ> (q \<circ> f) \<simeq> const.
     So (k\<circ>f)*(k\<circ>f) \<simeq> const.\<close>
  \<comment> \<open>Chain: g\<circ>f\<simeq>const, q\<circ>g=k\<circ>q, q\<circ>f=f*f on I_set, k distributes over product.\<close>
  have hkf2_triv: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
      (top1_path_product (k \<circ> f) (k \<circ> f)) (top1_constant_path (1, 0))"
  proof -
    have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    proof -
      have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV] by simp
      thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
    qed
    \<comment> \<open>q continuous.\<close>
    have hq_cont_local: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology ?q"
      using squaring_map_covering unfolding top1_covering_map_on_def by (by100 blast)
    \<comment> \<open>q \<circ> (g \<circ> f) \<simeq> q \<circ> const = const. Uses continuous_preserves_path_homotopic.\<close>
    have hqgf: "top1_path_homotopic_on top1_S1 top1_S1_topology (?q (1,0)) (?q (1,0))
        (?q \<circ> (g \<circ> f)) (?q \<circ> top1_constant_path (1, 0))"
      by (rule continuous_preserves_path_homotopic[OF hTS1 hTS1 hq_cont_local hgf_triv])
    have hq10: "?q (1::real, 0::real) = (1, 0)" by simp
    have hq_const: "?q \<circ> top1_constant_path (1, 0) = top1_constant_path (1, 0)"
      unfolding top1_constant_path_def comp_def using hq10 by (intro ext) simp
    have hqgf': "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
        (?q \<circ> (g \<circ> f)) (top1_constant_path (1, 0))"
      using hqgf hq10 hq_const by simp
    \<comment> \<open>q \<circ> (g \<circ> f) = q \<circ> g \<circ> f = k \<circ> q \<circ> f = k \<circ> (f*f) = (k\<circ>f)*(k\<circ>f) pointwise on I_set.\<close>
    have hchain_eq: "\<And>t. t \<in> I_set \<Longrightarrow> (?q \<circ> (g \<circ> f)) t = top1_path_product (k \<circ> f) (k \<circ> f) t"
    proof -
      fix t assume ht: "t \<in> I_set"
      have hft_S1: "f t \<in> top1_S1"
        using hf_cont ht unfolding top1_continuous_map_on_def by (by100 blast)
      have "(?q \<circ> (g \<circ> f)) t = ?q (g (f t))" by (simp add: comp_def)
      also have "\<dots> = k (?q (f t))"
      proof -
        have "?q (g (f t)) = k (?q (f t))" using hk_eq[rule_format, OF hft_S1] by simp
        thus ?thesis by (simp add: comp_def)
      qed
      also have "?q (f t) = top1_path_product f f t" by (rule hqf_eq)
      also have "k (top1_path_product f f t) = top1_path_product (k \<circ> f) (k \<circ> f) t"
        using hk_prod by simp
      finally show "(?q \<circ> (g \<circ> f)) t = top1_path_product (k \<circ> f) (k \<circ> f) t" .
    qed
    \<comment> \<open>Since the functions agree on I_set and one is homotopic to const, so is the other.\<close>
    have "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
        (?q \<circ> (g \<circ> f)) (top1_constant_path (1, 0))" by (rule hqgf')
    moreover have "\<forall>t\<in>I_set. (?q \<circ> (g \<circ> f)) t = top1_path_product (k \<circ> f) (k \<circ> f) t"
      using hchain_eq by (by100 blast)
    \<comment> \<open>The two functions agree on I_set. Path homotopy only depends on values on I_set.\<close>
    \<comment> \<open>Transfer via top1_path_homotopic_on_def: only I_set values matter.\<close>
    ultimately show ?thesis
    proof -
      assume hhom: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
          (?q \<circ> (g \<circ> f)) (top1_constant_path (1, 0))"
      assume heq: "\<forall>t\<in>I_set. (?q \<circ> (g \<circ> f)) t = top1_path_product (k \<circ> f) (k \<circ> f) t"
      obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology top1_S1 top1_S1_topology F"
          and hF0: "\<forall>s\<in>I_set. F (s, 0) = (?q \<circ> (g \<circ> f)) s"
          and hF1: "\<forall>s\<in>I_set. F (s, 1) = top1_constant_path (1, 0) s"
          and hFl: "\<forall>t\<in>I_set. F (0, t) = (1, 0)" and hFr: "\<forall>t\<in>I_set. F (1, t) = (1, 0)"
        using hhom unfolding top1_path_homotopic_on_def
        apply (by100 simp)
        apply (by100 blast)
        done
      have hF0': "\<forall>s\<in>I_set. F (s, 0) = top1_path_product (k \<circ> f) (k \<circ> f) s"
        using hF0 heq by simp
      have hkf_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (k \<circ> f)"
      proof -
        have "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology (k \<circ> f)"
          using top1_continuous_map_on_comp[OF hf_cont hk_cont] by (simp add: comp_assoc)
        moreover have "(k \<circ> f) 0 = (1, 0)"
        proof -
          have "f 0 = (1, 0)" using hf0 .
          have h10S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
          have "k (1, 0) = k (?q (1, 0))" by simp
          also have "\<dots> = ?q (g (1, 0))" using hk_eq[rule_format, OF h10S1] by simp
          also have "\<dots> = ?q (1, 0)" using hg10 by simp
          also have "\<dots> = (1, 0)" by simp
          finally show ?thesis using hf0 by (simp add: comp_def)
        qed
        moreover have "(k \<circ> f) 1 = (1, 0)"
        proof -
          have "f 1 = (1, 0)" using hf1 .
          thus ?thesis using \<open>(k \<circ> f) 0 = (1, 0)\<close> hf0 hf1 by (simp add: comp_def)
        qed
        ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
      qed
      have hpath1: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0)
          (top1_path_product (k \<circ> f) (k \<circ> f))"
        by (rule top1_path_product_is_path[OF hTS1 hkf_path hkf_path])
      have hpath2: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (top1_constant_path (1, 0))"
        using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
      show ?thesis unfolding top1_path_homotopic_on_def
        using hpath1 hpath2 hF hF0' hF1 hFl hFr by (by100 blast)
    qed
  qed
  \<comment> \<open>Step E: In \<pi>_1(S^1) \<cong> Z: k\<circ>f corresponds to n \<noteq> 0, (k\<circ>f)*(k\<circ>f) to 2n.
     2n = 0 and n \<noteq> 0 impossible. Use covering p: R \<rightarrow> S^1.\<close>
  \<comment> \<open>Lift k\<circ>f under p from 0 to some endpoint e1. Since k\<circ>f nontrivial, e1 \<noteq> 0.
     Lift (k\<circ>f)*(k\<circ>f) from 0 to 2*e1 (translated lift concatenation).
     Since (k\<circ>f)*(k\<circ>f) trivial, 2*e1 = 0. So e1 = 0. Contradiction.\<close>
  \<comment> \<open>Contradiction: k\<circ>f nontrivial (hkf_nontrivial) but (k\<circ>f)*(k\<circ>f) trivial (hkf2_triv).
     By Theorem_54_5_iso, \<pi>_1(S^1) \<cong> Z. In Z, 2n = 0 implies n = 0.
     The isomorphism maps [k\<circ>f] to n \<noteq> 0 and [(k\<circ>f)*(k\<circ>f)] to 2n = 0. Contradiction.\<close>
  \<comment> \<open>Use Theorem_54_5_iso: \<pi>_1(S^1,(1,0)) \<cong> Z (group isomorphism).
     The isomorphism \<phi> satisfies \<phi>([f]*[g]) = \<phi>([f]) + \<phi>([g]).
     \<phi>([k\<circ>f]) = n \<noteq> 0 (since k\<circ>f nontrivial).
     \<phi>([(k\<circ>f)*(k\<circ>f)]) = 2n = 0 (since (k\<circ>f)*(k\<circ>f) trivial).
     2n = 0 in Z implies n = 0. Contradiction.\<close>
  show False
  proof -
    let ?\<pi>1 = "top1_fundamental_group_carrier top1_S1 top1_S1_topology (1::real, 0::real)"
    let ?mul = "top1_fundamental_group_mul top1_S1 top1_S1_topology (1::real, 0::real)"
    obtain \<phi> where h\<phi>_iso: "top1_group_iso_on ?\<pi>1 ?mul top1_Z_group top1_Z_mul \<phi>"
      using Theorem_54_5_iso unfolding top1_groups_isomorphic_on_def by (by100 blast)
    have h\<phi>_hom: "\<forall>x\<in>?\<pi>1. \<forall>y\<in>?\<pi>1. \<phi> (?mul x y) = \<phi> x + \<phi> y"
      using h\<phi>_iso unfolding top1_group_iso_on_def top1_group_hom_on_def top1_Z_mul_def by (by100 blast)
    have h\<phi>_inj: "inj_on \<phi> ?\<pi>1"
      using h\<phi>_iso unfolding top1_group_iso_on_def bij_betw_def by (by100 blast)
    have hkf_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) (k \<circ> f)"
    proof -
      have hkf_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology (k \<circ> f)"
        using top1_continuous_map_on_comp[OF hf_cont hk_cont] by (simp add: comp_assoc)
      have h10S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
      have hk10: "k (1, 0) = (1, 0)"
        using hk_eq[rule_format, OF h10S1] hg10 by simp
      show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
        using hkf_cont hk10 hf0 hf1 by (simp add: comp_def)
    qed
    \<comment> \<open>Equivalence classes.\<close>
    define ckf where "ckf = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) (k \<circ> f) g}"
    define cid where "cid = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) (top1_constant_path (1, 0)) g}"
    have hckf_pi: "ckf \<in> ?\<pi>1"
      unfolding ckf_def top1_fundamental_group_carrier_def using hkf_loop by (by100 blast)
    have h10S1': "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    have hTS1': "is_topology_on top1_S1 top1_S1_topology"
    proof -
      have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV] by simp
      thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
    qed
    have hconst_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) (top1_constant_path (1, 0))"
      by (rule top1_constant_path_is_loop[OF hTS1' h10S1'])
    have hcid_pi: "cid \<in> ?\<pi>1"
      unfolding cid_def top1_fundamental_group_carrier_def using hconst_loop by (by100 blast)
    have hkf_path': "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (k \<circ> f)"
      using hkf_loop unfolding top1_is_loop_on_def by (by100 blast)
    have hkf_refl: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) (k \<circ> f) (k \<circ> f)"
      by (rule Lemma_51_1_path_homotopic_refl[OF hkf_path'])
    have hkf_in_ckf: "k \<circ> f \<in> ckf"
      unfolding ckf_def top1_loop_equiv_on_def using hkf_loop hkf_refl by (by100 blast)
    have hckf_ne_cid: "ckf \<noteq> cid"
    proof
      assume heq: "ckf = cid"
      have "k \<circ> f \<in> cid" using hkf_in_ckf heq by simp
      hence "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
          (top1_constant_path (1, 0)) (k \<circ> f)"
        unfolding cid_def by simp
      hence hle: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) (top1_constant_path (1, 0)) (k \<circ> f)"
        unfolding cid_def by simp
      have "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
          (top1_constant_path (1, 0)) (k \<circ> f)"
        using hle unfolding top1_loop_equiv_on_def by (by100 blast)
      hence "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
          (k \<circ> f) (top1_constant_path (1, 0))"
        by (rule Lemma_51_1_path_homotopic_sym)
      thus False using hkf_nontrivial by (by100 blast)
    qed
    have h\<phi>_id: "\<phi> cid = 0"
    proof -
      \<comment> \<open>\<phi>(e * e) = \<phi>(e) + \<phi>(e) and e * e = e, so 2*\<phi>(e) = \<phi>(e), hence \<phi>(e) = 0.\<close>
      have "?mul cid cid = cid"
      proof -
        \<comment> \<open>const * const \<simeq> const by left identity.\<close>
        have hcc_triv: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
            (top1_path_product (top1_constant_path (1, 0)) (top1_constant_path (1, 0)))
            (top1_constant_path (1, 0))"
          by (rule Theorem_51_2_left_identity[OF hTS1'
                top1_constant_path_is_path[OF hTS1' h10S1']])
        \<comment> \<open>So top1_path_product const const is in the constant class.\<close>
        \<comment> \<open>mul cid cid = {h | \<exists>f\<in>cid.\<exists>g\<in>cid. (f*g) equiv h}.\<close>
        \<comment> \<open>Take f = const, g = const. f*g = const*const \<simeq> const. So const \<in> mul cid cid.\<close>
        \<comment> \<open>Both sets are equivalence classes, so they're equal if they share an element.\<close>
        \<comment> \<open>By mul_class: mul cid cid = [const*const]. And [const*const] = [const] = cid.\<close>
        have hmul_cc: "?mul cid cid = {h. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
            (top1_path_product (top1_constant_path (1, 0)) (top1_constant_path (1, 0))) h}"
          unfolding cid_def
          by (rule top1_fundamental_group_mul_class[OF hTS1' hconst_loop hconst_loop])
        \<comment> \<open>[const*const] = [const] because const*const \<equiv> const (hcc_triv + equivalence).\<close>
        have hcc_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0)
            (top1_path_product (top1_constant_path (1, 0)) (top1_constant_path (1, 0)))"
          by (rule top1_path_product_is_loop[OF hTS1' hconst_loop hconst_loop])
        have hcc_equiv_const: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
            (top1_path_product (top1_constant_path (1, 0)) (top1_constant_path (1, 0)))
            (top1_constant_path (1, 0))"
          unfolding top1_loop_equiv_on_def using hcc_loop hconst_loop hcc_triv by (by100 blast)
        have "\<And>h. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
            (top1_path_product (top1_constant_path (1, 0)) (top1_constant_path (1, 0))) h
          \<longleftrightarrow> top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
            (top1_constant_path (1, 0)) h"
        proof -
          fix h
          show "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
              (top1_path_product (top1_constant_path (1, 0)) (top1_constant_path (1, 0))) h
            \<longleftrightarrow> top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
              (top1_constant_path (1, 0)) h"
          proof
            assume hcceh: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                (top1_path_product (top1_constant_path (1, 0)) (top1_constant_path (1, 0))) h"
            show "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) (top1_constant_path (1, 0)) h"
            proof -
              have hcsym: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                  (top1_constant_path (1, 0))
                  (top1_path_product (top1_constant_path (1, 0)) (top1_constant_path (1, 0)))"
                by (rule top1_loop_equiv_on_sym[OF hcc_equiv_const])
              show ?thesis by (rule top1_loop_equiv_on_trans[OF hTS1' hcsym hcceh])
            qed
          next
            assume hch: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) (top1_constant_path (1, 0)) h"
            show "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                (top1_path_product (top1_constant_path (1, 0)) (top1_constant_path (1, 0))) h"
              by (rule top1_loop_equiv_on_trans[OF hTS1' hcc_equiv_const hch])
          qed
        qed
        hence "{h. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
            (top1_path_product (top1_constant_path (1, 0)) (top1_constant_path (1, 0))) h}
          = {h. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) (top1_constant_path (1, 0)) h}"
          by (by100 auto)
        thus ?thesis using hmul_cc unfolding cid_def by simp
      qed
      moreover have "\<phi> (?mul cid cid) = \<phi> cid + \<phi> cid" using h\<phi>_hom hcid_pi by (by100 blast)
      ultimately have "\<phi> cid + \<phi> cid = \<phi> cid" by simp
      thus "\<phi> cid = 0" by simp
    qed
    have h\<phi>_ne: "\<phi> ckf \<noteq> \<phi> cid"
      using h\<phi>_inj hckf_pi hcid_pi hckf_ne_cid unfolding inj_on_def by (by100 blast)
    hence h\<phi>_ckf_ne0: "\<phi> ckf \<noteq> 0" using h\<phi>_id by simp
    have hmul_eq_id: "?mul ckf ckf = cid"
    proof -
      have hmul_kk: "?mul ckf ckf = {h. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
          (top1_path_product (k \<circ> f) (k \<circ> f)) h}"
        unfolding ckf_def by (rule top1_fundamental_group_mul_class[OF hTS1' hkf_loop hkf_loop])
      \<comment> \<open>[(k\<circ>f)*(k\<circ>f)] = [const] because (k\<circ>f)*(k\<circ>f) \<equiv> const.\<close>
      have hkf2_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0)
          (top1_path_product (k \<circ> f) (k \<circ> f))"
        by (rule top1_path_product_is_loop[OF hTS1' hkf_loop hkf_loop])
      have hkf2_equiv_const: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
          (top1_path_product (k \<circ> f) (k \<circ> f)) (top1_constant_path (1, 0))"
        unfolding top1_loop_equiv_on_def using hkf2_loop hconst_loop hkf2_triv by (by100 blast)
      have "\<And>h. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
          (top1_path_product (k \<circ> f) (k \<circ> f)) h
        \<longleftrightarrow> top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) (top1_constant_path (1, 0)) h"
      proof -
        fix h
        show "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
            (top1_path_product (k \<circ> f) (k \<circ> f)) h
          \<longleftrightarrow> top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) (top1_constant_path (1, 0)) h"
        proof
          assume "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
              (top1_path_product (k \<circ> f) (k \<circ> f)) h"
          show "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) (top1_constant_path (1, 0)) h"
            by (rule top1_loop_equiv_on_trans[OF hTS1'
                  top1_loop_equiv_on_sym[OF hkf2_equiv_const]
                  \<open>top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                    (top1_path_product (k \<circ> f) (k \<circ> f)) h\<close>])
        next
          assume "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) (top1_constant_path (1, 0)) h"
          show "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
              (top1_path_product (k \<circ> f) (k \<circ> f)) h"
            by (rule top1_loop_equiv_on_trans[OF hTS1' hkf2_equiv_const
                  \<open>top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) (top1_constant_path (1, 0)) h\<close>])
        qed
      qed
      hence "{h. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
          (top1_path_product (k \<circ> f) (k \<circ> f)) h}
        = {h. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) (top1_constant_path (1, 0)) h}"
        by (by100 auto)
      thus ?thesis using hmul_kk unfolding cid_def by simp
    qed
    have "\<phi> (?mul ckf ckf) = \<phi> ckf + \<phi> ckf"
      using h\<phi>_hom hckf_pi by (by100 blast)
    hence "2 * \<phi> ckf = 0" using hmul_eq_id h\<phi>_id by simp
    hence "\<phi> ckf = 0" by simp
    thus False using h\<phi>_ckf_ne0 by simp
  qed
qed



(** from *\<S>57 Theorem 57.1: antipode-preserving S^1 \<rightarrow> S^1 is NOT nulhomotopic.

    Munkres' proof:
    Step 1: WLOG h(b_0) = b_0 (rotate). Let q: S^1 \<rightarrow> S^1 be q(z) = z^2 (quotient
            map). q is a covering map and its fibers are antipodal pairs {z, -z}.
            Since h(-z) = -h(z), we have q(h(-z)) = q(h(z)), so q\<circ>h factors as
            k\<circ>q for some continuous k: S^1 \<rightarrow> S^1.
    Step 2: k_* is nontrivial. If \<tilde>f is any path in S^1 from b_0 to -b_0, the
            loop f = q\<circ>\<tilde>f represents a nontrivial element of \<pi>_1(S^1). For \<tilde>f is
            a lifting of f, starting at b_0 but not ending at b_0.
            Hence k_*[f] = [k\<circ>(q\<circ>\<tilde>f)] = [q\<circ>(h\<circ>\<tilde>f)] is also nontrivial.
    Step 3: k_* injective; q_* injective (multiplication by 2 in Z). So k_*\<circ>q_*
            is injective. Since q_*\<circ>h_* = k_*\<circ>q_*, h_* is injective, hence
            nontrivial, hence h is not nulhomotopic. **)
theorem Theorem_57_1:
  assumes "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h"
      and "top1_antipode_preserving_S1 h"
  shows "\<not> top1_nulhomotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h"
proof
  assume hnul: "top1_nulhomotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h"
  \<comment> \<open>Step 1: q(z)=z^2 is a covering map. h(-z)=-h(z) \<Rightarrow> q\<circ>h = k\<circ>q for some k.\<close>
  let ?q = "\<lambda>(x, y). (x^2 - y^2, 2*x*y)"
  have hq_cover: "top1_covering_map_on top1_S1 top1_S1_topology
      top1_S1 top1_S1_topology ?q" by (rule squaring_map_covering)
  obtain k where hk_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
      top1_S1 top1_S1_topology k"
      and hk_eq: "\<forall>z\<in>top1_S1. k (?q z) = ?q (h z)"
    by (rule squaring_map_factorization[OF assms])
  \<comment> \<open>WLOG: reduce to h(1,0) = (1,0) by rotation. Munkres: let \<rho> rotate h(b0) to b0.\<close>
  \<comment> \<open>Case 1: h(1,0) = (1,0). Then h_* at (1,0) is nontrivial (from covering theory),
     but nulhomotopic \<Rightarrow> h_* trivial. Contradiction.\<close>
  \<comment> \<open>Case 2: h(1,0) \<noteq> (1,0). Rotate to reduce to Case 1.\<close>
  \<comment> \<open>Derive contradiction via case split on h(1,0) = (1,0).\<close>
  \<comment> \<open>Remove hh_star_nontrivial — use antipode_preserving_basepoint_nontrivial directly in case split.\<close>
  \<comment> \<open>Helper: for any loop f at (1,0), h\<circ>f \<simeq> const_{h(1,0)} at h(1,0).
     This is proved via homotopy_induced_basepoint_change + path algebra.\<close>
  have hh_trivial_at_h10: "\<And>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f \<Longrightarrow>
      top1_path_homotopic_on top1_S1 top1_S1_topology (h (1, 0)) (h (1, 0))
          (h \<circ> f) (top1_constant_path (h (1, 0)))"
  proof -
    fix f assume hf: "top1_is_loop_on top1_S1 top1_S1_topology (1::real, 0::real) f"
    obtain c where hcS1: "c \<in> top1_S1"
        and hhom: "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h (\<lambda>_. c)"
      using hnul unfolding top1_nulhomotopic_on_def by (by100 blast)
    obtain H where hHcont: "top1_continuous_map_on (top1_S1 \<times> I_set)
            (product_topology_on top1_S1_topology I_top) top1_S1 top1_S1_topology H"
        and hH0: "\<forall>x\<in>top1_S1. H (x, 0) = h x"
        and hH1: "\<forall>x\<in>top1_S1. H (x, 1) = c"
      using hhom unfolding top1_homotopic_on_def by (by100 blast)
    have hTS1: "is_topology_on top1_S1 top1_S1_topology"
      unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF
            product_topology_on_is_topology_on[OF
              top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
              simplified]]) simp
    have h10S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    have hH1': "\<forall>x\<in>top1_S1. H (x, 1) = (\<lambda>_. c) x" using hH1 by (by100 simp)
    note hbc = homotopy_induced_basepoint_change[OF hTS1 hTS1 hHcont hH0 hH1' hf h10S1]
    have hbc': "top1_loop_equiv_on top1_S1 top1_S1_topology (h (1, 0)) (h \<circ> f)
        (top1_basepoint_change_on top1_S1 top1_S1_topology c (h (1, 0))
           (top1_path_reverse (\<lambda>t. H ((1, 0), t))) (top1_constant_path c))"
    proof -
      have "(\<lambda>_. c) \<circ> f = top1_constant_path c"
        by (rule ext) (simp add: top1_constant_path_def comp_def)
      thus ?thesis using hbc by simp
    qed
    have hbc_is_const: "top1_loop_equiv_on top1_S1 top1_S1_topology (h (1, 0))
        (top1_basepoint_change_on top1_S1 top1_S1_topology c (h (1, 0))
           (top1_path_reverse (\<lambda>t. H ((1, 0), t))) (top1_constant_path c))
        (top1_constant_path (h (1, 0)))"
    proof -
      let ?\<alpha> = "\<lambda>t. H ((1::real, 0::real), t)"
      have h\<alpha>_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology ?\<alpha>"
      proof -
        have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        have hp1: "pi1 \<circ> (\<lambda>t. ((1::real,0::real),t)) = (\<lambda>_. (1::real,0::real))"
          unfolding pi1_def by (rule ext) simp
        have hp2: "pi2 \<circ> (\<lambda>t. ((1::real,0::real),t)) = id"
          unfolding pi2_def by (rule ext) simp
        have hpair: "top1_continuous_map_on I_set I_top (top1_S1 \<times> I_set)
                       (product_topology_on top1_S1_topology I_top) (\<lambda>t. ((1::real, 0::real), t))"
          using iffD2[OF Theorem_18_4[OF hTI hTS1 hTI]]
                top1_continuous_map_on_const[OF hTI hTS1 h10S1, folded hp1]
                top1_continuous_map_on_id[OF hTI, folded hp2]
          by (by100 blast)
        show ?thesis using top1_continuous_map_on_comp[OF hpair hHcont] by (simp add: comp_def)
      qed
      have h\<alpha>_path: "top1_is_path_on top1_S1 top1_S1_topology (h (1, 0)) c ?\<alpha>"
        unfolding top1_is_path_on_def using h\<alpha>_cont
        by (auto simp: hH0[rule_format, OF h10S1] hH1[rule_format, OF h10S1])
      have hra: "top1_is_path_on top1_S1 top1_S1_topology c (h (1, 0)) (top1_path_reverse ?\<alpha>)"
        by (rule top1_path_reverse_is_path[OF h\<alpha>_path])
      have hconst_c: "top1_is_loop_on top1_S1 top1_S1_topology c (top1_constant_path c)"
        by (rule top1_constant_path_is_loop[OF hTS1 hcS1])
      have hbc_def: "top1_basepoint_change_on top1_S1 top1_S1_topology c (h (1, 0))
          (top1_path_reverse ?\<alpha>) (top1_constant_path c)
        = top1_path_product ?\<alpha> (top1_path_product (top1_constant_path c) (top1_path_reverse ?\<alpha>))"
        unfolding top1_basepoint_change_on_def top1_path_reverse_twice by (rule refl)
      have hchain: "top1_path_homotopic_on top1_S1 top1_S1_topology (h (1, 0)) (h (1, 0))
          (top1_basepoint_change_on top1_S1 top1_S1_topology c (h (1, 0))
             (top1_path_reverse ?\<alpha>) (top1_constant_path c))
          (top1_constant_path (h (1, 0)))"
        using Lemma_51_1_path_homotopic_trans[OF hTS1
            path_homotopic_product_right[OF hTS1 Theorem_51_2_left_identity[OF hTS1 hra] h\<alpha>_path,
              unfolded hbc_def[symmetric]]
            Theorem_51_2_invgerse_left[OF hTS1 h\<alpha>_path]] .
      have hh10S1: "h (1, 0) \<in> top1_S1"
        using assms(1) h10S1 unfolding top1_continuous_map_on_def by (by100 blast)
      show ?thesis unfolding top1_loop_equiv_on_def
        using top1_basepoint_change_is_loop[OF hTS1 hra hconst_c]
              top1_constant_path_is_loop[OF hTS1 hh10S1]
              hchain by (by100 blast)
    qed
    have hresult: "top1_loop_equiv_on top1_S1 top1_S1_topology (h (1, 0)) (h \<circ> f)
        (top1_constant_path (h (1, 0)))"
      by (rule top1_loop_equiv_on_trans[OF hTS1 hbc' hbc_is_const])
    show "top1_path_homotopic_on top1_S1 top1_S1_topology (h (1, 0)) (h (1, 0))
        (h \<circ> f) (top1_constant_path (h (1, 0)))"
      using hresult unfolding top1_loop_equiv_on_def by (by100 blast)
  qed
  \<comment> \<open>Case split: h(1,0) = (1,0) gives direct contradiction;
     h(1,0) \<noteq> (1,0) needs WLOG rotation.\<close>
  show False
  proof (cases "h (1, 0) = (1::real, 0::real)")
    case True
    have hh_triv: "\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
        \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
              (h \<circ> f) (top1_constant_path (1, 0))"
      using hh_trivial_at_h10 True by simp
    have hh_nontriv: "\<not> (\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
        \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
              (h \<circ> f) (top1_constant_path (1, 0)))"
      by (rule antipode_preserving_basepoint_nontrivial[OF assms(1,2) True])
    thus False using hh_triv by (by100 blast)
  next
    case False
    \<comment> \<open>h(1,0) \<noteq> (1,0): WLOG rotation. Let \<rho> rotate h(1,0) to (1,0).\<close>
    \<comment> \<open>h(1,0) \<in> S^1, so h(1,0) = (cos \<theta>, sin \<theta>) for some \<theta>.
       Rotation by -\<theta>: \<rho>(x,y) = (x cos\<theta> + y sin\<theta>, -x sin\<theta> + y cos\<theta>).
       Then \<rho>(h(1,0)) = (cos^2\<theta> + sin^2\<theta>, 0) = (1,0).\<close>
    have h10_S1: "(1::real,0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    have hh10: "h (1,0) \<in> top1_S1"
      using assms(1) h10_S1 unfolding top1_continuous_map_on_def by (by100 blast)
    let ?a = "fst (h (1, 0))" and ?b = "snd (h (1, 0))"
    have hab_S1: "?a^2 + ?b^2 = 1" using hh10 unfolding top1_S1_def by (by100 auto)
    \<comment> \<open>Define rotation \<rho>(x,y) = (ax+by, -bx+ay).\<close>
    let ?\<rho> = "\<lambda>(x::real,y::real). (?a*x + ?b*y, -?b*x + ?a*y)"
    have hrho_10: "?\<rho> (h (1,0)) = (1, 0)"
      using hab_S1 by (simp add: prod_eq_iff case_prod_beta power2_eq_square algebra_simps)
    \<comment> \<open>\<rho> commutes with negation: \<rho>(-x,-y) = -\<rho>(x,y).\<close>
    have hrho_neg: "\<And>x y. ?\<rho> (-x,-y) = (- fst (?\<rho> (x,y)), - snd (?\<rho> (x,y)))"
      by (by100 simp)
    \<comment> \<open>\<rho>\<circ>h is continuous, antipode-preserving, nulhomotopic.\<close>
    have "?\<rho> \<circ> h = (\<lambda>z. ?\<rho> (h z))" by (rule ext) (by100 simp)
    \<comment> \<open>\<rho> maps S^1 to S^1 and is continuous.\<close>
    have hrho_S1: "\<And>p. p \<in> top1_S1 \<Longrightarrow> ?\<rho> p \<in> top1_S1"
    proof -
      fix p assume hp: "p \<in> top1_S1"
      have hxy: "(fst p)^2 + (snd p)^2 = 1" using hp unfolding top1_S1_def by (by100 auto)
      have "(?a * fst p + ?b * snd p)^2 + (-?b * fst p + ?a * snd p)^2
          = (?a^2 + ?b^2) * ((fst p)^2 + (snd p)^2)"
        by (simp add: power2_eq_square algebra_simps)
      also have "\<dots> = 1" using hab_S1 hxy by (by100 simp)
      finally show "?\<rho> p \<in> top1_S1" unfolding top1_S1_def by (simp add: case_prod_beta)
    qed
    have hrho_cont_univ: "continuous_on UNIV ?\<rho>"
    proof -
      have "continuous_on UNIV (\<lambda>p::real\<times>real. (?a * fst p + ?b * snd p, -?b * fst p + ?a * snd p))"
        by (intro continuous_on_Pair continuous_on_add continuous_on_mult
            continuous_on_minus continuous_on_const continuous_on_fst continuous_on_snd continuous_on_id)
      moreover have "(\<lambda>p::real\<times>real. (?a * fst p + ?b * snd p, -?b * fst p + ?a * snd p)) = ?\<rho>"
        by (rule ext) (simp add: case_prod_beta)
      ultimately show ?thesis by (by100 metis)
    qed
    have hrho_top1: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology ?\<rho>"
    proof -
      have "top1_continuous_map_on top1_S1
          (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1)
          top1_S1 (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1) ?\<rho>"
        using top1_continuous_map_on_subspace_open_sets[OF hrho_S1 hrho_cont_univ]
        by (simp add: product_topology_on_open_sets[where ?'a=real and ?'b=real])
      thus ?thesis unfolding top1_S1_topology_def
        by (simp add: product_topology_on_open_sets[where ?'a=real and ?'b=real])
    qed
    have hrh_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (?\<rho> \<circ> h)"
      by (rule top1_continuous_map_on_comp[OF assms(1) hrho_top1])
    have hrh_anti: "top1_antipode_preserving_S1 (?\<rho> \<circ> h)"
      unfolding top1_antipode_preserving_S1_def
    proof (intro allI)
      fix x y
      have "h (-x, -y) = (- fst (h (x,y)), - snd (h (x,y)))"
        using assms(2) unfolding top1_antipode_preserving_S1_def by (by100 blast)
      thus "(?\<rho> \<circ> h) (-x, -y) = (- fst ((?\<rho> \<circ> h) (x, y)), - snd ((?\<rho> \<circ> h) (x, y)))"
        by (simp add: comp_def case_prod_beta algebra_simps)
    qed
    have hrh_nul: "top1_nulhomotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (?\<rho> \<circ> h)"
    proof -
      obtain c where hc: "c \<in> top1_S1"
          and hhom: "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology h (\<lambda>_. c)"
        using hnul unfolding top1_nulhomotopic_on_def by (by100 blast)
      have hrhc_S1: "?\<rho> c \<in> top1_S1"
        using hrho_S1[OF hc] by (by100 simp)
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF
              product_topology_on_is_topology_on[OF
                top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
                simplified]]) simp
      \<comment> \<open>Extract homotopy H from hhom, compose with \<rho>.\<close>
      obtain H where hHcont: "top1_continuous_map_on (top1_S1 \<times> I_set)
            (product_topology_on top1_S1_topology I_top) top1_S1 top1_S1_topology H"
          and hH0: "\<forall>x\<in>top1_S1. H (x, 0) = h x"
          and hH1: "\<forall>x\<in>top1_S1. H (x, 1) = c"
        using hhom unfolding top1_homotopic_on_def by (by100 blast)
      have hrH_cont: "top1_continuous_map_on (top1_S1 \<times> I_set)
          (product_topology_on top1_S1_topology I_top) top1_S1 top1_S1_topology (?\<rho> \<circ> H)"
        by (rule top1_continuous_map_on_comp[OF hHcont hrho_top1])
      have hconst_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (\<lambda>_. ?\<rho> c)"
        by (rule top1_continuous_map_on_const[OF hTS1 hTS1 hrhc_S1])
      have hrhH0: "\<forall>x\<in>top1_S1. (?\<rho> \<circ> H) (x, 0) = (?\<rho> \<circ> h) x"
        using hH0 by (by100 simp)
      have hrhH1: "\<forall>x\<in>top1_S1. (?\<rho> \<circ> H) (x, 1) = ?\<rho> c"
        using hH1 by (by100 simp)
      have "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology
          (?\<rho> \<circ> h) (\<lambda>_. ?\<rho> c)"
        unfolding top1_homotopic_on_def
        apply (intro conjI exI[of _ "?\<rho> \<circ> H"])
        apply (rule hrh_cont)
        apply (rule hconst_cont)
        apply (rule hrH_cont)
        using hrhH0 apply (by100 simp)
        using hrhH1 apply (by100 simp)
        done
      thus ?thesis unfolding top1_nulhomotopic_on_def using hrhc_S1 by (by100 blast)
    qed
    have hrh_10: "(?\<rho> \<circ> h) (1, 0) = (1, 0)"
      using hrho_10 by (by100 simp)
    \<comment> \<open>Apply the same argument as the True case to \<rho>\<circ>h.\<close>
    \<comment> \<open>Step 1: (\<rho>\<circ>h)\<circ>f \<simeq> const for all loops f at (1,0) — from nulhomotopy + basepoint change.\<close>
    have hrh_trivial: "\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
        \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
              ((?\<rho> \<circ> h) \<circ> f) (top1_constant_path (1, 0))"
    proof (intro allI impI)
      fix f assume hf: "top1_is_loop_on top1_S1 top1_S1_topology (1::real, 0::real) f"
      show "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
          ((?\<rho> \<circ> h) \<circ> f) (top1_constant_path (1, 0))"
        by (rule nulhomotopic_trivializes_loops[OF hrh_cont hrh_nul hrh_10 hf])
    qed
    \<comment> \<open>Step 2: (\<rho>\<circ>h)_* is nontrivial (covering theory: antipode-preserving \<Rightarrow> induced map \<times>2).\<close>
    have hrh_star_nontrivial: "\<not> (\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
        \<longrightarrow> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
              ((?\<rho> \<circ> h) \<circ> f) (top1_constant_path (1, 0)))"
      by (rule antipode_preserving_basepoint_nontrivial[OF hrh_cont hrh_anti hrh_10])
    show False using hrh_trivial hrh_star_nontrivial by (by100 blast)
  qed
qed

(** from *\<S>57 Theorem 57.3: Borsuk-Ulam theorem for S^2.
    Munkres' proof: by contradiction. If f(x) \<ne> f(-x) for all x \<in> S^2, then
    g(x) = (f(x) - f(-x))/||f(x) - f(-x)|| is continuous antipode-preserving
    S^2 \<rightarrow> S^1, contradicting Theorem 57.2. **)
theorem Theorem_57_3_BorsukUlam:
  fixes f :: "real \<times> real \<times> real \<Rightarrow> real \<times> real"
  assumes hf: "top1_continuous_map_on {p. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1}
    (subspace_topology UNIV
      (product_topology_on top1_open_sets
        (product_topology_on top1_open_sets top1_open_sets))
      {p. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1})
    UNIV (product_topology_on top1_open_sets top1_open_sets) f"
  shows "\<exists>x::real\<times>real\<times>real. fst x ^ 2 + fst (snd x) ^ 2 + snd (snd x) ^ 2 = 1
    \<and> f x = f (- fst x, - fst (snd x), - snd (snd x))"
proof (rule ccontr)
  assume hno: "\<not> (\<exists>x::real\<times>real\<times>real. fst x ^ 2 + fst (snd x) ^ 2 + snd (snd x) ^ 2 = 1
    \<and> f x = f (- fst x, - fst (snd x), - snd (snd x)))"
  \<comment> \<open>By assumption, f(x) \<noteq> f(-x) for all x \<in> S^2.\<close>
  let ?S2 = "{p::real\<times>real\<times>real. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1}"
  let ?neg = "\<lambda>x::real\<times>real\<times>real. (- fst x, - fst (snd x), - snd (snd x))"
  have hfne: "\<forall>x\<in>?S2. f x \<noteq> f (?neg x)" using hno by blast
  \<comment> \<open>Define g: S^2 \<rightarrow> S^1 by g(x) = (f(x) - f(-x)) / ||f(x) - f(-x)||.\<close>
  let ?diff = "\<lambda>x. (fst (f x) - fst (f (?neg x)), snd (f x) - snd (f (?neg x)))"
  let ?norm = "\<lambda>x. sqrt ((fst (?diff x))^2 + (snd (?diff x))^2)"
  let ?g = "\<lambda>x. (fst (?diff x) / ?norm x, snd (?diff x) / ?norm x)"
  \<comment> \<open>g is continuous (rational functions with nonzero denominator).\<close>
  have hg_cont: "top1_continuous_map_on ?S2
      (subspace_topology UNIV (product_topology_on top1_open_sets
        (product_topology_on top1_open_sets top1_open_sets)) ?S2)
      top1_S1 top1_S1_topology ?g"
  proof -
    \<comment> \<open>g maps S^2 into S^1.\<close>
    have hg_range: "\<And>x. x \<in> ?S2 \<Longrightarrow> ?g x \<in> top1_S1"
    proof -
      fix x assume hx: "x \<in> ?S2"
      have hne: "f x \<noteq> f (?neg x)" using hfne hx by (by100 blast)
      hence "fst (?diff x) \<noteq> 0 \<or> snd (?diff x) \<noteq> 0"
      proof -
        have "fst (f x) \<noteq> fst (f (?neg x)) \<or> snd (f x) \<noteq> snd (f (?neg x))"
          using hne by (auto simp: prod_eq_iff)
        thus ?thesis by auto
      qed
      hence hd_pos: "(fst (?diff x))^2 + (snd (?diff x))^2 > 0"
      proof -
        assume hne: "fst (?diff x) \<noteq> 0 \<or> snd (?diff x) \<noteq> 0"
        have h1: "\<And>a::real. a \<noteq> 0 \<Longrightarrow> a^2 > 0" by (by100 auto)
        have h2: "\<And>a::real. a^2 \<ge> 0" by (by100 auto)
        show ?thesis using hne h1[of "fst (?diff x)"] h1[of "snd (?diff x)"] h2[of "fst (?diff x)"] h2[of "snd (?diff x)"]
          by linarith
      qed
      have hn_pos: "?norm x > 0" using hd_pos by simp
      have "(fst (?g x))^2 + (snd (?g x))^2 = 1"
      proof -
        have hne: "?norm x \<noteq> 0" using hn_pos by linarith
        have hn_sq: "(?norm x)^2 = (fst (?diff x))^2 + (snd (?diff x))^2"
          using hn_pos by (simp add: real_sqrt_pow2)
        have "fst (?g x) ^ 2 + snd (?g x) ^ 2 =
            (fst (?diff x))^2 / (?norm x)^2 + (snd (?diff x))^2 / (?norm x)^2"
          by (simp add: power_divide)
        also have "\<dots> = ((fst (?diff x))^2 + (snd (?diff x))^2) / (?norm x)^2"
          by (simp add: add_divide_distrib[symmetric])
        also have "\<dots> = 1" using hn_sq hd_pos hne by simp
        finally show ?thesis .
      qed
      thus "?g x \<in> top1_S1" unfolding top1_S1_def by simp
    qed
    \<comment> \<open>g is continuous on S^2 and maps into S^1. Bridge to top1_continuous_map_on.\<close>
    have hg_cont_on: "continuous_on ?S2 ?g"
    proof -
      have hf_cont: "continuous_on ?S2 f"
      proof (rule iffD2[OF continuous_on_open_invariant])
        show "\<forall>B. open B \<longrightarrow> (\<exists>A. open A \<and> A \<inter> ?S2 = f -` B \<inter> ?S2)"
        proof (intro allI impI)
          fix B :: "(real \<times> real) set" assume hBo: "open B"
          have hB_os: "B \<in> (top1_open_sets :: (real \<times> real) set set)"
            using hBo unfolding top1_open_sets_def by simp
          have hB_prod: "B \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
            using hB_os product_topology_on_open_sets_real2 by simp
          have hpre: "{x \<in> ?S2. f x \<in> B} \<in> subspace_topology UNIV
              (product_topology_on top1_open_sets (product_topology_on top1_open_sets top1_open_sets)) ?S2"
            using hf hB_prod unfolding top1_continuous_map_on_def by (by100 blast)
          then obtain W where hW: "W \<in> product_topology_on top1_open_sets
              (product_topology_on top1_open_sets top1_open_sets)"
              and hWeq: "{x \<in> ?S2. f x \<in> B} = ?S2 \<inter> W"
            unfolding subspace_topology_def by (by100 blast)
          have "open W"
          proof -
            have "product_topology_on (top1_open_sets::real set set)
                (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set))
              = (top1_open_sets :: (real \<times> real \<times> real) set set)"
              using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
              by (simp add: product_topology_on_open_sets)
            hence "W \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)" using hW by simp
            thus "open W" unfolding top1_open_sets_def by simp
          qed
          moreover have "W \<inter> ?S2 = f -` B \<inter> ?S2" using hWeq by (by100 blast)
          ultimately show "\<exists>A. open A \<and> A \<inter> ?S2 = f -` B \<inter> ?S2" by (by100 blast)
        qed
      qed
      have hneg_S2: "\<And>x. x \<in> ?S2 \<Longrightarrow> ?neg x \<in> ?S2"
        by (by100 auto)
      have hfneg_cont: "continuous_on ?S2 (\<lambda>x. f (?neg x))"
      proof (rule continuous_on_compose2[OF hf_cont])
        show "continuous_on ?S2 ?neg" by (intro continuous_intros)
        show "?neg ` ?S2 \<subseteq> ?S2" using hneg_S2 by (by100 auto)
      qed
      have hdiff_fst_cont: "continuous_on ?S2 (\<lambda>x. fst (?diff x))"
        using hf_cont hfneg_cont by (intro continuous_intros)
      have hdiff_snd_cont: "continuous_on ?S2 (\<lambda>x. snd (?diff x))"
        using hf_cont hfneg_cont by (intro continuous_intros)
      have hnorm_pos: "\<And>x. x \<in> ?S2 \<Longrightarrow> ?norm x > 0"
      proof -
        fix x assume "x \<in> ?S2"
        have "f x \<noteq> f (?neg x)" using hfne \<open>x \<in> ?S2\<close> by (by100 blast)
        hence "fst (?diff x) \<noteq> 0 \<or> snd (?diff x) \<noteq> 0"
        proof -
          have "fst (f x) \<noteq> fst (f (?neg x)) \<or> snd (f x) \<noteq> snd (f (?neg x))"
            using \<open>f x \<noteq> f (?neg x)\<close> by (auto simp: prod_eq_iff)
          thus ?thesis by auto
        qed
        hence "(fst (?diff x))^2 + (snd (?diff x))^2 > 0"
        proof -
          assume "fst (?diff x) \<noteq> 0 \<or> snd (?diff x) \<noteq> 0"
          have h1: "\<And>a::real. a \<noteq> 0 \<Longrightarrow> a^2 > 0" by (by100 auto)
          have h2: "\<And>a::real. a^2 \<ge> 0" by (by100 auto)
          show ?thesis using \<open>fst (?diff x) \<noteq> 0 \<or> snd (?diff x) \<noteq> 0\<close>
            h1[of "fst (?diff x)"] h1[of "snd (?diff x)"]
            h2[of "fst (?diff x)"] h2[of "snd (?diff x)"] by linarith
        qed
        thus "?norm x > 0" by simp
      qed
      have hnorm_ne: "\<And>x. x \<in> ?S2 \<Longrightarrow> ?norm x \<noteq> 0"
      proof -
        fix x assume "x \<in> ?S2"
        hence "?norm x > 0" by (rule hnorm_pos)
        thus "?norm x \<noteq> 0" by linarith
      qed
      \<comment> \<open>Norm continuous: sqrt(d1^2+d2^2) where d1,d2 continuous.\<close>
      have hfst_mult: "continuous_on ?S2 (\<lambda>x. fst (?diff x) * fst (?diff x))"
        using continuous_on_mult[OF hdiff_fst_cont hdiff_fst_cont] .
      have hsnd_mult: "continuous_on ?S2 (\<lambda>x. snd (?diff x) * snd (?diff x))"
        using continuous_on_mult[OF hdiff_snd_cont hdiff_snd_cont] .
      have hsum_cont: "continuous_on ?S2 (\<lambda>x. fst (?diff x) * fst (?diff x) + snd (?diff x) * snd (?diff x))"
        using continuous_on_add[OF hfst_mult hsnd_mult] .
      have hnorm_cont: "continuous_on ?S2 ?norm"
        using continuous_on_real_sqrt[OF hsum_cont]
        by (simp add: power2_eq_square[symmetric])
      \<comment> \<open>g = (d1/norm, d2/norm) continuous via continuous_on_divide.\<close>
      have hfst_div: "continuous_on ?S2 (\<lambda>x. fst (?diff x) / ?norm x)"
        by (rule continuous_on_divide[OF hdiff_fst_cont hnorm_cont]) (use hnorm_ne in auto)
      have hsnd_div: "continuous_on ?S2 (\<lambda>x. snd (?diff x) / ?norm x)"
        by (rule continuous_on_divide[OF hdiff_snd_cont hnorm_cont]) (use hnorm_ne in auto)
      have "continuous_on ?S2 (\<lambda>x. (fst (?diff x) / ?norm x, snd (?diff x) / ?norm x))"
        by (rule continuous_on_Pair[OF hfst_div hsnd_div])
      thus "continuous_on ?S2 ?g" by simp
    qed
    \<comment> \<open>Bridge to top1_continuous_map_on via subspace_open_sets_on.\<close>
    \<comment> \<open>Bridge: subspace_open_sets_on gives top1_continuous_map_on with top1_open_sets.
       product_topology_on = top1_open_sets for R^2 and R^3 (by product_topology_on_open_sets).\<close>
    have hprod_R3: "product_topology_on (top1_open_sets::real set set)
        (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set))
      = (top1_open_sets :: (real \<times> real \<times> real) set set)"
      using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
      by (simp add: product_topology_on_open_sets)
    have hprod_R2: "product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set)
      = (top1_open_sets :: (real \<times> real) set set)"
      by (rule product_topology_on_open_sets_real2)
    have hS2_top_eq: "subspace_topology UNIV (product_topology_on top1_open_sets
        (product_topology_on top1_open_sets top1_open_sets)) ?S2
      = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) ?S2"
      unfolding hprod_R3 by simp
    have hS1_top_eq: "top1_S1_topology = subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1"
      unfolding top1_S1_topology_def hprod_R2 by simp
    show ?thesis
      using top1_continuous_map_on_subspace_open_sets_on[OF hg_range hg_cont_on]
      unfolding hS2_top_eq[symmetric] hS1_top_eq[symmetric] by simp
  qed
  \<comment> \<open>g is antipode-preserving: g(-x) = -g(x).\<close>
  have hg_anti: "\<forall>x\<in>?S2. ?g (?neg x) = (- fst (?g x), - snd (?g x))"
  proof (intro ballI)
    fix x :: "real \<times> real \<times> real" assume hx: "x \<in> ?S2"
    have hnegneg: "?neg (?neg x) = x" by (simp add: prod_eq_iff)
    have h1: "fst (?diff (?neg x)) = - fst (?diff x)" by (simp add: hnegneg)
    have h2: "snd (?diff (?neg x)) = - snd (?diff x)" by (simp add: hnegneg)
    have hpc1: "(fst (f (?neg x)) - fst (f x))\<^sup>2 = (fst (f x) - fst (f (?neg x)))\<^sup>2"
      by (rule power2_commute)
    have hpc2: "(snd (f (?neg x)) - snd (f x))\<^sup>2 = (snd (f x) - snd (f (?neg x)))\<^sup>2"
      by (rule power2_commute)
    have h3: "?norm (?neg x) = ?norm x" by (simp add: hnegneg hpc1 hpc2)
    have hd1: "fst (f (?neg x)) - fst (f x) = - (fst (f x) - fst (f (?neg x)))"
      by (by100 linarith)
    have hd2: "snd (f (?neg x)) - snd (f x) = - (snd (f x) - snd (f (?neg x)))"
      by (by100 linarith)
    show "?g (?neg x) = (- fst (?g x), - snd (?g x))"
      by (simp del: minus_diff_eq add: prod_eq_iff hnegneg h3 hd1 hd2)
  qed
  \<comment> \<open>Restrict g to equator S^1 \<hookrightarrow> S^2: h(x,y) = g(x,y,0). h is antipode-preserving S^1\<rightarrow>S^1.\<close>
  let ?embed = "\<lambda>(x::real, y::real). (x, y, 0::real)"
  let ?h = "?g \<circ> ?embed"
  \<comment> \<open>h is continuous S^1 \<rightarrow> S^1.\<close>
  have hh_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology ?h"
  proof -
    \<comment> \<open>embed maps S^1 into S^2: (x,y) \<in> S^1 \<Longrightarrow> (x,y,0) \<in> S^2.\<close>
    have hembed_range: "\<And>p. p \<in> top1_S1 \<Longrightarrow> ?embed p \<in> ?S2"
    proof -
      fix p assume hp: "p \<in> top1_S1"
      have "fst p ^ 2 + snd p ^ 2 = 1" using hp unfolding top1_S1_def by (by100 auto)
      thus "?embed p \<in> ?S2" by (cases p) simp
    qed
    \<comment> \<open>embed is continuous on S^1.\<close>
    have hembed_cont: "continuous_on top1_S1 ?embed"
    proof -
      have hc: "continuous_on top1_S1 (\<lambda>p::real\<times>real. (fst p, snd p, 0::real))"
        by (intro continuous_on_Pair continuous_on_fst continuous_on_snd continuous_on_const continuous_on_id)
      have heq: "(\<lambda>p::real\<times>real. (fst p, snd p, 0::real)) = ?embed"
        by (by100 auto)
      show ?thesis using hc unfolding heq .
    qed
    \<comment> \<open>Bridge to top1_continuous_map_on via subspace topologies.\<close>
    have hprod_R3: "product_topology_on (top1_open_sets::real set set)
        (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set))
      = (top1_open_sets :: (real \<times> real \<times> real) set set)"
      using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
      by (simp add: product_topology_on_open_sets)
    have hprod_R2: "product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set)
      = (top1_open_sets :: (real \<times> real) set set)"
      by (rule product_topology_on_open_sets_real2)
    have hembed_cmo: "top1_continuous_map_on top1_S1
        (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1)
        ?S2 (subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) ?S2)
        ?embed"
      by (rule top1_continuous_map_on_subspace_open_sets_on[OF hembed_range hembed_cont])
    have hS1_top_eq: "top1_S1_topology = subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1"
      unfolding top1_S1_topology_def hprod_R2 by (by100 simp)
    have hS2_top_eq: "subspace_topology UNIV (product_topology_on top1_open_sets
        (product_topology_on top1_open_sets top1_open_sets)) ?S2
      = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) ?S2"
      unfolding hprod_R3 by (by100 simp)
    have hembed_top: "top1_continuous_map_on top1_S1 top1_S1_topology ?S2
        (subspace_topology UNIV (product_topology_on top1_open_sets
          (product_topology_on top1_open_sets top1_open_sets)) ?S2) ?embed"
      using hembed_cmo unfolding hS1_top_eq hS2_top_eq by (by100 simp)
    show ?thesis by (rule top1_continuous_map_on_comp[OF hembed_top hg_cont])
  qed
  \<comment> \<open>h is antipode-preserving.\<close>
  have hg_anti_all: "\<And>p. ?g (?neg p) = (- fst (?g p), - snd (?g p))"
  proof -
    fix p :: "real \<times> real \<times> real"
    obtain a b c where hp: "p = (a, b, c)" by (cases p, cases "snd p") auto
    \<comment> \<open>Key: neg(neg(p)) = p, so diff(neg(p)) = f(neg(p))-f(neg(neg(p))) = f(neg(p))-f(p) = -diff(p).\<close>
    have hnn: "?neg (?neg p) = p" using hp by simp
    have hd1: "fst (?diff (?neg p)) = - fst (?diff p)" using hnn by simp
    have hd2: "snd (?diff (?neg p)) = - snd (?diff p)" using hnn by simp
    \<comment> \<open>Norm preserved: (-a)^2 = a^2, so norm(neg p) = norm(p).\<close>
    have hpc1: "(fst (f (?neg p)) - fst (f p))\<^sup>2 = (fst (f p) - fst (f (?neg p)))\<^sup>2"
      by (rule power2_commute)
    have hpc2: "(snd (f (?neg p)) - snd (f p))\<^sup>2 = (snd (f p) - snd (f (?neg p)))\<^sup>2"
      by (rule power2_commute)
    have h3: "?norm (?neg p) = ?norm p"
      using hnn hpc1 hpc2 by (by100 simp)
    \<comment> \<open>Raw difference rewrites for simp.\<close>
    have hd1a: "fst (f (?neg p)) - fst (f p) = - (fst (f p) - fst (f (?neg p)))"
      by (by100 linarith)
    have hd2a: "snd (f (?neg p)) - snd (f p) = - (snd (f p) - snd (f (?neg p)))"
      by (by100 linarith)
    show "?g (?neg p) = (- fst (?g p), - snd (?g p))"
      by (simp del: minus_diff_eq add: prod_eq_iff hnn h3 hd1a hd2a)
  qed
  have hh_anti: "top1_antipode_preserving_S1 ?h"
    unfolding top1_antipode_preserving_S1_def comp_def
  proof (intro allI)
    fix x y :: real
    have "?embed (-x, -y) = ?neg (?embed (x, y))" by simp
    thus "?g (?embed (-x, -y)) = (- fst (?g (?embed (x, y))), - snd (?g (?embed (x, y))))"
      using hg_anti_all[of "?embed (x, y)"] by simp
  qed
  \<comment> \<open>By Theorem 57.1: h is not nulhomotopic.\<close>
  have hh_not_nul: "\<not> top1_nulhomotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology ?h"
    by (rule Theorem_57_1[OF hh_cont hh_anti])
  \<comment> \<open>But h IS nulhomotopic: g extends h over the upper hemisphere E \<cong> B^2.
     Since E is contractible, g|E \<simeq> const. Restricting to S^1 = \<partial>E gives h \<simeq> const.\<close>
  have hh_nul: "top1_nulhomotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology ?h"
  proof -
    \<comment> \<open>Use Lemma 55.3 backward: h extends to k: B^2 \<rightarrow> S^1 via the upper hemisphere.
       Define \<phi>(x,y) = (x, y, sqrt(1-x^2-y^2)) mapping B^2 into S^2.
       Then k = g \<circ> \<phi> : B^2 \<rightarrow> S^1, and k|S^1 = g(x,y,0) = h(x,y).\<close>
    let ?\<phi> = "\<lambda>p::real\<times>real. (fst p, snd p, sqrt (1 - fst p ^ 2 - snd p ^ 2))"
    let ?k = "?g \<circ> ?\<phi>"
    have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    proof -
      have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
          (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
        using product_topology_on_is_topology_on[OF
              top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
      show ?thesis unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
    qed
    \<comment> \<open>\<phi> maps B^2 into S^2: x^2 + y^2 + (sqrt(1-x^2-y^2))^2 = 1.\<close>
    have h\<phi>_S2: "\<And>p. p \<in> top1_B2 \<Longrightarrow> ?\<phi> p \<in> ?S2"
    proof -
      fix p :: "real \<times> real" assume hp: "p \<in> top1_B2"
      have hle: "fst p ^ 2 + snd p ^ 2 \<le> 1" using hp unfolding top1_B2_def by (by100 auto)
      have hge: "1 - fst p ^ 2 - snd p ^ 2 \<ge> 0" using hle by (by100 linarith)
      have "(sqrt (1 - fst p ^ 2 - snd p ^ 2)) ^ 2 = 1 - fst p ^ 2 - snd p ^ 2"
        by (rule real_sqrt_pow2[OF hge])
      hence "fst p ^ 2 + snd p ^ 2 + (sqrt (1 - fst p ^ 2 - snd p ^ 2)) ^ 2 = 1"
        by (by100 linarith)
      thus "?\<phi> p \<in> ?S2" by simp
    qed
    \<comment> \<open>\<phi> is continuous on B^2 (polynomial + sqrt of nonneg).\<close>
    have h\<phi>_cont: "continuous_on top1_B2 ?\<phi>"
    proof -
      have hfst: "continuous_on top1_B2 (\<lambda>p::real\<times>real. fst p)" by (rule continuous_on_fst[OF continuous_on_id])
      have hsnd: "continuous_on top1_B2 (\<lambda>p::real\<times>real. snd p)" by (rule continuous_on_snd[OF continuous_on_id])
      have hfsq: "continuous_on top1_B2 (\<lambda>p. fst p ^ 2 :: real)"
        using continuous_on_power[OF hfst] by (by100 blast)
      have hssq: "continuous_on top1_B2 (\<lambda>p. snd p ^ 2 :: real)"
        using continuous_on_power[OF hsnd] by (by100 blast)
      have hdiff: "continuous_on top1_B2 (\<lambda>p. 1 - fst p ^ 2 - snd p ^ 2 :: real)"
        by (rule continuous_on_diff[OF continuous_on_diff[OF continuous_on_const hfsq] hssq])
      have hsqrt: "continuous_on top1_B2 (\<lambda>p. sqrt (1 - fst p ^ 2 - snd p ^ 2))"
        by (rule continuous_on_real_sqrt[OF hdiff])
      have hpair: "continuous_on top1_B2 (\<lambda>p::real\<times>real. (snd p, sqrt (1 - fst p ^ 2 - snd p ^ 2)))"
        by (rule continuous_on_Pair[OF hsnd hsqrt])
      show ?thesis by (rule continuous_on_Pair[OF hfst hpair])
    qed
    \<comment> \<open>k = g \<circ> \<phi> is continuous B^2 \<rightarrow> S^1.\<close>
    have hk_cont: "top1_continuous_map_on top1_B2 top1_B2_topology top1_S1 top1_S1_topology ?k"
    proof -
      \<comment> \<open>Bridge \<phi> to top1_continuous_map_on.\<close>
      have hprod_R3: "product_topology_on (top1_open_sets::real set set)
          (product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set))
        = (top1_open_sets :: (real \<times> real \<times> real) set set)"
        using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
        by (simp add: product_topology_on_open_sets)
      have hprod_R2: "product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set)
        = (top1_open_sets :: (real \<times> real) set set)"
        by (rule product_topology_on_open_sets_real2)
      have h\<phi>_cmo: "top1_continuous_map_on top1_B2
          (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_B2)
          ?S2 (subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) ?S2)
          ?\<phi>"
        by (rule top1_continuous_map_on_subspace_open_sets_on[OF h\<phi>_S2 h\<phi>_cont])
      have hB2_top_eq: "top1_B2_topology = subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_B2"
        unfolding top1_B2_topology_def hprod_R2 by (by100 simp)
      have hS2_top_eq: "subspace_topology UNIV (product_topology_on top1_open_sets
          (product_topology_on top1_open_sets top1_open_sets)) ?S2
        = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) ?S2"
        unfolding hprod_R3 by (by100 simp)
      have h\<phi>_top: "top1_continuous_map_on top1_B2 top1_B2_topology ?S2
          (subspace_topology UNIV (product_topology_on top1_open_sets
            (product_topology_on top1_open_sets top1_open_sets)) ?S2) ?\<phi>"
        using h\<phi>_cmo unfolding hB2_top_eq hS2_top_eq by (by100 simp)
      show ?thesis by (rule top1_continuous_map_on_comp[OF h\<phi>_top hg_cont])
    qed
    \<comment> \<open>Extension: k|S^1 = h. On S^1, sqrt(1-x^2-y^2) = sqrt(0) = 0, so \<phi>(x,y) = (x,y,0) = embed(x,y).\<close>
    have hext: "\<forall>x\<in>top1_S1. ?k x = ?h x"
    proof (intro ballI)
      fix p :: "real \<times> real" assume hp: "p \<in> top1_S1"
      have hS1: "fst p ^ 2 + snd p ^ 2 = 1" using hp unfolding top1_S1_def by (by100 auto)
      have "1 - fst p ^ 2 - snd p ^ 2 = 0" using hS1 by (by100 linarith)
      hence "sqrt (1 - fst p ^ 2 - snd p ^ 2) = 0" by (by100 simp)
      hence h\<phi>eq: "?\<phi> p = ?embed p" by (cases p) simp
      have "?k p = ?g (?\<phi> p)" unfolding comp_def by simp
      also have "\<dots> = ?g (?embed p)" using h\<phi>eq by simp
      also have "\<dots> = ?h p" unfolding comp_def by simp
      finally show "?k p = ?h p" .
    qed
    show ?thesis by (rule Lemma_55_3_backward[OF hh_cont hTS1 hk_cont hext])
  qed
  show False using hh_not_nul hh_nul by contradiction
qed



section \<open>\<S>58 Deformation Retracts and Homotopy Type\<close>

text \<open>A is a deformation retract of X: the identity map of X is homotopic
  to a map that carries all of X into A, with A fixed during the homotopy.\<close>
definition top1_deformation_retract_of_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_deformation_retract_of_on X TX A \<longleftrightarrow>
     A \<subseteq> X \<and>
     (\<exists>H. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H
          \<and> (\<forall>x\<in>X. H (x, 0) = x) \<and> (\<forall>x\<in>X. H (x, 1) \<in> A)
          \<and> (\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) = a))"

text \<open>Homotopy equivalence: f: X\<rightarrow>Y and g: Y\<rightarrow>X with g\<circ>f \<simeq> id_X and f\<circ>g \<simeq> id_Y.\<close>
definition top1_homotopy_equivalence_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_homotopy_equivalence_on X TX Y TY f g \<longleftrightarrow>
     top1_continuous_map_on X TX Y TY f \<and>
     top1_continuous_map_on Y TY X TX g \<and>
     top1_homotopic_on X TX X TX (g \<circ> f) (\<lambda>x. x) \<and>
     top1_homotopic_on Y TY Y TY (f \<circ> g) (\<lambda>y. y)"

text \<open>Spaces have the same homotopy type if there is a homotopy equivalence between them.\<close>
definition top1_same_homotopy_type_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> bool" where
  "top1_same_homotopy_type_on X TX Y TY \<longleftrightarrow>
     (\<exists>f g. top1_homotopy_equivalence_on X TX Y TY f g)"

text \<open>Homotopy equivalence is symmetric (swap f and g).\<close>
lemma top1_homotopy_equivalence_on_sym:
  assumes "top1_homotopy_equivalence_on X TX Y TY f g"
  shows "top1_homotopy_equivalence_on Y TY X TX g f"
  using assms unfolding top1_homotopy_equivalence_on_def by blast

text \<open>Same homotopy type is symmetric.\<close>
lemma top1_same_homotopy_type_on_sym:
  assumes "top1_same_homotopy_type_on X TX Y TY"
  shows "top1_same_homotopy_type_on Y TY X TX"
  using assms top1_homotopy_equivalence_on_sym
  unfolding top1_same_homotopy_type_on_def by blast

(** from \<S>58 Lemma 58.1: if h, k: (X, x_0) \<rightarrow> (Y, y_0) are homotopic with basepoint
    fixed during the homotopy, then h_* = k_* on fundamental groups. **)
lemma Lemma_58_1_basepoint_fixed:
  assumes hTX: "is_topology_on X TX"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hk: "top1_continuous_map_on X TX Y TY k"
      and hhx0: "h x0 = y0" and hkx0: "k x0 = y0"
      and hH: "\<exists>H. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY H
              \<and> (\<forall>x\<in>X. H (x, 0) = h x) \<and> (\<forall>x\<in>X. H (x, 1) = k x)
              \<and> (\<forall>t\<in>I_set. H (x0, t) = y0)"
      and hf: "top1_is_loop_on X TX x0 f"
  shows "top1_path_homotopic_on Y TY y0 y0
           (top1_induced_homomorphism_on X TX Y TY h f)
           (top1_induced_homomorphism_on X TX Y TY k f)"
proof -
  obtain H where hHcont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY H"
      and hH0: "\<forall>x\<in>X. H (x, 0) = h x" and hH1: "\<forall>x\<in>X. H (x, 1) = k x"
      and hHbase: "\<forall>t\<in>I_set. H (x0, t) = y0"
    using hH by blast
  have hfcont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast
  have hf_vals: "\<forall>s\<in>I_set. f s \<in> X"
    using hfcont unfolding top1_continuous_map_on_def by blast
  have hf0: "f 0 = x0" and hf1: "f 1 = x0"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
    by (rule product_topology_on_is_topology_on[OF hTX hTI])
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
    unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  \<comment> \<open>Continuity of (s,t) \<mapsto> (f s, t) : I \<times> I \<rightarrow> X \<times> I via Theorem_18_4.\<close>
  have hid_II': "top1_continuous_map_on (I_set \<times> I_set) II_topology
                  (I_set \<times> I_set) (product_topology_on I_top I_top) id"
    using top1_continuous_map_on_id[OF hTII] unfolding II_topology_def .
  have hpi1_II: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi1"
  proof -
    have "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top (pi1 \<circ> id)"
      using iffD1[OF Theorem_18_4[OF hTII hTI hTI] hid_II'] by blast
    thus ?thesis by (simp add: comp_def)
  qed
  have hpi2_II: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi2"
  proof -
    have "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top (pi2 \<circ> id)"
      using iffD1[OF Theorem_18_4[OF hTII hTI hTI] hid_II'] by blast
    thus ?thesis by (simp add: comp_def)
  qed
  have hfpi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (f \<circ> pi1)"
    by (rule top1_continuous_map_on_comp[OF hpi1_II hfcont])
  \<comment> \<open>Build (\<lambda>(s,t). (f s, t)) via Theorem_18_4.\<close>
  have hpi1_pair: "(pi1 \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p))) = f \<circ> pi1"
    unfolding pi1_def by (rule ext) simp
  have hpi2_pair: "(pi2 \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p))) = pi2"
    unfolding pi2_def by (rule ext) simp
  have hpi1_pair_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX
                         (pi1 \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p)))"
    using hfpi1 unfolding hpi1_pair .
  have hpi2_pair_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top
                         (pi2 \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p)))"
    using hpi2_II unfolding hpi2_pair .
  have hpair: "top1_continuous_map_on (I_set \<times> I_set) II_topology
                 (X \<times> I_set) (product_topology_on TX I_top)
                 (\<lambda>p::real\<times>real. (f (fst p), snd p))"
    using iffD2[OF Theorem_18_4[OF hTII hTX hTI]] hpi1_pair_cont hpi2_pair_cont
    unfolding II_topology_def by blast
  \<comment> \<open>Composition: F(s,t) = H(f s, t).\<close>
  let ?F = "\<lambda>p::real\<times>real. H (f (fst p), snd p)"
  have hFcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY
                 (H \<circ> (\<lambda>p::real\<times>real. (f (fst p), snd p)))"
    by (rule top1_continuous_map_on_comp[OF hpair hHcont])
  have hFcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY ?F"
    using hFcomp by (simp add: comp_def)
  \<comment> \<open>Boundary values.\<close>
  have h_hf_path: "top1_is_path_on Y TY y0 y0 (h \<circ> f)"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top Y TY (h \<circ> f)"
      by (rule top1_continuous_map_on_comp[OF hfcont hh])
  next
    show "(h \<circ> f) 0 = y0" using hf0 hhx0 by (simp add: comp_def)
  next
    show "(h \<circ> f) 1 = y0" using hf1 hhx0 by (simp add: comp_def)
  qed
  have h_kf_path: "top1_is_path_on Y TY y0 y0 (k \<circ> f)"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top Y TY (k \<circ> f)"
      by (rule top1_continuous_map_on_comp[OF hfcont hk])
  next
    show "(k \<circ> f) 0 = y0" using hf0 hkx0 by (simp add: comp_def)
  next
    show "(k \<circ> f) 1 = y0" using hf1 hkx0 by (simp add: comp_def)
  qed
  have hFs0: "\<forall>s\<in>I_set. ?F (s, 0) = (h \<circ> f) s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "f s \<in> X" using hf_vals hs by blast
    hence "H (f s, 0) = h (f s)" using hH0 by blast
    thus "?F (s, 0) = (h \<circ> f) s" by (simp add: comp_def)
  qed
  have hFs1: "\<forall>s\<in>I_set. ?F (s, 1) = (k \<circ> f) s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "f s \<in> X" using hf_vals hs by blast
    hence "H (f s, 1) = k (f s)" using hH1 by blast
    thus "?F (s, 1) = (k \<circ> f) s" by (simp add: comp_def)
  qed
  have hF0t: "\<forall>t\<in>I_set. ?F (0, t) = y0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "f 0 = x0" by (rule hf0)
    hence "?F (0, t) = H (x0, t)" by simp
    also have "\<dots> = y0" using hHbase ht by blast
    finally show "?F (0, t) = y0" .
  qed
  have hF1t: "\<forall>t\<in>I_set. ?F (1, t) = y0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "f 1 = x0" by (rule hf1)
    hence "?F (1, t) = H (x0, t)" by simp
    also have "\<dots> = y0" using hHbase ht by blast
    finally show "?F (1, t) = y0" .
  qed
  show ?thesis
    unfolding top1_path_homotopic_on_def top1_induced_homomorphism_on_def
    using h_hf_path h_kf_path hFcont hFs0 hFs1 hF0t hF1t by blast
qed

(** from \<S>58 Lemma 58.5: if A \<subseteq> X, H : X\<times>I \<rightarrow> X is a homotopy from id_X
    to some map k : X \<rightarrow> X with H(a, t) \<in> A for all a \<in> A and t \<in> I,
    and \<alpha>(t) = H(x_0, t) is the "base-tracking" path from x_0 to k(x_0),
    then the basepoint-change \<alpha>\<^sup>\<hat> commutes with the induced map on \<pi>_1. **)
lemma Lemma_58_5_basepoint_change:
  fixes X :: "'a set" and TX :: "'a set set" and A :: "'a set"
    and H :: "'a \<times> real \<Rightarrow> 'a" and k :: "'a \<Rightarrow> 'a" and x0 :: 'a
  assumes hTX: "is_topology_on_strict X TX"
      and hAsub: "A \<subseteq> X"
      and hHcont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H"
      and hH0: "\<forall>x\<in>X. H (x, 0) = x"
      and hH1: "\<forall>x\<in>X. H (x, 1) = k x"
      and hHA: "\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) \<in> A"
      and hx0A: "x0 \<in> A"
  shows "top1_is_path_on X TX x0 (k x0) (\<lambda>t. H (x0, t))"
proof -
  have hx0X: "x0 \<in> X" using hx0A hAsub by blast
  have hTX': "is_topology_on X TX" by (rule is_topology_on_strict_imp[OF hTX])
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
    by (rule product_topology_on_is_topology_on[OF hTX' hTI])
  \<comment> \<open>Continuity of t \<mapsto> (x_0, t) : I \<rightarrow> X \<times> I via Theorem_18_4.\<close>
  have hconst_x0: "top1_continuous_map_on I_set I_top X TX (\<lambda>_. x0)"
    by (rule top1_continuous_map_on_const[OF hTI hTX' hx0X])
  have hid_I: "top1_continuous_map_on I_set I_top I_set I_top id"
    by (rule top1_continuous_map_on_id[OF hTI])
  have hpi1_eq: "(pi1 \<circ> (\<lambda>t. (x0, t))) = (\<lambda>_. x0)"
    unfolding pi1_def by (rule ext) simp
  have hpi2_eq: "(pi2 \<circ> (\<lambda>t. (x0, t))) = id"
    unfolding pi2_def by (rule ext) simp
  have hpi1_cont: "top1_continuous_map_on I_set I_top X TX (pi1 \<circ> (\<lambda>t. (x0, t)))"
    using hconst_x0 unfolding hpi1_eq .
  have hpi2_cont: "top1_continuous_map_on I_set I_top I_set I_top (pi2 \<circ> (\<lambda>t. (x0, t)))"
    using hid_I unfolding hpi2_eq .
  have hpair: "top1_continuous_map_on I_set I_top (X \<times> I_set) (product_topology_on TX I_top)
                 (\<lambda>t. (x0, t))"
    using iffD2[OF Theorem_18_4[OF hTI hTX' hTI]] hpi1_cont hpi2_cont by blast
  \<comment> \<open>Composition H \<circ> (\<lambda>t. (x_0, t)) : I \<rightarrow> X is continuous.\<close>
  have hcomp: "top1_continuous_map_on I_set I_top X TX (H \<circ> (\<lambda>t. (x0, t)))"
    by (rule top1_continuous_map_on_comp[OF hpair hHcont])
  have hcont: "top1_continuous_map_on I_set I_top X TX (\<lambda>t. H (x0, t))"
    using hcomp by (simp add: comp_def)
  \<comment> \<open>Endpoints: H(x_0, 0) = x_0 and H(x_0, 1) = k x_0.\<close>
  have hstart: "H (x0, 0) = x0" using hH0 hx0X by blast
  have hend: "H (x0, 1) = k x0" using hH1 hx0X by blast
  show ?thesis
    unfolding top1_is_path_on_def
    using hcont hstart hend by simp
qed

(** from \<S>58 Theorem 58.7: a homotopy equivalence induces an isomorphism of fundamental groups.
    The strict version is trivially related.

    Munkres' proof (sketch):
    Given f and g as homotopy invgerses, Lemma 58.1 gives that (g o f)_* equals id_*
    and (f o g)_* equals id_*, so f_* and g_* are mutual invgerses in a suitable sense.
    Hence f_* is a bijection onto pi_1(Y, f x_0). **)
text \<open>Helper: continuous f: X \<rightarrow> Y preserves path homotopy.\<close>
lemma top1_continuous_preserves_path_homotopy:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_continuous_map_on X TX Y TY f"
      and hl: "top1_is_loop_on X TX x0 l"
      and hl': "top1_is_loop_on X TX x0 l'"
      and hll': "top1_path_homotopic_on X TX x0 x0 l l'"
  shows "top1_path_homotopic_on Y TY (f x0) (f x0) (f \<circ> l) (f \<circ> l')"
proof -
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hFs0: "\<forall>s\<in>I_set. F (s, 0) = l s" and hFs1: "\<forall>s\<in>I_set. F (s, 1) = l' s"
      and hF0: "\<forall>t\<in>I_set. F (0, t) = x0" and hF1: "\<forall>t\<in>I_set. F (1, t) = x0"
    using hll' unfolding top1_path_homotopic_on_def by blast
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
    unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  let ?G = "f \<circ> F"
  have hGcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY ?G"
    by (rule top1_continuous_map_on_comp[OF hF hf])
  have hl0: "l 0 = x0" and hl1: "l 1 = x0"
    using hl unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have hl'0: "l' 0 = x0" and hl'1: "l' 1 = x0"
    using hl' unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have hfl_path: "top1_is_path_on Y TY (f x0) (f x0) (f \<circ> l)"
    unfolding top1_is_path_on_def
    using top1_continuous_map_on_comp[OF top1_is_loop_on_continuous[OF hl] hf]
    by (simp add: comp_def hl0 hl1)
  have hfl'_path: "top1_is_path_on Y TY (f x0) (f x0) (f \<circ> l')"
    unfolding top1_is_path_on_def
    using top1_continuous_map_on_comp[OF top1_is_loop_on_continuous[OF hl'] hf]
    by (simp add: comp_def hl'0 hl'1)
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hfl_path hfl'_path hGcont hFs0 hFs1 hF0 hF1
    by (auto simp: comp_def)
qed

text \<open>Helper: continuous f sends loops to loops.\<close>
lemma top1_continuous_map_loop:
  assumes "top1_continuous_map_on X TX Y TY f"
      and "top1_is_loop_on X TX x0 l"
  shows "top1_is_loop_on Y TY (f x0) (f \<circ> l)"
proof -
  have hl0: "l 0 = x0" and hl1: "l 1 = x0"
    using assms(2) unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  show ?thesis
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using top1_continuous_map_on_comp[OF top1_is_loop_on_continuous[OF assms(2)] assms(1)]
    by (simp add: comp_def hl0 hl1)
qed

text \<open>Helper: f_* sends loops at x0 to loops at f(x0), preserving loop equiv.\<close>
lemma top1_induced_preserves_loop_equiv:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_continuous_map_on X TX Y TY f"
      and hl: "top1_is_loop_on X TX x0 l"
      and hl': "top1_is_loop_on X TX x0 l'"
      and hll': "top1_loop_equiv_on X TX x0 l l'"
  shows "top1_loop_equiv_on Y TY (f x0) (f \<circ> l) (f \<circ> l')"
  unfolding top1_loop_equiv_on_def
  using top1_continuous_map_loop[OF hf hl] top1_continuous_map_loop[OF hf hl']
        top1_continuous_preserves_path_homotopy[OF hTX hf hl hl']
  using hll' unfolding top1_loop_equiv_on_def by blast

theorem Theorem_58_7:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and heq: "top1_homotopy_equivalence_on X TX Y TY f g" and hx0: "x0 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier Y TY (f x0))
           (top1_fundamental_group_mul Y TY (f x0))"
proof -
  have hf: "top1_continuous_map_on X TX Y TY f"
    using heq unfolding top1_homotopy_equivalence_on_def by blast
  have hg: "top1_continuous_map_on Y TY X TX g"
    using heq unfolding top1_homotopy_equivalence_on_def by blast
  \<comment> \<open>Define f_* on equivalence classes.\<close>
  let ?f_star = "\<lambda>c. {h. \<exists>l\<in>c. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
  \<comment> \<open>f_* maps carrier to carrier (well-definedness).\<close>
  have hfstar_class: "\<And>l. top1_is_loop_on X TX x0 l \<Longrightarrow>
    ?f_star {h. top1_loop_equiv_on X TX x0 l h} =
    {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
  proof (intro set_eqI iffI)
    fix l h assume hl: "top1_is_loop_on X TX x0 l"
    assume "h \<in> ?f_star {h. top1_loop_equiv_on X TX x0 l h}"
    then obtain l' where hl': "top1_loop_equiv_on X TX x0 l l'"
        and hh: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l') h" by blast
    have hl'_loop: "top1_is_loop_on X TX x0 l'" using hl' unfolding top1_loop_equiv_on_def by blast
    have hfl_equiv: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l) (f \<circ> l')"
      by (rule top1_induced_preserves_loop_equiv[OF hTX hf hl hl'_loop hl'])
    show "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
      using top1_loop_equiv_on_trans[OF hTY hfl_equiv hh] by simp
  next
    fix l h assume hl: "top1_is_loop_on X TX x0 l"
    assume "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
    hence hh: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h" by simp
    have "l \<in> {h. top1_loop_equiv_on X TX x0 l h}"
      using top1_loop_equiv_on_refl[OF hl] by simp
    thus "h \<in> ?f_star {h. top1_loop_equiv_on X TX x0 l h}"
      using hh by blast
  qed
  have hfstar_range: "\<forall>c\<in>top1_fundamental_group_carrier X TX x0.
      ?f_star c \<in> top1_fundamental_group_carrier Y TY (f x0)"
  proof
    fix c assume "c \<in> top1_fundamental_group_carrier X TX x0"
    then obtain l where hl: "top1_is_loop_on X TX x0 l"
        and hc: "c = {h. top1_loop_equiv_on X TX x0 l h}"
      unfolding top1_fundamental_group_carrier_def by blast
    have "?f_star c = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l) h}"
      unfolding hc by (rule hfstar_class[OF hl])
    moreover have "top1_is_loop_on Y TY (f x0) (f \<circ> l)"
      by (rule top1_continuous_map_loop[OF hf hl])
    ultimately show "?f_star c \<in> top1_fundamental_group_carrier Y TY (f x0)"
      unfolding top1_fundamental_group_carrier_def by blast
  qed
  \<comment> \<open>Pointwise: f \<circ> (l1 * l2) = (f \<circ> l1) * (f \<circ> l2).\<close>
  have hf_comp_product: "\<And>l1 l2. f \<circ> top1_path_product l1 l2 = top1_path_product (f \<circ> l1) (f \<circ> l2)"
    unfolding top1_path_product_def comp_def by (rule ext) auto
  \<comment> \<open>f_* is a homomorphism.\<close>
  have hfstar_hom: "\<forall>c1\<in>top1_fundamental_group_carrier X TX x0.
    \<forall>c2\<in>top1_fundamental_group_carrier X TX x0.
    ?f_star (top1_fundamental_group_mul X TX x0 c1 c2) =
    top1_fundamental_group_mul Y TY (f x0) (?f_star c1) (?f_star c2)"
  proof (intro ballI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
    obtain l1 where hl1: "top1_is_loop_on X TX x0 l1"
        and hc1_eq: "c1 = {h. top1_loop_equiv_on X TX x0 l1 h}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain l2 where hl2: "top1_is_loop_on X TX x0 l2"
        and hc2_eq: "c2 = {h. top1_loop_equiv_on X TX x0 l2 h}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    have hl12: "top1_is_loop_on X TX x0 (top1_path_product l1 l2)"
      unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF hTX])
         (use hl1 hl2 in \<open>auto simp: top1_is_loop_on_def\<close>)
    \<comment> \<open>LHS: f_*(mul c1 c2) = f_*(class(l1*l2)) = class(f\<circ>(l1*l2)) = class((f\<circ>l1)*(f\<circ>l2)).\<close>
    have hmul_eq: "top1_fundamental_group_mul X TX x0 c1 c2
        = {h. top1_loop_equiv_on X TX x0 (top1_path_product l1 l2) h}"
      unfolding hc1_eq hc2_eq by (rule top1_fundamental_group_mul_class[OF hTX hl1 hl2])
    have hLHS: "?f_star (top1_fundamental_group_mul X TX x0 c1 c2)
        = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> top1_path_product l1 l2) h}"
      unfolding hmul_eq by (rule hfstar_class[OF hl12])
    have hLHS': "?f_star (top1_fundamental_group_mul X TX x0 c1 c2)
        = {h. top1_loop_equiv_on Y TY (f x0) (top1_path_product (f \<circ> l1) (f \<circ> l2)) h}"
      unfolding hLHS hf_comp_product ..
    \<comment> \<open>RHS: mul(f_*(c1), f_*(c2)) = mul(class(f\<circ>l1), class(f\<circ>l2)) = class((f\<circ>l1)*(f\<circ>l2)).\<close>
    have hfc1: "?f_star c1 = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) h}"
      unfolding hc1_eq by (rule hfstar_class[OF hl1])
    have hfc2: "?f_star c2 = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) h}"
      unfolding hc2_eq by (rule hfstar_class[OF hl2])
    have hfl1: "top1_is_loop_on Y TY (f x0) (f \<circ> l1)"
      by (rule top1_continuous_map_loop[OF hf hl1])
    have hfl2: "top1_is_loop_on Y TY (f x0) (f \<circ> l2)"
      by (rule top1_continuous_map_loop[OF hf hl2])
    have hRHS: "top1_fundamental_group_mul Y TY (f x0) (?f_star c1) (?f_star c2)
        = {h. top1_loop_equiv_on Y TY (f x0) (top1_path_product (f \<circ> l1) (f \<circ> l2)) h}"
      unfolding hfc1 hfc2 by (rule top1_fundamental_group_mul_class[OF hTY hfl1 hfl2])
    show "?f_star (top1_fundamental_group_mul X TX x0 c1 c2) =
          top1_fundamental_group_mul Y TY (f x0) (?f_star c1) (?f_star c2)"
      unfolding hLHS' hRHS ..
  qed
  \<comment> \<open>f_* is bijective.
     Injectivity: g_* \<circ> f_* is related to basepoint change (iso).
     Surjectivity: f_* \<circ> g_* is related to basepoint change (iso).\<close>
  have hgof: "top1_homotopic_on X TX X TX (g \<circ> f) (\<lambda>x. x)"
    using heq unfolding top1_homotopy_equivalence_on_def id_def[symmetric] by blast
  have hfog: "top1_homotopic_on Y TY Y TY (f \<circ> g) (\<lambda>y. y)"
    using heq unfolding top1_homotopy_equivalence_on_def id_def[symmetric] by blast
  \<comment> \<open>Injectivity of f_*: g_*\<circ>f_* = basepoint change (iso), so f_* injective.\<close>
  obtain H1 where hH1cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H1"
      and hH10: "\<forall>x\<in>X. H1 (x, 0) = (g \<circ> f) x" and hH11: "\<forall>x\<in>X. H1 (x, 1) = x"
    using hgof unfolding top1_homotopic_on_def id_def by blast
  let ?\<alpha>1 = "\<lambda>t. H1 (x0, t)"
  have hfstar_inj: "inj_on ?f_star (top1_fundamental_group_carrier X TX x0)"
  proof (rule inj_onI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
       and heq_fs: "?f_star c1 = ?f_star c2"
    obtain l1 where hl1: "top1_is_loop_on X TX x0 l1"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on X TX x0 l1 g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain l2 where hl2: "top1_is_loop_on X TX x0 l2"
        and hc2_eq: "c2 = {g. top1_loop_equiv_on X TX x0 l2 g}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    \<comment> \<open>f_*(c1)=f_*(c2) \<Rightarrow> f\<circ>l1 \<simeq> f\<circ>l2 at f(x0).\<close>
    have hfl_equiv: "top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) (f \<circ> l2)"
    proof -
      have "{h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) h}
          = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) h}"
        using heq_fs
        unfolding hc1_eq hc2_eq hfstar_class[OF hl1] hfstar_class[OF hl2] .
      moreover have "f \<circ> l1 \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l1) h}"
        using top1_loop_equiv_on_refl[OF top1_continuous_map_loop[OF hf hl1]] by simp
      ultimately have "f \<circ> l1 \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) h}" by simp
      hence "top1_loop_equiv_on Y TY (f x0) (f \<circ> l2) (f \<circ> l1)" by simp
      thus ?thesis by (rule top1_loop_equiv_on_sym)
    qed
    \<comment> \<open>Apply g: g\<circ>f\<circ>l1 \<simeq> g\<circ>f\<circ>l2 at g(f(x0)).\<close>
    have hgfl_equiv: "top1_loop_equiv_on X TX (g (f x0)) (g \<circ> f \<circ> l1) (g \<circ> f \<circ> l2)"
    proof -
      have "top1_loop_equiv_on X TX (g (f x0)) (g \<circ> (f \<circ> l1)) (g \<circ> (f \<circ> l2))"
        by (rule top1_induced_preserves_loop_equiv[OF hTY hg
            top1_continuous_map_loop[OF hf hl1]
            top1_continuous_map_loop[OF hf hl2] hfl_equiv])
      thus ?thesis by (simp add: comp_assoc)
    qed
    \<comment> \<open>By homotopy_induced_basepoint_change: g\<circ>f\<circ>li \<simeq> bc(li) at g(f(x0)).\<close>
    let ?bc = "\<lambda>l. top1_basepoint_change_on X TX x0 ((g \<circ> f) x0)
                     (top1_path_reverse ?\<alpha>1) l"
    have hH11id: "\<forall>x\<in>X. H1 (x, 1) = id x" using hH11 by simp
    note hbc_raw1 = homotopy_induced_basepoint_change[OF hTX hTX hH1cont hH10 hH11id hl1 hx0]
    have hbc1: "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l1) (?bc l1)"
    proof -
      have "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l1)
        (top1_basepoint_change_on X TX (id x0) ((g \<circ> f) x0)
           (top1_path_reverse ?\<alpha>1) (id \<circ> l1))"
        by (rule hbc_raw1)
      thus ?thesis by simp
    qed
    note hbc_raw2 = homotopy_induced_basepoint_change[OF hTX hTX hH1cont hH10 hH11id hl2 hx0]
    have hbc2: "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l2) (?bc l2)"
    proof -
      have "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l2)
        (top1_basepoint_change_on X TX (id x0) ((g \<circ> f) x0)
           (top1_path_reverse ?\<alpha>1) (id \<circ> l2))"
        by (rule hbc_raw2)
      thus ?thesis by simp
    qed
    \<comment> \<open>Chain: bc(l1) \<simeq> g\<circ>f\<circ>l1 \<simeq> g\<circ>f\<circ>l2 \<simeq> bc(l2) at g(f(x0)).\<close>
    have hgfx0: "(g \<circ> f) x0 = g (f x0)" by simp
    have hbc_equiv: "top1_loop_equiv_on X TX ((g \<circ> f) x0) (?bc l1) (?bc l2)"
    proof -
      have hgfl1': "top1_loop_equiv_on X TX ((g \<circ> f) x0) ((g \<circ> f) \<circ> l1) ((g \<circ> f) \<circ> l2)"
        using hgfl_equiv by (simp add: comp_def)
      show ?thesis by (rule top1_loop_equiv_on_trans[OF hTX
          top1_loop_equiv_on_trans[OF hTX
            top1_loop_equiv_on_sym[OF hbc1] hgfl1'] hbc2])
    qed
    \<comment> \<open>bc is injective by basepoint_change_iso_via_path + roundtrip.\<close>
    have hra1: "top1_is_path_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1"
    proof -
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      have hconst: "top1_continuous_map_on I_set I_top X TX (\<lambda>_. x0)"
        by (rule top1_continuous_map_on_const[OF hTI hTX hx0])
      have hid_I: "top1_continuous_map_on I_set I_top I_set I_top id"
        by (rule top1_continuous_map_on_id[OF hTI])
      have hp1: "(pi1 \<circ> (\<lambda>t. (x0, t))) = (\<lambda>_. x0)" unfolding pi1_def by (rule ext) simp
      have hp2: "(pi2 \<circ> (\<lambda>t. (x0, t))) = id" unfolding pi2_def by (rule ext) simp
      have hpair: "top1_continuous_map_on I_set I_top (X \<times> I_set) (product_topology_on TX I_top)
                     (\<lambda>t. (x0, t))"
        using iffD2[OF Theorem_18_4[OF hTI hTX hTI]]
              hconst[folded hp1] hid_I[folded hp2] by blast
      have hcomp: "top1_continuous_map_on I_set I_top X TX (\<lambda>t. H1 (x0, t))"
        using top1_continuous_map_on_comp[OF hpair hH1cont] by (simp add: comp_def)
      have "?\<alpha>1 0 = (g \<circ> f) x0" using hH10 hx0 by auto
      moreover have "?\<alpha>1 1 = x0" using hH11 hx0 by auto
      ultimately show ?thesis unfolding top1_is_path_on_def using hcomp by auto
    qed
    have hrev_a1: "top1_is_path_on X TX x0 ((g \<circ> f) x0) (top1_path_reverse ?\<alpha>1)"
      by (rule top1_path_reverse_is_path[OF hra1])
    \<comment> \<open>Roundtrip: li \<simeq> inv_bc(bc(li)). So bc(l1)\<simeq>bc(l2) \<Rightarrow> l1\<simeq>l2.\<close>
    have hrt1: "top1_loop_equiv_on X TX x0 l1
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l1))"
      unfolding top1_loop_equiv_on_def
      using hl1 top1_basepoint_change_is_loop[OF hTX hra1
              top1_basepoint_change_is_loop[OF hTX hrev_a1 hl1]]
            top1_basepoint_change_roundtrip[OF hTX hrev_a1 hl1,
              unfolded top1_path_reverse_twice] by blast
    have hrt2: "top1_loop_equiv_on X TX x0 l2
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l2))"
      unfolding top1_loop_equiv_on_def
      using hl2 top1_basepoint_change_is_loop[OF hTX hra1
              top1_basepoint_change_is_loop[OF hTX hrev_a1 hl2]]
            top1_basepoint_change_roundtrip[OF hTX hrev_a1 hl2,
              unfolded top1_path_reverse_twice] by blast
    have hbc_cong: "top1_loop_equiv_on X TX x0
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l1))
        (top1_basepoint_change_on X TX ((g \<circ> f) x0) x0 ?\<alpha>1 (?bc l2))"
      by (rule top1_basepoint_change_loop_equiv[OF hTX hra1
            top1_basepoint_change_is_loop[OF hTX hrev_a1 hl1]
            top1_basepoint_change_is_loop[OF hTX hrev_a1 hl2]
            hbc_equiv])
    have hl1l2: "top1_loop_equiv_on X TX x0 l1 l2"
      by (rule top1_loop_equiv_on_trans[OF hTX
          top1_loop_equiv_on_trans[OF hTX hrt1 hbc_cong]
          top1_loop_equiv_on_sym[OF hrt2]])
    show "c1 = c2"
    proof -
      have "\<And>g. top1_loop_equiv_on X TX x0 l1 g \<longleftrightarrow> top1_loop_equiv_on X TX x0 l2 g"
        using hl1l2 top1_loop_equiv_on_trans[OF hTX]
              top1_loop_equiv_on_trans[OF hTX top1_loop_equiv_on_sym[OF hl1l2]]
        by blast
      thus ?thesis unfolding hc1_eq hc2_eq by auto
    qed
  qed
  \<comment> \<open>Surjectivity: similar argument using f\<circ>g \<simeq> id.\<close>
  have hfstar_surj: "?f_star ` (top1_fundamental_group_carrier X TX x0)
      = top1_fundamental_group_carrier Y TY (f x0)"
  proof (intro set_eqI iffI)
    fix d assume "d \<in> ?f_star ` (top1_fundamental_group_carrier X TX x0)"
    thus "d \<in> top1_fundamental_group_carrier Y TY (f x0)"
      using hfstar_range by (by100 blast)
  next
    fix d assume hd: "d \<in> top1_fundamental_group_carrier Y TY (f x0)"
    \<comment> \<open>d = [m] for some loop m at f(x0) in Y.\<close>
    obtain m where hm: "top1_is_loop_on Y TY (f x0) m"
        and hd_eq: "d = {h. top1_loop_equiv_on Y TY (f x0) m h}"
      using hd unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>g\<circ>m is a loop at g(f(x0)) in X.\<close>
    have hgm: "top1_is_loop_on X TX (g (f x0)) (g \<circ> m)"
      by (rule top1_continuous_map_loop[OF hg hm])
    \<comment> \<open>Basepoint-change to x0: bc(\<alpha>1, g\<circ>m) is a loop at x0.\<close>
    have hra1: "top1_is_path_on X TX (g (f x0)) x0 ?\<alpha>1"
    proof -
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      have hconst: "top1_continuous_map_on I_set I_top X TX (\<lambda>_. x0)"
        by (rule top1_continuous_map_on_const[OF hTI hTX hx0])
      have hid_I: "top1_continuous_map_on I_set I_top I_set I_top id"
        by (rule top1_continuous_map_on_id[OF hTI])
      have hp1: "(pi1 \<circ> (\<lambda>t. (x0, t))) = (\<lambda>_. x0)" unfolding pi1_def by (rule ext) simp
      have hp2: "(pi2 \<circ> (\<lambda>t. (x0, t))) = id" unfolding pi2_def by (rule ext) simp
      have hpair: "top1_continuous_map_on I_set I_top (X \<times> I_set) (product_topology_on TX I_top)
                     (\<lambda>t. (x0, t))"
        using iffD2[OF Theorem_18_4[OF hTI hTX hTI]]
              hconst[folded hp1] hid_I[folded hp2] by (by100 blast)
      have hcomp: "top1_continuous_map_on I_set I_top X TX (\<lambda>t. H1 (x0, t))"
        using top1_continuous_map_on_comp[OF hpair hH1cont] by (simp add: comp_def)
      have "?\<alpha>1 0 = (g \<circ> f) x0" using hH10 hx0 by (by100 auto)
      moreover have "?\<alpha>1 1 = x0" using hH11 hx0 by (by100 auto)
      ultimately show ?thesis unfolding top1_is_path_on_def using hcomp by (by100 auto)
    qed
    let ?bc_gm = "top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m)"
    have hbc_loop: "top1_is_loop_on X TX x0 ?bc_gm"
      by (rule top1_basepoint_change_is_loop[OF hTX hra1 hgm])
    \<comment> \<open>c = [bc(\<alpha>1, g\<circ>m)] \<in> carrier(X, x0).\<close>
    let ?c = "{h. top1_loop_equiv_on X TX x0 ?bc_gm h}"
    have hc_mem: "?c \<in> top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hbc_loop by (by100 blast)
    \<comment> \<open>f_*(c) = d: use f\<circ>g \<simeq> id to relate f\<circ>bc(\<alpha>1, g\<circ>m) to a basepoint change of m.\<close>
    obtain H2 where hH2cont: "top1_continuous_map_on (Y \<times> I_set) (product_topology_on TY I_top) Y TY H2"
        and hH20: "\<forall>y\<in>Y. H2 (y, 0) = (f \<circ> g) y" and hH21: "\<forall>y\<in>Y. H2 (y, 1) = y"
      using hfog unfolding top1_homotopic_on_def id_def by (by100 blast)
    let ?\<alpha>2 = "\<lambda>t. H2 (f x0, t)"
    \<comment> \<open>By homotopy_induced_basepoint_change: (f\<circ>g)\<circ>m \<simeq> bc(rev \<alpha>2, m).\<close>
    have hfx0Y: "f x0 \<in> Y" using hf hx0 unfolding top1_continuous_map_on_def by (by100 blast)
    have hH21': "\<forall>y\<in>Y. H2 (y, 1) = id y" using hH21 by (by100 simp)
    note hbc2 = homotopy_induced_basepoint_change[OF hTY hTY hH2cont hH20 hH21' hm hfx0Y]
    \<comment> \<open>hbc2: loop_equiv ((f\<circ>g)(f x0)) ((f\<circ>g)\<circ>m) (bc(rev \<alpha>2, id\<circ>m)).\<close>
    have hbc2': "top1_loop_equiv_on Y TY (f (g (f x0))) (f \<circ> g \<circ> m)
        (top1_basepoint_change_on Y TY (f x0) (f (g (f x0)))
           (top1_path_reverse ?\<alpha>2) m)"
    proof -
      have "(\<lambda>y. f (g y)) \<circ> m = f \<circ> g \<circ> m" by (simp add: comp_def)
      moreover have "(\<lambda>y. y) \<circ> m = m" by (simp add: comp_def)
      ultimately show ?thesis using hbc2 by simp
    qed
    \<comment> \<open>f preserves path products: f \<circ> (p * q) = (f\<circ>p) * (f\<circ>q).\<close>
    have hf_comp_product: "\<And>p q. f \<circ> top1_path_product p q = top1_path_product (f \<circ> p) (f \<circ> q)"
      unfolding top1_path_product_def comp_def by (rule ext) (by100 auto)
    have hf_comp_rev: "\<And>p. f \<circ> top1_path_reverse p = top1_path_reverse (f \<circ> p)"
      unfolding top1_path_reverse_def comp_def by (rule ext) (by100 auto)
    \<comment> \<open>f \<circ> bc(\<alpha>1, g\<circ>m) = bc(f\<circ>\<alpha>1, f\<circ>g\<circ>m) since f preserves products.\<close>
    have hfbc_eq: "f \<circ> ?bc_gm = top1_basepoint_change_on Y TY (f (g (f x0))) (f x0)
        (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m)"
      unfolding top1_basepoint_change_on_def hf_comp_product hf_comp_rev
      by (simp add: comp_assoc)
    \<comment> \<open>Define \<gamma> = rev(\<alpha>2) * (f\<circ>\<alpha>1), a loop at f(x0).\<close>
    have hfa1: "top1_is_path_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1)"
    proof -
      have ha1_cont: "top1_continuous_map_on I_set I_top X TX ?\<alpha>1"
        using hra1 unfolding top1_is_path_on_def by (by100 blast)
      have "top1_continuous_map_on I_set I_top Y TY (f \<circ> ?\<alpha>1)"
        using top1_continuous_map_on_comp[OF ha1_cont hf] by (simp add: comp_assoc)
      moreover have "(f \<circ> ?\<alpha>1) 0 = f (g (f x0))" using hH10 hx0 by (by100 auto)
      moreover have "(f \<circ> ?\<alpha>1) 1 = f x0" using hH11 hx0 by (by100 auto)
      ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
    qed
    have ha2: "top1_is_path_on Y TY (f (g (f x0))) (f x0) ?\<alpha>2"
    proof -
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      have hconst_fx0: "top1_continuous_map_on I_set I_top Y TY (\<lambda>_. f x0)"
        by (rule top1_continuous_map_on_const[OF hTI hTY hfx0Y])
      have hid_I: "top1_continuous_map_on I_set I_top I_set I_top id"
        by (rule top1_continuous_map_on_id[OF hTI])
      have hp1: "(pi1 \<circ> (\<lambda>t. (f x0, t))) = (\<lambda>_. f x0)" unfolding pi1_def by (rule ext) simp
      have hp2: "(pi2 \<circ> (\<lambda>t. (f x0, t))) = id" unfolding pi2_def by (rule ext) simp
      have hpair: "top1_continuous_map_on I_set I_top (Y \<times> I_set) (product_topology_on TY I_top)
                     (\<lambda>t. (f x0, t))"
        using iffD2[OF Theorem_18_4[OF hTI hTY hTI]]
              hconst_fx0[folded hp1] hid_I[folded hp2] by (by100 blast)
      have hcomp: "top1_continuous_map_on I_set I_top Y TY (\<lambda>t. H2 (f x0, t))"
        using top1_continuous_map_on_comp[OF hpair hH2cont] by (simp add: comp_def)
      have "?\<alpha>2 0 = f (g (f x0))" using hH20 hfx0Y by (by100 auto)
      moreover have "?\<alpha>2 1 = f x0" using hH21 hfx0Y by (by100 auto)
      ultimately show ?thesis unfolding top1_is_path_on_def using hcomp by (by100 auto)
    qed
    have hra2: "top1_is_path_on Y TY (f x0) (f (g (f x0))) (top1_path_reverse ?\<alpha>2)"
      by (rule top1_path_reverse_is_path[OF ha2])
    let ?\<gamma> = "top1_path_product (top1_path_reverse ?\<alpha>2) (f \<circ> ?\<alpha>1)"
    have h\<gamma>_path: "top1_is_path_on Y TY (f x0) (f x0) ?\<gamma>"
      by (rule top1_path_product_is_path[OF hTY hra2 hfa1])
    \<comment> \<open>For ANY loop m' at f(x0): f \<circ> bc(\<alpha>1, g\<circ>m') \<simeq> bc(\<gamma>, m').\<close>
    have hcomp_is_bc: "\<And>m'. top1_is_loop_on Y TY (f x0) m' \<Longrightarrow>
        top1_loop_equiv_on Y TY (f x0) (f \<circ> top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m'))
            (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
    proof -
      fix m' assume hm': "top1_is_loop_on Y TY (f x0) m'"
      \<comment> \<open>f\<circ>bc(\<alpha>1, g\<circ>m') = bc(f\<circ>\<alpha>1, f\<circ>g\<circ>m') (f preserves products).\<close>
      have hfbc': "f \<circ> top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m') =
          top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m')"
        unfolding top1_basepoint_change_on_def hf_comp_product hf_comp_rev
        by (simp add: comp_assoc)
      \<comment> \<open>f\<circ>g\<circ>m' \<simeq> bc(rev \<alpha>2, m') by homotopy_induced_basepoint_change.\<close>
      have hbc2_m': "top1_loop_equiv_on Y TY (f (g (f x0))) (f \<circ> g \<circ> m')
          (top1_basepoint_change_on Y TY (f x0) (f (g (f x0)))
             (top1_path_reverse ?\<alpha>2) m')"
      proof -
        note hbc2_raw = homotopy_induced_basepoint_change[OF hTY hTY hH2cont hH20 hH21' hm' hfx0Y]
        have "(\<lambda>y. f (g y)) \<circ> m' = f \<circ> g \<circ> m'" by (simp add: comp_def)
        moreover have "(\<lambda>y. y) \<circ> m' = m'" by (simp add: comp_def)
        ultimately show ?thesis using hbc2_raw by simp
      qed
      \<comment> \<open>bc(f\<circ>\<alpha>1, f\<circ>g\<circ>m') \<simeq> bc(f\<circ>\<alpha>1, bc(rev\<alpha>2, m')) by bc_loop_equiv.\<close>
      have hfgm'_loop: "top1_is_loop_on Y TY (f (g (f x0))) (f \<circ> g \<circ> m')"
        using hbc2_m' unfolding top1_loop_equiv_on_def by (by100 blast)
      have hbc_ra2_m': "top1_is_loop_on Y TY (f (g (f x0)))
          (top1_basepoint_change_on Y TY (f x0) (f (g (f x0))) (top1_path_reverse ?\<alpha>2) m')"
        by (rule top1_basepoint_change_is_loop[OF hTY hra2 hm'])
      have hstep2: "top1_loop_equiv_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m'))
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1)
             (top1_basepoint_change_on Y TY (f x0) (f (g (f x0))) (top1_path_reverse ?\<alpha>2) m'))"
        by (rule top1_basepoint_change_loop_equiv[OF hTY hfa1 hfgm'_loop hbc_ra2_m' hbc2_m'])
      \<comment> \<open>bc(f\<circ>\<alpha>1, bc(rev\<alpha>2, m')) \<simeq> bc(\<gamma>, m') by double_bc.\<close>
      have hstep3: "top1_loop_equiv_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1)
             (top1_basepoint_change_on Y TY (f x0) (f (g (f x0))) (top1_path_reverse ?\<alpha>2) m'))
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
        by (rule double_basepoint_change_equiv[OF hTY hfa1 hra2 hm'])
      \<comment> \<open>Chain: f\<circ>bc = bc(f\<circ>\<alpha>1, f\<circ>g\<circ>m') \<simeq> bc(f\<circ>\<alpha>1, bc(rev\<alpha>2, m')) \<simeq> bc(\<gamma>, m').\<close>
      have hchain: "top1_loop_equiv_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f (g (f x0))) (f x0) (f \<circ> ?\<alpha>1) (f \<circ> g \<circ> m'))
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
        by (rule top1_loop_equiv_on_trans[OF hTY hstep2 hstep3])
      show "top1_loop_equiv_on Y TY (f x0)
          (f \<circ> top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> m'))
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> m')"
        using hchain unfolding hfbc' .
    qed
    \<comment> \<open>Take m' = bc(rev(\<gamma>), m). By roundtrip: m \<simeq> bc(\<gamma>, m').\<close>
    let ?r\<gamma> = "top1_path_reverse ?\<gamma>"
    have hr\<gamma>: "top1_is_path_on Y TY (f x0) (f x0) ?r\<gamma>"
      by (rule top1_path_reverse_is_path[OF h\<gamma>_path])
    let ?m' = "top1_basepoint_change_on Y TY (f x0) (f x0) ?r\<gamma> m"
    have hm'_loop: "top1_is_loop_on Y TY (f x0) ?m'"
      by (rule top1_basepoint_change_is_loop[OF hTY hr\<gamma> hm])
    have hroundtrip: "top1_loop_equiv_on Y TY (f x0) m
        (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
    proof -
      have "top1_path_homotopic_on Y TY (f x0) (f x0) m
          (top1_basepoint_change_on Y TY (f x0) (f x0) (top1_path_reverse ?r\<gamma>)
            (top1_basepoint_change_on Y TY (f x0) (f x0) ?r\<gamma> m))"
        by (rule top1_basepoint_change_roundtrip[OF hTY hr\<gamma> hm])
      hence hrt: "top1_path_homotopic_on Y TY (f x0) (f x0) m
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
        by (simp add: top1_path_reverse_twice)
      have hbc_gm'_loop: "top1_is_loop_on Y TY (f x0)
          (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
        by (rule top1_basepoint_change_is_loop[OF hTY h\<gamma>_path hm'_loop])
      show ?thesis
        unfolding top1_loop_equiv_on_def
        using hm hbc_gm'_loop hrt by (by100 blast)
    qed
    \<comment> \<open>Construct preimage: c' = [bc(\<alpha>1, g\<circ>m')].\<close>
    have hgm': "top1_is_loop_on X TX (g (f x0)) (g \<circ> ?m')"
      by (rule top1_continuous_map_loop[OF hg hm'_loop])
    let ?c_pre = "top1_basepoint_change_on X TX (g (f x0)) x0 ?\<alpha>1 (g \<circ> ?m')"
    have hcpre_loop: "top1_is_loop_on X TX x0 ?c_pre"
      by (rule top1_basepoint_change_is_loop[OF hTX hra1 hgm'])
    have hcpre_mem: "{h. top1_loop_equiv_on X TX x0 ?c_pre h}
        \<in> top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hcpre_loop by (by100 blast)
    \<comment> \<open>f_*([c']) = [f\<circ>c'] = [bc(\<gamma>, m')] by hcomp_is_bc.\<close>
    have hfcpre_equiv: "top1_loop_equiv_on Y TY (f x0)
        (f \<circ> ?c_pre) (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
      by (rule hcomp_is_bc[OF hm'_loop])
    \<comment> \<open>bc(\<gamma>, m') \<simeq> m by roundtrip (sym).\<close>
    have hbc_gm'_loop_Y: "top1_is_loop_on Y TY (f x0)
        (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
      by (rule top1_basepoint_change_is_loop[OF hTY h\<gamma>_path hm'_loop])
    have hrt_ph: "top1_path_homotopic_on Y TY (f x0) (f x0) m
        (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m')"
      using hroundtrip unfolding top1_loop_equiv_on_def by (by100 blast)
    have hbcgm_equiv_m: "top1_loop_equiv_on Y TY (f x0)
        (top1_basepoint_change_on Y TY (f x0) (f x0) ?\<gamma> ?m') m"
      unfolding top1_loop_equiv_on_def
      using hbc_gm'_loop_Y hm Lemma_51_1_path_homotopic_sym[OF hrt_ph]
      by (by100 blast)
    \<comment> \<open>f\<circ>c' \<simeq> m.\<close>
    have hfcpre_m: "top1_loop_equiv_on Y TY (f x0) (f \<circ> ?c_pre) m"
      by (rule top1_loop_equiv_on_trans[OF hTY hfcpre_equiv hbcgm_equiv_m])
    \<comment> \<open>f_*([c']) = [m] = d.\<close>
    have hfstar_cpre: "?f_star {h. top1_loop_equiv_on X TX x0 ?c_pre h} = d"
    proof -
      have "?f_star {h. top1_loop_equiv_on X TX x0 ?c_pre h}
          = {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> ?c_pre) h}"
        by (rule hfstar_class[OF hcpre_loop])
      also have "\<dots> = {h. top1_loop_equiv_on Y TY (f x0) m h}"
      proof (intro equalityI subsetI)
        fix h assume "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> ?c_pre) h}"
        thus "h \<in> {h. top1_loop_equiv_on Y TY (f x0) m h}"
          using top1_loop_equiv_on_trans[OF hTY
                  top1_loop_equiv_on_sym[OF hfcpre_m]] by (by100 simp)
      next
        fix h assume "h \<in> {h. top1_loop_equiv_on Y TY (f x0) m h}"
        thus "h \<in> {h. top1_loop_equiv_on Y TY (f x0) (f \<circ> ?c_pre) h}"
          using top1_loop_equiv_on_trans[OF hTY hfcpre_m] by (by100 simp)
      qed
      also have "\<dots> = d" using hd_eq by simp
      finally show ?thesis .
    qed
    thus "d \<in> ?f_star ` (top1_fundamental_group_carrier X TX x0)"
      using hcpre_mem by (by100 blast)
  qed
  have hfstar_bij: "bij_betw ?f_star (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_carrier Y TY (f x0))"
    unfolding bij_betw_def using hfstar_inj hfstar_surj by blast
  have hiso: "top1_group_iso_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier Y TY (f x0))
      (top1_fundamental_group_mul Y TY (f x0)) ?f_star"
    unfolding top1_group_iso_on_def top1_group_hom_on_def bij_betw_def
    using hfstar_range hfstar_hom hfstar_bij unfolding bij_betw_def by blast
  show ?thesis
    unfolding top1_groups_isomorphic_on_def using hiso by blast
qed

(** from \<S>58 Theorem 58.3: deformation retract induces isomorphism of fundamental groups.

    Munkres' proof: if A is a deformation retract of X via H, then the
    inclusion j: A \<hookrightarrow> X and the retraction r: X \<rightarrow> A = H(\<cdot>, 1) are homotopy
    invgerses. By Theorem 58.7, any homotopy equivalence induces an iso on \<pi>_1. **)

text \<open>Helper: the inclusion-induced map takes A-equivalence classes to X-equivalence classes.\<close>
lemma inclusion_induced_class:
  assumes hTX: "is_topology_on X TX" and hTA: "is_topology_on A TA"
      and hAsub: "A \<subseteq> X" and hTA_eq: "TA = subspace_topology X TX A"
      and hj: "top1_continuous_map_on A TA X TX id"
      and hf: "top1_is_loop_on A TA x0 f"
  shows "top1_fundamental_group_induced_on A TA x0 X TX x0 id
      {g. top1_loop_equiv_on A TA x0 f g}
    = {k. top1_loop_equiv_on X TX x0 f k}"
proof (intro set_eqI iffI)
  fix k assume "k \<in> top1_fundamental_group_induced_on A TA x0 X TX x0 id
      {g. top1_loop_equiv_on A TA x0 f g}"
  then obtain g where hfg: "top1_loop_equiv_on A TA x0 f g"
      and hgk: "top1_loop_equiv_on X TX x0 (id \<circ> g) k"
    unfolding top1_fundamental_group_induced_on_def by (by100 blast)
  have hg_loop: "top1_is_loop_on A TA x0 g"
    using hfg unfolding top1_loop_equiv_on_def by (by100 blast)
  have hfg_X: "top1_loop_equiv_on X TX x0 f g"
    using top1_induced_preserves_loop_equiv[OF hTA hj hf hg_loop hfg]
    by (simp add: comp_def)
  have hgk': "top1_loop_equiv_on X TX x0 g k"
    using hgk by (simp add: comp_def)
  show "k \<in> {k. top1_loop_equiv_on X TX x0 f k}"
    using top1_loop_equiv_on_trans[OF hTX hfg_X hgk'] by simp
next
  fix k assume hk: "k \<in> {k. top1_loop_equiv_on X TX x0 f k}"
  hence hfk: "top1_loop_equiv_on X TX x0 f k" by simp
  have hff: "top1_loop_equiv_on A TA x0 f f"
    by (rule top1_loop_equiv_on_refl[OF hf])
  have hfk': "top1_loop_equiv_on X TX x0 (id \<circ> f) k"
    using hfk by (simp add: comp_def)
  show "k \<in> top1_fundamental_group_induced_on A TA x0 X TX x0 id
      {g. top1_loop_equiv_on A TA x0 f g}"
    unfolding top1_fundamental_group_induced_on_def
    apply (rule CollectI)
    apply (rule bexI[of _ f])
    apply (rule hfk')
    apply (rule CollectI)
    apply (rule hff)
    done
qed

text \<open>Helper for Theorem 58.3: the inclusion-induced map on \<pi>_1 classes is
  a group isomorphism when the inclusion has a retraction homotopic to id.\<close>
lemma inclusion_retraction_iso:
  assumes hTX: "is_topology_on X TX" and hTA: "is_topology_on A TA"
      and hAsub: "A \<subseteq> X" and hTA_eq: "TA = subspace_topology X TX A"
      and hj: "top1_continuous_map_on A TA X TX id"
      and hr: "top1_continuous_map_on X TX A TA r"
      and hrj: "\<forall>a\<in>A. r a = a"
      and hjr: "\<And>f. top1_is_loop_on X TX x0 f \<Longrightarrow>
          top1_path_homotopic_on X TX x0 x0 (r \<circ> f) f"
      and hx0: "x0 \<in> A"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier A TA x0)
           (top1_fundamental_group_mul A TA x0)
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)"
proof -
  \<comment> \<open>The inclusion j: A \<hookrightarrow> X induces j_*: \<pi>_1(A) \<rightarrow> \<pi>_1(X).
     Step 1 (Injectivity): If j_*[f] = [const] in \<pi>_1(X), then f \<simeq> const in X.
     Apply r: r\<circ>f \<simeq> r\<circ>const = const in A. But r\<circ>f = f (since f \<subseteq> A and r|A = id).
     So f \<simeq> const in A. Hence j_* is injective.
     Step 2 (Surjectivity): For any loop f in X, hjr gives f \<simeq> r\<circ>f in X.
     r\<circ>f is a loop in A, so [f] = j_*[r\<circ>f]. Hence j_* is surjective.
     Step 3 (Homomorphism): j_* preserves products by functoriality.\<close>
  let ?j_star = "top1_fundamental_group_induced_on A TA x0 X TX x0 id"
  have hj_inj: "inj_on ?j_star (top1_fundamental_group_carrier A TA x0)"
  proof (rule inj_onI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier A TA x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier A TA x0"
       and heq: "?j_star c1 = ?j_star c2"
    obtain f where hf: "top1_is_loop_on A TA x0 f"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on A TA x0 f g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by (by100 blast)
    obtain g where hg: "top1_is_loop_on A TA x0 g"
        and hc2_eq: "c2 = {h. top1_loop_equiv_on A TA x0 g h}"
      using hc2 unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>j_*(c1) = [f]_X, j_*(c2) = [g]_X.\<close>
    have hjc1: "?j_star c1 = {k. top1_loop_equiv_on X TX x0 f k}"
      unfolding hc1_eq by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hf])
    have hjc2: "?j_star c2 = {k. top1_loop_equiv_on X TX x0 g k}"
      unfolding hc2_eq by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hg])
    \<comment> \<open>[f]_X = [g]_X, so f \<simeq>_X g.\<close>
    have hfg_X: "top1_loop_equiv_on X TX x0 f g"
    proof -
      have hf_X: "top1_is_loop_on X TX x0 f"
        using top1_continuous_map_loop[OF hj hf] by (simp add: comp_def)
      have hclass_eq: "{k. top1_loop_equiv_on X TX x0 f k}
          = {k. top1_loop_equiv_on X TX x0 g k}"
        using heq hjc1 hjc2 by simp
      have "top1_loop_equiv_on X TX x0 f f"
        by (rule top1_loop_equiv_on_refl[OF hf_X])
      hence "f \<in> {k. top1_loop_equiv_on X TX x0 f k}" by simp
      hence "f \<in> {k. top1_loop_equiv_on X TX x0 g k}"
        using hclass_eq by simp
      hence "top1_loop_equiv_on X TX x0 g f" by simp
      thus ?thesis by (rule top1_loop_equiv_on_sym)
    qed
    \<comment> \<open>Apply r: r\<circ>f \<simeq>_A r\<circ>g.\<close>
    have hfg_hom_X: "top1_path_homotopic_on X TX x0 x0 f g"
      using hfg_X unfolding top1_loop_equiv_on_def by (by100 blast)
    have hrf_rg_A: "top1_path_homotopic_on A TA (r x0) (r x0) (r \<circ> f) (r \<circ> g)"
      by (rule continuous_preserves_path_homotopic[OF hTX hTA hr hfg_hom_X])
    have hrx0: "r x0 = x0" using hrj hx0 by (by100 blast)
    have hrf_rg_A': "top1_path_homotopic_on A TA x0 x0 (r \<circ> f) (r \<circ> g)"
      using hrf_rg_A unfolding hrx0 .
    \<comment> \<open>r\<circ>f = f and r\<circ>g = g (since f, g map into A and r|A = id).\<close>
    have hf_mem: "\<forall>s\<in>I_set. f s \<in> A"
      using hf unfolding top1_is_loop_on_def top1_is_path_on_def
        top1_continuous_map_on_def by (by100 blast)
    have hg_mem: "\<forall>s\<in>I_set. g s \<in> A"
      using hg unfolding top1_is_loop_on_def top1_is_path_on_def
        top1_continuous_map_on_def by (by100 blast)
    have hrf_eq_f: "\<forall>s\<in>I_set. (r \<circ> f) s = f s"
    proof (intro ballI)
      fix s assume "s \<in> I_set"
      have "f s \<in> A" using hf_mem \<open>s \<in> I_set\<close> by (by100 blast)
      thus "(r \<circ> f) s = f s" using hrj by (simp add: comp_def)
    qed
    have hrg_eq_g: "\<forall>s\<in>I_set. (r \<circ> g) s = g s"
    proof (intro ballI)
      fix s assume "s \<in> I_set"
      have "g s \<in> A" using hg_mem \<open>s \<in> I_set\<close> by (by100 blast)
      thus "(r \<circ> g) s = g s" using hrj by (simp add: comp_def)
    qed
    \<comment> \<open>Transfer: f \<simeq>_A r\<circ>f and g \<simeq>_A r\<circ>g (by loop_agree_on_I).\<close>
    have hf_rf: "top1_path_homotopic_on A TA x0 x0 f (r \<circ> f)"
      using conjunct2[OF loop_agree_on_I[OF hf hrf_eq_f]] .
    have hg_rg: "top1_path_homotopic_on A TA x0 x0 g (r \<circ> g)"
      using conjunct2[OF loop_agree_on_I[OF hg hrg_eq_g]] .
    \<comment> \<open>Chain: f \<simeq>_A r\<circ>f \<simeq>_A r\<circ>g \<simeq>_A g.\<close>
    have hf_rg: "top1_path_homotopic_on A TA x0 x0 f (r \<circ> g)"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTA hf_rf hrf_rg_A'])
    have hrg_g: "top1_path_homotopic_on A TA x0 x0 (r \<circ> g) g"
      by (rule Lemma_51_1_path_homotopic_sym[OF hg_rg])
    have hfg_A: "top1_path_homotopic_on A TA x0 x0 f g"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTA hf_rg hrg_g])
    have hfg_equiv: "top1_loop_equiv_on A TA x0 f g"
      unfolding top1_loop_equiv_on_def using hf hg hfg_A by (by100 blast)
    show "c1 = c2"
    proof -
      have "\<And>h. top1_loop_equiv_on A TA x0 f h \<longleftrightarrow> top1_loop_equiv_on A TA x0 g h"
        using hfg_equiv top1_loop_equiv_on_trans[OF hTA]
              top1_loop_equiv_on_trans[OF hTA top1_loop_equiv_on_sym[OF hfg_equiv]]
        by (by100 blast)
      thus ?thesis unfolding hc1_eq hc2_eq by auto
    qed
  qed
  have hj_surj: "?j_star ` (top1_fundamental_group_carrier A TA x0)
      = top1_fundamental_group_carrier X TX x0"
  proof (intro set_eqI iffI)
    fix c assume "c \<in> ?j_star ` (top1_fundamental_group_carrier A TA x0)"
    then obtain c_A where hcA: "c_A \<in> top1_fundamental_group_carrier A TA x0"
        and hc_eq: "c = ?j_star c_A" by (by100 blast)
    obtain f where hf: "top1_is_loop_on A TA x0 f"
        and hcA_eq: "c_A = {g. top1_loop_equiv_on A TA x0 f g}"
      using hcA unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hjc: "c = {k. top1_loop_equiv_on X TX x0 f k}"
      unfolding hc_eq hcA_eq
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hf])
    have hf_X: "top1_is_loop_on X TX x0 f"
      using top1_continuous_map_loop[OF hj hf] by (simp add: comp_def)
    show "c \<in> top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def hjc
      using hf_X by (by100 blast)
  next
    fix c assume hc: "c \<in> top1_fundamental_group_carrier X TX x0"
    obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc_eq: "c = {g. top1_loop_equiv_on X TX x0 f g}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>r\<circ>f is a loop in A.\<close>
    have hrf_loop: "top1_is_loop_on A TA x0 (r \<circ> f)"
    proof -
      have hrf: "top1_is_loop_on A TA (r x0) (r \<circ> f)"
        by (rule top1_continuous_map_loop[OF hr hf])
      have hrx0: "r x0 = x0" using hrj hx0 by (by100 blast)
      show ?thesis using hrf unfolding hrx0 .
    qed
    \<comment> \<open>j_*([r\<circ>f]_A) = [r\<circ>f]_X.\<close>
    let ?c_A = "{g. top1_loop_equiv_on A TA x0 (r \<circ> f) g}"
    have hcA_mem: "?c_A \<in> top1_fundamental_group_carrier A TA x0"
      unfolding top1_fundamental_group_carrier_def using hrf_loop by (by100 blast)
    have hjcA: "?j_star ?c_A = {k. top1_loop_equiv_on X TX x0 (r \<circ> f) k}"
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hrf_loop])
    \<comment> \<open>r\<circ>f \<simeq> f in X (by hjr), so [r\<circ>f]_X = [f]_X.\<close>
    have hrf_f: "top1_path_homotopic_on X TX x0 x0 (r \<circ> f) f"
      by (rule hjr[OF hf])
    have hrf_equiv_f: "top1_loop_equiv_on X TX x0 (r \<circ> f) f"
      unfolding top1_loop_equiv_on_def using hrf_f
      using top1_continuous_map_loop[OF hj hrf_loop] hf
      by (simp add: comp_def top1_is_loop_on_def)
    have hclass_eq: "{k. top1_loop_equiv_on X TX x0 (r \<circ> f) k}
        = {k. top1_loop_equiv_on X TX x0 f k}"
    proof (intro set_eqI iffI)
      fix k assume "k \<in> {k. top1_loop_equiv_on X TX x0 (r \<circ> f) k}"
      hence hk: "top1_loop_equiv_on X TX x0 (r \<circ> f) k" by simp
      have "top1_loop_equiv_on X TX x0 f (r \<circ> f)"
        by (rule top1_loop_equiv_on_sym[OF hrf_equiv_f])
      thus "k \<in> {k. top1_loop_equiv_on X TX x0 f k}"
        using top1_loop_equiv_on_trans[OF hTX _ hk] by simp
    next
      fix k assume "k \<in> {k. top1_loop_equiv_on X TX x0 f k}"
      hence hk: "top1_loop_equiv_on X TX x0 f k" by simp
      thus "k \<in> {k. top1_loop_equiv_on X TX x0 (r \<circ> f) k}"
        using top1_loop_equiv_on_trans[OF hTX hrf_equiv_f] by simp
    qed
    show "c \<in> ?j_star ` (top1_fundamental_group_carrier A TA x0)"
      using hcA_mem unfolding hc_eq hjcA[symmetric] hclass_eq[symmetric] by (by100 blast)
  qed
  have hj_hom: "\<forall>c\<in>top1_fundamental_group_carrier A TA x0.
      \<forall>d\<in>top1_fundamental_group_carrier A TA x0.
      ?j_star (top1_fundamental_group_mul A TA x0 c d)
      = top1_fundamental_group_mul X TX x0 (?j_star c) (?j_star d)"
  proof (intro ballI)
    fix c d assume hc: "c \<in> top1_fundamental_group_carrier A TA x0"
        and hd: "d \<in> top1_fundamental_group_carrier A TA x0"
    obtain f where hf: "top1_is_loop_on A TA x0 f"
        and hc_eq: "c = {g. top1_loop_equiv_on A TA x0 f g}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 blast)
    obtain g where hg: "top1_is_loop_on A TA x0 g"
        and hd_eq: "d = {h. top1_loop_equiv_on A TA x0 g h}"
      using hd unfolding top1_fundamental_group_carrier_def by (by100 blast)
    \<comment> \<open>c \<cdot> d = [f*g]_A by mul_class.\<close>
    have hcd: "top1_fundamental_group_mul A TA x0 c d
        = {h. top1_loop_equiv_on A TA x0 (top1_path_product f g) h}"
      unfolding hc_eq hd_eq
      by (rule top1_fundamental_group_mul_class[OF hTA hf hg])
    \<comment> \<open>f*g is a loop in A.\<close>
    have hfg_loop: "top1_is_loop_on A TA x0 (top1_path_product f g)"
      by (rule top1_path_product_is_loop[OF hTA hf hg])
    \<comment> \<open>j_*(c\<cdot>d) = j_*([f*g]_A) = [f*g]_X.\<close>
    have hjcd: "?j_star (top1_fundamental_group_mul A TA x0 c d)
        = {k. top1_loop_equiv_on X TX x0 (top1_path_product f g) k}"
      unfolding hcd
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hfg_loop])
    \<comment> \<open>j_*(c) = [f]_X, j_*(d) = [g]_X.\<close>
    have hjc: "?j_star c = {k. top1_loop_equiv_on X TX x0 f k}"
      unfolding hc_eq
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hf])
    have hjd: "?j_star d = {k. top1_loop_equiv_on X TX x0 g k}"
      unfolding hd_eq
      by (rule inclusion_induced_class[OF hTX hTA hAsub hTA_eq hj hg])
    \<comment> \<open>f, g are loops in X (since A \<subseteq> X and inclusion is continuous).\<close>
    have hf_X: "top1_is_loop_on X TX x0 f"
      using top1_continuous_map_loop[OF hj hf] by (simp add: comp_def)
    have hg_X: "top1_is_loop_on X TX x0 g"
      using top1_continuous_map_loop[OF hj hg] by (simp add: comp_def)
    \<comment> \<open>[f]_X \<cdot> [g]_X = [f*g]_X by mul_class.\<close>
    have hjcd': "top1_fundamental_group_mul X TX x0 (?j_star c) (?j_star d)
        = {k. top1_loop_equiv_on X TX x0 (top1_path_product f g) k}"
      unfolding hjc hjd
      by (rule top1_fundamental_group_mul_class[OF hTX hf_X hg_X])
    show "?j_star (top1_fundamental_group_mul A TA x0 c d)
        = top1_fundamental_group_mul X TX x0 (?j_star c) (?j_star d)"
      unfolding hjcd hjcd' ..
  qed
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
  proof (intro exI conjI)
    show "top1_group_hom_on (top1_fundamental_group_carrier A TA x0)
        (top1_fundamental_group_mul A TA x0)
        (top1_fundamental_group_carrier X TX x0)
        (top1_fundamental_group_mul X TX x0) ?j_star"
      unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix c assume hc: "c \<in> top1_fundamental_group_carrier A TA x0"
      show "?j_star c \<in> top1_fundamental_group_carrier X TX x0"
        using hj_surj hc by (by100 blast)
    next
      fix c d assume hc: "c \<in> top1_fundamental_group_carrier A TA x0"
          and hd: "d \<in> top1_fundamental_group_carrier A TA x0"
      show "?j_star (top1_fundamental_group_mul A TA x0 c d)
          = top1_fundamental_group_mul X TX x0 (?j_star c) (?j_star d)"
        using hj_hom hc hd by (by100 blast)
    qed
    show "bij_betw ?j_star (top1_fundamental_group_carrier A TA x0)
        (top1_fundamental_group_carrier X TX x0)"
      unfolding bij_betw_def using hj_inj hj_surj by (by100 blast)
  qed
qed

theorem Theorem_58_3:
  assumes hdef: "top1_deformation_retract_of_on X TX A"
      and hTX: "is_topology_on X TX"
      and hx0: "x0 \<in> A"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
           (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)"
proof -
  obtain H where hAsub: "A \<subseteq> X"
      and hH: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H"
      and hH0: "\<forall>x\<in>X. H (x, 0) = x" and hH1: "\<forall>x\<in>X. H (x, 1) \<in> A"
      and hHA: "\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) = a"
    using hdef unfolding top1_deformation_retract_of_on_def by blast
  let ?TA = "subspace_topology X TX A"
  have hTA: "is_topology_on A ?TA"
    by (rule subspace_topology_is_topology_on[OF hTX hAsub])
  \<comment> \<open>j = id (inclusion) and r = H(\<cdot>,1) (retraction) form a homotopy equivalence.
     By Theorem 58.7, this gives the isomorphism.\<close>
  let ?r = "\<lambda>x. H (x, 1::real)"
  \<comment> \<open>1. Inclusion id: A \<rightarrow> X is continuous.\<close>
  have hj_cont: "top1_continuous_map_on A ?TA X TX id"
    by (rule top1_continuous_map_on_subspace_restrict[OF top1_continuous_map_on_id[OF hTX] hAsub])
  \<comment> \<open>2. Retraction r: X \<rightarrow> A is continuous.\<close>
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hpair1: "top1_continuous_map_on X TX (X \<times> I_set) (product_topology_on TX I_top)
                  (\<lambda>x. (x, 1::real))"
  proof -
    have hc1: "top1_continuous_map_on X TX I_set I_top (\<lambda>_. 1::real)"
      by (rule top1_continuous_map_on_const[OF hTX hTI h1_I])
    have hp1_eq: "pi1 \<circ> (\<lambda>x. (x, 1::real)) = id" unfolding pi1_def by (rule ext) simp
    have hp1: "top1_continuous_map_on X TX X TX (pi1 \<circ> (\<lambda>x. (x, 1::real)))"
      unfolding hp1_eq by (rule top1_continuous_map_on_id[OF hTX])
    have hp2_eq: "pi2 \<circ> (\<lambda>x. (x, 1::real)) = (\<lambda>_. 1::real)" unfolding pi2_def by (rule ext) simp
    have hp2: "top1_continuous_map_on X TX I_set I_top (pi2 \<circ> (\<lambda>x. (x, 1::real)))"
      unfolding hp2_eq by (rule hc1)
    show ?thesis
      using iffD2[OF Theorem_18_4[OF hTX hTX hTI, of "\<lambda>x. (x, 1::real)"]]
      hp1 hp2 by blast
  qed
  have hr_cont_X: "top1_continuous_map_on X TX X TX ?r"
    using top1_continuous_map_on_comp[OF hpair1 hH] by (simp add: comp_def)
  have hr_img: "?r ` X \<subseteq> A" using hH1 by auto
  have hr_cont: "top1_continuous_map_on X TX A ?TA ?r"
    by (rule top1_continuous_map_on_codomain_shrink[OF hr_cont_X hr_img hAsub])
  \<comment> \<open>3. r \<circ> id ≃ id_A: since H(a,1)=a for a\<in>A, r\<circ>id = id on A. Trivial homotopy.\<close>
  have hrj_eq: "\<forall>a\<in>A. ?r (id a) = id a"
    using hHA h1_I by auto
  have hrj_hom: "top1_homotopic_on A ?TA A ?TA (?r \<circ> id) id"
  proof -
    have hrj_fun_eq: "\<And>a. a \<in> A \<Longrightarrow> (?r \<circ> id) a = id a"
      using hrj_eq by simp
    \<comment> \<open>Constant homotopy: F(a,t) = a for all t.\<close>
    have hconst_hom: "top1_continuous_map_on (A \<times> I_set) (product_topology_on ?TA I_top)
                        A ?TA (\<lambda>p. fst p)"
    proof -
      have hTP: "is_topology_on (A \<times> I_set) (product_topology_on ?TA I_top)"
        by (rule product_topology_on_is_topology_on[OF hTA hTI])
      have "top1_continuous_map_on (A \<times> I_set) (product_topology_on ?TA I_top) A ?TA (pi1 \<circ> id)"
      proof -
        have "top1_continuous_map_on (A \<times> I_set) (product_topology_on ?TA I_top) A ?TA pi1"
          by (rule top1_continuous_pi1[OF hTA hTI])
        thus ?thesis by simp
      qed
      thus ?thesis unfolding pi1_def comp_def by simp
    qed
    have hcont_rj: "top1_continuous_map_on A ?TA A ?TA (?r \<circ> id)"
      using top1_continuous_map_on_comp[OF hj_cont hr_cont] by simp
    show ?thesis
      unfolding top1_homotopic_on_def
    proof (intro conjI exI)
      show "top1_continuous_map_on A ?TA A ?TA (?r \<circ> id)" by (rule hcont_rj)
      show "top1_continuous_map_on A ?TA A ?TA id" by (rule top1_continuous_map_on_id[OF hTA])
      show "top1_continuous_map_on (A \<times> I_set) (product_topology_on ?TA I_top) A ?TA (\<lambda>p. fst p)"
        by (rule hconst_hom)
      show "\<forall>x\<in>A. fst (x, 0::real) = (?r \<circ> id) x" using hrj_fun_eq by auto
      show "\<forall>x\<in>A. fst (x, 1::real) = id x" by simp
    qed
  qed
  \<comment> \<open>4. id \<circ> r ≃ id_X: via H(x, 1-t). H(x,0)=x=id(x), H(x,1)=(id\<circ>r)(x).\<close>
  have hjr_hom: "top1_homotopic_on X TX X TX (id \<circ> ?r) id"
  proof -
    \<comment> \<open>Homotopy F(x,t) = H(x, 1-t). F(x,0) = H(x,1) = r(x), F(x,1) = H(x,0) = x.\<close>
    let ?flip = "\<lambda>(x::'a, t::real). (x, 1 - t)"
    \<comment> \<open>flip is continuous X\<times>I \<rightarrow> X\<times>I via Theorem 18.4.\<close>
    have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
      by (rule product_topology_on_is_topology_on[OF hTX hTI])
    have hflip_pi1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        X TX (pi1 \<circ> ?flip)"
    proof -
      have "(pi1 \<circ> ?flip) = pi1" unfolding pi1_def by (rule ext) auto
      thus ?thesis using top1_continuous_pi1[OF hTX hTI] by simp
    qed
    have hflip_pi2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        I_set I_top (pi2 \<circ> ?flip)"
    proof -
      have hpi2_flip_eq: "(pi2 \<circ> ?flip) = (\<lambda>p. 1 - pi2 p)"
        unfolding pi2_def by (rule ext) auto
      \<comment> \<open>(\<lambda>t. 1-t) is continuous I \<rightarrow> I.\<close>
      have hrev_map: "\<And>t. t \<in> I_set \<Longrightarrow> 1 - t \<in> I_set"
        unfolding top1_unit_interval_def by auto
      have hrev_cont: "continuous_on UNIV (\<lambda>t::real. 1 - t)" by (intro continuous_intros)
      have hrev_I: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
      proof -
        have "top1_continuous_map_on I_set
          (subspace_topology UNIV top1_open_sets I_set) I_set
          (subspace_topology UNIV top1_open_sets I_set) (\<lambda>t. 1 - t)"
          by (rule top1_continuous_map_on_real_subspace_open_sets[OF hrev_map hrev_cont])
        thus ?thesis unfolding top1_unit_interval_topology_def .
      qed
      have hpi2_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top pi2"
        by (rule top1_continuous_pi2[OF hTX hTI])
      have hcomp: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top
          ((\<lambda>t. 1 - t) \<circ> pi2)"
        by (rule top1_continuous_map_on_comp[OF hpi2_cont hrev_I])
      have hcomp_eq: "((\<lambda>t. 1 - t) \<circ> pi2) = (\<lambda>p. 1 - pi2 p)" by (rule ext) (simp add: comp_def)
      show ?thesis unfolding hpi2_flip_eq hcomp_eq[symmetric] by (rule hcomp)
    qed
    have hflip_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        (X \<times> I_set) (product_topology_on TX I_top) ?flip"
      using iffD2[OF Theorem_18_4[OF hTP hTX hTI, of ?flip]]
      hflip_pi1 hflip_pi2 by blast
    have hF_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
        X TX (\<lambda>p. H (?flip p))"
      using top1_continuous_map_on_comp[OF hflip_cont hH] by (simp add: comp_def)
    have hF_eq: "\<And>p. ?flip p = (fst p, 1 - snd p)" by auto
    have hF0: "\<forall>x\<in>X. H (x, 1 - (0::real)) = (id \<circ> ?r) x" by simp
    have hF1: "\<forall>x\<in>X. H (x, 1 - (1::real)) = id x"
    proof
      fix x assume "x \<in> X"
      thus "H (x, 1 - 1) = id x" using hH0 by simp
    qed
    show ?thesis
      unfolding top1_homotopic_on_def id_def[symmetric]
    proof (intro conjI exI)
      show "top1_continuous_map_on X TX X TX (id \<circ> ?r)"
      proof -
        have "(id \<circ> ?r) = ?r" by (rule ext) (simp add: id_def)
        thus ?thesis using hr_cont_X by simp
      qed
      show "top1_continuous_map_on X TX X TX id" by (rule top1_continuous_map_on_id[OF hTX])
      show "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX
              (\<lambda>p. H (fst p, 1 - snd p))"
        using hF_cont by (simp add: case_prod_beta)
      show "\<forall>x\<in>X. H (fst (x, 0::real), 1 - snd (x, 0::real)) = (id \<circ> ?r) x"
        using hF0 by simp
      show "\<forall>x\<in>X. H (fst (x, 1::real), 1 - snd (x, 1::real)) = id x"
        using hF1 by simp
    qed
  qed
  \<comment> \<open>Following Munkres' textbook proof: use Lemma 58.1 (basepoint FIXED) directly.
     Key: H fixes x₀ ∈ A, so the basepoint-fixed version applies.\<close>
  have hx0X: "x0 \<in> X" using hx0 hAsub by blast
  \<comment> \<open>Lemma 58.1 applied: j\<circ>r \<simeq> id with x₀ fixed \<Rightarrow> (j\<circ>r)\<circ>f \<simeq> f for any loop f at x₀.\<close>
  have hjr_fixed: "\<And>f. top1_is_loop_on X TX x0 f \<Longrightarrow>
    top1_path_homotopic_on X TX x0 x0 ((\<lambda>x. ?r x) \<circ> f) f"
  proof -
    fix fl assume hfl: "top1_is_loop_on X TX x0 fl"
    \<comment> \<open>Homotopy from j\<circ>r to id that fixes x₀: use H with H(x₀,t) = x₀.\<close>
    have hH_base_fixed: "\<forall>t\<in>I_set. H (x0, t) = x0"
      using hHA hx0 by blast
    have hH_for_58_1: "\<exists>G. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX G
        \<and> (\<forall>x\<in>X. G (x, 0) = (\<lambda>x. ?r x) x) \<and> (\<forall>x\<in>X. G (x, 1) = id x)
        \<and> (\<forall>t\<in>I_set. G (x0, t) = x0)"
    proof (intro exI conjI)
      let ?G = "\<lambda>p. H (fst p, 1 - snd p)"
      show "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX ?G"
      proof -
        let ?flip = "\<lambda>(x::'a, t::real). (x, 1 - t)"
        have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
          by (rule product_topology_on_is_topology_on[OF hTX hTI])
        have hflip_pi1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX (pi1 \<circ> ?flip)"
        proof -
          have "(pi1 \<circ> ?flip) = pi1" unfolding pi1_def by (rule ext) auto
          thus ?thesis using top1_continuous_pi1[OF hTX hTI] by simp
        qed
        have hflip_pi2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top (pi2 \<circ> ?flip)"
        proof -
          have heq: "(pi2 \<circ> ?flip) = (\<lambda>p. 1 - pi2 p)" unfolding pi2_def by (rule ext) auto
          have hrev: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
          proof -
            have "top1_continuous_map_on I_set (subspace_topology UNIV top1_open_sets I_set) I_set
                (subspace_topology UNIV top1_open_sets I_set) (\<lambda>t. 1 - t)"
              by (rule top1_continuous_map_on_real_subspace_open_sets)
                 (auto simp: top1_unit_interval_def intro: continuous_intros)
            thus ?thesis unfolding top1_unit_interval_topology_def .
          qed
          have hcomp: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top ((\<lambda>t. 1 - t) \<circ> pi2)"
            by (rule top1_continuous_map_on_comp[OF top1_continuous_pi2[OF hTX hTI] hrev])
          show ?thesis unfolding heq using hcomp by (simp add: comp_def)
        qed
        have hflip_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
            (X \<times> I_set) (product_topology_on TX I_top) ?flip"
          using iffD2[OF Theorem_18_4[OF hTP hTX hTI, of ?flip]] hflip_pi1 hflip_pi2 by blast
        show ?thesis
          using top1_continuous_map_on_comp[OF hflip_cont hH] by (simp add: comp_def case_prod_beta)
      qed
      show "\<forall>x\<in>X. ?G (x, 0) = ?r x" by simp
      show "\<forall>x\<in>X. ?G (x, 1) = id x" using hH0 by simp
      show "\<forall>t\<in>I_set. ?G (x0, t) = x0"
      proof
        fix t assume "t \<in> I_set"
        hence "1 - t \<in> I_set" unfolding top1_unit_interval_def by auto
        thus "?G (x0, t) = x0" using hH_base_fixed by simp
      qed
    qed
    have hhx0: "(\<lambda>x. ?r x) x0 = x0"
      using hHA hx0 h1_I by auto
    have "top1_path_homotopic_on X TX x0 x0
        (top1_induced_homomorphism_on X TX X TX (\<lambda>x. ?r x) fl)
        (top1_induced_homomorphism_on X TX X TX id fl)"
      by (rule Lemma_58_1_basepoint_fixed[OF hTX
            hr_cont_X top1_continuous_map_on_id[OF hTX]
            hhx0 _ hH_for_58_1 hfl]) simp
    hence "top1_path_homotopic_on X TX x0 x0 ((\<lambda>x. ?r x) \<circ> fl) ((\<lambda>x. x) \<circ> fl)"
      unfolding top1_induced_homomorphism_on_def id_def by simp
    thus "top1_path_homotopic_on X TX x0 x0 ((\<lambda>x. ?r x) \<circ> fl) fl"
      by (simp add: comp_def)
  qed
  \<comment> \<open>Now: r_*\<circ>j_* = id on \<pi>_1(A) because r\<circ>j = id_A pointwise.
     And j_*\<circ>r_* = id on \<pi>_1(X) because j\<circ>r \<simeq> id with basepoint fixed (Lemma 58.1).
     So j_* is bijective (with inverse r_*), hence a group isomorphism.\<close>
  \<comment> \<open>Apply the inclusion-retraction lemma with j=id, r=H(\<cdot>,1).\<close>
  have hrj_pointwise: "\<forall>a\<in>A. ?r a = a" using hHA h1_I by auto
  show ?thesis
    by (rule inclusion_retraction_iso[OF hTX hTA hAsub refl hj_cont hr_cont hrj_pointwise hjr_fixed hx0])
qed

(** from \<S>58 Theorem 58.2: inclusion S^1 \<rightarrow> R^2-0 induces isomorphism of fundamental groups.

    Munkres' proof: S^1 is a deformation retract of R^2 - 0 via
    H(x, t) = (1-t)x + t(x/||x||). By Theorem 58.3, the inclusion induces
    an isomorphism of fundamental groups. **)
theorem Theorem_58_2_inclusion_iso:
  fixes TR2_0 :: "(real \<times> real) set set"
  defines "TR2_0 \<equiv> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0::real, 0::real)})"
  shows "top1_groups_isomorphic_on
    (top1_fundamental_group_carrier top1_S1 (subspace_topology (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1) (1, 0))
    (top1_fundamental_group_mul top1_S1 (subspace_topology (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1) (1, 0))
    (top1_fundamental_group_carrier (UNIV - {(0, 0)}) TR2_0 (1, 0))
    (top1_fundamental_group_mul (UNIV - {(0, 0)}) TR2_0 (1, 0))"
proof -
  \<comment> \<open>S^1 is a deformation retract of R^2 - {0} via H(x,t) = (1-t)x + t(x/|x|).\<close>
  have hdef: "top1_deformation_retract_of_on
    (UNIV - {(0::real, 0::real)})
    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
       (UNIV - {(0::real, 0::real)}))
    top1_S1"
  proof -
    let ?R2_0 = "UNIV - {(0::real, 0::real)}"
    let ?TR = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?R2_0"
    let ?norm = "\<lambda>x::real\<times>real. sqrt (fst x ^ 2 + snd x ^ 2)"
    let ?H = "\<lambda>(x::real\<times>real, t::real). ((1-t)*fst x + t*fst x/?norm x, (1-t)*snd x + t*snd x/?norm x)"
    have hS1sub: "top1_S1 \<subseteq> ?R2_0" unfolding top1_S1_def by auto
    have hH0: "\<forall>x\<in>?R2_0. ?H (x, 0) = x" by simp
    have hH1: "\<forall>x\<in>?R2_0. ?H (x, 1) \<in> top1_S1"
    proof
      fix x :: "real \<times> real" assume hx: "x \<in> ?R2_0"
      hence hne: "x \<noteq> (0, 0)" by simp
      hence hnorm_pos: "?norm x > 0"
      proof -
        have "fst x \<noteq> 0 \<or> snd x \<noteq> 0" using hne by (auto simp: prod_eq_iff)
        hence "fst x ^ 2 + snd x ^ 2 > 0" by (auto simp: sum_power2_gt_zero_iff)
        thus ?thesis by simp
      qed
      have "?H (x, 1) = (fst x / ?norm x, snd x / ?norm x)" by simp
      moreover have "(fst x / ?norm x) ^ 2 + (snd x / ?norm x) ^ 2 = 1"
      proof -
        have hns: "?norm x ^ 2 = fst x ^ 2 + snd x ^ 2"
          using hnorm_pos by (simp add: real_sqrt_pow2)
        have h1: "(fst x / ?norm x) ^ 2 = fst x ^ 2 / (fst x ^ 2 + snd x ^ 2)"
          unfolding power_divide hns ..
        have h2: "(snd x / ?norm x) ^ 2 = snd x ^ 2 / (fst x ^ 2 + snd x ^ 2)"
          unfolding power_divide hns ..
        have hdn: "fst x ^ 2 + snd x ^ 2 \<noteq> 0"
        proof -
          have "fst x \<noteq> 0 \<or> snd x \<noteq> 0" using hne by (auto simp: prod_eq_iff)
          hence "fst x ^ 2 + snd x ^ 2 > 0" by (auto simp: sum_power2_gt_zero_iff)
          thus ?thesis by linarith
        qed
        let ?d = "fst x ^ 2 + snd x ^ 2"
        have "fst x ^ 2 / ?d + snd x ^ 2 / ?d = ?d / ?d"
          by (metis add_divide_distrib)
        also have "?d / ?d = 1" using hdn by simp
        finally show ?thesis unfolding h1 h2 .
      qed
      ultimately show "?H (x, 1) \<in> top1_S1" unfolding top1_S1_def by simp
    qed
    have hHA: "\<forall>a\<in>top1_S1. \<forall>t\<in>I_set. ?H (a, t) = a"
    proof (intro ballI)
      fix a :: "real \<times> real" and t :: real
      assume ha: "a \<in> top1_S1" and ht: "t \<in> I_set"
      have heq: "fst a ^ 2 + snd a ^ 2 = 1" using ha unfolding top1_S1_def by simp
      hence hnorm: "?norm a = 1" by (simp add: real_sqrt_eq_1_iff)
      show "?H (a, t) = a" using hnorm by (simp add: prod_eq_iff algebra_simps)
    qed
    have hHcont: "top1_continuous_map_on (?R2_0 \<times> I_set) (product_topology_on ?TR I_top) ?R2_0 ?TR ?H"
    proof -
      \<comment> \<open>Step 1: continuous_on (R²-{0})×I H.\<close>
      have hH_std: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
          ((1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p),
           (1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p)))"
      proof -
        \<comment> \<open>Norm and division continuous on R²-{0}.\<close>
        have hnorm_cont: "continuous_on ?R2_0 ?norm"
          by (intro continuous_on_compose2[OF continuous_on_real_sqrt]
              continuous_on_add continuous_on_power continuous_intros) auto
        have hnorm_nz: "\<forall>x\<in>?R2_0. ?norm x \<noteq> 0"
        proof (intro ballI)
          fix x :: "real \<times> real" assume "x \<in> ?R2_0"
          hence "fst x ^ 2 + snd x ^ 2 > 0"
            by (cases x) (auto simp: sum_power2_gt_zero_iff)
          thus "?norm x \<noteq> 0" by (metis less_imp_neq not_sym real_sqrt_gt_zero)
        qed
        have hfst_div: "continuous_on ?R2_0 (\<lambda>x. fst x / ?norm x)"
          by (rule continuous_on_divide) (intro continuous_intros, rule hnorm_cont, rule hnorm_nz)
        have hsnd_div: "continuous_on ?R2_0 (\<lambda>x. snd x / ?norm x)"
          by (rule continuous_on_divide) (intro continuous_intros, rule hnorm_cont, rule hnorm_nz)
        \<comment> \<open>Lift to (R²-{0})×I via composition with fst.\<close>
        have hfst_R2: "continuous_on (?R2_0 \<times> I_set) (fst::(real\<times>real)\<times>real \<Rightarrow> real\<times>real)"
          by (intro continuous_intros)
        have hfst_img: "fst ` (?R2_0 \<times> I_set) \<subseteq> ?R2_0" by (by100 auto)
        have hfdiv': "continuous_on (?R2_0 \<times> I_set) (\<lambda>p. fst (fst p) / ?norm (fst p))"
          using continuous_on_compose[OF hfst_R2 continuous_on_subset[OF hfst_div hfst_img]]
          by (simp add: comp_def)
        have hsdiv': "continuous_on (?R2_0 \<times> I_set) (\<lambda>p. snd (fst p) / ?norm (fst p))"
          using continuous_on_compose[OF hfst_R2 continuous_on_subset[OF hsnd_div hfst_img]]
          by (simp add: comp_def)
        have hid: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. p)"
          by (rule continuous_on_id)
        have h1mt: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. 1 - snd p)"
          by (intro continuous_on_diff continuous_on_const continuous_on_snd[OF hid])
        have hff: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. fst (fst p))"
          by (intro continuous_on_fst[OF continuous_on_fst[OF hid]])
        have hsf: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. snd (fst p))"
          by (intro continuous_on_snd[OF continuous_on_fst[OF hid]])
        have ht: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real. snd p)"
          by (intro continuous_on_snd[OF hid])
        have htfd: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            snd p * (fst (fst p) / ?norm (fst p)))"
          by (rule continuous_on_mult[OF ht hfdiv'])
        have htsd: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            snd p * (snd (fst p) / ?norm (fst p)))"
          by (rule continuous_on_mult[OF ht hsdiv'])
        have hcomp1: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            (1 - snd p) * fst (fst p) + snd p * (fst (fst p) / ?norm (fst p)))"
          by (intro continuous_on_add continuous_on_mult h1mt hff ht hfdiv')
        have hcomp2: "continuous_on (?R2_0 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            (1 - snd p) * snd (fst p) + snd p * (snd (fst p) / ?norm (fst p)))"
          by (intro continuous_on_add continuous_on_mult h1mt hsf ht hsdiv')
        show ?thesis
          using continuous_on_Pair[OF hcomp1 hcomp2] by simp
      qed
      have hH_eq: "(\<lambda>p::(real\<times>real)\<times>real.
          ((1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p),
           (1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p)))
        = (\<lambda>p. ?H (fst p, snd p))"
        by (rule ext) (simp add: case_prod_beta)
      have hH_std': "continuous_on (?R2_0 \<times> I_set) (\<lambda>p. ?H (fst p, snd p))"
        using hH_std unfolding hH_eq .
      \<comment> \<open>Step 2: H maps into R²-{0}.\<close>
      have hH_range: "\<And>p. p \<in> ?R2_0 \<times> I_set \<Longrightarrow> (\<lambda>p. ?H (fst p, snd p)) p \<in> ?R2_0"
      proof -
        fix p :: "(real \<times> real) \<times> real"
        assume hp: "p \<in> ?R2_0 \<times> I_set"
        have hxR2: "fst p \<in> ?R2_0" using hp by (simp add: mem_Times_iff)
        hence hxnz: "fst p \<noteq> (0, 0)" by (by100 simp)
        have htI: "snd p \<in> I_set" using hp by (simp add: mem_Times_iff)
        have hnp: "?norm (fst p) > 0"
          using hxnz by (cases "fst p") (auto simp: sum_power2_gt_zero_iff real_sqrt_gt_zero)
        \<comment> \<open>H(x,t) \<noteq> 0: if it were, both components = 0 ⟹ x = 0, contradiction.\<close>
        have "?H (fst p, snd p) \<noteq> (0, 0)"
        proof
          assume habs: "?H (fst p, snd p) = (0, 0)"
          \<comment> \<open>Component 1: (1-t)*a + t*a/|x| = 0 means a*((1-t) + t/|x|) = 0.\<close>
          have h1: "(1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p) = 0"
            using habs by (simp add: prod_eq_iff case_prod_beta)
          have h2: "(1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p) = 0"
            using habs by (simp add: prod_eq_iff case_prod_beta)
          \<comment> \<open>Multiply by |x| > 0: (1-t)*a*|x| + t*a = 0 and similarly for b.\<close>
          have h1': "(1 - snd p) * fst (fst p) * ?norm (fst p) + snd p * fst (fst p) = 0"
          proof -
            from h1 have "((1 - snd p) * fst (fst p) + snd p * fst (fst p) / ?norm (fst p))
                * ?norm (fst p) = 0" by (by100 simp)
            hence "(1 - snd p) * fst (fst p) * ?norm (fst p) +
                snd p * fst (fst p) / ?norm (fst p) * ?norm (fst p) = 0"
              by (simp add: algebra_simps)
            moreover have "snd p * fst (fst p) / ?norm (fst p) * ?norm (fst p)
                = snd p * fst (fst p)"
              using hnp by (by100 simp)
            ultimately show ?thesis by (by100 linarith)
          qed
          have h2': "(1 - snd p) * snd (fst p) * ?norm (fst p) + snd p * snd (fst p) = 0"
          proof -
            from h2 have "((1 - snd p) * snd (fst p) + snd p * snd (fst p) / ?norm (fst p))
                * ?norm (fst p) = 0" by (by100 simp)
            hence "(1 - snd p) * snd (fst p) * ?norm (fst p) +
                snd p * snd (fst p) / ?norm (fst p) * ?norm (fst p) = 0"
              by (simp add: algebra_simps)
            moreover have "snd p * snd (fst p) / ?norm (fst p) * ?norm (fst p)
                = snd p * snd (fst p)"
              using hnp by (by100 simp)
            ultimately show ?thesis by (by100 linarith)
          qed
          \<comment> \<open>Factor: a * ((1-t)*|x| + t) = 0 and b * ((1-t)*|x| + t) = 0.\<close>
          have hfact1: "fst (fst p) * ((1 - snd p) * ?norm (fst p) + snd p) = 0"
            using h1' by (simp add: algebra_simps)
          have hfact2: "snd (fst p) * ((1 - snd p) * ?norm (fst p) + snd p) = 0"
            using h2' by (simp add: algebra_simps)
          \<comment> \<open>(1-t)*|x| + t > 0 since |x| > 0 and t \<ge> 0, 1-t \<ge> 0.\<close>
          have hc_pos: "(1 - snd p) * ?norm (fst p) + snd p > 0"
          proof (cases "snd p = 0")
            case True thus ?thesis using hnp by (by100 simp)
          next
            case False
            have "snd p > 0" using False htI unfolding top1_unit_interval_def by (by100 simp)
            moreover have "(1 - snd p) * ?norm (fst p) \<ge> 0"
              using htI hnp unfolding top1_unit_interval_def by (by100 simp)
            ultimately show ?thesis by (by100 linarith)
          qed
          have "fst (fst p) = 0" using hfact1 hc_pos by (by100 simp)
          moreover have "snd (fst p) = 0" using hfact2 hc_pos by (by100 simp)
          ultimately show False using hxnz by (simp add: prod_eq_iff)
        qed
        thus "(\<lambda>p. ?H (fst p, snd p)) p \<in> ?R2_0"
          by (simp add: case_prod_beta)
      qed
      \<comment> \<open>Step 3: Transfer.\<close>
      have "top1_continuous_map_on (?R2_0 \<times> I_set) (product_topology_on ?TR I_top)
          ?R2_0 ?TR (\<lambda>p. ?H (fst p, snd p))"
        by (rule R2_subspace_I_continuous_on_transfer[OF hH_std' hH_range])
      moreover have "(\<lambda>p::(real\<times>real)\<times>real. ?H (fst p, snd p)) = ?H"
        by (rule ext) (simp add: case_prod_beta)
      ultimately show ?thesis by simp
    qed
    show ?thesis unfolding top1_deformation_retract_of_on_def
      using hS1sub hHcont hH0 hH1 hHA by blast
  qed
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTR hTR] by simp
  have hTR2_0: "is_topology_on (UNIV - {(0::real, 0::real)})
    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))"
    by (rule subspace_topology_is_topology_on[OF hTR2]) simp
  have h10: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by simp
  have hS1_eq: "top1_S1_topology = subspace_topology
    (UNIV - {(0::real, 0::real)})
    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))
    top1_S1"
    unfolding top1_S1_topology_def
    by (rule subspace_topology_trans[of top1_S1 "UNIV - {(0, 0)}", symmetric])
       (auto simp: top1_S1_def)
  have hdef': "top1_deformation_retract_of_on (UNIV - {(0::real, 0::real)}) TR2_0 top1_S1"
    unfolding TR2_0_def by (rule hdef)
  have hTR2_0': "is_topology_on (UNIV - {(0::real, 0::real)}) TR2_0"
    unfolding TR2_0_def by (rule hTR2_0)
  show ?thesis
    unfolding TR2_0_def[symmetric]
    by (rule Theorem_58_3[OF hdef' hTR2_0' h10])
qed

corollary Theorem_58_7_strict:
  assumes "is_topology_on_strict X TX" and "is_topology_on_strict Y TY"
    and "top1_homotopy_equivalence_on X TX Y TY f g" and "x0 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier Y TY (f x0))
           (top1_fundamental_group_mul Y TY (f x0))"
  using Theorem_58_7[OF is_topology_on_strict_imp[OF assms(1)] is_topology_on_strict_imp[OF assms(2)] assms(3) assms(4)] by blast

text \<open>Strict version: if X and Y have the same homotopy type and X is strict,
  Y is also strict.\<close>
corollary top1_same_homotopy_type_strict:
  assumes "top1_same_homotopy_type_on X TX Y TY"
  shows "top1_same_homotopy_type_on Y TY X TX"
  by (rule top1_same_homotopy_type_on_sym[OF assms])

section \<open>\<S>59 The Fundamental Group of S^n\<close>

text \<open>The n-sphere S^n embedded in R^{n+1}.\<close>
definition top1_Sn :: "nat \<Rightarrow> (nat \<Rightarrow> real) set" where
  "top1_Sn n = {x. (\<forall>i \<ge> Suc n. x i = 0) \<and> (\<Sum>i\<le>n. (x i)^2) = 1}"

(** from \<S>59 Theorem 59.1: the images of i_*: \<pi>_1(U, x_0) \<rightarrow> \<pi>_1(X, x_0) and
    j_*: \<pi>_1(V, x_0) \<rightarrow> \<pi>_1(X, x_0) generate \<pi>_1(X, x_0). Equivalently, every loop in
    X at x_0 is path-homotopic to a finite concatenation of loops, each of which
    lies entirely in U or entirely in V. **)
text \<open>Helper: a path in a subspace is a path in the ambient space. (Moved here for use in 59.1.)\<close>
lemma path_in_subspace_is_path_in_ambient':
  assumes hTX: "is_topology_on X TX" and hWX: "W \<subseteq> X"
      and hg: "top1_is_path_on W (subspace_topology X TX W) a b g"
  shows "top1_is_path_on X TX a b g"
  unfolding top1_is_path_on_def
proof (intro conjI)
  have hg_cont: "top1_continuous_map_on I_set I_top W (subspace_topology X TX W) g"
    using hg unfolding top1_is_path_on_def by (by100 blast)
  show "top1_continuous_map_on I_set I_top X TX g"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix s assume "s \<in> I_set"
    thus "g s \<in> X" using hg_cont hWX unfolding top1_continuous_map_on_def by (by100 blast)
  next
    fix V assume hV: "V \<in> TX"
    have hVW: "W \<inter> V \<in> subspace_topology X TX W"
      unfolding subspace_topology_def using hV by (by100 blast)
    have "{s \<in> I_set. g s \<in> V} = {s \<in> I_set. g s \<in> W \<inter> V}"
      using hg_cont unfolding top1_continuous_map_on_def by (by100 blast)
    also have "\<dots> \<in> I_top" using hg_cont hVW unfolding top1_continuous_map_on_def by (by100 blast)
    finally show "{s \<in> I_set. g s \<in> V} \<in> I_top" .
  qed
  show "g 0 = a" using hg unfolding top1_is_path_on_def by (by100 blast)
  show "g 1 = b" using hg unfolding top1_is_path_on_def by (by100 blast)
qed

\<comment> \<open>Helper: foldr of path products respects base homotopy.\<close>
lemma foldr_path_product_base_homotopic:
  assumes hTX: "is_topology_on X TX"
      and hpaths: "\<And>i. i < length fs \<Longrightarrow> top1_is_path_on X TX (a i) (a (Suc i)) (fs!i)"
      and hbase: "top1_path_homotopic_on X TX (a (length fs)) (a (length fs)) base1 base2"
  shows "top1_path_homotopic_on X TX (a 0) (a (length fs))
      (foldr top1_path_product fs base1) (foldr top1_path_product fs base2)"
  using assms
proof (induction fs arbitrary: a)
  case Nil thus ?case by simp
next
  case (Cons f fs')
  have hf: "top1_is_path_on X TX (a 0) (a 1) f"
    using Cons.prems(2)[of 0] by simp
  define a' where "a' i = a (Suc i)" for i
  have hfs': "\<And>i. i < length fs' \<Longrightarrow> top1_is_path_on X TX (a' i) (a' (Suc i)) (fs'!i)"
  proof -
    fix i assume "i < length fs'"
    hence "Suc i < length (f # fs')" by simp
    thus "top1_is_path_on X TX (a' i) (a' (Suc i)) (fs'!i)"
      using Cons.prems(2)[of "Suc i"] unfolding a'_def by simp
  qed
  have hbase': "top1_path_homotopic_on X TX (a' (length fs')) (a' (length fs')) base1 base2"
    using Cons.prems(3) unfolding a'_def by simp
  have hIH: "top1_path_homotopic_on X TX (a' 0) (a' (length fs'))
      (foldr top1_path_product fs' base1) (foldr top1_path_product fs' base2)"
    by (rule Cons.IH[OF Cons.prems(1) hfs' hbase'])
  have hIH': "top1_path_homotopic_on X TX (a 1) (a (Suc (length fs')))
      (foldr top1_path_product fs' base1) (foldr top1_path_product fs' base2)"
    using hIH unfolding a'_def by simp
  have "top1_path_homotopic_on X TX (a 0) (a (Suc (length fs')))
      (top1_path_product f (foldr top1_path_product fs' base1))
      (top1_path_product f (foldr top1_path_product fs' base2))"
    by (rule path_homotopic_product_right[OF Cons.prems(1) hIH' hf])
  thus ?case by simp
qed

\<comment> \<open>Helper: foldr of path products is a path.\<close>
lemma foldr_path_product_is_path:
  assumes hTX: "is_topology_on X TX"
      and hpaths: "\<And>i. i < length fs \<Longrightarrow> top1_is_path_on X TX (a i) (a (Suc i)) (fs!i)"
      and hbase: "top1_is_path_on X TX (a (length fs)) y base"
  shows "top1_is_path_on X TX (a 0) y (foldr top1_path_product fs base)"
  using assms
proof (induction fs arbitrary: a)
  case Nil thus ?case by simp
next
  case (Cons f fs')
  have hf: "top1_is_path_on X TX (a 0) (a 1) f"
    using Cons.prems(2)[of 0] by simp
  define a' where "a' i = a (Suc i)" for i
  have hfs': "\<And>i. i < length fs' \<Longrightarrow> top1_is_path_on X TX (a' i) (a' (Suc i)) (fs'!i)"
  proof -
    fix i assume "i < length fs'"
    thus "top1_is_path_on X TX (a' i) (a' (Suc i)) (fs'!i)"
      using Cons.prems(2)[of "Suc i"] unfolding a'_def by simp
  qed
  have hbase': "top1_is_path_on X TX (a' (length fs')) y base"
    using Cons.prems(3) unfolding a'_def by simp
  have hIH: "top1_is_path_on X TX (a' 0) y (foldr top1_path_product fs' base)"
    by (rule Cons.IH[OF Cons.prems(1) hfs' hbase'])
  have "top1_is_path_on X TX (a 0) y (top1_path_product f (foldr top1_path_product fs' base))"
    by (rule top1_path_product_is_path[OF Cons.prems(1) hf]) (use hIH a'_def in simp)
  thus ?case by simp
qed

\<comment> \<open>Core telescoping identity: foldr of conjugated paths = α(0) * foldr of raw paths * rev(α(n)).\<close>
lemma telescoping_core:
  assumes hTX: "is_topology_on X TX" and hx0: "x0 \<in> X"
      and hlen: "length gs = k" "length fs = k" "k \<ge> 1"
      and h\<alpha>: "\<And>i. i \<le> k \<Longrightarrow> top1_is_path_on X TX x0 (a i) (\<alpha> i)"
      and hfi: "\<And>i. i < k \<Longrightarrow> top1_is_path_on X TX (a i) (a (Suc i)) (fs!i)"
      and hgi: "\<And>i. i < k \<Longrightarrow> gs!i = top1_path_product (top1_path_product (\<alpha> i) (fs!i))
                                     (top1_path_reverse (\<alpha> (Suc i)))"
  shows "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product gs (top1_constant_path x0))
      (top1_path_product (\<alpha> 0) (foldr top1_path_product fs
        (top1_path_product (top1_path_reverse (\<alpha> k)) (top1_constant_path x0))))"
proof -
  have hconst: "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_path[OF hTX hx0])
  \<comment> \<open>Proof by induction on k. The conclusion has the form:
     foldr gs const \<simeq> \<alpha>(0) * foldr fs (rev(\<alpha>(k)) * const).
     Base k=1: double associativity.
     Step k\<rightarrow>k+1: expand g0, apply IH to tail, cancel rev(\<alpha>1)*\<alpha>1.\<close>
  show ?thesis using hlen hfi hgi h\<alpha>
  proof (induction k arbitrary: gs fs \<alpha> a)
    case 0 thus ?case by (by100 simp)
  next
    case (Suc k')
    show ?case
    proof (cases "k' = 0")
      case True
      \<comment> \<open>Base k=1: ((a0*f0)*rev(a1))*const \<simeq> a0*(f0*(rev(a1)*const)).\<close>
      show ?thesis
      proof -
        have hk1: "Suc k' = 1" using True by (by100 simp)
        obtain g0 where hgs1: "gs = [g0]"
          using Suc.prems(1) hk1 by (cases gs) (by100 simp)+
        obtain f0 where hfs1: "fs = [f0]"
          using Suc.prems(2) hk1 by (cases fs) (by100 simp)+
        have hfoldr_gs: "foldr top1_path_product gs (top1_constant_path x0)
            = top1_path_product (gs ! 0) (top1_constant_path x0)"
          unfolding hgs1 by (by100 simp)
        have hfoldr_fs: "foldr top1_path_product fs
            (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))
            = top1_path_product (fs ! 0)
              (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))"
          unfolding hfs1 by (by100 simp)
        have hg0: "gs ! 0 = top1_path_product (top1_path_product (\<alpha> 0) (fs ! 0))
            (top1_path_reverse (\<alpha> (Suc k')))"
          using Suc.prems(5)[of 0] hk1 by (by100 simp)
        have h\<alpha>0: "top1_is_path_on X TX x0 (a 0) (\<alpha> 0)"
          using Suc.prems(6)[of 0] by (by100 simp)
        have h\<alpha>1: "top1_is_path_on X TX x0 (a (Suc k')) (\<alpha> (Suc k'))"
          using Suc.prems(6)[of "Suc k'"] by (by100 simp)
        have hf0: "top1_is_path_on X TX (a 0) (a (Suc 0)) (fs ! 0)"
          using Suc.prems(4)[of 0] hk1 by (by100 simp)
        have hSk': "Suc 0 = Suc k'" using hk1 by (by100 simp)
        have hrev: "top1_is_path_on X TX (a (Suc k')) x0 (top1_path_reverse (\<alpha> (Suc k')))"
          by (rule top1_path_reverse_is_path[OF h\<alpha>1])
        have h\<alpha>0f0: "top1_is_path_on X TX x0 (a (Suc k')) (top1_path_product (\<alpha> 0) (fs ! 0))"
          using top1_path_product_is_path[OF hTX h\<alpha>0 hf0] hSk' by (by100 simp)
        have hrevconst: "top1_is_path_on X TX (a (Suc k')) x0
            (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))"
          by (rule top1_path_product_is_path[OF hTX hrev hconst])
        have hassoc1: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product (top1_path_product (top1_path_product (\<alpha> 0) (fs ! 0))
              (top1_path_reverse (\<alpha> (Suc k')))) (top1_constant_path x0))
            (top1_path_product (top1_path_product (\<alpha> 0) (fs ! 0))
              (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0)))"
          by (rule Lemma_51_1_path_homotopic_sym[OF
                Theorem_51_2_associativity[OF hTX h\<alpha>0f0 hrev hconst]])
        have hf0': "top1_is_path_on X TX (a 0) (a (Suc k')) (fs ! 0)"
          using hf0 hSk' by (by100 simp)
        have hassoc2: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product (top1_path_product (\<alpha> 0) (fs ! 0))
              (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0)))
            (top1_path_product (\<alpha> 0) (top1_path_product (fs ! 0)
              (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))))"
          by (rule Lemma_51_1_path_homotopic_sym[OF
                Theorem_51_2_associativity[OF hTX h\<alpha>0 hf0' hrevconst]])
        have hchain: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product (top1_path_product (top1_path_product (\<alpha> 0) (fs ! 0))
              (top1_path_reverse (\<alpha> (Suc k')))) (top1_constant_path x0))
            (top1_path_product (\<alpha> 0) (top1_path_product (fs ! 0)
              (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))))"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTX hassoc1 hassoc2])
        show ?thesis using hchain hg0 hfoldr_gs hfoldr_fs by (by100 simp)
      qed
    next
      case False
      \<comment> \<open>Induction step: k = Suc k' with k' \<ge> 1.\<close>
      show ?thesis
      proof -
        have hk': "k' \<ge> 1" using False by (by100 simp)
        obtain g0 gs' where hgs_eq: "gs = g0 # gs'"
          using Suc.prems(1) by (cases gs) (by100 simp)+
        obtain f0 fs' where hfs_eq: "fs = f0 # fs'"
          using Suc.prems(2) by (cases fs) (by100 simp)+
        have hgs'_len: "length gs' = k'" using Suc.prems(1) hgs_eq by (by100 simp)
        have hfs'_len: "length fs' = k'" using Suc.prems(2) hfs_eq by (by100 simp)
        define \<alpha>' where "\<alpha>' i = \<alpha> (Suc i)" for i
        define a' where "a' i = a (Suc i)" for i
        have h\<alpha>': "\<And>i. i \<le> k' \<Longrightarrow> top1_is_path_on X TX x0 (a' i) (\<alpha>' i)"
          using Suc.prems(6) unfolding \<alpha>'_def a'_def by (by100 simp)
        have hfi': "\<And>i. i < k' \<Longrightarrow> top1_is_path_on X TX (a' i) (a' (Suc i)) (fs' ! i)"
        proof -
          fix i assume "i < k'"
          thus "top1_is_path_on X TX (a' i) (a' (Suc i)) (fs' ! i)"
            using Suc.prems(4)[of "Suc i"] hfs_eq unfolding a'_def by (by100 simp)
        qed
        have hgi': "\<And>i. i < k' \<Longrightarrow> gs' ! i = top1_path_product
            (top1_path_product (\<alpha>' i) (fs' ! i)) (top1_path_reverse (\<alpha>' (Suc i)))"
        proof -
          fix i assume "i < k'"
          thus "gs' ! i = top1_path_product (top1_path_product (\<alpha>' i) (fs' ! i))
              (top1_path_reverse (\<alpha>' (Suc i)))"
            using Suc.prems(5)[of "Suc i"] hgs_eq hfs_eq unfolding \<alpha>'_def by (by100 simp)
        qed
        have hIH: "top1_path_homotopic_on X TX x0 x0
            (foldr top1_path_product gs' (top1_constant_path x0))
            (top1_path_product (\<alpha>' 0) (foldr top1_path_product fs'
              (top1_path_product (top1_path_reverse (\<alpha>' k')) (top1_constant_path x0))))"
          unfolding \<alpha>'_def a'_def
          by (rule Suc.IH[of gs' fs' "\<lambda>i. a (Suc i)" "\<lambda>i. \<alpha> (Suc i)",
              OF hgs'_len hfs'_len hk' _ _ _])
             (use hfi' hgi' h\<alpha>' in \<open>unfold \<alpha>'_def a'_def, by100 simp\<close>)+
        \<comment> \<open>Now combine g0 * IH to get the result.
           g0 = (\<alpha>(0)*f0)*rev(\<alpha>(1)).
           foldr gs const = g0 * foldr gs' const
           \<simeq> g0 * (\<alpha>(1) * foldr fs' (rev(\<alpha>(Suc k')) * const))  [by IH]
           = ((\<alpha>(0)*f0)*rev(\<alpha>(1))) * (\<alpha>(1) * R)                  [expand g0]
           \<simeq> (\<alpha>(0)*f0) * (rev(\<alpha>(1)) * (\<alpha>(1) * R))              [assoc]
           \<simeq> (\<alpha>(0)*f0) * ((rev(\<alpha>(1)) * \<alpha>(1)) * R)              [assoc]
           \<simeq> (\<alpha>(0)*f0) * (const * R)                             [inverse]
           \<simeq> (\<alpha>(0)*f0) * R                                       [left id]
           \<simeq> \<alpha>(0) * (f0 * R)                                     [assoc]
           = \<alpha>(0) * foldr fs (rev(\<alpha>(Suc k')) * const).\<close>
        \<comment> \<open>First establish path facts needed for algebra.\<close>
        have hg0_eq: "g0 = top1_path_product (top1_path_product (\<alpha> 0) (fs ! 0))
            (top1_path_reverse (\<alpha> (Suc 0)))"
          using Suc.prems(5)[of 0] hgs_eq by (by100 simp)
        have hf0_eq: "f0 = fs ! 0" using hfs_eq by (by100 simp)
        have h\<alpha>0: "top1_is_path_on X TX x0 (a 0) (\<alpha> 0)"
          using Suc.prems(6)[of 0] by (by100 simp)
        have h\<alpha>1: "top1_is_path_on X TX x0 (a 1) (\<alpha> 1)"
          using Suc.prems(6)[of 1] by (by100 simp)
        have hf0_path: "top1_is_path_on X TX (a 0) (a 1) f0"
          using Suc.prems(4)[of 0] hfs_eq by (by100 simp)
        have hrev\<alpha>1: "top1_is_path_on X TX (a 1) x0 (top1_path_reverse (\<alpha> 1))"
          by (rule top1_path_reverse_is_path[OF h\<alpha>1])
        have h\<alpha>0f0: "top1_is_path_on X TX x0 (a 1) (top1_path_product (\<alpha> 0) f0)"
          using top1_path_product_is_path[OF hTX h\<alpha>0 hf0_path] by simp
        \<comment> \<open>Define R = foldr fs' (rev(\<alpha>(Suc k')) * const).\<close>
        define R where "R = foldr top1_path_product fs'
            (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))"
        \<comment> \<open>R is a path from a(1) to x0.\<close>
        have h\<alpha>Sk': "top1_is_path_on X TX x0 (a (Suc k')) (\<alpha> (Suc k'))"
          using Suc.prems(6)[of "Suc k'"] by (by100 simp)
        have hrev\<alpha>Sk': "top1_is_path_on X TX (a (Suc k')) x0 (top1_path_reverse (\<alpha> (Suc k')))"
          by (rule top1_path_reverse_is_path[OF h\<alpha>Sk'])
        have hrev\<alpha>Sk'_const: "top1_is_path_on X TX (a (Suc k')) x0
            (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))"
          by (rule top1_path_product_is_path[OF hTX hrev\<alpha>Sk' hconst])
        have ha1: "a 1 = a' 0" unfolding a'_def by simp
        have hfi'_len: "\<And>i. i < length fs' \<Longrightarrow> top1_is_path_on X TX (a' i) (a' (Suc i)) (fs'!i)"
          using hfi' hfs'_len by (by100 simp)
        have hbase_path: "top1_is_path_on X TX (a' (length fs')) x0
            (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0))"
          using hrev\<alpha>Sk'_const hfs'_len unfolding a'_def by (by100 simp)
        have hR: "top1_is_path_on X TX (a 1) x0 R"
          unfolding R_def ha1
          by (rule foldr_path_product_is_path[OF hTX hfi'_len hbase_path])
        \<comment> \<open>\<alpha>1 * R is a path from x0 to x0.\<close>
        have h\<alpha>1R: "top1_is_path_on X TX x0 x0 (top1_path_product (\<alpha> 1) R)"
          by (rule top1_path_product_is_path[OF hTX h\<alpha>1 hR])
        \<comment> \<open>foldr gs const = g0 * foldr gs' const.\<close>
        have hfoldr_gs: "foldr top1_path_product gs (top1_constant_path x0) =
            top1_path_product g0 (foldr top1_path_product gs' (top1_constant_path x0))"
          unfolding hgs_eq by (by100 simp)
        \<comment> \<open>foldr fs (rev(\<alpha>(Suc k'))*const) = f0 * R.\<close>
        have hfoldr_fs: "foldr top1_path_product fs
            (top1_path_product (top1_path_reverse (\<alpha> (Suc k'))) (top1_constant_path x0)) =
            top1_path_product f0 R"
          unfolding hfs_eq R_def by (by100 simp)
        \<comment> \<open>Step 1: g0 * foldr gs' \<simeq> g0 * (\<alpha>(1) * R) via IH.\<close>
        have hIH': "top1_path_homotopic_on X TX x0 x0
            (foldr top1_path_product gs' (top1_constant_path x0))
            (top1_path_product (\<alpha> 1) R)"
          using hIH unfolding \<alpha>'_def R_def by (by100 simp)
        have hSuc0: "Suc 0 = 1" by simp
        have hg0_path: "top1_is_path_on X TX x0 x0 g0"
          unfolding hg0_eq hf0_eq[symmetric] hSuc0
          by (rule top1_path_product_is_path[OF hTX
                top1_path_product_is_path[OF hTX h\<alpha>0 hf0_path] hrev\<alpha>1])
        have hstep1: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product g0 (foldr top1_path_product gs' (top1_constant_path x0)))
            (top1_path_product g0 (top1_path_product (\<alpha> 1) R))"
          by (rule path_homotopic_product_right[OF hTX hIH' hg0_path])
        \<comment> \<open>Step 2: ((\<alpha>0*f0)*rev(\<alpha>1)) * (\<alpha>1*R) \<simeq> (\<alpha>0*f0) * (rev(\<alpha>1) * (\<alpha>1*R)) [assoc].\<close>
        have hstep2: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product (top1_path_product (top1_path_product (\<alpha> 0) f0)
              (top1_path_reverse (\<alpha> 1))) (top1_path_product (\<alpha> 1) R))
            (top1_path_product (top1_path_product (\<alpha> 0) f0)
              (top1_path_product (top1_path_reverse (\<alpha> 1)) (top1_path_product (\<alpha> 1) R)))"
          by (rule Lemma_51_1_path_homotopic_sym[OF
                Theorem_51_2_associativity[OF hTX h\<alpha>0f0 hrev\<alpha>1 h\<alpha>1R]])
        \<comment> \<open>Step 3: rev(\<alpha>1) * (\<alpha>1*R) \<simeq> (rev(\<alpha>1)*\<alpha>1) * R [assoc].\<close>
        have hstep3_inner: "top1_path_homotopic_on X TX (a 1) x0
            (top1_path_product (top1_path_reverse (\<alpha> 1)) (top1_path_product (\<alpha> 1) R))
            (top1_path_product (top1_path_product (top1_path_reverse (\<alpha> 1)) (\<alpha> 1)) R)"
          by (rule Theorem_51_2_associativity[OF hTX hrev\<alpha>1 h\<alpha>1 hR])
        \<comment> \<open>Step 4: rev(\<alpha>1)*\<alpha>1 \<simeq> const [inverse].\<close>
        have hstep4_inner: "top1_path_homotopic_on X TX (a 1) (a 1)
            (top1_path_product (top1_path_reverse (\<alpha> 1)) (\<alpha> 1))
            (top1_constant_path (a 1))"
          by (rule Theorem_51_2_invgerse_right[OF hTX h\<alpha>1])
        \<comment> \<open>Step 5: const * R \<simeq> R [left identity].\<close>
        have ha1_X: "a 1 \<in> X"
        proof -
          have hcont: "\<forall>x\<in>top1_unit_interval. \<alpha> 1 x \<in> X"
            using h\<alpha>1 unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
          have h1I: "(1::real) \<in> top1_unit_interval"
            unfolding top1_unit_interval_def by (by100 simp)
          have "\<alpha> 1 1 \<in> X" using hcont h1I by (by100 blast)
          moreover have "\<alpha> 1 1 = a 1"
            using h\<alpha>1 unfolding top1_is_path_on_def by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        qed
        have hstep5_inner: "top1_path_homotopic_on X TX (a 1) x0
            (top1_path_product (top1_constant_path (a 1)) R)
            R"
          by (rule Theorem_51_2_left_identity[OF hTX hR])
        \<comment> \<open>Step 4': (rev(\<alpha>1)*\<alpha>1)*R \<simeq> const(a1)*R.\<close>
        have hstep4_lifted: "top1_path_homotopic_on X TX (a 1) x0
            (top1_path_product (top1_path_product (top1_path_reverse (\<alpha> 1)) (\<alpha> 1)) R)
            (top1_path_product (top1_constant_path (a 1)) R)"
          by (rule path_homotopic_product_left[OF hTX hstep4_inner hR])
        \<comment> \<open>Chain steps 3-5: rev(\<alpha>1)*(\<alpha>1*R) \<simeq> R.\<close>
        have hcancel: "top1_path_homotopic_on X TX (a 1) x0
            (top1_path_product (top1_path_reverse (\<alpha> 1)) (top1_path_product (\<alpha> 1) R))
            R"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTX
                Lemma_51_1_path_homotopic_trans[OF hTX hstep3_inner hstep4_lifted]
                hstep5_inner])
        \<comment> \<open>Lift to: (\<alpha>0*f0) * (rev(\<alpha>1)*(\<alpha>1*R)) \<simeq> (\<alpha>0*f0) * R.\<close>
        have hstep23456: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product (top1_path_product (\<alpha> 0) f0)
              (top1_path_product (top1_path_reverse (\<alpha> 1)) (top1_path_product (\<alpha> 1) R)))
            (top1_path_product (top1_path_product (\<alpha> 0) f0) R)"
          by (rule path_homotopic_product_right[OF hTX hcancel h\<alpha>0f0])
        \<comment> \<open>Step 6: (\<alpha>0*f0)*R \<simeq> \<alpha>0*(f0*R) [assoc].\<close>
        have hstep6: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product (top1_path_product (\<alpha> 0) f0) R)
            (top1_path_product (\<alpha> 0) (top1_path_product f0 R))"
          by (rule Lemma_51_1_path_homotopic_sym[OF
                Theorem_51_2_associativity[OF hTX h\<alpha>0 hf0_path hR]])
        \<comment> \<open>Chain everything together.\<close>
        have hstep1': "top1_path_homotopic_on X TX x0 x0
            (top1_path_product g0 (top1_path_product (\<alpha> 1) R))
            (top1_path_product (top1_path_product (\<alpha> 0) f0)
              (top1_path_product (top1_path_reverse (\<alpha> 1)) (top1_path_product (\<alpha> 1) R)))"
          using hstep2 hg0_eq hf0_eq by (by100 simp)
        have hfull: "top1_path_homotopic_on X TX x0 x0
            (top1_path_product g0 (foldr top1_path_product gs' (top1_constant_path x0)))
            (top1_path_product (\<alpha> 0) (top1_path_product f0 R))"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTX
                Lemma_51_1_path_homotopic_trans[OF hTX
                  Lemma_51_1_path_homotopic_trans[OF hTX hstep1 hstep1']
                  hstep23456]
                hstep6])
        show ?thesis using hfull hfoldr_gs hfoldr_fs by (by100 simp)
      qed
    qed
  qed
qed

\<comment> \<open>Telescoping lemma for conjugated path products (Munkres 59.1 Step 2).
   If gi = (\<alpha>i * fi) * rev(\<alpha>(i+1)) and \<alpha>0 = \<alpha>n = const_x0,
   then g0*g1*...*g(n-1)*const \<simeq> f0*f1*...*f(n-1)*const.\<close>
lemma telescoping_conjugated_product:
  assumes hTX: "is_topology_on X TX" and hx0: "x0 \<in> X"
      and hn: "n \<ge> 1"
      and hfs: "length fs = n" and hgs: "length gs = n"
      and h\<alpha>: "\<And>i. i \<le> n \<Longrightarrow> top1_is_path_on X TX x0 (a i) (\<alpha> i)"
      and hfi: "\<And>i. i < n \<Longrightarrow> top1_is_path_on X TX (a i) (a (Suc i)) (fs!i)"
      and hgi: "\<And>i. i < n \<Longrightarrow> gs!i = top1_path_product (top1_path_product (\<alpha> i) (fs!i))
                                     (top1_path_reverse (\<alpha> (Suc i)))"
      and h\<alpha>0: "\<alpha> 0 = top1_constant_path x0"
      and h\<alpha>n: "\<alpha> n = top1_constant_path x0"
      and ha0: "a 0 = x0" and han: "a n = x0"
  shows "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product fs (top1_constant_path x0))
      (foldr top1_path_product gs (top1_constant_path x0))"
proof -
  \<comment> \<open>By induction on n. We prove a slightly stronger statement:
     foldr pp gs const \<simeq> \<alpha>(0) * (foldr pp fs (rev(\<alpha>(n)) * const)).
     Then use \<alpha>(0) = \<alpha>(n) = const to simplify.\<close>
  \<comment> \<open>Helper: reverse of constant path is itself.\<close>
  have hrev_const: "top1_path_reverse (top1_constant_path x0) = top1_constant_path x0"
    unfolding top1_path_reverse_def top1_constant_path_def by (rule ext) simp
  have hconst: "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_path[OF hTX hx0])
  \<comment> \<open>The conjugation with \<alpha>(0) = const and \<alpha>(n) = const simplifies:
     const * (foldr fi (rev(const) * const)) \<simeq> const * (foldr fi (const * const))
     \<simeq> const * (foldr fi const) \<simeq> foldr fi const.\<close>
  \<comment> \<open>For the main argument, we show element-wise that the telescoping cancels.
     We prove this by a direct chain of homotopies for the m=1 base case,
     and then generalize by induction.\<close>
  \<comment> \<open>Proof: show foldr gs const \<simeq> foldr fs const by showing
     foldr gs const \<simeq> \<alpha>(0) * foldr fs (rev(\<alpha>(n)) * const)
     and then simplifying with \<alpha>(0) = \<alpha>(n) = const.\<close>
  \<comment> \<open>Step 1: foldr gs const \<simeq> \<alpha>(0) * foldr fs (rev(\<alpha>(n)) * const).\<close>
  have hstep1: "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product gs (top1_constant_path x0))
      (top1_path_product (\<alpha> 0) (foldr top1_path_product fs
        (top1_path_product (top1_path_reverse (\<alpha> n)) (top1_constant_path x0))))"
    using telescoping_core[OF hTX hx0 hgs hfs hn h\<alpha> hfi hgi] .
  \<comment> \<open>Was: Main telescoping induction on n.
       Base n=1: ((\<alpha>0*f0)*rev(\<alpha>1))*const \<simeq> \<alpha>0*(f0*(rev(\<alpha>1)*const)) by associativity.
       Step: g0*(foldr gs' const) \<simeq> g0*(\<alpha>1*foldr fs'(rev(\<alpha>n)*const)) (by IH)
             \<simeq> ((\<alpha>0*f0)*rev(\<alpha>1))*(\<alpha>1*...) (expand g0)
             \<simeq> (\<alpha>0*f0)*(rev(\<alpha>1)*\<alpha>1)*... (reassoc)
             \<simeq> (\<alpha>0*f0)*const*... (inverse cancel)
             \<simeq> (\<alpha>0*f0)*... (identity)
             = \<alpha>0*f0*foldr fs'(rev(\<alpha>n)*const)
             = \<alpha>0*foldr(f0#fs')(rev(\<alpha>n)*const).
       Each step uses Theorem_51_2 (assoc/id/inv) + product_left/right + trans.
       ~40 lines of Isabelle path algebra.\<close>
  \<comment> \<open>Step 2: Simplify RHS using \<alpha>(0) = \<alpha>(n) = const_x0.\<close>
  have hstep2: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product (\<alpha> 0) (foldr top1_path_product fs
        (top1_path_product (top1_path_reverse (\<alpha> n)) (top1_constant_path x0))))
      (foldr top1_path_product fs (top1_constant_path x0))"
  proof -
    \<comment> \<open>\<alpha>(0) = const, \<alpha>(n) = const, rev(const) = const.\<close>
    have "top1_path_product (top1_path_reverse (\<alpha> n)) (top1_constant_path x0)
        = top1_path_product (top1_constant_path x0) (top1_constant_path x0)"
      using h\<alpha>n hrev_const by simp
    moreover have "top1_path_homotopic_on X TX x0 x0
        (top1_path_product (top1_constant_path x0) (top1_constant_path x0))
        (top1_constant_path x0)"
      by (rule Theorem_51_2_left_identity[OF hTX hconst])
    ultimately have hrev_simp: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product (top1_path_reverse (\<alpha> n)) (top1_constant_path x0))
        (top1_constant_path x0)" by simp
    \<comment> \<open>Replace rev(\<alpha>n)*const with const in the foldr, then remove \<alpha>(0)=const via left identity.\<close>
    \<comment> \<open>Step 2a: foldr respects base homotopy: if base1 \<simeq> base2 then foldr fs base1 \<simeq> foldr fs base2.\<close>
    have hfoldr_base: "\<And>base1 base2. top1_path_homotopic_on X TX x0 x0 base1 base2 \<Longrightarrow>
        top1_path_homotopic_on X TX x0 x0
          (foldr top1_path_product fs base1) (foldr top1_path_product fs base2)"
      using foldr_path_product_base_homotopic[OF hTX, where a="\<lambda>i. a i" and fs=fs]
            hfi ha0 han hfs by simp
    have hstep2a: "top1_path_homotopic_on X TX x0 x0
        (foldr top1_path_product fs (top1_path_product (top1_path_reverse (\<alpha> n)) (top1_constant_path x0)))
        (foldr top1_path_product fs (top1_constant_path x0))"
      by (rule hfoldr_base[OF hrev_simp])
    \<comment> \<open>Step 2b: \<alpha>(0) = const, so const * foldr \<simeq> foldr (left identity).\<close>
    have hfoldr_path: "top1_is_path_on X TX x0 x0
        (foldr top1_path_product fs (top1_constant_path x0))"
      using foldr_path_product_is_path[OF hTX, where a="\<lambda>i. a i" and fs=fs and y=x0]
            hfi hconst ha0 han hfs by simp
    have hstep2b: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product (top1_constant_path x0) (foldr top1_path_product fs (top1_constant_path x0)))
        (foldr top1_path_product fs (top1_constant_path x0))"
      by (rule Theorem_51_2_left_identity[OF hTX hfoldr_path])
    \<comment> \<open>Combine: \<alpha>0 * foldr(rev(\<alpha>n)*const) \<simeq> const * foldr(rev(\<alpha>n)*const)
                                                \<simeq> const * foldr(const) \<simeq> foldr(const).\<close>
    have hstep2c: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product (\<alpha> 0) (foldr top1_path_product fs
          (top1_path_product (top1_path_reverse (\<alpha> n)) (top1_constant_path x0))))
        (top1_path_product (top1_constant_path x0) (foldr top1_path_product fs (top1_constant_path x0)))"
      using h\<alpha>0 path_homotopic_product_right[OF hTX hstep2a hconst] by simp
    show ?thesis
      using Lemma_51_1_path_homotopic_trans[OF hTX hstep2c hstep2b] .
  qed
  \<comment> \<open>Combine: foldr gs \<simeq> ... \<simeq> foldr fs. Use sym to get foldr fs \<simeq> foldr gs.\<close>
  have "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product gs (top1_constant_path x0))
      (foldr top1_path_product fs (top1_constant_path x0))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX hstep1 hstep2])
  thus ?thesis by (rule Lemma_51_1_path_homotopic_sym)
qed

text \<open>Theorem 51.3 (Munkres): Reparametrization preserves path homotopy class.
  If f is a path from x0 to x1, and 0=a0<a1<...<an=1, and fi(t) = f(a_{i-1}+t*(a_i-a_{i-1})),
  then [f] = [f1]*[f2]*...*[fn].

  We first prove the key splitting lemma: f \<simeq> f_L * f_R where
  f_L(t) = f(at) and f_R(t) = f(a+t(1-a)), for 0<a<1.
  Then the full theorem follows by induction on n.\<close>

lemma path_product_split:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
      and ha: "0 < a" "a < 1"
  defines "f_L \<equiv> \<lambda>t. f (a * t)"
  defines "f_R \<equiv> \<lambda>t. f (a + (1-a) * t)"
  shows "top1_path_homotopic_on X TX x0 x1 f (top1_path_product f_L f_R)"
proof -
  \<comment> \<open>The homotopy is H(s,t) = f(\<phi>_s(t)) where \<phi>_s interpolates linearly between
     t (at s=0) and the path-product reparametrization (at s=1).
     \<phi>_s(t) = (1-s)*t + s*(2*a*t) for t \<le> 1/2
     \<phi>_s(t) = (1-s)*t + s*(a + (2*t-1)*(1-a)) for t > 1/2.\<close>
  define \<phi> :: "real \<Rightarrow> real \<Rightarrow> real" where
    "\<phi> s t = (if t \<le> 1/2 then (1-s)*t + s*(2*a*t) else (1-s)*t + s*(a + (2*t-1)*(1-a)))" for s t
  \<comment> \<open>Key properties of \<phi>.\<close>
  have h\<phi>0: "\<And>t. \<phi> 0 t = t" unfolding \<phi>_def by simp
  have h\<phi>1: "\<And>t. t \<le> 1/2 \<Longrightarrow> \<phi> 1 t = 2*a*t" unfolding \<phi>_def by simp
  have h\<phi>1': "\<And>t. t > 1/2 \<Longrightarrow> \<phi> 1 t = a + (2*t-1)*(1-a)" unfolding \<phi>_def by simp
  have h\<phi>_start: "\<And>s. \<phi> s 0 = 0" unfolding \<phi>_def by simp
  have h\<phi>_end: "\<And>s. \<phi> s 1 = 1" unfolding \<phi>_def by simp
  have h\<phi>_half: "\<And>s. \<phi> s (1/2) = (1-s)/2 + s*a" unfolding \<phi>_def by (simp add: field_simps)
  \<comment> \<open>H(s,t) = f(\<phi>(s,t)).\<close>
  define H where "H p = f (\<phi> (fst p) (snd p))" for p :: "real \<times> real"
  \<comment> \<open>H is a path homotopy from f to f_L * f_R.\<close>
  have hH0: "\<And>t. H (0, t) = f t" unfolding H_def using h\<phi>0 by simp
  have hH1_le: "\<And>t. t \<le> 1/2 \<Longrightarrow> H (1, t) = f_L (2*t)"
    unfolding H_def f_L_def using h\<phi>1 by (simp add: field_simps)
  have hH1_gt: "\<And>t. t > 1/2 \<Longrightarrow> H (1, t) = f_R (2*t - 1)"
  proof -
    fix t :: real assume ht: "t > 1/2"
    have "\<phi> 1 t = a + (2*t-1)*(1-a)" using h\<phi>1'[OF ht] .
    moreover have "a + (2*t-1)*(1-a) = a + (1-a)*(2*t-1)" by (simp add: mult.commute)
    ultimately show "H (1, t) = f_R (2*t - 1)" unfolding H_def f_R_def by simp
  qed
  have hf0: "f 0 = x0" using hf unfolding top1_is_path_on_def by (by100 blast)
  have hf1: "f 1 = x1" using hf unfolding top1_is_path_on_def by (by100 blast)
  have hH_start: "\<And>s. H (s, 0) = x0"
    unfolding H_def using h\<phi>_start hf0 by simp
  have hH_end: "\<And>s. H (s, 1) = x1"
    unfolding H_def using h\<phi>_end hf1 by simp
  \<comment> \<open>H(1,t) = path_product f_L f_R (t).\<close>
  have hH1: "\<And>t. t \<in> I_set \<Longrightarrow> H (1, t) = top1_path_product f_L f_R t"
  proof -
    fix t assume ht: "t \<in> I_set"
    show "H (1, t) = top1_path_product f_L f_R t"
    proof (cases "t \<le> 1/2")
      case True
      hence "H (1, t) = f_L (2*t)" using hH1_le by simp
      moreover have "top1_path_product f_L f_R t = f_L (2*t)"
        using True unfolding top1_path_product_def by simp
      ultimately show ?thesis by simp
    next
      case False
      hence hgt: "t > 1/2" by simp
      hence "H (1, t) = f_R (2*t - 1)" using hH1_gt by simp
      moreover have "top1_path_product f_L f_R t = f_R (2*t - 1)"
        using False unfolding top1_path_product_def by simp
      ultimately show ?thesis by simp
    qed
  qed
  \<comment> \<open>\<phi> maps I\<times>I to I.\<close>
  have h\<phi>_range: "\<And>s t. s \<in> I_set \<Longrightarrow> t \<in> I_set \<Longrightarrow> \<phi> s t \<in> I_set"
  proof -
    fix s t :: real assume hs: "s \<in> I_set" and ht: "t \<in> I_set"
    have hs01: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
    have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
    show "\<phi> s t \<in> I_set"
    proof (cases "t \<le> 1/2")
      case True
      \<comment> \<open>\<phi> s t = (1-s)*t + s*2*a*t = t*(1-s+s*2*a). In [0, t*max(1,2a)] \<subseteq> [0,1].\<close>
      have "\<phi> s t = (1-s)*t + s*(2*a*t)" unfolding \<phi>_def using True by simp
      moreover have "(1-s)*t + s*(2*a*t) \<ge> 0"
        using hs01 ht01 ha(1) by (intro add_nonneg_nonneg mult_nonneg_nonneg) linarith+
      moreover have "(1-s)*t + s*(2*a*t) \<le> 1"
      proof -
        have "(1-s)*t \<le> (1-s) * (1/2)" using True hs01 by (intro mult_left_mono) linarith+
        moreover have "s*(2*a*t) \<le> s*(2*a*(1/2))" using True hs01 ha by (intro mult_left_mono mult_left_mono) linarith+
        hence "s*(2*a*t) \<le> s*a" by simp
        ultimately have "(1-s)*t + s*(2*a*t) \<le> (1-s)/2 + s*a" by linarith
        also have "\<dots> \<le> (1-s)/2 + s"
        proof -
          have "s*a \<le> s*1" by (rule mult_left_mono) (use hs01 ha in linarith)+
          thus ?thesis by linarith
        qed
        also have "\<dots> = (1+s)/2" by (simp add: field_simps)
        also have "\<dots> \<le> 1" using hs01 by simp
        finally show ?thesis .
      qed
      ultimately show ?thesis unfolding top1_unit_interval_def by simp
    next
      case False
      have hge: "t > 1/2" using False by simp
      have "\<phi> s t = (1-s)*t + s*(a + (2*t-1)*(1-a))" unfolding \<phi>_def using False by simp
      moreover have "(1-s)*t + s*(a + (2*t-1)*(1-a)) \<ge> 0"
        using hs01 ht01 ha hge
        by (intro add_nonneg_nonneg mult_nonneg_nonneg) linarith+
      moreover have "(1-s)*t + s*(a + (2*t-1)*(1-a)) \<le> 1"
      proof -
        have "(1-s)*t \<le> (1-s)*1" by (rule mult_left_mono) (use hs01 ht01 in linarith)+
        hence "(1-s)*t \<le> 1-s" by simp
        moreover have "a + (2*t-1)*(1-a) \<le> 1"
        proof -
          have "(2*t-1) \<le> 1" using ht01 by linarith
          hence "(2*t-1)*(1-a) \<le> 1*(1-a)" by (rule mult_right_mono) (use ha in linarith)
          hence "(2*t-1)*(1-a) \<le> 1-a" by simp
          thus ?thesis by linarith
        qed
        hence "s*(a + (2*t-1)*(1-a)) \<le> s*1"
          by (rule mult_left_mono) (use hs01 in linarith)+
        hence "s*(a + (2*t-1)*(1-a)) \<le> s" by simp
        ultimately show ?thesis by linarith
      qed
      ultimately show ?thesis unfolding top1_unit_interval_def by simp
    qed
  qed
  \<comment> \<open>H maps I\<times>I to X.\<close>
  have hf_range: "\<And>u. u \<in> I_set \<Longrightarrow> f u \<in> X"
    using hf unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
  have hH_range: "\<And>s t. s \<in> I_set \<Longrightarrow> t \<in> I_set \<Longrightarrow> H (s, t) \<in> X"
    unfolding H_def using h\<phi>_range hf_range by simp
  \<comment> \<open>\<phi> is continuous: piecewise linear, pieces agree at t=1/2.\<close>
  have h\<phi>_cont: "continuous_on (I_set \<times> I_set) (\<lambda>p. \<phi> (fst p) (snd p))"
  proof -
    \<comment> \<open>The two pieces as functions of (s,t).\<close>
    define g1 :: "real \<times> real \<Rightarrow> real" where "g1 p = (1-fst p)*(snd p) + (fst p)*(2*a*(snd p))" for p
    define g2 :: "real \<times> real \<Rightarrow> real" where "g2 p = (1-fst p)*(snd p) + (fst p)*(a + (2*(snd p)-1)*(1-a))" for p
    \<comment> \<open>Both are continuous (polynomials).\<close>
    have hg1_cont: "continuous_on UNIV g1" unfolding g1_def by (intro continuous_intros)
    have hg2_cont: "continuous_on UNIV g2" unfolding g2_def by (intro continuous_intros)
    \<comment> \<open>Closed halves.\<close>
    define A where "A = {p :: real \<times> real. snd p \<le> 1/2}"
    define B where "B = {p :: real \<times> real. snd p \<ge> 1/2}"
    have hA_closed: "closed A" unfolding A_def
      by (intro closed_Collect_le) (intro continuous_intros)+
    have hB_closed: "closed B" unfolding B_def
      by (intro closed_Collect_le) (intro continuous_intros)+
    \<comment> \<open>On the boundary t=1/2, both pieces give the same value.\<close>
    have hagree: "\<And>p. snd p = 1/2 \<Longrightarrow> g1 p = g2 p"
      unfolding g1_def g2_def by (simp add: field_simps)
    \<comment> \<open>The piecewise function.\<close>
    have hpw: "\<And>p. p \<in> A \<union> B \<Longrightarrow> \<phi> (fst p) (snd p) = (if snd p \<le> 1/2 then g1 p else g2 p)"
      unfolding \<phi>_def g1_def g2_def A_def B_def by auto
    have hpw_cont: "continuous_on (A \<union> B) (\<lambda>p. if snd p \<le> 1/2 then g1 p else g2 p)"
    proof (rule continuous_on_If[OF hA_closed hB_closed])
      show "continuous_on A g1" using continuous_on_subset[OF hg1_cont] by (by100 blast)
      show "continuous_on B g2" using continuous_on_subset[OF hg2_cont] by (by100 blast)
      show "\<And>x. x \<in> A \<Longrightarrow> \<not> snd x \<le> 1 / 2 \<Longrightarrow> g1 x = g2 x" unfolding A_def by simp
      show "\<And>x. x \<in> B \<Longrightarrow> snd x \<le> 1 / 2 \<Longrightarrow> g1 x = g2 x" using hagree unfolding B_def by force
    qed
    have hI_sub: "I_set \<times> I_set \<subseteq> A \<union> B" unfolding A_def B_def top1_unit_interval_def by auto
    have hpw_cont_I: "continuous_on (I_set \<times> I_set) (\<lambda>p. if snd p \<le> 1/2 then g1 p else g2 p)"
      by (rule continuous_on_subset[OF hpw_cont hI_sub])
    show ?thesis
    proof (rule continuous_on_cong[THEN iffD2, OF refl _ hpw_cont_I])
      fix p assume "p \<in> I_set \<times> I_set"
      show "\<phi> (fst p) (snd p) = (if snd p \<le> 1/2 then g1 p else g2 p)"
        unfolding \<phi>_def g1_def g2_def by auto
    qed
  qed
  \<comment> \<open>H is continuous.\<close>
  have h\<phi>_map: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top
      (\<lambda>p. \<phi> (fst p) (snd p))"
    by (rule top1_continuous_map_on_II_to_I) (use h\<phi>_range in auto, rule h\<phi>_cont)
  have hf_cont_top: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_path_on_def by (by100 blast)
  have hH_comp: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX
      (f \<circ> (\<lambda>p. \<phi> (fst p) (snd p)))"
    by (rule top1_continuous_map_on_comp[OF h\<phi>_map hf_cont_top])
  have hH_eq: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> (f \<circ> (\<lambda>p. \<phi> (fst p) (snd p))) p = H p"
    unfolding H_def comp_def by simp
  have hH_cont: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX H"
    using iffD1[OF top1_continuous_map_on_cong[of "I_set \<times> I_set" "f \<circ> (\<lambda>p. \<phi> (fst p) (snd p))" H]
      hH_comp]
    using hH_eq by (by100 blast)
  \<comment> \<open>Assemble the path homotopy. The definition uses F(s,t) where s=path, t=homotopy.\<close>
  define F where "F p = H (snd p, fst p)" for p :: "real \<times> real"
  have hswap_cont: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
      (I_set \<times> I_set) (product_topology_on I_top I_top) (\<lambda>p. (snd p, fst p))"
  proof -
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTP: "is_topology_on (I_set \<times> I_set) (product_topology_on I_top I_top)"
      by (rule product_topology_on_is_topology_on[OF hTI hTI])
    have hpi1: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top pi1"
      by (rule top1_continuous_pi1[OF hTI hTI])
    have hpi2: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top pi2"
      by (rule top1_continuous_pi2[OF hTI hTI])
    \<comment> \<open>swap = (pi2, pi1). Use Theorem 18.4 to get continuity.\<close>
    have hpi2_eq: "pi1 \<circ> (\<lambda>p :: real \<times> real. (snd p, fst p)) = pi2"
      unfolding pi1_def pi2_def by (rule ext) simp
    have hpi1_eq: "pi2 \<circ> (\<lambda>p :: real \<times> real. (snd p, fst p)) = pi1"
      unfolding pi1_def pi2_def by (rule ext) simp
    show ?thesis
      using iffD2[OF Theorem_18_4[OF hTP hTI hTI, of "(\<lambda>p. (snd p, fst p))"]]
      using hpi2 hpi1 unfolding hpi2_eq hpi1_eq by (by100 blast)
  qed
  have hF_comp: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX
      (H \<circ> (\<lambda>p. (snd p, fst p)))"
    by (rule top1_continuous_map_on_comp[OF hswap_cont hH_cont])
  have hF_eq: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> (H \<circ> (\<lambda>p. (snd p, fst p))) p = F p"
    unfolding F_def comp_def by simp
  have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
    unfolding II_topology_def
    using iffD1[OF top1_continuous_map_on_cong[of "I_set \<times> I_set" "H \<circ> (\<lambda>p. (snd p, fst p))" F]
      hF_comp]
    using hF_eq by (by100 blast)
  \<comment> \<open>f_L = f \<circ> (\<lambda>t. a*t) and f_R = f \<circ> (\<lambda>t. a+(1-a)*t) are paths.\<close>
  have hscale_range: "\<And>t. t \<in> I_set \<Longrightarrow> a * t \<in> I_set"
  proof -
    fix t assume "t \<in> I_set"
    hence ht01: "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by auto
    have "0 \<le> a * t" using ha ht01 by (intro mult_nonneg_nonneg) linarith+
    moreover have "a * t \<le> 1" using ha ht01 by (intro mult_le_one) linarith+
    ultimately show "a * t \<in> I_set" unfolding top1_unit_interval_def by simp
  qed
  have hshift_range: "\<And>t. t \<in> I_set \<Longrightarrow> a + (1-a) * t \<in> I_set"
  proof -
    fix t assume "t \<in> I_set"
    hence ht01: "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by auto
    have "a + (1-a)*t \<ge> 0" using ha ht01 by (intro add_nonneg_nonneg mult_nonneg_nonneg) linarith+
    moreover have "a + (1-a)*t \<le> a + (1-a)*1"
      by (intro add_left_mono mult_left_mono) (use ha ht01 in linarith)+
    hence "a + (1-a)*t \<le> 1" by simp
    ultimately show "a + (1-a)*t \<in> I_set" unfolding top1_unit_interval_def by simp
  qed
  have hfL_cont_top: "top1_continuous_map_on I_set I_top X TX f_L"
  proof -
    have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
      using hf unfolding top1_is_path_on_def by (by100 blast)
    have hf_range': "\<And>u. u \<in> I_set \<Longrightarrow> f u \<in> X"
      using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
    have hf_pre: "\<And>V. V \<in> TX \<Longrightarrow> {u \<in> I_set. f u \<in> V} \<in> I_top"
      using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix t assume "t \<in> I_set"
      thus "f_L t \<in> X" unfolding f_L_def using hscale_range hf_range' by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      \<comment> \<open>{t \<in> I | f(at) \<in> V} = {t \<in> I | at \<in> {u \<in> I | f u \<in> V}}.\<close>
      have hW: "{u \<in> I_set. f u \<in> V} \<in> I_top" by (rule hf_pre[OF hV])
      \<comment> \<open>I_top = subspace_topology {0..1} (euclidean). {u \<in> I | f u \<in> V} = I \<inter> W for some open W.\<close>
      obtain W where hoW: "open W" and hWI: "{u \<in> I_set. f u \<in> V} = I_set \<inter> W"
        using hW unfolding top1_unit_interval_topology_def subspace_topology_def top1_open_sets_def
        by auto
      \<comment> \<open>{t \<in> I | at \<in> I \<inter> W} = {t \<in> I | at \<in> W} (since at \<in> I for t \<in> I).\<close>
      have "{t \<in> I_set. f_L t \<in> V} = {t \<in> I_set. a*t \<in> W}"
      proof (intro Collect_cong conj_cong refl)
        fix t assume "t \<in> I_set"
        hence "a*t \<in> I_set" by (rule hscale_range)
        thus "(f_L t \<in> V) = (a*t \<in> W)" unfolding f_L_def using hWI by (by100 blast)
      qed
      \<comment> \<open>{t \<in> I | at \<in> W} is open in I: the linear map t \<mapsto> at is continuous, W is open.\<close>
      moreover have "{t \<in> I_set. a*t \<in> W} \<in> I_top"
      proof -
        have hcont_scale: "continuous_on UNIV (\<lambda>t::real. a*t)" by (intro continuous_intros)
        have "open ((\<lambda>t. a*t) -` W)" by (rule open_vimage[OF hoW hcont_scale])
        moreover have "{t. a*t \<in> W} = (\<lambda>t. a*t) -` W" by auto
        ultimately have "open {t. a*t \<in> W}" by simp
        hence "{t. a*t \<in> W} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
        hence "I_set \<inter> {t. a*t \<in> W} \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
        moreover have "I_set \<inter> {t. a*t \<in> W} = {t \<in> I_set. a*t \<in> W}" by (by100 blast)
        ultimately show ?thesis by simp
      qed
      ultimately show "{t \<in> I_set. f_L t \<in> V} \<in> I_top" by simp
    qed
  qed
  have hfL_path: "top1_is_path_on X TX x0 (f a) f_L"
    unfolding top1_is_path_on_def using hfL_cont_top hf0 ha
    unfolding f_L_def by simp
  have hfR_cont_top: "top1_continuous_map_on I_set I_top X TX f_R"
  proof -
    have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
      using hf unfolding top1_is_path_on_def by (by100 blast)
    have hf_range': "\<And>u. u \<in> I_set \<Longrightarrow> f u \<in> X"
      using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
    have hf_pre: "\<And>V. V \<in> TX \<Longrightarrow> {u \<in> I_set. f u \<in> V} \<in> I_top"
      using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix t assume "t \<in> I_set"
      thus "f_R t \<in> X" unfolding f_R_def using hshift_range hf_range' by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have hW: "{u \<in> I_set. f u \<in> V} \<in> I_top" using hf_pre[OF hV] .
      obtain W where hoW: "open W" and hWI: "{u \<in> I_set. f u \<in> V} = I_set \<inter> W"
        using hW unfolding top1_unit_interval_topology_def subspace_topology_def top1_open_sets_def
        by auto
      have "{t \<in> I_set. f_R t \<in> V} = {t \<in> I_set. a + (1-a)*t \<in> W}"
      proof (intro Collect_cong conj_cong refl)
        fix t assume "t \<in> I_set"
        hence "a + (1-a)*t \<in> I_set" by (rule hshift_range)
        thus "(f_R t \<in> V) = (a + (1-a)*t \<in> W)" unfolding f_R_def using hWI by (by100 blast)
      qed
      moreover have "{t \<in> I_set. a + (1-a)*t \<in> W} \<in> I_top"
      proof -
        have hcont_shift: "continuous_on UNIV (\<lambda>t::real. a + (1-a)*t)" by (intro continuous_intros)
        have "open ((\<lambda>t. a + (1-a)*t) -` W)" by (rule open_vimage[OF hoW hcont_shift])
        moreover have "{t. a + (1-a)*t \<in> W} = (\<lambda>t. a + (1-a)*t) -` W" by auto
        ultimately have "open {t. a + (1-a)*t \<in> W}" by simp
        hence "{t. a + (1-a)*t \<in> W} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
        hence "I_set \<inter> {t. a + (1-a)*t \<in> W} \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
        moreover have "I_set \<inter> {t. a + (1-a)*t \<in> W} = {t \<in> I_set. a + (1-a)*t \<in> W}" by (by100 blast)
        ultimately show ?thesis by simp
      qed
      ultimately show "{t \<in> I_set. f_R t \<in> V} \<in> I_top" by simp
    qed
  qed
  have hfR_path: "top1_is_path_on X TX (f a) x1 f_R"
    unfolding top1_is_path_on_def using hfR_cont_top hf1 ha
    unfolding f_R_def by simp
  have hfL_fR_path: "top1_is_path_on X TX x0 x1 (top1_path_product f_L f_R)"
    by (rule top1_path_product_is_path[OF hTX hfL_path hfR_path])
  show ?thesis
    unfolding top1_path_homotopic_on_def
  proof (intro conjI exI[of _ F])
    show "top1_is_path_on X TX x0 x1 f" by (rule hf)
    show "top1_is_path_on X TX x0 x1 (top1_path_product f_L f_R)" by (rule hfL_fR_path)
    show "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F" by (rule hF_cont)
    show "\<forall>s\<in>I_set. F (s, 0) = f s" unfolding F_def using hH0 by simp
    show "\<forall>s\<in>I_set. F (s, 1) = top1_path_product f_L f_R s" unfolding F_def using hH1 by simp
    show "\<forall>t\<in>I_set. F (0, t) = x0" unfolding F_def using hH_start by simp
    show "\<forall>t\<in>I_set. F (1, t) = x1" unfolding F_def using hH_end by simp
  qed
qed

text \<open>Theorem 51.3 by induction on the number of subdivision points.\<close>
lemma Theorem_51_3_aux:
  fixes f :: "real \<Rightarrow> 'a" and subdivision :: "nat \<Rightarrow> real"
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
      and hm: "m \<ge> 1"
      and hsub0: "subdivision 0 = 0" and hsubm: "subdivision m = 1"
      and hsub_mono: "\<And>i. i < m \<Longrightarrow> subdivision i < subdivision (Suc i)"
  shows "top1_path_homotopic_on X TX x0 x1 f
      (foldr top1_path_product
        (map (\<lambda>i t. f (subdivision i + t * (subdivision (Suc i) - subdivision i))) [0..<m])
        (top1_constant_path x1))"
  using hm hsub0 hsubm hsub_mono hf
proof (induction m arbitrary: subdivision f x0 x1)
  case 0 thus ?case by simp
next
  case (Suc m')
  show ?case
  proof (cases "m' = 0")
    case True
    have hfi0_eq: "(\<lambda>t. f (subdivision 0 + t * (subdivision 1 - subdivision 0))) = f"
    proof (intro ext)
      fix t :: real
      show "f (subdivision 0 + t * (subdivision 1 - subdivision 0)) = f t"
      proof -
        have hsub1: "subdivision (Suc m') = 1" using Suc.prems(3) .
        have "subdivision (Suc 0) = 1" using hsub1 True by simp
        have hsub0': "subdivision 0 = 0" using Suc.prems(2) .
        show "f (subdivision 0 + t * (subdivision 1 - subdivision 0)) = f t"
          using \<open>subdivision (Suc 0) = 1\<close> hsub0' by simp
      qed
    qed
    have heq: "foldr top1_path_product
        (map (\<lambda>i t. f (subdivision i + t * (subdivision (Suc i) - subdivision i))) [0..<Suc m'])
        (top1_constant_path x1) = top1_path_product f (top1_constant_path x1)"
      using True hfi0_eq by simp
    show ?thesis using Lemma_51_1_path_homotopic_sym[OF
        Theorem_51_2_right_identity[OF hTX Suc.prems(5)]] heq by simp
  next
    case False
    hence hm': "m' \<ge> 1" by simp
    define a where "a = subdivision 1"
    have ha_pos: "0 < a" using Suc.prems(2) Suc.prems(4)[of 0] unfolding a_def by simp
    note hsub_mono' = Suc.prems(4)
    have hsub_strict_mono: "\<And>i j. i < j \<Longrightarrow> j \<le> Suc m' \<Longrightarrow> subdivision i < subdivision j"
    proof -
      fix i j :: nat assume hij: "i < j" "j \<le> Suc m'"
      show "subdivision i < subdivision j" using hij
      proof (induction "j - i" arbitrary: j)
        case 0 thus ?case by simp
      next
        case (Suc d)
        hence hj_pos: "j > 0" by simp
        have hjm: "j - 1 < Suc m'" using Suc.prems by simp
        show ?case
        proof (cases "i < j - 1")
          case True
          have "subdivision i < subdivision (j-1)"
            using Suc.hyps(1)[of "j-1"] True hjm Suc.hyps(2) hj_pos by simp
          also have "subdivision (j-1) < subdivision j"
            using hsub_mono'[of "j-1"] hjm hj_pos by simp
          finally show ?thesis .
        next
          case False hence "i = j - 1" using Suc.prems by simp
          thus ?thesis using hsub_mono'[of "j-1"] hjm hj_pos by simp
        qed
      qed
    qed
    have ha_lt1: "a < 1"
    proof -
      have "subdivision 1 < subdivision (Suc m')"
        by (rule hsub_strict_mono) (use hm' in auto)
      thus ?thesis unfolding a_def using Suc.prems(3) by linarith
    qed
    \<comment> \<open>f \<simeq> f_L * f_R via path_product_split.\<close>
    have hf_split: "top1_path_homotopic_on X TX x0 x1 f
        (top1_path_product (\<lambda>t. f (a*t)) (\<lambda>t. f (a + (1-a)*t)))"
      by (rule path_product_split[OF hTX Suc.prems(5) ha_pos ha_lt1])
    \<comment> \<open>fi(0) = f_L.\<close>
    have hfi0_eq: "(\<lambda>t. f (subdivision 0 + t * (subdivision (Suc 0) - subdivision 0))) = (\<lambda>t. f (a*t))"
    proof (intro ext)
      fix t :: real
      show "f (subdivision 0 + t * (subdivision (Suc 0) - subdivision 0)) = f (a*t)"
        unfolding a_def using Suc.prems(2) by (simp add: mult.commute)
    qed
    \<comment> \<open>f_R path and IH setup.\<close>
    define f_R where "f_R t = f (a + (1-a)*t)" for t
    have hfR_path: "top1_is_path_on X TX (f a) x1 f_R"
    proof -
      have hf_path: "top1_is_path_on X TX x0 x1 f" using Suc.prems(5) .
      have hshift_range: "\<And>t. t \<in> I_set \<Longrightarrow> a + (1-a) * t \<in> I_set"
      proof -
        fix t assume "t \<in> I_set"
        hence ht01: "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by auto
        have "a + (1-a)*t \<ge> 0" using ha_pos ha_lt1 ht01
          by (intro add_nonneg_nonneg mult_nonneg_nonneg) linarith+
        moreover have "a + (1-a)*t \<le> a + (1-a)*1"
          by (intro add_left_mono mult_left_mono) (use ha_lt1 ht01 in linarith)+
        hence "a + (1-a)*t \<le> 1" by simp
        ultimately show "a + (1-a)*t \<in> I_set" unfolding top1_unit_interval_def by simp
      qed
      have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
        using hf_path unfolding top1_is_path_on_def by (by100 blast)
      have hf_pre: "\<And>V. V \<in> TX \<Longrightarrow> {u \<in> I_set. f u \<in> V} \<in> I_top"
        using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
      have hfR_cont: "top1_continuous_map_on I_set I_top X TX f_R"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix t assume "t \<in> I_set"
        thus "f_R t \<in> X" unfolding f_R_def
          using hshift_range hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
      next
        fix V assume hV: "V \<in> TX"
        obtain W where hoW: "open W" and hWI: "{u \<in> I_set. f u \<in> V} = I_set \<inter> W"
          using hf_pre[OF hV] unfolding top1_unit_interval_topology_def subspace_topology_def top1_open_sets_def by auto
        have "{t \<in> I_set. f_R t \<in> V} = {t \<in> I_set. a + (1-a)*t \<in> W}"
        proof (intro Collect_cong conj_cong refl)
          fix t assume "t \<in> I_set"
          hence "a + (1-a)*t \<in> I_set" by (rule hshift_range)
          thus "(f_R t \<in> V) = (a + (1-a)*t \<in> W)" unfolding f_R_def using hWI by (by100 blast)
        qed
        moreover have "{t \<in> I_set. a + (1-a)*t \<in> W} \<in> I_top"
        proof -
          have "continuous_on UNIV (\<lambda>t::real. a + (1-a)*t)" by (intro continuous_intros)
          hence "open ((\<lambda>t. a + (1-a)*t) -` W)" by (rule open_vimage[OF hoW])
          moreover have "{t. a + (1-a)*t \<in> W} = (\<lambda>t. a + (1-a)*t) -` W" by auto
          ultimately have "open {t. a + (1-a)*t \<in> W}" by simp
          hence "{t. a + (1-a)*t \<in> W} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
          hence "I_set \<inter> {t. a + (1-a)*t \<in> W} \<in> I_top"
            unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
          moreover have "I_set \<inter> {t. a + (1-a)*t \<in> W} = {t \<in> I_set. a + (1-a)*t \<in> W}" by (by100 blast)
          ultimately show ?thesis by simp
        qed
        ultimately show "{t \<in> I_set. f_R t \<in> V} \<in> I_top" by simp
      qed
      have hfR0: "f_R 0 = f a" unfolding f_R_def by simp
      have hfR1: "f_R 1 = x1" unfolding f_R_def
        using hf_path unfolding top1_is_path_on_def by simp
      show ?thesis unfolding top1_is_path_on_def using hfR_cont hfR0 hfR1 by (by100 blast)
    qed
    define sub' where "sub' j = (subdivision (Suc j) - a) / (1 - a)" for j
    have hsub'0: "sub' 0 = 0" unfolding sub'_def a_def by simp
    have hsub'm': "sub' m' = 1"
      unfolding sub'_def using Suc.prems(3) a_def ha_lt1 by simp
    have hsub'_mono: "\<And>j. j < m' \<Longrightarrow> sub' j < sub' (Suc j)"
    proof -
      fix j assume "j < m'"
      hence "Suc j < Suc m'" by simp
      hence "subdivision (Suc j) < subdivision (Suc (Suc j))" using Suc.prems(4) by simp
      thus "sub' j < sub' (Suc j)" unfolding sub'_def using ha_lt1
        by (simp add: divide_strict_right_mono)
    qed
    have hIH: "top1_path_homotopic_on X TX (f a) x1 f_R
        (foldr top1_path_product
          (map (\<lambda>j t. f_R (sub' j + t * (sub' (Suc j) - sub' j))) [0..<m'])
          (top1_constant_path x1))"
      by (rule Suc.IH[OF hm' hsub'0 hsub'm' hsub'_mono hfR_path])
    \<comment> \<open>Each piece fi'(j)(t) = f_R(sub'(j)+t*\<Delta>') = f(sub(j+1)+t*(sub(j+2)-sub(j+1))) = fi(j+1)(t).\<close>
    have hfi_shift: "\<And>j. j < m' \<Longrightarrow>
        (\<lambda>t. f_R (sub' j + t * (sub' (Suc j) - sub' j))) =
        (\<lambda>t. f (subdivision (Suc j) + t * (subdivision (Suc (Suc j)) - subdivision (Suc j))))"
    proof -
      fix j :: nat assume hj: "j < m'"
      show "(\<lambda>t. f_R (sub' j + t * (sub' (Suc j) - sub' j))) =
            (\<lambda>t. f (subdivision (Suc j) + t * (subdivision (Suc (Suc j)) - subdivision (Suc j))))"
      proof (intro ext)
        fix t :: real
        have h1a: "(1::real) - a > 0" using ha_lt1 by simp
        have "sub' j = (subdivision (Suc j) - a) / (1-a)" unfolding sub'_def ..
        have "sub' (Suc j) = (subdivision (Suc (Suc j)) - a) / (1-a)" unfolding sub'_def ..
        have "sub' (Suc j) - sub' j = (subdivision (Suc (Suc j)) - subdivision (Suc j)) / (1-a)"
          unfolding sub'_def using h1a by (simp add: divide_simps)
        hence "sub' j + t * (sub' (Suc j) - sub' j) =
              (subdivision (Suc j) - a) / (1-a) + t * ((subdivision (Suc (Suc j)) - subdivision (Suc j)) / (1-a))"
          unfolding sub'_def by simp
        also have "\<dots> = (subdivision (Suc j) - a + t * (subdivision (Suc (Suc j)) - subdivision (Suc j))) / (1-a)"
          using h1a by (simp add: add_divide_distrib)
        finally have harg: "a + (1-a) * (sub' j + t * (sub' (Suc j) - sub' j)) =
              subdivision (Suc j) + t * (subdivision (Suc (Suc j)) - subdivision (Suc j))"
          using h1a by simp
        show "f_R (sub' j + t * (sub' (Suc j) - sub' j)) =
              f (subdivision (Suc j) + t * (subdivision (Suc (Suc j)) - subdivision (Suc j)))"
          unfolding f_R_def using harg by simp
      qed
    qed
    \<comment> \<open>Rewrite IH: map fi' [0..<m'] = map (\<lambda>j. fi(Suc j)) [0..<m'].\<close>
    have hmap_eq: "map (\<lambda>j t. f_R (sub' j + t * (sub' (Suc j) - sub' j))) [0..<m'] =
        map (\<lambda>j t. f (subdivision (Suc j) + t * (subdivision (Suc (Suc j)) - subdivision (Suc j)))) [0..<m']"
    proof (rule map_cong[OF refl])
      fix j assume "j \<in> set [0..<m']"
      hence "j < m'" by simp
      thus "(\<lambda>t. f_R (sub' j + t * (sub' (Suc j) - sub' j))) =
            (\<lambda>t. f (subdivision (Suc j) + t * (subdivision (Suc (Suc j)) - subdivision (Suc j))))"
        by (rule hfi_shift)
    qed
    \<comment> \<open>Shift and foldr manipulation using a local definition.\<close>
    define fi' where "fi' i = (\<lambda>t::real. f (subdivision i + t * (subdivision (Suc i) - subdivision i)))" for i
    have hmap_shift: "map (\<lambda>j. fi' (Suc j)) [0..<m'] = map fi' [1..<Suc m']"
    proof -
      have "map (\<lambda>j. fi' (Suc j)) [0..<m'] = map (fi' \<circ> Suc) [0..<m']" by (simp add: comp_def)
      also have "\<dots> = map fi' (map Suc [0..<m'])" by (simp add: map_map)
      also have "map Suc [0..<m'] = [Suc 0..<Suc m']" by (rule map_Suc_upt)
      also have "[Suc 0..<Suc m'] = [1..<Suc m']" by simp
      finally show ?thesis .
    qed
    \<comment> \<open>fi'(0) = (\<lambda>t. f(a*t)).\<close>
    have hfi0: "fi' 0 = (\<lambda>t. f (a*t))"
    proof (intro ext)
      fix t :: real
      show "fi' 0 t = f (a*t)" unfolding fi'_def a_def using Suc.prems(2) by (simp add: mult.commute)
    qed
    \<comment> \<open>From IH + rewriting: f_R \<simeq> foldr [fi'(1),...,fi'(m')] const.\<close>
    have hmap_eq': "map (\<lambda>j t. f_R (sub' j + t * (sub' (Suc j) - sub' j))) [0..<m'] =
        map (\<lambda>j. fi' (Suc j)) [0..<m']"
    proof (rule map_cong[OF refl])
      fix j assume "j \<in> set [0..<m']"
      hence "j < m'" by simp
      thus "(\<lambda>t. f_R (sub' j + t * (sub' (Suc j) - sub' j))) = fi' (Suc j)"
        using hfi_shift unfolding fi'_def by simp
    qed
    have hIH': "top1_path_homotopic_on X TX (f a) x1 f_R
        (foldr top1_path_product (map fi' [1..<Suc m']) (top1_constant_path x1))"
      using hIH hmap_eq' hmap_shift by simp
    \<comment> \<open>[1..<Suc m'] is a prefix of [1..<Suc(Suc m')].\<close>
    have hupt_ext: "[1::nat..<Suc (Suc m')] = [1..<Suc m'] @ [Suc m']" by simp
    \<comment> \<open>Lift: (\<lambda>t. f(at)) * f_R \<simeq> (\<lambda>t. f(at)) * foldr [fi'(1),...,fi'(Suc m')] const.\<close>
    \<comment> \<open>But IH gives foldr [fi'(1),...,fi'(m')], and the full list is [fi'(1),...,fi'(Suc m')].\<close>
    \<comment> \<open>Wait: m = Suc m', so [0..<m] = [0..<Suc m'] and [1..<Suc m'] has m'-1 elements.\<close>
    \<comment> \<open>Actually: [1..<Suc(Suc m')] = [1,...,Suc m'] has Suc m' elements.\<close>
    \<comment> \<open>But the IH applies to m' pieces (j=0,...,m'-1), giving fi'(1),...,fi'(m').\<close>
    \<comment> \<open>We need foldr of fi'(0),...,fi'(Suc m') = fi'(0)*foldr(fi'(1),...,fi'(Suc m')).\<close>
    \<comment> \<open>And IH gives f_R \<simeq> foldr [fi'(1),...,fi'(m')] const.\<close>
    \<comment> \<open>Hmm, [1..<Suc m'] = [1,...,m'] has m' elements = fi'(1),...,fi'(m').\<close>
    \<comment> \<open>And [1..<Suc(Suc m')] = [1,...,Suc m'] has Suc m' elements.\<close>
    \<comment> \<open>So IH gives m' pieces but we need Suc m' pieces. Something is off.\<close>
    \<comment> \<open>Let me recheck: the goal is foldr [fi'(0),...,fi'(Suc m')] const where m=Suc(Suc m').\<close>
    \<comment> \<open>Wait: m = Suc m' in the induction. The goal has [0..<Suc m'] = [0,...,m'] = Suc m' pieces.\<close>
    \<comment> \<open>foldr = fi'(0) * foldr [fi'(1),...,fi'(m')] const. IH: f_R \<simeq> foldr [fi'(1),...,fi'(m')] const. OK!\<close>
    have hfL_path: "top1_is_path_on X TX x0 (f a) (\<lambda>t. f (a*t))"
    proof -
      have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
        using Suc.prems(5) unfolding top1_is_path_on_def by (by100 blast)
      have hf_pre: "\<And>V. V \<in> TX \<Longrightarrow> {u \<in> I_set. f u \<in> V} \<in> I_top"
        using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
      have hscale: "\<And>t. t \<in> I_set \<Longrightarrow> a*t \<in> I_set"
      proof -
        fix t assume "t \<in> I_set"
        hence "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by auto
        thus "a*t \<in> I_set" unfolding top1_unit_interval_def
          using ha_pos ha_lt1 by (auto intro: mult_nonneg_nonneg mult_le_one simp: less_imp_le)
      qed
      show ?thesis unfolding top1_is_path_on_def
      proof (intro conjI)
        show "top1_continuous_map_on I_set I_top X TX (\<lambda>t. f (a*t))"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix t assume "t \<in> I_set"
          thus "f (a*t) \<in> X" using hscale hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
        next
          fix V assume hV: "V \<in> TX"
          obtain W where hoW: "open W" and hWI: "{u \<in> I_set. f u \<in> V} = I_set \<inter> W"
            using hf_pre[OF hV] unfolding top1_unit_interval_topology_def subspace_topology_def top1_open_sets_def by auto
          have "{t \<in> I_set. f (a*t) \<in> V} = {t \<in> I_set. a*t \<in> W}"
            using hscale hWI by (by100 blast)
          moreover have "open ((\<lambda>t. a*t) -` W)"
            by (rule open_vimage[OF hoW]) (intro continuous_intros)
          hence "{t \<in> I_set. a*t \<in> W} \<in> I_top"
          proof -
            have "{t. a*t \<in> W} = (\<lambda>t. a*t) -` W" by auto
            hence "open {t. a*t \<in> W}" using \<open>open ((\<lambda>t. a*t) -` W)\<close> by simp
            hence "{t. a*t \<in> W} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
            hence "I_set \<inter> {t. a*t \<in> W} \<in> I_top"
              unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
            thus ?thesis by (simp add: Collect_conj_eq inf_commute)
          qed
          ultimately show "{t \<in> I_set. f (a*t) \<in> V} \<in> I_top" by simp
        qed
        show "f (a * 0) = x0" using Suc.prems(5) unfolding top1_is_path_on_def by simp
        show "f (a * 1) = f a" by simp
      qed
    qed
    have hlift: "top1_path_homotopic_on X TX x0 x1
        (top1_path_product (\<lambda>t. f (a*t)) f_R)
        (top1_path_product (\<lambda>t. f (a*t))
          (foldr top1_path_product (map fi' [1..<Suc m']) (top1_constant_path x1)))"
      by (rule path_homotopic_product_right[OF hTX hIH' hfL_path])
    have hf_split': "top1_path_homotopic_on X TX x0 x1 f
        (top1_path_product (\<lambda>t. f (a*t)) f_R)"
      using hf_split unfolding f_R_def by simp
    have hchain: "top1_path_homotopic_on X TX x0 x1 f
        (top1_path_product (\<lambda>t. f (a*t))
          (foldr top1_path_product (map fi' [1..<Suc m']) (top1_constant_path x1)))"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTX hf_split' hlift])
    \<comment> \<open>Now use hfoldr_cons: the above = foldr [fi'(0),...,fi'(m')] const.\<close>
    \<comment> \<open>Wait: hfoldr_cons splits [0..<Suc(Suc m')], but the goal has [0..<Suc m'].\<close>
    \<comment> \<open>Actually: Suc case has m = Suc m', so the goal is foldr [0..<Suc m'] = foldr [0,...,m'].\<close>
    \<comment> \<open>And hupt_cons says [0..<Suc m'] = 0 # [1..<Suc m']. Wait no, hupt_cons is for Suc(Suc m').\<close>
    \<comment> \<open>Let me redo: the case is m = Suc m'. Goal: foldr (map fi' [0..<Suc m']) const.\<close>
    \<comment> \<open>[0..<Suc m'] = 0 # [1..<Suc m'] when m' >= 1.\<close>
    have hupt_cons2: "[0::nat..<Suc m'] = 0 # [1..<Suc m']" using hm' by (simp add: upt_rec)
    have hfoldr_cons2: "foldr top1_path_product (map fi' [0..<Suc m']) (top1_constant_path x1) =
      top1_path_product (fi' 0)
        (foldr top1_path_product (map fi' [1..<Suc m']) (top1_constant_path x1))"
      unfolding hupt_cons2 by simp
    show ?thesis using hchain hfoldr_cons2 hfi0 unfolding fi'_def by simp
  qed
qed


theorem Theorem_59_1:
  assumes hT: "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and hUV: "U \<union> V = X" and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and hx0: "x0 \<in> U \<inter> V"
  shows "\<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
    (\<exists>n \<ge> 1. \<exists>gs. length gs = n \<and>
       (\<forall>i<n. top1_is_loop_on X TX x0 (gs!i)
            \<and> (gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V))
       \<and> top1_path_homotopic_on X TX x0 x0 f
           (foldr (top1_path_product) gs (top1_constant_path x0)))"
  \<comment> \<open>Munkres 59.1: Step 1: Lebesgue number gives subdivision a0<...<an with f([ai,ai+1])
     in U or V and f(ai) in U\<inter>V. Step 2: Choose paths \<alpha>i in U\<inter>V from x0 to f(ai).
     Set gi = (\<alpha>_{i-1} * fi) * \<alpha>i_bar. Each gi is a loop in U or V at x0, and
     [g1]*...*[gn] = [f1]*...*[fn] = [f].\<close>
proof (intro allI impI)
  fix f assume hf: "top1_is_loop_on X TX x0 f"
  \<comment> \<open>Step 1: Lebesgue subdivision. Find a0<...<an with f([ai,ai+1]) in U or V.\<close>
  obtain m :: nat and subdivision :: "nat \<Rightarrow> real" where
    hm: "m \<ge> 1" and hsub0: "subdivision 0 = 0" and hsubm: "subdivision m = 1"
    and hsub_mono: "\<forall>i<m. subdivision i < subdivision (Suc i)"
    and hsub_UV: "\<forall>i<m. f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)} \<subseteq> U
                       \<or> f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)} \<subseteq> V"
    and hsub_int: "\<forall>i\<le>m. f (subdivision i) \<in> U \<inter> V"
  proof -
    \<comment> \<open>Use open_cover_subdivision_01 from Top0 to get subdivision directly.\<close>
    have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
      by (rule top1_is_loop_on_continuous[OF hf])
    have hf0: "f 0 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hf1: "f 1 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hTX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
    have hUo: "U \<in> TX" using assms(2) unfolding openin_on_def by (by100 blast)
    have hVo: "V \<in> TX" using assms(3) unfolding openin_on_def by (by100 blast)
    have hpreU: "{t \<in> I_set. f t \<in> U} \<in> I_top"
      using hf_cont hUo unfolding top1_continuous_map_on_def by (by100 blast)
    have hpreV: "{t \<in> I_set. f t \<in> V} \<in> I_top"
      using hf_cont hVo unfolding top1_continuous_map_on_def by (by100 blast)
    \<comment> \<open>Standard topology bridge: get open W_U, W_V from preimages.\<close>
    obtain W_U where hWU: "open W_U" and hpreU_eq: "{t \<in> I_set. f t \<in> U} = I_set \<inter> W_U"
    proof -
      have "{t \<in> I_set. f t \<in> U} \<in> {I_set \<inter> W | W. W \<in> top1_open_sets}"
        using hpreU unfolding top1_unit_interval_topology_def subspace_topology_def by simp
      then obtain W where "W \<in> top1_open_sets" "{t \<in> I_set. f t \<in> U} = I_set \<inter> W"
        by (by100 blast)
      thus ?thesis using that unfolding top1_open_sets_def by (by100 blast)
    qed
    obtain W_V where hWV: "open W_V" and hpreV_eq: "{t \<in> I_set. f t \<in> V} = I_set \<inter> W_V"
    proof -
      have "{t \<in> I_set. f t \<in> V} \<in> {I_set \<inter> W | W. W \<in> top1_open_sets}"
        using hpreV unfolding top1_unit_interval_topology_def subspace_topology_def by simp
      then obtain W where "W \<in> top1_open_sets" "{t \<in> I_set. f t \<in> V} = I_set \<inter> W"
        by (by100 blast)
      thus ?thesis using that unfolding top1_open_sets_def by (by100 blast)
    qed
    have hcover: "{t \<in> I_set. f t \<in> U} \<union> {t \<in> I_set. f t \<in> V} = I_set"
    proof -
      have "\<forall>t \<in> I_set. f t \<in> X" using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
      thus ?thesis using hUV by (by100 blast)
    qed
    have hWcover: "I_set \<subseteq> W_U \<union> W_V" using hcover hpreU_eq hpreV_eq by (by100 blast)
    \<comment> \<open>Apply open_cover_subdivision_01 with A = {W_U, W_V}.
       Need: each s in [0,1] is in W_U or W_V (open), so has an \<epsilon>-ball inside it.\<close>
    have hpointwise: "\<forall>s::real. 0 \<le> s \<and> s \<le> 1 \<longrightarrow>
        (\<exists>W\<in>{W_U, W_V}. s \<in> W \<and> (\<exists>\<epsilon>>0. {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> W))"
    proof (intro allI impI)
      fix s :: real assume hs: "0 \<le> s \<and> s \<le> 1"
      hence "s \<in> I_set" unfolding top1_unit_interval_def by simp
      hence "s \<in> W_U \<or> s \<in> W_V" using hWcover by (by100 blast)
      thus "\<exists>W\<in>{W_U, W_V}. s \<in> W \<and> (\<exists>\<epsilon>>0. {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> W)"
      proof
        assume hsWU: "s \<in> W_U"
        have "\<exists>e>0. \<forall>y. dist y s < e \<longrightarrow> y \<in> W_U"
          using hWU hsWU unfolding open_dist by (by100 blast)
        then obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" "\<forall>y. dist y s < \<epsilon> \<longrightarrow> y \<in> W_U" by blast
        have "{t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> W_U"
        proof
          fix t assume "t \<in> {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1}"
          hence "\<bar>t - s\<bar> < \<epsilon>" by simp
          hence "dist t s < \<epsilon>" by (simp add: dist_real_def)
          thus "t \<in> W_U" using h\<epsilon>(2) by (by100 blast)
        qed
        thus ?thesis using hsWU h\<epsilon>(1) by (by100 blast)
      next
        assume hsWV: "s \<in> W_V"
        have "\<exists>e>0. \<forall>y. dist y s < e \<longrightarrow> y \<in> W_V"
          using hWV hsWV unfolding open_dist by (by100 blast)
        then obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" "\<forall>y. dist y s < \<epsilon> \<longrightarrow> y \<in> W_V" by blast
        have "{t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> W_V"
        proof
          fix t assume "t \<in> {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1}"
          hence "\<bar>t - s\<bar> < \<epsilon>" by simp
          hence "dist t s < \<epsilon>" by (simp add: dist_real_def)
          thus "t \<in> W_V" using h\<epsilon>(2) by (by100 blast)
        qed
        thus ?thesis using hsWV h\<epsilon>(1) by (by100 blast)
      qed
    qed
    obtain n_sub :: nat and sub0 :: "nat \<Rightarrow> real" where
      hn_sub: "n_sub \<ge> 1" and hsub0_0: "sub0 0 = 0" and hsub0_n: "sub0 n_sub = 1"
      and hsub0_mono: "\<forall>i<n_sub. sub0 i < sub0 (Suc i)"
      and hsub0_cover: "\<forall>i<n_sub. \<exists>W\<in>{W_U, W_V}.
          {s. sub0 i \<le> s \<and> s \<le> sub0 (Suc i) \<and> 0 \<le> s \<and> s \<le> 1} \<subseteq> W"
      using open_cover_subdivision_01[OF hpointwise] by blast
    \<comment> \<open>Transfer: each piece maps into U or V.\<close>
    have hsub0_UV: "\<forall>i<n_sub. f ` {s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> U
                         \<or> f ` {s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> V"
    proof (intro allI impI)
      fix i assume hi: "i < n_sub"
      obtain W where hW: "W \<in> {W_U, W_V}"
          and hWsub: "{s. sub0 i \<le> s \<and> s \<le> sub0 (Suc i) \<and> 0 \<le> s \<and> s \<le> 1} \<subseteq> W"
        using hsub0_cover hi by blast
      have hpiece_sub_W: "{s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> W"
      proof
        fix x assume "x \<in> {s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)}"
        hence "x \<in> I_set" "sub0 i \<le> x" "x \<le> sub0 (Suc i)" by auto
        hence "0 \<le> x" "x \<le> 1" unfolding top1_unit_interval_def by auto
        hence "x \<in> {s. sub0 i \<le> s \<and> s \<le> sub0 (Suc i) \<and> 0 \<le> s \<and> s \<le> 1}"
          using \<open>sub0 i \<le> x\<close> \<open>x \<le> sub0 (Suc i)\<close> by simp
        thus "x \<in> W" using hWsub by (by100 blast)
      qed
      show "f ` {s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> U
          \<or> f ` {s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> V"
      proof (cases "W = W_U")
        case True
        hence "{s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> I_set \<inter> W_U"
          using hpiece_sub_W by (by100 blast)
        hence "{s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> {t \<in> I_set. f t \<in> U}"
          using hpreU_eq by simp
        thus ?thesis by (by100 blast)
      next
        case False
        hence "W = W_V" using hW by (by100 blast)
        hence "{s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> I_set \<inter> W_V"
          using hpiece_sub_W by (by100 blast)
        hence "{s\<in>I_set. sub0 i \<le> s \<and> s \<le> sub0 (Suc i)} \<subseteq> {t \<in> I_set. f t \<in> V}"
          using hpreV_eq by simp
        thus ?thesis by (by100 blast)
      qed
    qed
    \<comment> \<open>Endpoints: each sub0 i is in [0,1], and is in both adjacent pieces.
       If adjacent pieces map to different sets, f(sub0 i) \<in> U \<inter> V.
       After merging consecutive same-set pieces, all internal endpoints are transitions.
       f(0) = x0 \<in> U\<inter>V, f(1) = x0 \<in> U\<inter>V.\<close>
    \<comment> \<open>Munkres deletion: if f(sub0(i)) \<notin> U\<inter>V for some 0<i<n_sub, delete sub0(i).
       Both adjacent pieces map to the same set, so the merged piece still maps to U or V.
       Repeat until all internal points are in U\<inter>V. Formalized via filtering.\<close>
    define good where "good i = (i = 0 \<or> i = n_sub \<or> f (sub0 i) \<in> U \<inter> V)" for i
    define glist where "glist = filter good [0..<Suc n_sub]"
    \<comment> \<open>0 and n_sub are always good.\<close>
    have hg0: "good 0" unfolding good_def by simp
    have hgn: "good n_sub" unfolding good_def by simp
    have h0_mem: "0 \<in> set glist" unfolding glist_def using hg0 hn_sub by simp
    have hn_mem: "n_sub \<in> set glist" unfolding glist_def using hgn by simp
    have hglist_sorted: "sorted glist" unfolding glist_def
      by (metis sorted_wrt_filter sorted_upt)
    have hglist_distinct: "distinct glist" unfolding glist_def by simp
    have hglist_sub: "set glist \<subseteq> {0..n_sub}" unfolding glist_def by auto
    have h0_ne_n: "(0::nat) \<noteq> n_sub" using hn_sub by simp
    have hglist_len: "length glist \<ge> 2"
    proof -
      have "card {0, n_sub} = 2" using h0_ne_n by simp
      moreover have "{0, n_sub} \<subseteq> set glist" using h0_mem hn_mem by (by100 blast)
      moreover have "card (set glist) = length glist" using hglist_distinct by (rule distinct_card)
      ultimately show ?thesis using card_mono[OF finite_set \<open>{0, n_sub} \<subseteq> set glist\<close>] by linarith
    qed
    define n1 where "n1 = length glist - 1"
    have hn1_ge: "n1 \<ge> 1" using hglist_len unfolding n1_def by simp
    define sub1 where "sub1 j = sub0 (glist ! j)" for j
    have hgl_0: "glist ! 0 = 0"
    proof -
      obtain j where hj: "glist ! j = 0" "j < length glist"
        using h0_mem by (metis in_set_conv_nth)
      have "glist ! 0 \<le> glist ! j"
        by (rule sorted_nth_mono[OF hglist_sorted]) (use hj hglist_len in auto)
      hence "glist ! 0 \<le> 0" using hj(1) by simp
      moreover have "glist ! 0 \<ge> 0" by simp
      ultimately show ?thesis by simp
    qed
    have hgl_n: "glist ! n1 = n_sub"
    proof -
      obtain j where hj: "glist ! j = n_sub" "j < length glist"
        using hn_mem by (metis in_set_conv_nth)
      have "glist ! j \<le> glist ! n1"
        by (rule sorted_nth_mono[OF hglist_sorted])
           (use hj hglist_len in \<open>auto simp: n1_def\<close>)
      hence "n_sub \<le> glist ! n1" using hj(1) by simp
      moreover have "glist ! n1 \<le> n_sub"
      proof -
        have "glist ! n1 \<in> set glist"
          using hglist_len unfolding n1_def by (intro nth_mem) simp
        thus ?thesis using hglist_sub by auto
      qed
      ultimately show ?thesis by simp
    qed
    have hsub1_0: "sub1 0 = 0" unfolding sub1_def using hgl_0 hsub0_0 by simp
    have hsub1_n: "sub1 n1 = 1" unfolding sub1_def using hgl_n hsub0_n by simp
    have hsub0_strict_mono: "\<And>j k. j < k \<Longrightarrow> k \<le> n_sub \<Longrightarrow> sub0 j < sub0 k"
    proof -
      fix j k :: nat assume "j < k" "k \<le> n_sub"
      thus "sub0 j < sub0 k"
      proof (induction k)
        case 0 thus ?case by simp
      next
        case (Suc k)
        show ?case
        proof (cases "j = k")
          case True thus ?thesis using hsub0_mono Suc.prems by simp
        next
          case False
          hence "j < k" using Suc.prems by simp
          hence "sub0 j < sub0 k" using Suc.IH Suc.prems by simp
          also have "sub0 k < sub0 (Suc k)" using hsub0_mono Suc.prems by simp
          finally show ?thesis .
        qed
      qed
    qed
    have hsub1_mono: "\<forall>i<n1. sub1 i < sub1 (Suc i)"
    proof (intro allI impI)
      fix i assume hi: "i < n1"
      have hi_len: "i < length glist" using hi n1_def hglist_len by linarith
      have hsi_len: "Suc i < length glist" using hi n1_def hglist_len by linarith
      have "glist ! i < glist ! Suc i"
        using sorted_nth_mono[OF hglist_sorted, of i "Suc i"] hsi_len
              nth_eq_iff_index_eq[OF hglist_distinct hi_len hsi_len]
        by linarith
      moreover have "glist ! Suc i \<le> n_sub"
      proof -
        have "glist ! Suc i \<in> set glist" using hsi_len by (rule nth_mem)
        thus ?thesis using hglist_sub by auto
      qed
      ultimately show "sub1 i < sub1 (Suc i)" unfolding sub1_def
        using hsub0_strict_mono by simp
    qed
    \<comment> \<open>Key lemma: if f(sub0(k)) \<notin> U\<inter>V for 0 < k < n_sub, both adjacent original pieces
       map to the same set. Proof: sub0(k) is in both pieces. f(sub0(k)) \<in> U \<or> V (from X=U\<union>V).
       If f(sub0(k)) \<in> U - V: piece k-1 maps into f\<inverse>(U) (sub0(k) in piece k-1 and f(sub0(k)) \<in> U
       forces piece k-1 into U since it maps to U or V and intersects U).
       Similarly piece k maps into U.\<close>
    have h_deleted_same: "\<And>k. 0 < k \<Longrightarrow> k < n_sub \<Longrightarrow> f (sub0 k) \<notin> U \<inter> V \<Longrightarrow>
        (f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> U
         \<and> f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> U)
        \<or> (f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> V
         \<and> f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> V)"
    proof -
      fix k assume hk_pos: "0 < k" and hk_lt: "k < n_sub" and hk_not: "f (sub0 k) \<notin> U \<inter> V"
      have hk_prev: "k - 1 < n_sub" using hk_pos hk_lt by simp
      have hSuc_prev: "Suc (k-1) = k" using hk_pos by simp
      \<comment> \<open>Piece k-1 and piece k each map to U or V.\<close>
      have hprev: "f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> U
          \<or> f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> V"
        using hsub0_UV[rule_format, OF hk_prev] hSuc_prev by simp
      have hcurr: "f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> U
          \<or> f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> V"
        using hsub0_UV[rule_format, OF hk_lt] by simp
      \<comment> \<open>sub0(k) is in both pieces (as an I_set point).\<close>
      have hk_in_I: "sub0 k \<in> I_set"
      proof -
        have "sub0 0 \<le> sub0 k"
          using hsub0_strict_mono[of 0 k] hk_pos hk_lt by linarith
        hence "0 \<le> sub0 k" using hsub0_0 by linarith
        moreover have "sub0 k \<le> sub0 n_sub"
          using hsub0_strict_mono[of k n_sub] hk_lt by linarith
        hence "sub0 k \<le> 1" using hsub0_n by linarith
        ultimately show ?thesis unfolding top1_unit_interval_def by simp
      qed
      have "sub0 (k-1) \<le> sub0 k"
        using hsub0_mono[rule_format, of "k-1"] hk_pos hk_lt hSuc_prev by auto
      have hk_in_prev: "sub0 k \<in> {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k}"
        using hk_in_I \<open>sub0 (k-1) \<le> sub0 k\<close> by simp
      have "sub0 k \<le> sub0 (Suc k)" using hsub0_mono[rule_format, OF hk_lt] by linarith
      have hk_in_curr: "sub0 k \<in> {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)}"
        using hk_in_I \<open>sub0 k \<le> sub0 (Suc k)\<close> by simp
      \<comment> \<open>f(sub0(k)) \<in> U \<union> V but not U \<inter> V, so either U-V or V-U.\<close>
      have hfk_UV: "f (sub0 k) \<in> U \<union> V"
        using hprev hk_in_prev by (by100 blast)
      show "(f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> U
         \<and> f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> U)
        \<or> (f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> V
         \<and> f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> V)"
      proof (cases "f (sub0 k) \<in> U")
        case True
        hence "f (sub0 k) \<notin> V" using hk_not by (by100 blast)
        have "f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> U"
          using hprev hk_in_prev \<open>f (sub0 k) \<notin> V\<close> by (by100 blast)
        moreover have "f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> U"
          using hcurr hk_in_curr \<open>f (sub0 k) \<notin> V\<close> by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      next
        case False
        hence "f (sub0 k) \<in> V" using hfk_UV by (by100 blast)
        hence "f (sub0 k) \<notin> U" using hk_not by (by100 blast)
        have "f ` {s\<in>I_set. sub0 (k-1) \<le> s \<and> s \<le> sub0 k} \<subseteq> V"
          using hprev hk_in_prev \<open>f (sub0 k) \<notin> U\<close> by (by100 blast)
        moreover have "f ` {s\<in>I_set. sub0 k \<le> s \<and> s \<le> sub0 (Suc k)} \<subseteq> V"
          using hcurr hk_in_curr \<open>f (sub0 k) \<notin> U\<close> by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
    qed
    \<comment> \<open>All original pieces between consecutive good points map to the same set (U or V).
       Proof by induction: if a deleted point is between them, h_deleted_same says
       both adjacent pieces map to the same set, so we can extend by one step.\<close>
    have h_range_same: "\<And>a b. a < b \<Longrightarrow> b \<le> n_sub \<Longrightarrow>
        (\<forall>k. a < k \<longrightarrow> k < b \<longrightarrow> f (sub0 k) \<notin> U \<inter> V) \<Longrightarrow>
        (\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow>
          f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U)
        \<or> (\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow>
          f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V)"
    proof -
      fix a b :: nat assume hab: "a < b" "b \<le> n_sub"
          and hno_good: "\<forall>k. a < k \<longrightarrow> k < b \<longrightarrow> f (sub0 k) \<notin> U \<inter> V"
      \<comment> \<open>Base: piece a maps to U or V.\<close>
      have ha_lt: "a < n_sub" using hab by simp
      have hpiece_a: "f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> U
          \<or> f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> V"
        using hsub0_UV[rule_format, OF ha_lt] by simp
      \<comment> \<open>Induction: extend from piece a to piece b-1.\<close>
      \<comment> \<open>Each piece j \<in> [a,b) maps to the same set as piece a. Prove by induction on j-a.\<close>
      have h_all_same_as_a: "\<And>j. a \<le> j \<Longrightarrow> j < b \<Longrightarrow>
          (f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> U \<longrightarrow>
           f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U)
        \<and> (f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> V \<longrightarrow>
           f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V)"
      proof -
        fix j assume haj: "a \<le> j" "j < b"
        \<comment> \<open>Prove: if piece a \<subseteq> S (for S = U or V), then piece j \<subseteq> S.
           By strong induction on j-a. Key step: sub0(j) \<in> piece(j-1) and piece(j-1) \<subseteq> S (IH).
           So f(sub0(j)) \<in> S. Since f(sub0(j)) \<notin> U\<inter>V, f(sub0(j)) \<in> S - (other set).
           h_deleted_same then gives piece(j) \<subseteq> S.\<close>
        have "\<And>S. S \<in> {U, V} \<Longrightarrow> f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> S \<Longrightarrow>
            f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> S"
        proof -
          fix S assume hS: "S \<in> {U, V}" and hpieceA: "f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> S"
          \<comment> \<open>By induction on j-a: all pieces in [a,j] map to S.\<close>
          have "\<And>j'. a \<le> j' \<Longrightarrow> j' < b \<Longrightarrow> f ` {s\<in>I_set. sub0 j' \<le> s \<and> s \<le> sub0 (Suc j')} \<subseteq> S"
          proof -
            fix j' assume "a \<le> j'" "j' < b"
            thus "f ` {s\<in>I_set. sub0 j' \<le> s \<and> s \<le> sub0 (Suc j')} \<subseteq> S"
            proof (induction "j' - a" arbitrary: j')
              case 0 hence "j' = a" by simp thus ?case using hpieceA by simp
            next
              case (Suc n)
              hence hj'_pos: "a < j'" by linarith
              have hj'_prev: "a \<le> j' - 1" "j' - 1 < b" using hj'_pos Suc.prems by linarith+
              have "j' - 1 - a = n" using Suc.hyps(2) by linarith
              hence hIH: "f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 (Suc (j'-1))} \<subseteq> S"
                using Suc.hyps(1)[of "j'-1"] hj'_prev by simp
              \<comment> \<open>sub0(j') \<in> piece(j'-1), so f(sub0(j')) \<in> S.\<close>
              have hSuc_eq: "Suc (j' - 1) = j'" using hj'_pos by simp
              hence hIH': "f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> S" using hIH by simp
              have hj'_lt_nsub: "j' < n_sub" using Suc.prems(2) hab(2) by simp
              have hj'_in_I: "sub0 j' \<in> I_set"
              proof -
                have "sub0 0 < sub0 j'" using hsub0_strict_mono[of 0 j'] hj'_pos hj'_lt_nsub by linarith
                hence "0 \<le> sub0 j'" using hsub0_0 by linarith
                moreover have "sub0 j' < sub0 n_sub" using hsub0_strict_mono[of j' n_sub] hj'_lt_nsub by simp
                hence "sub0 j' \<le> 1" using hsub0_n by linarith
                ultimately show ?thesis unfolding top1_unit_interval_def by simp
              qed
              have "j' - 1 < n_sub" using hj'_lt_nsub by simp
              have "sub0 (j'-1) < sub0 j'"
                using hsub0_mono[rule_format, of "j'-1"] \<open>j'-1 < n_sub\<close> hSuc_eq by simp
              hence "sub0 (j'-1) \<le> sub0 j'" by linarith
              hence "sub0 j' \<in> {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'}"
                using hj'_in_I by simp
              hence "f (sub0 j') \<in> S" using hIH' by (by100 blast)
              have hj'_not: "f (sub0 j') \<notin> U \<inter> V" using hno_good hj'_pos Suc.prems(2) by simp
              have hj'_lt: "j' < n_sub" using Suc.prems(2) hab(2) by simp
              \<comment> \<open>h_deleted_same at j': both adjacent pieces map to same set.\<close>
              have h_same: "(f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> U
                   \<and> f ` {s\<in>I_set. sub0 j' \<le> s \<and> s \<le> sub0 (Suc j')} \<subseteq> U)
                \<or> (f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> V
                   \<and> f ` {s\<in>I_set. sub0 j' \<le> s \<and> s \<le> sub0 (Suc j')} \<subseteq> V)"
                using h_deleted_same[of j'] hj'_pos hj'_lt hj'_not by simp
              \<comment> \<open>f(sub0(j')) \<in> S and \<notin> U\<inter>V. If S=U: f(sub0(j')) \<in> U-V, h_same gives U branch.
                 If S=V: f(sub0(j')) \<in> V-U, h_same gives V branch.\<close>
              show "f ` {s\<in>I_set. sub0 j' \<le> s \<and> s \<le> sub0 (Suc j')} \<subseteq> S"
              proof -
                \<comment> \<open>sub0(j') \<in> piece(j'-1) and f(sub0(j')) \<in> S, \<notin> U\<inter>V.
                   If S = U: f(sub0(j')) \<notin> V. piece(j'-1) contains sub0(j') so piece(j'-1) \<not>\<subseteq> V.
                   h_same: both \<subseteq> U or both \<subseteq> V. Since \<not>\<subseteq> V, both \<subseteq> U.
                   Similarly for S = V.\<close>
                have "f (sub0 j') \<notin> U \<or> f (sub0 j') \<notin> V" using hj'_not by (by100 blast)
                have hprev_not_other: "(S = U \<longrightarrow> \<not> f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> V)
                    \<and> (S = V \<longrightarrow> \<not> f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> U)"
                proof (intro conjI impI)
                  assume "S = U"
                  hence "f (sub0 j') \<notin> V" using \<open>f (sub0 j') \<in> S\<close> hj'_not by (by100 blast)
                  moreover have "sub0 j' \<in> {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'}"
                    using hj'_in_I \<open>sub0 (j'-1) \<le> sub0 j'\<close> by simp
                  ultimately show "\<not> f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> V"
                    by (by100 blast)
                next
                  assume "S = V"
                  hence "f (sub0 j') \<notin> U" using \<open>f (sub0 j') \<in> S\<close> hj'_not by (by100 blast)
                  moreover have "sub0 j' \<in> {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'}"
                    using hj'_in_I \<open>sub0 (j'-1) \<le> sub0 j'\<close> by simp
                  ultimately show "\<not> f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> U"
                    by (by100 blast)
                qed
                show ?thesis
                proof (cases "S = U")
                  case True thus ?thesis using h_same hprev_not_other by (by100 blast)
                next
                  case False hence hSV: "S = V" using hS by (by100 blast)
                  hence "\<not> f ` {s\<in>I_set. sub0 (j'-1) \<le> s \<and> s \<le> sub0 j'} \<subseteq> U"
                    using hprev_not_other by simp
                  thus ?thesis using h_same hSV by (by100 blast)
                qed
              qed
            qed
          qed
          thus "f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> S" using haj by simp
        qed
        note hdir = this
        show "(f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> U \<longrightarrow>
           f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U)
        \<and> (f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> V \<longrightarrow>
           f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V)"
          using hdir[of U] hdir[of V] by simp
      qed
      show "(\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow>
          f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U)
        \<or> (\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow>
          f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V)"
      proof (cases "f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> U")
        case True
        have "\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow>
            f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U"
        proof (intro allI impI)
          fix j assume "a \<le> j" "j < b"
          thus "f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U"
            using True h_all_same_as_a[of j] by simp
        qed
        thus ?thesis by (by100 blast)
      next
        case False
        hence "f ` {s\<in>I_set. sub0 a \<le> s \<and> s \<le> sub0 (Suc a)} \<subseteq> V"
          using hpiece_a by (by100 blast)
        hence "\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow>
            f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V"
          using h_all_same_as_a by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
    qed
    have hsub1_UV: "\<forall>i<n1. f ` {s\<in>I_set. sub1 i \<le> s \<and> s \<le> sub1 (Suc i)} \<subseteq> U
                         \<or> f ` {s\<in>I_set. sub1 i \<le> s \<and> s \<le> sub1 (Suc i)} \<subseteq> V"
    proof (intro allI impI)
      fix i assume hi: "i < n1"
      let ?a = "glist ! i" and ?b = "glist ! Suc i"
      have hi_len: "i < length glist" using hi n1_def hglist_len by linarith
      have hsi_len: "Suc i < length glist" using hi n1_def hglist_len by linarith
      have hab_lt: "?a < ?b"
        using sorted_nth_mono[OF hglist_sorted, of i "Suc i"] hsi_len
              nth_eq_iff_index_eq[OF hglist_distinct hi_len hsi_len] by linarith
      have hb_le: "?b \<le> n_sub"
      proof -
        have "?b \<in> set glist" using hsi_len by (rule nth_mem)
        thus ?thesis using hglist_sub by auto
      qed
      have hno_good_ab: "\<forall>k. ?a < k \<longrightarrow> k < ?b \<longrightarrow> f (sub0 k) \<notin> U \<inter> V"
      proof (intro allI impI)
        fix k assume hk: "?a < k" "k < ?b"
        \<comment> \<open>k is between consecutive glist elements, so k \<notin> set glist.\<close>
        have "k \<notin> set glist"
        proof
          assume "k \<in> set glist"
          then obtain m where hm: "m < length glist" "glist ! m = k" by (metis in_set_conv_nth)
          \<comment> \<open>glist!i < k = glist!m, and glist sorted+distinct \<Rightarrow> i < m.\<close>
          have "i \<noteq> m" using hk(1) hm(2) by auto
          have "i \<le> m \<or> m \<le> i" by linarith
          hence "i < m"
          proof
            assume "i \<le> m" thus "i < m" using \<open>i \<noteq> m\<close> by simp
          next
            assume "m \<le> i"
            hence "glist ! m \<le> glist ! i" using sorted_nth_mono[OF hglist_sorted] hi_len hm(1) by auto
            hence "k \<le> ?a" using hm(2) by simp
            thus "i < m" using hk(1) by simp
          qed
          \<comment> \<open>k = glist!m < glist!(Suc i), and sorted+distinct \<Rightarrow> m < Suc i.\<close>
          have "m \<noteq> Suc i"
          proof
            assume "m = Suc i"
            hence "glist ! m = ?b" by simp
            thus False using hm(2) hk(2) by simp
          qed
          have "m \<le> Suc i \<or> Suc i \<le> m" by linarith
          hence "m < Suc i"
          proof
            assume "m \<le> Suc i" thus ?thesis using \<open>m \<noteq> Suc i\<close> by simp
          next
            assume "Suc i \<le> m"
            hence "glist ! Suc i \<le> glist ! m" using sorted_nth_mono[OF hglist_sorted] hsi_len hm(1) by auto
            thus ?thesis using hm(2) hk(2) by simp
          qed
          thus False using \<open>i < m\<close> by simp
        qed
        have "k \<le> n_sub" using hk(2) hb_le by linarith
        hence "k \<in> set [0..<Suc n_sub]" by auto
        hence "\<not> good k" using \<open>k \<notin> set glist\<close> unfolding glist_def by auto
        moreover have "k \<noteq> 0" using hk(1) by simp
        moreover have "k \<noteq> n_sub"
        proof -
          have "k < n_sub" using \<open>k \<le> n_sub\<close> hk(2) hb_le by linarith
          thus ?thesis by simp
        qed
        ultimately show "f (sub0 k) \<notin> U \<inter> V" unfolding good_def by simp
      qed
      \<comment> \<open>h_range_same: all original pieces in [?a, ?b) map to U, or all map to V.\<close>
      have h_all: "(\<forall>j. ?a \<le> j \<longrightarrow> j < ?b \<longrightarrow>
          f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U)
        \<or> (\<forall>j. ?a \<le> j \<longrightarrow> j < ?b \<longrightarrow>
          f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V)"
        by (rule h_range_same[OF hab_lt hb_le hno_good_ab])
      \<comment> \<open>Every point in merged piece is in some original piece, hence f maps it to S.\<close>
      show "f ` {s\<in>I_set. sub1 i \<le> s \<and> s \<le> sub1 (Suc i)} \<subseteq> U
          \<or> f ` {s\<in>I_set. sub1 i \<le> s \<and> s \<le> sub1 (Suc i)} \<subseteq> V"
      proof -
        \<comment> \<open>For any s in merged piece, find j with sub0(j) \<le> s \<le> sub0(j+1).\<close>
        have hpoint: "\<And>s. s \<in> I_set \<Longrightarrow> sub0 ?a \<le> s \<Longrightarrow> s \<le> sub0 ?b \<Longrightarrow>
            \<exists>j. ?a \<le> j \<and> j < ?b \<and> sub0 j \<le> s \<and> s \<le> sub0 (Suc j)"
        proof -
          fix s assume hs: "s \<in> I_set" "sub0 ?a \<le> s" "s \<le> sub0 ?b"
          \<comment> \<open>Find the largest j with ?a \<le> j \<le> ?b and sub0(j) \<le> s.\<close>
          define J where "J = {j. ?a \<le> j \<and> j \<le> ?b \<and> sub0 j \<le> s}"
          have "?a \<in> J" using hs(2) hab_lt unfolding J_def by simp
          hence "J \<noteq> {}" by (by100 blast)
          have "finite J" unfolding J_def by simp
          have "J \<subseteq> {?a..?b}" unfolding J_def by auto
          obtain j where hj: "j \<in> J" "\<forall>k \<in> J. k \<le> j"
            using \<open>finite J\<close> \<open>J \<noteq> {}\<close> by (metis Max_in Max_ge)
          have "?a \<le> j" "j \<le> ?b" "sub0 j \<le> s" using hj(1) unfolding J_def by auto
          \<comment> \<open>If j = ?b, take ?b-1 instead (which works since sub0(?b-1) \<le> s \<le> sub0(?b)).\<close>
          define j' where "j' = (if j < ?b then j else ?b - 1)"
          have "?a \<le> j'" and "j' < ?b"
            unfolding j'_def using \<open>?a \<le> j\<close> hab_lt by auto
          have "sub0 j' \<le> s"
          proof (cases "j < ?b")
            case True thus ?thesis unfolding j'_def using \<open>sub0 j \<le> s\<close> by simp
          next
            case False
            hence "j = ?b" using \<open>j \<le> ?b\<close> by simp
            hence "sub0 ?b \<le> s" using \<open>sub0 j \<le> s\<close> by simp
            hence "s = sub0 ?b" using hs(3) by linarith
            have "sub0 (?b - 1) < sub0 ?b"
              using hsub0_strict_mono[of "?b-1" "?b"] hab_lt hb_le by linarith
            have "j' = ?b - 1" unfolding j'_def using False by simp
            hence "sub0 j' = sub0 (?b - 1)" by simp
            thus ?thesis using \<open>sub0 (?b - 1) < sub0 ?b\<close> \<open>s = sub0 ?b\<close> by linarith
          qed
          have "s \<le> sub0 (Suc j')"
          proof (cases "j < ?b")
            case True
            hence "j' = j" unfolding j'_def by simp
            show ?thesis
            proof (rule ccontr)
              assume "\<not> s \<le> sub0 (Suc j')"
              hence "sub0 (Suc j') \<le> s" by linarith
              hence "sub0 (Suc j) \<le> s" using \<open>j' = j\<close> by simp
              have "Suc j \<in> J" unfolding J_def
                using \<open>?a \<le> j\<close> True \<open>sub0 (Suc j) \<le> s\<close> by simp
              hence "Suc j \<le> j" using hj(2) by simp
              thus False by simp
            qed
          next
            case False
            hence hj_eq_b: "j = ?b" using \<open>j \<le> ?b\<close> by simp
            hence "j' = ?b - 1" unfolding j'_def by simp
            hence "Suc j' = ?b" using hab_lt by simp
            show ?thesis using hs(3) \<open>Suc j' = ?b\<close> by simp
          qed
          show "\<exists>j. ?a \<le> j \<and> j < ?b \<and> sub0 j \<le> s \<and> s \<le> sub0 (Suc j)"
            using \<open>?a \<le> j'\<close> \<open>j' < ?b\<close> \<open>sub0 j' \<le> s\<close> \<open>s \<le> sub0 (Suc j')\<close> by (by100 blast)
        qed
        have hfinal: "\<And>S. (\<forall>j. ?a \<le> j \<longrightarrow> j < ?b \<longrightarrow>
            f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> S)
            \<Longrightarrow> f ` {s\<in>I_set. sub0 ?a \<le> s \<and> s \<le> sub0 ?b} \<subseteq> S"
        proof -
          fix S assume hS: "\<forall>j. ?a \<le> j \<longrightarrow> j < ?b \<longrightarrow>
              f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> S"
          show "f ` {s\<in>I_set. sub0 ?a \<le> s \<and> s \<le> sub0 ?b} \<subseteq> S"
          proof
            fix y assume "y \<in> f ` {s\<in>I_set. sub0 ?a \<le> s \<and> s \<le> sub0 ?b}"
            then obtain s where hs: "s \<in> I_set" "sub0 ?a \<le> s" "s \<le> sub0 ?b" "y = f s"
              by (by100 blast)
            obtain j where hj: "?a \<le> j" "j < ?b" "sub0 j \<le> s" "s \<le> sub0 (Suc j)"
              using hpoint[OF hs(1-3)] by (by100 blast)
            have "f s \<in> S" using hS hj hs(1) by (by100 blast)
            thus "y \<in> S" using hs(4) by simp
          qed
        qed
        have hsub1_eq: "sub1 i = sub0 ?a" "sub1 (Suc i) = sub0 ?b" unfolding sub1_def by simp_all
        show ?thesis
        proof (rule disjE[OF h_all])
          assume "\<forall>j. ?a \<le> j \<longrightarrow> j < ?b \<longrightarrow> f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> U"
          hence "f ` {s\<in>I_set. sub0 ?a \<le> s \<and> s \<le> sub0 ?b} \<subseteq> U" by (rule hfinal)
          thus ?thesis unfolding sub1_def by simp
        next
          assume "\<forall>j. ?a \<le> j \<longrightarrow> j < ?b \<longrightarrow> f ` {s\<in>I_set. sub0 j \<le> s \<and> s \<le> sub0 (Suc j)} \<subseteq> V"
          hence "f ` {s\<in>I_set. sub0 ?a \<le> s \<and> s \<le> sub0 ?b} \<subseteq> V" by (rule hfinal)
          thus ?thesis unfolding sub1_def by simp
        qed
      qed
    qed
    have hsub1_int: "\<forall>i\<le>n1. f (sub1 i) \<in> U \<inter> V"
    proof (intro allI impI)
      fix i assume "i \<le> n1"
      show "f (sub1 i) \<in> U \<inter> V"
      proof (cases "i = 0")
        case True thus ?thesis using hsub1_0 hf0 hx0 by simp
      next
        case False
        show ?thesis
        proof (cases "i = n1")
          case True thus ?thesis using hsub1_n hf1 hx0 by simp
        next
          case False
          \<comment> \<open>Internal good point: good(glist!i) holds, and glist!i \<noteq> 0, glist!i \<noteq> n_sub.\<close>
          have "0 < i" "i < n1" using \<open>i \<le> n1\<close> \<open>i \<noteq> 0\<close> \<open>i \<noteq> n1\<close> by auto
          have hi_lt_len: "i < length glist" using \<open>i < n1\<close> n1_def hglist_len by simp
          have "glist ! i \<in> set glist" by (rule nth_mem[OF hi_lt_len])
          have "set glist \<subseteq> {i. good i}" unfolding glist_def by auto
          hence "good (glist ! i)" using \<open>glist ! i \<in> set glist\<close> by (by100 blast)
          moreover have "glist ! i \<noteq> 0"
          proof
            assume "glist ! i = 0"
            hence "glist ! i = glist ! 0" using hgl_0 by simp
            have "0 < length glist" using hglist_len by linarith
            hence "i = 0" using nth_eq_iff_index_eq[OF hglist_distinct]
              hi_lt_len \<open>0 < length glist\<close> \<open>glist ! i = glist ! 0\<close> by simp
            thus False using \<open>0 < i\<close> by simp
          qed
          moreover have "glist ! i \<noteq> n_sub"
          proof
            assume "glist ! i = n_sub"
            hence "glist ! i = glist ! n1" using hgl_n by simp
            have "n1 < length glist" using hglist_len n1_def by simp
            hence "i = n1" using nth_eq_iff_index_eq[OF hglist_distinct]
              hi_lt_len \<open>n1 < length glist\<close> \<open>glist ! i = glist ! n1\<close> by simp
            thus False using \<open>i < n1\<close> by simp
          qed
          ultimately show ?thesis unfolding sub1_def good_def by simp
        qed
      qed
    qed
    show ?thesis
      by (rule that[OF hn1_ge hsub1_0 hsub1_n hsub1_mono hsub1_UV hsub1_int])
  qed
  \<comment> \<open>Step 2: For each subinterval, define fi = f restricted + reparametrized.
     Choose paths \<alpha>i in U\<inter>V from x0 to f(ai). Set gi = (\<alpha>_{i-1} * fi) * rev \<alpha>i.\<close>
  \<comment> \<open>Step 2: Construct loops gi at x0, each in U or V, with f \<simeq> g1*...*gm.
     For each i, fi = f restricted to [ai, ai+1] and reparametrized to [0,1].
     Choose \<alpha>i: paths in U\<inter>V from x0 to f(ai) (U\<inter>V path-connected, f(ai) \<in> U\<inter>V).
     Set gi = rev(\<alpha>i) * fi * \<alpha>_{i+1}. Each gi is a loop at x0 in U or V.\<close>
  \<comment> \<open>Step 2a: Choose connecting paths \<alpha>i in U\<inter>V from x0 to f(subdivision i).\<close>
  have hUV_pc: "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
    by (rule assms(5))
  have "\<forall>i\<le>m. \<exists>\<alpha>. top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 (f (subdivision i)) \<alpha>"
  proof (intro allI impI)
    fix i assume "i \<le> m"
    have "f (subdivision i) \<in> U \<inter> V" using hsub_int \<open>i \<le> m\<close> by blast
    thus "\<exists>\<alpha>. top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 (f (subdivision i)) \<alpha>"
      using hUV_pc hx0 unfolding top1_path_connected_on_def by (by100 blast)
  qed
  \<comment> \<open>Step 2b: Construct fi (reparametrized restrictions) and gi (conjugated loops).\<close>
  \<comment> \<open>Step 2c: Show f \<simeq> g1*...*gm and each gi is a loop in U or V.\<close>
  obtain gs :: "(real \<Rightarrow> 'a) list" where
    hgs_len: "length gs = m" and
    hgs_loops: "\<forall>i<m. top1_is_loop_on X TX x0 (gs!i)
        \<and> (gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V)" and
    hgs_product: "top1_path_homotopic_on X TX x0 x0 f
        (foldr top1_path_product gs (top1_constant_path x0))"
  proof -
    \<comment> \<open>Choose connecting paths \<alpha>i from x0 to f(sub(i)) in U\<inter>V.\<close>
    have "\<forall>i\<le>m. \<exists>\<alpha>. top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 (f (subdivision i)) \<alpha>"
    proof (intro allI impI)
      fix i assume "i \<le> m"
      have "f (subdivision i) \<in> U \<inter> V" using hsub_int \<open>i \<le> m\<close> by blast
      thus "\<exists>\<alpha>. top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 (f (subdivision i)) \<alpha>"
        using hUV_pc hx0 unfolding top1_path_connected_on_def by (by100 blast)
    qed
    \<comment> \<open>For each i<m: define fi as f reparametrized on [sub(i), sub(i+1)].
       Define gi = rev(\<alpha>i) * fi * \<alpha>_{i+1}. Each gi is a loop at x0 in U or V.
       The telescoping product g1*...*gm = rev(\<alpha>0) * f * \<alpha>m = f (since \<alpha>0 = \<alpha>m = const_{x0}).
       Each gi maps into U or V because fi maps into U or V and \<alpha>i maps into U\<inter>V \<subseteq> U \<inter> V.\<close>
    \<comment> \<open>For each i<m, define:
       fi(t) = f(sub(i) + t*(sub(i+1)-sub(i))): reparametrization of f on [sub(i),sub(i+1)].
       gi = top1_path_product (top1_path_reverse (\<alpha>i)) (top1_path_product fi (\<alpha>(i+1))):
         loop at x0 via rev(\<alpha>i) from x0 to f(sub(i)), then fi to f(sub(i+1)), then \<alpha>(i+1) to x0.
       Each gi maps into U or V (fi maps into U or V, \<alpha>i maps into U\<inter>V \<subseteq> U,V).
       Telescoping: f \<simeq> f1*f2*...*fm (reparametrization of f)
                      \<simeq> (rev(\<alpha>0)*f1*\<alpha>1) * (rev(\<alpha>1)*f2*\<alpha>2) * ... * (rev(\<alpha>_{m-1})*fm*\<alpha>_m)
                      (by inserting \<alpha>i*rev(\<alpha>i) \<simeq> const between consecutive pieces).\<close>
    \<comment> \<open>Step 2a: Choose connecting paths \<alpha>i.\<close>
    obtain \<alpha>s where h\<alpha>s: "\<forall>i\<le>m. top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))
        x0 (f (subdivision i)) (\<alpha>s i)"
    proof -
      have "\<forall>i. \<exists>\<alpha>. i \<le> m \<longrightarrow> top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))
          x0 (f (subdivision i)) \<alpha>"
      proof
        fix i show "\<exists>\<alpha>. i \<le> m \<longrightarrow> top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))
            x0 (f (subdivision i)) \<alpha>"
        proof (cases "i \<le> m")
          case True
          hence "f (subdivision i) \<in> U \<inter> V" using hsub_int by blast
          then obtain \<alpha> where "top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))
              x0 (f (subdivision i)) \<alpha>"
            using hUV_pc hx0 unfolding top1_path_connected_on_def by (by100 blast)
          thus ?thesis by (by100 blast)
        next
          case False thus ?thesis by simp
        qed
      qed
      hence "\<exists>\<alpha>s. \<forall>i. i \<le> m \<longrightarrow> top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))
          x0 (f (subdivision i)) (\<alpha>s i)" by metis
      thus ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>Modify \<alpha>s so \<alpha>s(0) = const_x0 and \<alpha>s(m) = const_x0 (Munkres convention).\<close>
    define \<alpha>s' where "\<alpha>s' i = (if i = 0 \<or> i = m then top1_constant_path x0 else \<alpha>s i)" for i
    have h\<alpha>s': "\<forall>i\<le>m. top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))
        x0 (f (subdivision i)) (\<alpha>s' i)"
    proof (intro allI impI)
      fix i assume "i \<le> m"
      show "top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 (f (subdivision i)) (\<alpha>s' i)"
      proof (cases "i = 0 \<or> i = m")
        case True
        have h\<alpha>_const: "\<alpha>s' i = top1_constant_path x0" unfolding \<alpha>s'_def using True by simp
        have hf_x0: "f (subdivision i) = x0"
          using True hsub0 hsubm hf
          unfolding top1_is_loop_on_def top1_is_path_on_def by auto
        have hUVX: "U \<inter> V \<subseteq> X" using assms(2,3) unfolding openin_on_def by (by100 blast)
        have "is_topology_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
          by (rule subspace_topology_is_topology_on[OF is_topology_on_strict_imp[OF hT]])
             (use hUVX in blast)
        hence "top1_is_path_on (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 x0 (top1_constant_path x0)"
          by (rule top1_constant_path_is_path) (rule hx0)
        thus ?thesis using h\<alpha>_const hf_x0 by simp
      next
        case False thus ?thesis unfolding \<alpha>s'_def using h\<alpha>s \<open>i \<le> m\<close> by simp
      qed
    qed
    have h\<alpha>s'_0: "\<alpha>s' 0 = top1_constant_path x0" unfolding \<alpha>s'_def by simp
    have h\<alpha>s'_m: "\<alpha>s' m = top1_constant_path x0" unfolding \<alpha>s'_def by simp
    \<comment> \<open>Step 2b: Define reparametrized pieces fi(t) = f(sub(i) + t*(sub(i+1)-sub(i))).\<close>
    define fi where "fi i = (\<lambda>t. f (subdivision i + t * (subdivision (Suc i) - subdivision i)))" for i
    \<comment> \<open>Step 2c: Define conjugated loops gi = (\<alpha>s' i * fi i) * rev(\<alpha>s' (Suc i)).\<close>
    define gi where "gi i = top1_path_product (top1_path_product (\<alpha>s' i) (fi i))
        (top1_path_reverse (\<alpha>s' (Suc i)))" for i
    \<comment> \<open>Step 2d: Build the list gs = [gi 0, gi 1, ..., gi (m-1)].\<close>
    define gs_list where "gs_list = map gi [0..<m]"
    have hgs_len: "length gs_list = m" unfolding gs_list_def by simp
    \<comment> \<open>Step 2e: Each gi is a loop at x0 in U or V.\<close>
    \<comment> \<open>Helper: subdivision is weakly monotone.\<close>
    have hsub_weak_mono: "\<And>j k. j \<le> k \<Longrightarrow> k \<le> m \<Longrightarrow> subdivision j \<le> subdivision k"
    proof -
      fix j k :: nat assume hjk: "j \<le> k" "k \<le> m"
      show "subdivision j \<le> subdivision k" using hjk
      proof (induction "k - j" arbitrary: k)
        case 0 thus ?case by simp
      next
        case (Suc d)
        hence "j \<le> k - 1" "k - 1 \<le> m" "k > 0" by linarith+
        have hIH: "subdivision j \<le> subdivision (k - 1)"
          using Suc.hyps(1)[of "k-1"] \<open>j \<le> k-1\<close> \<open>k-1 \<le> m\<close> Suc.hyps(2) by linarith
        have "k - 1 < m" using Suc.prems(2) \<open>k > 0\<close> by linarith
        have "Suc (k - 1) = k" using \<open>k > 0\<close> by simp
        hence "subdivision (k - 1) < subdivision k"
          using hsub_mono[rule_format, OF \<open>k-1 < m\<close>] by simp
        thus ?case using hIH by linarith
      qed
    qed
    have hsub_in_I: "\<And>j. j \<le> m \<Longrightarrow> subdivision j \<in> I_set"
    proof -
      fix j assume "j \<le> m"
      have "subdivision j \<ge> 0" using hsub_weak_mono[of 0 j] \<open>j \<le> m\<close> hsub0 by simp
      moreover have "subdivision j \<le> 1" using hsub_weak_mono[of j m] \<open>j \<le> m\<close> hsubm by simp
      ultimately show "subdivision j \<in> I_set" unfolding top1_unit_interval_def by simp
    qed
    \<comment> \<open>fi(i) is a path from f(sub(i)) to f(sub(i+1)) in X, with image in U or V.\<close>
    have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
      by (rule top1_is_loop_on_continuous[OF hf])
    have hfi_path: "\<And>i. i < m \<Longrightarrow> top1_is_path_on X TX (f (subdivision i)) (f (subdivision (Suc i))) (fi i)"
    proof -
      fix i assume hi: "i < m"
      show "top1_is_path_on X TX (f (subdivision i)) (f (subdivision (Suc i))) (fi i)"
        unfolding top1_is_path_on_def
      proof (intro conjI)
        show "top1_continuous_map_on I_set I_top X TX (fi i)"
        proof -
          define \<phi> where "\<phi> t = subdivision i + t * (subdivision (Suc i) - subdivision i)" for t
          have hfi_eq: "fi i = f \<circ> \<phi>" unfolding fi_def \<phi>_def comp_def by (rule ext) simp
          have h\<phi>_cont_on: "continuous_on I_set \<phi>" unfolding \<phi>_def by (intro continuous_intros)
          have h\<phi>_maps: "\<forall>t\<in>I_set. \<phi> t \<in> I_set"
          proof (intro ballI)
            fix t assume "t \<in> I_set"
            hence "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by auto
            have hDelta: "subdivision (Suc i) - subdivision i \<ge> 0"
              using hsub_mono[rule_format, OF hi] by simp
            have "\<phi> t \<ge> subdivision i" unfolding \<phi>_def
              using \<open>0 \<le> t\<close> hDelta by (simp add: mult_nonneg_nonneg)
            moreover have "\<phi> t \<le> subdivision (Suc i)"
            proof -
              have "t * (subdivision (Suc i) - subdivision i) \<le> 1 * (subdivision (Suc i) - subdivision i)"
                by (rule mult_right_mono[OF \<open>t \<le> 1\<close> hDelta])
              thus ?thesis unfolding \<phi>_def by simp
            qed
            moreover have "subdivision i \<ge> 0" using hsub_weak_mono[of 0 i] hi hsub0 by simp
            moreover have "subdivision (Suc i) \<le> 1" using hsub_weak_mono[of "Suc i" m] hi hsubm by simp
            ultimately show "\<phi> t \<in> I_set" unfolding top1_unit_interval_def by simp
          qed
          have h\<phi>_cont: "top1_continuous_map_on I_set I_top I_set I_top \<phi>"
          proof -
            have hItop: "I_top = subspace_topology UNIV top1_open_sets I_set"
              unfolding top1_unit_interval_topology_def top1_unit_interval_def by simp
            show ?thesis unfolding top1_continuous_map_on_def
            proof (intro conjI ballI)
              fix t assume "t \<in> I_set" thus "\<phi> t \<in> I_set" using h\<phi>_maps by simp
            next
              fix V assume hV: "V \<in> I_top"
              obtain W where hW: "open W" "V = I_set \<inter> W"
                using hV unfolding hItop subspace_topology_def top1_open_sets_def by auto
              have "{t \<in> I_set. \<phi> t \<in> V} = {t \<in> I_set. \<phi> t \<in> W}"
                using h\<phi>_maps hW(2) by (by100 blast)
              also have "\<dots> = I_set \<inter> \<phi> -` W" by (by100 blast)
              also have "\<dots> \<in> I_top"
              proof -
                have "\<exists>A. open A \<and> A \<inter> I_set = \<phi> -` W \<inter> I_set"
                  using iffD1[OF continuous_on_open_invariant h\<phi>_cont_on] hW(1) by simp
                then obtain A where "open A" "A \<inter> I_set = \<phi> -` W \<inter> I_set" by (by100 blast)
                hence "I_set \<inter> A \<in> I_top" unfolding hItop subspace_topology_def top1_open_sets_def
                  by (by100 blast)
                moreover have "I_set \<inter> \<phi> -` W = I_set \<inter> A"
                  using \<open>A \<inter> I_set = \<phi> -` W \<inter> I_set\<close> by (by100 blast)
                ultimately show ?thesis by simp
              qed
              finally show "{t \<in> I_set. \<phi> t \<in> V} \<in> I_top" .
            qed
          qed
          show ?thesis unfolding hfi_eq
            by (rule top1_continuous_map_on_comp[OF h\<phi>_cont hf_cont])
        qed
        show "fi i 0 = f (subdivision i)" unfolding fi_def by simp
        show "fi i 1 = f (subdivision (Suc i))" unfolding fi_def by simp
      qed
    qed
    have hfi_UV: "\<And>i. i < m \<Longrightarrow> fi i ` I_set \<subseteq> U \<or> fi i ` I_set \<subseteq> V"
    proof -
      fix i assume hi: "i < m"
      have "fi i ` I_set = f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)}"
      proof (intro set_eqI iffI)
        fix y assume "y \<in> fi i ` I_set"
        then obtain t where ht: "t \<in> I_set" "y = fi i t" by (by100 blast)
        have hlb: "subdivision i + t * (subdivision (Suc i) - subdivision i) \<ge> subdivision i"
          using ht(1) hsub_mono[rule_format, OF hi]
          unfolding top1_unit_interval_def by (simp add: mult_nonneg_nonneg)
        moreover have hub: "subdivision i + t * (subdivision (Suc i) - subdivision i) \<le> subdivision (Suc i)"
        proof -
          have "t \<le> 1" using ht(1) unfolding top1_unit_interval_def by simp
          have "subdivision (Suc i) - subdivision i \<ge> 0" using hsub_mono[rule_format, OF hi] by simp
          hence "t * (subdivision (Suc i) - subdivision i) \<le> 1 * (subdivision (Suc i) - subdivision i)"
            using mult_right_mono[OF \<open>t \<le> 1\<close>] by simp
          thus ?thesis by simp
        qed
        moreover have "subdivision i + t * (subdivision (Suc i) - subdivision i) \<in> I_set"
        proof -
          have "subdivision 0 \<le> subdivision i"
          proof (cases "i = 0")
            case True thus ?thesis by simp
          next
            case False hence "0 < i" by simp
            show ?thesis
            proof (rule order.strict_implies_order)
              show "subdivision 0 < subdivision i"
                using \<open>0 < i\<close> hi hsub_mono
              proof (induction i)
                case 0 thus ?case by simp
              next
                case (Suc n)
                show ?case
                proof (cases "n = 0")
                  case True thus ?thesis using hsub_mono Suc.prems by simp
                next
                  case False
                  hence "subdivision 0 < subdivision n" using Suc by simp
                  also have "subdivision n < subdivision (Suc n)" using hsub_mono Suc.prems by simp
                  finally show ?thesis .
                qed
              qed
            qed
          qed
          hence "subdivision i \<ge> 0" using hsub0 by simp
          have "subdivision (Suc i) \<le> subdivision m"
          proof (cases "Suc i = m")
            case True thus ?thesis by simp
          next
            case False hence "Suc i < m" using hi by simp
            show ?thesis
            proof (rule order.strict_implies_order)
              show "subdivision (Suc i) < subdivision m"
                using \<open>Suc i < m\<close> hsub_mono
              proof (induction m)
                case 0 thus ?case by simp
              next
                case (Suc n)
                show ?case
                proof (cases "Suc i = n")
                  case True thus ?thesis using hsub_mono Suc.prems by simp
                next
                  case False
                  hence "Suc i < n" using Suc.prems by simp
                  hence "subdivision (Suc i) < subdivision n" using Suc by simp
                  also have "subdivision n < subdivision (Suc n)" using hsub_mono Suc.prems by simp
                  finally show ?thesis .
                qed
              qed
            qed
          qed
          hence "subdivision (Suc i) \<le> 1" using hsubm by simp
          have "0 \<le> subdivision i + t * (subdivision (Suc i) - subdivision i)"
            using \<open>subdivision i \<ge> 0\<close> hlb by linarith
          moreover have "subdivision i + t * (subdivision (Suc i) - subdivision i) \<le> 1"
            using \<open>subdivision (Suc i) \<le> 1\<close> hub by linarith
          ultimately show ?thesis unfolding top1_unit_interval_def by simp
        qed
        ultimately show "y \<in> f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)}"
          using ht(2) unfolding fi_def by (by100 blast)
      next
        fix y assume "y \<in> f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)}"
        then obtain s where hs: "s \<in> I_set" "subdivision i \<le> s" "s \<le> subdivision (Suc i)" "y = f s"
          by (by100 blast)
        define t where "t = (s - subdivision i) / (subdivision (Suc i) - subdivision i)"
        have hDelta: "subdivision (Suc i) - subdivision i > 0" using hsub_mono[rule_format, OF hi] by simp
        have "t \<ge> 0" unfolding t_def using hs(2) hDelta by simp
        moreover have "t \<le> 1" unfolding t_def using hs(3) hDelta by (simp add: divide_le_eq_1)
        ultimately have "t \<in> I_set" unfolding top1_unit_interval_def by simp
        moreover have "fi i t = f s"
        proof -
          have "subdivision i + (s - subdivision i) / (subdivision (Suc i) - subdivision i)
              * (subdivision (Suc i) - subdivision i) = s"
            using hDelta by simp
          thus ?thesis unfolding fi_def t_def by simp
        qed
        ultimately have "fi i t \<in> fi i ` I_set" by (by100 blast)
        thus "y \<in> fi i ` I_set" using hs(4) \<open>fi i t = f s\<close> by simp
      qed
      moreover have "f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)} \<subseteq> U
          \<or> f ` {s\<in>I_set. subdivision i \<le> s \<and> s \<le> subdivision (Suc i)} \<subseteq> V"
        using hsub_UV[rule_format, OF hi] by simp
      ultimately show "fi i ` I_set \<subseteq> U \<or> fi i ` I_set \<subseteq> V" by simp
    qed
    have hgs_loops: "\<forall>i<m. top1_is_loop_on X TX x0 (gs_list!i)
        \<and> (gs_list!i ` I_set \<subseteq> U \<or> gs_list!i ` I_set \<subseteq> V)"
    proof (intro allI impI conjI)
      fix i assume hi: "i < m"
      have hTX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
      have hUV_sub: "U \<inter> V \<subseteq> X" using assms(2,3) unfolding openin_on_def by (by100 blast)
      have h\<alpha>i: "top1_is_path_on X TX x0 (f (subdivision i)) (\<alpha>s' i)"
        by (rule path_in_subspace_is_path_in_ambient'[OF hTX hUV_sub h\<alpha>s'[rule_format]])
           (use hi in simp)
      have h\<alpha>si: "top1_is_path_on X TX x0 (f (subdivision (Suc i))) (\<alpha>s' (Suc i))"
        by (rule path_in_subspace_is_path_in_ambient'[OF hTX hUV_sub h\<alpha>s'[rule_format]])
           (use hi in simp)
      have hrev: "top1_is_path_on X TX (f (subdivision (Suc i))) x0 (top1_path_reverse (\<alpha>s' (Suc i)))"
        by (rule top1_path_reverse_is_path[OF h\<alpha>si])
      have hprod1: "top1_is_path_on X TX x0 (f (subdivision (Suc i)))
          (top1_path_product (\<alpha>s' i) (fi i))"
        by (rule top1_path_product_is_path[OF hTX h\<alpha>i hfi_path[OF hi]])
      have hgi_path: "top1_is_path_on X TX x0 x0 (gi i)"
        unfolding gi_def by (rule top1_path_product_is_path[OF hTX hprod1 hrev])
      have "gs_list ! i = gi i" unfolding gs_list_def using hi by simp
      show "top1_is_loop_on X TX x0 (gs_list ! i)"
        unfolding \<open>gs_list ! i = gi i\<close> top1_is_loop_on_def using hgi_path by simp
      \<comment> \<open>Image: \<alpha>s' \<subseteq> U\<inter>V, fi \<subseteq> U or V, rev \<subseteq> U\<inter>V.\<close>
      show "gs_list ! i ` I_set \<subseteq> U \<or> gs_list ! i ` I_set \<subseteq> V"
      proof -
        \<comment> \<open>Path product image \<subseteq> union of component images.\<close>
        have hprod_img: "\<And>f g :: real \<Rightarrow> 'a. top1_path_product f g ` I_set \<subseteq> f ` I_set \<union> g ` I_set"
        proof -
          fix f g :: "real \<Rightarrow> 'a"
          show "top1_path_product f g ` I_set \<subseteq> f ` I_set \<union> g ` I_set"
          proof
            fix y assume "y \<in> top1_path_product f g ` I_set"
            then obtain t where ht: "t \<in> I_set" "y = top1_path_product f g t" by (by100 blast)
            show "y \<in> f ` I_set \<union> g ` I_set"
            proof (cases "t \<le> 1/2")
              case True
              hence "y = f (2 * t)" using ht(2) unfolding top1_path_product_def by simp
              moreover have "2 * t \<in> I_set" using ht(1) True unfolding top1_unit_interval_def by auto
              ultimately show ?thesis by (by100 blast)
            next
              case False
              hence "y = g (2 * t - 1)" using ht(2) unfolding top1_path_product_def by simp
              moreover have "2 * t - 1 \<in> I_set" using ht(1) False unfolding top1_unit_interval_def by auto
              ultimately show ?thesis by (by100 blast)
            qed
          qed
        qed
        have hrev_img: "\<And>f :: real \<Rightarrow> 'a. top1_path_reverse f ` I_set \<subseteq> f ` I_set"
        proof -
          fix f :: "real \<Rightarrow> 'a"
          show "top1_path_reverse f ` I_set \<subseteq> f ` I_set"
          proof
            fix y assume "y \<in> top1_path_reverse f ` I_set"
            then obtain t where "t \<in> I_set" "y = f (1 - t)"
              unfolding top1_path_reverse_def by (by100 blast)
            moreover have "1 - t \<in> I_set" using \<open>t \<in> I_set\<close> unfolding top1_unit_interval_def by auto
            ultimately show "y \<in> f ` I_set" by (by100 blast)
          qed
        qed
        \<comment> \<open>gi image \<subseteq> \<alpha>s'(i) \<union> fi(i) \<union> rev(\<alpha>s'(Suc i)) images.\<close>
        have "gi i ` I_set \<subseteq> (top1_path_product (\<alpha>s' i) (fi i)) ` I_set
            \<union> (top1_path_reverse (\<alpha>s' (Suc i))) ` I_set"
          unfolding gi_def using hprod_img by (by100 blast)
        also have "\<dots> \<subseteq> \<alpha>s' i ` I_set \<union> fi i ` I_set \<union> \<alpha>s' (Suc i) ` I_set"
          using hprod_img hrev_img by (by100 blast)
        finally have hgi_img: "gi i ` I_set \<subseteq> \<alpha>s' i ` I_set \<union> fi i ` I_set \<union> \<alpha>s' (Suc i) ` I_set" .
        \<comment> \<open>\<alpha>s' images \<subseteq> U\<inter>V.\<close>
        have h\<alpha>i_maps: "\<forall>t\<in>I_set. \<alpha>s' i t \<in> U \<inter> V"
          using h\<alpha>s'[rule_format, of i] hi
          unfolding top1_is_path_on_def top1_continuous_map_on_def by simp
        have h\<alpha>i_img: "\<alpha>s' i ` I_set \<subseteq> U \<inter> V" using h\<alpha>i_maps by (by100 blast)
        have h\<alpha>si_maps: "\<forall>t\<in>I_set. \<alpha>s' (Suc i) t \<in> U \<inter> V"
          using h\<alpha>s'[rule_format, of "Suc i"] hi
          unfolding top1_is_path_on_def top1_continuous_map_on_def by simp
        have h\<alpha>si_img: "\<alpha>s' (Suc i) ` I_set \<subseteq> U \<inter> V" using h\<alpha>si_maps by (by100 blast)
        have "gi i ` I_set \<subseteq> U \<or> gi i ` I_set \<subseteq> V"
        proof (rule disjE[OF hfi_UV[OF hi]])
          assume hfiU: "fi i ` I_set \<subseteq> U"
          have hunionU: "\<alpha>s' i ` I_set \<union> fi i ` I_set \<union> \<alpha>s' (Suc i) ` I_set \<subseteq> U"
            using h\<alpha>i_img h\<alpha>si_img hfiU by (by100 blast)
          hence "gi i ` I_set \<subseteq> U" by (rule subset_trans[OF hgi_img])
          thus ?thesis by (by100 blast)
        next
          assume "fi i ` I_set \<subseteq> V"
          have h\<alpha>iV: "\<alpha>s' i ` I_set \<subseteq> V" using h\<alpha>i_img by (by100 blast)
          have h\<alpha>siV: "\<alpha>s' (Suc i) ` I_set \<subseteq> V" using h\<alpha>si_img by (by100 blast)
          have hunionV: "\<alpha>s' i ` I_set \<union> fi i ` I_set \<union> \<alpha>s' (Suc i) ` I_set \<subseteq> V"
            using h\<alpha>iV \<open>fi i ` I_set \<subseteq> V\<close> h\<alpha>siV by (by100 blast)
          hence "gi i ` I_set \<subseteq> V" by (rule subset_trans[OF hgi_img])
          thus ?thesis by (by100 blast)
        qed
        thus ?thesis unfolding \<open>gs_list ! i = gi i\<close> by simp
      qed
    qed
    \<comment> \<open>Step 2f: f \<simeq> foldr (*) gs_list const.\<close>
    \<comment> \<open>Step 2f-1: f \<simeq> f1*f2*...*fm (Theorem 51.3: reparametrization preserves homotopy class).\<close>
    define fi_list where "fi_list = map fi [0..<m]"
    have hf_path: "top1_is_path_on X TX x0 x0 f"
      using hf unfolding top1_is_loop_on_def by (by100 blast)
    have hTX_is: "is_topology_on X TX"
      using hT unfolding is_topology_on_strict_def by (by100 blast)
    have hf_fi: "top1_path_homotopic_on X TX x0 x0 f
        (foldr top1_path_product fi_list (top1_constant_path x0))"
      unfolding fi_list_def fi_def
      by (rule Theorem_51_3_aux[OF hTX_is hf_path hm hsub0 hsubm hsub_mono[rule_format]])
    \<comment> \<open>Step 2f-2: f1*...*fm \<simeq> g1*...*gm (telescoping via \<alpha>i * rev(\<alpha>i) \<simeq> const).\<close>
    have hfi_gi: "top1_path_homotopic_on X TX x0 x0
        (foldr top1_path_product fi_list (top1_constant_path x0))
        (foldr top1_path_product gs_list (top1_constant_path x0))"
    proof -
      have hTX': "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
      have hx0_X: "x0 \<in> X" using hx0 assms(2) unfolding openin_on_def by (by100 blast)
      have hUV_sub: "U \<inter> V \<subseteq> X" using assms(2,3) unfolding openin_on_def by (by100 blast)
      \<comment> \<open>Lift \<alpha>s' paths to X.\<close>
      have h\<alpha>'_X: "\<And>i. i \<le> m \<Longrightarrow> top1_is_path_on X TX x0 (f (subdivision i)) (\<alpha>s' i)"
        by (rule path_in_subspace_is_path_in_ambient'[OF hTX' hUV_sub h\<alpha>s'[rule_format]]) simp
      \<comment> \<open>Textbook "direct computation": by induction on m.
         Base m=1: g0*const = ((const*f0)*rev(const))*const \<simeq> f0*const.
         Step: use gi = (\<alpha>i*fi)*rev(\<alpha>(i+1)) and cancel rev(\<alpha>k)*\<alpha>k \<simeq> const.\<close>
      \<comment> \<open>The telescoping computation, following the textbook literally.
         For each i: gi = (\<alpha>i*fi)*rev(\<alpha>(i+1)).
         The product g0*g1*...*g(m-1)*const telescopes because
         rev(\<alpha>(k))*\<alpha>(k) cancels at each junction.
         With \<alpha>0 = \<alpha>m = const, the outermost factors also simplify.\<close>
      \<comment> \<open>Key facts for the algebra:\<close>
      have hrev_const: "top1_path_reverse (top1_constant_path x0) = top1_constant_path x0"
        unfolding top1_path_reverse_def top1_constant_path_def by (rule ext) simp
      have hfi_path_X: "\<And>i. i < m \<Longrightarrow> top1_is_path_on X TX (f (subdivision i)) (f (subdivision (Suc i))) (fi i)"
        by (rule hfi_path)
      have hconst_path: "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
        by (rule top1_constant_path_is_path[OF hTX' hx0_X])
      have hf0: "f 0 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      have hf1: "f 1 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      have hfsub0: "f (subdivision 0) = x0" using hsub0 hf0 by simp
      have hfsubm: "f (subdivision m) = x0" using hsubm hf1 by simp
      have hgi_eq: "\<And>i. i < m \<Longrightarrow> gs_list ! i = top1_path_product
          (top1_path_product (\<alpha>s' i) (fi_list ! i)) (top1_path_reverse (\<alpha>s' (Suc i)))"
        unfolding gs_list_def fi_list_def gi_def using hm by simp
      have hfi_len: "length fi_list = m" unfolding fi_list_def by simp
      have hfi_list_path: "\<And>i. i < m \<Longrightarrow> top1_is_path_on X TX
          (f (subdivision i)) (f (subdivision (Suc i))) (fi_list ! i)"
        unfolding fi_list_def using hfi_path_X by simp
      show ?thesis
        by (rule telescoping_conjugated_product[where a="\<lambda>i. f (subdivision i)",
            OF hTX' hx0_X hm hfi_len hgs_len h\<alpha>'_X hfi_list_path hgi_eq
            h\<alpha>s'_0 h\<alpha>s'_m hfsub0 hfsubm])
    qed
    have hgs_product: "top1_path_homotopic_on X TX x0 x0 f
        (foldr top1_path_product gs_list (top1_constant_path x0))"
    proof -
      have hTX': "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
      show ?thesis using Lemma_51_1_path_homotopic_trans[OF hTX' hf_fi hfi_gi] .
    qed
    show ?thesis by (rule that[OF hgs_len hgs_loops hgs_product])
  qed
  show "\<exists>n\<ge>1. \<exists>gs. length gs = n \<and>
       (\<forall>i<n. top1_is_loop_on X TX x0 (gs ! i) \<and>
              (gs ! i ` I_set \<subseteq> U \<or> gs ! i ` I_set \<subseteq> V)) \<and>
       top1_path_homotopic_on X TX x0 x0 f
        (foldr top1_path_product gs (top1_constant_path x0))"
    using hm hgs_len hgs_loops hgs_product by (by100 auto)
qed


text \<open>Helper: path homotopy in a subspace implies path homotopy in the ambient space.\<close>
lemma path_homotopic_subspace_to_ambient:
  assumes hTX: "is_topology_on X TX" and hUsub: "U \<subseteq> X"
      and hTU: "TU = subspace_topology X TX U"
      and hhom: "top1_path_homotopic_on U TU x0 x1 f g"
  shows "top1_path_homotopic_on X TX x0 x1 f g"
proof -
  \<comment> \<open>A path homotopy F: I\<times>I \<rightarrow> U in the subspace is also a path homotopy F: I\<times>I \<rightarrow> X
     in the ambient space, since U \<subseteq> X and the subspace topology makes F continuous in X.\<close>
  have hf_path: "top1_is_path_on U TU x0 x1 f"
    using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
  have hg_path: "top1_is_path_on U TU x0 x1 g"
    using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
  have "\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology U TU F
      \<and> (\<forall>s\<in>I_set. F (s, 0) = f s) \<and> (\<forall>s\<in>I_set. F (s, 1) = g s)
      \<and> (\<forall>t\<in>I_set. F (0, t) = x0) \<and> (\<forall>t\<in>I_set. F (1, t) = x1)"
    using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
  then obtain F where hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology U TU F"
      and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hFl: "\<forall>t\<in>I_set. F (0, t) = x0" and hFr: "\<forall>t\<in>I_set. F (1, t) = x1"
    by (by100 auto)
  \<comment> \<open>F is continuous in X (subspace continuous \<Rightarrow> ambient continuous).\<close>
  have hF_cont_X: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix p assume hp: "p \<in> I_set \<times> I_set"
    have "F p \<in> U" using hF_cont hp unfolding top1_continuous_map_on_def by (by100 blast)
    thus "F p \<in> X" using hUsub by (by100 blast)
  next
    fix V assume hV: "V \<in> TX"
    have hVU: "U \<inter> V \<in> TU" unfolding hTU subspace_topology_def using hV by (by100 blast)
    have "{p \<in> I_set \<times> I_set. F p \<in> V} = {p \<in> I_set \<times> I_set. F p \<in> U \<inter> V}"
    proof (rule set_eqI)
      fix p show "(p \<in> {p \<in> I_set \<times> I_set. F p \<in> V}) = (p \<in> {p \<in> I_set \<times> I_set. F p \<in> U \<inter> V})"
        using hF_cont unfolding top1_continuous_map_on_def by (by100 blast)
    qed
    also have "\<dots> \<in> II_topology"
      using hF_cont hVU unfolding top1_continuous_map_on_def by (by100 blast)
    finally show "{p \<in> I_set \<times> I_set. F p \<in> V} \<in> II_topology" .
  qed
  have hf_path_X: "top1_is_path_on X TX x0 x1 f"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    have hf_cont_U: "top1_continuous_map_on I_set I_top U TU f"
      using hf_path unfolding top1_is_path_on_def by (by100 blast)
    show "top1_continuous_map_on I_set I_top X TX f"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set"
      thus "f s \<in> X" using hf_cont_U hUsub unfolding top1_continuous_map_on_def by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have hVU: "U \<inter> V \<in> TU" unfolding hTU subspace_topology_def using hV by (by100 blast)
      have "{s \<in> I_set. f s \<in> V} = {s \<in> I_set. f s \<in> U \<inter> V}"
        using hf_cont_U unfolding top1_continuous_map_on_def by (by100 blast)
      also have "\<dots> \<in> I_top"
        using hf_cont_U hVU unfolding top1_continuous_map_on_def by (by100 blast)
      finally show "{s \<in> I_set. f s \<in> V} \<in> I_top" .
    qed
    show "f 0 = x0" using hf_path unfolding top1_is_path_on_def by (by100 blast)
    show "f 1 = x1" using hf_path unfolding top1_is_path_on_def by (by100 blast)
  qed
  have hg_path_X: "top1_is_path_on X TX x0 x1 g"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    have hg_cont_U: "top1_continuous_map_on I_set I_top U TU g"
      using hg_path unfolding top1_is_path_on_def by (by100 blast)
    show "top1_continuous_map_on I_set I_top X TX g"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set"
      thus "g s \<in> X" using hg_cont_U hUsub unfolding top1_continuous_map_on_def by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have hVU: "U \<inter> V \<in> TU" unfolding hTU subspace_topology_def using hV by (by100 blast)
      have "{s \<in> I_set. g s \<in> V} = {s \<in> I_set. g s \<in> U \<inter> V}"
        using hg_cont_U unfolding top1_continuous_map_on_def by (by100 blast)
      also have "\<dots> \<in> I_top"
        using hg_cont_U hVU unfolding top1_continuous_map_on_def by (by100 blast)
      finally show "{s \<in> I_set. g s \<in> V} \<in> I_top" .
    qed
    show "g 0 = x0" using hg_path unfolding top1_is_path_on_def by (by100 blast)
    show "g 1 = x1" using hg_path unfolding top1_is_path_on_def by (by100 blast)
  qed
  show ?thesis unfolding top1_path_homotopic_on_def
    using hf_path_X hg_path_X hF_cont_X hF0 hF1 hFl hFr by (by100 blast)
qed


text \<open>The induced homomorphism h_* commutes with \<pi>_1 multiplication.
  For continuous h: (X,x0) \<rightarrow> (Y,y0), h_*([f] \<cdot> [g]) = h_*([f]) \<cdot> h_*([g]).
  Key: h \<circ> (f*g) = (h\<circ>f)*(h\<circ>g) pointwise, and continuous maps preserve path homotopy.\<close>
lemma induced_hom_mul:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hh0: "h x0 = y0"
      and hf: "top1_is_loop_on X TX x0 f"
      and hg: "top1_is_loop_on X TX x0 g"
  shows "top1_fundamental_group_induced_on X TX x0 Y TY y0 h
      (top1_fundamental_group_mul X TX x0
        {k. top1_loop_equiv_on X TX x0 f k}
        {k. top1_loop_equiv_on X TX x0 g k})
    = top1_fundamental_group_mul Y TY y0
        (top1_fundamental_group_induced_on X TX x0 Y TY y0 h
          {k. top1_loop_equiv_on X TX x0 f k})
        (top1_fundamental_group_induced_on X TX x0 Y TY y0 h
          {k. top1_loop_equiv_on X TX x0 g k})"
proof -
  \<comment> \<open>Step 1: mul([f],[g]) = [f*g].\<close>
  have hmul_eq: "top1_fundamental_group_mul X TX x0
      {k. top1_loop_equiv_on X TX x0 f k} {k. top1_loop_equiv_on X TX x0 g k}
    = {k. top1_loop_equiv_on X TX x0 (top1_path_product f g) k}"
    by (rule top1_fundamental_group_mul_class[OF hTX hf hg])
  \<comment> \<open>Step 2: h_*([f*g]) = [h\<circ>(f*g)] = [(h\<circ>f)*(h\<circ>g)] (by hcomp_prod).\<close>
  have hcomp: "\<And>f' g'. h \<circ> (top1_path_product f' g') = top1_path_product (h \<circ> f') (h \<circ> g')"
    unfolding top1_path_product_def comp_def by (rule ext) auto
  \<comment> \<open>Step 3: h_*([f]) = [h\<circ>f]. Need: the induced map on equiv classes is well-defined.\<close>
  \<comment> \<open>For f' \<in> [f]: loop_equiv(f, f') \<Longrightarrow> loop_equiv(h\<circ>f, h\<circ>f')
     by continuous_preserves_path_homotopic.\<close>
  have hfg_loop: "top1_is_loop_on X TX x0 (top1_path_product f g)"
    unfolding top1_is_loop_on_def
    by (rule top1_path_product_is_path[OF hTX])
       (use hf hg in \<open>unfold top1_is_loop_on_def, blast\<close>)+
  have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
    using hg unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have hhf_cont: "top1_continuous_map_on I_set I_top Y TY (h \<circ> f)"
    by (rule top1_continuous_map_on_comp[OF hf_cont hh])
  have hhg_cont: "top1_continuous_map_on I_set I_top Y TY (h \<circ> g)"
    by (rule top1_continuous_map_on_comp[OF hg_cont hh])
  have hf0: "f 0 = x0" "f 1 = x0"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
  have hg0: "g 0 = x0" "g 1 = x0"
    using hg unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
  have hhf_loop: "top1_is_loop_on Y TY y0 (h \<circ> f)"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hhf_cont hf0 hh0 by (simp add: comp_def)
  have hhg_loop: "top1_is_loop_on Y TY y0 (h \<circ> g)"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hhg_cont hg0 hh0 by (simp add: comp_def)
  \<comment> \<open>LHS: h_*(mul([f],[g])) = h_*([f*g])
       = {k. \<exists>j \<in> [f*g]. loop_equiv_Y(h\<circ>j, k)}
     RHS: mul(h_*([f]), h_*([g]))
       = {k. \<exists>j1 \<in> h_*([f]). \<exists>j2 \<in> h_*([g]). loop_equiv_Y(j1*j2, k)}
     These are equal because h\<circ>(f*g) = (h\<circ>f)*(h\<circ>g) and loop_equiv is transitive.\<close>
  \<comment> \<open>General fact: induced([p]) = [h\<circ>p] for any loop p at x0.\<close>
  have hind_gen: "\<And>p. top1_is_loop_on X TX x0 p \<Longrightarrow>
      top1_fundamental_group_induced_on X TX x0 Y TY y0 h
        {k. top1_loop_equiv_on X TX x0 p k}
      = {k. top1_loop_equiv_on Y TY y0 (h \<circ> p) k}"
  proof (intro set_eqI iffI)
    fix p k assume hpl: "top1_is_loop_on X TX x0 p"
    assume "k \<in> top1_fundamental_group_induced_on X TX x0 Y TY y0 h
        {k. top1_loop_equiv_on X TX x0 p k}"
    then obtain j where hj: "top1_loop_equiv_on X TX x0 p j"
        and hk: "top1_loop_equiv_on Y TY y0 (h \<circ> j) k"
      unfolding top1_fundamental_group_induced_on_def by (by100 blast)
    have hpj: "top1_path_homotopic_on X TX x0 x0 p j"
      using hj unfolding top1_loop_equiv_on_def by (by100 blast)
    have hhp_hj: "top1_path_homotopic_on Y TY y0 y0 (h \<circ> p) (h \<circ> j)"
      using continuous_preserves_path_homotopic[OF hTX hTY hh hpj] hh0 by simp
    have hpl_cont: "top1_continuous_map_on I_set I_top X TX p"
      using hpl unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hp0: "p 0 = x0" "p 1 = x0"
      using hpl unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
    have hhpl: "top1_is_loop_on Y TY y0 (h \<circ> p)"
      unfolding top1_is_loop_on_def top1_is_path_on_def
      using top1_continuous_map_on_comp[OF hpl_cont hh] by (simp add: comp_def hp0 hh0)
    have hjl: "top1_is_loop_on X TX x0 j"
      using hj unfolding top1_loop_equiv_on_def by (by100 blast)
    have hjl_cont: "top1_continuous_map_on I_set I_top X TX j"
      using hjl unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hj0: "j 0 = x0" "j 1 = x0"
      using hjl unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
    have hhjl: "top1_is_loop_on Y TY y0 (h \<circ> j)"
      unfolding top1_is_loop_on_def top1_is_path_on_def
      using top1_continuous_map_on_comp[OF hjl_cont hh] by (simp add: comp_def hj0 hh0)
    have "top1_loop_equiv_on Y TY y0 (h \<circ> p) (h \<circ> j)"
      unfolding top1_loop_equiv_on_def using hhpl hhjl hhp_hj by (by100 blast)
    hence "top1_loop_equiv_on Y TY y0 (h \<circ> p) k"
      using hk by (rule top1_loop_equiv_on_trans[OF hTY])
    thus "k \<in> {k. top1_loop_equiv_on Y TY y0 (h \<circ> p) k}" by (by100 blast)
  next
    fix p k assume hpl: "top1_is_loop_on X TX x0 p"
    assume "k \<in> {k. top1_loop_equiv_on Y TY y0 (h \<circ> p) k}"
    hence hk: "top1_loop_equiv_on Y TY y0 (h \<circ> p) k" by (by100 blast)
    have hp_refl: "top1_loop_equiv_on X TX x0 p p"
      by (rule top1_loop_equiv_on_refl[OF hpl])
    show "k \<in> top1_fundamental_group_induced_on X TX x0 Y TY y0 h
        {k. top1_loop_equiv_on X TX x0 p k}"
      unfolding top1_fundamental_group_induced_on_def using hp_refl hk by (by100 blast)
  qed
  have hLHS: "top1_fundamental_group_induced_on X TX x0 Y TY y0 h
      {k. top1_loop_equiv_on X TX x0 (top1_path_product f g) k}
    = {k. top1_loop_equiv_on Y TY y0 (h \<circ> (top1_path_product f g)) k}"
    by (rule hind_gen[OF hfg_loop])
  have hind_f: "top1_fundamental_group_induced_on X TX x0 Y TY y0 h
      {k. top1_loop_equiv_on X TX x0 f k}
    = {k. top1_loop_equiv_on Y TY y0 (h \<circ> f) k}"
    by (rule hind_gen[OF hf])
  have hind_g: "top1_fundamental_group_induced_on X TX x0 Y TY y0 h
      {k. top1_loop_equiv_on X TX x0 g k}
    = {k. top1_loop_equiv_on Y TY y0 (h \<circ> g) k}"
    by (rule hind_gen[OF hg])
  \<comment> \<open>RHS = mul([h\<circ>f], [h\<circ>g]) = [(h\<circ>f)*(h\<circ>g)] = [h\<circ>(f*g)] by hcomp.\<close>
  have hmul_Y: "top1_fundamental_group_mul Y TY y0
      {k. top1_loop_equiv_on Y TY y0 (h \<circ> f) k}
      {k. top1_loop_equiv_on Y TY y0 (h \<circ> g) k}
    = {k. top1_loop_equiv_on Y TY y0 (top1_path_product (h \<circ> f) (h \<circ> g)) k}"
    by (rule top1_fundamental_group_mul_class[OF hTY hhf_loop hhg_loop])
  have hcomp_fg: "h \<circ> (top1_path_product f g) = top1_path_product (h \<circ> f) (h \<circ> g)"
    by (rule hcomp)
  show ?thesis unfolding hmul_eq hLHS hind_f hind_g hmul_Y hcomp_fg by (by100 simp)
qed

end
