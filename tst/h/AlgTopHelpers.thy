theory AlgTopHelpers
imports Complex_Main
begin

lemma sqnorm_memI: "fst z ^ 2 + snd z ^ 2 > R ^ 2 \<Longrightarrow>
    z \<in> {x :: real \<times> real. fst x ^ 2 + snd x ^ 2 > R ^ 2}" by blast

lemma right_top_strip_connected:
  fixes N :: real assumes "N > 0"
  shows "connected ({N<..} \<times> (UNIV::real set) \<union> (UNIV::real set) \<times> {N<..})"
proof (rule connected_Un)
  show "connected ({N<..} \<times> (UNIV :: real set))" by (rule connected_Times) simp_all
  show "connected ((UNIV :: real set) \<times> {N<..})" by (rule connected_Times) simp_all
  have "(N+1) > N" by simp
  hence "(N+1, N+1) \<in> {N<..} \<times> UNIV \<inter> (UNIV \<times> {N<..} :: (real\<times>real) set)" by simp
  thus "{N<..} \<times> UNIV \<inter> (UNIV \<times> {N<..} :: (real\<times>real) set) \<noteq> {}" by blast
qed

lemma four_strips_connected:
  fixes N :: "real" assumes "N > 0"
  shows "connected ({N<..} \<times> UNIV \<union> UNIV \<times> {N<..} \<union> {..<-N} \<times> UNIV \<union> UNIV \<times> {..<-N} :: (real\<times>real) set)"
proof -
  have hRT: "connected ({N<..} \<times> UNIV \<union> UNIV \<times> {N<..} :: (real\<times>real) set)"
    by (rule right_top_strip_connected[OF assms])
  have hL: "connected ({..<-N} \<times> (UNIV::real set))" by (rule connected_Times) simp_all
  have hB: "connected ((UNIV::real set) \<times> {..<-N})" by (rule connected_Times) simp_all
  have "(-N-1) < -N" by simp
  hence "(-N-1, N+1) \<in> UNIV \<times> {N<..}" by simp
  hence h1: "(-N-1, N+1) \<in> (({N<..} \<times> UNIV \<union> UNIV \<times> {N<..}) :: (real\<times>real) set)" by blast
  have h2: "(-N-1, N+1) \<in> (({..<-N} \<times> UNIV) :: (real\<times>real) set)" using \<open>(-N-1) < -N\<close> by simp
  have hRTL: "connected (({N<..} \<times> UNIV \<union> UNIV \<times> {N<..} \<union> {..<-N} \<times> UNIV) :: (real\<times>real) set)"
    by (rule connected_Un[OF hRT hL]) (use h1 h2 in blast)
  have h3: "(-N-1, -N-1) \<in> (({..<-N} \<times> UNIV) :: (real\<times>real) set)" using \<open>(-N-1) < -N\<close> by simp
  hence h3': "(-N-1, -N-1) \<in> (({N<..} \<times> UNIV \<union> UNIV \<times> {N<..} \<union> {..<-N} \<times> UNIV) :: (real\<times>real) set)" by blast
  have h4: "(-N-1, -N-1) \<in> ((UNIV \<times> {..<-N}) :: (real\<times>real) set)" using \<open>(-N-1) < -N\<close> by simp
  show ?thesis by (rule connected_Un[OF hRTL hB]) (use h3' h4 in blast)
qed

lemma exterior_ball_connected_R2:
  fixes R :: real
  shows "connected {x :: real \<times> real. fst x ^ 2 + snd x ^ 2 > R ^ 2}"
proof (rule connectedI)
  let ?E = "{x :: real \<times> real. fst x ^ 2 + snd x ^ 2 > R ^ 2}"
  fix A B :: "(real \<times> real) set"
  assume hA: "open A" and hB: "open B" and hcov: "?E \<subseteq> A \<union> B"
      and hdisj: "A \<inter> B \<inter> ?E = {}" and hAne: "A \<inter> ?E \<noteq> {}" and hBne: "B \<inter> ?E \<noteq> {}"
  define N where "N = \<bar>R\<bar> + 1"
  have hN: "N > 0" unfolding N_def by simp
  have hN2: "N^ 2 > R^ 2" by (simp add: N_def power2_eq_square algebra_simps power2_abs)
  define SR where "SR = {N<..} \<times> (UNIV :: real set)"
  define ST where "ST = (UNIV :: real set) \<times> {N<..}"
  define SL where "SL = {..<-N} \<times> (UNIV :: real set)"
  define SB where "SB = (UNIV :: real set) \<times> {..<-N}"
  define S4 where "S4 = SR \<union> ST \<union> SL \<union> SB"
  have hSR_E: "SR \<subseteq> ?E" unfolding SR_def proof fix z :: "real\<times>real"
    assume "z \<in> {N<..} \<times> UNIV" hence "fst z > N" by auto
    hence "fst z^ 2 > N^ 2" by (intro power_strict_mono) (use hN in simp_all)
    have "snd z ^ 2 \<ge> 0" by simp
    have "fst z ^ 2 + snd z ^ 2 > R ^ 2" using \<open>fst z ^ 2 > N ^ 2\<close> \<open>snd z ^ 2 \<ge> 0\<close> hN2 by linarith
    thus "z \<in> ?E" by (rule sqnorm_memI) qed
  have hST_E: "ST \<subseteq> ?E" unfolding ST_def proof fix z :: "real\<times>real"
    assume "z \<in> UNIV \<times> {N<..}" hence "snd z > N" by auto
    hence "snd z^ 2 > N^ 2" by (intro power_strict_mono) (use hN in simp_all)
    have "fst z ^ 2 \<ge> 0" by simp
    have "fst z ^ 2 + snd z ^ 2 > R ^ 2" using \<open>snd z ^ 2 > N ^ 2\<close> \<open>fst z ^ 2 \<ge> 0\<close> hN2 by linarith
    thus "z \<in> ?E" by (rule sqnorm_memI) qed
  have hSL_E: "SL \<subseteq> ?E" unfolding SL_def proof fix z :: "real\<times>real"
    assume "z \<in> {..<-N} \<times> UNIV" hence "fst z < -N" by auto hence "(-fst z) > N" by simp
    hence "(-fst z)^ 2 > N^ 2" by (intro power_strict_mono) (use hN in simp_all)
    hence "fst z^ 2 > N^ 2" by (simp add: power2_minus)
    have "snd z ^ 2 \<ge> 0" by simp
    have "fst z ^ 2 + snd z ^ 2 > R ^ 2" using \<open>fst z ^ 2 > N ^ 2\<close> \<open>snd z ^ 2 \<ge> 0\<close> hN2 by linarith
    thus "z \<in> ?E" by (rule sqnorm_memI) qed
  have hSB_E: "SB \<subseteq> ?E" unfolding SB_def proof fix z :: "real\<times>real"
    assume "z \<in> UNIV \<times> {..<-N}" hence "snd z < -N" by auto hence "(-snd z) > N" by simp
    hence "(-snd z)^ 2 > N^ 2" by (intro power_strict_mono) (use hN in simp_all)
    hence "snd z^ 2 > N^ 2" by (simp add: power2_minus)
    have "fst z ^ 2 \<ge> 0" by simp
    have "fst z ^ 2 + snd z ^ 2 > R ^ 2" using \<open>snd z ^ 2 > N ^ 2\<close> \<open>fst z ^ 2 \<ge> 0\<close> hN2 by linarith
    thus "z \<in> ?E" by (rule sqnorm_memI) qed
  have hS4_conn: "connected S4"
  proof -
    have "S4 = {N<..} \<times> UNIV \<union> UNIV \<times> {N<..} \<union> {..<-N} \<times> UNIV \<union> UNIV \<times> {..<-N}"
      unfolding S4_def SR_def ST_def SL_def SB_def by simp
    thus ?thesis using four_strips_connected[OF hN] by simp
  qed
  have hS4_E: "S4 \<subseteq> ?E" unfolding S4_def using hSR_E hST_E hSL_E hSB_E by blast
  have hS4_AB: "A \<inter> S4 = {} \<or> B \<inter> S4 = {}"
    by (rule connectedD[OF hS4_conn hA hB]) (use hdisj hcov hS4_E in blast)+
  have h_reach: "\<And>z. z \<in> ?E \<Longrightarrow> \<exists>S. connected S \<and> z \<in> S \<and> S \<subseteq> ?E \<and> S \<inter> S4 \<noteq> {}"
  proof -
    fix z assume hz: "z \<in> ?E" hence hzn: "fst z^ 2 + snd z^ 2 > R^ 2" by blast
    \<comment> \<open>Choose target: go to (fst z, N+1) or (fst z, -N-1) depending on sign of snd z.\<close>
    define t where "t = (if snd z \<ge> 0 then max (snd z) (N + 1) else min (snd z) (-N - 1))"
    define seg where "seg = {fst z} \<times> (if snd z \<ge> 0 then {snd z..t} else {t..snd z})"
    have hseg_conn: "connected seg" unfolding seg_def t_def
      by (rule connected_Times[OF connected_sing]) (simp_all add: connected_Icc)
    have hz_seg: "z \<in> seg" unfolding seg_def t_def by (cases z) auto
    have hseg_E: "seg \<subseteq> ?E" proof fix w assume "w \<in> seg"
      hence "fst w = fst z" unfolding seg_def by force
      have "\<bar>snd w\<bar> \<ge> \<bar>snd z\<bar>" using \<open>w \<in> seg\<close> unfolding seg_def t_def by (auto simp: abs_if)
      hence "snd w^ 2 \<ge> snd z^ 2"
        using power_mono[of "\<bar>snd z\<bar>" "\<bar>snd w\<bar>" 2] by (simp add: power2_abs)
      have "fst w ^ 2 = fst z ^ 2" using \<open>fst w = fst z\<close> by simp
      have "fst w^ 2 + snd w^ 2 \<ge> fst z^ 2 + snd z^ 2"
        using \<open>fst w ^ 2 = fst z ^ 2\<close> \<open>snd w ^ 2 \<ge> snd z ^ 2\<close> by linarith
      thus "w \<in> ?E" by (intro sqnorm_memI) (use hzn in linarith) qed
    have "(fst z, t) \<in> seg" unfolding seg_def t_def by (cases z) auto
    moreover have "(fst z, t) \<in> S4" unfolding S4_def SR_def ST_def SL_def SB_def t_def by auto
    ultimately have "seg \<inter> S4 \<noteq> {}" by blast
    show "\<exists>S. connected S \<and> z \<in> S \<and> S \<subseteq> ?E \<and> S \<inter> S4 \<noteq> {}"
      using hseg_conn hz_seg hseg_E \<open>seg \<inter> S4 \<noteq> {}\<close> by blast
  qed
  show False using hS4_AB proof
    assume "B \<inter> S4 = {}" hence "S4 \<subseteq> A" using hcov hS4_E by blast
    have "?E \<subseteq> A" proof fix z assume "z \<in> ?E"
      obtain S where hS: "connected S" "z \<in> S" "S \<subseteq> ?E" "S \<inter> S4 \<noteq> {}" using h_reach[OF \<open>z \<in> ?E\<close>] by blast
      have "A \<inter> S = {} \<or> B \<inter> S = {}" by (rule connectedD[OF hS(1) hA hB]) (use hdisj hcov hS(3) in blast)+
      thus "z \<in> A" using hS(4) \<open>S4 \<subseteq> A\<close> hcov hS(2,3) by blast qed
    thus False using hBne hdisj by blast
  next
    assume "A \<inter> S4 = {}" hence "S4 \<subseteq> B" using hcov hS4_E by blast
    have "?E \<subseteq> B" proof fix z assume "z \<in> ?E"
      obtain S where hS: "connected S" "z \<in> S" "S \<subseteq> ?E" "S \<inter> S4 \<noteq> {}" using h_reach[OF \<open>z \<in> ?E\<close>] by blast
      have "A \<inter> S = {} \<or> B \<inter> S = {}" by (rule connectedD[OF hS(1) hA hB]) (use hdisj hcov hS(3) in blast)+
      thus "z \<in> B" using hS(4) \<open>S4 \<subseteq> B\<close> hcov hS(2,3) by blast qed
    thus False using hAne hdisj by blast
  qed
qed

\<comment> \<open>connected_open_delete_R3, complement_compact_connected_R2 removed (unused/false).
   connected_minus_point_via_homeo is in AlgTop.thy.\<close>

end
