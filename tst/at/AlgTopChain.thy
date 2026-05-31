theory AlgTopChain
  imports "AlgTopWedgeHelpers.AlgTopWedgeHelpers"
begin

(** Cached sorry-free content from AlgTop.thy:
    Chunk 1 (lines 4-4892): §51-§72 infrastructure
    Chunk 2 (lines 5193-8429): §71.1 chain + wrapper **)

text \<open>Existence part of universal property.\<close>
lemma free_group_hom_exists:
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "top1_is_group_on H mulH eH invgH"
      and "\<forall>s\<in>S. \<phi> s \<in> H"
  shows "\<exists>\<psi>. top1_group_hom_on G mul H mulH \<psi> \<and> (\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s)"
proof -
  have hG_grp: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG_in: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG_gen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  \<comment> \<open>Step 1: The set of word-products equals G.
     Define W = {top1\_group\_word\_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws)
                | ws. \<forall>i<length ws. fst(ws!i) \<in> S}.
     W is a subgroup of G containing \<iota>(S), hence W = \<langle>\<iota>(S)\<rangle> = G.\<close>
  let ?eval_G = "\<lambda>ws. top1_group_word_product mul e invg (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
  let ?eval_H = "\<lambda>ws. top1_group_word_product mulH eH invgH (map (\<lambda>(s,b). (\<phi> s, b)) ws)"
  let ?W = "{?eval_G ws | ws. \<forall>i<length ws. fst (ws ! i) \<in> S}"
  have hW_eq_G: "?W = G"
  proof (rule set_eqI, rule iffI)
    \<comment> \<open>W \<subseteq> G: word products are in G.\<close>
    fix g assume "g \<in> ?W"
    then obtain ws where hws: "\<forall>i<length ws. fst (ws ! i) \<in> S" and hg: "g = ?eval_G ws"
      by (by100 blast)
    have "\<forall>i<length (map (\<lambda>(s,b). (\<iota> s, b)) ws). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! i) \<in> G"
    proof (intro allI impI)
      fix j assume "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
      hence hj: "j < length ws" by (by100 simp)
      obtain s b where hwj: "ws ! j = (s, b)" by (cases "ws!j") (by100 blast)
      have "s \<in> S" using hws hj hwj by (by100 force)
      thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
        using hG_in hj hwj by simp
    qed
    thus "g \<in> G" using hg word_product_in_group[OF hG_grp] by (by100 simp)
  next
    \<comment> \<open>G \<subseteq> W: G = \<langle>\<iota>(S)\<rangle> and W is a subgroup containing \<iota>(S).\<close>
    fix g assume hg: "g \<in> G"
    \<comment> \<open>W is a subgroup of G containing \<iota>(S).\<close>
    \<comment> \<open>Helper: mapped word elements are in G.\<close>
    have hmapped_G: "\<And>ws. \<forall>i<length ws. fst (ws ! i) \<in> S \<Longrightarrow>
        \<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
    proof (intro allI impI)
      fix ws and j
      assume h: "\<forall>i<length ws. fst (ws ! i) \<in> S" and hj: "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
      hence hjw: "j < length ws" by (by100 simp)
      obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
      have "sj \<in> S" using h hjw hwj by (by100 force)
      thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G" using hG_in hjw hwj by simp
    qed
    have hW_grp: "top1_is_group_on ?W mul e invg"
    proof -
      have he: "e \<in> ?W"
        apply (rule CollectI) apply (rule exI[of _ "[]"]) by (by100 simp)
      have hcl: "\<forall>x\<in>?W. \<forall>y\<in>?W. mul x y \<in> ?W"
      proof (intro ballI)
        fix x y assume "x \<in> ?W" "y \<in> ?W"
        then obtain ws1 ws2 where h1: "\<forall>i<length ws1. fst(ws1!i) \<in> S" "x = ?eval_G ws1"
            and h2: "\<forall>i<length ws2. fst(ws2!i) \<in> S" "y = ?eval_G ws2" by (by100 blast)
        have hmap_app: "map (\<lambda>(s,b). (\<iota> s, b)) (ws1 @ ws2) =
            map (\<lambda>(s,b). (\<iota> s, b)) ws1 @ map (\<lambda>(s,b). (\<iota> s, b)) ws2" by (by100 simp)
        have "mul x y = ?eval_G (ws1 @ ws2)"
          using h1(2) h2(2) word_product_append[OF hG_grp hmapped_G[OF h1(1)] hmapped_G[OF h2(1)]]
                hmap_app by (by100 simp)
        moreover have "\<forall>i<length (ws1@ws2). fst((ws1@ws2)!i) \<in> S"
          using h1(1) h2(1) by (simp add: nth_append)
        ultimately show "mul x y \<in> ?W" by (by100 blast)
      qed
      have hinv: "\<forall>x\<in>?W. invg x \<in> ?W"
      proof (intro ballI)
        fix x assume "x \<in> ?W"
        then obtain ws where hws: "\<forall>i<length ws. fst(ws!i) \<in> S" "x = ?eval_G ws" by (by100 blast)
        let ?rws = "map (\<lambda>(s,b). (s, \<not>b)) (rev ws)"
        have hrev_map: "map (\<lambda>(s,b). (\<iota> s, b)) ?rws
            = map (\<lambda>(x,b). (x, \<not>b)) (rev (map (\<lambda>(s,b). (\<iota> s, b)) ws))"
          by (induct ws) auto
        have "invg x = ?eval_G ?rws"
          using hws(2) word_product_rev_inv[OF hG_grp hmapped_G[OF hws(1)]] hrev_map by (by100 simp)
        moreover have "\<forall>i<length ?rws. fst(?rws!i) \<in> S"
        proof (intro allI impI)
          fix i assume "i < length ?rws"
          hence hi: "i < length ws" by (by100 simp)
          have "length ws - 1 - i < length ws" using hi by (by100 simp)
          obtain si bi where "ws ! (length ws - 1 - i) = (si, bi)"
            by (cases "ws!(length ws - 1 - i)") (by100 blast)
          hence hsi_S: "si \<in> S" using hws(1) \<open>length ws - 1 - i < length ws\<close> by (by100 force)
          have hrev_i: "rev ws ! i = ws ! (length ws - 1 - i)" using rev_nth[of i ws] hi by (by100 simp)
          hence hrev_si: "rev ws ! i = (si, bi)" using \<open>ws ! (length ws - 1 - i) = (si, bi)\<close> by (by100 simp)
          have "?rws ! i = (case rev ws ! i of (s, b) \<Rightarrow> (s, \<not>b))" using hi by (by100 simp)
          hence "?rws ! i = (si, \<not>bi)" using hrev_si by (by100 simp)
          thus "fst(?rws!i) \<in> S" using hsi_S by (by100 simp)
        qed
        ultimately show "invg x \<in> ?W" by (by100 blast)
      qed
      \<comment> \<open>W \<subseteq> G for group axioms.\<close>
      have hWG: "?W \<subseteq> G"
      proof
        fix g assume "g \<in> ?W"
        then obtain ws where "g = ?eval_G ws" "\<forall>i<length ws. fst(ws!i) \<in> S" by (by100 blast)
        thus "g \<in> G" using word_product_in_group[OF hG_grp hmapped_G] by (by100 simp)
      qed
      show ?thesis unfolding top1_is_group_on_def
      proof (intro conjI)
        show "e \<in> ?W" by (rule he)
        show "\<forall>x\<in>?W. \<forall>y\<in>?W. mul x y \<in> ?W" by (rule hcl)
        show "\<forall>x\<in>?W. invg x \<in> ?W" by (rule hinv)
      next
        show "\<forall>x\<in>?W. \<forall>y\<in>?W. \<forall>z\<in>?W. mul (mul x y) z = mul x (mul y z)"
          using hWG hG_grp unfolding top1_is_group_on_def by blast
        show "\<forall>x\<in>?W. mul e x = x \<and> mul x e = x"
          using hWG hG_grp unfolding top1_is_group_on_def by blast
        show "\<forall>x\<in>?W. mul (invg x) x = e \<and> mul x (invg x) = e"
          using hWG hG_grp unfolding top1_is_group_on_def by blast
      qed
    qed
    have hW_sub: "?W \<subseteq> G"
    proof
      fix g assume "g \<in> ?W"
      then obtain ws where hws: "\<forall>i<length ws. fst (ws ! i) \<in> S" "g = ?eval_G ws" by (by100 blast)
      have "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
      proof (intro allI impI)
        fix j assume "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
        hence hj: "j < length ws" by (by100 simp)
        obtain s b where "ws ! j = (s, b)" by (cases "ws!j") (by100 blast)
        have "fst (ws ! j) \<in> S" using hws(1) hj by (by100 blast)
        thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
          using hG_in hj \<open>ws ! j = (s, b)\<close> by simp
      qed
      thus "g \<in> G" using hws(2) word_product_in_group[OF hG_grp] by (by100 simp)
    qed
    have hiotaS_W: "\<iota> ` S \<subseteq> ?W"
    proof (intro image_subsetI)
      fix s assume hs: "s \<in> S"
      have "?eval_G [(s, True)] = mul (\<iota> s) e" by (by100 simp)
      also have "\<dots> = \<iota> s" using hG_grp hG_in hs unfolding top1_is_group_on_def by (by100 blast)
      finally have "\<iota> s = ?eval_G [(s, True)]" by (by100 simp)
      moreover have "\<forall>i<length [(s, True)]. fst ([(s, True)] ! i) \<in> S"
        using hs by (by100 simp)
      ultimately show "\<iota> s \<in> ?W" by (by100 blast)
    qed
    have hW_in: "?W \<in> {K. \<iota> ` S \<subseteq> K \<and> K \<subseteq> G \<and> top1_is_group_on K mul e invg}"
      using hiotaS_W hW_sub hW_grp by (by100 blast)
    hence "top1_subgroup_generated_on G mul e invg (\<iota> ` S) \<subseteq> ?W"
      unfolding top1_subgroup_generated_on_def
      using Inter_lower[OF hW_in] by (by100 blast)
    thus "g \<in> ?W" using hg hG_gen by (by100 blast)
  qed
  \<comment> \<open>Step 2: Define \<psi> via SOME word representation.\<close>
  let ?\<psi> = "\<lambda>g. ?eval_H (SOME ws. (\<forall>i<length ws. fst (ws ! i) \<in> S) \<and> ?eval_G ws = g)"
  \<comment> \<open>Helper: mapped word elements are in G.\<close>
  have hmapped_G: "\<And>ws. \<forall>i<length ws. fst (ws ! i) \<in> S \<Longrightarrow>
      \<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G"
  proof (intro allI impI)
    fix ws and j
    assume h: "\<forall>i<length ws. fst (ws ! i) \<in> S" and hj: "j < length (map (\<lambda>(s,b). (\<iota> s, b)) ws)"
    hence hjw: "j < length ws" by (by100 simp)
    obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
    have "sj \<in> S" using h hjw hwj by (by100 force)
    thus "fst (map (\<lambda>(s,b). (\<iota> s, b)) ws ! j) \<in> G" using hG_in hjw hwj by simp
  qed
  \<comment> \<open>Step 3: \<psi> is well-defined: any two word representations give the same H-value.\<close>
  \<comment> \<open>Helper: flip-rev preserves S-generators and commutes with map.\<close>
  have hfliprev_S: "\<And>ws. \<forall>i<length ws. fst (ws ! i) \<in> S \<Longrightarrow>
      \<forall>i<length (map (\<lambda>(s,b). (s, \<not>b)) (rev ws)). fst (map (\<lambda>(s,b). (s, \<not>b)) (rev ws) ! i) \<in> S"
  proof (intro allI impI)
    fix ws and i
    assume h: "\<forall>i<length ws. fst (ws ! i) \<in> S" and hi: "i < length (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))"
    hence hiw: "i < length ws" by (by100 simp)
    have "length ws - 1 - i < length ws" using hiw by (by100 simp)
    obtain s b where hsb: "ws ! (length ws - 1 - i) = (s, b)" by (cases "ws!(length ws-1-i)") (by100 blast)
    have "s \<in> S" using h \<open>length ws - 1 - i < length ws\<close> hsb by (by100 force)
    have hrev: "rev ws ! i = (s, b)" using rev_nth[of i ws] hiw hsb by (by100 simp)
    have "map (\<lambda>(s,b). (s, \<not>b)) (rev ws) ! i = (s, \<not>b)" using hiw hrev by simp
    thus "fst (map (\<lambda>(s,b). (s, \<not>b)) (rev ws) ! i) \<in> S" using \<open>s \<in> S\<close> by (by100 simp)
  qed
  have hmap_fliprev: "\<And>ws. map (\<lambda>(s,b). (\<iota> s, b)) (map (\<lambda>(s,b). (s, \<not>b)) (rev ws))
      = map (\<lambda>(x,b). (x, \<not>b)) (rev (map (\<lambda>(s,b). (\<iota> s, b)) ws))"
    by (induct_tac ws) auto
  have hwd: "\<And>ws1 ws2. \<forall>i<length ws1. fst (ws1 ! i) \<in> S \<Longrightarrow>
      \<forall>i<length ws2. fst (ws2 ! i) \<in> S \<Longrightarrow>
      ?eval_G ws1 = ?eval_G ws2 \<Longrightarrow>
      ?eval_H ws1 = ?eval_H ws2"
  proof (goal_cases)
    case (1 ws1 ws2)
    let ?fr2 = "map (\<lambda>(s,b). (s, \<not>b)) (rev ws2)"
    let ?ws3 = "ws1 @ ?fr2"
    \<comment> \<open>ws3 generators from S.\<close>
    have hfr2_S: "\<forall>i<length ?fr2. fst (?fr2 ! i) \<in> S" by (rule hfliprev_S[OF 1(2)])
    have hws3_S: "\<forall>i<length ?ws3. fst (?ws3 ! i) \<in> S"
      using 1(1) hfr2_S by (simp add: nth_append)
    \<comment> \<open>eval\_G(ws3) = e.\<close>
    have hmG1: "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws1). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws1 ! j) \<in> G"
      by (rule hmapped_G[OF 1(1)])
    have hmGr: "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ?fr2). fst (map (\<lambda>(s,b). (\<iota> s, b)) ?fr2 ! j) \<in> G"
      by (rule hmapped_G[OF hfr2_S])
    have hmG2: "\<forall>j<length (map (\<lambda>(s,b). (\<iota> s, b)) ws2). fst (map (\<lambda>(s,b). (\<iota> s, b)) ws2 ! j) \<in> G"
      by (rule hmapped_G[OF 1(2)])
    have happ_map: "map (\<lambda>(s,b). (\<iota> s, b)) ?ws3 =
        map (\<lambda>(s,b). (\<iota> s, b)) ws1 @ map (\<lambda>(s,b). (\<iota> s, b)) ?fr2" by (by100 simp)
    have heval_G_split: "?eval_G ?ws3 = mul (?eval_G ws1) (?eval_G ?fr2)"
      using word_product_append[OF hG_grp hmG1 hmGr] happ_map by (by100 simp)
    have heval_G_rev: "?eval_G ?fr2 = invg (?eval_G ws2)"
      using word_product_rev_inv[OF hG_grp hmG2] hmap_fliprev by (by100 simp)
    have heval_G_e: "?eval_G ?ws3 = e"
    proof -
      have "?eval_G ?ws3 = mul (?eval_G ws1) (invg (?eval_G ws2))"
        using heval_G_split heval_G_rev by (by100 simp)
      also have "\<dots> = mul (?eval_G ws1) (invg (?eval_G ws1))" using 1(3) by (by100 simp)
      also have "\<dots> = e"
      proof -
        have "?eval_G ws1 \<in> G" using word_product_in_group[OF hG_grp hmG1] by (by100 simp)
        thus ?thesis using hG_grp unfolding top1_is_group_on_def by (by100 blast)
      qed
      finally show ?thesis .
    qed
    \<comment> \<open>By word\_kernel: eval\_H(ws3) = eH.\<close>
    have heval_H_e: "?eval_H ?ws3 = eH"
      by (rule free_group_word_kernel[OF assms(1) assms(2) assms(3) hws3_S heval_G_e])
    \<comment> \<open>Decompose eval\_H similarly.\<close>
    have hmH_mapped: "\<And>ws. \<forall>i<length ws. fst(ws!i) \<in> S \<Longrightarrow>
        \<forall>j<length (map (\<lambda>(s,b). (\<phi> s, b)) ws). fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H"
    proof (intro allI impI)
      fix ws and j
      assume h: "\<forall>i<length ws. fst(ws!i) \<in> S" and hj: "j < length (map (\<lambda>(s,b). (\<phi> s, b)) ws)"
      hence hjw: "j < length ws" by (by100 simp)
      obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
      have "sj \<in> S" using h hjw hwj by (by100 force)
      hence "\<phi> sj \<in> H" using assms(3) by (by100 blast)
      thus "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H" using hjw hwj by simp
    qed
    have hmap_fliprev_H: "map (\<lambda>(s,b). (\<phi> s, b)) ?fr2
        = map (\<lambda>(x,b). (x, \<not>b)) (rev (map (\<lambda>(s,b). (\<phi> s, b)) ws2))"
      by (induct ws2) auto
    have heval_H_split: "?eval_H ?ws3 = mulH (?eval_H ws1) (?eval_H ?fr2)"
    proof -
      have "map (\<lambda>(s,b). (\<phi> s, b)) ?ws3 =
          map (\<lambda>(s,b). (\<phi> s, b)) ws1 @ map (\<lambda>(s,b). (\<phi> s, b)) ?fr2" by (by100 simp)
      thus ?thesis
        using word_product_append[OF assms(2) hmH_mapped[OF 1(1)] hmH_mapped[OF hfr2_S]] by (by100 simp)
    qed
    have heval_H_rev: "?eval_H ?fr2 = invgH (?eval_H ws2)"
      using word_product_rev_inv[OF assms(2) hmH_mapped[OF 1(2)]] hmap_fliprev_H by (by100 simp)
    \<comment> \<open>Combine: mulH (eval\_H ws1) (invgH (eval\_H ws2)) = eH.\<close>
    have "mulH (?eval_H ws1) (invgH (?eval_H ws2)) = eH"
      using heval_H_e heval_H_split heval_H_rev by (by100 simp)
    \<comment> \<open>Right-multiply by eval\_H ws2.\<close>
    hence "mulH (mulH (?eval_H ws1) (invgH (?eval_H ws2))) (?eval_H ws2) = mulH eH (?eval_H ws2)"
      by (by100 simp)
    hence "?eval_H ws1 = ?eval_H ws2"
    proof -
      have hH1: "?eval_H ws1 \<in> H" using word_product_in_group[OF assms(2) hmH_mapped[OF 1(1)]] by (by100 simp)
      have hH2: "?eval_H ws2 \<in> H" using word_product_in_group[OF assms(2) hmH_mapped[OF 1(2)]] by (by100 simp)
      have hiH2: "invgH (?eval_H ws2) \<in> H" using assms(2) hH2 unfolding top1_is_group_on_def by (by100 blast)
      \<comment> \<open>a \<cdot> b\<inverse> = eH \<Longrightarrow> a = b.\<close>
      \<comment> \<open>a \<cdot> b\<inverse> = eH implies a \<cdot> b\<inverse> \<cdot> b = eH \<cdot> b = b, and a \<cdot> (b\<inverse> \<cdot> b) = a \<cdot> eH = a. So a = b.\<close>
      have hcancel: "mulH (invgH (?eval_H ws2)) (?eval_H ws2) = eH"
        using assms(2) hH2 unfolding top1_is_group_on_def by (by100 blast)
      have hid_r: "mulH (?eval_H ws1) eH = ?eval_H ws1"
        using assms(2) hH1 unfolding top1_is_group_on_def by (by100 blast)
      have "?eval_H ws1 = mulH (?eval_H ws1) eH"
        using hid_r by (by100 simp)
      also have "\<dots> = mulH (?eval_H ws1) (mulH (invgH (?eval_H ws2)) (?eval_H ws2))"
        using hcancel by (by100 simp)
      also have "\<dots> = mulH (mulH (?eval_H ws1) (invgH (?eval_H ws2))) (?eval_H ws2)"
      proof -
        have "mulH (mulH (?eval_H ws1) (invgH (?eval_H ws2))) (?eval_H ws2)
            = mulH (?eval_H ws1) (mulH (invgH (?eval_H ws2)) (?eval_H ws2))"
          using assms(2) hH1 hiH2 hH2 unfolding top1_is_group_on_def by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      also have "\<dots> = mulH eH (?eval_H ws2)"
        using \<open>mulH (?eval_H ws1) (invgH (?eval_H ws2)) = eH\<close> by (by100 simp)
      also have "\<dots> = ?eval_H ws2"
        using assms(2) hH2 unfolding top1_is_group_on_def by (by100 blast)
      finally show ?thesis .
    qed
    thus ?case .
  qed
  \<comment> \<open>Helper: mapped word elements are in H.\<close>
  have hmH_mapped: "\<And>ws. \<forall>i<length ws. fst(ws!i) \<in> S \<Longrightarrow>
      \<forall>j<length (map (\<lambda>(s,b). (\<phi> s, b)) ws). fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H"
  proof (intro allI impI)
    fix ws and j
    assume h: "\<forall>i<length ws. fst(ws!i) \<in> S" and hj: "j < length (map (\<lambda>(s,b). (\<phi> s, b)) ws)"
    hence hjw: "j < length ws" by (by100 simp)
    obtain sj bj where hwj: "ws ! j = (sj, bj)" by (cases "ws!j") (by100 blast)
    have "sj \<in> S" using h hjw hwj by (by100 force)
    hence "\<phi> sj \<in> H" using assms(3) by (by100 blast)
    thus "fst (map (\<lambda>(s,b). (\<phi> s, b)) ws ! j) \<in> H" using hjw hwj by simp
  qed
  \<comment> \<open>Helper: for g \<in> G, SOME picks a valid word, and \<psi>(g) = eval\_H of any valid word.\<close>
  have hpsi_wd: "\<And>g ws. g \<in> G \<Longrightarrow> (\<forall>i<length ws. fst (ws ! i) \<in> S) \<Longrightarrow> ?eval_G ws = g \<Longrightarrow>
      ?\<psi> g = ?eval_H ws"
  proof -
    fix g ws
    assume hg: "g \<in> G" and hws: "\<forall>i<length ws. fst (ws ! i) \<in> S" and heval: "?eval_G ws = g"
    \<comment> \<open>SOME picks some word ws' with eval\_G(ws') = g.\<close>
    have "\<exists>ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g"
      using hws heval by (by100 blast)
    hence hsome: "(\<forall>i<length (SOME ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g).
        fst ((SOME ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g) ! i) \<in> S)
      \<and> ?eval_G (SOME ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g) = g"
      by (rule someI_ex)
    \<comment> \<open>By well-definedness, eval\_H of SOME word = eval\_H of ws.\<close>
    let ?ws' = "SOME ws'. (\<forall>i<length ws'. fst (ws' ! i) \<in> S) \<and> ?eval_G ws' = g"
    have hsome1: "\<forall>i<length ?ws'. fst (?ws' ! i) \<in> S" using hsome by (by100 blast)
    have hsome2: "?eval_G ?ws' = g" using hsome by (by100 blast)
    have "?eval_G ?ws' = ?eval_G ws" using hsome2 heval by (by100 simp)
    thus "?\<psi> g = ?eval_H ws" by (rule hwd[OF hsome1 hws])
  qed
  \<comment> \<open>Step 4: \<psi> is a homomorphism.\<close>
  have hhom: "top1_group_hom_on G mul H mulH ?\<psi>"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    \<comment> \<open>\<psi>(g) \<in> H for g \<in> G.\<close>
    fix g assume hg: "g \<in> G"
    have "g \<in> ?W" using hg hW_eq_G by (by100 simp)
    then obtain ws where hws: "\<forall>i<length ws. fst (ws ! i) \<in> S" "?eval_G ws = g"
      by (by100 blast)
    have "?\<psi> g = ?eval_H ws" by (rule hpsi_wd[OF hg hws(1) hws(2)])
    also have "\<dots> \<in> H" by (rule word_product_in_group[OF assms(2) hmH_mapped[OF hws(1)]])
    finally show "?\<psi> g \<in> H" .
  next
    \<comment> \<open>\<psi>(g1 \<cdot> g2) = mulH(\<psi> g1)(\<psi> g2).\<close>
    fix g1 g2 assume hg1: "g1 \<in> G" and hg2: "g2 \<in> G"
    \<comment> \<open>Get word representations.\<close>
    have "g1 \<in> ?W" using hg1 hW_eq_G by (by100 simp)
    then obtain ws1 where hws1: "\<forall>i<length ws1. fst (ws1 ! i) \<in> S" "?eval_G ws1 = g1"
      by (by100 blast)
    have "g2 \<in> ?W" using hg2 hW_eq_G by (by100 simp)
    then obtain ws2 where hws2: "\<forall>i<length ws2. fst (ws2 ! i) \<in> S" "?eval_G ws2 = g2"
      by (by100 blast)
    \<comment> \<open>ws1 @ ws2 is a word for mul g1 g2.\<close>
    have happ_S: "\<forall>i<length (ws1 @ ws2). fst ((ws1 @ ws2) ! i) \<in> S"
      using hws1(1) hws2(1) by (simp add: nth_append)
    have hmap_app: "map (\<lambda>(s,b). (\<iota> s, b)) (ws1 @ ws2) =
        map (\<lambda>(s,b). (\<iota> s, b)) ws1 @ map (\<lambda>(s,b). (\<iota> s, b)) ws2" by (by100 simp)
    have heval_app: "?eval_G (ws1 @ ws2) = mul g1 g2"
      using word_product_append[OF hG_grp hmapped_G[OF hws1(1)] hmapped_G[OF hws2(1)]]
            hmap_app hws1(2) hws2(2) by (by100 simp)
    have hmul_G: "mul g1 g2 \<in> G"
      using hG_grp hg1 hg2 unfolding top1_is_group_on_def by (by100 blast)
    \<comment> \<open>\<psi>(mul g1 g2) = eval\_H(ws1 @ ws2) by well-definedness.\<close>
    have "?\<psi> (mul g1 g2) = ?eval_H (ws1 @ ws2)"
      by (rule hpsi_wd[OF hmul_G happ_S heval_app])
    \<comment> \<open>eval\_H(ws1 @ ws2) = mulH(eval\_H ws1)(eval\_H ws2).\<close>
    also have "\<dots> = mulH (?eval_H ws1) (?eval_H ws2)"
    proof -
      have "map (\<lambda>(s,b). (\<phi> s, b)) (ws1 @ ws2) =
          map (\<lambda>(s,b). (\<phi> s, b)) ws1 @ map (\<lambda>(s,b). (\<phi> s, b)) ws2" by (by100 simp)
      thus ?thesis
        using word_product_append[OF assms(2) hmH_mapped[OF hws1(1)] hmH_mapped[OF hws2(1)]]
        by (by100 simp)
    qed
    \<comment> \<open>eval\_H(wsi) = \<psi>(gi) by well-definedness.\<close>
    also have "?eval_H ws1 = ?\<psi> g1" using hpsi_wd[OF hg1 hws1(1) hws1(2)] by (by100 simp)
    also have "?eval_H ws2 = ?\<psi> g2" using hpsi_wd[OF hg2 hws2(1) hws2(2)] by (by100 simp)
    finally show "?\<psi> (mul g1 g2) = mulH (?\<psi> g1) (?\<psi> g2)" by (by100 simp)
  qed
  \<comment> \<open>Step 5: \<psi>(\<iota>(s)) = \<phi>(s).\<close>
  have hext: "\<forall>s\<in>S. ?\<psi> (\<iota> s) = \<phi> s"
  proof (intro ballI)
    fix s assume hs: "s \<in> S"
    \<comment> \<open>The word [(s, True)] evaluates to \<iota>(s) in G.\<close>
    have hws_S: "\<forall>i<length [(s, True)]. fst ([(s, True)] ! i) \<in> S"
      using hs by (by100 simp)
    have heval_s: "?eval_G [(s, True)] = \<iota> s"
    proof -
      have "?eval_G [(s, True)] = mul (\<iota> s) e" by (by100 simp)
      also have "\<dots> = \<iota> s"
        using hG_grp hG_in hs unfolding top1_is_group_on_def by (by100 blast)
      finally show ?thesis .
    qed
    have hiota_G: "\<iota> s \<in> G" using hG_in hs by (by100 blast)
    \<comment> \<open>By well-definedness: \<psi>(\<iota> s) = eval\_H([(s, True)]).\<close>
    have "?\<psi> (\<iota> s) = ?eval_H [(s, True)]"
      by (rule hpsi_wd[OF hiota_G hws_S heval_s])
    \<comment> \<open>eval\_H([(s, True)]) = \<phi>(s).\<close>
    also have "\<dots> = mulH (\<phi> s) eH" by (by100 simp)
    also have "\<dots> = \<phi> s"
      using assms(2,3) hs unfolding top1_is_group_on_def by (by100 blast)
    finally show "?\<psi> (\<iota> s) = \<phi> s" .
  qed
  show ?thesis using hhom hext by (by100 blast)
qed

lemma free_group_universal_property:
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "top1_is_group_on H mulH eH invgH"
      and "\<forall>s\<in>S. \<phi> s \<in> H"
  shows "\<exists>\<psi>. top1_group_hom_on G mul H mulH \<psi> \<and> (\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s)
      \<and> (\<forall>\<psi>'. top1_group_hom_on G mul H mulH \<psi>' \<and> (\<forall>s\<in>S. \<psi>' (\<iota> s) = \<phi> s)
          \<longrightarrow> (\<forall>g\<in>G. \<psi>' g = \<psi> g))"
proof -
  have hG: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hgen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hS: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  obtain \<psi> where h\<psi>: "top1_group_hom_on G mul H mulH \<psi>"
      and h\<psi>_ext: "\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s"
    using free_group_hom_exists[OF assms] by (by100 blast)
  have huniq: "\<forall>\<psi>'. top1_group_hom_on G mul H mulH \<psi>' \<and> (\<forall>s\<in>S. \<psi>' (\<iota> s) = \<phi> s)
      \<longrightarrow> (\<forall>g\<in>G. \<psi>' g = \<psi> g)"
  proof (intro allI impI)
    fix \<psi>' assume h': "top1_group_hom_on G mul H mulH \<psi>' \<and> (\<forall>s\<in>S. \<psi>' (\<iota> s) = \<phi> s)"
    have h'_hom: "top1_group_hom_on G mul H mulH \<psi>'" using h' by (by100 blast)
    have "\<forall>s\<in>S. \<psi>' (\<iota> s) = \<psi> (\<iota> s)" using h' h\<psi>_ext by (by100 simp)
    thus "\<forall>g\<in>G. \<psi>' g = \<psi> g"
      by (rule free_group_hom_unique[OF hG assms(2) hgen hS h'_hom h\<psi>])
  qed
  show ?thesis using h\<psi> h\<psi>_ext huniq by (by100 blast)
qed

text \<open>Corollary: the exponent sum homomorphism. For each generator s0,
  there is a homomorphism \<epsilon>_{s0}: G \<rightarrow> (Z, +) counting the s0-exponent.\<close>
lemma free_group_exponent_sum:
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "s0 \<in> S"
  shows "\<exists>\<epsilon>. top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>
           \<and> \<epsilon> (\<iota> s0) = 1
           \<and> (\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<epsilon> (\<iota> s) = 0)"
proof -
  let ?\<phi> = "\<lambda>s. if s = s0 then (1::int) else (0::int)"
  have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
    unfolding top1_is_group_on_def by (by100 auto)
  have hphi_in: "\<forall>s\<in>S. ?\<phi> s \<in> (UNIV::int set)" by (by100 blast)
  from free_group_hom_exists[OF assms(1) hZ_grp hphi_in]
  obtain \<psi> where h\<psi>: "top1_group_hom_on G mul (UNIV::int set) (+) \<psi>"
      and h\<psi>_ext: "\<forall>s\<in>S. \<psi> (\<iota> s) = ?\<phi> s"
    by (by100 blast)
  have "\<psi> (\<iota> s0) = 1" using h\<psi>_ext assms(2) by (by100 simp)
  moreover have "\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<psi> (\<iota> s) = 0" using h\<psi>_ext by (by100 auto)
  ultimately show ?thesis using h\<psi> by (by100 blast)
qed

text \<open>Commutator subgroup elements have zero exponent sum for all generators.\<close>
lemma commutator_zero_exponent:
  assumes "top1_is_group_on G mul e invg"
      and "top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>"
  shows "\<forall>g\<in>top1_commutator_subgroup_on G mul e invg. \<epsilon> g = 0"
proof (intro ballI)
  fix g assume hg: "g \<in> top1_commutator_subgroup_on G mul e invg"
  have hZ_abel: "top1_is_abelian_group_on (UNIV::int set) (+) (0::int) uminus"
    unfolding top1_is_abelian_group_on_def top1_is_group_on_def by (by100 auto)
  have hcomm_ker: "top1_commutator_subgroup_on G mul e invg
      \<subseteq> top1_group_kernel_on G (0::int) \<epsilon>"
    by (rule Lemma_69_3_commutator_in_kernel[OF assms(1) hZ_abel assms(2)])
  hence "g \<in> top1_group_kernel_on G (0::int) \<epsilon>" using hg by (by100 blast)
  thus "\<epsilon> g = 0" unfolding top1_group_kernel_on_def by (by100 blast)
qed

lemma group_pow_in_group:
  assumes "top1_is_group_on G mul e invg" and "x \<in> G"
  shows "top1_group_pow mul e x n \<in> G"
proof (induction n)
  case 0 thus ?case using assms(1) unfolding top1_is_group_on_def by (by100 simp)
next
  case (Suc n)
  have "mul x (top1_group_pow mul e x n) \<in> G"
    using assms Suc.IH unfolding top1_is_group_on_def by (by100 blast)
  thus ?case by (by100 simp)
qed

text \<open>Integer group\_pow: iterated addition = multiplication.\<close>
lemma int_group_pow: "top1_group_pow (+) (0::int) k n = int n * k"
proof (induction n)
  case 0 show ?case by (by100 simp)
next
  case (Suc n)
  have "top1_group_pow (+) (0::int) k (Suc n) = k + top1_group_pow (+) (0::int) k n"
    by (by100 simp)
  also have "\<dots> = k + int n * k" using Suc.IH by (by100 simp)
  also have "\<dots> = (1 + int n) * k" by (by100 algebra)
  also have "\<dots> = int (Suc n) * k" by (by100 simp)
  finally show ?case .
qed

text \<open>Homomorphism distributes over group\_pow.\<close>
lemma hom_group_pow:
  assumes hG: "top1_is_group_on G mul e invg"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hhom: "top1_group_hom_on G mul H mulH f"
      and hx: "x \<in> G"
  shows "f (top1_group_pow mul e x n) = top1_group_pow mulH eH (f x) n"
proof (induction n)
  case 0
  have "f (top1_group_pow mul e x 0) = f e" by (by100 simp)
  also have "\<dots> = eH" by (rule hom_preserves_id[OF hG hH hhom])
  finally show ?case by (by100 simp)
next
  case (Suc n)
  have hpow_G: "top1_group_pow mul e x n \<in> G" by (rule group_pow_in_group[OF hG hx])
  have "f (top1_group_pow mul e x (Suc n)) = f (mul x (top1_group_pow mul e x n))"
    by (by100 simp)
  also have "\<dots> = mulH (f x) (f (top1_group_pow mul e x n))"
    using hhom hx hpow_G unfolding top1_group_hom_on_def by (by100 blast)
  also have "\<dots> = mulH (f x) (top1_group_pow mulH eH (f x) n)"
    using Suc.IH by (by100 simp)
  finally show ?case by (by100 simp)
qed

text \<open>Homomorphism distributes over foldr mul.\<close>
lemma hom_foldr_mul:
  assumes hG: "top1_is_group_on G mul e invg"
      and hH: "top1_is_group_on H mulH eH invgH"
      and hhom: "top1_group_hom_on G mul H mulH f"
      and hxs: "\<forall>i<length xs. xs!i \<in> G"
  shows "f (foldr mul xs e) = foldr mulH (map f xs) eH"
  using hxs
proof (induction xs)
  case Nil show ?case using hom_preserves_id[OF hG hH hhom] by (by100 simp)
next
  case (Cons a xs')
  have ha: "a \<in> G" using Cons.prems by (by100 force)
  have hxs': "\<forall>i<length xs'. xs'!i \<in> G" using Cons.prems by (by100 force)
  have hprod: "foldr mul xs' e \<in> G"
    by (rule foldr_mul_closed[OF hG hxs'])
  have "f (foldr mul (a # xs') e) = f (mul a (foldr mul xs' e))" by (by100 simp)
  also have "\<dots> = mulH (f a) (f (foldr mul xs' e))"
    using hhom ha hprod unfolding top1_group_hom_on_def by (by100 blast)
  also have "\<dots> = mulH (f a) (foldr mulH (map f xs') eH)"
    using Cons.IH[OF hxs'] by (by100 simp)
  finally show ?case by (by100 simp)
qed

text \<open>The quotient map G \<rightarrow> G/[G,G] is injective on generators of a free group.
  Extracted from Theorem 69.4 proof for reuse.\<close>
lemma abelianization_injective_on_generators:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g" and S :: "'s set"
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
  shows "inj_on (\<lambda>s. top1_group_coset_on G mul
      (top1_commutator_subgroup_on G mul e invg) (\<iota> s)) S"
proof -
  have hG: "top1_is_group_on G mul e invg"
    using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hgen_in_G: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  let ?\<phi> = "\<lambda>g. top1_group_coset_on G mul ?N g"
  show ?thesis
  proof (rule inj_onI)
    fix s1 s2 assume hs1: "s1 \<in> S" and hs2: "s2 \<in> S" and heq: "?\<phi> (\<iota> s1) = ?\<phi> (\<iota> s2)"
    show "s1 = s2"
    proof (rule ccontr)
      assume hne: "s1 \<noteq> s2"
      obtain \<epsilon> where heps_hom: "top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>"
          and heps_s1: "\<epsilon> (\<iota> s1) = 1"
          and heps_other: "\<forall>s\<in>S. s \<noteq> s1 \<longrightarrow> \<epsilon> (\<iota> s) = 0"
        using free_group_exponent_sum[OF assms hs1] by (by100 blast)
      have h_comm_ker: "\<forall>g\<in>?N. \<epsilon> g = 0"
        by (rule commutator_zero_exponent[OF hG heps_hom])
      have hs1G: "\<iota> s1 \<in> G" using hgen_in_G hs1 by (by100 blast)
      have hs2G: "\<iota> s2 \<in> G" using hgen_in_G hs2 by (by100 blast)
      \<comment> \<open>Coset equality \<Rightarrow> \<iota>(s1)\<cdot>invg(\<iota>(s2)) \<in> [G,G].\<close>
      have hprod_N: "mul (\<iota> s1) (invg (\<iota> s2)) \<in> ?N"
      proof -
        have hN_normal: "top1_normal_subgroup_on G mul e invg ?N"
          by (rule commutator_subgroup_is_normal[OF hG])
        have heq_sym: "?\<phi> (\<iota> s2) = ?\<phi> (\<iota> s1)" using heq by (by100 simp)
        have "mul (invg (\<iota> s2)) (\<iota> s1) \<in> ?N"
          using normal_coset_eq[OF hG hN_normal hs2G hs1G] heq_sym by (by100 blast)
        have hinvs2: "invg (\<iota> s2) \<in> G" using hG hs2G unfolding top1_is_group_on_def by (by100 blast)
        have hconj0: "mul (mul (\<iota> s1) (mul (invg (\<iota> s2)) (\<iota> s1))) (invg (\<iota> s1)) \<in> ?N"
          using hN_normal hs1G \<open>mul (invg (\<iota> s2)) (\<iota> s1) \<in> ?N\<close>
          unfolding top1_normal_subgroup_on_def by (by100 blast)
        have "mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1)) = invg (\<iota> s2)"
        proof -
          have "mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1))
              = mul (invg (\<iota> s2)) (mul (\<iota> s1) (invg (\<iota> s1)))"
            using hG hinvs2 hs1G unfolding top1_is_group_on_def by (by100 blast)
          also have "mul (\<iota> s1) (invg (\<iota> s1)) = e"
            using hG hs1G unfolding top1_is_group_on_def by (by100 blast)
          also have "mul (invg (\<iota> s2)) e = invg (\<iota> s2)"
            using hG hinvs2 unfolding top1_is_group_on_def by (by100 blast)
          finally show ?thesis .
        qed
        have hprod_in_G: "mul (invg (\<iota> s2)) (\<iota> s1) \<in> G"
          using hG hinvs2 hs1G unfolding top1_is_group_on_def by (by100 blast)
        have hinvs1: "invg (\<iota> s1) \<in> G" using hG hs1G unfolding top1_is_group_on_def by (by100 blast)
        have "mul (mul (\<iota> s1) (mul (invg (\<iota> s2)) (\<iota> s1))) (invg (\<iota> s1))
            = mul (\<iota> s1) (mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1)))"
          using hG hs1G hprod_in_G hinvs1 unfolding top1_is_group_on_def by (by100 blast)
        hence "mul (\<iota> s1) (mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1))) \<in> ?N"
          using hconj0 by (by100 simp)
        hence "mul (\<iota> s1) (invg (\<iota> s2)) \<in> ?N"
          using \<open>mul (mul (invg (\<iota> s2)) (\<iota> s1)) (invg (\<iota> s1)) = invg (\<iota> s2)\<close> by (by100 simp)
        thus ?thesis .
      qed
      \<comment> \<open>\<epsilon>-value contradiction.\<close>
      have heps_zero: "\<epsilon> (mul (\<iota> s1) (invg (\<iota> s2))) = 0" using h_comm_ker hprod_N by (by100 blast)
      have hinvG_s2: "invg (\<iota> s2) \<in> G"
        using hG hs2G unfolding top1_is_group_on_def by (by100 blast)
      have "\<epsilon> (mul (\<iota> s1) (invg (\<iota> s2))) = \<epsilon> (\<iota> s1) + \<epsilon> (invg (\<iota> s2))"
        using heps_hom hs1G hinvG_s2 unfolding top1_group_hom_on_def by (by100 blast)
      moreover have "\<epsilon> (invg (\<iota> s2)) = - \<epsilon> (\<iota> s2)"
      proof -
        have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
          unfolding top1_is_group_on_def by (by100 auto)
        show ?thesis by (rule hom_preserves_inv[OF hG hZ_grp heps_hom hs2G])
      qed
      moreover have "\<epsilon> (\<iota> s2) = 0" using heps_other hs2 hne[symmetric] by (by100 blast)
      ultimately show False using heps_s1 heps_zero by (by100 simp)
    qed
  qed
qed

text \<open>Independence of generators in the abelianization.
  Extracted from Theorem 69.4 proof for reuse.\<close>
lemma abelianization_independence_on_generators:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g" and S :: "'s set"
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "finite {s\<in>S. c s \<noteq> 0}" and "\<exists>s\<in>S. c s \<noteq> 0"
  shows "foldr (top1_quotient_group_mul_on mul)
      (map (\<lambda>s.
          if c s \<ge> 0 then top1_group_pow (top1_quotient_group_mul_on mul)
              (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) e)
              (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) (\<iota> s))
              (nat (c s))
          else top1_group_pow (top1_quotient_group_mul_on mul)
              (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) e)
              ((\<lambda>C. top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg)
                 (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul
                    (top1_commutator_subgroup_on G mul e invg) g)))
               (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) (\<iota> s)))
              (nat (- c s)))
        (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs))
      (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) e)
    \<noteq> top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) e"
proof -
  have hG: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hgen_in_G: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  let ?mulH = "top1_quotient_group_mul_on mul"
  let ?eH = "top1_group_coset_on G mul ?N e"
  let ?invgH = "\<lambda>C. top1_group_coset_on G mul ?N (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul ?N g))"
  let ?\<phi> = "\<lambda>g. top1_group_coset_on G mul ?N g"
  let ?\<iota>H = "\<lambda>s. ?\<phi> (\<iota> s)"
  have h_abel: "top1_is_abelianization_of
      (top1_quotient_group_carrier_on G mul ?N) ?mulH ?eH ?invgH G mul e invg ?\<phi>"
    by (rule abelianization_concrete[OF hG])
  have hH_abel: "top1_is_abelian_group_on
      (top1_quotient_group_carrier_on G mul ?N) ?mulH ?eH ?invgH"
    using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  have hphi_hom: "top1_group_hom_on G mul (top1_quotient_group_carrier_on G mul ?N) ?mulH ?\<phi>"
    using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  \<comment> \<open>The proof follows the same structure as Theorem 69.4's hH\_indep.
     For the given nonzero c with support s0, use the exponent sum \<epsilon>
     to show the G-level product has \<epsilon>-value c(s0) \<noteq> 0,
     contradicting membership in [G,G].\<close>
  from assms(3) obtain s0 where hs0: "s0 \<in> S" "c s0 \<noteq> 0" by (by100 blast)
  obtain \<epsilon> where heps: "top1_group_hom_on G mul (UNIV::int set) (+) \<epsilon>"
      and heps_s0: "\<epsilon> (\<iota> s0) = 1"
      and heps_other: "\<forall>s\<in>S. s \<noteq> s0 \<longrightarrow> \<epsilon> (\<iota> s) = 0"
    using free_group_exponent_sum[OF assms(1) hs0(1)] by (by100 blast)
  have hcomm_ker: "\<forall>g\<in>?N. \<epsilon> g = 0"
    by (rule commutator_zero_exponent[OF hG heps])
  let ?xs = "SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs"
  let ?gp = "foldr mul (map (\<lambda>s.
        if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
        else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
      ?xs) e"
  \<comment> \<open>\<epsilon>(gp) = c(s0) (proved in Theorem 69.4).\<close>
  have heps_gp: "\<epsilon> ?gp = c s0"
  proof -
    have hZ: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
      unfolding top1_is_group_on_def by (by100 auto)
    \<comment> \<open>Step 1: \<epsilon> of each term = c(s)\<cdot>\<epsilon>(\<iota>(s)).\<close>
    have heps_term: "\<And>s. s \<in> S \<Longrightarrow>
        \<epsilon> (if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))) = c s * \<epsilon> (\<iota> s)"
    proof -
      fix s assume hs: "s \<in> S"
      have h\<iota>s: "\<iota> s \<in> G" using hgen_in_G hs by (by100 blast)
      have hinvs: "invg (\<iota> s) \<in> G" using hG h\<iota>s unfolding top1_is_group_on_def by (by100 blast)
      show "\<epsilon> (if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
          else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))) = c s * \<epsilon> (\<iota> s)"
      proof (cases "c s \<ge> 0")
        case True
        have "\<epsilon> (top1_group_pow mul e (\<iota> s) (nat (c s)))
            = top1_group_pow (+) (0::int) (\<epsilon> (\<iota> s)) (nat (c s))"
          by (rule hom_group_pow[OF hG hZ heps h\<iota>s])
        also have "\<dots> = int (nat (c s)) * \<epsilon> (\<iota> s)" by (rule int_group_pow)
        also have "int (nat (c s)) = c s" using True by (by100 simp)
        finally show ?thesis using True by (by100 simp)
      next
        case False
        have "\<epsilon> (top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
            = top1_group_pow (+) (0::int) (\<epsilon> (invg (\<iota> s))) (nat (- c s))"
          by (rule hom_group_pow[OF hG hZ heps hinvs])
        also have "\<dots> = int (nat (- c s)) * \<epsilon> (invg (\<iota> s))" by (rule int_group_pow)
        also have "\<epsilon> (invg (\<iota> s)) = - \<epsilon> (\<iota> s)"
          by (rule hom_preserves_inv[OF hG hZ heps h\<iota>s])
        also have "int (nat (- c s)) * (- \<epsilon> (\<iota> s)) = c s * \<epsilon> (\<iota> s)"
          using False by (by100 simp)
        finally show ?thesis using False by (by100 simp)
      qed
    qed
    \<comment> \<open>Step 2: \<epsilon> distributes over foldr.\<close>
    let ?gterm = "\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
        else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))"
    {fix ys :: "'s list"
     assume hys: "\<forall>i<length ys. ys!i \<in> S"
     hence "\<epsilon> (foldr mul (map ?gterm ys) e) = (\<Sum>s\<leftarrow>ys. c s * \<epsilon> (\<iota> s))"
     proof (induction ys)
       case Nil show ?case using hom_preserves_id[OF hG hZ heps] by (by100 simp)
     next
       case (Cons s ys')
       have hs: "s \<in> S" using Cons.prems by (by100 force)
       have hys': "\<forall>i<length ys'. ys'!i \<in> S" using Cons.prems by (by100 force)
       have hgs: "?gterm s \<in> G"
       proof -
         have h\<iota>s: "\<iota> s \<in> G" using hgen_in_G hs by (by100 blast)
         have hinvs: "invg (\<iota> s) \<in> G" using hG h\<iota>s unfolding top1_is_group_on_def by (by100 blast)
         show ?thesis using group_pow_in_group[OF hG h\<iota>s] group_pow_in_group[OF hG hinvs] by (by100 auto)
       qed
       have hprod: "foldr mul (map ?gterm ys') e \<in> G"
       proof (rule foldr_mul_closed[OF hG])
         show "\<forall>i<length (map ?gterm ys'). (map ?gterm ys')!i \<in> G"
         proof (intro allI impI)
           fix i assume hi: "i < length (map ?gterm ys')"
           have hsi: "ys'!i \<in> S" using hys' hi by (by100 simp)
           have h\<iota>si: "\<iota> (ys'!i) \<in> G" using hgen_in_G hsi by (by100 blast)
           have hinvsi: "invg (\<iota> (ys'!i)) \<in> G" using hG h\<iota>si unfolding top1_is_group_on_def by (by100 blast)
           show "(map ?gterm ys')!i \<in> G" using hi group_pow_in_group[OF hG h\<iota>si] group_pow_in_group[OF hG hinvsi] by (by100 auto)
         qed
       qed
       have "\<epsilon> (foldr mul (map ?gterm (s # ys')) e)
           = \<epsilon> (mul (?gterm s) (foldr mul (map ?gterm ys') e))" by (by100 simp)
       also have "\<dots> = \<epsilon> (?gterm s) + \<epsilon> (foldr mul (map ?gterm ys') e)"
         using heps hgs hprod unfolding top1_group_hom_on_def by (by100 blast)
       also have "\<epsilon> (?gterm s) = c s * \<epsilon> (\<iota> s)" by (rule heps_term[OF hs])
       also have "c s * \<epsilon> (\<iota> s) + \<epsilon> (foldr mul (map ?gterm ys') e)
           = c s * \<epsilon> (\<iota> s) + (\<Sum>s\<leftarrow>ys'. c s * \<epsilon> (\<iota> s))"
         using Cons.IH[OF hys'] by (by100 simp)
       finally show ?case by (by100 simp)
     qed}
    moreover have hxs_S: "\<forall>i<length ?xs. ?xs!i \<in> S"
    proof (intro allI impI)
      fix i assume hi: "i < length ?xs"
      have "\<exists>xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs"
        using finite_distinct_list[OF assms(2)] by (by100 blast)
      hence "set ?xs = {s \<in> S. c s \<noteq> 0} \<and> distinct ?xs" by (rule someI_ex)
      thus "?xs!i \<in> S" using nth_mem[OF hi] by (by100 blast)
    qed
    ultimately have hfoldr: "\<epsilon> ?gp = (\<Sum>s\<leftarrow>?xs. c s * \<epsilon> (\<iota> s))" by (by100 simp)
    \<comment> \<open>Step 3: Kronecker delta: sum = c(s0).\<close>
    have hprop: "set ?xs = {s \<in> S. c s \<noteq> 0} \<and> distinct ?xs"
    proof -
      have "\<exists>xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs"
        using finite_distinct_list[OF assms(2)] by (by100 blast)
      thus ?thesis by (rule someI_ex)
    qed
    have hs0_in: "s0 \<in> set ?xs" using hprop hs0 by (by100 blast)
    have hdist: "distinct ?xs" using hprop by (by100 blast)
    have "\<And>s. s \<in> set ?xs \<Longrightarrow> c s * \<epsilon> (\<iota> s) = (if s = s0 then c s0 else 0)"
    proof -
      fix s assume hs_in: "s \<in> set ?xs"
      have hs_S: "s \<in> S" using hs_in hprop by (by100 blast)
      show "c s * \<epsilon> (\<iota> s) = (if s = s0 then c s0 else 0)"
      proof (cases "s = s0")
        case True thus ?thesis using heps_s0 by (by100 simp)
      next
        case False thus ?thesis using heps_other hs_S by (by100 simp)
      qed
    qed
    have "map (\<lambda>s. c s * \<epsilon> (\<iota> s)) ?xs = map (\<lambda>s. if s = s0 then c s0 else (0::int)) ?xs"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>s. c s * \<epsilon> (\<iota> s)) ?xs) = length (map (\<lambda>s. if s = s0 then c s0 else 0) ?xs)"
        by (by100 simp)
    next
      fix i assume "i < length (map (\<lambda>s. c s * \<epsilon> (\<iota> s)) ?xs)"
      hence hi: "i < length ?xs" by (by100 simp)
      hence "?xs!i \<in> set ?xs" by (rule nth_mem)
      thus "map (\<lambda>s. c s * \<epsilon> (\<iota> s)) ?xs ! i = map (\<lambda>s. if s = s0 then c s0 else (0::int)) ?xs ! i"
        using \<open>\<And>s. s \<in> set ?xs \<Longrightarrow> c s * \<epsilon> (\<iota> s) = (if s = s0 then c s0 else 0)\<close> hi by (by100 simp)
    qed
    hence "sum_list (map (\<lambda>s. c s * \<epsilon> (\<iota> s)) ?xs) = sum_list (map (\<lambda>s. if s = s0 then c s0 else (0::int)) ?xs)"
      by (rule arg_cong[of _ _ sum_list])
    hence "(\<Sum>s\<leftarrow>?xs. c s * \<epsilon> (\<iota> s)) = (\<Sum>s\<leftarrow>?xs. if s = s0 then c s0 else 0)" by (by100 simp)
    also have "\<dots> = c s0"
    proof -
      {fix ys :: "'s list"
       assume hyin: "s0 \<in> set ys" and hdist: "distinct ys"
       hence "(\<Sum>s\<leftarrow>ys. if s = s0 then c s0 else (0::int)) = c s0"
       proof (induction ys)
         case Nil thus ?case by (by100 simp)
       next
         case (Cons a ys')
         show ?case
         proof (cases "a = s0")
           case True
           hence "s0 \<notin> set ys'" using Cons.prems(2) by (by100 force)
           hence "(\<Sum>s\<leftarrow>ys'. if s = s0 then c s0 else (0::int)) = 0"
             by (induction ys') (by100 auto)+
           thus ?thesis using True by (by100 simp)
         next
           case False
           hence "s0 \<in> set ys'" using Cons.prems(1) by (by100 simp)
           moreover have "distinct ys'" using Cons.prems(2) by (by100 simp)
           ultimately show ?thesis using False Cons.IH by (by100 simp)
         qed
       qed}
      thus ?thesis using hs0_in hdist by (by100 blast)
    qed
    finally show ?thesis using hfoldr by (by100 simp)
  qed
  hence "?gp \<notin> ?N" using hcomm_ker hs0(2) by (by100 force)
  \<comment> \<open>The H-product = \<phi>(gp).\<close>
  have hH_grp: "top1_is_group_on (top1_quotient_group_carrier_on G mul ?N) ?mulH ?eH ?invgH"
    using hH_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hH_prod_eq: "foldr ?mulH (map (\<lambda>s.
        if c s \<ge> 0 then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
        else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s)))
      ?xs) ?eH = ?\<phi> ?gp"
  proof -
    let ?hterm = "\<lambda>s. if c s \<ge> 0 then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
        else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s))"
    let ?gterm = "\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
        else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))"
    \<comment> \<open>h\_term\_eq: \<phi>(gterm s) = hterm s for each s \<in> S.\<close>
    have h_term_eq: "\<And>s. s \<in> S \<Longrightarrow> ?\<phi> (?gterm s) = ?hterm s"
    proof -
      fix s assume hs: "s \<in> S"
      have h\<iota>s: "\<iota> s \<in> G" using hgen_in_G hs by (by100 blast)
      have hinvs: "invg (\<iota> s) \<in> G" using hG h\<iota>s unfolding top1_is_group_on_def by (by100 blast)
      show "?\<phi> (?gterm s) = ?hterm s"
      proof (cases "c s \<ge> 0")
        case True
        have "?\<phi> (top1_group_pow mul e (\<iota> s) (nat (c s)))
            = top1_group_pow ?mulH ?eH (?\<phi> (\<iota> s)) (nat (c s))"
          by (rule hom_group_pow[OF hG hH_grp hphi_hom h\<iota>s])
        thus ?thesis using True by (by100 simp)
      next
        case False
        have "?\<phi> (top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
            = top1_group_pow ?mulH ?eH (?\<phi> (invg (\<iota> s))) (nat (- c s))"
          by (rule hom_group_pow[OF hG hH_grp hphi_hom hinvs])
        moreover have "?\<phi> (invg (\<iota> s)) = ?invgH (?\<phi> (\<iota> s))"
          by (rule hom_preserves_inv[OF hG hH_grp hphi_hom h\<iota>s])
        ultimately show ?thesis using False by (by100 simp)
      qed
    qed
    \<comment> \<open>Induction on ?xs.\<close>
    {fix ys :: "'s list"
     assume hys: "\<forall>i<length ys. ys!i \<in> S"
     hence "foldr ?mulH (map ?hterm ys) ?eH = ?\<phi> (foldr mul (map ?gterm ys) e)"
     proof (induction ys)
       case Nil show ?case using hom_preserves_id[OF hG hH_grp hphi_hom] by (by100 simp)
     next
       case (Cons s ys')
       have hs: "s \<in> S" using Cons.prems by (by100 force)
       have hys': "\<forall>i<length ys'. ys'!i \<in> S" using Cons.prems by (by100 force)
       have hgs: "?gterm s \<in> G"
       proof -
         have h\<iota>s: "\<iota> s \<in> G" using hgen_in_G hs by (by100 blast)
         have hinvs: "invg (\<iota> s) \<in> G" using hG h\<iota>s unfolding top1_is_group_on_def by (by100 blast)
         show ?thesis using group_pow_in_group[OF hG h\<iota>s] group_pow_in_group[OF hG hinvs]
           by (by100 auto)
       qed
       have hprod: "foldr mul (map ?gterm ys') e \<in> G"
       proof (rule foldr_mul_closed[OF hG])
         show "\<forall>i<length (map ?gterm ys'). (map ?gterm ys')!i \<in> G"
         proof (intro allI impI)
           fix i assume hi: "i < length (map ?gterm ys')"
           have hsi: "ys'!i \<in> S" using hys' hi by (by100 simp)
           have h\<iota>si: "\<iota> (ys'!i) \<in> G" using hgen_in_G hsi by (by100 blast)
           have hinvsi: "invg (\<iota> (ys'!i)) \<in> G" using hG h\<iota>si unfolding top1_is_group_on_def by (by100 blast)
           show "(map ?gterm ys')!i \<in> G" using hi
             group_pow_in_group[OF hG h\<iota>si] group_pow_in_group[OF hG hinvsi] by (by100 auto)
         qed
       qed
       have "foldr ?mulH (map ?hterm (s # ys')) ?eH
           = ?mulH (?hterm s) (foldr ?mulH (map ?hterm ys') ?eH)" by (by100 simp)
       also have "\<dots> = ?mulH (?hterm s) (?\<phi> (foldr mul (map ?gterm ys') e))"
         using Cons.IH[OF hys'] by (by100 simp)
       also have "?hterm s = ?\<phi> (?gterm s)" using h_term_eq[OF hs] by (by100 simp)
       also have "?mulH (?\<phi> (?gterm s)) (?\<phi> (foldr mul (map ?gterm ys') e))
           = ?\<phi> (mul (?gterm s) (foldr mul (map ?gterm ys') e))"
         using hphi_hom hgs hprod unfolding top1_group_hom_on_def by (by100 blast)
       also have "mul (?gterm s) (foldr mul (map ?gterm ys') e)
           = foldr mul (map ?gterm (s # ys')) e" by (by100 simp)
       finally show ?case by (by100 simp)
     qed}
    moreover have "\<forall>i<length ?xs. ?xs!i \<in> S"
    proof (intro allI impI)
      fix i assume hi: "i < length ?xs"
      have "\<exists>xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs"
        using finite_distinct_list[OF assms(2)] by (by100 blast)
      hence "set ?xs = {s \<in> S. c s \<noteq> 0} \<and> distinct ?xs" by (rule someI_ex)
      thus "?xs!i \<in> S" using nth_mem[OF hi] by (by100 blast)
    qed
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>If the H-product = ?eH, then \<phi>(gp) = ?eH, so gp \<in> [G,G]. Contradiction.\<close>
  show ?thesis
  proof
    assume heq: "foldr ?mulH (map (\<lambda>s.
        if c s \<ge> 0 then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
        else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s)))
      ?xs) ?eH = ?eH"
    hence "?\<phi> ?gp = ?eH" using hH_prod_eq by (by100 simp)
    hence "?gp \<in> ?N"
    proof -
      assume hphi_e: "?\<phi> ?gp = ?eH"
      have hker_eq: "top1_group_kernel_on G ?eH ?\<phi> = ?N"
        using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
      have hgp_G: "?gp \<in> G"
      proof (rule foldr_mul_closed[OF hG])
        show "\<forall>i<length (map (\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))) ?xs).
          (map (\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))) ?xs) ! i \<in> G"
        proof (intro allI impI)
          fix i assume hi: "i < length (map (\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))) ?xs)"
          have hsi: "?xs ! i \<in> S"
          proof -
            have "\<exists>xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs"
              using finite_distinct_list[OF assms(2)] by (by100 blast)
            hence "set ?xs = {s \<in> S. c s \<noteq> 0} \<and> distinct ?xs" by (rule someI_ex)
            thus ?thesis using nth_mem hi by (by100 force)
          qed
          have h\<iota>si: "\<iota> (?xs!i) \<in> G" using hgen_in_G hsi by (by100 blast)
          have hinvsi: "invg (\<iota> (?xs!i)) \<in> G"
            using hG h\<iota>si unfolding top1_is_group_on_def by (by100 blast)
          show "(map (\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))) ?xs) ! i \<in> G"
            using hi group_pow_in_group[OF hG h\<iota>si] group_pow_in_group[OF hG hinvsi]
            by (by100 auto)
        qed
      qed
      have "?gp \<in> top1_group_kernel_on G ?eH ?\<phi>"
        unfolding top1_group_kernel_on_def using hgp_G hphi_e by (by100 blast)
      thus "?gp \<in> ?N" using hker_eq by (by100 simp)
    qed
    thus False using \<open>?gp \<notin> ?N\<close> by (by100 blast)
  qed
qed

(** from \<S>69 Theorem 69.4: abelianization of free group is free abelian.
    If G is free on S, then G/[G,G] is free abelian on the images of S. **)
theorem Theorem_69_4:
  fixes G :: "'g set"
    and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g
    and invg :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g"
    and S :: "'s set"
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
  shows "\<exists>(H :: 'g set set) mulH eH invgH \<phi> \<iota>H.
           top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi>
         \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H S
         \<and> (\<forall>s\<in>S. \<iota>H s = \<phi> (\<iota> s))"
proof -
  have hG: "top1_is_group_on G mul e invg"
    using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  let ?H = "top1_quotient_group_carrier_on G mul ?N"
  let ?mulH = "top1_quotient_group_mul_on mul"
  let ?eH = "top1_group_coset_on G mul ?N e"
  let ?invgH = "\<lambda>C. top1_group_coset_on G mul ?N
         (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul ?N g))"
  let ?\<phi> = "\<lambda>g. top1_group_coset_on G mul ?N g"
  have h_abel: "top1_is_abelianization_of ?H ?mulH ?eH ?invgH G mul e invg ?\<phi>"
    by (rule abelianization_concrete[OF hG])
  \<comment> \<open>Step 2: \<phi>(\<iota>(S)) generates H and satisfies no nontrivial integer relations
     (exponent sum argument in the free group).\<close>
  let ?\<iota>H = "\<lambda>s. ?\<phi> (\<iota> s)"
  \<comment> \<open>Step 2a: H is abelian (from abelianization).\<close>
  have hH_abel: "top1_is_abelian_group_on ?H ?mulH ?eH ?invgH"
    using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  \<comment> \<open>Step 2b: \<iota>(s) \<in> G for each s, so \<phi>(\<iota>(s)) \<in> H.\<close>
  have hgen_in_G: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hphi_surj: "?\<phi> ` G = ?H"
    using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  have hiotaH_in_H: "\<forall>s\<in>S. ?\<iota>H s \<in> ?H"
  proof (intro ballI)
    fix s assume "s \<in> S"
    hence "\<iota> s \<in> G" using hgen_in_G by (by100 blast)
    thus "?\<iota>H s \<in> ?H" using hphi_surj by (by100 blast)
  qed
  \<comment> \<open>Step 2c: \<iota>H injective on S.
     Proof: if ?\<phi>(\<iota> s1) = ?\<phi>(\<iota> s2), then \<iota> s1 \<cdot> invg(\<iota> s2) \<in> [G,G].
     But in a free group, \<iota> s1 \<cdot> invg(\<iota> s2) for s1 \<noteq> s2 is a non-trivial reduced word,
     and its exponent sums are nonzero, so it cannot be in [G,G].
     (The exponent sum of s1 is +1, of s2 is -1.)\<close>
  have hiotaH_inj: "inj_on ?\<iota>H S"
    by (rule abelianization_injective_on_generators[OF assms])
  \<comment> \<open>Step 2d: H = \<langle>\<iota>H(S)\<rangle> (generated by images of generators).
     Since G = \<langle>\<iota>(S)\<rangle> and \<phi> is surjective, H = \<phi>(G) = \<phi>(\<langle>\<iota>(S)\<rangle>) = \<langle>\<phi>(\<iota>(S))\<rangle> = \<langle>\<iota>H(S)\<rangle>.\<close>
  have hH_gen: "?H = top1_subgroup_generated_on ?H ?mulH ?eH ?invgH (?\<iota>H ` S)"
  proof -
    have hH_grp: "top1_is_group_on ?H ?mulH ?eH ?invgH"
      using hH_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
    have hphi_hom: "top1_group_hom_on G mul ?H ?mulH ?\<phi>"
      using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hphi_surj: "?\<phi> ` G = ?H"
      using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hiotaS_sub: "\<iota> ` S \<subseteq> G"
      using hgen_in_G by (by100 blast)
    have hG_gen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
      using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
    have "?H = top1_subgroup_generated_on ?H ?mulH ?eH ?invgH (?\<phi> ` (\<iota> ` S))"
      by (rule surj_hom_generated[OF hG hH_grp hphi_hom hphi_surj hiotaS_sub hG_gen])
    moreover have "?\<phi> ` (\<iota> ` S) = ?\<iota>H ` S" by (by100 force)
    ultimately show ?thesis by (by100 simp)
  qed
  \<comment> \<open>Step 2e: No nontrivial integer relations.
     For c: S \<rightarrow> Z with finite support and some c(s) \<noteq> 0:
     \<Pi> \<iota>H(s)^{c(s)} = ?\<phi>(\<Pi> \<iota>(s)^{c(s)}) \<noteq> ?eH.
     Because \<Pi> \<iota>(s)^{c(s)} \<notin> ker(\<phi>) = [G,G] (exponent sum argument:
     the exponent sum of s0 in \<Pi> \<iota>(s)^{c(s)} equals c(s0) \<noteq> 0,
     but all elements of [G,G] have zero exponent sums).\<close>
  have hH_indep: "\<forall>c :: 's \<Rightarrow> int.
      finite {s\<in>S. c s \<noteq> 0} \<longrightarrow>
      (\<exists>s\<in>S. c s \<noteq> 0) \<longrightarrow>
      foldr ?mulH (map (\<lambda>s.
          if c s \<ge> 0 then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
          else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s)))
        (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) ?eH \<noteq> ?eH"
    using abelianization_independence_on_generators[OF assms] by (by100 blast)
  \<comment> \<open>Step 2f: Assemble all conditions into free abelian group definition.\<close>
  have h_free_abel: "\<exists>\<iota>H.
      top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH \<iota>H S
    \<and> (\<forall>s\<in>S. \<iota>H s = ?\<phi> (\<iota> s))"
  proof (intro exI conjI)
    show "top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH ?\<iota>H S"
      unfolding top1_is_free_abelian_group_full_on_def
    proof (intro conjI)
      show "top1_is_abelian_group_on ?H ?mulH ?eH ?invgH" by (rule hH_abel)
      show "\<forall>s\<in>S. ?\<iota>H s \<in> ?H" by (rule hiotaH_in_H)
      show "inj_on ?\<iota>H S" by (rule hiotaH_inj)
      show "?H = top1_subgroup_generated_on ?H ?mulH ?eH ?invgH (?\<iota>H ` S)" by (rule hH_gen)
      show "\<forall>c::'s \<Rightarrow> int.
        finite {s \<in> S. c s \<noteq> 0} \<longrightarrow>
        (\<exists>s\<in>S. c s \<noteq> 0) \<longrightarrow>
        foldr ?mulH
         (map (\<lambda>s. if 0 \<le> c s then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
                   else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s)))
           (SOME xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs))
         ?eH \<noteq> ?eH" by (rule hH_indep)
    qed
    show "\<forall>s\<in>S. ?\<iota>H s = ?\<phi> (\<iota> s)" by (by100 simp)
  qed
  show ?thesis using h_abel h_free_abel by (by100 blast)
qed

text \<open>Key algebraic fact: if G = F/N where F is free on S and N \<subseteq> [F,F],
  then the abelianization G/[G,G] is isomorphic to F/[F,F] (free abelian on S).
  Proof via first isomorphism theorem: the composition F \<rightarrow> G \<rightarrow> G/[G,G]
  is surjective with kernel [F,F]\<cdot>N = [F,F] (since N \<subseteq> [F,F]).\<close>
text \<open>Independence transfers through group isomorphism: if G has independence
  and f: G \<rightarrow> H is an iso, then H has independence (via f\<inverse>).\<close>
lemma free_abelian_independence_transfer:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g" and S :: "'s set"
    and H :: "'h set" and mulH :: "'h \<Rightarrow> 'h \<Rightarrow> 'h"
    and eH :: 'h and invgH :: "'h \<Rightarrow> 'h"
    and f :: "'g \<Rightarrow> 'h"
  assumes hG_grp: "top1_is_group_on G mul e invg"
      and hH_grp: "top1_is_group_on H mulH eH invgH"
      and hf_hom: "top1_group_hom_on G mul H mulH f"
      and hf_bij: "bij_betw f G H"
      and h\<iota>_in: "\<forall>s\<in>S. \<iota> s \<in> G"
      and hG_indep: "\<And>c. finite {s\<in>S. c s \<noteq> 0} \<Longrightarrow> (\<exists>s\<in>S. c s \<noteq> 0) \<Longrightarrow>
          foldr mul (map (\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
              else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
            (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) e \<noteq> e"
      and hfin: "finite {s\<in>S. c s \<noteq> 0}" and hex: "\<exists>s\<in>S. c s \<noteq> 0"
  shows "foldr mulH (map (\<lambda>s.
          if c s \<ge> 0 then top1_group_pow mulH eH (f (\<iota> s)) (nat (c s))
          else top1_group_pow mulH eH (invgH (f (\<iota> s))) (nat (- c s)))
        (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) eH \<noteq> eH"
proof -
  let ?gterm = "\<lambda>s. if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
      else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s))"
  let ?hterm = "\<lambda>s. if c s \<ge> 0 then top1_group_pow mulH eH (f (\<iota> s)) (nat (c s))
      else top1_group_pow mulH eH (invgH (f (\<iota> s))) (nat (- c s))"
  let ?xs = "SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs"
  \<comment> \<open>H-product = f(G-product) by induction.\<close>
  {fix ys :: "'s list"
   assume hys: "\<forall>i<length ys. ys!i \<in> S"
   hence "foldr mulH (map ?hterm ys) eH = f (foldr mul (map ?gterm ys) e)"
   proof (induction ys)
     case Nil show ?case using hom_preserves_id[OF hG_grp hH_grp hf_hom] by (by100 simp)
   next
     case (Cons s ys')
     have hs: "s \<in> S" using Cons.prems by (by100 force)
     have hys': "\<forall>i<length ys'. ys'!i \<in> S" using Cons.prems by (by100 force)
     have h\<iota>s: "\<iota> s \<in> G" using h\<iota>_in hs by (by100 blast)
     have hinvs: "invg (\<iota> s) \<in> G" using hG_grp h\<iota>s unfolding top1_is_group_on_def by (by100 blast)
     have hgs: "?gterm s \<in> G"
       using group_pow_in_group[OF hG_grp h\<iota>s] group_pow_in_group[OF hG_grp hinvs] by (by100 auto)
     have hprod: "foldr mul (map ?gterm ys') e \<in> G"
     proof (rule foldr_mul_closed[OF hG_grp])
       show "\<forall>i<length (map ?gterm ys'). (map ?gterm ys')!i \<in> G"
       proof (intro allI impI)
         fix i assume hi: "i < length (map ?gterm ys')"
         have hsi: "ys'!i \<in> S" using hys' hi by (by100 simp)
         have h\<iota>si: "\<iota> (ys'!i) \<in> G" using h\<iota>_in hsi by (by100 blast)
         have hinvsi: "invg (\<iota> (ys'!i)) \<in> G" using hG_grp h\<iota>si unfolding top1_is_group_on_def by (by100 blast)
         show "(map ?gterm ys')!i \<in> G" using hi
           group_pow_in_group[OF hG_grp h\<iota>si] group_pow_in_group[OF hG_grp hinvsi] by (by100 auto)
       qed
     qed
     have h_eq: "f (?gterm s) = ?hterm s"
     proof (cases "c s \<ge> 0")
       case True
       have "f (top1_group_pow mul e (\<iota> s) (nat (c s)))
           = top1_group_pow mulH eH (f (\<iota> s)) (nat (c s))"
         by (rule hom_group_pow[OF hG_grp hH_grp hf_hom h\<iota>s])
       thus ?thesis using True by (by100 simp)
     next
       case False
       have "f (top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
           = top1_group_pow mulH eH (f (invg (\<iota> s))) (nat (- c s))"
         by (rule hom_group_pow[OF hG_grp hH_grp hf_hom hinvs])
       moreover have "f (invg (\<iota> s)) = invgH (f (\<iota> s))"
         by (rule hom_preserves_inv[OF hG_grp hH_grp hf_hom h\<iota>s])
       ultimately show ?thesis using False by (by100 simp)
     qed
     have "foldr mulH (map ?hterm (s # ys')) eH
         = mulH (?hterm s) (foldr mulH (map ?hterm ys') eH)" by (by100 simp)
     also have "\<dots> = mulH (?hterm s) (f (foldr mul (map ?gterm ys') e))"
       using Cons.IH[OF hys'] by (by100 simp)
     also have "?hterm s = f (?gterm s)" using h_eq by (by100 simp)
     also have "mulH (f (?gterm s)) (f (foldr mul (map ?gterm ys') e))
         = f (mul (?gterm s) (foldr mul (map ?gterm ys') e))"
     proof -
       have "f (mul (?gterm s) (foldr mul (map ?gterm ys') e))
           = mulH (f (?gterm s)) (f (foldr mul (map ?gterm ys') e))"
         using hf_hom hgs hprod unfolding top1_group_hom_on_def by (by100 blast)
       thus ?thesis by (by100 simp)
     qed
     also have "mul (?gterm s) (foldr mul (map ?gterm ys') e)
         = foldr mul (map ?gterm (s # ys')) e" by (by100 simp)
     finally show ?case by (by100 simp)
   qed}
  moreover have hxs_S: "\<forall>i<length ?xs. ?xs!i \<in> S"
  proof (intro allI impI)
    fix i assume hi: "i < length ?xs"
    have "\<exists>xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs"
      using finite_distinct_list[OF hfin] by (by100 blast)
    hence "set ?xs = {s \<in> S. c s \<noteq> 0} \<and> distinct ?xs" by (rule someI_ex)
    thus "?xs!i \<in> S" using nth_mem[OF hi] by (by100 blast)
  qed
  ultimately have hH_eq: "foldr mulH (map ?hterm ?xs) eH = f (foldr mul (map ?gterm ?xs) e)"
    by (by100 simp)
  \<comment> \<open>Contradiction via injectivity.\<close>
  show ?thesis
  proof
    assume heq: "foldr mulH (map ?hterm ?xs) eH = eH"
    have "f (foldr mul (map ?gterm ?xs) e) = eH" using heq hH_eq by (by100 simp)
    moreover have "f e = eH" by (rule hom_preserves_id[OF hG_grp hH_grp hf_hom])
    moreover have "inj_on f G" using hf_bij unfolding bij_betw_def by (by100 blast)
    moreover have "foldr mul (map ?gterm ?xs) e \<in> G"
    proof (rule foldr_mul_closed[OF hG_grp])
      show "\<forall>i<length (map ?gterm ?xs). (map ?gterm ?xs)!i \<in> G"
      proof (intro allI impI)
        fix i assume hi: "i < length (map ?gterm ?xs)"
        have hsi: "?xs!i \<in> S" using hxs_S hi by (by100 simp)
        have h\<iota>si: "\<iota> (?xs!i) \<in> G" using h\<iota>_in hsi by (by100 blast)
        have hinvsi: "invg (\<iota> (?xs!i)) \<in> G" using hG_grp h\<iota>si unfolding top1_is_group_on_def by (by100 blast)
        show "(map ?gterm ?xs)!i \<in> G" using hi
          group_pow_in_group[OF hG_grp h\<iota>si] group_pow_in_group[OF hG_grp hinvsi] by (by100 auto)
      qed
    qed
    moreover have "e \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
    ultimately have "foldr mul (map ?gterm ?xs) e = e"
    proof -
      assume h1: "f (foldr mul (map ?gterm ?xs) e) = eH"
         and h2: "f e = eH" and h3: "inj_on f G"
         and h4: "foldr mul (map ?gterm ?xs) e \<in> G" and h5: "e \<in> G"
      have "f (foldr mul (map ?gterm ?xs) e) = f e" using h1 h2 by (by100 simp)
      thus ?thesis using h3 h4 h5 unfolding inj_on_def by (by100 blast)
    qed
    thus False using hG_indep[OF hfin hex] by (by100 blast)
  qed
qed

text \<open>Free abelian groups are preserved under group isomorphism.\<close>
lemma free_abelian_invariant_under_iso:
  assumes "top1_is_free_abelian_group_full_on G mul e invg \<iota> S"
      and "top1_group_iso_on G mul H mulH f"
      and "top1_is_abelian_group_on H mulH eH invgH"
  shows "\<exists>\<iota>'. top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>' S"
proof -
  define \<iota>' where "\<iota>' s = f (\<iota> s)" for s
  have hG_grp: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_free_abelian_group_full_on_def
      top1_is_abelian_group_on_def by (by100 blast)
  have hH_grp: "top1_is_group_on H mulH eH invgH"
    using assms(3) unfolding top1_is_abelian_group_on_def by (by100 blast)
  have h\<iota>_in: "\<forall>s\<in>S. \<iota> s \<in> G"
    using assms(1) unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have h\<iota>_inj: "inj_on \<iota> S"
    using assms(1) unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  have hf_hom: "top1_group_hom_on G mul H mulH f"
    using assms(2) unfolding top1_group_iso_on_def by (by100 blast)
  have hf_bij: "bij_betw f G H"
    using assms(2) unfolding top1_group_iso_on_def by (by100 blast)
  \<comment> \<open>Part 1: \<iota>' maps S into H.\<close>
  have h1: "\<forall>s\<in>S. \<iota>' s \<in> H"
    unfolding \<iota>'_def using h\<iota>_in hf_bij unfolding bij_betw_def by (by100 blast)
  \<comment> \<open>Part 2: \<iota>' is injective.\<close>
  have h2: "inj_on \<iota>' S"
    unfolding \<iota>'_def
  proof (rule inj_onI)
    fix x y assume hx: "x \<in> S" and hy: "y \<in> S" and hfeq: "f (\<iota> x) = f (\<iota> y)"
    have "inj_on f G" using hf_bij unfolding bij_betw_def by (by100 blast)
    hence "\<iota> x = \<iota> y" using hfeq h\<iota>_in hx hy unfolding inj_on_def by (by100 blast)
    thus "x = y" using h\<iota>_inj hx hy unfolding inj_on_def by (by100 blast)
  qed
  \<comment> \<open>Part 3: \<iota>'(S) generates H.\<close>
  have h3: "H = top1_subgroup_generated_on H mulH eH invgH (\<iota>' ` S)"
  proof -
    have "\<iota>' ` S = f ` (\<iota> ` S)" unfolding \<iota>'_def image_image by (by100 blast)
    moreover have "f ` G = H" using hf_bij unfolding bij_betw_def by (by100 blast)
    moreover have "\<iota> ` S \<subseteq> G" using h\<iota>_in by (by100 blast)
    moreover have "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
      using assms(1) unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
    ultimately show ?thesis
      by (metis surj_hom_generated[OF hG_grp hH_grp hf_hom _ _ _])
  qed
  \<comment> \<open>Part 4: Independence via free\_abelian\_independence\_transfer.\<close>
  have "top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>' S"
    unfolding top1_is_free_abelian_group_full_on_def \<iota>'_def
  proof (intro conjI)
    show "top1_is_abelian_group_on H mulH eH invgH" by (rule assms(3))
    show "\<forall>s\<in>S. f (\<iota> s) \<in> H" using h1 unfolding \<iota>'_def by (by100 blast)
    show "inj_on (\<lambda>s. f (\<iota> s)) S" using h2 unfolding \<iota>'_def by (by100 blast)
    show "H = top1_subgroup_generated_on H mulH eH invgH ((\<lambda>s. f (\<iota> s)) ` S)"
      using h3 unfolding \<iota>'_def by (by100 blast)
  next
    show "\<forall>c. finite {s \<in> S. c s \<noteq> 0} \<longrightarrow> (\<exists>s\<in>S. c s \<noteq> 0) \<longrightarrow>
        foldr mulH (map (\<lambda>s. if 0 \<le> c s then top1_group_pow mulH eH (f (\<iota> s)) (nat (c s))
            else top1_group_pow mulH eH (invgH (f (\<iota> s))) (nat (- c s)))
          (SOME xs. set xs = {s \<in> S. c s \<noteq> 0} \<and> distinct xs)) eH \<noteq> eH"
      using free_abelian_independence_transfer[OF hG_grp hH_grp hf_hom hf_bij h\<iota>_in]
        assms(1) unfolding top1_is_free_abelian_group_full_on_def by (by100 blast)
  qed
  thus ?thesis by (by100 blast)
qed

text \<open>Concrete corollary: the quotient G/[G,G] is free abelian on S
  (extracts the concrete quotient from Theorem 69.4 by re-using the same proof).\<close>
lemma Theorem_69_4_concrete_free_abelian:
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
  shows "\<exists>\<iota>H. top1_is_free_abelian_group_full_on
      (top1_quotient_group_carrier_on G mul (top1_commutator_subgroup_on G mul e invg))
      (top1_quotient_group_mul_on mul)
      (top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg) e)
      (\<lambda>C. top1_group_coset_on G mul (top1_commutator_subgroup_on G mul e invg)
         (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul
            (top1_commutator_subgroup_on G mul e invg) g)))
      \<iota>H S"
proof -
  \<comment> \<open>The abelianization property holds for the concrete quotient.\<close>
  have hG: "top1_is_group_on G mul e invg"
    using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  let ?H = "top1_quotient_group_carrier_on G mul ?N"
  let ?mulH = "top1_quotient_group_mul_on mul"
  let ?eH = "top1_group_coset_on G mul ?N e"
  let ?invgH = "\<lambda>C. top1_group_coset_on G mul ?N (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul ?N g))"
  let ?\<phi> = "\<lambda>g. top1_group_coset_on G mul ?N g"
  let ?\<iota>H = "\<lambda>s. ?\<phi> (\<iota> s)"
  have h_abel: "top1_is_abelianization_of ?H ?mulH ?eH ?invgH G mul e invg ?\<phi>"
    by (rule abelianization_concrete[OF hG])
  \<comment> \<open>The proof of Theorem\_69\_4 returns exactly ?H, ?mulH, etc. as witnesses.
     We need: free\_abelian\_full\_on ?H ?mulH ?eH ?invgH ?\<iota>H S.
     Since this IS what Theorem\_69\_4's proof establishes (h\_free\_abel fact),
     we re-derive the key parts inline.\<close>
  \<comment> \<open>Step 1: ?\<iota>H maps S into ?H.\<close>
  have h\<iota>H_in: "\<forall>s\<in>S. ?\<iota>H s \<in> ?H"
  proof (intro ballI)
    fix s assume hs: "s \<in> S"
    have "\<iota> s \<in> G" using assms hs unfolding top1_is_free_group_full_on_def by (by100 blast)
    hence "?\<phi> (\<iota> s) \<in> ?\<phi> ` G" by (by100 blast)
    also have "?\<phi> ` G = ?H" using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    finally show "?\<iota>H s \<in> ?H" by (by100 simp)
  qed
  \<comment> \<open>Step 2: ?\<iota>H is injective on S.\<close>
  have h\<iota>H_inj: "inj_on ?\<iota>H S"
    by (rule abelianization_injective_on_generators[OF assms])
  \<comment> \<open>Step 3: ?\<iota>H(S) generates ?H.\<close>
  have hH_gen: "?H = top1_subgroup_generated_on ?H ?mulH ?eH ?invgH (?\<iota>H ` S)"
  proof -
    have hH_grp: "top1_is_group_on ?H ?mulH ?eH ?invgH"
      using h_abel unfolding top1_is_abelianization_of_def top1_is_abelian_group_on_def
      by (by100 blast)
    have hphi_hom: "top1_group_hom_on G mul ?H ?mulH ?\<phi>"
      using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hphi_surj: "?\<phi> ` G = ?H"
      using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
    have hG_gen: "G = top1_subgroup_generated_on G mul e invg (\<iota> ` S)"
      using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
    have h\<iota>S_sub: "\<iota> ` S \<subseteq> G"
      using assms unfolding top1_is_free_group_full_on_def by (by100 blast)
    have "?\<iota>H ` S = ?\<phi> ` (\<iota> ` S)" by (by100 force)
    thus ?thesis
      by (metis surj_hom_generated[OF hG hH_grp hphi_hom hphi_surj h\<iota>S_sub hG_gen])
  qed
  \<comment> \<open>Step 4: Independence (no nontrivial integer combination = ?eH).\<close>
  have hH_indep: "\<And>c. finite {s\<in>S. c s \<noteq> 0} \<Longrightarrow> (\<exists>s\<in>S. c s \<noteq> 0) \<Longrightarrow>
      foldr ?mulH (map (\<lambda>s.
          if c s \<ge> 0 then top1_group_pow ?mulH ?eH (?\<iota>H s) (nat (c s))
          else top1_group_pow ?mulH ?eH (?invgH (?\<iota>H s)) (nat (- c s)))
        (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) ?eH \<noteq> ?eH"
    by (rule abelianization_independence_on_generators[OF assms])
  \<comment> \<open>Step 5: ?H is abelian.\<close>
  have hH_abel: "top1_is_abelian_group_on ?H ?mulH ?eH ?invgH"
    using h_abel unfolding top1_is_abelianization_of_def by (by100 blast)
  show ?thesis
    apply (rule exI[of _ ?\<iota>H])
    unfolding top1_is_free_abelian_group_full_on_def
    using hH_abel h\<iota>H_in h\<iota>H_inj hH_gen hH_indep by (by100 blast)
qed


lemma abelianization_of_presented_group:
  fixes F :: "'g set" and mulF :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and eF :: 'g and invgF :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g" and S :: "'s set"
    and G :: "'h set" and mulG :: "'h \<Rightarrow> 'h \<Rightarrow> 'h"
    and eG :: 'h and invgG :: "'h \<Rightarrow> 'h"
    and \<pi> :: "'g \<Rightarrow> 'h"
  assumes hF_free: "top1_is_free_group_full_on F mulF eF invgF \<iota> S"
      and hG_grp: "top1_is_group_on G mulG eG invgG"
      and hpi_hom: "top1_group_hom_on F mulF G mulG \<pi>"
      and hpi_surj: "\<pi> ` F = G"
      and hker_sub_comm: "top1_group_kernel_on F eG \<pi> \<subseteq>
          top1_commutator_subgroup_on F mulF eF invgF"
  shows "\<exists>(H :: 'h set set) mulH eH invgH \<phi> \<iota>H.
      top1_is_abelianization_of H mulH eH invgH G mulG eG invgG \<phi>
    \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H S"
proof -
  \<comment> \<open>Step 1: Get the concrete abelianization of F.\<close>
  have hF_grp: "top1_is_group_on F mulF eF invgF"
    using hF_free unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?NF = "top1_commutator_subgroup_on F mulF eF invgF"
  \<comment> \<open>Step 2: Compose \<pi> with projection G \<rightarrow> G/[G,G].\<close>
  let ?NG = "top1_commutator_subgroup_on G mulG eG invgG"
  let ?HG = "top1_quotient_group_carrier_on G mulG ?NG"
  let ?mulHG = "top1_quotient_group_mul_on mulG"
  let ?eHG = "top1_group_coset_on G mulG ?NG eG"
  let ?\<phi>G = "\<lambda>g. top1_group_coset_on G mulG ?NG g"
  have habel_G: "top1_is_abelianization_of ?HG ?mulHG ?eHG
      (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g)))
      G mulG eG invgG ?\<phi>G"
    by (rule abelianization_concrete[OF hG_grp])
  \<comment> \<open>Step 3: The composition j = \<phi>G \<circ> \<pi>: F \<rightarrow> G/[G,G] is surjective with kernel [F,F].
     Surjective: \<pi> surjective + \<phi>G surjective.
     Kernel = {f \<in> F | \<phi>G(\<pi>(f)) = ?eHG} = {f \<in> F | \<pi>(f) \<in> [G,G]}
     = \<pi>\<inverse>([G,G]). Since \<pi> maps [F,F] to [G,G] and ker(\<pi>) \<subseteq> [F,F]:
     \<pi>\<inverse>([G,G]) = [F,F] \<cdot> ker(\<pi>) = [F,F] (since ker(\<pi>) \<subseteq> [F,F]).\<close>
  \<comment> \<open>Step 4: By first iso theorem: F/[F,F] \<cong> G/[G,G].\<close>
  \<comment> \<open>Step 5: By Theorem 69.4: F/[F,F] is free abelian on S.\<close>
  \<comment> \<open>Step 5-6: F/[F,F] is free abelian (Theorem 69.4).
     F/[F,F] \<cong> G/[G,G] via first iso theorem on j = \<phi>G\<circ>\<pi>.
     Transfer the free abelian structure from F/[F,F] to G/[G,G].\<close>
  \<comment> \<open>F/[F,F] is free abelian on S by Theorem 69.4.\<close>
  have hfab: "\<exists>(HF :: 'g set set) mulHF eHF invgHF \<phi>F \<iota>HF.
      top1_is_abelianization_of HF mulHF eHF invgHF F mulF eF invgF \<phi>F
    \<and> top1_is_free_abelian_group_full_on HF mulHF eHF invgHF \<iota>HF S"
    using Theorem_69_4[OF hF_free] by (by100 blast)
  \<comment> \<open>Transfer: F/[F,F] \<cong> G/[G,G] via first iso theorem on j = \<phi>G\<circ>\<pi>.
     The kernel of the composed map j: F \<rightarrow> G/[G,G] is:
     ker(j) = {f \<in> F | \<phi>G(\<pi>(f)) = eHG} = {f \<in> F | \<pi>(f) \<in> [G,G]}
     Since \<pi> maps [F,F] onto [G,G] and ker(\<pi>) \<subseteq> [F,F]:
     ker(j) = [F,F] \<cdot> ker(\<pi>) = [F,F].
     By first iso theorem: F/ker(j) = F/[F,F] \<cong> im(j) = G/[G,G].
     The free abelian structure transfers.\<close>
  \<comment> \<open>Compute ker(j) where j = \<phi>G \<circ> \<pi>.\<close>
  \<comment> \<open>Step A: \<pi>([F,F]) = [G,G] (surjective hom maps commutator subgroup onto commutator subgroup).\<close>
  have hpi_comm: "\<pi> ` ?NF \<supseteq> ?NG"
  proof -
    \<comment> \<open>Every commutator in G lifts to a commutator in F (via surjectivity of \<pi>).\<close>
    have hcomms_in_image: "{top1_group_commutator_on mulG invgG g h |g h. g \<in> G \<and> h \<in> G}
        \<subseteq> \<pi> ` ?NF"
    proof (rule subsetI, clarify)
      fix g h assume hg: "g \<in> G" and hh: "h \<in> G"
      obtain a where ha: "a \<in> F" "\<pi> a = g" using hpi_surj hg by (by100 blast)
      obtain b where hb: "b \<in> F" "\<pi> b = h" using hpi_surj hh by (by100 blast)
      \<comment> \<open>[a,b] \<in> [F,F]: commutator is a generator of commutator subgroup.\<close>
      have hcomms_sub_F: "{top1_group_commutator_on mulF invgF x y |x y. x \<in> F \<and> y \<in> F} \<subseteq> F"
      proof (rule subsetI, clarify)
        fix x y assume "x \<in> F" "y \<in> F"
        have hinvx: "invgF x \<in> F" using hF_grp \<open>x \<in> F\<close> unfolding top1_is_group_on_def by (by100 blast)
        have hinvy: "invgF y \<in> F" using hF_grp \<open>y \<in> F\<close> unfolding top1_is_group_on_def by (by100 blast)
        show "top1_group_commutator_on mulF invgF x y \<in> F"
          unfolding top1_group_commutator_on_def
          using hF_grp \<open>x \<in> F\<close> \<open>y \<in> F\<close> hinvx hinvy unfolding top1_is_group_on_def by (by100 blast)
      qed
      have "top1_group_commutator_on mulF invgF a b
          \<in> {top1_group_commutator_on mulF invgF x y |x y. x \<in> F \<and> y \<in> F}"
        using ha(1) hb(1) by (by100 blast)
      hence hab_NF: "top1_group_commutator_on mulF invgF a b \<in> ?NF"
        unfolding top1_commutator_subgroup_on_def
        by (rule subgroup_generated_contains[OF hF_grp hcomms_sub_F])
      \<comment> \<open>\<pi>([a,b]) = [\<pi>(a),\<pi>(b)] = [g,h]: hom preserves commutator.\<close>
      have hinva: "invgF a \<in> F" using hF_grp ha(1) unfolding top1_is_group_on_def by (by100 blast)
      have hinvb: "invgF b \<in> F" using hF_grp hb(1) unfolding top1_is_group_on_def by (by100 blast)
      have hab_F: "mulF a b \<in> F" using hF_grp ha(1) hb(1) unfolding top1_is_group_on_def by (by100 blast)
      have habinva: "mulF (mulF a b) (invgF a) \<in> F"
        using hF_grp hab_F hinva unfolding top1_is_group_on_def by (by100 blast)
      have "\<pi> (top1_group_commutator_on mulF invgF a b)
          = top1_group_commutator_on mulG invgG g h"
        unfolding top1_group_commutator_on_def
        using hpi_hom ha hb hinva hinvb hab_F habinva
        unfolding top1_group_hom_on_def
        using hom_preserves_inv[OF hF_grp hG_grp hpi_hom ha(1)]
              hom_preserves_inv[OF hF_grp hG_grp hpi_hom hb(1)]
        by (by100 simp)
      thus "top1_group_commutator_on mulG invgG g h \<in> \<pi> ` ?NF"
        using hab_NF by (by100 force)
    qed
    \<comment> \<open>[G,G] = ⟨commutators⟩ \<subseteq> \<pi>([F,F]) since \<pi>([F,F]) is a subgroup containing commutators.\<close>
    have himage_sub: "\<pi> ` ?NF \<subseteq> G"
    proof (rule image_subsetI)
      fix x assume "x \<in> ?NF"
      hence "x \<in> F" using commutator_subgroup_is_normal[OF hF_grp]
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      thus "\<pi> x \<in> G" using hpi_hom unfolding top1_group_hom_on_def by (by100 blast)
    qed
    have himage_grp: "top1_is_group_on (\<pi> ` ?NF) mulG eG invgG"
    proof -
      have hNF_grp: "top1_is_group_on ?NF mulF eF invgF"
        using commutator_subgroup_is_normal[OF hF_grp] unfolding top1_normal_subgroup_on_def
        by (by100 blast)
      have hNF_sub: "?NF \<subseteq> F" using hNF_grp commutator_subgroup_is_normal[OF hF_grp]
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      \<comment> \<open>Identity: eG = \<pi>(eF) \<in> \<pi>([F,F]).\<close>
      have heF_NF: "eF \<in> ?NF" using hNF_grp unfolding top1_is_group_on_def by (by100 blast)
      have heG_im: "eG \<in> \<pi> ` ?NF"
      proof -
        have "\<pi> eF = eG" by (rule hom_preserves_id[OF hF_grp hG_grp hpi_hom])
        thus ?thesis using heF_NF by (by100 force)
      qed
      \<comment> \<open>Closure: \<pi>(x) \<cdot> \<pi>(y) = \<pi>(x\<cdot>y) \<in> \<pi>([F,F]).\<close>
      have hclos: "\<forall>x\<in>\<pi> ` ?NF. \<forall>y\<in>\<pi> ` ?NF. mulG x y \<in> \<pi> ` ?NF"
      proof (intro ballI)
        fix px py assume "px \<in> \<pi> ` ?NF" "py \<in> \<pi> ` ?NF"
        then obtain x y where hx: "x \<in> ?NF" "px = \<pi> x" and hy: "y \<in> ?NF" "py = \<pi> y"
          by (by100 blast)
        have "\<pi> (mulF x y) = mulG (\<pi> x) (\<pi> y)"
          using hpi_hom hx(1) hy(1) hNF_sub unfolding top1_group_hom_on_def by (by100 blast)
        hence "mulG px py = \<pi> (mulF x y)" using hx(2) hy(2) by (by100 simp)
        moreover have "mulF x y \<in> ?NF"
          using hNF_grp hx(1) hy(1) unfolding top1_is_group_on_def by (by100 blast)
        ultimately show "mulG px py \<in> \<pi> ` ?NF" by (by100 force)
      qed
      \<comment> \<open>Inverse: invgG(\<pi>(x)) = \<pi>(invgF(x)) \<in> \<pi>([F,F]).\<close>
      have hinv: "\<forall>x\<in>\<pi> ` ?NF. invgG x \<in> \<pi> ` ?NF"
      proof (intro ballI)
        fix px assume "px \<in> \<pi> ` ?NF"
        then obtain x where hx: "x \<in> ?NF" "px = \<pi> x" by (by100 blast)
        have hxF: "x \<in> F" using hx(1) hNF_sub by (by100 blast)
        have "invgG px = \<pi> (invgF x)"
          using hx(2) hom_preserves_inv[OF hF_grp hG_grp hpi_hom hxF] by (by100 simp)
        moreover have "invgF x \<in> ?NF"
          using hNF_grp hx(1) unfolding top1_is_group_on_def by (by100 blast)
        ultimately show "invgG px \<in> \<pi> ` ?NF" by (by100 force)
      qed
      \<comment> \<open>Group axioms (associativity, identity, inverse) from G restricted to image.\<close>
      have hassoc: "\<forall>x\<in>\<pi>`?NF. \<forall>y\<in>\<pi>`?NF. \<forall>z\<in>\<pi>`?NF.
          mulG (mulG x y) z = mulG x (mulG y z)"
        using hG_grp himage_sub unfolding top1_is_group_on_def by (by100 blast)
      have hid: "\<forall>x\<in>\<pi>`?NF. mulG eG x = x \<and> mulG x eG = x"
        using hG_grp himage_sub unfolding top1_is_group_on_def by (by100 blast)
      have hinvax: "\<forall>x\<in>\<pi>`?NF. mulG (invgG x) x = eG \<and> mulG x (invgG x) = eG"
        using hG_grp himage_sub unfolding top1_is_group_on_def by (by100 blast)
      show ?thesis unfolding top1_is_group_on_def
        using heG_im hclos hinv hassoc hid hinvax by (by100 blast)
    qed
    have "top1_subgroup_generated_on G mulG eG invgG
        {top1_group_commutator_on mulG invgG g h |g h. g \<in> G \<and> h \<in> G}
      \<subseteq> \<pi> ` ?NF"
      by (rule subgroup_generated_minimal[OF hcomms_in_image himage_sub himage_grp])
    thus ?thesis unfolding top1_commutator_subgroup_on_def by (by100 blast)
  qed
  have hpi_comm2: "\<pi> ` ?NF \<subseteq> ?NG"
  proof -
    \<comment> \<open>G/[G,G] is abelian, so [G,G] \<subseteq> ker of the projection G \<rightarrow> G/[G,G].
       Equivalently, [F,F] maps into ker of F \<rightarrow> G \<rightarrow> G/[G,G] which contains [G,G].\<close>
    \<comment> \<open>More directly: the image of [F,F] under any hom to any group lands in [G,G]
       because hom preserves commutators.\<close>
    have hNG_normal: "top1_normal_subgroup_on G mulG eG invgG ?NG"
      by (rule commutator_subgroup_is_normal[OF hG_grp])
    have hNG_sub: "?NG \<subseteq> G" using hNG_normal unfolding top1_normal_subgroup_on_def by (by100 blast)
    have hHG_abel: "top1_is_abelian_group_on ?HG ?mulHG ?eHG
        (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g)))"
      using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
    have hphiG_hom: "top1_group_hom_on G mulG ?HG ?mulHG ?\<phi>G"
      using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
    \<comment> \<open>\<phi>G \<circ> \<pi> maps [F,F] into ker(\<phi>G) = [G,G] because G/[G,G] is abelian.\<close>
    have hj_hom: "top1_group_hom_on F mulF ?HG ?mulHG (\<lambda>f. ?\<phi>G (\<pi> f))"
    proof -
      show ?thesis unfolding top1_group_hom_on_def
      proof (intro conjI ballI)
        fix f assume hf: "f \<in> F"
        have "\<pi> f \<in> G" using hpi_hom hf unfolding top1_group_hom_on_def by (by100 blast)
        thus "?\<phi>G (\<pi> f) \<in> ?HG" using hphiG_hom unfolding top1_group_hom_on_def by (by100 blast)
      next
        fix f1 f2 assume hf1: "f1 \<in> F" and hf2: "f2 \<in> F"
        have h1: "\<pi> f1 \<in> G" using hpi_hom hf1 unfolding top1_group_hom_on_def by (by100 blast)
        have h2: "\<pi> f2 \<in> G" using hpi_hom hf2 unfolding top1_group_hom_on_def by (by100 blast)
        have "\<pi> (mulF f1 f2) = mulG (\<pi> f1) (\<pi> f2)"
          using hpi_hom hf1 hf2 unfolding top1_group_hom_on_def by (by100 blast)
        hence "?\<phi>G (\<pi> (mulF f1 f2)) = ?\<phi>G (mulG (\<pi> f1) (\<pi> f2))"
          by (by100 simp)
        also have "\<dots> = ?mulHG (?\<phi>G (\<pi> f1)) (?\<phi>G (\<pi> f2))"
          using hphiG_hom h1 h2 unfolding top1_group_hom_on_def by (by100 blast)
        finally show "?\<phi>G (\<pi> (mulF f1 f2)) = ?mulHG (?\<phi>G (\<pi> f1)) (?\<phi>G (\<pi> f2))" .
      qed
    qed
    have "?NF \<subseteq> top1_group_kernel_on F ?eHG (\<lambda>f. ?\<phi>G (\<pi> f))"
      by (rule Lemma_69_3_commutator_in_kernel[OF hF_grp hHG_abel hj_hom])
    hence "\<forall>f\<in>?NF. ?\<phi>G (\<pi> f) = ?eHG"
      unfolding top1_group_kernel_on_def by (by100 blast)
    hence "\<forall>f\<in>?NF. \<pi> f \<in> ?NG"
    proof (intro ballI)
      fix f assume hf: "f \<in> ?NF" and hall: "\<forall>f\<in>?NF. ?\<phi>G (\<pi> f) = ?eHG"
      have hfF: "f \<in> F" using hf commutator_subgroup_is_normal[OF hF_grp]
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      have hpif: "\<pi> f \<in> G" using hpi_hom hfF unfolding top1_group_hom_on_def by (by100 blast)
      have "?\<phi>G (\<pi> f) = ?eHG" using hall hf by (by100 blast)
      have "top1_group_kernel_on G ?eHG ?\<phi>G = ?NG"
        using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
      thus "\<pi> f \<in> ?NG" using \<open>?\<phi>G (\<pi> f) = ?eHG\<close> hpif
        unfolding top1_group_kernel_on_def by (by100 blast)
    qed
    thus ?thesis by (by100 blast)
  qed
  \<comment> \<open>Step B: ker(j) = [F,F].\<close>
  let ?j = "\<lambda>f. ?\<phi>G (\<pi> f)"
  have hker_j: "top1_group_kernel_on F ?eHG ?j = ?NF"
  proof (rule set_eqI, rule iffI)
    \<comment> \<open>\<supseteq>: f \<in> [F,F] \<Longrightarrow> \<pi>(f) \<in> [G,G] \<Longrightarrow> \<phi>G(\<pi>(f)) = eHG.\<close>
    fix f assume "f \<in> ?NF"
    hence "\<pi> f \<in> ?NG" using hpi_comm2 by (by100 blast)
    hence "?\<phi>G (\<pi> f) = ?eHG"
      using habel_G unfolding top1_is_abelianization_of_def top1_group_kernel_on_def
      by (by100 blast)
    moreover have "f \<in> F"
    proof -
      have "?NF \<subseteq> F" using commutator_subgroup_is_normal[OF hF_grp]
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      thus ?thesis using \<open>f \<in> ?NF\<close> by (by100 blast)
    qed
    ultimately show "f \<in> top1_group_kernel_on F ?eHG ?j"
      unfolding top1_group_kernel_on_def by (by100 blast)
  next
    \<comment> \<open>\<subseteq>: f \<in> ker(j) \<Longrightarrow> \<pi>(f) \<in> [G,G] = \<pi>([F,F]).
       Pick c \<in> [F,F] with \<pi>(c) = \<pi>(f). Then f\<cdot>c\<inverse> \<in> ker(\<pi>) \<subseteq> [F,F].
       Hence f = (f\<cdot>c\<inverse>)\<cdot>c \<in> [F,F]\<cdot>[F,F] = [F,F].\<close>
    fix f assume hf: "f \<in> top1_group_kernel_on F ?eHG ?j"
    hence hfF: "f \<in> F" and hfker: "?\<phi>G (\<pi> f) = ?eHG"
      unfolding top1_group_kernel_on_def by (by100 blast)+
    \<comment> \<open>\<pi>(f) \<in> [G,G] (from \<phi>G(\<pi>(f)) = eHG and ker(\<phi>G) = [G,G]).\<close>
    have hpif_NG: "\<pi> f \<in> ?NG"
    proof -
      have "top1_group_kernel_on G ?eHG ?\<phi>G = ?NG"
        using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
      moreover have "\<pi> f \<in> G" using hpi_hom hfF unfolding top1_group_hom_on_def by (by100 blast)
      ultimately show ?thesis using hfker unfolding top1_group_kernel_on_def by (by100 blast)
    qed
    \<comment> \<open>Pick c \<in> [F,F] with \<pi>(c) = \<pi>(f).\<close>
    have "\<pi> f \<in> \<pi> ` ?NF" using hpif_NG hpi_comm by (by100 blast)
    then obtain c where hc: "c \<in> ?NF" "\<pi> c = \<pi> f" by (by100 auto)
    \<comment> \<open>f\<cdot>c\<inverse> \<in> ker(\<pi>).\<close>
    have hcF: "c \<in> F" using hc(1) commutator_subgroup_is_normal[OF hF_grp]
      unfolding top1_normal_subgroup_on_def by (by100 blast)
    have hinvc: "invgF c \<in> F" using hF_grp hcF unfolding top1_is_group_on_def by (by100 blast)
    have hfc: "mulF f (invgF c) \<in> F" using hF_grp hfF hinvc
      unfolding top1_is_group_on_def by (by100 blast)
    have "\<pi> (mulF f (invgF c)) = mulG (\<pi> f) (invgG (\<pi> c))"
    proof -
      have "\<pi> (mulF f (invgF c)) = mulG (\<pi> f) (\<pi> (invgF c))"
        using hpi_hom hfF hinvc unfolding top1_group_hom_on_def by (by100 blast)
      moreover have "\<pi> (invgF c) = invgG (\<pi> c)"
        by (rule hom_preserves_inv[OF hF_grp hG_grp hpi_hom hcF])
      ultimately show ?thesis by (by100 simp)
    qed
    also have "mulG (\<pi> f) (invgG (\<pi> c)) = mulG (\<pi> f) (invgG (\<pi> f))"
      using hc(2) by (by100 simp)
    also have "\<dots> = eG" using hG_grp hpi_hom hfF
      unfolding top1_group_hom_on_def top1_is_group_on_def by (by100 blast)
    finally have "mulF f (invgF c) \<in> top1_group_kernel_on F eG \<pi>"
      unfolding top1_group_kernel_on_def using hfc by (by100 blast)
    hence "mulF f (invgF c) \<in> ?NF" using hker_sub_comm by (by100 blast)
    \<comment> \<open>f = (f\<cdot>c\<inverse>)\<cdot>c \<in> [F,F].\<close>
    have "f = mulF (mulF f (invgF c)) c"
    proof -
      have "mulF (mulF f (invgF c)) c = mulF f (mulF (invgF c) c)"
        using hF_grp hfF hinvc hcF unfolding top1_is_group_on_def by (by100 blast)
      also have "mulF (invgF c) c = eF"
        using hF_grp hcF unfolding top1_is_group_on_def by (by100 blast)
      also have "mulF f eF = f"
        using hF_grp hfF unfolding top1_is_group_on_def by (by100 blast)
      finally show ?thesis by (by100 simp)
    qed
    moreover have "mulF (mulF f (invgF c)) c \<in> ?NF"
    proof -
      have hNF_grp: "top1_is_group_on ?NF mulF eF invgF"
        using commutator_subgroup_is_normal[OF hF_grp]
        unfolding top1_normal_subgroup_on_def by (by100 blast)
      have "\<forall>x\<in>?NF. \<forall>y\<in>?NF. mulF x y \<in> ?NF"
        using hNF_grp unfolding top1_is_group_on_def by (by100 blast)
      thus ?thesis using \<open>mulF f (invgF c) \<in> ?NF\<close> hc(1) by (by100 blast)
    qed
    ultimately show "f \<in> ?NF" by (by100 simp)
  qed
  \<comment> \<open>Step C: Apply first iso theorem: F/[F,F] \<cong> G/[G,G].\<close>
  \<comment> \<open>Then transfer free abelian from F/[F,F] (via Theorem 69.4) to G/[G,G].\<close>
  \<comment> \<open>Step C1: j = \<phi>G \<circ> \<pi> is a surjective hom with kernel [F,F].\<close>
  let ?j = "\<lambda>f. ?\<phi>G (\<pi> f)"
  have hj_hom: "top1_group_hom_on F mulF ?HG ?mulHG ?j"
  proof -
    have hphiG_hom: "top1_group_hom_on G mulG ?HG ?mulHG ?\<phi>G"
      using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
    show ?thesis unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix f assume hf: "f \<in> F"
      have "\<pi> f \<in> G" using hpi_hom hf unfolding top1_group_hom_on_def by (by100 blast)
      thus "?j f \<in> ?HG" using hphiG_hom unfolding top1_group_hom_on_def by (by100 blast)
    next
      fix f1 f2 assume hf1: "f1 \<in> F" and hf2: "f2 \<in> F"
      have h1: "\<pi> f1 \<in> G" using hpi_hom hf1 unfolding top1_group_hom_on_def by (by100 blast)
      have h2: "\<pi> f2 \<in> G" using hpi_hom hf2 unfolding top1_group_hom_on_def by (by100 blast)
      have "\<pi> (mulF f1 f2) = mulG (\<pi> f1) (\<pi> f2)"
        using hpi_hom hf1 hf2 unfolding top1_group_hom_on_def by (by100 blast)
      hence "?j (mulF f1 f2) = ?\<phi>G (mulG (\<pi> f1) (\<pi> f2))" by (by100 simp)
      also have "\<dots> = ?mulHG (?j f1) (?j f2)"
        using hphiG_hom h1 h2 unfolding top1_group_hom_on_def by (by100 blast)
      finally show "?j (mulF f1 f2) = ?mulHG (?j f1) (?j f2)" .
    qed
  qed
  have hj_surj: "?j ` F = ?HG"
  proof -
    have "?j ` F = ?\<phi>G ` (\<pi> ` F)" by (by100 auto)
    also have "\<pi> ` F = G" by (rule hpi_surj)
    also have "?\<phi>G ` G = ?HG"
      using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
    finally show ?thesis .
  qed
  have hNF_normal: "top1_normal_subgroup_on F mulF eF invgF ?NF"
    by (rule commutator_subgroup_is_normal[OF hF_grp])
  have hHG_grp: "top1_is_group_on ?HG ?mulHG ?eHG
      (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g)))"
    using habel_G unfolding top1_is_abelianization_of_def top1_is_abelian_group_on_def
    by (by100 blast)
  \<comment> \<open>Step C2: By first iso theorem: G/[G,G] \<cong> F/[F,F].\<close>
  have hiso: "top1_groups_isomorphic_on ?HG ?mulHG
      (top1_quotient_group_carrier_on F mulF ?NF)
      (top1_quotient_group_mul_on mulF)"
    by (rule first_isomorphism_theorem[OF hF_grp hNF_normal hHG_grp hj_hom hj_surj hker_j])
  \<comment> \<open>Step C3: F/[F,F] is free abelian on S (Theorem 69.4).\<close>
  \<comment> \<open>Step C4: Transfer via iso G/[G,G] \<cong> F/[F,F] + free\_abelian\_invariant\_under\_iso.\<close>
  \<comment> \<open>Step C3-C4: F/[F,F] is free abelian on S. Transfer to G/[G,G] via iso.\<close>
  have hfab_F: "\<exists>\<iota>HF. top1_is_free_abelian_group_full_on
      (top1_quotient_group_carrier_on F mulF ?NF) (top1_quotient_group_mul_on mulF)
      (top1_group_coset_on F mulF ?NF eF)
      (\<lambda>C. top1_group_coset_on F mulF ?NF (invgF (SOME g. g \<in> F \<and>
          C = top1_group_coset_on F mulF ?NF g))) \<iota>HF S"
  proof -
    \<comment> \<open>Theorem\_69\_4 gives some (HF :: 'g set set) that's free abelian on S.\<close>
    show ?thesis by (rule Theorem_69_4_concrete_free_abelian[OF hF_free])
  qed
  \<comment> \<open>The iso gives G/[G,G] \<cong> F/[F,F]. Transfer free abelian.\<close>
  from hfab_F obtain \<iota>HF where hfa_F:
    "top1_is_free_abelian_group_full_on
      (top1_quotient_group_carrier_on F mulF ?NF) (top1_quotient_group_mul_on mulF)
      (top1_group_coset_on F mulF ?NF eF)
      (\<lambda>C. top1_group_coset_on F mulF ?NF (invgF (SOME g. g \<in> F \<and>
          C = top1_group_coset_on F mulF ?NF g))) \<iota>HF S"
    by (by100 blast)
  \<comment> \<open>G/[G,G] is abelian.\<close>
  have hHG_abel: "top1_is_abelian_group_on ?HG ?mulHG ?eHG
      (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g)))"
    using habel_G unfolding top1_is_abelianization_of_def by (by100 blast)
  \<comment> \<open>Use isomorphism + free\_abelian\_invariant\_under\_iso.\<close>
  from hiso obtain fiso where hfiso:
    "top1_group_iso_on ?HG ?mulHG
      (top1_quotient_group_carrier_on F mulF ?NF) (top1_quotient_group_mul_on mulF) fiso"
    unfolding top1_groups_isomorphic_on_def by (by100 blast)
  \<comment> \<open>The inverse iso transfers free abelian from F/[F,F] to G/[G,G].\<close>
  \<comment> \<open>Reverse iso: F/[F,F] \<cong> G/[G,G].\<close>
  have hHG_grp2: "top1_is_group_on ?HG ?mulHG ?eHG
      (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g)))"
    using hHG_abel unfolding top1_is_abelian_group_on_def by (by100 blast)
  have hFN_grp: "top1_is_group_on (top1_quotient_group_carrier_on F mulF ?NF)
      (top1_quotient_group_mul_on mulF)
      (top1_group_coset_on F mulF ?NF eF)
      (\<lambda>C. top1_group_coset_on F mulF ?NF (invgF (SOME g. g \<in> F \<and>
          C = top1_group_coset_on F mulF ?NF g)))"
    by (rule quotient_group_is_group[OF hF_grp hNF_normal])
  have hrev_iso: "top1_groups_isomorphic_on
      (top1_quotient_group_carrier_on F mulF ?NF) (top1_quotient_group_mul_on mulF)
      ?HG ?mulHG"
    by (rule top1_groups_isomorphic_on_sym[OF hiso hHG_grp2 hFN_grp])
  \<comment> \<open>Transfer free abelian from F/[F,F] to G/[G,G] via reverse iso.\<close>
  have hFN_abel: "top1_is_abelian_group_on (top1_quotient_group_carrier_on F mulF ?NF)
      (top1_quotient_group_mul_on mulF)
      (top1_group_coset_on F mulF ?NF eF)
      (\<lambda>C. top1_group_coset_on F mulF ?NF (invgF (SOME g. g \<in> F \<and>
          C = top1_group_coset_on F mulF ?NF g)))"
  proof -
    have h_ab_F: "top1_is_abelianization_of
        (top1_quotient_group_carrier_on F mulF ?NF) (top1_quotient_group_mul_on mulF)
        (top1_group_coset_on F mulF ?NF eF)
        (\<lambda>C. top1_group_coset_on F mulF ?NF (invgF (SOME g. g \<in> F \<and>
            C = top1_group_coset_on F mulF ?NF g)))
        F mulF eF invgF (\<lambda>g. top1_group_coset_on F mulF ?NF g)"
      by (rule abelianization_concrete[OF hF_grp])
    thus ?thesis unfolding top1_is_abelianization_of_def by (by100 blast)
  qed
  from hrev_iso obtain f_rev where hf_rev:
    "top1_group_iso_on (top1_quotient_group_carrier_on F mulF ?NF)
      (top1_quotient_group_mul_on mulF) ?HG ?mulHG f_rev"
    unfolding top1_groups_isomorphic_on_def by (by100 blast)
  have "\<exists>\<iota>'. top1_is_free_abelian_group_full_on ?HG ?mulHG ?eHG
      (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g))) \<iota>' S"
    by (rule free_abelian_invariant_under_iso[OF hfa_F hf_rev hHG_abel])
  then obtain \<iota>H where hfa_G: "top1_is_free_abelian_group_full_on ?HG ?mulHG ?eHG
      (\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g))) \<iota>H S"
    by (by100 blast)
  show ?thesis
    apply (rule exI[of _ ?HG], rule exI[of _ ?mulHG], rule exI[of _ ?eHG])
    apply (rule exI[of _ "\<lambda>C. top1_group_coset_on G mulG ?NG (invgG (SOME g. g \<in> G \<and> C = ?\<phi>G g))"])
    apply (rule exI[of _ ?\<phi>G], rule exI[of _ \<iota>H])
    using habel_G hfa_G by (by100 blast)
qed


text \<open>Rank of a finitely generated free group is invariant.\<close>
lemma free_group_rank_invariant_finite:
  assumes "top1_is_free_group_full_on G mul e invg \<iota>1 S1"
      and "top1_is_free_group_full_on G mul e invg \<iota>2 S2"
      and "finite S1" and "finite S2"
  shows "card S1 = card S2"
proof -
  \<comment> \<open>Munkres: Abelianize G. G/[G,G] is free abelian on both p(S1) and p(S2).
     By Theorem 67.8, |p(S1)| = |p(S2)|. Since p is injective on generators
     of a free group, |S1| = |p(S1)| and |S2| = |p(S2)|.\<close>
  \<comment> \<open>Proof: Abelianize G via Theorem 69.4. G/[G,G] is free abelian
     on both p(S1) and p(S2). Theorem 67.8 gives |S1| = |S2|.
     Depends on Theorem\_69\_4 (defined later) and Theorem\_67\_8.\<close>
  \<comment> \<open>Munkres Corollary 69.5: Abelianize G via Theorem 69.4. G/[G,G] is free abelian
     on S1 (from first free group structure) and on S2 (from second).
     By Theorem 67.8, |S1| = |S2|.\<close>
  \<comment> \<open>Step 1: Get the concrete abelianization = G/[G,G].\<close>
  have hG: "top1_is_group_on G mul e invg"
    using assms(1) unfolding top1_is_free_group_full_on_def by (by100 blast)
  let ?N = "top1_commutator_subgroup_on G mul e invg"
  let ?H = "top1_quotient_group_carrier_on G mul ?N"
  let ?mulH = "top1_quotient_group_mul_on mul"
  let ?eH = "top1_group_coset_on G mul ?N e"
  let ?invgH = "\<lambda>C. top1_group_coset_on G mul ?N (invg (SOME g. g \<in> G \<and> C = top1_group_coset_on G mul ?N g))"
  \<comment> \<open>Step 2: Apply Theorem 69.4 to get free abelian on S1.\<close>
  let ?\<phi> = "\<lambda>g. top1_group_coset_on G mul ?N g"
  let ?\<iota>H1 = "\<lambda>s. ?\<phi> (\<iota>1 s)"
  let ?\<iota>H2 = "\<lambda>s. ?\<phi> (\<iota>2 s)"
  \<comment> \<open>Both Theorem\_69\_4 applications return the same concrete H, mulH, eH, invgH.\<close>
  have hfab1: "\<exists>\<iota>H. top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH \<iota>H S1"
    by (rule Theorem_69_4_concrete_free_abelian[OF assms(1)])
  have hfab2: "\<exists>\<iota>H. top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH \<iota>H S2"
    by (rule Theorem_69_4_concrete_free_abelian[OF assms(2)])
  \<comment> \<open>Step 3: Both are free abelian on the same H. Apply Theorem 67.8.\<close>
  from hfab1 obtain \<iota>H1 where hfa1: "top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH \<iota>H1 S1"
    by (by100 blast)
  from hfab2 obtain \<iota>H2 where hfa2: "top1_is_free_abelian_group_full_on ?H ?mulH ?eH ?invgH \<iota>H2 S2"
    by (by100 blast)
  from Theorem_67_8_rank_unique[OF hfa1 hfa2 assms(3,4)]
  obtain f where "bij_betw f S1 S2" by (by100 blast)
  thus "card S1 = card S2" using bij_betw_same_card by (by100 blast)
qed




\<comment> \<open>Helper: Z/nZ is the quotient of Z by the subgroup nZ.
   More precisely: the quotient of (UNIV::int set, +) by the normal subgroup
   generated by {int n} is isomorphic to (top1_Zn_group n, top1_Zn_mul n).\<close>
lemma Z_quotient_nZ_iso:
  assumes "n \<ge> 1"
  shows "top1_groups_isomorphic_on
      (top1_quotient_group_carrier_on (UNIV::int set) (+)
         (top1_normal_subgroup_generated_on (UNIV::int set) (+) (0::int) uminus {int n}))
      (top1_quotient_group_mul_on (+))
      (top1_Zn_group n) (top1_Zn_mul n)"
proof -
  \<comment> \<open>Step 1: The normal subgroup generated by {n} in (Z,+) is nZ = {k*n | k}.\<close>
  let ?nZ = "top1_normal_subgroup_generated_on (UNIV::int set) (+) (0::int) uminus {int n}"
  have hnZ_eq: "?nZ = {k * int n | k. True}"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> ?nZ"
    \<comment> \<open>?nZ \<subseteq> every normal subgroup containing {n}. nZ is such a subgroup.\<close>
    have hnZ_normal: "top1_normal_subgroup_on (UNIV::int set) (+) 0 uminus {k * int n | k. True}"
      unfolding top1_normal_subgroup_on_def
    proof (intro conjI)
      show "{k * int n |k. True} \<subseteq> (UNIV::int set)" by (by100 blast)
      show "top1_is_group_on {k * int n |k. True} (+) 0 uminus"
        unfolding top1_is_group_on_def
      proof (intro conjI)
        show "(0::int) \<in> {k * int n |k. True}"
        proof -
          have "(0::int) = (0::int) * int n" by (by100 simp)
          thus ?thesis by (by100 blast)
        qed
        show "\<forall>x\<in>{k * int n |k. True}. \<forall>y\<in>{k * int n |k. True}. x + y \<in> {k * int n |k. True}"
        proof (intro ballI)
          fix x y :: int assume "x \<in> {k * int n |k. True}" "y \<in> {k * int n |k. True}"
          then obtain kx ky where "x = kx * int n" "y = ky * int n" by (by100 blast)
          hence "x + y = (kx + ky) * int n" using distrib_right[of kx ky "int n"] by (by100 simp)
          thus "x + y \<in> {k * int n |k. True}" by (by100 blast)
        qed
        show "\<forall>x\<in>{k * int n |k. True}. uminus x \<in> {k * int n |k. True}"
        proof (intro ballI)
          fix x :: int assume "x \<in> {k * int n |k. True}"
          then obtain kx where "x = kx * int n" by (by100 blast)
          hence "uminus x = (-kx) * int n" by (by100 simp)
          thus "uminus x \<in> {k * int n |k. True}" by (by100 blast)
        qed
        show "\<forall>x\<in>{k * int n |k. True}. \<forall>y\<in>{k * int n |k. True}.
            \<forall>z\<in>{k * int n |k. True}. x + y + z = x + (y + z)" by (by100 simp)
        show "\<forall>x\<in>{k * int n |k. True}. (0::int) + x = x \<and> x + 0 = x" by (by100 simp)
        show "\<forall>x\<in>{k * int n |k. True}. uminus x + x = (0::int) \<and> x + uminus x = 0" by (by100 simp)
      qed
      show "\<forall>g\<in>(UNIV::int set). \<forall>h\<in>{k * int n |k. True}. g + h + uminus g \<in> {k * int n |k. True}"
      proof (intro ballI)
        fix g h :: int assume "g \<in> (UNIV::int set)" "h \<in> {k * int n |k. True}"
        then obtain kh where "h = kh * int n" by (by100 blast)
        hence "g + h + uminus g = kh * int n" by (by100 simp)
        thus "g + h + uminus g \<in> {k * int n |k. True}" by (by100 blast)
      qed
    qed
    have "{int n} \<subseteq> {k * int n |k. True}"
    proof -
      have "int n = (1::int) * int n" by (by100 simp)
      thus ?thesis by (by100 blast)
    qed
    hence "?nZ \<subseteq> {k * int n |k. True}"
      unfolding top1_normal_subgroup_generated_on_def using hnZ_normal by (by100 blast)
    thus "x \<in> {k * int n |k. True}" using \<open>x \<in> ?nZ\<close> by (by100 blast)
  next
    fix x assume "x \<in> {k * int n |k. True}"
    then obtain k :: int where hk: "x = k * int n" by (by100 blast)
    \<comment> \<open>n \<in> ?nZ and ?nZ is a group, so k*n \<in> ?nZ by closure.\<close>
    have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
      using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
        top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 simp)
    have hn_in_nZ: "int n \<in> ?nZ"
    proof -
      have "{int n} \<subseteq> ?nZ"
        unfolding top1_normal_subgroup_generated_on_def by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    have hN_sub: "?nZ \<subseteq> (UNIV::int set)" by (by100 blast)
    have hN_grp: "top1_is_group_on ?nZ (+) (0::int) uminus"
      using normal_subgroup_generated_is_normal[OF hZ_grp, of "{int n}"]
      unfolding top1_normal_subgroup_on_def by (by100 blast)
    \<comment> \<open>Induction: k*n \<in> ?nZ for all k.\<close>
    have "k * int n \<in> ?nZ"
    proof (cases "k \<ge> 0")
      case True
      have "\<forall>j::int. j \<ge> 0 \<longrightarrow> j * int n \<in> ?nZ"
      proof (rule allI, rule impI)
        fix j :: int assume "j \<ge> 0"
        then obtain jn :: nat where "j = int jn" using nonneg_int_cases by (by100 blast)
        show "j * int n \<in> ?nZ"
        proof -
          have "int jn * int n \<in> ?nZ"
          proof (induct jn)
            case 0
            have "(0::int) \<in> ?nZ" using hN_grp unfolding top1_is_group_on_def by (by100 blast)
            thus ?case by (by100 simp)
          next
            case (Suc jn)
            have hS: "int (Suc jn) * int n = int jn * int n + int n"
            proof -
              have "int (Suc jn) = 1 + int jn" by (by100 simp)
              hence "int (Suc jn) * int n = (1 + int jn) * int n" by (by100 simp)
              also have "\<dots> = 1 * int n + int jn * int n"
                using distrib_right[of 1 "int jn" "int n"] by (by100 simp)
              finally show ?thesis by (by100 simp)
            qed
            have "int jn * int n + int n \<in> ?nZ"
            proof -
              have "\<forall>x\<in>?nZ. \<forall>y\<in>?nZ. x + y \<in> ?nZ"
                using hN_grp unfolding top1_is_group_on_def by (by100 blast)
              thus ?thesis using Suc hn_in_nZ by (by100 blast)
            qed
            thus ?case using hS by (by100 simp)
          qed
          thus ?thesis using \<open>j = int jn\<close> by (by100 simp)
        qed
      qed
      thus ?thesis using True by (by100 blast)
    next
      case False
      hence "k < 0" by (by100 simp)
      hence "-k > 0" by (by100 simp)
      have "(-k) * int n \<in> ?nZ"
      proof -
        have "-k \<ge> 0" using \<open>-k > 0\<close> by (by100 simp)
        then obtain jn :: nat where "-k = int jn" using nonneg_int_cases by (by100 blast)
        have "int jn * int n \<in> ?nZ"
        proof (induct jn)
          case 0 thus ?case using hN_grp unfolding top1_is_group_on_def by (by100 simp)
        next
          case (Suc jn)
          have "int (Suc jn) * int n = int jn * int n + int n"
          proof -
            have "int (Suc jn) = 1 + int jn" by (by100 simp)
            hence "int (Suc jn) * int n = (1 + int jn) * int n" by (by100 simp)
            also have "\<dots> = 1 * int n + int jn * int n"
              using distrib_right[of 1 "int jn" "int n"] by (by100 simp)
            finally show ?thesis by (by100 simp)
          qed
          have "int jn * int n + int n \<in> ?nZ"
          proof -
            have "\<forall>x\<in>?nZ. \<forall>y\<in>?nZ. x + y \<in> ?nZ"
              using hN_grp unfolding top1_is_group_on_def by (by100 blast)
            thus ?thesis using Suc hn_in_nZ by (by100 blast)
          qed
          thus ?case using \<open>int (Suc jn) * int n = int jn * int n + int n\<close> by (by100 simp)
        qed
        thus ?thesis using \<open>-k = int jn\<close> by (by100 simp)
      qed
      hence "uminus ((-k) * int n) \<in> ?nZ" using hN_grp unfolding top1_is_group_on_def by (by100 blast)
      moreover have "uminus ((-k) * int n) = k * int n" by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    thus "x \<in> ?nZ" using hk by (by100 simp)
  qed
  \<comment> \<open>Step 2: Define the quotient map \<phi>: Z \<rightarrow> Z/nZ by \<phi>(k) = k mod n.\<close>
  let ?\<phi> = "\<lambda>k::int. k mod int n"
  \<comment> \<open>Step 3: \<phi> is a surjective group homomorphism with kernel nZ.\<close>
  have hphi_hom: "\<forall>a::int. \<forall>b::int. ?\<phi> (a + b) = top1_Zn_mul n (?\<phi> a) (?\<phi> b)"
    unfolding top1_Zn_mul_def
  proof (intro allI)
    fix a b :: int
    show "(a + b) mod int n = (a mod int n + b mod int n) mod int n"
      using mod_add_eq[of a "int n" b] by (by100 simp)
  qed
  have hphi_surj: "?\<phi> ` (UNIV::int set) = top1_Zn_group n"
    unfolding top1_Zn_group_def
  proof (rule equalityI)
    show "(\<lambda>k::int. k mod int n) ` UNIV \<subseteq> {0..<int n}"
      using assms by (by100 auto)
    show "{0..<int n} \<subseteq> (\<lambda>k::int. k mod int n) ` UNIV"
    proof
      fix x :: int assume hx: "x \<in> {0..<int n}"
      hence hxmod: "x mod int n = x" using assms by (by100 auto)
      show "x \<in> (\<lambda>k. k mod int n) ` UNIV"
        apply (rule image_eqI[of _ _ x])
        using hxmod apply (by100 simp)
        apply (by100 simp)
        done
    qed
  qed
  have hphi_ker: "{k::int. ?\<phi> k = 0} = ?nZ"
    unfolding hnZ_eq
  proof (rule set_eqI, rule iffI)
    fix k :: int assume "k \<in> {k. k mod int n = 0}"
    hence "k mod int n = 0" by (by100 blast)
    hence "int n dvd k"
    proof -
      have "k div int n * int n + k mod int n = k" by (rule div_mult_mod_eq)
      hence "k = k div int n * int n" using \<open>k mod int n = 0\<close> by (by100 simp)
      hence "k = int n * (k div int n)" using mult.commute[of "k div int n" "int n"] by (by100 simp)
      thus ?thesis unfolding dvd_def by (by100 blast)
    qed
    then obtain j where "k = int n * j" unfolding dvd_def by (by100 blast)
    hence "k = j * int n" using mult.commute[of "int n" j] by (by100 simp)
    thus "k \<in> {k * int n |k. True}" by (by100 blast)
  next
    fix k :: int assume "k \<in> {k * int n |k. True}"
    then obtain j where hk: "k = j * int n" by (by100 blast)
    hence "k mod int n = 0" using assms by (by100 simp)
    thus "k \<in> {k. k mod int n = 0}" by (by100 blast)
  qed
  \<comment> \<open>Step 4: By first isomorphism theorem: Z/nZ \<cong> im(\<phi>) = Z_n.\<close>
  have hZ_grp: "top1_is_group_on (UNIV::int set) (+) (0::int) uminus"
    using top1_Z_is_abelian_group unfolding top1_is_abelian_group_on_def
      top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def by (by100 simp)
  have hN_normal: "top1_normal_subgroup_on (UNIV::int set) (+) (0::int) uminus ?nZ"
    by (rule normal_subgroup_generated_is_normal[OF hZ_grp]) (by100 simp)
  have hZn_grp: "top1_is_group_on (top1_Zn_group n) (top1_Zn_mul n)
      (0::int) (top1_Zn_invg n)"
    using top1_Zn_is_abelian_group[OF assms] unfolding top1_is_abelian_group_on_def top1_Zn_id_def
    by (by100 blast)
  have hphi_hom_on: "top1_group_hom_on (UNIV::int set) (+) (top1_Zn_group n) (top1_Zn_mul n) ?\<phi>"
    unfolding top1_group_hom_on_def
  proof (intro conjI ballI)
    fix x :: int show "?\<phi> x \<in> top1_Zn_group n"
      unfolding top1_Zn_group_def using assms by (by100 auto)
    fix y :: int show "?\<phi> (x + y) = top1_Zn_mul n (?\<phi> x) (?\<phi> y)"
      using hphi_hom by (by100 blast)
  qed
  have hphi_ker_on: "top1_group_kernel_on (UNIV::int set) (0::int) ?\<phi> = ?nZ"
  proof -
    have "top1_group_kernel_on (UNIV::int set) (0::int) ?\<phi> = {k::int. ?\<phi> k = 0} \<inter> UNIV"
      unfolding top1_group_kernel_on_def by (by100 blast)
    also have "\<dots> = {k::int. ?\<phi> k = 0}" by (by100 simp)
    also have "\<dots> = ?nZ" by (rule hphi_ker)
    finally show ?thesis .
  qed
  from first_isomorphism_theorem[OF hZ_grp hN_normal hZn_grp hphi_hom_on hphi_surj hphi_ker_on]
  show ?thesis
    by (rule top1_groups_isomorphic_on_sym[OF _ hZn_grp quotient_group_is_group[OF hZ_grp hN_normal]])
qed

text \<open>Bridge: compact in HOL Analysis equals top1\_compact\_on for R^2 subspaces.\<close>
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



text \<open>Polygon-to-disk homeomorphism: proved in PolygonDisk session (3794 lines, zero sorry).
  This wrapper adds the hno\_collinear assumption which the full proof requires.\<close>
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
      and hstrict_hp: "\<forall>i<n. \<forall>k<n. k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod n \<longrightarrow>
          cross2 (vx k - vx i, vy k - vy i)
              (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) < 0"
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
    \<and> (\<forall>i<n. \<forall>t\<in>I_set. \<psi> ((1-t) * vx i + t * vx (Suc i mod n),
                              (1-t) * vy i + t * vy (Suc i mod n))
        = (cos (2 * pi * (real i + t) / real n), sin (2 * pi * (real i + t) / real n)))"
proof -
  \<comment> \<open>Derive hno_collinear from strict half-plane condition.\<close>
  have hno_collinear: "\<forall>i<n. \<forall>j<n. j \<noteq> i \<longrightarrow> Suc i mod n \<noteq> j \<longrightarrow>
      PolygonDisk.cross2 (vx j - vx i, vy j - vy i) (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<noteq> 0"
    using hstrict_hp unfolding cross2_def PolygonDisk.cross2_def by (by5000 force)
  have hvert_hp': "\<forall>i<n. \<forall>k<n. PolygonDisk.cross2 (vx k - vx i, vy k - vy i)
      (vx (Suc i mod n) - vx i, vy (Suc i mod n) - vy i) \<le> 0"
    using hvert_hp unfolding cross2_def PolygonDisk.cross2_def by (by100 simp)
  from PolygonDisk.polygon_homeomorphic_to_disk_with_boundary[OF assms(1,2)
      hverts_in hP_hull hccw hvert_hp' hno_collinear]
  obtain \<psi> where h1: "top1_homeomorphism_on P
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P)
        top1_B2 top1_B2_topology \<psi>"
      and h2: "\<psi> ` (\<Union>i<n. {((1-t) * vx i + t * vx (Suc i mod n),
                     (1-t) * vy i + t * vy (Suc i mod n)) | t. t \<in> I_set})
        = top1_S1"
      and h3: "top1_homeomorphism_on
        (P - (\<Union>i<n. {((1-t) * vx i + t * vx (Suc i mod n),
                       (1-t) * vy i + t * vy (Suc i mod n)) | t. t \<in> I_set}))
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
           (P - (\<Union>i<n. {((1-t) * vx i + t * vx (Suc i mod n),
                          (1-t) * vy i + t * vy (Suc i mod n)) | t. t \<in> I_set})))
        (top1_B2 - top1_S1)
        (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
        \<psi>"
      and h4: "\<forall>i<n. \<forall>t\<in>I_set. \<psi> ((1-t) * vx i + t * vx (Suc i mod n),
                              (1-t) * vy i + t * vy (Suc i mod n))
        = (cos (2 * pi * (real i + t) / real n), sin (2 * pi * (real i + t) / real n))"
    by - (erule exE, erule conjE, erule conjE, erule conjE, rule that, assumption, assumption, assumption, assumption)
  show ?thesis
    apply (rule exI[of _ \<psi>])
    apply (intro conjI)
    using h1 apply (by100 blast)
    using h2 apply (by100 blast)
    using h3 apply (by100 blast)
    using h4 apply (by100 blast)
    done
qed
text \<open>Hausdorff property for scheme quotients. Following Munkres Theorem 74.1:
  the quotient map q: P \<rightarrow> X is a closed map (preimages of saturations are closed
  by finite edge image argument), and a closed quotient of a normal space is Hausdorff.\<close>
lemma scheme_quotient_hausdorff:
  assumes "top1_quotient_of_scheme_on X TX scheme"
      and "length scheme \<ge> 3"
  shows "is_hausdorff_on X TX"
proof -
  \<comment> \<open>Extract P, q, vx, vy from the scheme definition.\<close>
  obtain P q vx vy where
    hP: "top1_is_polygonal_region_on P (length scheme)" and
    hq: "top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q" and
    hverts: "\<forall>i<length scheme. (vx i, vy i) \<in> P" and
    hedge: "\<forall>i<length scheme. \<forall>j<length scheme.
        fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
           (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme))))" and
    hint: "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
          p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme)))
       \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')" and
    hno_extra: "\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
          q ((1-t) * vx i + t * vx (Suc i mod length scheme),
             (1-t) * vy i + t * vy (Suc i mod length scheme))
        = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
             (1-s) * vy j + s * vy (Suc j mod length scheme))
        \<longrightarrow> (i = j \<and> t = s)
          \<or> (fst (scheme!i) = fst (scheme!j) \<and>
             (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))"
    using assms(1)[unfolded top1_quotient_of_scheme_on_def] assms(2)
    by (elim conjE exE) (rule that, assumption+)
  let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
  let ?n = "length scheme"
  have hn_pos: "?n > 0" using assms(2) by (by100 linarith)
  have hX_strict: "is_topology_on_strict X TX"
    using assms(1) unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have hTX: "is_topology_on X TX"
    using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
  have hTP: "is_topology_on P ?TP" using hq unfolding top1_quotient_map_on_def by (by100 blast)
  have hq_cont: "top1_continuous_map_on P ?TP X TX q"
    using hq unfolding top1_quotient_map_on_def by (by100 blast)
  have hq_surj: "q ` P = X" using hq unfolding top1_quotient_map_on_def by (by5000 blast)
  have hq_maps: "\<forall>x\<in>P. q x \<in> X"
    using hq_cont unfolding top1_continuous_map_on_def by (by5000 blast)
  have hqm_prop: "\<forall>V. V \<subseteq> X \<longrightarrow> ({x \<in> P. q x \<in> V} \<in> ?TP \<longrightarrow> V \<in> TX)"
    using hq unfolding top1_quotient_map_on_def by (by100 blast)
  \<comment> \<open>Step 1: P is compact Hausdorff, hence normal.\<close>
  have hP_compact: "top1_compact_on P ?TP"
    by (rule polygonal_region_compact[OF hP assms(2)])
  have hR2_haus: "is_hausdorff_on (UNIV::(real\<times>real) set)
      (product_topology_on top1_open_sets top1_open_sets)"
    using top1_R2_is_hausdorff .
  have hP_haus: "is_hausdorff_on P ?TP"
    using hausdorff_subspace[OF hR2_haus] by (by100 blast)
  have hP_normal: "top1_normal_on P ?TP"
    using Theorem_32_3[OF hP_compact hP_haus] .
  \<comment> \<open>Step 2 (Munkres 74.1): q is a closed map.
     For closed C \<subseteq> P, preimg = {p \<in> P. q p \<in> q ` C} is closed because:
     preimg \<subseteq> C \<union> (finite union of images of C \<inter> edge under pasting maps).
     Interior points: by hint, p \<in> preimg \<and> p interior \<Rightarrow> p \<in> C.
     Boundary points: by hedge, pasted partners of C \<inter> edge_j lie on edge_i.
     Each pasting image is compact (continuous image of compact), hence closed.\<close>
  have hq_closed_map: "\<forall>C. closedin_on P ?TP C \<longrightarrow> closedin_on X TX (q ` C)"
  proof (intro allI impI)
    fix C assume hC: "closedin_on P ?TP C"
    have hC_sub: "C \<subseteq> P" using hC unfolding closedin_on_def by (by100 blast)
    define preimg where "preimg = {p \<in> P. q p \<in> q ` C}"
    \<comment> \<open>preimg is closed in P: it equals C \<union> finite union of edge images.\<close>
    have hpreimg_closed: "closedin_on P ?TP preimg"
    proof -
      \<comment> \<open>Munkres 74.1: preimg = C \<union> \<Union>_{(i,j) same label} paste(C \<inter> edge_j \<rightarrow> edge_i).
         Interior points: by hint, p \<in> preimg \<and> p not on any edge \<Rightarrow> p \<in> C.
         Edge points: by hedge, boundary pasting maps carry C \<inter> edge_j to edge_i.\<close>
      \<comment> \<open>Define edge pasting images.\<close>
      define edge where "edge i = {((1-t) * vx i + t * vx (Suc i mod ?n),
          (1-t) * vy i + t * vy (Suc i mod ?n)) | t::real. 0 \<le> t \<and> t \<le> 1}" for i
      define paste_img where "paste_img i j =
          (if fst (scheme!i) = fst (scheme!j) then
            (if snd (scheme!i) = snd (scheme!j)
             then (\<lambda>t. ((1-t) * vx i + t * vx (Suc i mod ?n),
                        (1-t) * vy i + t * vy (Suc i mod ?n)))
                  ` {t. 0 \<le> t \<and> t \<le> 1 \<and>
                       ((1-t) * vx j + t * vx (Suc j mod ?n),
                        (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C}
             else (\<lambda>t. (t * vx i + (1-t) * vx (Suc i mod ?n),
                        t * vy i + (1-t) * vy (Suc i mod ?n)))
                  ` {t. 0 \<le> t \<and> t \<le> 1 \<and>
                       ((1-t) * vx j + t * vx (Suc j mod ?n),
                        (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C})
           else {})" for i j
      \<comment> \<open>Edge points are in P (convex combination of vertices).
         Placed early so both hpreimg\_sub and hpaste\_sub can use them.\<close>
      have hedge_in_P0: "\<And>i t. (i::nat) < ?n \<Longrightarrow> (0::real) \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow>
          ((1-t) * vx i + t * vx (Suc i mod ?n),
           (1-t) * vy i + t * vy (Suc i mod ?n)) \<in> P"
      proof -
        fix i :: nat and t :: real
        assume hi: "i < ?n" and ht0: "0 \<le> t" and ht1: "t \<le> 1"
        have hvi: "(vx i, vy i) \<in> P" using hverts hi by (by100 blast)
        have hvi': "(vx (Suc i mod ?n), vy (Suc i mod ?n)) \<in> P"
        proof -
          have "Suc i mod ?n < ?n" using mod_less_divisor hn_pos by (by100 blast)
          thus ?thesis using hverts by (by100 blast)
        qed
        from polygonal_region_convex_combo[OF hP assms(2) hvi hvi' ht0 ht1]
        show "((1-t) * vx i + t * vx (Suc i mod ?n),
               (1-t) * vy i + t * vy (Suc i mod ?n)) \<in> P"
          by (by100 simp)
      qed
      have hedge_rev_in_P0: "\<And>i t. (i::nat) < ?n \<Longrightarrow> (0::real) \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow>
          (t * vx i + (1-t) * vx (Suc i mod ?n),
           t * vy i + (1-t) * vy (Suc i mod ?n)) \<in> P"
      proof -
        fix i :: nat and t :: real
        assume hi: "i < ?n" and ht0: "0 \<le> t" and ht1: "t \<le> 1"
        have h1: "0 \<le> 1 - t" using ht1 by (by100 linarith)
        have h2: "1 - t \<le> 1" using ht0 by (by100 linarith)
        have "((1 - (1-t)) * vx i + (1-t) * vx (Suc i mod ?n),
               (1 - (1-t)) * vy i + (1-t) * vy (Suc i mod ?n)) \<in> P"
          using hedge_in_P0[OF hi h1 h2] .
        moreover have "((1 - (1-t)) * vx i + (1-t) * vx (Suc i mod ?n),
               (1 - (1-t)) * vy i + (1-t) * vy (Suc i mod ?n))
             = (t * vx i + (1-t) * vx (Suc i mod ?n),
                t * vy i + (1-t) * vy (Suc i mod ?n))"
          by (by100 simp)
        ultimately show "(t * vx i + (1-t) * vx (Suc i mod ?n),
               t * vy i + (1-t) * vy (Suc i mod ?n)) \<in> P" by (by100 simp)
      qed
      \<comment> \<open>preimg \<subseteq> C \<union> \<Union>_{i<n,j<n} paste\_img i j: by hint + hedge.\<close>
      have hpreimg_sub: "preimg \<subseteq> C \<union> (\<Union>i<?n. \<Union>j<?n. paste_img i j)"
      proof (rule subsetI)
        fix p assume hp: "p \<in> preimg"
        hence "p \<in> P" "q p \<in> q ` C" unfolding preimg_def by (by100 blast)+
        then obtain c where hc: "c \<in> C" "q p = q c" by (by100 blast)
        have hc_P: "c \<in> P" using hc(1) hC_sub by (by100 blast)
        show "p \<in> C \<union> (\<Union>i<?n. \<Union>j<?n. paste_img i j)"
        proof (cases "p \<in> C")
          case True thus ?thesis by (by100 blast)
        next
          case False
          hence hpc: "p \<noteq> c" using hc(1) by (by100 blast)
          \<comment> \<open>p must be on some edge (otherwise hint gives p = c, contradiction).\<close>
          have "\<exists>i t. i < ?n \<and> t \<in> I_set \<and>
              p = ((1-t) * vx i + t * vx (Suc i mod ?n), (1-t) * vy i + t * vy (Suc i mod ?n))"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            hence "\<forall>i<?n. \<forall>t\<in>I_set. p \<noteq> ((1-t) * vx i + t * vx (Suc i mod ?n),
                (1-t) * vy i + t * vy (Suc i mod ?n))" by (by100 blast)
            hence hp_int: "\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p'"
              using hint \<open>p \<in> P\<close> by (by100 blast)
            from hp_int[rule_format, OF hc_P] hc(2)
            have "p = c" by (by100 blast)
            thus False using hpc by (by100 blast)
          qed
          then obtain i t where hi: "i < ?n" and ht: "t \<in> I_set" and
            hp_eq: "p = ((1-t) * vx i + t * vx (Suc i mod ?n),
                        (1-t) * vy i + t * vy (Suc i mod ?n))" by (by100 blast)
          \<comment> \<open>c must also be on some edge (otherwise hint gives c = p, contradiction).\<close>
          have "\<exists>j s. j < ?n \<and> s \<in> I_set \<and>
              c = ((1-s) * vx j + s * vx (Suc j mod ?n), (1-s) * vy j + s * vy (Suc j mod ?n))"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            hence "\<forall>j<?n. \<forall>s\<in>I_set. c \<noteq> ((1-s) * vx j + s * vx (Suc j mod ?n),
                (1-s) * vy j + s * vy (Suc j mod ?n))" by (by100 blast)
            hence hc_int: "\<forall>p'\<in>P. q c = q p' \<longrightarrow> c = p'"
              using hint hc_P by (by100 blast)
            have "q c = q p" using hc(2) by (by100 simp)
            from hc_int[rule_format, OF \<open>p \<in> P\<close> this]
            have "c = p" .
            thus False using hpc by (by100 blast)
          qed
          then obtain j s where hj: "j < ?n" and hs: "s \<in> I_set" and
            hc_eq: "c = ((1-s) * vx j + s * vx (Suc j mod ?n),
                        (1-s) * vy j + s * vy (Suc j mod ?n))" by (by100 blast)
          \<comment> \<open>By hno\_extra: q(edge_i(t)) = q(edge_j(s)) implies same point or same label.\<close>
          have "q ((1-t) * vx i + t * vx (Suc i mod ?n), (1-t) * vy i + t * vy (Suc i mod ?n))
              = q ((1-s) * vx j + s * vx (Suc j mod ?n), (1-s) * vy j + s * vy (Suc j mod ?n))"
            using hc(2) hp_eq hc_eq by (by100 simp)
          from hno_extra[rule_format, OF hi hj ht hs this]
          have "(i = j \<and> t = s) \<or> (fst (scheme!i) = fst (scheme!j) \<and>
                (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))" .
          thus ?thesis
          proof
            assume "i = j \<and> t = s"
            hence "p = c" using hp_eq hc_eq by (by100 simp)
            thus ?thesis using hpc by (by100 blast)
          next
            assume hsame: "fst (scheme!i) = fst (scheme!j) \<and>
                (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t)"
            \<comment> \<open>p is in paste\_img i j: p = edge_i(t) where c = edge_j(s) \<in> C, same label.\<close>
            have "p \<in> paste_img i j"
            proof -
              have hlabel: "fst (scheme ! i) = fst (scheme ! j)" using hsame by (by100 blast)
              have hs01: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by (by100 auto)+
              have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)+
              have hc_in_C: "((1-s) * vx j + s * vx (Suc j mod ?n),
                  (1-s) * vy j + s * vy (Suc j mod ?n)) \<in> C"
                using hc(1) hc_eq by (by100 simp)
              show ?thesis
              proof (cases "snd (scheme!i) = snd (scheme!j)")
                case True
                have "s = t" using hsame True by (by100 simp)
                have "p \<in> (\<lambda>t. ((1-t) * vx i + t * vx (Suc i mod ?n),
                    (1-t) * vy i + t * vy (Suc i mod ?n))) `
                    {t. 0 \<le> t \<and> t \<le> 1 \<and> ((1-t) * vx j + t * vx (Suc j mod ?n),
                        (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C}"
                  using ht01 hp_eq hc_in_C \<open>s = t\<close> by (by100 force)
                thus ?thesis unfolding paste_img_def using hlabel True by (by100 simp)
              next
                case False
                have "s = 1 - t" using hsame False by (by100 simp)
                \<comment> \<open>Witness: t' = 1-t. edge\_j(1-t) = edge\_j(s) = c \<in> C.
                   rev\_edge\_i(1-t) = ((1-t)*vx\_i + t*vx\_{i+1},...) = p.\<close>
                let ?t' = "1 - t"
                have ht'01: "0 \<le> ?t'" "?t' \<le> 1" using ht01 by (by100 linarith)+
                have hc_at_t': "((1-?t') * vx j + ?t' * vx (Suc j mod ?n),
                    (1-?t') * vy j + ?t' * vy (Suc j mod ?n)) \<in> C"
                  using hc_in_C \<open>s = 1 - t\<close> by (by100 simp)
                have hp_rev: "p = (?t' * vx i + (1-?t') * vx (Suc i mod ?n),
                    ?t' * vy i + (1-?t') * vy (Suc i mod ?n))"
                  using hp_eq by (simp add: algebra_simps)
                have "p \<in> (\<lambda>t. (t * vx i + (1-t) * vx (Suc i mod ?n),
                    t * vy i + (1-t) * vy (Suc i mod ?n))) `
                    {t. 0 \<le> t \<and> t \<le> 1 \<and> ((1-t) * vx j + t * vx (Suc j mod ?n),
                        (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C}"
                proof (rule image_eqI[of _ _ ?t'])
                  show "p = (?t' * vx i + (1-?t') * vx (Suc i mod ?n),
                      ?t' * vy i + (1-?t') * vy (Suc i mod ?n))" by (rule hp_rev)
                  show "?t' \<in> {t. 0 \<le> t \<and> t \<le> 1 \<and> ((1-t) * vx j + t * vx (Suc j mod ?n),
                      (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C}"
                    using ht'01 hc_at_t' by (by100 simp)
                qed
                thus ?thesis unfolding paste_img_def using hlabel False by (by100 simp)
              qed
            qed
            thus ?thesis using hi hj by (by100 blast)
          qed
        qed
      qed
      have hpaste_sub: "C \<union> (\<Union>i<?n. \<Union>j<?n. paste_img i j) \<subseteq> preimg"
      proof (rule Un_least)
        \<comment> \<open>C \<subseteq> preimg: trivial.\<close>
        show "C \<subseteq> preimg" unfolding preimg_def using hC_sub by (by100 blast)
      next
        \<comment> \<open>Each paste\_img point is in preimg.\<close>
        show "(\<Union>i<?n. \<Union>j<?n. paste_img i j) \<subseteq> preimg"
        proof (rule UN_least, rule UN_least)
          fix i j assume hi: "i \<in> {..<?n}" and hj: "j \<in> {..<?n}"
          have hi': "i < ?n" using hi by (by100 blast)
          have hj': "j < ?n" using hj by (by100 blast)
          show "paste_img i j \<subseteq> preimg"
          proof (cases "fst (scheme!i) = fst (scheme!j)")
            case False thus ?thesis unfolding paste_img_def by (by100 simp)
          next
            case True note hlab = this
            show ?thesis
            proof (cases "snd (scheme!i) = snd (scheme!j)")
              case True note hdir = this
              \<comment> \<open>Same label, same direction: q(edge\_i(t)) = q(edge\_j(t)).\<close>
              show ?thesis
              proof (rule subsetI)
                fix p assume "p \<in> paste_img i j"
                then obtain t :: real where ht0: "0 \<le> t" and ht1: "t \<le> 1"
                  and hc_in: "((1-t) * vx j + t * vx (Suc j mod ?n),
                               (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C"
                  and hp: "p = ((1-t) * vx i + t * vx (Suc i mod ?n),
                                (1-t) * vy i + t * vy (Suc i mod ?n))"
                  unfolding paste_img_def using hlab hdir by (by5000 auto)
                have hp_in_P: "p \<in> P" unfolding hp using hedge_in_P0[OF hi' ht0 ht1] .
                have ht_I: "t \<in> I_set" unfolding top1_unit_interval_def using ht0 ht1 by (by100 simp)
                \<comment> \<open>Apply hedge to get q(edge\_i(t)) = q(edge\_j(t)).\<close>
                have hedge_inst: "q ((1-t) * vx i + t * vx (Suc i mod ?n),
                                    (1-t) * vy i + t * vy (Suc i mod ?n))
                  = (if snd (scheme!i) = snd (scheme!j)
                     then q ((1-t) * vx j + t * vx (Suc j mod ?n),
                             (1-t) * vy j + t * vy (Suc j mod ?n))
                     else q (t * vx j + (1-t) * vx (Suc j mod ?n),
                             t * vy j + (1-t) * vy (Suc j mod ?n)))"
                  using hedge hi' hj' hlab ht_I by (by100 blast)
                have "q p = q ((1-t) * vx j + t * vx (Suc j mod ?n),
                               (1-t) * vy j + t * vy (Suc j mod ?n))"
                  unfolding hp using hedge_inst hdir by (by100 simp)
                hence "q p \<in> q ` C" using hc_in by (by100 blast)
                thus "p \<in> preimg" unfolding preimg_def using hp_in_P by (by100 blast)
              qed
            next
              case False note hdir = this
              \<comment> \<open>Same label, different direction: q(edge\_j(t)) = q(edge\_i\_rev(t)).\<close>
              show ?thesis
              proof (rule subsetI)
                fix p assume "p \<in> paste_img i j"
                then obtain t :: real where ht0: "0 \<le> t" and ht1: "t \<le> 1"
                  and hc_in: "((1-t) * vx j + t * vx (Suc j mod ?n),
                               (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C"
                  and hp: "p = (t * vx i + (1-t) * vx (Suc i mod ?n),
                                t * vy i + (1-t) * vy (Suc i mod ?n))"
                  unfolding paste_img_def using hlab hdir by (by5000 auto)
                have hp_in_P: "p \<in> P" unfolding hp using hedge_rev_in_P0[OF hi' ht0 ht1] .
                have ht_I: "t \<in> I_set" unfolding top1_unit_interval_def using ht0 ht1 by (by100 simp)
                \<comment> \<open>From hedge with j,i: q(edge\_j(t)) = q(edge\_i\_rev(t)).\<close>
                have hlab': "fst (scheme!j) = fst (scheme!i)" using hlab by (by100 simp)
                have hdir'': "\<not> (snd (scheme!j) = snd (scheme!i))" using hdir by (by100 blast)
                have hedge_ji: "q ((1-t) * vx j + t * vx (Suc j mod ?n),
                         (1-t) * vy j + t * vy (Suc j mod ?n))
                    = (if snd (scheme!j) = snd (scheme!i)
                       then q ((1-t) * vx i + t * vx (Suc i mod ?n),
                               (1-t) * vy i + t * vy (Suc i mod ?n))
                       else q (t * vx i + (1-t) * vx (Suc i mod ?n),
                               t * vy i + (1-t) * vy (Suc i mod ?n)))"
                  using hedge hj' hi' hlab' ht_I by (by100 blast)
                hence "q ((1-t) * vx j + t * vx (Suc j mod ?n),
                         (1-t) * vy j + t * vy (Suc j mod ?n)) = q p"
                  unfolding hp using hdir'' by (by100 simp)
                hence "q p = q ((1-t) * vx j + t * vx (Suc j mod ?n),
                               (1-t) * vy j + t * vy (Suc j mod ?n))"
                  by (by100 simp)
                hence "q p \<in> q ` C" using hc_in by (by100 blast)
                thus "p \<in> preimg" unfolding preimg_def using hp_in_P by (by100 blast)
              qed
            qed
          qed
        qed
      qed
      \<comment> \<open>Each paste\_img i j is compact (continuous affine image of compact set).\<close>
      \<comment> \<open>product\_topology\_on top1\_open\_sets top1\_open\_sets = top1\_open\_sets for R2.\<close>
      have hR2_eq: "product_topology_on top1_open_sets top1_open_sets
            = (top1_open_sets :: (real \<times> real) set set)"
        by (rule product_topology_on_open_sets)
      \<comment> \<open>C closedin\_on P means C closed in the standard topology of R2.
         Proof: P compact \<Rightarrow> P closedin R2; C closedin P \<Rightarrow> C closedin R2 (Thm 17.3).
         closedin R2 = closed.\<close>
      have hP_closedin_R2: "closedin_on (UNIV::(real\<times>real) set)
            (product_topology_on top1_open_sets top1_open_sets) P"
        using compact_in_hausdorff_closed[OF hR2_haus hP_compact] by (by100 blast)
      have hR2_top: "is_topology_on (UNIV::(real \<times> real) set)
            (product_topology_on top1_open_sets top1_open_sets)"
      proof -
        have hR_os: "is_topology_on (UNIV::real set) top1_open_sets"
          unfolding top1_open_sets_def is_topology_on_def
          using open_UNIV open_empty open_Un open_Int by (by5000 auto)
        hence "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
            (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on by (by100 blast)
        thus ?thesis by (by100 simp)
      qed
      have hC_closedin_R2: "closedin_on (UNIV::(real\<times>real) set)
            (product_topology_on top1_open_sets top1_open_sets) C"
        using Theorem_17_3[OF hR2_top hP_closedin_R2 hC] .
      have hC_closed_R2: "closed C"
      proof -
        from hC_closedin_R2 have "UNIV - C \<in> product_topology_on top1_open_sets top1_open_sets"
          unfolding closedin_on_def by (by100 blast)
        hence "UNIV - C \<in> (top1_open_sets :: (real \<times> real) set set)" using hR2_eq by (by100 simp)
        hence "open (UNIV - C)" unfolding top1_open_sets_def by (by100 simp)
        thus "closed C" unfolding closed_def using Compl_eq_Diff_UNIV[of C] by (by100 simp)
      qed
      \<comment> \<open>Edge maps are continuous.\<close>
      have hedge_cont: "\<And>j. continuous_on {0..1::real}
          (\<lambda>t. ((1-t) * vx j + t * vx (Suc j mod ?n),
                (1-t) * vy j + t * vy (Suc j mod ?n)))"
        by (intro continuous_on_Pair continuous_on_add continuous_on_mult
            continuous_on_diff continuous_on_const continuous_on_id)
      \<comment> \<open>The domain set {t \<in> [0,1] | edge\_j(t) \<in> C} is compact.\<close>
      have hdom_compact: "\<And>j. compact {t::real. 0 \<le> t \<and> t \<le> 1 \<and>
            ((1-t) * vx j + t * vx (Suc j mod ?n),
             (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C}"
      proof -
        fix j
        define ej where "ej t = ((1-t) * vx j + t * vx (Suc j mod ?n),
             (1-t) * vy j + t * vy (Suc j mod ?n))" for t :: real
        have hej_cont: "continuous_on {0..1} ej"
          unfolding ej_def
          by (intro continuous_on_Pair continuous_on_add continuous_on_mult
              continuous_on_diff continuous_on_const continuous_on_id)
        have hdom_eq: "{t::real. 0 \<le> t \<and> t \<le> 1 \<and>
            ((1-t) * vx j + t * vx (Suc j mod ?n),
             (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C}
            = ej -` C \<inter> {0..1}"
          unfolding ej_def by (by100 auto)
        have "closed (ej -` C \<inter> {0..1})"
          by (rule closed_vimage_Int[OF hC_closed_R2 hej_cont]) (by100 simp)
        moreover have "ej -` C \<inter> {0..1} \<subseteq> {0..1::real}" by (by100 blast)
        ultimately have "compact (ej -` C \<inter> {0..1})"
          using closed_subset_compact[OF compact_Icc] by (by100 blast)
        thus "compact {t::real. 0 \<le> t \<and> t \<le> 1 \<and>
            ((1-t) * vx j + t * vx (Suc j mod ?n),
             (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C}"
          using hdom_eq by (by100 simp)
      qed
      \<comment> \<open>Affine pasting maps are continuous.\<close>
      have hpaste_fwd_cont: "\<And>i. continuous_on UNIV
          (\<lambda>t::real. ((1-t) * vx i + t * vx (Suc i mod ?n),
                      (1-t) * vy i + t * vy (Suc i mod ?n)))"
        by (intro continuous_on_Pair continuous_on_add continuous_on_mult
            continuous_on_diff continuous_on_const continuous_on_id)
      have hpaste_rev_cont: "\<And>i. continuous_on UNIV
          (\<lambda>t::real. (t * vx i + (1-t) * vx (Suc i mod ?n),
                      t * vy i + (1-t) * vy (Suc i mod ?n)))"
        by (intro continuous_on_Pair continuous_on_add continuous_on_mult
            continuous_on_diff continuous_on_const continuous_on_id)
      have hpaste_compact: "\<forall>i<?n. \<forall>j<?n. compact (paste_img i j)"
      proof (intro allI impI)
        fix i j assume hi: "i < ?n" and hj: "j < ?n"
        show "compact (paste_img i j)"
        proof (cases "fst (scheme!i) = fst (scheme!j)")
          case False
          thus ?thesis unfolding paste_img_def by (by100 simp)
        next
          case True
          show ?thesis
          proof (cases "snd (scheme!i) = snd (scheme!j)")
            case True2: True
            have "paste_img i j = (\<lambda>t. ((1-t) * vx i + t * vx (Suc i mod ?n),
                        (1-t) * vy i + t * vy (Suc i mod ?n)))
                  ` {t. 0 \<le> t \<and> t \<le> 1 \<and>
                       ((1-t) * vx j + t * vx (Suc j mod ?n),
                        (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C}"
              unfolding paste_img_def using True True2 by (by100 simp)
            moreover have "compact ((\<lambda>t. ((1-t) * vx i + t * vx (Suc i mod ?n),
                        (1-t) * vy i + t * vy (Suc i mod ?n)))
                  ` {t. 0 \<le> t \<and> t \<le> 1 \<and>
                       ((1-t) * vx j + t * vx (Suc j mod ?n),
                        (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C})"
            proof (rule compact_continuous_image)
              show "continuous_on {t. 0 \<le> t \<and> t \<le> 1 \<and>
                       ((1-t) * vx j + t * vx (Suc j mod ?n),
                        (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C}
                  (\<lambda>t. ((1-t) * vx i + t * vx (Suc i mod ?n),
                        (1-t) * vy i + t * vy (Suc i mod ?n)))"
                using continuous_on_subset[OF hpaste_fwd_cont] by (by100 blast)
              show "compact {t. 0 \<le> t \<and> t \<le> 1 \<and>
                       ((1-t) * vx j + t * vx (Suc j mod ?n),
                        (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C}"
                by (rule hdom_compact)
            qed
            ultimately show ?thesis by (by100 simp)
          next
            case False2: False
            have "paste_img i j = (\<lambda>t. (t * vx i + (1-t) * vx (Suc i mod ?n),
                        t * vy i + (1-t) * vy (Suc i mod ?n)))
                  ` {t. 0 \<le> t \<and> t \<le> 1 \<and>
                       ((1-t) * vx j + t * vx (Suc j mod ?n),
                        (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C}"
              unfolding paste_img_def using True False2 by (by100 simp)
            moreover have "compact ((\<lambda>t. (t * vx i + (1-t) * vx (Suc i mod ?n),
                        t * vy i + (1-t) * vy (Suc i mod ?n)))
                  ` {t. 0 \<le> t \<and> t \<le> 1 \<and>
                       ((1-t) * vx j + t * vx (Suc j mod ?n),
                        (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C})"
            proof (rule compact_continuous_image)
              show "continuous_on {t. 0 \<le> t \<and> t \<le> 1 \<and>
                       ((1-t) * vx j + t * vx (Suc j mod ?n),
                        (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C}
                  (\<lambda>t. (t * vx i + (1-t) * vx (Suc i mod ?n),
                        t * vy i + (1-t) * vy (Suc i mod ?n)))"
                using continuous_on_subset[OF hpaste_rev_cont] by (by100 blast)
              show "compact {t. 0 \<le> t \<and> t \<le> 1 \<and>
                       ((1-t) * vx j + t * vx (Suc j mod ?n),
                        (1-t) * vy j + t * vy (Suc j mod ?n)) \<in> C}"
                by (rule hdom_compact)
            qed
            ultimately show ?thesis by (by100 simp)
          qed
        qed
      qed
      \<comment> \<open>Compact in R2 implies closed. Closed implies closedin\_on P.\<close>
      \<comment> \<open>P is closedin\_on in R2 (compact in Hausdorff).\<close>
      have hP_closedin_R2: "closedin_on (UNIV::(real\<times>real) set)
            (product_topology_on top1_open_sets top1_open_sets) P"
        using compact_in_hausdorff_closed[OF hR2_haus hP_compact] by (by100 blast)
      \<comment> \<open>paste\_img i j \<subseteq> P.\<close>
      have hpaste_sub_P: "\<And>i j. i < ?n \<Longrightarrow> j < ?n \<Longrightarrow> paste_img i j \<subseteq> P"
      proof -
        fix i j assume hi: "i < ?n" and hj: "j < ?n"
        show "paste_img i j \<subseteq> P"
        proof (cases "fst (scheme!i) = fst (scheme!j)")
          case False thus ?thesis unfolding paste_img_def by (by100 simp)
        next
          case True
          show ?thesis
          proof (cases "snd (scheme!i) = snd (scheme!j)")
            case True2: True
            show ?thesis
            proof (rule subsetI)
              fix p assume "p \<in> paste_img i j"
              then obtain t :: real where ht0: "0 \<le> t" and ht1: "t \<le> 1"
                and hp: "p = ((1-t) * vx i + t * vx (Suc i mod ?n),
                              (1-t) * vy i + t * vy (Suc i mod ?n))"
                unfolding paste_img_def using True True2 by (by5000 auto)
              show "p \<in> P" unfolding hp using hedge_in_P0[OF hi ht0 ht1] .
            qed
          next
            case False2: False
            show ?thesis
            proof (rule subsetI)
              fix p assume "p \<in> paste_img i j"
              then obtain t :: real where ht0: "0 \<le> t" and ht1: "t \<le> 1"
                and hp: "p = (t * vx i + (1-t) * vx (Suc i mod ?n),
                              t * vy i + (1-t) * vy (Suc i mod ?n))"
                unfolding paste_img_def using True False2 by (by5000 auto)
              show "p \<in> P" unfolding hp using hedge_rev_in_P0[OF hi ht0 ht1] .
            qed
          qed
        qed
      qed
      have hpaste_closed: "\<forall>i<?n. \<forall>j<?n. closedin_on P ?TP (paste_img i j)"
      proof (intro allI impI)
        fix i j assume hi: "i < ?n" and hj: "j < ?n"
        have hcomp: "compact (paste_img i j)" using hpaste_compact hi hj by (by100 blast)
        have hsub: "paste_img i j \<subseteq> P" using hpaste_sub_P[OF hi hj] .
        have hsub_univ: "paste_img i j \<subseteq> (UNIV::(real\<times>real) set)" by (by100 blast)
        have "top1_compact_on (paste_img i j)
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (paste_img i j))"
          using compact_R2_bridge[OF hcomp] .
        hence hcl_R2: "closedin_on (UNIV::(real\<times>real) set)
            (product_topology_on top1_open_sets top1_open_sets) (paste_img i j)"
          using compact_in_hausdorff_closed[OF hR2_haus _ hsub_univ] by (by100 blast)
        show "closedin_on P ?TP (paste_img i j)"
          using closedin_on_subspace[OF hR2_top _ hP_closedin_R2 hcl_R2 hsub] by (by100 blast)
      qed
      \<comment> \<open>Finite union of closed + C closed = preimg closed.\<close>
      have hunion_closed: "closedin_on P ?TP (\<Union>i<?n. \<Union>j<?n. paste_img i j)"
      proof -
        \<comment> \<open>Flatten the double union into a single finite union of sets.\<close>
        define FF where "FF = {paste_img i j | i j. i < ?n \<and> j < ?n}"
        have hFF_fin: "finite FF"
        proof -
          have hsub: "FF \<subseteq> (\<lambda>(i,j). paste_img i j) ` ({..<?n} \<times> {..<?n})"
            unfolding FF_def by (by100 blast)
          have "finite ({..<?n} \<times> {..<?n})" by (by100 blast)
          hence "finite ((\<lambda>(i,j). paste_img i j) ` ({..<?n} \<times> {..<?n}))" by (by100 blast)
          thus ?thesis using finite_subset[OF hsub] by (by100 blast)
        qed
        have hFF_cl: "\<forall>S\<in>FF. closedin_on P ?TP S"
          unfolding FF_def using hpaste_closed by (by100 blast)
        have "closedin_on P ?TP (\<Union>FF)"
          using closedin_on_finite_Union[OF hTP hFF_cl hFF_fin] .
        moreover have "\<Union>FF = (\<Union>i<?n. \<Union>j<?n. paste_img i j)"
          unfolding FF_def by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      have "preimg = C \<union> (\<Union>i<?n. \<Union>j<?n. paste_img i j)"
        using hpreimg_sub hpaste_sub by (by100 blast)
      thus ?thesis using closedin_on_Un[OF hTP hC hunion_closed] by (by100 simp)
    qed
    \<comment> \<open>preimg closed \<Rightarrow> q(C) closed via quotient map property.\<close>
    have "q ` C \<subseteq> X" using hC_sub hq_maps by (by100 blast)
    hence "X - q ` C \<subseteq> X" by (by100 blast)
    have hcomp_eq: "P - preimg = {p \<in> P. q p \<in> X - q ` C}"
      unfolding preimg_def using hq_maps by (by100 blast)
    have "P - preimg \<in> ?TP" using hpreimg_closed unfolding closedin_on_def preimg_def
      by (by100 blast)
    hence "{p \<in> P. q p \<in> X - q ` C} \<in> ?TP" using hcomp_eq by (by100 simp)
    hence "X - q ` C \<in> TX" using hqm_prop \<open>X - q ` C \<subseteq> X\<close> by (by100 blast)
    thus "closedin_on X TX (q ` C)" unfolding closedin_on_def
      using \<open>q ` C \<subseteq> X\<close> by (by100 blast)
  qed
  \<comment> \<open>Step 3: X is Hausdorff (Lemma 73.3 argument).
     For x \<noteq> y: preimages q\<inverse>({x}), q\<inverse>({y}) are disjoint closed in P.
     P normal \<Rightarrow> separated by disjoint open U, V.
     X - q(P-U), X - q(P-V) are disjoint open neighborhoods of x, y.\<close>
  show "is_hausdorff_on X TX" unfolding is_hausdorff_on_def
  proof (intro conjI ballI impI)
    show "is_topology_on X TX" by (rule hTX)
  next
    fix x y assume hx: "x \<in> X" and hy: "y \<in> X" and hne: "x \<noteq> y"
    \<comment> \<open>Preimages are disjoint closed in P.\<close>
    define Fx where "Fx = {p \<in> P. q p = x}"
    define Fy where "Fy = {p \<in> P. q p = y}"
    have hFx_ne: "Fx \<noteq> {}" unfolding Fx_def using hq_surj hx by (by100 blast)
    have hFy_ne: "Fy \<noteq> {}" unfolding Fy_def using hq_surj hy by (by100 blast)
    have hFx_sub: "Fx \<subseteq> P" unfolding Fx_def by (by100 blast)
    have hFy_sub: "Fy \<subseteq> P" unfolding Fy_def by (by100 blast)
    have hFxy_disj: "Fx \<inter> Fy = {}" unfolding Fx_def Fy_def using hne by (by100 blast)
    \<comment> \<open>Fx, Fy are closed in P (preimage of closed singleton under continuous q).
       First show X is T1: q closed map + P Hausdorff ⟹ singletons in X are closed.
       Then Fx = q⁻¹({x}) is closed as preimage of closed set under continuous map.\<close>
    have hx_closed: "closedin_on X TX {x}"
    proof -
      obtain p0 where hp0: "p0 \<in> P" "q p0 = x"
        using hq_surj hx by (by100 blast)
      have "{p0} \<subseteq> P" using hp0(1) by (by100 blast)
      have "closedin_on P ?TP {p0}"
        using singleton_closed_in_hausdorff[OF hP_haus hp0(1)] .
      hence "closedin_on X TX (q ` {p0})"
        using hq_closed_map by (by100 blast)
      thus ?thesis using hp0(2) by (by100 simp)
    qed
    have hy_closed: "closedin_on X TX {y}"
    proof -
      obtain p0 where hp0: "p0 \<in> P" "q p0 = y"
        using hq_surj hy by (by100 blast)
      have "closedin_on P ?TP {p0}"
        using singleton_closed_in_hausdorff[OF hP_haus hp0(1)] .
      hence "closedin_on X TX (q ` {p0})"
        using hq_closed_map by (by100 blast)
      thus ?thesis using hp0(2) by (by100 simp)
    qed
    have hFx_closed: "closedin_on P ?TP Fx"
    proof -
      have "Fx = {p \<in> P. q p \<in> {x}}" unfolding Fx_def by (by100 blast)
      thus ?thesis
        using continuous_preimage_closedin[OF hTP hTX hq_cont hx_closed] by (by100 simp)
    qed
    have hFy_closed: "closedin_on P ?TP Fy"
    proof -
      have "Fy = {p \<in> P. q p \<in> {y}}" unfolding Fy_def by (by100 blast)
      thus ?thesis
        using continuous_preimage_closedin[OF hTP hTX hq_cont hy_closed] by (by100 simp)
    qed
    \<comment> \<open>P normal: separate Fx, Fy by disjoint open U, V.\<close>
    from normal_separation[OF hP_normal hFx_closed hFy_closed hFxy_disj]
    obtain U V where hU: "U \<in> ?TP" and hV: "V \<in> ?TP"
        and hFxU: "Fx \<subseteq> U" and hFyV: "Fy \<subseteq> V" and hUV: "U \<inter> V = {}" by (by100 blast)
    \<comment> \<open>X - q(P-U) is open (q closed map) and contains x.\<close>
    have hTP_strict: "is_topology_on_strict P ?TP"
      unfolding is_topology_on_strict_def
    proof (intro conjI)
      show "is_topology_on P ?TP" by (rule hTP)
    next
      show "?TP \<subseteq> Pow P" unfolding subspace_topology_def by (by100 blast)
    qed
    have hU_sub: "U \<subseteq> P"
      using hU hTP_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hV_sub: "V \<subseteq> P"
      using hV hTP_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hPmU_closed: "closedin_on P ?TP (P - U)"
    proof -
      have "P - U \<subseteq> P" by (by100 blast)
      moreover have "P - (P - U) = U" using hU_sub by (by100 blast)
      hence "P - (P - U) \<in> ?TP" using hU by (by100 simp)
      ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
    qed
    have hPmV_closed: "closedin_on P ?TP (P - V)"
    proof -
      have "P - V \<subseteq> P" by (by100 blast)
      moreover have "P - (P - V) = V" using hV_sub by (by100 blast)
      hence "P - (P - V) \<in> ?TP" using hV by (by100 simp)
      ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
    qed
    have hqPmU_closed: "closedin_on X TX (q ` (P - U))"
      using hq_closed_map hPmU_closed by (by100 blast)
    have hqPmV_closed: "closedin_on X TX (q ` (P - V))"
      using hq_closed_map hPmV_closed by (by100 blast)
    define Ux where "Ux = X - q ` (P - U)"
    define Vy where "Vy = X - q ` (P - V)"
    have hUx_open: "Ux \<in> TX"
      using hqPmU_closed unfolding Ux_def closedin_on_def by (by100 blast)
    have hVy_open: "Vy \<in> TX"
      using hqPmV_closed unfolding Vy_def closedin_on_def by (by100 blast)
    have hx_Ux: "x \<in> Ux"
    proof -
      have "\<forall>p \<in> P - U. q p \<noteq> x"
      proof (intro ballI)
        fix p assume "p \<in> P - U"
        hence "p \<in> P" "p \<notin> U" by (by100 blast)+
        hence "p \<notin> Fx" using hFxU by (by100 blast)
        thus "q p \<noteq> x" unfolding Fx_def using \<open>p \<in> P\<close> by (by100 blast)
      qed
      hence "x \<notin> q ` (P - U)" by (by100 blast)
      thus "x \<in> Ux" unfolding Ux_def using hx by (by100 blast)
    qed
    have hy_Vy: "y \<in> Vy"
    proof -
      have "\<forall>p \<in> P - V. q p \<noteq> y"
      proof (intro ballI)
        fix p assume "p \<in> P - V"
        hence "p \<in> P" "p \<notin> V" by (by100 blast)+
        hence "p \<notin> Fy" using hFyV by (by100 blast)
        thus "q p \<noteq> y" unfolding Fy_def using \<open>p \<in> P\<close> by (by100 blast)
      qed
      hence "y \<notin> q ` (P - V)" by (by100 blast)
      thus "y \<in> Vy" unfolding Vy_def using hy by (by100 blast)
    qed
    have hUxVy_disj: "Ux \<inter> Vy = {}"
    proof (rule ccontr)
      assume "Ux \<inter> Vy \<noteq> {}"
      then obtain z where "z \<in> Ux" "z \<in> Vy" by (by100 blast)
      hence "z \<notin> q ` (P - U)" "z \<notin> q ` (P - V)"
        unfolding Ux_def Vy_def by (by100 blast)+
      have "z \<in> X" using \<open>z \<in> Ux\<close> unfolding Ux_def by (by100 blast)
      then obtain p where "p \<in> P" "q p = z" using hq_surj by (by100 blast)
      have "p \<notin> P - U" using \<open>z \<notin> q ` (P - U)\<close> \<open>q p = z\<close> by (by100 blast)
      hence "p \<in> U" using \<open>p \<in> P\<close> by (by100 blast)
      have "p \<notin> P - V" using \<open>z \<notin> q ` (P - V)\<close> \<open>q p = z\<close> by (by100 blast)
      hence "p \<in> V" using \<open>p \<in> P\<close> by (by100 blast)
      from \<open>p \<in> U\<close> \<open>p \<in> V\<close> hUV show False by (by100 blast)
    qed
    show "\<exists>U V. neighborhood_of x X TX U \<and> neighborhood_of y X TX V \<and> U \<inter> V = {}"
      unfolding neighborhood_of_def
      using hUx_open hVy_open hx_Ux hy_Vy hUxVy_disj by (by100 blast)
  qed
qed

text \<open>Key helper: a scheme quotient provides the attaching data for Theorem 72.1.
  The 1-skeleton A = q(boundary of polygon) is closed and path-connected.
  The attaching map h = q composed with polygon-to-disk homeomorphism is continuous.
  The interior of the disk maps homeomorphically to X - A.\<close>
lemma scheme_quotient_CW_data:
  assumes "top1_quotient_of_scheme_on X TX scheme"
      and "length scheme \<ge> 3"
      \<comment> \<open>Vertex connectivity: all vertices are identified under any valid edge identification.
         This is a combinatorial property of the scheme (label graph connected).
         True for torus, projective, and all standard schemes.\<close>
      and hvert_connected: "\<forall>(q::real\<times>real\<Rightarrow>'a) (vx::nat\<Rightarrow>real) (vy::nat\<Rightarrow>real).
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
  shows "\<exists>(A :: 'a set) (h :: real \<times> real \<Rightarrow> 'a) (a :: 'a) (q :: real \<times> real \<Rightarrow> 'a)
      (vx :: nat \<Rightarrow> real) (vy :: nat \<Rightarrow> real).
      closedin_on X TX A
    \<and> top1_path_connected_on A (subspace_topology X TX A)
    \<and> top1_continuous_map_on top1_B2 top1_B2_topology X TX h
    \<and> a \<in> A
    \<and> top1_homeomorphism_on
        (top1_B2 - top1_S1) (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
        (X - A) (subspace_topology X TX (X - A)) h
    \<and> h ` top1_S1 \<subseteq> A
    \<and> (\<forall>z\<in>top1_S1. h z \<in> A)
    \<comment> \<open>Additional: the internal witnesses for reasoning about A's structure.\<close>
    \<and> A = q ` (\<Union>i<length scheme. {((1-t) * vx i + t * vx (Suc i mod length scheme),
                   (1-t) * vy i + t * vy (Suc i mod length scheme)) | t. t \<in> I_set})
    \<and> a = q (vx 0, vy 0)
    \<and> (\<forall>i<length scheme. \<forall>j<length scheme. q (vx i, vy i) = q (vx j, vy j))
    \<and> (\<forall>i<length scheme. \<forall>j<length scheme.
          fst (scheme!i) = fst (scheme!j) \<longrightarrow>
          (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
              (1-t) * vy i + t * vy (Suc i mod length scheme))
           = (if snd (scheme!i) = snd (scheme!j)
              then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                      (1-t) * vy j + t * vy (Suc j mod length scheme))
              else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                      t * vy j + (1-t) * vy (Suc j mod length scheme)))))
    \<and> (\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
          q ((1-t) * vx i + t * vx (Suc i mod length scheme),
             (1-t) * vy i + t * vy (Suc i mod length scheme))
        = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
             (1-s) * vy j + s * vy (Suc j mod length scheme))
        \<longrightarrow> (i = j \<and> t = s)
          \<or> (fst (scheme!i) = fst (scheme!j) \<and>
             (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t)))
    \<comment> \<open>Continuity of q on individual edges (for constructing circle homeomorphisms).\<close>
    \<and> (\<forall>i<length scheme.
          top1_continuous_map_on I_set top1_unit_interval_topology A (subspace_topology X TX A)
            (\<lambda>t. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
                     (1-t) * vy i + t * vy (Suc i mod length scheme))))
    \<and> (\<forall>i<length scheme. \<forall>t\<in>I_set.
          h (cos (2 * pi * (real i + t) / real (length scheme)),
             sin (2 * pi * (real i + t) / real (length scheme)))
        = q ((1-t) * vx i + t * vx (Suc i mod length scheme),
             (1-t) * vy i + t * vy (Suc i mod length scheme)))"
proof -
  \<comment> \<open>Step 1: Extract (P, q, vx, vy) from the scheme definition.\<close>
  obtain P q vx vy where
    hP: "top1_is_polygonal_region_on P (length scheme)" and
    hq: "top1_quotient_map_on P (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q" and
    hlen3: "length scheme \<ge> 3" and
    hverts: "\<forall>i<length scheme. (vx i, vy i) \<in> P" and
    hP_hull_extract: "P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<length scheme. coeffs i) = 1
                       \<and> x = (\<Sum>i<length scheme. coeffs i * vx i)
                       \<and> y = (\<Sum>i<length scheme. coeffs i * vy i)}" and
    hedge: "\<forall>i<length scheme. \<forall>j<length scheme.
        fst (scheme!i) = fst (scheme!j) \<longrightarrow>
        (\<forall>t\<in>I_set. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
           (1-t) * vy i + t * vy (Suc i mod length scheme))
         = (if snd (scheme!i) = snd (scheme!j)
            then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                    (1-t) * vy j + t * vy (Suc j mod length scheme))
            else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                    t * vy j + (1-t) * vy (Suc j mod length scheme))))" and
    hint: "\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
          p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme)))
       \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')" and
    hno_extra_cw: "\<forall>i<length scheme. \<forall>j<length scheme. \<forall>t\<in>I_set. \<forall>s\<in>I_set.
          q ((1-t) * vx i + t * vx (Suc i mod length scheme),
             (1-t) * vy i + t * vy (Suc i mod length scheme))
        = q ((1-s) * vx j + s * vx (Suc j mod length scheme),
             (1-s) * vy j + s * vy (Suc j mod length scheme))
        \<longrightarrow> (i = j \<and> t = s)
          \<or> (fst (scheme!i) = fst (scheme!j) \<and>
             (if snd (scheme!i) = snd (scheme!j) then s = t else s = 1 - t))" and
    hccw_extract: "\<forall>i<length scheme.
        let cx = (\<Sum>j<length scheme. vx j) / real (length scheme);
            cy = (\<Sum>j<length scheme. vy j) / real (length scheme)
        in (vx i - cx) * (vy (Suc i mod length scheme) - cy)
         - (vy i - cy) * (vx (Suc i mod length scheme) - cx) > 0" and
    hstrict_hp: "\<forall>i<length scheme. \<forall>k<length scheme.
        k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod length scheme \<longrightarrow>
        (vx k - vx i) * (vy (Suc i mod length scheme) - vy i)
        - (vy k - vy i) * (vx (Suc i mod length scheme) - vx i) < 0"
    using assms(1)[unfolded top1_quotient_of_scheme_on_def] assms(2)
    by (elim conjE exE) (rule that, assumption+)
  \<comment> \<open>Step 2: Get homeomorphism \<psi>: P \<rightarrow> B^2 with boundary correspondence.\<close>
  let ?TP = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P"
  have hP_hull: "P = {(x, y) | x y.
            \<exists>coeffs. (\<forall>i<length scheme. coeffs i \<ge> 0)
                   \<and> (\<Sum>i<length scheme. coeffs i) = 1
                   \<and> x = (\<Sum>i<length scheme. coeffs i * vx i)
                   \<and> y = (\<Sum>i<length scheme. coeffs i * vy i)}"
    using hP_hull_extract by (by100 simp)
  have hvert_hp: "\<forall>i<length scheme. \<forall>k<length scheme.
      cross2 (vx k - vx i, vy k - vy i)
          (vx (Suc i mod length scheme) - vx i,
           vy (Suc i mod length scheme) - vy i) \<le> 0"
  proof (intro allI impI)
    fix i k :: nat assume hi: "i < length scheme" and hk: "k < length scheme"
    show "cross2 (vx k - vx i, vy k - vy i)
        (vx (Suc i mod length scheme) - vx i, vy (Suc i mod length scheme) - vy i) \<le> 0"
    proof (cases "k = i \<or> k = Suc i mod length scheme")
      case True thus ?thesis unfolding cross2_def by (by100 force)
    next
      case False
      hence "k \<noteq> i" "k \<noteq> Suc i mod length scheme" by (by100 blast)+
      have "(vx k - vx i) * (vy (Suc i mod length scheme) - vy i)
          - (vy k - vy i) * (vx (Suc i mod length scheme) - vx i) < 0"
        using hstrict_hp \<open>k \<noteq> i\<close> \<open>k \<noteq> Suc i mod length scheme\<close> hi hk by (by5000 blast)
      hence "(vx k - vx i) * (vy (Suc i mod length scheme) - vy i)
          - (vy k - vy i) * (vx (Suc i mod length scheme) - vx i) \<le> 0" by (by100 linarith)
      thus ?thesis unfolding cross2_def by (by100 simp)
    qed
  qed
  have hstrict_hp': "\<forall>i<length scheme. \<forall>k<length scheme. k \<noteq> i \<longrightarrow> k \<noteq> Suc i mod length scheme \<longrightarrow>
      cross2 (vx k - vx i, vy k - vy i)
          (vx (Suc i mod length scheme) - vx i, vy (Suc i mod length scheme) - vy i) < 0"
    using hstrict_hp unfolding cross2_def by (by100 force)
  from polygon_homeomorphic_to_disk_with_boundary[OF hP hlen3 hverts hP_hull hccw_extract hvert_hp hstrict_hp']
  obtain \<psi> where h\<psi>: "top1_homeomorphism_on P ?TP top1_B2 top1_B2_topology \<psi>"
      and h\<psi>_bd: "\<psi> ` (\<Union>i<length scheme. {((1-t) * vx i + t * vx (Suc i mod length scheme),
                     (1-t) * vy i + t * vy (Suc i mod length scheme)) | t. t \<in> I_set})
          = top1_S1"
      and h\<psi>_int: "top1_homeomorphism_on
          (P - (\<Union>i<length scheme. {((1-t) * vx i + t * vx (Suc i mod length scheme),
                          (1-t) * vy i + t * vy (Suc i mod length scheme)) | t. t \<in> I_set}))
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
             (P - (\<Union>i<length scheme. {((1-t) * vx i + t * vx (Suc i mod length scheme),
                            (1-t) * vy i + t * vy (Suc i mod length scheme)) | t. t \<in> I_set})))
          (top1_B2 - top1_S1)
          (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
          \<psi>"
      and h\<psi>_edge_arc: "\<forall>i<length scheme. \<forall>t\<in>I_set.
          \<psi> ((1-t) * vx i + t * vx (Suc i mod length scheme),
              (1-t) * vy i + t * vy (Suc i mod length scheme))
          = (cos (2 * pi * (real i + t) / real (length scheme)),
             sin (2 * pi * (real i + t) / real (length scheme)))"
    by - (erule exE, (erule conjE)+, rule that, assumption+)
  \<comment> \<open>Step 3: Define A = q(Bd P) where Bd P = union of edges.\<close>
  define BdP where "BdP = (\<Union>i<length scheme.
      {((1-t) * vx i + t * vx (Suc i mod length scheme),
        (1-t) * vy i + t * vy (Suc i mod length scheme)) | t. t \<in> I_set})"
  define A where "A = q ` BdP"
  have hBdP_sub_P: "BdP \<subseteq> P"
  proof (rule subsetI)
    fix p assume "p \<in> BdP"
    then obtain i t where hi: "i < length scheme" and ht: "t \<in> I_set"
        and hp: "p = ((1-t) * vx i + t * vx (Suc i mod length scheme),
                     (1-t) * vy i + t * vy (Suc i mod length scheme))"
      unfolding BdP_def by (by5000 force)
    have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)+
    have hvi: "(vx i, vy i) \<in> P" using hverts hi by (by100 blast)
    have hlen_pos: "length scheme > 0" using assms(2) by (by100 linarith)
    have hi1: "Suc i mod length scheme < length scheme" using hlen_pos by (by100 simp)
    have hvi1: "(vx (Suc i mod length scheme), vy (Suc i mod length scheme)) \<in> P"
      using hverts hi1 by (by100 blast)
    show "p \<in> P" using polygonal_region_convex_combo[OF hP hlen3 hvi hvi1 ht01(1) ht01(2)]
      hp by (by100 simp)
  qed
  \<comment> \<open>Step 4: Define h = q \<circ> \<psi>^{-1}: B^2 \<rightarrow> X.\<close>
  let ?\<psi>inv = "inv_into P \<psi>"
  have h\<psi>inv: "top1_homeomorphism_on top1_B2 top1_B2_topology P ?TP ?\<psi>inv"
    by (rule homeomorphism_inverse[OF h\<psi>])
  have h\<psi>_bij: "bij_betw \<psi> P top1_B2"
    using h\<psi> unfolding top1_homeomorphism_on_def by (by100 blast)
  have h\<psi>inv_inv: "\<forall>z\<in>top1_B2. \<psi> (?\<psi>inv z) = z"
  proof (intro ballI)
    fix z assume "z \<in> top1_B2"
    hence "z \<in> \<psi> ` P" using h\<psi>_bij unfolding bij_betw_def by (by100 simp)
    thus "\<psi> (?\<psi>inv z) = z" by (rule f_inv_into_f)
  qed
  have h\<psi>inv_inv2: "\<forall>p\<in>P. ?\<psi>inv (\<psi> p) = p"
  proof (intro ballI)
    fix p assume "p \<in> P"
    have "inj_on \<psi> P" using h\<psi>_bij unfolding bij_betw_def by (by100 blast)
    thus "?\<psi>inv (\<psi> p) = p" using \<open>p \<in> P\<close> by (rule inv_into_f_f)
  qed
  define h where "h z = q (inv_into P \<psi> z)" for z
  define a where "a = q (vx 0, vy 0)"
  \<comment> \<open>Step 5: Verify all CW data properties.\<close>
  have hP_compact_top: "top1_compact_on P ?TP"
    by (rule polygonal_region_compact[OF hP hlen3])
  have hX_strict: "is_topology_on_strict X TX"
    using assms(1) unfolding top1_quotient_of_scheme_on_def by (by100 blast)
  have hX_haus: "is_hausdorff_on X TX"
    by (rule scheme_quotient_hausdorff[OF assms(1) assms(2)])
  have hq_cont: "top1_continuous_map_on P ?TP X TX q"
    using hq unfolding top1_quotient_map_on_def by (by100 blast)
  have hBdP_closed: "closedin_on P ?TP BdP"
    proof -
      \<comment> \<open>BdP is compact (finite union of compact line segments in R²).
         Compact in R² \<Rightarrow> closed in R² (t2\_space). Closed in R² \<Rightarrow> closedin\_on P.\<close>
      have hBdP_sub_P: "BdP \<subseteq> P"
      proof (rule subsetI)
        fix p assume "p \<in> BdP"
        then obtain i t where hi: "i < length scheme" and ht: "t \<in> I_set"
            and hp: "p = ((1-t) * vx i + t * vx (Suc i mod length scheme),
                         (1-t) * vy i + t * vy (Suc i mod length scheme))"
          unfolding BdP_def by (by5000 force)
        have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)+
        have hvi: "(vx i, vy i) \<in> P" using hverts hi by (by100 blast)
        have hlen_pos: "length scheme > 0" using assms(2) by (by100 linarith)
        have hi1: "Suc i mod length scheme < length scheme" using hlen_pos by (by100 simp)
        have hvi1: "(vx (Suc i mod length scheme), vy (Suc i mod length scheme)) \<in> P"
          using hverts hi1 by (by100 blast)
        have "p = ((1-t) * fst (vx i, vy i) + t * fst (vx (Suc i mod length scheme), vy (Suc i mod length scheme)),
                   (1-t) * snd (vx i, vy i) + t * snd (vx (Suc i mod length scheme), vy (Suc i mod length scheme)))"
          using hp by (by100 simp)
        thus "p \<in> P"
          using polygonal_region_convex_combo[OF hP hlen3 hvi hvi1 ht01(1) ht01(2)]
          by (by100 simp)
      qed
      have "compact BdP"
      proof -
        \<comment> \<open>BdP = \<Union>_{i<n} edge_i. Each edge is compact (continuous image of [0,1]).
           Finite union of compact sets is compact.\<close>
        have "\<forall>i<length scheme. compact {((1-t) * vx i + t * vx (Suc i mod length scheme),
            (1-t) * vy i + t * vy (Suc i mod length scheme)) | t::real. 0 \<le> t \<and> t \<le> 1}"
        proof (intro allI impI)
          fix i assume "i < length scheme"
          \<comment> \<open>Edge i = image of [0,1] under (\<lambda>t. ((1-t)*vx_i + t*vx_{i+1}, ...)).\<close>
          have "(\<lambda>t. ((1-t) * vx i + t * vx (Suc i mod length scheme),
                      (1-t) * vy i + t * vy (Suc i mod length scheme))) ` {0..1}
              = {((1-t) * vx i + t * vx (Suc i mod length scheme),
                  (1-t) * vy i + t * vy (Suc i mod length scheme)) | t. 0 \<le> t \<and> t \<le> 1}"
            by (by100 auto)
          moreover have "compact ((\<lambda>t. ((1-t) * vx i + t * vx (Suc i mod length scheme),
                      (1-t) * vy i + t * vy (Suc i mod length scheme))) ` {0..1::real})"
          proof (rule compact_continuous_image[OF _ compact_Icc])
            show "continuous_on {0..1::real} (\<lambda>t. ((1-t) * vx i + t * vx (Suc i mod length scheme),
                      (1-t) * vy i + t * vy (Suc i mod length scheme)))"
              by (intro continuous_on_Pair continuous_on_add continuous_on_mult
                  continuous_on_diff continuous_on_const continuous_on_id)
          qed
          ultimately show "compact {((1-t) * vx i + t * vx (Suc i mod length scheme),
              (1-t) * vy i + t * vy (Suc i mod length scheme)) | t. 0 \<le> t \<and> t \<le> 1}"
            by (by100 simp)
        qed
        define edges where "edges = (\<lambda>i. {((1-t) * vx i + t * vx (Suc i mod length scheme),
            (1-t) * vy i + t * vy (Suc i mod length scheme)) | t::real. 0 \<le> t \<and> t \<le> 1})"
        define edges where "edges = (\<lambda>i. {((1-t) * vx i + t * vx (Suc i mod length scheme),
            (1-t) * vy i + t * vy (Suc i mod length scheme)) | t::real. 0 \<le> t \<and> t \<le> 1})"
        have hfin: "finite (edges ` {..<length scheme})" by (by100 blast)
        have hall: "\<forall>S \<in> edges ` {..<length scheme}. compact S"
        proof (intro ballI)
          fix S assume "S \<in> edges ` {..<length scheme}"
          then obtain i where "i < length scheme" "S = edges i" by (by100 blast)
          thus "compact S" using \<open>\<forall>i<length scheme. compact _\<close> unfolding edges_def by (by100 blast)
        qed
        have "compact (\<Union>(edges ` {..<length scheme}))"
          by (rule compact_Union[OF hfin hall])
        moreover have "BdP = \<Union>(edges ` {..<length scheme})"
          unfolding BdP_def edges_def top1_unit_interval_def by (by5000 auto)
        ultimately show "compact BdP" by (by100 simp)
      qed
      hence "closed BdP" using compact_imp_closed by (by100 blast)
      \<comment> \<open>closed BdP means UNIV - BdP is open. In the subspace topology on P,
         P - BdP = P \<inter> (UNIV - BdP) is open, hence BdP is closedin\_on P.\<close>
      hence "open (- BdP)" unfolding closed_def by (by100 simp)
      hence "(- BdP) \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
      hence hbdp_prod: "(- BdP) \<in> product_topology_on top1_open_sets top1_open_sets"
        using product_topology_on_open_sets by (by5000 fast)
      hence "P \<inter> (- BdP) \<in> ?TP" unfolding subspace_topology_def by (by5000 blast)
      moreover have "P - BdP = P \<inter> (- BdP)" by (by100 blast)
      ultimately have "P - BdP \<in> ?TP" by (by100 simp)
      thus ?thesis unfolding closedin_on_def using hBdP_sub_P by (by100 blast)
    qed
  have hA_closed: "closedin_on X TX A"
  proof -
    from compact_hausdorff_continuous_closed_map[OF hP_compact_top hX_haus hq_cont hBdP_closed]
    show ?thesis unfolding A_def .
  qed
  have hA_pc: "top1_path_connected_on A (subspace_topology X TX A)"
  proof -
    \<comment> \<open>BdP is path-connected (polygon boundary is a cycle of edges).\<close>
    have hBdP_pc: "top1_path_connected_on BdP (subspace_topology UNIV
        (product_topology_on top1_open_sets top1_open_sets) BdP)"
    proof -
      let ?R2 = "product_topology_on (top1_open_sets :: real set set) top1_open_sets"
      let ?TBdP = "subspace_topology (UNIV::(real\<times>real) set) ?R2 BdP"
      let ?n = "length scheme"
      have hn_pos: "?n > 0" using hlen3 by (by100 linarith)
      have hR_top: "is_topology_on (UNIV::real set) top1_open_sets"
        unfolding top1_open_sets_def is_topology_on_def
        using open_UNIV open_empty open_Un open_Int by (by5000 auto)
      have hR2_top: "is_topology_on (UNIV::(real\<times>real) set) ?R2"
      proof -
        have "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by (by100 auto)
        thus ?thesis using product_topology_on_is_topology_on[OF hR_top hR_top] by (by100 simp)
      qed
      have hBdP_top: "is_topology_on BdP ?TBdP"
        by (rule subspace_topology_is_topology_on[OF hR2_top]) (by100 blast)
      \<comment> \<open>Edge point membership: edge i at parameter t is in BdP.\<close>
      have edge_mem: "\<And>i t. i < ?n \<Longrightarrow> t \<in> I_set \<Longrightarrow>
          ((1-t) * vx i + t * vx (Suc i mod ?n),
           (1-t) * vy i + t * vy (Suc i mod ?n)) \<in> BdP"
        unfolding BdP_def by (by5000 force)
      \<comment> \<open>Vertex i is in BdP (edge i at parameter 0).\<close>
      have v_in_BdP: "\<And>i. i < ?n \<Longrightarrow> (vx i, vy i) \<in> BdP"
      proof -
        fix i assume hi: "i < ?n"
        have "((1-(0::real)) * vx i + 0 * vx (Suc i mod ?n),
               (1-0) * vy i + 0 * vy (Suc i mod ?n)) \<in> BdP"
          by (rule edge_mem[OF hi]) (simp add: top1_unit_interval_def)
        thus "(vx i, vy i) \<in> BdP" by (by100 simp)
      qed
      \<comment> \<open>Edge path: straight line from v_i to v_{Suc i mod n} lies in BdP.\<close>
      have edge_path: "\<And>i. i < ?n \<Longrightarrow>
          \<exists>f. top1_is_path_on BdP ?TBdP (vx i, vy i)
              (vx (Suc i mod ?n), vy (Suc i mod ?n)) f"
      proof -
        fix i assume hi: "i < ?n"
        define \<gamma> where "\<gamma> t = ((1-t)*vx i + t*vx(Suc i mod ?n),
                               (1-t)*vy i + t*vy(Suc i mod ?n))" for t
        have himg: "\<forall>t\<in>I_set. \<gamma> t \<in> BdP"
          unfolding \<gamma>_def using edge_mem[OF hi] by (by100 blast)
        have h\<gamma>_eq: "\<gamma> = (\<lambda>t. ((1-t) * fst (vx i, vy i) + t * fst (vx(Suc i mod ?n), vy(Suc i mod ?n)),
                              (1-t) * snd (vx i, vy i) + t * snd (vx(Suc i mod ?n), vy(Suc i mod ?n))))"
          unfolding \<gamma>_def by (by100 simp)
        have "top1_is_path_on UNIV ?R2 (vx i, vy i) (vx(Suc i mod ?n), vy(Suc i mod ?n)) \<gamma>"
          using R2_straight_line_path[of "(vx i, vy i)" "(vx(Suc i mod ?n), vy(Suc i mod ?n))"]
          h\<gamma>_eq by (by100 simp)
        hence hcont: "top1_continuous_map_on I_set I_top UNIV ?R2 \<gamma>"
          unfolding top1_is_path_on_def by (by100 blast)
        have "top1_continuous_map_on I_set I_top BdP ?TBdP \<gamma>"
          by (rule continuous_map_restrict_codomain[OF hcont himg]) (by100 blast)
        moreover have "\<gamma> 0 = (vx i, vy i)" unfolding \<gamma>_def by (by100 simp)
        moreover have "\<gamma> 1 = (vx(Suc i mod ?n), vy(Suc i mod ?n))" unfolding \<gamma>_def by (by100 simp)
        ultimately have "top1_is_path_on BdP ?TBdP (vx i, vy i) (vx(Suc i mod ?n), vy(Suc i mod ?n)) \<gamma>"
          unfolding top1_is_path_on_def by (by100 blast)
        thus "\<exists>f. top1_is_path_on BdP ?TBdP (vx i, vy i) (vx(Suc i mod ?n), vy(Suc i mod ?n)) f"
          by (by100 blast)
      qed
      \<comment> \<open>Reverse edge: path from v_{Suc i mod n} to v_i.\<close>
      have rev_edge: "\<And>i. i < ?n \<Longrightarrow>
          \<exists>f. top1_is_path_on BdP ?TBdP (vx (Suc i mod ?n), vy (Suc i mod ?n)) (vx i, vy i) f"
      proof -
        fix i assume hi: "i < ?n"
        from edge_path[OF hi] obtain f where
          hf: "top1_is_path_on BdP ?TBdP (vx i, vy i) (vx(Suc i mod ?n), vy(Suc i mod ?n)) f"
          by (by100 blast)
        from top1_is_path_on_reverse[OF hBdP_top hf]
        show "\<exists>f. top1_is_path_on BdP ?TBdP (vx(Suc i mod ?n), vy(Suc i mod ?n)) (vx i, vy i) f"
          by (by100 blast)
      qed
      \<comment> \<open>By induction: vertex j connects to vertex 0 in BdP.\<close>
      have v_to_v0: "\<forall>j<?n. \<exists>f. top1_is_path_on BdP ?TBdP (vx j, vy j) (vx 0, vy 0) f"
      proof (intro allI impI)
        fix j assume hj: "j < ?n"
        show "\<exists>f. top1_is_path_on BdP ?TBdP (vx j, vy j) (vx 0, vy 0) f"
          using hj
        proof (induction j)
          case 0
          from top1_constant_path_is_path[OF hBdP_top v_in_BdP[OF 0]]
          show ?case by (by100 blast)
        next
          case (Suc k)
          have hk: "k < ?n" using Suc.prems by (by100 linarith)
          have hsk_mod: "Suc k mod ?n = Suc k" using Suc.prems by (by100 simp)
          from rev_edge[OF hk] obtain f1 where
            hf1: "top1_is_path_on BdP ?TBdP (vx(Suc k mod ?n), vy(Suc k mod ?n)) (vx k, vy k) f1"
            by (by100 blast)
          hence hf1': "top1_is_path_on BdP ?TBdP (vx(Suc k), vy(Suc k)) (vx k, vy k) f1"
            using hsk_mod by (by100 simp)
          from Suc.IH[OF hk] obtain f2 where
            hf2: "top1_is_path_on BdP ?TBdP (vx k, vy k) (vx 0, vy 0) f2"
            by (by100 blast)
          from top1_path_product_is_path[OF hBdP_top hf1' hf2]
          show ?case by (by100 blast)
        qed
      qed
      \<comment> \<open>Any point p \<in> BdP connects to v_0.\<close>
      have any_to_v0: "\<And>p. p \<in> BdP \<Longrightarrow> \<exists>f. top1_is_path_on BdP ?TBdP p (vx 0, vy 0) f"
      proof -
        fix p assume hp: "p \<in> BdP"
        then obtain j t where hj: "j < ?n" and ht: "t \<in> I_set" and
          hp_eq: "p = ((1-t)*vx j + t*vx(Suc j mod ?n), (1-t)*vy j + t*vy(Suc j mod ?n))"
          unfolding BdP_def by (by5000 force)
        \<comment> \<open>Straight line from p to (vx j, vy j): stays in edge j \<subseteq> BdP.\<close>
        define \<gamma>0 where "\<gamma>0 s = ((1-s)*fst p + s*vx j, (1-s)*snd p + s*vy j)" for s
        have himg0: "\<forall>s\<in>I_set. \<gamma>0 s \<in> BdP"
        proof (intro ballI)
          fix s assume hs: "s \<in> I_set"
          have hs01: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by (by100 auto)+
          have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)+
          define t' where "t' = (1-s)*t"
          have ht'01: "0 \<le> t'" using hs01 ht01 unfolding t'_def
            by (by100 simp)
          have ht'le1: "t' \<le> 1" unfolding t'_def
            using mult_le_one[of "1-s" t] hs01 ht01 by (by100 linarith)
          have ht'I: "t' \<in> I_set" unfolding top1_unit_interval_def using ht'01 ht'le1 by (by100 simp)
          have "\<gamma>0 s = ((1-t')*vx j + t'*vx(Suc j mod ?n), (1-t')*vy j + t'*vy(Suc j mod ?n))"
            unfolding \<gamma>0_def hp_eq t'_def by (simp add: algebra_simps)
          thus "\<gamma>0 s \<in> BdP" using edge_mem[OF hj ht'I] by (by100 simp)
        qed
        have h\<gamma>0_eq: "\<gamma>0 = (\<lambda>s. ((1-s)*fst p + s*fst(vx j, vy j), (1-s)*snd p + s*snd(vx j, vy j)))"
          unfolding \<gamma>0_def by (by100 simp)
        have "top1_is_path_on UNIV ?R2 p (vx j, vy j) \<gamma>0"
          using R2_straight_line_path[of p "(vx j, vy j)"] h\<gamma>0_eq by (by100 simp)
        hence hcont0: "top1_continuous_map_on I_set I_top UNIV ?R2 \<gamma>0"
          unfolding top1_is_path_on_def by (by100 blast)
        have hcont_BdP: "top1_continuous_map_on I_set I_top BdP ?TBdP \<gamma>0"
          by (rule continuous_map_restrict_codomain[OF hcont0 himg0]) (by100 blast)
        have "\<gamma>0 0 = p" unfolding \<gamma>0_def by (by100 simp)
        moreover have "\<gamma>0 1 = (vx j, vy j)" unfolding \<gamma>0_def by (by100 simp)
        ultimately have hpath0: "top1_is_path_on BdP ?TBdP p (vx j, vy j) \<gamma>0"
          unfolding top1_is_path_on_def using hcont_BdP by (by100 blast)
        from v_to_v0 hj obtain f1 where
          hf1: "top1_is_path_on BdP ?TBdP (vx j, vy j) (vx 0, vy 0) f1"
          by (by100 blast)
        from top1_path_product_is_path[OF hBdP_top hpath0 hf1]
        show "\<exists>f. top1_is_path_on BdP ?TBdP p (vx 0, vy 0) f"
          by (by100 blast)
      qed
      \<comment> \<open>Conclusion: BdP is path-connected.\<close>
      show ?thesis unfolding top1_path_connected_on_def
      proof (intro conjI ballI)
        show "is_topology_on BdP ?TBdP" by (rule hBdP_top)
      next
        fix x y assume hx: "x \<in> BdP" and hy: "y \<in> BdP"
        from any_to_v0[OF hx] obtain fx where hfx: "top1_is_path_on BdP ?TBdP x (vx 0, vy 0) fx"
          by (by100 blast)
        from any_to_v0[OF hy] obtain fy where hfy: "top1_is_path_on BdP ?TBdP y (vx 0, vy 0) fy"
          by (by100 blast)
        from top1_is_path_on_reverse[OF hBdP_top hfy]
        have hfyr: "top1_is_path_on BdP ?TBdP (vx 0, vy 0) y (\<lambda>t. fy (1-t))" .
        from top1_path_product_is_path[OF hBdP_top hfx hfyr]
        show "\<exists>f. top1_is_path_on BdP ?TBdP x y f" by (by100 blast)
      qed
    qed
    \<comment> \<open>q restricted to BdP is continuous: BdP \<subseteq> P, q continuous on P.\<close>
    have hq_cont_Bd: "top1_continuous_map_on BdP
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) BdP)
        X TX q"
    proof -
      have hq_cont_P: "top1_continuous_map_on P ?TP X TX q"
        using hq unfolding top1_quotient_map_on_def by (by100 blast)
      have hBdP_sub_P: "BdP \<subseteq> P"
      proof (rule subsetI)
        fix p assume "p \<in> BdP"
        then obtain i t where hi: "i < length scheme" and ht: "t \<in> I_set"
            and hp: "p = ((1-t) * vx i + t * vx (Suc i mod length scheme),
                         (1-t) * vy i + t * vy (Suc i mod length scheme))"
          unfolding BdP_def by (by5000 force)
        have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)+
        have hvi: "(vx i, vy i) \<in> P" using hverts hi by (by100 blast)
        have hlen_pos: "length scheme > 0" using assms(2) by (by100 linarith)
        have hi1: "Suc i mod length scheme < length scheme" using hlen_pos by (by100 simp)
        have hvi1: "(vx (Suc i mod length scheme), vy (Suc i mod length scheme)) \<in> P"
          using hverts hi1 by (by100 blast)
        show "p \<in> P" using polygonal_region_convex_combo[OF hP hlen3 hvi hvi1 ht01(1) ht01(2)]
          hp by (by100 simp)
      qed
      from top1_continuous_map_on_restrict_domain_simple[OF hq_cont_P hBdP_sub_P]
      have "top1_continuous_map_on BdP (subspace_topology P ?TP BdP) X TX q" .
      moreover have "subspace_topology P ?TP BdP =
          subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) BdP"
        using subspace_topology_trans[OF hBdP_sub_P] by (by100 simp)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>A = q(BdP) is path-connected (continuous image of path-connected).\<close>
    \<comment> \<open>Apply top1\_path\_connected\_continuous\_image: BdP path-connected, q continuous,
       q(BdP) = A, A \<subseteq> X.\<close>
    have himg_q: "\<forall>x \<in> BdP. q x \<in> X"
    proof (intro ballI)
      fix p assume "p \<in> BdP"
      hence "p \<in> P" using hBdP_sub_P by (by100 blast)
      thus "q p \<in> X" using hq unfolding top1_quotient_map_on_def top1_continuous_map_on_def
        by (by5000 blast)
    qed
    have hA_eq: "q ` BdP = A" unfolding A_def by (by100 simp)
    have hA_sub_X: "A \<subseteq> X"
    proof -
      have "q ` P = X" using hq unfolding top1_quotient_map_on_def by (by5000 blast)
      hence "q ` BdP \<subseteq> X" using hBdP_sub_P by (by100 blast)
      thus ?thesis unfolding A_def by (by100 simp)
    qed
    have hX_top: "is_topology_on X TX"
      using assms(1) unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def
      by (by100 blast)
    from top1_path_connected_continuous_image[where X=BdP and TX="subspace_topology UNIV
        (product_topology_on top1_open_sets top1_open_sets) BdP" and Y=X and TY=TX
        and f=q and Z=A and TZ="subspace_topology X TX A"]
    show ?thesis using hBdP_pc hq_cont_Bd himg_q hA_eq hA_sub_X hX_top by (by5000 blast)
  qed
  have hh_cont: "top1_continuous_map_on top1_B2 top1_B2_topology X TX h"
  proof -
    have hq_cont: "top1_continuous_map_on P ?TP X TX q"
      using hq unfolding top1_quotient_map_on_def by (by100 blast)
    have h\<psi>inv_cont: "top1_continuous_map_on top1_B2 top1_B2_topology P ?TP (inv_into P \<psi>)"
      using h\<psi>inv unfolding top1_homeomorphism_on_def by (by100 blast)
    from top1_continuous_map_on_comp[OF h\<psi>inv_cont hq_cont]
    have "top1_continuous_map_on top1_B2 top1_B2_topology X TX (q \<circ> inv_into P \<psi>)" .
    moreover have "h = q \<circ> inv_into P \<psi>" unfolding h_def comp_def by (by100 simp)
    ultimately show ?thesis by (by100 simp)
  qed
  have ha_A: "a \<in> A"
  proof -
    have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have hlen_pos: "length scheme > 0" using assms(2) by (by100 linarith)
    have "0 < length scheme" using hlen_pos .
    have hv0_bd: "(vx 0, vy 0) \<in> BdP" unfolding BdP_def
    proof -
      have "((1-(0::real)) * vx 0 + 0 * vx (Suc 0 mod length scheme),
             (1-0) * vy 0 + 0 * vy (Suc 0 mod length scheme)) = (vx 0, vy 0)"
        by (by100 simp)
      moreover have "(0::real) \<in> I_set" using h0_I .
      ultimately show "(vx 0, vy 0) \<in> (\<Union>i<length scheme. {((1-t) * vx i + t * vx (Suc i mod length scheme),
          (1-t) * vy i + t * vy (Suc i mod length scheme)) | t. t \<in> I_set})"
        using hlen_pos h0_I by (by5000 force)
    qed
    thus ?thesis unfolding a_def A_def by (by100 blast)
  qed
  have hh_homeo: "top1_homeomorphism_on (top1_B2 - top1_S1)
      (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
      (X - A) (subspace_topology X TX (X - A)) h"
  proof -
    \<comment> \<open>Fold BdP\_def into h\<psi>\_int.\<close>
    have h\<psi>_int_BdP: "top1_homeomorphism_on (P - BdP)
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (P - BdP))
        (top1_B2 - top1_S1)
        (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
        \<psi>"
      using h\<psi>_int[folded BdP_def] by (by100 simp)
    \<comment> \<open>Inverse: inv\_into (P-BdP) \<psi> is homeomorphism B2-S1 \<rightarrow> P-BdP.\<close>
    have h\<psi>inv_homeo: "top1_homeomorphism_on (top1_B2 - top1_S1)
        (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
        (P - BdP) (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (P - BdP))
        (inv_into (P - BdP) \<psi>)"
      by (rule homeomorphism_inverse[OF h\<psi>_int_BdP])
    \<comment> \<open>inv\_into P \<psi> = inv\_into (P-BdP) \<psi> on B2-S1.\<close>
    have h\<psi>_inj: "inj_on \<psi> P"
      using h\<psi>_bij unfolding bij_betw_def by (by100 blast)
    have hinv_agree: "\<forall>z\<in>top1_B2 - top1_S1. inv_into P \<psi> z = inv_into (P - BdP) \<psi> z"
    proof (intro ballI)
      fix z assume hz: "z \<in> top1_B2 - top1_S1"
      have hbij_int: "bij_betw \<psi> (P - BdP) (top1_B2 - top1_S1)"
        using h\<psi>_int_BdP unfolding top1_homeomorphism_on_def by (by100 blast)
      hence hz_img: "z \<in> \<psi> ` (P - BdP)" using hz unfolding bij_betw_def by (by100 blast)
      then obtain p where hp: "p \<in> P - BdP" "\<psi> p = z" by (by100 blast)
      have hp_P: "p \<in> P" using hp(1) by (by100 blast)
      have "inv_into (P - BdP) \<psi> z = p"
        using inv_into_f_f[of \<psi> "P - BdP" p] hbij_int hp
        unfolding bij_betw_def by (by100 blast)
      moreover have "inv_into P \<psi> z = p"
        using inv_into_f_f[OF h\<psi>_inj hp_P] hp(2) by (by100 simp)
      ultimately show "inv_into P \<psi> z = inv_into (P - BdP) \<psi> z" by (by100 simp)
    qed
    have hq_surj: "q ` P = X" using hq unfolding top1_quotient_map_on_def by (by5000 blast)
    \<comment> \<open>Step 2: q is injective on P-BdP.\<close>
    have hq_inj_int: "inj_on q (P - BdP)"
    proof (rule inj_onI)
      fix p p' assume hp: "p \<in> P - BdP" and hp': "p' \<in> P - BdP" and hqeq: "q p = q p'"
      have hp_P: "p \<in> P" using hp by (by100 blast)
      have hp'_P: "p' \<in> P" using hp' by (by100 blast)
      have hpnot: "\<forall>i<length scheme. \<forall>t\<in>I_set.
          p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                (1-t) * vy i + t * vy (Suc i mod length scheme))"
      proof (intro allI ballI impI)
        fix i t assume hi: "i < length scheme" and ht: "t \<in> I_set"
        show "p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                   (1-t) * vy i + t * vy (Suc i mod length scheme))"
        proof
          assume "p = ((1-t) * vx i + t * vx (Suc i mod length scheme),
                       (1-t) * vy i + t * vy (Suc i mod length scheme))"
          hence "p \<in> BdP" unfolding BdP_def using hi ht by (by5000 force)
          thus False using hp by (by100 blast)
        qed
      qed
      from hint hp_P hpnot hp'_P hqeq
      show "p = p'" by (by100 blast)
    qed
    \<comment> \<open>Step 3: q(P-BdP) = X - A.\<close>
    have hq_int_eq: "q ` (P - BdP) = X - A"
    proof
      show "q ` (P - BdP) \<subseteq> X - A"
      proof (rule image_subsetI)
        fix p assume hp: "p \<in> P - BdP"
        have hp_P: "p \<in> P" using hp by (by100 blast)
        have hp_notBdP: "p \<notin> BdP" using hp by (by100 blast)
        have hqp_X: "q p \<in> X" using hq_surj hp_P by (by100 blast)
        have hqp_notA: "q p \<notin> A"
        proof
          assume "q p \<in> A"
          hence "q p \<in> q ` BdP" unfolding A_def by (by100 simp)
          then obtain b where hb: "b \<in> BdP" "q b = q p" by (by100 auto)
          have hb_P: "b \<in> P" using hb(1) hBdP_sub_P by (by100 blast)
          have hpnot: "\<forall>i<length scheme. \<forall>t\<in>I_set.
              p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                    (1-t) * vy i + t * vy (Suc i mod length scheme))"
          proof (intro allI ballI impI)
            fix i t assume hi: "i < length scheme" and ht: "t \<in> I_set"
            show "p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                       (1-t) * vy i + t * vy (Suc i mod length scheme))"
            proof
              assume "p = ((1-t) * vx i + t * vx (Suc i mod length scheme),
                           (1-t) * vy i + t * vy (Suc i mod length scheme))"
              hence "p \<in> BdP" unfolding BdP_def using hi ht by (by5000 force)
              thus False using hp_notBdP by (by100 blast)
            qed
          qed
          from hint hp_P hpnot hb_P hb(2)[symmetric]
          have "p = b" by (by100 blast)
          thus False using hp_notBdP hb(1) by (by100 blast)
        qed
        thus "q p \<in> X - A" using hqp_X hqp_notA by (by100 blast)
      qed
    next
      show "X - A \<subseteq> q ` (P - BdP)"
      proof (rule subsetI)
        fix x assume hx: "x \<in> X - A"
        have hx_X: "x \<in> X" using hx by (by100 blast)
        have hx_notA: "x \<notin> A" using hx by (by100 blast)
        from hq_surj hx_X obtain p where hp_P: "p \<in> P" and hqp: "q p = x"
          by (by100 blast)
        have "p \<notin> BdP"
        proof
          assume "p \<in> BdP"
          hence "q p \<in> q ` BdP" by (by100 blast)
          hence "x \<in> A" using hqp A_def by (by100 simp)
          thus False using hx_notA by (by100 blast)
        qed
        thus "x \<in> q ` (P - BdP)" using hp_P hqp by (by100 blast)
      qed
    qed
    \<comment> \<open>Step 4: q|_{P-BdP} is a homeomorphism via Theorem 22.1 + bijectivity.\<close>
    have hPBdP_sat: "top1_saturated_with_respect_to_on P q (P - BdP)"
      unfolding top1_saturated_with_respect_to_on_def
    proof (intro conjI)
      show "P - BdP \<subseteq> P" by (by100 blast)
    next
      show "\<forall>x\<in>P - BdP. \<forall>y\<in>P. q y = q x \<longrightarrow> y \<in> P - BdP"
      proof (intro ballI impI)
        fix p p' assume hp: "p \<in> P - BdP" and hp': "p' \<in> P" and hqeq: "q p' = q p"
        have hp_P: "p \<in> P" using hp by (by100 blast)
        have hp_notBdP: "p \<notin> BdP" using hp by (by100 blast)
        have hpnot: "\<forall>i<length scheme. \<forall>t\<in>I_set.
            p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                  (1-t) * vy i + t * vy (Suc i mod length scheme))"
        proof (intro allI ballI impI)
          fix i t assume hi: "i < length scheme" and ht: "t \<in> I_set"
          show "p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                     (1-t) * vy i + t * vy (Suc i mod length scheme))"
          proof
            assume "p = ((1-t) * vx i + t * vx (Suc i mod length scheme),
                         (1-t) * vy i + t * vy (Suc i mod length scheme))"
            hence "p \<in> BdP" unfolding BdP_def using hi ht by (by5000 force)
            thus False using hp_notBdP by (by100 blast)
          qed
        qed
        from hint hp_P hpnot hp' hqeq[symmetric]
        have "p = p'" by (by100 blast)
        thus "p' \<in> P - BdP" using hp by (by100 simp)
      qed
    qed
    have hPBdP_open: "openin_on P ?TP (P - BdP)"
      using closedin_complement_openin[OF hBdP_closed] by (by100 simp)
    have hq_quot_int: "top1_quotient_map_on (P - BdP)
        (subspace_topology P ?TP (P - BdP))
        (q ` (P - BdP)) (subspace_topology X TX (q ` (P - BdP))) q"
    proof -
      from Theorem_22_1(1)[OF hq hPBdP_sat] hPBdP_open
      show ?thesis by (by100 simp)
    qed
    have hTP_sub: "subspace_topology P ?TP (P - BdP) =
        subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (P - BdP)"
      using subspace_topology_trans[of "P - BdP" P] by (by100 simp)
    have hq_quot_XA: "top1_quotient_map_on (P - BdP)
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (P - BdP))
        (X - A) (subspace_topology X TX (X - A)) q"
      using hq_quot_int hTP_sub hq_int_eq by (by100 simp)
    have hq_bij_int: "bij_betw q (P - BdP) (X - A)"
      unfolding bij_betw_def using hq_inj_int hq_int_eq by (by100 blast)
    have hq_homeo_int: "top1_homeomorphism_on (P - BdP)
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (P - BdP))
        (X - A) (subspace_topology X TX (X - A)) q"
      by (rule top1_bij_quotient_map_on_imp_homeomorphism_on[OF hq_quot_XA hq_bij_int])
    \<comment> \<open>Compose: (q \<circ> inv\_into (P-BdP) \<psi>) is homeomorphism B2-S1 \<rightarrow> X-A.\<close>
    have hcomp_homeo: "top1_homeomorphism_on (top1_B2 - top1_S1)
        (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
        (X - A) (subspace_topology X TX (X - A)) (q \<circ> inv_into (P - BdP) \<psi>)"
      by (rule homeomorphism_comp[OF h\<psi>inv_homeo hq_homeo_int])
    \<comment> \<open>h agrees with q \<circ> inv\_into (P-BdP) \<psi> on B2-S1.\<close>
    have hext: "\<forall>z\<in>top1_B2 - top1_S1. h z = (q \<circ> inv_into (P - BdP) \<psi>) z"
    proof (intro ballI)
      fix z assume hz: "z \<in> top1_B2 - top1_S1"
      have "h z = q (inv_into P \<psi> z)" unfolding h_def by (by100 simp)
      also have "inv_into P \<psi> z = inv_into (P - BdP) \<psi> z" using hinv_agree hz by (by100 simp)
      finally show "h z = (q \<circ> inv_into (P - BdP) \<psi>) z" unfolding comp_def by (by100 simp)
    qed
    \<comment> \<open>Transfer the homeomorphism from q \<circ> inv\_into (P-BdP) \<psi> to h.\<close>
    show ?thesis
    proof -
      \<comment> \<open>Extract pieces from the composition homeomorphism.\<close>
      have htop1: "is_topology_on (top1_B2 - top1_S1) (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))"
        using hcomp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have htop2: "is_topology_on (X - A) (subspace_topology X TX (X - A))"
        using hcomp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have hbij_comp: "bij_betw (q \<circ> inv_into (P - BdP) \<psi>) (top1_B2 - top1_S1) (X - A)"
        using hcomp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      \<comment> \<open>bij\_betw h from bij\_betw of composition + extensional equality.\<close>
      have hbij_h: "bij_betw h (top1_B2 - top1_S1) (X - A)"
      proof -
        have hinj_comp: "inj_on (q \<circ> inv_into (P - BdP) \<psi>) (top1_B2 - top1_S1)"
          using hbij_comp unfolding bij_betw_def by (by100 blast)
        have hinj_h: "inj_on h (top1_B2 - top1_S1)"
        proof (rule inj_onI)
          fix a b assume ha: "a \<in> top1_B2 - top1_S1" and hb: "b \<in> top1_B2 - top1_S1"
              and hab: "h a = h b"
          have "(q \<circ> inv_into (P - BdP) \<psi>) a = (q \<circ> inv_into (P - BdP) \<psi>) b"
            using hab hext ha hb by (by100 simp)
          thus "a = b" using inj_onD[OF hinj_comp _ ha hb] by (by100 simp)
        qed
        have himg_h: "h ` (top1_B2 - top1_S1) = X - A"
        proof
          show "h ` (top1_B2 - top1_S1) \<subseteq> X - A"
          proof (rule image_subsetI)
            fix z assume hz: "z \<in> top1_B2 - top1_S1"
            have "h z = (q \<circ> inv_into (P - BdP) \<psi>) z" using hext hz by (by100 simp)
            moreover have "(q \<circ> inv_into (P - BdP) \<psi>) z \<in> X - A"
              using hbij_comp hz unfolding bij_betw_def by (by100 blast)
            ultimately show "h z \<in> X - A" by (by100 simp)
          qed
        next
          show "X - A \<subseteq> h ` (top1_B2 - top1_S1)"
          proof (rule subsetI)
            fix x assume hx: "x \<in> X - A"
            have hx_img: "x \<in> (q \<circ> inv_into (P - BdP) \<psi>) ` (top1_B2 - top1_S1)"
              using hbij_comp hx unfolding bij_betw_def by (by100 blast)
            then obtain z where hz: "z \<in> top1_B2 - top1_S1" and hqz: "(q \<circ> inv_into (P - BdP) \<psi>) z = x"
              by (by100 blast)
            have "h z = x" using hext hz hqz by (by100 simp)
            thus "x \<in> h ` (top1_B2 - top1_S1)" using hz by (by100 blast)
          qed
        qed
        show ?thesis unfolding bij_betw_def using hinj_h himg_h by (by100 blast)
      qed
      \<comment> \<open>Continuity of h from continuity of composition.\<close>
      have hcont_comp: "top1_continuous_map_on (top1_B2 - top1_S1) (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
          (X - A) (subspace_topology X TX (X - A)) (q \<circ> inv_into (P - BdP) \<psi>)"
        using hcomp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have hmap_h: "\<forall>z\<in>top1_B2 - top1_S1. h z \<in> X - A"
      proof (intro ballI)
        fix z assume hz: "z \<in> top1_B2 - top1_S1"
        have "h z = (q \<circ> inv_into (P - BdP) \<psi>) z" using hext hz by (by100 simp)
        moreover have "(q \<circ> inv_into (P - BdP) \<psi>) z \<in> X - A"
          using hcont_comp hz unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "h z \<in> X - A" by (by100 simp)
      qed
      have hpre_h: "\<forall>V\<in>subspace_topology X TX (X - A).
          {z \<in> top1_B2 - top1_S1. h z \<in> V}
          \<in> subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1)"
      proof (intro ballI)
        fix V assume hV: "V \<in> subspace_topology X TX (X - A)"
        have hpre_eq: "{z \<in> top1_B2 - top1_S1. h z \<in> V} =
            {z \<in> top1_B2 - top1_S1. (q \<circ> inv_into (P - BdP) \<psi>) z \<in> V}"
          using hext by (by100 auto)
        have "{z \<in> top1_B2 - top1_S1. (q \<circ> inv_into (P - BdP) \<psi>) z \<in> V}
            \<in> subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1)"
          using hcont_comp hV unfolding top1_continuous_map_on_def by (by100 blast)
        thus "{z \<in> top1_B2 - top1_S1. h z \<in> V}
            \<in> subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1)"
          using hpre_eq by (by100 simp)
      qed
      have hcont_h: "top1_continuous_map_on (top1_B2 - top1_S1) (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
          (X - A) (subspace_topology X TX (X - A)) h"
        unfolding top1_continuous_map_on_def
        using htop1 htop2 hmap_h hpre_h by (by5000 blast)
      \<comment> \<open>Inverse continuity: inv\_into (B2-S1) h agrees with inv\_into (B2-S1) (q \<circ> inv\_into (P-BdP) \<psi>) on X-A.\<close>
      have hcont_inv_comp: "top1_continuous_map_on (X - A) (subspace_topology X TX (X - A))
          (top1_B2 - top1_S1) (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
          (inv_into (top1_B2 - top1_S1) (q \<circ> inv_into (P - BdP) \<psi>))"
        using hcomp_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
      have hinj_comp: "inj_on (q \<circ> inv_into (P - BdP) \<psi>) (top1_B2 - top1_S1)"
        using hbij_comp unfolding bij_betw_def by (by100 blast)
      have hinj_h: "inj_on h (top1_B2 - top1_S1)"
        using hbij_h unfolding bij_betw_def by (by100 blast)
      have hext_inv: "\<forall>x\<in>X - A. inv_into (top1_B2 - top1_S1) h x =
          inv_into (top1_B2 - top1_S1) (q \<circ> inv_into (P - BdP) \<psi>) x"
      proof (intro ballI)
        fix x assume hx: "x \<in> X - A"
        have hx_img: "x \<in> (q \<circ> inv_into (P - BdP) \<psi>) ` (top1_B2 - top1_S1)"
          using hbij_comp hx unfolding bij_betw_def by (by100 blast)
        then obtain z where hz: "z \<in> top1_B2 - top1_S1" and hqz: "(q \<circ> inv_into (P - BdP) \<psi>) z = x"
          by (by100 blast)
        have hh_z: "h z = x" using hext hz hqz by (by100 simp)
        have "inv_into (top1_B2 - top1_S1) h x = z"
          using inv_into_f_eq[OF hinj_h hz hh_z] by (by100 simp)
        moreover have "inv_into (top1_B2 - top1_S1) (q \<circ> inv_into (P - BdP) \<psi>) x = z"
          using inv_into_f_eq[OF hinj_comp hz hqz] unfolding comp_def by (by100 simp)
        ultimately show "inv_into (top1_B2 - top1_S1) h x =
            inv_into (top1_B2 - top1_S1) (q \<circ> inv_into (P - BdP) \<psi>) x" by (by100 simp)
      qed
      have hmap_inv: "\<forall>x\<in>X - A. inv_into (top1_B2 - top1_S1) h x \<in> top1_B2 - top1_S1"
      proof (intro ballI)
        fix x assume hx: "x \<in> X - A"
        have "inv_into (top1_B2 - top1_S1) h x = inv_into (top1_B2 - top1_S1) (q \<circ> inv_into (P - BdP) \<psi>) x"
          using hext_inv hx by (by100 simp)
        moreover have "inv_into (top1_B2 - top1_S1) (q \<circ> inv_into (P - BdP) \<psi>) x \<in> top1_B2 - top1_S1"
          using hcont_inv_comp hx unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "inv_into (top1_B2 - top1_S1) h x \<in> top1_B2 - top1_S1" by (by100 simp)
      qed
      have hpre_inv: "\<forall>V\<in>subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1).
          {x \<in> X - A. inv_into (top1_B2 - top1_S1) h x \<in> V}
          \<in> subspace_topology X TX (X - A)"
      proof (intro ballI)
        fix V assume hV: "V \<in> subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1)"
        have hpre_eq: "{x \<in> X - A. inv_into (top1_B2 - top1_S1) h x \<in> V} =
            {x \<in> X - A. inv_into (top1_B2 - top1_S1) (q \<circ> inv_into (P - BdP) \<psi>) x \<in> V}"
          using hext_inv by (by100 auto)
        have "{x \<in> X - A. inv_into (top1_B2 - top1_S1) (q \<circ> inv_into (P - BdP) \<psi>) x \<in> V}
            \<in> subspace_topology X TX (X - A)"
          using hcont_inv_comp hV unfolding top1_continuous_map_on_def by (by100 blast)
        thus "{x \<in> X - A. inv_into (top1_B2 - top1_S1) h x \<in> V}
            \<in> subspace_topology X TX (X - A)"
          using hpre_eq by (by100 simp)
      qed
      have hcont_inv_h: "top1_continuous_map_on (X - A) (subspace_topology X TX (X - A))
          (top1_B2 - top1_S1) (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
          (inv_into (top1_B2 - top1_S1) h)"
        unfolding top1_continuous_map_on_def
        using htop2 htop1 hmap_inv hpre_inv by (by5000 blast)
      show ?thesis unfolding top1_homeomorphism_on_def
        using htop1 htop2 hbij_h hcont_h hcont_inv_h by (by100 blast)
    qed
  qed
  have hh_S1: "h ` top1_S1 \<subseteq> A"
  proof -
    \<comment> \<open>S1 = \<psi>(BdP) from h\<psi>\_bd. So \<psi>inv(S1) = BdP. h(S1) = q(\<psi>inv(S1)) = q(BdP) = A.\<close>
    have "\<psi> ` BdP = top1_S1" using h\<psi>_bd unfolding BdP_def by (by100 simp)
    hence "inv_into P \<psi> ` top1_S1 \<subseteq> BdP"
    proof -
      assume h\<psi>BdP: "\<psi> ` BdP = top1_S1"
      show "inv_into P \<psi> ` top1_S1 \<subseteq> BdP"
      proof (rule image_subsetI)
        fix z assume "z \<in> top1_S1"
        hence "z \<in> \<psi> ` BdP" using h\<psi>BdP by (by100 simp)
        then obtain p where "p \<in> BdP" "\<psi> p = z" by (by100 blast)
        have "p \<in> P" using \<open>p \<in> BdP\<close> hBdP_sub_P by (by100 blast)
        have "inj_on \<psi> P" using h\<psi>_bij unfolding bij_betw_def by (by100 blast)
        hence "inv_into P \<psi> z = p"
          using inv_into_f_f[OF \<open>inj_on \<psi> P\<close> \<open>p \<in> P\<close>] \<open>\<psi> p = z\<close> by (by100 simp)
        thus "inv_into P \<psi> z \<in> BdP" using \<open>p \<in> BdP\<close> by (by100 simp)
      qed
    qed
    hence "q ` (inv_into P \<psi> ` top1_S1) \<subseteq> q ` BdP" by (by100 blast)
    moreover have "h ` top1_S1 = q ` (inv_into P \<psi> ` top1_S1)"
      unfolding h_def by (by100 auto)
    ultimately show ?thesis unfolding A_def by (by100 blast)
  qed
  have hh_S1': "\<forall>z\<in>top1_S1. h z \<in> A" using hh_S1 by (by100 blast)
  have hA_eq: "A = q ` (\<Union>i<length scheme. {((1-t) * vx i + t * vx (Suc i mod length scheme),
                   (1-t) * vy i + t * vy (Suc i mod length scheme)) | t. t \<in> I_set})"
    unfolding A_def BdP_def by (by100 simp)
  have ha_eq: "a = q (vx 0, vy 0)" unfolding a_def by (by100 simp)
  have hvert_all_id: "\<forall>i<length scheme. \<forall>j<length scheme. q (vx i, vy i) = q (vx j, vy j)"
    using mp[OF spec[OF spec[OF spec[OF hvert_connected, of q], of vx], of vy] hedge] .
  \<comment> \<open>Continuity of q on individual edges.\<close>
  have hq_edge_cont: "\<forall>i<length scheme.
      top1_continuous_map_on I_set top1_unit_interval_topology A (subspace_topology X TX A)
        (\<lambda>t. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
                 (1-t) * vy i + t * vy (Suc i mod length scheme)))"
  proof (intro allI impI)
    fix i assume hi: "i < length scheme"
    let ?f = "\<lambda>t. q ((1-t) * vx i + t * vx (Suc i mod length scheme),
                     (1-t) * vy i + t * vy (Suc i mod length scheme))"
    \<comment> \<open>The affine map t \<mapsto> edge\_i(t) is continuous from I\_set to R2.\<close>
    \<comment> \<open>q is continuous from P to X (quotient map). Compose.\<close>
    have hq_cont: "top1_continuous_map_on P ?TP X TX q"
      using hq unfolding top1_quotient_map_on_def by (by100 blast)
    \<comment> \<open>The affine map is continuous from I\_set to P.\<close>
    have hTI: "is_topology_on I_set top1_unit_interval_topology"
      by (rule top1_unit_interval_topology_is_topology_on)
    \<comment> \<open>The edge points lie in P.\<close>
    have hlen_pos: "length scheme > 0" using assms(2) by (by100 linarith)
    have hi1: "Suc i mod length scheme < length scheme" using hlen_pos by (by100 simp)
    have hvi: "(vx i, vy i) \<in> P" using hverts hi by (by100 blast)
    have hvi1: "(vx (Suc i mod length scheme), vy (Suc i mod length scheme)) \<in> P"
      using hverts hi1 by (by100 blast)
    \<comment> \<open>The edge map lands in P (convex combination of polygon vertices).\<close>
    have hedge_in_P: "\<forall>t\<in>I_set. ((1-t) * vx i + t * vx (Suc i mod length scheme),
                     (1-t) * vy i + t * vy (Suc i mod length scheme)) \<in> P"
    proof (intro ballI)
      fix t assume "t \<in> I_set"
      hence "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by (by100 auto)+
      thus "((1-t) * vx i + t * vx (Suc i mod length scheme),
             (1-t) * vy i + t * vy (Suc i mod length scheme)) \<in> P"
        using polygonal_region_convex_combo[OF hP hlen3 hvi hvi1] by (by100 simp)
    qed
    \<comment> \<open>The composition lands in A.\<close>
    have hf_in_A: "\<forall>t\<in>I_set. ?f t \<in> A"
    proof (intro ballI)
      fix t assume ht: "t \<in> I_set"
      have "?f t \<in> q ` (\<Union>j<length scheme. {((1-s) * vx j + s * vx (Suc j mod length scheme),
                   (1-s) * vy j + s * vy (Suc j mod length scheme)) | s. s \<in> I_set})"
        using hi ht by (by100 blast)
      thus "?f t \<in> A" unfolding hA_eq by (by100 simp)
    qed
    \<comment> \<open>Full proof via composition of continuous maps.\<close>
    \<comment> \<open>Step 1: The affine map is continuous from R to R2.\<close>
    define aff_i :: "real \<Rightarrow> real \<times> real" where
      "aff_i t = ((1-t) * vx i + t * vx (Suc i mod length scheme),
                  (1-t) * vy i + t * vy (Suc i mod length scheme))" for t
    have haff_eq: "\<And>t. ?f t = q (aff_i t)" unfolding aff_i_def by (by100 simp)
    have haff_cont_univ: "continuous_on UNIV aff_i"
      unfolding aff_i_def
      by (intro continuous_intros)
    have haff_in_P: "\<And>t. t \<in> I_set \<Longrightarrow> aff_i t \<in> P"
      using hedge_in_P unfolding aff_i_def by (by100 blast)
    \<comment> \<open>Step 2: Affine map continuous from I\_set to P (restrict domain and range).\<close>
    have haff_cont_I: "top1_continuous_map_on I_set top1_unit_interval_topology P ?TP aff_i"
    proof -
      \<comment> \<open>aff\_i is continuous on UNIV as R \<to> R2. Restrict domain to I\_set, range to P.\<close>
      have h1: "top1_continuous_map_on (UNIV::real set) top1_open_sets
           (UNIV :: (real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets) aff_i"
      proof -
        have "top1_continuous_map_on (UNIV::real set) top1_open_sets
           (UNIV :: (real\<times>real) set)
           (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) UNIV) aff_i"
          using top1_continuous_map_on_R_to_R2_subspace[of aff_i "UNIV :: (real\<times>real) set"]
                haff_cont_univ by (by100 simp)
        moreover have "subspace_topology (UNIV :: (real\<times>real) set)
            (product_topology_on top1_open_sets top1_open_sets) (UNIV :: (real\<times>real) set)
            = product_topology_on top1_open_sets top1_open_sets"
          by (rule subspace_topology_UNIV_self)
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>Restrict domain to I\_set.\<close>
      have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
        by (rule top1_open_sets_is_topology_on_UNIV)
      have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      proof -
        have "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
            (product_topology_on top1_open_sets top1_open_sets)"
          by (rule product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
               top1_open_sets_is_topology_on_UNIV])
        thus ?thesis by (by100 simp)
      qed
      have hP_sub: "P \<subseteq> (UNIV :: (real\<times>real) set)" by (by100 blast)
      have hTR2': "is_topology_on P ?TP"
        using subspace_topology_is_topology_on[OF hTR2 hP_sub] by (by100 blast)
      have h2: "top1_continuous_map_on I_set (subspace_topology UNIV top1_open_sets I_set)
           (UNIV :: (real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets) aff_i"
        using Theorem_18_2(4)[OF hTR hTR2 hTR2'] h1 by (by5000 blast)
      have hI_sub: "top1_unit_interval_topology = subspace_topology UNIV top1_open_sets I_set"
        unfolding top1_unit_interval_topology_def by (by100 simp)
      have h3: "top1_continuous_map_on I_set top1_unit_interval_topology
           (UNIV :: (real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets) aff_i"
        using h2 hI_sub by (by100 simp)
      \<comment> \<open>Restrict range to P.\<close>
      have himg: "aff_i ` I_set \<subseteq> P" using haff_in_P by (by100 blast)
      have hP_sub: "P \<subseteq> (UNIV :: (real\<times>real) set)" by (by100 blast)
      from Theorem_18_2(5)[OF hTI hTR2 hTR2']
      have "\<forall>W f. top1_continuous_map_on I_set top1_unit_interval_topology
           (UNIV :: (real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets) f \<and>
           W \<subseteq> (UNIV :: (real\<times>real) set) \<and> f ` I_set \<subseteq> W \<longrightarrow>
           top1_continuous_map_on I_set top1_unit_interval_topology W
             (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) W) f"
        by (by5000 blast)
      thus ?thesis using h3 hP_sub himg by (by100 blast)
    qed
    \<comment> \<open>Step 3: Compose with q : P \<to> X.\<close>
    have hf_cont_X: "top1_continuous_map_on I_set top1_unit_interval_topology X TX ?f"
    proof -
      have "top1_continuous_map_on I_set top1_unit_interval_topology X TX (q \<circ> aff_i)"
        using top1_continuous_map_on_comp[OF haff_cont_I hq_cont] by (by100 blast)
      moreover have "q \<circ> aff_i = ?f" unfolding aff_i_def comp_def by (by100 auto)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>Step 4: Restrict codomain to A.\<close>
    have hTX_top: "is_topology_on X TX"
      using assms(1) unfolding top1_quotient_of_scheme_on_def is_topology_on_strict_def by (by100 blast)
    have hA_sub_X: "A \<subseteq> X" using hA_closed closedin_sub by (by100 blast)
    have hTA_top: "is_topology_on A (subspace_topology X TX A)"
      using subspace_topology_is_topology_on[OF hTX_top hA_sub_X] by (by100 blast)
    have himg_A: "?f ` I_set \<subseteq> A" using hf_in_A by (by100 blast)
    from Theorem_18_2(5)[OF hTI hTX_top hTA_top]
    show "top1_continuous_map_on I_set top1_unit_interval_topology A (subspace_topology X TX A) ?f"
      using hf_cont_X hA_sub_X himg_A by (by100 blast)
  qed
  \<comment> \<open>Edge-to-arc: h maps circle at angle 2\<pi>(i+t)/n to the edge loop.\<close>
  have hedge_to_arc: "\<forall>i<length scheme. \<forall>t\<in>I_set.
      h (cos (2 * pi * (real i + t) / real (length scheme)),
         sin (2 * pi * (real i + t) / real (length scheme)))
    = q ((1-t) * vx i + t * vx (Suc i mod length scheme),
         (1-t) * vy i + t * vy (Suc i mod length scheme))"
  proof (intro allI impI ballI)
    fix i :: nat and t :: real
    assume hi: "i < length scheme" and ht: "t \<in> I_set"
    \<comment> \<open>From edge-to-arc property of \<psi>: \<psi>(edge\_i(t)) = (cos(\<theta>), sin(\<theta>)).\<close>
    let ?edge_pt = "((1-t) * vx i + t * vx (Suc i mod length scheme),
         (1-t) * vy i + t * vy (Suc i mod length scheme))"
    let ?\<theta> = "2 * pi * (real i + t) / real (length scheme)"
    have h\<psi>_edge: "\<psi> ?edge_pt = (cos ?\<theta>, sin ?\<theta>)"
      using h\<psi>_edge_arc[rule_format, OF hi ht] .
    \<comment> \<open>h = q \<circ> \<psi>^{-1}, so h(cos\<theta>, sin\<theta>) = q(\<psi>^{-1}(cos\<theta>, sin\<theta>)) = q(edge\_pt).\<close>
    have hedge_in_P: "?edge_pt \<in> P"
    proof -
      have "?edge_pt \<in> BdP" unfolding BdP_def
        using hi ht by (by100 blast)
      thus ?thesis using hBdP_sub_P by (by100 blast)
    qed
    hence "\<psi> ?edge_pt \<in> \<psi> ` P" by (by100 blast)
    have h\<psi>_inj: "inj_on \<psi> P"
      using h\<psi>[unfolded top1_homeomorphism_on_def bij_betw_def] by (by100 blast)
    have h_inv: "inv_into P \<psi> (\<psi> ?edge_pt) = ?edge_pt"
      using inv_into_f_f[OF h\<psi>_inj hedge_in_P] by (by100 simp)
    show "h (cos ?\<theta>, sin ?\<theta>) = q ?edge_pt"
      using h_inv h\<psi>_edge unfolding h_def by (by100 simp)
  qed
  show ?thesis
    apply (rule exI[of _ A], rule exI[of _ h], rule exI[of _ a],
           rule exI[of _ q], rule exI[of _ vx], rule exI[of _ vy])
    apply (intro conjI)
    using hA_closed apply (by100 blast)
    using hA_pc apply (by100 blast)
    using hh_cont apply (by100 blast)
    using ha_A apply (by100 blast)
    using hh_homeo apply (by100 assumption)
    using hh_S1 apply (by100 blast)
    using hh_S1' apply (by100 blast)
    using hA_eq apply (by100 blast)
    using ha_eq apply (by100 blast)
    using hvert_all_id apply (by100 blast)
    using hedge apply (by100 blast)
    using hno_extra_cw apply (by100 blast)
    using hq_edge_cont apply (by100 blast)
    using hedge_to_arc apply (by100 blast)
    done
qed

(** === §71.1 chain === **)

text \<open>Inverse of a group isomorphism is a group isomorphism.\<close>
lemma group_iso_on_inverse:
  assumes hiso: "top1_group_iso_on G mulG H mulH f"
      and hG_grp: "top1_is_group_on G mulG eG invgG"
      and hH_grp: "top1_is_group_on H mulH eH invgH"
  shows "top1_group_iso_on H mulH G mulG (inv_into G f)"
proof -
  have hbij: "bij_betw f G H" using hiso unfolding top1_group_iso_on_def by (by100 blast)
  have hhom: "top1_group_hom_on G mulG H mulH f" using hiso unfolding top1_group_iso_on_def by (by100 blast)
  have hinj: "inj_on f G" using hbij unfolding bij_betw_def by (by100 blast)
  have hsurj: "f ` G = H" using hbij unfolding bij_betw_def by (by100 blast)
  have hbij_inv: "bij_betw (inv_into G f) H G"
    using bij_betw_inv_into[OF hbij] by (by100 blast)
  have hhom_inv: "top1_group_hom_on H mulH G mulG (inv_into G f)"
    unfolding top1_group_hom_on_def
  proof (intro conjI allI ballI impI)
    fix x assume "x \<in> H"
    thus "inv_into G f x \<in> G" using hbij_inv unfolding bij_betw_def by (by100 blast)
  next
    fix x y assume "x \<in> H" "y \<in> H"
    \<comment> \<open>Let a = f^{-1}(x), b = f^{-1}(y). Then f(a)=x, f(b)=y.
       f(mulG a b) = mulH (f a) (f b) = mulH x y.
       So f^{-1}(mulH x y) = mulG a b = mulG (f^{-1}(x)) (f^{-1}(y)).\<close>
    have "inv_into G f x \<in> G" using hbij_inv \<open>x \<in> H\<close> unfolding bij_betw_def by (by100 blast)
    have "inv_into G f y \<in> G" using hbij_inv \<open>y \<in> H\<close> unfolding bij_betw_def by (by100 blast)
    have "x \<in> f ` G" using \<open>x \<in> H\<close> hsurj by (by100 simp)
    have "f (inv_into G f x) = x" using f_inv_into_f[OF \<open>x \<in> f ` G\<close>] by (by100 blast)
    have "y \<in> f ` G" using \<open>y \<in> H\<close> hsurj by (by100 simp)
    have "f (inv_into G f y) = y" using f_inv_into_f[OF \<open>y \<in> f ` G\<close>] by (by100 blast)
    have "mulG (inv_into G f x) (inv_into G f y) \<in> G"
      using hG_grp \<open>inv_into G f x \<in> G\<close> \<open>inv_into G f y \<in> G\<close>
      unfolding top1_is_group_on_def by (by100 blast)
    have "f (mulG (inv_into G f x) (inv_into G f y)) =
        mulH (f (inv_into G f x)) (f (inv_into G f y))"
      using hhom \<open>inv_into G f x \<in> G\<close> \<open>inv_into G f y \<in> G\<close>
      unfolding top1_group_hom_on_def by (by100 blast)
    hence "f (mulG (inv_into G f x) (inv_into G f y)) = mulH x y"
      using \<open>f (inv_into G f x) = x\<close> \<open>f (inv_into G f y) = y\<close> by (by100 simp)
    thus "inv_into G f (mulH x y) = mulG (inv_into G f x) (inv_into G f y)"
      using inv_into_f_f[OF hinj \<open>mulG (inv_into G f x) (inv_into G f y) \<in> G\<close>] by (by100 simp)
  qed
  show ?thesis unfolding top1_group_iso_on_def using hhom_inv hbij_inv by (by100 blast)
qed

text \<open>NOTE: free\_product\_factor\_iso\_transfer was planned here but is blocked by
  Isabelle's type system: the free product predicate requires all factor groups
  to have the same element type, so transferring from int-typed to 'a set-typed
  factors requires a type-level change that can't be expressed within a single
  top1\_is\_free\_product\_on statement. The bijectivity proof uses a different route.\<close>

text \<open>A hom between free groups on the same index set that maps generators to generators
  is an isomorphism. Standard free group fact from the universal property.\<close>
lemma free_group_hom_generators_iso:
  assumes hG: "top1_is_free_group_full_on G mulG eG invgG iotaG S"
      and hH: "top1_is_free_group_full_on H mulH eH invgH iotaH S"
      and hf: "top1_group_hom_on G mulG H mulH f"
      and hgen: "\<forall>s \<in> S. f (iotaG s) = iotaH s"
  shows "bij_betw f G H"
proof -
  \<comment> \<open>Construct inverse: \<Psi>: H \<rightarrow> G with \<Psi>(iotaH(s)) = iotaG(s).\<close>
  have hG_grp: "top1_is_group_on G mulG eG invgG"
    using hG unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hH_grp: "top1_is_group_on H mulH eH invgH"
    using hH unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hiotaG_in: "\<forall>s\<in>S. iotaG s \<in> G"
    using hG unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hiotaH_in: "\<forall>s\<in>S. iotaH s \<in> H"
    using hH unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hG_gen: "G = top1_subgroup_generated_on G mulG eG invgG (iotaG ` S)"
    using hG unfolding top1_is_free_group_full_on_def by (by100 blast)
  have hH_gen: "H = top1_subgroup_generated_on H mulH eH invgH (iotaH ` S)"
    using hH unfolding top1_is_free_group_full_on_def by (by100 blast)
  from free_group_hom_exists[OF hH hG_grp hiotaG_in]
  obtain \<Psi> where h\<Psi>_hom: "top1_group_hom_on H mulH G mulG \<Psi>"
    and h\<Psi>_gen: "\<forall>s\<in>S. \<Psi> (iotaH s) = iotaG s"
    by (by100 blast)
  \<comment> \<open>\<Psi> \<circ> f = id on G: (\<Psi>\<circ>f)(iotaG(s)) = \<Psi>(iotaH(s)) = iotaG(s) = id(iotaG(s)).
     By free\_group\_hom\_unique, \<Psi>\<circ>f = id on all of G.\<close>
  \<comment> \<open>\<Psi> \<circ> f is a hom G \<rightarrow> G. id is a hom G \<rightarrow> G. Both map iotaG(s) to iotaG(s).\<close>
  have hPsif_hom: "top1_group_hom_on G mulG G mulG (\<lambda>x. \<Psi> (f x))"
    using group_hom_comp[OF hf h\<Psi>_hom] unfolding comp_def by (by100 blast)
  have hid_hom: "top1_group_hom_on G mulG G mulG (\<lambda>x. x)"
    using group_hom_id[OF hG_grp] unfolding id_def by (by100 blast)
  have hPsif_gen: "\<forall>s\<in>S. \<Psi> (f (iotaG s)) = iotaG s"
  proof
    fix s assume "s \<in> S"
    have "f (iotaG s) = iotaH s" using hgen \<open>s \<in> S\<close> by (by100 blast)
    thus "\<Psi> (f (iotaG s)) = iotaG s" using h\<Psi>_gen \<open>s \<in> S\<close> by (by100 simp)
  qed
  have hcomp1: "\<forall>x\<in>G. \<Psi> (f x) = x"
    using free_group_hom_unique[OF hG_grp hG_grp hG_gen hiotaG_in hPsif_hom hid_hom]
          hPsif_gen by (by100 blast)
  \<comment> \<open>Similarly: f \<circ> \<Psi> = id on H.\<close>
  have hfPsi_hom: "top1_group_hom_on H mulH H mulH (\<lambda>y. f (\<Psi> y))"
    using group_hom_comp[OF h\<Psi>_hom hf] unfolding comp_def by (by100 blast)
  have hidH_hom: "top1_group_hom_on H mulH H mulH (\<lambda>y. y)"
    using group_hom_id[OF hH_grp] unfolding id_def by (by100 blast)
  have hfPsi_gen: "\<forall>s\<in>S. f (\<Psi> (iotaH s)) = iotaH s"
  proof
    fix s assume "s \<in> S"
    have "\<Psi> (iotaH s) = iotaG s" using h\<Psi>_gen \<open>s \<in> S\<close> by (by100 blast)
    thus "f (\<Psi> (iotaH s)) = iotaH s" using hgen \<open>s \<in> S\<close> by (by100 simp)
  qed
  have hcomp2: "\<forall>y\<in>H. f (\<Psi> y) = y"
    using free_group_hom_unique[OF hH_grp hH_grp hH_gen hiotaH_in hfPsi_hom hidH_hom]
          hfPsi_gen by (by100 blast)
  \<comment> \<open>From left/right inverse: f bijective.\<close>
  show ?thesis unfolding bij_betw_def
  proof (intro conjI)
    \<comment> \<open>Injective: if f(x) = f(y) then x = \<Psi>(f(x)) = \<Psi>(f(y)) = y.\<close>
    show "inj_on f G"
    proof (rule inj_onI)
      fix x y assume "x \<in> G" "y \<in> G" "f x = f y"
      have "x = \<Psi> (f x)" using hcomp1 \<open>x \<in> G\<close> by (by100 simp)
      also have "\<dots> = \<Psi> (f y)" using \<open>f x = f y\<close> by (by100 simp)
      also have "\<dots> = y" using hcomp1 \<open>y \<in> G\<close> by (by100 simp)
      finally show "x = y" .
    qed
    \<comment> \<open>Surjective: for y \<in> H, \<Psi>(y) \<in> G and f(\<Psi>(y)) = y.\<close>
    show "f ` G = H"
    proof (rule set_eqI, rule iffI)
      fix y assume "y \<in> f ` G"
      then obtain x where "x \<in> G" "y = f x" by (by100 blast)
      have "\<forall>x\<in>G. f x \<in> H" using hf unfolding top1_group_hom_on_def by (by100 blast)
      thus "y \<in> H" using \<open>x \<in> G\<close> \<open>y = f x\<close> by (by100 blast)
    next
      fix y assume "y \<in> H"
      have h\<Psi>_maps: "\<forall>y\<in>H. \<Psi> y \<in> G"
        using h\<Psi>_hom unfolding top1_group_hom_on_def by (by100 blast)
      have "\<Psi> y \<in> G" using h\<Psi>_maps \<open>y \<in> H\<close> by (by100 blast)
      moreover have "f (\<Psi> y) = y" using hcomp2 \<open>y \<in> H\<close> by (by100 blast)
      ultimately have "f (\<Psi> y) \<in> f ` G" by (by100 blast)
      thus "y \<in> f ` G" using \<open>f (\<Psi> y) = y\<close> by (by100 simp)
    qed
  qed
qed

text \<open>Helper: extract the free product part of Theorem 69.2.\<close>
lemma Theorem_69_2_free_product_part:
  assumes hG1: "top1_is_free_group_full_on G1 mul1 e1 invg1 iota1 S1"
      and hG2: "top1_is_free_group_full_on G2 mul2 e2 invg2 iota2 S2"
      and hS: "S1 \<inter> S2 = {}"
  shows "\<exists>(FP :: (nat \<times> 'a) list set) (mulFP :: (nat \<times> 'a) list \<Rightarrow> (nat \<times> 'a) list \<Rightarrow> (nat \<times> 'a) list) (eFP :: (nat \<times> 'a) list) (invgFP :: (nat \<times> 'a) list \<Rightarrow> (nat \<times> 'a) list) (iotafam :: nat \<Rightarrow> 'a \<Rightarrow> (nat \<times> 'a) list).
      top1_is_free_product_on FP mulFP eFP invgFP
        (\<lambda>i::nat. if i = 0 then G1 else G2) (\<lambda>i. if i = 0 then mul1 else mul2)
        iotafam {0::nat, 1}
    \<and> (\<exists>iotaS. top1_is_free_group_full_on FP mulFP eFP invgFP iotaS (S1 \<union> S2))"
proof -
  from Theorem_69_2[OF hG1 hG2 hS] show ?thesis
  proof -
    note hex = Theorem_69_2[OF hG1 hG2 hS]
    \<comment> \<open>hex has the Theorem\_69\_2 result with schematic internal names.
       The thesis requires the same structure but with possibly different names.
       Use ML-level or schematic_goal to match.\<close>
    from hex show ?thesis
      apply (elim exE conjE)
      subgoal for fp_w mul_w e_w invg_w iotafam_w iotaS_w
        apply (rule_tac x=fp_w in exI)
        apply (rule_tac x=mul_w in exI)
        apply (rule_tac x=e_w in exI)
        apply (rule_tac x=invg_w in exI)
        apply (rule_tac x=iotafam_w in exI)
        apply (rule conjI)
        apply assumption
        apply (rule_tac x=iotaS_w in exI)
        apply assumption
        done
      done
  qed
qed

text \<open>SvK with generator tracking: the specific hom FP \<rightarrow> \<pi>\_1(X) from
  Lemma\_68\_3 (extending the inclusion maps) IS the SvK iso.
  It maps iotafam(0,c) \<rightarrow> j\_U*(c) and iotafam(1,c) \<rightarrow> j\_V*(c).\<close>
lemma svk_iso_with_tracking:
  assumes hstrict: "is_topology_on_strict X TX"
      and hU_open: "openin_on X TX U" and hV_open: "openin_on X TX V"
      and hUV_cover: "U \<union> V = X"
      and hUV_sc: "top1_simply_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and hU_pc: "top1_path_connected_on U (subspace_topology X TX U)"
      and hV_pc: "top1_path_connected_on V (subspace_topology X TX V)"
      and hp: "p \<in> U \<inter> V"
      and hFP: "top1_is_free_product_on FP mulFP eFP invgFP
          (\<lambda>i::nat. if i = 0
             then top1_fundamental_group_carrier U (subspace_topology X TX U) p
             else top1_fundamental_group_carrier V (subspace_topology X TX V) p)
          (\<lambda>i. if i = 0
             then top1_fundamental_group_mul U (subspace_topology X TX U) p
             else top1_fundamental_group_mul V (subspace_topology X TX V) p)
          iotafam {0::nat, 1}"
  shows "\<exists>h. top1_group_iso_on FP mulFP
      (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p) h
    \<and> (\<forall>c \<in> top1_fundamental_group_carrier U (subspace_topology X TX U) p.
        h (iotafam 0 c) = top1_fundamental_group_induced_on U (subspace_topology X TX U) p X TX p (\<lambda>x. x) c)
    \<and> (\<forall>c \<in> top1_fundamental_group_carrier V (subspace_topology X TX V) p.
        h (iotafam 1 c) = top1_fundamental_group_induced_on V (subspace_topology X TX V) p X TX p (\<lambda>x. x) c)"
proof -
  let ?TU = "subspace_topology X TX U" and ?TV = "subspace_topology X TX V"
  let ?TUV = "subspace_topology X TX (U \<inter> V)"
  let ?\<pi>X = "top1_fundamental_group_carrier X TX p"
  let ?mX = "top1_fundamental_group_mul X TX p"
  let ?eX = "top1_fundamental_group_id X TX p"
  let ?iX = "top1_fundamental_group_invg X TX p"
  let ?\<pi>U = "top1_fundamental_group_carrier U ?TU p"
  let ?mU = "top1_fundamental_group_mul U ?TU p"
  let ?eU = "top1_fundamental_group_id U ?TU p"
  let ?iU = "top1_fundamental_group_invg U ?TU p"
  let ?\<pi>V = "top1_fundamental_group_carrier V ?TV p"
  let ?mV = "top1_fundamental_group_mul V ?TV p"
  let ?eV = "top1_fundamental_group_id V ?TV p"
  let ?iV = "top1_fundamental_group_invg V ?TV p"
  let ?jU = "top1_fundamental_group_induced_on U ?TU p X TX p (\<lambda>x. x)"
  let ?jV = "top1_fundamental_group_induced_on V ?TV p X TX p (\<lambda>x. x)"
  define GG where "GG \<equiv> (\<lambda>i::nat. if i = 0 then ?\<pi>U else ?\<pi>V)"
  define mulGG where "mulGG \<equiv> (\<lambda>i::nat. if i = 0 then ?mU else ?mV)"
  \<comment> \<open>Basic topology/group facts.\<close>
  have hTX: "is_topology_on X TX" using hstrict unfolding is_topology_on_strict_def
    by (by100 blast)
  have hUsub: "U \<subseteq> X" using hU_open unfolding openin_on_def by (by100 blast)
  have hVsub: "V \<subseteq> X" using hV_open unfolding openin_on_def by (by100 blast)
  have hp_X: "p \<in> X" using hp hUsub by (by100 blast)
  have hp_U: "p \<in> U" using hp by (by100 blast)
  have hp_V: "p \<in> V" using hp by (by100 blast)
  have hTU: "is_topology_on U ?TU" using subspace_topology_is_topology_on[OF hTX hUsub] .
  have hTV: "is_topology_on V ?TV" using subspace_topology_is_topology_on[OF hTX hVsub] .
  have hUVsub: "U \<inter> V \<subseteq> X" using hUsub hVsub by (by100 blast)
  have hTUV: "is_topology_on (U \<inter> V) ?TUV"
    using subspace_topology_is_topology_on[OF hTX hUVsub] .
  have hUV_pc: "top1_path_connected_on (U \<inter> V) ?TUV"
    using hUV_sc top1_simply_connected_on_path_connected by (by100 blast)
  have hpi1X_grp: "top1_is_group_on ?\<pi>X ?mX ?eX ?iX"
    using top1_fundamental_group_is_group[OF hTX hp_X] by (by100 blast)
  have hpi1U_grp: "top1_is_group_on ?\<pi>U ?mU ?eU ?iU"
    using top1_fundamental_group_is_group[OF hTU hp_U] by (by100 blast)
  have hpi1V_grp: "top1_is_group_on ?\<pi>V ?mV ?eV ?iV"
    using top1_fundamental_group_is_group[OF hTV hp_V] by (by100 blast)
  have hFP_grp: "top1_is_group_on FP mulFP eFP invgFP"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  \<comment> \<open>Inclusion-induced maps are group homs.\<close>
  have hjU_hom: "top1_group_hom_on ?\<pi>U ?mU ?\<pi>X ?mX ?jU"
    using subspace_inclusion_induced_hom[OF hTX hUsub hp_U] by (by100 blast)
  have hjV_hom: "top1_group_hom_on ?\<pi>V ?mV ?\<pi>X ?mX ?jV"
    using subspace_inclusion_induced_hom[OF hTX hVsub hp_V] by (by100 blast)
  \<comment> \<open>iotafam maps are group homs (from free product definition).\<close>
  \<comment> \<open>Extract free product conditions for iotafam.\<close>
  have hFP_mem: "\<forall>a\<in>{0::nat,1}. \<forall>x\<in>(if a = 0 then ?\<pi>U else ?\<pi>V). iotafam a x \<in> FP"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have hFP_mul: "\<forall>a\<in>{0::nat,1}. \<forall>x\<in>(if a = 0 then ?\<pi>U else ?\<pi>V).
      \<forall>y\<in>(if a = 0 then ?\<pi>U else ?\<pi>V).
      iotafam a ((if a = 0 then ?mU else ?mV) x y) = mulFP (iotafam a x) (iotafam a y)"
    using hFP unfolding top1_is_free_product_on_def by (by100 blast)
  have hiotafam0_in: "\<forall>x\<in>?\<pi>U. iotafam 0 x \<in> FP"
    using hFP_mem by (by100 force)
  have hiotafam0_mul: "\<forall>x\<in>?\<pi>U. \<forall>y\<in>?\<pi>U. iotafam 0 (?mU x y) = mulFP (iotafam 0 x) (iotafam 0 y)"
    using hFP_mul by (by100 force)
  have hiotafam0_hom: "top1_group_hom_on ?\<pi>U ?mU FP mulFP (iotafam 0)"
    unfolding top1_group_hom_on_def using hiotafam0_in hiotafam0_mul by (by100 blast)
  have hiotafam1_in: "\<forall>x\<in>?\<pi>V. iotafam 1 x \<in> FP"
  proof
    fix x assume "x \<in> ?\<pi>V"
    have "(1::nat) \<in> {0::nat,1}" by (by100 blast)
    have "(if (1::nat) = 0 then ?\<pi>U else ?\<pi>V) = ?\<pi>V" by (by100 simp)
    thus "iotafam 1 x \<in> FP"
      using hFP_mem \<open>x \<in> ?\<pi>V\<close> \<open>(1::nat) \<in> {0::nat,1}\<close> by (by100 force)
  qed
  have hiotafam1_mul: "\<forall>x\<in>?\<pi>V. \<forall>y\<in>?\<pi>V. iotafam 1 (?mV x y) = mulFP (iotafam 1 x) (iotafam 1 y)"
  proof (intro ballI)
    fix x y assume "x \<in> ?\<pi>V" "y \<in> ?\<pi>V"
    have h1: "(1::nat) \<in> {0::nat,1}" by (by100 blast)
    have "iotafam 1 ((if (1::nat) = 0 then ?mU else ?mV) x y)
        = mulFP (iotafam 1 x) (iotafam 1 y)"
      using hFP_mul[rule_format, OF h1] \<open>x \<in> ?\<pi>V\<close> \<open>y \<in> ?\<pi>V\<close> by (by100 force)
    thus "iotafam 1 (?mV x y) = mulFP (iotafam 1 x) (iotafam 1 y)" by (by100 simp)
  qed
  have hiotafam1_hom: "top1_group_hom_on ?\<pi>V ?mV FP mulFP (iotafam 1)"
    unfolding top1_group_hom_on_def using hiotafam1_in hiotafam1_mul by (by100 blast)
  \<comment> \<open>Step 1: Lemma\_68\_3 gives h: FP \<rightarrow> \<pi>\_1(X) extending j\_U*, j\_V*.\<close>
  have h683_hfam: "\<forall>a\<in>{0::nat, 1}. top1_group_hom_on (GG a) (mulGG a) ?\<pi>X ?mX
      (\<lambda>c. if a = 0 then ?jU c else ?jV c)"
  proof (intro ballI)
    fix a assume "a \<in> {0::nat, 1}"
    show "top1_group_hom_on (GG a) (mulGG a) ?\<pi>X ?mX (\<lambda>c. if a = 0 then ?jU c else ?jV c)"
    proof (cases "a = 0")
      case True thus ?thesis unfolding GG_def mulGG_def using hjU_hom by (by100 simp)
    next
      case False
      hence "a = 1" using \<open>a \<in> {0::nat, 1}\<close> by (by100 blast)
      thus ?thesis unfolding GG_def mulGG_def using hjV_hom by (by100 simp)
    qed
  qed
  have h683_grps: "\<forall>a\<in>{0::nat, 1}. top1_is_group_on (GG a) (mulGG a)
      (if a = 0 then ?eU else ?eV) (if a = 0 then ?iU else ?iV)"
  proof (intro ballI)
    fix a assume "a \<in> {0::nat, 1}"
    show "top1_is_group_on (GG a) (mulGG a)
        (if a = 0 then ?eU else ?eV) (if a = 0 then ?iU else ?iV)"
    proof (cases "a = 0")
      case True thus ?thesis unfolding GG_def mulGG_def using hpi1U_grp by (by100 simp)
    next
      case False
      hence "a = 1" using \<open>a \<in> {0::nat, 1}\<close> by (by100 blast)
      thus ?thesis unfolding GG_def mulGG_def using hpi1V_grp by (by100 simp)
    qed
  qed
  note h683_result = Lemma_68_3_extension_property[OF hFP[folded GG_def mulGG_def] hpi1X_grp h683_hfam h683_grps]
  define h where "h \<equiv> SOME h. top1_group_hom_on FP mulFP ?\<pi>X ?mX h
    \<and> (\<forall>a\<in>{0::nat, 1}. \<forall>x\<in>GG a. h (iotafam a x) = (if a = 0 then ?jU x else ?jV x))
    \<and> (\<forall>h'. top1_group_hom_on FP mulFP ?\<pi>X ?mX h'
        \<longrightarrow> (\<forall>a\<in>{0::nat, 1}. \<forall>x\<in>GG a. h' (iotafam a x) = (if a = 0 then ?jU x else ?jV x))
        \<longrightarrow> (\<forall>g\<in>FP. h' g = h g))"
  have hh_props: "top1_group_hom_on FP mulFP ?\<pi>X ?mX h
    \<and> (\<forall>a\<in>{0::nat, 1}. \<forall>x\<in>GG a. h (iotafam a x) = (if a = 0 then ?jU x else ?jV x))
    \<and> (\<forall>h'. top1_group_hom_on FP mulFP ?\<pi>X ?mX h'
        \<longrightarrow> (\<forall>a\<in>{0::nat, 1}. \<forall>x\<in>GG a. h' (iotafam a x) = (if a = 0 then ?jU x else ?jV x))
        \<longrightarrow> (\<forall>g\<in>FP. h' g = h g))"
    unfolding h_def using someI_ex[OF h683_result] by (by5000 blast)
  have hh_hom: "top1_group_hom_on FP mulFP ?\<pi>X ?mX h"
    using hh_props by (by100 blast)
  have hh_track: "\<forall>a\<in>{0::nat, 1}. \<forall>x\<in>GG a. h (iotafam a x) = (if a = 0 then ?jU x else ?jV x)"
    using hh_props by (by100 blast)
  \<comment> \<open>Extract specific tracking for U and V.\<close>
  have hh_trackU: "\<forall>c\<in>?\<pi>U. h (iotafam 0 c) = ?jU c"
    using hh_track unfolding GG_def by (by100 simp)
  have hh_trackV: "\<forall>c\<in>?\<pi>V. h (iotafam 1 c) = ?jV c"
    using hh_track unfolding GG_def by (by100 force)
  \<comment> \<open>Step 2: Theorem\_70\_1 gives \<Phi>: \<pi>\_1(X) \<rightarrow> FP extending iotafam(0), iotafam(1).\<close>
  \<comment> \<open>Compatibility condition: trivial since U\<inter>V simply connected.\<close>
  \<comment> \<open>Compatibility condition: trivial since U\<inter>V simply connected, so \<pi>\_1(U\<inter>V) = \{e\}.\<close>
  have hUV_trivial: "top1_fundamental_group_carrier (U \<inter> V) ?TUV p
      = {top1_fundamental_group_id (U \<inter> V) ?TUV p}"
    using simply_connected_trivial_carrier[OF hUV_sc hp] by (by100 blast)
  \<comment> \<open>iotafam(0) and iotafam(1) are homs, so they send identities to eFP.\<close>
  have hiotafam0_e: "iotafam 0 ?eU = eFP"
    using hom_preserves_id[OF hpi1U_grp hFP_grp hiotafam0_hom] by (by100 blast)
  have hiotafam1_e: "iotafam 1 ?eV = eFP"
    using hom_preserves_id[OF hpi1V_grp hFP_grp hiotafam1_hom] by (by100 blast)
  \<comment> \<open>Inclusion-induced maps U\<inter>V \<rightarrow> U and U\<inter>V \<rightarrow> V send the identity to identity.\<close>
  \<comment> \<open>Iterated subspace: subspace(U, subspace(X,TX,U), U\<inter>V) = subspace(X,TX,U\<inter>V).\<close>
  have hUV_sub_U: "U \<inter> V \<subseteq> U" by (by100 blast)
  have hUV_sub_V: "U \<inter> V \<subseteq> V" by (by100 blast)
  have hiter_U: "subspace_topology U ?TU (U \<inter> V) = ?TUV"
    using subspace_topology_trans[OF hUV_sub_U] by (by100 blast)
  have hiter_V: "subspace_topology V ?TV (U \<inter> V) = ?TUV"
    using subspace_topology_trans[OF hUV_sub_V] by (by100 blast)
  \<comment> \<open>Inclusion U\<inter>V \<rightarrow> U is a group hom (via subspace\_inclusion\_induced\_hom on U).\<close>
  have hjUV_U_hom_raw: "top1_group_hom_on
      (top1_fundamental_group_carrier (U \<inter> V) (subspace_topology U ?TU (U \<inter> V)) p)
      (top1_fundamental_group_mul (U \<inter> V) (subspace_topology U ?TU (U \<inter> V)) p)
      ?\<pi>U ?mU (top1_fundamental_group_induced_on (U \<inter> V) (subspace_topology U ?TU (U \<inter> V)) p U ?TU p (\<lambda>x. x))"
    using subspace_inclusion_induced_hom[OF hTU hUV_sub_U hp] by (by100 blast)
  have hjUV_U_hom: "top1_group_hom_on
      (top1_fundamental_group_carrier (U \<inter> V) ?TUV p)
      (top1_fundamental_group_mul (U \<inter> V) ?TUV p)
      ?\<pi>U ?mU (top1_fundamental_group_induced_on (U \<inter> V) ?TUV p U ?TU p (\<lambda>x. x))"
    using hjUV_U_hom_raw unfolding hiter_U by (by100 blast)
  have hjUV_V_hom_raw: "top1_group_hom_on
      (top1_fundamental_group_carrier (U \<inter> V) (subspace_topology V ?TV (U \<inter> V)) p)
      (top1_fundamental_group_mul (U \<inter> V) (subspace_topology V ?TV (U \<inter> V)) p)
      ?\<pi>V ?mV (top1_fundamental_group_induced_on (U \<inter> V) (subspace_topology V ?TV (U \<inter> V)) p V ?TV p (\<lambda>x. x))"
    using subspace_inclusion_induced_hom[OF hTV hUV_sub_V hp] by (by100 blast)
  have hjUV_V_hom: "top1_group_hom_on
      (top1_fundamental_group_carrier (U \<inter> V) ?TUV p)
      (top1_fundamental_group_mul (U \<inter> V) ?TUV p)
      ?\<pi>V ?mV (top1_fundamental_group_induced_on (U \<inter> V) ?TUV p V ?TV p (\<lambda>x. x))"
    using hjUV_V_hom_raw unfolding hiter_V by (by100 blast)
  \<comment> \<open>π₁(U∩V) is a group.\<close>
  have hpi1UV_grp: "top1_is_group_on
      (top1_fundamental_group_carrier (U \<inter> V) ?TUV p)
      (top1_fundamental_group_mul (U \<inter> V) ?TUV p)
      (top1_fundamental_group_id (U \<inter> V) ?TUV p)
      (top1_fundamental_group_invg (U \<inter> V) ?TUV p)"
    using top1_fundamental_group_is_group[OF hTUV hp] by (by100 blast)
  have hjUV_U_id: "top1_fundamental_group_induced_on (U \<inter> V) ?TUV p U ?TU p (\<lambda>x. x)
      (top1_fundamental_group_id (U \<inter> V) ?TUV p) = ?eU"
    using hom_preserves_id[OF hpi1UV_grp hpi1U_grp hjUV_U_hom] by (by100 blast)
  have hjUV_V_id: "top1_fundamental_group_induced_on (U \<inter> V) ?TUV p V ?TV p (\<lambda>x. x)
      (top1_fundamental_group_id (U \<inter> V) ?TUV p) = ?eV"
    using hom_preserves_id[OF hpi1UV_grp hpi1V_grp hjUV_V_hom] by (by100 blast)
  have hcompat: "\<forall>c\<in>top1_fundamental_group_carrier (U \<inter> V) ?TUV p.
      iotafam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV p U ?TU p (\<lambda>x. x) c)
    = iotafam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV p V ?TV p (\<lambda>x. x) c)"
  proof
    fix c assume "c \<in> top1_fundamental_group_carrier (U \<inter> V) ?TUV p"
    hence "c = top1_fundamental_group_id (U \<inter> V) ?TUV p" using hUV_trivial by (by100 blast)
    thus "iotafam 0 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV p U ?TU p (\<lambda>x. x) c)
        = iotafam 1 (top1_fundamental_group_induced_on (U \<inter> V) ?TUV p V ?TV p (\<lambda>x. x) c)"
      using hjUV_U_id hjUV_V_id hiotafam0_e hiotafam1_e by (by100 simp)
  qed
  from Theorem_70_1_universal_property[OF hstrict hU_open hV_open hUV_cover hUV_pc hU_pc hV_pc hp
      hFP_grp hiotafam0_hom hiotafam1_hom hcompat]
  obtain \<Phi> where h\<Phi>_hom: "top1_group_hom_on ?\<pi>X ?mX FP mulFP \<Phi>"
    and h\<Phi>_trackU: "\<forall>a\<in>?\<pi>U. \<Phi> (?jU a) = iotafam 0 a"
    and h\<Phi>_trackV: "\<forall>b\<in>?\<pi>V. \<Phi> (?jV b) = iotafam 1 b"
    by (by5000 blast)
  \<comment> \<open>Step 3: h \<circ> \<Phi> = id on \<pi>\_1(X) via Theorem\_70\_1\_uniqueness.\<close>
  have hhPhi_hom: "top1_group_hom_on ?\<pi>X ?mX ?\<pi>X ?mX (h \<circ> \<Phi>)"
    using group_hom_comp[OF h\<Phi>_hom hh_hom] by (by100 blast)
  have hid_hom: "top1_group_hom_on ?\<pi>X ?mX ?\<pi>X ?mX id"
    using group_hom_id[OF hpi1X_grp] by (by100 blast)
  \<comment> \<open>h \<circ> \<Phi> and id agree on j\_U* and j\_V* images.\<close>
  have hhPhi_eqU: "\<forall>a\<in>?\<pi>U. (h \<circ> \<Phi>) (?jU a) = id (?jU a)"
  proof
    fix a assume "a \<in> ?\<pi>U"
    have "(h \<circ> \<Phi>) (?jU a) = h (iotafam 0 a)" using h\<Phi>_trackU \<open>a \<in> ?\<pi>U\<close> by (by100 simp)
    also have "\<dots> = ?jU a" using hh_trackU \<open>a \<in> ?\<pi>U\<close> by (by100 blast)
    finally show "(h \<circ> \<Phi>) (?jU a) = id (?jU a)" by (by100 simp)
  qed
  have hhPhi_eqV: "\<forall>b\<in>?\<pi>V. (h \<circ> \<Phi>) (?jV b) = id (?jV b)"
  proof
    fix b assume "b \<in> ?\<pi>V"
    have "(h \<circ> \<Phi>) (?jV b) = h (iotafam 1 b)" using h\<Phi>_trackV \<open>b \<in> ?\<pi>V\<close> by (by100 simp)
    also have "\<dots> = ?jV b" using hh_trackV \<open>b \<in> ?\<pi>V\<close> by (by100 blast)
    finally show "(h \<circ> \<Phi>) (?jV b) = id (?jV b)" by (by100 simp)
  qed
  from Theorem_70_1_uniqueness[OF hstrict hU_open hV_open hUV_cover hUV_pc hU_pc hV_pc hp
      hpi1X_grp hhPhi_hom hid_hom hhPhi_eqU hhPhi_eqV]
  have hhPhi_id: "\<forall>c\<in>?\<pi>X. (h \<circ> \<Phi>) c = c" by (by100 simp)
  \<comment> \<open>Step 4: \<Phi> \<circ> h = id on FP via Lemma\_68\_3 uniqueness.\<close>
  have hPhih_hom: "top1_group_hom_on FP mulFP FP mulFP (\<Phi> \<circ> h)"
    using group_hom_comp[OF hh_hom h\<Phi>_hom] by (by100 blast)
  have hFPid_hom: "top1_group_hom_on FP mulFP FP mulFP id"
    using group_hom_id[OF hFP_grp] by (by100 blast)
  \<comment> \<open>\<Phi> \<circ> h and id agree on iotafam images.\<close>
  \<comment> \<open>Both \<Phi> \<circ> h and id extend the same maps on the factors, so they agree on FP.\<close>
  have hPhih_on_factors: "\<forall>a\<in>{0::nat, 1}. \<forall>x\<in>GG a. (\<Phi> \<circ> h) (iotafam a x) = iotafam a x"
  proof (intro ballI)
    fix a x assume "a \<in> {0::nat, 1}" "x \<in> GG a"
    show "(\<Phi> \<circ> h) (iotafam a x) = iotafam a x"
    proof (cases "a = 0")
      case True
      hence "x \<in> ?\<pi>U" using \<open>x \<in> GG a\<close> unfolding GG_def by (by100 simp)
      have "(\<Phi> \<circ> h) (iotafam 0 x) = \<Phi> (h (iotafam 0 x))" by (by100 simp)
      also have "\<dots> = \<Phi> (?jU x)" using hh_trackU \<open>x \<in> ?\<pi>U\<close> by (by100 simp)
      also have "\<dots> = iotafam 0 x" using h\<Phi>_trackU \<open>x \<in> ?\<pi>U\<close> by (by100 blast)
      finally show ?thesis using True by (by100 simp)
    next
      case False
      hence "a = 1" using \<open>a \<in> {0::nat, 1}\<close> by (by100 blast)
      hence "x \<in> ?\<pi>V" using \<open>x \<in> GG a\<close> unfolding GG_def by (by100 simp)
      have "(\<Phi> \<circ> h) (iotafam 1 x) = \<Phi> (h (iotafam 1 x))" by (by100 simp)
      also have "\<dots> = \<Phi> (?jV x)" using hh_trackV \<open>x \<in> ?\<pi>V\<close> by (by100 simp)
      also have "\<dots> = iotafam 1 x" using h\<Phi>_trackV \<open>x \<in> ?\<pi>V\<close> by (by100 blast)
      finally show ?thesis using \<open>a = 1\<close> by (by100 simp)
    qed
  qed
  \<comment> \<open>id also maps iotafam images to themselves.\<close>
  have hid_on_factors: "\<forall>a\<in>{0::nat, 1}. \<forall>x\<in>GG a. id (iotafam a x) = iotafam a x"
    by (by100 simp)
  \<comment> \<open>Both \<Phi>\<circ>h and id extend the same factor maps, so by Lemma\_68\_3 uniqueness on FP
     (which is a separate use with H = FP), they agree on all of FP.\<close>
  have h_grps_for_68_3: "\<forall>a\<in>{0::nat, 1}. top1_is_group_on (GG a) (mulGG a)
      (if a = 0 then ?eU else ?eV) (if a = 0 then ?iU else ?iV)"
    using h683_grps by (by100 blast)
  have hiotafam_homs: "\<forall>a\<in>{0::nat, 1}. top1_group_hom_on (GG a) (mulGG a) FP mulFP
      (\<lambda>x. iotafam a x)"
  proof (intro ballI)
    fix a assume "a \<in> {0::nat, 1}"
    show "top1_group_hom_on (GG a) (mulGG a) FP mulFP (\<lambda>x. iotafam a x)"
    proof (cases "a = 0")
      case True thus ?thesis unfolding GG_def mulGG_def using hiotafam0_hom by (by100 simp)
    next
      case False
      hence "a = 1" using \<open>a \<in> {0::nat, 1}\<close> by (by100 blast)
      thus ?thesis unfolding GG_def mulGG_def using hiotafam1_hom by (by100 simp)
    qed
  qed
  from Lemma_68_3_extension_property[OF hFP[folded GG_def mulGG_def] hFP_grp hiotafam_homs h_grps_for_68_3]
  obtain h_ext where hh_ext_hom: "top1_group_hom_on FP mulFP FP mulFP h_ext"
    and hh_ext_track: "\<forall>a\<in>{0::nat, 1}. \<forall>x\<in>GG a. h_ext (iotafam a x) = iotafam a x"
    and hh_ext_unique: "\<forall>h'. top1_group_hom_on FP mulFP FP mulFP h'
        \<longrightarrow> (\<forall>a\<in>{0::nat, 1}. \<forall>x\<in>GG a. h' (iotafam a x) = iotafam a x)
        \<longrightarrow> (\<forall>g\<in>FP. h' g = h_ext g)"
    by (by5000 blast)
  \<comment> \<open>Both \<Phi>\<circ>h and id satisfy the conditions, so they equal h\_ext on FP.\<close>
  have hPhih_eq: "\<forall>g\<in>FP. (\<Phi> \<circ> h) g = h_ext g"
    using hh_ext_unique hPhih_hom hPhih_on_factors by (by100 blast)
  have hid_eq: "\<forall>g\<in>FP. id g = h_ext g"
    using hh_ext_unique hFPid_hom hid_on_factors by (by100 blast)
  have hPhih_id_FP: "\<forall>g\<in>FP. (\<Phi> \<circ> h) g = g"
  proof
    fix g assume "g \<in> FP"
    have "(\<Phi> \<circ> h) g = h_ext g" using hPhih_eq \<open>g \<in> FP\<close> by (by100 blast)
    also have "\<dots> = id g" using hid_eq \<open>g \<in> FP\<close> by (by100 simp)
    finally show "(\<Phi> \<circ> h) g = g" by (by100 simp)
  qed
  \<comment> \<open>Step 5: h is bijective (h \<circ> \<Phi> = id AND \<Phi> \<circ> h = id gives mutual inverses).\<close>
  have hh_surj: "h ` FP = ?\<pi>X"
  proof
    show "h ` FP \<subseteq> ?\<pi>X"
      using hh_hom unfolding top1_group_hom_on_def by (by100 blast)
    show "?\<pi>X \<subseteq> h ` FP"
    proof
      fix c assume "c \<in> ?\<pi>X"
      have "\<Phi> c \<in> FP" using h\<Phi>_hom \<open>c \<in> ?\<pi>X\<close> unfolding top1_group_hom_on_def by (by100 blast)
      have "h (\<Phi> c) = c" using hhPhi_id \<open>c \<in> ?\<pi>X\<close> by (by100 simp)
      thus "c \<in> h ` FP" using \<open>\<Phi> c \<in> FP\<close> by (by100 blast)
    qed
  qed
  have hh_inj: "inj_on h FP"
  proof (rule inj_onI)
    fix x y assume "x \<in> FP" "y \<in> FP" "h x = h y"
    have "\<Phi> (h x) = \<Phi> (h y)" using \<open>h x = h y\<close> by (by100 simp)
    hence "x = y" using hPhih_id_FP \<open>x \<in> FP\<close> \<open>y \<in> FP\<close> by (by100 simp)
    thus "x = y" .
  qed
  have hh_bij: "bij_betw h FP ?\<pi>X"
    unfolding bij_betw_def using hh_inj hh_surj by (by100 blast)
  \<comment> \<open>Step 6: h is a group iso with tracking.\<close>
  have hh_iso: "top1_group_iso_on FP mulFP ?\<pi>X ?mX h"
    unfolding top1_group_iso_on_def using hh_hom hh_bij by (by100 blast)
  show ?thesis using hh_iso hh_trackU hh_trackV by (by100 blast)
qed

text \<open>Strengthened version: \<pi>\_1(X) free with SPECIFIC generators that are
  the inclusion-induced images of the \<pi>\_1(U), \<pi>\_1(V) generators.\<close>
lemma svk_free_product_free_with_generators:
  assumes hstrict: "is_topology_on_strict X TX"
      and hU_open: "openin_on X TX U" and hV_open: "openin_on X TX V"
      and hUV_cover: "U \<union> V = X"
      and hUV_sc: "top1_simply_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and hU_pc: "top1_path_connected_on U (subspace_topology X TX U)"
      and hV_pc: "top1_path_connected_on V (subspace_topology X TX V)"
      and hp: "p \<in> U \<inter> V"
      and hU_free: "top1_is_free_group_full_on
          (top1_fundamental_group_carrier U (subspace_topology X TX U) p)
          (top1_fundamental_group_mul U (subspace_topology X TX U) p)
          (top1_fundamental_group_id U (subspace_topology X TX U) p)
          (top1_fundamental_group_invg U (subspace_topology X TX U) p)
          \<iota>U S1"
      and hV_free: "top1_is_free_group_full_on
          (top1_fundamental_group_carrier V (subspace_topology X TX V) p)
          (top1_fundamental_group_mul V (subspace_topology X TX V) p)
          (top1_fundamental_group_id V (subspace_topology X TX V) p)
          (top1_fundamental_group_invg V (subspace_topology X TX V) p)
          \<iota>V S2"
      and hS_disj: "S1 \<inter> S2 = {}"
  shows "\<exists>\<iota>X. top1_is_free_group_full_on
      (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
      (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
      \<iota>X (S1 \<union> S2)
    \<and> (\<forall>s\<in>S1. \<iota>X s = top1_fundamental_group_induced_on U (subspace_topology X TX U) p X TX p (\<lambda>x. x) (\<iota>U s))
    \<and> (\<forall>s\<in>S2. \<iota>X s = top1_fundamental_group_induced_on V (subspace_topology X TX V) p X TX p (\<lambda>x. x) (\<iota>V s))"
proof -
  let ?TU = "subspace_topology X TX U" and ?TV = "subspace_topology X TX V"
  let ?\<pi>U = "top1_fundamental_group_carrier U ?TU p"
  let ?mU = "top1_fundamental_group_mul U ?TU p"
  let ?\<pi>V = "top1_fundamental_group_carrier V ?TV p"
  let ?mV = "top1_fundamental_group_mul V ?TV p"
  have hTX: "is_topology_on X TX"
    using hstrict unfolding is_topology_on_strict_def by (by100 blast)
  have hp_X: "p \<in> X" using hp hUV_cover by (by100 blast)
  have hpi1_grp: "top1_is_group_on
      (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
      (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)"
    using top1_fundamental_group_is_group[OF hTX hp_X] by (by100 blast)
  \<comment> \<open>Apply Theorem\_69\_2 to get FP free on S1 \<union> S2 with iotaS tracking.\<close>
  from Theorem_69_2[OF hU_free hV_free hS_disj] show ?thesis
  proof (elim exE conjE)
    fix FP_uv mulFP_uv eFP_uv invgFP_uv iotafam_uv iotaS_uv
    assume hFP_prod: "top1_is_free_product_on FP_uv mulFP_uv eFP_uv invgFP_uv
        (\<lambda>i::nat. if i = 0 then ?\<pi>U else ?\<pi>V) (\<lambda>i. if i = 0 then ?mU else ?mV)
        iotafam_uv {0, 1}"
    assume hFP_free: "top1_is_free_group_full_on FP_uv mulFP_uv eFP_uv invgFP_uv iotaS_uv (S1 \<union> S2)"
    assume hiotaS_U: "\<forall>s\<in>S1. iotaS_uv s = iotafam_uv 0 (\<iota>U s)"
    assume hiotaS_V: "\<forall>s\<in>S2. iotaS_uv s = iotafam_uv 1 (\<iota>V s)"
    \<comment> \<open>Get the SvK iso WITH tracking from svk\_iso\_with\_tracking.\<close>
    from svk_iso_with_tracking[OF hstrict hU_open hV_open hUV_cover hUV_sc hU_pc hV_pc hp hFP_prod]
    obtain h where hh_iso: "top1_group_iso_on FP_uv mulFP_uv
        (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p) h"
      and hh_trackU: "\<forall>c\<in>?\<pi>U. h (iotafam_uv 0 c) =
          top1_fundamental_group_induced_on U ?TU p X TX p (\<lambda>x. x) c"
      and hh_trackV: "\<forall>c\<in>?\<pi>V. h (iotafam_uv 1 c) =
          top1_fundamental_group_induced_on V ?TV p X TX p (\<lambda>x. x) c"
      by (by100 blast)
    \<comment> \<open>Transfer freeness from FP to \<pi>\_1(X) via h.\<close>
    have hFP_grp: "top1_is_group_on FP_uv mulFP_uv eFP_uv invgFP_uv"
      using hFP_free unfolding top1_is_free_group_full_on_def by (by100 blast)
    note h_fgii = free_group_invariant_under_iso[OF hFP_free hh_iso hpi1_grp]
    define \<iota>X where "\<iota>X \<equiv> SOME \<iota>'. top1_is_free_group_full_on
        (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
        (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
        \<iota>' (S1 \<union> S2) \<and> (\<forall>s\<in>S1 \<union> S2. \<iota>' s = h (iotaS_uv s))"
    have hiotaX_props: "top1_is_free_group_full_on
        (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
        (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
        \<iota>X (S1 \<union> S2) \<and> (\<forall>s\<in>S1 \<union> S2. \<iota>X s = h (iotaS_uv s))"
      unfolding \<iota>X_def using someI_ex[OF h_fgii] by (by5000 blast)
    have hpi1X_free: "top1_is_free_group_full_on
        (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
        (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
        \<iota>X (S1 \<union> S2)"
      using hiotaX_props by (by100 blast)
    have hiotaX_eq: "\<forall>s\<in>S1 \<union> S2. \<iota>X s = h (iotaS_uv s)"
      using hiotaX_props by (by100 blast)
    \<comment> \<open>Generator tracking: for s \<in> S1, \<iota>X(s) = h(iotaS\_uv(s)) = h(iotafam\_uv(0, \<iota>U(s))) = j\_U*(\<iota>U(s)).\<close>
    have hgenU: "\<forall>s\<in>S1. \<iota>X s =
        top1_fundamental_group_induced_on U ?TU p X TX p (\<lambda>x. x) (\<iota>U s)"
    proof
      fix s assume "s \<in> S1"
      have "\<iota>X s = h (iotaS_uv s)" using hiotaX_eq \<open>s \<in> S1\<close> by (by100 blast)
      also have "\<dots> = h (iotafam_uv 0 (\<iota>U s))" using hiotaS_U \<open>s \<in> S1\<close> by (by100 simp)
      also have "\<dots> = top1_fundamental_group_induced_on U ?TU p X TX p (\<lambda>x. x) (\<iota>U s)"
      proof -
        have "\<iota>U s \<in> ?\<pi>U"
          using hU_free \<open>s \<in> S1\<close> unfolding top1_is_free_group_full_on_def by (by5000 simp)
        thus ?thesis using hh_trackU by (by100 blast)
      qed
      finally show "\<iota>X s = top1_fundamental_group_induced_on U ?TU p X TX p (\<lambda>x. x) (\<iota>U s)" .
    qed
    have hgenV: "\<forall>s\<in>S2. \<iota>X s =
        top1_fundamental_group_induced_on V ?TV p X TX p (\<lambda>x. x) (\<iota>V s)"
    proof
      fix s assume "s \<in> S2"
      have "\<iota>X s = h (iotaS_uv s)" using hiotaX_eq \<open>s \<in> S2\<close> by (by100 blast)
      also have "\<dots> = h (iotafam_uv 1 (\<iota>V s))" using hiotaS_V \<open>s \<in> S2\<close> by (by100 simp)
      also have "\<dots> = top1_fundamental_group_induced_on V ?TV p X TX p (\<lambda>x. x) (\<iota>V s)"
      proof -
        have "\<iota>V s \<in> ?\<pi>V"
          using hV_free \<open>s \<in> S2\<close> unfolding top1_is_free_group_full_on_def by (by5000 simp)
        thus ?thesis using hh_trackV by (by100 blast)
      qed
      finally show "\<iota>X s = top1_fundamental_group_induced_on V ?TV p X TX p (\<lambda>x. x) (\<iota>V s)" .
    qed
    show ?thesis using hpi1X_free hgenU hgenV by (by100 blast)
  qed
qed

text \<open>Helper: combine Theorem 69.2 + Corollary 70.3 + free\_group\_invariant\_under\_iso
  to get \<pi>\_1(X) free when \<pi>\_1(U) and \<pi>\_1(V) are free and U\<inter>V simply connected.\<close>
lemma svk_free_product_free:
  assumes hstrict: "is_topology_on_strict X TX"
      and hU_open: "openin_on X TX U" and hV_open: "openin_on X TX V"
      and hUV_cover: "U \<union> V = X"
      and hUV_sc: "top1_simply_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and hU_pc: "top1_path_connected_on U (subspace_topology X TX U)"
      and hV_pc: "top1_path_connected_on V (subspace_topology X TX V)"
      and hp: "p \<in> U \<inter> V"
      and hU_free: "top1_is_free_group_full_on
          (top1_fundamental_group_carrier U (subspace_topology X TX U) p)
          (top1_fundamental_group_mul U (subspace_topology X TX U) p)
          (top1_fundamental_group_id U (subspace_topology X TX U) p)
          (top1_fundamental_group_invg U (subspace_topology X TX U) p)
          \<iota>U S1"
      and hV_free: "top1_is_free_group_full_on
          (top1_fundamental_group_carrier V (subspace_topology X TX V) p)
          (top1_fundamental_group_mul V (subspace_topology X TX V) p)
          (top1_fundamental_group_id V (subspace_topology X TX V) p)
          (top1_fundamental_group_invg V (subspace_topology X TX V) p)
          \<iota>V S2"
      and hS_disj: "S1 \<inter> S2 = {}"
  shows "\<exists>\<iota>X. top1_is_free_group_full_on
      (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
      (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
      \<iota>X (S1 \<union> S2)"
proof -
  let ?TU = "subspace_topology X TX U" and ?TV = "subspace_topology X TX V"
  let ?\<pi>U = "top1_fundamental_group_carrier U ?TU p"
  let ?mU = "top1_fundamental_group_mul U ?TU p"
  let ?\<pi>V = "top1_fundamental_group_carrier V ?TV p"
  let ?mV = "top1_fundamental_group_mul V ?TV p"
  have hTX: "is_topology_on X TX"
    using hstrict unfolding is_topology_on_strict_def by (by100 blast)
  have hp_X: "p \<in> X" using hp hUV_cover by (by100 blast)
  have hpi1_grp: "top1_is_group_on
      (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
      (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)"
    using top1_fundamental_group_is_group[OF hTX hp_X] by (by100 blast)
  \<comment> \<open>Step 1: Theorem\_69\_2\_free\_product\_part gives extraction with 5-variable existential.\<close>
  \<comment> \<open>Apply Theorem\_69\_2 directly (avoiding the extraction problem)
     and compose with SvK + transfer in a single existential chain.\<close>
  from Theorem_69_2[OF hU_free hV_free hS_disj] show ?thesis
  proof (elim exE conjE)
    fix FP_uv mulFP_uv eFP_uv invgFP_uv iotafam_uv iotaS_uv
    assume hFP_prod: "top1_is_free_product_on FP_uv mulFP_uv eFP_uv invgFP_uv
        (\<lambda>i::nat. if i = 0 then ?\<pi>U else ?\<pi>V) (\<lambda>i. if i = 0 then ?mU else ?mV)
        iotafam_uv {0, 1}"
    assume hFP_free: "top1_is_free_group_full_on FP_uv mulFP_uv eFP_uv invgFP_uv iotaS_uv (S1 \<union> S2)"
    \<comment> \<open>SvK: \<pi>\_1(X) \<cong> FP\_uv.\<close>
    have hSvK: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
        FP_uv mulFP_uv"
      using Corollary_70_3_simply_connected_intersection_param[OF
        hstrict hU_open hV_open hUV_cover hUV_sc hU_pc hV_pc hp hFP_prod]
      by (by100 blast)
    \<comment> \<open>Transfer freeness.\<close>
    from hSvK[unfolded top1_groups_isomorphic_on_def]
    obtain \<psi>_svk where h\<psi>_iso: "top1_group_iso_on
        (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
        FP_uv mulFP_uv \<psi>_svk"
      by (by100 blast)
    have hFP_grp: "top1_is_group_on FP_uv mulFP_uv eFP_uv invgFP_uv"
      using hFP_free unfolding top1_is_free_group_full_on_def by (by100 blast)
    have h\<psi>_inv: "top1_group_iso_on FP_uv mulFP_uv
        (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
        (inv_into (top1_fundamental_group_carrier X TX p) \<psi>_svk)"
      using group_iso_on_inverse[OF h\<psi>_iso hpi1_grp hFP_grp] by (by100 blast)
    from free_group_invariant_under_iso[OF hFP_free h\<psi>_inv hpi1_grp]
    show ?thesis by (by100 blast)
  qed
qed

lemma foldr_in_subgroup:
  assumes hN_grp: "top1_is_group_on N mul e invg"
      and hys: "\<forall>i<length ys. ys!i \<in> N"
  shows "foldr mul ys e \<in> N"
  using hys
proof (induction ys)
  case Nil
  have "e \<in> N" using hN_grp[unfolded top1_is_group_on_def] by (by100 simp)
  thus ?case by (by100 simp)
next
  case (Cons a rest)
  have "a \<in> N" using Cons.prems by (by100 force)
  have "\<forall>i<length rest. rest!i \<in> N" using Cons.prems by (by100 force)
  hence "foldr mul rest e \<in> N" using Cons.IH by (by100 blast)
  have hmul_closure: "\<forall>x\<in>N. \<forall>y\<in>N. mul x y \<in> N"
  proof (intro ballI)
    fix x y assume "x \<in> N" "y \<in> N"
    have "\<forall>x\<in>N. \<forall>y\<in>N. mul x y \<in> N"
      using hN_grp[unfolded top1_is_group_on_def] by (by100 simp)
    thus "mul x y \<in> N" using \<open>x \<in> N\<close> \<open>y \<in> N\<close> by (by100 blast)
  qed
  have "mul a (foldr mul rest e) \<in> N"
    using hmul_closure \<open>a \<in> N\<close> \<open>foldr mul rest e \<in> N\<close> by (by100 blast)
  thus ?case by (by100 simp)
qed

text \<open>If G = gen(S), f: G \<rightarrow> H hom, N subgroup of H, f(S) \<subseteq> N, then f(G) \<subseteq> N.
  Proof: every g \<in> G is a word product of elements from S \<union> invg(S).
  f maps word products to word products, which stay in N since N is a subgroup.\<close>
lemma hom_image_in_subgroup_from_generators:
  assumes hG_grp: "top1_is_group_on G mulG eG invgG"
      and hH_grp: "top1_is_group_on H mulH eH invgH"
      and hf: "top1_group_hom_on G mulG H mulH f"
      and hG_gen: "G = top1_subgroup_generated_on G mulG eG invgG S"
      and hS_sub: "S \<subseteq> G"
      and hN_grp: "top1_is_group_on N mulH eH invgH"
      and hN_sub: "N \<subseteq> H"
      and hfS_N: "f ` S \<subseteq> N"
  shows "f ` G \<subseteq> N"
proof (rule image_subsetI)
  fix g assume "g \<in> G"
  hence "g \<in> top1_subgroup_generated_on G mulG eG invgG S" using hG_gen by (by100 simp)
  \<comment> \<open>g = e or g = word product of elements from S \<union> invg(S).\<close>
  from subgroup_generated_word_repr[OF hG_grp hS_sub this]
  have "g = eG \<or> (\<exists>ws. length ws > 0 \<and>
      (\<forall>i<length ws. ws!i \<in> S \<or> (\<exists>s\<in>S. ws!i = invgG s)) \<and>
      foldr mulG ws eG = g)" .
  thus "f g \<in> N"
  proof (elim disjE exE conjE)
    assume "g = eG"
    have "f eG = eH"
      using hom_preserves_id[OF hG_grp hH_grp hf] by (by100 blast)
    hence "f g = eH" using \<open>g = eG\<close> by (by100 simp)
    thus ?thesis using hN_grp unfolding top1_is_group_on_def by (by100 blast)
  next
    fix ws assume hlen: "length ws > 0"
      and hws: "\<forall>i<length ws. ws!i \<in> S \<or> (\<exists>s\<in>S. ws!i = invgG s)"
      and hprod: "foldr mulG ws eG = g"
    \<comment> \<open>f(g) = f(foldr mulG ws eG) = foldr mulH (map f ws) eH.\<close>
    \<comment> \<open>Each f(ws!i) is either f(s) \<in> N or f(invg(s)) = invgH(f(s)) \<in> N.\<close>
    \<comment> \<open>So the product is in N (N closed under multiplication).\<close>
    \<comment> \<open>Each ws!i maps to N: if ws!i \<in> S then f(ws!i) \<in> N by hfS\_N.
       If ws!i = invg(s) for s \<in> S, then f(ws!i) = invgH(f(s)) \<in> N since N group.\<close>
    have hmap_N: "\<forall>i<length ws. f (ws!i) \<in> N"
    proof (intro allI impI)
      fix i :: nat assume "i < length ws"
      from hws[rule_format, OF this] have hwsi: "ws!i \<in> S \<or> (\<exists>s\<in>S. ws!i = invgG s)" .
      show "f (ws!i) \<in> N"
      proof (cases "ws!i \<in> S")
        case True thus ?thesis using hfS_N by (by100 blast)
      next
        case False
        from hwsi False obtain s where "s \<in> S" "ws!i = invgG s" by (by100 blast)
        have "s \<in> G" using \<open>s \<in> S\<close> hS_sub by (by100 blast)
        have "f s \<in> N" using \<open>s \<in> S\<close> hfS_N by (by100 blast)
        have "f (invgG s) = invgH (f s)"
          using hom_preserves_inv[OF hG_grp hH_grp hf \<open>s \<in> G\<close>] by (by100 blast)
        hence "f (ws!i) = invgH (f s)" using \<open>ws!i = invgG s\<close> by (by100 simp)
        have "invgH (f s) \<in> N" using \<open>f s \<in> N\<close> hN_grp unfolding top1_is_group_on_def by (by100 blast)
        thus ?thesis using \<open>f (ws!i) = invgH (f s)\<close> by (by100 simp)
      qed
    qed
    \<comment> \<open>f preserves foldr: f(foldr mulG ws eG) = foldr mulH (map f ws) eH.\<close>
    have hws_in_G: "\<forall>i<length ws. ws!i \<in> G"
    proof (intro allI impI)
      fix i :: nat assume "i < length ws"
      from hws[rule_format, OF this] have hwsi: "ws!i \<in> S \<or> (\<exists>s\<in>S. ws!i = invgG s)" .
      show "ws!i \<in> G"
      proof (cases "ws!i \<in> S")
        case True thus ?thesis using hS_sub by (by100 blast)
      next
        case False
        from hwsi False obtain s where "s \<in> S" "ws!i = invgG s" by (by100 blast)
        have "s \<in> G" using \<open>s \<in> S\<close> hS_sub by (by100 blast)
        hence "invgG s \<in> G" using hG_grp unfolding top1_is_group_on_def by (by100 blast)
        thus ?thesis using \<open>ws!i = invgG s\<close> by (by100 simp)
      qed
    qed
    have hf_foldr: "f (foldr mulG ws eG) = foldr mulH (map f ws) eH"
      using hom_foldr_mul[OF hG_grp hH_grp hf hws_in_G] by (by100 blast)
    \<comment> \<open>foldr mulH (map f ws) eH \<in> N since each (map f ws)!i \<in> N and N closed.\<close>
    have "\<forall>i<length (map f ws). (map f ws)!i \<in> N"
      using hmap_N by (by100 auto)
    hence "foldr mulH (map f ws) eH \<in> N"
      using foldr_in_subgroup[OF hN_grp] by (by100 blast)
    thus "f g \<in> N" using hprod hf_foldr by (by100 simp)
  qed
qed

text \<open>Helper: inclusion-induced images of generators are in the hom image,
  when the generators map to specific elements via gen corr + inclusion.\<close>
lemma inclusion_gen_images_in_hom_image:
  assumes hTX: "is_topology_on X TX"
      and hV_sub: "V \<subseteq> X"
      and hloop: "\<forall>k\<in>S. top1_is_loop_on V (subspace_topology X TX V) p (\<lambda>t. gk k (cos (2*pi*t), sin (2*pi*t)))"
      and hgen_eq: "\<forall>k\<in>S. \<iota>V k = {l. top1_loop_equiv_on V (subspace_topology X TX V) p (\<lambda>t. gk k (cos (2*pi*t), sin (2*pi*t))) l}"
      and h\<Phi>_gen: "\<forall>k\<in>S. \<Phi> (\<iota>_G k) = {l. top1_loop_equiv_on X TX p (\<lambda>t. gk k (cos (2*pi*t), sin (2*pi*t))) l}"
      and hiG_in: "\<forall>k\<in>S. \<iota>_G k \<in> G"
  shows "(top1_fundamental_group_induced_on V (subspace_topology X TX V) p X TX p (\<lambda>x. x)) `
      (\<iota>V ` S) \<subseteq> \<Phi> ` G"
proof -
  let ?jV = "top1_fundamental_group_induced_on V (subspace_topology X TX V) p X TX p (\<lambda>x. x)"
  have "\<forall>k\<in>S. ?jV (\<iota>V k) \<in> \<Phi> ` G"
  proof
    fix k assume "k \<in> S"
    have hloop_k: "top1_is_loop_on V (subspace_topology X TX V) p
        (\<lambda>t. gk k (cos (2*pi*t), sin (2*pi*t)))"
      using hloop \<open>k \<in> S\<close> by (by100 blast)
    have "?jV (\<iota>V k) = ?jV {l. top1_loop_equiv_on V (subspace_topology X TX V) p
        (\<lambda>t. gk k (cos (2*pi*t), sin (2*pi*t))) l}"
      using hgen_eq \<open>k \<in> S\<close> by (by100 simp)
    also have "\<dots> = {l. top1_loop_equiv_on X TX p (\<lambda>t. gk k (cos (2*pi*t), sin (2*pi*t))) l}"
      by (rule subspace_inclusion_induced_class[OF hTX hV_sub hloop_k])
    also have "\<dots> = \<Phi> (\<iota>_G k)"
      using h\<Phi>_gen \<open>k \<in> S\<close> by (by100 simp)
    finally show "?jV (\<iota>V k) \<in> \<Phi> ` G"
      using hiG_in \<open>k \<in> S\<close> by (by100 blast)
  qed
  thus ?thesis by (by100 blast)
qed

text \<open>Helper: g(k) composed with the standard loop is a loop on V,
  when C(k) \<subseteq> V and g(k) is a homeomorphism S1 \<rightarrow> C(k).\<close>
lemma loop_on_superspace_via_homeo:
  assumes hTX: "is_topology_on X TX"
      and hV_sub: "V \<subseteq> X"
      and hCk_sub_V: "Ck \<subseteq> V"
      and hgk_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
          Ck (subspace_topology X TX Ck) gk"
      and hgk_base: "gk (1, 0) = p"
      and hp_V: "p \<in> V"
  shows "top1_is_loop_on V (subspace_topology X TX V) p
      (\<lambda>t. gk (cos (2*pi*t), sin (2*pi*t)))"
proof -
  let ?loop = "\<lambda>t. gk (cos (2*pi*t), sin (2*pi*t))"
  \<comment> \<open>std\_loop is a loop on S1.\<close>
  have hstd: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0)
      (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))"
    by (rule standard_S1_loop_is_loop)
  \<comment> \<open>Compose with gk: loop on Ck.\<close>
  have hgk_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
      Ck (subspace_topology X TX Ck) gk"
    using hgk_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hloop_Ck: "top1_is_loop_on Ck (subspace_topology X TX Ck) (gk (1,0))
      (gk \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))))"
    by (rule top1_continuous_map_loop_early[OF hgk_cont hstd])
  have hcomp_eq: "gk \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) = ?loop"
    unfolding comp_def by (by100 simp)
  have hloop_Ck': "top1_is_loop_on Ck (subspace_topology X TX Ck) p ?loop"
    using hloop_Ck hcomp_eq hgk_base by (by100 simp)
  \<comment> \<open>Transfer from Ck to V: Ck \<subseteq> V \<subseteq> X.\<close>
  have hCk_trans: "subspace_topology V (subspace_topology X TX V) Ck = subspace_topology X TX Ck"
    using subspace_topology_trans[OF hCk_sub_V] by (by100 simp)
  have hloop_Ck_V: "top1_is_loop_on Ck (subspace_topology V (subspace_topology X TX V) Ck) p ?loop"
    using hloop_Ck' hCk_trans by (by100 simp)
  \<comment> \<open>Expand from Ck to V.\<close>
  have hTV: "is_topology_on V (subspace_topology X TX V)"
    using subspace_topology_is_topology_on[OF hTX hV_sub] by (by100 blast)
  have hloop_cont_Ck: "top1_continuous_map_on I_set I_top
      Ck (subspace_topology V (subspace_topology X TX V) Ck) ?loop"
    using hloop_Ck_V unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  have hI_top: "is_topology_on I_set I_top"
    using top1_unit_interval_topology_is_topology_on by (by100 blast)
  have hTCk: "is_topology_on Ck (subspace_topology V (subspace_topology X TX V) Ck)"
    using subspace_topology_is_topology_on[OF hTV hCk_sub_V] by (by100 blast)
  have hloop_cont_V: "top1_continuous_map_on I_set I_top V (subspace_topology X TX V) ?loop"
    using Theorem_18_2(6)[OF hI_top hTCk hTV] hloop_cont_Ck hCk_sub_V hCk_trans
    by (by5000 blast)
  have "?loop 0 = p" using hgk_base by (by100 simp)
  have "?loop 1 = p" using hgk_base by (by100 simp)
  show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
    using hloop_cont_V \<open>?loop 0 = p\<close> \<open>?loop 1 = p\<close> by (by100 blast)
qed

text \<open>Munkres Theorem 71.1 (witnessed version with chosen loop generators).
  For a finite wedge of circles with explicit circle data (homeomorphisms, basepoints),
  \<pi>_1 is free and the chosen circle loops are the free generators.
  Proof by induction on |J| using SvK (Corollary\_70\_3) + Theorem\_69\_2.
  Following Munkres' proof exactly.\<close>
lemma finite_wedge_pi1_free_with_chosen_loops:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and p :: 'a
    and C :: "nat \<Rightarrow> 'a set" and g :: "nat \<Rightarrow> real \<times> real \<Rightarrow> 'a"
  assumes hstrict: "is_topology_on_strict X TX"
      and hhaus: "is_hausdorff_on X TX"
      and hp: "p \<in> X"
      and hC_sub: "\<forall>j<n. C j \<subseteq> X \<and> p \<in> C j"
      and hC_union: "(\<Union>j\<in>{..<n}. C j) = X"
      and hC_disj: "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> C i \<inter> C j = {p}"
      and hC_homeo: "\<forall>j<n. top1_homeomorphism_on top1_S1 top1_S1_topology
          (C j) (subspace_topology X TX (C j)) (g j)"
      and hC_base: "\<forall>j<n. g j (1, 0) = p"
      and hC_closed: "\<forall>D\<subseteq>X. closedin_on X TX D \<longleftrightarrow>
          (\<forall>j<n. closedin_on (C j) (subspace_topology X TX (C j)) (C j \<inter> D))"
  shows "\<exists>(F::int set) mul e invg (\<eta>::nat \<Rightarrow> int) \<Phi>.
      top1_is_free_group_full_on F mul e invg \<eta> {..<n}
    \<and> top1_group_iso_on F mul
        (top1_fundamental_group_carrier X TX p)
        (top1_fundamental_group_mul X TX p) \<Phi>
    \<and> (\<forall>j<n. \<Phi> (\<eta> j) = {l. top1_loop_equiv_on X TX p
        (\<lambda>t. g j (cos (2 * pi * t), sin (2 * pi * t))) l})"
  using assms proof (induction n arbitrary: X TX p C g rule: less_induct)
    case (less n)
    show ?case
    proof (cases "n = 0")
      case True
      \<comment> \<open>Base n=0: X = {p}, \<pi>_1 trivial, free on empty set.\<close>
      \<comment> \<open>n=0: X = \<Union>{} = {} but p \<in> X. Contradiction.\<close>
      have "X = {}" using less.prems(5) True by (by100 simp)
      thus ?thesis using less.prems(3) by (by100 blast)
    next
      case False hence hn_pos: "n > 0" by (by100 simp)
      show ?thesis
      proof (cases "n = 1")
        case True
        \<comment> \<open>Base n=1: X = C(0) homeomorphic to S1. pi1(X) = Z.
           The standard loop f_0 generates. Use Theorem\_54\_5 or cached results.\<close>
        \<comment> \<open>n = 1: X = C(0) \<cong> S1 via g(0). pi1(X,p) \<cong> Z.
           Loop class = [g(0) \<circ> standard S1 loop] maps to generator 1 \<in> Z.\<close>
        have hJ1: "{..<n} = {0::nat}" using True by auto
        \<comment> \<open>X = C(0).\<close>
        have hX_eq: "X = C 0" using less.prems(5) hJ1 by (by100 simp)
        \<comment> \<open>Z is free on {0} with generator \<iota>(0) = 1.\<close>
        let ?F = "top1_Z_group" and ?mul = "top1_Z_mul" and ?e = "top1_Z_id"
        let ?invg = "top1_Z_invg" and ?\<eta> = "\<lambda>(_::nat). (1::int)"
        have hZ_free: "top1_is_free_group_full_on ?F ?mul ?e ?invg ?\<eta> {0::nat}"
          by (rule Z_is_free_on_one_generator)
        \<comment> \<open>g(0): S1 \<rightarrow> C(0) = X is a homeomorphism.\<close>
        have hg0_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
            X (subspace_topology X TX X) (g 0)"
        proof -
          have "0 < n" using True by (by100 simp)
          have "top1_homeomorphism_on top1_S1 top1_S1_topology
              (C 0) (subspace_topology X TX (C 0)) (g 0)"
            using less.prems(7) \<open>0 < n\<close> by (by100 blast)
          thus ?thesis using hX_eq by (by100 simp)
        qed
        \<comment> \<open>Transfer iso: pi1(S1,(1,0)) \<cong> Z \<Rightarrow> pi1(X,p) \<cong> Z with generator tracking.\<close>
        \<comment> \<open>Theorem\_54\_5\_iso\_with\_generator gives phi: pi1(S1) \<cong> Z with phi([std loop]) = 1.\<close>
        from Theorem_54_5_iso_with_generator obtain \<phi>0 where
          h\<phi>0_iso: "top1_group_iso_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0)) ?F ?mul \<phi>0"
          and h\<phi>0_gen: "\<phi>0 {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
            (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) g} = (1::int)"
          by (by100 blast)
        \<comment> \<open>g(0)\_* : pi1(S1,(1,0)) \<rightarrow> pi1(X,p) is an isomorphism (homeomorphism induces iso).\<close>
        \<comment> \<open>Compose: \<Phi> = \<phi>0^{-1} composed with g(0)\_*^{-1}.\<close>
        \<comment> \<open>Actually: we need \<Phi>: Z \<rightarrow> pi1(X,p). So \<Phi> = g(0)\_* \<circ> \<phi>0^{-1}.\<close>
        \<comment> \<open>g(0)\_*: \<pi>_1(S1,(1,0)) \<rightarrow> \<pi>_1(X,p) is an iso (homeomorphism induces iso).\<close>
        have hTX: "is_topology_on X TX"
          using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
        have hg0_base: "g 0 (1, 0) = p" using less.prems(8) True by (by100 simp)
        have hTS1: "is_topology_on top1_S1 top1_S1_topology"
          using top1_S1_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
        \<comment> \<open>Subspace topology on X = full topology (X \<subseteq> X).\<close>
        have hTX_pow: "TX \<subseteq> Pow X"
          using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
        have hTX_sub: "subspace_topology X TX X = TX"
        proof (rule set_eqI, rule iffI)
          fix U assume "U \<in> subspace_topology X TX X"
          then obtain V where "V \<in> TX" "U = X \<inter> V" unfolding subspace_topology_def by (by100 blast)
          moreover have "V \<subseteq> X" using \<open>V \<in> TX\<close> hTX_pow by (by100 blast)
          ultimately have "U = V" by (by100 blast)
          thus "U \<in> TX" using \<open>V \<in> TX\<close> by (by100 simp)
        next
          fix U assume "U \<in> TX"
          moreover have "U \<subseteq> X" using \<open>U \<in> TX\<close> hTX_pow by (by100 blast)
          ultimately have "X \<inter> U = U" by (by100 blast)
          thus "U \<in> subspace_topology X TX X" unfolding subspace_topology_def
            using \<open>U \<in> TX\<close> by (by100 blast)
        qed
        have hg0_homeo': "top1_homeomorphism_on top1_S1 top1_S1_topology X TX (g 0)"
          using hg0_homeo hTX_sub by (by100 simp)
        \<comment> \<open>Homeomorphism induces isomorphism on \<pi>_1.\<close>
        have h10_S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
        have hg0_iso: "top1_groups_isomorphic_on
            (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
            (top1_fundamental_group_carrier X TX p)
            (top1_fundamental_group_mul X TX p)"
          by (rule Corollary_52_5_homeomorphism_iso[OF hTS1 hTX hg0_homeo' h10_S1 hg0_base])
        \<comment> \<open>Explicit construction: \<Phi> = g(0)\_* \<circ> \<phi>0^{-1} for generator tracking.
           g(0)\_* : \<pi>_1(S1) \<rightarrow> \<pi>_1(X) is the induced map.
           \<phi>0^{-1} : Z \<rightarrow> \<pi>_1(S1) is the inverse of the Theorem\_54\_5 iso.\<close>
        let ?pi1_S1 = "top1_fundamental_group_carrier top1_S1 top1_S1_topology (1::real, 0::real)"
        let ?mul_S1 = "top1_fundamental_group_mul top1_S1 top1_S1_topology (1::real, 0::real)"
        let ?g0_star = "top1_fundamental_group_induced_on
            top1_S1 top1_S1_topology (1, 0) X TX p (g 0)"
        have hg0_cont: "top1_continuous_map_on top1_S1 top1_S1_topology X TX (g 0)"
          using hg0_homeo' unfolding top1_homeomorphism_on_def by (by100 blast)
        \<comment> \<open>\<phi>0 is bijective \<pi>_1(S1) \<rightarrow> Z.\<close>
        have hphi0_bij: "bij_betw \<phi>0 ?pi1_S1 ?F"
          using h\<phi>0_iso unfolding top1_group_iso_on_def by (by100 blast)
        have hphi0_inj: "inj_on \<phi>0 ?pi1_S1"
          using hphi0_bij unfolding bij_betw_def by (by100 blast)
        \<comment> \<open>Standard loop on S1.\<close>
        let ?std_loop = "\<lambda>s::real. (cos (2 * pi * s), sin (2 * pi * s))"
        let ?std_class = "{f. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) ?std_loop f}"
        \<comment> \<open>[std\_loop] \<in> \<pi>_1(S1): std\_loop is a loop on S1 at (1,0).\<close>
        have hstd_in_pi1: "?std_class \<in> ?pi1_S1"
          by (rule standard_S1_loop_class_in_carrier)
        \<comment> \<open>\<phi>0^{-1}(1) = [std\_loop] (from \<phi>0([std\_loop]) = 1 and \<phi>0 injective).\<close>
        have hphi0_inv: "inv_into ?pi1_S1 \<phi>0 (1::int) = ?std_class"
          using inv_into_f_eq[OF hphi0_inj hstd_in_pi1 h\<phi>0_gen] by (by100 simp)
        \<comment> \<open>g(0)\_*([std\_loop]) = loop\_class(0).
           By definition: g(0)\_*(c) = {h. \<exists>f\<in>c. loop\_equiv(g0\<circ>f, h)}.
           Since std\_loop \<in> [std\_loop] (reflexivity), g0\<circ>std\_loop = \<lambda>t. g 0 (cos .., sin ..).
           Conversely, if f \<in> [std\_loop] then g0\<circ>f homotopic to g0\<circ>std\_loop
           by continuous\_preserves\_path\_homotopic.\<close>
        \<comment> \<open>Helper: std\_loop is a loop on S1 (from cached lemma).\<close>
        have hstd_is_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) ?std_loop"
          by (rule standard_S1_loop_is_loop)
        \<comment> \<open>Helper: g(0) \<circ> std\_loop is a loop on X at p.\<close>
        have hg0_std_loop: "top1_is_loop_on X TX p ((g 0) \<circ> ?std_loop)"
          using top1_continuous_map_loop_early[OF hg0_cont hstd_is_loop] hg0_base
          by (by100 simp)
        \<comment> \<open>Helper: (g 0) \<circ> std\_loop = \<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t)) pointwise.\<close>
        have hcomp_eq: "\<And>t. ((g 0) \<circ> ?std_loop) t = g 0 (cos (2*pi*t), sin (2*pi*t))"
          unfolding comp_def by (by100 simp)
        have hg0_star_std: "?g0_star ?std_class =
            {l. top1_loop_equiv_on X TX p (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l}"
          unfolding top1_fundamental_group_induced_on_def
        proof (rule set_eqI, rule iffI)
          fix l
          assume "l \<in> {h. \<exists>f\<in>?std_class. top1_loop_equiv_on X TX p ((g 0) \<circ> f) h}"
          then obtain f where hf_in: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
              ?std_loop f"
              and hle: "top1_loop_equiv_on X TX p ((g 0) \<circ> f) l" by (by100 blast)
          \<comment> \<open>f is loop-equiv to std\_loop, so g0\<circ>f is path-homotopic to g0\<circ>std\_loop.\<close>
          have hf_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f"
            using hf_in unfolding top1_loop_equiv_on_def by (by100 blast)
          have hph: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) ?std_loop f"
            using hf_in unfolding top1_loop_equiv_on_def by (by100 blast)
          have hph_X: "top1_path_homotopic_on X TX p p ((g 0) \<circ> ?std_loop) ((g 0) \<circ> f)"
            using top1_continuous_preserves_path_homotopy[OF hTS1 hg0_cont hstd_is_loop hf_loop hph]
                  hg0_base by (by100 simp)
          \<comment> \<open>Build loop\_equiv for g0 \<circ> std\_loop and g0 \<circ> f.\<close>
          have hg0f_loop: "top1_is_loop_on X TX p ((g 0) \<circ> f)"
            using hle unfolding top1_loop_equiv_on_def by (by100 blast)
          have hg0_std_equiv_f: "top1_loop_equiv_on X TX p ((g 0) \<circ> ?std_loop) ((g 0) \<circ> f)"
            unfolding top1_loop_equiv_on_def
            using hg0_std_loop hg0f_loop hph_X by (by100 blast)
          \<comment> \<open>By transitivity: g0 \<circ> std\_loop loop-equiv l.\<close>
          have "top1_loop_equiv_on X TX p ((g 0) \<circ> ?std_loop) l"
            by (rule top1_loop_equiv_on_trans[OF hTX hg0_std_equiv_f hle])
          thus "l \<in> {l. top1_loop_equiv_on X TX p (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l}"
            using hcomp_eq unfolding comp_def by (by100 simp)
        next
          fix l
          assume hl: "l \<in> {l. top1_loop_equiv_on X TX p (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l}"
          \<comment> \<open>Take f = std\_loop. std\_loop \<in> std\_class by reflexivity.\<close>
          have "?std_loop \<in> ?std_class"
            using top1_loop_equiv_on_refl[OF hstd_is_loop] by (by100 simp)
          moreover have "top1_loop_equiv_on X TX p ((g 0) \<circ> ?std_loop) l"
            using hl hcomp_eq unfolding comp_def by (by100 simp)
          ultimately show "l \<in> {h. \<exists>f\<in>?std_class. top1_loop_equiv_on X TX p ((g 0) \<circ> f) h}"
            by (by100 blast)
        qed
        \<comment> \<open>Define \<Phi> = g(0)\_* \<circ> \<phi>0^{-1}.\<close>
        define \<Phi> where "\<Phi> = ?g0_star \<circ> (inv_into ?pi1_S1 \<phi>0)"
        \<comment> \<open>Generator correspondence: \<Phi>(1) = loop\_class(0).\<close>
        have h\<Phi>_gen: "\<forall>j<n. \<Phi> (?\<eta> j) = {l. top1_loop_equiv_on X TX p
            (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) l}"
        proof (intro allI impI)
          fix j assume "j < n"
          hence "j = 0" using True by (by100 simp)
          thus "\<Phi> (?\<eta> j) = {l. top1_loop_equiv_on X TX p
              (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) l}"
            unfolding \<Phi>_def comp_def using hphi0_inv hg0_star_std by (by100 simp)
        qed
        \<comment> \<open>\<Phi> is an isomorphism Z \<rightarrow> \<pi>_1(X,p): composition of two isos.\<close>
        \<comment> \<open>Step A: g(0)\_* is an iso \<pi>_1(S1) \<rightarrow> \<pi>_1(X,p).
           Homeomorphism \<Rightarrow> homotopy equivalence \<Rightarrow> AlgIsoFixed.Theorem\_58\_7.\<close>
        have hg0_star_iso: "top1_group_iso_on ?pi1_S1 ?mul_S1
            (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p) ?g0_star"
        proof -
          \<comment> \<open>Construct homotopy equivalence from homeomorphism g(0): S1 \<rightarrow> X.\<close>
          let ?ginv = "inv_into top1_S1 (g 0)"
          have hbij: "bij_betw (g 0) top1_S1 X"
            using hg0_homeo' unfolding top1_homeomorphism_on_def by (by100 blast)
          have hinj: "inj_on (g 0) top1_S1"
            using hbij unfolding bij_betw_def by (by100 blast)
          have hginv_cont: "top1_continuous_map_on X TX top1_S1 top1_S1_topology ?ginv"
            using hg0_homeo' unfolding top1_homeomorphism_on_def by (by100 blast)
          \<comment> \<open>ginv \<circ> g(0) = id on S1.\<close>
          have hgh_eq: "\<forall>x\<in>top1_S1. (?ginv \<circ> (g 0)) x = x"
            using inv_into_f_f[OF hinj] by (by100 simp)
          \<comment> \<open>g(0) \<circ> ginv = id on X.\<close>
          have hhg_eq: "\<forall>y\<in>X. ((g 0) \<circ> ?ginv) y = y"
          proof (intro ballI)
            fix y assume "y \<in> X"
            hence "y \<in> (g 0) ` top1_S1" using hbij unfolding bij_betw_def by (by100 blast)
            thus "((g 0) \<circ> ?ginv) y = y"
            proof -
              from \<open>y \<in> (g 0) ` top1_S1\<close> have "?ginv y \<in> top1_S1"
                by (rule inv_into_into)
              from \<open>y \<in> (g 0) ` top1_S1\<close> have "(g 0) (?ginv y) = y" by (rule f_inv_into_f)
              thus ?thesis by (by100 simp)
            qed
          qed
          \<comment> \<open>ginv \<circ> g(0) homotopic to id (constant homotopy, since they agree on S1).\<close>
          have hgh_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (?ginv \<circ> (g 0))"
            by (rule top1_continuous_map_on_comp[OF hg0_cont hginv_cont])
          have hid_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology id"
            by (rule top1_continuous_map_on_id[OF hTS1])
          have hgh_htpy: "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology
              (?ginv \<circ> (g 0)) (\<lambda>x. x)"
            unfolding top1_homotopic_on_def
          proof (intro conjI)
            show "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (?ginv \<circ> (g 0))"
              by (rule hgh_cont)
            show "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology (\<lambda>x. x)"
              using hid_cont unfolding id_def by (by100 simp)
            show "\<exists>F. top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
                top1_S1 top1_S1_topology F
              \<and> (\<forall>x\<in>top1_S1. F (x, 0) = (?ginv \<circ> (g 0)) x) \<and> (\<forall>x\<in>top1_S1. F (x, 1) = x)"
            proof (rule exI[of _ "\<lambda>p. (?ginv \<circ> (g 0)) (fst p)"])
              have hF_cont: "top1_continuous_map_on (top1_S1 \<times> I_set)
                  (product_topology_on top1_S1_topology I_top) top1_S1 top1_S1_topology
                  (\<lambda>p. (?ginv \<circ> (g 0)) (fst p))"
                by (rule homotopy_const_continuous[OF hgh_cont hTS1])
              show "top1_continuous_map_on (top1_S1 \<times> I_set)
                    (product_topology_on top1_S1_topology I_top) top1_S1 top1_S1_topology
                    (\<lambda>p. (?ginv \<circ> (g 0)) (fst p))
                  \<and> (\<forall>x\<in>top1_S1. (?ginv \<circ> (g 0)) (fst (x, 0::real)) = (?ginv \<circ> (g 0)) x)
                  \<and> (\<forall>x\<in>top1_S1. (?ginv \<circ> (g 0)) (fst (x, 1::real)) = x)"
                using hF_cont hgh_eq by (by100 simp)
            qed
          qed
          \<comment> \<open>g(0) \<circ> ginv homotopic to id on X.\<close>
          have hhg_cont: "top1_continuous_map_on X TX X TX ((g 0) \<circ> ?ginv)"
            by (rule top1_continuous_map_on_comp[OF hginv_cont hg0_cont])
          have hid_X_cont: "top1_continuous_map_on X TX X TX id"
            by (rule top1_continuous_map_on_id[OF hTX])
          have hhg_htpy: "top1_homotopic_on X TX X TX ((g 0) \<circ> ?ginv) (\<lambda>y. y)"
            unfolding top1_homotopic_on_def
          proof (intro conjI)
            show "top1_continuous_map_on X TX X TX ((g 0) \<circ> ?ginv)" by (rule hhg_cont)
            show "top1_continuous_map_on X TX X TX (\<lambda>y. y)"
              using hid_X_cont unfolding id_def by (by100 simp)
            show "\<exists>F. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX F
              \<and> (\<forall>y\<in>X. F (y, 0) = ((g 0) \<circ> ?ginv) y) \<and> (\<forall>y\<in>X. F (y, 1) = y)"
            proof (rule exI[of _ "\<lambda>p. ((g 0) \<circ> ?ginv) (fst p)"])
              have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX
                  (\<lambda>p. ((g 0) \<circ> ?ginv) (fst p))"
                by (rule homotopy_const_continuous[OF hhg_cont hTX])
              thus "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX
                    (\<lambda>p. ((g 0) \<circ> ?ginv) (fst p))
                  \<and> (\<forall>y\<in>X. ((g 0) \<circ> ?ginv) (fst (y, 0::real)) = ((g 0) \<circ> ?ginv) y)
                  \<and> (\<forall>y\<in>X. ((g 0) \<circ> ?ginv) (fst (y, 1::real)) = y)"
                using hhg_eq by (by100 simp)
            qed
          qed
          have heq: "top1_homotopy_equivalence_on top1_S1 top1_S1_topology X TX (g 0) ?ginv"
            unfolding top1_homotopy_equivalence_on_def
            using hg0_cont hginv_cont hgh_htpy hhg_htpy by (by100 blast)
          \<comment> \<open>Apply Theorem\_58\_7 (AlgIsoFixed version): induced map is an iso.\<close>
          show ?thesis
            using AlgIsoFixed.Theorem_58_7[OF hTS1 hTX heq h10_S1] hg0_base by (by100 simp)
        qed
        \<comment> \<open>Step B: \<phi>0^{-1} is an iso Z \<rightarrow> \<pi>_1(S1).
           From bij\_hom\_inv\_is\_hom + bij\_betw\_inv\_into.\<close>
        have hphi0_inv_iso: "top1_group_iso_on ?F ?mul ?pi1_S1 ?mul_S1
            (inv_into ?pi1_S1 \<phi>0)"
        proof -
          have hphi0_hom: "top1_group_hom_on ?pi1_S1 ?mul_S1 ?F ?mul \<phi>0"
            using h\<phi>0_iso unfolding top1_group_iso_on_def by (by100 blast)
          have hZ_grp: "top1_is_group_on ?F ?mul ?e ?invg"
            using hZ_free unfolding top1_is_free_group_full_on_def by (by100 blast)
          have hS1_grp: "top1_is_group_on ?pi1_S1 ?mul_S1
              (top1_fundamental_group_id top1_S1 top1_S1_topology (1, 0))
              (top1_fundamental_group_invg top1_S1 top1_S1_topology (1, 0))"
            by (rule top1_fundamental_group_is_group[OF hTS1 h10_S1])
          have "top1_group_hom_on ?F ?mul ?pi1_S1 ?mul_S1 (inv_into ?pi1_S1 \<phi>0)"
            by (rule bij_hom_inv_is_hom[OF hS1_grp hZ_grp hphi0_bij hphi0_hom])
          moreover have "bij_betw (inv_into ?pi1_S1 \<phi>0) ?F ?pi1_S1"
            using bij_betw_inv_into[OF hphi0_bij] by (by100 simp)
          ultimately show ?thesis unfolding top1_group_iso_on_def by (by100 blast)
        qed
        \<comment> \<open>Step C: Compose g(0)\_* \<circ> \<phi>0^{-1} to get \<Phi> iso.\<close>
        have h\<Phi>_iso: "top1_group_iso_on ?F ?mul
            (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p) \<Phi>"
        proof -
          have hZ_grp: "top1_is_group_on ?F ?mul ?e ?invg"
            using hZ_free unfolding top1_is_free_group_full_on_def by (by100 blast)
          have hS1_grp: "top1_is_group_on ?pi1_S1 ?mul_S1
              (top1_fundamental_group_id top1_S1 top1_S1_topology (1, 0))
              (top1_fundamental_group_invg top1_S1 top1_S1_topology (1, 0))"
            by (rule top1_fundamental_group_is_group[OF hTS1 h10_S1])
          have hX_grp: "top1_is_group_on
              (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
              (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)"
            by (rule top1_fundamental_group_is_group[OF hTX less.prems(3)])
          show ?thesis unfolding \<Phi>_def
            by (rule group_iso_on_compose[OF hphi0_inv_iso hg0_star_iso hZ_grp hS1_grp hX_grp])
        qed
        \<comment> \<open>Package.\<close>
        show ?thesis unfolding hJ1
          apply (rule exI[of _ ?F], rule exI[of _ ?mul], rule exI[of _ ?e],
                 rule exI[of _ ?invg], rule exI[of _ ?\<eta>], rule exI[of _ \<Phi>])
          using hZ_free h\<Phi>_iso h\<Phi>_gen hJ1 by (by100 blast)
      next
        case False hence hn2: "n \<ge> 2" using hn_pos by (by100 linarith)
        \<comment> \<open>Inductive step: n \<ge> 2. Following Munkres 71.1 exactly.
           Step 1: Construct U, V (Munkres' decomposition).
           Step 2: U \<inter> V simply connected (deformation retract to p).
           Step 3: SvK (Corollary\_70\_3): \<pi>_1(X) \<cong> FP (free product of \<pi>_1(U), \<pi>_1(V)).
           Step 4: Deformation retracts: \<pi>_1(U) \<cong> \<pi>_1(C 0) \<cong> Z, \<pi>_1(V) \<cong> \<pi>_1(sub-wedge).
           Step 5: IH on V: sub-wedge has n-1 circles, free on loops f_1,...,f_{n-1}.
           Step 6: Theorem\_69\_2: FP free on f_0,...,f_{n-1} with explicit generator map.
           Step 7: Compose isomorphisms to get \<Phi> with \<Phi>(\<eta> j) = loop\_class j.\<close>
        \<comment> \<open>Munkres 71.1 inductive step, following AlgTopCached:31794-39914.
           We decompose X into U, V with U \<inter> V simply connected,
           then apply SvK + Theorem\_69\_2 + IH.\<close>
        \<comment> \<open>Step 1: Choose q(j) \<in> C(j) \ {p} via homeomorphism (S1 has more than one point).\<close>
        define q where "q j = (if j < n then g j (- 1, 0) else undefined)" for j
        have hq: "\<forall>j<n. q j \<in> C j \<and> q j \<noteq> p"
        proof (intro allI impI conjI)
          fix j assume hj: "j < n"
          have hg_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
              (C j) (subspace_topology X TX (C j)) (g j)"
            using less.prems(7) hj by (by100 blast)
          have hg_bij: "bij_betw (g j) top1_S1 (C j)"
            using hg_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
          have hm1_S1: "(- 1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
          \<comment> \<open>q(j) = g(j)(-1,0) \<in> C(j) since (-1,0) \<in> S1 and g(j) maps S1 to C(j).\<close>
          have hg_img: "g j ` top1_S1 = C j"
            using hg_bij unfolding bij_betw_def by (by100 blast)
          have "q j = g j (- 1, 0)" unfolding q_def using hj by (by100 simp)
          thus "q j \<in> C j" using hm1_S1 hg_img by (by100 blast)
          \<comment> \<open>q(j) \<noteq> p since g(j) injective and (-1,0) \<noteq> (1,0) and g(j)(1,0) = p.\<close>
          show "q j \<noteq> p"
          proof -
            have hinj: "inj_on (g j) top1_S1"
              using hg_bij unfolding bij_betw_def by (by100 blast)
            have h10_ne: "(1::real, 0::real) \<noteq> (- 1::real, 0::real)" by (by100 simp)
            have h10_S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
            have "g j (- 1, 0) \<noteq> g j (1, 0)"
            proof
              assume "g j (- 1, 0) = g j (1, 0)"
              hence "(- 1::real, 0::real) = (1, 0)" using inj_onD[OF hinj] hm1_S1 h10_S1 by (by100 blast)
              thus False by (by100 simp)
            qed
            thus ?thesis unfolding q_def using hj less.prems(8) by (by100 simp)
          qed
        qed
        \<comment> \<open>W(j) = C(j) \ {q(j)} (punctured circle = arc).\<close>
        define W where "W j = C j - {q j}" for j
        \<comment> \<open>Step 2: U = C(0) \<union> \<Union>{W(j) | 1 \<le> j < n}, V = W(0) \<union> \<Union>{C(j) | 1 \<le> j < n}.\<close>
        define U where "U = C 0 \<union> (\<Union>j\<in>{1..<n}. W j)"
        define V where "V = W 0 \<union> (\<Union>j\<in>{1..<n}. C j)"
        \<comment> \<open>Key fact: each C(j) is closed in X.
           Munkres: "each space S\_i, being compact, is closed in X."
           S1 compact (S1\_compact), g(j) continuous + bij \<Rightarrow> C(j) compact, Hausdorff \<Rightarrow> closed.\<close>
        have hC_closed: "\<forall>j<n. closedin_on X TX (C j)"
        proof (intro allI impI)
          fix j assume hj: "j < n"
          have hg_h: "top1_homeomorphism_on top1_S1 top1_S1_topology
              (C j) (subspace_topology X TX (C j)) (g j)"
            using less.prems(7) hj by (by100 blast)
          have hg_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
              (C j) (subspace_topology X TX (C j)) (g j)"
            using hg_h unfolding top1_homeomorphism_on_def by (by100 blast)
          have hg_bij: "bij_betw (g j) top1_S1 (C j)"
            using hg_h unfolding top1_homeomorphism_on_def by (by100 blast)
          have hg_img: "C j = (g j) ` top1_S1"
            using hg_bij unfolding bij_betw_def by (by100 blast)
          have hTX': "is_topology_on X TX"
            using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
          have hCj_sub: "C j \<subseteq> X" using less.prems(4) hj by (by100 blast)
          have hTCj: "is_topology_on (C j) (subspace_topology X TX (C j))"
            by (rule subspace_topology_is_topology_on[OF hTX' hCj_sub])
          have hCj_compact: "top1_compact_on (C j) (subspace_topology X TX (C j))"
          proof -
            have "top1_compact_on ((g j) ` top1_S1) (subspace_topology (C j) (subspace_topology X TX (C j)) ((g j) ` top1_S1))"
              by (rule top1_compact_on_continuous_image[OF S1_compact hTCj hg_cont])
            moreover have "(g j) ` top1_S1 = C j" using hg_img by (by100 simp)
            moreover have "subspace_topology (C j) (subspace_topology X TX (C j)) (C j)
                = subspace_topology X TX (C j)"
            proof (rule subspace_topology_self)
              show "\<forall>U\<in>subspace_topology X TX (C j). U \<subseteq> C j"
                unfolding subspace_topology_def by (by100 blast)
            qed
            ultimately show ?thesis by (by100 simp)
          qed
          have "C j \<subseteq> X" using less.prems(4) hj by (by100 blast)
          thus "closedin_on X TX (C j)"
            by (rule Theorem_26_3[OF less.prems(2) _ hCj_compact])
        qed
        \<comment> \<open>Step 3: Basic set properties.\<close>
        have hUV_cover: "U \<union> V = X"
        proof -
          have "U \<union> V = C 0 \<union> (\<Union>j\<in>{1..<n}. W j) \<union> (W 0 \<union> (\<Union>j\<in>{1..<n}. C j))"
            unfolding U_def V_def by (by100 blast)
          also have "\<dots> = C 0 \<union> (\<Union>j\<in>{1..<n}. C j)"
          proof -
            have "\<forall>j. W j \<subseteq> C j" unfolding W_def by (by100 blast)
            hence "W 0 \<subseteq> C 0" by (by100 blast)
            hence "C 0 \<union> W 0 = C 0" by (by100 blast)
            moreover have "\<forall>j\<in>{1..<n}. W j \<subseteq> C j" using \<open>\<forall>j. W j \<subseteq> C j\<close> by (by100 blast)
            ultimately show ?thesis by (by100 blast)
          qed
          also have "\<dots> = (\<Union>j\<in>{..<n}. C j)"
          proof -
            have "{..<n} = {0} \<union> {1..<n}" using hn_pos by (by100 auto)
            thus ?thesis by (by100 auto)
          qed
          also have "\<dots> = X" using less.prems(5) by (by100 simp)
          finally show ?thesis .
        qed
        have hW_sub_C: "\<forall>j. W j \<subseteq> C j" unfolding W_def by (by100 blast)
        have hp_W: "\<forall>j<n. p \<in> W j"
        proof (intro allI impI)
          fix j assume "j < n"
          have "p \<in> C j" using less.prems(4) \<open>j < n\<close> by (by100 blast)
          moreover have "p \<noteq> q j" using hq \<open>j < n\<close> by (by100 blast)
          ultimately show "p \<in> W j" unfolding W_def by (by100 blast)
        qed
        have hUV_inter: "U \<inter> V = (\<Union>j\<in>{..<n}. W j)"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> U \<inter> V"
          hence hxU: "x \<in> U" and hxV: "x \<in> V" by (by100 blast)+
          from hxU have "x \<in> C 0 \<or> (\<exists>j\<in>{1..<n}. x \<in> W j)" unfolding U_def by (by100 blast)
          thus "x \<in> (\<Union>j\<in>{..<n}. W j)"
          proof
            assume "x \<in> C 0"
            from hxV have "x \<in> W 0 \<or> (\<exists>j\<in>{1..<n}. x \<in> C j)" unfolding V_def by (by100 blast)
            thus ?thesis
            proof
              assume "x \<in> W 0"
              thus ?thesis using hn_pos by (by100 blast)
            next
              assume "\<exists>j\<in>{1..<n}. x \<in> C j"
              then obtain j where "j \<in> {1..<n}" "x \<in> C j" by (by100 blast)
              hence "x \<in> C 0 \<inter> C j" using \<open>x \<in> C 0\<close> by (by100 blast)
              hence "x = p" using less.prems(6) hn_pos \<open>j \<in> {1..<n}\<close> by (by100 force)
              thus ?thesis using hp_W hn_pos by (by100 blast)
            qed
          next
            assume "\<exists>j\<in>{1..<n}. x \<in> W j"
            then obtain j where hj1: "j \<in> {1..<n}" and "x \<in> W j" by (by100 blast)
            hence "j \<in> {..<n}" by (by100 simp)
            thus ?thesis using \<open>x \<in> W j\<close> by (by100 blast)
          qed
        next
          fix x assume "x \<in> (\<Union>j\<in>{..<n}. W j)"
          then obtain j where "j \<in> {..<n}" "x \<in> W j" by (by100 blast)
          hence hj: "j < n" and "x \<in> C j" "x \<noteq> q j" unfolding W_def by (by100 blast)+
          show "x \<in> U \<inter> V"
          proof (cases "j = 0")
            case True
            hence "x \<in> C 0" using \<open>x \<in> C j\<close> by (by100 simp)
            hence "x \<in> U" unfolding U_def by (by100 blast)
            have "x \<in> W 0" using \<open>x \<in> W j\<close> True by (by100 simp)
            hence "x \<in> V" unfolding V_def by (by100 blast)
            thus ?thesis using \<open>x \<in> U\<close> by (by100 blast)
          next
            case False hence "j \<ge> 1" by (by100 simp)
            hence "j \<in> {1..<n}" using hj by (by100 simp)
            hence "x \<in> (\<Union>j\<in>{1..<n}. W j)" using \<open>x \<in> W j\<close> by (by100 blast)
            hence "x \<in> U" unfolding U_def by (by100 blast)
            have "x \<in> (\<Union>j\<in>{1..<n}. C j)" using \<open>j \<in> {1..<n}\<close> \<open>x \<in> C j\<close> by (by100 blast)
            hence "x \<in> V" unfolding V_def by (by100 blast)
            thus ?thesis using \<open>x \<in> U\<close> by (by100 blast)
          qed
        qed
        \<comment> \<open>Step 4: U, V are open in X (from coherent/weak topology).\<close>
        \<comment> \<open>Complement lemma: X - U = {q(j) | j \<in> {1..<n}} (finite set of removed points).\<close>
        have hXmU: "X - U = q ` {1..<n}"
        proof (rule set_eqI, rule iffI)
          fix x assume hx: "x \<in> X - U"
          hence "x \<in> X" "x \<notin> U" by (by100 blast)+
          hence "x \<notin> C 0" "\<forall>j\<in>{1..<n}. x \<notin> W j" unfolding U_def by (by100 blast)+
          from \<open>x \<in> X\<close> have "x \<in> (\<Union>j\<in>{..<n}. C j)" using less.prems(5) by (by100 simp)
          then obtain k where "k < n" "x \<in> C k" by (by100 blast)
          have "k \<noteq> 0"
          proof
            assume "k = 0" thus False using \<open>x \<notin> C 0\<close> \<open>x \<in> C k\<close> by (by100 simp)
          qed
          hence hk1: "k \<in> {1..<n}" using \<open>k < n\<close> by (by100 simp)
          from \<open>\<forall>j\<in>{1..<n}. x \<notin> W j\<close> hk1 have "x \<notin> W k" by (by100 blast)
          hence "x = q k" using \<open>x \<in> C k\<close> unfolding W_def by (by100 blast)
          thus "x \<in> q ` {1..<n}" using hk1 by (by100 blast)
        next
          fix x assume "x \<in> q ` {1..<n}"
          then obtain k where hk1: "k \<in> {1..<n}" and hxqk: "x = q k" by (by100 blast)
          hence hkn: "k < n" by (by100 simp)
          have "x \<in> C k" using hxqk hq hkn by (by100 blast)
          hence "x \<in> X" using less.prems(4) hkn by (by100 blast)
          have "x \<notin> C 0"
          proof
            assume "x \<in> C 0"
            hence "x \<in> C 0 \<inter> C k" using \<open>x \<in> C k\<close> by (by100 blast)
            hence "x = p" using less.prems(6) hn_pos hkn hk1 by (by100 force)
            thus False using hxqk hq hkn by (by100 blast)
          qed
          have "\<forall>j\<in>{1..<n}. x \<notin> W j"
          proof (intro ballI)
            fix j assume "j \<in> {1..<n}"
            show "x \<notin> W j"
            proof (cases "j = k")
              case True thus ?thesis using hxqk unfolding W_def by (by100 blast)
            next
              case False
              have "j < n" using \<open>j \<in> {1..<n}\<close> by (by100 simp)
              have "x \<notin> C j"
              proof
                assume "x \<in> C j"
                hence "x \<in> C j \<inter> C k" using \<open>x \<in> C k\<close> by (by100 blast)
                hence "x = p" using less.prems(6) \<open>j < n\<close> hkn False by (by100 force)
                thus False using hxqk hq hkn by (by100 blast)
              qed
              thus ?thesis unfolding W_def by (by100 blast)
            qed
          qed
          thus "x \<in> X - U" using \<open>x \<in> X\<close> \<open>x \<notin> C 0\<close> unfolding U_def by (by100 blast)
        qed
        have hU_open: "openin_on X TX U"
        proof -
          have hfin: "finite (q ` {1..<n})" by (by100 simp)
          have hsub: "q ` {1..<n} \<subseteq> X" using hq less.prems(4) by (by100 force)
          have hhaus: "is_hausdorff_on X TX" using less.prems(2) .
          have hcl: "closedin_on X TX (q ` {1..<n})"
            by (rule Theorem_17_8[OF hhaus hfin hsub])
          have "X - U = q ` {1..<n}" by (rule hXmU)
          hence "U = X - q ` {1..<n}"
          proof -
            have "C 0 \<subseteq> X" using less.prems(4) hn_pos by (by100 blast)
            moreover have "\<forall>j\<in>{1..<n}. W j \<subseteq> X"
              using hW_sub_C less.prems(4) by (by100 force)
            ultimately have "U \<subseteq> X" unfolding U_def by (by100 blast)
            thus ?thesis using hXmU by (by100 blast)
          qed
          thus ?thesis using closed_complement_open[OF hcl] by (by100 simp)
        qed
        \<comment> \<open>Similarly: X - V = {q(0)} (one removed point).\<close>
        have hXmV: "X - V = {q 0}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> X - V"
          hence "x \<in> X" "x \<notin> V" by (by100 blast)+
          hence "x \<notin> W 0" "\<forall>j\<in>{1..<n}. x \<notin> C j" unfolding V_def by (by100 blast)+
          from \<open>x \<in> X\<close> obtain k where "k < n" "x \<in> C k"
            using less.prems(5) by (by100 force)
          have "k = 0"
          proof (rule ccontr)
            assume "k \<noteq> 0" hence "k \<in> {1..<n}" using \<open>k < n\<close> by (by100 simp)
            thus False using \<open>\<forall>j\<in>{1..<n}. x \<notin> C j\<close> \<open>x \<in> C k\<close> by (by100 blast)
          qed
          hence "x \<in> C 0" using \<open>x \<in> C k\<close> by (by100 simp)
          hence "x \<in> C 0 - W 0" using \<open>x \<notin> W 0\<close> by (by100 blast)
          thus "x \<in> {q 0}" unfolding W_def by (by100 blast)
        next
          fix x assume "x \<in> {q 0}"
          hence hx: "x = q 0" by (by100 blast)
          have "x \<in> C 0" using hx hq hn_pos by (by100 blast)
          hence "x \<in> X" using less.prems(4) hn_pos by (by100 blast)
          have "x \<notin> W 0" using hx unfolding W_def by (by100 blast)
          have "\<forall>j\<in>{1..<n}. x \<notin> C j"
          proof (intro ballI)
            fix j assume "j \<in> {1..<n}"
            show "x \<notin> C j"
            proof
              assume "x \<in> C j"
              hence "x \<in> C 0 \<inter> C j" using \<open>x \<in> C 0\<close> by (by100 blast)
              hence "x = p" using less.prems(6) hn_pos \<open>j \<in> {1..<n}\<close> by (by100 force)
              thus False using hx hq hn_pos by (by100 blast)
            qed
          qed
          thus "x \<in> X - V" using \<open>x \<in> X\<close> \<open>x \<notin> W 0\<close> unfolding V_def by (by100 blast)
        qed
        have hV_open: "openin_on X TX V"
        proof -
          have "q 0 \<in> C 0" using hq hn_pos by (by100 blast)
          hence hq0X: "q 0 \<in> X" using less.prems(4) hn_pos by (by100 blast)
          have hsub: "{q 0} \<subseteq> X" using hq0X by (by100 blast)
          have hcl: "closedin_on X TX {q 0}"
            by (rule Theorem_17_8[OF less.prems(2) _ hsub]) (by100 simp)
          have "W 0 \<subseteq> X" using hW_sub_C less.prems(4) hn_pos by (by100 force)
          moreover have "\<forall>j\<in>{1..<n}. C j \<subseteq> X" using less.prems(4) by (by100 force)
          ultimately have hVsub: "V \<subseteq> X" unfolding V_def by (by100 blast)
          have "V = X - {q 0}" using hXmV hVsub by (by100 blast)
          thus ?thesis using closed_complement_open[OF hcl] by (by100 simp)
        qed
        \<comment> \<open>Step 5: U \<inter> V is simply connected (each W(j) is simply connected,
           they share only p, and the union deformation-retracts to p).
           Uses: circle\_minus\_point\_simply\_connected from AlgTopSvK.\<close>
        \<comment> \<open>\<Union>W(j) deformation-retracts to {p}. Each W(j) is an arc containing p.
           Retract each point to p along the arc. Compatible since W(j) \<inter> W(k) = {p}.\<close>
        \<comment> \<open>Each W(j) deformation retracts to {p} (Munkres: "W\_i homeomorphic to open interval").\<close>
        have hW_retract: "\<forall>j<n. top1_deformation_retract_of_on
            (W j) (subspace_topology X TX (W j)) {p}"
        proof (intro allI impI)
          fix j assume hj: "j < n"
          have hg_h: "top1_homeomorphism_on top1_S1 top1_S1_topology
              (C j) (subspace_topology X TX (C j)) (g j)"
            using less.prems(7) hj by (by100 blast)
          have hqj: "q j \<in> C j" using hq hj by (by100 blast)
          have hpj: "p \<in> C j" using less.prems(4) hj by (by100 blast)
          have hpq: "q j \<noteq> p" using hq hj by (by100 blast)
          have "top1_deformation_retract_of_on (C j - {q j})
              (subspace_topology (C j) (subspace_topology X TX (C j)) (C j - {q j})) {p}"
            by (rule circle_minus_point_deformation_retract[OF hg_h hqj hpj hpq])
          moreover have "subspace_topology (C j) (subspace_topology X TX (C j)) (C j - {q j})
              = subspace_topology X TX (C j - {q j})"
            by (rule subspace_topology_trans) (by100 blast)
          ultimately show "top1_deformation_retract_of_on (W j) (subspace_topology X TX (W j)) {p}"
            unfolding W_def by (by100 simp)
        qed
        \<comment> \<open>Munkres: "The maps F\_i fit together... pasting lemma applies."
           W(j) closed in U \<inter> V because S(j) closed in X and W(j) = S(j) \<inter> (U\<inter>V).\<close>
        have hUV_retract: "top1_deformation_retract_of_on
            (U \<inter> V) (subspace_topology X TX (U \<inter> V)) {p}"
        proof -
          let ?TUV = "subspace_topology X TX (U \<inter> V)"
          have hTX: "is_topology_on X TX"
            using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
          have hUVsub: "U \<inter> V \<subseteq> X"
          proof -
            have "C 0 \<subseteq> X" using less.prems(4) hn_pos by (by100 blast)
            moreover have "\<forall>j\<in>{1..<n}. W j \<subseteq> X"
              using hW_sub_C less.prems(4) by (by100 force)
            ultimately have "U \<subseteq> X" unfolding U_def by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
          have hTUV_strict: "is_topology_on_strict (U \<inter> V) ?TUV"
            by (rule subspace_topology_is_strict[OF less.prems(1) hUVsub])
          have hTUV: "is_topology_on (U \<inter> V) ?TUV"
            using hTUV_strict unfolding is_topology_on_strict_def by (by100 blast)
          define F_set where "F_set = W ` {..<n}"
          have hfin: "finite F_set" unfolding F_set_def by (by100 simp)
          have hcover: "U \<inter> V = \<Union>F_set"
            unfolding F_set_def using hUV_inter by (by100 auto)
          \<comment> \<open>Each W(j) is closed in U \<inter> V. Munkres: "S\_i is closed in X,
             so W\_i = S\_i - q\_i is closed in U \<inter> V." (since q\_i \<notin> U \<inter> V)\<close>
          have hF_closed: "\<forall>A\<in>F_set. closedin_on (U \<inter> V) ?TUV A"
          proof (intro ballI)
            fix A assume "A \<in> F_set"
            then obtain j where "j < n" "A = W j" unfolding F_set_def by (by100 blast)
            \<comment> \<open>C(j) closed in X: compact (homeo to S1) in Hausdorff space.\<close>
            have "closedin_on X TX (C j)" using hC_closed \<open>j < n\<close> by (by100 blast)
            \<comment> \<open>W(j) = C(j) \<inter> (U \<inter> V), so closed in subspace U \<inter> V.\<close>
            moreover have "A = C j \<inter> (U \<inter> V)"
            proof -
              have "W j = C j \<inter> (U \<inter> V)"
              proof -
                \<comment> \<open>W(j) \<subseteq> C(j) \<inter> (U\<inter>V): W(j) \<subseteq> C(j) and W(j) \<subseteq> U\<inter>V (from hUV\_inter).\<close>
                have "W j \<subseteq> C j" using hW_sub_C by (by100 blast)
                moreover have "W j \<subseteq> U \<inter> V" using hUV_inter \<open>j < n\<close> by (by100 force)
                ultimately have "W j \<subseteq> C j \<inter> (U \<inter> V)" by (by100 blast)
                \<comment> \<open>C(j) \<inter> (U\<inter>V) \<subseteq> W(j): if x \<in> C(j) \<inter> (U\<inter>V) then x \<noteq> q(j)
                   (since q(j) \<notin> U\<inter>V), hence x \<in> C(j) - {q(j)} = W(j).\<close>
                moreover have "C j \<inter> (U \<inter> V) \<subseteq> W j"
                proof (intro subsetI)
                  fix x assume "x \<in> C j \<inter> (U \<inter> V)"
                  hence "x \<in> C j" "x \<in> U \<inter> V" by (by100 blast)+
                  have "x \<noteq> q j"
                  proof
                    assume "x = q j"
                    \<comment> \<open>q(j) \<notin> U\<inter>V = \<Union>W(k): q(j) \<notin> W(j) and q(j) \<notin> W(k) for k\<noteq>j.\<close>
                    have "x \<notin> W j" using \<open>x = q j\<close> unfolding W_def by (by100 blast)
                    moreover have "\<forall>k<n. k \<noteq> j \<longrightarrow> x \<notin> W k"
                    proof (intro allI impI)
                      fix k assume "k < n" "k \<noteq> j"
                      have "x \<in> C j" using \<open>x \<in> C j\<close> .
                      have "W k \<subseteq> C k" using hW_sub_C by (by100 blast)
                      moreover have "x \<noteq> p" using \<open>x = q j\<close> hq \<open>j < n\<close> by (by100 blast)
                      hence "x \<notin> C k"
                        using less.prems(6) \<open>j < n\<close> \<open>k < n\<close> \<open>k \<noteq> j\<close> \<open>x \<in> C j\<close>
                        by (by100 force)
                      ultimately show "x \<notin> W k" by (by100 blast)
                    qed
                    ultimately have "x \<notin> (\<Union>k\<in>{..<n}. W k)" by (by100 force)
                    hence "x \<notin> U \<inter> V" using hUV_inter by (by100 simp)
                    thus False using \<open>x \<in> U \<inter> V\<close> by (by100 blast)
                  qed
                  thus "x \<in> W j" using \<open>x \<in> C j\<close> unfolding W_def by (by100 blast)
                qed
                ultimately show ?thesis by (by100 blast)
              qed
              thus ?thesis using \<open>A = W j\<close> by (by100 simp)
            qed
            ultimately have "closedin_on (U \<inter> V) ?TUV (C j \<inter> (U \<inter> V))"
              using iffD2[OF Theorem_17_2[OF hTX hUVsub]] by (by100 blast)
            thus "closedin_on (U \<inter> V) ?TUV A" using \<open>A = C j \<inter> (U \<inter> V)\<close> by (by100 simp)
          qed
          have hp_UV: "p \<in> U \<inter> V"
          proof -
            have "p \<in> C 0" using less.prems(4) hn_pos by (by100 blast)
            hence "p \<in> U" unfolding U_def by (by100 blast)
            have "p \<noteq> q 0" using hq hn_pos by (by100 blast)
            hence "p \<in> W 0" using \<open>p \<in> C 0\<close> unfolding W_def by (by100 blast)
            hence "p \<in> V" unfolding V_def by (by100 blast)
            thus ?thesis using \<open>p \<in> U\<close> by (by100 blast)
          qed
          have hp_all: "\<forall>A\<in>F_set. p \<in> A" unfolding F_set_def using hp_W by (by100 force)
          have hpairwise: "\<forall>A\<in>F_set. \<forall>B\<in>F_set. A \<noteq> B \<longrightarrow> A \<inter> B = {p}"
          proof (intro ballI impI)
            fix A B assume hAB: "A \<in> F_set" "B \<in> F_set" "A \<noteq> B"
            from hAB(1) obtain i where hi: "i < n" "A = W i" unfolding F_set_def by (by100 blast)
            from hAB(2) obtain j where hj: "j < n" "B = W j" unfolding F_set_def by (by100 blast)
            have "i \<noteq> j"
            proof
              assume "i = j" thus False using hAB(3) hi(2) hj(2) by (by100 simp)
            qed
            have "W i \<inter> W j \<subseteq> C i \<inter> C j" using hW_sub_C by (by100 blast)
            also have "\<dots> = {p}" using less.prems(6) \<open>i < n\<close> \<open>j < n\<close> \<open>i \<noteq> j\<close> by (by100 force)
            finally have "W i \<inter> W j \<subseteq> {p}" .
            moreover have "p \<in> W i \<inter> W j" using hp_W \<open>i < n\<close> \<open>j < n\<close> by (by100 blast)
            ultimately show "A \<inter> B = {p}" using \<open>A = W i\<close> \<open>B = W j\<close> by (by100 blast)
          qed
          \<comment> \<open>Transfer retractions from subspace X TX (W j) to subspace (U\<inter>V) ?TUV (W j).\<close>
          have hdr: "\<forall>A\<in>F_set. top1_deformation_retract_of_on A (subspace_topology (U \<inter> V) ?TUV A) {p}"
          proof (intro ballI)
            fix A assume "A \<in> F_set"
            then obtain j where "j < n" "A = W j" unfolding F_set_def by (by100 blast)
            have "top1_deformation_retract_of_on (W j) (subspace_topology X TX (W j)) {p}"
              using hW_retract \<open>j < n\<close> by (by100 blast)
            moreover have "W j \<subseteq> U \<inter> V"
              using hUV_inter \<open>j < n\<close> by (by100 force)
            hence "subspace_topology (U \<inter> V) ?TUV (W j) = subspace_topology X TX (W j)"
              by (rule subspace_topology_trans)
            ultimately show "top1_deformation_retract_of_on A (subspace_topology (U \<inter> V) ?TUV A) {p}"
              using \<open>A = W j\<close> by (by100 simp)
          qed
          show ?thesis
            by (rule pasting_deformation_retracts_to_point[OF hTUV_strict hfin hF_closed hcover hp_UV hp_all hpairwise hdr])
        qed
        have hUV_sc: "top1_simply_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
        proof -
          have hTX: "is_topology_on X TX"
            using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
          have hUVsub: "U \<inter> V \<subseteq> X"
          proof -
            have "C 0 \<subseteq> X" using less.prems(4) hn_pos by (by100 blast)
            moreover have "\<forall>j\<in>{1..<n}. W j \<subseteq> X"
              using hW_sub_C less.prems(4) by (by100 force)
            ultimately have "U \<subseteq> X" unfolding U_def by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
          have hTUV: "is_topology_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
            by (rule subspace_topology_is_topology_on[OF hTX hUVsub])
          have hp_UV': "p \<in> {p}" by (by100 blast)
          \<comment> \<open>Deformation retract to {p} gives \<pi>_1(U \<inter> V) \<cong> \<pi>_1({p}) = trivial.\<close>
          from Theorem_58_3[OF hUV_retract hTUV hp_UV']
          have "top1_groups_isomorphic_on
              (top1_fundamental_group_carrier {p} (subspace_topology (U \<inter> V) (subspace_topology X TX (U \<inter> V)) {p}) p)
              (top1_fundamental_group_mul {p} (subspace_topology (U \<inter> V) (subspace_topology X TX (U \<inter> V)) {p}) p)
              (top1_fundamental_group_carrier (U \<inter> V) (subspace_topology X TX (U \<inter> V)) p)
              (top1_fundamental_group_mul (U \<inter> V) (subspace_topology X TX (U \<inter> V)) p)" .
          \<comment> \<open>\<pi>_1({p}) is trivial, so \<pi>_1(U \<inter> V) is trivial. Combined with path-connected.\<close>
          \<comment> \<open>U \<inter> V is path-connected: union of path-connected W(j) sharing p.\<close>
          have hUV_pc: "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
          proof -
            define F where "F = W ` {..<n}"
            have hfin: "finite F" unfolding F_def by (by100 simp)
            have hF_sub: "\<forall>A\<in>F. A \<subseteq> U \<inter> V"
              unfolding F_def hUV_inter by (by100 blast)
            have hp_F: "\<forall>A\<in>F. p \<in> A"
              unfolding F_def using hp_W by (by100 force)
            have hF_pc: "\<forall>A\<in>F. top1_path_connected_on A
                (subspace_topology (U \<inter> V) (subspace_topology X TX (U \<inter> V)) A)"
            proof (intro ballI)
              fix A assume "A \<in> F"
              then obtain j where "j < n" "A = W j" unfolding F_def by (by100 blast)
              have hAtrans: "subspace_topology (U \<inter> V) (subspace_topology X TX (U \<inter> V)) A
                  = subspace_topology X TX A"
              proof -
                have "A \<subseteq> U \<inter> V" using hF_sub \<open>A \<in> F\<close> by (by100 blast)
                thus ?thesis by (rule subspace_topology_trans)
              qed
              have hg_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology X TX (C j)) (g j)"
                using less.prems(7) \<open>j < n\<close> by (by100 blast)
              have hqj_in: "q j \<in> C j" using hq \<open>j < n\<close> by (by100 blast)
              have "top1_path_connected_on (C j - {q j})
                  (subspace_topology (C j) (subspace_topology X TX (C j)) (C j - {q j}))"
                using circle_minus_point_path_connected[OF hg_homeo hqj_in] by (by100 simp)
              moreover have "C j - {q j} \<subseteq> C j" by (by100 blast)
              hence "subspace_topology (C j) (subspace_topology X TX (C j)) (C j - {q j})
                  = subspace_topology X TX (C j - {q j})"
                by (rule subspace_topology_trans)
              ultimately have "top1_path_connected_on (W j) (subspace_topology X TX (W j))"
                unfolding W_def by (by100 simp)
              thus "top1_path_connected_on A
                  (subspace_topology (U \<inter> V) (subspace_topology X TX (U \<inter> V)) A)"
                using hAtrans \<open>A = W j\<close> by (by100 simp)
            qed
            have hUV_eq: "U \<inter> V = \<Union>F"
              unfolding F_def using hUV_inter by (by100 auto)
            show ?thesis
              using path_connected_finite_union_common_point[OF hTUV hfin hF_sub hF_pc hp_F hUV_eq] .
          qed
          \<comment> \<open>Every loop at p in U \<inter> V is nulhomotopic.
             From the deformation retraction H: for any loop f at p,
             G(s,t) = H(f(s),t) is a null-homotopy. Continuous by composition.\<close>
          have hp_in_UV: "p \<in> U \<inter> V"
          proof -
            have "p \<in> C 0" using less.prems(4) hn_pos by (by100 blast)
            hence "p \<in> U" unfolding U_def by (by100 blast)
            have "p \<noteq> q 0" using hq hn_pos by (by100 blast)
            hence "p \<in> W 0" using \<open>p \<in> C 0\<close> unfolding W_def by (by100 blast)
            hence "p \<in> V" unfolding V_def by (by100 blast)
            thus ?thesis using \<open>p \<in> U\<close> by (by100 blast)
          qed
          show ?thesis
            by (rule deformation_retract_to_singleton_imp_simply_connected[OF hTUV hp_in_UV hUV_pc hUV_retract])
        qed
        \<comment> \<open>Step 6: U, V are path-connected.\<close>
        have hU_pc: "top1_path_connected_on U (subspace_topology X TX U)"
        proof -
          have hTX: "is_topology_on X TX"
            using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
          have "C 0 \<subseteq> X" using less.prems(4) hn_pos by (by100 blast)
          moreover have "\<forall>j\<in>{1..<n}. W j \<subseteq> X"
            using hW_sub_C less.prems(4) by (by100 force)
          ultimately have hUsub: "U \<subseteq> X" unfolding U_def by (by100 blast)
          have hTU: "is_topology_on U (subspace_topology X TX U)"
            by (rule subspace_topology_is_topology_on[OF hTX hUsub])
          \<comment> \<open>Family: {C(0)} \<union> {W(j) | j \<in> {1..<n}}.\<close>
          define F where "F = insert (C 0) (W ` {1..<n})"
          have hfin: "finite F" unfolding F_def by (by100 simp)
          have hF_sub: "\<forall>A\<in>F. A \<subseteq> U" unfolding F_def U_def by (by100 blast)
          have hp_F: "\<forall>A\<in>F. p \<in> A"
            unfolding F_def using less.prems(4) hn_pos hp_W by (by100 force)
          have hU_eq: "U = \<Union>F" unfolding F_def U_def by (by100 blast)
          \<comment> \<open>Each piece is path-connected in subspace of U. By transitivity,
             subspace U (subspace X TX U) A = subspace X TX A.\<close>
          have hF_pc: "\<forall>A\<in>F. top1_path_connected_on A (subspace_topology U (subspace_topology X TX U) A)"
          proof (intro ballI)
            fix A assume "A \<in> F"
            hence "A \<subseteq> U" using hF_sub by (by100 blast)
            hence hAtrans: "subspace_topology U (subspace_topology X TX U) A = subspace_topology X TX A"
              by (rule subspace_topology_trans)
            from \<open>A \<in> F\<close> have "A = C 0 \<or> (\<exists>j\<in>{1..<n}. A = W j)" unfolding F_def by (by100 blast)
            thus "top1_path_connected_on A (subspace_topology U (subspace_topology X TX U) A)"
            proof
              assume "A = C 0"
              have "top1_path_connected_on (C 0) (subspace_topology X TX (C 0))"
                using circle_path_connected less.prems(7) hn_pos by (by100 blast)
              thus ?thesis using hAtrans \<open>A = C 0\<close> by (by100 simp)
            next
              assume "\<exists>j\<in>{1..<n}. A = W j"
              then obtain j where hj: "j \<in> {1..<n}" and hA: "A = W j" by (by100 blast)
              have hjn: "j < n" using hj by (by100 simp)
              have hg_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C j) (subspace_topology X TX (C j)) (g j)"
                using less.prems(7) hjn by (by100 blast)
              have hqj_in: "q j \<in> C j" using hq hjn by (by100 blast)
              have "top1_path_connected_on (C j - {q j}) (subspace_topology (C j) (subspace_topology X TX (C j)) (C j - {q j}))"
                using circle_minus_point_path_connected[OF hg_homeo hqj_in] by (by100 simp)
              moreover have "C j - {q j} \<subseteq> C j" by (by100 blast)
              hence "subspace_topology (C j) (subspace_topology X TX (C j)) (C j - {q j}) = subspace_topology X TX (C j - {q j})"
                by (rule subspace_topology_trans)
              ultimately have "top1_path_connected_on (W j) (subspace_topology X TX (W j))"
                unfolding W_def by (by100 simp)
              thus ?thesis using hAtrans hA by (by100 simp)
            qed
          qed
          show ?thesis using path_connected_finite_union_common_point[OF hTU hfin hF_sub hF_pc hp_F hU_eq] .
        qed
        have hV_pc: "top1_path_connected_on V (subspace_topology X TX V)"
        proof -
          have hTX: "is_topology_on X TX"
            using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
          have "W 0 \<subseteq> X" using hW_sub_C less.prems(4) hn_pos by (by100 force)
          moreover have "\<forall>j\<in>{1..<n}. C j \<subseteq> X" using less.prems(4) by (by100 force)
          ultimately have hVsub: "V \<subseteq> X" unfolding V_def by (by100 blast)
          have hTV: "is_topology_on V (subspace_topology X TX V)"
            by (rule subspace_topology_is_topology_on[OF hTX hVsub])
          define F where "F = insert (W 0) (C ` {1..<n})"
          have hfin: "finite F" unfolding F_def by (by100 simp)
          have hF_sub: "\<forall>A\<in>F. A \<subseteq> V" unfolding F_def V_def by (by100 blast)
          have hp_F: "\<forall>A\<in>F. p \<in> A"
            unfolding F_def using hp_W hn_pos less.prems(4) by (by100 force)
          have hV_eq: "V = \<Union>F" unfolding F_def V_def by (by100 blast)
          have hF_pc: "\<forall>A\<in>F. top1_path_connected_on A (subspace_topology V (subspace_topology X TX V) A)"
          proof (intro ballI)
            fix A assume "A \<in> F"
            hence "A \<subseteq> V" using hF_sub by (by100 blast)
            hence hAtrans: "subspace_topology V (subspace_topology X TX V) A = subspace_topology X TX A"
              by (rule subspace_topology_trans)
            from \<open>A \<in> F\<close> have "A = W 0 \<or> (\<exists>j\<in>{1..<n}. A = C j)" unfolding F_def by (by100 blast)
            thus "top1_path_connected_on A (subspace_topology V (subspace_topology X TX V) A)"
            proof
              assume "A = W 0"
              have hg0_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
                  (C 0) (subspace_topology X TX (C 0)) (g 0)"
                using less.prems(7) hn_pos by (by100 blast)
              have hq0_in: "q 0 \<in> C 0" using hq hn_pos by (by100 blast)
              have "top1_path_connected_on (C 0 - {q 0}) (subspace_topology (C 0) (subspace_topology X TX (C 0)) (C 0 - {q 0}))"
                using circle_minus_point_path_connected[OF hg0_homeo hq0_in] by (by100 simp)
              moreover have "C 0 - {q 0} \<subseteq> C 0" by (by100 blast)
              hence "subspace_topology (C 0) (subspace_topology X TX (C 0)) (C 0 - {q 0}) = subspace_topology X TX (C 0 - {q 0})"
                by (rule subspace_topology_trans)
              ultimately have "top1_path_connected_on (W 0) (subspace_topology X TX (W 0))"
                unfolding W_def by (by100 simp)
              thus ?thesis using hAtrans \<open>A = W 0\<close> by (by100 simp)
            next
              assume "\<exists>j\<in>{1..<n}. A = C j"
              then obtain j where hj: "j \<in> {1..<n}" and hA: "A = C j" by (by100 blast)
              have hjn: "j < n" using hj by (by100 simp)
              have "top1_path_connected_on (C j) (subspace_topology X TX (C j))"
                using circle_path_connected less.prems(7) hjn by (by100 blast)
              thus ?thesis using hAtrans hA by (by100 simp)
            qed
          qed
          show ?thesis using path_connected_finite_union_common_point[OF hTV hfin hF_sub hF_pc hp_F hV_eq] .
        qed
        have hp_UV: "p \<in> U \<inter> V"
        proof -
          have "p \<in> C 0" using less.prems(4) hn_pos by (by100 blast)
          hence "p \<in> U" unfolding U_def by (by100 blast)
          have "p \<noteq> q 0" using hq hn_pos by (by100 blast)
          hence "p \<in> W 0" using \<open>p \<in> C 0\<close> unfolding W_def by (by100 blast)
          hence "p \<in> V" unfolding V_def by (by100 blast)
          thus ?thesis using \<open>p \<in> U\<close> by (by100 blast)
        qed
        \<comment> \<open>Step 7: The whole inductive step is assembled from the above.
           Apply SvK (Corollary\_70\_3) + Theorem\_69\_2 + IH.
           The composition of isomorphisms gives \<Phi> with generator tracking.\<close>
        \<comment> \<open>Step 7: Apply SvK (Corollary\_70\_3): \<pi>_1(X) \<cong> FP = \<pi>_1(U) * \<pi>_1(V).\<close>
        have hstrict: "is_topology_on_strict X TX" using less.prems(1) .
        \<comment> \<open>Step 8: \<pi>_1(U) \<cong> Z (deformation retract U to C(0) \<cong> S1).
           U = C(0) \<union> arcs. Retract arcs to p. Then \<pi>_1(U) \<cong> \<pi>_1(C(0)) \<cong> Z.\<close>
        \<comment> \<open>U deformation retracts to C(0). Each W(j) for j \<ge> 1 retracts to p \<in> C(0).\<close>
        \<comment> \<open>Munkres: "A similar argument shows that S\_1 is a deformation retract of U."
           U = C(0) \<union> arcs. Identity on C(0), retract each arc W(j) to p \<in> C(0).
           Pasting: C(0) closed in U (compact in Hausdorff), each W(j) closed (same reason).\<close>
        have hU_retract: "top1_deformation_retract_of_on U (subspace_topology X TX U) (C 0)"
        proof -
          let ?TU = "subspace_topology X TX U"
          have hTX: "is_topology_on X TX"
            using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
          have "C 0 \<subseteq> X" using less.prems(4) hn_pos by (by100 blast)
          moreover have "\<forall>j\<in>{1..<n}. W j \<subseteq> X" using hW_sub_C less.prems(4) by (by100 force)
          ultimately have hUsub: "U \<subseteq> X" unfolding U_def by (by100 blast)
          have hTU'_strict: "is_topology_on_strict U ?TU"
            by (rule subspace_topology_is_strict[OF less.prems(1) hUsub])
          have hTU': "is_topology_on U ?TU"
            using hTU'_strict unfolding is_topology_on_strict_def by (by100 blast)
          define F_U where "F_U = insert (C 0) (W ` {1..<n})"
          have hU_eq': "U = \<Union>F_U" unfolding F_U_def U_def by (by100 blast)
          have hfin': "finite F_U" unfolding F_U_def by (by100 simp)
          have hC0_in: "C 0 \<in> F_U" unfolding F_U_def by (by100 blast)
          have hF_closed': "\<forall>A\<in>F_U. closedin_on U ?TU A"
          proof (intro ballI)
            fix A assume "A \<in> F_U"
            hence "A = C 0 \<or> (\<exists>j\<in>{1..<n}. A = W j)" unfolding F_U_def by (by100 blast)
            thus "closedin_on U ?TU A"
            proof
              assume "A = C 0"
              have "closedin_on X TX (C 0)" using hC_closed hn_pos by (by100 blast)
              have "C 0 \<subseteq> U" unfolding U_def by (by100 blast)
              hence "C 0 = C 0 \<inter> U" by (by100 blast)
              thus ?thesis using \<open>A = C 0\<close> iffD2[OF Theorem_17_2[OF hTX hUsub]]
                \<open>closedin_on X TX (C 0)\<close> by (by100 blast)
            next
              assume "\<exists>j\<in>{1..<n}. A = W j"
              then obtain j where "j \<in> {1..<n}" "A = W j" by (by100 blast)
              have hjn: "j < n" using \<open>j \<in> {1..<n}\<close> by (by100 simp)
              have "closedin_on X TX (C j)" using hC_closed hjn by (by100 blast)
              have "W j \<subseteq> U" unfolding U_def using \<open>j \<in> {1..<n}\<close> by (by100 blast)
              have "W j = C j \<inter> U"
              proof -
                have "q j \<notin> U"
                proof -
                  have "q j \<in> q ` {1..<n}" using \<open>j \<in> {1..<n}\<close> by (by100 blast)
                  hence "q j \<in> X - U" using hXmU by (by100 simp)
                  thus ?thesis by (by100 blast)
                qed
                have "C j \<subseteq> U \<union> {q j}"
                proof
                  fix x assume "x \<in> C j"
                  show "x \<in> U \<union> {q j}"
                  proof (cases "x = q j")
                    case True thus ?thesis by (by100 blast)
                  next
                    case False hence "x \<in> W j" using \<open>x \<in> C j\<close> unfolding W_def by (by100 blast)
                    hence "x \<in> U" unfolding U_def using \<open>j \<in> {1..<n}\<close> by (by100 blast)
                    thus ?thesis by (by100 blast)
                  qed
                qed
                thus ?thesis unfolding W_def using \<open>q j \<notin> U\<close> by (by100 blast)
              qed
              thus ?thesis using \<open>A = W j\<close> iffD2[OF Theorem_17_2[OF hTX hUsub]]
                \<open>closedin_on X TX (C j)\<close> by (by100 blast)
            qed
          qed
          have hpairwise': "\<forall>A\<in>F_U. \<forall>B\<in>F_U. A \<noteq> B \<longrightarrow> A \<inter> B \<subseteq> {p}"
          proof (intro ballI impI)
            fix A B assume "A \<in> F_U" "B \<in> F_U" "A \<noteq> B"
            from \<open>A \<in> F_U\<close> have hA: "A = C 0 \<or> (\<exists>i\<in>{1..<n}. A = W i)" unfolding F_U_def by (by100 blast)
            from \<open>B \<in> F_U\<close> have hB: "B = C 0 \<or> (\<exists>j\<in>{1..<n}. B = W j)" unfolding F_U_def by (by100 blast)
            show "A \<inter> B \<subseteq> {p}"
            proof -
              have hCij: "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> C i \<inter> C j = {p}"
                using less.prems(6) by (by100 force)
              \<comment> \<open>Case analysis: A and B are among C(0), W(i) for i \<ge> 1.
                 In all cases A \<subseteq> C(iA) and B \<subseteq> C(iB) with iA \<noteq> iB.\<close>
              from hA show ?thesis
              proof
                assume "A = C 0"
                from hB show ?thesis
                proof
                  assume "B = C 0" thus ?thesis using \<open>A = C 0\<close> \<open>A \<noteq> B\<close> by (by100 blast)
                next
                  assume "\<exists>j\<in>{1..<n}. B = W j"
                  then obtain j where "j \<in> {1..<n}" "B = W j" by (by100 blast)
                  have "A \<inter> B \<subseteq> C 0 \<inter> C j" using \<open>A = C 0\<close> \<open>B = W j\<close> hW_sub_C by (by100 blast)
                  also have "\<dots> = {p}" using hCij hn_pos \<open>j \<in> {1..<n}\<close> by (by100 force)
                  finally show ?thesis .
                qed
              next
                assume "\<exists>i\<in>{1..<n}. A = W i"
                then obtain i where "i \<in> {1..<n}" "A = W i" by (by100 blast)
                from hB show ?thesis
                proof
                  assume "B = C 0"
                  have "A \<inter> B \<subseteq> C i \<inter> C 0" using \<open>A = W i\<close> \<open>B = C 0\<close> hW_sub_C by (by100 blast)
                  also have "\<dots> = {p}" using hCij hn_pos \<open>i \<in> {1..<n}\<close> by (by100 force)
                  finally show ?thesis .
                next
                  assume "\<exists>j\<in>{1..<n}. B = W j"
                  then obtain j where "j \<in> {1..<n}" "B = W j" by (by100 blast)
                  have "i \<noteq> j"
                  proof
                    assume "i = j" thus False using \<open>A = W i\<close> \<open>B = W j\<close> \<open>A \<noteq> B\<close> by (by100 simp)
                  qed
                  have "A \<inter> B \<subseteq> C i \<inter> C j" using \<open>A = W i\<close> \<open>B = W j\<close> hW_sub_C by (by100 blast)
                  also have "\<dots> = {p}" using hCij \<open>i \<in> {1..<n}\<close> \<open>j \<in> {1..<n}\<close> \<open>i \<noteq> j\<close> by (by100 force)
                  finally show ?thesis .
                qed
              qed
            qed
          qed
          have hdr': "\<forall>A\<in>F_U - {C 0}. top1_deformation_retract_of_on A (subspace_topology U ?TU A) {p}"
          proof (intro ballI)
            fix A assume "A \<in> F_U - {C 0}"
            then obtain j where "j \<in> {1..<n}" "A = W j" unfolding F_U_def by (by100 blast)
            have "top1_deformation_retract_of_on (W j) (subspace_topology X TX (W j)) {p}"
              using hW_retract \<open>j \<in> {1..<n}\<close> by (by100 force)
            moreover have "W j \<subseteq> U" unfolding U_def using \<open>j \<in> {1..<n}\<close> by (by100 blast)
            hence "subspace_topology U ?TU (W j) = subspace_topology X TX (W j)"
              by (rule subspace_topology_trans)
            ultimately show "top1_deformation_retract_of_on A (subspace_topology U ?TU A) {p}"
              using \<open>A = W j\<close> by (by100 simp)
          qed
          have "p \<in> C 0" using less.prems(4) hn_pos by (by100 blast)
          show ?thesis
          proof -
            have hp_all_FU: "\<forall>A\<in>F_U. p \<in> A"
              unfolding F_U_def using \<open>p \<in> C 0\<close> hp_W by (by100 force)
            show ?thesis
              by (rule pasting_deformation_retract_to_subspace[OF hTU'_strict hfin' hC0_in hF_closed' hU_eq' \<open>p \<in> C 0\<close> hp_all_FU hpairwise' hdr'])
          qed
        qed
        \<comment> \<open>By Theorem\_58\_3: deformation retract gives \<pi>_1 iso.\<close>
        have hTU: "is_topology_on U (subspace_topology X TX U)"
        proof -
          have hTX: "is_topology_on X TX"
            using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
          have "C 0 \<subseteq> X" using less.prems(4) hn_pos by (by100 blast)
          moreover have "\<forall>j\<in>{1..<n}. W j \<subseteq> X"
            using hW_sub_C less.prems(4) by (by100 force)
          ultimately have "U \<subseteq> X" unfolding U_def by (by100 blast)
          thus ?thesis by (rule subspace_topology_is_topology_on[OF hTX])
        qed
        have hC0_sub_U: "C 0 \<subseteq> U" unfolding U_def by (by100 blast)
        have hp_C0: "p \<in> C 0" using less.prems(4) hn_pos by (by100 blast)
        \<comment> \<open>Book Theorem 58.3: the inclusion-induced map is THE iso.\<close>
        have hC0_trans: "subspace_topology U (subspace_topology X TX U) (C 0) = subspace_topology X TX (C 0)"
          using hC0_sub_U by (rule subspace_topology_trans)
        let ?incl_U = "top1_fundamental_group_induced_on (C 0) (subspace_topology X TX (C 0)) p U (subspace_topology X TX U) p (\<lambda>x. x)"
        have hC0_incl_iso_U: "top1_group_iso_on
            (top1_fundamental_group_carrier (C 0) (subspace_topology X TX (C 0)) p)
            (top1_fundamental_group_mul (C 0) (subspace_topology X TX (C 0)) p)
            (top1_fundamental_group_carrier U (subspace_topology X TX U) p)
            (top1_fundamental_group_mul U (subspace_topology X TX U) p) ?incl_U"
        proof -
          from Theorem_58_3_explicit[OF hU_retract hTU hp_C0]
          show ?thesis using hC0_trans by (by100 simp)
        qed
        \<comment> \<open>\<pi>_1(C(0), subspace X TX (C 0)) is free on {0} with loop\_class(0) as generator.
           Apply the n=1 case to C(0). First verify the hypotheses.\<close>
        \<comment> \<open>Munkres: "\<pi>\_1(U) is infinite cyclic, and f\_1 represents a generator."
           Step 1: Apply the n=1 case (less.IH with 1 < n) to C(0) \<cong> S1.
           Step 2: Transfer through Theorem\_58\_3 iso (deformation retract).
           Step 3: Generator preservation via inclusion-induced map.\<close>
        \<comment> \<open>Step 1: \<pi>\_1(C(0)) is free on {0} with g(0)\<circ>std\_loop as generator.\<close>
        have hC0_free: "\<exists>(G1::int set) mul1 e1 invg1 (\<eta>1::nat \<Rightarrow> int) \<Phi>1.
            top1_is_free_group_full_on G1 mul1 e1 invg1 \<eta>1 {..<(1::nat)}
          \<and> top1_group_iso_on G1 mul1
              (top1_fundamental_group_carrier (C 0) (subspace_topology X TX (C 0)) p)
              (top1_fundamental_group_mul (C 0) (subspace_topology X TX (C 0)) p) \<Phi>1
          \<and> (\<forall>j<(1::nat). \<Phi>1 (\<eta>1 j) = {l. top1_loop_equiv_on (C 0) (subspace_topology X TX (C 0)) p
              (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l})"
        proof -
          \<comment> \<open>Apply less.IH with n'=1 to C(0).\<close>
          let ?TX0 = "subspace_topology X TX (C 0)"
          let ?C0 = "\<lambda>_::nat. C 0"
          let ?g0 = "\<lambda>_::nat. g 0"
          have h1_lt: "(1::nat) < n" using hn2 by (by100 linarith)
          \<comment> \<open>Verify the 9 hypotheses for C(0) as a 1-circle wedge.\<close>
          have hstrict0: "is_topology_on_strict (C 0) ?TX0"
            using subspace_topology_is_strict[OF less.prems(1)]
                  less.prems(4) hn_pos by (by100 force)
          have hhaus0: "is_hausdorff_on (C 0) ?TX0"
            using conjunct2[OF conjunct2[OF Theorem_17_11]] less.prems(2) less.prems(4) hn_pos
            by (by100 blast)
          have hp0: "p \<in> C 0" using less.prems(4) hn_pos by (by100 blast)
          have hC_sub0: "\<forall>j<(1::nat). ?C0 j \<subseteq> C 0 \<and> p \<in> ?C0 j"
            using hp0 by (by100 simp)
          have hC_union0: "(\<Union>j\<in>{..<(1::nat)}. ?C0 j) = C 0"
          proof -
            have "{..<(1::nat)} = {0}" by (by100 auto)
            thus ?thesis by (by100 simp)
          qed
          have hC_disj0: "\<forall>i<(1::nat). \<forall>j<(1::nat). i \<noteq> j \<longrightarrow> ?C0 i \<inter> ?C0 j = {p}"
            by (by100 simp)
          have hC_homeo0: "\<forall>j<(1::nat). top1_homeomorphism_on top1_S1 top1_S1_topology
              (?C0 j) (subspace_topology (C 0) ?TX0 (?C0 j)) (?g0 j)"
          proof (intro allI impI)
            fix j :: nat assume "j < 1"
            hence "j = 0" by (by100 simp)
            have "subspace_topology (C 0) ?TX0 (C 0) = ?TX0"
            proof (rule subspace_topology_self)
              show "\<forall>U\<in>?TX0. U \<subseteq> C 0" unfolding subspace_topology_def by (by100 blast)
            qed
            thus "top1_homeomorphism_on top1_S1 top1_S1_topology (?C0 j) (subspace_topology (C 0) ?TX0 (?C0 j)) (?g0 j)"
              using less.prems(7) hn_pos \<open>j = 0\<close> by (by100 simp)
          qed
          have hC_base0: "\<forall>j<(1::nat). ?g0 j (1, 0) = p"
            using less.prems(8) hn_pos by (by100 simp)
          \<comment> \<open>Coherent topology for 1 circle is trivial: closedin(C0) D \<longleftrightarrow> closedin(C0) (C0 \<inter> D)
             which holds since D \<subseteq> C0 gives C0 \<inter> D = D.\<close>
          have hC0_self: "subspace_topology (C 0) ?TX0 (C 0) = ?TX0"
          proof (rule subspace_topology_self)
            show "\<forall>U\<in>?TX0. U \<subseteq> C 0" unfolding subspace_topology_def by (by100 blast)
          qed
          have hC_closed0: "\<forall>D\<subseteq>C 0. closedin_on (C 0) ?TX0 D \<longleftrightarrow>
              (\<forall>j<(1::nat). closedin_on (?C0 j) (subspace_topology (C 0) ?TX0 (?C0 j)) (?C0 j \<inter> D))"
          proof (intro allI impI)
            fix D assume hD: "D \<subseteq> C 0"
            hence hCD: "C 0 \<inter> D = D" by (by100 blast)
            show "closedin_on (C 0) ?TX0 D \<longleftrightarrow>
                (\<forall>j<(1::nat). closedin_on (?C0 j) (subspace_topology (C 0) ?TX0 (?C0 j)) (?C0 j \<inter> D))"
              using hC0_self hCD by (by100 simp)
          qed
          from less.IH[OF h1_lt hstrict0 hhaus0 hp0 hC_sub0 hC_union0 hC_disj0 hC_homeo0 hC_base0 hC_closed0]
          show ?thesis .
        qed
        \<comment> \<open>Step 2+3: Transfer from \<pi>\_1(C(0)) to \<pi>\_1(U) via deformation retract.
           The Theorem\_58\_3 iso is the inclusion-induced map, which preserves loop classes
           by subspace\_inclusion\_induced\_class.\<close>
        have hU_free: "\<exists>(G1::int set) mul1 e1 invg1 (\<eta>1::nat \<Rightarrow> int) \<Phi>1.
            top1_is_free_group_full_on G1 mul1 e1 invg1 \<eta>1 {0::nat}
          \<and> top1_group_iso_on G1 mul1
              (top1_fundamental_group_carrier U (subspace_topology X TX U) p)
              (top1_fundamental_group_mul U (subspace_topology X TX U) p) \<Phi>1
          \<and> \<Phi>1 (\<eta>1 0) = {l. top1_loop_equiv_on U (subspace_topology X TX U) p
              (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l}"
        proof -
          \<comment> \<open>Step 1: Extract from hC0\_free.\<close>
          from hC0_free obtain G1 :: "int set" and mul1 e1 invg1
              and \<eta>1 :: "nat \<Rightarrow> int" and \<Phi>1' where
            hG1_all: "top1_is_free_group_full_on G1 mul1 e1 invg1 \<eta>1 {..<(1::nat)}
            \<and> top1_group_iso_on G1 mul1
                (top1_fundamental_group_carrier (C 0) (subspace_topology X TX (C 0)) p)
                (top1_fundamental_group_mul (C 0) (subspace_topology X TX (C 0)) p) \<Phi>1'
            \<and> (\<forall>j<(1::nat). \<Phi>1' (\<eta>1 j) = {l. top1_loop_equiv_on (C 0)
                (subspace_topology X TX (C 0)) p (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l})"
            by (by5000 auto)
          have hG1_free: "top1_is_free_group_full_on G1 mul1 e1 invg1 \<eta>1 {..<(1::nat)}"
            using hG1_all by (by100 blast)
          have h\<Phi>1'_iso: "top1_group_iso_on G1 mul1
              (top1_fundamental_group_carrier (C 0) (subspace_topology X TX (C 0)) p)
              (top1_fundamental_group_mul (C 0) (subspace_topology X TX (C 0)) p) \<Phi>1'"
            using hG1_all by (by100 blast)
          have h\<Phi>1'_gen: "\<forall>j<(1::nat). \<Phi>1' (\<eta>1 j) = {l. top1_loop_equiv_on (C 0)
              (subspace_topology X TX (C 0)) p (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l}"
            using hG1_all by (by100 blast)
          have hJ1: "{..<(1::nat)} = {0}" by (by100 auto)
          \<comment> \<open>Step 2: Compose \<Phi>1 = incl\_U \<circ> \<Phi>1' : G1 \<rightarrow> \<pi>\_1(C(0)) \<rightarrow> \<pi>\_1(U).\<close>
          define \<Phi>1 where "\<Phi>1 = ?incl_U \<circ> \<Phi>1'"
          \<comment> \<open>\<Phi>1 is an iso (composition of isos) by group\_iso\_on\_compose.\<close>
          have h\<Phi>1_iso: "top1_group_iso_on G1 mul1
              (top1_fundamental_group_carrier U (subspace_topology X TX U) p)
              (top1_fundamental_group_mul U (subspace_topology X TX U) p) \<Phi>1"
          proof -
            have hG1_grp: "top1_is_group_on G1 mul1 e1 invg1"
              using hG1_free unfolding top1_is_free_group_full_on_def by (by100 blast)
            have hC0_grp: "top1_is_group_on
                (top1_fundamental_group_carrier (C 0) (subspace_topology X TX (C 0)) p)
                (top1_fundamental_group_mul (C 0) (subspace_topology X TX (C 0)) p)
                (top1_fundamental_group_id (C 0) (subspace_topology X TX (C 0)) p)
                (top1_fundamental_group_invg (C 0) (subspace_topology X TX (C 0)) p)"
            proof -
              have hTX_here: "is_topology_on X TX"
                using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
              have "C 0 \<subseteq> X" using less.prems(4) hn_pos by (by100 blast)
              have "is_topology_on (C 0) (subspace_topology X TX (C 0))"
                by (rule subspace_topology_is_topology_on[OF hTX_here \<open>C 0 \<subseteq> X\<close>])
              thus ?thesis by (rule top1_fundamental_group_is_group) (rule hp_C0)
            qed
            have hU_grp: "top1_is_group_on
                (top1_fundamental_group_carrier U (subspace_topology X TX U) p)
                (top1_fundamental_group_mul U (subspace_topology X TX U) p)
                (top1_fundamental_group_id U (subspace_topology X TX U) p)
                (top1_fundamental_group_invg U (subspace_topology X TX U) p)"
            proof -
              have "p \<in> U" unfolding U_def using hp_C0 by (by100 blast)
              thus ?thesis by (rule top1_fundamental_group_is_group[OF hTU])
            qed
            show ?thesis unfolding \<Phi>1_def
              by (rule group_iso_on_compose[OF h\<Phi>1'_iso hC0_incl_iso_U hG1_grp hC0_grp hU_grp])
          qed
          \<comment> \<open>Step 3: Generator correspondence via subspace\_inclusion\_induced\_class.
             \<Phi>1(\<eta>1 0) = incl\_U(\<Phi>1'(\<eta>1 0)) = incl\_U([g0\<circ>std\_loop]\_{C(0)}) = [g0\<circ>std\_loop]\_U.\<close>
          have h\<Phi>1_gen: "\<Phi>1 (\<eta>1 0) = {l. top1_loop_equiv_on U (subspace_topology X TX U) p
              (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l}"
          proof -
            have h0lt: "(0::nat) < 1" by (by100 simp)
            have "\<Phi>1 (\<eta>1 0) = ?incl_U (\<Phi>1' (\<eta>1 0))" unfolding \<Phi>1_def comp_def by (by100 simp)
            also have "\<Phi>1' (\<eta>1 0) = {l. top1_loop_equiv_on (C 0) (subspace_topology X TX (C 0)) p
                (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l}"
              using h\<Phi>1'_gen h0lt by (by100 blast)
            also have "?incl_U \<dots> = {k. top1_loop_equiv_on U (subspace_topology X TX U) p
                (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) k}"
            proof -
              let ?loop0 = "\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))"
              have hloop0: "top1_is_loop_on (C 0) (subspace_topology X TX (C 0)) p ?loop0"
              proof -
                have hg0_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C 0) (subspace_topology X TX (C 0)) (g 0)"
                  using less.prems(7) hn_pos by (by100 blast)
                have hg0_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
                    (C 0) (subspace_topology X TX (C 0)) (g 0)"
                  using hg0_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
                have hstd: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0)
                    (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))"
                  by (rule standard_S1_loop_is_loop)
                have "top1_is_loop_on (C 0) (subspace_topology X TX (C 0)) (g 0 (1, 0))
                    ((g 0) \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))))"
                  by (rule top1_continuous_map_loop_early[OF hg0_cont hstd])
                moreover have "(g 0) \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) = ?loop0"
                  unfolding comp_def by (by100 simp)
                moreover have "g 0 (1, 0) = p" using less.prems(8) hn_pos by (by100 blast)
                ultimately show ?thesis by (by100 simp)
              qed
              \<comment> \<open>subspace\_inclusion\_induced\_class with X=U, A=C(0).\<close>
              have hloop0': "top1_is_loop_on (C 0) (subspace_topology U (subspace_topology X TX U) (C 0)) p ?loop0"
                using hloop0 hC0_trans by (by100 simp)
              have "top1_fundamental_group_induced_on (C 0) (subspace_topology U (subspace_topology X TX U) (C 0))
                  p U (subspace_topology X TX U) p (\<lambda>x. x)
                  {k. top1_loop_equiv_on (C 0) (subspace_topology U (subspace_topology X TX U) (C 0)) p ?loop0 k}
                = {k. top1_loop_equiv_on U (subspace_topology X TX U) p ?loop0 k}"
                by (rule subspace_inclusion_induced_class[OF hTU hC0_sub_U hloop0'])
              \<comment> \<open>Simplify using hC0\_trans.\<close>
              thus ?thesis using hC0_trans by (by100 simp)
            qed
            finally show ?thesis .
          qed
          have hG1_free': "top1_is_free_group_full_on G1 mul1 e1 invg1 \<eta>1 {0::nat}"
            using hG1_free hJ1 by (by100 simp)
          show ?thesis
            apply (rule exI[of _ G1], rule exI[of _ mul1], rule exI[of _ e1],
                   rule exI[of _ invg1], rule exI[of _ \<eta>1], rule exI[of _ \<Phi>1])
            using hG1_free' h\<Phi>1_iso h\<Phi>1_gen by (by100 blast)
        qed
        \<comment> \<open>Step 9: IH on V. V contains circles C(1),...,C(n-1) as a sub-wedge.
           By inductive hypothesis (less.IH with n-1 < n), \<pi>_1(V) is free on n-1 generators
           with loop correspondence for C(1),...,C(n-1).\<close>
        \<comment> \<open>Munkres: "S\_2 \<union> \<cdots> \<union> S\_n is a deformation retract of V."
           V = W(0) \<union> C(1) \<union> \<cdots> \<union> C(n-1). Retract W(0) to p.\<close>
        define X' where "X' = (\<Union>j\<in>{1..<n}. C j)"
        have hV_retract: "top1_deformation_retract_of_on V (subspace_topology X TX V) X'"
        proof -
          \<comment> \<open>V = W(0) \<union> C(1) \<union> ... \<union> C(n-1). X' = C(1) \<union> ... \<union> C(n-1).
             Retract W(0) to {p} \<subseteq> X'. Identity on C(j) for j \<ge> 1.
             Use pasting\_deformation\_retract\_to\_subspace with A0 = X'.\<close>
          let ?TV = "subspace_topology X TX V"
          have hTX: "is_topology_on X TX"
            using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
          have "W 0 \<subseteq> X" using hW_sub_C less.prems(4) hn_pos by (by100 force)
          moreover have "\<forall>j\<in>{1..<n}. C j \<subseteq> X" using less.prems(4) by (by100 force)
          ultimately have hVsub: "V \<subseteq> X" unfolding V_def by (by100 blast)
          have hTV'_strict: "is_topology_on_strict V ?TV"
            by (rule subspace_topology_is_strict[OF less.prems(1) hVsub])
          have hTV': "is_topology_on V ?TV"
            using hTV'_strict unfolding is_topology_on_strict_def by (by100 blast)
          \<comment> \<open>F = {X', W(0)}. X' is the "base" set, W(0) retracts to p.\<close>
          define F_V where "F_V = {X', W 0}"
          have hfin': "finite F_V" unfolding F_V_def by (by100 simp)
          have hX'_in: "X' \<in> F_V" unfolding F_V_def by (by100 blast)
          have hV_eq': "V = \<Union>F_V" unfolding F_V_def V_def X'_def by (by100 blast)
          have hF_closed': "\<forall>A\<in>F_V. closedin_on V ?TV A"
          proof (intro ballI)
            fix A assume "A \<in> F_V"
            hence "A = X' \<or> A = W 0" unfolding F_V_def by (by100 blast)
            thus "closedin_on V ?TV A"
            proof
              assume "A = X'"
              \<comment> \<open>X' = \<Union>{1..<n} C(j). Each C(j) closed in X, finite union closed.\<close>
              have "closedin_on X TX X'"
              proof -
                have "\<forall>j\<in>{1..<n}. closedin_on X TX (C j)"
                  using hC_closed by (by100 force)
                moreover have "X' = (\<Union>j\<in>{1..<n}. C j)" unfolding X'_def ..
                ultimately show ?thesis
                proof -
                  assume hcl: "\<forall>j\<in>{1..<n}. closedin_on X TX (C j)" and hX'eq: "X' = (\<Union>j\<in>{1..<n}. C j)"
                  have "\<forall>A\<in>C ` {1..<n}. closedin_on X TX A" using hcl by (by100 blast)
                  moreover have "finite (C ` {1..<n})" by (by100 simp)
                  have hTXh: "is_topology_on X TX"
                    using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
                  ultimately have "closedin_on X TX (\<Union>(C ` {1..<n}))"
                    using closedin_on_finite_Union[OF hTXh, of "C ` {1..<n}"] by (by100 blast)
                  moreover have "(\<Union>(C ` {1..<n})) = X'" using hX'eq by (by100 auto)
                  ultimately show ?thesis by (by100 simp)
                qed
              qed
              have "X' \<subseteq> V" unfolding X'_def V_def by (by100 blast)
              hence "X' = X' \<inter> V" by (by100 blast)
              thus ?thesis using \<open>A = X'\<close> iffD2[OF Theorem_17_2[OF hTX hVsub]]
                \<open>closedin_on X TX X'\<close> by (by100 blast)
            next
              assume "A = W 0"
              have "closedin_on X TX (C 0)" using hC_closed hn_pos by (by100 blast)
              have "W 0 \<subseteq> V" unfolding V_def by (by100 blast)
              have "W 0 = C 0 \<inter> V"
              proof -
                have "q 0 \<notin> V" using hXmV by (by100 blast)
                \<comment> \<open>C(0) \<subseteq> V \<union> {q 0}: V = W(0) \<union> ... and W(0) = C(0) - {q(0)}.\<close>
                have "C 0 \<subseteq> V \<union> {q 0}"
                proof
                  fix x assume "x \<in> C 0"
                  show "x \<in> V \<union> {q 0}"
                  proof (cases "x = q 0")
                    case True thus ?thesis by (by100 blast)
                  next
                    case False hence "x \<in> W 0" using \<open>x \<in> C 0\<close> unfolding W_def by (by100 blast)
                    hence "x \<in> V" unfolding V_def by (by100 blast)
                    thus ?thesis by (by100 blast)
                  qed
                qed
                thus ?thesis unfolding W_def using \<open>q 0 \<notin> V\<close> by (by100 blast)
              qed
              thus ?thesis using \<open>A = W 0\<close> iffD2[OF Theorem_17_2[OF hTX hVsub]]
                \<open>closedin_on X TX (C 0)\<close> by (by100 blast)
            qed
          qed
          have hpairwise': "\<forall>A\<in>F_V. \<forall>B\<in>F_V. A \<noteq> B \<longrightarrow> A \<inter> B \<subseteq> {p}"
          proof (intro ballI impI)
            fix A B assume "A \<in> F_V" "B \<in> F_V" "A \<noteq> B"
            hence "A = X' \<and> B = W 0 \<or> A = W 0 \<and> B = X'"
              unfolding F_V_def by (by100 blast)
            hence "A \<inter> B = X' \<inter> W 0 \<or> A \<inter> B = W 0 \<inter> X'" by (by100 blast)
            moreover have "X' \<inter> W 0 \<subseteq> {p}"
            proof -
              have "X' \<inter> W 0 \<subseteq> (\<Union>j\<in>{1..<n}. C j) \<inter> C 0"
                unfolding X'_def using hW_sub_C by (by100 blast)
              also have "\<dots> \<subseteq> {p}"
                using less.prems(6) hn_pos by (by100 force)
              finally show ?thesis .
            qed
            ultimately show "A \<inter> B \<subseteq> {p}" by (by100 blast)
          qed
          have hp_X': "p \<in> X'"
            unfolding X'_def using less.prems(4) hn2 by (by100 force)
          have hdr': "\<forall>A\<in>F_V - {X'}. top1_deformation_retract_of_on A (subspace_topology V ?TV A) {p}"
          proof (intro ballI)
            fix A assume "A \<in> F_V - {X'}"
            hence "A = W 0" unfolding F_V_def by (by100 blast)
            have "top1_deformation_retract_of_on (W 0) (subspace_topology X TX (W 0)) {p}"
              using hW_retract hn_pos by (by100 blast)
            moreover have "W 0 \<subseteq> V" unfolding V_def by (by100 blast)
            hence "subspace_topology V ?TV (W 0) = subspace_topology X TX (W 0)"
              by (rule subspace_topology_trans)
            ultimately show "top1_deformation_retract_of_on A (subspace_topology V ?TV A) {p}"
              using \<open>A = W 0\<close> by (by100 simp)
          qed
          show ?thesis
          proof -
            have hp_all_FV: "\<forall>A\<in>F_V. p \<in> A"
              unfolding F_V_def using hp_X' hp_W hn_pos by (by100 force)
            show ?thesis
              by (rule pasting_deformation_retract_to_subspace[OF hTV'_strict hfin' hX'_in hF_closed' hV_eq' hp_X' hp_all_FV hpairwise' hdr'])
          qed
        qed
        \<comment> \<open>Munkres: "using the induction hypothesis, \<pi>\_1(V,p) is a free group,
           with loops f\_2,...,f\_n as free generators."
           IH: apply less.IH with n-1 < n to X' = C(1) \<union> \<cdots> \<union> C(n-1).
           Re-index: C'(j) = C(j+1), g'(j) = g(j+1) for j < n-1.\<close>
        \<comment> \<open>Expert Step 6: IH on X' with re-indexing, then transfer via deformation retract.\<close>
        \<comment> \<open>Step 6a: Apply IH to X' = C(1) \<union> ... \<union> C(n-1) with n-1 circles.\<close>
        have hn1_lt: "n - 1 < n" using hn2 by (by100 simp)
        define C' where "C' j = C (j + 1)" for j
        define g' where "g' j = g (j + 1)" for j
        have hX'_free: "\<exists>(G2::int set) mul2 e2 invg2 (\<eta>2::nat \<Rightarrow> int) \<Phi>2.
            top1_is_free_group_full_on G2 mul2 e2 invg2 \<eta>2 {..<n-1}
          \<and> top1_group_iso_on G2 mul2
              (top1_fundamental_group_carrier X' (subspace_topology X TX X') p)
              (top1_fundamental_group_mul X' (subspace_topology X TX X') p) \<Phi>2
          \<and> (\<forall>j<n-1. \<Phi>2 (\<eta>2 j) = {l. top1_loop_equiv_on X' (subspace_topology X TX X') p
              (\<lambda>t. g' j (cos (2*pi*t), sin (2*pi*t))) l})"
        proof -
          let ?TX' = "subspace_topology X TX X'"
          have hTX_is: "is_topology_on X TX"
            using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
          have hX'_sub: "X' \<subseteq> X" unfolding X'_def using less.prems(4) by (by100 force)
          have hstrict': "is_topology_on_strict X' ?TX'"
            by (rule subspace_topology_is_strict[OF less.prems(1) hX'_sub])
          have hhaus': "is_hausdorff_on X' ?TX'"
            using conjunct2[OF conjunct2[OF Theorem_17_11]] less.prems(2) hX'_sub by (by100 blast)
          have hp': "p \<in> X'" unfolding X'_def using less.prems(4) hn2 by (by100 force)
          have hC_sub': "\<forall>j<n-1. C' j \<subseteq> X' \<and> p \<in> C' j"
            unfolding C'_def X'_def using less.prems(4) by (by100 force)
          have hC_union': "(\<Union>j\<in>{..<n-1}. C' j) = X'"
          proof -
            have "(\<Union>j\<in>{..<n-1}. C' j) = (\<Union>j\<in>{..<n-1}. C (j+1))" unfolding C'_def ..
            also have "\<dots> = X'"
            proof (rule set_eqI, rule iffI)
              fix x assume "x \<in> (\<Union>j\<in>{..<n-1}. C (j+1))"
              then obtain j where "j < n-1" "x \<in> C (j+1)" by (by100 blast)
              hence "j+1 \<in> {1..<n}" by (by100 simp)
              thus "x \<in> X'" unfolding X'_def using \<open>x \<in> C (j+1)\<close> by (by100 blast)
            next
              fix x assume "x \<in> X'"
              then obtain k where "k \<in> {1..<n}" "x \<in> C k" unfolding X'_def by (by100 blast)
              hence "k - 1 < n - 1"
              proof -
                from \<open>k \<in> {1..<n}\<close> have "1 \<le> k" "k < n" by (by100 simp)+
                thus ?thesis by (by100 simp)
              qed
              moreover have "C k = C ((k-1)+1)" using \<open>k \<in> {1..<n}\<close> by (by100 simp)
              ultimately show "x \<in> (\<Union>j\<in>{..<n-1}. C (j+1))"
                using \<open>x \<in> C k\<close> by (by100 force)
            qed
            finally show ?thesis .
          qed
          have hC_disj': "\<forall>i<n-1. \<forall>j<n-1. i \<noteq> j \<longrightarrow> C' i \<inter> C' j = {p}"
          proof (intro allI impI)
            fix i j :: nat assume "i < n-1" "j < n-1" "i \<noteq> j"
            hence "i+1 < n" "j+1 < n" "i+1 \<noteq> j+1" by (by100 simp)+
            thus "C' i \<inter> C' j = {p}" unfolding C'_def
              using less.prems(6) by (by100 blast)
          qed
          have hC_homeo': "\<forall>j<n-1. top1_homeomorphism_on top1_S1 top1_S1_topology
              (C' j) (subspace_topology X' ?TX' (C' j)) (g' j)"
          proof (intro allI impI)
            fix j assume "j < n - 1"
            hence hjn: "j + 1 < n" by (by100 simp)
            have hCj_sub: "C' j \<subseteq> X'" unfolding C'_def X'_def using hjn by (by100 force)
            have "subspace_topology X' ?TX' (C' j) = subspace_topology X TX (C' j)"
              using hCj_sub by (rule subspace_topology_trans)
            thus "top1_homeomorphism_on top1_S1 top1_S1_topology (C' j) (subspace_topology X' ?TX' (C' j)) (g' j)"
              unfolding C'_def g'_def using less.prems(7) hjn by (by100 simp)
          qed
          have hC_base': "\<forall>j<n-1. g' j (1, 0) = p"
          proof (intro allI impI)
            fix j assume "j < n - 1"
            thus "g' j (1, 0) = p" unfolding g'_def using less.prems(8) by (by100 force)
          qed
          \<comment> \<open>Coherent topology: Munkres note. Each C'(j) is closed in X', X' = \<Union>C'(j).
             (\<Rightarrow>) D closed in X' \<Rightarrow> C'(j) \<inter> D closed in subspace C'(j).
             (\<Leftarrow>) Each C'(j) \<inter> D closed in C'(j) (closed in X') \<Rightarrow> closed in X'.
             D = \<Union>(C'(j) \<inter> D) is finite union of closed, hence closed.\<close>
          have hCj_closed_in_X': "\<forall>j<n-1. closedin_on X' ?TX' (C' j)"
          proof (intro allI impI)
            fix j assume "j < n - 1"
            hence "j + 1 < n" by (by100 simp)
            have "closedin_on X TX (C (j+1))" using hC_closed \<open>j + 1 < n\<close> by (by100 blast)
            have "C' j \<subseteq> X'" unfolding C'_def X'_def using \<open>j + 1 < n\<close> by (by100 force)
            have "C' j = C (j+1) \<inter> X'" unfolding C'_def
            proof -
              have "C (j+1) \<inter> X' = C (j+1)"
                using \<open>C' j \<subseteq> X'\<close> unfolding C'_def by (by100 blast)
              thus "C (j + 1) = C (j + 1) \<inter> X'" by (by100 simp)
            qed
            thus "closedin_on X' ?TX' (C' j)"
              using iffD2[OF Theorem_17_2[OF hTX_is hX'_sub]] \<open>closedin_on X TX (C (j+1))\<close>
              unfolding C'_def by (by100 blast)
          qed
          have hC_closed': "\<forall>D\<subseteq>X'. closedin_on X' ?TX' D \<longleftrightarrow>
              (\<forall>j<n-1. closedin_on (C' j) (subspace_topology X' ?TX' (C' j)) (C' j \<inter> D))"
          proof (intro allI impI)
            fix D assume hD: "D \<subseteq> X'"
            show "closedin_on X' ?TX' D \<longleftrightarrow>
                (\<forall>j<n-1. closedin_on (C' j) (subspace_topology X' ?TX' (C' j)) (C' j \<inter> D))"
            proof
              assume hcl: "closedin_on X' ?TX' D"
              show "\<forall>j<n-1. closedin_on (C' j) (subspace_topology X' ?TX' (C' j)) (C' j \<inter> D)"
              proof (intro allI impI)
                fix j assume "j < n - 1"
                \<comment> \<open>C'(j) \<inter> D is closed in subspace C'(j) by Theorem\_17\_2 (\<Leftarrow>).\<close>
                have "closedin_on X' ?TX' (C' j)" using hCj_closed_in_X' \<open>j < n-1\<close> by (by100 blast)
                hence "closedin_on X' ?TX' (C' j \<inter> D)"
                  using closedin_inter2[OF subspace_topology_is_topology_on[OF hTX_is hX'_sub]] hcl
                  by (by100 blast)
                have "C' j \<subseteq> X'" unfolding C'_def X'_def using \<open>j < n - 1\<close> by (by100 force)
                have "\<exists>E. closedin_on X' ?TX' E \<and> C' j \<inter> D = E \<inter> C' j"
                proof (rule exI[of _ "C' j \<inter> D"])
                  show "closedin_on X' ?TX' (C' j \<inter> D) \<and> C' j \<inter> D = (C' j \<inter> D) \<inter> C' j"
                    using \<open>closedin_on X' ?TX' (C' j \<inter> D)\<close> by (by100 blast)
                qed
                thus "closedin_on (C' j) (subspace_topology X' ?TX' (C' j)) (C' j \<inter> D)"
                  using iffD2[OF Theorem_17_2[OF
                    subspace_topology_is_topology_on[OF hTX_is hX'_sub] \<open>C' j \<subseteq> X'\<close>]] by (by100 blast)
              qed
            next
              assume "\<forall>j<n-1. closedin_on (C' j) (subspace_topology X' ?TX' (C' j)) (C' j \<inter> D)"
              \<comment> \<open>Each C'(j) \<inter> D is closed in C'(j) (closed subspace of X'), hence in X'.\<close>
              hence "\<forall>j<n-1. closedin_on X' ?TX' (C' j \<inter> D)"
              proof (intro allI impI)
                fix j assume "j < n-1"
                   and hall: "\<forall>j<n-1. closedin_on (C' j) (subspace_topology X' ?TX' (C' j)) (C' j \<inter> D)"
                have "closedin_on X' ?TX' (C' j)" using hCj_closed_in_X' \<open>j < n-1\<close> by (by100 blast)
                from Theorem_17_3[OF subspace_topology_is_topology_on[OF hTX_is hX'_sub] this]
                show "closedin_on X' ?TX' (C' j \<inter> D)" using hall \<open>j < n-1\<close> by (by100 blast)
              qed
              \<comment> \<open>D = \<Union>(C'(j) \<inter> D) is a finite union of closed sets.\<close>
              moreover have "D = (\<Union>j\<in>{..<n-1}. C' j \<inter> D)"
                using hD hC_union' by (by100 blast)
              ultimately show "closedin_on X' ?TX' D"
              proof -
                assume hcl_all: "\<forall>j<n-1. closedin_on X' ?TX' (C' j \<inter> D)"
                   and hD_eq: "D = (\<Union>j\<in>{..<n-1}. C' j \<inter> D)"
                define S where "S = (\<lambda>j. C' j \<inter> D) ` {..<n-1}"
                have "finite S" unfolding S_def by (by100 simp)
                have "\<forall>A\<in>S. closedin_on X' ?TX' A" unfolding S_def using hcl_all by (by100 blast)
                hence "closedin_on X' ?TX' (\<Union>S)"
                  using closedin_on_finite_Union[OF subspace_topology_is_topology_on[OF hTX_is hX'_sub]
                        \<open>\<forall>A\<in>S. closedin_on X' ?TX' A\<close> \<open>finite S\<close>] by (by100 simp)
                moreover have "\<Union>S = D" unfolding S_def using hD_eq by (by100 blast)
                ultimately show ?thesis by (by100 simp)
              qed
            qed
          qed
          from less.IH[OF hn1_lt hstrict' hhaus' hp' hC_sub' hC_union' hC_disj' hC_homeo' hC_base' hC_closed']
          show ?thesis .
        qed
        \<comment> \<open>Step 6b: Transfer from X' to V via deformation retract + re-indexing.\<close>
        have hV_free: "\<exists>(G2::int set) mul2 e2 invg2 (\<eta>2::nat \<Rightarrow> int) \<Phi>2.
            top1_is_free_group_full_on G2 mul2 e2 invg2 \<eta>2 {1..<n}
          \<and> top1_group_iso_on G2 mul2
              (top1_fundamental_group_carrier V (subspace_topology X TX V) p)
              (top1_fundamental_group_mul V (subspace_topology X TX V) p) \<Phi>2
          \<and> (\<forall>j\<in>{1..<n}. \<Phi>2 (\<eta>2 j) = {l. top1_loop_equiv_on V (subspace_topology X TX V) p
              (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) l})"
        proof -
          \<comment> \<open>Step 1: Extract from hX'\_free.\<close>
          from hX'_free obtain G2 :: "int set" and mul2 e2 invg2
              and \<eta>2' :: "nat \<Rightarrow> int" and \<Phi>2' where
            hG2_all: "top1_is_free_group_full_on G2 mul2 e2 invg2 \<eta>2' {..<n-1}
            \<and> top1_group_iso_on G2 mul2
                (top1_fundamental_group_carrier X' (subspace_topology X TX X') p)
                (top1_fundamental_group_mul X' (subspace_topology X TX X') p) \<Phi>2'
            \<and> (\<forall>j<n-1. \<Phi>2' (\<eta>2' j) = {l. top1_loop_equiv_on X' (subspace_topology X TX X') p
                (\<lambda>t. g' j (cos (2*pi*t), sin (2*pi*t))) l})"
            by (by5000 auto)
          have hG2_free': "top1_is_free_group_full_on G2 mul2 e2 invg2 \<eta>2' {..<n-1}"
            using hG2_all by (by100 blast)
          have h\<Phi>2'_iso: "top1_group_iso_on G2 mul2
              (top1_fundamental_group_carrier X' (subspace_topology X TX X') p)
              (top1_fundamental_group_mul X' (subspace_topology X TX X') p) \<Phi>2'"
            using hG2_all by (by100 blast)
          have h\<Phi>2'_gen: "\<forall>j<n-1. \<Phi>2' (\<eta>2' j) = {l. top1_loop_equiv_on X' (subspace_topology X TX X') p
              (\<lambda>t. g' j (cos (2*pi*t), sin (2*pi*t))) l}"
            using hG2_all by (by100 blast)
          \<comment> \<open>Step 2: Explicit inclusion iso X' \<hookrightarrow> V via Theorem\_58\_3\_explicit.\<close>
          have hX'_sub_V: "X' \<subseteq> V" unfolding X'_def V_def by (by100 blast)
          have hX'_trans: "subspace_topology V (subspace_topology X TX V) X' = subspace_topology X TX X'"
            using hX'_sub_V by (rule subspace_topology_trans)
          have hp_X'_V: "p \<in> X'" unfolding X'_def using less.prems(4) hn2 by (by100 force)
          let ?incl_V = "top1_fundamental_group_induced_on X' (subspace_topology X TX X') p V (subspace_topology X TX V) p (\<lambda>x. x)"
          have hTX_is: "is_topology_on X TX"
            using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
          have hVsub_here: "V \<subseteq> X"
          proof -
            have "W 0 \<subseteq> X" using hW_sub_C less.prems(4) hn_pos by (by100 force)
            moreover have "\<forall>j\<in>{1..<n}. C j \<subseteq> X" using less.prems(4) by (by100 force)
            ultimately show ?thesis unfolding V_def by (by100 blast)
          qed
          have hTV_here: "is_topology_on V (subspace_topology X TX V)"
            by (rule subspace_topology_is_topology_on[OF hTX_is hVsub_here])
          have hX'_incl_iso_V: "top1_group_iso_on
              (top1_fundamental_group_carrier X' (subspace_topology X TX X') p)
              (top1_fundamental_group_mul X' (subspace_topology X TX X') p)
              (top1_fundamental_group_carrier V (subspace_topology X TX V) p)
              (top1_fundamental_group_mul V (subspace_topology X TX V) p) ?incl_V"
          proof -
            from Theorem_58_3_explicit[OF hV_retract hTV_here hp_X'_V]
            show ?thesis using hX'_trans by (by100 simp)
          qed
          \<comment> \<open>Step 3: Re-index. Define \<eta>2(k) = \<eta>2'(k-1) for k \<in> {1..<n}.\<close>
          define \<eta>2 where "\<eta>2 k = \<eta>2' (k - 1)" for k
          \<comment> \<open>Step 4: Compose \<Phi>2 = incl\_V \<circ> \<Phi>2'.\<close>
          define \<Phi>2 where "\<Phi>2 = ?incl_V \<circ> \<Phi>2'"
          \<comment> \<open>Step 5: \<Phi>2 is an iso (composition).\<close>
          have h\<Phi>2_iso: "top1_group_iso_on G2 mul2
              (top1_fundamental_group_carrier V (subspace_topology X TX V) p)
              (top1_fundamental_group_mul V (subspace_topology X TX V) p) \<Phi>2"
          proof -
            have hG2_grp: "top1_is_group_on G2 mul2 e2 invg2"
              using hG2_free' unfolding top1_is_free_group_full_on_def by (by100 blast)
            have hTX_is: "is_topology_on X TX"
              using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
            have hX'_sub: "X' \<subseteq> X" unfolding X'_def using less.prems(4) by (by100 force)
            have hX'_grp: "top1_is_group_on
                (top1_fundamental_group_carrier X' (subspace_topology X TX X') p)
                (top1_fundamental_group_mul X' (subspace_topology X TX X') p)
                (top1_fundamental_group_id X' (subspace_topology X TX X') p)
                (top1_fundamental_group_invg X' (subspace_topology X TX X') p)"
              by (rule top1_fundamental_group_is_group[OF subspace_topology_is_topology_on[OF hTX_is hX'_sub] hp_X'_V])
            have hV_grp: "top1_is_group_on
                (top1_fundamental_group_carrier V (subspace_topology X TX V) p)
                (top1_fundamental_group_mul V (subspace_topology X TX V) p)
                (top1_fundamental_group_id V (subspace_topology X TX V) p)
                (top1_fundamental_group_invg V (subspace_topology X TX V) p)"
            proof -
              have "p \<in> V" unfolding V_def using hp_W hn_pos by (by100 force)
              thus ?thesis by (rule top1_fundamental_group_is_group[OF hTV_here])
            qed
            show ?thesis unfolding \<Phi>2_def
              by (rule group_iso_on_compose[OF h\<Phi>2'_iso hX'_incl_iso_V hG2_grp hX'_grp hV_grp])
          qed
          \<comment> \<open>Step 6: Free group re-indexed from {..<n-1} to {1..<n}.\<close>
          have hG2_free: "top1_is_free_group_full_on G2 mul2 e2 invg2 \<eta>2 {1..<n}"
          proof -
            \<comment> \<open>The bijection \<phi>: k \<mapsto> k-1 maps {1..<n} to {..<n-1}.\<close>
            define \<phi> where "\<phi> k = k - (1::nat)" for k
            have h\<phi>_bij: "bij_betw \<phi> {1..<n} {..<n-1}"
              unfolding \<phi>_def bij_betw_def
            proof (intro conjI)
              show "inj_on (\<lambda>k::nat. k - 1) {1..<n}" unfolding inj_on_def
              proof (intro ballI impI)
                fix x y :: nat assume hx: "x \<in> {1..<n}" and hy: "y \<in> {1..<n}" and heq: "x - 1 = y - 1"
                from hx have "1 \<le> x" by (by100 simp)
                from hy have "1 \<le> y" by (by100 simp)
                from heq \<open>1 \<le> x\<close> \<open>1 \<le> y\<close> show "x = y" by (by100 linarith)
              qed
              show "(\<lambda>k. k - 1) ` {1..<n} = {..<n - 1}"
              proof (rule set_eqI, rule iffI)
                fix x assume "x \<in> (\<lambda>k. k - 1) ` {1..<n}"
                then obtain k where hk: "k \<in> {1..<n}" "x = k - 1" by (by100 blast)
                from hk have "1 \<le> k" "k < n" by (by100 simp)+
                thus "x \<in> {..<n - 1}" using \<open>x = k - 1\<close> by (by100 simp)
              next
                fix x assume "x \<in> {..<n - 1}"
                hence "x + 1 \<in> {1..<n}" by (by100 simp)
                moreover have "x = (x + 1) - 1" by (by100 simp)
                ultimately show "x \<in> (\<lambda>k. k - 1) ` {1..<n}" by (by100 blast)
              qed
            qed
            have h\<eta>2_eq: "\<forall>k\<in>{1..<n}. \<eta>2 k = \<eta>2' (\<phi> k)"
              unfolding \<eta>2_def \<phi>_def by (by100 simp)
            have h\<eta>2_img: "\<eta>2 ` {1..<n} = \<eta>2' ` {..<n-1}"
            proof -
              have "\<eta>2 ` {1..<n} = (\<eta>2' \<circ> \<phi>) ` {1..<n}"
              proof (rule image_cong)
                fix k assume "k \<in> {1..<n}"
                thus "\<eta>2 k = (\<eta>2' \<circ> \<phi>) k" using h\<eta>2_eq by (by100 simp)
              qed (by100 simp)
              also have "\<dots> = \<eta>2' ` (\<phi> ` {1..<n})" unfolding image_comp[symmetric] by (by100 simp)
              also have "\<phi> ` {1..<n} = {..<n-1}" using h\<phi>_bij unfolding bij_betw_def by (by100 blast)
              finally show ?thesis .
            qed
            \<comment> \<open>Transfer free\_group\_full from {..<n-1} to {1..<n}.\<close>
            \<comment> \<open>\<eta>2 = \<eta>2' \<circ> \<phi>. Apply free\_group\_full\_reindex.\<close>
            have h\<eta>2_is_comp: "\<eta>2 = \<eta>2' \<circ> \<phi>"
              unfolding \<eta>2_def \<phi>_def comp_def by (by100 simp)
            show ?thesis using free_group_full_reindex[OF hG2_free' h\<phi>_bij]
              h\<eta>2_is_comp by (by100 simp)
          qed
          \<comment> \<open>Step 7: Generator correspondence.\<close>
          have h\<Phi>2_gen: "\<forall>j\<in>{1..<n}. \<Phi>2 (\<eta>2 j) = {l. top1_loop_equiv_on V (subspace_topology X TX V) p
              (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) l}"
          proof (intro ballI)
            fix k assume hk: "k \<in> {1..<n}"
            hence hk_bound: "k - 1 < n - 1"
            proof -
              from hk have "1 \<le> k" "k < n" by (by100 simp)+
              thus ?thesis by (by100 simp)
            qed
            \<comment> \<open>\<Phi>2(\<eta>2 k) = incl\_V(\<Phi>2'(\<eta>2'(k-1))).\<close>
            have "\<Phi>2 (\<eta>2 k) = ?incl_V (\<Phi>2' (\<eta>2' (k - 1)))"
              unfolding \<Phi>2_def \<eta>2_def comp_def by (by100 simp)
            \<comment> \<open>\<Phi>2'(\<eta>2'(k-1)) = [g'(k-1)\<circ>std\_loop]\_{X'}.\<close>
            also have "\<Phi>2' (\<eta>2' (k - 1)) = {l. top1_loop_equiv_on X' (subspace_topology X TX X') p
                (\<lambda>t. g' (k-1) (cos (2*pi*t), sin (2*pi*t))) l}"
              using h\<Phi>2'_gen hk_bound by (by100 blast)
            \<comment> \<open>g'(k-1) = g(k) by definition.\<close>
            also have "g' (k - 1) = g k" unfolding g'_def using hk by (by100 simp)
            \<comment> \<open>incl\_V sends [f]\_{X'} to [f]\_V by subspace\_inclusion\_induced\_class.\<close>
            also have "?incl_V {l. top1_loop_equiv_on X' (subspace_topology X TX X') p
                (\<lambda>t. g k (cos (2*pi*t), sin (2*pi*t))) l}
              = {l. top1_loop_equiv_on V (subspace_topology X TX V) p
                (\<lambda>t. g k (cos (2*pi*t), sin (2*pi*t))) l}"
            proof -
              let ?loop_k = "\<lambda>t. g k (cos (2*pi*t), sin (2*pi*t))"
              have hloop_k: "top1_is_loop_on X' (subspace_topology X TX X') p ?loop_k"
              proof -
                have hkn: "k < n" using hk by (by100 simp)
                have hgk_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C k) (subspace_topology X TX (C k)) (g k)"
                  using less.prems(7) hkn by (by100 blast)
                have hgk_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
                    (C k) (subspace_topology X TX (C k)) (g k)"
                  using hgk_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
                have hstd: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0)
                    (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))"
                  by (rule standard_S1_loop_is_loop)
                have "top1_is_loop_on (C k) (subspace_topology X TX (C k)) (g k (1, 0))
                    ((g k) \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))))"
                  by (rule top1_continuous_map_loop_early[OF hgk_cont hstd])
                moreover have "(g k) \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) = ?loop_k"
                  unfolding comp_def by (by100 simp)
                moreover have "g k (1, 0) = p" using less.prems(8) hkn by (by100 blast)
                \<comment> \<open>Loop on C(k) \<subseteq> X'. Transfer via subspace.\<close>
                moreover have "C k \<subseteq> X'" unfolding X'_def using hk by (by100 force)
                moreover have "subspace_topology (C k) (subspace_topology X TX (C k)) (C k)
                    = subspace_topology X TX (C k)"
                proof (rule subspace_topology_self)
                  show "\<forall>U\<in>subspace_topology X TX (C k). U \<subseteq> C k"
                    unfolding subspace_topology_def by (by100 blast)
                qed
                ultimately have "top1_is_loop_on (C k) (subspace_topology X TX (C k)) p ?loop_k"
                  by (by100 simp)
                \<comment> \<open>Transfer loop from C(k) to X' \<supseteq> C(k).\<close>
                moreover have hCk_sub_X': "C k \<subseteq> X'" unfolding X'_def using hk by (by100 force)
                ultimately have hloop_Ck: "top1_is_loop_on (C k) (subspace_topology X TX (C k)) p ?loop_k"
                  by (by100 simp)
                \<comment> \<open>Expand codomain from C(k) to X'.\<close>
                thus ?thesis
                proof -
                  assume hloop: "top1_is_loop_on (C k) (subspace_topology X TX (C k)) p ?loop_k"
                  have hf_cont_Ck: "top1_continuous_map_on I_set I_top (C k) (subspace_topology X TX (C k)) ?loop_k"
                    using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  have hf0: "?loop_k 0 = p" using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  have hf1: "?loop_k 1 = p" using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  \<comment> \<open>subspace X TX C(k) = subspace X' TX' C(k) by transitivity.\<close>
                  have hCk_trans: "subspace_topology X TX (C k) = subspace_topology X' (subspace_topology X TX X') (C k)"
                    using subspace_topology_trans[OF hCk_sub_X'] by (by100 simp)
                  \<comment> \<open>f continuous I \<rightarrow> C(k) in subspace X' TX' C(k).\<close>
                  have hf_cont_Ck': "top1_continuous_map_on I_set I_top (C k) (subspace_topology X' (subspace_topology X TX X') (C k)) ?loop_k"
                    using hf_cont_Ck hCk_trans by (by100 simp)
                  \<comment> \<open>Expand codomain: C(k) \<subseteq> X', topology matches.\<close>
                  have hTI: "is_topology_on I_set I_top"
                    by (rule top1_unit_interval_topology_is_topology_on)
                  have hX'_sub_X: "X' \<subseteq> X" unfolding X'_def using less.prems(4) by (by100 force)
                  have hTX'_is: "is_topology_on X' (subspace_topology X TX X')"
                    by (rule subspace_topology_is_topology_on)
                       (rule less.prems(1)[unfolded is_topology_on_strict_def, THEN conjunct1],
                        rule hX'_sub_X)
                  have hTCk: "is_topology_on (C k) (subspace_topology X' (subspace_topology X TX X') (C k))"
                    by (rule subspace_topology_is_topology_on[OF hTX'_is hCk_sub_X'])
                  have hf_cont_X': "top1_continuous_map_on I_set I_top X' (subspace_topology X TX X') ?loop_k"
                    using Theorem_18_2(6)[OF hTI hTCk hTX'_is, rule_format]
                          hf_cont_Ck' hCk_sub_X' hCk_trans by (by100 blast)
                  show "top1_is_loop_on X' (subspace_topology X TX X') p ?loop_k"
                    unfolding top1_is_loop_on_def top1_is_path_on_def
                    using hf_cont_X' hf0 hf1 by (by100 blast)
                qed
              qed
              have hloop_k': "top1_is_loop_on X' (subspace_topology V (subspace_topology X TX V) X') p ?loop_k"
                using hloop_k hX'_trans by (by100 simp)
              show ?thesis
                using subspace_inclusion_induced_class[OF hTV_here hX'_sub_V hloop_k']
                      hX'_trans by (by100 simp)
            qed
            finally show "\<Phi>2 (\<eta>2 k) = {l. top1_loop_equiv_on V (subspace_topology X TX V) p
                (\<lambda>t. g k (cos (2*pi*t), sin (2*pi*t))) l}" .
          qed
          show ?thesis
            apply (rule exI[of _ G2], rule exI[of _ mul2], rule exI[of _ e2],
                   rule exI[of _ invg2], rule exI[of _ \<eta>2], rule exI[of _ \<Phi>2])
            using hG2_free h\<Phi>2_iso h\<Phi>2_gen by (by100 blast)
        qed
        \<comment> \<open>Step 10: Compose SvK + Theorem\_69\_2 + iso tracking.
           \<pi>_1(X) \<cong> FP(\<pi>_1(U), \<pi>_1(V)) \<cong> FP(Z, F_{n-1}) \<cong> F_n.\<close>
        \<comment> \<open>Munkres: "Our theorem now follows from Theorem 69.2."
           Step 7a: SvK gives \<pi>\_1(X) \<cong> FP = \<pi>\_1(U) * \<pi>\_1(V).\<close>
        have hp_UV_final: "p \<in> U \<inter> V"
        proof -
          have "p \<in> C 0" using less.prems(4) hn_pos by (by100 blast)
          hence "p \<in> U" unfolding U_def by (by100 blast)
          have "p \<noteq> q 0" using hq hn_pos by (by100 blast)
          hence "p \<in> W 0" using \<open>p \<in> C 0\<close> unfolding W_def by (by100 blast)
          hence "p \<in> V" unfolding V_def by (by100 blast)
          thus ?thesis using \<open>p \<in> U\<close> by (by100 blast)
        qed
        \<comment> \<open>Step 7b: Extract from hU\_free and hV\_free.\<close>
        from hU_free obtain G1 :: "int set" and mul1 e1 invg1 and \<eta>1 :: "nat \<Rightarrow> int" and \<Phi>1 where
          hG1_free: "top1_is_free_group_full_on G1 mul1 e1 invg1 \<eta>1 {0::nat}" and
          h\<Phi>1_iso: "top1_group_iso_on G1 mul1
              (top1_fundamental_group_carrier U (subspace_topology X TX U) p)
              (top1_fundamental_group_mul U (subspace_topology X TX U) p) \<Phi>1" and
          h\<Phi>1_gen: "\<Phi>1 (\<eta>1 0) = {l. top1_loop_equiv_on U (subspace_topology X TX U) p
              (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l}"
          by (by100 blast)
        from hV_free obtain G2 :: "int set" and mul2 e2 invg2 and \<eta>2 :: "nat \<Rightarrow> int" and \<Phi>2 where
          hG2_free: "top1_is_free_group_full_on G2 mul2 e2 invg2 \<eta>2 {1..<n}" and
          h\<Phi>2_iso: "top1_group_iso_on G2 mul2
              (top1_fundamental_group_carrier V (subspace_topology X TX V) p)
              (top1_fundamental_group_mul V (subspace_topology X TX V) p) \<Phi>2" and
          h\<Phi>2_gen: "\<forall>j\<in>{1..<n}. \<Phi>2 (\<eta>2 j) = {l. top1_loop_equiv_on V (subspace_topology X TX V) p
              (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) l}"
          by (by100 blast)
        \<comment> \<open>Step 7c: Apply Theorem 69.2.
           G1 free on {0}, G2 free on {1..<n}. {0} \<inter> {1..<n} = {}.
           Theorem\_69\_2: FP(G1,G2) is free on {0} \<union> {1..<n} = {..<n}.\<close>
        have hS_disj: "{0::nat} \<inter> {1..<n} = {}" by (by100 auto)
        have hS_union: "{0::nat} \<union> {1..<n} = {..<n}"
        proof -
          have "{..<n} = {0} \<union> {1..<n}" using hn_pos by (by100 auto)
          thus ?thesis by (by100 simp)
        qed
        \<comment> \<open>Step 7d: "Our theorem now follows from Theorem 69.2." (Munkres)
           Apply Theorem\_69\_2 to get FP = G1 * G2, free on {..<n} with gen tracking.
           Then use cached theorem for int carrier + free\_group\_hom\_exists for
           the generator-correct iso.\<close>
        \<comment> \<open>Step 7d-i: Apply Theorem\_69\_2.\<close>
        have hThm692: "\<exists>(FP :: (nat \<times> int) list set) mulFP eFP invgFP iotafam12 iotaS12.
          top1_is_free_product_on FP mulFP eFP invgFP
            (\<lambda>i::nat. if i = 0 then G1 else G2) (\<lambda>i. if i = 0 then mul1 else mul2)
            iotafam12 {0, 1} \<and>
          top1_is_free_group_full_on FP mulFP eFP invgFP iotaS12 ({0::nat} \<union> {1..<n}) \<and>
          (\<forall>s\<in>{0::nat}. iotaS12 s = iotafam12 0 (\<eta>1 s)) \<and>
          (\<forall>s\<in>{1..<n}. iotaS12 s = iotafam12 1 (\<eta>2 s))"
          using Theorem_69_2[OF hG1_free hG2_free hS_disj] by (by100 blast)
        from hThm692
        obtain FP :: "(nat \<times> int) list set" and mulFP eFP invgFP iotafam12
            and iotaS12 :: "nat \<Rightarrow> (nat \<times> int) list" where
          hFP_prod: "top1_is_free_product_on FP mulFP eFP invgFP
            (\<lambda>i::nat. if i = 0 then G1 else G2) (\<lambda>i. if i = 0 then mul1 else mul2)
            iotafam12 {0, 1}" and
          hFP_free: "top1_is_free_group_full_on FP mulFP eFP invgFP iotaS12 ({0::nat} \<union> {1..<n})" and
          hiotaS_G1: "\<forall>s\<in>{0::nat}. iotaS12 s = iotafam12 0 (\<eta>1 s)" and
          hiotaS_G2: "\<forall>s\<in>{1..<n}. iotaS12 s = iotafam12 1 (\<eta>2 s)"
          apply (rule exE)
          apply (by100 blast)
          done
        have hFP_free': "top1_is_free_group_full_on FP mulFP eFP invgFP iotaS12 {..<n}"
          using hFP_free hS_union by (by100 simp)
        \<comment> \<open>Step 7d-ii: Get int-typed carrier from cached theorem.\<close>
        have hwedge_X: "top1_is_wedge_of_circles_on X TX {..<n} p"
          unfolding top1_is_wedge_of_circles_on_def
        proof (intro conjI)
          show "is_topology_on_strict X TX" by (rule less.prems(1))
          show "is_hausdorff_on X TX" by (rule less.prems(2))
          show "p \<in> X" by (rule less.prems(3))
          show "\<exists>Ca. (\<forall>\<alpha>\<in>{..<n}. Ca \<alpha> \<subseteq> X \<and> p \<in> Ca \<alpha>
                 \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                          (Ca \<alpha>) (subspace_topology X TX (Ca \<alpha>)) h))
              \<and> (\<Union>\<alpha>\<in>{..<n}. Ca \<alpha>) = X
              \<and> (\<forall>\<alpha>\<in>{..<n}. \<forall>\<beta>\<in>{..<n}. \<alpha> \<noteq> \<beta> \<longrightarrow> Ca \<alpha> \<inter> Ca \<beta> = {p})
              \<and> (\<forall>D. D \<subseteq> X \<longrightarrow>
                   (closedin_on X TX D \<longleftrightarrow>
                    (\<forall>\<alpha>\<in>{..<n}. closedin_on (Ca \<alpha>) (subspace_topology X TX (Ca \<alpha>)) (Ca \<alpha> \<inter> D))))"
          proof (rule exI[of _ C])
            show "(\<forall>\<alpha>\<in>{..<n}. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
                   \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                            (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h))
                \<and> (\<Union>\<alpha>\<in>{..<n}. C \<alpha>) = X
                \<and> (\<forall>\<alpha>\<in>{..<n}. \<forall>\<beta>\<in>{..<n}. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p})
                \<and> (\<forall>D. D \<subseteq> X \<longrightarrow>
                     (closedin_on X TX D \<longleftrightarrow>
                      (\<forall>\<alpha>\<in>{..<n}. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D))))"
            proof (intro conjI)
              show "\<forall>\<alpha>\<in>{..<n}. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
                   \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                            (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h)"
                using less.prems(4,7) by (by100 blast)
              show "(\<Union>\<alpha>\<in>{..<n}. C \<alpha>) = X" by (rule less.prems(5))
              show "\<forall>\<alpha>\<in>{..<n}. \<forall>\<beta>\<in>{..<n}. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p}"
                using less.prems(6) by (by100 blast)
              show "\<forall>D. D \<subseteq> X \<longrightarrow>
                     (closedin_on X TX D \<longleftrightarrow>
                      (\<forall>\<alpha>\<in>{..<n}. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)))"
                using less.prems(9) by (by100 blast)
            qed
          qed
        qed
        from Theorem_71_1_wedge_of_circles_finite[OF hwedge_X]
        obtain G :: "int set" and mul_G e_G invg_G and \<iota>_G :: "nat \<Rightarrow> int" where
          hG_free: "top1_is_free_group_full_on G mul_G e_G invg_G \<iota>_G {..<n}" and
          hG_iso: "top1_groups_isomorphic_on G mul_G
              (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)"
          by (by100 blast)
        \<comment> \<open>Step 7d-iii: Define the loop classes (the target generator images).\<close>
        define loop_class where "loop_class j =
          {l. top1_loop_equiv_on X TX p (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) l}" for j
        \<comment> \<open>Step 7d-iv: Each loop\_class(j) is in \<pi>\_1(X,p).\<close>
        have hloop_in_pi1: "\<forall>j<n. loop_class j \<in>
            top1_fundamental_group_carrier X TX p"
        proof (intro allI impI)
          fix j assume "j < n"
          define fj where "fj = (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t)))"
          have "top1_is_loop_on X TX p fj"
          proof -
            \<comment> \<open>std\_loop is a loop on S1 at (1,0).\<close>
            have hstd: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0)
                (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))"
              by (rule standard_S1_loop_is_loop)
            \<comment> \<open>g(j) is continuous S1 \<rightarrow> C(j) (homeomorphism).\<close>
            have hgj_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
                (C j) (subspace_topology X TX (C j)) (g j)"
              using less.prems(7) \<open>j < n\<close> by (by100 blast)
            have hgj_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
                (C j) (subspace_topology X TX (C j)) (g j)"
              using hgj_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>Endpoints: g(j)(1,0) = p.\<close>
            have hgj_base: "g j (1, 0) = p"
              using less.prems(8) \<open>j < n\<close> by (by100 blast)
            \<comment> \<open>fj = g(j) \<circ> std\_loop is a loop on C(j) at p.\<close>
            \<comment> \<open>std\_loop as a path: continuous I \<rightarrow> S1.\<close>
            have hstd_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0)
                (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))"
              using hstd unfolding top1_is_loop_on_def by (by100 blast)
            have hstd_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology
                (\<lambda>s. (cos (2*pi*s), sin (2*pi*s)))"
              using hstd_path unfolding top1_is_path_on_def by (by100 blast)
            \<comment> \<open>Compose: fj = g(j) \<circ> std\_loop continuous I \<rightarrow> C(j).\<close>
            have hfj_cont_Cj: "top1_continuous_map_on I_set I_top
                (C j) (subspace_topology X TX (C j)) fj"
            proof (rule continuous_map_onI)
              show "\<forall>t \<in> I_set. fj t \<in> C j"
              proof
                fix t assume "t \<in> I_set"
                have "(cos (2*pi*t), sin (2*pi*t)) \<in> top1_S1"
                  unfolding top1_S1_def by (by100 simp)
                thus "fj t \<in> C j"
                  using continuous_map_maps_to[OF hgj_cont] unfolding fj_def by (by100 blast)
              qed
              show "\<forall>V \<in> subspace_topology X TX (C j). {t \<in> I_set. fj t \<in> V} \<in> I_top"
              proof
                fix V assume "V \<in> subspace_topology X TX (C j)"
                \<comment> \<open>Preimage under g(j).\<close>
                have hpre_g: "{s \<in> top1_S1. g j s \<in> V} \<in> top1_S1_topology"
                  using continuous_map_preimage_open[OF hgj_cont \<open>V \<in> subspace_topology X TX (C j)\<close>]
                  by (by100 blast)
                \<comment> \<open>Preimage under std\_loop.\<close>
                have "{t \<in> I_set. (cos (2*pi*t), sin (2*pi*t)) \<in> {s \<in> top1_S1. g j s \<in> V}} \<in> I_top"
                  using continuous_map_preimage_open[OF hstd_cont hpre_g] by (by100 blast)
                moreover have "{t \<in> I_set. fj t \<in> V}
                    = {t \<in> I_set. (cos (2*pi*t), sin (2*pi*t)) \<in> {s \<in> top1_S1. g j s \<in> V}}"
                proof (rule set_eqI, rule iffI)
                  fix t assume "t \<in> {t \<in> I_set. fj t \<in> V}"
                  hence "t \<in> I_set" "fj t \<in> V" by (by100 blast)+
                  have "(cos (2*pi*t), sin (2*pi*t)) \<in> top1_S1"
                    unfolding top1_S1_def by (by100 simp)
                  thus "t \<in> {t \<in> I_set. (cos (2*pi*t), sin (2*pi*t)) \<in> {s \<in> top1_S1. g j s \<in> V}}"
                    using \<open>t \<in> I_set\<close> \<open>fj t \<in> V\<close> unfolding fj_def by (by100 simp)
                next
                  fix t assume "t \<in> {t \<in> I_set. (cos (2*pi*t), sin (2*pi*t)) \<in> {s \<in> top1_S1. g j s \<in> V}}"
                  thus "t \<in> {t \<in> I_set. fj t \<in> V}" unfolding fj_def by (by100 simp)
                qed
                ultimately show "{t \<in> I_set. fj t \<in> V} \<in> I_top" by (by100 simp)
              qed
            qed
            have hfj_loop_Cj: "top1_is_loop_on (C j) (subspace_topology X TX (C j)) p fj"
              unfolding top1_is_loop_on_def top1_is_path_on_def
              using hfj_cont_Cj hgj_base unfolding fj_def by (by100 simp)
            \<comment> \<open>Transfer from C(j) to X via Theorem\_18\_2(6) (expand range).\<close>
            have hCj_sub: "C j \<subseteq> X" using less.prems(4) \<open>j < n\<close> by (by100 blast)
            \<comment> \<open>Transfer loop from C(j) to X: expand range via Theorem\_18\_2(6).\<close>
            have hfj_cont_X: "top1_continuous_map_on I_set I_top X TX fj"
            proof -
              have hfj_cont_Cj': "top1_continuous_map_on I_set I_top
                  (C j) (subspace_topology X TX (C j)) fj"
                using hfj_loop_Cj unfolding top1_is_loop_on_def top1_is_path_on_def
                by (by100 blast)
              have hI_top: "is_topology_on I_set I_top"
                using top1_unit_interval_topology_is_topology_on by (by100 blast)
              have hTX_loc: "is_topology_on X TX"
                using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
              have hTCj: "is_topology_on (C j) (subspace_topology X TX (C j))"
                using subspace_topology_is_topology_on[OF hTX_loc hCj_sub] by (by100 blast)
              show ?thesis
                using Theorem_18_2(6)[OF hI_top hTCj hTX_loc] hfj_cont_Cj' hCj_sub
                by (by100 blast)
            qed
            have hfj_0: "fj 0 = p" unfolding fj_def using hgj_base by (by100 simp)
            have hfj_1: "fj 1 = p" unfolding fj_def using hgj_base by (by100 simp)
            show ?thesis
              unfolding top1_is_loop_on_def top1_is_path_on_def
              using hfj_cont_X hfj_0 hfj_1 by (by100 blast)
          qed
          moreover have "loop_class j = {l. top1_loop_equiv_on X TX p fj l}"
            unfolding loop_class_def fj_def by (by100 simp)
          ultimately show "loop_class j \<in> top1_fundamental_group_carrier X TX p"
            unfolding top1_fundamental_group_carrier_def by (by100 blast)
        qed
        \<comment> \<open>Step 7d-v: \<pi>\_1(X,p) is a group.\<close>
        have hTX: "is_topology_on X TX"
          using less.prems(1) unfolding is_topology_on_strict_def by (by100 blast)
        have hpi1_grp: "top1_is_group_on
            (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
            (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)"
          using top1_fundamental_group_is_group[OF hTX less.prems(3)] by (by100 blast)
        \<comment> \<open>Step 7d-vi: By free\_group\_hom\_exists, construct hom \<Phi>: G \<rightarrow> \<pi>\_1(X,p)
           that maps \<iota>\_G(j) to loop\_class(j).\<close>
        have hloop_in: "\<forall>s\<in>{..<n}. loop_class s \<in> top1_fundamental_group_carrier X TX p"
          using hloop_in_pi1 by (by100 blast)
        from free_group_hom_exists[OF hG_free hpi1_grp hloop_in]
        obtain \<Phi> where h\<Phi>_hom: "top1_group_hom_on G mul_G
            (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p) \<Phi>"
          and h\<Phi>_gen: "\<forall>j\<in>{..<n}. \<Phi> (\<iota>_G j) = loop_class j"
          by (by100 blast)
        \<comment> \<open>Step 7d-vii: \<Phi> is bijective (hence iso).
           Both G and \<pi>\_1(X,p) are free on {..<n}. A hom between free groups of same
           rank that maps generators to generators is an iso.
           Proof: construct inverse hom \<Psi>: \<pi>\_1(X,p) \<rightarrow> G via free\_group\_hom\_exists
           (using the FP-based freeness of \<pi>\_1(X,p)). Then \<Psi> \<circ> \<Phi> = id on generators
           \<Rightarrow> \<Psi> \<circ> \<Phi> = id (by uniqueness). Similarly \<Phi> \<circ> \<Psi> = id. Hence \<Phi> bijective.\<close>
        \<comment> \<open>Step 7d-vii: Construct free product of \<pi>\_1(U) and \<pi>\_1(V), apply parameterized SvK,
           compose with Theorem\_69\_2 to show \<pi>\_1(X) is free on {..<n} with loop\_class generators.
           Then construct inverse of \<Phi> and prove bijectivity.\<close>
        \<comment> \<open>Step 7d-vii: \<Phi> bijective. Munkres: "Our theorem follows from Theorem 69.2."
           Key insight: apply Theorem\_69\_2 directly to \<pi>\_1(U) and \<pi>\_1(V) (both have type
           'a set set, so the type constraint is satisfied). This avoids the int vs 'a set
           type barrier. Then use free\_group\_invariant\_under\_iso to transfer freeness to
           \<pi>\_1(X), and free\_group\_hom\_generators\_iso to show \<Phi> bijective.\<close>
        \<comment> \<open>Step A: \<pi>\_1(U) is free on {0} with loop\_class(0) as generator.\<close>
        have hTU_top: "is_topology_on U (subspace_topology X TX U)"
          using subspace_topology_is_topology_on[OF hTX] hU_open unfolding openin_on_def
          by (by100 blast)
        have hTV_top: "is_topology_on V (subspace_topology X TX V)"
          using subspace_topology_is_topology_on[OF hTX] hV_open unfolding openin_on_def
          by (by100 blast)
        have hp_U: "p \<in> U" using hp_UV_final by (by100 blast)
        have hp_V: "p \<in> V" using hp_UV_final by (by100 blast)
        have hpi1U_grp: "top1_is_group_on
            (top1_fundamental_group_carrier U (subspace_topology X TX U) p)
            (top1_fundamental_group_mul U (subspace_topology X TX U) p)
            (top1_fundamental_group_id U (subspace_topology X TX U) p)
            (top1_fundamental_group_invg U (subspace_topology X TX U) p)"
          using top1_fundamental_group_is_group[OF hTU_top hp_U] by (by100 blast)
        have hpi1V_grp: "top1_is_group_on
            (top1_fundamental_group_carrier V (subspace_topology X TX V) p)
            (top1_fundamental_group_mul V (subspace_topology X TX V) p)
            (top1_fundamental_group_id V (subspace_topology X TX V) p)
            (top1_fundamental_group_invg V (subspace_topology X TX V) p)"
          using top1_fundamental_group_is_group[OF hTV_top hp_V] by (by100 blast)
        have hpi1U_free: "\<exists>\<iota>U'. top1_is_free_group_full_on
            (top1_fundamental_group_carrier U (subspace_topology X TX U) p)
            (top1_fundamental_group_mul U (subspace_topology X TX U) p)
            (top1_fundamental_group_id U (subspace_topology X TX U) p)
            (top1_fundamental_group_invg U (subspace_topology X TX U) p)
            \<iota>U' {0::nat}
          \<and> \<iota>U' 0 = \<Phi>1 (\<eta>1 0)"
        proof -
          from free_group_invariant_under_iso[OF hG1_free h\<Phi>1_iso hpi1U_grp]
          show ?thesis by (by100 blast)
        qed
        \<comment> \<open>Step B: \<pi>\_1(V) is free on {1..<n}.\<close>
        have hpi1V_free: "\<exists>\<iota>V'. top1_is_free_group_full_on
            (top1_fundamental_group_carrier V (subspace_topology X TX V) p)
            (top1_fundamental_group_mul V (subspace_topology X TX V) p)
            (top1_fundamental_group_id V (subspace_topology X TX V) p)
            (top1_fundamental_group_invg V (subspace_topology X TX V) p)
            \<iota>V' {1..<n}
          \<and> (\<forall>k\<in>{1..<n}. \<iota>V' k = \<Phi>2 (\<eta>2 k))"
        proof -
          from free_group_invariant_under_iso[OF hG2_free h\<Phi>2_iso hpi1V_grp]
          show ?thesis by (by100 blast)
        qed
        \<comment> \<open>Step C: Apply Theorem\_69\_2 to \<pi>\_1(U) and \<pi>\_1(V) (SAME type 'a set set!).\<close>
        \<comment> \<open>This gives FP\_UV free on {..<n} and FP\_UV = free product of \<pi>\_1(U), \<pi>\_1(V).\<close>
        \<comment> \<open>Step D: Apply SvK: \<pi>\_1(X) \<cong> FP\_UV.\<close>
        \<comment> \<open>Step E: free\_group\_invariant\_under\_iso: \<pi>\_1(X) free on {..<n}.\<close>
        \<comment> \<open>Step F: Generator tracking gives \<iota>\_pi1(j) = loop\_class(j).\<close>
        \<comment> \<open>Step G: free\_group\_hom\_generators\_iso: \<Phi> bijective.\<close>
        have hpi1X_free: "\<exists>\<iota>X'. top1_is_free_group_full_on
            (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
            (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
            \<iota>X' {..<n} \<and> (\<forall>j\<in>{..<n}. \<iota>X' j = loop_class j)"
        proof -
          let ?\<pi>U = "top1_fundamental_group_carrier U (subspace_topology X TX U) p"
          let ?mU = "top1_fundamental_group_mul U (subspace_topology X TX U) p"
          let ?eU = "top1_fundamental_group_id U (subspace_topology X TX U) p"
          let ?iU = "top1_fundamental_group_invg U (subspace_topology X TX U) p"
          let ?\<pi>V = "top1_fundamental_group_carrier V (subspace_topology X TX V) p"
          let ?mV = "top1_fundamental_group_mul V (subspace_topology X TX V) p"
          let ?eV = "top1_fundamental_group_id V (subspace_topology X TX V) p"
          let ?iV = "top1_fundamental_group_invg V (subspace_topology X TX V) p"
          \<comment> \<open>Step C: Extract \<pi>\_1(U) and \<pi>\_1(V) as full free groups with gen tracking.\<close>
          from hpi1U_free obtain \<iota>U' where
            hU'_free: "top1_is_free_group_full_on ?\<pi>U ?mU ?eU ?iU \<iota>U' {0::nat}"
            and hU'_gen: "\<iota>U' 0 = \<Phi>1 (\<eta>1 0)"
            by (by100 blast)
          from hpi1V_free obtain \<iota>V' where
            hV'_free: "top1_is_free_group_full_on ?\<pi>V ?mV ?eV ?iV \<iota>V' {1..<n}"
            and hV'_gen: "\<forall>k\<in>{1..<n}. \<iota>V' k = \<Phi>2 (\<eta>2 k)"
            by (by100 blast)
          \<comment> \<open>Step D: Apply svk\_free\_product\_free\_with\_generators (the newly proved lemma).
             This gives \<pi>\_1(X) free on {0}\<union>{1..<n} with SPECIFIC generators
             that are inclusion-induced images of \<iota>U' and \<iota>V'.\<close>
          note hsvk_gen_result = svk_free_product_free_with_generators[OF less.prems(1) hU_open hV_open hUV_cover hUV_sc
                hU_pc hV_pc hp_UV_final hU'_free hV'_free hS_disj]
          define \<iota>X_raw where "\<iota>X_raw \<equiv> SOME \<iota>X. top1_is_free_group_full_on
              (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
              (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
              \<iota>X ({0::nat} \<union> {1..<n})
            \<and> (\<forall>s\<in>{0::nat}. \<iota>X s =
              top1_fundamental_group_induced_on U (subspace_topology X TX U) p X TX p (\<lambda>x. x) (\<iota>U' s))
            \<and> (\<forall>s\<in>{1..<n}. \<iota>X s =
              top1_fundamental_group_induced_on V (subspace_topology X TX V) p X TX p (\<lambda>x. x) (\<iota>V' s))"
          have hsvk_gen_props: "top1_is_free_group_full_on
              (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
              (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
              \<iota>X_raw ({0::nat} \<union> {1..<n})
            \<and> (\<forall>s\<in>{0::nat}. \<iota>X_raw s =
              top1_fundamental_group_induced_on U (subspace_topology X TX U) p X TX p (\<lambda>x. x) (\<iota>U' s))
            \<and> (\<forall>s\<in>{1..<n}. \<iota>X_raw s =
              top1_fundamental_group_induced_on V (subspace_topology X TX V) p X TX p (\<lambda>x. x) (\<iota>V' s))"
            unfolding \<iota>X_raw_def using someI_ex[OF hsvk_gen_result] by (by5000 blast)
          have hpi1X_raw: "top1_is_free_group_full_on
              (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
              (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
              \<iota>X_raw ({0::nat} \<union> {1..<n})"
            using hsvk_gen_props by (by100 blast)
          have hgenU_track: "\<forall>s\<in>{0::nat}. \<iota>X_raw s =
              top1_fundamental_group_induced_on U (subspace_topology X TX U) p X TX p (\<lambda>x. x) (\<iota>U' s)"
            using hsvk_gen_props by (by100 blast)
          have hgenV_track: "\<forall>s\<in>{1..<n}. \<iota>X_raw s =
              top1_fundamental_group_induced_on V (subspace_topology X TX V) p X TX p (\<lambda>x. x) (\<iota>V' s)"
            using hsvk_gen_props by (by100 blast)
          have hpi1X_raw': "top1_is_free_group_full_on
              (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
              (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
              \<iota>X_raw {..<n}"
            using hpi1X_raw hS_union by (by100 simp)
          \<comment> \<open>Generator tracking: connect \<iota>X\_raw(j) to loop\_class(j).
             For j=0: \<iota>X\_raw(0) = j\_U*(\<iota>U'(0)) = j\_U*(\<Phi>1(\<eta>1(0))) = j\_U*([g0\<circ>std\_loop]\_U) = loop\_class(0).
             For j\<in>{1..<n}: \<iota>X\_raw(j) = j\_V*(\<iota>V'(j)) = j\_V*(\<Phi>2(\<eta>2(j))) = j\_V*([gj\<circ>std\_loop]\_V) = loop\_class(j).
             The last step uses subspace\_inclusion\_induced\_class.\<close>
          have hgen_corr: "\<forall>j\<in>{..<n}. \<iota>X_raw j = loop_class j"
          proof
            fix j assume "j \<in> {..<n}"
            show "\<iota>X_raw j = loop_class j"
            proof (cases "j = 0")
              case True
              \<comment> \<open>\<iota>X\_raw(0) = j\_U*(\<iota>U'(0)) = j\_U*(\<Phi>1(\<eta>1(0))) = j\_U*([g0\<circ>std\_loop]\_U) = loop\_class(0).\<close>
              have "\<iota>X_raw 0 = top1_fundamental_group_induced_on U (subspace_topology X TX U) p X TX p (\<lambda>x. x) (\<iota>U' 0)"
                using hgenU_track by (by100 blast)
              also have "\<iota>U' 0 = \<Phi>1 (\<eta>1 0)" using hU'_gen by (by100 blast)
              also have "\<Phi>1 (\<eta>1 0) = {l. top1_loop_equiv_on U (subspace_topology X TX U) p
                  (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l}" using h\<Phi>1_gen by (by100 blast)
              finally have h0_eq: "\<iota>X_raw 0 = top1_fundamental_group_induced_on U (subspace_topology X TX U) p X TX p (\<lambda>x. x)
                  {l. top1_loop_equiv_on U (subspace_topology X TX U) p
                      (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l}" .
              \<comment> \<open>Inclusion sends class: j\_U*([f]\_U) = [f]\_X.\<close>
              have hU_sub: "U \<subseteq> X" using hU_open unfolding openin_on_def by (by100 blast)
              have hloop0_U: "top1_is_loop_on U (subspace_topology X TX U) p
                  (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t)))"
              proof -
                have hg0_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C 0) (subspace_topology X TX (C 0)) (g 0)"
                  using less.prems(7) hn_pos by (by100 blast)
                have hg0_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
                    (C 0) (subspace_topology X TX (C 0)) (g 0)"
                  using hg0_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
                have hloop_C0: "top1_is_loop_on (C 0) (subspace_topology X TX (C 0)) p
                    (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t)))"
                proof -
                  have hloop_raw: "top1_is_loop_on (C 0) (subspace_topology X TX (C 0)) (g 0 (1, 0))
                      ((g 0) \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))))"
                    by (rule top1_continuous_map_loop_early[OF hg0_cont standard_S1_loop_is_loop])
                  have heq: "(g 0) \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) =
                      (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t)))"
                    unfolding comp_def by (by100 simp)
                  have "g 0 (1, 0) = p" using less.prems(8) hn_pos by (by100 blast)
                  thus ?thesis using hloop_raw heq by (by100 simp)
                qed
                \<comment> \<open>C(0) \<subseteq> U, expand loop from C(0) to U.\<close>
                have hC0_sub_U: "C 0 \<subseteq> U" unfolding U_def by (by100 blast)
                have hC0_trans: "subspace_topology U (subspace_topology X TX U) (C 0) =
                    subspace_topology X TX (C 0)"
                  using subspace_topology_trans[OF hC0_sub_U] by (by100 simp)
                have hloop_C0_U: "top1_is_loop_on (C 0) (subspace_topology U (subspace_topology X TX U) (C 0)) p
                    (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t)))"
                  using hloop_C0 hC0_trans by (by100 simp)
                have hloop_cont: "top1_continuous_map_on I_set I_top
                    (C 0) (subspace_topology U (subspace_topology X TX U) (C 0))
                    (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t)))"
                  using hloop_C0_U unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                have hI_top: "is_topology_on I_set I_top"
                  using top1_unit_interval_topology_is_topology_on by (by100 blast)
                have hTC0: "is_topology_on (C 0) (subspace_topology U (subspace_topology X TX U) (C 0))"
                  using subspace_topology_is_topology_on[OF hTU_top hC0_sub_U] by (by100 blast)
                have hloop_cont_U: "top1_continuous_map_on I_set I_top U (subspace_topology X TX U)
                    (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t)))"
                  using Theorem_18_2(6)[OF hI_top hTC0 hTU_top, rule_format, of
                      "(\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t)))"]
                  hloop_cont hC0_sub_U hC0_trans
                  by (by5000 blast)
                have "(\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) 0 = p"
                  using less.prems(8) hn_pos by (by100 force)
                have "(\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) 1 = p"
                  using less.prems(8) hn_pos by (by100 force)
                show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
                  using hloop_cont_U \<open>(\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) 0 = p\<close>
                  \<open>(\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) 1 = p\<close> by (by100 blast)
              qed
              have "top1_fundamental_group_induced_on U (subspace_topology X TX U) p X TX p (\<lambda>x. x)
                  {l. top1_loop_equiv_on U (subspace_topology X TX U) p
                      (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l}
                = {l. top1_loop_equiv_on X TX p (\<lambda>t. g 0 (cos (2*pi*t), sin (2*pi*t))) l}"
                using subspace_inclusion_induced_class[OF hTX hU_sub hloop0_U] by (by100 blast)
              thus "\<iota>X_raw j = loop_class j"
                using h0_eq True unfolding loop_class_def by (by100 simp)
            next
              case False
              hence "j \<in> {1..<n}" using \<open>j \<in> {..<n}\<close> by (by100 force)
              \<comment> \<open>\<iota>X\_raw(j) = j\_V*(\<iota>V'(j)) = j\_V*(\<Phi>2(\<eta>2(j))) = j\_V*([gj\<circ>std\_loop]\_V) = loop\_class(j).\<close>
              have "\<iota>X_raw j = top1_fundamental_group_induced_on V (subspace_topology X TX V) p X TX p (\<lambda>x. x) (\<iota>V' j)"
                using hgenV_track \<open>j \<in> {1..<n}\<close> by (by100 blast)
              also have "\<iota>V' j = \<Phi>2 (\<eta>2 j)" using hV'_gen \<open>j \<in> {1..<n}\<close> by (by100 blast)
              also have "\<Phi>2 (\<eta>2 j) = {l. top1_loop_equiv_on V (subspace_topology X TX V) p
                  (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) l}" using h\<Phi>2_gen \<open>j \<in> {1..<n}\<close> by (by100 blast)
              finally have hj_eq: "\<iota>X_raw j = top1_fundamental_group_induced_on V (subspace_topology X TX V) p X TX p (\<lambda>x. x)
                  {l. top1_loop_equiv_on V (subspace_topology X TX V) p
                      (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) l}" .
              have hV_sub: "V \<subseteq> X" using hV_open unfolding openin_on_def by (by100 blast)
              have hloopj_V: "top1_is_loop_on V (subspace_topology X TX V) p
                  (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t)))"
              proof -
                have "j < n" using \<open>j \<in> {1..<n}\<close> by (by100 force)
                have hgj_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology
                    (C j) (subspace_topology X TX (C j)) (g j)"
                  using less.prems(7) \<open>j < n\<close> by (by100 blast)
                have hgj_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
                    (C j) (subspace_topology X TX (C j)) (g j)"
                  using hgj_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
                have hloop_Cj: "top1_is_loop_on (C j) (subspace_topology X TX (C j)) p
                    (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t)))"
                proof -
                  have hloop_raw: "top1_is_loop_on (C j) (subspace_topology X TX (C j)) (g j (1, 0))
                      ((g j) \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))))"
                    by (rule top1_continuous_map_loop_early[OF hgj_cont standard_S1_loop_is_loop])
                  have heq: "(g j) \<circ> (\<lambda>s. (cos (2*pi*s), sin (2*pi*s))) =
                      (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t)))"
                    unfolding comp_def by (by100 simp)
                  have "g j (1, 0) = p" using less.prems(8) \<open>j < n\<close> by (by100 blast)
                  thus ?thesis using hloop_raw heq by (by100 simp)
                qed
                \<comment> \<open>C(j) \<subseteq> V for j \<in> {1..<n}, expand loop from C(j) to V.\<close>
                have hCj_sub_V: "C j \<subseteq> V" unfolding V_def using \<open>j \<in> {1..<n}\<close> by (by100 blast)
                have hCj_trans: "subspace_topology V (subspace_topology X TX V) (C j) =
                    subspace_topology X TX (C j)"
                  using subspace_topology_trans[OF hCj_sub_V] by (by100 simp)
                have hloop_Cj_V: "top1_is_loop_on (C j) (subspace_topology V (subspace_topology X TX V) (C j)) p
                    (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t)))"
                  using hloop_Cj hCj_trans by (by100 simp)
                have hloop_cont: "top1_continuous_map_on I_set I_top
                    (C j) (subspace_topology V (subspace_topology X TX V) (C j))
                    (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t)))"
                  using hloop_Cj_V unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                have hI_top: "is_topology_on I_set I_top"
                  using top1_unit_interval_topology_is_topology_on by (by100 blast)
                have hTCj: "is_topology_on (C j) (subspace_topology V (subspace_topology X TX V) (C j))"
                  using subspace_topology_is_topology_on[OF hTV_top hCj_sub_V] by (by100 blast)
                have hloop_cont_V: "top1_continuous_map_on I_set I_top V (subspace_topology X TX V)
                    (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t)))"
                  using Theorem_18_2(6)[OF hI_top hTCj hTV_top, rule_format, of
                      "(\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t)))"]
                  hloop_cont hCj_sub_V hCj_trans
                  by (by5000 blast)
                have "(\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) 0 = p"
                  using less.prems(8) \<open>j < n\<close> by (by100 force)
                have "(\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) 1 = p"
                  using less.prems(8) \<open>j < n\<close> by (by100 force)
                show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
                  using hloop_cont_V \<open>(\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) 0 = p\<close>
                  \<open>(\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) 1 = p\<close> by (by100 blast)
              qed
              have "top1_fundamental_group_induced_on V (subspace_topology X TX V) p X TX p (\<lambda>x. x)
                  {l. top1_loop_equiv_on V (subspace_topology X TX V) p
                      (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) l}
                = {l. top1_loop_equiv_on X TX p (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) l}"
                using subspace_inclusion_induced_class[OF hTX hV_sub hloopj_V] by (by100 blast)
              thus "\<iota>X_raw j = loop_class j"
                using hj_eq unfolding loop_class_def by (by100 simp)
            qed
          qed
          show ?thesis using hpi1X_raw' hgen_corr by (by100 blast)
        qed
        \<comment> \<open>\<Phi> bijective via free\_group\_hom\_generators\_iso (book-faithful, no Hopfian).
           hpi1X\_free gives \<pi>\_1(X) free on {..<n} with gen = loop\_class.
           \<Phi> maps \<iota>\_G(j) to loop\_class(j) = \<iota>X'(j). So \<Phi> is bijective.\<close>
        from hpi1X_free obtain \<iota>X' where
          hpi1X_free': "top1_is_free_group_full_on
            (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p)
            (top1_fundamental_group_id X TX p) (top1_fundamental_group_invg X TX p)
            \<iota>X' {..<n}"
          and hpi1X_gen': "\<forall>j\<in>{..<n}. \<iota>X' j = loop_class j"
          by (by100 blast)
        have hgen_eq: "\<forall>j\<in>{..<n}. \<Phi> (\<iota>_G j) = \<iota>X' j"
          using h\<Phi>_gen hpi1X_gen' by (by100 simp)
        have h\<Phi>_bij: "bij_betw \<Phi> G (top1_fundamental_group_carrier X TX p)"
          using free_group_hom_generators_iso[OF hG_free hpi1X_free' h\<Phi>_hom hgen_eq]
          by (by100 blast)
        have h\<Phi>_iso: "top1_group_iso_on G mul_G
            (top1_fundamental_group_carrier X TX p) (top1_fundamental_group_mul X TX p) \<Phi>"
          unfolding top1_group_iso_on_def using h\<Phi>_hom h\<Phi>_bij by (by100 blast)
        have h\<Phi>_gen': "\<forall>j<n. \<Phi> (\<iota>_G j) = {l. top1_loop_equiv_on X TX p
            (\<lambda>t. g j (cos (2*pi*t), sin (2*pi*t))) l}"
          using h\<Phi>_gen unfolding loop_class_def by (by100 blast)
        show ?thesis
          apply (rule exI[of _ G], rule exI[of _ mul_G], rule exI[of _ e_G],
                 rule exI[of _ invg_G], rule exI[of _ \<iota>_G], rule exI[of _ \<Phi>])
          using hG_free h\<Phi>_iso h\<Phi>_gen' by (by100 blast)
      qed
    qed
  qed

end
