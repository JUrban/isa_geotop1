theory AlgTopCached7
  imports "AlgTopCached6.AlgTopCached6"
begin

(* Cached sorry-free §84 infrastructure + homotopy helpers.
   Extracted from AlgTop.thy for faster builds. *)


(* word_product_foldr_class: needed by Lemma_84_6 *)
text \<open>Helper: word\_product in \<pi>_1 = class of foldr path product.
  By induction: each \<pi>_1 multiplication step corresponds to a path\_product step.\<close>
lemma word_product_foldr_class:
  assumes hTA: "is_topology_on Y TY"
    and hloops: "\<forall>k<length ws. top1_is_loop_on Y TY y0 (fs k)"
    and hmatch: "\<forall>k<length ws.
        {g. top1_loop_equiv_on Y TY y0 (fs k) g}
      = (if snd (ws!k) then fst (ws!k)
         else top1_fundamental_group_invg Y TY y0 (fst (ws!k)))"
  shows "top1_group_word_product
      (top1_fundamental_group_mul Y TY y0)
      (top1_fundamental_group_id Y TY y0)
      (top1_fundamental_group_invg Y TY y0)
      ws
    = {g. top1_loop_equiv_on Y TY y0
        (foldr top1_path_product (map fs [0..<length ws]) (top1_constant_path y0)) g}"
  using assms
proof (induction ws arbitrary: fs)
  case Nil
  show ?case unfolding top1_fundamental_group_id_def by (by100 simp)
next
  case (Cons w rest)
  obtain x b where hw: "w = (x, b)" by (cases w) (by100 blast)
  \<comment> \<open>Shifted fs for the tail.\<close>
  define fs' where "fs' k = fs (Suc k)" for k
  have hloops': "\<forall>k<length rest. top1_is_loop_on Y TY y0 (fs' k)"
    using Cons(3) unfolding fs'_def by (by100 force)
  have hmatch': "\<forall>k<length rest.
      {g. top1_loop_equiv_on Y TY y0 (fs' k) g}
    = (if snd (rest!k) then fst (rest!k)
       else top1_fundamental_group_invg Y TY y0 (fst (rest!k)))"
    using Cons(4) unfolding fs'_def hw by (by100 force)
  \<comment> \<open>IH gives word\_product rest = class of foldr rest.\<close>
  have hIH: "top1_group_word_product
      (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
      (top1_fundamental_group_invg Y TY y0) rest
    = {g. top1_loop_equiv_on Y TY y0
        (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0)) g}"
    using Cons(1)[OF Cons(2) hloops' hmatch'] .
  \<comment> \<open>fs 0 is a loop, and its class matches w.\<close>
  have hfs0_loop: "top1_is_loop_on Y TY y0 (fs 0)"
    using Cons(3) by (by100 force)
  have hfs0_class: "{g. top1_loop_equiv_on Y TY y0 (fs 0) g}
      = (if b then x else top1_fundamental_group_invg Y TY y0 x)"
    using Cons(4) hw by (by100 force)
  \<comment> \<open>The foldr of the rest is a loop.\<close>
  have hfoldr_loop: "top1_is_loop_on Y TY y0
      (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0))"
  proof -
    have hy0_Y: "y0 \<in> Y"
    proof -
      have hfs0: "top1_is_loop_on Y TY y0 (fs 0)" using Cons(3) by (by100 force)
      have "fs 0 0 = y0" using hfs0 unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 auto)
      moreover have "fs 0 0 \<in> Y" using hfs0 \<open>0 \<in> I_set\<close>
        unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hconst: "top1_is_loop_on Y TY y0 (top1_constant_path y0)"
      using top1_constant_path_is_loop[OF hTA hy0_Y] .
    have hloops_set: "\<forall>g \<in> set (map fs' [0..<length rest]). top1_is_loop_on Y TY y0 g"
      using hloops' by (by100 force)
    show ?thesis using foldr_path_product_loops_is_loop[OF hTA hconst hloops_set] .
  qed
  \<comment> \<open>Apply top1\_fundamental\_group\_mul\_class.\<close>
  have hmul: "top1_fundamental_group_mul Y TY y0
      {g. top1_loop_equiv_on Y TY y0 (fs 0) g}
      {g. top1_loop_equiv_on Y TY y0
          (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0)) g}
    = {g. top1_loop_equiv_on Y TY y0
          (top1_path_product (fs 0)
            (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0))) g}"
    using top1_fundamental_group_mul_class[OF hTA hfs0_loop hfoldr_loop] .
  \<comment> \<open>word\_product (w#rest) = \<pi>_1\_mul(x\^b, word\_product rest).\<close>
  have hstep: "top1_group_word_product
      (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
      (top1_fundamental_group_invg Y TY y0) (w # rest)
    = top1_fundamental_group_mul Y TY y0
        (if b then x else top1_fundamental_group_invg Y TY y0 x)
        (top1_group_word_product
          (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
          (top1_fundamental_group_invg Y TY y0) rest)"
    unfolding hw by (cases b) (by100 simp)+
  \<comment> \<open>Substitute class(fs 0) for x\^b, and IH for word\_product rest.\<close>
  have "top1_group_word_product
      (top1_fundamental_group_mul Y TY y0) (top1_fundamental_group_id Y TY y0)
      (top1_fundamental_group_invg Y TY y0) (w # rest)
    = top1_fundamental_group_mul Y TY y0
        {g. top1_loop_equiv_on Y TY y0 (fs 0) g}
        {g. top1_loop_equiv_on Y TY y0
            (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0)) g}"
    using hstep hfs0_class hIH by (by100 simp)
  \<comment> \<open>= class of (fs 0 * foldr rest const) by mul\_class.\<close>
  also have "\<dots> = {g. top1_loop_equiv_on Y TY y0
      (top1_path_product (fs 0)
        (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0))) g}"
    using hmul .
  \<comment> \<open>= class of foldr (map fs [0..<Suc(length rest)]) const.\<close>
  also have "top1_path_product (fs 0)
      (foldr top1_path_product (map fs' [0..<length rest]) (top1_constant_path y0))
    = foldr top1_path_product (map fs [0..<length (w # rest)]) (top1_constant_path y0)"
  proof -
    have "map fs [0..<Suc (length rest)] = fs 0 # map fs' [0..<length rest]"
      unfolding fs'_def using upt_rec[of 0 "Suc (length rest)"] map_Suc_upt[of 0 "length rest", symmetric]
      by (by100 simp)
    thus ?thesis by (by100 simp)
  qed
  finally show ?case .
qed

lemma cancel_pair_not_reduced:
  assumes "i + 1 < length xs"
      and "fst (xs ! i) = fst (xs ! (i+1))"
      and "snd (xs ! i) \<noteq> snd (xs ! (i+1))"
  shows "\<not> top1_is_reduced_word xs"
  using assms
proof (induction xs arbitrary: i)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases i)
    case 0
    from Cons.prems(1) have "xs \<noteq> []" by auto
    then obtain y ys where hxs: "xs = y # ys" by (cases xs) auto
    obtain a b where "x = (a, b)" by (cases x) auto
    obtain c d where "y = (c, d)" by (cases y) auto
    from Cons.prems(2,3) 0 have "a = c \<and> b \<noteq> d"
      unfolding \<open>x = (a,b)\<close> \<open>y = (c,d)\<close> hxs by simp
    thus ?thesis unfolding \<open>x = (a,b)\<close> hxs \<open>y = (c,d)\<close> by simp
  next
    case (Suc i')
    from Cons.prems have "i' + 1 < length xs" "fst (xs ! i') = fst (xs ! (i'+1))"
        "snd (xs ! i') \<noteq> snd (xs ! (i'+1))" using Suc by auto
    from Cons.IH[OF this] have "\<not> top1_is_reduced_word xs" .
    moreover obtain a b where "x = (a,b)" by (cases x) auto
    ultimately show ?thesis
    proof (cases xs)
      case Nil thus ?thesis using \<open>\<not> top1_is_reduced_word xs\<close> by simp
    next
      case (Cons y ys)
      obtain c d where "y = (c,d)" by (cases y) auto
      show ?thesis using \<open>\<not> top1_is_reduced_word xs\<close>
        unfolding \<open>x = (a,b)\<close> Cons \<open>y = (c,d)\<close> by simp
    qed
  qed
qed

lemma foldr_replicate_is_path_power:
  "foldr top1_path_product (replicate n f) (top1_constant_path x) = top1_path_power f x n"
  by (induction n) (simp_all add: top1_path_power_0 top1_path_power_Suc)

lemma map_const_upt_replicate: "map (\<lambda>(_::nat). f) [0..<n] = replicate n f"
  by (simp add: map_replicate_trivial map_upt_eqI)

lemma foldr_uniform_is_path_power:
  "foldr top1_path_product (map (\<lambda>_. f) [0..<n]) (top1_constant_path x) = top1_path_power f x n"
  unfolding map_const_upt_replicate by (rule foldr_replicate_is_path_power)

text \<open>Helper: given a loop g with k pieces, a connecting path cp from a to g(sub3(1)) in set S,
  where piece 1 is also in S, construct g' homotopic to g with k-1 pieces.
  This is the core of Case A, parameterized by the connecting path.\<close>
text \<open>Construction-only: cp*g\_R is a loop with k-1 pieces.
  Same construction as hgen\_connecting\_path\_reduction but without the g\_L~cp homotopy.\<close>
lemma hgen_subdivision_only:
  assumes hTX: "is_topology_on X TX"
      and hk: "k \<ge> 2"
      and hg_loop: "top1_is_loop_on X TX a g"
      and hs0: "sub3 0 = 0" and hsk: "sub3 k = 1"
      and hs_inc: "\<forall>i<k. sub3 i < sub3 (Suc i)"
      and hs_UV: "\<forall>i\<le>k. g (sub3 i) \<in> UV"
      and hs_pieces: "\<forall>i<k. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> U') \<or>
             (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> V')"
      and hcp: "top1_is_path_on X TX a (g (sub3 1)) cp"
      and hcp_in_S: "\<forall>s \<in> I_set. cp s \<in> S"
      and hS_sub: "S \<subseteq> X"
      and hpiece1_in_S: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> S"
      and hS_type: "S = U' \<or> S = V'"
  shows "\<exists>sub3'. top1_is_loop_on X TX a
      (top1_path_product cp (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))) \<and>
      (k-1) \<ge> 1 \<and> sub3' 0 = 0 \<and> sub3' (k-1) = 1 \<and>
      (\<forall>i<k-1. sub3' i < sub3' (Suc i)) \<and>
      (\<forall>i\<le>k-1. (top1_path_product cp (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))) (sub3' i) \<in> UV) \<and>
      (\<forall>i<k-1. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> (top1_path_product cp (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t)))(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U') \<or>
             (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> (top1_path_product cp (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t)))(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V'))"
proof -
  define g_R where "g_R = (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))"
  let ?g' = "top1_path_product cp g_R"
  \<comment> \<open>Reuse the full helper by providing a trivial homotopy (g\\_L ~ cp for SOME cp).
     Actually, we can't do that since g\\_L and cp may be in different SC spaces.
     Instead, note that the construction part of the full helper's proof doesn't use hgL\\_htpy.
     We replicate just the construction.\<close>
  have hsub31_pos: "0 < sub3 1" using hs_inc hs0 hk by (by100 force)
  have hsub3_strict: "\<And>i j. i < j \<Longrightarrow> j \<le> k \<Longrightarrow> sub3 i < sub3 j"
  proof -
    fix i j :: nat assume "i < j" "j \<le> k"
    thus "sub3 i < sub3 j"
    proof (induction j)
      case 0 thus ?case by simp
    next
      case (Suc j) show ?case
      proof (cases "i = j")
        case True thus ?thesis using hs_inc Suc.prems by simp
      next
        case False hence "sub3 i < sub3 j" using Suc by linarith
        also have "sub3 j < sub3 (Suc j)" using hs_inc Suc.prems by simp
        finally show ?thesis .
      qed
    qed
  qed
  have hsub31_lt1: "sub3 1 < 1" using hsub3_strict[of 1 k] hk hsk by linarith
  \<comment> \<open>g\\_R: path from g(sub3(1)) to a.\<close>
  have hgR_path: "top1_is_path_on X TX (g (sub3 1)) a g_R"
  proof -
    have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
      using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have "top1_continuous_map_on I_set I_top X TX (g \<circ> (\<lambda>t. sub3 1 + t * (1 - sub3 1)))"
      by (rule top1_continuous_map_on_comp[OF
          affine_map_continuous_I_to_I[of "sub3 1" 1, OF _ _ _] hg_cont])
        (use hsub31_pos hsub31_lt1 in linarith)+
    moreover have "(g \<circ> (\<lambda>t. sub3 1 + t * (1 - sub3 1))) = g_R"
      unfolding g_R_def by (rule ext) (simp add: algebra_simps)
    ultimately have "top1_continuous_map_on I_set I_top X TX g_R" by simp
    moreover have "g_R 0 = g (sub3 1)" unfolding g_R_def by simp
    moreover have "g_R 1 = a"
    proof -
      have "g 1 = a" using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      thus ?thesis unfolding g_R_def by simp
    qed
    ultimately show ?thesis unfolding top1_is_path_on_def by blast
  qed
  \<comment> \<open>g' = cp * g\\_R is a loop at a.\<close>
  have hg'_loop: "top1_is_loop_on X TX a ?g'"
  proof -
    from top1_path_product_is_path[OF hTX hcp hgR_path]
    show ?thesis unfolding top1_is_loop_on_def by (by100 blast)
  qed
  \<comment> \<open>Subdivision for g' with k-1 pieces. Same as full helper.\<close>
  let ?d = "1 - sub3 1"
  have hd_pos: "?d > 0" using hsub31_lt1 by linarith
  define sub3' where "sub3' j = (if j = 0 then 0
      else 1/2 + (sub3 (j+1) - sub3 1) / (2 * ?d))" for j
  have hsub3'_0: "sub3' 0 = 0" unfolding sub3'_def by simp
  have hsub3'_km1: "sub3' (k-1) = 1"
  proof -
    have "sub3' (k-1) = 1/2 + (sub3 ((k-1)+1) - sub3 1) / (2 * ?d)"
      unfolding sub3'_def using hk by simp
    also have "(k-1)+1 = k" using hk by linarith
    also have "sub3 k = 1" using hsk .
    finally show ?thesis using hd_pos by (simp add: field_simps)
  qed
  \<comment> \<open>Mono, UV, pieces: same proofs as full helper.\<close>
  have hsub3'_mono: "\<forall>i<k-1. sub3' i < sub3' (Suc i)"
  proof (intro allI impI)
    fix i assume hi: "i < k - 1"
    show "sub3' i < sub3' (Suc i)"
    proof (cases "i = 0")
      case True
      have "sub3' (Suc 0) = 1/2 + (sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d)"
        unfolding sub3'_def by simp
      moreover have "(sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d) \<ge> 0"
        using hsub3_strict[of 1 "Suc 0 + 1"] hk hd_pos by (by100 simp)
      ultimately have "sub3' (Suc 0) > 0" by linarith
      thus ?thesis using True hsub3'_0 by simp
    next
      case False
      have hv1: "sub3' i = 1/2 + (sub3 (i+1) - sub3 1) / (2 * ?d)"
        unfolding sub3'_def using False by auto
      have hv2: "sub3' (Suc i) = 1/2 + (sub3 (Suc i + 1) - sub3 1) / (2 * ?d)"
        unfolding sub3'_def by auto
      have "sub3 (i+1) < sub3 (Suc i + 1)"
        using hsub3_strict[of "i+1" "Suc i + 1"] hi hk by linarith
      hence "(sub3 (i+1) - sub3 1) / (2 * ?d) < (sub3 (Suc i + 1) - sub3 1) / (2 * ?d)"
      proof -
        have "0 < 2 * ?d"
        proof -
          from hd_pos have "(0::real) < 1 - sub3 1" .
          hence "(0::real) < 2 - 2 * sub3 1" by linarith
          thus ?thesis by (simp add: algebra_simps)
        qed
        thus ?thesis using \<open>sub3 (i+1) < sub3 (Suc i+1)\<close>
          by (intro divide_strict_right_mono) linarith+
      qed
      thus ?thesis using hv1 hv2 by linarith
    qed
  qed
  \<comment> \<open>Path product helpers.\<close>
  have pp_gt: "\<And>s::real. s > 1/2 \<Longrightarrow> ?g' s = g_R (2*s - 1)"
    unfolding top1_path_product_def by simp
  have hsub3'_gt: "\<And>j. j \<ge> 1 \<Longrightarrow> j \<le> k-1 \<Longrightarrow> sub3' j > 1/2"
  proof -
    fix j :: nat assume "j \<ge> 1" "j \<le> k-1"
    have "sub3' j = 1/2 + (sub3 (j+1) - sub3 1) / (2 * ?d)"
      unfolding sub3'_def using \<open>j \<ge> 1\<close> by auto
    moreover have "sub3 (j+1) > sub3 1"
      using hsub3_strict[of 1 "j+1"] \<open>j \<ge> 1\<close> \<open>j \<le> k-1\<close> hk by linarith
    hence "(sub3 (j+1) - sub3 1) / (2 * ?d) > 0" using hd_pos by (by100 simp)
    ultimately show "sub3' j > 1/2" by linarith
  qed
  \<comment> \<open>g'(sub3'(j)) = g(sub3(j+1)) for j\<ge>1.\<close>
  have hg'_val: "\<And>j. j \<ge> 1 \<Longrightarrow> j \<le> k-1 \<Longrightarrow> ?g' (sub3' j) = g (sub3 (j+1))"
  proof -
    fix j :: nat assume hj1: "j \<ge> 1" and hj2: "j \<le> k-1"
    have "?g' (sub3' j) = g_R (2 * sub3' j - 1)"
      by (rule pp_gt[OF hsub3'_gt[OF hj1 hj2]])
    also have "g_R (2 * sub3' j - 1) = g (sub3 1 + ?d * (2 * sub3' j - 1))"
      unfolding g_R_def by (simp add: mult.commute)
    also have "sub3 1 + ?d * (2 * sub3' j - 1) = sub3 (j+1)"
    proof -
      have hval: "sub3' j = 1/2 + (sub3 (j+1) - sub3 1) / (2 * ?d)"
        unfolding sub3'_def using hj1 by auto
      have "2 * sub3' j - 1 = (sub3 (j+1) - sub3 1) / ?d"
      proof -
        from hval have "2 * sub3' j = 1 + 2 * ((sub3 (j+1) - sub3 1) / (2 * ?d))"
          by linarith
        also have "2 * ((sub3 (j+1) - sub3 1) / (2 * ?d)) = (sub3 (j+1) - sub3 1) / ?d"
        proof -
          have "2 * (sub3 (j+1) - sub3 1) / (2 * ?d) = (sub3 (j+1) - sub3 1) / ?d"
            using mult_divide_mult_cancel_left[of "(2::real)" "sub3 (j+1) - sub3 1" "?d"]
              hd_pos by linarith
          moreover have "2 * ((sub3 (j+1) - sub3 1) / (2 * ?d)) =
              2 * (sub3 (j+1) - sub3 1) / (2 * ?d)" by simp
          ultimately show ?thesis by simp
        qed
        finally show ?thesis by linarith
      qed
      hence "?d * (2 * sub3' j - 1) = sub3 (j+1) - sub3 1"
        using hd_pos by (by100 simp)
      thus ?thesis by linarith
    qed
    finally show "?g' (sub3' j) = g (sub3 (j+1))" .
  qed
  have hsub3'_UV: "\<forall>i\<le>k-1. ?g' (sub3' i) \<in> UV"
  proof (intro allI impI)
    fix i assume hi: "i \<le> k - 1"
    show "?g' (sub3' i) \<in> UV"
    proof (cases "i = 0")
      case True
      have "?g' (sub3' 0) = ?g' 0" using hsub3'_0 by simp
      also have "... = cp 0"
        using top1_path_product_at_start[of cp g_R] by simp
      also have "cp 0 = a" using hcp unfolding top1_is_path_on_def by (by100 blast)
      finally have "?g' (sub3' i) = a" using True by simp
      moreover have "a \<in> UV"
      proof -
        have "g (sub3 0) \<in> UV" using hs_UV hk by (by100 force)
        moreover have "g 0 = a" using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
          by (by100 blast)
        ultimately show ?thesis using hs0 by simp
      qed
      ultimately show ?thesis by simp
    next
      case False hence "i \<ge> 1" by linarith
      have "?g' (sub3' i) = g (sub3 (i+1))" by (rule hg'_val[OF \<open>i \<ge> 1\<close> hi])
      moreover have "g (sub3 (i+1)) \<in> UV"
        using hs_UV[rule_format, of "i+1"] hi hk by linarith
      ultimately show ?thesis by simp
    qed
  qed
  \<comment> \<open>Reparametrization for j\<ge>1: same as full helper.\<close>
  have hpiece_j_ge1: "\<And>j t. j \<ge> 1 \<Longrightarrow> j < k-1 \<Longrightarrow> 0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow>
      ?g' (sub3' j + t * (sub3' (Suc j) - sub3' j)) =
      g (sub3 (j+1) + t * (sub3 (Suc j + 1) - sub3 (j+1)))"
  proof -
    fix j :: nat and t :: real
    assume hj1: "j \<ge> 1" and hjk: "j < k-1" and ht0: "0 \<le> t" and ht1: "t \<le> 1"
    have hgt: "sub3' j + t * (sub3' (Suc j) - sub3' j) > 1/2"
    proof -
      have "sub3' j > 1/2" by (rule hsub3'_gt[OF hj1]) (use hjk in linarith)
      moreover have "sub3' (Suc j) \<ge> sub3' j"
        using hsub3'_mono[rule_format, of j] hjk by linarith
      hence "t * (sub3' (Suc j) - sub3' j) \<ge> 0" using ht0 by (by100 simp)
      ultimately show ?thesis by linarith
    qed
    have "?g' (sub3' j + t * (sub3' (Suc j) - sub3' j)) =
        g_R (2 * (sub3' j + t * (sub3' (Suc j) - sub3' j)) - 1)"
      by (rule pp_gt[OF hgt])
    also have "... = g (sub3 1 + ?d * (2 * (sub3' j + t * (sub3' (Suc j) - sub3' j)) - 1))"
      unfolding g_R_def by (simp add: mult.commute)
    also have "sub3 1 + ?d * (2 * (sub3' j + t * (sub3' (Suc j) - sub3' j)) - 1) =
        sub3 (j+1) + t * (sub3 (Suc j + 1) - sub3 (j+1))"
    proof -
      have "?d * (2 * (sub3' j + t * (sub3' (Suc j) - sub3' j)) - 1) =
          ?d * (2 * sub3' j - 1) + 2 * ?d * t * (sub3' (Suc j) - sub3' j)"
        by (simp add: algebra_simps)
      moreover have "?d * (2 * sub3' j - 1) = sub3 (j+1) - sub3 1"
      proof -
        have "2 * sub3' j - 1 = (sub3 (j+1) - sub3 1) / ?d"
        proof -
          have hval: "sub3' j = 1/2 + (sub3 (j+1) - sub3 1) / (2 * ?d)"
            unfolding sub3'_def using hj1 by auto
          from hval have "2 * sub3' j = 1 + 2 * ((sub3 (j+1) - sub3 1) / (2 * ?d))"
            by linarith
          also have "2 * ((sub3 (j+1) - sub3 1) / (2 * ?d)) = (sub3 (j+1) - sub3 1) / ?d"
          proof -
            have "2 * (sub3 (j+1) - sub3 1) / (2 * ?d) = (sub3 (j+1) - sub3 1) / ?d"
              using mult_divide_mult_cancel_left[of "(2::real)" "sub3 (j+1) - sub3 1" "?d"]
                hd_pos by linarith
            moreover have "2 * ((sub3 (j+1) - sub3 1) / (2 * ?d)) =
                2 * (sub3 (j+1) - sub3 1) / (2 * ?d)" by simp
            ultimately show ?thesis by simp
          qed
          finally show ?thesis by linarith
        qed
        thus ?thesis using hd_pos by (by100 simp)
      qed
      moreover have "2 * ?d * (sub3' (Suc j) - sub3' j) = sub3 (Suc j + 1) - sub3 (j+1)"
      proof -
        have hsi_ne: "Suc j \<noteq> 0" by simp
        have hj_ne: "j \<noteq> 0" using hj1 by linarith
        have "sub3' (Suc j) - sub3' j =
            (sub3 (Suc j + 1) - sub3 1) / (2 * ?d) - (sub3 (j+1) - sub3 1) / (2 * ?d)"
          unfolding sub3'_def using hsi_ne hj_ne by auto
        also have "... = (sub3 (Suc j + 1) - sub3 (j+1)) / (2 * ?d)"
          using hd_pos by (simp add: diff_divide_distrib)
        finally have "sub3' (Suc j) - sub3' j = (sub3 (Suc j + 1) - sub3 (j+1)) / (2 * ?d)" .
        hence "2 * ?d * (sub3' (Suc j) - sub3' j) =
            2 * ?d * ((sub3 (Suc j + 1) - sub3 (j+1)) / (2 * ?d))" by simp
        also have "... = sub3 (Suc j + 1) - sub3 (j+1)"
        proof -
          from hd_pos have "0 < 2 - 2 * sub3 1" by linarith
          hence h2d_ne: "(2 * ?d) \<noteq> (0::real)" by (simp add: algebra_simps)
          show ?thesis using nonzero_mult_div_cancel_left[OF h2d_ne] by simp
        qed
        finally show ?thesis .
      qed
      moreover have "2 * ?d * t * (sub3' (Suc j) - sub3' j) =
          t * (sub3 (Suc j + 1) - sub3 (j+1))"
      proof -
        have "2 * ?d * (sub3' (Suc j) - sub3' j) = sub3 (Suc j + 1) - sub3 (j+1)"
          by fact
        hence "t * (2 * ?d * (sub3' (Suc j) - sub3' j)) = t * (sub3 (Suc j + 1) - sub3 (j+1))"
          by simp
        thus ?thesis by (simp add: mult.assoc mult.commute)
      qed
      ultimately show ?thesis by linarith
    qed
    finally show "?g' (sub3' j + t * (sub3' (Suc j) - sub3' j)) =
        g (sub3 (j+1) + t * (sub3 (Suc j + 1) - sub3 (j+1)))" .
  qed
  have hsub3'_pieces: "\<forall>i<k-1.
      (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> ?g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U') \<or>
      (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> ?g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V')"
  proof (intro allI impI)
    fix i assume hi: "i < k - 1"
    show "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> ?g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U') \<or>
         (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> ?g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V')"
    proof (cases "i = 0")
      case True
      \<comment> \<open>Piece 0: merged cp+piece\_1. Both in S. S = U' or V'.\<close>
      have pp_le: "\<And>s::real. s \<le> 1/2 \<Longrightarrow> ?g' s = cp (2*s)"
        unfolding top1_path_product_def by simp
      have hpiece0_in_S: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> ?g'(sub3' 0 + t*(sub3' (Suc 0) - sub3' 0)) \<in> S"
      proof (intro allI impI)
        fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
        define s where "s = t * sub3' (Suc 0)"
        have hs_eq: "sub3' 0 + t*(sub3' (Suc 0) - sub3' 0) = s"
          using hsub3'_0 unfolding s_def by simp
        show "?g' (sub3' 0 + t * (sub3' (Suc 0) - sub3' 0)) \<in> S"
        proof (cases "s \<le> 1/2")
          case True
          hence "?g' s = cp (2*s)" by (rule pp_le)
          moreover have "cp (2*s) \<in> S"
          proof -
            have "sub3' (Suc 0) \<ge> 0"
              using hsub3'_mono[rule_format, of 0] hi hsub3'_0 by linarith
            hence "s \<ge> 0" unfolding s_def using ht by (intro mult_nonneg_nonneg) auto
            hence "2*s \<in> I_set" using True unfolding top1_unit_interval_def by (by100 simp)
            thus ?thesis using hcp_in_S by blast
          qed
          ultimately show ?thesis using hs_eq by simp
        next
          case False hence "s > 1/2" by linarith
          hence "?g' s = g_R (2*s - 1)" by (rule pp_gt)
          also have "g_R (2*s - 1) \<in> S"
          proof -
            have hs_le: "s \<le> sub3' (Suc 0)"
            proof -
              have "sub3' (Suc 0) \<ge> 0"
                using hsub3'_mono[rule_format, of 0] hi hsub3'_0 by linarith
              have "sub3' (Suc 0) * t \<le> sub3' (Suc 0)"
                using mult_left_le[of t "sub3' (Suc 0)"] \<open>0 \<le> sub3' (Suc 0)\<close> ht by linarith
              hence "t * sub3' (Suc 0) \<le> sub3' (Suc 0)" by (simp add: mult.commute)
              thus ?thesis unfolding s_def .
            qed
            have h12: "sub3 (Suc 0 + 1) > sub3 1"
              using hsub3_strict[of 1 "Suc 0 + 1"] hk by linarith
            hence h12_ne: "sub3 (Suc 0 + 1) - sub3 1 > 0" by linarith
            have hu_bound: "2*s - 1 \<le> (sub3 (Suc 0 + 1) - sub3 1) / ?d"
            proof -
              have "sub3' (Suc 0) = 1/2 + (sub3 (Suc 0+1) - sub3 1) / (2*?d)"
                unfolding sub3'_def by simp
              have "2*s \<le> 2 * sub3' (Suc 0)" using hs_le by linarith
              also have "2 * sub3' (Suc 0) = 1 + 2*((sub3 (Suc 0+1) - sub3 1)/(2*?d))"
                using \<open>sub3' (Suc 0) = 1/2 + _\<close> by linarith
              also have "2*((sub3 (Suc 0+1) - sub3 1)/(2*?d)) = (sub3 (Suc 0+1) - sub3 1)/?d"
              proof -
                have "2*(sub3 (Suc 0+1) - sub3 1)/(2*?d) = (sub3 (Suc 0+1) - sub3 1)/?d"
                  using mult_divide_mult_cancel_left[of "(2::real)" "sub3 (Suc 0+1) - sub3 1" "?d"]
                    hd_pos by linarith
                moreover have "2*((sub3 (Suc 0+1) - sub3 1)/(2*?d)) = 2*(sub3 (Suc 0+1) - sub3 1)/(2*?d)"
                  by simp
                ultimately show ?thesis by simp
              qed
              finally show ?thesis by linarith
            qed
            define t' where "t' = ?d * (2*s - 1) / (sub3 (Suc 0 + 1) - sub3 1)"
            have ht'0: "t' \<ge> 0" unfolding t'_def using False hd_pos h12_ne by (by100 simp)
            have ht'1: "t' \<le> 1"
            proof -
              have "?d * (2*s-1) \<le> ?d * ((sub3 (Suc 0+1) - sub3 1)/?d)"
                using hu_bound hd_pos by (intro mult_left_mono) linarith+
              also have "?d * ((sub3 (Suc 0+1) - sub3 1)/?d) = sub3 (Suc 0+1) - sub3 1"
                using hd_pos by simp
              finally show ?thesis unfolding t'_def using h12_ne by (by100 simp)
            qed
            have "g_R (2*s - 1) = g (sub3 1 + ?d * (2*s - 1))" unfolding g_R_def
              by (simp add: mult.commute)
            also have "sub3 1 + ?d * (2*s - 1) = sub3 1 + t' * (sub3 (Suc 0 + 1) - sub3 1)"
              unfolding t'_def using h12_ne by (by100 simp)
            finally have "g_R (2*s - 1) = g (sub3 1 + t' * (sub3 (Suc 0 + 1) - sub3 1))" .
            moreover have "Suc 0 + 1 = Suc 1" by simp
            ultimately have "g_R (2*s - 1) = g (sub3 1 + t' * (sub3 (Suc 1) - sub3 1))" by simp
            thus ?thesis using hpiece1_in_S ht'0 ht'1 by simp
          qed
          finally show ?thesis using hs_eq by simp
        qed
      qed
      from hS_type show ?thesis using True hpiece0_in_S by blast
    next
      case False hence "i \<ge> 1" by linarith
      have "i + 1 < k" using hi by linarith
      from hs_pieces[rule_format, OF \<open>i+1 < k\<close>]
      have hpiece_orig: "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 (i+1) + t*(sub3 (Suc (i+1)) - sub3 (i+1))) \<in> U') \<or>
          (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 (i+1) + t*(sub3 (Suc (i+1)) - sub3 (i+1))) \<in> V')"
        by simp
      from this show ?thesis
      proof
        assume hU: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 (i+1) + t*(sub3 (Suc (i+1)) - sub3 (i+1))) \<in> U'"
        show ?thesis
        proof (intro disjI1 allI impI)
          fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
          from hpiece_j_ge1[OF \<open>i \<ge> 1\<close> hi] ht
          have "?g' (sub3' i + t * (sub3' (Suc i) - sub3' i)) =
              g (sub3 (i+1) + t * (sub3 (Suc i + 1) - sub3 (i+1)))" by blast
          also have "Suc i + 1 = Suc (i + 1)" by linarith
          finally show "?g' (sub3' i + t * (sub3' (Suc i) - sub3' i)) \<in> U'"
            using hU ht by simp
        qed
      next
        assume hV: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 (i+1) + t*(sub3 (Suc (i+1)) - sub3 (i+1))) \<in> V'"
        show ?thesis
        proof (intro disjI2 allI impI)
          fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
          from hpiece_j_ge1[OF \<open>i \<ge> 1\<close> hi] ht
          have "?g' (sub3' i + t * (sub3' (Suc i) - sub3' i)) =
              g (sub3 (i+1) + t * (sub3 (Suc i + 1) - sub3 (i+1)))" by blast
          also have "Suc i + 1 = Suc (i + 1)" by linarith
          finally show "?g' (sub3' i + t * (sub3' (Suc i) - sub3' i)) \<in> V'"
            using hV ht by simp
        qed
      qed
    qed
  qed
  have hk_m1: "k-1 \<ge> 1" using hk by linarith
  have "?g' = top1_path_product cp (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))"
    unfolding g_R_def by simp
  show ?thesis
    apply (rule exI[of _ sub3'])
    using hg'_loop hk_m1 hsub3'_0 hsub3'_km1 hsub3'_mono hsub3'_UV hsub3'_pieces
    unfolding g_R_def by blast
qed

lemma hgen_connecting_path_reduction:
  assumes hTX: "is_topology_on X TX"
      and hk: "k \<ge> 2"
      and hg_loop: "top1_is_loop_on X TX a g"
      and hs0: "sub3 0 = 0" and hsk: "sub3 k = 1"
      and hs_inc: "\<forall>i<k. sub3 i < sub3 (Suc i)"
      and hs_UV: "\<forall>i\<le>k. g (sub3 i) \<in> UV"
      and hs_pieces: "\<forall>i<k. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> U') \<or>
             (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> V')"
      and hcp: "top1_is_path_on X TX a (g (sub3 1)) cp"
      and hcp_in_S: "\<forall>s \<in> I_set. cp s \<in> S"
      and hS_sub: "S \<subseteq> X"
      and hpiece1_in_S: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> S"
      and hS_type: "S = U' \<or> S = V'"
      and hgL_htpy: "top1_path_homotopic_on X TX a (g (sub3 1))
          (\<lambda>t. g (sub3 1 * t)) cp"
  shows "\<exists>g' sub3'. top1_path_homotopic_on X TX a a g g' \<and>
      top1_is_loop_on X TX a g' \<and>
      (k-1) \<ge> 1 \<and> sub3' 0 = 0 \<and> sub3' (k-1) = 1 \<and>
      (\<forall>i<k-1. sub3' i < sub3' (Suc i)) \<and>
      (\<forall>i\<le>k-1. g' (sub3' i) \<in> UV) \<and>
      (\<forall>i<k-1. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U') \<or>
             (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V'))"
proof -
  \<comment> \<open>Step 1: Split g at sub3(1).\<close>
  have hsub31_pos: "0 < sub3 1" using hs_inc hs0 hk by (by100 force)
  have hsub3_strict: "\<And>i j. i < j \<Longrightarrow> j \<le> k \<Longrightarrow> sub3 i < sub3 j"
  proof -
    fix i j :: nat assume "i < j" "j \<le> k"
    thus "sub3 i < sub3 j"
    proof (induction j)
      case 0 thus ?case by simp
    next
      case (Suc j) show ?case
      proof (cases "i = j")
        case True thus ?thesis using hs_inc Suc.prems by simp
      next
        case False hence "sub3 i < sub3 j" using Suc by linarith
        also have "sub3 j < sub3 (Suc j)" using hs_inc Suc.prems by simp
        finally show ?thesis .
      qed
    qed
  qed
  have hsub31_lt1: "sub3 1 < 1"
    using hsub3_strict[of 1 k] hk hsk by linarith
  define g_L where "g_L = (\<lambda>t. g (sub3 1 * t))"
  define g_R where "g_R = (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))"
  have hg_path: "top1_is_path_on X TX a a g"
    using hg_loop unfolding top1_is_loop_on_def by (by100 blast)
  have hg_split: "top1_path_homotopic_on X TX a a g (top1_path_product g_L g_R)"
    unfolding g_L_def g_R_def
    by (rule path_product_split[OF hTX hg_path hsub31_pos hsub31_lt1])
  \<comment> \<open>Step 2: g\\_L ~ cp (given by hgL\\_htpy).\<close>
  have hgL_htpy': "top1_path_homotopic_on X TX a (g (sub3 1)) g_L cp"
    using hgL_htpy unfolding g_L_def .
  \<comment> \<open>Step 3: g\\_R is a path from g(sub3(1)) to a.\<close>
  have hgR_path: "top1_is_path_on X TX (g (sub3 1)) a g_R"
  proof -
    have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
      using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have haffR: "top1_continuous_map_on I_set I_top I_set I_top
        (\<lambda>t. sub3 1 + t * (1 - sub3 1))"
      by (rule affine_map_continuous_I_to_I) (use hsub31_pos hsub31_lt1 in linarith)+
    have "top1_continuous_map_on I_set I_top X TX (g \<circ> (\<lambda>t. sub3 1 + t * (1 - sub3 1)))"
      by (rule top1_continuous_map_on_comp[OF haffR hg_cont])
    moreover have "(g \<circ> (\<lambda>t. sub3 1 + t * (1 - sub3 1))) = g_R"
      unfolding g_R_def by (rule ext) (simp add: algebra_simps)
    ultimately have "top1_continuous_map_on I_set I_top X TX g_R" by simp
    moreover have "g_R 0 = g (sub3 1)" unfolding g_R_def by simp
    moreover have "g_R 1 = a"
    proof -
      have "g 1 = a" using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      thus ?thesis unfolding g_R_def by simp
    qed
    ultimately show ?thesis unfolding top1_is_path_on_def by blast
  qed
  \<comment> \<open>Step 4: g' = cp * g\\_R. g ~ g' via homotopy.\<close>
  define g' where "g' = top1_path_product cp g_R"
  have hg'_loop: "top1_is_loop_on X TX a g'"
  proof -
    have "top1_is_path_on X TX a a (top1_path_product cp g_R)"
      by (rule top1_path_product_is_path[OF hTX hcp hgR_path])
    thus ?thesis unfolding g'_def top1_is_loop_on_def by (by100 blast)
  qed
  have hg_htpy_g': "top1_path_homotopic_on X TX a a g g'"
  proof -
    have "top1_path_homotopic_on X TX a a (top1_path_product g_L g_R) (top1_path_product cp g_R)"
      by (rule path_homotopic_product_left[OF hTX hgL_htpy' hgR_path])
    from Lemma_51_1_path_homotopic_trans[OF hTX hg_split this]
    show ?thesis unfolding g'_def .
  qed
  \<comment> \<open>Step 5: Subdivision for g' with k-1 pieces.\<close>
  let ?d = "1 - sub3 1"
  have hd_pos: "?d > 0" using hsub31_lt1 by linarith
  define sub3' where "sub3' j = (if j = 0 then 0
      else 1/2 + (sub3 (j+1) - sub3 1) / (2 * ?d))" for j
  \<comment> \<open>All subdivision properties: same proof as Case A.\<close>
  have hsub3'_0: "sub3' 0 = 0" unfolding sub3'_def by simp
  have hsub3'_km1: "sub3' (k-1) = 1"
  proof -
    have "sub3' (k-1) = 1/2 + (sub3 ((k-1)+1) - sub3 1) / (2 * ?d)"
      unfolding sub3'_def using hk by simp
    also have "(k-1)+1 = k" using hk by linarith
    also have "sub3 k = 1" using hsk .
    finally show ?thesis using hd_pos by (simp add: field_simps)
  qed
  \<comment> \<open>Remaining subdivision properties: sorry for now (same as Case A).\<close>
  have hsub3'_mono: "\<forall>i<k-1. sub3' i < sub3' (Suc i)"
  proof (intro allI impI)
    fix i assume hi: "i < k - 1"
    show "sub3' i < sub3' (Suc i)"
    proof (cases "i = 0")
      case True
      have "sub3' (Suc 0) = 1/2 + (sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d)"
        unfolding sub3'_def by simp
      moreover have "(sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d) \<ge> 0"
        using hsub3_strict[of 1 "Suc 0 + 1"] hk hd_pos by (by100 simp)
      ultimately have "sub3' (Suc 0) > 0" by linarith
      thus ?thesis using True hsub3'_0 by simp
    next
      case False
      have hv1: "sub3' i = 1/2 + (sub3 (i+1) - sub3 1) / (2 * ?d)"
        unfolding sub3'_def using False by auto
      have hv2: "sub3' (Suc i) = 1/2 + (sub3 (Suc i + 1) - sub3 1) / (2 * ?d)"
        unfolding sub3'_def by auto
      have "sub3 (i+1) < sub3 (Suc i + 1)"
        using hsub3_strict[of "i+1" "Suc i + 1"] hi hk by linarith
      hence "(sub3 (i+1) - sub3 1) / (2 * ?d) < (sub3 (Suc i + 1) - sub3 1) / (2 * ?d)"
      proof -
        have "0 < 2 * ?d"
        proof -
          from hd_pos have "(0::real) < 1 - sub3 1" .
          hence "(0::real) < 2 - 2 * sub3 1" by linarith
          thus ?thesis by (simp add: algebra_simps)
        qed
        thus ?thesis using \<open>sub3 (i+1) < sub3 (Suc i+1)\<close>
          by (intro divide_strict_right_mono) linarith+
      qed
      thus ?thesis using hv1 hv2 by linarith
    qed
  qed
  \<comment> \<open>Path product helpers.\<close>
  have pp_gt: "\<And>s::real. s > 1/2 \<Longrightarrow> g' s = g_R (2*s - 1)"
    unfolding g'_def top1_path_product_def by simp
  have hsub3'_gt: "\<And>j. j \<ge> 1 \<Longrightarrow> j \<le> k-1 \<Longrightarrow> sub3' j > 1/2"
  proof -
    fix j :: nat assume "j \<ge> 1" "j \<le> k-1"
    have "sub3' j = 1/2 + (sub3 (j+1) - sub3 1) / (2 * ?d)"
      unfolding sub3'_def using \<open>j \<ge> 1\<close> by auto
    moreover have "sub3 (j+1) > sub3 1"
      using hsub3_strict[of 1 "j+1"] \<open>j \<ge> 1\<close> \<open>j \<le> k-1\<close> hk by linarith
    hence "(sub3 (j+1) - sub3 1) / (2 * ?d) > 0" using hd_pos by (by100 simp)
    ultimately show "sub3' j > 1/2" by linarith
  qed
  \<comment> \<open>g'(sub3'(j)) = g(sub3(j+1)) for j\\<ge>1.\<close>
  have hg'_val: "\<And>j. j \<ge> 1 \<Longrightarrow> j \<le> k-1 \<Longrightarrow> g' (sub3' j) = g (sub3 (j+1))"
  proof -
    fix j :: nat assume hj1: "j \<ge> 1" and hj2: "j \<le> k-1"
    have "g' (sub3' j) = g_R (2 * sub3' j - 1)"
      by (rule pp_gt[OF hsub3'_gt[OF hj1 hj2]])
    also have "g_R (2 * sub3' j - 1) = g (sub3 1 + ?d * (2 * sub3' j - 1))"
      unfolding g_R_def by (simp add: mult.commute)
    also have "sub3 1 + ?d * (2 * sub3' j - 1) = sub3 (j+1)"
    proof -
      have hval: "sub3' j = 1/2 + (sub3 (j+1) - sub3 1) / (2 * ?d)"
        unfolding sub3'_def using hj1 by auto
      have "2 * sub3' j - 1 = (sub3 (j+1) - sub3 1) / ?d"
      proof -
        from hval have "2 * sub3' j = 1 + 2 * ((sub3 (j+1) - sub3 1) / (2 * ?d))"
          by linarith
        also have "2 * ((sub3 (j+1) - sub3 1) / (2 * ?d)) = (sub3 (j+1) - sub3 1) / ?d"
        proof -
          have "?d \<noteq> 0" using hd_pos by linarith
          from hd_pos have "0 < 2 - 2 * sub3 1" by linarith
          hence "(2::real) * ?d \<noteq> 0" by (simp add: algebra_simps)
          have "2 * (sub3 (j+1) - sub3 1) / (2 * ?d) = (sub3 (j+1) - sub3 1) / ?d"
            using mult_divide_mult_cancel_left[of "(2::real)" "sub3 (j+1) - sub3 1" "?d"]
              hd_pos by linarith
          moreover have "2 * ((sub3 (j+1) - sub3 1) / (2*?d)) = 2 * (sub3 (j+1) - sub3 1) / (2*?d)"
            by simp
          ultimately show ?thesis by simp
        qed
        finally show ?thesis by linarith
      qed
      hence "?d * (2 * sub3' j - 1) = sub3 (j+1) - sub3 1"
        using hd_pos by (by100 simp)
      thus ?thesis by linarith
    qed
    finally show "g' (sub3' j) = g (sub3 (j+1))" .
  qed
  have hsub3'_UV: "\<forall>i\<le>k-1. g' (sub3' i) \<in> UV"
  proof (intro allI impI)
    fix i assume hi: "i \<le> k - 1"
    show "g' (sub3' i) \<in> UV"
    proof (cases "i = 0")
      case True
      have "g' (sub3' 0) = g' 0" using hsub3'_0 by simp
      also have "... = cp 0"
        using top1_path_product_at_start[of cp g_R] unfolding g'_def by simp
      also have "cp 0 = a" using hcp unfolding top1_is_path_on_def by (by100 blast)
      finally have "g' (sub3' i) = a" using True by simp
      moreover have "a \<in> UV"
      proof -
        have "g (sub3 0) \<in> UV" using hs_UV hk by (by100 force)
        moreover have "g 0 = a" using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
          by (by100 blast)
        ultimately show ?thesis using hs0 by simp
      qed
      ultimately show ?thesis by simp
    next
      case False hence "i \<ge> 1" by linarith
      have "g' (sub3' i) = g (sub3 (i+1))" by (rule hg'_val[OF \<open>i \<ge> 1\<close> hi])
      moreover have "g (sub3 (i+1)) \<in> UV"
        using hs_UV[rule_format, of "i+1"] hi hk by linarith
      ultimately show ?thesis by simp
    qed
  qed
  \<comment> \<open>Reparametrization for j\\<ge>1: same as Case A.\<close>
  have hpiece_j_ge1: "\<And>j t. j \<ge> 1 \<Longrightarrow> j < k-1 \<Longrightarrow> 0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow>
      g' (sub3' j + t * (sub3' (Suc j) - sub3' j)) =
      g (sub3 (j+1) + t * (sub3 (Suc j + 1) - sub3 (j+1)))"
  proof -
    fix j :: nat and t :: real
    assume hj1: "j \<ge> 1" and hjk: "j < k-1" and ht0: "0 \<le> t" and ht1: "t \<le> 1"
    have hgt: "sub3' j + t * (sub3' (Suc j) - sub3' j) > 1/2"
    proof -
      have "sub3' j > 1/2" by (rule hsub3'_gt[OF hj1]) (use hjk in linarith)
      moreover have "sub3' (Suc j) \<ge> sub3' j"
        using hsub3'_mono[rule_format, of j] hjk by linarith
      hence "t * (sub3' (Suc j) - sub3' j) \<ge> 0" using ht0 by (by100 simp)
      ultimately show ?thesis by linarith
    qed
    have "g' (sub3' j + t * (sub3' (Suc j) - sub3' j)) =
        g_R (2 * (sub3' j + t * (sub3' (Suc j) - sub3' j)) - 1)"
      by (rule pp_gt[OF hgt])
    also have "... = g (sub3 1 + ?d * (2 * (sub3' j + t * (sub3' (Suc j) - sub3' j)) - 1))"
      unfolding g_R_def by (simp add: mult.commute)
    also have "sub3 1 + ?d * (2 * (sub3' j + t * (sub3' (Suc j) - sub3' j)) - 1) =
        sub3 (j+1) + t * (sub3 (Suc j + 1) - sub3 (j+1))"
    proof -
      have "?d * (2 * (sub3' j + t * (sub3' (Suc j) - sub3' j)) - 1) =
          ?d * (2 * sub3' j - 1) + 2 * ?d * t * (sub3' (Suc j) - sub3' j)"
        by (simp add: algebra_simps)
      moreover have "?d * (2 * sub3' j - 1) = sub3 (j+1) - sub3 1"
      proof -
        have "2 * sub3' j - 1 = (sub3 (j+1) - sub3 1) / ?d"
        proof -
          have hval: "sub3' j = 1/2 + (sub3 (j+1) - sub3 1) / (2 * ?d)"
            unfolding sub3'_def using hj1 by auto
          from hval have "2 * sub3' j = 1 + 2 * ((sub3 (j+1) - sub3 1) / (2 * ?d))"
            by linarith
          also have "2 * ((sub3 (j+1) - sub3 1) / (2 * ?d)) = (sub3 (j+1) - sub3 1) / ?d"
          proof -
            have "2 * (sub3 (j+1) - sub3 1) / (2 * ?d) = (sub3 (j+1) - sub3 1) / ?d"
              using mult_divide_mult_cancel_left[of "(2::real)" "sub3 (j+1) - sub3 1" "?d"]
                hd_pos by linarith
            moreover have "2 * ((sub3 (j+1) - sub3 1) / (2 * ?d)) =
                2 * (sub3 (j+1) - sub3 1) / (2 * ?d)" by simp
            ultimately show ?thesis by simp
          qed
          finally show ?thesis by linarith
        qed
        thus ?thesis using hd_pos by (by100 simp)
      qed
      moreover have "2 * ?d * (sub3' (Suc j) - sub3' j) = sub3 (Suc j + 1) - sub3 (j+1)"
      proof -
        have hsi_ne: "Suc j \<noteq> 0" by simp
        have hj_ne: "j \<noteq> 0" using hj1 by linarith
        have "sub3' (Suc j) - sub3' j =
            (sub3 (Suc j + 1) - sub3 1) / (2 * ?d) - (sub3 (j+1) - sub3 1) / (2 * ?d)"
          unfolding sub3'_def using hsi_ne hj_ne by auto
        also have "... = (sub3 (Suc j + 1) - sub3 (j+1)) / (2 * ?d)"
          using hd_pos by (simp add: diff_divide_distrib)
        finally have "sub3' (Suc j) - sub3' j = (sub3 (Suc j + 1) - sub3 (j+1)) / (2 * ?d)" .
        hence "2 * ?d * (sub3' (Suc j) - sub3' j) =
            2 * ?d * ((sub3 (Suc j + 1) - sub3 (j+1)) / (2 * ?d))" by simp
        also have "... = sub3 (Suc j + 1) - sub3 (j+1)"
        proof -
          from hd_pos have "0 < 2 - 2 * sub3 1" by linarith
          hence h2d_ne: "(2 * ?d) \<noteq> (0::real)" by (simp add: algebra_simps)
          show ?thesis using nonzero_mult_div_cancel_left[OF h2d_ne] by simp
        qed
        finally show ?thesis .
      qed
      moreover have "2 * ?d * t * (sub3' (Suc j) - sub3' j) =
          t * (sub3 (Suc j + 1) - sub3 (j+1))"
      proof -
        have "2 * ?d * (sub3' (Suc j) - sub3' j) = sub3 (Suc j + 1) - sub3 (j+1)"
          by fact
        hence "t * (2 * ?d * (sub3' (Suc j) - sub3' j)) = t * (sub3 (Suc j + 1) - sub3 (j+1))"
          by simp
        thus ?thesis by (simp add: mult.assoc mult.commute)
      qed
      ultimately show ?thesis by linarith
    qed
    finally show "g' (sub3' j + t * (sub3' (Suc j) - sub3' j)) =
        g (sub3 (j+1) + t * (sub3 (Suc j + 1) - sub3 (j+1)))" .
  qed
  have hsub3'_pieces: "\<forall>i<k-1. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U') \<or>
         (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V')"
  proof (intro allI impI)
    fix i assume hi: "i < k - 1"
    show "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U') \<or>
         (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V')"
    proof (cases "i = 0")
      case True
      \<comment> \<open>Piece 0: merged cp+piece\\_1. Both in S. S = U' or V'.\<close>
      \<comment> \<open>Merged piece 0. For s \\<le> 1/2: g'(s) = cp(2s) \\<in> S. For s > 1/2: g'(s) = g\\_R(2s-1) maps to piece\\_1 \\<in> S.\<close>
      have pp_le: "\<And>s::real. s \<le> 1/2 \<Longrightarrow> g' s = cp (2*s)"
        unfolding g'_def top1_path_product_def by simp
      \<comment> \<open>Any t in [0,1]: g'(t*sub3'(1)) is in S.\<close>
      have hpiece0_in_S: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' 0 + t*(sub3' (Suc 0) - sub3' 0)) \<in> S"
      proof (intro allI impI)
        fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
        define s where "s = t * sub3' (Suc 0)"
        have hs_eq: "sub3' 0 + t*(sub3' (Suc 0) - sub3' 0) = s"
          using hsub3'_0 unfolding s_def by simp
        show "g' (sub3' 0 + t * (sub3' (Suc 0) - sub3' 0)) \<in> S"
        proof (cases "s \<le> 1/2")
          case True
          hence "g' s = cp (2*s)" by (rule pp_le)
          moreover have "cp (2*s) \<in> S"
          proof -
            have "sub3' (Suc 0) \<ge> 0"
              using hsub3'_mono[rule_format, of 0] hi hsub3'_0 by linarith
            hence "s \<ge> 0" unfolding s_def using ht by (intro mult_nonneg_nonneg) auto
            hence "2*s \<in> I_set" using True unfolding top1_unit_interval_def by (by100 simp)
            thus ?thesis using hcp_in_S by blast
          qed
          ultimately show ?thesis using hs_eq by simp
        next
          case False hence "s > 1/2" by linarith
          hence "g' s = g_R (2*s - 1)" by (rule pp_gt)
          also have "g_R (2*s - 1) \<in> S"
          proof -
            have hs_le: "s \<le> sub3' (Suc 0)"
            proof -
              have "sub3' (Suc 0) \<ge> 0"
                using hsub3'_mono[rule_format, of 0] hi hsub3'_0 by linarith
              have "sub3' (Suc 0) * t \<le> sub3' (Suc 0)"
                using mult_left_le[of t "sub3' (Suc 0)"] \<open>0 \<le> sub3' (Suc 0)\<close> ht by linarith
              hence "t * sub3' (Suc 0) \<le> sub3' (Suc 0)" by (simp add: mult.commute)
              thus ?thesis unfolding s_def .
            qed
            have h12: "sub3 (Suc 0 + 1) > sub3 1"
              using hsub3_strict[of 1 "Suc 0 + 1"] hk by linarith
            hence h12_ne: "sub3 (Suc 0 + 1) - sub3 1 > 0" by linarith
            \<comment> \<open>2s-1 \\<le> (sub3(2)-sub3(1))/d from s \\<le> sub3'(1).\<close>
            have hu_bound: "2*s - 1 \<le> (sub3 (Suc 0 + 1) - sub3 1) / ?d"
            proof -
              have "sub3' (Suc 0) = 1/2 + (sub3 (Suc 0+1) - sub3 1) / (2*?d)"
                unfolding sub3'_def by simp
              have "2*s \<le> 2 * sub3' (Suc 0)" using hs_le by linarith
              also have "2 * sub3' (Suc 0) = 1 + 2*((sub3 (Suc 0+1) - sub3 1)/(2*?d))"
                using \<open>sub3' (Suc 0) = 1/2 + _\<close> by linarith
              also have "2*((sub3 (Suc 0+1) - sub3 1)/(2*?d)) = (sub3 (Suc 0+1) - sub3 1)/?d"
              proof -
                have "2*(sub3 (Suc 0+1) - sub3 1)/(2*?d) = (sub3 (Suc 0+1) - sub3 1)/?d"
                  using mult_divide_mult_cancel_left[of "(2::real)" "sub3 (Suc 0+1) - sub3 1" "?d"]
                    hd_pos by linarith
                moreover have "2*((sub3 (Suc 0+1) - sub3 1)/(2*?d)) = 2*(sub3 (Suc 0+1) - sub3 1)/(2*?d)"
                  by simp
                ultimately show ?thesis by simp
              qed
              finally show ?thesis by linarith
            qed
            define t' where "t' = ?d * (2*s - 1) / (sub3 (Suc 0 + 1) - sub3 1)"
            have ht'0: "t' \<ge> 0" unfolding t'_def using False hd_pos h12_ne by (by100 simp)
            have ht'1: "t' \<le> 1"
            proof -
              have "?d * (2*s-1) \<le> ?d * ((sub3 (Suc 0+1) - sub3 1)/?d)"
                using hu_bound hd_pos by (intro mult_left_mono) linarith+
              also have "?d * ((sub3 (Suc 0+1) - sub3 1)/?d) = sub3 (Suc 0+1) - sub3 1"
                using hd_pos by simp
              finally show ?thesis unfolding t'_def using h12_ne by (by100 simp)
            qed
            have "g_R (2*s - 1) = g (sub3 1 + ?d * (2*s - 1))" unfolding g_R_def
              by (simp add: mult.commute)
            also have "sub3 1 + ?d * (2*s - 1) = sub3 1 + t' * (sub3 (Suc 0 + 1) - sub3 1)"
              unfolding t'_def using h12_ne by (by100 simp)
            finally have "g_R (2*s - 1) = g (sub3 1 + t' * (sub3 (Suc 0 + 1) - sub3 1))" .
            moreover have "Suc 0 + 1 = Suc 1" by simp
            ultimately have "g_R (2*s - 1) = g (sub3 1 + t' * (sub3 (Suc 1) - sub3 1))" by simp
            thus ?thesis using hpiece1_in_S ht'0 ht'1 by simp
          qed
          finally show ?thesis using hs_eq by simp
        qed
      qed
      \<comment> \<open>S = U' or V', so piece 0 \\<in> U' or V'.\<close>
      from hS_type show ?thesis using True hpiece0_in_S by blast
    next
      case False hence "i \<ge> 1" by linarith
      have "i + 1 < k" using hi by linarith
      from hs_pieces[rule_format, OF \<open>i+1 < k\<close>]
      have hpiece_orig: "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 (i+1) + t*(sub3 (Suc (i+1)) - sub3 (i+1))) \<in> U') \<or>
          (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 (i+1) + t*(sub3 (Suc (i+1)) - sub3 (i+1))) \<in> V')"
        by simp
      from this show ?thesis
      proof
        assume hU: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 (i+1) + t*(sub3 (Suc (i+1)) - sub3 (i+1))) \<in> U'"
        show ?thesis
        proof (intro disjI1 allI impI)
          fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
          from hpiece_j_ge1[OF \<open>i \<ge> 1\<close> hi] ht
          have "g' (sub3' i + t * (sub3' (Suc i) - sub3' i)) =
              g (sub3 (i+1) + t * (sub3 (Suc i + 1) - sub3 (i+1)))" by blast
          also have "Suc i + 1 = Suc (i + 1)" by linarith
          finally show "g' (sub3' i + t * (sub3' (Suc i) - sub3' i)) \<in> U'"
            using hU ht by simp
        qed
      next
        assume hV: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 (i+1) + t*(sub3 (Suc (i+1)) - sub3 (i+1))) \<in> V'"
        show ?thesis
        proof (intro disjI2 allI impI)
          fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
          from hpiece_j_ge1[OF \<open>i \<ge> 1\<close> hi] ht
          have "g' (sub3' i + t * (sub3' (Suc i) - sub3' i)) =
              g (sub3 (i+1) + t * (sub3 (Suc i + 1) - sub3 (i+1)))" by blast
          also have "Suc i + 1 = Suc (i + 1)" by linarith
          finally show "g' (sub3' i + t * (sub3' (Suc i) - sub3' i)) \<in> V'"
            using hV ht by simp
        qed
      qed
    qed
  qed
  have hk_m1: "k-1 \<ge> 1" using hk by linarith
  show ?thesis
  proof (intro exI conjI)
    show "top1_path_homotopic_on X TX a a g g'" by (rule hg_htpy_g')
    show "top1_is_loop_on X TX a g'" by (rule hg'_loop)
    show "(k-1) \<ge> 1" by (rule hk_m1)
    show "sub3' 0 = 0" by (rule hsub3'_0)
    show "sub3' (k-1) = 1" by (rule hsub3'_km1)
    show "\<forall>i<k-1. sub3' i < sub3' (Suc i)" by (rule hsub3'_mono)
    show "\<forall>i\<le>k-1. g' (sub3' i) \<in> UV" by (rule hsub3'_UV)
    show "\<forall>i<k-1. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U') \<or>
           (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V')"
      by (rule hsub3'_pieces)
  qed
qed

text \<open>Lemma 84.6 (Munkres): Two-component SvK generation.
  If X = U \<union> V open, U \<inter> V = A \<union> B disjoint open PC,
  U and V simply connected, \<alpha> path in U from a\<in>A to b\<in>B,
  \<beta> path in V from b to a, then [\<alpha>*\<beta>] generates \<pi>_1(X, a).
  Combined with Theorem 63.1 ([\<alpha>*\<beta>] non-trivial), gives \<pi>_1(X, a) \<cong> \<Z>.\<close>
lemma Lemma_84_6_two_component_generation:
  assumes hTX: "is_topology_on_strict X TX"
      and hU_open: "openin_on X TX U" and hV_open: "openin_on X TX V"
      and hcover: "U \<union> V = X"
      and hUV_split: "U \<inter> V = A \<union> B"
      and hAB_disj: "A \<inter> B = {}"
      and hA_open: "openin_on X TX A" and hB_open: "openin_on X TX B"
      and hA_pc: "top1_path_connected_on A (subspace_topology X TX A)"
      and hB_pc: "top1_path_connected_on B (subspace_topology X TX B)"
      and ha: "a \<in> A" and hb: "b \<in> B"
      and halpha: "top1_is_path_on U (subspace_topology X TX U) a b \<alpha>"
      and hbeta: "top1_is_path_on V (subspace_topology X TX V) b a \<beta>"
      and hU_sc: "top1_simply_connected_on U (subspace_topology X TX U)"
      and hV_sc: "top1_simply_connected_on V (subspace_topology X TX V)"
  shows "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier X TX a)
      (top1_fundamental_group_mul X TX a)
      top1_Z_group top1_Z_mul"
proof -
  let ?TX_loc = TX
  have hTX_top: "is_topology_on X TX"
    using hTX unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>Step 1 (book Lemma 84.6): [\\<alpha>*\\<beta>] generates \\<pi>\\_1(X, a).
     Every loop at a is a power of [\\<alpha>*\\<beta>] or [\\<beta>\\_bar*\\<alpha>\\_bar].
     Book proof: SvK-like decomposition into pieces in U or V,
     connecting paths through A or B. SC of U, V \\<Rightarrow> each piece trivial.\<close>
  have hgen: "\<forall>f. top1_is_loop_on X TX a f \<longrightarrow>
      (\<exists>n::nat. top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_product \<alpha> \<beta>) a n)
        \<or> top1_path_homotopic_on X TX a a f
             (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n))"
  proof (intro allI impI)
    fix f assume hf: "top1_is_loop_on X TX a f"
    \<comment> \<open>Step 1: Subdivide the loop f into pieces lying in U or V (Lebesgue number).\<close>
    from loop_subdivision_UV[OF hTX_top hU_open hV_open hcover hf]
    obtain n_sub sub_fn where
      hn_pos: "n_sub \<ge> 1" and
      hsub_0: "sub_fn 0 = 0" and hsub_n: "sub_fn n_sub = 1" and
      hsub_inc: "\<forall>i<n_sub. sub_fn i < sub_fn (Suc i)" and
      hpieces_UV: "\<forall>i<n_sub.
        (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (sub_fn i + t * (sub_fn (Suc i) - sub_fn i)) \<in> U) \<or>
        (\<forall>t. 0 \<le> t \<and> t \<le> 1 \<longrightarrow> f (sub_fn i + t * (sub_fn (Suc i) - sub_fn i)) \<in> V)"
      by (by5000 blast)
    \<comment> \<open>Step 2: Refine subdivision so all endpoints f(sub(i)) \\<in> U \\<inter> V.
       Merge consecutive same-type pieces: if f(sub(i)) \\<notin> U\\<inter>V, both adjacent
       pieces map to same set, so merging is valid. After merging, all internal
       endpoints are at U/V transitions, hence in U\\<inter>V. f(0)=f(1)=a\\<in>A\\<subseteq>U\\<inter>V.\<close>
    have h_refined: "\<exists>m sub2. m \<ge> 1 \<and> sub2 0 = 0 \<and> sub2 m = 1 \<and>
        (\<forall>i<m. sub2 i < sub2 (Suc i)) \<and>
        (\<forall>i\<le>m. f (sub2 i) \<in> U \<inter> V) \<and>
        (\<forall>i<m. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> f(sub2 i + t*(sub2 (Suc i) - sub2 i)) \<in> U) \<or>
               (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> f(sub2 i + t*(sub2 (Suc i) - sub2 i)) \<in> V))"
    proof -
      \<comment> \<open>Filter: keep only indices i where f(sub(i)) \\<in> U\\<inter>V (plus 0 and n\\_sub).\<close>
      define good where "good i = (i = 0 \<or> i = n_sub \<or> f (sub_fn i) \<in> U \<inter> V)" for i
      \<comment> \<open>f(0) = a \\<in> A \\<subseteq> U\\<inter>V, f(1) = a \\<in> A \\<subseteq> U\\<inter>V.\<close>
      have hf0: "f 0 = a" using hf unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      have hf1: "f 1 = a" using hf unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      have ha_UV: "a \<in> U \<inter> V" using hUV_split ha by (by100 blast)
      have hg0: "good 0" unfolding good_def by simp
      have hgn: "good n_sub" unfolding good_def by simp
      \<comment> \<open>Key: if f(sub(i)) \\<notin> U\\<inter>V, both adjacent pieces map to same set.\<close>
      \<comment> \<open>Define in\\_S predicate to avoid Suc(j-1) substitution issues.\<close>
      define in_S where "in_S i S = (\<forall>t::real. 0 \<le> t \<and> t \<le> 1 \<longrightarrow>
          f (sub_fn i + t * (sub_fn (Suc i) - sub_fn i)) \<in> S)" for i :: nat and S
      \<comment> \<open>hpieces\\_UV in terms of in\\_S.\<close>
      have hpieces_inS: "\<forall>i<n_sub. in_S i U \<or> in_S i V"
        using hpieces_UV unfolding in_S_def by blast
      \<comment> \<open>Strict monotonicity.\<close>
      have hsub_strict: "\<And>j l. j < l \<Longrightarrow> l \<le> n_sub \<Longrightarrow> sub_fn j < sub_fn l"
      proof -
        fix j l :: nat assume "j < l" "l \<le> n_sub"
        thus "sub_fn j < sub_fn l"
        proof (induction l)
          case 0 thus ?case by simp
        next
          case (Suc l) show ?case
          proof (cases "j = l")
            case True thus ?thesis using hsub_inc Suc.prems by simp
          next
            case False hence "j < l" using Suc.prems by linarith
            hence "sub_fn j < sub_fn l" using Suc.IH Suc.prems by linarith
            also have "sub_fn l < sub_fn (Suc l)" using hsub_inc Suc.prems by (by100 force)
            finally show ?thesis .
          qed
        qed
      qed
      \<comment> \<open>in\\_S i S at t=1 gives f(sub\\_fn(Suc i)) \\<in> S. At t=0 gives f(sub\\_fn i) \\<in> S.\<close>
      have in_S_t1: "\<And>i S. in_S i S \<Longrightarrow> f (sub_fn (Suc i)) \<in> S"
      proof -
        fix i :: nat and S
        assume h: "in_S i S"
        from h[unfolded in_S_def, rule_format, of 1]
        show "f (sub_fn (Suc i)) \<in> S" by simp
      qed
      have in_S_t0: "\<And>i S. in_S i S \<Longrightarrow> f (sub_fn i) \<in> S"
      proof -
        fix i :: nat and S
        assume h: "in_S i S"
        from h[unfolded in_S_def, rule_format, of 0]
        show "f (sub_fn i) \<in> S" by simp
      qed
      \<comment> \<open>h\\_same\\_type: if f(sub(k)) \\<notin> U\\<inter>V, pieces k-1 and k in same set.\<close>
      have h_same_type: "\<And>k. 0 < k \<Longrightarrow> k < n_sub \<Longrightarrow> f (sub_fn k) \<notin> U \<inter> V \<Longrightarrow>
          (in_S (k-1) U \<and> in_S k U) \<or> (in_S (k-1) V \<and> in_S k V)"
      proof -
        fix k assume hk_pos: "0 < k" and hk_lt: "k < n_sub" and hk_not: "f (sub_fn k) \<notin> U \<inter> V"
        have "k - 1 < n_sub" using hk_pos hk_lt by linarith
        have hp: "in_S (k-1) U \<or> in_S (k-1) V"
          using hpieces_inS \<open>k - 1 < n_sub\<close> by blast
        have hc: "in_S k U \<or> in_S k V"
          using hpieces_inS hk_lt by blast
        have hSuc_k1: "Suc (k-1) = k" using hk_pos by simp
        have hfk_endpoint: "in_S (k-1) U \<Longrightarrow> f (sub_fn k) \<in> U"
          using in_S_t1[of "k-1" U] hSuc_k1 by simp
        have hfk_endpoint_V: "in_S (k-1) V \<Longrightarrow> f (sub_fn k) \<in> V"
          using in_S_t1[of "k-1" V] hSuc_k1 by simp
        have hfk_0: "in_S k U \<Longrightarrow> f (sub_fn k) \<in> U" by (rule in_S_t0)
        have hfk_0V: "in_S k V \<Longrightarrow> f (sub_fn k) \<in> V" by (rule in_S_t0)
        show "(in_S (k-1) U \<and> in_S k U) \<or> (in_S (k-1) V \<and> in_S k V)"
        proof (cases "f (sub_fn k) \<in> U")
          case True hence "f (sub_fn k) \<notin> V" using hk_not by blast
          hence "\<not> in_S (k-1) V" using hfk_endpoint_V by blast
          hence "in_S (k-1) U" using hp by blast
          moreover have "\<not> in_S k V" using hfk_0V \<open>f (sub_fn k) \<notin> V\<close> by blast
          hence "in_S k U" using hc by blast
          ultimately show ?thesis by blast
        next
          case False
          have "f (sub_fn k) \<in> U \<or> f (sub_fn k) \<in> V"
            using hp hfk_endpoint hfk_endpoint_V by blast
          hence "f (sub_fn k) \<in> V" using False by blast
          hence "f (sub_fn k) \<notin> U" using hk_not by blast
          hence "\<not> in_S (k-1) U" using hfk_endpoint by blast
          hence "in_S (k-1) V" using hp by blast
          moreover have "\<not> in_S k U" using hfk_0 \<open>f (sub_fn k) \<notin> U\<close> by blast
          hence "in_S k V" using hc by blast
          ultimately show ?thesis by blast
        qed
      qed
      \<comment> \<open>h\\_all\\_same: between consecutive good pts, all pieces in same set.\<close>
      have h_all_same: "\<And>a b. a < b \<Longrightarrow> b \<le> n_sub \<Longrightarrow>
          (\<forall>k. a < k \<longrightarrow> k < b \<longrightarrow> \<not> good k) \<Longrightarrow>
          (\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow> in_S j U) \<or> (\<forall>j. a \<le> j \<longrightarrow> j < b \<longrightarrow> in_S j V)"
      proof -
        fix a0 b0 :: nat
        assume hab: "a0 < b0" "b0 \<le> n_sub"
          and hno_good: "\<forall>k. a0 < k \<longrightarrow> k < b0 \<longrightarrow> \<not> good k"
        have ha0_lt: "a0 < n_sub" using hab by linarith
        have hpiece_a0: "in_S a0 U \<or> in_S a0 V" using hpieces_inS ha0_lt by blast
        \<comment> \<open>Transfer: if in\\_S a0 S then in\\_S j S for all j in [a0, b0).\<close>
        have h_xfer: "\<And>j. a0 \<le> j \<Longrightarrow> j < b0 \<Longrightarrow> in_S a0 U \<longrightarrow> in_S j U"
        proof -
          fix j assume haj: "a0 \<le> j" "j < b0"
          show "in_S a0 U \<longrightarrow> in_S j U" using haj
          proof (induction "j - a0" arbitrary: j)
            case 0 hence "j = a0" by simp thus ?case by simp
          next
            case (Suc n)
            hence hj_pos: "a0 < j" by linarith
            have hj_lt: "j < n_sub" using Suc.prems(2) hab(2) by linarith
            have "\<not> good j" using hno_good hj_pos Suc.prems(2) by simp
            hence hj_not: "f (sub_fn j) \<notin> U \<inter> V" unfolding good_def
              using hj_pos Suc.prems(2) hab(2) by linarith
            have hj_pos0: "0 < j" using hj_pos by linarith
            from h_same_type[OF hj_pos0 hj_lt hj_not]
            have h_adj: "(in_S (j-1) U \<and> in_S j U) \<or> (in_S (j-1) V \<and> in_S j V)" .
            have "n = (j-1) - a0" "a0 \<le> j-1" "j-1 < b0"
              using Suc.hyps(2) hj_pos Suc.prems by linarith+
            from Suc.hyps(1)[OF \<open>n = (j-1) - a0\<close> \<open>a0 \<le> j-1\<close> \<open>j-1 < b0\<close>]
            have hIH: "in_S a0 U \<longrightarrow> in_S (j-1) U" .
            show "in_S a0 U \<longrightarrow> in_S j U"
            proof
              assume "in_S a0 U"
              from hIH this have "in_S (j-1) U" by blast
              from h_adj show "in_S j U"
              proof
                assume "(in_S (j-1) U \<and> in_S j U)" thus "in_S j U" by blast
              next
                assume h: "in_S (j-1) V \<and> in_S j V"
                \<comment> \<open>Contradiction: in\\_S (j-1) U and in\\_S (j-1) V give f(sub\\_fn(Suc(j-1))) \\<in> U\\<inter>V.\<close>
                from in_S_t1[of "j-1" U] \<open>in_S (j-1) U\<close> have "f (sub_fn (Suc (j-1))) \<in> U" by blast
                from in_S_t1[of "j-1" V] h have "f (sub_fn (Suc (j-1))) \<in> V" by blast
                have "Suc (j-1) = j" using hj_pos0 by simp
                hence "f (sub_fn j) \<in> U" "f (sub_fn j) \<in> V"
                  using \<open>f (sub_fn (Suc (j-1))) \<in> U\<close> \<open>f (sub_fn (Suc (j-1))) \<in> V\<close> by simp+
                hence "f (sub_fn j) \<in> U \<inter> V" by blast
                thus "in_S j U" using hj_not by blast
              qed
            qed
          qed
        qed
        \<comment> \<open>Symmetric for V.\<close>
        have h_xfer_V: "\<And>j. a0 \<le> j \<Longrightarrow> j < b0 \<Longrightarrow> in_S a0 V \<longrightarrow> in_S j V"
        proof -
          fix j assume haj: "a0 \<le> j" "j < b0"
          show "in_S a0 V \<longrightarrow> in_S j V" using haj
          proof (induction "j - a0" arbitrary: j)
            case 0 hence "j = a0" by simp thus ?case by simp
          next
            case (Suc n)
            hence hj_pos: "a0 < j" by linarith
            have hj_lt: "j < n_sub" using Suc.prems(2) hab(2) by linarith
            have "\<not> good j" using hno_good hj_pos Suc.prems(2) by simp
            hence hj_not: "f (sub_fn j) \<notin> U \<inter> V" unfolding good_def
              using hj_pos Suc.prems(2) hab(2) by linarith
            have hj_pos0: "0 < j" using hj_pos by linarith
            from h_same_type[OF hj_pos0 hj_lt hj_not]
            have h_adj: "(in_S (j-1) U \<and> in_S j U) \<or> (in_S (j-1) V \<and> in_S j V)" .
            have "n = (j-1) - a0" "a0 \<le> j-1" "j-1 < b0"
              using Suc.hyps(2) hj_pos Suc.prems by linarith+
            from Suc.hyps(1)[OF \<open>n = (j-1) - a0\<close> \<open>a0 \<le> j-1\<close> \<open>j-1 < b0\<close>]
            have hIH: "in_S a0 V \<longrightarrow> in_S (j-1) V" .
            show "in_S a0 V \<longrightarrow> in_S j V"
            proof
              assume "in_S a0 V"
              from hIH this have "in_S (j-1) V" by blast
              from h_adj show "in_S j V"
              proof
                assume h: "in_S (j-1) U \<and> in_S j U"
                from in_S_t1[of "j-1" V] \<open>in_S (j-1) V\<close> have "f (sub_fn (Suc (j-1))) \<in> V" by blast
                from in_S_t1[of "j-1" U] h have "f (sub_fn (Suc (j-1))) \<in> U" by blast
                have "Suc (j-1) = j" using hj_pos0 by simp
                hence "f (sub_fn j) \<in> U" "f (sub_fn j) \<in> V"
                  using \<open>f (sub_fn (Suc (j-1))) \<in> U\<close> \<open>f (sub_fn (Suc (j-1))) \<in> V\<close> by simp+
                hence "f (sub_fn j) \<in> U \<inter> V" by blast
                thus "in_S j V" using hj_not by blast
              next
                assume "(in_S (j-1) V \<and> in_S j V)" thus "in_S j V" by blast
              qed
            qed
          qed
        qed
        show "(\<forall>j. a0 \<le> j \<longrightarrow> j < b0 \<longrightarrow> in_S j U) \<or> (\<forall>j. a0 \<le> j \<longrightarrow> j < b0 \<longrightarrow> in_S j V)"
        proof (cases "in_S a0 U")
          case True
          have "\<forall>j. a0 \<le> j \<longrightarrow> j < b0 \<longrightarrow> in_S j U" using h_xfer True by blast
          thus ?thesis by blast
        next
          case False hence "in_S a0 V" using hpiece_a0 by blast
          have "\<forall>j. a0 \<le> j \<longrightarrow> j < b0 \<longrightarrow> in_S j V" using h_xfer_V \<open>in_S a0 V\<close> by blast
          thus ?thesis by blast
        qed
      qed
      \<comment> \<open>h\\_value\\_in\\_piece: any s in [sub(a), sub(b)] falls in some original piece.\<close>
      have h_value_in_piece: "\<And>a b s. a < b \<Longrightarrow> b \<le> n_sub \<Longrightarrow>
          sub_fn a \<le> s \<Longrightarrow> s \<le> sub_fn b \<Longrightarrow>
          \<exists>j. a \<le> j \<and> j < b \<and> sub_fn j \<le> s \<and> s \<le> sub_fn (Suc j)"
      proof -
        fix a0 b0 :: nat and s :: real
        assume hab: "a0 < b0" "b0 \<le> n_sub" and hs: "sub_fn a0 \<le> s" "s \<le> sub_fn b0"
        show "\<exists>j. a0 \<le> j \<and> j < b0 \<and> sub_fn j \<le> s \<and> s \<le> sub_fn (Suc j)"
          using hab hs
        proof (induction "b0 - a0" arbitrary: b0)
          case 0 thus ?case by simp
        next
          case (Suc n)
          show ?case
          proof (cases "s \<le> sub_fn (b0 - 1)")
            case True show ?thesis
            proof (cases "a0 = b0 - 1")
              case True hence "b0 = Suc a0" using Suc.prems(1) by linarith
              thus ?thesis using Suc.prems(3,4) \<open>s \<le> sub_fn (b0-1)\<close>
                by (rule_tac exI[of _ a0]) auto
            next
              case False hence "a0 < b0 - 1" using Suc.prems(1) by linarith
              moreover have "b0 - 1 \<le> n_sub" using Suc.prems(2) by linarith
              moreover have "b0 - 1 - a0 = n" using Suc.hyps(2) Suc.prems(1) by linarith
              ultimately obtain j where "a0 \<le> j" "j < b0 - 1" "sub_fn j \<le> s" "s \<le> sub_fn (Suc j)"
                using Suc.hyps(1)[of "b0-1"] Suc.prems(3) True by blast
              thus ?thesis
                apply (rule_tac exI[of _ j])
                using \<open>j < b0 - 1\<close> by linarith
            qed
          next
            case False
            hence "sub_fn (b0-1) < s" by linarith
            have "a0 \<le> b0 - 1" using Suc.prems(1) by linarith
            have "Suc (b0-1) = b0" using Suc.prems(1) by linarith
            show ?thesis
              apply (rule exI[of _ "b0-1"])
              using \<open>a0 \<le> b0 - 1\<close> Suc.prems(1) \<open>sub_fn (b0-1) < s\<close> Suc.prems(4) \<open>Suc (b0-1) = b0\<close>
              by simp
          qed
        qed
      qed
      \<comment> \<open>Filtering construction.\<close>
      define glist where "glist = filter good [0..<Suc n_sub]"
      have h0_mem: "0 \<in> set glist" unfolding glist_def using hg0 hn_pos by simp
      have hn_mem: "n_sub \<in> set glist" unfolding glist_def using hgn by simp
      have hglist_sorted: "sorted glist" unfolding glist_def
        by (metis sorted_wrt_filter sorted_upt)
      have hglist_distinct: "distinct glist" unfolding glist_def by simp
      have hglist_sub: "set glist \<subseteq> {0..n_sub}" unfolding glist_def by auto
      have hglist_len: "length glist \<ge> 2"
      proof -
        have "card {0, n_sub} = 2" using hn_pos by simp
        moreover have "{0, n_sub} \<subseteq> set glist" using h0_mem hn_mem by blast
        moreover have "card (set glist) = length glist" using hglist_distinct by (rule distinct_card)
        ultimately show ?thesis using card_mono[OF finite_set \<open>{0, n_sub} \<subseteq> set glist\<close>] by linarith
      qed
      define m_ref where "m_ref = length glist - 1"
      have hm_ge: "m_ref \<ge> 1" using hglist_len m_ref_def by linarith
      define sub2 where "sub2 j = sub_fn (glist ! j)" for j
      have hgl_0: "glist ! 0 = 0"
      proof -
        obtain j where hj: "glist ! j = 0" "j < length glist"
          using h0_mem by (metis in_set_conv_nth)
        have "glist ! 0 \<le> glist ! j"
          by (rule sorted_nth_mono[OF hglist_sorted]) (use hj hglist_len in auto)
        thus "glist ! 0 = 0" using hj(1) by simp
      qed
      have hgl_m: "glist ! m_ref = n_sub"
      proof -
        obtain j where hj: "glist ! j = n_sub" "j < length glist"
          using hn_mem by (metis in_set_conv_nth)
        have "glist ! j \<le> glist ! m_ref"
          by (rule sorted_nth_mono[OF hglist_sorted])
             (use hj hglist_len in \<open>auto simp: m_ref_def\<close>)
        hence "n_sub \<le> glist ! m_ref" using hj(1) by simp
        moreover have "glist ! m_ref \<le> n_sub"
        proof -
          have "glist ! m_ref \<in> set glist"
            using hglist_len unfolding m_ref_def by (intro nth_mem) simp
          thus ?thesis using hglist_sub by auto
        qed
        ultimately show ?thesis by simp
      qed
      have hsub2_0: "sub2 0 = 0" unfolding sub2_def using hgl_0 hsub_0 by simp
      have hsub2_m: "sub2 m_ref = 1" unfolding sub2_def using hgl_m hsub_n by simp
      have hsub2_inc: "\<forall>i<m_ref. sub2 i < sub2 (Suc i)"
      proof (intro allI impI)
        fix i assume hi: "i < m_ref"
        have hi_len: "i < length glist" using hi m_ref_def hglist_len by linarith
        have hsi_len: "Suc i < length glist" using hi m_ref_def hglist_len by linarith
        have "glist ! i < glist ! Suc i"
          using sorted_nth_mono[OF hglist_sorted, of i "Suc i"] hsi_len
                nth_eq_iff_index_eq[OF hglist_distinct hi_len hsi_len]
          by linarith
        moreover have "glist ! Suc i \<le> n_sub"
        proof -
          have "glist ! Suc i \<in> set glist" using hsi_len by (rule nth_mem)
          thus ?thesis using hglist_sub by auto
        qed
        ultimately show "sub2 i < sub2 (Suc i)" unfolding sub2_def
          using hsub_strict by simp
      qed
      have hsub2_UV: "\<forall>i\<le>m_ref. f (sub2 i) \<in> U \<inter> V"
      proof (intro allI impI)
        fix i assume "i \<le> m_ref"
        hence "i < length glist" using m_ref_def hglist_len by linarith
        hence hgi_mem: "glist ! i \<in> set glist" by (rule nth_mem)
        have "good (glist ! i)"
        proof -
          have "set glist \<subseteq> {x. good x}" unfolding glist_def by auto
          thus ?thesis using hgi_mem by blast
        qed
        thus "f (sub2 i) \<in> U \<inter> V" unfolding sub2_def good_def
          using hsub_0 hf0 ha_UV hsub_n hf1 by (by100 force)
      qed
      \<comment> \<open>Between consecutive glist entries, no other good index exists.\<close>
      have h_consec_no_good: "\<And>i. i < m_ref \<Longrightarrow>
          \<forall>k. glist ! i < k \<longrightarrow> k < glist ! (Suc i) \<longrightarrow> \<not> good k"
      proof (intro allI impI)
        fix i k assume hi: "i < m_ref" and hk1: "glist ! i < k" and hk2: "k < glist ! (Suc i)"
        have hsi_len: "Suc i < length glist" using hi m_ref_def hglist_len by linarith
        \<comment> \<open>k \\<in> {0..n\\_sub} (from glist bounds).\<close>
        have "glist ! (Suc i) \<le> n_sub"
          using hglist_sub nth_mem[OF hsi_len] by (by100 force)
        hence "k \<le> n_sub" using hk2 by linarith
        hence "k \<in> {0..<Suc n_sub}" by simp
        \<comment> \<open>If good k, then k \\<in> set glist.\<close>
        show "\<not> good k"
        proof
          assume "good k"
          hence "k \<in> set glist" unfolding glist_def
            using \<open>k \<in> {0..<Suc n_sub}\<close> hgn by auto
          then obtain j where hj: "j < length glist" "glist ! j = k"
            by (metis in_set_conv_nth)
          \<comment> \<open>k > glist[i] and k < glist[Suc i], but glist is sorted.\<close>
          have hi_len: "i < length glist" using hi m_ref_def hglist_len by linarith
          have "j > i"
          proof (rule ccontr)
            assume "\<not> j > i" hence "j \<le> i" by linarith
            hence "glist ! j \<le> glist ! i" by (rule sorted_nth_mono[OF hglist_sorted]) (use hi_len in auto)
            hence "k \<le> glist ! i" using hj(2) by linarith
            thus False using hk1 by linarith
          qed
          have "j \<le> Suc i"
          proof (rule ccontr)
            assume "\<not> j \<le> Suc i" hence "Suc i \<le> j" by linarith
            hence "glist ! (Suc i) \<le> glist ! j"
              by (rule sorted_nth_mono[OF hglist_sorted]) (use hj hsi_len in auto)
            hence "glist ! (Suc i) \<le> k" using hj(2) by linarith
            thus False using hk2 by linarith
          qed
          hence "j = Suc i" using \<open>j > i\<close> by linarith
          hence "k = glist ! (Suc i)" using hj(2) by simp
          thus False using hk2 by linarith
        qed
      qed
      have hpieces2: "\<forall>i<m_ref. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> f(sub2 i + t*(sub2 (Suc i) - sub2 i)) \<in> U) \<or>
               (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> f(sub2 i + t*(sub2 (Suc i) - sub2 i)) \<in> V)"
      proof (intro allI impI)
        fix i assume hi: "i < m_ref"
        have hi_len: "i < length glist" using hi m_ref_def hglist_len by linarith
        have hsi_len: "Suc i < length glist" using hi m_ref_def hglist_len by linarith
        define gi where "gi = glist ! i"
        define gsi where "gsi = glist ! (Suc i)"
        have hgi_lt: "gi < gsi" using sorted_nth_mono[OF hglist_sorted, of i "Suc i"] hsi_len
            nth_eq_iff_index_eq[OF hglist_distinct hi_len hsi_len] unfolding gi_def gsi_def by linarith
        have hgsi_le: "gsi \<le> n_sub"
          using hglist_sub nth_mem[OF hsi_len] unfolding gsi_def by (by100 force)
        have hno_good: "\<forall>k. gi < k \<longrightarrow> k < gsi \<longrightarrow> \<not> good k"
          using h_consec_no_good[OF hi] unfolding gi_def gsi_def .
        \<comment> \<open>All original pieces between gi and gsi are in same set.\<close>
        from h_all_same[OF hgi_lt hgsi_le hno_good]
        have h_same: "(\<forall>j. gi \<le> j \<longrightarrow> j < gsi \<longrightarrow> in_S j U) \<or>
            (\<forall>j. gi \<le> j \<longrightarrow> j < gsi \<longrightarrow> in_S j V)" .
        \<comment> \<open>Any t \\<in> [0,1] maps to s = sub2(i) + t*(sub2(i+1)-sub2(i)) \\<in> [sub\\_fn(gi), sub\\_fn(gsi)].\<close>
        have hgi_lt_sub: "sub_fn gi < sub_fn gsi" using hsub_strict[OF hgi_lt hgsi_le] .
        have h_s_bounds: "\<And>t. 0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow>
            sub_fn gi \<le> sub_fn gi + t * (sub_fn gsi - sub_fn gi) \<and>
            sub_fn gi + t * (sub_fn gsi - sub_fn gi) \<le> sub_fn gsi"
        proof -
          fix t :: real assume ht0: "0 \<le> t" and ht1: "t \<le> 1"
          have hd: "sub_fn gsi - sub_fn gi > 0" using hgi_lt_sub by linarith
          have "t * (sub_fn gsi - sub_fn gi) \<ge> 0" using ht0 hd by (by100 simp)
          moreover have "t * (sub_fn gsi - sub_fn gi) \<le> sub_fn gsi - sub_fn gi"
          proof -
            have "t * (sub_fn gsi - sub_fn gi) \<le> 1 * (sub_fn gsi - sub_fn gi)"
              by (rule mult_right_mono[OF ht1]) (use hd in linarith)
            thus ?thesis by simp
          qed
          ultimately show "sub_fn gi \<le> sub_fn gi + t * (sub_fn gsi - sub_fn gi) \<and>
              sub_fn gi + t * (sub_fn gsi - sub_fn gi) \<le> sub_fn gsi" by linarith
        qed
        show "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> f(sub2 i + t*(sub2 (Suc i) - sub2 i)) \<in> U) \<or>
              (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> f(sub2 i + t*(sub2 (Suc i) - sub2 i)) \<in> V)"
        proof -
          have hsub2_eq: "sub2 i = sub_fn gi" "sub2 (Suc i) = sub_fn gsi"
            unfolding sub2_def gi_def gsi_def by simp+
          from h_same show ?thesis
          proof
            assume hU: "\<forall>j. gi \<le> j \<longrightarrow> j < gsi \<longrightarrow> in_S j U"
            show ?thesis
            proof (intro disjI1 allI impI)
              fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
              define s where "s = sub_fn gi + t * (sub_fn gsi - sub_fn gi)"
              have hs_bounds: "sub_fn gi \<le> s" "s \<le> sub_fn gsi"
                unfolding s_def using h_s_bounds ht by blast+
              from hs_bounds obtain j where hj: "gi \<le> j" "j < gsi" "sub_fn j \<le> s" "s \<le> sub_fn (Suc j)"
                using h_value_in_piece[OF hgi_lt hgsi_le] by blast
              have "in_S j U" using hU hj(1,2) by blast
              \<comment> \<open>s \\<in> [sub\\_fn j, sub\\_fn(Suc j)]: express s as sub\\_fn j + t' * (sub\\_fn(Suc j) - sub\\_fn j).\<close>
              have hj_lt: "j < n_sub" using hj(2) hgsi_le by linarith
              have "sub_fn j < sub_fn (Suc j)" using hsub_inc hj_lt by blast
              define t' where "t' = (s - sub_fn j) / (sub_fn (Suc j) - sub_fn j)"
              have ht': "0 \<le> t'" "t' \<le> 1" unfolding t'_def
                using hj(3,4) \<open>sub_fn j < sub_fn (Suc j)\<close> by (simp_all add: divide_simps)
              have "s = sub_fn j + t' * (sub_fn (Suc j) - sub_fn j)" unfolding t'_def
                using \<open>sub_fn j < sub_fn (Suc j)\<close> by (simp add: field_simps)
              hence "f s \<in> U" using \<open>in_S j U\<close>[unfolded in_S_def] ht' by blast
              thus "f (sub2 i + t * (sub2 (Suc i) - sub2 i)) \<in> U"
                unfolding hsub2_eq s_def by blast
            qed
          next
            assume hV: "\<forall>j. gi \<le> j \<longrightarrow> j < gsi \<longrightarrow> in_S j V"
            show ?thesis
            proof (intro disjI2 allI impI)
              fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
              define s where "s = sub_fn gi + t * (sub_fn gsi - sub_fn gi)"
              have hs_bounds: "sub_fn gi \<le> s" "s \<le> sub_fn gsi"
                unfolding s_def using h_s_bounds ht by blast+
              from hs_bounds obtain j where hj: "gi \<le> j" "j < gsi" "sub_fn j \<le> s" "s \<le> sub_fn (Suc j)"
                using h_value_in_piece[OF hgi_lt hgsi_le] by blast
              have "in_S j V" using hV hj(1,2) by blast
              have hj_lt: "j < n_sub" using hj(2) hgsi_le by linarith
              have "sub_fn j < sub_fn (Suc j)" using hsub_inc hj_lt by blast
              define t' where "t' = (s - sub_fn j) / (sub_fn (Suc j) - sub_fn j)"
              have ht': "0 \<le> t'" "t' \<le> 1" unfolding t'_def
                using hj(3,4) \<open>sub_fn j < sub_fn (Suc j)\<close> by (simp_all add: divide_simps)
              have "s = sub_fn j + t' * (sub_fn (Suc j) - sub_fn j)" unfolding t'_def
                using \<open>sub_fn j < sub_fn (Suc j)\<close> by (simp add: field_simps)
              hence "f s \<in> V" using \<open>in_S j V\<close>[unfolded in_S_def] ht' by blast
              thus "f (sub2 i + t * (sub2 (Suc i) - sub2 i)) \<in> V"
                unfolding hsub2_eq s_def by blast
            qed
          qed
        qed
      qed
      show ?thesis
        apply (rule exI[of _ m_ref])
        apply (rule exI[of _ sub2])
        using hm_ge hsub2_0 hsub2_m hsub2_inc hsub2_UV hpieces2 by blast
    qed
    then obtain m sub2 where
      hm_pos: "m \<ge> 1" and hsub2_0: "sub2 0 = 0" and hsub2_m: "sub2 m = 1" and
      hsub2_inc: "\<forall>i<m. sub2 i < sub2 (Suc i)" and
      hsub2_UV: "\<forall>i\<le>m. f (sub2 i) \<in> U \<inter> V" and
      hpieces2_UV: "\<forall>i<m. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> f(sub2 i + t*(sub2 (Suc i) - sub2 i)) \<in> U) \<or>
             (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> f(sub2 i + t*(sub2 (Suc i) - sub2 i)) \<in> V)"
      by blast
    \<comment> \<open>Step 3-6: From refined subdivision, prove by strong induction on m.
       Main claim: any loop with m-piece refined subdivision gives a power of [\\<alpha>*\\<beta>].\<close>
    define gen_power where "gen_power g = (\<exists>n::nat. top1_path_homotopic_on X TX a a g
            (top1_path_power (top1_path_product \<alpha> \<beta>) a n)
          \<or> top1_path_homotopic_on X TX a a g
               (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n))" for g
    have h_from_refined_ind: "\<forall>k. \<forall>g sub3.
        k \<ge> 1 \<longrightarrow> top1_is_loop_on X TX a g \<longrightarrow>
        sub3 0 = 0 \<longrightarrow> sub3 k = 1 \<longrightarrow>
        (\<forall>i<k. sub3 i < sub3 (Suc i)) \<longrightarrow>
        (\<forall>i\<le>k. g (sub3 i) \<in> U \<inter> V) \<longrightarrow>
        (\<forall>i<k. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> U) \<or>
               (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> V)) \<longrightarrow>
        gen_power g"
    proof (rule allI, rule nat_less_induct)
      fix k :: nat
      assume IH: "\<forall>j<k. \<forall>g sub3.
          j \<ge> 1 \<longrightarrow> top1_is_loop_on X TX a g \<longrightarrow>
          sub3 0 = 0 \<longrightarrow> sub3 j = 1 \<longrightarrow>
          (\<forall>i<j. sub3 i < sub3 (Suc i)) \<longrightarrow>
          (\<forall>i\<le>j. g (sub3 i) \<in> U \<inter> V) \<longrightarrow>
          (\<forall>i<j. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> U) \<or>
                 (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> V)) \<longrightarrow>
          gen_power g"
      show "\<forall>g sub3. k \<ge> 1 \<longrightarrow> top1_is_loop_on X TX a g \<longrightarrow>
          sub3 0 = 0 \<longrightarrow> sub3 k = 1 \<longrightarrow>
          (\<forall>i<k. sub3 i < sub3 (Suc i)) \<longrightarrow>
          (\<forall>i\<le>k. g (sub3 i) \<in> U \<inter> V) \<longrightarrow>
          (\<forall>i<k. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> U) \<or>
                 (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> V)) \<longrightarrow>
          gen_power g"
      proof (intro allI impI)
        fix g :: "real \<Rightarrow> 'a" and sub3 :: "nat \<Rightarrow> real"
        assume hk: "k \<ge> 1" and hg_loop: "top1_is_loop_on X TX a g"
          and hs0: "sub3 0 = 0" and hsk: "sub3 k = 1"
          and hs_inc: "\<forall>i<k. sub3 i < sub3 (Suc i)"
          and hs_UV: "\<forall>i\<le>k. g (sub3 i) \<in> U \<inter> V"
          and hs_pieces: "\<forall>i<k. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> U) \<or>
                 (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> V)"
        show "gen_power g"
        proof (cases "k = 1")
          case True
          \<comment> \<open>Base: k=1, loop entirely in U or V. SC \\<Rightarrow> null-homotopic = power 0.\<close>
          have "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> U) \<or>
                (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> V)"
            using hs_pieces True by (by100 force)
          hence hg_in: "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g t \<in> U) \<or> (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g t \<in> V)"
            using hs0 hsk True by simp
          have "\<exists>n::nat. top1_path_homotopic_on X TX a a g
              (top1_path_power (top1_path_product \<alpha> \<beta>) a n)"
          proof (rule exI[of _ 0])
            have "top1_path_power (top1_path_product \<alpha> \<beta>) a 0 = top1_constant_path a"
              by (by100 simp)
            moreover have "top1_path_homotopic_on X TX a a g (top1_constant_path a)"
            proof -
              have ha_U_loc: "a \<in> U" using hUV_split ha by (by100 blast)
              have ha_V_loc: "a \<in> V" using hUV_split ha by (by100 blast)
              have hU_sub_loc: "U \<subseteq> X" using hU_open unfolding openin_on_def by (by100 blast)
              have hV_sub_loc: "V \<subseteq> X" using hV_open unfolding openin_on_def by (by100 blast)
              have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
                using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
              have hg0: "g 0 = a" using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                by (by100 blast)
              have hg1: "g 1 = a" using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                by (by100 blast)
              show ?thesis
              proof (cases "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g t \<in> U")
                case True
                have hg_img_U: "\<forall>s \<in> I_set. g s \<in> U"
                proof (intro ballI)
                  fix s assume "s \<in> I_set"
                  hence "0 \<le> s \<and> s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)
                  thus "g s \<in> U" using True by blast
                qed
                have hg_cont_U: "top1_continuous_map_on I_set I_top U (subspace_topology X TX U) g"
                  by (rule continuous_map_restrict_codomain[OF hg_cont hg_img_U hU_sub_loc])
                have hg_loop_U: "top1_is_loop_on U (subspace_topology X TX U) a g"
                  unfolding top1_is_loop_on_def top1_is_path_on_def
                  using hg_cont_U ha_U_loc hg0 hg1 hg_img_U by (by100 blast)
                have "top1_path_homotopic_on U (subspace_topology X TX U) a a g (top1_constant_path a)"
                  using hU_sc hg_loop_U ha_U_loc
                  unfolding top1_simply_connected_on_def by (by100 blast)
                thus ?thesis
                  using path_homotopic_subspace_to_ambient[OF hTX_top hU_sub_loc _
                      \<open>top1_path_homotopic_on U (subspace_topology X TX U) a a g (top1_constant_path a)\<close>]
                  by (by100 simp)
              next
                case False
                hence "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g t \<in> V" using hg_in by blast
                have hg_img_V: "\<forall>s \<in> I_set. g s \<in> V"
                proof (intro ballI)
                  fix s assume "s \<in> I_set"
                  hence "0 \<le> s \<and> s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)
                  thus "g s \<in> V" using \<open>\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g t \<in> V\<close> by blast
                qed
                have hg_cont_V: "top1_continuous_map_on I_set I_top V (subspace_topology X TX V) g"
                  by (rule continuous_map_restrict_codomain[OF hg_cont hg_img_V hV_sub_loc])
                have hg_loop_V: "top1_is_loop_on V (subspace_topology X TX V) a g"
                  unfolding top1_is_loop_on_def top1_is_path_on_def
                  using hg_cont_V ha_V_loc hg0 hg1 hg_img_V by (by100 blast)
                have "top1_path_homotopic_on V (subspace_topology X TX V) a a g (top1_constant_path a)"
                  using hV_sc hg_loop_V ha_V_loc
                  unfolding top1_simply_connected_on_def by (by100 blast)
                thus ?thesis
                  using path_homotopic_subspace_to_ambient[OF hTX_top hV_sub_loc _
                      \<open>top1_path_homotopic_on V (subspace_topology X TX V) a a g (top1_constant_path a)\<close>]
                  by (by100 simp)
              qed
            qed
            ultimately show "top1_path_homotopic_on X TX a a g
                (top1_path_power (top1_path_product \<alpha> \<beta>) a 0)" by simp
          qed
          thus ?thesis unfolding gen_power_def by blast
        next
          case False
          hence hk_ge2: "k \<ge> 2" using hk by linarith
          \<comment> \<open>Inductive case k \\<ge> 2. Use book proof:
             g(sub3(1)) \\<in> U\\<inter>V = A\\<union>B. Choose connecting path \\<gamma> in A or B.
             Case A: \\<gamma> from a to g(sub3(1)) in A.
               First piece g|[0,sub3(1)] ~ \\<gamma> in U (SC). Merge \\<gamma>*piece\\_2 \\<subseteq> V. Apply IH(k-1).
             Case B: \\<gamma> from b to g(sub3(1)) in B.
               First piece g|[0,sub3(1)] * \\<gamma>\\_bar ~ \\<alpha> in U (SC).
               Then g ~ \\<alpha>*\\<beta>*(loop with k-1 pieces). Apply IH(k-1).
               Combine: gen\\_power g follows from IH result + one \\<alpha>*\\<beta> factor.\<close>
          \<comment> \<open>g(sub3(1)) \\<in> U\\<inter>V = A\\<union>B since 1 \\<le> k.\<close>
          have hx1_UV: "g (sub3 1) \<in> U \<inter> V" using hs_UV hk_ge2 by (by100 force)
          hence hx1_AB: "g (sub3 1) \<in> A \<or> g (sub3 1) \<in> B" using hUV_split by (by100 blast)
          \<comment> \<open>First piece type: in U or V.\<close>
          have hpiece0: "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> U) \<or>
                (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> V)"
            using hs_pieces hk_ge2 by (by100 force)
          \<comment> \<open>Useful: sub3(0) = 0, g(0) = a, a \\<in> A \\<subseteq> U\\<inter>V.\<close>
          have hg0: "g 0 = a"
            using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have hg1: "g 1 = a"
            using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have hU_sub_loc: "U \<subseteq> X" using hU_open unfolding openin_on_def by (by100 blast)
          have hV_sub_loc: "V \<subseteq> X" using hV_open unfolding openin_on_def by (by100 blast)
          have ha_U_loc: "a \<in> U" using hUV_split ha by (by100 blast)
          have ha_V_loc: "a \<in> V" using hUV_split ha by (by100 blast)
          \<comment> \<open>Apply IH. Need: k-1 \\<ge> 1 and k-1 < k.\<close>
          have hk_m1_lt: "k - 1 < k" using hk_ge2 by linarith
          have hk_m1_ge: "k - 1 \<ge> 1" using hk_ge2 by linarith
          \<comment> \<open>Case analysis on g(sub3(1)) \\<in> A vs B.\<close>
          show "gen_power g"
          proof (cases "g (sub3 1) \<in> A")
            case True
            \<comment> \<open>Case A: g(sub3(1)) \\<in> A. Connect a to g(sub3(1)) in A.
               First piece goes a\\<rightarrow>g(sub3(1)) in U (or V).
               SC implies piece\\_1 ~ connecting path \\<gamma> in A.
               Then g ~ \\<gamma> * piece\\_2 * ... which has k-1 effective pieces.
               The merged \\<gamma>*piece\\_2 lies in the SAME set as piece\\_2 (since \\<gamma>\\<subseteq>A\\<subseteq>U\\<inter>V).
               So we get k-1 pieces. Apply IH.\<close>
            \<comment> \<open>Case A: there exists g' homotopic to g with k-1 pieces.
               g' = \\<gamma> * g\\_tail where \\<gamma> is connecting path in A,
               and \\<gamma>*piece\\_1 merged into one piece.\<close>
            \<comment> \<open>Step 1: Split g at sub3(1) using path\\_product\\_split.\<close>
            have hsub31_pos: "0 < sub3 1" using hs_inc hs0 hk_ge2 by (by100 force)
            have hsub3_strict: "\<And>i j. i < j \<Longrightarrow> j \<le> k \<Longrightarrow> sub3 i < sub3 j"
            proof -
              fix i j :: nat assume "i < j" "j \<le> k"
              thus "sub3 i < sub3 j"
              proof (induction j)
                case 0 thus ?case by simp
              next
                case (Suc j) show ?case
                proof (cases "i = j")
                  case True thus ?thesis using hs_inc Suc.prems by simp
                next
                  case False hence "sub3 i < sub3 j" using Suc by linarith
                  also have "sub3 j < sub3 (Suc j)" using hs_inc Suc.prems by simp
                  finally show ?thesis .
                qed
              qed
            qed
            have hsub31_lt1: "sub3 1 < 1"
              using hsub3_strict[of 1 k] hk_ge2 hsk by linarith
            define g_L where "g_L = (\<lambda>t. g (sub3 1 * t))"
            define g_R where "g_R = (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))"
            have hg_path: "top1_is_path_on X TX a a g"
              using hg_loop unfolding top1_is_loop_on_def by (by100 blast)
            have hg_split: "top1_path_homotopic_on X TX a a g (top1_path_product g_L g_R)"
              unfolding g_L_def g_R_def
              by (rule path_product_split[OF hTX_top hg_path hsub31_pos hsub31_lt1])
            \<comment> \<open>Step 2: g\\_L goes from a to g(sub3(1)), same as piece 0.
               \\<gamma> also goes from a to g(sub3(1)) in A.
               Both in U (or V) since A \\<subseteq> U\\<inter>V. SC gives g\\_L ~ \\<gamma>.\<close>
            have hx1_A_loc: "g (sub3 1) \<in> A" using True .
            have ha_A_loc: "a \<in> A" using ha .
            have hA_pc_loc: "top1_path_connected_on A (subspace_topology X TX A)" using hA_pc .
            obtain \<gamma> where h\<gamma>: "top1_is_path_on A (subspace_topology X TX A) a (g (sub3 1)) \<gamma>"
              using hA_pc_loc ha_A_loc hx1_A_loc
              unfolding top1_path_connected_on_def by blast
            \<comment> \<open>g\\_L is a path from a to g(sub3(1)) in X.\<close>
            have hgL_path: "top1_is_path_on X TX a (g (sub3 1)) g_L"
            proof -
              \<comment> \<open>g\\_L is one of the two factors from path\\_product\\_split.
                 From hg\\_split, g ~ g\\_L * g\\_R. Since g is a path a\\<rightarrow>a, the split gives
                 g\\_L: a\\<rightarrow>g(sub3(1)) and g\\_R: g(sub3(1))\\<rightarrow>a.\<close>
              from path_product_split[OF hTX_top hg_path hsub31_pos hsub31_lt1]
              have "top1_path_homotopic_on X TX a a g (top1_path_product (\<lambda>t. g (sub3 1 * t))
                  (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t)))" .
              \<comment> \<open>From this homotopy, g\\_L and g\\_R are paths. Extract path property.\<close>
              \<comment> \<open>g\\_L(t) = g(sub3(1)*t) = (g \\<circ> (\\<lambda>t. 0 + t*(sub3(1)-0)))(t).\<close>
              have hg_cont_loop: "top1_continuous_map_on I_set I_top X TX g"
                using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
              have haffL: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. t * sub3 1)"
              proof -
                have "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 0 + t * (sub3 1 - 0))"
                  by (rule affine_map_continuous_I_to_I) (use hsub31_pos hsub31_lt1 in linarith)+
                thus ?thesis by simp
              qed
              have "top1_continuous_map_on I_set I_top X TX (g \<circ> (\<lambda>t. t * sub3 1))"
                by (rule top1_continuous_map_on_comp[OF haffL hg_cont_loop])
              moreover have "(g \<circ> (\<lambda>t. t * sub3 1)) = (\<lambda>t. g (sub3 1 * t))"
                by (rule ext) (simp add: mult.commute)
              ultimately have "top1_continuous_map_on I_set I_top X TX (\<lambda>t. g (sub3 1 * t))" by simp
              moreover have "(\<lambda>t. g (sub3 1 * t)) 0 = a" using hg0 by simp
              moreover have "(\<lambda>t. g (sub3 1 * t)) 1 = g (sub3 1)" by simp
              ultimately show ?thesis unfolding g_L_def top1_is_path_on_def by blast
            qed
            \<comment> \<open>\\<gamma> is also a path from a to g(sub3(1)) in X.\<close>
            have hA_sub_X: "A \<subseteq> X"
              using hA_open unfolding openin_on_def by (by100 blast)
            have h\<gamma>_X: "top1_is_path_on X TX a (g (sub3 1)) \<gamma>"
              by (rule path_in_subspace_is_path_in_ambient[OF hTX_top hA_sub_X h\<gamma>])
            \<comment> \<open>g\\_L ~ \\<gamma> in X (from SC of U or V, both contain g\\_L and \\<gamma>).\<close>
            have hgL_htpy_\<gamma>: "top1_path_homotopic_on X TX a (g (sub3 1)) g_L \<gamma>"
            proof -
              \<comment> \<open>Piece 0 of g is in U or V. g\\_L = reparametrized piece 0.
                 \\<gamma> is in A \\<subseteq> U\\<inter>V \\<subseteq> U and V. Both go a\\<rightarrow>g(sub3(1)) in the same SC space.\<close>
              have hpiece0_reparam: "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> U) \<or>
                    (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> V)"
                using hs_pieces hk_ge2 by (by100 force)
              \<comment> \<open>sub3(0) = 0, so piece 0 is g(t*(sub3(1))) = g\\_L(t).\<close>
              have hsimp: "\<And>t. g(sub3 0 + t*(sub3 1 - sub3 0)) = g_L t"
                unfolding g_L_def using hs0 by (simp add: mult.commute)
              hence hgL_in: "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g_L t \<in> U) \<or> (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g_L t \<in> V)"
                using hpiece0_reparam by (simp add: mult.commute)
              show ?thesis
              proof (cases "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g_L t \<in> U")
                case True
                \<comment> \<open>g\\_L maps [0,1] into U. \\<gamma> maps [0,1] into A \\<subseteq> U.\<close>
                have hgL_U: "top1_is_path_on U (subspace_topology X TX U) a (g (sub3 1)) g_L"
                proof -
                  have hgL_img: "\<forall>s \<in> I_set. g_L s \<in> U"
                  proof (intro ballI)
                    fix s assume "s \<in> I_set"
                    hence "0 \<le> s \<and> s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)
                    thus "g_L s \<in> U" using True by blast
                  qed
                  have hgL_cont: "top1_continuous_map_on I_set I_top X TX g_L"
                    using hgL_path unfolding top1_is_path_on_def by (by100 blast)
                  have "top1_continuous_map_on I_set I_top U (subspace_topology X TX U) g_L"
                    by (rule continuous_map_restrict_codomain[OF hgL_cont hgL_img hU_sub_loc])
                  thus ?thesis unfolding top1_is_path_on_def
                    using ha_U_loc hgL_path[unfolded top1_is_path_on_def] by blast
                qed
                have h\<gamma>_U: "top1_is_path_on U (subspace_topology X TX U) a (g (sub3 1)) \<gamma>"
                proof -
                  have "A \<subseteq> U" using hUV_split by (by100 blast)
                  from top1_continuous_map_on_codomain_enlarge[OF
                      h\<gamma>[unfolded top1_is_path_on_def, THEN conjunct1] \<open>A \<subseteq> U\<close> hU_sub_loc]
                  have "top1_continuous_map_on I_set I_top U (subspace_topology X TX U) \<gamma>" .
                  thus ?thesis unfolding top1_is_path_on_def
                    using ha_U_loc h\<gamma>[unfolded top1_is_path_on_def] by blast
                qed
                from simply_connected_paths_homotopic[OF hU_sc hgL_U h\<gamma>_U ha_U_loc]
                have "top1_path_homotopic_on U (subspace_topology X TX U) a (g (sub3 1)) g_L \<gamma>" .
                from path_homotopic_subspace_to_ambient[OF hTX_top hU_sub_loc _ this]
                show ?thesis by (by100 simp)
              next
                case False
                hence "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g_L t \<in> V" using hgL_in by blast
                \<comment> \<open>Symmetric: g\\_L and \\<gamma> both in V, SC of V.\<close>
                have hgL_V: "top1_is_path_on V (subspace_topology X TX V) a (g (sub3 1)) g_L"
                proof -
                  have hgL_img: "\<forall>s \<in> I_set. g_L s \<in> V"
                  proof (intro ballI)
                    fix s assume "s \<in> I_set"
                    hence "0 \<le> s \<and> s \<le> 1" unfolding top1_unit_interval_def by (by100 simp)
                    thus "g_L s \<in> V" using \<open>\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g_L t \<in> V\<close> by blast
                  qed
                  have hgL_cont2: "top1_continuous_map_on I_set I_top X TX g_L"
                    using hgL_path unfolding top1_is_path_on_def by (by100 blast)
                  have "top1_continuous_map_on I_set I_top V (subspace_topology X TX V) g_L"
                    by (rule continuous_map_restrict_codomain[OF hgL_cont2 hgL_img hV_sub_loc])
                  thus ?thesis unfolding top1_is_path_on_def
                    using ha_V_loc hgL_path[unfolded top1_is_path_on_def] by blast
                qed
                have h\<gamma>_V: "top1_is_path_on V (subspace_topology X TX V) a (g (sub3 1)) \<gamma>"
                proof -
                  have "A \<subseteq> V" using hUV_split by (by100 blast)
                  from top1_continuous_map_on_codomain_enlarge[OF
                      h\<gamma>[unfolded top1_is_path_on_def, THEN conjunct1] \<open>A \<subseteq> V\<close> hV_sub_loc]
                  have "top1_continuous_map_on I_set I_top V (subspace_topology X TX V) \<gamma>" .
                  thus ?thesis unfolding top1_is_path_on_def
                    using ha_V_loc h\<gamma>[unfolded top1_is_path_on_def] by blast
                qed
                from simply_connected_paths_homotopic[OF hV_sc hgL_V h\<gamma>_V ha_V_loc]
                have "top1_path_homotopic_on V (subspace_topology X TX V) a (g (sub3 1)) g_L \<gamma>" .
                from path_homotopic_subspace_to_ambient[OF hTX_top hV_sub_loc _ this]
                show ?thesis by (by100 simp)
              qed
            qed
            \<comment> \<open>Step 3: g ~ g\\_L * g\\_R ~ \\<gamma> * g\\_R.\<close>
            have hgR_path: "top1_is_path_on X TX (g (sub3 1)) a g_R"
            proof -
              have hg_cont_loop2: "top1_continuous_map_on I_set I_top X TX g"
                using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
              have haffR: "top1_continuous_map_on I_set I_top I_set I_top
                  (\<lambda>t. sub3 1 + t * (1 - sub3 1))"
                by (rule affine_map_continuous_I_to_I) (use hsub31_pos hsub31_lt1 in linarith)+
              have "top1_continuous_map_on I_set I_top X TX (g \<circ> (\<lambda>t. sub3 1 + t * (1 - sub3 1)))"
                by (rule top1_continuous_map_on_comp[OF haffR hg_cont_loop2])
              moreover have "(g \<circ> (\<lambda>t. sub3 1 + t * (1 - sub3 1))) = g_R"
                unfolding g_R_def by (rule ext) (simp add: algebra_simps)
              ultimately have "top1_continuous_map_on I_set I_top X TX g_R" by simp
              moreover have "g_R 0 = g (sub3 1)" unfolding g_R_def by simp
              moreover have "g_R 1 = a" unfolding g_R_def using hg1 by simp
              ultimately show ?thesis unfolding top1_is_path_on_def by blast
            qed
            have hg_htpy_\<gamma>gR: "top1_path_homotopic_on X TX a a g (top1_path_product \<gamma> g_R)"
            proof -
              \<comment> \<open>g ~ g\\_L * g\\_R (from hg\\_split).\<close>
              \<comment> \<open>g\\_L ~ \\<gamma> (from hgL\\_htpy\\_\\<gamma>). So g\\_L * g\\_R ~ \\<gamma> * g\\_R.\<close>
              have "top1_path_homotopic_on X TX a a (top1_path_product g_L g_R) (top1_path_product \<gamma> g_R)"
                by (rule path_homotopic_product_left[OF hTX_top hgL_htpy_\<gamma> hgR_path])
              from Lemma_51_1_path_homotopic_trans[OF hTX_top hg_split this]
              show ?thesis .
            qed
            \<comment> \<open>Step 4: \\<gamma> * g\\_R is a loop at a with k-1 effective pieces.\<close>
            define g' where "g' = top1_path_product \<gamma> g_R"
            have hg'_loop: "top1_is_loop_on X TX a g'"
            proof -
              have "top1_is_path_on X TX a a (top1_path_product \<gamma> g_R)"
                by (rule top1_path_product_is_path[OF hTX_top h\<gamma>_X hgR_path])
              thus ?thesis unfolding g'_def top1_is_loop_on_def by (by100 blast)
            qed
            \<comment> \<open>Step 5: Construct subdivision for g' with k-1 pieces.\<close>
            \<comment> \<open>Define sub3' explicitly: rescale original subdivision to g' parametrization.\<close>
            let ?d = "1 - sub3 1" \<comment> \<open>length of g\\_R domain interval\<close>
            have hd_pos: "?d > 0" using hsub31_lt1 by linarith
            define sub3' where "sub3' j = (if j = 0 then 0
                else 1/2 + (sub3 (j+1) - sub3 1) / (2 * ?d))" for j
            have "\<exists>sub3'. (k-1) \<ge> 1 \<and> sub3' 0 = 0 \<and> sub3' (k-1) = 1 \<and>
                (\<forall>i<k-1. sub3' i < sub3' (Suc i)) \<and>
                (\<forall>i\<le>k-1. g' (sub3' i) \<in> U \<inter> V) \<and>
                (\<forall>i<k-1. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U) \<or>
                       (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V))"
            proof (rule exI[of _ sub3'])
              have hsub3'_0: "sub3' 0 = 0" unfolding sub3'_def by simp
              have hsub3'_km1: "sub3' (k-1) = 1"
              proof -
                have "sub3' (k-1) = 1/2 + (sub3 ((k-1)+1) - sub3 1) / (2 * ?d)"
                  unfolding sub3'_def using hk_ge2 by simp
                also have "(k-1)+1 = k" using hk_ge2 by linarith
                also have "sub3 k = 1" using hsk .
                finally show ?thesis using hd_pos by (simp add: field_simps)
              qed
              have hsub3'_mono: "\<forall>i<k-1. sub3' i < sub3' (Suc i)"
              proof (intro allI impI)
                fix i assume hi: "i < k - 1"
                show "sub3' i < sub3' (Suc i)"
                proof (cases "i = 0")
                  case True
                  have "sub3' 0 = 0" using hsub3'_0 by simp
                  moreover have "sub3' (Suc 0) > 0"
                  proof -
                    have "sub3' (Suc 0) = 1/2 + (sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d)"
                      unfolding sub3'_def by simp
                    moreover have "(sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d) \<ge> 0"
                    proof -
                      have "sub3 (Suc 0 + 1) \<ge> sub3 1"
                        using hsub3_strict[of 1 "Suc 0 + 1"] hk_ge2 by linarith
                      thus ?thesis using hd_pos by (by100 simp)
                    qed
                    ultimately show ?thesis by linarith
                  qed
                  ultimately show ?thesis using True by simp
                next
                  case False hence "i \<ge> 1" by linarith
                  have hi_ne0: "i \<noteq> 0" using False by simp
                  have hsi_ne0: "Suc i \<noteq> 0" by simp
                  have hv1: "sub3' i = 1/2 + (sub3 (i+1) - sub3 1) / (2 * ?d)"
                    unfolding sub3'_def using hi_ne0 by auto
                  have hv2: "sub3' (Suc i) = 1/2 + (sub3 (Suc i + 1) - sub3 1) / (2 * ?d)"
                    unfolding sub3'_def using hsi_ne0 by auto
                  have "sub3 (i+1) < sub3 (Suc i + 1)"
                    using hsub3_strict[of "i+1" "Suc i + 1"] hi hk_ge2 by linarith
                  hence "(sub3 (i+1) - sub3 1) / (2 * ?d) < (sub3 (Suc i + 1) - sub3 1) / (2 * ?d)"
                  proof -
                    have "0 < 2 * ?d"
                    proof -
                      from hd_pos have "(0::real) < 1 - sub3 1" .
                      hence "(0::real) < 2 - 2 * sub3 1" by linarith
                      thus ?thesis by (simp add: algebra_simps)
                    qed
                    thus ?thesis using \<open>sub3 (i+1) < sub3 (Suc i+1)\<close>
                      by (intro divide_strict_right_mono) linarith+
                  qed
                  thus ?thesis using hv1 hv2 by linarith
                qed
              qed
              have pp_gt: "\<And>s::real. s > 1/2 \<Longrightarrow> g' s = g_R (2*s - 1)"
                unfolding g'_def top1_path_product_def by simp
              have hsub3'_gt: "\<And>j. j \<ge> 1 \<Longrightarrow> j \<le> k-1 \<Longrightarrow> sub3' j > 1/2"
              proof -
                fix j :: nat assume "j \<ge> 1" "j \<le> k-1"
                have "sub3' j = 1/2 + (sub3 (j+1) - sub3 1) / (2 * ?d)"
                  unfolding sub3'_def using \<open>j \<ge> 1\<close> by auto
                moreover have "sub3 (j+1) > sub3 1"
                  using hsub3_strict[of 1 "j+1"] \<open>j \<ge> 1\<close> \<open>j \<le> k-1\<close> hk_ge2 by linarith
                hence "(sub3 (j+1) - sub3 1) / (2 * ?d) > 0" using hd_pos by (by100 simp)
                ultimately show "sub3' j > 1/2" by linarith
              qed
              have hg'_val: "\<And>j. j \<ge> 1 \<Longrightarrow> j \<le> k-1 \<Longrightarrow> g' (sub3' j) = g (sub3 (j+1))"
              proof -
                fix j :: nat assume hj1: "j \<ge> 1" and hj2: "j \<le> k-1"
                \<comment> \<open>Step 1: g'(sub3'(j)) = g\\_R(2*sub3'(j) - 1) since sub3'(j) > 1/2.\<close>
                have "g' (sub3' j) = g_R (2 * sub3' j - 1)"
                  by (rule pp_gt[OF hsub3'_gt[OF hj1 hj2]])
                \<comment> \<open>Step 2: g\\_R(u) = g(sub3(1) + (1-sub3(1))*u). Compute at u = 2*sub3'(j)-1.\<close>
                also have "g_R (2 * sub3' j - 1) = g (sub3 1 + ?d * (2 * sub3' j - 1))"
                  unfolding g_R_def by (simp add: mult.commute)
                \<comment> \<open>Step 3: sub3(1) + d*(2*sub3'(j)-1) = sub3(j+1).\<close>
                also have "sub3 1 + ?d * (2 * sub3' j - 1) = sub3 (j+1)"
                proof -
                  have hval: "sub3' j = 1/2 + (sub3 (j+1) - sub3 1) / (2 * ?d)"
                    unfolding sub3'_def using hj1 by auto
                  \<comment> \<open>Compute: d*(2*(1/2 + x/(2d)) - 1) = d*(x/d) = x.\<close>
                  have "2 * sub3' j - 1 = (sub3 (j+1) - sub3 1) / ?d"
                  proof -
                    from hval have "2 * sub3' j = 1 + 2 * ((sub3 (j+1) - sub3 1) / (2 * ?d))"
                      by linarith
                    also have "2 * ((sub3 (j+1) - sub3 1) / (2 * ?d)) = (sub3 (j+1) - sub3 1) / ?d"
                    proof -
                      have "?d \<noteq> (0::real)" using hd_pos by linarith
                      have "(2::real) \<noteq> 0" by simp
                      show ?thesis
                        using mult_divide_mult_cancel_left[OF \<open>(2::real) \<noteq> 0\<close>,
                            of "sub3 (j+1) - sub3 1" "?d"] \<open>?d \<noteq> 0\<close>
                        by (by100 simp)
                    qed
                    finally show ?thesis by linarith
                  qed
                  hence "?d * (2 * sub3' j - 1) = sub3 (j+1) - sub3 1"
                    using hd_pos by (by100 simp)
                  thus ?thesis by linarith
                qed
                finally show "g' (sub3' j) = g (sub3 (j+1))" .
              qed
              have hsub3'_UV: "\<forall>i\<le>k-1. g' (sub3' i) \<in> U \<inter> V"
              proof (intro allI impI)
                fix i assume hi: "i \<le> k - 1"
                show "g' (sub3' i) \<in> U \<inter> V"
                proof (cases "i = 0")
                  case True
                  have "g' 0 = \<gamma> 0"
                    by (rule top1_path_product_at_start[of \<gamma> g_R, folded g'_def])
                  also have "\<gamma> 0 = a" using h\<gamma> unfolding top1_is_path_on_def by (by100 blast)
                  finally have "g' (sub3' i) = a" using True hsub3'_0 by simp
                  thus ?thesis using hUV_split ha by (by100 blast)
                next
                  case False hence "i \<ge> 1" by linarith
                  have "g' (sub3' i) = g (sub3 (i+1))" by (rule hg'_val[OF \<open>i \<ge> 1\<close> hi])
                  moreover have "g (sub3 (i+1)) \<in> U \<inter> V"
                    using hs_UV[rule_format, of "i+1"] hi hk_ge2 by linarith
                  ultimately show ?thesis by simp
                qed
              qed
              \<comment> \<open>For j\\<ge>1: g'(sub3'(j)+t*\\<Delta>') = g(sub3(j+1)+t*(sub3(j+2)-sub3(j+1))) = piece j+1 of g.\<close>
              have hpiece_j_ge1: "\<And>j t. j \<ge> 1 \<Longrightarrow> j < k-1 \<Longrightarrow> 0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow>
                  g' (sub3' j + t * (sub3' (Suc j) - sub3' j)) =
                  g (sub3 (j+1) + t * (sub3 (Suc j + 1) - sub3 (j+1)))"
              proof -
                fix j :: nat and t :: real
                assume hj1: "j \<ge> 1" and hjk: "j < k-1" and ht0: "0 \<le> t" and ht1: "t \<le> 1"
                \<comment> \<open>Step 1: sub3'(j) + t*\\<Delta>' > 1/2.\<close>
                have hgt: "sub3' j + t * (sub3' (Suc j) - sub3' j) > 1/2"
                proof -
                  have "sub3' j > 1/2" by (rule hsub3'_gt[OF hj1]) (use hjk in linarith)
                  moreover have "sub3' (Suc j) \<ge> sub3' j"
                    using hsub3'_mono[rule_format, of j] hjk by linarith
                  hence "t * (sub3' (Suc j) - sub3' j) \<ge> 0" using ht0 by (by100 simp)
                  ultimately show ?thesis by linarith
                qed
                \<comment> \<open>Step 2: g' at that point = g\\_R(2*(...) - 1).\<close>
                have "g' (sub3' j + t * (sub3' (Suc j) - sub3' j)) =
                    g_R (2 * (sub3' j + t * (sub3' (Suc j) - sub3' j)) - 1)"
                  by (rule pp_gt[OF hgt])
                \<comment> \<open>Step 3: g\\_R(u) = g(sub3(1) + ?d*u).\<close>
                also have "... = g (sub3 1 + ?d * (2 * (sub3' j + t * (sub3' (Suc j) - sub3' j)) - 1))"
                  unfolding g_R_def by (simp add: mult.commute)
                \<comment> \<open>Step 4: sub3(1) + ?d*(...) = sub3(j+1) + t*(sub3(j+2)-sub3(j+1)).\<close>
                also have "sub3 1 + ?d * (2 * (sub3' j + t * (sub3' (Suc j) - sub3' j)) - 1) =
                    sub3 (j+1) + t * (sub3 (Suc j + 1) - sub3 (j+1))"
                proof -
                  \<comment> \<open>Expand: ?d*(2*(sub3'(j)+t*\\<Delta>')-1) = ?d*(2*sub3'(j)-1) + 2*?d*t*\\<Delta>'.\<close>
                  have "?d * (2 * (sub3' j + t * (sub3' (Suc j) - sub3' j)) - 1) =
                      ?d * (2 * sub3' j - 1) + 2 * ?d * t * (sub3' (Suc j) - sub3' j)"
                    by (simp add: algebra_simps)
                  \<comment> \<open>?d*(2*sub3'(j)-1) = sub3(j+1) - sub3(1).\<close>
                  moreover have "?d * (2 * sub3' j - 1) = sub3 (j+1) - sub3 1"
                  proof -
                    have "2 * sub3' j - 1 = (sub3 (j+1) - sub3 1) / ?d"
                    proof -
                      have hval: "sub3' j = 1/2 + (sub3 (j+1) - sub3 1) / (2 * ?d)"
                        unfolding sub3'_def using hj1 by auto
                      from hval have "2 * sub3' j = 1 + 2 * ((sub3 (j+1) - sub3 1) / (2 * ?d))"
                        by linarith
                      also have "2 * ((sub3 (j+1) - sub3 1) / (2 * ?d)) = (sub3 (j+1) - sub3 1) / ?d"
                      proof -
                        have "2 * (sub3 (j+1) - sub3 1) / (2 * ?d) = (sub3 (j+1) - sub3 1) / ?d"
                          using mult_divide_mult_cancel_left[of "(2::real)" "sub3 (j+1) - sub3 1" "?d"]
                            hd_pos by linarith
                        moreover have "2 * ((sub3 (j+1) - sub3 1) / (2 * ?d)) =
                            2 * (sub3 (j+1) - sub3 1) / (2 * ?d)"
                          by simp
                        ultimately show ?thesis by simp
                      qed
                      finally show ?thesis by linarith
                    qed
                    thus ?thesis using hd_pos by (by100 simp)
                  qed
                  \<comment> \<open>2*?d*\\<Delta>' = sub3(j+2)-sub3(j+1).\<close>
                  moreover have "2 * ?d * (sub3' (Suc j) - sub3' j) = sub3 (Suc j + 1) - sub3 (j+1)"
                  proof -
                    have hsi_ne: "Suc j \<noteq> 0" by simp
                    have hj_ne: "j \<noteq> 0" using hj1 by linarith
                    have "sub3' (Suc j) - sub3' j =
                        (sub3 (Suc j + 1) - sub3 1) / (2 * ?d) - (sub3 (j+1) - sub3 1) / (2 * ?d)"
                      unfolding sub3'_def using hsi_ne hj_ne by auto
                    also have "... = (sub3 (Suc j + 1) - sub3 (j+1)) / (2 * ?d)"
                      using hd_pos by (simp add: diff_divide_distrib)
                    finally have "sub3' (Suc j) - sub3' j = (sub3 (Suc j + 1) - sub3 (j+1)) / (2 * ?d)" .
                    hence "2 * ?d * (sub3' (Suc j) - sub3' j) =
                        2 * ?d * ((sub3 (Suc j + 1) - sub3 (j+1)) / (2 * ?d))" by simp
                    also have "... = sub3 (Suc j + 1) - sub3 (j+1)"
                    proof -
                      from hd_pos have "0 < 2 - 2 * sub3 1" by linarith
                      hence h2d_ne: "(2 * ?d) \<noteq> (0::real)" by (simp add: algebra_simps)
                      show ?thesis using nonzero_mult_div_cancel_left[OF h2d_ne] by simp
                    qed
                    finally show ?thesis .
                  qed
                  \<comment> \<open>Combine: expand ?d*(...), substitute eq1 and eq2, simplify.\<close>
                  \<comment> \<open>Expand the LHS and substitute.\<close>
                  moreover have h_expand: "?d * (2 * (sub3' j + t * (sub3' (Suc j) - sub3' j)) - 1) =
                      ?d * (2 * sub3' j - 1) + 2 * ?d * t * (sub3' (Suc j) - sub3' j)"
                    by (simp add: algebra_simps)
                  moreover have "2 * ?d * t * (sub3' (Suc j) - sub3' j) =
                      t * (sub3 (Suc j + 1) - sub3 (j+1))"
                  proof -
                    have "2 * ?d * (sub3' (Suc j) - sub3' j) = sub3 (Suc j + 1) - sub3 (j+1)"
                      by fact
                    hence "t * (2 * ?d * (sub3' (Suc j) - sub3' j)) = t * (sub3 (Suc j + 1) - sub3 (j+1))"
                      by simp
                    thus ?thesis by (simp add: mult.assoc mult.commute)
                  qed
                  ultimately show ?thesis by linarith
                qed
                finally show "g' (sub3' j + t * (sub3' (Suc j) - sub3' j)) =
                    g (sub3 (j+1) + t * (sub3 (Suc j + 1) - sub3 (j+1)))" .
              qed
              have hsub3'_pieces: "\<forall>i<k-1. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U) \<or>
                     (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V)"
              proof (intro allI impI)
                fix i assume hi: "i < k - 1"
                show "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U) \<or>
                     (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V)"
                proof (cases "i = 0")
                  case True
                  \<comment> \<open>Piece 0: merged \\<gamma> + piece 1 of g. All in same set as piece 1.\<close>
                  \<comment> \<open>Piece 0 is in same set as piece 1 of g.
                     For s \\<le> 1/2: g'(s) = \\<gamma>(2s) \\<in> A \\<subseteq> U\\<inter>V.
                     For s > 1/2: g'(s) = g\\_R(2s-1) = g at point in [sub3(1),sub3(2)] = piece 1.\<close>
                  have h_piece1: "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> U) \<or>
                      (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> V)"
                    using hs_pieces[rule_format, of 1] hk_ge2 by force
                  \<comment> \<open>\\<gamma> maps into A which is \\<subseteq> U and \\<subseteq> V.\<close>
                  have h\<gamma>_in_A: "\<forall>s \<in> I_set. \<gamma> s \<in> A"
                    using h\<gamma> unfolding top1_is_path_on_def top1_continuous_map_on_def
                    by (by100 blast)
                  \<comment> \<open>Helper: g' for s \\<le> 1/2.\<close>
                  have pp_le: "\<And>s::real. s \<le> 1/2 \<Longrightarrow> g' s = \<gamma> (2*s)"
                    unfolding g'_def top1_path_product_def by simp
                  \<comment> \<open>For any s in [0, sub3'(1)]: g'(s) \\<in> U or V (whichever piece 1 is in).\<close>
                  from h_piece1 show ?thesis
                  proof
                    assume hU1: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> U"
                    show ?thesis
                    proof (intro disjI1 allI impI)
                      fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
                      have "sub3' 0 = 0" using hsub3'_0 .
                      hence hs_eq: "sub3' i + t * (sub3' (Suc i) - sub3' i) = t * sub3' (Suc 0)"
                        using True by simp
                      define s where "s = t * sub3' (Suc 0)"
                      have hg'_at_s: "g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) = g' s"
                        using True hsub3'_0 unfolding s_def by simp
                      show "g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U"
                      proof (cases "s \<le> 1/2")
                        case True
                        hence "g' s = \<gamma> (2*s)" by (rule pp_le)
                        moreover have "\<gamma> (2*s) \<in> A"
                        proof -
                          have "2*s \<in> I_set"
                          proof -
                            have "sub3' (Suc 0) \<ge> 0"
                              using hsub3'_mono[rule_format, of 0] hi hsub3'_0 by linarith
                            hence "s \<ge> 0" unfolding s_def
                              using ht by (intro mult_nonneg_nonneg) auto
                            thus ?thesis using True unfolding top1_unit_interval_def by (by100 simp)
                          qed
                          thus ?thesis using h\<gamma>_in_A by blast
                        qed
                        ultimately have "g' s \<in> A" by simp
                        hence "g' s \<in> U" using hUV_split by (by100 blast)
                        thus ?thesis using hg'_at_s by simp
                      next
                        case False hence "s > 1/2" by linarith
                        hence "g' s = g_R (2*s - 1)" by (rule pp_gt)
                        also have "g_R (2*s - 1) \<in> U"
                        proof -
                          \<comment> \<open>g\\_R(u) = g(sub3(1) + ?d*u). Express ?d*(2s-1) as t'*(sub3(2)-sub3(1)).\<close>
                          have hs_le: "s \<le> sub3' (Suc 0)"
                          proof -
                            have "sub3' (Suc 0) \<ge> 0"
                              using hsub3'_mono[rule_format, of 0] hi hsub3'_0 by linarith
                            have "sub3' (Suc 0) * t \<le> sub3' (Suc 0)"
                              using mult_left_le[of t "sub3' (Suc 0)"] \<open>0 \<le> sub3' (Suc 0)\<close> ht by linarith
                            hence "t * sub3' (Suc 0) \<le> sub3' (Suc 0)"
                              by (simp add: mult.commute)
                            thus ?thesis unfolding s_def .
                          qed
                          have "2*s - 1 \<le> 2 * sub3' (Suc 0) - 1" using hs_le by linarith
                          also have "2 * sub3' (Suc 0) - 1 = (sub3 (Suc 0 + 1) - sub3 1) / ?d"
                          proof -
                            have hval: "sub3' (Suc 0) = 1/2 + (sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d)"
                              unfolding sub3'_def by simp
                            from hval have "2 * sub3' (Suc 0) = 1 + 2 * ((sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d))"
                              by linarith
                            also have "2 * ((sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d)) = (sub3 (Suc 0 + 1) - sub3 1) / ?d"
                            proof -
                              have "2 * (sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d) = (sub3 (Suc 0 + 1) - sub3 1) / ?d"
                                using mult_divide_mult_cancel_left[of "(2::real)" "sub3 (Suc 0 + 1) - sub3 1" "?d"]
                                  hd_pos by linarith
                              moreover have "2 * ((sub3 (Suc 0+1) - sub3 1) / (2*?d)) = 2 * (sub3 (Suc 0+1) - sub3 1) / (2*?d)"
                                by simp
                              ultimately show ?thesis by simp
                            qed
                            finally show ?thesis by linarith
                          qed
                          finally have hu_bound: "2*s - 1 \<le> (sub3 (Suc 0 + 1) - sub3 1) / ?d" .
                          have hu_pos: "2*s - 1 \<ge> 0" using False by linarith
                          \<comment> \<open>Define t' = ?d*(2s-1) / (sub3(2)-sub3(1)).\<close>
                          have h12: "sub3 (Suc 0 + 1) > sub3 1"
                            using hsub3_strict[of 1 "Suc 0 + 1"] hk_ge2 by linarith
                          hence h12_ne: "sub3 (Suc 0 + 1) - sub3 1 > 0" by linarith
                          define t' where "t' = ?d * (2*s - 1) / (sub3 (Suc 0 + 1) - sub3 1)"
                          have ht'0: "t' \<ge> 0" unfolding t'_def using hu_pos hd_pos h12_ne
                            by (by100 simp)
                          have ht'1: "t' \<le> 1"
                          proof -
                            have "?d * (2*s - 1) \<le> ?d * ((sub3 (Suc 0 + 1) - sub3 1) / ?d)"
                              using hu_bound hd_pos by (intro mult_left_mono) linarith+
                            also have "?d * ((sub3 (Suc 0 + 1) - sub3 1) / ?d) = sub3 (Suc 0 + 1) - sub3 1"
                              using hd_pos by simp
                            finally show ?thesis unfolding t'_def using h12_ne by (by100 simp)
                          qed
                          \<comment> \<open>g\\_R(2s-1) = g(sub3(1) + ?d*(2s-1)) = g(sub3(1) + t'*(sub3(2)-sub3(1))).\<close>
                          have "g_R (2*s - 1) = g (sub3 1 + ?d * (2*s - 1))" unfolding g_R_def
                            by (simp add: mult.commute)
                          also have "sub3 1 + ?d * (2*s - 1) = sub3 1 + t' * (sub3 (Suc 0 + 1) - sub3 1)"
                            unfolding t'_def using h12_ne by (by100 simp)
                          finally have "g_R (2*s - 1) = g (sub3 1 + t' * (sub3 (Suc 0 + 1) - sub3 1))" .
                          moreover have "Suc 0 + 1 = Suc 1" by simp
                          ultimately have "g_R (2*s - 1) = g (sub3 1 + t' * (sub3 (Suc 1) - sub3 1))" by simp
                          thus ?thesis using hU1 ht'0 ht'1 by simp
                        qed
                        finally show ?thesis using hg'_at_s by simp
                      qed
                    qed
                  next
                    assume hV1: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> V"
                    show ?thesis
                    proof (intro disjI2 allI impI)
                      fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
                      \<comment> \<open>Symmetric to U case.\<close>
                      define s where "s = t * sub3' (Suc 0)"
                      have hg'_at_s: "g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) = g' s"
                        using True hsub3'_0 unfolding s_def by simp
                      show "g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V"
                      proof (cases "s \<le> 1/2")
                        case True
                        hence "g' s = \<gamma> (2*s)" by (rule pp_le)
                        moreover have "\<gamma> (2*s) \<in> A"
                        proof -
                          have "sub3' (Suc 0) \<ge> 0"
                            using hsub3'_mono[rule_format, of 0] hi hsub3'_0 by linarith
                          hence "s \<ge> 0" unfolding s_def
                            using ht by (intro mult_nonneg_nonneg) auto
                          hence "2*s \<in> I_set" using True unfolding top1_unit_interval_def by (by100 simp)
                          thus ?thesis using h\<gamma>_in_A by blast
                        qed
                        ultimately have "g' s \<in> A" by simp
                        hence "g' s \<in> V" using hUV_split by (by100 blast)
                        thus ?thesis using hg'_at_s by simp
                      next
                        case False hence "s > 1/2" by linarith
                        hence "g' s = g_R (2*s - 1)" by (rule pp_gt)
                        also have "g_R (2*s - 1) \<in> V"
                        proof -
                          have hs_le: "s \<le> sub3' (Suc 0)"
                          proof -
                            have "sub3' (Suc 0) \<ge> 0"
                              using hsub3'_mono[rule_format, of 0] hi hsub3'_0 by linarith
                            have "sub3' (Suc 0) * t \<le> sub3' (Suc 0)"
                              using mult_left_le[of t "sub3' (Suc 0)"] \<open>0 \<le> sub3' (Suc 0)\<close> ht by linarith
                            hence "t * sub3' (Suc 0) \<le> sub3' (Suc 0)"
                              by (simp add: mult.commute)
                            thus ?thesis unfolding s_def .
                          qed
                          have "2*s - 1 \<le> 2 * sub3' (Suc 0) - 1" using hs_le by linarith
                          also have "2 * sub3' (Suc 0) - 1 = (sub3 (Suc 0 + 1) - sub3 1) / ?d"
                          proof -
                            have hval: "sub3' (Suc 0) = 1/2 + (sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d)"
                              unfolding sub3'_def by simp
                            from hval have "2 * sub3' (Suc 0) = 1 + 2 * ((sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d))"
                              by linarith
                            also have "2 * ((sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d)) = (sub3 (Suc 0 + 1) - sub3 1) / ?d"
                            proof -
                              have "2 * (sub3 (Suc 0 + 1) - sub3 1) / (2 * ?d) = (sub3 (Suc 0 + 1) - sub3 1) / ?d"
                                using mult_divide_mult_cancel_left[of "(2::real)" "sub3 (Suc 0 + 1) - sub3 1" "?d"]
                                  hd_pos by linarith
                              moreover have "2 * ((sub3 (Suc 0+1) - sub3 1) / (2*?d)) = 2 * (sub3 (Suc 0+1) - sub3 1) / (2*?d)"
                                by simp
                              ultimately show ?thesis by simp
                            qed
                            finally show ?thesis by linarith
                          qed
                          finally have hu_bound: "2*s - 1 \<le> (sub3 (Suc 0 + 1) - sub3 1) / ?d" .
                          have hu_pos: "2*s - 1 \<ge> 0" using False by linarith
                          have h12: "sub3 (Suc 0 + 1) > sub3 1"
                            using hsub3_strict[of 1 "Suc 0 + 1"] hk_ge2 by linarith
                          hence h12_ne: "sub3 (Suc 0 + 1) - sub3 1 > 0" by linarith
                          define t' where "t' = ?d * (2*s - 1) / (sub3 (Suc 0 + 1) - sub3 1)"
                          have ht'0: "t' \<ge> 0" unfolding t'_def using hu_pos hd_pos h12_ne
                            by (by100 simp)
                          have ht'1: "t' \<le> 1"
                          proof -
                            have "?d * (2*s - 1) \<le> ?d * ((sub3 (Suc 0 + 1) - sub3 1) / ?d)"
                              using hu_bound hd_pos by (intro mult_left_mono) linarith+
                            also have "?d * ((sub3 (Suc 0 + 1) - sub3 1) / ?d) = sub3 (Suc 0 + 1) - sub3 1"
                              using hd_pos by simp
                            finally show ?thesis unfolding t'_def using h12_ne by (by100 simp)
                          qed
                          have "g_R (2*s - 1) = g (sub3 1 + ?d * (2*s - 1))" unfolding g_R_def
                            by (simp add: mult.commute)
                          also have "sub3 1 + ?d * (2*s - 1) = sub3 1 + t' * (sub3 (Suc 0 + 1) - sub3 1)"
                            unfolding t'_def using h12_ne by (by100 simp)
                          finally have "g_R (2*s - 1) = g (sub3 1 + t' * (sub3 (Suc 0 + 1) - sub3 1))" .
                          moreover have "Suc 0 + 1 = Suc 1" by simp
                          ultimately have "g_R (2*s - 1) = g (sub3 1 + t' * (sub3 (Suc 1) - sub3 1))" by simp
                          thus ?thesis using hV1 ht'0 ht'1 by simp
                        qed
                        finally show ?thesis using hg'_at_s by simp
                      qed
                    qed
                  qed
                next
                  case False hence "i \<ge> 1" by linarith
                  \<comment> \<open>Piece j\\<ge>1: reparametrization maps to piece j+1 of g.\<close>
                  have "i + 1 < k" using hi by linarith
                  from hs_pieces[rule_format, OF \<open>i+1 < k\<close>]
                  have hpiece_orig: "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 (i+1) + t*(sub3 (Suc (i+1)) - sub3 (i+1))) \<in> U) \<or>
                      (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 (i+1) + t*(sub3 (Suc (i+1)) - sub3 (i+1))) \<in> V)"
                    by simp
                  from this show ?thesis
                  proof
                    assume hU: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 (i+1) + t*(sub3 (Suc (i+1)) - sub3 (i+1))) \<in> U"
                    show ?thesis
                    proof (intro disjI1 allI impI)
                      fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
                      from hpiece_j_ge1[OF \<open>i \<ge> 1\<close> hi] ht
                      have "g' (sub3' i + t * (sub3' (Suc i) - sub3' i)) =
                          g (sub3 (i+1) + t * (sub3 (Suc i + 1) - sub3 (i+1)))" by blast
                      also have "Suc i + 1 = Suc (i + 1)" by linarith
                      finally show "g' (sub3' i + t * (sub3' (Suc i) - sub3' i)) \<in> U"
                        using hU ht by simp
                    qed
                  next
                    assume hV: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 (i+1) + t*(sub3 (Suc (i+1)) - sub3 (i+1))) \<in> V"
                    show ?thesis
                    proof (intro disjI2 allI impI)
                      fix t :: real assume ht: "0 \<le> t \<and> t \<le> 1"
                      from hpiece_j_ge1[OF \<open>i \<ge> 1\<close> hi] ht
                      have "g' (sub3' i + t * (sub3' (Suc i) - sub3' i)) =
                          g (sub3 (i+1) + t * (sub3 (Suc i + 1) - sub3 (i+1)))" by blast
                      also have "Suc i + 1 = Suc (i + 1)" by linarith
                      finally show "g' (sub3' i + t * (sub3' (Suc i) - sub3' i)) \<in> V"
                        using hV ht by simp
                    qed
                  qed
                qed
              qed
              show "(k-1) \<ge> 1 \<and> sub3' 0 = 0 \<and> sub3' (k-1) = 1 \<and>
                  (\<forall>i<k-1. sub3' i < sub3' (Suc i)) \<and>
                  (\<forall>i\<le>k-1. g' (sub3' i) \<in> U \<inter> V) \<and>
                  (\<forall>i<k-1. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U) \<or>
                         (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V))"
                using hk_m1_ge hsub3'_0 hsub3'_km1 hsub3'_mono hsub3'_UV hsub3'_pieces by blast
            qed
            then obtain sub3' where hg'_sub: "(k-1) \<ge> 1" "sub3' 0 = 0" "sub3' (k-1) = 1"
                "(\<forall>i<k-1. sub3' i < sub3' (Suc i))"
                "(\<forall>i\<le>k-1. g' (sub3' i) \<in> U \<inter> V)"
                "(\<forall>i<k-1. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U) \<or>
                       (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V))"
              by blast
            \<comment> \<open>Assemble: g ~ g' with k-1 pieces.\<close>
            have "\<exists>g' sub3'. top1_path_homotopic_on X TX a a g g' \<and>
                top1_is_loop_on X TX a g' \<and>
                (k-1) \<ge> 1 \<and> sub3' 0 = 0 \<and> sub3' (k-1) = 1 \<and>
                (\<forall>i<k-1. sub3' i < sub3' (Suc i)) \<and>
                (\<forall>i\<le>k-1. g' (sub3' i) \<in> U \<inter> V) \<and>
                (\<forall>i<k-1. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U) \<or>
                       (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V))"
              using hg_htpy_\<gamma>gR hg'_loop hg'_sub unfolding g'_def by blast
            then obtain g' sub3' where hg'_htpy: "top1_path_homotopic_on X TX a a g g'"
                and hg'_loop: "top1_is_loop_on X TX a g'"
                and hg'_props: "(k-1) \<ge> 1" "sub3' 0 = 0" "sub3' (k-1) = 1"
                  "(\<forall>i<k-1. sub3' i < sub3' (Suc i))"
                  "(\<forall>i\<le>k-1. g' (sub3' i) \<in> U \<inter> V)"
                  "(\<forall>i<k-1. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U) \<or>
                         (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g'(sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V))"
              by blast
            \<comment> \<open>IH gives gen\\_power(g').\<close>
            have "gen_power g'"
            proof -
              from IH have "\<forall>g sub3. k - 1 \<ge> 1 \<longrightarrow> top1_is_loop_on X TX a g \<longrightarrow>
                  sub3 0 = 0 \<longrightarrow> sub3 (k-1) = 1 \<longrightarrow>
                  (\<forall>i<k-1. sub3 i < sub3 (Suc i)) \<longrightarrow>
                  (\<forall>i\<le>k-1. g (sub3 i) \<in> U \<inter> V) \<longrightarrow>
                  (\<forall>i<k-1. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> U) \<or>
                         (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> V)) \<longrightarrow>
                  gen_power g" using hk_m1_lt by blast
              thus ?thesis using hg'_loop hg'_props by blast
            qed
            \<comment> \<open>g ~ g' and gen\\_power(g') \\<Rightarrow> gen\\_power(g).\<close>
            thus "gen_power g" unfolding gen_power_def
              using hg'_htpy Lemma_51_1_path_homotopic_trans[OF hTX_top]
                    Lemma_51_1_path_homotopic_sym by (by100 blast)
          next
            case False
            hence hx1_B: "g (sub3 1) \<in> B" using hx1_AB by blast
            \<comment> \<open>Case B: gen\_power(g) directly. Merge same-type or extract factor from alternating.\<close>
            \<comment> \<open>Sub-case split: piece 0 and piece 1 same type or different.\<close>
            have hpiece0_type: "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> U) \<or>
                (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> V)"
              using hs_pieces hk_ge2 by (by100 force)
            have "1 < k" using hk_ge2 by linarith
            have hpiece1_type: "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> U) \<or>
                (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> V)"
              using hs_pieces[rule_format, OF \<open>1 < k\<close>] by simp
            show "gen_power g"
            proof (cases "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> U) \<and>
                (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> U)
              \<or> (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> V) \<and>
                (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> V)")
              case True
              \<comment> \<open>Sub-case (a): pieces 0 and 1 in same set. Merge \\<Rightarrow> k-1 pieces \\<Rightarrow> IH.\<close>
              \<comment> \<open>The SAME g with merged subdivision (removing sub3(1)) has k-1 pieces.\<close>
              \<comment> \<open>Define merged subdivision: skip sub3(1).\<close>
              define sub3_m where "sub3_m j = (if j = 0 then sub3 0 else sub3 (Suc j))" for j
              have "gen_power g"
              proof -
                have hm_ge: "k - 1 \<ge> 1" using hk_ge2 by linarith
                have hm_lt: "k - 1 < k" using hk_ge2 by linarith
                have hm0: "sub3_m 0 = 0" unfolding sub3_m_def using hs0 by simp
                have hmk: "sub3_m (k-1) = 1"
                proof -
                  have "sub3_m (k-1) = sub3 (Suc (k-1))" unfolding sub3_m_def using hk_ge2 by simp
                  also have "Suc (k-1) = k" using hk_ge2 by linarith
                  finally show ?thesis using hsk by simp
                qed
                have hm_inc: "\<forall>i<k-1. sub3_m i < sub3_m (Suc i)"
                proof (intro allI impI)
                  fix i assume hi: "i < k-1"
                  show "sub3_m i < sub3_m (Suc i)"
                  proof (cases "i = 0")
                    case True
                    hence "sub3_m 0 = sub3 0" unfolding sub3_m_def by simp
                    moreover have "sub3_m (Suc 0) = sub3 (Suc (Suc 0))" unfolding sub3_m_def by simp
                    moreover have "sub3 0 < sub3 (Suc (Suc 0))"
                    proof -
                      have "sub3 0 < sub3 (Suc 0)" using hs_inc hk_ge2 by (by100 force)
                      also have "sub3 (Suc 0) < sub3 (Suc (Suc 0))"
                        using hs_inc[rule_format, of "Suc 0"] hk_ge2 by linarith
                      finally show ?thesis .
                    qed
                    ultimately show ?thesis using True by simp
                  next
                    case False
                    have "sub3_m i = sub3 (Suc i)" unfolding sub3_m_def using False by simp
                    moreover have "sub3_m (Suc i) = sub3 (Suc (Suc i))" unfolding sub3_m_def by simp
                    moreover have "sub3 (Suc i) < sub3 (Suc (Suc i))"
                      using hs_inc[rule_format, of "Suc i"] hi by linarith
                    ultimately show ?thesis by simp
                  qed
                qed
                have hm_UV: "\<forall>i\<le>k-1. g (sub3_m i) \<in> U \<inter> V"
                proof (intro allI impI)
                  fix i assume hi: "i \<le> k-1"
                  show "g (sub3_m i) \<in> U \<inter> V"
                  proof (cases "i = 0")
                    case True
                    have "g (sub3 0) \<in> U \<inter> V" using hs_UV hk_ge2 by (by100 force)
                    thus ?thesis unfolding sub3_m_def using True hs0 by simp
                  next
                    case False
                    have "sub3_m i = sub3 (Suc i)" unfolding sub3_m_def using False by simp
                    moreover have "g (sub3 (Suc i)) \<in> U \<inter> V"
                      using hs_UV[rule_format, of "Suc i"] hi hk_ge2 by linarith
                    ultimately show ?thesis by simp
                  qed
                qed
                have hm_pieces: "\<forall>i<k-1. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3_m i + t*(sub3_m (Suc i) - sub3_m i)) \<in> U) \<or>
                    (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3_m i + t*(sub3_m (Suc i) - sub3_m i)) \<in> V)"
                proof (intro allI impI)
                  fix i assume hi: "i < k-1"
                  show "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3_m i + t*(sub3_m (Suc i) - sub3_m i)) \<in> U) \<or>
                      (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3_m i + t*(sub3_m (Suc i) - sub3_m i)) \<in> V)"
                  proof (cases "i = 0")
                    case True
                    \<comment> \<open>Merged piece: sub3\\_m(0)=sub3(0) to sub3\\_m(1)=sub3(2). Both original pieces in same set S.\<close>
                    have "sub3_m 0 = sub3 0" unfolding sub3_m_def by simp
                    have "sub3_m (Suc 0) = sub3 (Suc (Suc 0))" unfolding sub3_m_def by simp
                    \<comment> \<open>Any point in [sub3(0), sub3(2)] is in piece 0 or piece 1 of original, both in S.\<close>
                    \<comment> \<open>The outer True case gives: pieces 0,1 both in U \\<or> both in V.\<close>
                    have hsame: "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> U) \<and>
                        (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> U) \<or>
                        (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> V) \<and>
                        (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> V)"
                      using \<open>(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> U) \<and>
                        (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> U) \<or>
                        (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> V) \<and>
                        (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> V)\<close> .
                    \<comment> \<open>For any t, the merged point is in piece 0 or piece 1 of original g. Both in same set.\<close>
                    \<comment> \<open>Helper: any s \\<in> [sub3(0), sub3(2)] that's in piece 0 or 1 of g is in set S.\<close>
                    have h01_pos: "sub3 1 > sub3 0" using hs_inc hk_ge2 by (by100 force)
                    have h12_pos: "sub3 (Suc 1) > sub3 1" using hs_inc[rule_format, of 1] hk_ge2 by linarith
                    have h02_pos: "sub3 (Suc (Suc 0)) > sub3 0"
                      using h01_pos h12_pos by (by100 simp)
                    \<comment> \<open>For any s \\<in> [sub3(0), sub3(2)]: find t' for the right piece.\<close>
                    have hmerged_in_S: "\<And>S. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> S) \<Longrightarrow>
                        (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> S) \<Longrightarrow>
                        (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 (Suc (Suc 0)) - sub3 0)) \<in> S)"
                    proof (intro allI impI)
                      fix S :: "'a set" and t :: real
                      assume hS0: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> S"
                        and hS1: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> S"
                        and ht: "0 \<le> t \<and> t \<le> 1"
                      define s where "s = sub3 0 + t * (sub3 (Suc (Suc 0)) - sub3 0)"
                      show "g (sub3 0 + t * (sub3 (Suc (Suc 0)) - sub3 0)) \<in> S"
                      proof (cases "s \<le> sub3 1")
                        case True
                        define t' where "t' = (s - sub3 0) / (sub3 1 - sub3 0)"
                        have "s \<ge> sub3 0" unfolding s_def using ht h02_pos by (by100 simp)
                        have "t' \<ge> 0" unfolding t'_def using \<open>s \<ge> sub3 0\<close> h01_pos by (by100 simp)
                        have "t' \<le> 1" unfolding t'_def using True h01_pos s_def by (by100 simp)
                        have "s = sub3 0 + t' * (sub3 1 - sub3 0)" unfolding t'_def
                          using h01_pos by (simp add: field_simps)
                        hence "g s \<in> S" using hS0 \<open>t' \<ge> 0\<close> \<open>t' \<le> 1\<close> by blast
                        thus ?thesis unfolding s_def .
                      next
                        case False hence "s > sub3 1" by linarith
                        define t' where "t' = (s - sub3 1) / (sub3 (Suc 1) - sub3 1)"
                        have "t' \<ge> 0" unfolding t'_def using \<open>s > sub3 1\<close> h12_pos by (by100 simp)
                        have hs_le: "s \<le> sub3 (Suc (Suc 0))"
                        proof -
                          have hd: "sub3 (Suc (Suc 0)) - sub3 0 \<ge> 0" using h02_pos by linarith
                          from mult_left_le[of t "sub3 (Suc (Suc 0)) - sub3 0"] ht hd
                          have "t * (sub3 (Suc (Suc 0)) - sub3 0) \<le> sub3 (Suc (Suc 0)) - sub3 0"
                            by (simp add: mult.commute)
                          thus ?thesis unfolding s_def by linarith
                        qed
                        have "t' \<le> 1" unfolding t'_def using hs_le h12_pos by (by100 simp)
                        have "s = sub3 1 + t' * (sub3 (Suc 1) - sub3 1)" unfolding t'_def
                          using h12_pos by (simp add: field_simps)
                        hence "g s \<in> S" using hS1 \<open>t' \<ge> 0\<close> \<open>t' \<le> 1\<close> by blast
                        thus ?thesis unfolding s_def .
                      qed
                    qed
                    from hsame show ?thesis
                    proof
                      assume h: "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> U) \<and>
                          (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> U)"
                      from hmerged_in_S[OF conjunct1[OF h] conjunct2[OF h]]
                      show ?thesis using True \<open>sub3_m 0 = sub3 0\<close> \<open>sub3_m (Suc 0) = sub3 (Suc (Suc 0))\<close>
                        by simp
                    next
                      assume h: "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> V) \<and>
                          (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> V)"
                      from hmerged_in_S[OF conjunct1[OF h] conjunct2[OF h]]
                      show ?thesis using True \<open>sub3_m 0 = sub3 0\<close> \<open>sub3_m (Suc 0) = sub3 (Suc (Suc 0))\<close>
                        by simp
                    qed
                  next
                    case False
                    \<comment> \<open>Non-merged piece: sub3\\_m(i)=sub3(Suc i) to sub3\\_m(Suc i)=sub3(Suc(Suc i)). Same as original piece Suc i.\<close>
                    have "sub3_m i = sub3 (Suc i)" unfolding sub3_m_def using False by simp
                    moreover have "sub3_m (Suc i) = sub3 (Suc (Suc i))" unfolding sub3_m_def by simp
                    ultimately have "sub3_m i + t * (sub3_m (Suc i) - sub3_m i) =
                        sub3 (Suc i) + t * (sub3 (Suc (Suc i)) - sub3 (Suc i))" for t by simp
                    moreover have "Suc i < k" using hi by linarith
                    ultimately show ?thesis using hs_pieces by (by100 force)
                  qed
                qed
                from IH have "\<forall>g sub3. k-1 \<ge> 1 \<longrightarrow> top1_is_loop_on X TX a g \<longrightarrow>
                    sub3 0 = 0 \<longrightarrow> sub3 (k-1) = 1 \<longrightarrow>
                    (\<forall>i<k-1. sub3 i < sub3 (Suc i)) \<longrightarrow>
                    (\<forall>i\<le>k-1. g (sub3 i) \<in> U \<inter> V) \<longrightarrow>
                    (\<forall>i<k-1. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> U) \<or>
                           (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> V)) \<longrightarrow>
                    gen_power g" using hm_lt by blast
                thus ?thesis using hg_loop hm_ge hm0 hmk hm_inc hm_UV hm_pieces by blast
              qed
              thus ?thesis .
            next
              case False
              \<comment> \<open>Sub-case (b)/(c): pieces 0 and 1 in different sets (alternating at pos 1).
                 Extract (\\<alpha>*\\<beta>) or rev(\\<alpha>*\\<beta>) factor, merge with piece\\_1 \\<Rightarrow> k-1 \\<Rightarrow> IH.\<close>
              \<comment> \<open>Pieces 0,1 in different sets. Extract (\\<alpha>*\\<beta>) or rev, construct g' with k-1 pieces.\<close>
              show "gen_power g"
              proof -
                \<comment> \<open>Get connecting path \\<delta> from b to g(sub3(1)) in B.\<close>
                obtain \<delta> where h\<delta>: "top1_is_path_on B (subspace_topology X TX B) b (g (sub3 1)) \<delta>"
                  using hB_pc hb hx1_B unfolding top1_path_connected_on_def by blast
                \<comment> \<open>Determine which set piece\\_0 is in.\<close>
                from hpiece0_type show ?thesis
                proof
                  assume hp0U: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> U"
                  \<comment> \<open>piece\\_0 \\<in> U, piece\\_1 \\<in> V (from False). Connecting path \\<beta>\\_bar*\\<delta> \\<in> V.
                     g ~ (\\<alpha>*\\<beta>) * g'. g' = \\<beta>\\_bar*\\<delta>*g\\_R with k-1 pieces. IH \\<Rightarrow> gen\\_power(g').\<close>
                  \<comment> \<open>piece\\_0 \\<in> U. Extract (\\<alpha>*\\<beta>) factor.
                     g ~ \\<alpha> * (\\<delta>*g\\_R) ~ (\\<alpha>*\\<beta>) * (\\<beta>\\_bar*\\<delta>*g\\_R).
                     g' = (\\<beta>\\_bar*\\<delta>)*g\\_R has k-1 pieces (merge \\<beta>\\_bar*\\<delta>\\<in>V with piece\\_1\\<in>V).
                     IH \\<Rightarrow> gen\\_power(g') \\<Rightarrow> gen\\_power(g) via \\<alpha>*\\<beta> factor.\<close>
                  show ?thesis
                  proof -
                    \<comment> \<open>Step 1: piece\\_1 \\<in> V (from alternating).\<close>
                    have hp1V: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> V"
                    proof -
                      from hpiece1_type show ?thesis
                      proof
                        assume "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> U"
                        hence "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> U) \<and>
                            (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> U)"
                          using hp0U by blast
                        thus ?thesis using False by blast
                      next
                        assume "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> V"
                        thus ?thesis .
                      qed
                    qed
                    \<comment> \<open>Step 2: Build cp = \\<beta>\\_bar * \\<delta>: a \\<rightarrow> b \\<rightarrow> g(sub3(1)), in V.\<close>
                    have hB_sub: "B \<subseteq> X"
                      using hB_open unfolding openin_on_def by (by100 blast)
                    have hV_sub: "V \<subseteq> X"
                      using hV_open unfolding openin_on_def by (by100 blast)
                    have hU_sub: "U \<subseteq> X"
                      using hU_open unfolding openin_on_def by (by100 blast)
                    have h\<delta>_X: "top1_is_path_on X TX b (g (sub3 1)) \<delta>"
                      by (rule path_in_subspace_is_path_in_ambient[OF hTX_top hB_sub h\<delta>])
                    have hbeta_X: "top1_is_path_on X TX b a \<beta>"
                      by (rule path_in_subspace_is_path_in_ambient[OF hTX_top hV_sub hbeta])
                    have halpha_X: "top1_is_path_on X TX a b \<alpha>"
                      by (rule path_in_subspace_is_path_in_ambient[OF hTX_top hU_sub halpha])
                    have hbeta_bar_X: "top1_is_path_on X TX a b (top1_path_reverse \<beta>)"
                      by (rule top1_path_reverse_is_path[OF hbeta_X])
                    define cp where "cp = top1_path_product (top1_path_reverse \<beta>) \<delta>"
                    have hcp_path: "top1_is_path_on X TX a (g (sub3 1)) cp"
                      unfolding cp_def
                      by (rule top1_path_product_is_path[OF hTX_top hbeta_bar_X h\<delta>_X])
                    \<comment> \<open>cp(s) \\<in> V for all s.\<close>
                    have hcp_in_V: "\<forall>s \<in> I_set. cp s \<in> V"
                    proof (intro ballI)
                      fix s assume hs: "s \<in> I_set"
                      hence hs01: "0 \<le> s \<and> s \<le> 1"
                        unfolding top1_unit_interval_def by (by100 simp)
                      show "cp s \<in> V"
                      proof (cases "s \<le> 1/2")
                        case True
                        hence "cp s = (top1_path_reverse \<beta>) (2*s)"
                          unfolding cp_def top1_path_product_def by simp
                        also have "... = \<beta> (1 - 2*s)"
                          unfolding top1_path_reverse_def by simp
                        also have "... \<in> V"
                        proof -
                          have "1 - 2*s \<in> I_set"
                            using True hs01 unfolding top1_unit_interval_def
                            by (by100 simp)
                          from hbeta[unfolded top1_is_path_on_def, THEN conjunct1,
                              unfolded top1_continuous_map_on_def]
                          have "\<forall>x \<in> I_set. \<beta> x \<in> V" by (by100 blast)
                          thus ?thesis using \<open>1 - 2*s \<in> I_set\<close> by blast
                        qed
                        finally show ?thesis .
                      next
                        case False hence "s > 1/2" by linarith
                        hence "cp s = \<delta> (2*s - 1)"
                          unfolding cp_def top1_path_product_def by simp
                        also have "... \<in> V"
                        proof -
                          have "2*s - 1 \<in> I_set"
                            using False hs01 unfolding top1_unit_interval_def
                            by (by100 simp)
                          have "B \<subseteq> V" using hUV_split by (by100 blast)
                          from h\<delta>[unfolded top1_is_path_on_def, THEN conjunct1,
                              unfolded top1_continuous_map_on_def]
                          have "\<forall>x \<in> I_set. \<delta> x \<in> B" by (by100 blast)
                          hence "\<delta> (2*s - 1) \<in> B" using \<open>2*s - 1 \<in> I_set\<close> by blast
                          thus ?thesis using \<open>B \<subseteq> V\<close> by blast
                        qed
                        finally show ?thesis .
                      qed
                    qed
                    \<comment> \<open>Step 3: Apply hgen\\_subdivision\\_only.\<close>
                    have hS_type: "(V::'a set) = U \<or> V = V" by blast
                    from hgen_subdivision_only[OF hTX_top hk_ge2 hg_loop hs0 hsk hs_inc
                        hs_UV hs_pieces hcp_path hcp_in_V hV_sub hp1V hS_type]
                    obtain sub3' where
                      hg'_loop: "top1_is_loop_on X TX a
                        (top1_path_product cp (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t)))" and
                      hg'_k: "(k-1) \<ge> 1" and hg'_0: "sub3' 0 = 0" and
                      hg'_km1: "sub3' (k-1) = 1" and
                      hg'_mono: "\<forall>i<k-1. sub3' i < sub3' (Suc i)" and
                      hg'_UV: "\<forall>i\<le>k-1.
                        (top1_path_product cp (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))) (sub3' i)
                          \<in> U \<inter> V" and
                      hg'_pieces: "\<forall>i<k-1.
                        (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow>
                          (top1_path_product cp (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t)))
                            (sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> U) \<or>
                        (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow>
                          (top1_path_product cp (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t)))
                            (sub3' i + t*(sub3' (Suc i) - sub3' i)) \<in> V)"
                      by blast
                    define g'_alt where
                      "g'_alt = top1_path_product cp (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))"
                    \<comment> \<open>Step 4: g ~ (\\<alpha>*\\<beta>)*g'\\_alt via path algebra.\<close>
                    have hg_htpy_ab_g': "top1_path_homotopic_on X TX a a g
                        (top1_path_product (top1_path_product \<alpha> \<beta>) g'_alt)"
                    proof -
                      \<comment> \<open>Split g at sub3(1).\<close>
                      have hsub31_pos: "0 < sub3 1" using hs_inc hs0 hk_ge2 by (by100 force)
                      have hsub31_lt1: "sub3 1 < 1"
                      proof -
                        have "\<And>i j. i < j \<Longrightarrow> j \<le> k \<Longrightarrow> sub3 i < sub3 j"
                        proof -
                          fix i j :: nat assume "i < j" "j \<le> k"
                          thus "sub3 i < sub3 j"
                          proof (induction j)
                            case 0 thus ?case by simp
                          next
                            case (Suc j) show ?case
                            proof (cases "i = j")
                              case True thus ?thesis using hs_inc Suc.prems by simp
                            next
                              case False hence "sub3 i < sub3 j" using Suc by linarith
                              also have "sub3 j < sub3 (Suc j)" using hs_inc Suc.prems by simp
                              finally show ?thesis .
                            qed
                          qed
                        qed
                        from this[of 1 k] have "sub3 1 < sub3 k" using hk_ge2 by simp
                        thus ?thesis using hsk by linarith
                      qed
                      define g_L where "g_L = (\<lambda>t. g (sub3 1 * t))"
                      define g_R_loc where "g_R_loc = (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))"
                      have hg_path: "top1_is_path_on X TX a a g"
                        using hg_loop unfolding top1_is_loop_on_def by (by100 blast)
                      have hg0: "g 0 = a"
                        using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                        by (by100 blast)
                      have hg_split: "top1_path_homotopic_on X TX a a g
                          (top1_path_product g_L g_R_loc)"
                        unfolding g_L_def g_R_loc_def
                        by (rule path_product_split[OF hTX_top hg_path hsub31_pos hsub31_lt1])
                      \<comment> \<open>g\\_R\\_loc is the same \\<lambda> as in g'\\_alt.\<close>
                      have hgR_eq: "g_R_loc = (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))"
                        unfolding g_R_loc_def ..
                      \<comment> \<open>Path properties.\<close>
                      have hgL_path: "top1_is_path_on X TX a (g (sub3 1)) g_L"
                      proof -
                        have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
                          using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                          by (by100 blast)
                        have haffL: "top1_continuous_map_on I_set I_top I_set I_top
                            (\<lambda>t. t * sub3 1)"
                        proof -
                          have "top1_continuous_map_on I_set I_top I_set I_top
                              (\<lambda>t. 0 + t * (sub3 1 - 0))"
                            by (rule affine_map_continuous_I_to_I)
                               (use hsub31_pos hsub31_lt1 in linarith)+
                          thus ?thesis by simp
                        qed
                        have "top1_continuous_map_on I_set I_top X TX (g \<circ> (\<lambda>t. t * sub3 1))"
                          by (rule top1_continuous_map_on_comp[OF haffL hg_cont])
                        moreover have "(g \<circ> (\<lambda>t. t * sub3 1)) = (\<lambda>t. g (sub3 1 * t))"
                          by (rule ext) (simp add: mult.commute)
                        ultimately have "top1_continuous_map_on I_set I_top X TX
                            (\<lambda>t. g (sub3 1 * t))" by simp
                        moreover have "(\<lambda>t. g (sub3 1 * t)) 0 = a" using hg0 by simp
                        moreover have "(\<lambda>t. g (sub3 1 * t)) 1 = g (sub3 1)" by simp
                        ultimately show ?thesis unfolding g_L_def top1_is_path_on_def by blast
                      qed
                      have hgR_path: "top1_is_path_on X TX (g (sub3 1)) a g_R_loc"
                      proof -
                        have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
                          using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                          by (by100 blast)
                        have hg1: "g 1 = a"
                          using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                          by (by100 blast)
                        have haffR: "top1_continuous_map_on I_set I_top I_set I_top
                            (\<lambda>t. sub3 1 + t * (1 - sub3 1))"
                          by (rule affine_map_continuous_I_to_I)
                             (use hsub31_pos hsub31_lt1 in linarith)+
                        have "top1_continuous_map_on I_set I_top X TX
                            (g \<circ> (\<lambda>t. sub3 1 + t * (1 - sub3 1)))"
                          by (rule top1_continuous_map_on_comp[OF haffR hg_cont])
                        moreover have "(g \<circ> (\<lambda>t. sub3 1 + t * (1 - sub3 1))) = g_R_loc"
                          unfolding g_R_loc_def by (rule ext) (simp add: algebra_simps)
                        ultimately have "top1_continuous_map_on I_set I_top X TX g_R_loc"
                          by simp
                        moreover have "g_R_loc 0 = g (sub3 1)"
                          unfolding g_R_loc_def by simp
                        moreover have "g_R_loc 1 = a"
                          unfolding g_R_loc_def using hg1 by simp
                        ultimately show ?thesis unfolding top1_is_path_on_def by blast
                      qed
                      \<comment> \<open>SC of U: g\\_L ~ \\<alpha>*\\<delta>.\<close>
                      have h_ad_path: "top1_is_path_on X TX a (g (sub3 1))
                          (top1_path_product \<alpha> \<delta>)"
                        by (rule top1_path_product_is_path[OF hTX_top halpha_X h\<delta>_X])
                      have hgL_htpy: "top1_path_homotopic_on X TX a (g (sub3 1)) g_L
                          (top1_path_product \<alpha> \<delta>)"
                      proof -
                        \<comment> \<open>g\\_L maps [0,1] into U (from piece\\_0 \\<in> U).\<close>
                        have hsimp_gL: "\<And>t. g(sub3 0 + t*(sub3 1 - sub3 0)) = g_L t"
                          unfolding g_L_def using hs0 by (simp add: mult.commute)
                        have hgL_in_U: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g_L t \<in> U"
                          using hp0U hsimp_gL by (simp add: mult.commute)
                        \<comment> \<open>g\\_L as path in U.\<close>
                        have hgL_U: "top1_is_path_on U (subspace_topology X TX U) a (g (sub3 1)) g_L"
                        proof -
                          have hgL_img: "\<forall>s \<in> I_set. g_L s \<in> U"
                          proof (intro ballI)
                            fix s assume "s \<in> I_set"
                            hence "0 \<le> s \<and> s \<le> 1"
                              unfolding top1_unit_interval_def by (by100 simp)
                            thus "g_L s \<in> U" using hgL_in_U by blast
                          qed
                          have hgL_cont: "top1_continuous_map_on I_set I_top X TX g_L"
                            using hgL_path unfolding top1_is_path_on_def by (by100 blast)
                          have "top1_continuous_map_on I_set I_top U (subspace_topology X TX U) g_L"
                            by (rule continuous_map_restrict_codomain[OF hgL_cont hgL_img hU_sub])
                          thus ?thesis unfolding top1_is_path_on_def
                            using ha_U_loc hgL_path[unfolded top1_is_path_on_def] by blast
                        qed
                        \<comment> \<open>\\<alpha>*\\<delta> as path in U.\<close>
                        have h_ad_U: "top1_is_path_on U (subspace_topology X TX U) a (g (sub3 1))
                            (top1_path_product \<alpha> \<delta>)"
                        proof -
                          have "A \<subseteq> U" using hUV_split by (by100 blast)
                          have "B \<subseteq> U" using hUV_split by (by100 blast)
                          \<comment> \<open>\\<alpha> is in U.\<close>
                          have h\<alpha>_U: "top1_is_path_on U (subspace_topology X TX U) a b \<alpha>"
                          proof -
                            from top1_continuous_map_on_codomain_enlarge[OF
                                halpha[unfolded top1_is_path_on_def, THEN conjunct1]
                                subset_refl hU_sub]
                            show ?thesis unfolding top1_is_path_on_def
                              using ha_U_loc halpha[unfolded top1_is_path_on_def] by blast
                          qed
                          \<comment> \<open>\\<delta> is in B \\<subseteq> U.\<close>
                          have h\<delta>_U: "top1_is_path_on U (subspace_topology X TX U) b (g (sub3 1)) \<delta>"
                          proof -
                            from top1_continuous_map_on_codomain_enlarge[OF
                                h\<delta>[unfolded top1_is_path_on_def, THEN conjunct1]
                                \<open>B \<subseteq> U\<close> hU_sub]
                            have "top1_continuous_map_on I_set I_top U (subspace_topology X TX U) \<delta>" .
                            thus ?thesis unfolding top1_is_path_on_def
                              using hb h\<delta>[unfolded top1_is_path_on_def] \<open>B \<subseteq> U\<close>
                              by (by100 blast)
                          qed
                          show ?thesis
                            by (rule top1_path_product_is_path[OF
                                subspace_topology_is_topology_on[OF hTX_top hU_sub]
                                h\<alpha>_U h\<delta>_U])
                        qed
                        \<comment> \<open>SC of U: g\\_L ~ \\<alpha>*\\<delta>.\<close>
                        from simply_connected_paths_homotopic[OF hU_sc hgL_U h_ad_U ha_U_loc]
                        have "top1_path_homotopic_on U (subspace_topology X TX U)
                            a (g (sub3 1)) g_L (top1_path_product \<alpha> \<delta>)" .
                        from path_homotopic_subspace_to_ambient[OF hTX_top hU_sub _ this]
                        show ?thesis by (by100 simp)
                      qed
                      \<comment> \<open>g ~ (\\<alpha>*\\<delta>)*g\\_R\\_loc.\<close>
                      have hstep1: "top1_path_homotopic_on X TX a a g
                          (top1_path_product (top1_path_product \<alpha> \<delta>) g_R_loc)"
                      proof -
                        from path_homotopic_product_left[OF hTX_top hgL_htpy hgR_path]
                        have "top1_path_homotopic_on X TX a a
                            (top1_path_product g_L g_R_loc)
                            (top1_path_product (top1_path_product \<alpha> \<delta>) g_R_loc)" .
                        from Lemma_51_1_path_homotopic_trans[OF hTX_top hg_split this]
                        show ?thesis .
                      qed
                      \<comment> \<open>(\\<alpha>*\\<beta>)*g'\\_alt ~ (\\<alpha>*\\<delta>)*g\\_R\\_loc via algebra.\<close>
                      have hstep2: "top1_path_homotopic_on X TX a a
                          (top1_path_product (top1_path_product \<alpha> \<beta>) g'_alt)
                          (top1_path_product (top1_path_product \<alpha> \<delta>) g_R_loc)"
                      proof -
                        \<comment> \<open>Path facts needed for algebra.\<close>
                        have hab_path: "top1_is_path_on X TX a a (top1_path_product \<alpha> \<beta>)"
                          by (rule top1_path_product_is_path[OF hTX_top halpha_X hbeta_X])
                        have hbcp_path: "top1_is_path_on X TX b (g (sub3 1))
                            (top1_path_product \<beta> cp)"
                          by (rule top1_path_product_is_path[OF hTX_top hbeta_X hcp_path])
                        have hbb_path: "top1_is_path_on X TX b b
                            (top1_path_product \<beta> (top1_path_reverse \<beta>))"
                          by (rule top1_path_product_is_path[OF hTX_top hbeta_X hbeta_bar_X])
                        have habcp_path: "top1_is_path_on X TX a (g (sub3 1))
                            (top1_path_product (top1_path_product \<alpha> \<beta>) cp)"
                          by (rule top1_path_product_is_path[OF hTX_top hab_path hcp_path])
                        \<comment> \<open>Step A: (\\<alpha>*\\<beta>)*(cp*g\\_R) ~ ((\\<alpha>*\\<beta>)*cp)*g\\_R  [assoc].\<close>
                        from Theorem_51_2_associativity[OF hTX_top hab_path hcp_path hgR_path]
                        have hA: "top1_path_homotopic_on X TX a a
                            (top1_path_product (top1_path_product \<alpha> \<beta>) (top1_path_product cp g_R_loc))
                            (top1_path_product (top1_path_product (top1_path_product \<alpha> \<beta>) cp) g_R_loc)" .
                        \<comment> \<open>Step B: (\\<alpha>*\\<beta>)*cp ~ \\<alpha>*\\<delta>.\<close>
                        \<comment> \<open>B1: (\\<alpha>*\\<beta>)*cp ~ \\<alpha>*(\\<beta>*cp). [sym of assoc]\<close>
                        from Theorem_51_2_associativity[OF hTX_top halpha_X hbeta_X hcp_path]
                        have "top1_path_homotopic_on X TX a (g (sub3 1))
                            (top1_path_product \<alpha> (top1_path_product \<beta> cp))
                            (top1_path_product (top1_path_product \<alpha> \<beta>) cp)" .
                        from Lemma_51_1_path_homotopic_sym[OF this]
                        have hB1: "top1_path_homotopic_on X TX a (g (sub3 1))
                            (top1_path_product (top1_path_product \<alpha> \<beta>) cp)
                            (top1_path_product \<alpha> (top1_path_product \<beta> cp))" .
                        \<comment> \<open>B2: \\<beta>*cp ~ \\<delta>.
                           cp = \\<beta>\\_bar*\\<delta>, so \\<beta>*cp = \\<beta>*(\\<beta>\\_bar*\\<delta>).\<close>
                        \<comment> \<open>B2a: \\<beta>*(\\<beta>\\_bar*\\<delta>) ~ (\\<beta>*\\<beta>\\_bar)*\\<delta>  [assoc, direct].\<close>
                        from Theorem_51_2_associativity[OF hTX_top hbeta_X hbeta_bar_X h\<delta>_X]
                        have hB2a: "top1_path_homotopic_on X TX b (g (sub3 1))
                            (top1_path_product \<beta> (top1_path_product (top1_path_reverse \<beta>) \<delta>))
                            (top1_path_product (top1_path_product \<beta> (top1_path_reverse \<beta>)) \<delta>)" .
                        \<comment> \<open>B2b: \\<beta>*\\<beta>\\_bar ~ e\\_b.\<close>
                        from Theorem_51_2_invgerse_left[OF hTX_top hbeta_X]
                        have hB2b: "top1_path_homotopic_on X TX b b
                            (top1_path_product \<beta> (top1_path_reverse \<beta>)) (top1_constant_path b)" .
                        \<comment> \<open>B2c: (\\<beta>*\\<beta>\\_bar)*\\<delta> ~ e\\_b*\\<delta>.\<close>
                        from path_homotopic_product_left[OF hTX_top hB2b h\<delta>_X]
                        have hB2c: "top1_path_homotopic_on X TX b (g (sub3 1))
                            (top1_path_product (top1_path_product \<beta> (top1_path_reverse \<beta>)) \<delta>)
                            (top1_path_product (top1_constant_path b) \<delta>)" .
                        \<comment> \<open>B2d: e\\_b*\\<delta> ~ \\<delta>.\<close>
                        from Theorem_51_2_left_identity[OF hTX_top h\<delta>_X]
                        have hB2d: "top1_path_homotopic_on X TX b (g (sub3 1))
                            (top1_path_product (top1_constant_path b) \<delta>) \<delta>" .
                        \<comment> \<open>B2 chain: \\<beta>*cp ~ (\\<beta>*\\<beta>\\_bar)*\\<delta> ~ e\\_b*\\<delta> ~ \\<delta>.\<close>
                        have hB2_cp: "top1_path_product (top1_path_reverse \<beta>) \<delta> = cp"
                          unfolding cp_def ..
                        hence "top1_path_product \<beta> (top1_path_product (top1_path_reverse \<beta>) \<delta>)
                            = top1_path_product \<beta> cp" by simp
                        hence hB2a': "top1_path_homotopic_on X TX b (g (sub3 1))
                            (top1_path_product \<beta> cp)
                            (top1_path_product (top1_path_product \<beta> (top1_path_reverse \<beta>)) \<delta>)"
                          using hB2a by simp
                        from Lemma_51_1_path_homotopic_trans[OF hTX_top hB2a' hB2c]
                        have "top1_path_homotopic_on X TX b (g (sub3 1))
                            (top1_path_product \<beta> cp)
                            (top1_path_product (top1_constant_path b) \<delta>)" .
                        from Lemma_51_1_path_homotopic_trans[OF hTX_top this hB2d]
                        have hB2: "top1_path_homotopic_on X TX b (g (sub3 1))
                            (top1_path_product \<beta> cp) \<delta>" .
                        \<comment> \<open>B3: \\<alpha>*(\\<beta>*cp) ~ \\<alpha>*\\<delta>.\<close>
                        from path_homotopic_product_right[OF hTX_top hB2 halpha_X]
                        have hB3: "top1_path_homotopic_on X TX a (g (sub3 1))
                            (top1_path_product \<alpha> (top1_path_product \<beta> cp))
                            (top1_path_product \<alpha> \<delta>)" .
                        \<comment> \<open>B chain: (\\<alpha>*\\<beta>)*cp ~ \\<alpha>*(\\<beta>*cp) ~ \\<alpha>*\\<delta>.\<close>
                        from Lemma_51_1_path_homotopic_trans[OF hTX_top hB1 hB3]
                        have hB: "top1_path_homotopic_on X TX a (g (sub3 1))
                            (top1_path_product (top1_path_product \<alpha> \<beta>) cp)
                            (top1_path_product \<alpha> \<delta>)" .
                        \<comment> \<open>Step C: ((\\<alpha>*\\<beta>)*cp)*g\\_R ~ (\\<alpha>*\\<delta>)*g\\_R.\<close>
                        from path_homotopic_product_left[OF hTX_top hB hgR_path]
                        have hC: "top1_path_homotopic_on X TX a a
                            (top1_path_product (top1_path_product (top1_path_product \<alpha> \<beta>) cp) g_R_loc)
                            (top1_path_product (top1_path_product \<alpha> \<delta>) g_R_loc)" .
                        \<comment> \<open>Step D: chain A and C. g'\\_alt = cp*g\\_R\\_loc.\<close>
                        have hgalt_eq: "g'_alt = top1_path_product cp g_R_loc"
                          unfolding g'_alt_def hgR_eq ..
                        hence "(top1_path_product (top1_path_product \<alpha> \<beta>) g'_alt)
                            = (top1_path_product (top1_path_product \<alpha> \<beta>) (top1_path_product cp g_R_loc))"
                          by simp
                        hence hA_g': "top1_path_homotopic_on X TX a a
                            (top1_path_product (top1_path_product \<alpha> \<beta>) g'_alt)
                            (top1_path_product (top1_path_product (top1_path_product \<alpha> \<beta>) cp) g_R_loc)"
                          using hA by simp
                        from Lemma_51_1_path_homotopic_trans[OF hTX_top hA_g' hC]
                        show ?thesis .
                      qed
                      \<comment> \<open>Combine: g ~ (\\<alpha>*\\<delta>)*g\\_R ~ (\\<alpha>*\\<beta>)*g'\\_alt.\<close>
                      from Lemma_51_1_path_homotopic_sym[OF hstep2]
                      have "top1_path_homotopic_on X TX a a
                          (top1_path_product (top1_path_product \<alpha> \<delta>) g_R_loc)
                          (top1_path_product (top1_path_product \<alpha> \<beta>) g'_alt)" .
                      from Lemma_51_1_path_homotopic_trans[OF hTX_top hstep1 this]
                      show ?thesis .
                    qed
                    \<comment> \<open>Step 5: IH \\<Rightarrow> gen\\_power(g'\\_alt).\<close>
                    have hg'_gen: "gen_power g'_alt"
                    proof -
                      have "top1_is_loop_on X TX a g'_alt"
                        using hg'_loop unfolding g'_alt_def .
                      moreover from IH have "\<forall>g sub3. k-1 \<ge> 1 \<longrightarrow>
                          top1_is_loop_on X TX a g \<longrightarrow>
                          sub3 0 = 0 \<longrightarrow> sub3 (k-1) = 1 \<longrightarrow>
                          (\<forall>i<k-1. sub3 i < sub3 (Suc i)) \<longrightarrow>
                          (\<forall>i\<le>k-1. g (sub3 i) \<in> U \<inter> V) \<longrightarrow>
                          (\<forall>i<k-1.
                            (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow>
                              g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> U) \<or>
                            (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow>
                              g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> V)) \<longrightarrow>
                          gen_power g" using hk_m1_lt by blast
                      ultimately show ?thesis
                        using hg'_k hg'_0 hg'_km1 hg'_mono hg'_UV hg'_pieces
                        unfolding g'_alt_def by blast
                    qed
                    \<comment> \<open>Step 6: gen\\_power algebra.\<close>
                    show "gen_power g" unfolding gen_power_def
                    proof -
                      let ?ab = "top1_path_product \<alpha> \<beta>"
                      have hab_path: "top1_is_path_on X TX a a ?ab"
                        by (rule top1_path_product_is_path[OF hTX_top halpha_X hbeta_X])
                      have hab_loop: "top1_is_loop_on X TX a ?ab"
                        using hab_path unfolding top1_is_loop_on_def by (by100 blast)
                      from hg'_gen[unfolded gen_power_def]
                      obtain n_g' where hn_g':
                        "top1_path_homotopic_on X TX a a g'_alt
                            (top1_path_power ?ab a n_g')
                        \<or> top1_path_homotopic_on X TX a a g'_alt
                            (top1_path_power (top1_path_reverse ?ab) a n_g')"
                        by blast
                      from hn_g' show "\<exists>n. top1_path_homotopic_on X TX a a g
                          (top1_path_power ?ab a n)
                        \<or> top1_path_homotopic_on X TX a a g
                            (top1_path_power (top1_path_reverse ?ab) a n)"
                      proof
                        \<comment> \<open>Case 1: g' ~ ?ab^n. g ~ ?ab*?ab^n = ?ab^{Suc n}.\<close>
                        assume "top1_path_homotopic_on X TX a a g'_alt
                            (top1_path_power ?ab a n_g')"
                        from path_homotopic_product_right[OF hTX_top this hab_path]
                        have "top1_path_homotopic_on X TX a a
                            (top1_path_product ?ab g'_alt)
                            (top1_path_product ?ab (top1_path_power ?ab a n_g'))" .
                        hence "top1_path_homotopic_on X TX a a
                            (top1_path_product ?ab g'_alt)
                            (top1_path_power ?ab a (Suc n_g'))"
                          unfolding top1_path_power_Suc by assumption
                        from Lemma_51_1_path_homotopic_trans[OF hTX_top hg_htpy_ab_g' this]
                        show ?thesis by blast
                      next
                        \<comment> \<open>Case 2: g' ~ rev(?ab)^n.\<close>
                        assume hg'_rev: "top1_path_homotopic_on X TX a a g'_alt
                            (top1_path_power (top1_path_reverse ?ab) a n_g')"
                        show ?thesis
                        proof (cases n_g')
                          case 0
                          \<comment> \<open>g' ~ e. g ~ ?ab*e ~ ?ab = ?ab^1.\<close>
                          have "top1_path_power (top1_path_reverse ?ab) a 0 = top1_constant_path a"
                            by (by100 simp)
                          hence "top1_path_homotopic_on X TX a a g'_alt (top1_constant_path a)"
                            using hg'_rev 0 by simp
                          from path_homotopic_product_right[OF hTX_top this hab_path]
                          have "top1_path_homotopic_on X TX a a
                              (top1_path_product ?ab g'_alt)
                              (top1_path_product ?ab (top1_constant_path a))" .
                          moreover from Theorem_51_2_right_identity[OF hTX_top hab_path]
                          have "top1_path_homotopic_on X TX a a
                              (top1_path_product ?ab (top1_constant_path a)) ?ab" .
                          ultimately have "top1_path_homotopic_on X TX a a
                              (top1_path_product ?ab g'_alt) ?ab"
                            using Lemma_51_1_path_homotopic_trans[OF hTX_top] by blast
                          hence "top1_path_homotopic_on X TX a a g ?ab"
                            using Lemma_51_1_path_homotopic_trans[OF hTX_top hg_htpy_ab_g']
                            by blast
                          moreover have "top1_path_homotopic_on X TX a a ?ab
                              (top1_path_power ?ab a 1)"
                          proof -
                            have "top1_path_power ?ab a 1 =
                                top1_path_product ?ab (top1_constant_path a)"
                              by (by100 simp)
                            moreover from Theorem_51_2_right_identity[OF hTX_top hab_path]
                            have "top1_path_homotopic_on X TX a a
                                (top1_path_product ?ab (top1_constant_path a)) ?ab" .
                            ultimately have "top1_path_homotopic_on X TX a a
                                (top1_path_power ?ab a 1) ?ab" by simp
                            thus ?thesis by (rule Lemma_51_1_path_homotopic_sym)
                          qed
                          ultimately have "top1_path_homotopic_on X TX a a g
                              (top1_path_power ?ab a 1)"
                            using Lemma_51_1_path_homotopic_trans[OF hTX_top] by blast
                          thus ?thesis by blast
                        next
                          case (Suc m)
                          \<comment> \<open>g ~ ?ab*rev(?ab)^{Suc m} ~ rev(?ab)^m.\<close>
                          have hrev_loop: "top1_is_loop_on X TX a (top1_path_reverse ?ab)"
                            by (rule top1_path_reverse_is_loop[OF hab_loop])
                          have hrev_path: "top1_is_path_on X TX a a (top1_path_reverse ?ab)"
                            using hrev_loop unfolding top1_is_loop_on_def by (by100 blast)
                          have hrev_pow_loop: "top1_is_loop_on X TX a
                              (top1_path_power (top1_path_reverse ?ab) a m)"
                            by (rule top1_path_power_is_loop[OF hTX_top hrev_loop])
                          have hrev_pow_path: "top1_is_path_on X TX a a
                              (top1_path_power (top1_path_reverse ?ab) a m)"
                            using hrev_pow_loop unfolding top1_is_loop_on_def by (by100 blast)
                          \<comment> \<open>g' ~ rev(?ab)^{Suc m} = rev(?ab)*rev(?ab)^m.\<close>
                          have "top1_path_power (top1_path_reverse ?ab) a (Suc m)
                              = top1_path_product (top1_path_reverse ?ab)
                                  (top1_path_power (top1_path_reverse ?ab) a m)"
                            unfolding top1_path_power_Suc ..
                          hence hg'_rev_Suc: "top1_path_homotopic_on X TX a a g'_alt
                              (top1_path_product (top1_path_reverse ?ab)
                                  (top1_path_power (top1_path_reverse ?ab) a m))"
                            using hg'_rev Suc by simp
                          \<comment> \<open>?ab*g' ~ ?ab*(rev*pow).\<close>
                          from path_homotopic_product_right[OF hTX_top hg'_rev_Suc hab_path]
                          have h1: "top1_path_homotopic_on X TX a a
                              (top1_path_product ?ab g'_alt)
                              (top1_path_product ?ab (top1_path_product (top1_path_reverse ?ab)
                                  (top1_path_power (top1_path_reverse ?ab) a m)))" .
                          \<comment> \<open>Assoc: ?ab*(rev*pow) ~ (?ab*rev)*pow.\<close>
                          from Theorem_51_2_associativity[OF hTX_top hab_path hrev_path
                              hrev_pow_path]
                          have h2: "top1_path_homotopic_on X TX a a
                              (top1_path_product ?ab (top1_path_product (top1_path_reverse ?ab)
                                  (top1_path_power (top1_path_reverse ?ab) a m)))
                              (top1_path_product (top1_path_product ?ab (top1_path_reverse ?ab))
                                  (top1_path_power (top1_path_reverse ?ab) a m))" .
                          \<comment> \<open>?ab*rev(?ab) ~ e.\<close>
                          from Theorem_51_2_invgerse_left[OF hTX_top hab_path]
                          have h3: "top1_path_homotopic_on X TX a a
                              (top1_path_product ?ab (top1_path_reverse ?ab))
                              (top1_constant_path a)" .
                          \<comment> \<open>(?ab*rev)*pow ~ e*pow.\<close>
                          from path_homotopic_product_left[OF hTX_top h3 hrev_pow_path]
                          have h4: "top1_path_homotopic_on X TX a a
                              (top1_path_product (top1_path_product ?ab (top1_path_reverse ?ab))
                                  (top1_path_power (top1_path_reverse ?ab) a m))
                              (top1_path_product (top1_constant_path a)
                                  (top1_path_power (top1_path_reverse ?ab) a m))" .
                          \<comment> \<open>e*pow ~ pow.\<close>
                          from Theorem_51_2_left_identity[OF hTX_top hrev_pow_path]
                          have h5: "top1_path_homotopic_on X TX a a
                              (top1_path_product (top1_constant_path a)
                                  (top1_path_power (top1_path_reverse ?ab) a m))
                              (top1_path_power (top1_path_reverse ?ab) a m)" .
                          \<comment> \<open>Chain: g ~ ?ab*g' ~ ?ab*(rev*pow) ~ (?ab*rev)*pow ~ e*pow ~ pow.\<close>
                          from Lemma_51_1_path_homotopic_trans[OF hTX_top hg_htpy_ab_g' h1]
                          have "top1_path_homotopic_on X TX a a g
                              (top1_path_product ?ab (top1_path_product (top1_path_reverse ?ab)
                                  (top1_path_power (top1_path_reverse ?ab) a m)))" .
                          from Lemma_51_1_path_homotopic_trans[OF hTX_top this h2]
                          have "top1_path_homotopic_on X TX a a g
                              (top1_path_product (top1_path_product ?ab (top1_path_reverse ?ab))
                                  (top1_path_power (top1_path_reverse ?ab) a m))" .
                          from Lemma_51_1_path_homotopic_trans[OF hTX_top this h4]
                          have "top1_path_homotopic_on X TX a a g
                              (top1_path_product (top1_constant_path a)
                                  (top1_path_power (top1_path_reverse ?ab) a m))" .
                          from Lemma_51_1_path_homotopic_trans[OF hTX_top this h5]
                          have "top1_path_homotopic_on X TX a a g
                              (top1_path_power (top1_path_reverse ?ab) a m)" .
                          thus ?thesis by blast
                        qed
                      qed
                    qed
                  qed
                next
                  assume hp0V: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> V"
                  \<comment> \<open>piece\\_0 \\<in> V, piece\\_1 \\<in> U. Connecting path \\<alpha>*\\<delta> \\<in> U.
                     g ~ rev(\\<alpha>*\\<beta>) * g'. g' = \\<alpha>*\\<delta>*g\\_R with k-1 pieces.\<close>
                  show ?thesis
                  proof -
                    \<comment> \<open>piece\\_1 \\<in> U (from alternating).\<close>
                    have hp1U: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> U"
                    proof -
                      from hpiece1_type show ?thesis
                      proof
                        assume "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> U"
                        thus ?thesis .
                      next
                        assume "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> V"
                        hence "(\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 0 + t*(sub3 1 - sub3 0)) \<in> V) \<and>
                            (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 1 + t*(sub3 (Suc 1) - sub3 1)) \<in> V)"
                          using hp0V by blast
                        thus ?thesis using False by blast
                      qed
                    qed
                    \<comment> \<open>Build cp\\_v = \\<alpha>*\\<delta>: a \\<rightarrow> b \\<rightarrow> g(sub3(1)), in U.\<close>
                    have hB_sub: "B \<subseteq> X"
                      using hB_open unfolding openin_on_def by (by100 blast)
                    have hV_sub: "V \<subseteq> X"
                      using hV_open unfolding openin_on_def by (by100 blast)
                    have hU_sub: "U \<subseteq> X"
                      using hU_open unfolding openin_on_def by (by100 blast)
                    have h\<delta>_X: "top1_is_path_on X TX b (g (sub3 1)) \<delta>"
                      by (rule path_in_subspace_is_path_in_ambient[OF hTX_top hB_sub h\<delta>])
                    have hbeta_X: "top1_is_path_on X TX b a \<beta>"
                      by (rule path_in_subspace_is_path_in_ambient[OF hTX_top hV_sub hbeta])
                    have halpha_X: "top1_is_path_on X TX a b \<alpha>"
                      by (rule path_in_subspace_is_path_in_ambient[OF hTX_top hU_sub halpha])
                    define cp_v where "cp_v = top1_path_product \<alpha> \<delta>"
                    have hcp_v_path: "top1_is_path_on X TX a (g (sub3 1)) cp_v"
                      unfolding cp_v_def
                      by (rule top1_path_product_is_path[OF hTX_top halpha_X h\<delta>_X])
                    have hcp_v_in_U: "\<forall>s \<in> I_set. cp_v s \<in> U"
                    proof (intro ballI)
                      fix s assume hs: "s \<in> I_set"
                      hence hs01: "0 \<le> s \<and> s \<le> 1"
                        unfolding top1_unit_interval_def by (by100 simp)
                      show "cp_v s \<in> U"
                      proof (cases "s \<le> 1/2")
                        case True
                        hence "cp_v s = \<alpha> (2*s)"
                          unfolding cp_v_def top1_path_product_def by simp
                        also have "... \<in> U"
                        proof -
                          have "2*s \<in> I_set"
                            using True hs01 unfolding top1_unit_interval_def by (by100 simp)
                          from halpha[unfolded top1_is_path_on_def, THEN conjunct1,
                              unfolded top1_continuous_map_on_def]
                          have "\<forall>x \<in> I_set. \<alpha> x \<in> U" by (by100 blast)
                          thus ?thesis using \<open>2*s \<in> I_set\<close> by blast
                        qed
                        finally show ?thesis .
                      next
                        case False hence "s > 1/2" by linarith
                        hence "cp_v s = \<delta> (2*s - 1)"
                          unfolding cp_v_def top1_path_product_def by simp
                        also have "... \<in> U"
                        proof -
                          have "2*s - 1 \<in> I_set"
                            using False hs01 unfolding top1_unit_interval_def by (by100 simp)
                          have "B \<subseteq> U" using hUV_split by (by100 blast)
                          from h\<delta>[unfolded top1_is_path_on_def, THEN conjunct1,
                              unfolded top1_continuous_map_on_def]
                          have "\<forall>x \<in> I_set. \<delta> x \<in> B" by (by100 blast)
                          hence "\<delta> (2*s - 1) \<in> B" using \<open>2*s - 1 \<in> I_set\<close> by blast
                          thus ?thesis using \<open>B \<subseteq> U\<close> by blast
                        qed
                        finally show ?thesis .
                      qed
                    qed
                    have hS_type_v: "(U::'a set) = U \<or> U = V" by blast
                    \<comment> \<open>Apply hgen\\_subdivision\\_only with S=U.\<close>
                    from hgen_subdivision_only[OF hTX_top hk_ge2 hg_loop hs0 hsk hs_inc
                        hs_UV hs_pieces hcp_v_path hcp_v_in_U hU_sub hp1U hS_type_v]
                    obtain sub3_v where
                      hg'v_loop: "top1_is_loop_on X TX a
                        (top1_path_product cp_v (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t)))" and
                      hg'v_k: "(k-1) \<ge> 1" and hg'v_0: "sub3_v 0 = 0" and
                      hg'v_km1: "sub3_v (k-1) = 1" and
                      hg'v_mono: "\<forall>i<k-1. sub3_v i < sub3_v (Suc i)" and
                      hg'v_UV: "\<forall>i\<le>k-1.
                        (top1_path_product cp_v (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))) (sub3_v i)
                          \<in> U \<inter> V" and
                      hg'v_pieces: "\<forall>i<k-1.
                        (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow>
                          (top1_path_product cp_v (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t)))
                            (sub3_v i + t*(sub3_v (Suc i) - sub3_v i)) \<in> U) \<or>
                        (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow>
                          (top1_path_product cp_v (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t)))
                            (sub3_v i + t*(sub3_v (Suc i) - sub3_v i)) \<in> V)"
                      by blast
                    define g'_v where
                      "g'_v = top1_path_product cp_v (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))"
                    \<comment> \<open>g ~ rev(\\<alpha>*\\<beta>)*g'\\_v via path algebra.\<close>
                    have hg_htpy_rab_g': "top1_path_homotopic_on X TX a a g
                        (top1_path_product (top1_path_reverse (top1_path_product \<alpha> \<beta>)) g'_v)"
                    proof -
                      have hsub31_pos: "0 < sub3 1" using hs_inc hs0 hk_ge2 by (by100 force)
                      have hsub31_lt1: "sub3 1 < 1"
                      proof -
                        have "\<And>i j. i < j \<Longrightarrow> j \<le> k \<Longrightarrow> sub3 i < sub3 j"
                        proof -
                          fix i j :: nat assume "i < j" "j \<le> k"
                          thus "sub3 i < sub3 j"
                          proof (induction j)
                            case 0 thus ?case by simp
                          next
                            case (Suc j) show ?case
                            proof (cases "i = j")
                              case True thus ?thesis using hs_inc Suc.prems by simp
                            next
                              case False hence "sub3 i < sub3 j" using Suc by linarith
                              also have "sub3 j < sub3 (Suc j)" using hs_inc Suc.prems by simp
                              finally show ?thesis .
                            qed
                          qed
                        qed
                        from this[of 1 k] have "sub3 1 < sub3 k" using hk_ge2 by simp
                        thus ?thesis using hsk by linarith
                      qed
                      define g_L where "g_L = (\<lambda>t. g (sub3 1 * t))"
                      define g_R_loc where "g_R_loc = (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))"
                      have hg_path: "top1_is_path_on X TX a a g"
                        using hg_loop unfolding top1_is_loop_on_def by (by100 blast)
                      have hg0: "g 0 = a"
                        using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                        by (by100 blast)
                      have hg_split: "top1_path_homotopic_on X TX a a g
                          (top1_path_product g_L g_R_loc)"
                        unfolding g_L_def g_R_loc_def
                        by (rule path_product_split[OF hTX_top hg_path hsub31_pos hsub31_lt1])
                      have hgR_eq: "g_R_loc = (\<lambda>t. g (sub3 1 + (1 - sub3 1) * t))"
                        unfolding g_R_loc_def ..
                      \<comment> \<open>Path properties.\<close>
                      have hgL_path: "top1_is_path_on X TX a (g (sub3 1)) g_L"
                      proof -
                        have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
                          using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                          by (by100 blast)
                        have "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. t * sub3 1)"
                        proof -
                          have "top1_continuous_map_on I_set I_top I_set I_top
                              (\<lambda>t. 0 + t * (sub3 1 - 0))"
                            by (rule affine_map_continuous_I_to_I)
                               (use hsub31_pos hsub31_lt1 in linarith)+
                          thus ?thesis by simp
                        qed
                        hence "top1_continuous_map_on I_set I_top X TX (g \<circ> (\<lambda>t. t * sub3 1))"
                          by (rule top1_continuous_map_on_comp[OF _ hg_cont])
                        moreover have "(g \<circ> (\<lambda>t. t * sub3 1)) = (\<lambda>t. g (sub3 1 * t))"
                          by (rule ext) (simp add: mult.commute)
                        ultimately have "top1_continuous_map_on I_set I_top X TX
                            (\<lambda>t. g (sub3 1 * t))" by simp
                        moreover have "(\<lambda>t. g (sub3 1 * t)) 0 = a" using hg0 by simp
                        moreover have "(\<lambda>t. g (sub3 1 * t)) 1 = g (sub3 1)" by simp
                        ultimately show ?thesis unfolding g_L_def top1_is_path_on_def by blast
                      qed
                      have hgR_path: "top1_is_path_on X TX (g (sub3 1)) a g_R_loc"
                      proof -
                        have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
                          using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                          by (by100 blast)
                        have hg1: "g 1 = a"
                          using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def
                          by (by100 blast)
                        have "top1_continuous_map_on I_set I_top I_set I_top
                            (\<lambda>t. sub3 1 + t * (1 - sub3 1))"
                          by (rule affine_map_continuous_I_to_I)
                             (use hsub31_pos hsub31_lt1 in linarith)+
                        hence "top1_continuous_map_on I_set I_top X TX
                            (g \<circ> (\<lambda>t. sub3 1 + t * (1 - sub3 1)))"
                          by (rule top1_continuous_map_on_comp[OF _ hg_cont])
                        moreover have "(g \<circ> (\<lambda>t. sub3 1 + t * (1 - sub3 1))) = g_R_loc"
                          unfolding g_R_loc_def by (rule ext) (simp add: algebra_simps)
                        ultimately have "top1_continuous_map_on I_set I_top X TX g_R_loc"
                          by simp
                        moreover have "g_R_loc 0 = g (sub3 1)"
                          unfolding g_R_loc_def by simp
                        moreover have "g_R_loc 1 = a"
                          unfolding g_R_loc_def using hg1 by simp
                        ultimately show ?thesis unfolding top1_is_path_on_def by blast
                      qed
                      \<comment> \<open>SC of V: g\\_L ~ \\<beta>\\_bar*\\<delta> in V.\<close>
                      have hbeta_bar_X: "top1_is_path_on X TX a b (top1_path_reverse \<beta>)"
                        by (rule top1_path_reverse_is_path[OF hbeta_X])
                      have h_bd_path: "top1_is_path_on X TX a (g (sub3 1))
                          (top1_path_product (top1_path_reverse \<beta>) \<delta>)"
                        by (rule top1_path_product_is_path[OF hTX_top hbeta_bar_X h\<delta>_X])
                      have hgL_htpy: "top1_path_homotopic_on X TX a (g (sub3 1)) g_L
                          (top1_path_product (top1_path_reverse \<beta>) \<delta>)"
                      proof -
                        have hsimp_gL: "\<And>t. g(sub3 0 + t*(sub3 1 - sub3 0)) = g_L t"
                          unfolding g_L_def using hs0 by (simp add: mult.commute)
                        have hgL_in_V: "\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g_L t \<in> V"
                          using hp0V hsimp_gL by (simp add: mult.commute)
                        have hgL_V: "top1_is_path_on V (subspace_topology X TX V) a (g (sub3 1)) g_L"
                        proof -
                          have hgL_img: "\<forall>s \<in> I_set. g_L s \<in> V"
                          proof (intro ballI)
                            fix s assume "s \<in> I_set"
                            hence "0 \<le> s \<and> s \<le> 1"
                              unfolding top1_unit_interval_def by (by100 simp)
                            thus "g_L s \<in> V" using hgL_in_V by blast
                          qed
                          have hgL_cont: "top1_continuous_map_on I_set I_top X TX g_L"
                            using hgL_path unfolding top1_is_path_on_def by (by100 blast)
                          have "top1_continuous_map_on I_set I_top V (subspace_topology X TX V) g_L"
                            by (rule continuous_map_restrict_codomain[OF hgL_cont hgL_img hV_sub])
                          thus ?thesis unfolding top1_is_path_on_def
                            using ha_V_loc hgL_path[unfolded top1_is_path_on_def] by blast
                        qed
                        have h_bd_V: "top1_is_path_on V (subspace_topology X TX V) a (g (sub3 1))
                            (top1_path_product (top1_path_reverse \<beta>) \<delta>)"
                        proof -
                          have h\<beta>bar_V: "top1_is_path_on V (subspace_topology X TX V) a b
                              (top1_path_reverse \<beta>)"
                          proof -
                            from top1_continuous_map_on_codomain_enlarge[OF
                                hbeta[unfolded top1_is_path_on_def, THEN conjunct1]
                                subset_refl hV_sub]
                            have "top1_continuous_map_on I_set I_top V (subspace_topology X TX V) \<beta>" .
                            hence "top1_is_path_on V (subspace_topology X TX V) b a \<beta>"
                              unfolding top1_is_path_on_def
                              using hbeta[unfolded top1_is_path_on_def] by blast
                            thus ?thesis
                              by (rule top1_path_reverse_is_path)
                          qed
                          have "B \<subseteq> V" using hUV_split by (by100 blast)
                          have h\<delta>_V: "top1_is_path_on V (subspace_topology X TX V) b (g (sub3 1)) \<delta>"
                          proof -
                            from top1_continuous_map_on_codomain_enlarge[OF
                                h\<delta>[unfolded top1_is_path_on_def, THEN conjunct1]
                                \<open>B \<subseteq> V\<close> hV_sub]
                            have "top1_continuous_map_on I_set I_top V (subspace_topology X TX V) \<delta>" .
                            thus ?thesis unfolding top1_is_path_on_def
                              using hb h\<delta>[unfolded top1_is_path_on_def] \<open>B \<subseteq> V\<close>
                              by (by100 blast)
                          qed
                          show ?thesis
                            by (rule top1_path_product_is_path[OF
                                subspace_topology_is_topology_on[OF hTX_top hV_sub]
                                h\<beta>bar_V h\<delta>_V])
                        qed
                        from simply_connected_paths_homotopic[OF hV_sc hgL_V h_bd_V ha_V_loc]
                        have "top1_path_homotopic_on V (subspace_topology X TX V)
                            a (g (sub3 1)) g_L
                            (top1_path_product (top1_path_reverse \<beta>) \<delta>)" .
                        from path_homotopic_subspace_to_ambient[OF hTX_top hV_sub _ this]
                        show ?thesis by (by100 simp)
                      qed
                      \<comment> \<open>g ~ (\\<beta>\\_bar*\\<delta>)*g\\_R\\_loc.\<close>
                      have hstep1: "top1_path_homotopic_on X TX a a g
                          (top1_path_product (top1_path_product (top1_path_reverse \<beta>) \<delta>) g_R_loc)"
                      proof -
                        from path_homotopic_product_left[OF hTX_top hgL_htpy hgR_path]
                        have "top1_path_homotopic_on X TX a a
                            (top1_path_product g_L g_R_loc)
                            (top1_path_product (top1_path_product (top1_path_reverse \<beta>) \<delta>) g_R_loc)" .
                        from Lemma_51_1_path_homotopic_trans[OF hTX_top hg_split this]
                        show ?thesis .
                      qed
                      \<comment> \<open>rev(\\<alpha>*\\<beta>) = \\<beta>\\_bar*\\<alpha>\\_bar (function equality).\<close>
                      have halpha_bar_X: "top1_is_path_on X TX b a (top1_path_reverse \<alpha>)"
                        by (rule top1_path_reverse_is_path[OF halpha_X])
                      have hrev_eq: "top1_path_reverse (top1_path_product \<alpha> \<beta>)
                          = top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>)"
                      proof (rule ext)
                        fix s :: real
                        show "top1_path_reverse (top1_path_product \<alpha> \<beta>) s =
                            top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>) s"
                        proof -
                          have ha0: "\<alpha> 0 = a"
                            using halpha unfolding top1_is_path_on_def by (by100 blast)
                          have ha1: "\<alpha> 1 = b"
                            using halpha unfolding top1_is_path_on_def by (by100 blast)
                          have hb0: "\<beta> 0 = b"
                            using hbeta unfolding top1_is_path_on_def by (by100 blast)
                          have hb1: "\<beta> 1 = a"
                            using hbeta unfolding top1_is_path_on_def by (by100 blast)
                          show ?thesis
                            unfolding top1_path_reverse_def top1_path_product_def
                            using ha0 ha1 hb0 hb1 by (simp add: field_simps)
                        qed
                      qed
                      \<comment> \<open>Path algebra: rev(\\<alpha>*\\<beta>)*g'\\_v = (\\<beta>\\_bar*\\<alpha>\\_bar)*(\\<alpha>*\\<delta>*g\\_R) ~ (\\<beta>\\_bar*\\<delta>)*g\\_R.\<close>
                      have hrab_path: "top1_is_path_on X TX a a
                          (top1_path_reverse (top1_path_product \<alpha> \<beta>))"
                      proof -
                        have "top1_is_path_on X TX a a (top1_path_product \<alpha> \<beta>)"
                          by (rule top1_path_product_is_path[OF hTX_top halpha_X hbeta_X])
                        thus ?thesis by (rule top1_path_reverse_is_path)
                      qed
                      have hba_path: "top1_is_path_on X TX a a
                          (top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>))"
                        by (rule top1_path_product_is_path[OF hTX_top hbeta_bar_X halpha_bar_X])
                      have hstep2: "top1_path_homotopic_on X TX a a
                          (top1_path_product (top1_path_reverse (top1_path_product \<alpha> \<beta>)) g'_v)
                          (top1_path_product (top1_path_product (top1_path_reverse \<beta>) \<delta>) g_R_loc)"
                      proof -
                        \<comment> \<open>Rewrite rev(\\<alpha>*\\<beta>) to \\<beta>\\_bar*\\<alpha>\\_bar.\<close>
                        have h_rewrite: "top1_path_product (top1_path_reverse (top1_path_product \<alpha> \<beta>)) g'_v
                            = top1_path_product (top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>)) g'_v"
                          using hrev_eq by simp
                        \<comment> \<open>g'\\_v = cp\\_v*g\\_R\\_loc = (\\<alpha>*\\<delta>)*g\\_R\\_loc.\<close>
                        have hgv_eq: "g'_v = top1_path_product cp_v g_R_loc"
                          unfolding g'_v_def hgR_eq ..
                        \<comment> \<open>Assoc: (\\<beta>\\_bar*\\<alpha>\\_bar)*((\\<alpha>*\\<delta>)*g\\_R) ~ ((\\<beta>\\_bar*\\<alpha>\\_bar)*(\\<alpha>*\\<delta>))*g\\_R.\<close>
                        from Theorem_51_2_associativity[OF hTX_top hba_path hcp_v_path hgR_path]
                        have hA: "top1_path_homotopic_on X TX a a
                            (top1_path_product (top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>))
                                (top1_path_product cp_v g_R_loc))
                            (top1_path_product (top1_path_product (top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>)) cp_v)
                                g_R_loc)" .
                        \<comment> \<open>(\\<beta>\\_bar*\\<alpha>\\_bar)*(\\<alpha>*\\<delta>) ~ \\<beta>\\_bar*\\<delta>.\<close>
                        \<comment> \<open>B1: (\\<beta>\\_bar*\\<alpha>\\_bar)*(\\<alpha>*\\<delta>) ~ \\<beta>\\_bar*(\\<alpha>\\_bar*(\\<alpha>*\\<delta>)).\<close>
                        from Theorem_51_2_associativity[OF hTX_top hbeta_bar_X halpha_bar_X hcp_v_path]
                        have "top1_path_homotopic_on X TX a (g (sub3 1))
                            (top1_path_product (top1_path_reverse \<beta>) (top1_path_product (top1_path_reverse \<alpha>) cp_v))
                            (top1_path_product (top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>)) cp_v)" .
                        from Lemma_51_1_path_homotopic_sym[OF this]
                        have hB1: "top1_path_homotopic_on X TX a (g (sub3 1))
                            (top1_path_product (top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>)) cp_v)
                            (top1_path_product (top1_path_reverse \<beta>) (top1_path_product (top1_path_reverse \<alpha>) cp_v))" .
                        \<comment> \<open>\\<alpha>\\_bar*(\\<alpha>*\\<delta>) ~ \\<delta>.\<close>
                        from Theorem_51_2_associativity[OF hTX_top halpha_bar_X halpha_X h\<delta>_X]
                        have "top1_path_homotopic_on X TX b (g (sub3 1))
                            (top1_path_product (top1_path_reverse \<alpha>) (top1_path_product \<alpha> \<delta>))
                            (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) \<alpha>) \<delta>)" .
                        hence hB2a: "top1_path_homotopic_on X TX b (g (sub3 1))
                            (top1_path_product (top1_path_reverse \<alpha>) cp_v)
                            (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) \<alpha>) \<delta>)"
                          unfolding cp_v_def .
                        from Theorem_51_2_invgerse_right[OF hTX_top halpha_X]
                        have hB2b: "top1_path_homotopic_on X TX b b
                            (top1_path_product (top1_path_reverse \<alpha>) \<alpha>) (top1_constant_path b)" .
                        from path_homotopic_product_left[OF hTX_top hB2b h\<delta>_X]
                        have hB2c: "top1_path_homotopic_on X TX b (g (sub3 1))
                            (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) \<alpha>) \<delta>)
                            (top1_path_product (top1_constant_path b) \<delta>)" .
                        from Theorem_51_2_left_identity[OF hTX_top h\<delta>_X]
                        have hB2d: "top1_path_homotopic_on X TX b (g (sub3 1))
                            (top1_path_product (top1_constant_path b) \<delta>) \<delta>" .
                        from Lemma_51_1_path_homotopic_trans[OF hTX_top hB2a hB2c]
                        have "top1_path_homotopic_on X TX b (g (sub3 1))
                            (top1_path_product (top1_path_reverse \<alpha>) cp_v)
                            (top1_path_product (top1_constant_path b) \<delta>)" .
                        from Lemma_51_1_path_homotopic_trans[OF hTX_top this hB2d]
                        have hB2: "top1_path_homotopic_on X TX b (g (sub3 1))
                            (top1_path_product (top1_path_reverse \<alpha>) cp_v) \<delta>" .
                        \<comment> \<open>\\<beta>\\_bar*(\\<alpha>\\_bar*cp\\_v) ~ \\<beta>\\_bar*\\<delta>.\<close>
                        from path_homotopic_product_right[OF hTX_top hB2 hbeta_bar_X]
                        have hB3: "top1_path_homotopic_on X TX a (g (sub3 1))
                            (top1_path_product (top1_path_reverse \<beta>) (top1_path_product (top1_path_reverse \<alpha>) cp_v))
                            (top1_path_product (top1_path_reverse \<beta>) \<delta>)" .
                        from Lemma_51_1_path_homotopic_trans[OF hTX_top hB1 hB3]
                        have hB: "top1_path_homotopic_on X TX a (g (sub3 1))
                            (top1_path_product (top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>)) cp_v)
                            (top1_path_product (top1_path_reverse \<beta>) \<delta>)" .
                        from path_homotopic_product_left[OF hTX_top hB hgR_path]
                        have hC: "top1_path_homotopic_on X TX a a
                            (top1_path_product (top1_path_product (top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>)) cp_v) g_R_loc)
                            (top1_path_product (top1_path_product (top1_path_reverse \<beta>) \<delta>) g_R_loc)" .
                        \<comment> \<open>Combine: rewrite + assoc + algebra.\<close>
                        have "top1_path_product (top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>))
                            (top1_path_product cp_v g_R_loc)
                          = top1_path_product (top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>)) g'_v"
                          using hgv_eq by simp
                        hence hA': "top1_path_homotopic_on X TX a a
                            (top1_path_product (top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>)) g'_v)
                            (top1_path_product (top1_path_product (top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>)) cp_v) g_R_loc)"
                          using hA by simp
                        from Lemma_51_1_path_homotopic_trans[OF hTX_top hA' hC]
                        have "top1_path_homotopic_on X TX a a
                            (top1_path_product (top1_path_product (top1_path_reverse \<beta>) (top1_path_reverse \<alpha>)) g'_v)
                            (top1_path_product (top1_path_product (top1_path_reverse \<beta>) \<delta>) g_R_loc)" .
                        thus ?thesis using h_rewrite by simp
                      qed
                      from Lemma_51_1_path_homotopic_sym[OF hstep2]
                      have "top1_path_homotopic_on X TX a a
                          (top1_path_product (top1_path_product (top1_path_reverse \<beta>) \<delta>) g_R_loc)
                          (top1_path_product (top1_path_reverse (top1_path_product \<alpha> \<beta>)) g'_v)" .
                      from Lemma_51_1_path_homotopic_trans[OF hTX_top hstep1 this]
                      show ?thesis .
                    qed
                    \<comment> \<open>IH \\<Rightarrow> gen\\_power(g'\\_v).\<close>
                    have hg'v_gen: "gen_power g'_v"
                    proof -
                      have "top1_is_loop_on X TX a g'_v"
                        using hg'v_loop unfolding g'_v_def .
                      moreover from IH have "\<forall>g sub3. k-1 \<ge> 1 \<longrightarrow>
                          top1_is_loop_on X TX a g \<longrightarrow>
                          sub3 0 = 0 \<longrightarrow> sub3 (k-1) = 1 \<longrightarrow>
                          (\<forall>i<k-1. sub3 i < sub3 (Suc i)) \<longrightarrow>
                          (\<forall>i\<le>k-1. g (sub3 i) \<in> U \<inter> V) \<longrightarrow>
                          (\<forall>i<k-1.
                            (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow>
                              g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> U) \<or>
                            (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow>
                              g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> V)) \<longrightarrow>
                          gen_power g" using hk_m1_lt by blast
                      ultimately show ?thesis
                        using hg'v_k hg'v_0 hg'v_km1 hg'v_mono hg'v_UV hg'v_pieces
                        unfolding g'_v_def by blast
                    qed
                    \<comment> \<open>gen\\_power algebra with rev(\\<alpha>*\\<beta>).\<close>
                    show "gen_power g" unfolding gen_power_def
                    proof -
                      let ?ab = "top1_path_product \<alpha> \<beta>"
                      have hab_path: "top1_is_path_on X TX a a ?ab"
                        by (rule top1_path_product_is_path[OF hTX_top halpha_X hbeta_X])
                      have hab_loop: "top1_is_loop_on X TX a ?ab"
                        using hab_path unfolding top1_is_loop_on_def by (by100 blast)
                      have hrab_path: "top1_is_path_on X TX a a (top1_path_reverse ?ab)"
                        by (rule top1_path_reverse_is_path[OF hab_path])
                      from hg'v_gen[unfolded gen_power_def]
                      obtain n_g' where hn_g':
                        "top1_path_homotopic_on X TX a a g'_v
                            (top1_path_power ?ab a n_g')
                        \<or> top1_path_homotopic_on X TX a a g'_v
                            (top1_path_power (top1_path_reverse ?ab) a n_g')"
                        by blast
                      from hn_g' show "\<exists>n. top1_path_homotopic_on X TX a a g
                          (top1_path_power ?ab a n)
                        \<or> top1_path_homotopic_on X TX a a g
                            (top1_path_power (top1_path_reverse ?ab) a n)"
                      proof
                        \<comment> \<open>Case 1: g' ~ ?ab^n. Mixed: rev(?ab)*?ab^n.\<close>
                        assume hg'_pos: "top1_path_homotopic_on X TX a a g'_v
                            (top1_path_power ?ab a n_g')"
                        show ?thesis
                        proof (cases n_g')
                          case 0
                          \<comment> \<open>?ab^0 = const. g ~ rev(?ab)*const ~ rev(?ab) = rev(?ab)^1.\<close>
                          have "top1_path_power ?ab a 0 = top1_constant_path a" by (by100 simp)
                          hence "top1_path_homotopic_on X TX a a g'_v (top1_constant_path a)"
                            using hg'_pos 0 by simp
                          from path_homotopic_product_right[OF hTX_top this hrab_path]
                          have "top1_path_homotopic_on X TX a a
                              (top1_path_product (top1_path_reverse ?ab) g'_v)
                              (top1_path_product (top1_path_reverse ?ab) (top1_constant_path a))" .
                          moreover from Theorem_51_2_right_identity[OF hTX_top hrab_path]
                          have "top1_path_homotopic_on X TX a a
                              (top1_path_product (top1_path_reverse ?ab) (top1_constant_path a))
                              (top1_path_reverse ?ab)" .
                          ultimately have "top1_path_homotopic_on X TX a a
                              (top1_path_product (top1_path_reverse ?ab) g'_v) (top1_path_reverse ?ab)"
                            using Lemma_51_1_path_homotopic_trans[OF hTX_top] by blast
                          hence "top1_path_homotopic_on X TX a a g (top1_path_reverse ?ab)"
                            using Lemma_51_1_path_homotopic_trans[OF hTX_top hg_htpy_rab_g']
                            by blast
                          moreover have "top1_path_homotopic_on X TX a a (top1_path_reverse ?ab)
                              (top1_path_power (top1_path_reverse ?ab) a 1)"
                          proof -
                            have "top1_path_power (top1_path_reverse ?ab) a 1
                                = top1_path_product (top1_path_reverse ?ab) (top1_constant_path a)"
                              by (by100 simp)
                            from Lemma_51_1_path_homotopic_sym[OF
                                Theorem_51_2_right_identity[OF hTX_top hrab_path]]
                            show ?thesis using \<open>top1_path_power _ a 1 = _\<close> by simp
                          qed
                          ultimately show ?thesis
                            using Lemma_51_1_path_homotopic_trans[OF hTX_top] by blast
                        next
                          case (Suc m)
                          \<comment> \<open>rev(?ab)*?ab^{Suc m} = rev(?ab)*?ab*?ab^m ~ const*?ab^m ~ ?ab^m.\<close>
                          have hab_pow_loop: "top1_is_loop_on X TX a (top1_path_power ?ab a m)"
                            by (rule top1_path_power_is_loop[OF hTX_top hab_loop])
                          have hab_pow_path: "top1_is_path_on X TX a a (top1_path_power ?ab a m)"
                            using hab_pow_loop unfolding top1_is_loop_on_def by (by100 blast)
                          have "top1_path_power ?ab a (Suc m)
                              = top1_path_product ?ab (top1_path_power ?ab a m)"
                            unfolding top1_path_power_Suc ..
                          hence hg'_Suc: "top1_path_homotopic_on X TX a a g'_v
                              (top1_path_product ?ab (top1_path_power ?ab a m))"
                            using hg'_pos Suc by simp
                          from path_homotopic_product_right[OF hTX_top hg'_Suc hrab_path]
                          have h1: "top1_path_homotopic_on X TX a a
                              (top1_path_product (top1_path_reverse ?ab) g'_v)
                              (top1_path_product (top1_path_reverse ?ab)
                                  (top1_path_product ?ab (top1_path_power ?ab a m)))" .
                          from Theorem_51_2_associativity[OF hTX_top hrab_path hab_path hab_pow_path]
                          have h2: "top1_path_homotopic_on X TX a a
                              (top1_path_product (top1_path_reverse ?ab)
                                  (top1_path_product ?ab (top1_path_power ?ab a m)))
                              (top1_path_product (top1_path_product (top1_path_reverse ?ab) ?ab)
                                  (top1_path_power ?ab a m))" .
                          from Theorem_51_2_invgerse_right[OF hTX_top hab_path]
                          have h3: "top1_path_homotopic_on X TX a a
                              (top1_path_product (top1_path_reverse ?ab) ?ab)
                              (top1_constant_path a)" .
                          from path_homotopic_product_left[OF hTX_top h3 hab_pow_path]
                          have h4: "top1_path_homotopic_on X TX a a
                              (top1_path_product (top1_path_product (top1_path_reverse ?ab) ?ab)
                                  (top1_path_power ?ab a m))
                              (top1_path_product (top1_constant_path a)
                                  (top1_path_power ?ab a m))" .
                          from Theorem_51_2_left_identity[OF hTX_top hab_pow_path]
                          have h5: "top1_path_homotopic_on X TX a a
                              (top1_path_product (top1_constant_path a)
                                  (top1_path_power ?ab a m))
                              (top1_path_power ?ab a m)" .
                          from Lemma_51_1_path_homotopic_trans[OF hTX_top hg_htpy_rab_g' h1]
                          have "top1_path_homotopic_on X TX a a g
                              (top1_path_product (top1_path_reverse ?ab)
                                  (top1_path_product ?ab (top1_path_power ?ab a m)))" .
                          from Lemma_51_1_path_homotopic_trans[OF hTX_top this h2]
                          have "top1_path_homotopic_on X TX a a g
                              (top1_path_product (top1_path_product (top1_path_reverse ?ab) ?ab)
                                  (top1_path_power ?ab a m))" .
                          from Lemma_51_1_path_homotopic_trans[OF hTX_top this h4]
                          have "top1_path_homotopic_on X TX a a g
                              (top1_path_product (top1_constant_path a)
                                  (top1_path_power ?ab a m))" .
                          from Lemma_51_1_path_homotopic_trans[OF hTX_top this h5]
                          have "top1_path_homotopic_on X TX a a g
                              (top1_path_power ?ab a m)" .
                          thus ?thesis by blast
                        qed
                      next
                        \<comment> \<open>Case 2: g' ~ rev(?ab)^n. Then g ~ rev(?ab)*rev(?ab)^n = rev(?ab)^{Suc n}.\<close>
                        assume "top1_path_homotopic_on X TX a a g'_v
                            (top1_path_power (top1_path_reverse ?ab) a n_g')"
                        from path_homotopic_product_right[OF hTX_top this hrab_path]
                        have "top1_path_homotopic_on X TX a a
                            (top1_path_product (top1_path_reverse ?ab) g'_v)
                            (top1_path_product (top1_path_reverse ?ab)
                                (top1_path_power (top1_path_reverse ?ab) a n_g'))" .
                        hence "top1_path_homotopic_on X TX a a
                            (top1_path_product (top1_path_reverse ?ab) g'_v)
                            (top1_path_power (top1_path_reverse ?ab) a (Suc n_g'))"
                          unfolding top1_path_power_Suc by assumption
                        from Lemma_51_1_path_homotopic_trans[OF hTX_top hg_htpy_rab_g' this]
                        show ?thesis by blast
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
    have h_from_refined: "\<And>k g sub3.
        k \<ge> 1 \<Longrightarrow> top1_is_loop_on X TX a g \<Longrightarrow>
        sub3 0 = 0 \<Longrightarrow> sub3 k = 1 \<Longrightarrow>
        (\<forall>i<k. sub3 i < sub3 (Suc i)) \<Longrightarrow>
        (\<forall>i\<le>k. g (sub3 i) \<in> U \<inter> V) \<Longrightarrow>
        (\<forall>i<k. (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> U) \<or>
               (\<forall>t. 0\<le>t \<and> t\<le>1 \<longrightarrow> g(sub3 i + t*(sub3 (Suc i) - sub3 i)) \<in> V)) \<Longrightarrow>
        (\<exists>n::nat. top1_path_homotopic_on X TX a a g
            (top1_path_power (top1_path_product \<alpha> \<beta>) a n)
          \<or> top1_path_homotopic_on X TX a a g
               (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n))"
      using h_from_refined_ind unfolding gen_power_def by blast
    show "\<exists>n::nat. top1_path_homotopic_on X TX a a f (top1_path_power (top1_path_product \<alpha> \<beta>) a n)
        \<or> top1_path_homotopic_on X TX a a f
             (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n)"
      by (rule h_from_refined[OF hm_pos hf hsub2_0 hsub2_m hsub2_inc hsub2_UV hpieces2_UV])
  qed
  \<comment> \<open>Step 2: [\\<alpha>*\\<beta>] is non-trivial (Theorem 63.1).\<close>
  have ha_U: "a \<in> U" using hUV_split ha by (by100 blast)
  have hb_U: "b \<in> U" using hUV_split hb by (by100 blast)
  have ha_V: "a \<in> V" using hUV_split ha by (by100 blast)
  have hb_V: "b \<in> V" using hUV_split hb by (by100 blast)
  have hU_sub: "U \<subseteq> X" using hU_open unfolding openin_on_def by (by100 blast)
  have hV_sub: "V \<subseteq> X" using hV_open unfolding openin_on_def by (by100 blast)
  have halpha_X: "top1_is_path_on X TX a b \<alpha>"
    by (rule path_in_subspace_is_path_in_ambient[OF hTX_top hU_sub halpha])
  have hbeta_X: "top1_is_path_on X TX b a \<beta>"
    by (rule path_in_subspace_is_path_in_ambient[OF hTX_top hV_sub hbeta])
  have hnontrivial: "\<not> top1_path_homotopic_on X TX a a
      (top1_path_product \<alpha> \<beta>) (top1_constant_path a)"
    by (rule Theorem_63_1_loop_nontrivial[OF hTX_top hU_open hV_open hcover hUV_split
        hAB_disj hA_open hB_open ha hb halpha hbeta])
  \<comment> \<open>Step 3: [\\<alpha>*\\<beta>] has infinite order (no positive power is trivial).\<close>
  have hinf_order: "\<And>m::nat. m > 0 \<Longrightarrow> \<not> top1_path_homotopic_on X TX a a
      (top1_path_power (top1_path_product \<alpha> \<beta>) a m) (top1_constant_path a)"
  proof -
    fix m :: nat assume "m > 0"
    \<comment> \<open>Use Theorem\\_63\\_1\\_c\\_subgroups\\_trivial with a'=a, \\<gamma>=const(a), \\<delta>=const(a).\<close>
    have ha_U_loc: "a \<in> U" using hUV_split ha by (by100 blast)
    have ha_V_loc: "a \<in> V" using hUV_split ha by (by100 blast)
    have hconst_U: "top1_is_path_on U (subspace_topology X TX U) a a (top1_constant_path a)"
    proof -
      have "is_topology_on U (subspace_topology X TX U)"
        by (rule subspace_topology_is_topology_on[OF hTX_top hU_sub])
      from top1_constant_path_is_path[OF this ha_U_loc] show ?thesis .
    qed
    have hconst_V: "top1_is_path_on V (subspace_topology X TX V) a a (top1_constant_path a)"
    proof -
      have "is_topology_on V (subspace_topology X TX V)"
        by (rule subspace_topology_is_topology_on[OF hTX_top hV_sub])
      from top1_constant_path_is_path[OF this ha_V_loc] show ?thesis .
    qed
    \<comment> \<open>If [\\<alpha>*\\<beta>]^m \\<sim> e = [const*const]^0, then m = 0 by Theorem 63.1(c).\<close>
    show "\<not> top1_path_homotopic_on X TX a a
        (top1_path_power (top1_path_product \<alpha> \<beta>) a m) (top1_constant_path a)"
    proof
      assume "top1_path_homotopic_on X TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a m) (top1_constant_path a)"
      \<comment> \<open>const = path\\_power(const*const, a, 0), so htpy above gives [\\<alpha>*\\<beta>]^m \\<sim> [const*const]^0.\<close>
      have "top1_path_power (top1_path_product (top1_constant_path a) (top1_constant_path a)) a 0
          = top1_constant_path a" by (by100 simp)
      have "top1_path_homotopic_on X TX a a
          (top1_path_power (top1_path_product \<alpha> \<beta>) a m)
          (top1_path_power (top1_path_product (top1_constant_path a) (top1_constant_path a)) a 0)"
        using \<open>top1_path_homotopic_on X TX a a _ (top1_constant_path a)\<close>
          \<open>top1_path_power _ a 0 = top1_constant_path a\<close> by (by100 simp)
      from Theorem_63_1_c_subgroups_trivial[OF hTX_top hU_open hV_open hcover hUV_split
          hAB_disj hA_open hB_open ha hb halpha hbeta ha hconst_U hconst_V this]
      have "m = 0" .
      thus False using \<open>m > 0\<close> by (by100 simp)
    qed
  qed
  \<comment> \<open>Step 4: Construct iso \\<pi>\\_1(X, a) \\<cong> \\<Z>.
     Show \\<pi>\\_1 is free on {0} via [\\<alpha>*\\<beta>]. Then \\<pi>\\_1 \\<cong> \\<Z> from free\\_group\\_hom\\_generators\\_iso.\<close>
  have ha_X: "a \<in> X" using hUV_split ha hcover by (by100 blast)
  let ?pi = "top1_fundamental_group_carrier X TX a"
  let ?mul = "top1_fundamental_group_mul X TX a"
  let ?eid = "top1_fundamental_group_id X TX a"
  let ?invg = "top1_fundamental_group_invg X TX a"
  have hpi_grp: "top1_is_group_on ?pi ?mul ?eid ?invg"
    by (rule top1_fundamental_group_is_group[OF hTX_top ha_X])
  \<comment> \<open>\\<pi>\\_1 is free on {0::nat} via [\\<alpha>*\\<beta>].\<close>
  have hpi_free: "top1_is_free_group_full_on ?pi ?mul ?eid ?invg
      (\<lambda>(_::nat). {g. top1_loop_equiv_on X TX a (top1_path_product \<alpha> \<beta>) g}) {0::nat}"
    unfolding top1_is_free_group_full_on_def
  proof (intro conjI)
    show "top1_is_group_on ?pi ?mul ?eid ?invg" by (rule hpi_grp)
    show "\<forall>s\<in>{0::nat}. (\<lambda>(_::nat). {g. top1_loop_equiv_on X TX a (top1_path_product \<alpha> \<beta>) g}) s \<in> ?pi"
    proof (intro ballI)
      fix s :: nat assume "s \<in> {0::nat}"
      have "top1_is_loop_on X TX a (top1_path_product \<alpha> \<beta>)"
      proof -
        have "top1_is_path_on X TX a a (top1_path_product \<alpha> \<beta>)"
          by (rule top1_path_product_is_path[OF hTX_top halpha_X hbeta_X])
        thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
      qed
      thus "(\<lambda>(_::nat). {g. top1_loop_equiv_on X TX a (top1_path_product \<alpha> \<beta>) g}) s \<in> ?pi"
        unfolding top1_fundamental_group_carrier_def by (by100 blast)
    qed
    show "inj_on (\<lambda>(_::nat). {g. top1_loop_equiv_on X TX a (top1_path_product \<alpha> \<beta>) g}) {0::nat}"
      by (by100 simp)
    show "?pi = top1_subgroup_generated_on ?pi ?mul ?eid ?invg
        ((\<lambda>(_::nat). {g. top1_loop_equiv_on X TX a (top1_path_product \<alpha> \<beta>) g}) ` {0::nat})"
    proof -
      let ?class_ab = "{g. top1_loop_equiv_on X TX a (top1_path_product \<alpha> \<beta>) g}"
      let ?S = "(\<lambda>(_::nat). ?class_ab) ` {0::nat}"
      have hS_eq: "?S = {?class_ab}" by (by100 simp)
      have hab_loop: "top1_is_loop_on X TX a (top1_path_product \<alpha> \<beta>)"
      proof -
        have "top1_is_path_on X TX a a (top1_path_product \<alpha> \<beta>)"
          by (rule top1_path_product_is_path[OF hTX_top halpha_X hbeta_X])
        thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
      qed
      have hclass_ab_in_pi: "?class_ab \<in> ?pi"
        unfolding top1_fundamental_group_carrier_def using hab_loop by (by100 blast)
      have hS_sub: "?S \<subseteq> ?pi" using hclass_ab_in_pi by (by100 simp)
      \<comment> \<open>\\<subseteq>: generated \\<subseteq> \\<pi>\\_1.\<close>
      have h_sub: "top1_subgroup_generated_on ?pi ?mul ?eid ?invg ?S \<subseteq> ?pi"
        by (rule subgroup_generated_subset[OF hpi_grp hS_sub])
      \<comment> \<open>\\<supseteq>: \\<pi>\\_1 \\<subseteq> generated. Every [f] is a power of [\\<alpha>*\\<beta>] or its inverse.\<close>
      have h_sup: "?pi \<subseteq> top1_subgroup_generated_on ?pi ?mul ?eid ?invg ?S"
      proof (intro subsetI)
        fix x assume hx: "x \<in> ?pi"
        \<comment> \<open>x = [f] for some loop f.\<close>
        from hx obtain f where hf_loop: "top1_is_loop_on X TX a f"
            and hx_eq: "x = {g. top1_loop_equiv_on X TX a f g}"
          unfolding top1_fundamental_group_carrier_def by (by100 blast)
        \<comment> \<open>hgen: f ~ (\\<alpha>*\\<beta>)^n or f ~ rev(\\<alpha>*\\<beta>)^n.\<close>
        from hgen[rule_format, OF hf_loop] obtain n where hn:
            "top1_path_homotopic_on X TX a a f
                (top1_path_power (top1_path_product \<alpha> \<beta>) a n) \<or>
             top1_path_homotopic_on X TX a a f
                (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n)"
          by blast
        \<comment> \<open>Path power \\<rightarrow> group power correspondence.\<close>
        have hab_rev_loop: "top1_is_loop_on X TX a
            (top1_path_reverse (top1_path_product \<alpha> \<beta>))"
          by (rule top1_path_reverse_is_loop[OF hab_loop])
        have hpow_class: "\<And>m h. top1_is_loop_on X TX a h \<Longrightarrow>
            {g. top1_loop_equiv_on X TX a (top1_path_power h a m) g}
              = top1_group_pow ?mul ?eid {g. top1_loop_equiv_on X TX a h g} m"
        proof -
          fix m :: nat and h :: "real \<Rightarrow> 'a"
          assume hh: "top1_is_loop_on X TX a h"
          show "{g. top1_loop_equiv_on X TX a (top1_path_power h a m) g}
              = top1_group_pow ?mul ?eid {g. top1_loop_equiv_on X TX a h g} m"
          proof (induction m)
            case 0
            show ?case unfolding top1_fundamental_group_id_def by (by5000 auto)
          next
            case (Suc k)
            have h_pp_loop: "top1_is_loop_on X TX a (top1_path_power h a k)"
              by (rule top1_path_power_is_loop[OF hTX_top hh])
            have "{g. top1_loop_equiv_on X TX a (top1_path_power h a (Suc k)) g}
                = {g. top1_loop_equiv_on X TX a
                    (top1_path_product h (top1_path_power h a k)) g}"
              by (by100 simp)
            also have "... = ?mul {g. top1_loop_equiv_on X TX a h g}
                {g. top1_loop_equiv_on X TX a (top1_path_power h a k) g}"
              using top1_fundamental_group_mul_class[OF hTX_top hh h_pp_loop]
              by (by100 simp)
            also have "... = ?mul {g. top1_loop_equiv_on X TX a h g}
                (top1_group_pow ?mul ?eid {g. top1_loop_equiv_on X TX a h g} k)"
              using Suc.IH by simp
            finally show ?case by simp
          qed
        qed
        \<comment> \<open>Show x \\<in> generated({[\\<alpha>*\\<beta>]}).\<close>
        show "x \<in> top1_subgroup_generated_on ?pi ?mul ?eid ?invg ?S"
          unfolding top1_subgroup_generated_on_def hS_eq
        proof (intro InterI)
          fix H assume hH: "H \<in> {H'. {?class_ab} \<subseteq> H' \<and> H' \<subseteq> ?pi \<and>
              top1_is_group_on H' ?mul ?eid ?invg}"
          hence hH_grp: "top1_is_group_on H ?mul ?eid ?invg"
              and hab_in_H: "?class_ab \<in> H" and hH_sub: "H \<subseteq> ?pi"
            by (by100 blast)+
          from hn show "x \<in> H"
          proof
            \<comment> \<open>Case 1: f ~ (\\<alpha>*\\<beta>)^n.\<close>
            assume "top1_path_homotopic_on X TX a a f
                (top1_path_power (top1_path_product \<alpha> \<beta>) a n)"
            from path_homotopic_same_class[OF hTX_top this]
            have "x = {g. top1_loop_equiv_on X TX a
                (top1_path_power (top1_path_product \<alpha> \<beta>) a n) g}"
              using hx_eq by simp
            also have "... = top1_group_pow ?mul ?eid ?class_ab n"
              using hpow_class[OF hab_loop, of n] by simp
            finally have "x = top1_group_pow ?mul ?eid ?class_ab n" .
            thus "x \<in> H"
              using group_pow_in_group'[OF hH_grp hab_in_H] by simp
          next
            \<comment> \<open>Case 2: f ~ rev(\\<alpha>*\\<beta>)^n.\<close>
            assume "top1_path_homotopic_on X TX a a f
                (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n)"
            from path_homotopic_same_class[OF hTX_top this]
            have "x = {g. top1_loop_equiv_on X TX a
                (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a n) g}"
              using hx_eq by simp
            also have "... = top1_group_pow ?mul ?eid
                {g. top1_loop_equiv_on X TX a
                    (top1_path_reverse (top1_path_product \<alpha> \<beta>)) g} n"
              using hpow_class[OF hab_rev_loop, of n] by simp
            also have "{g. top1_loop_equiv_on X TX a
                (top1_path_reverse (top1_path_product \<alpha> \<beta>)) g}
                = ?invg ?class_ab"
              using fundamental_group_invg_class[OF hTX_top hab_loop] by simp
            finally have "x = top1_group_pow ?mul ?eid (?invg ?class_ab) n" .
            moreover have "?invg ?class_ab \<in> H"
            proof -
              from hH_grp[unfolded top1_is_group_on_def]
              have "\<forall>x \<in> H. ?invg x \<in> H" by (by100 fast)
              thus ?thesis using hab_in_H by blast
            qed
            ultimately show "x \<in> H"
              using group_pow_in_group'[OF hH_grp] by simp
          qed
        qed
      qed
      show ?thesis using h_sub h_sup by blast
    qed
    show "\<forall>ws::(nat \<times> bool) list. ws \<noteq> [] \<longrightarrow>
        top1_is_reduced_word (map (\<lambda>(s, b). ((\<lambda>(_::nat). {g. top1_loop_equiv_on X TX a
            (top1_path_product \<alpha> \<beta>) g}) s, b)) ws) \<longrightarrow>
        (\<forall>i<length ws. fst (ws ! i) \<in> {0::nat}) \<longrightarrow>
        top1_group_word_product ?mul ?eid ?invg
            (map (\<lambda>(s, b). ((\<lambda>(_::nat). {g. top1_loop_equiv_on X TX a
                (top1_path_product \<alpha> \<beta>) g}) s, b)) ws) \<noteq> ?eid"
      \<comment> \<open>Reduced words with one generator: all-(0,True) or all-(0,False).
         Word product = [\\<alpha>*\\<beta>]^n or [rev(\\<alpha>*\\<beta>)]^n, both \\<noteq> e.\<close>
      proof (intro allI impI)
        fix ws :: "(nat \<times> bool) list"
        assume hws_ne: "ws \<noteq> []"
          and hws_red: "top1_is_reduced_word (map (\<lambda>(s, b). ((\<lambda>(_::nat).
              {g. top1_loop_equiv_on X TX a (top1_path_product \<alpha> \<beta>) g}) s, b)) ws)"
          and hws_gen: "\<forall>i<length ws. fst (ws ! i) \<in> {0::nat}"
        \<comment> \<open>All entries have fst = 0, so all entries are (0, True) or (0, False).
           Reduced \\<Rightarrow> all same boolean (no adjacent cancellation pair).\<close>
        have hws_uniform: "(\<forall>i<length ws. snd (ws ! i) = True) \<or>
            (\<forall>i<length ws. snd (ws ! i) = False)"
        proof -
          \<comment> \<open>All adjacent pairs have same snd (from reduced + all fst equal).\<close>
          have hadj: "\<And>i. i + 1 < length ws \<Longrightarrow> snd (ws ! i) = snd (ws ! (i+1))"
          proof (rule ccontr)
            fix i assume hi: "i + 1 < length ws" and hne: "snd (ws ! i) \<noteq> snd (ws ! (i+1))"
            \<comment> \<open>fst of mapped ws at positions i and i+1 are both \\<iota> 0.\<close>
            let ?\<iota> = "\<lambda>(_::nat). {g. top1_loop_equiv_on X TX a (top1_path_product \<alpha> \<beta>) g}"
            let ?mws = "map (\<lambda>(s, b). (?\<iota> s, b)) ws"
            have hlen: "length ?mws = length ws" by simp
            have "fst (?mws ! i) = ?\<iota> (fst (ws ! i))"
              using hi by (simp add: nth_map case_prod_beta)
            moreover have "fst (?mws ! (i+1)) = ?\<iota> (fst (ws ! (i+1)))"
              using hi by (simp add: nth_map case_prod_beta)
            moreover have "fst (ws ! i) = 0" using hws_gen hi by (by100 force)
            moreover have "fst (ws ! (i+1)) = 0" using hws_gen hi by (by100 force)
            ultimately have "fst (?mws ! i) = fst (?mws ! (i+1))" by simp
            moreover have "snd (?mws ! i) = snd (ws ! i)"
              using hi by (simp add: nth_map case_prod_beta)
            moreover have "snd (?mws ! (i+1)) = snd (ws ! (i+1))"
              using hi by (simp add: nth_map case_prod_beta)
            ultimately have "fst (?mws ! i) = fst (?mws ! (i+1)) \<and> snd (?mws ! i) \<noteq> snd (?mws ! (i+1))"
              using hne by simp
            \<comment> \<open>A cancel pair at i means NOT reduced. Prove by induction on the list.\<close>
            hence "\<not> top1_is_reduced_word ?mws"
            proof -
              assume h: "fst (?mws ! i) = fst (?mws ! (i+1)) \<and> snd (?mws ! i) \<noteq> snd (?mws ! (i+1))"
              have "i + 1 < length ?mws" using hi by simp
              from cancel_pair_not_reduced[OF this] h show ?thesis by blast
            qed
            thus False using hws_red by blast
          qed
          \<comment> \<open>All adjacent same \\<Rightarrow> all same.\<close>
          show ?thesis
          proof (cases "snd (ws ! 0)")
            case True
            have "\<forall>i<length ws. snd (ws ! i) = True"
            proof (intro allI impI)
              fix i show "i < length ws \<Longrightarrow> snd (ws ! i) = True"
              proof (induction i)
                case 0 thus ?case using True by simp
              next
                case (Suc i)
                hence "snd (ws ! i) = True" by linarith
                moreover have "snd (ws ! i) = snd (ws ! (i+1))"
                  using hadj[of i] Suc.prems by linarith
                ultimately show ?case by simp
              qed
            qed
            thus ?thesis by blast
          next
            case False
            have "\<forall>i<length ws. snd (ws ! i) = False"
            proof (intro allI impI)
              fix i show "i < length ws \<Longrightarrow> snd (ws ! i) = False"
              proof (induction i)
                case 0 thus ?case using False by simp
              next
                case (Suc i)
                hence "snd (ws ! i) = False" by linarith
                moreover have "snd (ws ! i) = snd (ws ! (i+1))"
                  using hadj[of i] Suc.prems by linarith
                ultimately show ?case by simp
              qed
            qed
            thus ?thesis by blast
          qed
        qed
        \<comment> \<open>Word product of uniform list = power of [\\<alpha>*\\<beta>] or [rev(\\<alpha>*\\<beta>)].\<close>
        let ?ab_class = "{g. top1_loop_equiv_on X TX a (top1_path_product \<alpha> \<beta>) g}"
        let ?rab_class = "{g. top1_loop_equiv_on X TX a (top1_path_reverse (top1_path_product \<alpha> \<beta>)) g}"
        have hab_loop_main: "top1_is_loop_on X TX a (top1_path_product \<alpha> \<beta>)"
        proof -
          from top1_path_product_is_path[OF hTX_top halpha_X hbeta_X]
          show ?thesis unfolding top1_is_loop_on_def by (by100 blast)
        qed
        \<comment> \<open>Word product = [(\\<alpha>*\\<beta>)^n] or [rev(\\<alpha>*\\<beta>)^n] where n = length ws.\<close>
        have hword_eq: "top1_group_word_product ?mul ?eid ?invg
            (map (\<lambda>(s, b). ((\<lambda>(_::nat). ?ab_class) s, b)) ws) =
            {g. top1_loop_equiv_on X TX a (top1_path_power (top1_path_product \<alpha> \<beta>) a (length ws)) g}
          \<or> top1_group_word_product ?mul ?eid ?invg
            (map (\<lambda>(s, b). ((\<lambda>(_::nat). ?ab_class) s, b)) ws) =
            {g. top1_loop_equiv_on X TX a (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a (length ws)) g}"
        proof -
          let ?ab = "top1_path_product \<alpha> \<beta>"
          let ?rab = "top1_path_reverse ?ab"
          let ?mws = "map (\<lambda>(s, b). ((\<lambda>(_::nat). ?ab_class) s, b)) ws"
          have hlen_mws: "length ?mws = length ws" by simp
          from hws_uniform show ?thesis
          proof
            \<comment> \<open>All-True case: fs k = \\<alpha>*\\<beta>.\<close>
            assume hT: "\<forall>i<length ws. snd (ws ! i) = True"
            define fs where "fs = (\<lambda>(_::nat). ?ab)"
            have hloops: "\<forall>k<length ?mws. top1_is_loop_on X TX a (fs k)"
              unfolding fs_def using hab_loop_main by blast
            have hmatch: "\<forall>k<length ?mws.
                {g. top1_loop_equiv_on X TX a (fs k) g}
              = (if snd (?mws!k) then fst (?mws!k)
                 else top1_fundamental_group_invg X TX a (fst (?mws!k)))"
            proof (intro allI impI)
              fix k assume hk: "k < length ?mws"
              have "snd (?mws!k) = snd (ws!k)" using hk by (simp add: nth_map case_prod_beta)
              also have "... = True" using hT hk hlen_mws by simp
              finally have "snd (?mws!k) = True" .
              moreover have "fst (?mws!k) = ?ab_class" using hk by (simp add: nth_map case_prod_beta)
              moreover have "{g. top1_loop_equiv_on X TX a (fs k) g} = ?ab_class"
                unfolding fs_def by simp
              ultimately show "{g. top1_loop_equiv_on X TX a (fs k) g} =
                  (if snd (?mws!k) then fst (?mws!k)
                   else top1_fundamental_group_invg X TX a (fst (?mws!k)))" by simp
            qed
            from word_product_foldr_class[OF hTX_top hloops hmatch]
            have "top1_group_word_product ?mul ?eid ?invg ?mws =
                {g. top1_loop_equiv_on X TX a (foldr top1_path_product (map fs [0..<length ?mws]) (top1_constant_path a)) g}" .
            moreover have "foldr top1_path_product (map fs [0..<length ?mws]) (top1_constant_path a) =
                top1_path_power ?ab a (length ws)"
              unfolding fs_def hlen_mws by (rule foldr_uniform_is_path_power)
            ultimately show ?thesis by simp
          next
            \<comment> \<open>All-False case: fs k = rev(\\<alpha>*\\<beta>).\<close>
            assume hF: "\<forall>i<length ws. snd (ws ! i) = False"
            define fs where "fs = (\<lambda>(_::nat). ?rab)"
            have hloops: "\<forall>k<length ?mws. top1_is_loop_on X TX a (fs k)"
              unfolding fs_def using top1_path_reverse_is_loop[OF hab_loop_main] by blast
            have hmatch: "\<forall>k<length ?mws.
                {g. top1_loop_equiv_on X TX a (fs k) g}
              = (if snd (?mws!k) then fst (?mws!k)
                 else top1_fundamental_group_invg X TX a (fst (?mws!k)))"
            proof (intro allI impI)
              fix k assume hk: "k < length ?mws"
              have "snd (?mws!k) = snd (ws!k)" using hk by (simp add: nth_map case_prod_beta)
              also have "... = False" using hF hk hlen_mws by simp
              finally have hsnd: "snd (?mws!k) = False" .
              have hfst: "fst (?mws!k) = ?ab_class" using hk by (simp add: nth_map case_prod_beta)
              have "{g. top1_loop_equiv_on X TX a (fs k) g} =
                  top1_fundamental_group_invg X TX a ?ab_class"
                unfolding fs_def
                using fundamental_group_invg_class[OF hTX_top hab_loop_main] by simp
              thus "{g. top1_loop_equiv_on X TX a (fs k) g} =
                  (if snd (?mws!k) then fst (?mws!k)
                   else top1_fundamental_group_invg X TX a (fst (?mws!k)))"
                using hsnd hfst by simp
            qed
            from word_product_foldr_class[OF hTX_top hloops hmatch]
            have "top1_group_word_product ?mul ?eid ?invg ?mws =
                {g. top1_loop_equiv_on X TX a (foldr top1_path_product (map fs [0..<length ?mws]) (top1_constant_path a)) g}" .
            moreover have "foldr top1_path_product (map fs [0..<length ?mws]) (top1_constant_path a) =
                top1_path_power ?rab a (length ws)"
              unfolding fs_def hlen_mws by (rule foldr_uniform_is_path_power)
            ultimately show ?thesis by simp
          qed
        qed
        \<comment> \<open>[(\\<alpha>*\\<beta>)^n] \\<noteq> eid for n \\<ge> 1 by hinf\\_order.\<close>
        show "top1_group_word_product ?mul ?eid ?invg
            (map (\<lambda>(s, b). ((\<lambda>(_::nat). ?ab_class) s, b)) ws) \<noteq> ?eid"
        proof
          assume heq: "top1_group_word_product ?mul ?eid ?invg
              (map (\<lambda>(s, b). ((\<lambda>(_::nat). ?ab_class) s, b)) ws) = ?eid"
          have hlen_pos: "length ws > 0" using hws_ne by (by100 blast)
          from hword_eq show False
          proof
            assume "top1_group_word_product ?mul ?eid ?invg
                (map (\<lambda>(s, b). ((\<lambda>(_::nat). ?ab_class) s, b)) ws) =
                {g. top1_loop_equiv_on X TX a (top1_path_power (top1_path_product \<alpha> \<beta>) a (length ws)) g}"
            hence hclass1: "{g. top1_loop_equiv_on X TX a (top1_path_power (top1_path_product \<alpha> \<beta>) a (length ws)) g} = ?eid"
              using heq by simp
            \<comment> \<open>const \\<in> eid (reflexivity). So const \\<in> class(f). So equiv f const. So f ~ const.\<close>
            have "top1_constant_path a \<in> ?eid"
            proof -
              have "top1_is_loop_on X TX a (top1_constant_path a)"
                using top1_constant_path_is_path[OF hTX_top ha_X]
                unfolding top1_is_loop_on_def top1_is_path_on_def top1_constant_path_def
                by (by100 blast)
              from Lemma_51_1_path_homotopic_refl[OF this[unfolded top1_is_loop_on_def]]
              show ?thesis unfolding top1_fundamental_group_id_def top1_loop_equiv_on_def
                using \<open>top1_is_loop_on X TX a (top1_constant_path a)\<close> by (by100 blast)
            qed
            hence "top1_loop_equiv_on X TX a (top1_path_power (top1_path_product \<alpha> \<beta>) a (length ws))
                (top1_constant_path a)" using hclass1 by blast
            hence "top1_path_homotopic_on X TX a a
                (top1_path_power (top1_path_product \<alpha> \<beta>) a (length ws)) (top1_constant_path a)"
              unfolding top1_loop_equiv_on_def by (by100 blast)
            thus False using hinf_order[OF hlen_pos] by blast
          next
            assume "top1_group_word_product ?mul ?eid ?invg
                (map (\<lambda>(s, b). ((\<lambda>(_::nat). ?ab_class) s, b)) ws) =
                {g. top1_loop_equiv_on X TX a (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a (length ws)) g}"
            hence hclass2: "{g. top1_loop_equiv_on X TX a (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a (length ws)) g} = ?eid"
              using heq by simp
            have "top1_constant_path a \<in> ?eid"
            proof -
              have "top1_is_loop_on X TX a (top1_constant_path a)"
                using top1_constant_path_is_path[OF hTX_top ha_X]
                unfolding top1_is_loop_on_def top1_is_path_on_def top1_constant_path_def
                by (by100 blast)
              from Lemma_51_1_path_homotopic_refl[OF this[unfolded top1_is_loop_on_def]]
              show ?thesis unfolding top1_fundamental_group_id_def top1_loop_equiv_on_def
                using \<open>top1_is_loop_on X TX a (top1_constant_path a)\<close> by (by100 blast)
            qed
            hence "top1_loop_equiv_on X TX a (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a (length ws))
                (top1_constant_path a)" using hclass2 by blast
            hence "top1_path_homotopic_on X TX a a
                (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a (length ws)) (top1_constant_path a)"
              unfolding top1_loop_equiv_on_def by (by100 blast)
            \<comment> \<open>rev(\\<alpha>*\\<beta>)^n ~ const contradicts hinf\\_order (via path\\_power\\_reverse).\<close>
            \<comment> \<open>rev(f)^n ~ const \\<Rightarrow> rev(f^n) ~ const (path\\_power\\_reverse) \\<Rightarrow> f^n ~ const (reverse both sides).\<close>
            hence hrev_pow_const: "top1_path_homotopic_on X TX a a
                (top1_path_reverse (top1_path_power (top1_path_product \<alpha> \<beta>) a (length ws))) (top1_constant_path a)"
            proof -
              assume hrev: "top1_path_homotopic_on X TX a a
                  (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a (length ws))
                  (top1_constant_path a)"
              from path_power_reverse[OF hTX_top hab_loop_main, of "length ws"]
              have "top1_path_homotopic_on X TX a a
                  (top1_path_reverse (top1_path_power (top1_path_product \<alpha> \<beta>) a (length ws)))
                  (top1_path_power (top1_path_reverse (top1_path_product \<alpha> \<beta>)) a (length ws))" .
              from Lemma_51_1_path_homotopic_trans[OF hTX_top this hrev]
              show ?thesis .
            qed
            have hab_pow_path: "top1_is_path_on X TX a a
                (top1_path_power (top1_path_product \<alpha> \<beta>) a (length ws))"
              using top1_path_power_is_loop[OF hTX_top hab_loop_main]
              unfolding top1_is_loop_on_def by (by100 blast)
            have hconst_path: "top1_is_path_on X TX a a (top1_constant_path a)"
              using top1_constant_path_is_path[OF hTX_top ha_X] .
            from path_homotopic_reverse[OF hTX_top hrev_pow_const
                top1_path_reverse_is_path[OF hab_pow_path]
                hconst_path]
            have "top1_path_homotopic_on X TX a a
                (top1_path_reverse (top1_path_reverse (top1_path_power (top1_path_product \<alpha> \<beta>) a (length ws))))
                (top1_path_reverse (top1_constant_path a))" .
            have hrev_inv: "top1_path_reverse (top1_path_reverse
                (top1_path_power (top1_path_product \<alpha> \<beta>) a (length ws))) =
                top1_path_power (top1_path_product \<alpha> \<beta>) a (length ws)"
              by (rule path_reverse_involution)
            from \<open>top1_path_homotopic_on X TX a a (top1_path_reverse (top1_path_reverse _)) _\<close>
            have "top1_path_homotopic_on X TX a a
                (top1_path_power (top1_path_product \<alpha> \<beta>) a (length ws))
                (top1_path_reverse (top1_constant_path a))"
              using hrev_inv by simp
            moreover have "top1_path_reverse (top1_constant_path a) = top1_constant_path a"
              unfolding top1_path_reverse_def top1_constant_path_def by (rule ext) simp
            ultimately have "top1_path_homotopic_on X TX a a
                (top1_path_power (top1_path_product \<alpha> \<beta>) a (length ws)) (top1_constant_path a)" by simp
            thus False using hinf_order[OF hlen_pos] by blast
          qed
        qed
      qed
  qed
  \<comment> \<open>\\<Z> is free on {0::nat}.\<close>
  have hZ_free: "top1_is_free_group_full_on top1_Z_group top1_Z_mul
      top1_Z_id top1_Z_invg (\<lambda>(_::nat). (1::int)) {0::nat}"
    by (rule Z_is_free_on_one_generator)
  \<comment> \<open>Both free on {0} \\<Rightarrow> isomorphic (via unique hom mapping generators).\<close>
  \<comment> \<open>Get hom \\<Z> \\<rightarrow> \\<pi>\\_1 mapping 1 \\<mapsto> [\\<alpha>*\\<beta>].\<close>
  let ?\<iota>_pi = "\<lambda>(_::nat). {g. top1_loop_equiv_on X TX a (top1_path_product \<alpha> \<beta>) g}"
  have h_gen_in_pi: "\<forall>s\<in>{0::nat}. ?\<iota>_pi s \<in> ?pi"
  proof (intro ballI)
    fix s :: nat assume "s \<in> {0::nat}"
    have "top1_is_loop_on X TX a (top1_path_product \<alpha> \<beta>)"
    proof -
      have hab: "top1_is_path_on X TX a b \<alpha>" using halpha_X .
      have hba: "top1_is_path_on X TX b a \<beta>" using hbeta_X .
      have "top1_is_path_on X TX a a (top1_path_product \<alpha> \<beta>)"
        by (rule top1_path_product_is_path[OF hTX_top hab hba])
      thus ?thesis unfolding top1_is_loop_on_def by (by100 blast)
    qed
    thus "?\<iota>_pi s \<in> ?pi"
      unfolding top1_fundamental_group_carrier_def by (by100 blast)
  qed
  from free_group_hom_exists[OF hZ_free hpi_grp h_gen_in_pi]
  obtain \<psi> where h\<psi>_hom: "top1_group_hom_on top1_Z_group top1_Z_mul ?pi ?mul \<psi>" and
    h\<psi>_gen: "\<forall>s\<in>{0::nat}. \<psi> ((\<lambda>(_::nat). (1::int)) s) = ?\<iota>_pi s"
    by (by100 blast)
  \<comment> \<open>\\<psi> maps generators to generators \\<Rightarrow> bijection.\<close>
  from free_group_hom_generators_iso[OF hZ_free hpi_free h\<psi>_hom h\<psi>_gen]
  have h\<psi>_bij: "bij_betw \<psi> top1_Z_group ?pi" .
  \<comment> \<open>bij + hom = iso.\<close>
  have "top1_group_iso_on top1_Z_group top1_Z_mul ?pi ?mul \<psi>"
    unfolding top1_group_iso_on_def using h\<psi>_hom h\<psi>_bij by (by100 blast)
  hence "top1_groups_isomorphic_on top1_Z_group top1_Z_mul ?pi ?mul"
    unfolding top1_groups_isomorphic_on_def by (by100 blast)
  have hZ_grp: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
    using hZ_free unfolding top1_is_free_group_full_on_def by (by100 blast)
  show ?thesis
    by (rule top1_groups_isomorphic_on_sym[OF
        \<open>top1_groups_isomorphic_on top1_Z_group _ ?pi _\<close> hZ_grp hpi_grp])
qed

text \<open>Helper: free group structure transfers across isomorphism.\<close>
lemma free_group_iso_transfer:
  assumes "top1_is_free_group_full_on G mulG eG invgG \<iota> S"
      and "top1_groups_isomorphic_on G mulG H mulH"
      and "top1_is_group_on H mulH eH invgH"
  shows "\<exists>\<iota>'. top1_is_free_group_full_on H mulH eH invgH \<iota>' S"
proof -
  from assms(2) obtain f where hf: "top1_group_iso_on G mulG H mulH f"
    unfolding top1_groups_isomorphic_on_def by (by100 blast)
  from free_group_invariant_under_iso[OF assms(1) hf assms(3)]
  show ?thesis by (by100 blast)
qed

text \<open>Helper: tree union arcs (with endpoints in tree) is path-connected.
  Used in Theorem 84.7 for targets of deformation retractions.\<close>
lemma tree_union_arcs_path_connected:
  assumes hTX: "is_topology_on X TX"
      and hT_tree: "top1_is_tree_on T (subspace_topology X TX T)"
      and hT_sub: "T \<subseteq> X"
      and hS_fin: "finite S"
      and hS_arcs: "\<forall>A\<in>S. top1_is_arc_on A (subspace_topology X TX A) \<and> A \<subseteq> X"
      and hS_endpts: "\<forall>A\<in>S. \<exists>e. e \<in> T \<and> e \<in> A"
      and hx0: "x0 \<in> T"
  shows "top1_path_connected_on (T \<union> \<Union>S) (subspace_topology X TX (T \<union> \<Union>S))"
proof -
  let ?Y = "T \<union> \<Union>S"
  have hY_sub: "?Y \<subseteq> X" using hT_sub hS_arcs by (by100 blast)
  have hY_top: "is_topology_on ?Y (subspace_topology X TX ?Y)"
    by (rule subspace_topology_is_topology_on[OF hTX]) (use hY_sub in blast)
  have hT_pc: "top1_path_connected_on T (subspace_topology X TX T)"
    using tree_simply_connected[OF hT_tree] top1_simply_connected_on_path_connected by (by100 blast)
  \<comment> \<open>Each arc in S is PC.\<close>
  have hS_pc: "\<forall>A\<in>S. top1_path_connected_on A (subspace_topology X TX A)"
  proof (intro ballI)
    fix A assume "A \<in> S"
    have "top1_is_arc_on A (subspace_topology X TX A)" using hS_arcs \<open>A \<in> S\<close> by (by100 blast)
    obtain h where hh: "top1_homeomorphism_on top1_unit_interval
        top1_unit_interval_topology A (subspace_topology X TX A) h"
      using \<open>top1_is_arc_on A _\<close> unfolding top1_is_arc_on_def by (by100 blast)
    have hI_pc: "top1_path_connected_on top1_unit_interval top1_unit_interval_topology"
    proof -
      have "top1_unit_interval \<noteq> {}" unfolding top1_unit_interval_def by (by100 auto)
      have "\<And>x y t. x \<in> top1_unit_interval \<Longrightarrow> y \<in> top1_unit_interval \<Longrightarrow>
          0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow> (1 - t) * x + t * y \<in> top1_unit_interval"
      proof -
        fix x y t :: real
        assume "x \<in> top1_unit_interval" "y \<in> top1_unit_interval" "0 \<le> t" "t \<le> 1"
        have "0 \<le> x" "x \<le> 1" "0 \<le> y" "y \<le> 1"
          using \<open>x \<in> _\<close> \<open>y \<in> _\<close> unfolding top1_unit_interval_def by (by100 simp)+
        have "1 - t \<ge> 0" using \<open>t \<le> 1\<close> by (by100 linarith)
        have "(1 - t) * x \<ge> 0" using \<open>1 - t \<ge> 0\<close> \<open>0 \<le> x\<close> by (by100 simp)
        have "t * y \<ge> 0" using \<open>0 \<le> t\<close> \<open>0 \<le> y\<close> by (by100 simp)
        have "(1 - t) * x \<le> 1 - t" using mult_left_mono[OF \<open>x \<le> 1\<close> \<open>1 - t \<ge> 0\<close>] by (by100 simp)
        have "t * y \<le> t" using mult_left_mono[OF \<open>y \<le> 1\<close> \<open>0 \<le> t\<close>] by (by100 simp)
        show "(1 - t) * x + t * y \<in> top1_unit_interval"
          unfolding top1_unit_interval_def using \<open>(1-t)*x \<ge> 0\<close> \<open>t*y \<ge> 0\<close>
            \<open>(1-t)*x \<le> 1-t\<close> \<open>t*y \<le> t\<close> by (by100 simp)
      qed
      from convex_real_subspace_path_connected[OF \<open>top1_unit_interval \<noteq> {}\<close> this]
      show ?thesis unfolding top1_unit_interval_topology_def top1_unit_interval_def by (by100 simp)
    qed
    show "top1_path_connected_on A (subspace_topology X TX A)"
      using homeomorphism_preserves_path_connected[OF hh hI_pc] .
  qed
  \<comment> \<open>Use F = {T \\<union> A | A \\<in> S} \\<union> {T}. Each contains x0. Each is PC.\<close>
  let ?F = "insert T ((\<lambda>A. T \<union> A) ` S)"
  have hF_fin: "finite ?F" using hS_fin by (by100 auto)
  have hF_cover: "?Y = \<Union>?F" by (by100 blast)
  have hF_sub: "\<forall>B\<in>?F. B \<subseteq> ?Y" by (by100 blast)
  have hF_x0: "\<forall>B\<in>?F. x0 \<in> B" using hx0 by (by100 blast)
  \<comment> \<open>Each B \\<in> F is PC in subspace of Y.\<close>
  have hF_pc: "\<forall>B\<in>?F. top1_path_connected_on B (subspace_topology ?Y (subspace_topology X TX ?Y) B)"
  proof -
    \<comment> \<open>Helper: T \\<union> A is PC for any arc A with endpoint in T.\<close>
    have hTA_pc: "\<And>A. A \<in> S \<Longrightarrow> top1_path_connected_on (T \<union> A) (subspace_topology X TX (T \<union> A))"
    proof -
      fix A assume "A \<in> S"
      have "A \<subseteq> X" using hS_arcs \<open>A \<in> S\<close> by (by100 blast)
      have hA_pc: "top1_path_connected_on A (subspace_topology X TX A)"
        using hS_pc \<open>A \<in> S\<close> by (by100 blast)
      obtain e0 where "e0 \<in> T" "e0 \<in> A" using hS_endpts \<open>A \<in> S\<close> by (by100 blast)
      have hTA_top: "is_topology_on (T \<union> A) (subspace_topology X TX (T \<union> A))"
        by (rule subspace_topology_is_topology_on[OF hTX])
           (use hT_sub \<open>A \<subseteq> X\<close> in blast)
      \<comment> \<open>Use path\\_connected\\_finite\\_union\\_common\\_point with {T, A} and e0.\<close>
      let ?Fj = "{T, A}"
      have "\<forall>C\<in>?Fj. C \<subseteq> T \<union> A" by (by100 blast)
      have "\<forall>C\<in>?Fj. e0 \<in> C" using \<open>e0 \<in> T\<close> \<open>e0 \<in> A\<close> by (by100 blast)
      have hT_pc_TA: "top1_path_connected_on T
          (subspace_topology (T \<union> A) (subspace_topology X TX (T \<union> A)) T)"
        using hT_pc subspace_topology_trans[of T "T \<union> A" X TX] by (by100 simp)
      have hA_pc_TA: "top1_path_connected_on A
          (subspace_topology (T \<union> A) (subspace_topology X TX (T \<union> A)) A)"
        using hA_pc subspace_topology_trans[of A "T \<union> A" X TX] by (by100 simp)
      have "\<forall>C\<in>?Fj. top1_path_connected_on C
          (subspace_topology (T \<union> A) (subspace_topology X TX (T \<union> A)) C)"
        using hT_pc_TA hA_pc_TA by (by100 blast)
      from path_connected_finite_union_common_point[OF hTA_top _
          \<open>\<forall>C\<in>?Fj. C \<subseteq> T \<union> A\<close>
          \<open>\<forall>C\<in>?Fj. top1_path_connected_on C _\<close>
          \<open>\<forall>C\<in>?Fj. e0 \<in> C\<close>]
      show "top1_path_connected_on (T \<union> A) (subspace_topology X TX (T \<union> A))"
        by (by100 simp)
    qed
    show ?thesis
    proof (intro ballI)
      fix B assume "B \<in> ?F"
      have hB_sub_Y: "B \<subseteq> ?Y" using hF_sub \<open>B \<in> ?F\<close> by (by100 blast)
      have "subspace_topology ?Y (subspace_topology X TX ?Y) B = subspace_topology X TX B"
        by (rule subspace_topology_trans[OF hB_sub_Y])
      have "top1_path_connected_on B (subspace_topology X TX B)"
      proof -
        from \<open>B \<in> ?F\<close> consider "B = T" | "\<exists>A\<in>S. B = T \<union> A" by (by100 blast)
        thus ?thesis
        proof cases
          case 1 thus ?thesis using hT_pc by (by100 simp)
        next
          case 2
          then obtain A where "A \<in> S" "B = T \<union> A" by (by100 blast)
          thus ?thesis using hTA_pc[OF \<open>A \<in> S\<close>] by (by100 simp)
        qed
      qed
      thus "top1_path_connected_on B (subspace_topology ?Y (subspace_topology X TX ?Y) B)"
        using \<open>subspace_topology ?Y _ B = _\<close> by (by100 simp)
    qed
  qed
  from path_connected_finite_union_common_point[OF hY_top hF_fin hF_sub hF_pc hF_x0 hF_cover]
  show ?thesis .
qed

text \<open>Helper: deformation retract onto path-connected subspace implies path-connected.
  If X deformation retracts onto A and A is path-connected, then X is path-connected.
  Proof: the homotopy H gives a path from x to H(x,1) \<in> A for each x \<in> X.\<close>
text \<open>Helper: convex real subspace is simply connected.
  Uses straight-line homotopy H(s,t) = (1-t)*f(s) + t*x0.\<close>
lemma convex_real_subspace_simply_connected:
  assumes hS_ne: "S \<noteq> {}"
      and hS_conv: "\<And>x y t. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> 0 \<le> t \<Longrightarrow> t \<le> 1
          \<Longrightarrow> (1 - t) * x + t * (y::real) \<in> S"
  shows "top1_simply_connected_on S (subspace_topology (UNIV::real set) top1_open_sets S)"
proof -
  let ?TS = "subspace_topology (UNIV::real set) top1_open_sets S"
  have hS_pc: "top1_path_connected_on S ?TS"
    by (rule convex_real_subspace_path_connected[OF hS_ne hS_conv])
  obtain x0 where hx0: "x0 \<in> S" using hS_ne by (by100 blast)
  have hTS: "is_topology_on S ?TS"
    by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) (by100 blast)
  \<comment> \<open>Prove all-loops-trivial in a SEPARATE block (avoids simp closing the show goal).\<close>
  have hall_trivial: "\<forall>f. top1_is_loop_on S ?TS x0 f \<longrightarrow>
      top1_path_homotopic_on S ?TS x0 x0 f (top1_constant_path x0)"
  proof (intro allI impI)
    fix f assume hf: "top1_is_loop_on S ?TS x0 f"
    have hf_path: "top1_is_path_on S ?TS x0 x0 f"
      using hf unfolding top1_is_loop_on_def by (by100 blast)
    have hf_img: "\<forall>s\<in>I_set. f s \<in> S"
      using hf_path unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
    have hf0: "f 0 = x0" using hf_path unfolding top1_is_path_on_def by (by100 blast)
    have hf1: "f 1 = x0" using hf_path unfolding top1_is_path_on_def by (by100 blast)
    \<comment> \<open>Straight-line homotopy.\<close>
    \<comment> \<open>Use top1\\_slh\\_ext for the homotopy. Prove it contracts f to const in S.\<close>
    have hf_cont_on: "continuous_on I_set f"
    proof -
      \<comment> \<open>f is continuous I \\<rightarrow> S (subspace of R). Extend to f continuous I \\<rightarrow> R.\<close>
      have "S \<subseteq> (UNIV::real set)" by (by100 blast)
      have hf_cont_R: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets f"
      proof -
        have hf_cont_S_loc: "top1_continuous_map_on I_set I_top S ?TS f"
          using hf_path unfolding top1_is_path_on_def by (by100 blast)
        from top1_continuous_map_on_codomain_enlarge[OF hf_cont_S_loc \<open>S \<subseteq> UNIV\<close> subset_refl]
        have "top1_continuous_map_on I_set I_top UNIV (subspace_topology UNIV top1_open_sets UNIV) f" .
        moreover have "subspace_topology (UNIV::real set) top1_open_sets UNIV = top1_open_sets"
          by (rule subspace_topology_self) (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>Convert top1\\_continuous\\_map\\_on I\\<rightarrow>R to continuous\\_on I f.\<close>
      show ?thesis unfolding continuous_on_open_invariant
      proof (intro allI impI)
        fix B :: "real set" assume "open B"
        hence "B \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
        hence "{s \<in> I_set. f s \<in> B} \<in> I_top"
          using hf_cont_R unfolding top1_continuous_map_on_def by (by100 blast)
        hence "{s \<in> I_set. f s \<in> B} \<in> subspace_topology UNIV top1_open_sets I_set"
          unfolding top1_unit_interval_topology_def .
        then obtain W where "W \<in> top1_open_sets" "{s \<in> I_set. f s \<in> B} = I_set \<inter> W"
          unfolding subspace_topology_def by (by100 blast)
        have "open W" using \<open>W \<in> top1_open_sets\<close> unfolding top1_open_sets_def by (by100 blast)
        have "W \<inter> I_set = f -` B \<inter> I_set" using \<open>{s \<in> I_set. f s \<in> B} = I_set \<inter> W\<close> by (by100 blast)
        thus "\<exists>A. open A \<and> A \<inter> I_set = f -` B \<inter> I_set"
          using \<open>open W\<close> by (by100 blast)
      qed
    qed
    define H where "H = top1_slh_ext f x0"
    have hH_cont_UNIV: "continuous_on UNIV H"
      unfolding H_def by (rule top1_slh_ext_continuous[OF hf_cont_on])
    have hH_cont_II: "top1_continuous_map_on (I_set \<times> I_set) II_topology (UNIV::real set) top1_open_sets H"
      by (rule top1_continuous_map_on_II_to_UNIV[OF hH_cont_UNIV])
    have hH_eq: "\<forall>p\<in>I_set \<times> I_set. H p = (1 - snd p) * f (fst p) + snd p * x0"
      unfolding H_def using top1_slh_ext_agrees by (by100 blast)
    have hH_img: "\<forall>p\<in>I_set \<times> I_set. H p \<in> S"
    proof (intro ballI)
      fix p assume "p \<in> I_set \<times> I_set"
      hence "fst p \<in> I_set" "snd p \<in> I_set" by (by100 auto)+
      have "f (fst p) \<in> S" using hf_img \<open>fst p \<in> I_set\<close> by (by100 blast)
      have "0 \<le> snd p" "snd p \<le> 1"
        using \<open>snd p \<in> I_set\<close> unfolding top1_unit_interval_def by (by100 simp)+
      have "H p = (1 - snd p) * f (fst p) + snd p * x0"
        using hH_eq \<open>p \<in> I_set \<times> I_set\<close> by (by100 blast)
      thus "H p \<in> S"
        using hS_conv[OF \<open>f (fst p) \<in> S\<close> hx0 \<open>0 \<le> snd p\<close> \<open>snd p \<le> 1\<close>]
        by (by100 simp)
    qed
    have hH_cont_S: "top1_continuous_map_on (I_set \<times> I_set) II_topology S ?TS H"
    proof -
      have "S \<subseteq> (UNIV::real set)" by (by100 blast)
      from continuous_map_restrict_codomain[OF hH_cont_II hH_img this]
      show ?thesis .
    qed
    show "top1_path_homotopic_on S ?TS x0 x0 f (top1_constant_path x0)"
      unfolding top1_path_homotopic_on_def
    proof (intro conjI)
      show "top1_is_path_on S ?TS x0 x0 f" by (rule hf_path)
      show "top1_is_path_on S ?TS x0 x0 (top1_constant_path x0)"
        by (rule top1_constant_path_is_path[OF hTS hx0])
      show "\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology S ?TS F \<and>
          (\<forall>s\<in>I_set. F (s, 0) = f s) \<and> (\<forall>s\<in>I_set. F (s, 1) = top1_constant_path x0 s) \<and>
          (\<forall>t\<in>I_set. F (0, t) = x0) \<and> (\<forall>t\<in>I_set. F (1, t) = x0)"
      proof (rule exI[of _ H], intro conjI)
        show "top1_continuous_map_on (I_set \<times> I_set) II_topology S ?TS H" by (rule hH_cont_S)
        have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
        show "\<forall>s\<in>I_set. H (s, 0) = f s"
        proof (intro ballI)
          fix s assume "s \<in> I_set"
          have hs0_II: "(s, 0::real) \<in> I_set \<times> I_set" using \<open>s \<in> I_set\<close> h0I by (by100 blast)
          show "H (s, 0) = f s" using hH_eq[rule_format, OF hs0_II] by (by100 simp)
        qed
        show "\<forall>s\<in>I_set. H (s, 1) = top1_constant_path x0 s"
        proof (intro ballI)
          fix s assume "s \<in> I_set"
          have hs1_II: "(s, 1::real) \<in> I_set \<times> I_set" using \<open>s \<in> I_set\<close> h1I by (by100 blast)
          have "H (s, 1) = (1 - 1) * f s + 1 * x0" using hH_eq[rule_format, OF hs1_II] by (by100 simp)
          thus "H (s, 1) = top1_constant_path x0 s"
            unfolding top1_constant_path_def by (by100 simp)
        qed
        show "\<forall>t\<in>I_set. H (0, t) = x0"
        proof (intro ballI)
          fix t assume "t \<in> I_set"
          have h0t_II: "(0::real, t) \<in> I_set \<times> I_set" using h0I \<open>t \<in> I_set\<close> by (by100 blast)
          have "H (0, t) = (1 - t) * f 0 + t * x0" using hH_eq[rule_format, OF h0t_II] by (by100 simp)
          also have "... = (1 - t) * x0 + t * x0" using hf0 by (by100 simp)
          also have "... = x0" using distrib_right[of "1-t" t x0, symmetric] by (by100 simp)
          finally show "H (0, t) = x0" .
        qed
        show "\<forall>t\<in>I_set. H (1, t) = x0"
        proof (intro ballI)
          fix t assume "t \<in> I_set"
          have h1t_II: "(1::real, t) \<in> I_set \<times> I_set" using h1I \<open>t \<in> I_set\<close> by (by100 blast)
          have "H (1, t) = (1 - t) * f 1 + t * x0" using hH_eq[rule_format, OF h1t_II] by (by100 simp)
          also have "... = (1 - t) * x0 + t * x0" using hf1 by (by100 simp)
          also have "... = x0" using distrib_right[of "1-t" t x0, symmetric] by (by100 simp)
          finally show "H (1, t) = x0" .
        qed
      qed
    qed
  qed
  show ?thesis
    by (rule top1_simply_connected_from_one_point[OF hTS hS_pc hx0])
       (use hall_trivial in blast)
qed

text \<open>Helper: trivial \<pi>_1 carrier + path-connected \<Rightarrow> simply connected.\<close>
lemma trivial_pi1_imp_simply_connected:
  assumes "is_topology_on X TX"
      and "top1_path_connected_on X TX"
      and "x0 \<in> X"
      and "top1_fundamental_group_carrier X TX x0 =
          {top1_fundamental_group_id X TX x0}"
  shows "top1_simply_connected_on X TX"
proof -
  have "\<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
      top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
  proof (intro allI impI)
    fix f assume hf: "top1_is_loop_on X TX x0 f"
    \<comment> \<open>f's class \\<in> carrier = {id}, so class = id.\<close>
    have hcl: "{g. top1_loop_equiv_on X TX x0 f g} \<in>
        top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hf by (by100 blast)
    hence hcl_id: "{g. top1_loop_equiv_on X TX x0 f g} =
        top1_fundamental_group_id X TX x0"
      using assms(4) by (by5000 force)
    \<comment> \<open>f \\<in> class(f) by reflexivity.\<close>
    have hpath: "top1_is_path_on X TX x0 x0 f"
      using hf unfolding top1_is_loop_on_def by (by100 blast)
    have "top1_loop_equiv_on X TX x0 f f"
      unfolding top1_loop_equiv_on_def
      using hf Lemma_51_1_path_homotopic_refl[OF hpath] by (by100 blast)
    hence "f \<in> {g. top1_loop_equiv_on X TX x0 f g}" by (by100 blast)
    \<comment> \<open>So f \\<in> id\\_class = {g. loop\\_equiv(const, g)}.\<close>
    hence "f \<in> top1_fundamental_group_id X TX x0" using hcl_id by (by100 simp)
    hence "top1_loop_equiv_on X TX x0 (top1_constant_path x0) f"
      unfolding top1_fundamental_group_id_def by (by100 blast)
    hence "top1_path_homotopic_on X TX x0 x0 (top1_constant_path x0) f"
      unfolding top1_loop_equiv_on_def by (by100 blast)
    show "top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
      by (rule Lemma_51_1_path_homotopic_sym) (rule \<open>top1_path_homotopic_on _ _ _ _ _ f\<close>)
  qed
  show ?thesis
    by (rule top1_simply_connected_from_one_point[OF assms(1) assms(2) assms(3)])
       (use \<open>\<forall>f. _\<close> in blast)
qed

lemma deformation_retract_path_connected:
  assumes hdr: "top1_deformation_retract_of_on X TX A"
      and hTX: "is_topology_on X TX"
      and hA_pc: "top1_path_connected_on A (subspace_topology X TX A)"
  shows "top1_path_connected_on X TX"
proof -
  have hA_sub: "A \<subseteq> X"
    using conjunct1[OF hdr[unfolded top1_deformation_retract_of_on_def]] by (by100 blast)
  from hdr obtain H where
    hH_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H" and
    hH_0: "\<forall>x\<in>X. H (x, 0) = x" and
    hH_1: "\<forall>x\<in>X. H (x, 1) \<in> A" and
    hH_A: "\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) = a"
    unfolding top1_deformation_retract_of_on_def by (by100 blast)
  have hI_top: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  \<comment> \<open>For each x \\<in> X, t \\<mapsto> H(x, t) is a path from x to H(x,1) \\<in> A.\<close>
  have hpath_to_A: "\<And>x. x \<in> X \<Longrightarrow> top1_is_path_on X TX x (H (x, 1)) (\<lambda>t. H (x, t))"
  proof -
    fix x assume hx: "x \<in> X"
    \<comment> \<open>t \\<mapsto> H(x, t) = H \\<circ> (\\<lambda>t. (x, t)). The section \\<lambda>t. (x, t) is continuous I \\<rightarrow> X \\<times> I.\<close>
    have hsection: "top1_continuous_map_on I_set I_top (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>t. (x, t))"
      by (rule top1_continuous_map_on_section2[OF hTX hI_top hx])
    from top1_continuous_map_on_comp[OF hsection hH_cont]
    have hcomp: "top1_continuous_map_on I_set I_top X TX (\<lambda>t. H (x, t))"
      unfolding comp_def by (by100 simp)
    have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by (by100 simp)
    show "top1_is_path_on X TX x (H (x, 1)) (\<lambda>t. H (x, t))"
      unfolding top1_is_path_on_def
      using hcomp hH_0[rule_format, OF hx] hH_1[rule_format, OF hx] h0_I h1_I
      by (by100 blast)
  qed
  show ?thesis unfolding top1_path_connected_on_def
  proof (intro conjI ballI)
    show "is_topology_on X TX" by (rule hTX)
  next
    fix x y assume hx: "x \<in> X" and hy: "y \<in> X"
    \<comment> \<open>Path x \\<rightarrow> H(x,1) in X.\<close>
    have hpx: "top1_is_path_on X TX x (H (x, 1)) (\<lambda>t. H (x, t))"
      by (rule hpath_to_A[OF hx])
    \<comment> \<open>Path H(y,1) \\<rightarrow> y in X (reverse of H(y, \\<cdot>)).\<close>
    have hpy: "top1_is_path_on X TX y (H (y, 1)) (\<lambda>t. H (y, t))"
      by (rule hpath_to_A[OF hy])
    have hpy_rev: "top1_is_path_on X TX (H (y, 1)) y (top1_path_reverse (\<lambda>t. H (y, t)))"
      by (rule top1_path_reverse_is_path[OF hpy])
    \<comment> \<open>Path H(x,1) \\<rightarrow> H(y,1) in A (path-connected).\<close>
    have hHx_A: "H (x, 1) \<in> A" using hH_1 hx by (by100 blast)
    have hHy_A: "H (y, 1) \<in> A" using hH_1 hy by (by100 blast)
    obtain g where hg: "top1_is_path_on A (subspace_topology X TX A) (H (x, 1)) (H (y, 1)) g"
      using hA_pc hHx_A hHy_A unfolding top1_path_connected_on_def by (by100 blast)
    \<comment> \<open>Lift g to X (A \\<subseteq> X).\<close>
    have hg_X: "top1_is_path_on X TX (H (x, 1)) (H (y, 1)) g"
      by (rule path_in_subspace_is_path_in_ambient[OF hTX hA_sub hg])
    \<comment> \<open>Concatenate: x \\<rightarrow> H(x,1) \\<rightarrow> H(y,1) \\<rightarrow> y.\<close>
    have hpxg: "top1_is_path_on X TX x (H (y, 1)) (top1_path_product (\<lambda>t. H (x, t)) g)"
      by (rule top1_path_product_is_path[OF hTX hpx hg_X])
    have hfinal: "top1_is_path_on X TX x y
        (top1_path_product (top1_path_product (\<lambda>t. H (x, t)) g) (top1_path_reverse (\<lambda>t. H (y, t))))"
      by (rule top1_path_product_is_path[OF hTX hpxg hpy_rev])
    show "\<exists>f. top1_is_path_on X TX x y f" by (rule exI[of _ _]) (rule hfinal)
  qed
qed

\<comment> \<open>Helper: subgraph coherent topology. If X is a graph and Y = \\<Union>B for B \\<subseteq> arcs,
   then the subspace topology on Y is coherent with the arcs in B.
   Proof: (\\<Rightarrow>) restriction of closed. (\\<Leftarrow>) non-B arcs intersect Y at endpoints only
   (finite, closed in Hausdorff); use X coherent topology to get C closed in X.\<close>
lemma subgraph_coherent_topology:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes hgraph: "top1_is_graph_on X TX"
      and h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and h\<A>_cover: "\<Union>\<A> = X"
      and h\<A>_inter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and h\<A>_coh: "\<forall>C. C \<subseteq> X \<longrightarrow>
           (closedin_on X TX C \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
      and hB_sub: "\<B> \<subseteq> \<A>"
      and hY_eq: "Y = \<Union>\<B>"
  shows "\<forall>C. C \<subseteq> Y \<longrightarrow>
      (closedin_on Y (subspace_topology X TX Y) C \<longleftrightarrow>
       (\<forall>A\<in>\<B>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
proof (intro allI impI)
  fix C assume hC_sub: "C \<subseteq> Y"
  have hY_sub: "Y \<subseteq> X" using hY_eq hB_sub h\<A> by (by100 blast)
  show "closedin_on Y (subspace_topology X TX Y) C =
       (\<forall>A\<in>\<B>. closedin_on A (subspace_topology X TX A) (A \<inter> C))"
  proof (rule iffI)
    \<comment> \<open>(\\<Rightarrow>) C closed in Y \\<Rightarrow> C\\<inter>A closed in A for each A\\<in>B.\<close>
    assume hC_cl: "closedin_on Y (subspace_topology X TX Y) C"
    show "\<forall>A\<in>\<B>. closedin_on A (subspace_topology X TX A) (A \<inter> C)"
    proof (intro ballI)
      fix A assume hA_B: "A \<in> \<B>"
      have hA_sub_Y: "A \<subseteq> Y" using hA_B hY_eq by (by100 blast)
      have hA_sub_X: "A \<subseteq> X" using hA_B hB_sub h\<A> by (by100 blast)
      have hTX: "is_topology_on X TX"
        using hgraph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
      \<comment> \<open>C closed in Y (subspace of X) \\<Rightarrow> C = Y \\<inter> D for some D closed in X.\<close>
      from Theorem_17_2[OF hTX hY_sub, rule_format, of C]
      have "\<exists>D. closedin_on X TX D \<and> C = D \<inter> Y" using hC_cl by (by100 blast)
      then obtain D where hD_cl: "closedin_on X TX D" and hC_eq: "C = D \<inter> Y" by (by100 blast)
      have "A \<inter> C = A \<inter> D" using hC_eq hA_sub_Y by (by100 blast)
      moreover from Theorem_17_2[OF hTX hA_sub_X, rule_format, of "A \<inter> D"]
      have "closedin_on A (subspace_topology X TX A) (A \<inter> D)"
        using hD_cl by (by100 blast)
      ultimately show "closedin_on A (subspace_topology X TX A) (A \<inter> C)" by simp
    qed
  next
    \<comment> \<open>(\\<Leftarrow>) C\\<inter>A closed in A for each A\\<in>B \\<Rightarrow> C closed in Y.\<close>
    assume hC_pieces: "\<forall>A\<in>\<B>. closedin_on A (subspace_topology X TX A) (A \<inter> C)"
    \<comment> \<open>For non-B arcs: C\\<inter>A \\<subseteq> Y\\<inter>A \\<subseteq> endpoints, finite, closed in Hausdorff.\<close>
    have hC_all: "\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)"
    proof (intro ballI)
      fix A assume hA_full: "A \<in> \<A>"
      show "closedin_on A (subspace_topology X TX A) (A \<inter> C)"
      proof (cases "A \<in> \<B>")
        case True thus ?thesis using hC_pieces by (by100 blast)
      next
        case False
        \<comment> \<open>A \\<notin> B. Then A \\<inter> Y \\<subseteq> \\<Union>{A \\<inter> B' | B'\\<in>B} \\<subseteq> endpoints.\<close>
        have hA_Y_finite: "finite (A \<inter> Y)"
        proof -
          \<comment> \<open>A \\<inter> Y \\<subseteq> endpoints(A): for each B'\\<in>B, A\\<inter>B' \\<subseteq> endpoints(A) since A\\<noteq>B'.\<close>
          have "A \<inter> Y \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
          proof (intro subsetI)
            fix x assume "x \<in> A \<inter> Y"
            hence "x \<in> A" "x \<in> Y" by (by100 blast)+
            from \<open>x \<in> Y\<close> obtain B' where hB': "B' \<in> \<B>" "x \<in> B'"
              using hY_eq by (by100 blast)
            have "B' \<in> \<A>" using hB' hB_sub by (by100 blast)
            have "A \<noteq> B'" using False hB'(1) by (by100 blast)
            from h\<A>_inter[rule_format, OF hA_full \<open>B' \<in> \<A>\<close> \<open>A \<noteq> B'\<close>]
            have "A \<inter> B' \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)" by (by100 blast)
            thus "x \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
              using \<open>x \<in> A\<close> \<open>x \<in> B'\<close> by (by100 blast)
          qed
          moreover have "finite (top1_arc_endpoints_on A (subspace_topology X TX A))"
          proof -
            have hA_arc: "top1_is_arc_on A (subspace_topology X TX A)"
              using hA_full h\<A> by (by100 blast)
            obtain h where hh: "top1_homeomorphism_on top1_unit_interval
                top1_unit_interval_topology A (subspace_topology X TX A) h"
              using hA_arc unfolding top1_is_arc_on_def by (by100 blast)
            have hX_strict: "is_topology_on_strict X TX"
              using hgraph unfolding top1_is_graph_on_def by (by100 blast)
            have hX_haus: "is_hausdorff_on X TX"
              using hgraph unfolding top1_is_graph_on_def by (by100 blast)
            have hA_sub_X: "A \<subseteq> X" using hA_full h\<A> by (by100 blast)
            from arc_endpoints_are_boundary[OF hX_strict hX_haus hA_sub_X hA_arc hh]
            show ?thesis by (by100 simp)
          qed
          ultimately show ?thesis using finite_subset by (by100 blast)
        qed
        have "A \<inter> C \<subseteq> A \<inter> Y" using hC_sub by (by100 blast)
        hence "finite (A \<inter> C)" using hA_Y_finite by (rule finite_subset)
        \<comment> \<open>Finite set in Hausdorff arc is closed.\<close>
        have hA_sub_X: "A \<subseteq> X" using hA_full h\<A> by (by100 blast)
        have hX_haus: "is_hausdorff_on X TX"
          using hgraph unfolding top1_is_graph_on_def by (by100 blast)
        have hA_haus: "is_hausdorff_on A (subspace_topology X TX A)"
          using Theorem_17_11 hX_haus hA_sub_X by (by100 blast)
        have "A \<inter> C \<subseteq> A" by (by100 blast)
        from Theorem_17_8[OF hA_haus \<open>finite (A \<inter> C)\<close> \<open>A \<inter> C \<subseteq> A\<close>]
        show ?thesis .
      qed
    qed
    have "closedin_on X TX C"
      using h\<A>_coh hC_sub hY_sub hC_all by (by100 blast)
    have hTX: "is_topology_on X TX"
      using hgraph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
    have "C = C \<inter> Y" using hC_sub by (by100 blast)
    thus "closedin_on Y (subspace_topology X TX Y) C"
      using Theorem_17_2[OF hTX hY_sub] \<open>closedin_on X TX C\<close> by (by100 blast)
  qed
qed

\<comment> \<open>Helper: in a graph, a connected subspace Y \\<subseteq> X equals \\<Union>{arcs \\<subseteq> Y}
   whenever Y contains \\<ge>2 points and the only points of Y NOT in arcs\\<subseteq>Y
   are finitely many arc endpoints.\<close>
lemma graph_connected_sub_covered_by_arcs:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes hgraph: "top1_is_graph_on X TX"
      and h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and h\<A>_cover: "\<Union>\<A> = X"
      and h\<A>_coh: "\<forall>C. C \<subseteq> X \<longrightarrow>
           (closedin_on X TX C \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
      and hY_sub: "Y \<subseteq> X"
      and hY_conn: "top1_connected_on Y (subspace_topology X TX Y)"
      and hY_2pts: "\<exists>y1 y2. y1 \<in> Y \<and> y2 \<in> Y \<and> y1 \<noteq> y2"
      \<comment> \<open>Non-Y arcs intersect Y only finitely (at endpoints).\<close>
      and hY_finite_inter: "\<forall>A\<in>\<A>. \<not> A \<subseteq> Y \<longrightarrow> finite (A \<inter> Y)"
      \<comment> \<open>The set of non-Y arcs is finite (needed for finite union argument).\<close>
      and hY_finite_non: "finite {A \<in> \<A>. \<not> A \<subseteq> Y}"
  shows "Y = \<Union>{A \<in> \<A>. A \<subseteq> Y}"
proof -
  let ?D = "\<Union>{A \<in> \<A>. A \<subseteq> Y}"
  let ?C = "Y - ?D"
  have hD_sub: "?D \<subseteq> Y" by (by100 blast)
  have hC_sub: "?C \<subseteq> Y" by (by100 blast)
  have hY_eq: "Y = ?C \<union> ?D" by (by100 blast)
  have hCD_disj: "?C \<inter> ?D = {}" by (by100 blast)
  have hTX: "is_topology_on X TX"
    using hgraph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
  have hX_haus: "is_hausdorff_on X TX"
    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
  \<comment> \<open>C is closed in X (coherent topology: C\\<inter>A closed in A for all A).\<close>
  have "closedin_on X TX ?C"
  proof -
    have "\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> ?C)"
    proof (intro ballI)
      fix A assume "A \<in> \<A>"
      show "closedin_on A (subspace_topology X TX A) (A \<inter> ?C)"
      proof (cases "A \<subseteq> Y")
        case True
        hence "A \<in> {A \<in> \<A>. A \<subseteq> Y}" using \<open>A \<in> \<A>\<close> by (by100 blast)
        hence "A \<subseteq> ?D" by (by100 blast)
        hence "A \<inter> ?C = {}" by (by100 blast)
        have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
        thus ?thesis using \<open>A \<inter> ?C = {}\<close>
          closedin_empty[OF subspace_topology_is_topology_on[OF hTX \<open>A \<subseteq> X\<close>]]
          by (by100 simp)
      next
        case False
        have "A \<inter> ?C \<subseteq> A \<inter> Y" by (by100 blast)
        moreover have "finite (A \<inter> Y)" using hY_finite_inter \<open>A \<in> \<A>\<close> False by (by100 blast)
        ultimately have "finite (A \<inter> ?C)" using finite_subset by (by100 blast)
        have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
        have "is_hausdorff_on A (subspace_topology X TX A)"
          using Theorem_17_11 hX_haus \<open>A \<subseteq> X\<close> by (by100 blast)
        have "A \<inter> ?C \<subseteq> A" by (by100 blast)
        from Theorem_17_8[OF \<open>is_hausdorff_on A _\<close> \<open>finite (A \<inter> ?C)\<close> \<open>A \<inter> ?C \<subseteq> A\<close>]
        show ?thesis .
      qed
    qed
    thus ?thesis using h\<A>_coh hC_sub hY_sub by (by100 blast)
  qed
  \<comment> \<open>D is closed in X (same argument).\<close>
  have "closedin_on X TX ?D"
  proof -
    have "\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> ?D)"
    proof (intro ballI)
      fix A assume "A \<in> \<A>"
      show "closedin_on A (subspace_topology X TX A) (A \<inter> ?D)"
      proof (cases "A \<subseteq> Y")
        case True
        hence "A \<subseteq> ?D" using \<open>A \<in> \<A>\<close> by (by100 blast)
        hence "A \<inter> ?D = A" by (by100 blast)
        have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
        have "closedin_on A (subspace_topology X TX A) A"
        proof (rule closedin_intro)
          show "A \<subseteq> A" by (by100 blast)
          show "A - A \<in> subspace_topology X TX A"
          proof -
            have "A - A = {}" by (by100 blast)
            moreover have "{} \<in> subspace_topology X TX A"
              using subspace_topology_is_topology_on[OF hTX \<open>A \<subseteq> X\<close>]
              unfolding is_topology_on_def by (by5000 fast)
            ultimately show ?thesis by simp
          qed
        qed
        thus ?thesis using \<open>A \<inter> ?D = A\<close> by simp
      next
        case False
        have "A \<inter> ?D \<subseteq> A \<inter> Y" using hD_sub by (by100 blast)
        moreover have "finite (A \<inter> Y)" using hY_finite_inter \<open>A \<in> \<A>\<close> False by (by100 blast)
        ultimately have "finite (A \<inter> ?D)" using finite_subset by (by100 blast)
        have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
        have "is_hausdorff_on A (subspace_topology X TX A)"
          using Theorem_17_11 hX_haus \<open>A \<subseteq> X\<close> by (by100 blast)
        have "A \<inter> ?D \<subseteq> A" by (by100 blast)
        from Theorem_17_8[OF \<open>is_hausdorff_on A _\<close> \<open>finite (A \<inter> ?D)\<close> \<open>A \<inter> ?D \<subseteq> A\<close>]
        show ?thesis .
      qed
    qed
    thus ?thesis using h\<A>_coh hD_sub hY_sub by (by100 blast)
  qed
  \<comment> \<open>C and D both closed in Y (restriction of closed-in-X).\<close>
  have hC_cl_Y: "closedin_on Y (subspace_topology X TX Y) ?C"
    using Theorem_17_2[OF hTX hY_sub] \<open>closedin_on X TX ?C\<close> hC_sub
    by (by100 blast)
  have hD_cl_Y: "closedin_on Y (subspace_topology X TX Y) ?D"
    using Theorem_17_2[OF hTX hY_sub] \<open>closedin_on X TX ?D\<close> hD_sub
    by (by100 blast)
  \<comment> \<open>Y = C \\<union> D, disjoint, both closed, Y connected \\<Rightarrow> C = {} or D = {}.\<close>
  have "?C = {} \<or> ?D = {}"
  proof (rule ccontr)
    assume "\<not> (?C = {} \<or> ?D = {})"
    hence hC_ne: "?C \<noteq> {}" and hD_ne: "?D \<noteq> {}" by (by100 blast)+
    \<comment> \<open>C and D are open in Y (complement of closed is open).\<close>
    have "Y - ?C = ?D" using hY_eq hCD_disj by (by100 blast)
    have "Y - ?D = ?C" using hY_eq hCD_disj by (by100 blast)
    have hC_open: "?C \<in> subspace_topology X TX Y"
      using hD_cl_Y \<open>Y - ?D = ?C\<close> unfolding closedin_on_def by (by100 simp)
    have hD_open: "?D \<in> subspace_topology X TX Y"
      using hC_cl_Y \<open>Y - ?C = ?D\<close> unfolding closedin_on_def by (by100 simp)
    \<comment> \<open>Separation of Y: contradicts connectedness.\<close>
    have "\<not> top1_connected_on Y (subspace_topology X TX Y)"
      unfolding top1_connected_on_def
      using hC_open hD_open hC_ne hD_ne hCD_disj hY_eq by (by100 blast)
    thus False using hY_conn by contradiction
  qed
  \<comment> \<open>D \\<noteq> {} (Y has \\<ge>2 points, so some arc \\<subseteq> Y has \\<ge>2 points).\<close>
  moreover have "?D \<noteq> {}"
  proof -
    from hY_2pts obtain y1 y2 where "y1 \<in> Y" "y2 \<in> Y" "y1 \<noteq> y2" by (by100 blast)
    \<comment> \<open>If D = {}: Y = C, and C \\<subseteq> finitely many endpoints. Y Hausdorff + finite + \\<ge>2 pts \\<Rightarrow> disconnected.\<close>
    show ?thesis
    proof
      assume "?D = {}"
      hence "Y = ?C" using hY_eq by (by100 blast)
      \<comment> \<open>Every point in Y is in a non-Y arc at an endpoint.\<close>
      have "finite Y"
      proof -
        have "Y \<subseteq> \<Union>{A \<inter> Y | A. A \<in> \<A> \<and> \<not> A \<subseteq> Y}"
        proof (intro subsetI)
          fix x assume "x \<in> Y"
          hence "x \<in> X" using hY_sub by (by100 blast)
          hence "x \<in> \<Union>\<A>" using h\<A>_cover by simp
          then obtain A where "A \<in> \<A>" "x \<in> A" by (by100 blast)
          have "\<not> A \<subseteq> Y"
          proof
            assume "A \<subseteq> Y"
            hence "A \<in> {A \<in> \<A>. A \<subseteq> Y}" using \<open>A \<in> \<A>\<close> by (by100 blast)
            hence "x \<in> ?D" using \<open>x \<in> A\<close> by (by100 blast)
            thus False using \<open>?D = {}\<close> by (by100 blast)
          qed
          thus "x \<in> \<Union>{A \<inter> Y | A. A \<in> \<A> \<and> \<not> A \<subseteq> Y}" using \<open>A \<in> \<A>\<close> \<open>x \<in> A\<close> \<open>x \<in> Y\<close>
            by (by100 blast)
        qed
        moreover have "finite (\<Union>{A \<inter> Y | A. A \<in> \<A> \<and> \<not> A \<subseteq> Y})"
        proof -
          have "(\<Union>{A \<inter> Y | A. A \<in> \<A> \<and> \<not> A \<subseteq> Y}) = (\<Union>A \<in> {A \<in> \<A>. \<not> A \<subseteq> Y}. A \<inter> Y)"
            by (by100 blast)
          moreover have "finite (\<Union>A \<in> {A \<in> \<A>. \<not> A \<subseteq> Y}. A \<inter> Y)"
          proof (rule finite_UN_I[OF hY_finite_non])
            fix A assume "A \<in> {A \<in> \<A>. \<not> A \<subseteq> Y}"
            thus "finite (A \<inter> Y)" using hY_finite_inter by (by100 blast)
          qed
          ultimately show ?thesis by simp
        qed
        ultimately show ?thesis using finite_subset by (by100 blast)
      qed
      \<comment> \<open>Finite Hausdorff \\<ge>2 pts \\<Rightarrow> disconnected (each point is closed \\<Rightarrow> {y1} is clopen).\<close>
      have "is_hausdorff_on Y (subspace_topology X TX Y)"
        using Theorem_17_11 hX_haus hY_sub by (by100 blast)
      have h_y1_closed: "closedin_on Y (subspace_topology X TX Y) {y1}"
        using Theorem_17_8[OF \<open>is_hausdorff_on Y _\<close>] \<open>y1 \<in> Y\<close> by (by100 simp)
      have h_Ymy1_closed: "closedin_on Y (subspace_topology X TX Y) (Y - {y1})"
        using Theorem_17_8[OF \<open>is_hausdorff_on Y _\<close>] \<open>finite Y\<close> \<open>y1 \<in> Y\<close> by (by100 simp)
      have "Y - (Y - {y1}) \<in> subspace_topology X TX Y"
      proof -
        from h_Ymy1_closed have "Y - (Y - {y1}) \<in> subspace_topology X TX Y"
          unfolding closedin_on_def by (by100 blast)
        thus ?thesis .
      qed
      have "Y - (Y - {y1}) = {y1}" using \<open>y1 \<in> Y\<close> by (by100 blast)
      hence "{y1} \<in> subspace_topology X TX Y"
        using \<open>Y - (Y - {y1}) \<in> _\<close> by simp
      moreover have "Y - {y1} \<in> subspace_topology X TX Y"
        using h_y1_closed unfolding closedin_on_def by (by100 blast)
      moreover have "{y1} \<noteq> {}" by (by100 blast)
      moreover have "Y - {y1} \<noteq> {}" using \<open>y2 \<in> Y\<close> \<open>y1 \<noteq> y2\<close> by (by100 blast)
      moreover have "{y1} \<inter> (Y - {y1}) = {}" by (by100 blast)
      moreover have "{y1} \<union> (Y - {y1}) = Y" using \<open>y1 \<in> Y\<close> by (by100 blast)
      ultimately have "\<not> top1_connected_on Y (subspace_topology X TX Y)"
        unfolding top1_connected_on_def by (by100 blast)
      thus False using hY_conn by contradiction
    qed
  qed
  ultimately have "?C = {}" by (by100 blast)
  thus ?thesis by (by100 blast)
qed

\<comment> \<open>Deformation retract helper: removing interior points of non-tree arcs
   gives a subspace that deformation retracts onto the complementary tree \\<union> arcs.
   Used in both graph\\_pi1\\_free\\_weak (card>1) and Theorem 84.7.\<close>
lemma graph_deformation_retract_helper:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes hgraph: "top1_is_graph_on X TX"
      and h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and h\<A>_cover: "\<Union>\<A> = X"
      and h\<A>_inter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and h\<A>_coh: "\<forall>C. C \<subseteq> X \<longrightarrow>
           (closedin_on X TX C \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
      and hT_tree: "top1_is_tree_on T (subspace_topology X TX T)"
      and hT_sub: "T \<subseteq> X"
      and hT_subgraph: "\<forall>A\<in>\<A>. \<not> A \<subseteq> T \<longrightarrow>
           A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
      and hNT_endpoints: "\<forall>A\<in>{A\<in>\<A>. \<not> A \<subseteq> T}. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology X TX A). e \<in> T"
      and hS_fin: "finite S"
      and hS_sub: "S \<subseteq> {A\<in>\<A>. \<not> A \<subseteq> T}"
      and hps: "\<forall>A\<in>S. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
  shows "top1_deformation_retract_of_on (X - ps ` S)
      (subspace_topology X TX (X - ps ` S))
      (T \<union> \<Union>({A\<in>\<A>. \<not> A \<subseteq> T} - S))"
proof -
  let ?NT = "{A\<in>\<A>. \<not> A \<subseteq> T}"
  have hX_top: "is_topology_on X TX"
    using hgraph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
  have hX_strict: "is_topology_on_strict X TX"
    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
  have hX_haus: "is_hausdorff_on X TX"
    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
  let ?Y = "X - ps ` S"
  let ?TY = "subspace_topology X TX ?Y"
  let ?target = "T \<union> \<Union>(?NT - S)"
  \<comment> \<open>The proof follows the same pattern as graph\\_remove\\_interior\\_points\\_sc.
     Define H\\_DR on Y \\<times> I: identity on target, slide half-arcs to T-endpoints.
     Continuity by pasting on closed pieces.\<close>
  have htarget_sub: "?target \<subseteq> ?Y"
  proof -
    have "T \<subseteq> ?Y"
    proof -
      have "\<forall>A\<in>S. ps A \<notin> T"
      proof (intro ballI)
        fix A assume "A \<in> S"
        hence "A \<in> ?NT" using hS_sub by (by100 blast)
        hence "A \<in> \<A>" "\<not> A \<subseteq> T" by (by100 blast)+
        from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>] \<open>\<not> A \<subseteq> T\<close>
        have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)" by (by100 blast)
        have "ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
          using hps \<open>A \<in> S\<close> by (by100 blast)
        thus "ps A \<notin> T"
          using \<open>A \<inter> T \<subseteq> _\<close> \<open>ps A \<notin> _\<close> hps \<open>A \<in> S\<close> by (by100 blast)
      qed
      thus ?thesis using hT_sub by (by100 blast)
    qed
    moreover have "\<Union>(?NT - S) \<subseteq> ?Y"
    proof -
      have "\<forall>A\<in>?NT - S. A \<subseteq> ?Y"
      proof (intro ballI)
        fix A assume "A \<in> ?NT - S"
        have "A \<in> \<A>" using \<open>A \<in> ?NT - S\<close> by (by100 blast)
        have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
        have "A \<inter> ps ` S = {}"
        proof (rule ccontr)
          assume "A \<inter> ps ` S \<noteq> {}"
          then obtain B where "B \<in> S" "ps B \<in> A" by (by100 blast)
          have "B \<in> \<A>" using hS_sub \<open>B \<in> S\<close> by (by100 blast)
          have "B \<noteq> A" using \<open>A \<in> ?NT - S\<close> \<open>B \<in> S\<close> by (by100 blast)
          have "ps B \<in> B" using hps \<open>B \<in> S\<close> by (by100 blast)
          hence "ps B \<in> A \<inter> B" using \<open>ps B \<in> A\<close> by (by100 blast)
          hence "ps B \<in> top1_arc_endpoints_on B (subspace_topology X TX B)"
            using h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>B \<noteq> A\<close>[symmetric]]
            by (by100 blast)
          thus False using hps \<open>B \<in> S\<close> by (by100 blast)
        qed
        thus "A \<subseteq> ?Y" using \<open>A \<subseteq> X\<close> by (by100 blast)
      qed
      thus ?thesis by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Infrastructure: homeomorphisms for arcs in S.\<close>
  define hAc where "hAc \<equiv> \<lambda>A.
    SOME h. top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      A (subspace_topology X TX A) h"
  define tAc where "tAc \<equiv> \<lambda>A. inv_into top1_unit_interval (hAc A) (ps A)"
  have hhAc: "\<And>A. A \<in> S \<Longrightarrow> top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
      A (subspace_topology X TX A) (hAc A)"
  proof -
    fix A assume "A \<in> S"
    hence "A \<in> ?NT" using hS_sub by (by100 blast)
    hence "A \<in> \<A>" by (by100 blast)
    hence "top1_is_arc_on A (subspace_topology X TX A)" using h\<A> by (by100 blast)
    then obtain h where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        A (subspace_topology X TX A) h" unfolding top1_is_arc_on_def by (by100 blast)
    thus "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        A (subspace_topology X TX A) (hAc A)"
      unfolding hAc_def
      by (rule someI[of "\<lambda>h. top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          A (subspace_topology X TX A) h"])
  qed
  \<comment> \<open>Define H\\_DR: for x \\<in> target: H(x,t) = x. For x in half-arc: slide.\<close>
  define H_DR where "H_DR \<equiv> \<lambda>(x, t::real).
    if x \<in> ?target then x
    else (let A = THE A. A \<in> S \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A) in
          let h = hAc A in
          let \<sigma> = inv_into top1_unit_interval h x in
          let ep = (if \<sigma> < tAc A then 0 else 1) in
          h (\<sigma> + t * (ep - \<sigma>)))"
  show "top1_deformation_retract_of_on ?Y ?TY ?target"
    unfolding top1_deformation_retract_of_on_def
  proof (intro conjI)
    show "?target \<subseteq> ?Y" using htarget_sub .
    show "\<exists>H. top1_continuous_map_on (?Y \<times> I_set) (product_topology_on ?TY I_top) ?Y ?TY H
        \<and> (\<forall>x\<in>?Y. H (x, 0) = x) \<and> (\<forall>x\<in>?Y. H (x, 1) \<in> ?target)
        \<and> (\<forall>a\<in>?target. \<forall>t\<in>I_set. H (a, t) = a)"
    proof (rule exI[of _ H_DR])
      have "(\<forall>x\<in>?Y. H_DR (x, 0) = x)"
      proof (intro ballI)
        fix x assume "x \<in> ?Y"
        show "H_DR (x, 0) = x"
        proof (cases "x \<in> ?target")
          case True thus ?thesis unfolding H_DR_def by (by100 simp)
        next
          case False
          \<comment> \<open>x \\<notin> target. x is in some arc A \\<in> S. t=0 gives h(\\<sigma>) = x.\<close>
          have "x \<in> X" using \<open>x \<in> ?Y\<close> by (by100 blast)
          hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
          then obtain A where "A \<in> \<A>" "x \<in> A" by (by100 blast)
          have "A \<in> S"
          proof (rule ccontr)
            assume "A \<notin> S"
            show False
            proof (cases "A \<subseteq> T")
              case True thus False using \<open>x \<in> A\<close> False by (by100 blast)
            next
              case aFalse: False
              hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
              hence "A \<in> ?NT - S" using \<open>A \<notin> S\<close> by (by100 blast)
              hence "x \<in> \<Union>(?NT - S)" using \<open>x \<in> A\<close> by (by100 blast)
              hence "x \<in> ?target" by (by100 blast)
              thus False using False by (by100 blast)
            qed
          qed
          have hbij_A: "bij_betw (hAc A) top1_unit_interval A"
            using hhAc[OF \<open>A \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
          have "x \<in> hAc A ` top1_unit_interval"
            using \<open>x \<in> A\<close> hbij_A unfolding bij_betw_def by (by100 blast)
          have "hAc A (inv_into top1_unit_interval (hAc A) x) = x"
            by (rule f_inv_into_f[OF \<open>x \<in> hAc A ` top1_unit_interval\<close>])
          \<comment> \<open>With t=0: \\<sigma> + 0*(ep - \\<sigma>) = \\<sigma>. hAc(\\<sigma>) = x.\<close>
          \<comment> \<open>x \\<notin> endpoints of A (endpoints \\<in> T \\<subseteq> target, but x \\<notin> target).\<close>
          have "A \<in> ?NT" using hS_sub \<open>A \<in> S\<close> by (by100 blast)
          have "x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hNT_endpoints[rule_format, OF \<open>A \<in> ?NT\<close>] False by (by100 blast)
          hence hx_int: "x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
            using \<open>x \<in> A\<close> by (by100 blast)
          \<comment> \<open>THE uniqueness: A is the unique arc in S containing x as interior point.\<close>
          have hTHE: "(THE A. A \<in> S \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = A"
          proof (rule the_equality)
            show "A \<in> S \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
              using \<open>A \<in> S\<close> hx_int by (by100 blast)
          next
            fix A' assume h: "A' \<in> S \<and> x \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
            hence "A' \<in> \<A>" "x \<in> A'" using hS_sub by (by100 blast)+
            show "A' = A"
            proof (rule ccontr)
              assume "A' \<noteq> A"
              from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> A\<close>[symmetric]]
              show False using \<open>x \<in> A\<close> \<open>x \<in> A'\<close> \<open>x \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
            qed
          qed
          show ?thesis unfolding H_DR_def Let_def using False hTHE
            \<open>hAc A (inv_into top1_unit_interval (hAc A) x) = x\<close> by (by100 simp)
        qed
      qed
      moreover have "(\<forall>x\<in>?Y. H_DR (x, 1) \<in> ?target)"
      proof (intro ballI)
        fix x assume "x \<in> ?Y"
        show "H_DR (x, 1) \<in> ?target"
        proof (cases "x \<in> ?target")
          case True thus ?thesis unfolding H_DR_def by (by100 simp)
        next
          case False
          \<comment> \<open>x \\<notin> target. H\\_DR(x,1) = hAc A (ep) where ep=0 or 1.\<close>
          have "x \<in> X" using \<open>x \<in> ?Y\<close> by (by100 blast)
          hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
          then obtain A where "A \<in> \<A>" "x \<in> A" by (by100 blast)
          have "A \<in> S"
          proof (rule ccontr)
            assume "A \<notin> S"
            show False
            proof (cases "A \<subseteq> T")
              case True thus False using \<open>x \<in> A\<close> False by (by100 blast)
            next
              case aFalse: False
              hence "A \<in> ?NT - S" using \<open>A \<in> \<A>\<close> \<open>A \<notin> S\<close> by (by100 blast)
              thus False using \<open>x \<in> A\<close> False by (by100 blast)
            qed
          qed
          have "A \<in> ?NT" using hS_sub \<open>A \<in> S\<close> by (by100 blast)
          have "x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hNT_endpoints[rule_format, OF \<open>A \<in> ?NT\<close>] False by (by100 blast)
          hence hx_int: "x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
            using \<open>x \<in> A\<close> by (by100 blast)
          have hTHE: "(THE A. A \<in> S \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = A"
          proof (rule the_equality)
            show "A \<in> S \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
              using \<open>A \<in> S\<close> hx_int by (by100 blast)
          next
            fix A' assume "A' \<in> S \<and> x \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
            hence "A' \<in> \<A>" "x \<in> A'" using hS_sub by (by100 blast)+
            show "A' = A"
            proof (rule ccontr)
              assume "A' \<noteq> A"
              from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> A\<close>[symmetric]]
              show False using \<open>x \<in> A\<close> \<open>x \<in> A'\<close> \<open>x \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
            qed
          qed
          \<comment> \<open>With t=1: \\<sigma> + 1*(ep-\\<sigma>) = ep. hAc A ep \\<in> T \\<subseteq> target.\<close>
          have "H_DR (x, 1) = hAc A (if inv_into top1_unit_interval (hAc A) x < tAc A then 0 else 1)"
            unfolding H_DR_def Let_def using False hTHE by (by100 simp)
          moreover have "hAc A 0 \<in> T" and "hAc A 1 \<in> T"
          proof -
            have hX_strict: "is_topology_on_strict X TX"
              using hgraph unfolding top1_is_graph_on_def by (by100 blast)
            have hX_haus: "is_hausdorff_on X TX"
              using hgraph unfolding top1_is_graph_on_def by (by100 blast)
            have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
            have harc: "top1_is_arc_on A (subspace_topology X TX A)"
              using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
            from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>A \<subseteq> X\<close> harc hhAc[OF \<open>A \<in> S\<close>]]
            have hep: "top1_arc_endpoints_on A (subspace_topology X TX A) = {hAc A 0, hAc A 1}" .
            show "hAc A 0 \<in> T" using hNT_endpoints[rule_format, OF \<open>A \<in> ?NT\<close>] hep by (by100 simp)
            show "hAc A 1 \<in> T" using hNT_endpoints[rule_format, OF \<open>A \<in> ?NT\<close>] hep by (by100 simp)
          qed
          ultimately show ?thesis by (by100 auto)
        qed
      qed
      moreover have "(\<forall>a\<in>?target. \<forall>t\<in>I_set. H_DR (a, t) = a)"
        unfolding H_DR_def by (by100 simp)
      moreover have "top1_continuous_map_on (?Y \<times> I_set) (product_topology_on ?TY I_top) ?Y ?TY H_DR"
      proof -
        let ?YI = "?Y \<times> I_set"
        let ?YItop = "product_topology_on ?TY I_top"
        have hX_top: "is_topology_on X TX"
          using hgraph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
        have hY_sub: "?Y \<subseteq> X" by (by100 blast)
        have hTY_top: "is_topology_on ?Y ?TY"
          by (rule subspace_topology_is_topology_on[OF hX_top hY_sub])
        have hYI_top: "is_topology_on ?YI ?YItop"
          by (rule product_topology_on_is_topology_on[OF hTY_top
              top1_unit_interval_topology_is_topology_on])
        \<comment> \<open>Decompose Y\\<times>I into target\\<times>I and (Y\\\\target)\\<times>I.\<close>
        define D_T where "D_T = ?target \<times> I_set"
        define D_B where "D_B = (\<Union>A\<in>S. A \<inter> ?Y) \<times> I_set"
        \<comment> \<open>D\\_T \\<cup> D\\_B = Y\\<times>I (target \\<cup> \\<Union>{A\\<cap>Y | A \\<in> S} = Y).\<close>
        have hcover: "D_T \<union> D_B = ?YI"
        proof (rule set_eqI, rule iffI)
          fix p assume "p \<in> D_T \<union> D_B"
          thus "p \<in> ?YI" unfolding D_T_def D_B_def using htarget_sub by (by100 blast)
        next
          fix p assume "p \<in> ?YI"
          then obtain x t where hxt: "p = (x, t)" "x \<in> ?Y" "t \<in> I_set" by (by100 blast)
          show "p \<in> D_T \<union> D_B"
          proof (cases "x \<in> ?target")
            case True thus ?thesis unfolding D_T_def hxt(1) using hxt(3) by (by100 blast)
          next
            case False
            have "x \<in> X" using hxt(2) by (by100 blast)
            hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
            then obtain A where "A \<in> \<A>" "x \<in> A" by (by100 blast)
            have "A \<in> S"
            proof (rule ccontr)
              assume "A \<notin> S"
              show False
              proof (cases "A \<subseteq> T")
                case True thus False using \<open>x \<in> A\<close> False by (by100 blast)
              next
                case aFalse: False
                hence "A \<in> ?NT - S" using \<open>A \<in> \<A>\<close> \<open>A \<notin> S\<close> by (by100 blast)
                thus False using \<open>x \<in> A\<close> False by (by100 blast)
              qed
            qed
            thus ?thesis unfolding D_B_def hxt(1) using \<open>x \<in> A\<close> hxt by (by100 blast)
          qed
        qed
        \<comment> \<open>target closed in Y (needs coherent topology — same as SC lemma T closed in Y).
           For now: sorry this standard fact.\<close>
        have htarget_closed: "closedin_on ?Y ?TY ?target"
        proof -
          \<comment> \<open>T closed in X (coherent topology + per-arc closedin).\<close>
          have hT_closed_X_dr: "closedin_on X TX T"
          proof -
            have "\<forall>Ag\<in>\<A>. closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> T)"
            proof (intro ballI)
              fix Ag assume "Ag \<in> \<A>"
              have "Ag \<subseteq> X" using h\<A> \<open>Ag \<in> \<A>\<close> by (by100 blast)
              show "closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> T)"
              proof (cases "Ag \<subseteq> T")
                case True
                hence "Ag \<inter> T = Ag" by (by100 blast)
                thus ?thesis using closedin_carrier[OF subspace_topology_is_topology_on[OF hX_top \<open>Ag \<subseteq> X\<close>]]
                  by (by100 simp)
              next
                case False
                from hT_subgraph[rule_format, OF \<open>Ag \<in> \<A>\<close>] False
                have "Ag \<inter> T \<subseteq> top1_arc_endpoints_on Ag (subspace_topology X TX Ag)" by (by100 blast)
                have hX_haus: "is_hausdorff_on X TX"
                  using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                have hX_strict: "is_topology_on_strict X TX"
                  using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                have harc: "top1_is_arc_on Ag (subspace_topology X TX Ag)"
                  using h\<A> \<open>Ag \<in> \<A>\<close> by (by100 blast)
                then obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                    Ag (subspace_topology X TX Ag) h" unfolding top1_is_arc_on_def by (by100 blast)
                from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>Ag \<subseteq> X\<close> harc hh]
                have "top1_arc_endpoints_on Ag (subspace_topology X TX Ag) = {h 0, h 1}" .
                hence "finite (top1_arc_endpoints_on Ag (subspace_topology X TX Ag))" by (by100 simp)
                from finite_subset[OF \<open>Ag \<inter> T \<subseteq> _\<close> this]
                have "finite (Ag \<inter> T)" .
                have "is_hausdorff_on Ag (subspace_topology X TX Ag)"
                  using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>Ag \<subseteq> X\<close> hX_haus by (by100 blast)
                show ?thesis
                  by (rule Theorem_17_8[OF \<open>is_hausdorff_on Ag _\<close> \<open>finite (Ag \<inter> T)\<close>]) (by100 blast)
              qed
            qed
            thus ?thesis using h\<A>_coh[rule_format, OF hT_sub] by (by100 blast)
          qed
          \<comment> \<open>T closed in Y.\<close>
          have hT_closed_Y_dr: "closedin_on ?Y ?TY T"
          proof -
            from Theorem_17_2[OF hX_top hY_sub, of T]
            show ?thesis using hT_closed_X_dr htarget_sub by (by100 blast)
          qed
          \<comment> \<open>\\<Union>(NT\\\\S) closed in Y: complement is Y \\<setminus> (T \\<union> \\<Union>(NT\\\\S)) = interiors of arcs in S.
             This is a finite union of open sets (since S is finite). Hence complement open,
             hence target closed.
             Alternative: target closed in X (by coherent topology) then restrict to Y.\<close>
          \<comment> \<open>target closed in X: by coherent topology, target \\<cap> A closed in A for each arc.\<close>
          have htarget_closed_X: "closedin_on X TX ?target"
          proof -
            have "\<forall>Ag\<in>\<A>. closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> ?target)"
            proof (intro ballI)
              fix Ag assume "Ag \<in> \<A>"
              have "Ag \<subseteq> X" using h\<A> \<open>Ag \<in> \<A>\<close> by (by100 blast)
              show "closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> ?target)"
              proof (cases "Ag \<in> S")
                case True
                \<comment> \<open>Ag \\<in> S: Ag \\<cap> target = Ag \\<cap> T (endpoints only, since Ag non-tree and not in NT\\\\S).\<close>
                have "Ag \<in> ?NT" using hS_sub True by (by100 blast)
                hence "\<not> Ag \<subseteq> T" by (by100 blast)
                from hT_subgraph[rule_format, OF \<open>Ag \<in> \<A>\<close>] this
                have "Ag \<inter> T \<subseteq> top1_arc_endpoints_on Ag (subspace_topology X TX Ag)" by (by100 blast)
                have "Ag \<inter> ?target = Ag \<inter> T"
                proof -
                  have "Ag \<inter> \<Union>(?NT - S) \<subseteq> Ag \<inter> T"
                  proof (intro subsetI)
                    fix x assume "x \<in> Ag \<inter> \<Union>(?NT - S)"
                    then obtain B where "B \<in> ?NT - S" "x \<in> B" "x \<in> Ag" by (by100 blast)
                    have "B \<in> \<A>" using \<open>B \<in> ?NT - S\<close> by (by100 blast)
                    have "B \<noteq> Ag" using \<open>B \<in> ?NT - S\<close> True by (by100 blast)
                    hence "x \<in> top1_arc_endpoints_on Ag (subspace_topology X TX Ag)"
                      using h\<A>_inter[rule_format, OF \<open>Ag \<in> \<A>\<close> \<open>B \<in> \<A>\<close>] \<open>x \<in> Ag\<close> \<open>x \<in> B\<close> \<open>B \<noteq> Ag\<close>
                      by (by100 blast)
                    thus "x \<in> Ag \<inter> T"
                      using hNT_endpoints[rule_format, OF \<open>Ag \<in> ?NT\<close>] \<open>x \<in> Ag\<close> by (by100 blast)
                  qed
                  thus ?thesis by (by100 blast)
                qed
                \<comment> \<open>Ag \\<cap> T is finite (endpoints) hence closed in Hausdorff Ag.\<close>
                have hX_haus: "is_hausdorff_on X TX"
                  using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                have hX_strict: "is_topology_on_strict X TX"
                  using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                have harc: "top1_is_arc_on Ag (subspace_topology X TX Ag)"
                  using h\<A> \<open>Ag \<in> \<A>\<close> by (by100 blast)
                then obtain h where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                    Ag (subspace_topology X TX Ag) h" unfolding top1_is_arc_on_def by (by100 blast)
                from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>Ag \<subseteq> X\<close> harc this]
                have "top1_arc_endpoints_on Ag (subspace_topology X TX Ag) = {h 0, h 1}" .
                hence "finite (top1_arc_endpoints_on Ag (subspace_topology X TX Ag))" by (by100 simp)
                from finite_subset[OF \<open>Ag \<inter> T \<subseteq> _\<close> this]
                have "finite (Ag \<inter> T)" .
                have "is_hausdorff_on Ag (subspace_topology X TX Ag)"
                  using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>Ag \<subseteq> X\<close> hX_haus by (by100 blast)
                have "closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> T)"
                  by (rule Theorem_17_8[OF \<open>is_hausdorff_on Ag _\<close> \<open>finite (Ag \<inter> T)\<close>]) (by100 blast)
                thus ?thesis using \<open>Ag \<inter> ?target = Ag \<inter> T\<close> by (by100 simp)
              next
                case False
                \<comment> \<open>Ag \\<notin> S: either Ag \\<subseteq> T or Ag \\<in> NT\\\\S. In both cases Ag \\<subseteq> target.\<close>
                have "Ag \<subseteq> ?target"
                proof (cases "Ag \<subseteq> T")
                  case True thus ?thesis by (by100 blast)
                next
                  case aFalse: False
                  hence "Ag \<in> ?NT" using \<open>Ag \<in> \<A>\<close> by (by100 blast)
                  hence "Ag \<in> ?NT - S" using False by (by100 blast)
                  thus ?thesis by (by100 blast)
                qed
                hence "Ag \<inter> ?target = Ag" by (by100 blast)
                thus ?thesis
                  using closedin_carrier[OF subspace_topology_is_topology_on[OF hX_top \<open>Ag \<subseteq> X\<close>]]
                  by (by100 simp)
              qed
            qed
            have "?target \<subseteq> X" using hT_sub h\<A> by (by100 blast)
            note hper_arc = \<open>\<forall>Ag\<in>\<A>. closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> ?target)\<close>
            thus ?thesis using h\<A>_coh[rule_format, OF \<open>?target \<subseteq> X\<close>] hper_arc by (by100 blast)
          qed
          \<comment> \<open>target closed in Y (from target closed in X + Theorem\\_17\\_2).\<close>
          from Theorem_17_2[OF hX_top hY_sub, of ?target]
          show ?thesis using htarget_closed_X htarget_sub by (by100 blast)
        qed
        \<comment> \<open>Each A\\<cap>Y closed in Y for A \\<in> S.\<close>
        have hS_AY_closed: "\<forall>A\<in>S. closedin_on ?Y ?TY (A \<inter> ?Y)"
        proof (intro ballI)
          fix A assume "A \<in> S"
          have "A \<in> ?NT" using hS_sub \<open>A \<in> S\<close> by (by100 blast)
          hence "A \<in> \<A>" by (by100 blast)
          hence "A \<subseteq> X" using h\<A> by (by100 blast)
          have harc_A: "top1_is_arc_on A (subspace_topology X TX A)"
            using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
          then obtain h0 where hh0: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
              A (subspace_topology X TX A) h0" unfolding top1_is_arc_on_def by (by100 blast)
          have hI_cpt: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
          proof -
            have hCI: "top1_compact_on (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1)"
              by (rule top1_closed_interval_compact) (by100 linarith)
            have hCI_eq: "top1_closed_interval 0 1 = top1_unit_interval"
              unfolding top1_closed_interval_def top1_unit_interval_def by (by100 auto)
            show ?thesis unfolding top1_compact_on_def
            proof (intro conjI allI impI)
              show "is_topology_on top1_unit_interval top1_unit_interval_topology"
                by (rule top1_unit_interval_topology_is_topology_on)
            next
              fix Uc assume hUc: "Uc \<subseteq> top1_unit_interval_topology \<and> top1_unit_interval \<subseteq> \<Union>Uc"
              have "Uc \<subseteq> top1_closed_interval_topology 0 1"
                using hUc I_top_sub_closed_interval_top by (by100 blast)
              moreover have "top1_closed_interval 0 1 \<subseteq> \<Union>Uc" using hUc hCI_eq by (by100 simp)
              ultimately have "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> top1_closed_interval 0 1 \<subseteq> \<Union>F"
                using hCI unfolding top1_compact_on_def by (by100 blast)
              thus "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> top1_unit_interval \<subseteq> \<Union>F" using hCI_eq by (by100 simp)
            qed
          qed
          have hh0c: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              A (subspace_topology X TX A) h0"
            using hh0 unfolding top1_homeomorphism_on_def by (by100 blast)
          have hTA: "is_topology_on A (subspace_topology X TX A)"
            by (rule subspace_topology_is_topology_on[OF hX_top \<open>A \<subseteq> X\<close>])
          from top1_compact_on_continuous_image[OF hI_cpt hTA hh0c]
          have "top1_compact_on (h0 ` top1_unit_interval)
              (subspace_topology A (subspace_topology X TX A) (h0 ` top1_unit_interval))" .
          have "h0 ` top1_unit_interval = A"
            using hh0 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
          have "subspace_topology A (subspace_topology X TX A) A = subspace_topology X TX A"
          proof (rule subspace_topology_self)
            show "\<forall>U\<in>subspace_topology X TX A. U \<subseteq> A"
              unfolding subspace_topology_def by (by100 blast)
          qed
          hence "top1_compact_on A (subspace_topology X TX A)"
            using \<open>top1_compact_on (h0 ` top1_unit_interval) _\<close> \<open>h0 ` top1_unit_interval = A\<close>
            by (by100 simp)
          have hX_haus: "is_hausdorff_on X TX"
            using hgraph unfolding top1_is_graph_on_def by (by100 blast)
          have hX_strict: "is_topology_on_strict X TX"
            using hgraph unfolding top1_is_graph_on_def by (by100 blast)
          have "closedin_on X TX A"
            by (rule compact_in_strict_hausdorff_closedin_on[OF hX_haus hX_strict \<open>A \<subseteq> X\<close>
                \<open>top1_compact_on A (subspace_topology X TX A)\<close>])
          from Theorem_17_2[OF hX_top hY_sub, of "A \<inter> ?Y"]
          show "closedin_on ?Y ?TY (A \<inter> ?Y)" using \<open>closedin_on X TX A\<close> by (by100 blast)
        qed
        have hB_closed: "closedin_on ?Y ?TY (\<Union>A\<in>S. A \<inter> ?Y)"
          by (rule closedin_on_finite_indexed_Union[OF hTY_top hS_fin])
             (use hS_AY_closed in \<open>by100 blast\<close>)
        \<comment> \<open>D\\_T, D\\_B closed in Y\\<times>I.\<close>
        have hfst_cont: "top1_continuous_map_on ?YI ?YItop ?Y ?TY fst"
        proof -
          from top1_continuous_pi1[OF hTY_top top1_unit_interval_topology_is_topology_on]
          show ?thesis unfolding pi1_def by (by100 simp)
        qed
        have hDT_closed: "closedin_on ?YI ?YItop D_T"
        proof -
          have "{p \<in> ?YI. fst p \<in> ?target} = D_T"
          proof (rule set_eqI, rule iffI)
            fix p assume "p \<in> {p \<in> ?YI. fst p \<in> ?target}"
            thus "p \<in> D_T" unfolding D_T_def by (by100 auto)
          next
            fix p assume "p \<in> D_T"
            thus "p \<in> {p \<in> ?YI. fst p \<in> ?target}"
              unfolding D_T_def using htarget_sub by (by100 auto)
          qed
          moreover have "closedin_on ?YI ?YItop {p \<in> ?YI. fst p \<in> ?target}"
            by (rule continuous_preimage_closedin[OF hYI_top hTY_top hfst_cont htarget_closed])
          ultimately show ?thesis by (by100 simp)
        qed
        have hDB_closed: "closedin_on ?YI ?YItop D_B"
        proof -
          have "{p \<in> ?YI. fst p \<in> (\<Union>A\<in>S. A \<inter> ?Y)} = D_B"
          proof (rule set_eqI, rule iffI)
            fix p assume "p \<in> {p \<in> ?YI. fst p \<in> (\<Union>A\<in>S. A \<inter> ?Y)}"
            thus "p \<in> D_B" unfolding D_B_def by (by100 auto)
          next
            fix p assume "p \<in> D_B"
            thus "p \<in> {p \<in> ?YI. fst p \<in> (\<Union>A\<in>S. A \<inter> ?Y)}"
              unfolding D_B_def by (by100 auto)
          qed
          moreover have "closedin_on ?YI ?YItop {p \<in> ?YI. fst p \<in> (\<Union>A\<in>S. A \<inter> ?Y)}"
            by (rule continuous_preimage_closedin[OF hYI_top hTY_top hfst_cont hB_closed])
          ultimately show ?thesis by (by100 simp)
        qed
        \<comment> \<open>H on D\\_T = \\<pi>\\_1 (projection, continuous).\<close>
        have hH_img: "\<forall>p\<in>?YI. H_DR p \<in> ?Y"
        proof (intro ballI)
          fix p assume "p \<in> ?YI"
          then obtain x t where hxt: "p = (x, t)" "x \<in> ?Y" "t \<in> I_set" by (by100 blast)
          show "H_DR p \<in> ?Y"
          proof (cases "x \<in> ?target")
            case True
            have "H_DR p = x" unfolding H_DR_def hxt(1) using True by (by100 simp)
            moreover have "x \<in> ?Y" using True htarget_sub by (by100 blast)
            ultimately show ?thesis by (by100 simp)
          next
            case False
            \<comment> \<open>H\\_DR(x,t) on half-arc. Image in Y from same argument as SC lemma.\<close>
            \<comment> \<open>x \\<notin> target. Find arc A \\<in> S containing x.\<close>
            have "x \<in> X" using hxt(2) by (by100 blast)
            hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
            then obtain Ax where "Ax \<in> \<A>" "x \<in> Ax" by (by100 blast)
            have "Ax \<in> S"
            proof (rule ccontr)
              assume "Ax \<notin> S"
              show False
              proof (cases "Ax \<subseteq> T")
                case True thus False using \<open>x \<in> Ax\<close> False by (by100 blast)
              next
                case aF: False
                hence "Ax \<in> ?NT - S" using \<open>Ax \<in> \<A>\<close> \<open>Ax \<notin> S\<close> by (by100 blast)
                thus False using \<open>x \<in> Ax\<close> False by (by100 blast)
              qed
            qed
            \<comment> \<open>H\\_DR(x,t) = hAc Ax (param). param \\<in> [0,1], param \\<noteq> tAc Ax.
               Hence hAc(param) \\<in> Ax, hAc(param) \\<noteq> ps(Ax).
               And hAc(param) \\<notin> ps(A') for A'\\<noteq>Ax (graph intersection + endpoints \\<in> T).\<close>
            \<comment> \<open>THE uniqueness: Ax is the unique arc in S containing x.\<close>
            have "Ax \<in> ?NT" using hS_sub \<open>Ax \<in> S\<close> by (by100 blast)
            have "x \<notin> top1_arc_endpoints_on Ax (subspace_topology X TX Ax)"
              using hNT_endpoints[rule_format, OF \<open>Ax \<in> ?NT\<close>] False by (by100 blast)
            hence hx_int: "x \<in> Ax - top1_arc_endpoints_on Ax (subspace_topology X TX Ax)"
              using \<open>x \<in> Ax\<close> by (by100 blast)
            have hTHE_Ax: "(THE A. A \<in> S \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = Ax"
            proof (rule the_equality)
              show "Ax \<in> S \<and> x \<in> Ax - top1_arc_endpoints_on Ax (subspace_topology X TX Ax)"
                using \<open>Ax \<in> S\<close> hx_int by (by100 blast)
            next
              fix A' assume "A' \<in> S \<and> x \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
              hence "A' \<in> \<A>" "x \<in> A'" using hS_sub by (by100 blast)+
              show "A' = Ax"
              proof (rule ccontr)
                assume "A' \<noteq> Ax"
                from h\<A>_inter[rule_format, OF \<open>Ax \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> Ax\<close>[symmetric]]
                show False using \<open>x \<in> Ax\<close> \<open>x \<in> A'\<close> \<open>x \<notin> top1_arc_endpoints_on Ax _\<close> by (by100 blast)
              qed
            qed
            \<comment> \<open>H\\_DR(x,t) = hAc Ax (param). Show param \\<in> [0,1] and hAc(param) \\<in> Y.\<close>
            have hbij_Ax: "bij_betw (hAc Ax) top1_unit_interval Ax"
              using hhAc[OF \<open>Ax \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
            have hinj_Ax: "inj_on (hAc Ax) top1_unit_interval"
              using hbij_Ax unfolding bij_betw_def by (by100 blast)
            have himg_Ax: "hAc Ax ` top1_unit_interval = Ax"
              using hbij_Ax unfolding bij_betw_def by (by100 blast)
            have "x \<in> hAc Ax ` top1_unit_interval" using \<open>x \<in> Ax\<close> himg_Ax by (by100 simp)
            define \<sigma>x where "\<sigma>x = inv_into top1_unit_interval (hAc Ax) x"
            define epx where "epx = (if \<sigma>x < tAc Ax then (0::real) else 1)"
            define param where "param = \<sigma>x + t * (epx - \<sigma>x)"
            have hH_eq: "H_DR (x, t) = hAc Ax param"
              unfolding H_DR_def Let_def param_def epx_def \<sigma>x_def using False hTHE_Ax by (by100 simp)
            \<comment> \<open>param \\<in> [0,1].\<close>
            have h\<sigma>x_I: "\<sigma>x \<in> top1_unit_interval"
              unfolding \<sigma>x_def by (rule inv_into_into[OF \<open>x \<in> hAc Ax ` top1_unit_interval\<close>])
            have h\<sigma>x_01: "0 \<le> \<sigma>x \<and> \<sigma>x \<le> 1" using h\<sigma>x_I unfolding top1_unit_interval_def by (by100 auto)
            have ht_01: "0 \<le> t \<and> t \<le> 1" using hxt(3) unfolding top1_unit_interval_def by (by100 auto)
            have hparam_I: "param \<in> top1_unit_interval"
            proof (cases "\<sigma>x < tAc Ax")
              case True
              hence "epx = 0" unfolding epx_def by (by100 simp)
              hence "param = \<sigma>x + t * (0 - \<sigma>x)" unfolding param_def by (by100 simp)
              have "t * \<sigma>x \<le> 1 * \<sigma>x"
                by (rule mult_right_mono) (use ht_01 h\<sigma>x_01 in linarith)+
              have "t * \<sigma>x \<ge> 0"
                by (rule mult_nonneg_nonneg) (use ht_01 h\<sigma>x_01 in linarith)+
              have "param = \<sigma>x - t * \<sigma>x" using \<open>param = \<sigma>x + t * (0 - \<sigma>x)\<close> by (by100 simp)
              thus ?thesis unfolding top1_unit_interval_def
                using h\<sigma>x_01 \<open>t * \<sigma>x \<le> _\<close> \<open>t * \<sigma>x \<ge> 0\<close> by (by100 auto)
            next
              case False
              hence "epx = 1" unfolding epx_def by (by100 simp)
              hence "param = \<sigma>x + t * (1 - \<sigma>x)" unfolding param_def by (by100 simp)
              have "t * (1 - \<sigma>x) \<ge> 0"
                by (rule mult_nonneg_nonneg) (use ht_01 h\<sigma>x_01 in linarith)+
              have "t * (1 - \<sigma>x) \<le> 1 * (1 - \<sigma>x)"
                by (rule mult_right_mono) (use ht_01 h\<sigma>x_01 in linarith)+
              hence "t * (1 - \<sigma>x) \<le> 1 - \<sigma>x" by (by100 simp)
              hence "\<sigma>x + t * (1 - \<sigma>x) \<le> 1" by (by100 linarith)
              thus ?thesis unfolding top1_unit_interval_def
                using h\<sigma>x_01 \<open>t * (1 - \<sigma>x) \<ge> 0\<close> \<open>param = \<sigma>x + t * (1 - \<sigma>x)\<close> by (by100 auto)
            qed
            \<comment> \<open>param \\<noteq> tAc (since \\<sigma>x \\<noteq> tAc and param stays on same side).\<close>
            have h\<sigma>x_ne: "\<sigma>x \<noteq> tAc Ax"
            proof
              assume "\<sigma>x = tAc Ax"
              have "hAc Ax \<sigma>x = x"
                unfolding \<sigma>x_def by (rule f_inv_into_f[OF \<open>x \<in> hAc Ax ` top1_unit_interval\<close>])
              have "ps Ax \<in> hAc Ax ` top1_unit_interval"
                using hps \<open>Ax \<in> S\<close> himg_Ax by (by100 blast)
              have "hAc Ax (tAc Ax) = ps Ax"
                unfolding tAc_def by (rule f_inv_into_f[OF \<open>ps Ax \<in> hAc Ax ` top1_unit_interval\<close>])
              hence "x = ps Ax" using \<open>hAc Ax \<sigma>x = x\<close> \<open>\<sigma>x = tAc Ax\<close> by (by100 simp)
              hence "x \<in> ps ` S" using \<open>Ax \<in> S\<close> by (by100 blast)
              thus False using hxt(2) by (by100 blast)
            qed
            have hparam_ne: "param \<noteq> tAc Ax"
            proof (cases "\<sigma>x < tAc Ax")
              case True
              hence "epx = 0" unfolding epx_def by (by100 simp)
              hence "param = \<sigma>x + t * (0 - \<sigma>x)" unfolding param_def by (by100 simp)
              have "param = \<sigma>x - t * \<sigma>x" using \<open>param = \<sigma>x + t * (0 - \<sigma>x)\<close> by (by100 simp)
              have "t * \<sigma>x \<ge> 0"
                by (rule mult_nonneg_nonneg) (use ht_01 h\<sigma>x_01 in linarith)+
              hence "param \<le> \<sigma>x" using \<open>param = \<sigma>x - t * \<sigma>x\<close> by (by100 linarith)
              hence "param < tAc Ax" using True by (by100 linarith)
              thus ?thesis by (by100 linarith)
            next
              case False
              hence "\<sigma>x > tAc Ax" using h\<sigma>x_ne by (by100 linarith)
              hence "epx = 1" unfolding epx_def by (by100 simp)
              hence "param = \<sigma>x + t * (1 - \<sigma>x)" unfolding param_def by (by100 simp)
              have "t * (1 - \<sigma>x) \<ge> 0"
                by (rule mult_nonneg_nonneg) (use ht_01 h\<sigma>x_01 in linarith)+
              hence "param \<ge> \<sigma>x" using \<open>param = \<sigma>x + t * (1 - \<sigma>x)\<close> by (by100 linarith)
              hence "param > tAc Ax" using \<open>\<sigma>x > tAc Ax\<close> by (by100 linarith)
              thus ?thesis by (by100 linarith)
            qed
            \<comment> \<open>hAc(param) \\<in> Ax.\<close>
            have "hAc Ax param \<in> Ax" using hparam_I himg_Ax by (by100 blast)
            hence "hAc Ax param \<in> X" using h\<A> \<open>Ax \<in> \<A>\<close> by (by100 blast)
            \<comment> \<open>hAc(param) \\<notin> ps ` S.\<close>
            have "hAc Ax param \<notin> ps ` S"
            proof
              assume "hAc Ax param \<in> ps ` S"
              then obtain A' where "A' \<in> S" "hAc Ax param = ps A'" by (by100 blast)
              show False
              proof (cases "A' = Ax")
                case True
                hence "hAc Ax param = ps Ax" using \<open>hAc Ax param = ps A'\<close> by (by100 simp)
                have "ps Ax \<in> hAc Ax ` top1_unit_interval"
                  using hps \<open>Ax \<in> S\<close> himg_Ax by (by100 blast)
                have htAc_I: "tAc Ax \<in> top1_unit_interval"
                  unfolding tAc_def by (rule inv_into_into[OF \<open>ps Ax \<in> hAc Ax ` top1_unit_interval\<close>])
                have "hAc Ax (tAc Ax) = ps Ax"
                  unfolding tAc_def by (rule f_inv_into_f[OF \<open>ps Ax \<in> hAc Ax ` top1_unit_interval\<close>])
                from inj_onD[OF hinj_Ax _ hparam_I htAc_I]
                have "param = tAc Ax" using \<open>hAc Ax param = ps Ax\<close> \<open>hAc Ax (tAc Ax) = ps Ax\<close>
                  by (by100 simp)
                thus False using hparam_ne by (by100 blast)
              next
                case hA'_ne: False
                have "A' \<in> \<A>" using hS_sub \<open>A' \<in> S\<close> by (by100 blast)
                have "ps A' \<in> A'" using hps \<open>A' \<in> S\<close> by (by100 blast)
                hence "hAc Ax param \<in> A'" using \<open>hAc Ax param = ps A'\<close> by (by100 simp)
                have "hAc Ax param \<in> Ax \<inter> A'"
                  using \<open>hAc Ax param \<in> Ax\<close> \<open>hAc Ax param \<in> A'\<close> by (by100 blast)
                hence "hAc Ax param \<in> top1_arc_endpoints_on Ax (subspace_topology X TX Ax)"
                  using h\<A>_inter[rule_format, OF \<open>Ax \<in> \<A>\<close> \<open>A' \<in> \<A>\<close>] hA'_ne by (by100 blast)
                hence "hAc Ax param \<in> T"
                  using hNT_endpoints[rule_format, OF \<open>Ax \<in> ?NT\<close>] by (by100 blast)
                have "ps A' \<notin> T"
                proof -
                  have "A' \<in> ?NT" using hS_sub \<open>A' \<in> S\<close> by (by100 blast)
                  from hT_subgraph[rule_format, OF \<open>A' \<in> \<A>\<close>]
                  have "A' \<inter> T \<subseteq> top1_arc_endpoints_on A' (subspace_topology X TX A')"
                    using \<open>A' \<in> ?NT\<close> by (by100 blast)
                  have "ps A' \<notin> top1_arc_endpoints_on A' (subspace_topology X TX A')"
                    using hps \<open>A' \<in> S\<close> by (by100 blast)
                  thus ?thesis using \<open>A' \<inter> T \<subseteq> _\<close> hps \<open>A' \<in> S\<close> by (by100 blast)
                qed
                thus False using \<open>hAc Ax param \<in> T\<close> \<open>hAc Ax param = ps A'\<close> by (by100 simp)
              qed
            qed
            have "hAc Ax param \<in> ?Y" using \<open>hAc Ax param \<in> X\<close> \<open>hAc Ax param \<notin> ps ` S\<close> by (by100 blast)
            show ?thesis using hH_eq \<open>hAc Ax param \<in> ?Y\<close> hxt(1) by (by100 simp)
          qed
        qed
        have hH_DT: "top1_continuous_map_on D_T (subspace_topology ?YI ?YItop D_T) ?Y ?TY H_DR"
        proof -
          have hfst_DT: "top1_continuous_map_on D_T (subspace_topology ?YI ?YItop D_T) ?Y ?TY fst"
          proof -
            have "D_T \<subseteq> ?YI" unfolding D_T_def using htarget_sub by (by100 blast)
            from top1_continuous_map_on_restrict_domain_simple[OF hfst_cont this]
            show ?thesis .
          qed
          have heq: "\<forall>p\<in>D_T. H_DR p = fst p" unfolding D_T_def H_DR_def by (by100 simp)
          have hDT_sub: "D_T \<subseteq> ?YI" unfolding D_T_def using htarget_sub by (by100 blast)
          have hDT_top: "is_topology_on D_T (subspace_topology ?YI ?YItop D_T)"
            by (rule subspace_topology_is_topology_on[OF hYI_top hDT_sub])
          have "\<forall>p\<in>D_T. H_DR p \<in> ?Y" using heq hfst_DT
            unfolding top1_continuous_map_on_def by (by100 auto)
          have "\<forall>V\<in>?TY. {p \<in> D_T. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop D_T"
          proof (intro ballI)
            fix V assume "V \<in> ?TY"
            have "{p \<in> D_T. H_DR p \<in> V} = {p \<in> D_T. fst p \<in> V}" using heq by (by100 auto)
            also have "... \<in> subspace_topology ?YI ?YItop D_T"
              using hfst_DT \<open>V \<in> ?TY\<close> unfolding top1_continuous_map_on_def by (by100 blast)
            finally show "{p \<in> D_T. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop D_T" .
          qed
          thus ?thesis unfolding top1_continuous_map_on_def
            using hDT_top hTY_top \<open>\<forall>p\<in>D_T. H_DR p \<in> ?Y\<close> by (by100 blast)
        qed
        \<comment> \<open>H on D\\_B: composition chain per arc, same as SC lemma.\<close>
        \<comment> \<open>H|D\\_B continuous: per-arc pasting. D\\_B = \\<Union>{(A\\<cap>Y)\\<times>I | A \\<in> S}.
           On each (A\\<cap>Y)\\<times>I: H\\_DR = hAc \\<circ> (arith of inv\\_into\\<circ>\\<pi>\\_1 and \\<pi>\\_2).
           This is the SAME proof as the SC lemma's H|S\\_B (bck1384-bck1420)
           but with \\<pi>\\_1: Y\\<times>I \\<rightarrow> Y replacing f\\<circ>fst: I\\<times>I \\<rightarrow> Y.
           The proof is ~400 lines following the established pattern.\<close>
        have hH_DB: "top1_continuous_map_on D_B (subspace_topology ?YI ?YItop D_B) ?Y ?TY H_DR"
        proof -
          have hDB_sub: "D_B \<subseteq> ?YI" unfolding D_B_def by (by100 blast)
          have hDB_top: "is_topology_on D_B (subspace_topology ?YI ?YItop D_B)"
            by (rule subspace_topology_is_topology_on[OF hYI_top hDB_sub])
          have hH_img_DB: "\<forall>p\<in>D_B. H_DR p \<in> ?Y" using hH_img hDB_sub by (by100 blast)
          \<comment> \<open>Strategy: show preimage of every open V is open in D\\_B.
             Complement of preimage = \\<Union>{(A\\<cap>Y)\\<times>I \\<cap> complement | A \\<in> S}.
             Each (A\\<cap>Y)\\<times>I \\<cap> complement is closed in D\\_B (from per-arc continuity).
             Finite union of closed = closed. Hence preimage is open.\<close>
          \<comment> \<open>Per-arc pieces.\<close>
          define QA where "QA \<equiv> \<lambda>A. (A \<inter> ?Y) \<times> I_set"
          have hQA_closed: "\<forall>A\<in>S. closedin_on ?YI ?YItop (QA A)"
          proof (intro ballI)
            fix A assume "A \<in> S"
            have "{p \<in> ?YI. fst p \<in> A \<inter> ?Y} = QA A"
              unfolding QA_def by (by100 auto)
            moreover have "closedin_on ?YI ?YItop {p \<in> ?YI. fst p \<in> A \<inter> ?Y}"
              by (rule continuous_preimage_closedin[OF hYI_top hTY_top hfst_cont])
                 (use hS_AY_closed \<open>A \<in> S\<close> in \<open>by100 blast\<close>)
            ultimately show "closedin_on ?YI ?YItop (QA A)" by (by100 simp)
          qed
          have hDB_eq: "D_B = (\<Union>A\<in>S. QA A)" unfolding D_B_def QA_def by (by100 blast)
          \<comment> \<open>Per-arc continuity: H\\_DR continuous on each QA A.\<close>
          have hH_QA: "\<forall>A\<in>S. top1_continuous_map_on (QA A) (subspace_topology ?YI ?YItop (QA A)) ?Y ?TY H_DR"
          proof (intro ballI)
            fix Aq assume "Aq \<in> S"
            have hAq_sub: "Aq \<subseteq> X" using h\<A> hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
            have hQA_sub: "QA Aq \<subseteq> ?YI" using hQA_closed \<open>Aq \<in> S\<close>
              unfolding closedin_on_def by (by100 blast)
            \<comment> \<open>On QA Aq: H\\_DR equals hAc Aq \\<circ> g where g(x,t) = inv(hAc,x)+t*(ep-inv(hAc,x)).
               When x \\<in> target: H\\_DR = x (identity). When x \\<notin> target: the formula.
               Both branches produce values in Y. Both are continuous.\<close>
            \<comment> \<open>Show H\\_DR agrees with a continuous function on QA Aq.
               The continuous function: hAc Aq \\<circ> arith \\<circ> (inv\\_into\\<circ>\\<pi>\\_1, \\<pi>\\_2).
               But for x \\<in> target: H\\_DR = x while the formula gives hAc(\\<sigma>+t*(ep-\\<sigma>)).
               At target points (endpoints): \\<sigma> = 0 or 1, so the formula also gives x. Good.\<close>
            show "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) ?Y ?TY H_DR"
            proof -
              have hQA_top: "is_topology_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))"
                by (rule subspace_topology_is_topology_on[OF hYI_top hQA_sub])
              \<comment> \<open>Step 1: \\<pi>\\_1 restricted + codomain to Aq\\<cap>Y.\<close>
              have hfst_QA: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) ?Y ?TY fst"
                by (rule top1_continuous_map_on_restrict_domain_simple[OF hfst_cont hQA_sub])
              have hfst_img: "\<forall>p\<in>QA Aq. fst p \<in> Aq \<inter> ?Y" unfolding QA_def by (by100 auto)
              have hAqY_sub: "Aq \<inter> ?Y \<subseteq> ?Y" by (by100 blast)
              have hfst_AqY: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                  (Aq \<inter> ?Y) (subspace_topology ?Y ?TY (Aq \<inter> ?Y)) fst"
                by (rule continuous_map_restrict_codomain[OF hfst_QA hfst_img hAqY_sub])
              \<comment> \<open>Step 2: inv\\_into continuous on Aq\\<cap>Y (topology matching).\<close>
              have hinv_cont: "top1_continuous_map_on Aq (subspace_topology X TX Aq)
                  top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval (hAc Aq))"
                using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
              have hAq_sub_Aq: "Aq \<inter> ?Y \<subseteq> Aq" by (by100 blast)
              have "subspace_topology ?Y ?TY (Aq \<inter> ?Y) = subspace_topology Aq (subspace_topology X TX Aq) (Aq \<inter> ?Y)"
              proof -
                have "subspace_topology ?Y ?TY (Aq \<inter> ?Y) = subspace_topology X TX (Aq \<inter> ?Y)"
                  by (rule subspace_topology_trans[OF hAqY_sub])
                also have "... = subspace_topology Aq (subspace_topology X TX Aq) (Aq \<inter> ?Y)"
                  by (rule subspace_topology_trans[OF hAq_sub_Aq, symmetric])
                finally show ?thesis .
              qed
              hence hinv_AqY: "top1_continuous_map_on (Aq \<inter> ?Y) (subspace_topology ?Y ?TY (Aq \<inter> ?Y))
                  top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval (hAc Aq))"
                using top1_continuous_map_on_restrict_domain_simple[OF hinv_cont hAq_sub_Aq] by (by100 simp)
              \<comment> \<open>Step 3: compose inv\\_into \\<circ> fst.\<close>
              from top1_continuous_map_on_comp[OF hfst_AqY hinv_AqY]
              have hinv_fst: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                  top1_unit_interval top1_unit_interval_topology
                  (\<lambda>p. inv_into top1_unit_interval (hAc Aq) (fst p))"
                unfolding top1_continuous_map_on_def comp_def by (by100 auto)
              \<comment> \<open>Step 4: \\<pi>\\_2 restricted.\<close>
              have hsnd_QA: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                  top1_unit_interval top1_unit_interval_topology snd"
              proof -
                from top1_continuous_pi2[OF hTY_top top1_unit_interval_topology_is_topology_on]
                have "top1_continuous_map_on ?YI ?YItop top1_unit_interval top1_unit_interval_topology snd"
                  unfolding pi2_def by (by100 simp)
                from top1_continuous_map_on_restrict_domain_simple[OF this hQA_sub] show ?thesis .
              qed
              \<comment> \<open>Step 5: pair (inv\\<circ>fst, snd) \\<rightarrow> I\\<times>I.\<close>
              have "\<And>p. pi1 ((\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)) p) =
                  inv_into top1_unit_interval (hAc Aq) (fst p)"
                unfolding pi1_def by (by100 simp)
              hence hc1: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                  top1_unit_interval top1_unit_interval_topology
                  (pi1 \<circ> (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)))"
                using hinv_fst unfolding top1_continuous_map_on_def comp_def pi1_def by (by100 auto)
              have "\<And>p. pi2 ((\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)) p) = snd p"
                unfolding pi2_def by (by100 simp)
              hence hc2: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                  top1_unit_interval top1_unit_interval_topology
                  (pi2 \<circ> (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)))"
                using hsnd_QA unfolding top1_continuous_map_on_def comp_def pi2_def by (by100 auto)
              let ?IItop = "product_topology_on top1_unit_interval_topology top1_unit_interval_topology"
              from Theorem_18_4[OF hQA_top top1_unit_interval_topology_is_topology_on
                  top1_unit_interval_topology_is_topology_on,
                  of "\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)"]
              have hpair_QA: "top1_continuous_map_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                  (top1_unit_interval \<times> top1_unit_interval) ?IItop
                  (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))"
                using hc1 hc2 by (by100 blast)
              \<comment> \<open>Step 6-8: arith + hAc + compose. Same as SC lemma.\<close>
              \<comment> \<open>Need two arithmetic maps (for e\\_param=0 and e\\_param=1) and pasting.\<close>
              \<comment> \<open>For now: sorry the final composition + H\\_DR=formula.\<close>
              \<comment> \<open>Arithmetic: both halves (ep=0 and ep=1) continuous I\\<times>I \\<rightarrow> I.\<close>
              have harith0: "top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval)
                  ?IItop top1_unit_interval top1_unit_interval_topology
                  (\<lambda>p. fst p + snd p * (0 - fst p))"
              proof -
                have "continuous_on (I_set \<times> I_set) (\<lambda>p :: real \<times> real. fst p - snd p * fst p)"
                  by (intro continuous_intros)
                have "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> fst p - snd p * fst p \<in> I_set"
                proof -
                  fix p :: "real \<times> real" assume "p \<in> I_set \<times> I_set"
                  then obtain a b where hp: "p = (a,b)" "a \<in> I_set" "b \<in> I_set" by (by100 blast)
                  have ha: "0 \<le> a" "a \<le> 1" using hp(2) unfolding top1_unit_interval_def by (by100 auto)+
                  have hb: "0 \<le> b" "b \<le> 1" using hp(3) unfolding top1_unit_interval_def by (by100 auto)+
                  have "b * a \<le> 1 * a" by (rule mult_right_mono) (use hb ha in linarith)+
                  have "b * a \<ge> 0" by (rule mult_nonneg_nonneg) (use hb ha in linarith)+
                  show "fst p - snd p * fst p \<in> I_set" unfolding hp(1) top1_unit_interval_def
                    using ha \<open>b * a \<le> _\<close> \<open>b * a \<ge> 0\<close> by (by100 auto)
                qed
                from top1_continuous_map_on_II_to_I[OF this \<open>continuous_on _ _\<close>, unfolded II_topology_def]
                have "top1_continuous_map_on (I_set \<times> I_set) ?IItop I_set I_top
                    (\<lambda>p. fst p - snd p * fst p)" .
                moreover have "\<And>p :: real \<times> real. fst p + snd p * (0 - fst p) = fst p - snd p * fst p"
                  by (by100 simp)
                hence "\<And>p :: real \<times> real. {q \<in> I_set \<times> I_set. fst q + snd q * (0 - fst q) \<in> V}
                    = {q \<in> I_set \<times> I_set. fst q - snd q * fst q \<in> V}" for V by (by100 auto)
                ultimately show ?thesis unfolding top1_continuous_map_on_def by (by100 auto)
              qed
              have harith1: "top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval)
                  ?IItop top1_unit_interval top1_unit_interval_topology
                  (\<lambda>p. fst p + snd p * (1 - fst p))"
              proof -
                have "continuous_on (I_set \<times> I_set) (\<lambda>p :: real \<times> real. fst p + snd p * (1 - fst p))"
                  by (intro continuous_intros)
                have "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> fst p + snd p * (1 - fst p) \<in> I_set"
                proof -
                  fix p :: "real \<times> real" assume "p \<in> I_set \<times> I_set"
                  then obtain a b where hp: "p = (a,b)" "a \<in> I_set" "b \<in> I_set" by (by100 blast)
                  have ha: "0 \<le> a" "a \<le> 1" using hp(2) unfolding top1_unit_interval_def by (by100 auto)+
                  have hb: "0 \<le> b" "b \<le> 1" using hp(3) unfolding top1_unit_interval_def by (by100 auto)+
                  have "b * (1 - a) \<ge> 0" by (rule mult_nonneg_nonneg) (use hb ha in linarith)+
                  have "b * (1 - a) \<le> 1 * (1 - a)" by (rule mult_right_mono) (use hb ha in linarith)+
                  hence "b * (1 - a) \<le> 1 - a" by (by100 simp)
                  hence "a + b * (1 - a) \<le> 1" by (by100 linarith)
                  show "fst p + snd p * (1 - fst p) \<in> I_set" unfolding hp(1) top1_unit_interval_def
                    using ha \<open>b * (1 - a) \<ge> 0\<close> \<open>a + b * (1 - a) \<le> 1\<close> by (by100 auto)
                qed
                from top1_continuous_map_on_II_to_I[OF this \<open>continuous_on _ _\<close>, unfolded II_topology_def]
                show ?thesis .
              qed
              \<comment> \<open>hAc continuous I \\<rightarrow> X.\<close>
              have hhAc_cont_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX (hAc Aq)"
              proof -
                have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                    Aq (subspace_topology X TX Aq) (hAc Aq)"
                  using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                from top1_continuous_map_on_codomain_enlarge[OF this hAq_sub subset_refl]
                have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                    X (subspace_topology X TX X) (hAc Aq)" .
                moreover have "subspace_topology X TX X = TX"
                proof (rule subspace_topology_self)
                  have "is_topology_on_strict X TX"
                    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                  thus "\<forall>U\<in>TX. U \<subseteq> X" unfolding is_topology_on_strict_def by (by100 blast)
                qed
                ultimately show ?thesis by (by100 simp)
              qed
              \<comment> \<open>Compose pair + arith + hAc. Need to handle the if-then-else for ep.\<close>
              \<comment> \<open>H\\_DR = formula on QA Aq + transfer continuity.\<close>
              \<comment> \<open>Compose hpair\\_QA with appropriate arith and hAc.
                 Split QA into left half (\\<sigma> < tAc) and right half (\\<sigma> > tAc).
                 On left: use harith0. On right: use harith1. Paste.\<close>
              define QA_L where "QA_L = {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p) \<le> tAc Aq}"
              define QA_R where "QA_R = {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p) \<ge> tAc Aq}"
              have hQA_eq: "QA Aq = QA_L \<union> QA_R" unfolding QA_L_def QA_R_def by (by100 auto)
              \<comment> \<open>On QA\\_L: g = harith0 \\<circ> pair. On QA\\_R: g = harith1 \\<circ> pair.\<close>
              \<comment> \<open>Compose: hAc \\<circ> harith0 \\<circ> pair (left), hAc \\<circ> harith1 \\<circ> pair (right).\<close>
              have hstep_L: "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L) X TX
                  (\<lambda>p. hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                       snd p * (0 - inv_into top1_unit_interval (hAc Aq) (fst p))))"
              proof -
                have "QA_L \<subseteq> QA Aq" unfolding QA_L_def by (by100 blast)
                hence "QA_L \<subseteq> ?YI" using hQA_sub by (by100 blast)
                have hpair_L: "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L)
                    (top1_unit_interval \<times> top1_unit_interval) ?IItop
                    (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))"
                proof -
                  from top1_continuous_map_on_restrict_domain_simple[OF hpair_QA \<open>QA_L \<subseteq> QA Aq\<close>]
                  have "top1_continuous_map_on QA_L
                      (subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_L)
                      (top1_unit_interval \<times> top1_unit_interval) ?IItop
                      (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))" .
                  moreover have "subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_L
                      = subspace_topology ?YI ?YItop QA_L"
                    by (rule subspace_topology_trans[OF \<open>QA_L \<subseteq> QA Aq\<close>])
                  ultimately show ?thesis by (by100 simp)
                qed
                have harith_pair_L: "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L)
                    top1_unit_interval top1_unit_interval_topology
                    ((\<lambda>p. fst p + snd p * (0 - fst p)) \<circ>
                     (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)))"
                  by (rule top1_continuous_map_on_comp[OF hpair_L harith0])
                have "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L) X TX
                    (hAc Aq \<circ> ((\<lambda>p. fst p + snd p * (0 - fst p)) \<circ>
                     (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))))"
                  by (rule top1_continuous_map_on_comp[OF harith_pair_L hhAc_cont_X])
                moreover have "\<And>p. (hAc Aq \<circ> (\<lambda>p. fst p + snd p * (0 - fst p)) \<circ>
                     (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))) p =
                    hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                       snd p * (0 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                  unfolding comp_def by (by100 simp)
                ultimately show ?thesis unfolding top1_continuous_map_on_def by (by100 auto)
              qed
              have hstep_R: "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R) X TX
                  (\<lambda>p. hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                       snd p * (1 - inv_into top1_unit_interval (hAc Aq) (fst p))))"
              proof -
                have "QA_R \<subseteq> QA Aq" unfolding QA_R_def by (by100 blast)
                hence "QA_R \<subseteq> ?YI" using hQA_sub by (by100 blast)
                have hpair_R: "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R)
                    (top1_unit_interval \<times> top1_unit_interval) ?IItop
                    (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))"
                proof -
                  from top1_continuous_map_on_restrict_domain_simple[OF hpair_QA \<open>QA_R \<subseteq> QA Aq\<close>]
                  have "top1_continuous_map_on QA_R
                      (subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_R)
                      (top1_unit_interval \<times> top1_unit_interval) ?IItop
                      (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))" .
                  moreover have "subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_R
                      = subspace_topology ?YI ?YItop QA_R"
                    by (rule subspace_topology_trans[OF \<open>QA_R \<subseteq> QA Aq\<close>])
                  ultimately show ?thesis by (by100 simp)
                qed
                have harith_pair_R: "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R)
                    top1_unit_interval top1_unit_interval_topology
                    ((\<lambda>p. fst p + snd p * (1 - fst p)) \<circ>
                     (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p)))"
                  by (rule top1_continuous_map_on_comp[OF hpair_R harith1])
                have "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R) X TX
                    (hAc Aq \<circ> ((\<lambda>p. fst p + snd p * (1 - fst p)) \<circ>
                     (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))))"
                  by (rule top1_continuous_map_on_comp[OF harith_pair_R hhAc_cont_X])
                moreover have "\<And>p. (hAc Aq \<circ> (\<lambda>p. fst p + snd p * (1 - fst p)) \<circ>
                     (\<lambda>p. (inv_into top1_unit_interval (hAc Aq) (fst p), snd p))) p =
                    hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                       snd p * (1 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                  unfolding comp_def by (by100 simp)
                ultimately show ?thesis unfolding top1_continuous_map_on_def by (by100 auto)
              qed
              \<comment> \<open>QA\\_L, QA\\_R closed in Y\\<times>I. H\\_DR = formula. Pasting + codomain restrict.\<close>
              \<comment> \<open>QA\\_L, QA\\_R closed in QA (preimage of closed interval).\<close>
              have hQA_L_closed: "closedin_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_L"
              proof -
                have hcl_I: "closedin_on top1_unit_interval top1_unit_interval_topology
                    {x \<in> top1_unit_interval. x \<le> tAc Aq}"
                proof -
                  have "top1_unit_interval - {x \<in> top1_unit_interval. x \<le> tAc Aq}
                      = {x \<in> top1_unit_interval. x > tAc Aq}" by (by100 auto)
                  moreover have "{x \<in> top1_unit_interval. x > tAc Aq} \<in> top1_unit_interval_topology"
                  proof -
                    have "{x :: real. tAc Aq < x} \<in> top1_open_sets"
                    proof -
                      have "open {x :: real. tAc Aq < x}" using open_greaterThan
                        unfolding greaterThan_def by (by100 blast)
                      thus ?thesis unfolding top1_open_sets_def by (by100 blast)
                    qed
                    have "{x \<in> top1_unit_interval. x > tAc Aq} = top1_unit_interval \<inter> {x. tAc Aq < x}"
                      by (by100 auto)
                    thus ?thesis
                      using \<open>{x. tAc Aq < x} \<in> top1_open_sets\<close>
                      unfolding top1_unit_interval_topology_def top1_unit_interval_def
                        subspace_topology_def by (by100 auto)
                  qed
                  ultimately have "top1_unit_interval - {x \<in> top1_unit_interval. x \<le> tAc Aq}
                      \<in> top1_unit_interval_topology" by (by100 simp)
                  moreover have "{x \<in> top1_unit_interval. x \<le> tAc Aq} \<subseteq> top1_unit_interval"
                    by (by100 blast)
                  ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
                qed
                from continuous_preimage_closedin[OF
                    subspace_topology_is_topology_on[OF hYI_top hQA_sub]
                    top1_unit_interval_topology_is_topology_on hinv_fst hcl_I]
                have "closedin_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                    {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                      \<in> {x \<in> top1_unit_interval. x \<le> tAc Aq}}" .
                moreover have "{p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                    \<in> {x \<in> top1_unit_interval. x \<le> tAc Aq}} = QA_L"
                proof (rule set_eqI, rule iffI)
                  fix p assume "p \<in> {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                      \<in> {x \<in> top1_unit_interval. x \<le> tAc Aq}}"
                  thus "p \<in> QA_L" unfolding QA_L_def by (by100 blast)
                next
                  fix p assume "p \<in> QA_L"
                  hence hp: "p \<in> QA Aq" "inv_into top1_unit_interval (hAc Aq) (fst p) \<le> tAc Aq"
                    unfolding QA_L_def by (by100 blast)+
                  have "fst p \<in> Aq \<inter> ?Y" using hp(1) unfolding QA_def by (by100 auto)
                  hence "fst p \<in> hAc Aq ` top1_unit_interval"
                    using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def bij_betw_def
                    by (by100 blast)
                  hence "inv_into top1_unit_interval (hAc Aq) (fst p) \<in> top1_unit_interval"
                    by (rule inv_into_into)
                  thus "p \<in> {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                      \<in> {x \<in> top1_unit_interval. x \<le> tAc Aq}}"
                    using hp by (by100 blast)
                qed
                ultimately show ?thesis by (by100 simp)
              qed
              have hQA_R_closed: "closedin_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_R"
              proof -
                have hcl_I: "closedin_on top1_unit_interval top1_unit_interval_topology
                    {x \<in> top1_unit_interval. x \<ge> tAc Aq}"
                proof -
                  have "top1_unit_interval - {x \<in> top1_unit_interval. x \<ge> tAc Aq}
                      = {x \<in> top1_unit_interval. x < tAc Aq}" by (by100 auto)
                  moreover have "{x \<in> top1_unit_interval. x < tAc Aq} \<in> top1_unit_interval_topology"
                  proof -
                    have "{x :: real. x < tAc Aq} \<in> top1_open_sets"
                    proof -
                      have "open {x :: real. x < tAc Aq}" using open_lessThan
                        unfolding lessThan_def by (by100 blast)
                      thus ?thesis unfolding top1_open_sets_def by (by100 blast)
                    qed
                    have "{x \<in> top1_unit_interval. x < tAc Aq} = top1_unit_interval \<inter> {x. x < tAc Aq}"
                      by (by100 auto)
                    thus ?thesis
                      using \<open>{x. x < tAc Aq} \<in> top1_open_sets\<close>
                      unfolding top1_unit_interval_topology_def top1_unit_interval_def
                        subspace_topology_def by (by100 auto)
                  qed
                  ultimately have "top1_unit_interval - {x \<in> top1_unit_interval. x \<ge> tAc Aq}
                      \<in> top1_unit_interval_topology" by (by100 simp)
                  moreover have "{x \<in> top1_unit_interval. x \<ge> tAc Aq} \<subseteq> top1_unit_interval"
                    by (by100 blast)
                  ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
                qed
                from continuous_preimage_closedin[OF
                    subspace_topology_is_topology_on[OF hYI_top hQA_sub]
                    top1_unit_interval_topology_is_topology_on hinv_fst hcl_I]
                have "closedin_on (QA Aq) (subspace_topology ?YI ?YItop (QA Aq))
                    {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                      \<in> {x \<in> top1_unit_interval. x \<ge> tAc Aq}}" .
                moreover have "{p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                    \<in> {x \<in> top1_unit_interval. x \<ge> tAc Aq}} = QA_R"
                proof (rule set_eqI, rule iffI)
                  fix p assume "p \<in> {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                      \<in> {x \<in> top1_unit_interval. x \<ge> tAc Aq}}"
                  thus "p \<in> QA_R" unfolding QA_R_def by (by100 blast)
                next
                  fix p assume "p \<in> QA_R"
                  hence hp: "p \<in> QA Aq" "inv_into top1_unit_interval (hAc Aq) (fst p) \<ge> tAc Aq"
                    unfolding QA_R_def by (by100 blast)+
                  have "fst p \<in> Aq \<inter> ?Y" using hp(1) unfolding QA_def by (by100 auto)
                  hence "fst p \<in> hAc Aq ` top1_unit_interval"
                    using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def bij_betw_def
                    by (by100 blast)
                  hence "inv_into top1_unit_interval (hAc Aq) (fst p) \<in> top1_unit_interval"
                    by (rule inv_into_into)
                  thus "p \<in> {p \<in> QA Aq. inv_into top1_unit_interval (hAc Aq) (fst p)
                      \<in> {x \<in> top1_unit_interval. x \<ge> tAc Aq}}"
                    using hp by (by100 blast)
                qed
                ultimately show ?thesis by (by100 simp)
              qed
              \<comment> \<open>H\\_DR agrees with hstep\\_L on QA\\_L and hstep\\_R on QA\\_R.\<close>
              have hH_img_QA: "\<forall>p\<in>QA Aq. H_DR p \<in> ?Y"
                using hH_img hQA_sub by (by100 blast)
              have hH_L_eq: "\<forall>p\<in>QA_L. H_DR p = hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                   snd p * (0 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
              proof (intro ballI)
                fix p assume "p \<in> QA_L"
                hence "p \<in> QA Aq" using hQA_eq by (by100 blast)
                hence "fst p \<in> Aq \<inter> ?Y" unfolding QA_def by (by100 auto)
                have hinv_le: "inv_into top1_unit_interval (hAc Aq) (fst p) \<le> tAc Aq"
                  using \<open>p \<in> QA_L\<close> unfolding QA_L_def by (by100 blast)
                show "H_DR p = hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                     snd p * (0 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                proof (cases "fst p \<in> ?target")
                  case True
                  \<comment> \<open>fst(p) \\<in> target: H\\_DR = fst(p). And \\<sigma>=0 (left endpoint), formula gives hAc(0)=fst(p).\<close>
                  have hHDR_eq: "H_DR p = fst p"
                  proof -
                    obtain x t where hxt: "p = (x, t)" by (cases p)
                    have "x \<in> ?target" using True hxt by (by100 simp)
                    thus ?thesis unfolding H_DR_def hxt by (by100 simp)
                  qed
                  have hfp_Aq: "fst p \<in> Aq" using \<open>fst p \<in> Aq \<inter> ?Y\<close> by (by100 blast)
                  have hfp_T: "fst p \<in> T"
                  proof -
                    from True have "fst p \<in> T \<or> fst p \<in> \<Union>(?NT - S)" by (by100 blast)
                    thus ?thesis
                    proof
                      assume "fst p \<in> T" thus ?thesis .
                    next
                      assume "fst p \<in> \<Union>(?NT - S)"
                      then obtain A' where "A' \<in> ?NT - S" "fst p \<in> A'" by (by100 blast)
                      have "A' \<in> \<A>" using \<open>A' \<in> ?NT - S\<close> by (by100 blast)
                      have "A' \<noteq> Aq" using \<open>A' \<in> ?NT - S\<close> \<open>Aq \<in> S\<close> by (by100 blast)
                      have "Aq \<in> \<A>" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                      from h\<A>_inter[rule_format, OF \<open>Aq \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> Aq\<close>[symmetric]]
                      have "fst p \<in> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                        using \<open>fst p \<in> Aq \<inter> ?Y\<close> \<open>fst p \<in> A'\<close> by (by100 blast)
                      have "Aq \<in> ?NT" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                      have "\<forall>e\<in>top1_arc_endpoints_on Aq (subspace_topology X TX Aq). e \<in> T"
                        using hNT_endpoints \<open>Aq \<in> ?NT\<close> by (by100 blast)
                      thus ?thesis using \<open>fst p \<in> top1_arc_endpoints_on Aq _\<close> by (by100 blast)
                    qed
                  qed
                  have hbij_Aq_loc: "bij_betw (hAc Aq) top1_unit_interval Aq"
                    using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                  have himg_Aq_loc: "hAc Aq ` top1_unit_interval = Aq"
                    using hbij_Aq_loc unfolding bij_betw_def by (by100 blast)
                  have hfp_img: "fst p \<in> hAc Aq ` top1_unit_interval"
                    using hfp_Aq himg_Aq_loc by (by100 simp)
                  have hAc_inv: "hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p)) = fst p"
                    by (rule f_inv_into_f) (use hfp_img in blast)
                  \<comment> \<open>Show \\<sigma> = 0: fst p is an endpoint of Aq (T \\<cap> non-tree arc \\<subseteq> endpoints),
                     endpoints = {hAc 0, hAc 1}, and \\<sigma> \\<le> tAc < 1 rules out \\<sigma> = 1.\<close>
                  let ?\<sigma> = "inv_into top1_unit_interval (hAc Aq) (fst p)"
                  have h\<sigma>_0: "?\<sigma> = 0"
                  proof -
                    have hAq_in_A: "Aq \<in> \<A>" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                    have "Aq \<in> ?NT" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                    hence "\<not> Aq \<subseteq> T" by (by100 blast)
                    from hT_subgraph[rule_format, OF hAq_in_A] \<open>\<not> Aq \<subseteq> T\<close>
                    have "Aq \<inter> T \<subseteq> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)" by (by100 blast)
                    hence hfp_ep: "fst p \<in> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                      using hfp_T hfp_Aq by (by100 blast)
                    have hX_strict: "is_topology_on_strict X TX"
                      using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                    have hX_haus: "is_hausdorff_on X TX"
                      using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                    have "Aq \<subseteq> X" using h\<A> hAq_in_A by (by100 blast)
                    have harc: "top1_is_arc_on Aq (subspace_topology X TX Aq)"
                      using h\<A> hAq_in_A by (by100 blast)
                    from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>Aq \<subseteq> X\<close> harc hhAc[OF \<open>Aq \<in> S\<close>]]
                    have hep: "top1_arc_endpoints_on Aq (subspace_topology X TX Aq) = {hAc Aq 0, hAc Aq 1}" .
                    from hfp_ep hep have "fst p = hAc Aq 0 \<or> fst p = hAc Aq 1" by (by100 blast)
                    have hinj: "inj_on (hAc Aq) top1_unit_interval"
                      using hbij_Aq_loc unfolding bij_betw_def by (by100 blast)
                    have h0_I: "(0::real) \<in> top1_unit_interval"
                      unfolding top1_unit_interval_def by (by100 simp)
                    have h1_I: "(1::real) \<in> top1_unit_interval"
                      unfolding top1_unit_interval_def by (by100 simp)
                    have h\<sigma>_I: "?\<sigma> \<in> top1_unit_interval"
                      using inv_into_into[OF hfp_img] by (by100 blast)
                    have "fst p \<noteq> hAc Aq 1"
                    proof
                      assume "fst p = hAc Aq 1"
                      hence "hAc Aq ?\<sigma> = hAc Aq 1" using hAc_inv by (by100 simp)
                      hence "?\<sigma> = 1" using hinj h\<sigma>_I h1_I unfolding inj_on_def by (by100 blast)
                      have "tAc Aq \<noteq> 1"
                      proof
                        assume "tAc Aq = 1"
                        have hps_img: "ps Aq \<in> hAc Aq ` top1_unit_interval"
                          using hps \<open>Aq \<in> S\<close> himg_Aq_loc by (by100 blast)
                        have "hAc Aq (tAc Aq) = ps Aq"
                          unfolding tAc_def by (rule f_inv_into_f[OF hps_img])
                        hence "hAc Aq 1 = ps Aq" using \<open>tAc Aq = 1\<close> by (by100 simp)
                        hence "ps Aq \<in> {hAc Aq 0, hAc Aq 1}" by (by100 simp)
                        hence "ps Aq \<in> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                          using hep by (by100 simp)
                        thus False using hps \<open>Aq \<in> S\<close> by (by100 blast)
                      qed
                      have hps_img2: "ps Aq \<in> hAc Aq ` top1_unit_interval"
                        using hps \<open>Aq \<in> S\<close> himg_Aq_loc by (by100 blast)
                      have "tAc Aq \<in> top1_unit_interval"
                        using inv_into_into[OF hps_img2] unfolding tAc_def by (by100 blast)
                      hence "tAc Aq \<le> 1" unfolding top1_unit_interval_def by (by100 simp)
                      hence "tAc Aq < 1" using \<open>tAc Aq \<noteq> 1\<close> by (by100 linarith)
                      thus False using hinv_le \<open>?\<sigma> = 1\<close> by (by100 linarith)
                    qed
                    hence "fst p = hAc Aq 0" using \<open>fst p = hAc Aq 0 \<or> fst p = hAc Aq 1\<close> by (by100 blast)
                    hence "hAc Aq ?\<sigma> = hAc Aq 0" using hAc_inv by (by100 simp)
                    thus "?\<sigma> = 0" using hinj h\<sigma>_I h0_I unfolding inj_on_def by (by100 blast)
                  qed
                  show ?thesis using hHDR_eq hAc_inv h\<sigma>_0 by (by100 simp)
                next
                  case False
                  \<comment> \<open>fst(p) \\<notin> target: THE = Aq, \\<sigma> < tAc, ep=0. Formula matches H\\_DR.\<close>
                  have hAq_NT: "Aq \<in> ?NT" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                  have "fst p \<notin> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                    using hNT_endpoints[rule_format, OF hAq_NT] False by (by100 blast)
                  have hTHE: "(THE A. A \<in> S \<and> fst p \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = Aq"
                  proof (rule the_equality)
                    show "Aq \<in> S \<and> fst p \<in> Aq - top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                      using \<open>Aq \<in> S\<close> \<open>fst p \<in> Aq \<inter> ?Y\<close> \<open>fst p \<notin> top1_arc_endpoints_on Aq _\<close>
                      by (by100 blast)
                  next
                    fix A' assume "A' \<in> S \<and> fst p \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
                    hence "A' \<in> \<A>" "fst p \<in> A'" using hS_sub by (by100 blast)+
                    show "A' = Aq"
                    proof (rule ccontr)
                      assume "A' \<noteq> Aq"
                      have "Aq \<in> \<A>" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                      from h\<A>_inter[rule_format, OF \<open>Aq \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> Aq\<close>[symmetric]]
                      show False using \<open>fst p \<in> Aq \<inter> ?Y\<close> \<open>fst p \<in> A'\<close>
                        \<open>fst p \<notin> top1_arc_endpoints_on Aq _\<close> by (by100 blast)
                    qed
                  qed
                  have "fst p \<in> hAc Aq ` top1_unit_interval"
                  proof -
                    have hbij_loc2: "bij_betw (hAc Aq) top1_unit_interval Aq"
                      using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                    show ?thesis using \<open>fst p \<in> Aq \<inter> ?Y\<close> hbij_loc2 unfolding bij_betw_def by (by100 blast)
                  qed
                  have "fst p \<in> ?Y" using \<open>fst p \<in> Aq \<inter> ?Y\<close> by (by100 blast)
                  have h\<sigma>_ne: "inv_into top1_unit_interval (hAc Aq) (fst p) \<noteq> tAc Aq"
                  proof
                    assume "inv_into top1_unit_interval (hAc Aq) (fst p) = tAc Aq"
                    have "hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p)) = fst p"
                      by (rule f_inv_into_f[OF \<open>fst p \<in> hAc Aq ` top1_unit_interval\<close>])
                    have "ps Aq \<in> hAc Aq ` top1_unit_interval"
                    proof -
                      have himg_loc3: "hAc Aq ` top1_unit_interval = Aq"
                        using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def bij_betw_def
                        by (by100 blast)
                      show ?thesis using hps \<open>Aq \<in> S\<close> himg_loc3 by (by100 blast)
                    qed
                    have "hAc Aq (tAc Aq) = ps Aq"
                      unfolding tAc_def by (rule f_inv_into_f[OF \<open>ps Aq \<in> hAc Aq ` _\<close>])
                    hence "fst p = ps Aq"
                      using \<open>hAc Aq _ = fst p\<close> \<open>inv_into _ _ (fst p) = tAc Aq\<close> by (by100 simp)
                    thus False using \<open>fst p \<in> ?Y\<close> \<open>Aq \<in> S\<close> by (by100 blast)
                  qed
                  hence "inv_into top1_unit_interval (hAc Aq) (fst p) < tAc Aq"
                    using hinv_le by (by100 linarith)
                  hence "(if inv_into top1_unit_interval (hAc Aq) (fst p) < tAc Aq then (0::real) else 1) = 0"
                    by (by100 simp)
                  obtain x t where hxt2: "p = (x, t)" by (cases p)
                  have "x \<notin> ?target" using False hxt2 by (by100 simp)
                  show ?thesis unfolding H_DR_def Let_def hxt2
                    using \<open>x \<notin> ?target\<close> hTHE \<open>(if _ then (0::real) else 1) = 0\<close>
                    hxt2 by (by100 simp)
                qed
              qed
              have hH_R_eq: "\<forall>p\<in>QA_R. H_DR p = hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                   snd p * (1 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
              proof (intro ballI)
                fix p assume "p \<in> QA_R"
                hence "p \<in> QA Aq" using hQA_eq by (by100 blast)
                hence "fst p \<in> Aq \<inter> ?Y" unfolding QA_def by (by100 auto)
                have hinv_ge: "inv_into top1_unit_interval (hAc Aq) (fst p) \<ge> tAc Aq"
                  using \<open>p \<in> QA_R\<close> unfolding QA_R_def by (by100 blast)
                show "H_DR p = hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                     snd p * (1 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                proof (cases "fst p \<in> ?target")
                  case True
                  have hHDR_eq: "H_DR p = fst p"
                  proof -
                    obtain x t where hxt: "p = (x, t)" by (cases p)
                    have "x \<in> ?target" using True hxt by (by100 simp)
                    thus ?thesis unfolding H_DR_def hxt by (by100 simp)
                  qed
                  have hfp_Aq: "fst p \<in> Aq" using \<open>fst p \<in> Aq \<inter> ?Y\<close> by (by100 blast)
                  have hfp_T: "fst p \<in> T"
                  proof -
                    from True have "fst p \<in> T \<or> fst p \<in> \<Union>(?NT - S)" by (by100 blast)
                    thus ?thesis
                    proof
                      assume "fst p \<in> T" thus ?thesis .
                    next
                      assume "fst p \<in> \<Union>(?NT - S)"
                      then obtain A' where "A' \<in> ?NT - S" "fst p \<in> A'" by (by100 blast)
                      have "A' \<in> \<A>" using \<open>A' \<in> ?NT - S\<close> by (by100 blast)
                      have "A' \<noteq> Aq" using \<open>A' \<in> ?NT - S\<close> \<open>Aq \<in> S\<close> by (by100 blast)
                      have "Aq \<in> \<A>" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                      from h\<A>_inter[rule_format, OF \<open>Aq \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> Aq\<close>[symmetric]]
                      have "fst p \<in> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                        using \<open>fst p \<in> Aq \<inter> ?Y\<close> \<open>fst p \<in> A'\<close> by (by100 blast)
                      have "Aq \<in> ?NT" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                      thus ?thesis using hNT_endpoints \<open>Aq \<in> ?NT\<close>
                        \<open>fst p \<in> top1_arc_endpoints_on Aq _\<close> by (by100 blast)
                    qed
                  qed
                  have hbij_Aq_loc: "bij_betw (hAc Aq) top1_unit_interval Aq"
                    using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                  have himg_Aq_loc: "hAc Aq ` top1_unit_interval = Aq"
                    using hbij_Aq_loc unfolding bij_betw_def by (by100 blast)
                  have hfp_img: "fst p \<in> hAc Aq ` top1_unit_interval"
                    using hfp_Aq himg_Aq_loc by (by100 simp)
                  have hAc_inv: "hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p)) = fst p"
                    by (rule f_inv_into_f) (use hfp_img in blast)
                  let ?\<sigma> = "inv_into top1_unit_interval (hAc Aq) (fst p)"
                  have h\<sigma>_1: "?\<sigma> = 1"
                  proof -
                    have hAq_in_A: "Aq \<in> \<A>" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                    have "Aq \<in> ?NT" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                    hence "\<not> Aq \<subseteq> T" by (by100 blast)
                    from hT_subgraph[rule_format, OF hAq_in_A] \<open>\<not> Aq \<subseteq> T\<close>
                    have "Aq \<inter> T \<subseteq> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)" by (by100 blast)
                    hence hfp_ep: "fst p \<in> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                      using hfp_T hfp_Aq by (by100 blast)
                    have hX_strict: "is_topology_on_strict X TX"
                      using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                    have hX_haus: "is_hausdorff_on X TX"
                      using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                    have "Aq \<subseteq> X" using h\<A> hAq_in_A by (by100 blast)
                    have harc: "top1_is_arc_on Aq (subspace_topology X TX Aq)"
                      using h\<A> hAq_in_A by (by100 blast)
                    from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>Aq \<subseteq> X\<close> harc hhAc[OF \<open>Aq \<in> S\<close>]]
                    have hep: "top1_arc_endpoints_on Aq (subspace_topology X TX Aq) = {hAc Aq 0, hAc Aq 1}" .
                    from hfp_ep hep have "fst p = hAc Aq 0 \<or> fst p = hAc Aq 1" by (by100 blast)
                    have hinj: "inj_on (hAc Aq) top1_unit_interval"
                      using hbij_Aq_loc unfolding bij_betw_def by (by100 blast)
                    have h0_I: "(0::real) \<in> top1_unit_interval"
                      unfolding top1_unit_interval_def by (by100 simp)
                    have h1_I: "(1::real) \<in> top1_unit_interval"
                      unfolding top1_unit_interval_def by (by100 simp)
                    have h\<sigma>_I: "?\<sigma> \<in> top1_unit_interval"
                      using inv_into_into[OF hfp_img] by (by100 blast)
                    have "fst p \<noteq> hAc Aq 0"
                    proof
                      assume "fst p = hAc Aq 0"
                      hence "hAc Aq ?\<sigma> = hAc Aq 0" using hAc_inv by (by100 simp)
                      hence "?\<sigma> = 0" using hinj h\<sigma>_I h0_I unfolding inj_on_def by (by100 blast)
                      have "tAc Aq \<noteq> 0"
                      proof
                        assume "tAc Aq = 0"
                        have hps_img: "ps Aq \<in> hAc Aq ` top1_unit_interval"
                          using hps \<open>Aq \<in> S\<close> himg_Aq_loc by (by100 blast)
                        have "hAc Aq (tAc Aq) = ps Aq"
                          unfolding tAc_def by (rule f_inv_into_f[OF hps_img])
                        hence "hAc Aq 0 = ps Aq" using \<open>tAc Aq = 0\<close> by (by100 simp)
                        hence "ps Aq \<in> {hAc Aq 0, hAc Aq 1}" by (by100 simp)
                        hence "ps Aq \<in> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                          using hep by (by100 simp)
                        thus False using hps \<open>Aq \<in> S\<close> by (by100 blast)
                      qed
                      have "tAc Aq \<in> top1_unit_interval"
                      proof -
                        have hps_img: "ps Aq \<in> hAc Aq ` top1_unit_interval"
                          using hps \<open>Aq \<in> S\<close> himg_Aq_loc by (by100 blast)
                        show ?thesis using inv_into_into[OF hps_img] unfolding tAc_def by (by100 blast)
                      qed
                      hence "tAc Aq \<ge> 0" unfolding top1_unit_interval_def by (by100 simp)
                      hence "tAc Aq > 0" using \<open>tAc Aq \<noteq> 0\<close> by (by100 linarith)
                      thus False using hinv_ge \<open>?\<sigma> = 0\<close> by (by100 linarith)
                    qed
                    hence "fst p = hAc Aq 1" using \<open>fst p = hAc Aq 0 \<or> fst p = hAc Aq 1\<close> by (by100 blast)
                    hence "hAc Aq ?\<sigma> = hAc Aq 1" using hAc_inv by (by100 simp)
                    thus "?\<sigma> = 1" using hinj h\<sigma>_I h1_I unfolding inj_on_def by (by100 blast)
                  qed
                  show ?thesis using hHDR_eq hAc_inv h\<sigma>_1 by (by100 simp)
                next
                  case False
                  have hAq_NT: "Aq \<in> ?NT" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                  have "fst p \<notin> top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                    using hNT_endpoints[rule_format, OF hAq_NT] False by (by100 blast)
                  have hTHE: "(THE A. A \<in> S \<and> fst p \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = Aq"
                  proof (rule the_equality)
                    show "Aq \<in> S \<and> fst p \<in> Aq - top1_arc_endpoints_on Aq (subspace_topology X TX Aq)"
                      using \<open>Aq \<in> S\<close> \<open>fst p \<in> Aq \<inter> ?Y\<close> \<open>fst p \<notin> top1_arc_endpoints_on Aq _\<close>
                      by (by100 blast)
                  next
                    fix A' assume "A' \<in> S \<and> fst p \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
                    hence "A' \<in> \<A>" "fst p \<in> A'" using hS_sub by (by100 blast)+
                    show "A' = Aq"
                    proof (rule ccontr)
                      assume "A' \<noteq> Aq"
                      have "Aq \<in> \<A>" using hS_sub \<open>Aq \<in> S\<close> by (by100 blast)
                      from h\<A>_inter[rule_format, OF \<open>Aq \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> Aq\<close>[symmetric]]
                      show False using \<open>fst p \<in> Aq \<inter> ?Y\<close> \<open>fst p \<in> A'\<close>
                        \<open>fst p \<notin> top1_arc_endpoints_on Aq _\<close> by (by100 blast)
                    qed
                  qed
                  have "fst p \<in> hAc Aq ` top1_unit_interval"
                  proof -
                    have hbij_loc2: "bij_betw (hAc Aq) top1_unit_interval Aq"
                      using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                    show ?thesis using \<open>fst p \<in> Aq \<inter> ?Y\<close> hbij_loc2 unfolding bij_betw_def by (by100 blast)
                  qed
                  have "fst p \<in> ?Y" using \<open>fst p \<in> Aq \<inter> ?Y\<close> by (by100 blast)
                  have h\<sigma>_ne: "inv_into top1_unit_interval (hAc Aq) (fst p) \<noteq> tAc Aq"
                  proof
                    assume "inv_into top1_unit_interval (hAc Aq) (fst p) = tAc Aq"
                    have "hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p)) = fst p"
                      by (rule f_inv_into_f[OF \<open>fst p \<in> hAc Aq ` top1_unit_interval\<close>])
                    have "ps Aq \<in> hAc Aq ` top1_unit_interval"
                    proof -
                      have himg_loc3: "hAc Aq ` top1_unit_interval = Aq"
                        using hhAc[OF \<open>Aq \<in> S\<close>] unfolding top1_homeomorphism_on_def bij_betw_def
                        by (by100 blast)
                      show ?thesis using hps \<open>Aq \<in> S\<close> himg_loc3 by (by100 blast)
                    qed
                    have "hAc Aq (tAc Aq) = ps Aq"
                      unfolding tAc_def by (rule f_inv_into_f[OF \<open>ps Aq \<in> hAc Aq ` _\<close>])
                    hence "fst p = ps Aq"
                      using \<open>hAc Aq _ = fst p\<close> \<open>inv_into _ _ (fst p) = tAc Aq\<close> by (by100 simp)
                    thus False using \<open>fst p \<in> ?Y\<close> \<open>Aq \<in> S\<close> by (by100 blast)
                  qed
                  hence "inv_into top1_unit_interval (hAc Aq) (fst p) > tAc Aq"
                    using hinv_ge by (by100 linarith)
                  hence "(if inv_into top1_unit_interval (hAc Aq) (fst p) < tAc Aq then (0::real) else 1) = 1"
                    by (by100 simp)
                  obtain x t where hxt2: "p = (x, t)" by (cases p)
                  have "x \<notin> ?target" using False hxt2 by (by100 simp)
                  show ?thesis unfolding H_DR_def Let_def hxt2
                    using \<open>x \<notin> ?target\<close> hTHE \<open>(if _ then (0::real) else 1) = 1\<close>
                    hxt2 by (by100 simp)
                qed
              qed
              \<comment> \<open>hstep\\_L/R restricted to QA\\_L/R in QA's subspace.\<close>
              \<comment> \<open>H\\_DR continuous on QA\\_L (from hstep\\_L + formula equality + codomain restrict).\<close>
              have hstep_L_QA: "top1_continuous_map_on QA_L
                  (subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_L) ?Y ?TY H_DR"
              proof -
                have hQA_L_sub: "QA_L \<subseteq> QA Aq" unfolding QA_L_def by (by100 blast)
                have htop_L: "subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_L
                    = subspace_topology ?YI ?YItop QA_L"
                  by (rule subspace_topology_trans[OF hQA_L_sub])
                have "\<forall>p\<in>QA_L. H_DR p \<in> ?Y" using hH_img_QA hQA_eq by (by100 blast)
                \<comment> \<open>hstep\\_L gives the formula continuous QA\\_L \\<rightarrow> X. Restrict to Y.\<close>
                define fL where "fL \<equiv> \<lambda>p. hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                     snd p * (0 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                have hfL_cont: "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L)
                    X TX fL" using hstep_L unfolding fL_def .
                have hfL_img_Y: "\<forall>p\<in>QA_L. fL p \<in> ?Y"
                  using hH_L_eq \<open>\<forall>p\<in>QA_L. H_DR p \<in> ?Y\<close> unfolding fL_def by (by100 auto)
                from continuous_map_restrict_codomain[OF hfL_cont hfL_img_Y hY_sub]
                have hfL_cont_Y: "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L)
                    ?Y ?TY fL" .
                have hH_fL: "\<forall>p\<in>QA_L. H_DR p = fL p" using hH_L_eq unfolding fL_def by (by100 auto)
                have "\<forall>V\<in>?TY. {p \<in> QA_L. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop QA_L"
                proof (intro ballI)
                  fix V assume "V \<in> ?TY"
                  have "{p \<in> QA_L. H_DR p \<in> V} = {p \<in> QA_L. fL p \<in> V}" using hH_fL by (by100 auto)
                  also have "... \<in> subspace_topology ?YI ?YItop QA_L"
                    using hfL_cont_Y \<open>V \<in> ?TY\<close> unfolding top1_continuous_map_on_def by (by100 blast)
                  finally show "{p \<in> QA_L. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop QA_L" .
                qed
                have hQA_L_sub2: "QA_L \<subseteq> ?YI" using hQA_sub hQA_eq by (by100 blast)
                have "is_topology_on QA_L (subspace_topology ?YI ?YItop QA_L)"
                  by (rule subspace_topology_is_topology_on[OF hYI_top hQA_L_sub2])
                have "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L) ?Y ?TY H_DR"
                  unfolding top1_continuous_map_on_def
                  using \<open>is_topology_on QA_L _\<close> hTY_top \<open>\<forall>p\<in>QA_L. H_DR p \<in> ?Y\<close>
                  \<open>\<forall>V\<in>?TY. {p \<in> QA_L. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop QA_L\<close>
                  by (by100 blast)
                show ?thesis
                proof -
                  have "top1_continuous_map_on QA_L (subspace_topology ?YI ?YItop QA_L) ?Y ?TY H_DR"
                    using \<open>top1_continuous_map_on QA_L _ ?Y ?TY H_DR\<close> .
                  thus ?thesis unfolding htop_L .
                qed
              qed
              have hstep_R_QA: "top1_continuous_map_on QA_R
                  (subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_R) ?Y ?TY H_DR"
              proof -
                have hQA_R_sub: "QA_R \<subseteq> QA Aq" unfolding QA_R_def by (by100 blast)
                have htop_R: "subspace_topology (QA Aq) (subspace_topology ?YI ?YItop (QA Aq)) QA_R
                    = subspace_topology ?YI ?YItop QA_R"
                  by (rule subspace_topology_trans[OF hQA_R_sub])
                have "\<forall>p\<in>QA_R. H_DR p \<in> ?Y" using hH_img_QA hQA_eq by (by100 blast)
                define fR where "fR \<equiv> \<lambda>p. hAc Aq (inv_into top1_unit_interval (hAc Aq) (fst p) +
                     snd p * (1 - inv_into top1_unit_interval (hAc Aq) (fst p)))"
                have hfR_cont: "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R)
                    X TX fR" using hstep_R unfolding fR_def .
                have hfR_img_Y: "\<forall>p\<in>QA_R. fR p \<in> ?Y"
                  using hH_R_eq \<open>\<forall>p\<in>QA_R. H_DR p \<in> ?Y\<close> unfolding fR_def by (by100 auto)
                from continuous_map_restrict_codomain[OF hfR_cont hfR_img_Y hY_sub]
                have hfR_cont_Y: "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R)
                    ?Y ?TY fR" .
                have hH_fR: "\<forall>p\<in>QA_R. H_DR p = fR p" using hH_R_eq unfolding fR_def by (by100 auto)
                have "\<forall>V\<in>?TY. {p \<in> QA_R. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop QA_R"
                proof (intro ballI)
                  fix V assume "V \<in> ?TY"
                  have "{p \<in> QA_R. H_DR p \<in> V} = {p \<in> QA_R. fR p \<in> V}" using hH_fR by (by100 auto)
                  also have "... \<in> subspace_topology ?YI ?YItop QA_R"
                    using hfR_cont_Y \<open>V \<in> ?TY\<close> unfolding top1_continuous_map_on_def by (by100 blast)
                  finally show "{p \<in> QA_R. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop QA_R" .
                qed
                have hQA_R_sub2: "QA_R \<subseteq> ?YI" using hQA_sub hQA_eq by (by100 blast)
                have "is_topology_on QA_R (subspace_topology ?YI ?YItop QA_R)"
                  by (rule subspace_topology_is_topology_on[OF hYI_top hQA_R_sub2])
                have "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R) ?Y ?TY H_DR"
                  unfolding top1_continuous_map_on_def
                  using \<open>is_topology_on QA_R _\<close> hTY_top \<open>\<forall>p\<in>QA_R. H_DR p \<in> ?Y\<close>
                  \<open>\<forall>V\<in>?TY. {p \<in> QA_R. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop QA_R\<close>
                  by (by100 blast)
                show ?thesis
                proof -
                  have "top1_continuous_map_on QA_R (subspace_topology ?YI ?YItop QA_R) ?Y ?TY H_DR"
                    using \<open>top1_continuous_map_on QA_R _ ?Y ?TY H_DR\<close> .
                  thus ?thesis unfolding htop_R .
                qed
              qed
              \<comment> \<open>Pasting QA\\_L and QA\\_R.\<close>
              show ?thesis
                by (rule pasting_lemma_two_closed[OF hQA_top hTY_top
                    hQA_L_closed hQA_R_closed hQA_eq[symmetric] hH_img_QA
                    hstep_L_QA hstep_R_QA])
            qed
          qed
          \<comment> \<open>Finite pasting: D\\_B = \\<Union>{QA A | A \\<in> S}, each closed, H cont on each.\<close>
          have "\<forall>V\<in>?TY. {p \<in> D_B. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop D_B"
          proof (intro ballI)
            fix V assume "V \<in> ?TY"
            \<comment> \<open>Complement: D\\_B - preimage = \\<Union>{QA A - preimage | A \\<in> S}.\<close>
            have "D_B - {p \<in> D_B. H_DR p \<in> V} = (\<Union>A\<in>S. QA A - {p \<in> QA A. H_DR p \<in> V})"
              using hDB_eq by (by100 blast)
            \<comment> \<open>Each QA A - preimage is closed in Y\\<times>I.\<close>
            have hcompl_closed: "\<forall>A\<in>S. closedin_on ?YI ?YItop (QA A - {p \<in> QA A. H_DR p \<in> V})"
            proof (intro ballI)
              fix A assume "A \<in> S"
              have "{p \<in> QA A. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop (QA A)"
                using hH_QA \<open>A \<in> S\<close> \<open>V \<in> ?TY\<close> unfolding top1_continuous_map_on_def by (by100 blast)
              have hQA_sub: "QA A \<subseteq> ?YI" using hQA_closed \<open>A \<in> S\<close>
                unfolding closedin_on_def by (by100 blast)
              have hQA_top: "is_topology_on (QA A) (subspace_topology ?YI ?YItop (QA A))"
                by (rule subspace_topology_is_topology_on[OF hYI_top hQA_sub])
              have "QA A - {p \<in> QA A. H_DR p \<in> V} \<subseteq> QA A" by (by100 blast)
              moreover have "QA A - (QA A - {p \<in> QA A. H_DR p \<in> V}) = {p \<in> QA A. H_DR p \<in> V}"
                by (by100 blast)
              hence "QA A - (QA A - {p \<in> QA A. H_DR p \<in> V}) \<in> subspace_topology ?YI ?YItop (QA A)"
                using \<open>{p \<in> QA A. H_DR p \<in> V} \<in> _\<close> by (by100 simp)
              ultimately have "closedin_on (QA A) (subspace_topology ?YI ?YItop (QA A))
                  (QA A - {p \<in> QA A. H_DR p \<in> V})"
                unfolding closedin_on_def by (by100 blast)
              from Theorem_17_3[OF hYI_top _ this]
              show "closedin_on ?YI ?YItop (QA A - {p \<in> QA A. H_DR p \<in> V})"
                using hQA_closed \<open>A \<in> S\<close> by (by100 blast)
            qed
            have "closedin_on ?YI ?YItop (\<Union>A\<in>S. QA A - {p \<in> QA A. H_DR p \<in> V})"
              by (rule closedin_on_finite_indexed_Union[OF hYI_top hS_fin])
                 (use hcompl_closed in \<open>by100 blast\<close>)
            hence "closedin_on ?YI ?YItop (D_B - {p \<in> D_B. H_DR p \<in> V})"
              using \<open>D_B - {p \<in> D_B. H_DR p \<in> V} = _\<close> by (by100 simp)
            \<comment> \<open>Closed in D\\_B (from closed in Y\\<times>I via Theorem\\_17\\_2).\<close>
            from Theorem_17_2[OF hYI_top hDB_sub, of "D_B - {p \<in> D_B. H_DR p \<in> V}"]
            have "closedin_on D_B (subspace_topology ?YI ?YItop D_B)
                (D_B - {p \<in> D_B. H_DR p \<in> V})"
              using \<open>closedin_on ?YI ?YItop (D_B - {p \<in> D_B. H_DR p \<in> V})\<close> by (by100 blast)
            hence "D_B - (D_B - {p \<in> D_B. H_DR p \<in> V}) \<in> subspace_topology ?YI ?YItop D_B"
              unfolding closedin_on_def by (by100 blast)
            moreover have "D_B - (D_B - {p \<in> D_B. H_DR p \<in> V}) = {p \<in> D_B. H_DR p \<in> V}"
              by (by100 blast)
            ultimately show "{p \<in> D_B. H_DR p \<in> V} \<in> subspace_topology ?YI ?YItop D_B"
              by (by100 simp)
          qed
          show ?thesis unfolding top1_continuous_map_on_def
            using hDB_top hTY_top hH_img_DB \<open>\<forall>V\<in>?TY. _\<close> by (by100 blast)
        qed
        \<comment> \<open>Pasting D\\_T and D\\_B.\<close>
        show ?thesis
          by (rule pasting_lemma_two_closed[OF hYI_top hTY_top hDT_closed hDB_closed
              hcover hH_img hH_DT hH_DB])
      qed
      ultimately show "top1_continuous_map_on (?Y \<times> I_set) (product_topology_on ?TY I_top) ?Y ?TY H_DR
          \<and> (\<forall>x\<in>?Y. H_DR (x, 0) = x) \<and> (\<forall>x\<in>?Y. H_DR (x, 1) \<in> ?target)
          \<and> (\<forall>a\<in>?target. \<forall>t\<in>I_set. H_DR (a, t) = a)" by (by100 blast)
    qed
  qed
qed

\<comment> \<open>Helper: graph with no non-tree arcs (Y=T) has trivial hence free \\<pi>\\_1.\<close>
lemma graph_tree_free_pi1:
  assumes "top1_is_graph_on Y TY"
      and "y0 \<in> Y"
      and "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and "\<Union>\<A> = Y"
      and "top1_is_tree_on T (subspace_topology Y TY T)"
      and "T \<subseteq> Y"
      and "y0 \<in> T"
      and "{A\<in>\<A>. \<not> A \<subseteq> T} = {}"
  shows "\<exists>(\<iota>::nat \<Rightarrow> _) (S::nat set). top1_is_free_group_full_on
      (top1_fundamental_group_carrier Y TY y0)
      (top1_fundamental_group_mul Y TY y0)
      (top1_fundamental_group_id Y TY y0)
      (top1_fundamental_group_invg Y TY y0)
      \<iota> S"
proof -
  have "Y = T"
  proof -
    have "\<forall>A\<in>\<A>. A \<subseteq> T" using assms(8) by (by100 blast)
    hence "\<Union>\<A> \<subseteq> T" by (by100 blast)
    hence "Y \<subseteq> T" using assms(4) by (by100 simp)
    thus ?thesis using assms(6) by (by100 blast)
  qed
  have hTY_top: "is_topology_on Y TY"
    using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by5000 blast)
  have hTY_strict: "is_topology_on_strict Y TY"
    using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
  have "top1_simply_connected_on Y TY"
  proof -
    from tree_simply_connected[OF assms(5)]
    have "top1_simply_connected_on T (subspace_topology Y TY T)" .
    have "\<forall>U\<in>TY. U \<subseteq> Y"
      using hTY_strict unfolding is_topology_on_strict_def by (by100 blast)
    from subspace_topology_self[OF this]
    have "subspace_topology Y TY Y = TY" .
    hence "subspace_topology Y TY T = TY" using \<open>Y = T\<close> by (by100 simp)
    thus ?thesis using \<open>top1_simply_connected_on T _\<close> \<open>Y = T\<close> by (by100 simp)
  qed
  have hpi1_triv: "top1_fundamental_group_carrier Y TY y0 = {top1_fundamental_group_id Y TY y0}"
    by (rule simply_connected_trivial_carrier[OF \<open>top1_simply_connected_on Y TY\<close> assms(2)])
  let ?G = "top1_fundamental_group_carrier Y TY y0"
  let ?mul = "top1_fundamental_group_mul Y TY y0"
  let ?e = "top1_fundamental_group_id Y TY y0"
  let ?invg = "top1_fundamental_group_invg Y TY y0"
  have hgrp: "top1_is_group_on ?G ?mul ?e ?invg"
    by (rule top1_fundamental_group_is_group[OF hTY_top assms(2)])
  show ?thesis
    unfolding top1_is_free_group_full_on_def
  proof (intro exI[of _ "\<lambda>_::nat. ?e"] exI[of _ "{}::nat set"] conjI)
    show "top1_is_group_on ?G ?mul ?e ?invg" by (rule hgrp)
    show "\<forall>s\<in>({}::nat set). ((\<lambda>_::nat. ?e) s) \<in> ?G" by (by100 blast)
    show "inj_on (\<lambda>_::nat. ?e) ({} :: nat set)" by (by100 simp)
    show "?G = top1_subgroup_generated_on ?G ?mul ?e ?invg ((\<lambda>_::nat. ?e) ` ({} :: nat set))"
    proof -
      have "(\<lambda>_::nat. ?e) ` ({} :: nat set) = {}" by (by100 simp)
      hence "top1_subgroup_generated_on ?G ?mul ?e ?invg ((\<lambda>_::nat. ?e) ` ({} :: nat set)) =
          top1_subgroup_generated_on ?G ?mul ?e ?invg {}" by (by100 simp)
      also have "... = \<Inter>{H. {} \<subseteq> H \<and> H \<subseteq> ?G \<and> top1_is_group_on H ?mul ?e ?invg}"
        unfolding top1_subgroup_generated_on_def by (by100 blast)
      also have "... = ?G"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> \<Inter>{H. {} \<subseteq> H \<and> H \<subseteq> ?G \<and> top1_is_group_on H ?mul ?e ?invg}"
        have "?G \<in> {H. {} \<subseteq> H \<and> H \<subseteq> ?G \<and> top1_is_group_on H ?mul ?e ?invg}"
          using hgrp by (by100 blast)
        thus "x \<in> ?G" using \<open>x \<in> _\<close> by (by100 blast)
      next
        fix x assume "x \<in> ?G"
        show "x \<in> \<Inter>{H. {} \<subseteq> H \<and> H \<subseteq> ?G \<and> top1_is_group_on H ?mul ?e ?invg}"
        proof (rule InterI)
          fix H assume "H \<in> {H. {} \<subseteq> H \<and> H \<subseteq> ?G \<and> top1_is_group_on H ?mul ?e ?invg}"
          hence "H \<subseteq> ?G" by (by100 blast)
          have "?G = {?e}" by (rule hpi1_triv)
          hence "x = ?e" using \<open>x \<in> ?G\<close> by (by100 blast)
          have "?e \<in> H"
            using \<open>H \<in> _\<close> unfolding top1_is_group_on_def by (by100 blast)
          thus "x \<in> H" using \<open>x = ?e\<close> by (by100 simp)
        qed
      qed
      finally show ?thesis by (by100 simp)
    qed
    show "\<forall>ws :: (nat \<times> bool) list.
        ws \<noteq> [] \<longrightarrow>
        top1_is_reduced_word (map (\<lambda>(s, b). ((\<lambda>_::nat. ?e) s, b)) ws) \<longrightarrow>
        (\<forall>i<length ws. fst (ws ! i) \<in> ({} :: nat set)) \<longrightarrow>
        top1_group_word_product ?mul ?e ?invg (map (\<lambda>(s, b). ((\<lambda>_::nat. ?e) s, b)) ws) \<noteq> ?e"
    proof (intro allI impI)
      fix ws :: "(nat \<times> bool) list"
      assume "ws \<noteq> []" and "\<forall>i<length ws. fst (ws ! i) \<in> ({} :: nat set)"
      have "0 < length ws" using \<open>ws \<noteq> []\<close> by (by100 simp)
      from \<open>\<forall>i<length ws. fst (ws ! i) \<in> {}\<close>[rule_format, OF \<open>0 < length ws\<close>]
      have False by (by100 simp)
      thus "top1_group_word_product ?mul ?e ?invg
          (map (\<lambda>(s, b). ((\<lambda>_::nat. ?e) s, b)) ws) \<noteq> ?e" by (by100 blast)
    qed
  qed
qed

\<comment> \<open>Auxiliary: finite case of graph\\_pi1\\_free\\_weak by induction on card(NT).\<close>

\<comment> \<open>Card=1 case: graph with exactly 1 non-tree arc has \\<pi>\\_1 \\<cong> \\<Z>.\<close>
lemma graph_one_edge_pi1_iso_Z:
  fixes Y :: "'a set" and TY :: "'a set set" and y0 :: 'a and A1 :: "'a set"
  assumes hgraph: "top1_is_graph_on Y TY"
      and hconn: "top1_connected_on Y TY"
      and hy0: "y0 \<in> Y"
      and h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
      and h\<A>_cover: "\<Union>\<A> = Y"
      and h\<A>_inter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and h\<A>_coh: "\<forall>C. C \<subseteq> Y \<longrightarrow>
           (closedin_on Y TY C \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
      and hT_tree: "top1_is_tree_on T (subspace_topology Y TY T)"
      and hT_sub: "T \<subseteq> Y"
      and hT_subgraph: "\<forall>A\<in>\<A>. A \<subseteq> T \<or>
           A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
      and hT_x0: "y0 \<in> T"
      and hNT_endpoints: "\<forall>A\<in>{A\<in>\<A>. \<not> A \<subseteq> T}. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology Y TY A). e \<in> T"
      and hA1: "A1 \<in> {A\<in>\<A>. \<not> A \<subseteq> T}"
      and hNT_singleton: "{A\<in>\<A>. \<not> A \<subseteq> T} = {A1}"
  shows "top1_groups_isomorphic_on
      (top1_fundamental_group_carrier Y TY y0) (top1_fundamental_group_mul Y TY y0)
      top1_Z_group top1_Z_mul"
proof -
  let ?NT = "{A\<in>\<A>. \<not> A \<subseteq> T}"
  have "Y = T \<union> A1"
  proof -
    have "\<forall>A\<in>\<A>. A \<subseteq> T \<or> A = A1"
    proof (intro ballI)
      fix A assume "A \<in> \<A>"
      show "A \<subseteq> T \<or> A = A1"
      proof (cases "A \<subseteq> T")
        case True thus ?thesis by (by100 blast)
      next
        case False
        hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
        thus ?thesis using hNT_singleton by (by100 blast)
      qed
    qed
    hence "\<Union>\<A> \<subseteq> T \<union> A1" by (by100 blast)
    hence "Y \<subseteq> T \<union> A1" using h\<A>_cover by (by100 simp)
    moreover have "T \<union> A1 \<subseteq> Y" using hT_sub h\<A> hA1 by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
    \<comment> \<open>Book Step 2: Setup for Lemma 84.6.\<close>
    have hA1_arc: "top1_is_arc_on A1 (subspace_topology Y TY A1)"
      using h\<A> hA1 by (by100 blast)
    have hA1_sub: "A1 \<subseteq> Y" using h\<A> hA1 by (by100 blast)
    obtain hA where hhA: "top1_homeomorphism_on top1_unit_interval
        top1_unit_interval_topology A1 (subspace_topology Y TY A1) hA"
      using hA1_arc unfolding top1_is_arc_on_def by (by100 blast)
    \<comment> \<open>Endpoints and midpoint.\<close>
    let ?ep_l = "hA 0" and ?ep_r = "hA 1" and ?mid = "hA (1/2)"
    have hY_strict: "is_topology_on_strict Y TY"
      using hgraph unfolding top1_is_graph_on_def by (by100 blast)
    have hY_haus: "is_hausdorff_on Y TY"
      using hgraph unfolding top1_is_graph_on_def by (by100 blast)
    have hTY_top: "is_topology_on Y TY"
      using hY_strict unfolding is_topology_on_strict_def by (by100 blast)
    have hep_l_T: "?ep_l \<in> T" and hep_r_T: "?ep_r \<in> T"
    proof -
      from arc_endpoints_are_boundary[OF hY_strict hY_haus hA1_sub hA1_arc hhA]
      have "top1_arc_endpoints_on A1 (subspace_topology Y TY A1) = {?ep_l, ?ep_r}" .
      from hNT_endpoints[rule_format, OF hA1]
      show "?ep_l \<in> T" and "?ep_r \<in> T"
        using \<open>top1_arc_endpoints_on A1 _ = {?ep_l, ?ep_r}\<close> by (by100 simp)+
    qed
    \<comment> \<open>Endpoint membership in A1.\<close>
    have hbij_hA: "bij_betw hA top1_unit_interval A1"
      using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
    have h0_I: "(0::real) \<in> top1_unit_interval"
      unfolding top1_unit_interval_def by (by100 simp)
    have h1_I: "(1::real) \<in> top1_unit_interval"
      unfolding top1_unit_interval_def by (by100 simp)
    have hep_l_A1: "?ep_l \<in> A1" using hbij_hA h0_I
      unfolding bij_betw_def by (by100 blast)
    have hep_r_A1: "?ep_r \<in> A1" using hbij_hA h1_I
      unfolding bij_betw_def by (by100 blast)
    \<comment> \<open>U = A1 - {endpoints} (open arc). V = Y - {midpoint}.\<close>
    let ?U = "A1 - {?ep_l, ?ep_r}"
    let ?V = "Y - {?mid}"
    \<comment> \<open>Key properties for Lemma 84.6:\<close>
    have hU_open: "openin_on Y TY ?U"
    proof -
      \<comment> \<open>Y - U = (Y - A1) \\<union> {ep\\_l, ep\\_r}. Show closed via coherent topology.\<close>
      have "Y - ?U = (Y - A1) \<union> {?ep_l, ?ep_r}"
        using hA1_sub hep_l_T hep_r_T hT_sub by (by100 blast)
      have "\<forall>A'\<in>\<A>. closedin_on A' (subspace_topology Y TY A') (A' \<inter> (Y - ?U))"
      proof (intro ballI)
        fix A' assume "A' \<in> \<A>"
        show "closedin_on A' (subspace_topology Y TY A') (A' \<inter> (Y - ?U))"
        proof (cases "A' = A1")
          case True
          have "A' \<inter> (Y - ?U) = A1 \<inter> (Y - (A1 - {?ep_l, ?ep_r}))"
            using True by simp
          also have "... = {?ep_l, ?ep_r}"
            using hep_l_A1 hep_r_A1 hA1_sub by (by100 blast)
          finally have "A' \<inter> (Y - ?U) = {?ep_l, ?ep_r}" .
          have "A' \<subseteq> Y" using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
          have "is_hausdorff_on A' (subspace_topology Y TY A')"
            using Theorem_17_11 hY_haus \<open>A' \<subseteq> Y\<close> by (by100 blast)
          have "finite {?ep_l, ?ep_r}" by (by100 simp)
          have "{?ep_l, ?ep_r} \<subseteq> A'"
            using True hep_l_A1 hep_r_A1 by (by100 blast)
          from Theorem_17_8[OF \<open>is_hausdorff_on A' _\<close> \<open>finite {?ep_l, ?ep_r}\<close>
              \<open>{?ep_l, ?ep_r} \<subseteq> A'\<close>]
          show ?thesis using \<open>A' \<inter> (Y - ?U) = {?ep_l, ?ep_r}\<close> by simp
        next
          case False
          \<comment> \<open>A' \\<noteq> A1. Since NT = {A1}, A' \\<subseteq> T. So A' \\<subseteq> Y - U.\<close>
          have "A' \<subseteq> T"
          proof -
            have "A' \<notin> ?NT \<or> A' = A1" using hNT_singleton by (by100 blast)
            thus ?thesis using False \<open>A' \<in> \<A>\<close> by (by100 blast)
          qed
          hence "A' \<subseteq> Y - ?U"
          proof -
            have "A' \<inter> A1 \<subseteq> {?ep_l, ?ep_r}"
            proof -
              from h\<A>_inter[rule_format, OF \<open>A' \<in> \<A>\<close> _ False]
              have "A' \<inter> A1 \<subseteq> top1_arc_endpoints_on A1 (subspace_topology Y TY A1)"
                using hA1 by (by100 blast)
              from arc_endpoints_are_boundary[OF hY_strict hY_haus hA1_sub hA1_arc hhA]
              show ?thesis using \<open>A' \<inter> A1 \<subseteq> _\<close> by (by100 simp)
            qed
            hence "A' \<subseteq> (Y - A1) \<union> {?ep_l, ?ep_r}"
              using \<open>A' \<subseteq> T\<close> hT_sub by (by100 blast)
            thus ?thesis using \<open>Y - ?U = _\<close> by simp
          qed
          hence "A' \<inter> (Y - ?U) = A'"
            using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
          have "A' \<subseteq> Y" using h\<A> \<open>A' \<in> \<A>\<close> by (by100 blast)
          have "is_topology_on A' (subspace_topology Y TY A')"
            by (rule subspace_topology_is_topology_on[OF hTY_top \<open>A' \<subseteq> Y\<close>])
          have "closedin_on A' (subspace_topology Y TY A') A'"
          proof -
            have "{} \<in> subspace_topology Y TY A'"
              using \<open>is_topology_on A' _\<close> unfolding is_topology_on_def by (by100 fast)
            hence "A' - A' \<in> subspace_topology Y TY A'" by simp
            thus ?thesis unfolding closedin_on_def by (by100 blast)
          qed
          thus ?thesis using \<open>A' \<inter> (Y - ?U) = A'\<close> by simp
        qed
      qed
      hence "closedin_on Y TY (Y - ?U)"
        using h\<A>_coh by (by100 blast)
      hence "Y - (Y - ?U) \<in> TY" unfolding closedin_on_def by (by100 blast)
      have "Y - (Y - ?U) = ?U" using hA1_sub by (by100 blast)
      hence "?U \<in> TY" using \<open>Y - (Y - ?U) \<in> TY\<close> by simp
      have "?U \<subseteq> Y" using hA1_sub by (by100 blast)
      show ?thesis unfolding openin_on_def
        using \<open>?U \<in> TY\<close> \<open>?U \<subseteq> Y\<close> by (by100 blast)
    qed
    have hV_open: "openin_on Y TY ?V"
    proof -
      have "?mid \<in> A1"
      proof -
        have "(1/2::real) \<in> top1_unit_interval"
          unfolding top1_unit_interval_def by (by100 simp)
        have "bij_betw hA top1_unit_interval A1"
          using hhA unfolding top1_homeomorphism_on_def by (by100 blast)
        thus ?thesis using \<open>(1/2::real) \<in> _\<close> unfolding bij_betw_def by (by100 blast)
      qed
      have "?mid \<in> Y" using \<open>?mid \<in> A1\<close> hA1_sub by (by100 blast)
      have "finite {?mid}" by (by100 simp)
      have "{?mid} \<subseteq> Y" using \<open>?mid \<in> Y\<close> by (by100 blast)
      from Theorem_17_8[OF hY_haus \<open>finite {?mid}\<close> \<open>{?mid} \<subseteq> Y\<close>]
      have "closedin_on Y TY {?mid}" .
      thus ?thesis unfolding openin_on_def closedin_on_def by (by100 blast)
    qed
    \<comment> \<open>mid \\<noteq> ep\\_l, mid \\<noteq> ep\\_r (injectivity of hA).\<close>
    have hinj_hA: "inj_on hA top1_unit_interval"
      using hbij_hA unfolding bij_betw_def by (by100 blast)
    have h12_I: "(1/2::real) \<in> top1_unit_interval"
      unfolding top1_unit_interval_def by (by100 simp)
    have hmid_ne_l: "?mid \<noteq> ?ep_l"
    proof
      assume "?mid = ?ep_l"
      from inj_onD[OF hinj_hA this h12_I h0_I] show False by (by100 simp)
    qed
    have hmid_ne_r: "?mid \<noteq> ?ep_r"
    proof
      assume "?mid = ?ep_r"
      from inj_onD[OF hinj_hA this h12_I h1_I] show False by (by100 simp)
    qed
    have hmid_in_U: "?mid \<in> ?U"
    proof -
      have "?mid \<in> A1" using hbij_hA h12_I unfolding bij_betw_def by (by100 blast)
      thus ?thesis using hmid_ne_l hmid_ne_r by (by100 blast)
    qed
    \<comment> \<open>mid \\<notin> T (mid is interior to A1, but T \\<inter> A1 \\<subseteq> endpoints).\<close>
    have hmid_not_T: "?mid \<notin> T"
    proof
      assume "?mid \<in> T"
      have "\<not> A1 \<subseteq> T" using hA1 by (by100 blast)
      from hT_subgraph[rule_format, OF _] \<open>\<not> A1 \<subseteq> T\<close>
      have "A1 \<inter> T \<subseteq> top1_arc_endpoints_on A1 (subspace_topology Y TY A1)"
        using hA1 by (by100 blast)
      from arc_endpoints_are_boundary[OF hY_strict hY_haus hA1_sub hA1_arc hhA]
      have "top1_arc_endpoints_on A1 (subspace_topology Y TY A1) = {?ep_l, ?ep_r}" .
      have "?mid \<in> {?ep_l, ?ep_r}"
        using \<open>?mid \<in> T\<close> \<open>A1 \<inter> T \<subseteq> _\<close> \<open>_ = {?ep_l, ?ep_r}\<close> hmid_in_U
        by (by100 blast)
      thus False using hmid_ne_l hmid_ne_r by (by100 blast)
    qed
    have hcover: "?U \<union> ?V = Y"
    proof -
      have "T \<subseteq> ?V" using hmid_not_T hT_sub by (by100 blast)
      have "A1 \<subseteq> ?U \<union> ?V"
      proof -
        have "\<forall>x \<in> A1. x \<in> ?U \<union> ?V"
        proof (intro ballI)
          fix x assume "x \<in> A1"
          show "x \<in> ?U \<union> ?V"
          proof (cases "x = ?mid")
            case True
            have "?mid \<in> ?U \<union> ?V" using hmid_in_U by (by100 blast)
            thus ?thesis using True by simp
          next
            case False
            hence "x \<in> ?V" using \<open>x \<in> A1\<close> hA1_sub by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
        qed
        thus ?thesis by (by100 blast)
      qed
      have "Y = T \<union> A1" using \<open>Y = T \<union> A1\<close> .
      thus ?thesis using \<open>T \<subseteq> ?V\<close> \<open>A1 \<subseteq> ?U \<union> ?V\<close> by (by100 blast)
    qed
    have hU_sc: "top1_simply_connected_on ?U (subspace_topology Y TY ?U)"
    proof -
      \<comment> \<open>(0,1) is SC (convex real subset).\<close>
      let ?I01_open = "{t::real. 0 < t \<and> t < 1}"
      have hI01_ne: "?I01_open \<noteq> {}"
      proof -
        have "(1/2::real) \<in> ?I01_open" by (by100 simp)
        thus ?thesis by (by100 blast)
      qed
      have hI01_convex: "\<And>x y t::real. x \<in> ?I01_open \<Longrightarrow> y \<in> ?I01_open \<Longrightarrow>
          0 \<le> t \<Longrightarrow> t \<le> 1 \<Longrightarrow> (1 - t) * x + t * y \<in> ?I01_open"
      proof -
        fix x y t :: real
        assume "x \<in> ?I01_open" "y \<in> ?I01_open" "0 \<le> t" "t \<le> 1"
        hence "0 < x" "x < 1" "0 < y" "y < 1" by (by100 simp)+
        have h1: "0 < (1-t)*x + t*y"
        proof (cases "t = 0")
          case True thus ?thesis using \<open>0 < x\<close> by simp
        next
          case False hence "t > 0" using \<open>0 \<le> t\<close> by linarith
          have "(1-t)*x \<ge> 0" using \<open>0 < x\<close> \<open>0 \<le> t\<close> \<open>t \<le> 1\<close>
            by (intro mult_nonneg_nonneg) linarith+
          have "t*y > 0" using \<open>0 < y\<close> \<open>t > 0\<close> by (by100 simp)
          show ?thesis using \<open>(1-t)*x \<ge> 0\<close> \<open>t*y > 0\<close> by linarith
        qed
        moreover have h2: "(1-t)*x + t*y < 1"
        proof (cases "t = 1")
          case True thus ?thesis using \<open>0 < y\<close> \<open>y < 1\<close> by simp
        next
          case False hence "1-t > 0" using \<open>t \<le> 1\<close> by linarith
          hence "(1-t)*x < (1-t)" using \<open>x < 1\<close> by (by100 simp)
          have "t*y \<le> t" using \<open>y < 1\<close> \<open>0 \<le> t\<close>
            by (intro mult_left_le) linarith+
          show ?thesis using \<open>(1-t)*x < 1-t\<close> \<open>t*y \<le> t\<close> by linarith
        qed
        ultimately show "(1-t)*x + t*y \<in> ?I01_open" by (by100 simp)
      qed
      have hI01_sc: "top1_simply_connected_on ?I01_open
          (subspace_topology UNIV top1_open_sets ?I01_open)"
        by (rule convex_real_subspace_simply_connected[OF hI01_ne hI01_convex])
      \<comment> \<open>hA restricted to (0,1) gives homeomorphism (0,1) \\<rightarrow> U.\<close>
      have hI01_sub: "?I01_open \<subseteq> top1_unit_interval"
        unfolding top1_unit_interval_def by (by100 auto)
      from homeomorphism_on_restrict[OF hhA hI01_sub]
      have hhA_open: "top1_homeomorphism_on ?I01_open
          (subspace_topology top1_unit_interval top1_unit_interval_topology ?I01_open)
          (hA ` ?I01_open) (subspace_topology A1 (subspace_topology Y TY A1) (hA ` ?I01_open)) hA" .
      \<comment> \<open>hA\\`(0,1) = A1 - {endpoints} = U.\<close>
      have "hA ` ?I01_open = ?U"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> hA ` ?I01_open"
        then obtain t where ht: "t \<in> ?I01_open" and hx: "x = hA t" by (by100 blast)
        have "t \<in> top1_unit_interval" using ht hI01_sub by (by100 blast)
        hence "x \<in> A1" using hx hbij_hA unfolding bij_betw_def by (by100 blast)
        have "x \<noteq> ?ep_l"
        proof
          assume "x = ?ep_l"
          hence "hA t = hA 0" using hx by simp
          from inj_onD[OF hinj_hA this \<open>t \<in> top1_unit_interval\<close> h0_I]
          have "t = 0" .
          thus False using ht by (by100 simp)
        qed
        have "x \<noteq> ?ep_r"
        proof
          assume "x = ?ep_r"
          hence "hA t = hA 1" using hx by simp
          from inj_onD[OF hinj_hA this \<open>t \<in> top1_unit_interval\<close> h1_I]
          have "t = 1" .
          thus False using ht by (by100 simp)
        qed
        show "x \<in> ?U" using \<open>x \<in> A1\<close> \<open>x \<noteq> ?ep_l\<close> \<open>x \<noteq> ?ep_r\<close> by (by100 blast)
      next
        fix x assume "x \<in> ?U"
        hence "x \<in> A1" "x \<noteq> ?ep_l" "x \<noteq> ?ep_r" by (by100 blast)+
        have "x \<in> hA ` top1_unit_interval"
          using hbij_hA \<open>x \<in> A1\<close> unfolding bij_betw_def by (by100 blast)
        then obtain t where ht: "t \<in> top1_unit_interval" and hx: "hA t = x" by (by100 blast)
        have "t \<noteq> 0"
        proof
          assume "t = 0" hence "x = ?ep_l" using hx by simp
          thus False using \<open>x \<noteq> ?ep_l\<close> by contradiction
        qed
        have "t \<noteq> 1"
        proof
          assume "t = 1" hence "x = ?ep_r" using hx by simp
          thus False using \<open>x \<noteq> ?ep_r\<close> by contradiction
        qed
        have "t \<in> ?I01_open" using ht \<open>t \<noteq> 0\<close> \<open>t \<noteq> 1\<close>
          unfolding top1_unit_interval_def by (by100 simp)
        thus "x \<in> hA ` ?I01_open" using hx by (by100 blast)
      qed
      \<comment> \<open>Topology adjustments: subspace of subspace = subspace of Y.\<close>
      have hU_top_eq: "subspace_topology A1 (subspace_topology Y TY A1) ?U =
          subspace_topology Y TY ?U"
        by (rule subspace_topology_trans) (by100 blast)
      have hI01_top_eq: "subspace_topology top1_unit_interval top1_unit_interval_topology ?I01_open =
          subspace_topology UNIV top1_open_sets ?I01_open"
      proof -
        have "subspace_topology top1_unit_interval
            (subspace_topology UNIV top1_open_sets top1_unit_interval) ?I01_open =
            subspace_topology UNIV top1_open_sets ?I01_open"
          by (rule subspace_topology_trans[OF hI01_sub])
        thus ?thesis unfolding top1_unit_interval_topology_def by simp
      qed
      \<comment> \<open>Transfer SC via homeomorphism.\<close>
      have hhA_open': "top1_homeomorphism_on ?I01_open
          (subspace_topology UNIV top1_open_sets ?I01_open)
          ?U (subspace_topology Y TY ?U) hA"
        using hhA_open \<open>hA ` ?I01_open = ?U\<close> hU_top_eq hI01_top_eq by simp
      from homeomorphism_preserves_simply_connected[OF hhA_open' hI01_sc]
      show ?thesis .
    qed
    have hV_sc: "top1_simply_connected_on ?V (subspace_topology Y TY ?V)"
    proof -
      \<comment> \<open>Apply graph\\_remove\\_interior\\_points\\_sc with NT={A1}, ps=\\<lambda>A. mid.\<close>
      define ps :: "'a set \<Rightarrow> 'a" where "ps = (\<lambda>_. hA (1/2))"
      have hV_eq_ps: "?V = Y - ps ` {A1}" unfolding ps_def by (by100 simp)
      have h\<A>_inter_sub: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
          A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
        using h\<A>_inter by (by100 blast)
      have hps_loc: "\<forall>A\<in>{A1}. ps A \<in> A \<and>
          ps A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
      proof (intro ballI conjI)
        fix A assume "A \<in> {A1}" hence "A = A1" by (by100 blast)
        show "ps A \<in> A" unfolding ps_def using \<open>A = A1\<close> hmid_in_U by (by100 blast)
        show "ps A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
        proof -
          from arc_endpoints_are_boundary[OF hY_strict hY_haus hA1_sub hA1_arc hhA]
          have "top1_arc_endpoints_on A1 (subspace_topology Y TY A1) = {?ep_l, ?ep_r}" .
          thus ?thesis unfolding ps_def using \<open>A = A1\<close> hmid_ne_l hmid_ne_r by (by100 simp)
        qed
      qed
      have "top1_simply_connected_on (Y - ps ` {A1}) (subspace_topology Y TY (Y - ps ` {A1}))"
      proof (rule graph_remove_interior_points_sc[OF hgraph h\<A> h\<A>_cover
          h\<A>_inter_sub hT_tree hT_sub hT_subgraph _ _ hps_loc _ hT_x0 h\<A>_coh])
        show "{A1} = {A \<in> \<A>. \<not> A \<subseteq> T}" using hNT_singleton by simp
        show "finite {A1}" by (by100 simp)
        show "\<forall>A\<in>\<A>. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology Y TY A). e \<in> T"
        proof (intro ballI)
          fix A e assume "A \<in> \<A>" "e \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
          show "e \<in> T"
          proof (cases "A \<subseteq> T")
            case True2: True
            have "e \<in> A" using \<open>e \<in> _\<close> unfolding top1_arc_endpoints_on_def by (by100 blast)
            thus ?thesis using True2 by (by100 blast)
          next
            case False2: False
            hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
            thus ?thesis using hNT_endpoints \<open>e \<in> _\<close> by (by100 blast)
          qed
        qed
      qed
      thus ?thesis using \<open>?V = Y - ps ` {A1}\<close> by simp
    qed
    \<comment> \<open>U \\<inter> V has 2 path components.\<close>
    have hUV_sub: "?U \<inter> ?V \<subseteq> A1 - {?ep_l, ?ep_r, ?mid}"
      using hA1_sub by (by100 blast)
    have hUV_sup: "A1 - {?ep_l, ?ep_r, ?mid} \<subseteq> ?U \<inter> ?V"
      using hA1_sub by (by100 blast)
    \<comment> \<open>This has 2 path-connected components (two open arcs of A1).\<close>
    \<comment> \<open>Define the two components: hA\\`(0,1/2) and hA\\`(1/2,1).\<close>
    define A_comp where "A_comp = hA ` {t. 0 < t \<and> t < 1/2}"
    define B_comp where "B_comp = hA ` {t. 1/2 < t \<and> t < 1}"
    have "\<exists>A_comp B_comp.
        ?U \<inter> ?V = A_comp \<union> B_comp \<and> A_comp \<inter> B_comp = {} \<and>
        openin_on Y TY A_comp \<and> openin_on Y TY B_comp \<and>
        top1_path_connected_on A_comp (subspace_topology Y TY A_comp) \<and>
        top1_path_connected_on B_comp (subspace_topology Y TY B_comp) \<and>
        (\<exists>a. a \<in> A_comp) \<and> (\<exists>b. b \<in> B_comp)"
    proof (rule exI[of _ A_comp], rule exI[of _ B_comp], intro conjI)
      \<comment> \<open>Union = U \\<inter> V.\<close>
      show "?U \<inter> ?V = A_comp \<union> B_comp"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> ?U \<inter> ?V"
        hence "x \<in> A1" "x \<noteq> ?ep_l" "x \<noteq> ?ep_r" "x \<noteq> ?mid" by (by100 blast)+
        from \<open>x \<in> A1\<close> obtain t where ht: "t \<in> top1_unit_interval" "hA t = x"
          using hbij_hA unfolding bij_betw_def by (by100 blast)
        have "t \<noteq> 0"
        proof
          assume "t = 0" hence "x = ?ep_l" using ht(2) by simp
          thus False using \<open>x \<noteq> ?ep_l\<close> by contradiction
        qed
        have "t \<noteq> 1"
        proof
          assume "t = 1" hence "x = ?ep_r" using ht(2) by simp
          thus False using \<open>x \<noteq> ?ep_r\<close> by contradiction
        qed
        have "t \<noteq> 1/2"
        proof
          assume ht12: "t = 1/2"
          have "x = hA (1/2)" using ht(2) ht12 by simp
          thus False using \<open>x \<noteq> ?mid\<close> by contradiction
        qed
        have "0 \<le> t" "t \<le> 1" using ht(1) unfolding top1_unit_interval_def by (by100 simp)+
        hence "0 < t \<and> t < 1/2 \<or> 1/2 < t \<and> t < 1"
          using \<open>t \<noteq> 0\<close> \<open>t \<noteq> 1\<close> \<open>t \<noteq> 1/2\<close> by linarith
        thus "x \<in> A_comp \<union> B_comp"
        proof
          assume "0 < t \<and> t < 1/2"
          hence "x \<in> A_comp" unfolding A_comp_def using ht(2) by (by100 blast)
          thus ?thesis by (by100 blast)
        next
          assume "1/2 < t \<and> t < 1"
          hence "x \<in> B_comp" unfolding B_comp_def using ht(2) by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
      next
        fix x assume "x \<in> A_comp \<union> B_comp"
        thus "x \<in> ?U \<inter> ?V"
        proof
          assume "x \<in> A_comp"
          then obtain t where "0 < t" "t < 1/2" "x = hA t"
            unfolding A_comp_def by (by100 blast)
          have "t \<in> top1_unit_interval" using \<open>0 < t\<close> \<open>t < 1/2\<close>
            unfolding top1_unit_interval_def by (by100 simp)
          have "x \<in> A1" using hbij_hA \<open>t \<in> _\<close> \<open>x = hA t\<close>
            unfolding bij_betw_def by (by100 blast)
          have "x \<noteq> ?ep_l"
          proof
            assume "x = ?ep_l"
            from inj_onD[OF hinj_hA \<open>x = ?ep_l\<close>[unfolded \<open>x = hA t\<close>]
                \<open>t \<in> top1_unit_interval\<close> h0_I]
            show False using \<open>0 < t\<close> by (by100 simp)
          qed
          have "x \<noteq> ?ep_r"
          proof
            assume "x = ?ep_r"
            from inj_onD[OF hinj_hA \<open>x = ?ep_r\<close>[unfolded \<open>x = hA t\<close>]
                \<open>t \<in> top1_unit_interval\<close> h1_I]
            show False using \<open>t < 1/2\<close> by (by100 simp)
          qed
          have "x \<noteq> ?mid"
          proof
            assume "x = ?mid"
            from inj_onD[OF hinj_hA \<open>x = ?mid\<close>[unfolded \<open>x = hA t\<close>]
                \<open>t \<in> top1_unit_interval\<close> h12_I]
            show False using \<open>t < 1/2\<close> \<open>0 < t\<close> by (by100 simp)
          qed
          show "x \<in> ?U \<inter> ?V"
            using \<open>x \<in> A1\<close> \<open>x \<noteq> ?ep_l\<close> \<open>x \<noteq> ?ep_r\<close> \<open>x \<noteq> ?mid\<close> hA1_sub
            by (by100 blast)
        next
          assume "x \<in> B_comp"
          then obtain t where "1/2 < t" "t < 1" "x = hA t"
            unfolding B_comp_def by (by100 blast)
          have "t \<in> top1_unit_interval" using \<open>1/2 < t\<close> \<open>t < 1\<close>
            unfolding top1_unit_interval_def by (by100 simp)
          have "x \<in> A1" using hbij_hA \<open>t \<in> _\<close> \<open>x = hA t\<close>
            unfolding bij_betw_def by (by100 blast)
          have "x \<noteq> ?ep_l"
          proof
            assume "x = ?ep_l"
            from inj_onD[OF hinj_hA \<open>x = ?ep_l\<close>[unfolded \<open>x = hA t\<close>]
                \<open>t \<in> top1_unit_interval\<close> h0_I]
            show False using \<open>1/2 < t\<close> by (by100 simp)
          qed
          have "x \<noteq> ?ep_r"
          proof
            assume "x = ?ep_r"
            from inj_onD[OF hinj_hA \<open>x = ?ep_r\<close>[unfolded \<open>x = hA t\<close>]
                \<open>t \<in> top1_unit_interval\<close> h1_I]
            show False using \<open>t < 1\<close> \<open>1/2 < t\<close> by (by100 simp)
          qed
          have "x \<noteq> ?mid"
          proof
            assume "x = ?mid"
            from inj_onD[OF hinj_hA \<open>x = ?mid\<close>[unfolded \<open>x = hA t\<close>]
                \<open>t \<in> top1_unit_interval\<close> h12_I]
            show False using \<open>1/2 < t\<close> by (by100 simp)
          qed
          show "x \<in> ?U \<inter> ?V"
            using \<open>x \<in> A1\<close> \<open>x \<noteq> ?ep_l\<close> \<open>x \<noteq> ?ep_r\<close> \<open>x \<noteq> ?mid\<close> hA1_sub
            by (by100 blast)
        qed
      qed
      \<comment> \<open>Disjoint.\<close>
      show "A_comp \<inter> B_comp = {}"
      proof (rule ccontr)
        assume "A_comp \<inter> B_comp \<noteq> {}"
        then obtain x where "x \<in> A_comp" "x \<in> B_comp" by (by100 blast)
        from \<open>x \<in> A_comp\<close> obtain s where hs: "0 < s" "s < 1/2" "x = hA s"
          unfolding A_comp_def by (by100 blast)
        from \<open>x \<in> B_comp\<close> obtain t where ht: "1/2 < t" "t < 1" "x = hA t"
          unfolding B_comp_def by (by100 blast)
        have "hA s = hA t" using hs(3) ht(3) by simp
        have "s \<in> top1_unit_interval" using hs unfolding top1_unit_interval_def by (by100 simp)
        have "t \<in> top1_unit_interval" using ht unfolding top1_unit_interval_def by (by100 simp)
        from inj_onD[OF hinj_hA \<open>hA s = hA t\<close> \<open>s \<in> _\<close> \<open>t \<in> _\<close>]
        have "s = t" .
        thus False using hs(2) ht(1) by linarith
      qed
      \<comment> \<open>Open in Y.\<close>
      show "openin_on Y TY A_comp"
      proof -
        \<comment> \<open>A\\_comp open in U (homeomorphic image of open (0,1/2)), U open in Y \\<Rightarrow> A\\_comp open in Y.\<close>
        \<comment> \<open>Step 1: A\\_comp \\<in> subspace\\_topology Y TY U (open in U).\<close>
        have hA_comp_open_U: "A_comp \<in> subspace_topology Y TY ?U"
        proof -
          \<comment> \<open>Re-derive homeomorphism (0,1) \\<rightarrow> U.\<close>
          let ?I01 = "{t::real. 0 < t \<and> t < 1}"
          have hI01_sub_I: "?I01 \<subseteq> top1_unit_interval"
            unfolding top1_unit_interval_def by (by100 auto)
          from homeomorphism_on_restrict[OF hhA hI01_sub_I]
          have hhA01: "top1_homeomorphism_on ?I01
              (subspace_topology top1_unit_interval top1_unit_interval_topology ?I01)
              (hA ` ?I01) (subspace_topology A1 (subspace_topology Y TY A1) (hA ` ?I01)) hA" .
          have "hA ` ?I01 = ?U"
          proof -
            \<comment> \<open>Already proved in U SC block; re-derive briefly.\<close>
            have "\<forall>x. x \<in> hA ` ?I01 \<longleftrightarrow> x \<in> ?U"
            proof (intro allI iffI)
              fix x assume "x \<in> hA ` ?I01"
              then obtain t where "0 < t" "t < 1" "x = hA t" by (by100 blast)
              have "t \<in> top1_unit_interval" using \<open>0 < t\<close> \<open>t < 1\<close>
                unfolding top1_unit_interval_def by (by100 simp)
              have "x \<in> A1" using hbij_hA \<open>t \<in> _\<close> \<open>x = hA t\<close>
                unfolding bij_betw_def by (by100 blast)
              have "x \<noteq> ?ep_l"
              proof
                assume "x = ?ep_l"
                from inj_onD[OF hinj_hA \<open>x = ?ep_l\<close>[unfolded \<open>x = hA t\<close>]
                    \<open>t \<in> _\<close> h0_I]
                show False using \<open>0 < t\<close> by (by100 simp)
              qed
              have "x \<noteq> ?ep_r"
              proof
                assume "x = ?ep_r"
                from inj_onD[OF hinj_hA \<open>x = ?ep_r\<close>[unfolded \<open>x = hA t\<close>]
                    \<open>t \<in> _\<close> h1_I]
                show False using \<open>t < 1\<close> by (by100 simp)
              qed
              show "x \<in> ?U" using \<open>x \<in> A1\<close> \<open>x \<noteq> ?ep_l\<close> \<open>x \<noteq> ?ep_r\<close> by (by100 blast)
            next
              fix x assume "x \<in> ?U"
              hence "x \<in> A1" "x \<noteq> ?ep_l" "x \<noteq> ?ep_r" by (by100 blast)+
              obtain t where "t \<in> top1_unit_interval" "hA t = x"
                using hbij_hA \<open>x \<in> A1\<close> unfolding bij_betw_def by (by100 blast)
              have "t \<noteq> 0" using \<open>x \<noteq> ?ep_l\<close> \<open>hA t = x\<close> by (by100 blast)
              have "t \<noteq> 1" using \<open>x \<noteq> ?ep_r\<close> \<open>hA t = x\<close> by (by100 blast)
              have "t \<in> ?I01" using \<open>t \<in> _\<close> \<open>t \<noteq> 0\<close> \<open>t \<noteq> 1\<close>
                unfolding top1_unit_interval_def by (by100 simp)
              show "x \<in> hA ` ?I01" using \<open>hA t = x\<close> \<open>t \<in> ?I01\<close> by (by100 blast)
            qed
            thus ?thesis by (by100 blast)
          qed
          \<comment> \<open>Adjust topologies.\<close>
          have "subspace_topology A1 (subspace_topology Y TY A1) ?U =
              subspace_topology Y TY ?U"
            by (rule subspace_topology_trans) (by100 blast)
          have "subspace_topology top1_unit_interval top1_unit_interval_topology ?I01 =
              subspace_topology UNIV top1_open_sets ?I01"
          proof -
            have "subspace_topology top1_unit_interval
                (subspace_topology UNIV top1_open_sets top1_unit_interval) ?I01 =
                subspace_topology UNIV top1_open_sets ?I01"
              by (rule subspace_topology_trans[OF hI01_sub_I])
            thus ?thesis unfolding top1_unit_interval_topology_def by simp
          qed
          have hhA01': "top1_homeomorphism_on ?I01
              (subspace_topology UNIV top1_open_sets ?I01)
              ?U (subspace_topology Y TY ?U) hA"
            using hhA01 \<open>hA ` ?I01 = ?U\<close>
              \<open>subspace_topology A1 _ ?U = subspace_topology Y TY ?U\<close>
              \<open>subspace_topology top1_unit_interval _ ?I01 = subspace_topology UNIV _ ?I01\<close>
            by simp
          \<comment> \<open>(0,1/2) is open in (0,1) (subspace of \\<real>).\<close>
          let ?I_A = "{t::real. 0 < t \<and> t < 1/2}"
          have "?I_A \<subseteq> ?I01" by (by100 auto)
          have "?I_A \<in> subspace_topology UNIV top1_open_sets ?I01"
          proof -
            have ho: "open {t::real. t < 1/2}"
              using open_lessThan[of "1/2::real"] unfolding lessThan_def by simp
            have "{t::real. t < 1/2} \<in> top1_open_sets"
              using ho unfolding top1_open_sets_def by (by100 blast)
            have "?I01 \<inter> {t::real. t < 1/2} = ?I_A" by (by100 auto)
            thus ?thesis unfolding subspace_topology_def
              using \<open>{t::real. t < 1/2} \<in> top1_open_sets\<close> by (by100 blast)
          qed
          \<comment> \<open>Apply homeomorphism\\_image\\_open.\<close>
          from homeomorphism_image_open[OF hhA01' \<open>?I_A \<in> _\<close> \<open>?I_A \<subseteq> ?I01\<close>]
          have "hA ` ?I_A \<in> subspace_topology Y TY ?U" .
          thus ?thesis unfolding A_comp_def .
        qed
        \<comment> \<open>Step 2: U \\<in> TY (U is open in Y).\<close>
        have "?U \<in> TY" using hU_open unfolding openin_on_def by (by100 blast)
        \<comment> \<open>Step 3: Open in open subspace \\<Rightarrow> open in ambient (Lemma 16.2).\<close>
        from Lemma_16_2[OF hTY_top \<open>?U \<in> TY\<close> hA_comp_open_U]
        have "A_comp \<in> TY" .
        have "A_comp \<subseteq> A1"
        proof -
          have "{t::real. 0 < t \<and> t < 1/2} \<subseteq> top1_unit_interval"
            unfolding top1_unit_interval_def by (by100 auto)
          thus ?thesis unfolding A_comp_def
            using hbij_hA unfolding bij_betw_def by (by100 blast)
        qed
        have "A_comp \<subseteq> Y" using \<open>A_comp \<subseteq> A1\<close> hA1_sub by (by100 blast)
        show ?thesis unfolding openin_on_def
          using \<open>A_comp \<in> TY\<close> \<open>A_comp \<subseteq> Y\<close> by (by100 blast)
      qed
      show "openin_on Y TY B_comp"
      proof -
        have hB_comp_open_U: "B_comp \<in> subspace_topology Y TY ?U"
        proof -
          \<comment> \<open>Re-derive homeomorphism (0,1) \\<rightarrow> U.\<close>
          let ?I01 = "{t::real. 0 < t \<and> t < 1}"
          let ?I_B = "{t::real. 1/2 < t \<and> t < 1}"
          have hI01_sub_I: "?I01 \<subseteq> top1_unit_interval"
            unfolding top1_unit_interval_def by (by100 auto)
          from homeomorphism_on_restrict[OF hhA hI01_sub_I]
          have hhA01: "top1_homeomorphism_on ?I01
              (subspace_topology top1_unit_interval top1_unit_interval_topology ?I01)
              (hA ` ?I01) (subspace_topology A1 (subspace_topology Y TY A1) (hA ` ?I01)) hA" .
          have "hA ` ?I01 = ?U"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> hA ` ?I01"
            then obtain t where "0 < t" "t < 1" "x = hA t" by (by100 blast)
            have "t \<in> top1_unit_interval" using \<open>0 < t\<close> \<open>t < 1\<close>
              unfolding top1_unit_interval_def by (by100 simp)
            have "x \<in> A1" using hbij_hA \<open>t \<in> _\<close> \<open>x = hA t\<close>
              unfolding bij_betw_def by (by100 blast)
            have "x \<noteq> ?ep_l"
            proof
              assume "x = ?ep_l"
              hence "hA t = hA 0" using \<open>x = hA t\<close> by simp
              hence "t = 0" using inj_onD[OF hinj_hA _ h0_I \<open>t \<in> _\<close>] by (by100 simp)
              thus False using \<open>0 < t\<close> by (by100 simp)
            qed
            have "x \<noteq> ?ep_r"
            proof
              assume "x = ?ep_r"
              hence "hA t = hA 1" using \<open>x = hA t\<close> by simp
              hence "t = 1" using inj_onD[OF hinj_hA _ h1_I \<open>t \<in> _\<close>] by (by100 simp)
              thus False using \<open>t < 1\<close> by (by100 simp)
            qed
            show "x \<in> ?U" using \<open>x \<in> A1\<close> \<open>x \<noteq> ?ep_l\<close> \<open>x \<noteq> ?ep_r\<close> by (by100 blast)
          next
            fix x assume "x \<in> ?U"
            hence "x \<in> A1" "x \<noteq> ?ep_l" "x \<noteq> ?ep_r" by (by100 blast)+
            obtain t where "t \<in> top1_unit_interval" "hA t = x"
              using hbij_hA \<open>x \<in> A1\<close> unfolding bij_betw_def by (by100 blast)
            have "t \<noteq> 0" using \<open>x \<noteq> ?ep_l\<close> \<open>hA t = x\<close> by (by100 blast)
            have "t \<noteq> 1" using \<open>x \<noteq> ?ep_r\<close> \<open>hA t = x\<close> by (by100 blast)
            have "t \<in> ?I01" using \<open>t \<in> _\<close> \<open>t \<noteq> 0\<close> \<open>t \<noteq> 1\<close>
              unfolding top1_unit_interval_def by (by100 simp)
            show "x \<in> hA ` ?I01" using \<open>hA t = x\<close> \<open>t \<in> ?I01\<close> by (by100 blast)
          qed
          have "subspace_topology A1 (subspace_topology Y TY A1) ?U =
              subspace_topology Y TY ?U"
            by (rule subspace_topology_trans) (by100 blast)
          have "subspace_topology top1_unit_interval top1_unit_interval_topology ?I01 =
              subspace_topology UNIV top1_open_sets ?I01"
          proof -
            have "subspace_topology top1_unit_interval
                (subspace_topology UNIV top1_open_sets top1_unit_interval) ?I01 =
                subspace_topology UNIV top1_open_sets ?I01"
              by (rule subspace_topology_trans[OF hI01_sub_I])
            thus ?thesis unfolding top1_unit_interval_topology_def by simp
          qed
          have hhA01': "top1_homeomorphism_on ?I01
              (subspace_topology UNIV top1_open_sets ?I01)
              ?U (subspace_topology Y TY ?U) hA"
            using hhA01 \<open>hA ` ?I01 = ?U\<close>
              \<open>subspace_topology A1 _ ?U = subspace_topology Y TY ?U\<close>
              \<open>subspace_topology top1_unit_interval _ ?I01 = subspace_topology UNIV _ ?I01\<close>
            by simp
          \<comment> \<open>(1/2,1) is open in (0,1) (subspace of \\<real>).\<close>
          have "?I_B \<subseteq> ?I01" by (by100 auto)
          have "?I_B \<in> subspace_topology UNIV top1_open_sets ?I01"
          proof -
            have ho: "open {t::real. 1/2 < t}"
              using open_greaterThan[of "1/2::real"] unfolding greaterThan_def by simp
            have "{t::real. 1/2 < t} \<in> top1_open_sets"
              using ho unfolding top1_open_sets_def by (by100 blast)
            have "?I01 \<inter> {t::real. 1/2 < t} = ?I_B" by (by100 auto)
            thus ?thesis unfolding subspace_topology_def
              using \<open>{t::real. 1/2 < t} \<in> top1_open_sets\<close> by (by100 blast)
          qed
          from homeomorphism_image_open[OF hhA01' \<open>?I_B \<in> _\<close> \<open>?I_B \<subseteq> ?I01\<close>]
          have "hA ` ?I_B \<in> subspace_topology Y TY ?U" .
          thus ?thesis unfolding B_comp_def .
        qed
        have "?U \<in> TY" using hU_open unfolding openin_on_def by (by100 blast)
        from Lemma_16_2[OF hTY_top \<open>?U \<in> TY\<close> hB_comp_open_U]
        have "B_comp \<in> TY" .
        have "B_comp \<subseteq> A1"
        proof -
          have "{t::real. 1/2 < t \<and> t < 1} \<subseteq> top1_unit_interval"
            unfolding top1_unit_interval_def by (by100 auto)
          thus ?thesis unfolding B_comp_def
            using hbij_hA unfolding bij_betw_def by (by100 blast)
        qed
        have "B_comp \<subseteq> Y" using \<open>B_comp \<subseteq> A1\<close> hA1_sub by (by100 blast)
        show ?thesis unfolding openin_on_def
          using \<open>B_comp \<in> TY\<close> \<open>B_comp \<subseteq> Y\<close> by (by100 blast)
      qed
      \<comment> \<open>Path-connected.\<close>
      show "top1_path_connected_on A_comp (subspace_topology Y TY A_comp)"
      proof -
        \<comment> \<open>(0,1/2) is convex \\<Rightarrow> SC \\<Rightarrow> PC. Homeomorphism transfers PC.\<close>
        let ?I_A = "{t::real. 0 < t \<and> t < 1/2}"
        have "?I_A \<subseteq> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
        from homeomorphism_on_restrict[OF hhA this]
        have "top1_homeomorphism_on ?I_A
            (subspace_topology top1_unit_interval top1_unit_interval_topology ?I_A)
            A_comp (subspace_topology A1 (subspace_topology Y TY A1) A_comp) hA"
          unfolding A_comp_def .
        have "A_comp \<subseteq> A1" unfolding A_comp_def
          using hbij_hA \<open>?I_A \<subseteq> top1_unit_interval\<close> unfolding bij_betw_def by (by100 blast)
        hence "subspace_topology A1 (subspace_topology Y TY A1) A_comp =
            subspace_topology Y TY A_comp"
          by (rule subspace_topology_trans)
        \<comment> \<open>(0,1/2) is SC (convex) \\<Rightarrow> PC.\<close>
        have hIA_sc: "top1_simply_connected_on ?I_A (subspace_topology UNIV top1_open_sets ?I_A)"
        proof (rule convex_real_subspace_simply_connected)
          show "?I_A \<noteq> {}"
          proof -
            have "(1/4::real) \<in> ?I_A" by (by100 simp)
            thus ?thesis by (by100 blast)
          qed
          fix x y t :: real assume "x \<in> ?I_A" "y \<in> ?I_A" "0 \<le> t" "t \<le> 1"
          thus "(1-t)*x + t*y \<in> ?I_A"
          proof (cases "t = 0")
            case True thus ?thesis using \<open>x \<in> ?I_A\<close> by simp
          next
            case False hence "t > 0" using \<open>0 \<le> t\<close> by linarith
            have "(1-t)*x \<ge> 0" using \<open>x \<in> ?I_A\<close> \<open>0 \<le> t\<close> \<open>t \<le> 1\<close>
              by (intro mult_nonneg_nonneg) (by100 simp)+
            have "t*y > 0" using \<open>y \<in> ?I_A\<close> \<open>t > 0\<close> by (by100 simp)
            hence "0 < (1-t)*x + t*y" using \<open>(1-t)*x \<ge> 0\<close> by linarith
            moreover have "(1-t)*x + t*y < 1/2"
            proof (cases "t = 1")
              case True thus ?thesis using \<open>y \<in> ?I_A\<close> by simp
            next
              case False hence "1-t > 0" using \<open>t \<le> 1\<close> by linarith
              have "(1-t)*x < (1-t)*(1/2)" using \<open>x \<in> ?I_A\<close> \<open>1-t > 0\<close> by (by100 simp)
              have "t*y \<le> t*(1/2)" using \<open>y \<in> ?I_A\<close> \<open>0 \<le> t\<close>
                by (intro mult_left_mono) (by100 simp)+
              show ?thesis using \<open>(1-t)*x < (1-t)*(1/2)\<close> \<open>t*y \<le> t*(1/2)\<close>
                by (simp add: algebra_simps)
            qed
            ultimately show ?thesis by (by100 simp)
          qed
        qed
        have hIA_pc: "top1_path_connected_on ?I_A (subspace_topology UNIV top1_open_sets ?I_A)"
          using hIA_sc unfolding top1_simply_connected_on_def by (by100 blast)
        \<comment> \<open>Transfer PC via homeomorphism.\<close>
        have "subspace_topology top1_unit_interval top1_unit_interval_topology ?I_A =
            subspace_topology UNIV top1_open_sets ?I_A"
        proof -
          have "subspace_topology top1_unit_interval
              (subspace_topology UNIV top1_open_sets top1_unit_interval) ?I_A =
              subspace_topology UNIV top1_open_sets ?I_A"
            by (rule subspace_topology_trans[OF \<open>?I_A \<subseteq> top1_unit_interval\<close>])
          thus ?thesis unfolding top1_unit_interval_topology_def by simp
        qed
        have "top1_homeomorphism_on ?I_A
            (subspace_topology UNIV top1_open_sets ?I_A)
            A_comp (subspace_topology Y TY A_comp) hA"
          using \<open>top1_homeomorphism_on ?I_A _ A_comp _ hA\<close>
              \<open>subspace_topology A1 _ A_comp = subspace_topology Y TY A_comp\<close>
              \<open>subspace_topology top1_unit_interval _ ?I_A = subspace_topology UNIV _ ?I_A\<close>
          by simp
        from homeomorphism_preserves_path_connected[OF this hIA_pc]
        show ?thesis .
      qed
      show "top1_path_connected_on B_comp (subspace_topology Y TY B_comp)"
      proof -
        let ?I_B = "{t::real. 1/2 < t \<and> t < 1}"
        have hIB_sub: "?I_B \<subseteq> top1_unit_interval"
          unfolding top1_unit_interval_def by (by100 auto)
        from homeomorphism_on_restrict[OF hhA hIB_sub]
        have hhA_B: "top1_homeomorphism_on ?I_B
            (subspace_topology top1_unit_interval top1_unit_interval_topology ?I_B)
            (hA ` ?I_B) (subspace_topology A1 (subspace_topology Y TY A1) (hA ` ?I_B)) hA" .
        have "hA ` ?I_B = B_comp" unfolding B_comp_def by (by100 blast)
        have "B_comp \<subseteq> A1" unfolding B_comp_def
          using hbij_hA hIB_sub unfolding bij_betw_def by (by100 blast)
        have "subspace_topology A1 (subspace_topology Y TY A1) B_comp =
            subspace_topology Y TY B_comp"
          by (rule subspace_topology_trans[OF \<open>B_comp \<subseteq> A1\<close>])
        have hIB_sc: "top1_simply_connected_on ?I_B (subspace_topology UNIV top1_open_sets ?I_B)"
        proof (rule convex_real_subspace_simply_connected)
          have "(3/4::real) \<in> ?I_B" by (by100 simp)
          thus "?I_B \<noteq> {}" by (by100 blast)
          fix x y t :: real assume "x \<in> ?I_B" "y \<in> ?I_B" "0 \<le> t" "t \<le> 1"
          hence hx: "1/2 < x" "x < 1" and hy: "1/2 < y" "y < 1"
            by (by100 simp)+
          show "(1-t)*x + t*y \<in> ?I_B"
          proof (intro CollectI conjI)
            show "1/2 < (1-t)*x + t*y"
            proof (cases "t = 0")
              case True thus ?thesis using hx by simp
            next
              case False hence "t > 0" using \<open>0 \<le> t\<close> by linarith
              have "(1-t)*x \<ge> (1-t)*(1/2)" using hx \<open>0 \<le> t\<close> \<open>t \<le> 1\<close>
                by (intro mult_left_mono) linarith+
              have "t*y > t*(1/2)" using hy \<open>t > 0\<close> by (by100 simp)
              have "(1-t)*x + t*y > (1-t)*(1/2) + t*(1/2)"
                using \<open>(1-t)*x \<ge> _\<close> \<open>t*y > _\<close> by linarith
              moreover have "(1-t)*(1/2) + t*(1/2) = (1/2::real)"
                by (simp add: field_simps)
              ultimately show ?thesis by linarith
            qed
            show "(1-t)*x + t*y < 1"
            proof (cases "t = 1")
              case True thus ?thesis using hy by simp
            next
              case False hence "1-t > 0" using \<open>t \<le> 1\<close> by linarith
              have "(1-t)*x < (1-t)" using hx \<open>1-t > 0\<close> by (by100 simp)
              have "t*y \<le> t" using hy \<open>0 \<le> t\<close> by (intro mult_left_le) linarith+
              show ?thesis using \<open>(1-t)*x < _\<close> \<open>t*y \<le> _\<close> by linarith
            qed
          qed
        qed
        have hIB_pc: "top1_path_connected_on ?I_B (subspace_topology UNIV top1_open_sets ?I_B)"
          using hIB_sc unfolding top1_simply_connected_on_def by (by100 blast)
        have "subspace_topology top1_unit_interval top1_unit_interval_topology ?I_B =
            subspace_topology UNIV top1_open_sets ?I_B"
        proof -
          have "subspace_topology top1_unit_interval
              (subspace_topology UNIV top1_open_sets top1_unit_interval) ?I_B =
              subspace_topology UNIV top1_open_sets ?I_B"
            by (rule subspace_topology_trans[OF hIB_sub])
          thus ?thesis unfolding top1_unit_interval_topology_def by simp
        qed
        have "top1_homeomorphism_on ?I_B
            (subspace_topology UNIV top1_open_sets ?I_B)
            B_comp (subspace_topology Y TY B_comp) hA"
          using hhA_B \<open>hA ` ?I_B = B_comp\<close>
              \<open>subspace_topology A1 _ B_comp = subspace_topology Y TY B_comp\<close>
              \<open>subspace_topology top1_unit_interval _ ?I_B = subspace_topology UNIV _ ?I_B\<close>
          by simp
        from homeomorphism_preserves_path_connected[OF this hIB_pc]
        show ?thesis .
      qed
      \<comment> \<open>Non-empty.\<close>
      show "\<exists>a. a \<in> A_comp"
      proof -
        have "(1/4::real) \<in> {t. 0 < t \<and> t < 1/2}" by (by100 simp)
        thus ?thesis unfolding A_comp_def by (by100 blast)
      qed
      show "\<exists>b. b \<in> B_comp"
      proof -
        have "(3/4::real) \<in> {t. 1/2 < t \<and> t < 1}" by (by100 simp)
        thus ?thesis unfolding B_comp_def by (by100 blast)
      qed
    qed
    then obtain A_comp B_comp where hAB: "?U \<inter> ?V = A_comp \<union> B_comp"
        "A_comp \<inter> B_comp = {}" "openin_on Y TY A_comp" "openin_on Y TY B_comp"
        "top1_path_connected_on A_comp (subspace_topology Y TY A_comp)"
        "top1_path_connected_on B_comp (subspace_topology Y TY B_comp)"
      and ha_comp: "\<exists>a. a \<in> A_comp" and hb_comp: "\<exists>b. b \<in> B_comp"
      by - ((erule exE)+, (erule conjE)+, rule that, assumption+)
    then obtain pt_a pt_b where hpta: "pt_a \<in> A_comp" and hptb: "pt_b \<in> B_comp"
      by (by100 blast)
    \<comment> \<open>Paths \\<alpha> in U from pt\\_a to pt\\_b, \\<beta> in V from pt\\_b to pt\\_a.\<close>
    \<comment> \<open>U and V are path-connected (SC \\<Rightarrow> PC).\<close>
    have hU_pc: "top1_path_connected_on ?U (subspace_topology Y TY ?U)"
      using hU_sc top1_simply_connected_on_path_connected by (by100 blast)
    have hV_pc: "top1_path_connected_on ?V (subspace_topology Y TY ?V)"
      using hV_sc top1_simply_connected_on_path_connected by (by100 blast)
    \<comment> \<open>pt\\_a, pt\\_b \\<in> U (they are in U\\<inter>V \\<subseteq> U).\<close>
    have "pt_a \<in> ?U \<inter> ?V" using hpta hAB(1) by (by100 blast)
    hence hpta_U: "pt_a \<in> ?U" and hpta_V: "pt_a \<in> ?V" by (by100 blast)+
    have "pt_b \<in> ?U \<inter> ?V" using hptb hAB(1) by (by100 blast)
    hence hptb_U: "pt_b \<in> ?U" and hptb_V: "pt_b \<in> ?V" by (by100 blast)+
    \<comment> \<open>Get paths from path-connectivity.\<close>
    obtain \<alpha> where h\<alpha>: "top1_is_path_on ?U (subspace_topology Y TY ?U) pt_a pt_b \<alpha>"
      using hU_pc hpta_U hptb_U unfolding top1_path_connected_on_def by (by100 blast)
    obtain \<beta> where h\<beta>: "top1_is_path_on ?V (subspace_topology Y TY ?V) pt_b pt_a \<beta>"
      using hV_pc hptb_V hpta_V unfolding top1_path_connected_on_def by (by100 blast)
    \<comment> \<open>Apply Lemma 84.6 at basepoint pt\\_a.\<close>
    have hpta_A: "pt_a \<in> A_comp" using hpta .
    have hptb_B: "pt_b \<in> B_comp" using hptb .
    from Lemma_84_6_two_component_generation[OF hY_strict hU_open hV_open
        hcover hAB(1) hAB(2) hAB(3) hAB(4) hAB(5) hAB(6)
        hpta hptb h\<alpha> h\<beta> hU_sc hV_sc]
    have hpi1_a_Z: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier Y TY pt_a) (top1_fundamental_group_mul Y TY pt_a)
        top1_Z_group top1_Z_mul" .
    \<comment> \<open>Basepoint change: Y is PC, so \\<pi>\\_1(Y,y0) \\<cong> \\<pi>\\_1(Y,pt\\_a).\<close>
    have hY_pc: "top1_path_connected_on Y TY"
    proof -
      have hA1_arc: "top1_is_arc_on A1 (subspace_topology Y TY A1)"
        using h\<A> hA1 by (by100 blast)
      obtain h' where hh': "top1_homeomorphism_on top1_unit_interval
          top1_unit_interval_topology A1 (subspace_topology Y TY A1) h'"
        using hA1_arc unfolding top1_is_arc_on_def by (by100 blast)
      from arc_endpoints_are_boundary[OF hY_strict hY_haus hA1_sub hA1_arc hh']
      have "top1_arc_endpoints_on A1 (subspace_topology Y TY A1) = {h' 0, h' 1}" .
      have "h' 0 \<in> T"
        using hNT_endpoints[rule_format, OF \<open>A1 \<in> ?NT\<close>]
        \<open>top1_arc_endpoints_on A1 _ = {h' 0, h' 1}\<close> by (by100 simp)
      have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
      have "h' 0 \<in> A1"
        using hh' \<open>(0::real) \<in> top1_unit_interval\<close>
        unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "\<exists>e. e \<in> T \<and> e \<in> A1" using \<open>h' 0 \<in> T\<close> \<open>h' 0 \<in> A1\<close> by (by100 blast)
      from tree_union_arcs_path_connected[OF hTY_top hT_tree hT_sub _ _ _ hT_x0,
          of "{A1}"]
      have "top1_path_connected_on (T \<union> \<Union>{A1}) (subspace_topology Y TY (T \<union> \<Union>{A1}))"
        using hA1_arc hA1_sub \<open>\<exists>e. e \<in> T \<and> e \<in> A1\<close> by (by100 simp)
      hence hpc: "top1_path_connected_on (T \<union> A1) (subspace_topology Y TY (T \<union> A1))"
        by simp
      have "T \<union> A1 = Y" using \<open>Y = T \<union> A1\<close> by simp
      have "\<forall>U\<in>TY. U \<subseteq> Y"
        using hY_strict unfolding is_topology_on_strict_def by (by100 blast)
      have "subspace_topology Y TY Y = TY"
        by (rule subspace_topology_self[OF \<open>\<forall>U\<in>TY. U \<subseteq> Y\<close>])
      thus ?thesis using hpc \<open>T \<union> A1 = Y\<close> by simp
    qed
    have ha_Y: "pt_a \<in> Y" using hpta_A hAB(1) by (by100 blast)
    obtain \<gamma> where h\<gamma>: "top1_is_path_on Y TY pt_a y0 \<gamma>"
      using hY_pc ha_Y hy0 unfolding top1_path_connected_on_def by (by100 blast)
    from basepoint_change_iso_via_path[OF hTY_top h\<gamma>]
    have hbc: "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier Y TY pt_a) (top1_fundamental_group_mul Y TY pt_a)
        (top1_fundamental_group_carrier Y TY y0) (top1_fundamental_group_mul Y TY y0)" .
    have hpi1_y0_grp: "top1_is_group_on
        (top1_fundamental_group_carrier Y TY y0) (top1_fundamental_group_mul Y TY y0)
        (top1_fundamental_group_id Y TY y0) (top1_fundamental_group_invg Y TY y0)"
      by (rule top1_fundamental_group_is_group[OF hTY_top hy0])
    have hpi1_a_grp: "top1_is_group_on
        (top1_fundamental_group_carrier Y TY pt_a) (top1_fundamental_group_mul Y TY pt_a)
        (top1_fundamental_group_id Y TY pt_a) (top1_fundamental_group_invg Y TY pt_a)"
      by (rule top1_fundamental_group_is_group[OF hTY_top ha_Y])
    from top1_groups_isomorphic_on_sym[OF hbc hpi1_a_grp hpi1_y0_grp]
    have "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier Y TY y0) (top1_fundamental_group_mul Y TY y0)
        (top1_fundamental_group_carrier Y TY pt_a) (top1_fundamental_group_mul Y TY pt_a)" .
    from groups_isomorphic_trans_fwd[OF this hpi1_a_Z]
    show ?thesis .
qed

\<comment> \<open>The n parameter bounds the number of non-tree arcs.\<close>
lemma graph_pi1_free_weak_finite:
  fixes n :: nat
  shows "\<And>Y :: 'a set. \<And>TY :: 'a set set. \<And>y0 :: 'a. \<And>\<A> T.
      top1_is_graph_on Y TY \<Longrightarrow> top1_connected_on Y TY \<Longrightarrow> y0 \<in> Y \<Longrightarrow>
      card {A\<in>\<A>. \<not> A \<subseteq> T} \<le> n \<Longrightarrow> finite {A\<in>\<A>. \<not> A \<subseteq> T} \<Longrightarrow>
      (\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)) \<Longrightarrow>
      \<Union>\<A> = Y \<Longrightarrow>
      (\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2) \<Longrightarrow>
      (\<forall>C. C \<subseteq> Y \<longrightarrow>
           (closedin_on Y TY C \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))) \<Longrightarrow>
      top1_is_tree_on T (subspace_topology Y TY T) \<Longrightarrow>
      T \<subseteq> Y \<Longrightarrow>
      (\<forall>A\<in>\<A>. A \<subseteq> T \<or>
           A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)) \<Longrightarrow>
      y0 \<in> T \<Longrightarrow>
      (\<forall>A\<in>{A\<in>\<A>. \<not> A \<subseteq> T}. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology Y TY A). e \<in> T) \<Longrightarrow>
      \<exists>(\<iota>::nat \<Rightarrow> _) (S::nat set). top1_is_free_group_full_on
          (top1_fundamental_group_carrier Y TY y0)
          (top1_fundamental_group_mul Y TY y0)
          (top1_fundamental_group_id Y TY y0)
          (top1_fundamental_group_invg Y TY y0)
          \<iota> S"
proof (induction n)
  case 0
  \<comment> \<open>Base case: card(NT) \\<le> 0, so NT = {}. Y = T. Tree \\<Rightarrow> SC \\<Rightarrow> trivial \\<pi>\\_1.\<close>
  have hNT_empty: "{A\<in>\<A>. \<not> A \<subseteq> T} = {}" using 0(4) 0(5) by (by100 simp)
  show ?case by (rule graph_tree_free_pi1[OF 0(1) 0(3) 0(6) 0(7) 0(10) 0(11) 0(13) hNT_empty])
next
  case (Suc n)
  \<comment> \<open>Step: card(NT) \\<le> Suc n.\<close>
  show ?case
  proof (cases "card {A\<in>\<A>. \<not> A \<subseteq> T} = 0")
    case True
    \<comment> \<open>card = 0: NT = {}. Use graph\\_tree\\_free\\_pi1.\<close>
    have hNT_empty: "{A\<in>\<A>. \<not> A \<subseteq> T} = {}" using True Suc(6) by (by100 simp)
    show ?thesis by (rule graph_tree_free_pi1[OF Suc(2) Suc(4) Suc(7) Suc(8) Suc(11) Suc(12) Suc(14) hNT_empty])
  next
    case hcard_ne0: False
    \<comment> \<open>card \\<ge> 1. Card=1: Lemma 84.6. Card>1: SvK + Suc.IH.\<close>
    have hNT_ne: "{A\<in>\<A>. \<not> A \<subseteq> T} \<noteq> {}" using hcard_ne0 Suc(6) by (by100 simp)
    then obtain A1 where hA1: "A1 \<in> {A\<in>\<A>. \<not> A \<subseteq> T}" by (by100 blast)
    show ?thesis
    proof (cases "card {A\<in>\<A>. \<not> A \<subseteq> T} = 1")
      case True
      \<comment> \<open>Card=1: \\<pi>\\_1(Y) \\<cong> \\<Z> (Lemma 84.6), \\<Z> free \\<Rightarrow> \\<pi>\\_1 free.\<close>
      note hgraph = Suc(2) and hy0 = Suc(4)
      note h\<A> = Suc(7) and h\<A>_cover = Suc(8) and h\<A>_inter = Suc(9) and h\<A>_coh = Suc(10)
      note hT_tree = Suc(11) and hT_sub = Suc(12) and hT_subgraph = Suc(13)
      note hT_x0 = Suc(14) and hNT_endpoints = Suc(15)
      let ?NT = "{A\<in>\<A>. \<not> A \<subseteq> T}"
      have hNT_singleton: "?NT = {A1}"
      proof -
        from card_1_singletonE[OF True] obtain B where hB: "?NT = {B}" by (by100 blast)
        hence "A1 = B" using hA1 by (by100 blast)
        thus ?thesis using hB by (by100 simp)
      qed
      have hpi1_iso_Z: "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier Y TY y0) (top1_fundamental_group_mul Y TY y0)
          top1_Z_group top1_Z_mul"
        by (rule graph_one_edge_pi1_iso_Z[OF hgraph Suc(3) hy0
            h\<A> h\<A>_cover h\<A>_inter h\<A>_coh hT_tree hT_sub hT_subgraph hT_x0
            hNT_endpoints hA1 hNT_singleton])
      have hZ_free: "top1_is_free_group_full_on top1_Z_group top1_Z_mul
          top1_Z_id top1_Z_invg (\<lambda>(_::nat). (1::int)) {0::nat}"
        by (rule Z_is_free_on_one_generator)
      have hTY_top: "is_topology_on Y TY"
        using hgraph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by5000 blast)
      have hpi1_grp: "top1_is_group_on
          (top1_fundamental_group_carrier Y TY y0) (top1_fundamental_group_mul Y TY y0)
          (top1_fundamental_group_id Y TY y0) (top1_fundamental_group_invg Y TY y0)"
        by (rule top1_fundamental_group_is_group[OF hTY_top hy0])
      have hZ_grp: "top1_is_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
        using hZ_free unfolding top1_is_free_group_full_on_def by (by100 blast)
      from top1_groups_isomorphic_on_sym[OF hpi1_iso_Z hpi1_grp hZ_grp]
      have "top1_groups_isomorphic_on top1_Z_group top1_Z_mul
          (top1_fundamental_group_carrier Y TY y0) (top1_fundamental_group_mul Y TY y0)" .
      from free_group_iso_transfer[OF hZ_free this hpi1_grp]
      show ?thesis by (by100 blast)
    next
      case hcard_ge2: False
      \<comment> \<open>Card \\<ge> 2: SvK decomposition + Suc.IH for recursive calls.\<close>
      have hcard_gt1: "card {A\<in>\<A>. \<not> A \<subseteq> T} > 1"
      proof -
        have "card {A\<in>\<A>. \<not> A \<subseteq> T} \<noteq> 0" using Suc(6) hNT_ne by (by100 auto)
        moreover have "card {A\<in>\<A>. \<not> A \<subseteq> T} \<noteq> 1" using hcard_ge2 by (by100 blast)
        ultimately show ?thesis by (by100 linarith)
      qed
      \<comment> \<open>The IH: for any graph with \\<le> n NT arcs, \\<pi>\\_1 is free.\<close>
      note IH = Suc(1)
      note hgraph = Suc(2) and hy0 = Suc(4)
      note hcard_suc = Suc(5) and hfin = Suc(6)
      note h\<A> = Suc(7) and h\<A>_cover = Suc(8) and h\<A>_inter = Suc(9) and h\<A>_coh = Suc(10)
      note hT_tree = Suc(11) and hT_sub = Suc(12) and hT_subgraph = Suc(13)
      note hT_x0 = Suc(14) and hNT_endpoints = Suc(15)
      let ?NT = "{A\<in>\<A>. \<not> A \<subseteq> T}"
      \<comment> \<open>The SvK infrastructure is the same as in graph\\_pi1\\_free\\_weak card>1.
         The only change: IH sorrys become IH calls.\<close>
      \<comment> \<open>For target\\_U (T \\<union> A1): card(NT\\_U) = 1 \\<le> n.
         For target\\_V (T \\<union> \\<Union>(NT-{A1})): card(NT\\_V) = card(NT)-1 \\<le> n.\<close>
      \<comment> \<open>Card bound: card(NT) \\<le> Suc n and card(NT) \\<ge> 2 implies n \\<ge> 1.\<close>
      have hn_ge1: "n \<ge> 1"
      proof -
        have "card ?NT \<le> Suc n" using hcard_suc .
        moreover have "card ?NT \<ge> 2" using hcard_gt1 by (by100 linarith)
        ultimately show ?thesis by (by100 linarith)
      qed
      \<comment> \<open>This is the full SvK + IH proof from graph\\_pi1\\_free\\_weak card>1,
         with proper IH calls replacing sorry.\<close>
      \<comment> \<open>Full SvK + IH proof for card>1.\<close>
      \<comment> \<open>Step 1: Interior points.\<close>
      have hint_pts: "\<forall>A\<in>?NT. \<exists>p. p \<in> A \<and> p \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
      proof (intro ballI)
        fix A assume "A \<in> ?NT"
        hence "A \<in> \<A>" by (by100 blast)
        have harc: "top1_is_arc_on A (subspace_topology Y TY A)" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
        obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
            A (subspace_topology Y TY A) h" using harc unfolding top1_is_arc_on_def by (by100 blast)
        have hbij: "bij_betw h top1_unit_interval A"
          using hh unfolding top1_homeomorphism_on_def by (by100 blast)
        have hY_strict: "is_topology_on_strict Y TY"
          using hgraph unfolding top1_is_graph_on_def by (by100 blast)
        have hY_haus: "is_hausdorff_on Y TY"
          using hgraph unfolding top1_is_graph_on_def by (by100 blast)
        have "A \<subseteq> Y" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
        from arc_endpoints_are_boundary[OF hY_strict hY_haus \<open>A \<subseteq> Y\<close> harc hh]
        have hep: "top1_arc_endpoints_on A (subspace_topology Y TY A) = {h 0, h 1}" .
        have h12_I: "(1/2::real) \<in> top1_unit_interval"
          unfolding top1_unit_interval_def by (by100 simp)
        have "h (1/2) \<in> A" using hbij h12_I unfolding bij_betw_def by (by100 blast)
        moreover have "h (1/2) \<notin> {h 0, h 1}"
        proof -
          have hinj: "inj_on h top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
          have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
          have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
          have "(1/2::real) \<noteq> 0" by (by100 simp)
          hence "h (1/2) \<noteq> h 0" using hinj h12_I h0_I unfolding inj_on_def by (by100 blast)
          have "(1/2::real) \<noteq> 1" by (by100 simp)
          hence "h (1/2) \<noteq> h 1" using hinj h12_I h1_I unfolding inj_on_def by (by100 blast)
          thus ?thesis using \<open>h (1/2) \<noteq> h 0\<close> by (by100 blast)
        qed
        ultimately show "\<exists>p. p \<in> A \<and> p \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
          using hep by (by100 blast)
      qed
      have "\<exists>ps. \<forall>A\<in>?NT. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
      proof -
        have "\<forall>A. A \<in> ?NT \<longrightarrow> (\<exists>p. p \<in> A \<and> p \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A))"
          using hint_pts by (by100 blast)
        hence "\<exists>f. \<forall>A. A \<in> ?NT \<longrightarrow> f A \<in> A \<and> f A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
          by (rule choice_iff'[THEN iffD1])
        thus ?thesis by (by100 blast)
      qed
      then obtain ps where hps: "\<forall>A\<in>?NT. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
        by (by5000 blast)
      \<comment> \<open>Step 2: Define U, V.\<close>
      let ?S_U = "?NT - {A1}"
      let ?U = "Y - ps ` ?S_U"
      let ?V = "Y - ps ` {A1}"
      let ?UV = "Y - ps ` ?NT"
      \<comment> \<open>Step 3: U\\<union>V=Y, U\\<inter>V=UV.\<close>
      have hUV_cover: "?U \<union> ?V = Y"
      proof -
        have "ps ` (?NT - {A1}) \<inter> ps ` {A1} = {}"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then obtain B where "B \<in> ?NT - {A1}" "ps B = ps A1" by (by100 blast)
          have "B \<in> \<A>" using \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
          have "B \<noteq> A1" using \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
          have "ps B \<in> B" using hps \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
          have "ps B \<notin> top1_arc_endpoints_on B (subspace_topology Y TY B)"
            using hps \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
          have "ps B \<in> A1" using \<open>ps B = ps A1\<close> hps hA1 by (by100 simp)
          have "ps B \<in> B \<inter> A1" using \<open>ps B \<in> B\<close> \<open>ps B \<in> A1\<close> by (by100 blast)
          have "A1 \<in> \<A>" using hA1 by (by100 blast)
          from h\<A>_inter[rule_format, OF \<open>B \<in> \<A>\<close> \<open>A1 \<in> \<A>\<close> \<open>B \<noteq> A1\<close>]
          have "B \<inter> A1 \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)" by (by100 blast)
          hence "ps B \<in> top1_arc_endpoints_on B (subspace_topology Y TY B)"
            using \<open>ps B \<in> B \<inter> A1\<close> by (by100 blast)
          thus False using \<open>ps B \<notin> _\<close> by (by100 blast)
        qed
        thus ?thesis by (by100 blast)
      qed
      have hUV_eq: "?U \<inter> ?V = ?UV"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> ?U \<inter> ?V"
        hence "x \<in> Y" "x \<notin> ps ` (?NT - {A1})" "x \<notin> ps ` {A1}" by (by100 blast)+
        have "?NT = (?NT - {A1}) \<union> {A1}" using hA1 by (by100 blast)
        hence "ps ` ?NT = ps ` (?NT - {A1}) \<union> ps ` {A1}"
          using image_Un[of ps "?NT - {A1}" "{A1}"] by (by100 simp)
        thus "x \<in> ?UV" using \<open>x \<in> Y\<close> \<open>x \<notin> ps ` (?NT - {A1})\<close> \<open>x \<notin> ps ` {A1}\<close> by (by100 blast)
      next
        fix x assume "x \<in> ?UV"
        hence "x \<in> Y" "x \<notin> ps ` ?NT" by (by100 blast)+
        have "x \<notin> ps ` (?NT - {A1})" using \<open>x \<notin> ps ` ?NT\<close> by (by100 blast)
        have "x \<notin> ps ` {A1}" using \<open>x \<notin> ps ` ?NT\<close> hA1 by (by100 blast)
        thus "x \<in> ?U \<inter> ?V" using \<open>x \<in> Y\<close> \<open>x \<notin> ps ` (?NT - {A1})\<close> \<open>x \<notin> ps ` {A1}\<close>
          by (by100 blast)
      qed
      \<comment> \<open>Step 4: U, V open.\<close>
      have hY_strict: "is_topology_on_strict Y TY"
        using hgraph unfolding top1_is_graph_on_def by (by100 blast)
      have hY_haus: "is_hausdorff_on Y TY"
        using hgraph unfolding top1_is_graph_on_def by (by100 blast)
      have hTY_top: "is_topology_on Y TY"
        using hY_strict unfolding is_topology_on_strict_def by (by100 blast)
      have hU_open: "openin_on Y TY ?U"
      proof -
        have hfin_SU: "finite (ps ` ?S_U)" using hfin by (by100 simp)
        have hsub_SU: "ps ` ?S_U \<subseteq> Y" using hps h\<A> by (by100 blast)
        have "closedin_on Y TY (ps ` ?S_U)"
          by (rule Theorem_17_8[OF hY_haus hfin_SU hsub_SU])
        thus ?thesis using closedin_complement_openin by (by100 simp)
      qed
      have hV_open: "openin_on Y TY ?V"
      proof -
        have hfin_SV: "finite (ps ` {A1})" by (by100 simp)
        have hsub_SV: "ps ` {A1} \<subseteq> Y" using hps hA1 h\<A> by (by100 blast)
        have "closedin_on Y TY (ps ` {A1})"
          by (rule Theorem_17_8[OF hY_haus hfin_SV hsub_SV])
        thus ?thesis using closedin_complement_openin by (by100 simp)
      qed
      \<comment> \<open>Step 5: UV SC.\<close>
      have hUV_sc: "top1_simply_connected_on ?UV (subspace_topology Y TY ?UV)"
      proof -
        have hvert_T: "\<forall>A\<in>\<A>. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology Y TY A). e \<in> T"
        proof (intro ballI)
          fix A e assume "A \<in> \<A>" "e \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
          show "e \<in> T"
          proof (cases "A \<subseteq> T")
            case True
            have "e \<in> A" using \<open>e \<in> top1_arc_endpoints_on A _\<close>
              unfolding top1_arc_endpoints_on_def by (by100 blast)
            thus ?thesis using True by (by100 blast)
          next
            case False
            hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
            thus ?thesis using hNT_endpoints \<open>e \<in> top1_arc_endpoints_on A _\<close> by (by100 blast)
          qed
        qed
        have h\<A>_inter': "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
            A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
          using h\<A>_inter by (by100 blast)
        have hNT_eq: "?NT = {A \<in> \<A>. \<not> A \<subseteq> T}" by (by100 blast)
        have hT_subgraph_impl: "\<forall>A\<in>\<A>. \<not> A \<subseteq> T \<longrightarrow>
            A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
          using hT_subgraph by (by100 blast)
        show ?thesis
          using graph_remove_interior_points_sc[OF hgraph h\<A> h\<A>_cover h\<A>_inter' hT_tree hT_sub
              hT_subgraph hNT_eq hfin hps hvert_T hT_x0 h\<A>_coh] by (by100 blast)
      qed
      \<comment> \<open>Step 6: DR.\<close>
      let ?target_U = "T \<union> A1"
      let ?target_V = "T \<union> \<Union>(?NT - {A1})"
      have hNT_endpoints_all: "\<forall>A\<in>?NT. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology Y TY A). e \<in> T"
        using hNT_endpoints by (by100 blast)
      have hU_dr_raw: "top1_deformation_retract_of_on (Y - ps ` ?S_U) (subspace_topology Y TY (Y - ps ` ?S_U))
          (T \<union> \<Union>(?NT - ?S_U))"
      proof (rule graph_deformation_retract_helper)
        show "top1_is_graph_on Y TY" by (rule hgraph)
        show "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)" by (rule h\<A>)
        show "\<Union>\<A> = Y" by (rule h\<A>_cover)
        show "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
             A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
           \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
           \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" by (rule h\<A>_inter)
        show "\<forall>C. C \<subseteq> Y \<longrightarrow> (closedin_on Y TY C \<longleftrightarrow>
              (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))" by (rule h\<A>_coh)
        show "top1_is_tree_on T (subspace_topology Y TY T)" by (rule hT_tree)
        show "T \<subseteq> Y" by (rule hT_sub)
        show "\<forall>A\<in>\<A>. \<not> A \<subseteq> T \<longrightarrow> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
          using hT_subgraph by (by100 blast)
        show "\<forall>A\<in>?NT. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology Y TY A). e \<in> T"
          by (rule hNT_endpoints_all)
        show "finite ?S_U" using hfin by (by100 blast)
        show "?S_U \<subseteq> ?NT" by (by100 blast)
        show "\<forall>A\<in>?S_U. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
          using hps by (by100 blast)
      qed
      have "?NT - ?S_U = {A1}" using hA1 by (by100 blast)
      hence "T \<union> \<Union>(?NT - ?S_U) = ?target_U" by (by100 simp)
      have hU_dr: "top1_deformation_retract_of_on ?U (subspace_topology Y TY ?U) ?target_U"
        using hU_dr_raw \<open>T \<union> \<Union>(?NT - ?S_U) = ?target_U\<close> by simp
      have hV_dr: "top1_deformation_retract_of_on ?V (subspace_topology Y TY ?V) ?target_V"
      proof (rule graph_deformation_retract_helper)
        show "top1_is_graph_on Y TY" by (rule hgraph)
        show "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)" by (rule h\<A>)
        show "\<Union>\<A> = Y" by (rule h\<A>_cover)
        show "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
             A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
           \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
           \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" by (rule h\<A>_inter)
        show "\<forall>C. C \<subseteq> Y \<longrightarrow> (closedin_on Y TY C \<longleftrightarrow>
              (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))" by (rule h\<A>_coh)
        show "top1_is_tree_on T (subspace_topology Y TY T)" by (rule hT_tree)
        show "T \<subseteq> Y" by (rule hT_sub)
        show "\<forall>A\<in>\<A>. \<not> A \<subseteq> T \<longrightarrow> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
          using hT_subgraph by (by100 blast)
        show "\<forall>A\<in>?NT. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology Y TY A). e \<in> T"
          by (rule hNT_endpoints_all)
        show "finite {A1}" by (by100 simp)
        show "{A1} \<subseteq> ?NT" using hA1 by (by100 blast)
        show "\<forall>A\<in>{A1}. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
          using hps hA1 by (by100 blast)
      qed
      \<comment> \<open>Step 7: Targets graph + connected.\<close>
      \<comment> \<open>Arc infrastructure for A1.\<close>
      have hA1_arc_loc: "top1_is_arc_on A1 (subspace_topology Y TY A1)"
        using h\<A> hA1 by (by100 blast)
      have hA1_sub_loc: "A1 \<subseteq> Y" using h\<A> hA1 by (by100 blast)
      have hA1_endpt_T: "\<exists>e. e \<in> T \<and> e \<in> A1"
      proof -
        obtain hj where hhj: "top1_homeomorphism_on top1_unit_interval
            top1_unit_interval_topology A1 (subspace_topology Y TY A1) hj"
          using hA1_arc_loc unfolding top1_is_arc_on_def by (by100 blast)
        from arc_endpoints_are_boundary[OF hY_strict hY_haus hA1_sub_loc hA1_arc_loc hhj]
        have "top1_arc_endpoints_on A1 (subspace_topology Y TY A1) = {hj 0, hj 1}" .
        have "hj 0 \<in> T"
          using hNT_endpoints[rule_format, OF hA1] \<open>_ = {hj 0, hj 1}\<close> by (by100 simp)
        have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
        have "hj 0 \<in> A1"
          using hhj \<open>(0::real) \<in> _\<close> unfolding top1_homeomorphism_on_def bij_betw_def
          by (by100 blast)
        thus ?thesis using \<open>hj 0 \<in> T\<close> by (by100 blast)
      qed
      \<comment> \<open>Connectivity via tree\\_union\\_arcs\\_path\\_connected.\<close>
      have htU_pc_raw: "top1_path_connected_on ?target_U (subspace_topology Y TY ?target_U)"
      proof -
        from tree_union_arcs_path_connected[OF hTY_top hT_tree hT_sub _
            _ _ hT_x0, of "{A1}"]
        have "top1_path_connected_on (T \<union> \<Union>{A1}) (subspace_topology Y TY (T \<union> \<Union>{A1}))"
          using hA1_arc_loc hA1_sub_loc hA1_endpt_T by (by100 simp)
        thus ?thesis by simp
      qed
      have htU_conn: "top1_connected_on ?target_U (subspace_topology Y TY ?target_U)"
        using htU_pc_raw top1_path_connected_imp_connected by (by100 blast)
      have htV_pc_raw: "top1_path_connected_on ?target_V (subspace_topology Y TY ?target_V)"
      proof -
        have hNT_A1_arcs: "\<forall>A\<in>?NT - {A1}. top1_is_arc_on A (subspace_topology Y TY A) \<and> A \<subseteq> Y"
          using h\<A> by (by100 blast)
        have hNT_A1_endpts: "\<forall>A\<in>?NT - {A1}. \<exists>e. e \<in> T \<and> e \<in> A"
        proof (intro ballI)
          fix A assume "A \<in> ?NT - {A1}"
          hence "A \<in> ?NT" by (by100 blast)
          hence "A \<in> \<A>" by (by100 blast)
          have harc: "top1_is_arc_on A (subspace_topology Y TY A)" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
          obtain hj where hhj: "top1_homeomorphism_on top1_unit_interval
              top1_unit_interval_topology A (subspace_topology Y TY A) hj"
            using harc unfolding top1_is_arc_on_def by (by100 blast)
          from arc_endpoints_are_boundary[OF hY_strict hY_haus _ harc hhj]
          have "top1_arc_endpoints_on A (subspace_topology Y TY A) = {hj 0, hj 1}"
            using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
          have "hj 0 \<in> T"
            using hNT_endpoints[rule_format, OF \<open>A \<in> ?NT\<close>] \<open>_ = {hj 0, hj 1}\<close> by (by100 simp)
          have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
          have "hj 0 \<in> A"
            using hhj \<open>(0::real) \<in> _\<close> unfolding top1_homeomorphism_on_def bij_betw_def
            by (by100 blast)
          thus "\<exists>e. e \<in> T \<and> e \<in> A" using \<open>hj 0 \<in> T\<close> by (by100 blast)
        qed
        have hfin_NTA1: "finite (?NT - {A1})" using hfin by (by100 blast)
        from tree_union_arcs_path_connected[OF hTY_top hT_tree hT_sub hfin_NTA1
            hNT_A1_arcs hNT_A1_endpts hT_x0]
        show ?thesis .
      qed
      have htV_conn: "top1_connected_on ?target_V (subspace_topology Y TY ?target_V)"
        using htV_pc_raw top1_path_connected_imp_connected by (by100 blast)
      \<comment> \<open>Graph structure of targets.\<close>
      have htU_graph: "top1_is_graph_on ?target_U (subspace_topology Y TY ?target_U)"
      proof -
        let ?\<B>U = "{A \<in> \<A>. A \<subseteq> ?target_U}"
        have htU_eq: "?target_U = \<Union>?\<B>U"
        proof (rule graph_connected_sub_covered_by_arcs)
          show "top1_is_graph_on Y TY" by (rule hgraph)
          show "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)" by (rule h\<A>)
          show "\<Union>\<A> = Y" by (rule h\<A>_cover)
          show "\<forall>C. C \<subseteq> Y \<longrightarrow> (closedin_on Y TY C \<longleftrightarrow>
                (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))" by (rule h\<A>_coh)
          show "?target_U \<subseteq> Y" using hT_sub h\<A> hA1 by (by100 blast)
          show "top1_connected_on ?target_U (subspace_topology Y TY ?target_U)" by (rule htU_conn)
          show "\<exists>y1 y2. y1 \<in> ?target_U \<and> y2 \<in> ?target_U \<and> y1 \<noteq> y2"
          proof -
            obtain hh where hhh: "top1_homeomorphism_on top1_unit_interval
                top1_unit_interval_topology A1 (subspace_topology Y TY A1) hh"
              using hA1_arc_loc unfolding top1_is_arc_on_def by (by100 blast)
            have hbij: "bij_betw hh top1_unit_interval A1"
              using hhh unfolding top1_homeomorphism_on_def by (by100 blast)
            have hinj: "inj_on hh top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
            have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have "hh 0 \<in> A1" using hbij h0_I unfolding bij_betw_def by (by100 blast)
            have "hh 1 \<in> A1" using hbij h1_I unfolding bij_betw_def by (by100 blast)
            have "hh 0 \<noteq> hh 1"
            proof
              assume "hh 0 = hh 1"
              from inj_onD[OF hinj this h0_I h1_I] show False by (by100 simp)
            qed
            thus ?thesis using \<open>hh 0 \<in> A1\<close> \<open>hh 1 \<in> A1\<close> by (by100 blast)
          qed
          show "\<forall>A\<in>\<A>. \<not> A \<subseteq> ?target_U \<longrightarrow> finite (A \<inter> ?target_U)"
          proof (intro ballI impI)
            fix A assume "A \<in> \<A>" "\<not> A \<subseteq> ?target_U"
            have "A \<inter> ?target_U \<subseteq> A \<inter> T \<union> (A \<inter> A1)" by (by100 blast)
            have "\<not> A \<subseteq> T" using \<open>\<not> A \<subseteq> ?target_U\<close> by (by100 blast)
            have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              using hT_subgraph \<open>A \<in> \<A>\<close> \<open>\<not> A \<subseteq> T\<close> by (by100 blast)
            have "finite (top1_arc_endpoints_on A (subspace_topology Y TY A))"
            proof -
              obtain h where hh: "top1_homeomorphism_on top1_unit_interval
                  top1_unit_interval_topology A (subspace_topology Y TY A) h"
                using h\<A> \<open>A \<in> \<A>\<close> unfolding top1_is_arc_on_def by (by100 blast)
              from arc_endpoints_are_boundary[OF hY_strict hY_haus _ _ hh]
              show ?thesis using h\<A> \<open>A \<in> \<A>\<close> by (by100 simp)
            qed
            have "finite (A \<inter> T)" using \<open>A \<inter> T \<subseteq> top1_arc_endpoints_on A _\<close>
              \<open>finite (top1_arc_endpoints_on A _)\<close> finite_subset by (by100 blast)
            have "A \<noteq> A1" using \<open>\<not> A \<subseteq> ?target_U\<close> by (by100 blast)
            have "A \<inter> A1 \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              using h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> _ \<open>A \<noteq> A1\<close>] hA1 by (by100 blast)
            hence "finite (A \<inter> A1)" using \<open>finite (top1_arc_endpoints_on A _)\<close>
              finite_subset by (by100 blast)
            thus "finite (A \<inter> ?target_U)"
              using \<open>finite (A \<inter> T)\<close> \<open>finite (A \<inter> A1)\<close>
              \<open>A \<inter> ?target_U \<subseteq> A \<inter> T \<union> (A \<inter> A1)\<close> finite_subset finite_UnI by (by100 blast)
          qed
          show "finite {A \<in> \<A>. \<not> A \<subseteq> ?target_U}"
          proof -
            have "{A \<in> \<A>. \<not> A \<subseteq> ?target_U} \<subseteq> ?NT - {A1}" by (by100 blast)
            thus ?thesis using hfin finite_subset by (by100 blast)
          qed
        qed
        have hBU_arcs: "\<forall>A\<in>?\<B>U. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
          using h\<A> by (by100 blast)
        have hBU_cover: "\<Union>?\<B>U \<subseteq> Y" using h\<A> by (by100 blast)
        have hBU_inter: "\<forall>A\<in>?\<B>U. \<forall>B\<in>?\<B>U. A \<noteq> B \<longrightarrow>
            A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A) \<and>
            A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B) \<and>
            finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
          using h\<A>_inter by (by100 blast)
        have hBU_coh: "\<forall>C. C \<subseteq> ?target_U \<longrightarrow>
            (closedin_on ?target_U (subspace_topology Y TY ?target_U) C \<longleftrightarrow>
             (\<forall>A\<in>?\<B>U. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
        proof (rule subgraph_coherent_topology)
          show "top1_is_graph_on Y TY" by (rule hgraph)
          show "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)" by (rule h\<A>)
          show "\<Union>\<A> = Y" by (rule h\<A>_cover)
          show "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
               A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
             \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
             \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" by (rule h\<A>_inter)
          show "\<forall>C. C \<subseteq> Y \<longrightarrow> (closedin_on Y TY C \<longleftrightarrow>
                (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))" by (rule h\<A>_coh)
          show "?\<B>U \<subseteq> \<A>" by (by100 blast)
          show "?target_U = \<Union>?\<B>U" by (rule htU_eq)
        qed
        from subgraph_union_of_arcs_is_graph[OF hgraph hBU_arcs hBU_cover hBU_inter]
        have "top1_is_graph_on (\<Union>?\<B>U) (subspace_topology Y TY (\<Union>?\<B>U))"
          using hBU_coh htU_eq by simp
        thus ?thesis using htU_eq by simp
      qed
      have htV_graph: "top1_is_graph_on ?target_V (subspace_topology Y TY ?target_V)"
      proof -
        let ?\<B>V = "{A \<in> \<A>. A \<subseteq> ?target_V}"
        have htV_eq: "?target_V = \<Union>?\<B>V"
        proof (rule graph_connected_sub_covered_by_arcs)
          show "top1_is_graph_on Y TY" by (rule hgraph)
          show "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)" by (rule h\<A>)
          show "\<Union>\<A> = Y" by (rule h\<A>_cover)
          show "\<forall>C. C \<subseteq> Y \<longrightarrow> (closedin_on Y TY C \<longleftrightarrow>
                (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))" by (rule h\<A>_coh)
          show "?target_V \<subseteq> Y" using hT_sub h\<A> by (by100 blast)
          show "top1_connected_on ?target_V (subspace_topology Y TY ?target_V)" by (rule htV_conn)
          show "\<exists>y1 y2. y1 \<in> ?target_V \<and> y2 \<in> ?target_V \<and> y1 \<noteq> y2"
          proof -
            \<comment> \<open>A1 has 2 distinct endpoints in T \\<subseteq> target\\_V.\<close>
            obtain hh where hhh: "top1_homeomorphism_on top1_unit_interval
                top1_unit_interval_topology A1 (subspace_topology Y TY A1) hh"
              using hA1_arc_loc unfolding top1_is_arc_on_def by (by100 blast)
            have hbij: "bij_betw hh top1_unit_interval A1"
              using hhh unfolding top1_homeomorphism_on_def by (by100 blast)
            have hinj: "inj_on hh top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
            have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            from arc_endpoints_are_boundary[OF hY_strict hY_haus hA1_sub_loc hA1_arc_loc hhh]
            have hep_hh: "top1_arc_endpoints_on A1 (subspace_topology Y TY A1) = {hh 0, hh 1}" .
            have "hh 0 \<in> T" using hNT_endpoints[rule_format, OF hA1] hep_hh by (by100 simp)
            have "hh 1 \<in> T" using hNT_endpoints[rule_format, OF hA1] hep_hh by (by100 simp)
            have "hh 0 \<noteq> hh 1"
            proof
              assume "hh 0 = hh 1"
              from inj_onD[OF hinj this h0_I h1_I] show False by (by100 simp)
            qed
            thus ?thesis using \<open>hh 0 \<in> T\<close> \<open>hh 1 \<in> T\<close> by (by100 blast)
          qed
          show "\<forall>A\<in>\<A>. \<not> A \<subseteq> ?target_V \<longrightarrow> finite (A \<inter> ?target_V)"
          proof (intro ballI impI)
            fix A assume "A \<in> \<A>" "\<not> A \<subseteq> ?target_V"
            hence "A = A1"
            proof -
              have "\<not> A \<subseteq> T" using \<open>\<not> A \<subseteq> ?target_V\<close> by (by100 blast)
              hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
              have "A \<notin> ?NT - {A1}" using \<open>\<not> A \<subseteq> ?target_V\<close> by (by100 blast)
              thus "A = A1" using \<open>A \<in> ?NT\<close> by (by100 blast)
            qed
            have "A \<inter> ?target_V \<subseteq> (A \<inter> T) \<union> (A \<inter> \<Union>(?NT - {A1}))" by (by100 blast)
            have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              using hT_subgraph \<open>A \<in> \<A>\<close> \<open>\<not> A \<subseteq> ?target_V\<close> by (by100 blast)
            have "finite (top1_arc_endpoints_on A (subspace_topology Y TY A))"
            proof -
              obtain h where hh: "top1_homeomorphism_on top1_unit_interval
                  top1_unit_interval_topology A (subspace_topology Y TY A) h"
                using h\<A> \<open>A \<in> \<A>\<close> unfolding top1_is_arc_on_def by (by100 blast)
              from arc_endpoints_are_boundary[OF hY_strict hY_haus _ _ hh]
              show ?thesis using h\<A> \<open>A \<in> \<A>\<close> by (by100 simp)
            qed
            have "finite (A \<inter> T)" using \<open>A \<inter> T \<subseteq> top1_arc_endpoints_on A _\<close>
              \<open>finite (top1_arc_endpoints_on A _)\<close> finite_subset by (by100 blast)
            have "\<forall>B\<in>?NT - {A1}. finite (A \<inter> B)"
            proof (intro ballI)
              fix B assume "B \<in> ?NT - {A1}"
              hence "B \<in> \<A>" by (by100 blast)
              have "A \<noteq> B" using \<open>A = A1\<close> \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
              from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
              show "finite (A \<inter> B)" by (by100 blast)
            qed
            have "finite (?NT - {A1})" using hfin by (by100 blast)
            have "finite (A \<inter> \<Union>(?NT - {A1}))"
            proof -
              have "finite ((\<lambda>B. A \<inter> B) ` (?NT - {A1}))"
                using \<open>finite (?NT - {A1})\<close> by (by100 simp)
              moreover have "\<forall>S\<in>(\<lambda>B. A \<inter> B) ` (?NT - {A1}). finite S"
                using \<open>\<forall>B\<in>?NT - {A1}. finite (A \<inter> B)\<close> by (by100 blast)
              ultimately have "finite (\<Union>((\<lambda>B. A \<inter> B) ` (?NT - {A1})))"
                using finite_Union by (by100 blast)
              moreover have "\<Union>((\<lambda>B. A \<inter> B) ` (?NT - {A1})) = A \<inter> \<Union>(?NT - {A1})"
                by (by100 blast)
              ultimately show ?thesis by (by100 simp)
            qed
            show "finite (A \<inter> ?target_V)"
            proof -
              have "A \<inter> ?target_V \<subseteq> (A \<inter> T) \<union> (A \<inter> \<Union>(?NT - {A1}))" by (by100 blast)
              thus ?thesis using \<open>finite (A \<inter> T)\<close> \<open>finite (A \<inter> \<Union>(?NT - {A1}))\<close>
                finite_subset finite_UnI by (by100 blast)
            qed
          qed
          show "finite {A \<in> \<A>. \<not> A \<subseteq> ?target_V}"
          proof -
            have "{A \<in> \<A>. \<not> A \<subseteq> ?target_V} \<subseteq> {A1}" by (by100 blast)
            thus ?thesis using finite_subset by (by100 blast)
          qed
        qed
        have hBV_arcs: "\<forall>A\<in>?\<B>V. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)"
          using h\<A> by (by100 blast)
        have hBV_cover: "\<Union>?\<B>V \<subseteq> Y" using h\<A> by (by100 blast)
        have hBV_inter: "\<forall>A\<in>?\<B>V. \<forall>B\<in>?\<B>V. A \<noteq> B \<longrightarrow>
            A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A) \<and>
            A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B) \<and>
            finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
        proof (intro ballI impI)
          fix A B assume "A \<in> ?\<B>V" "B \<in> ?\<B>V" "A \<noteq> B"
          from h\<A>_inter[rule_format, OF _ _ \<open>A \<noteq> B\<close>]
          show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A) \<and>
              A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B) \<and>
              finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
            using \<open>A \<in> ?\<B>V\<close> \<open>B \<in> ?\<B>V\<close> by (by100 blast)
        qed
        have hBV_coh: "\<forall>C. C \<subseteq> ?target_V \<longrightarrow>
            (closedin_on ?target_V (subspace_topology Y TY ?target_V) C \<longleftrightarrow>
             (\<forall>A\<in>?\<B>V. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
        proof (rule subgraph_coherent_topology)
          show "top1_is_graph_on Y TY" by (rule hgraph)
          show "\<forall>A\<in>\<A>. A \<subseteq> Y \<and> top1_is_arc_on A (subspace_topology Y TY A)" by (rule h\<A>)
          show "\<Union>\<A> = Y" by (rule h\<A>_cover)
          show "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
               A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
             \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
             \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" by (rule h\<A>_inter)
          show "\<forall>C. C \<subseteq> Y \<longrightarrow> (closedin_on Y TY C \<longleftrightarrow>
                (\<forall>A\<in>\<A>. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))" by (rule h\<A>_coh)
          show "?\<B>V \<subseteq> \<A>" by (by100 blast)
          show "?target_V = \<Union>?\<B>V" by (rule htV_eq)
        qed
        from subgraph_union_of_arcs_is_graph[OF hgraph hBV_arcs hBV_cover hBV_inter]
        have "top1_is_graph_on (\<Union>?\<B>V) (subspace_topology Y TY (\<Union>?\<B>V))"
          using hBV_coh htV_eq by simp
        thus ?thesis using htV_eq by simp
      qed
      \<comment> \<open>Step 8: IH — \\<pi>\\_1 of targets is free.\<close>
      have htU_free: "\<exists>(\<iota>::nat \<Rightarrow> _) (S::nat set). top1_is_free_group_full_on
          (top1_fundamental_group_carrier ?target_U (subspace_topology Y TY ?target_U) y0)
          (top1_fundamental_group_mul ?target_U (subspace_topology Y TY ?target_U) y0)
          (top1_fundamental_group_id ?target_U (subspace_topology Y TY ?target_U) y0)
          (top1_fundamental_group_invg ?target_U (subspace_topology Y TY ?target_U) y0)
          \<iota> S"
      proof -
        let ?\<A>_U = "{A\<in>\<A>. A \<subseteq> ?target_U}"
        let ?TY_U = "subspace_topology Y TY ?target_U"
        note q1 = htU_graph
        note q2 = htU_conn
        have q3: "y0 \<in> ?target_U" using hT_x0 by (by100 blast)
        have hNT_U: "{A\<in>?\<A>_U. \<not> A \<subseteq> T} = {A1}"
        proof (rule set_eqI, rule iffI)
          fix A assume "A \<in> {A\<in>?\<A>_U. \<not> A \<subseteq> T}"
          hence "A \<in> \<A>" "A \<subseteq> T \<union> A1" "\<not> A \<subseteq> T" by (by100 blast)+
          hence "A \<in> ?NT" by (by100 blast)
          show "A \<in> {A1}"
          proof (rule ccontr)
            assume "A \<notin> {A1}" hence "A \<noteq> A1" by (by100 blast)
            have "A1 \<in> \<A>" using hA1 by (by100 blast)
            from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A1 \<in> \<A>\<close> \<open>A \<noteq> A1\<close>]
            have "A \<inter> A1 \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)" by (by100 blast)
            have "A \<inter> A1 \<subseteq> T" using \<open>A \<inter> A1 \<subseteq> _\<close> hNT_endpoints \<open>A \<in> ?NT\<close> by (by100 blast)
            have "A \<subseteq> T"
            proof
              fix x assume "x \<in> A"
              show "x \<in> T"
              proof (cases "x \<in> A1")
                case True thus ?thesis using \<open>x \<in> A\<close> \<open>A \<inter> A1 \<subseteq> T\<close> by (by100 blast)
              next
                case False thus ?thesis using \<open>x \<in> A\<close> \<open>A \<subseteq> T \<union> A1\<close> by (by100 blast)
              qed
            qed
            thus False using \<open>\<not> A \<subseteq> T\<close> by contradiction
          qed
        next
          fix A assume "A \<in> {A1}" thus "A \<in> {A\<in>?\<A>_U. \<not> A \<subseteq> T}" using hA1 by (by100 blast)
        qed
        have q4: "card {A\<in>?\<A>_U. \<not> A \<subseteq> T} \<le> n"
          using hNT_U hn_ge1 by (by100 simp)
        have q5: "finite {A\<in>?\<A>_U. \<not> A \<subseteq> T}" using hNT_U by (by100 simp)
        have q6: "\<forall>A\<in>?\<A>_U. A \<subseteq> ?target_U \<and> top1_is_arc_on A (subspace_topology ?target_U ?TY_U A)"
        proof (intro ballI conjI)
          fix A assume "A \<in> ?\<A>_U"
          show "A \<subseteq> ?target_U" using \<open>A \<in> ?\<A>_U\<close> by (by100 blast)
          have "A \<in> \<A>" using \<open>A \<in> ?\<A>_U\<close> by (by100 blast)
          have "A \<subseteq> ?target_U" using \<open>A \<in> ?\<A>_U\<close> by (by100 blast)
          have "subspace_topology ?target_U ?TY_U A = subspace_topology Y TY A"
            by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?target_U\<close>])
          thus "top1_is_arc_on A (subspace_topology ?target_U ?TY_U A)"
            using h\<A> \<open>A \<in> \<A>\<close> by simp
        qed
        have htU_eq_ext: "?target_U = \<Union>?\<A>_U"
        proof (rule graph_connected_sub_covered_by_arcs[OF hgraph h\<A> h\<A>_cover h\<A>_coh])
          show "?target_U \<subseteq> Y" using hT_sub h\<A> hA1 by (by100 blast)
          show "top1_connected_on ?target_U ?TY_U" by (rule htU_conn)
          show "\<exists>y1 y2. y1 \<in> ?target_U \<and> y2 \<in> ?target_U \<and> y1 \<noteq> y2"
          proof -
            obtain hh where hhh: "top1_homeomorphism_on top1_unit_interval
                top1_unit_interval_topology A1 (subspace_topology Y TY A1) hh"
              using hA1_arc_loc unfolding top1_is_arc_on_def by (by100 blast)
            from arc_endpoints_are_boundary[OF hY_strict hY_haus hA1_sub_loc hA1_arc_loc hhh]
            have hep: "top1_arc_endpoints_on A1 (subspace_topology Y TY A1) = {hh 0, hh 1}" .
            have hbij: "bij_betw hh top1_unit_interval A1"
              using hhh unfolding top1_homeomorphism_on_def by (by100 blast)
            have hinj: "inj_on hh top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
            have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have "hh 0 \<in> A1" using hbij h0_I unfolding bij_betw_def by (by100 blast)
            have "hh 1 \<in> A1" using hbij h1_I unfolding bij_betw_def by (by100 blast)
            have "hh 0 \<noteq> hh 1"
            proof
              assume "hh 0 = hh 1"
              from inj_onD[OF hinj this h0_I h1_I] show False by (by100 simp)
            qed
            thus ?thesis using \<open>hh 0 \<in> A1\<close> \<open>hh 1 \<in> A1\<close> by (by100 blast)
          qed
          show "\<forall>A\<in>\<A>. \<not> A \<subseteq> ?target_U \<longrightarrow> finite (A \<inter> ?target_U)"
          proof (intro ballI impI)
            fix A assume "A \<in> \<A>" "\<not> A \<subseteq> ?target_U"
            have "\<not> A \<subseteq> T" using \<open>\<not> A \<subseteq> ?target_U\<close> by (by100 blast)
            have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              using hT_subgraph \<open>A \<in> \<A>\<close> \<open>\<not> A \<subseteq> T\<close> by (by100 blast)
            have "finite (top1_arc_endpoints_on A (subspace_topology Y TY A))"
            proof -
              obtain h where hh: "top1_homeomorphism_on top1_unit_interval
                  top1_unit_interval_topology A (subspace_topology Y TY A) h"
                using h\<A> \<open>A \<in> \<A>\<close> unfolding top1_is_arc_on_def by (by100 blast)
              from arc_endpoints_are_boundary[OF hY_strict hY_haus _ _ hh]
              show ?thesis using h\<A> \<open>A \<in> \<A>\<close> by (by100 simp)
            qed
            have "finite (A \<inter> T)"
              using \<open>A \<inter> T \<subseteq> top1_arc_endpoints_on A _\<close>
              \<open>finite (top1_arc_endpoints_on A _)\<close> finite_subset by (by100 blast)
            have "A \<noteq> A1" using \<open>\<not> A \<subseteq> ?target_U\<close> by (by100 blast)
            have "A \<inter> A1 \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              using h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> _ \<open>A \<noteq> A1\<close>] hA1 by (by100 blast)
            hence "finite (A \<inter> A1)" using \<open>finite (top1_arc_endpoints_on A _)\<close>
              finite_subset by (by100 blast)
            show "finite (A \<inter> ?target_U)"
            proof -
              have "A \<inter> ?target_U \<subseteq> (A \<inter> T) \<union> (A \<inter> A1)" by (by100 blast)
              thus ?thesis using \<open>finite (A \<inter> T)\<close> \<open>finite (A \<inter> A1)\<close>
                finite_subset finite_UnI by (by100 blast)
            qed
          qed
          show "finite {A \<in> \<A>. \<not> A \<subseteq> ?target_U}"
          proof -
            have "{A \<in> \<A>. \<not> A \<subseteq> ?target_U} \<subseteq> ?NT - {A1}" by (by100 blast)
            thus ?thesis using hfin finite_subset by (by100 blast)
          qed
        qed
        have q7: "\<Union>?\<A>_U = ?target_U" using htU_eq_ext by simp
        have q8: "\<forall>A\<in>?\<A>_U. \<forall>B\<in>?\<A>_U. A \<noteq> B \<longrightarrow>
            A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?target_U ?TY_U A)
          \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?target_U ?TY_U B)
          \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
        proof (intro ballI impI)
          fix A B assume "A \<in> ?\<A>_U" "B \<in> ?\<A>_U" "A \<noteq> B"
          hence "A \<in> \<A>" "B \<in> \<A>" by (by100 blast)+
          from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
          have hAB: "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
            \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
            \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" .
          have "A \<subseteq> ?target_U" using \<open>A \<in> ?\<A>_U\<close> by (by100 blast)
          have "B \<subseteq> ?target_U" using \<open>B \<in> ?\<A>_U\<close> by (by100 blast)
          show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?target_U ?TY_U A) \<and>
              A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?target_U ?TY_U B) \<and>
              finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
            using hAB subspace_topology_trans[OF \<open>A \<subseteq> ?target_U\<close>]
              subspace_topology_trans[OF \<open>B \<subseteq> ?target_U\<close>] by simp
        qed
        have q9: "\<forall>C. C \<subseteq> ?target_U \<longrightarrow>
            (closedin_on ?target_U ?TY_U C \<longleftrightarrow>
             (\<forall>A\<in>?\<A>_U. closedin_on A (subspace_topology ?target_U ?TY_U A) (A \<inter> C)))"
        proof -
          from subgraph_coherent_topology[OF hgraph h\<A> h\<A>_cover h\<A>_inter h\<A>_coh]
          have hcoh_raw: "\<forall>C. C \<subseteq> ?target_U \<longrightarrow>
              (closedin_on ?target_U (subspace_topology Y TY ?target_U) C \<longleftrightarrow>
               (\<forall>A\<in>?\<A>_U. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
          proof -
            have "?\<A>_U \<subseteq> \<A>" by (by100 blast)
            from subgraph_coherent_topology[OF hgraph h\<A> h\<A>_cover h\<A>_inter h\<A>_coh this htU_eq_ext]
            show ?thesis .
          qed
          show ?thesis
          proof (intro allI impI iffI ballI)
            fix C A
            assume hC: "C \<subseteq> ?target_U"
              and "closedin_on ?target_U ?TY_U C" and "A \<in> ?\<A>_U"
            have "A \<subseteq> ?target_U" using \<open>A \<in> ?\<A>_U\<close> by (by100 blast)
            from hcoh_raw[rule_format, OF hC] \<open>closedin_on ?target_U ?TY_U C\<close>
            have "\<forall>A\<in>?\<A>_U. closedin_on A (subspace_topology Y TY A) (A \<inter> C)" by simp
            thus "closedin_on A (subspace_topology ?target_U ?TY_U A) (A \<inter> C)"
              using \<open>A \<in> ?\<A>_U\<close> subspace_topology_trans[OF \<open>A \<subseteq> ?target_U\<close>] by simp
          next
            fix C
            assume hC: "C \<subseteq> ?target_U"
              and hall: "\<forall>A\<in>?\<A>_U. closedin_on A (subspace_topology ?target_U ?TY_U A) (A \<inter> C)"
            have "\<forall>A\<in>?\<A>_U. closedin_on A (subspace_topology Y TY A) (A \<inter> C)"
            proof (intro ballI)
              fix A assume "A \<in> ?\<A>_U"
              have "A \<subseteq> ?target_U" using \<open>A \<in> ?\<A>_U\<close> by (by100 blast)
              from hall[rule_format, OF \<open>A \<in> ?\<A>_U\<close>]
              show "closedin_on A (subspace_topology Y TY A) (A \<inter> C)"
                using subspace_topology_trans[OF \<open>A \<subseteq> ?target_U\<close>] by simp
            qed
            from hcoh_raw[rule_format, OF hC, THEN iffD2, OF this]
            show "closedin_on ?target_U ?TY_U C" by simp
          qed
        qed
        have q10: "top1_is_tree_on T (subspace_topology ?target_U ?TY_U T)"
          using hT_tree subspace_topology_trans[of T ?target_U Y TY] by (by100 simp)
        have q11: "T \<subseteq> ?target_U" by (by100 blast)
        have q12: "\<forall>A\<in>?\<A>_U. A \<subseteq> T \<or>
            A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?target_U ?TY_U A)"
        proof (intro ballI)
          fix A assume "A \<in> ?\<A>_U"
          hence "A \<in> \<A>" "A \<subseteq> ?target_U" by (by100 blast)+
          from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>]
          show "A \<subseteq> T \<or> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?target_U ?TY_U A)"
            using subspace_topology_trans[OF \<open>A \<subseteq> ?target_U\<close>] by simp
        qed
        have q13: "y0 \<in> T" by (rule hT_x0)
        have q14: "\<forall>A\<in>{A\<in>?\<A>_U. \<not> A \<subseteq> T}. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology ?target_U ?TY_U A). e \<in> T"
        proof (intro ballI)
          fix A e assume "A \<in> {A\<in>?\<A>_U. \<not> A \<subseteq> T}"
              and "e \<in> top1_arc_endpoints_on A (subspace_topology ?target_U ?TY_U A)"
          hence "A \<in> \<A>" "\<not> A \<subseteq> T" "A \<subseteq> ?target_U" by (by100 blast)+
          hence "A \<in> ?NT" by (by100 blast)
          have "subspace_topology ?target_U ?TY_U A = subspace_topology Y TY A"
            by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?target_U\<close>])
          hence "e \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
            using \<open>e \<in> _\<close> by simp
          thus "e \<in> T" using hNT_endpoints[rule_format, OF \<open>A \<in> ?NT\<close>] by (by100 blast)
        qed
        show ?thesis
          by (rule IH[OF q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14])
      qed
      have htV_free: "\<exists>(\<iota>::nat \<Rightarrow> _) (S::nat set). top1_is_free_group_full_on
          (top1_fundamental_group_carrier ?target_V (subspace_topology Y TY ?target_V) y0)
          (top1_fundamental_group_mul ?target_V (subspace_topology Y TY ?target_V) y0)
          (top1_fundamental_group_id ?target_V (subspace_topology Y TY ?target_V) y0)
          (top1_fundamental_group_invg ?target_V (subspace_topology Y TY ?target_V) y0)
          \<iota> S"
      proof -
        let ?\<A>_V = "{A\<in>\<A>. A \<subseteq> ?target_V}"
        let ?TY_V = "subspace_topology Y TY ?target_V"
        \<comment> \<open>Premise 1: graph.\<close>
        note p1 = htV_graph
        \<comment> \<open>Premise 2: connected.\<close>
        note p2 = htV_conn
        \<comment> \<open>Premise 3: y0 \\<in> target\\_V.\<close>
        have p3: "y0 \<in> ?target_V" using hT_x0 by (by100 blast)
        \<comment> \<open>Premise 4: card \\<le> n.\<close>
        have hNT_V: "{A\<in>?\<A>_V. \<not> A \<subseteq> T} = ?NT - {A1}"
        proof (rule set_eqI, rule iffI)
          fix A assume "A \<in> {A\<in>?\<A>_V. \<not> A \<subseteq> T}"
          hence "A \<in> \<A>" "A \<subseteq> ?target_V" "\<not> A \<subseteq> T" by (by100 blast)+
          hence "A \<in> ?NT" by (by100 blast)
          moreover have "A \<noteq> A1"
          proof
            assume "A = A1"
            hence "A1 \<subseteq> ?target_V" using \<open>A \<subseteq> ?target_V\<close> by simp
            \<comment> \<open>ps(A1) is an interior point of A1, not in T or other arcs.\<close>
            have "ps A1 \<in> A1" using hps hA1 by (by100 blast)
            have "ps A1 \<notin> top1_arc_endpoints_on A1 (subspace_topology Y TY A1)"
              using hps hA1 by (by100 blast)
            have "ps A1 \<notin> T"
            proof -
              have "A1 \<inter> T \<subseteq> top1_arc_endpoints_on A1 (subspace_topology Y TY A1)"
                using hT_subgraph hA1 by (by100 blast)
              thus ?thesis using \<open>ps A1 \<in> A1\<close> \<open>ps A1 \<notin> top1_arc_endpoints_on A1 _\<close>
                by (by100 blast)
            qed
            have "ps A1 \<notin> \<Union>(?NT - {A1})"
            proof
              assume "ps A1 \<in> \<Union>(?NT - {A1})"
              then obtain B where "B \<in> ?NT - {A1}" "ps A1 \<in> B" by (by100 blast)
              have "B \<in> \<A>" using \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
              have "B \<noteq> A1" using \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
              have "A1 \<in> \<A>" using hA1 by (by100 blast)
              from h\<A>_inter[rule_format, OF \<open>A1 \<in> \<A>\<close> \<open>B \<in> \<A>\<close>]
              have "A1 \<inter> B \<subseteq> top1_arc_endpoints_on A1 (subspace_topology Y TY A1)"
                using \<open>B \<noteq> A1\<close> by (by100 blast)
              hence "ps A1 \<in> top1_arc_endpoints_on A1 (subspace_topology Y TY A1)"
                using \<open>ps A1 \<in> A1\<close> \<open>ps A1 \<in> B\<close> by (by100 blast)
              thus False using \<open>ps A1 \<notin> top1_arc_endpoints_on A1 _\<close> by (by100 blast)
            qed
            have "ps A1 \<notin> ?target_V" using \<open>ps A1 \<notin> T\<close> \<open>ps A1 \<notin> \<Union>(?NT - {A1})\<close>
              by (by100 blast)
            thus False using \<open>A1 \<subseteq> ?target_V\<close> \<open>ps A1 \<in> A1\<close> by (by100 blast)
          qed
          ultimately show "A \<in> ?NT - {A1}" by (by100 blast)
        next
          fix A assume "A \<in> ?NT - {A1}"
          hence "A \<in> \<A>" "\<not> A \<subseteq> T" "A \<noteq> A1" by (by100 blast)+
          have "A \<in> ?NT" using \<open>A \<in> \<A>\<close> \<open>\<not> A \<subseteq> T\<close> by (by100 blast)
          have "A \<subseteq> ?target_V" using \<open>A \<in> ?NT - {A1}\<close> by (by100 blast)
          thus "A \<in> {A\<in>?\<A>_V. \<not> A \<subseteq> T}" using \<open>A \<in> \<A>\<close> \<open>\<not> A \<subseteq> T\<close> \<open>A \<subseteq> ?target_V\<close>
            by (by100 blast)
        qed
        have p4: "card {A\<in>?\<A>_V. \<not> A \<subseteq> T} \<le> n"
        proof -
          have "card (?NT - {A1}) = card ?NT - 1"
            using hfin hA1 by (by100 simp)
          moreover have "card ?NT \<le> Suc n" using hcard_suc .
          ultimately show ?thesis using hNT_V by (by100 simp)
        qed
        \<comment> \<open>Premise 5: finite.\<close>
        have p5: "finite {A\<in>?\<A>_V. \<not> A \<subseteq> T}"
          using hNT_V hfin by (by100 simp)
        \<comment> \<open>Premises 6-14: arc structure of target\\_V.\<close>
        \<comment> \<open>Premise 6: arcs of target\\_V.\<close>
        have p6: "\<forall>A\<in>?\<A>_V. A \<subseteq> ?target_V \<and> top1_is_arc_on A (subspace_topology ?target_V ?TY_V A)"
        proof (intro ballI conjI)
          fix A assume "A \<in> ?\<A>_V"
          hence "A \<in> \<A>" "A \<subseteq> ?target_V" by (by100 blast)+
          show "A \<subseteq> ?target_V" using \<open>A \<subseteq> ?target_V\<close> .
          have "top1_is_arc_on A (subspace_topology Y TY A)" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
          have "subspace_topology ?target_V ?TY_V A = subspace_topology Y TY A"
            by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?target_V\<close>])
          thus "top1_is_arc_on A (subspace_topology ?target_V ?TY_V A)"
            using \<open>top1_is_arc_on A (subspace_topology Y TY A)\<close> by simp
        qed
        \<comment> \<open>Premise 7: cover.\<close>
        have htV_eq_ext: "?target_V = \<Union>?\<A>_V"
        proof (rule graph_connected_sub_covered_by_arcs[OF hgraph h\<A> h\<A>_cover h\<A>_coh])
          show "?target_V \<subseteq> Y" using hT_sub h\<A> by (by100 blast)
          show "top1_connected_on ?target_V ?TY_V" by (rule htV_conn)
          show "\<exists>y1 y2. y1 \<in> ?target_V \<and> y2 \<in> ?target_V \<and> y1 \<noteq> y2"
          proof -
            obtain hh where hhh: "top1_homeomorphism_on top1_unit_interval
                top1_unit_interval_topology A1 (subspace_topology Y TY A1) hh"
              using hA1_arc_loc unfolding top1_is_arc_on_def by (by100 blast)
            from arc_endpoints_are_boundary[OF hY_strict hY_haus hA1_sub_loc hA1_arc_loc hhh]
            have hep: "top1_arc_endpoints_on A1 (subspace_topology Y TY A1) = {hh 0, hh 1}" .
            have "hh 0 \<in> T" using hNT_endpoints[rule_format, OF hA1] hep by (by100 simp)
            have "hh 1 \<in> T" using hNT_endpoints[rule_format, OF hA1] hep by (by100 simp)
            have hbij: "bij_betw hh top1_unit_interval A1"
              using hhh unfolding top1_homeomorphism_on_def by (by100 blast)
            have hinj: "inj_on hh top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
            have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
            have "hh 0 \<noteq> hh 1"
            proof
              assume "hh 0 = hh 1"
              from inj_onD[OF hinj this h0_I h1_I] show False by (by100 simp)
            qed
            thus ?thesis using \<open>hh 0 \<in> T\<close> \<open>hh 1 \<in> T\<close> by (by100 blast)
          qed
          show "\<forall>A\<in>\<A>. \<not> A \<subseteq> ?target_V \<longrightarrow> finite (A \<inter> ?target_V)"
          proof (intro ballI impI)
            fix A assume "A \<in> \<A>" "\<not> A \<subseteq> ?target_V"
            hence "A = A1"
            proof -
              have "\<not> A \<subseteq> T" using \<open>\<not> A \<subseteq> ?target_V\<close> by (by100 blast)
              hence "A \<in> ?NT" using \<open>A \<in> \<A>\<close> by (by100 blast)
              have "A \<notin> ?NT - {A1}" using \<open>\<not> A \<subseteq> ?target_V\<close> by (by100 blast)
              thus "A = A1" using \<open>A \<in> ?NT\<close> by (by100 blast)
            qed
            have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              using hT_subgraph \<open>A \<in> \<A>\<close> \<open>\<not> A \<subseteq> ?target_V\<close> by (by100 blast)
            have "finite (top1_arc_endpoints_on A (subspace_topology Y TY A))"
            proof -
              obtain h where hh: "top1_homeomorphism_on top1_unit_interval
                  top1_unit_interval_topology A (subspace_topology Y TY A) h"
                using h\<A> \<open>A \<in> \<A>\<close> unfolding top1_is_arc_on_def by (by100 blast)
              from arc_endpoints_are_boundary[OF hY_strict hY_haus _ _ hh]
              show ?thesis using h\<A> \<open>A \<in> \<A>\<close> by (by100 simp)
            qed
            have "finite (A \<inter> T)"
              using \<open>A \<inter> T \<subseteq> top1_arc_endpoints_on A _\<close>
              \<open>finite (top1_arc_endpoints_on A _)\<close> finite_subset by (by100 blast)
            have "\<forall>B\<in>?NT - {A1}. finite (A \<inter> B)"
            proof (intro ballI)
              fix B assume "B \<in> ?NT - {A1}"
              hence "B \<in> \<A>" by (by100 blast)
              have "A \<noteq> B" using \<open>A = A1\<close> \<open>B \<in> ?NT - {A1}\<close> by (by100 blast)
              from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
              show "finite (A \<inter> B)" by (by100 blast)
            qed
            have "finite (?NT - {A1})" using hfin by (by100 blast)
            have "finite (A \<inter> \<Union>(?NT - {A1}))"
            proof -
              have "finite ((\<lambda>B. A \<inter> B) ` (?NT - {A1}))"
                using \<open>finite (?NT - {A1})\<close> by (by100 simp)
              moreover have "\<forall>S\<in>(\<lambda>B. A \<inter> B) ` (?NT - {A1}). finite S"
                using \<open>\<forall>B\<in>?NT - {A1}. finite (A \<inter> B)\<close> by (by100 blast)
              ultimately have "finite (\<Union>((\<lambda>B. A \<inter> B) ` (?NT - {A1})))"
                using finite_Union by (by100 blast)
              moreover have "\<Union>((\<lambda>B. A \<inter> B) ` (?NT - {A1})) = A \<inter> \<Union>(?NT - {A1})"
                by (by100 blast)
              ultimately show ?thesis by (by100 simp)
            qed
            show "finite (A \<inter> ?target_V)"
            proof -
              have "A \<inter> ?target_V \<subseteq> (A \<inter> T) \<union> (A \<inter> \<Union>(?NT - {A1}))" by (by100 blast)
              thus ?thesis using \<open>finite (A \<inter> T)\<close> \<open>finite (A \<inter> \<Union>(?NT - {A1}))\<close>
                finite_subset finite_UnI by (by100 blast)
            qed
          qed
          show "finite {A \<in> \<A>. \<not> A \<subseteq> ?target_V}"
          proof -
            have "{A \<in> \<A>. \<not> A \<subseteq> ?target_V} \<subseteq> {A1}" by (by100 blast)
            thus ?thesis using finite_subset by (by100 blast)
          qed
        qed
        have p7: "\<Union>?\<A>_V = ?target_V" using htV_eq_ext by simp
        \<comment> \<open>Premise 8: inter.\<close>
        have p8: "\<forall>A\<in>?\<A>_V. \<forall>B\<in>?\<A>_V. A \<noteq> B \<longrightarrow>
            A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?target_V ?TY_V A)
          \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?target_V ?TY_V B)
          \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
        proof (intro ballI impI)
          fix A B assume "A \<in> ?\<A>_V" "B \<in> ?\<A>_V" "A \<noteq> B"
          hence "A \<in> \<A>" "B \<in> \<A>" by (by100 blast)+
          from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>B \<in> \<A>\<close> \<open>A \<noteq> B\<close>]
          have hAB: "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)
            \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology Y TY B)
            \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" .
          have "A \<subseteq> ?target_V" using \<open>A \<in> ?\<A>_V\<close> by (by100 blast)
          have "B \<subseteq> ?target_V" using \<open>B \<in> ?\<A>_V\<close> by (by100 blast)
          have "subspace_topology ?target_V ?TY_V A = subspace_topology Y TY A"
            by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?target_V\<close>])
          have "subspace_topology ?target_V ?TY_V B = subspace_topology Y TY B"
            by (rule subspace_topology_trans[OF \<open>B \<subseteq> ?target_V\<close>])
          show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?target_V ?TY_V A)
            \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?target_V ?TY_V B)
            \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
            using hAB \<open>subspace_topology ?target_V ?TY_V A = _\<close>
              \<open>subspace_topology ?target_V ?TY_V B = _\<close> by simp
        qed
        \<comment> \<open>Premise 9: coherent topology.\<close>
        have p9: "\<forall>C. C \<subseteq> ?target_V \<longrightarrow>
            (closedin_on ?target_V ?TY_V C \<longleftrightarrow>
             (\<forall>A\<in>?\<A>_V. closedin_on A (subspace_topology ?target_V ?TY_V A) (A \<inter> C)))"
        proof -
          from subgraph_coherent_topology[OF hgraph h\<A> h\<A>_cover h\<A>_inter h\<A>_coh]
          have hcoh_raw: "\<forall>C. C \<subseteq> ?target_V \<longrightarrow>
              (closedin_on ?target_V (subspace_topology Y TY ?target_V) C \<longleftrightarrow>
               (\<forall>A\<in>?\<A>_V. closedin_on A (subspace_topology Y TY A) (A \<inter> C)))"
          proof -
            have "?\<A>_V \<subseteq> \<A>" by (by100 blast)
            from subgraph_coherent_topology[OF hgraph h\<A> h\<A>_cover h\<A>_inter h\<A>_coh this htV_eq_ext]
            show ?thesis .
          qed
          show ?thesis
          proof (intro allI impI iffI ballI)
            fix C A
            assume hC: "C \<subseteq> ?target_V"
              and "closedin_on ?target_V ?TY_V C" and "A \<in> ?\<A>_V"
            have "A \<subseteq> ?target_V" using \<open>A \<in> ?\<A>_V\<close> by (by100 blast)
            from hcoh_raw[rule_format, OF hC] \<open>closedin_on ?target_V ?TY_V C\<close>
            have "\<forall>A\<in>?\<A>_V. closedin_on A (subspace_topology Y TY A) (A \<inter> C)" by simp
            thus "closedin_on A (subspace_topology ?target_V ?TY_V A) (A \<inter> C)"
              using \<open>A \<in> ?\<A>_V\<close> subspace_topology_trans[OF \<open>A \<subseteq> ?target_V\<close>] by simp
          next
            fix C
            assume hC: "C \<subseteq> ?target_V"
              and hall: "\<forall>A\<in>?\<A>_V. closedin_on A (subspace_topology ?target_V ?TY_V A) (A \<inter> C)"
            have "\<forall>A\<in>?\<A>_V. closedin_on A (subspace_topology Y TY A) (A \<inter> C)"
            proof (intro ballI)
              fix A assume "A \<in> ?\<A>_V"
              have "A \<subseteq> ?target_V" using \<open>A \<in> ?\<A>_V\<close> by (by100 blast)
              from hall[rule_format, OF \<open>A \<in> ?\<A>_V\<close>]
              show "closedin_on A (subspace_topology Y TY A) (A \<inter> C)"
                using subspace_topology_trans[OF \<open>A \<subseteq> ?target_V\<close>] by simp
            qed
            from hcoh_raw[rule_format, OF hC, THEN iffD2, OF this]
            show "closedin_on ?target_V ?TY_V C" by simp
          qed
        qed
        \<comment> \<open>Premise 10: tree.\<close>
        have p10: "top1_is_tree_on T (subspace_topology ?target_V ?TY_V T)"
        proof -
          have "T \<subseteq> ?target_V" by (by100 blast)
          have "subspace_topology ?target_V ?TY_V T = subspace_topology Y TY T"
            by (rule subspace_topology_trans[OF \<open>T \<subseteq> ?target_V\<close>])
          thus ?thesis using hT_tree by simp
        qed
        \<comment> \<open>Premise 11.\<close>
        have p11: "T \<subseteq> ?target_V" by (by100 blast)
        \<comment> \<open>Premise 12: subgraph.\<close>
        have p12: "\<forall>A\<in>?\<A>_V. A \<subseteq> T \<or>
            A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?target_V ?TY_V A)"
        proof (intro ballI)
          fix A assume "A \<in> ?\<A>_V"
          hence "A \<in> \<A>" "A \<subseteq> ?target_V" by (by100 blast)+
          from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>]
          show "A \<subseteq> T \<or> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology ?target_V ?TY_V A)"
            using subspace_topology_trans[OF \<open>A \<subseteq> ?target_V\<close>] by simp
        qed
        \<comment> \<open>Premise 13.\<close>
        have p13: "y0 \<in> T" by (rule hT_x0)
        \<comment> \<open>Premise 14: endpoints.\<close>
        have p14: "\<forall>A\<in>{A\<in>?\<A>_V. \<not> A \<subseteq> T}. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology ?target_V ?TY_V A). e \<in> T"
        proof (intro ballI)
          fix A e assume "A \<in> {A\<in>?\<A>_V. \<not> A \<subseteq> T}"
              and "e \<in> top1_arc_endpoints_on A (subspace_topology ?target_V ?TY_V A)"
          hence "A \<in> \<A>" "\<not> A \<subseteq> T" "A \<subseteq> ?target_V" by (by100 blast)+
          hence "A \<in> ?NT" by (by100 blast)
          have "subspace_topology ?target_V ?TY_V A = subspace_topology Y TY A"
            by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?target_V\<close>])
          hence "e \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
            using \<open>e \<in> _\<close> by simp
          thus "e \<in> T" using hNT_endpoints[rule_format, OF \<open>A \<in> ?NT\<close>] by (by100 blast)
        qed
        \<comment> \<open>Apply IH.\<close>
        show ?thesis
          by (rule IH[OF p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14])
      qed
      \<comment> \<open>Step 9: U, V PC.\<close>
      have htU_sub_U: "?target_U \<subseteq> ?U"
        using conjunct1[OF hU_dr[unfolded top1_deformation_retract_of_on_def]] by (by100 blast)
      have htV_sub_V: "?target_V \<subseteq> ?V"
        using conjunct1[OF hV_dr[unfolded top1_deformation_retract_of_on_def]] by (by100 blast)
      have hU_top: "is_topology_on ?U (subspace_topology Y TY ?U)"
        by (rule subspace_topology_is_topology_on[OF hTY_top]) (by100 blast)
      have hV_top: "is_topology_on ?V (subspace_topology Y TY ?V)"
        by (rule subspace_topology_is_topology_on[OF hTY_top]) (by100 blast)
      have htU_pc: "top1_path_connected_on ?target_U (subspace_topology Y TY ?target_U)"
        using htU_pc_raw .
      have htV_pc: "top1_path_connected_on ?target_V (subspace_topology Y TY ?target_V)"
        using htV_pc_raw .
      have htU_pc_U: "top1_path_connected_on ?target_U (subspace_topology ?U (subspace_topology Y TY ?U) ?target_U)"
        using htU_pc subspace_topology_trans[OF htU_sub_U] by simp
      have htV_pc_V: "top1_path_connected_on ?target_V (subspace_topology ?V (subspace_topology Y TY ?V) ?target_V)"
        using htV_pc subspace_topology_trans[OF htV_sub_V] by simp
      have hU_pc: "top1_path_connected_on ?U (subspace_topology Y TY ?U)"
        by (rule deformation_retract_path_connected[OF hU_dr hU_top htU_pc_U])
      have hV_pc: "top1_path_connected_on ?V (subspace_topology Y TY ?V)"
        by (rule deformation_retract_path_connected[OF hV_dr hV_top htV_pc_V])
      \<comment> \<open>Step 10: y0 \\<in> U\\<inter>V.\<close>
      have hx0_UV: "y0 \<in> ?UV"
      proof -
        have "\<forall>A\<in>?NT. y0 \<noteq> ps A"
        proof (intro ballI)
          fix A assume "A \<in> ?NT"
          hence "A \<in> \<A>" "\<not> A \<subseteq> T" by (by100 blast)+
          have "ps A \<in> A" using hps \<open>A \<in> ?NT\<close> by (by100 blast)
          have "ps A \<notin> top1_arc_endpoints_on A (subspace_topology Y TY A)"
            using hps \<open>A \<in> ?NT\<close> by (by100 blast)
          show "y0 \<noteq> ps A"
          proof
            assume "y0 = ps A"
            hence "y0 \<in> A" using \<open>ps A \<in> A\<close> by (by100 simp)
            hence "y0 \<in> A \<inter> T" using hT_x0 by (by100 blast)
            have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              using hT_subgraph \<open>A \<in> \<A>\<close> \<open>\<not> A \<subseteq> T\<close> by (by100 blast)
            hence "y0 \<in> top1_arc_endpoints_on A (subspace_topology Y TY A)"
              using \<open>y0 \<in> A \<inter> T\<close> by (by100 blast)
            thus False using \<open>y0 = ps A\<close> \<open>ps A \<notin> _\<close> by (by100 simp)
          qed
        qed
        hence "y0 \<notin> ps ` ?NT" by (by100 blast)
        thus ?thesis using hy0 by (by100 blast)
      qed
      \<comment> \<open>Step 11: DR iso + free transfer.\<close>
      have hU_free_direct: "\<exists>(\<iota>::nat \<Rightarrow> _) (S::nat set). top1_is_free_group_full_on
          (top1_fundamental_group_carrier ?U (subspace_topology Y TY ?U) y0)
          (top1_fundamental_group_mul ?U (subspace_topology Y TY ?U) y0)
          (top1_fundamental_group_id ?U (subspace_topology Y TY ?U) y0)
          (top1_fundamental_group_invg ?U (subspace_topology Y TY ?U) y0)
          \<iota> S"
      proof -
        have hTU_trans: "subspace_topology ?U (subspace_topology Y TY ?U) ?target_U =
            subspace_topology Y TY ?target_U"
          by (rule subspace_topology_trans[OF htU_sub_U])
        note htU_free' = htU_free[unfolded hTU_trans[symmetric]]
        have hx0_tU: "y0 \<in> ?target_U" using hT_x0 by (by100 blast)
        have hpi1_U_iso: "top1_groups_isomorphic_on
            (top1_fundamental_group_carrier ?target_U (subspace_topology ?U (subspace_topology Y TY ?U) ?target_U) y0)
            (top1_fundamental_group_mul ?target_U (subspace_topology ?U (subspace_topology Y TY ?U) ?target_U) y0)
            (top1_fundamental_group_carrier ?U (subspace_topology Y TY ?U) y0)
            (top1_fundamental_group_mul ?U (subspace_topology Y TY ?U) y0)"
          by (rule Theorem_58_3[OF hU_dr hU_top hx0_tU])
        have hpi1_U_grp: "top1_is_group_on
            (top1_fundamental_group_carrier ?U (subspace_topology Y TY ?U) y0)
            (top1_fundamental_group_mul ?U (subspace_topology Y TY ?U) y0)
            (top1_fundamental_group_id ?U (subspace_topology Y TY ?U) y0)
            (top1_fundamental_group_invg ?U (subspace_topology Y TY ?U) y0)"
        proof -
          have "y0 \<in> ?U" using hx0_UV hUV_eq by (by100 blast)
          thus ?thesis by (rule top1_fundamental_group_is_group[OF hU_top])
        qed
        show ?thesis using htU_free' hpi1_U_iso hpi1_U_grp
          apply -
          apply (erule exE)+
          apply (drule free_group_iso_transfer, assumption, assumption)
          apply (erule exE, rule exI, rule exI, assumption)
          done
      qed
      have hV_free_direct: "\<exists>(\<iota>::nat \<Rightarrow> _) (S::nat set). top1_is_free_group_full_on
          (top1_fundamental_group_carrier ?V (subspace_topology Y TY ?V) y0)
          (top1_fundamental_group_mul ?V (subspace_topology Y TY ?V) y0)
          (top1_fundamental_group_id ?V (subspace_topology Y TY ?V) y0)
          (top1_fundamental_group_invg ?V (subspace_topology Y TY ?V) y0)
          \<iota> S"
      proof -
        have hTV_trans: "subspace_topology ?V (subspace_topology Y TY ?V) ?target_V =
            subspace_topology Y TY ?target_V"
          by (rule subspace_topology_trans[OF htV_sub_V])
        note htV_free' = htV_free[unfolded hTV_trans[symmetric]]
        have hx0_tV: "y0 \<in> ?target_V" using hT_x0 by (by100 blast)
        have hpi1_V_iso: "top1_groups_isomorphic_on
            (top1_fundamental_group_carrier ?target_V (subspace_topology ?V (subspace_topology Y TY ?V) ?target_V) y0)
            (top1_fundamental_group_mul ?target_V (subspace_topology ?V (subspace_topology Y TY ?V) ?target_V) y0)
            (top1_fundamental_group_carrier ?V (subspace_topology Y TY ?V) y0)
            (top1_fundamental_group_mul ?V (subspace_topology Y TY ?V) y0)"
          by (rule Theorem_58_3[OF hV_dr hV_top hx0_tV])
        have hpi1_V_grp: "top1_is_group_on
            (top1_fundamental_group_carrier ?V (subspace_topology Y TY ?V) y0)
            (top1_fundamental_group_mul ?V (subspace_topology Y TY ?V) y0)
            (top1_fundamental_group_id ?V (subspace_topology Y TY ?V) y0)
            (top1_fundamental_group_invg ?V (subspace_topology Y TY ?V) y0)"
        proof -
          have "y0 \<in> ?V"
          proof -
            have "y0 \<in> ?UV" using hx0_UV .
            have "ps ` {A1} \<subseteq> ps ` ?NT" using hA1 by (by100 blast)
            hence "?UV \<subseteq> ?V" by (by100 blast)
            thus ?thesis using \<open>y0 \<in> ?UV\<close> by (by100 blast)
          qed
          thus ?thesis by (rule top1_fundamental_group_is_group[OF hV_top])
        qed
        show ?thesis using htV_free' hpi1_V_iso hpi1_V_grp
          apply -
          apply (erule exE)+
          apply (drule free_group_iso_transfer, assumption, assumption)
          apply (erule exE, rule exI, rule exI, assumption)
          done
      qed
      \<comment> \<open>Step 12: SvK assembly.\<close>
      from hU_free_direct hV_free_direct
      obtain \<iota>U :: "nat \<Rightarrow> _" and S1 :: "nat set" and \<iota>V :: "nat \<Rightarrow> _" and S2 :: "nat set"
        where hU_f: "top1_is_free_group_full_on
              (top1_fundamental_group_carrier ?U (subspace_topology Y TY ?U) y0)
              (top1_fundamental_group_mul ?U (subspace_topology Y TY ?U) y0)
              (top1_fundamental_group_id ?U (subspace_topology Y TY ?U) y0)
              (top1_fundamental_group_invg ?U (subspace_topology Y TY ?U) y0)
              \<iota>U S1"
          and hV_f: "top1_is_free_group_full_on
              (top1_fundamental_group_carrier ?V (subspace_topology Y TY ?V) y0)
              (top1_fundamental_group_mul ?V (subspace_topology Y TY ?V) y0)
              (top1_fundamental_group_id ?V (subspace_topology Y TY ?V) y0)
              (top1_fundamental_group_invg ?V (subspace_topology Y TY ?V) y0)
              \<iota>V S2"
        by - ((erule exE)+, (erule that))
      \<comment> \<open>Reindex for disjointness.\<close>
      define f1 :: "nat \<Rightarrow> nat" where "f1 n = 2*n" for n
      define f2 :: "nat \<Rightarrow> nat" where "f2 n = 2*n+1" for n
      have hbij1: "bij_betw (the_inv_into S1 f1) (f1 ` S1) S1"
      proof -
        have "inj f1" unfolding f1_def by (intro injI) (by100 simp)
        hence "inj_on f1 S1" using inj_on_subset[OF \<open>inj f1\<close>] by (by100 blast)
        hence "bij_betw f1 S1 (f1 ` S1)" unfolding bij_betw_def by (by100 blast)
        thus ?thesis by (rule bij_betw_the_inv_into)
      qed
      from free_group_full_reindex[OF hU_f hbij1]
      have hU_re: "top1_is_free_group_full_on
          (top1_fundamental_group_carrier ?U (subspace_topology Y TY ?U) y0)
          (top1_fundamental_group_mul ?U (subspace_topology Y TY ?U) y0)
          (top1_fundamental_group_id ?U (subspace_topology Y TY ?U) y0)
          (top1_fundamental_group_invg ?U (subspace_topology Y TY ?U) y0)
          (\<iota>U \<circ> the_inv_into S1 f1) (f1 ` S1)" .
      have hbij2: "bij_betw (the_inv_into S2 f2) (f2 ` S2) S2"
      proof -
        have "inj f2" unfolding f2_def by (intro injI) (by100 simp)
        hence "inj_on f2 S2" using inj_on_subset[OF \<open>inj f2\<close>] by (by100 blast)
        hence "bij_betw f2 S2 (f2 ` S2)" unfolding bij_betw_def by (by100 blast)
        thus ?thesis by (rule bij_betw_the_inv_into)
      qed
      from free_group_full_reindex[OF hV_f hbij2]
      have hV_re: "top1_is_free_group_full_on
          (top1_fundamental_group_carrier ?V (subspace_topology Y TY ?V) y0)
          (top1_fundamental_group_mul ?V (subspace_topology Y TY ?V) y0)
          (top1_fundamental_group_id ?V (subspace_topology Y TY ?V) y0)
          (top1_fundamental_group_invg ?V (subspace_topology Y TY ?V) y0)
          (\<iota>V \<circ> the_inv_into S2 f2) (f2 ` S2)" .
      have hS_disj: "f1 ` S1 \<inter> f2 ` S2 = {}"
      proof (rule ccontr)
        assume "\<not> ?thesis"
        then obtain x where "x \<in> f1 ` S1" "x \<in> f2 ` S2" by (by100 blast)
        then obtain a b where "x = 2*a" "x = 2*b+1"
          unfolding f1_def f2_def by (by100 blast)
        thus False by presburger
      qed
      have hY_strict: "is_topology_on_strict Y TY"
        using hgraph unfolding top1_is_graph_on_def by (by100 blast)
      have hx0_UV': "y0 \<in> ?U \<inter> ?V" using hx0_UV hUV_eq by (by100 simp)
      have hUV_sc': "top1_simply_connected_on (?U \<inter> ?V) (subspace_topology Y TY (?U \<inter> ?V))"
        using hUV_sc hUV_eq by (by100 simp)
      from svk_free_product_free[OF hY_strict hU_open hV_open hUV_cover
          hUV_sc' hU_pc hV_pc hx0_UV' hU_re hV_re hS_disj]
      obtain \<iota>Y where hY_fr: "top1_is_free_group_full_on
          (top1_fundamental_group_carrier Y TY y0)
          (top1_fundamental_group_mul Y TY y0)
          (top1_fundamental_group_id Y TY y0)
          (top1_fundamental_group_invg Y TY y0)
          \<iota>Y (f1 ` S1 \<union> f2 ` S2)" by (by100 blast)
      show ?thesis using hY_fr by (by5000 blast)
    qed
  qed
qed

end
