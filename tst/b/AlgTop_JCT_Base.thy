theory AlgTop_JCT_Base
  imports "AlgTopBase0.AlgTop_JCT_Base0"
begin


text \<open>The correct version of "nulhomotopic loop is contractible" is Munkres Lemma 55.3,
  already fully proved in Top1_Ch9_13:
  - Lemma_55_3_nulhomotopic_characterization: h:S^1->X nulhomotopic iff extends to B^2
  - nulhomotopic_trivializes_loops_general: nulhomotopic g => g o f path-homotopic to const
  A previous attempt (nulhomotopic_loop_path_homotopic_constant) had a wrong hypothesis
  (nulhomotopic on I instead of S^1, vacuously true since I is contractible) and has been deleted.\<close>

(* Deleted 900 lines: nulhomotopic_loop_path_homotopic_constant.
   Wrong statement (nulhomotopic on I, vacuously true). Correct version is
   Lemma_55_3_nulhomotopic_characterization + nulhomotopic_trivializes_loops_general
   in Top1_Ch9_13. See REPORT_JCT_BASE_902.md. *)

text \<open>Helper: a path in a subspace is a path in the ambient space.\<close>
lemma path_in_subspace_is_path_in_ambient:
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

text \<open>A path in a subspace is also a path in the ambient space.\<close>
lemma path_in_subspace_imp_path_in_ambient:
  assumes hTX: "is_topology_on_strict X TX"
      and hUsub: "U \<subseteq> X"
      and hf: "top1_is_path_on U (subspace_topology X TX U) a b f"
  shows "top1_is_path_on X TX a b f"
proof -
  have hTX': "is_topology_on X TX" using hTX unfolding is_topology_on_strict_def by (by100 blast)
  have hf_cont_U: "top1_continuous_map_on I_set I_top U (subspace_topology X TX U) f"
    using hf unfolding top1_is_path_on_def by (by100 blast)
  have hf_cont_X: "top1_continuous_map_on I_set I_top X TX f"
  proof -
    have "top1_continuous_map_on I_set I_top X (subspace_topology X TX X) f"
      by (rule top1_continuous_map_on_codomain_enlarge[OF hf_cont_U hUsub]) simp
    moreover have "subspace_topology X TX X = TX"
    proof (rule subspace_topology_self_carrier)
      show "\<forall>U\<in>TX. U \<subseteq> X" using hTX unfolding is_topology_on_strict_def
        by (by100 blast)
    qed
    ultimately show ?thesis by simp
  qed
  have hf_map: "\<forall>t\<in>I_set. f t \<in> U" using hf_cont_U unfolding top1_continuous_map_on_def by (by100 blast)
  have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have "f 0 = a" using hf unfolding top1_is_path_on_def by (by100 blast)
  have "f 1 = b" using hf unfolding top1_is_path_on_def by (by100 blast)
  have "a \<in> U" using hf_map h0_I \<open>f 0 = a\<close> by (by100 force)
  have "a \<in> X" using \<open>a \<in> U\<close> hUsub by (by100 blast)
  have "b \<in> U" using hf_map h1_I \<open>f 1 = b\<close> by (by100 force)
  have "b \<in> X" using \<open>b \<in> U\<close> hUsub by (by100 blast)
  show ?thesis unfolding top1_is_path_on_def
    using hf_cont_X \<open>f 0 = a\<close> \<open>f 1 = b\<close> \<open>a \<in> X\<close> \<open>b \<in> X\<close> by (by100 blast)
qed

text \<open>Helper: union of path-connected open sets with nonempty path-connected intersection
  is path-connected.\<close>
lemma path_connected_union:
  assumes hTX: "is_topology_on X TX"
      and hU_pc: "top1_path_connected_on U (subspace_topology X TX U)"
      and hV_pc: "top1_path_connected_on V (subspace_topology X TX V)"
      and hUV_pc: "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and hUV: "U \<union> V = X" and hUsub: "U \<subseteq> X" and hVsub: "V \<subseteq> X"
      and hUV_ne: "U \<inter> V \<noteq> {}"
  shows "top1_path_connected_on X TX"
  unfolding top1_path_connected_on_def
proof (intro conjI ballI)
  show "is_topology_on X TX" by (rule hTX)
next
  fix x y assume hx: "x \<in> X" and hy: "y \<in> X"
  \<comment> \<open>Case analysis: both in U, both in V, or one in each (join via U\<inter>V).\<close>
  show "\<exists>f. top1_is_path_on X TX x y f"
  proof (cases "x \<in> U \<and> y \<in> U")
    case True
    \<comment> \<open>Path in U, transfer to X via subspace inclusion.\<close>
    obtain f where hf: "top1_is_path_on U (subspace_topology X TX U) x y f"
      using hU_pc True unfolding top1_path_connected_on_def by (by100 auto)
    have "top1_is_path_on X TX x y f"
      by (rule path_in_subspace_is_path_in_ambient[OF hTX hUsub hf])
    thus ?thesis by (by100 blast)
  next
    case False
    \<comment> \<open>x \<notin> U \<or> y \<notin> U. Since x,y \<in> U\<union>V, the missing one is in V.
       Pick z \<in> U\<inter>V, path in U to/from z, path in V to/from z, concatenate.\<close>
    have hx_mem: "x \<in> U \<or> x \<in> V" and hy_mem: "y \<in> U \<or> y \<in> V"
      using hx hy hUV by (by100 blast)+
    \<comment> \<open>Get z \<in> U \<inter> V for joining paths.\<close>
    obtain z where hz: "z \<in> U \<inter> V" using hUV_ne by (by100 blast)
    \<comment> \<open>For any a \<in> U and b \<in> V, there's a path a\<rightarrow>z in U and z\<rightarrow>b in V in X.\<close>
    \<comment> \<open>Full proof requires path extraction from each subspace + transfer + concatenation.
       Follows the same pattern as the True case above.\<close>
    \<comment> \<open>Helper: get path in X between points in a path-connected subspace W.\<close>
    have hzU: "z \<in> U" and hzV: "z \<in> V" using hz by (by100 blast)+
    \<comment> \<open>x is in U or V; get path x\<rightarrow>z in X.\<close>
    obtain g1 where hg1: "top1_is_path_on X TX x z g1"
    proof -
      have "\<exists>g. top1_is_path_on X TX x z g"
      proof (cases "x \<in> U")
        case True
        obtain g where "top1_is_path_on U (subspace_topology X TX U) x z g"
          using hU_pc True hzU unfolding top1_path_connected_on_def by (by100 auto)
        thus ?thesis using path_in_subspace_is_path_in_ambient[OF hTX hUsub] by (by100 blast)
      next
        case FalseU: False
        hence "x \<in> V" using hx_mem by (by100 blast)
        obtain g where "top1_is_path_on V (subspace_topology X TX V) x z g"
          using hV_pc \<open>x \<in> V\<close> hzV unfolding top1_path_connected_on_def by (by100 auto)
        thus ?thesis using path_in_subspace_is_path_in_ambient[OF hTX hVsub] by (by100 blast)
      qed
      thus ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>y is in U or V; get path z\<rightarrow>y in X.\<close>
    obtain g2 where hg2: "top1_is_path_on X TX z y g2"
    proof -
      have "\<exists>g. top1_is_path_on X TX z y g"
      proof (cases "y \<in> U")
        case True
        obtain g where "top1_is_path_on U (subspace_topology X TX U) z y g"
          using hU_pc hzU True unfolding top1_path_connected_on_def by (by100 auto)
        thus ?thesis using path_in_subspace_is_path_in_ambient[OF hTX hUsub] by (by100 blast)
      next
        case FalseU: False
        hence "y \<in> V" using hy_mem by (by100 blast)
        obtain g where "top1_is_path_on V (subspace_topology X TX V) z y g"
          using hV_pc hzV \<open>y \<in> V\<close> unfolding top1_path_connected_on_def by (by100 auto)
        thus ?thesis using path_in_subspace_is_path_in_ambient[OF hTX hVsub] by (by100 blast)
      qed
      thus ?thesis using that by (by100 blast)
    qed
    \<comment> \<open>Concatenate: x \<rightarrow> z \<rightarrow> y.\<close>
    have "top1_is_path_on X TX x y (top1_path_product g1 g2)"
      by (rule top1_path_product_is_path[OF hTX hg1 hg2])
    thus ?thesis by (by100 blast)
  qed
qed

text \<open>Helper: R with top1\_open\_sets is Hausdorff.\<close>
lemma top1_R_is_hausdorff:
  "is_hausdorff_on (UNIV :: real set) top1_open_sets"
proof -
  have hT: "is_topology_on (UNIV :: real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hH: "\<forall>x\<in>(UNIV::real set). \<forall>y\<in>(UNIV::real set). x \<noteq> y \<longrightarrow>
      (\<exists>U V. neighborhood_of x UNIV top1_open_sets U \<and>
             neighborhood_of y UNIV top1_open_sets V \<and> U \<inter> V = {})"
  proof (intro ballI impI)
    fix x y :: real assume "x \<in> UNIV" "y \<in> UNIV" "x \<noteq> y"
    show "\<exists>U V. neighborhood_of x UNIV top1_open_sets U \<and>
                neighborhood_of y UNIV top1_open_sets V \<and> U \<inter> V = {}"
    proof (cases "x < y")
      case True
      let ?m = "(x + y) / 2"
      have "{..<(?m::real)} \<in> {U. open U} \<and> x \<in> {..<(?m::real)}"
        using True by simp
      moreover have "{?m<..} \<in> {U. open U} \<and> y \<in> {?m<..}"
        using True by simp
      moreover have "{..<(?m::real)} \<inter> {?m<..} = {}" by auto
      ultimately show ?thesis unfolding neighborhood_of_def top1_open_sets_def by blast
    next
      case False
      hence "x > y" using \<open>x \<noteq> y\<close> by simp
      let ?m = "(x + y) / 2"
      have "{?m<..} \<in> {U. open U} \<and> x \<in> {?m<..}"
        using \<open>x > y\<close> by simp
      moreover have "{..<(?m::real)} \<in> {U. open U} \<and> y \<in> {..<(?m::real)}"
        using \<open>x > y\<close> by simp
      moreover have "{?m<..} \<inter> {..<(?m::real)} = {}" by auto
      ultimately show ?thesis unfolding neighborhood_of_def top1_open_sets_def by blast
    qed
  qed
  show ?thesis unfolding is_hausdorff_on_def using hT hH by (by100 blast)
qed

text \<open>Helper: R^2 with product topology is Hausdorff.\<close>
lemma top1_R2_is_hausdorff:
  "is_hausdorff_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
proof -
  have hR: "is_hausdorff_on (UNIV :: real set) top1_open_sets" by (rule top1_R_is_hausdorff)
  have hR2: "is_hausdorff_on (UNIV \<times> UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
    using conjunct1[OF conjunct2[OF Theorem_17_11]] hR by (by100 blast)
  thus ?thesis by simp
qed

text \<open>Helper: S^1 subspace is Hausdorff.\<close>
lemma top1_S1_is_hausdorff:
  "is_hausdorff_on top1_S1 top1_S1_topology"
proof -
  have "top1_S1 \<subseteq> (UNIV :: (real \<times> real) set)" by simp
  thus ?thesis unfolding top1_S1_topology_def
    using conjunct2[OF conjunct2[OF Theorem_17_11]] top1_R2_is_hausdorff by (by100 blast)
qed

text \<open>Helper: R^3 = R \<times> (R \<times> R) is Hausdorff.\<close>
lemma top1_R3_is_hausdorff:
  "is_hausdorff_on (UNIV :: (real \<times> real \<times> real) set)
     (product_topology_on top1_open_sets (product_topology_on top1_open_sets top1_open_sets))"
proof -
  have hR: "is_hausdorff_on (UNIV :: real set) top1_open_sets" by (rule top1_R_is_hausdorff)
  have hR2: "is_hausdorff_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
    by (rule top1_R2_is_hausdorff)
  have "is_hausdorff_on (UNIV \<times> UNIV :: (real \<times> (real \<times> real)) set)
      (product_topology_on top1_open_sets (product_topology_on top1_open_sets top1_open_sets))"
    using conjunct1[OF conjunct2[OF Theorem_17_11]] hR hR2 by (by100 blast)
  thus ?thesis by simp
qed

text \<open>S^1 has strict topology.\<close>
lemma top1_S1_is_topology_on_strict:
  "is_topology_on_strict top1_S1 top1_S1_topology"
  unfolding is_topology_on_strict_def
proof (intro conjI)
  show "is_topology_on top1_S1 top1_S1_topology"
    using top1_S1_is_hausdorff unfolding is_hausdorff_on_def by (by100 blast)
  show "top1_S1_topology \<subseteq> Pow top1_S1"
    unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
qed

text \<open>R^2 - {0} has strict topology.\<close>
lemma top1_R2_minus_0_is_topology_on_strict:
  "is_topology_on_strict (UNIV - {(0::real, 0::real)})
     (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))"
  unfolding is_topology_on_strict_def
proof (intro conjI)
  show "is_topology_on (UNIV - {(0::real, 0::real)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))"
  proof -
    have "is_topology_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using top1_R2_is_hausdorff unfolding is_hausdorff_on_def by (by100 blast)
    thus ?thesis by (rule subspace_topology_is_topology_on) simp
  qed
  show "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)})
      \<subseteq> Pow (UNIV - {(0::real, 0::real)})"
    unfolding subspace_topology_def by (by100 blast)
qed

text \<open>Helper: closed set has open complement.\<close>
lemma closedin_complement_openin:
  assumes "closedin_on X TX A"
  shows "openin_on X TX (X - A)"
  using assms unfolding closedin_on_def openin_on_def by (by100 blast)

text \<open>Helper: open set has closed complement.\<close>
lemma openin_complement_closedin:
  assumes "openin_on X TX A"
  shows "closedin_on X TX (X - A)"
proof -
  have hA: "A \<in> TX" and hAsub: "A \<subseteq> X"
    using assms unfolding openin_on_def by (by100 blast)+
  have "X - (X - A) = A" using hAsub by (by100 blast)
  thus ?thesis unfolding closedin_on_def using hA by (by100 simp)
qed


text \<open>Helper: if each loop in a list is nulhomotopic, their foldr product is nulhomotopic.\<close>
lemma foldr_path_product_nulhomotopic:
  assumes hTX: "is_topology_on X TX" and hx0: "x0 \<in> X"
      and hnul: "\<forall>i < length gs. top1_path_homotopic_on X TX x0 x0 (gs!i) (top1_constant_path x0)"
  shows "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product gs (top1_constant_path x0)) (top1_constant_path x0)"
  using hnul
proof (induction gs)
  case Nil
  have "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_path[OF hTX hx0])
  thus ?case by (simp, rule Lemma_51_1_path_homotopic_refl)
next
  case (Cons g gs')
  have hg_nul: "top1_path_homotopic_on X TX x0 x0 g (top1_constant_path x0)"
    using Cons.prems by force
  have hgs'_nul: "\<forall>i < length gs'. top1_path_homotopic_on X TX x0 x0 (gs'!i) (top1_constant_path x0)"
    using Cons.prems by force
  have hrest_nul: "top1_path_homotopic_on X TX x0 x0
      (foldr top1_path_product gs' (top1_constant_path x0)) (top1_constant_path x0)"
    by (rule Cons.IH[OF hgs'_nul])
  have hrest_path: "top1_is_path_on X TX x0 x0 (foldr top1_path_product gs' (top1_constant_path x0))"
    using hrest_nul unfolding top1_path_homotopic_on_def by (by100 blast)
  have step1: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product g (foldr top1_path_product gs' (top1_constant_path x0)))
      (top1_path_product (top1_constant_path x0) (foldr top1_path_product gs' (top1_constant_path x0)))"
    by (rule path_homotopic_product_left[OF hTX hg_nul hrest_path])
  have step2: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product (top1_constant_path x0) (foldr top1_path_product gs' (top1_constant_path x0)))
      (foldr top1_path_product gs' (top1_constant_path x0))"
    by (rule Theorem_51_2_left_identity[OF hTX hrest_path])
  have step12: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product g (foldr top1_path_product gs' (top1_constant_path x0)))
      (foldr top1_path_product gs' (top1_constant_path x0))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX step1 step2])
  show ?case
    by (simp, rule Lemma_51_1_path_homotopic_trans[OF hTX step12 hrest_nul])
qed

(** from \<S>59 Corollary 59.2: U, V open, simply connected, U \<inter> V path-connected
    and nonempty \<Longrightarrow> X = U \<union> V is simply connected. **)
corollary Corollary_59_2:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V \<noteq> {}"
      and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "top1_simply_connected_on U (subspace_topology X TX U)"
      and "top1_simply_connected_on V (subspace_topology X TX V)"
  shows "top1_simply_connected_on X TX"
proof -
  \<comment> \<open>Munkres 59.2: By Thm 59.1, every loop decomposes into loops in U or V.
     U, V simply connected \<Rightarrow> each piece nulhomotopic \<Rightarrow> whole loop nulhomotopic.\<close>
  obtain x0 where hx0: "x0 \<in> U \<inter> V" using assms(5) by (by100 blast)
  \<comment> \<open>Step 1: X is path-connected (U, V path-connected via simply connected, joined via U\<inter>V).\<close>
  have hpc: "top1_path_connected_on X TX"
  proof -
    have hU_pc: "top1_path_connected_on U (subspace_topology X TX U)"
      using assms(7) top1_simply_connected_on_path_connected by (by100 blast)
    have hV_pc: "top1_path_connected_on V (subspace_topology X TX V)"
      using assms(8) top1_simply_connected_on_path_connected by (by100 blast)
    show ?thesis
      by (rule path_connected_union[OF is_topology_on_strict_imp[OF assms(1)]
            hU_pc hV_pc assms(6) assms(4) openin_on_sub[OF assms(2)] openin_on_sub[OF assms(3)] assms(5)])
  qed
  \<comment> \<open>Step 2: Every loop at x0 is nulhomotopic.\<close>
  have hnul: "\<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
      top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
  proof (intro allI impI)
    fix f assume hf: "top1_is_loop_on X TX x0 f"
    \<comment> \<open>By Theorem 59.1, f decomposes into loops in U or V.\<close>
    obtain n gs where hn: "n \<ge> 1" and hlen: "length gs = n"
        and hgs: "\<forall>i<n. top1_is_loop_on X TX x0 (gs!i)
                      \<and> (gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V)"
        and hprod: "top1_path_homotopic_on X TX x0 x0 f
            (foldr top1_path_product gs (top1_constant_path x0))"
      using Theorem_59_1[OF assms(1,2,3,4,6) hx0] hf by blast
    \<comment> \<open>Each gi lies in U or V, hence is nulhomotopic there (simply connected).\<close>
    have hgi_nul: "\<forall>i<n. top1_path_homotopic_on X TX x0 x0 (gs!i) (top1_constant_path x0)"
    proof (intro allI impI)
      fix i assume hi: "i < n"
      have hgi_loop: "top1_is_loop_on X TX x0 (gs!i)" using hgs hi by (by100 blast)
      have "gs!i ` I_set \<subseteq> U \<or> gs!i ` I_set \<subseteq> V" using hgs hi by (by100 blast)
      \<comment> \<open>If in U: simply connected U \<Rightarrow> nulhomotopic in U \<Rightarrow> nulhomotopic in X.
         If in V: simply connected V \<Rightarrow> nulhomotopic in V \<Rightarrow> nulhomotopic in X.\<close>
      thus "top1_path_homotopic_on X TX x0 x0 (gs!i) (top1_constant_path x0)"
      proof
        assume hU_case: "gs!i ` I_set \<subseteq> U"
        \<comment> \<open>gs!i is a loop in U. U simply connected \<Rightarrow> nulhomotopic in U.\<close>
        have hgi_loop_U: "top1_is_loop_on U (subspace_topology X TX U) x0 (gs!i)"
        proof -
          have hcont_X: "top1_continuous_map_on I_set I_top X TX (gs!i)"
            using hgi_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have himg: "(gs!i) ` I_set \<subseteq> U" using hU_case .
          have hUsub: "U \<subseteq> X" using openin_on_sub[OF assms(2)] .
          have hcont_U: "top1_continuous_map_on I_set I_top U (subspace_topology X TX U) (gs!i)"
            by (rule top1_continuous_map_on_codomain_shrink[OF hcont_X himg hUsub])
          have hg0: "(gs!i) 0 = x0" and hg1: "(gs!i) 1 = x0"
            using hgi_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
            using hcont_U hg0 hg1 by (by100 simp)
        qed
        have hgi_nul_U: "top1_path_homotopic_on U (subspace_topology X TX U) x0 x0
            (gs!i) (top1_constant_path x0)"
        proof -
          have hx0U: "x0 \<in> U" using hx0 by (by100 blast)
          show ?thesis using assms(7) hgi_loop_U hx0U
            unfolding top1_simply_connected_on_def by (by100 blast)
        qed
        show ?thesis
          by (rule path_homotopic_subspace_to_ambient[OF
                is_topology_on_strict_imp[OF assms(1)] _ refl hgi_nul_U])
             (rule openin_on_sub[OF assms(2)])
      next
        assume hV_case: "gs!i ` I_set \<subseteq> V"
        have hgi_loop_V: "top1_is_loop_on V (subspace_topology X TX V) x0 (gs!i)"
        proof -
          have hcont_X: "top1_continuous_map_on I_set I_top X TX (gs!i)"
            using hgi_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have himg: "(gs!i) ` I_set \<subseteq> V" using hV_case .
          have hVsub: "V \<subseteq> X" using openin_on_sub[OF assms(3)] .
          have hcont_V: "top1_continuous_map_on I_set I_top V (subspace_topology X TX V) (gs!i)"
            by (rule top1_continuous_map_on_codomain_shrink[OF hcont_X himg hVsub])
          have hg0: "(gs!i) 0 = x0" and hg1: "(gs!i) 1 = x0"
            using hgi_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
          show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
            using hcont_V hg0 hg1 by (by100 simp)
        qed
        have hgi_nul_V: "top1_path_homotopic_on V (subspace_topology X TX V) x0 x0
            (gs!i) (top1_constant_path x0)"
        proof -
          have hx0V: "x0 \<in> V" using hx0 by (by100 blast)
          show ?thesis using assms(8) hgi_loop_V hx0V
            unfolding top1_simply_connected_on_def by (by100 blast)
        qed
        show ?thesis
          by (rule path_homotopic_subspace_to_ambient[OF
                is_topology_on_strict_imp[OF assms(1)] _ refl hgi_nul_V])
             (rule openin_on_sub[OF assms(3)])
      qed
    qed
    \<comment> \<open>Product of nulhomotopic loops is nulhomotopic.\<close>
    have hx0X: "x0 \<in> X" using hx0 assms(4) by (by100 blast)
    have hTX_weak: "is_topology_on X TX" by (rule is_topology_on_strict_imp[OF assms(1)])
    have "top1_path_homotopic_on X TX x0 x0
        (foldr top1_path_product gs (top1_constant_path x0)) (top1_constant_path x0)"
    proof -
      have "\<forall>i < length gs. top1_path_homotopic_on X TX x0 x0 (gs!i) (top1_constant_path x0)"
        using hgi_nul hlen by (by100 simp)
      thus ?thesis by (rule foldr_path_product_nulhomotopic[OF hTX_weak hx0X])
    qed
    \<comment> \<open>Transitivity: f \<simeq> product \<simeq> const.\<close>
    thus "top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
      by (rule Lemma_51_1_path_homotopic_trans[OF is_topology_on_strict_imp[OF assms(1)] hprod])
  qed
  \<comment> \<open>Assemble: path-connected + all loops at x0 nulhomotopic \<Rightarrow> simply connected.\<close>
  have hx0X_outer: "x0 \<in> X" using hx0 assms(4) by (by100 blast)
  show ?thesis
    by (rule top1_simply_connected_from_one_point[OF
          is_topology_on_strict_imp[OF assms(1)] hpc hx0X_outer hnul])
qed

text \<open>Helper: normalized interpolation on S^n gives a continuous path.
  For x,y \<in> S^n with x \<noteq> -y, the path \<gamma>(t) = ((1-t)x + ty)/||(1-t)x + ty|| is
  continuous in the indexed product topology and stays on S^n.\<close>
lemma Sn_normalized_interpolation_path:
  fixes n :: nat and x y :: "nat \<Rightarrow> real"
  assumes hx: "x \<in> top1_Sn n" and hy: "y \<in> top1_Sn n"
      and hna: "x \<noteq> (\<lambda>i. - y i)" \<comment> \<open>x \<noteq> -y (not antipodal)\<close>
  defines "\<gamma> \<equiv> \<lambda>t. \<lambda>i. ((1-t) * x i + t * y i) /
      sqrt (\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2)"
  shows "top1_is_path_on (top1_Sn n)
      (subspace_topology UNIV
        (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))
        (top1_Sn n)) x y \<gamma>"
proof -
  let ?TSn = "subspace_topology UNIV
      (top1_product_topology_on UNIV (\<lambda>_::nat. UNIV::real set) (\<lambda>_. top1_open_sets))
      (top1_Sn n)"
  let ?N = "\<lambda>t. sqrt (\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2)"
  \<comment> \<open>Step 1: N(t) > 0 for all t \<in> [0,1], since x \<noteq> -y.\<close>
  have hx_norm0: "(\<Sum>j\<le>n. (x j)^2) = 1"
    using hx unfolding top1_Sn_def by (by100 blast)
  have hy_norm0: "(\<Sum>j\<le>n. (y j)^2) = 1"
    using hy unfolding top1_Sn_def by (by100 blast)
  have hN_pos: "\<forall>t. ?N t > 0"
  proof -
    have hne: "\<And>t. \<exists>k\<le>n. (1-t) * x k + t * y k \<noteq> 0"
    proof (rule ccontr)
      fix t :: real
      assume "\<not> (\<exists>k\<le>n. (1-t) * x k + t * y k \<noteq> 0)"
      hence hall: "\<And>k. k \<le> n \<Longrightarrow> (1-t) * x k + t * y k = 0" by (by100 blast)
      have hall': "\<And>k. k \<le> n \<Longrightarrow> (1-t) * x k = -(t * y k)"
      proof -
        fix k assume "k \<le> n"
        hence "(1-t) * x k + t * y k = 0" by (rule hall)
        thus "(1-t) * x k = -(t * y k)" by (by100 linarith)
      qed
      have hx_zero_above: "\<And>i. i \<ge> Suc n \<Longrightarrow> x i = 0"
        using hx unfolding top1_Sn_def by (by100 blast)
      have hy_zero_above: "\<And>i. i \<ge> Suc n \<Longrightarrow> y i = 0"
        using hy unfolding top1_Sn_def by (by100 blast)
      show False
      proof (cases "t = 0")
        case True
        hence "\<And>k. k \<le> n \<Longrightarrow> x k = 0" using hall by (by100 simp)
        hence "(\<Sum>j\<le>n. (x j)^2) = 0" by (by100 simp)
        thus False using hx_norm0 by (by100 linarith)
      next
        case False note ht0 = this
        show False
        proof (cases "t = 1")
          case True
          hence "\<And>k. k \<le> n \<Longrightarrow> y k = 0" using hall by (by100 simp)
          hence "(\<Sum>j\<le>n. (y j)^2) = 0" by (by100 simp)
          thus False using hy_norm0 by (by100 linarith)
        next
          case False
          hence ht1: "1 - t \<noteq> 0" by (by100 linarith)
          have hxi: "\<And>k. k \<le> n \<Longrightarrow> x k = -(t/(1-t)) * y k"
          proof -
            fix k assume hk: "k \<le> n"
            have h1: "(1-t) * x k = -(t * y k)" by (rule hall'[OF hk])
            have "x k = (1-t) * x k / (1-t)" using ht1 by (by100 simp)
            also have "\<dots> = -(t * y k) / (1-t)" using h1 by (by100 simp)
            finally show "x k = -(t/(1-t)) * y k" by (by100 simp)
          qed
          have hxi_all: "\<And>i. x i = - (t/(1-t)) * y i"
          proof -
            fix i show "x i = - (t/(1-t)) * y i"
            proof (cases "i \<le> n")
              case True thus ?thesis using hxi[OF True] by (by100 linarith)
            next
              case False hence "i \<ge> Suc n" by (by100 linarith)
              thus ?thesis using hx_zero_above hy_zero_above by (by100 simp)
            qed
          qed
          have "x = (\<lambda>i. - y i)"
          proof -
            have hratio: "(t/(1-t))^2 = 1"
            proof -
              have "(\<Sum>j\<le>n. (x j)^2) = (\<Sum>j\<le>n. (-(t/(1-t)) * y j)^2)"
                using hxi by (intro sum.cong) (by100 simp)+
              also have "\<dots> = (\<Sum>j\<le>n. (t/(1-t))^2 * (y j)^2)"
                using power_mult_distrib[of "-(t/(1-t))" _ 2]
                by (intro sum.cong) (by100 simp)+
              also have "\<dots> = (t/(1-t))^2 * (\<Sum>j\<le>n. (y j)^2)"
                by (rule sum_distrib_left[symmetric])
              finally have "(t/(1-t))^2 * 1 = 1" using hx_norm0 hy_norm0 by (by100 simp)
              thus ?thesis by (by100 simp)
            qed
            have "t/(1-t) = 1 \<or> t/(1-t) = -1"
            proof -
              have h_sq: "(\<bar>t/(1-t)\<bar>)^2 = (1::real)^2"
                using hratio power2_abs[of "t/(1-t)"] by (by100 simp)
              have h_abs_nn: "(0::real) \<le> \<bar>t/(1-t)\<bar>" by (by100 simp)
              have h_1_nn: "(0::real) \<le> 1" by (by100 simp)
              have "\<bar>t/(1-t)\<bar> = (1::real)"
                by (rule power2_eq_imp_eq[OF h_sq h_abs_nn h_1_nn])
              thus ?thesis by (by100 linarith)
            qed
            thus ?thesis
            proof
              assume ht_eq: "t/(1-t) = 1"
              have "\<And>i. x i = -y i"
              proof -
                fix i have "x i = -(t/(1-t)) * y i" by (rule hxi_all)
                thus "x i = -y i" using ht_eq by (by100 simp)
              qed
              thus ?thesis by (rule ext)
            next
              assume "t/(1-t) = -1"
              hence "\<And>i. x i = y i" using hxi_all by (by100 simp)
              hence "x = y" by (rule ext)
              \<comment> \<open>But then (1-t)*x+t*y = x \<noteq> 0 since ||x||=1, contradiction.\<close>
              hence "\<And>k. k \<le> n \<Longrightarrow> x k = 0"
              proof -
                fix k assume hk: "k \<le> n"
                have "(1-t) * x k + t * x k = 0" using hall[OF hk] \<open>x = y\<close> by (by100 simp)
                hence "x k = 0" by (by100 algebra)
                thus "x k = 0" .
              qed
              hence "(\<Sum>j\<le>n. (x j)^2) = 0" by (by100 simp)
              thus ?thesis using hx_norm0 by (by100 linarith)
            qed
          qed
          thus False using hna by (by100 simp)
        qed
      qed
    qed
    show ?thesis
    proof (intro allI)
      fix t :: real
      obtain k where hk: "k \<le> n" "(1-t) * x k + t * y k \<noteq> 0" using hne by (by100 blast)
      have hksq: "((1-t) * x k + t * y k)^2 > 0" using hk(2) by (by100 simp)
      have hge: "\<And>j. ((1-t) * x j + t * y j)^2 \<ge> 0" by (by100 simp)
      have "(\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2) \<ge> ((1-t) * x k + t * y k)^2"
      proof -
        have hfin: "finite ({..n}::nat set)" by (by100 simp)
        have hk_in: "k \<in> {..n}" using hk(1) by (by100 simp)
        have "(\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2) =
              ((1-t) * x k + t * y k)^2 + (\<Sum>j\<in>{..n}-{k}. ((1-t) * x j + t * y j)^2)"
          using sum.remove[OF hfin hk_in] by (by100 simp)
        moreover have "(\<Sum>j\<in>{..n}-{k}. ((1-t) * x j + t * y j)^2) \<ge> 0"
          by (rule sum_nonneg) (by100 simp)
        ultimately show ?thesis by (by100 linarith)
      qed
      hence "(\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2) > 0" using hksq by (by100 linarith)
      thus "?N t > 0" by (by100 simp)
    qed
  qed
  \<comment> \<open>Step 2: \<gamma> maps into S^n.\<close>
  have hx_zero: "\<And>i. i \<ge> Suc n \<Longrightarrow> x i = 0" using hx unfolding top1_Sn_def by (by100 blast)
  have hy_zero: "\<And>i. i \<ge> Suc n \<Longrightarrow> y i = 0" using hy unfolding top1_Sn_def by (by100 blast)
  have h\<gamma>_Sn: "\<forall>t. \<gamma> t \<in> top1_Sn n"
  proof (intro allI)
    fix t :: real
    have hNt: "?N t > 0" using hN_pos by (by100 blast)
    show "\<gamma> t \<in> top1_Sn n" unfolding top1_Sn_def \<gamma>_def
    proof (intro CollectI conjI allI impI)
      fix i assume "i \<ge> Suc n"
      hence "x i = 0" "y i = 0" using hx_zero hy_zero by (by100 blast)+
      thus "((1 - t) * x i + t * y i) / ?N t = 0" by (by100 simp)
    next
      have hstep1: "\<And>j. (((1-t) * x j + t * y j) / ?N t)^2
          = ((1-t) * x j + t * y j)^2 / (?N t)^2"
        using power_divide by (by100 blast)
      have "(\<Sum>j\<le>n. (((1 - t) * x j + t * y j) / ?N t)\<^sup>2)
          = (\<Sum>j\<le>n. ((1 - t) * x j + t * y j)\<^sup>2 / (?N t)\<^sup>2)"
        using hstep1 by (intro sum.cong) (by100 simp)+
      also have "\<dots> = (\<Sum>j\<le>n. ((1 - t) * x j + t * y j)\<^sup>2) / (?N t)\<^sup>2"
        using sum_divide_distrib[symmetric] by (by100 simp)
      also have "(?N t)\<^sup>2 = (\<Sum>j\<le>n. ((1 - t) * x j + t * y j)\<^sup>2)"
        using hNt by (by100 simp)
      also have "(\<Sum>j\<le>n. ((1 - t) * x j + t * y j)\<^sup>2) /
          (\<Sum>j\<le>n. ((1 - t) * x j + t * y j)\<^sup>2) = 1"
        using hNt by (by100 simp)
      finally show "(\<Sum>j\<le>n. (((1 - t) * x j + t * y j) / ?N t)\<^sup>2) = 1" .
    qed
  qed
  \<comment> \<open>Step 3: \<gamma>(0) = x and \<gamma>(1) = y.\<close>
  have h\<gamma>0: "\<gamma> 0 = x"
  proof (rule ext)
    fix i
    have "?N 0 = sqrt (\<Sum>j\<le>n. (x j)^2)" by (by100 simp)
    also have "\<dots> = 1" using hx_norm0 by (by100 simp)
    finally have hN0: "?N 0 = 1" .
    show "\<gamma> 0 i = x i" unfolding \<gamma>_def using hN0 by (by100 simp)
  qed
  have h\<gamma>1: "\<gamma> 1 = y"
  proof (rule ext)
    fix i
    have "?N 1 = sqrt (\<Sum>j\<le>n. (y j)^2)" by (by100 simp)
    also have "\<dots> = 1" using hy_norm0 by (by100 simp)
    finally have hN1: "?N 1 = 1" .
    show "\<gamma> 1 i = y i" unfolding \<gamma>_def using hN1 by (by100 simp)
  qed
  \<comment> \<open>Step 4: \<gamma> is continuous I \<rightarrow> S^n in the subspace topology.\<close>
  have h\<gamma>_cont: "top1_continuous_map_on I_set I_top (top1_Sn n) ?TSn \<gamma>"
  proof -
    \<comment> \<open>Each coordinate of \<gamma> is continuous: polynomial / sqrt(polynomial), with sqrt > 0.\<close>
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTop_each: "\<forall>j\<in>(UNIV::nat set). is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
      using top1_open_sets_is_topology_on_UNIV by (by100 simp)
    \<comment> \<open>Numerator for coordinate i: (1-t)*x(i) + t*y(i) is continuous_on I_set.\<close>
    have hnum_cont: "\<And>i. continuous_on I_set (\<lambda>t. (1-t) * x i + t * y i)"
      by (intro continuous_intros)
    \<comment> \<open>The sum under sqrt: \<Sum>j\<le>n ((1-t)*x(j)+t*y(j))^2 is continuous_on I_set.\<close>
    have hsumsq_cont: "continuous_on I_set (\<lambda>t. \<Sum>j\<le>n. ((1-t) * x j + t * y j)^2)"
      by (intro continuous_intros)
    \<comment> \<open>N(t) = sqrt(...) is continuous_on I_set.\<close>
    have hN_cont: "continuous_on I_set ?N"
      by (rule continuous_on_real_sqrt[OF hsumsq_cont])
    \<comment> \<open>N(t) \<noteq> 0 on I_set.\<close>
    have hN_ne: "\<forall>t\<in>I_set. ?N t \<noteq> 0"
    proof (intro ballI)
      fix t assume "t \<in> I_set"
      have "?N t > 0" using hN_pos by (by100 blast)
      thus "?N t \<noteq> 0" by (by100 linarith)
    qed
    \<comment> \<open>Each coordinate: ((1-t)*x(i)+t*y(i)) / N(t) is continuous_on I_set.\<close>
    have hcoord_cont: "\<And>i. continuous_on I_set (\<lambda>t. ((1-t) * x i + t * y i) / ?N t)"
    proof -
      fix i
      show "continuous_on I_set (\<lambda>t. ((1-t) * x i + t * y i) / ?N t)"
        by (rule continuous_on_divide[OF hnum_cont hN_cont hN_ne])
    qed
    \<comment> \<open>Bridge: continuous_on I_set gives top1_continuous_map_on I_set I_top UNIV top1_open_sets.\<close>
    have hcoord_top: "\<And>i. top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets
        (\<lambda>t. ((1-t) * x i + t * y i) / ?N t)"
    proof -
      fix i
      have hc: "continuous_on I_set (\<lambda>t. ((1-t) * x i + t * y i) / ?N t)" by (rule hcoord_cont)
      have hrange: "\<And>t. t \<in> I_set \<Longrightarrow> ((1-t) * x i + t * y i) / ?N t \<in> (UNIV::real set)"
        by (by100 simp)
      have "top1_continuous_map_on I_set
          (subspace_topology UNIV top1_open_sets I_set)
          (UNIV::real set) (subspace_topology UNIV (top1_open_sets::real set set) UNIV)
          (\<lambda>t. ((1-t) * x i + t * y i) / ?N t)"
        by (rule top1_continuous_map_on_subspace_open_sets_on[OF hrange hc])
      thus "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets
          (\<lambda>t. ((1-t) * x i + t * y i) / ?N t)"
      proof -
        have heq1: "subspace_topology UNIV (top1_open_sets::real set set) UNIV = top1_open_sets"
          unfolding subspace_topology_def by (by100 auto)
        have heq2: "subspace_topology UNIV top1_open_sets I_set = I_top"
          unfolding top1_unit_interval_topology_def by (by100 simp)
        show ?thesis
          using top1_continuous_map_on_subspace_open_sets_on[OF hrange hc]
          unfolding heq1 heq2 .
      qed
    qed
    \<comment> \<open>The coordinate function is \<gamma> t i.\<close>
    have hcoord_eq: "\<And>i t. \<gamma> t i = ((1-t) * x i + t * y i) / ?N t"
      unfolding \<gamma>_def by (by100 simp)
    \<comment> \<open>Apply Theorem 19.6: \<gamma> continuous iff each coordinate continuous.\<close>
    have h\<gamma>_UNIV: "top1_continuous_map_on I_set I_top
        (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
        (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets)) \<gamma>"
    proof -
      have hmap: "\<forall>t\<in>I_set. \<gamma> t \<in> top1_PiE UNIV (\<lambda>_::nat. UNIV::real set)"
        unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
      have hcoords: "\<forall>i\<in>(UNIV::nat set). top1_continuous_map_on I_set I_top
          (UNIV::real set) top1_open_sets (\<lambda>t. (\<gamma> t) i)"
      proof (intro ballI)
        fix i :: nat
        show "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (\<lambda>t. (\<gamma> t) i)"
          using hcoord_top[of i] hcoord_eq by (by100 simp)
      qed
      show ?thesis using iffD2[OF Theorem_19_6[OF hTI hTop_each hmap]] hcoords by (by100 blast)
    qed
    \<comment> \<open>Restrict codomain from UNIV to S^n using h\<gamma>_Sn.\<close>
    have h\<gamma>_img: "\<forall>t\<in>I_set. \<gamma> t \<in> top1_Sn n" using h\<gamma>_Sn by (by100 blast)
    have hPiE_eq: "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
      unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
    have h\<gamma>_img2: "\<gamma> ` I_set \<subseteq> top1_Sn n" using h\<gamma>_img by (by100 blast)
    show ?thesis
      using top1_continuous_map_on_codomain_shrink[OF h\<gamma>_UNIV[unfolded hPiE_eq] h\<gamma>_img2]
      by (by100 simp)
  qed
  show ?thesis unfolding top1_is_path_on_def
    using h\<gamma>_cont h\<gamma>0 h\<gamma>1 by (by100 blast)
qed
text \<open>Helper corollaries of Sn_normalized_interpolation_path: membership and norm.\<close>
lemma Sn_interpolation_norm_pos:
  fixes x y :: "nat \<Rightarrow> real"
  assumes "x \<in> top1_Sn n" "y \<in> top1_Sn n" "x \<noteq> (\<lambda>i. - y i)"
  shows "sqrt (\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2) > 0"
proof -
  have hx_norm: "(\<Sum>j\<le>n. (x j)^2) = 1" using assms(1) unfolding top1_Sn_def by (by100 blast)
  have hy_norm: "(\<Sum>j\<le>n. (y j)^2) = 1" using assms(2) unfolding top1_Sn_def by (by100 blast)
  have hx_zero: "\<And>i. i \<ge> Suc n \<Longrightarrow> x i = 0" using assms(1) unfolding top1_Sn_def by (by100 blast)
  have hy_zero: "\<And>i. i \<ge> Suc n \<Longrightarrow> y i = 0" using assms(2) unfolding top1_Sn_def by (by100 blast)
  have "\<exists>k\<le>n. (1-t) * x k + t * y k \<noteq> 0"
  proof (rule ccontr)
    assume "\<not>(\<exists>k\<le>n. (1-t) * x k + t * y k \<noteq> 0)"
    hence hall: "\<And>k. k \<le> n \<Longrightarrow> (1-t) * x k + t * y k = 0" by (by100 blast)
    show False
    proof (cases "t = 0")
      case True hence "\<And>k. k \<le> n \<Longrightarrow> x k = 0" using hall by (by100 simp)
      hence "(\<Sum>j\<le>n. (x j)^2) = 0" by (by100 simp)
      thus False using hx_norm by (by100 linarith)
    next
      case ht0: False show False
      proof (cases "t = 1")
        case True hence "\<And>k. k \<le> n \<Longrightarrow> y k = 0" using hall by (by100 simp)
        hence "(\<Sum>j\<le>n. (y j)^2) = 0" by (by100 simp)
        thus False using hy_norm by (by100 linarith)
      next
        case False hence ht1: "1-t \<noteq> 0" by (by100 linarith)
        have hxi: "\<And>k. k \<le> n \<Longrightarrow> x k = -(t/(1-t)) * y k"
        proof -
          fix k assume hk: "k \<le> n"
          have h1: "(1-t) * x k = -(t * y k)" using hall[OF hk] by (by100 linarith)
          have "x k = (1-t) * x k / (1-t)" using ht1 by (by100 simp)
          also have "\<dots> = -(t * y k) / (1-t)" using h1 by (by100 simp)
          finally show "x k = -(t/(1-t)) * y k" by (by100 simp)
        qed
        have hxi_all: "\<And>i. x i = -(t/(1-t)) * y i"
        proof -
          fix i show "x i = -(t/(1-t)) * y i"
            using hxi[of i] hx_zero[of i] hy_zero[of i] by (cases "i \<le> n") (by100 simp)+
        qed
        have "(\<Sum>j\<le>n. (x j)^2) = (\<Sum>j\<le>n. (-(t/(1-t)) * y j)^2)"
          using hxi by (intro sum.cong) (by100 simp)+
        also have "\<dots> = (\<Sum>j\<le>n. (t/(1-t))^2 * (y j)^2)"
          using power_mult_distrib[of "-(t/(1-t))" _ 2]
          by (intro sum.cong) (by100 simp)+
        also have "\<dots> = (t/(1-t))^2 * (\<Sum>j\<le>n. (y j)^2)"
          by (rule sum_distrib_left[symmetric])
        finally have hratio: "(t/(1-t))^2 = 1" using hx_norm hy_norm by (by100 simp)
        have h_sq: "(\<bar>t/(1-t)\<bar>)^2 = (1::real)^2"
          using hratio power2_abs[of "t/(1-t)"] by (by100 simp)
        have "\<bar>t/(1-t)\<bar> = (1::real)"
          by (rule power2_eq_imp_eq[OF h_sq]) (by100 simp)+
        hence "t/(1-t) = 1 \<or> t/(1-t) = -1" by (by100 linarith)
        thus False
        proof
          assume ht_eq: "t/(1-t) = 1"
          have "\<And>i. x i = -y i"
          proof -
            fix i have "x i = -(t/(1-t)) * y i" by (rule hxi_all)
            thus "x i = -y i" using ht_eq by (by100 simp)
          qed
          hence "x = (\<lambda>i. -y i)" by (rule ext)
          thus False using assms(3) by (by100 blast)
        next
          assume ht_eq: "t/(1-t) = -1"
          have "\<And>i. x i = y i"
          proof -
            fix i have "x i = -(t/(1-t)) * y i" by (rule hxi_all)
            thus "x i = y i" using ht_eq by (by100 simp)
          qed
          hence "x = y" by (rule ext)
          have "\<And>k. k \<le> n \<Longrightarrow> y k = 0"
          proof -
            fix k assume hk: "k \<le> n"
            have "(1-t) * y k + t * y k = 0" using hall[OF hk] \<open>x = y\<close> by (by100 simp)
            thus "y k = 0" by (by100 algebra)
          qed
          hence "(\<Sum>j\<le>n. (y j)^2) = 0" by (by100 simp)
          thus False using hy_norm by (by100 linarith)
        qed
      qed
    qed
  qed
  then obtain k where hk: "k \<le> n" "(1-t) * x k + t * y k \<noteq> 0" by (by100 blast)
  have "(\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2) \<ge> ((1-t) * x k + t * y k)^2"
  proof -
    have hk_in: "k \<in> {..n}" using hk(1) by (by100 blast)
    have "(\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2) =
          ((1-t) * x k + t * y k)^2 + (\<Sum>j\<in>{..n}-{k}. ((1-t) * x j + t * y j)^2)"
      using sum.remove[OF finite_atMost hk_in] by (by100 simp)
    moreover have "(\<Sum>j\<in>{..n}-{k}. ((1-t) * x j + t * y j)^2) \<ge> 0"
      by (rule sum_nonneg) (by100 simp)
    ultimately show ?thesis by (by100 linarith)
  qed
  moreover have "((1-t) * x k + t * y k)^2 > 0" using hk(2) by (by100 simp)
  ultimately have "(\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2) > 0" by (by100 linarith)
  thus ?thesis by (by100 simp)
qed


lemma Sn_interpolation_in_Sn:
  fixes x y :: "nat \<Rightarrow> real"
  assumes hx: "x \<in> top1_Sn n" and hy: "y \<in> top1_Sn n" and hna: "x \<noteq> (\<lambda>i. - y i)"
  shows "(\<lambda>i. ((1-t) * x i + t * y i) / sqrt (\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2)) \<in> top1_Sn n"
proof -
  let ?N = "sqrt (\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2)"
  have hN_pos: "?N > 0" by (rule Sn_interpolation_norm_pos[OF assms])
  have hx_zero: "\<And>i. i \<ge> Suc n \<Longrightarrow> x i = 0" using hx unfolding top1_Sn_def by (by100 blast)
  have hy_zero: "\<And>i. i \<ge> Suc n \<Longrightarrow> y i = 0" using hy unfolding top1_Sn_def by (by100 blast)
  show ?thesis unfolding top1_Sn_def
  proof (intro CollectI conjI allI impI)
    fix i assume "i \<ge> Suc n"
    hence "x i = 0" "y i = 0" using hx_zero hy_zero by (by100 blast)+
    thus "((1-t) * x i + t * y i) / ?N = 0" by (by100 simp)
  next
    have "(\<Sum>j\<le>n. (((1-t) * x j + t * y j) / ?N)^2) = (\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2) / ?N^2"
    proof -
      have "\<And>j. (((1-t) * x j + t * y j) / ?N)^2 = ((1-t) * x j + t * y j)^2 / ?N^2"
        using power_divide by (by100 blast)
      hence "(\<Sum>j\<le>n. (((1-t) * x j + t * y j) / ?N)^2) = (\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2 / ?N^2)"
        by (intro sum.cong) (by100 simp)+
      also have "\<dots> = (\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2) / ?N^2"
        using sum_divide_distrib[symmetric] by (by100 simp)
      finally show ?thesis .
    qed
    also have "?N^2 = (\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2)" using hN_pos by (by100 simp)
    also have "(\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2) / (\<Sum>j\<le>n. ((1-t) * x j + t * y j)^2) = 1"
      using hN_pos by (by100 simp)
    finally show "(\<Sum>j\<le>n. (((1-t) * x j + t * y j) / ?N)^2) = 1" .
  qed
qed



lemma Sn_interpolation_at_1:
  fixes x y :: "nat \<Rightarrow> real"
  assumes "x \<in> top1_Sn n" "y \<in> top1_Sn n" "x \<noteq> (\<lambda>i. - y i)"
  shows "(\<lambda>i. ((1-(1::real)) * x i + 1 * y i) / sqrt (\<Sum>j\<le>n. ((1-1) * x j + 1 * y j)^2)) = y"
proof -
  have hy_norm: "(\<Sum>j\<le>n. (y j)^2) = 1" using assms(2) unfolding top1_Sn_def by (by100 blast)
  have hN: "(\<Sum>j\<le>n. ((1-(1::real)) * x j + 1 * y j)^2) = (\<Sum>j\<le>n. (y j)^2)"
    by (intro sum.cong) (by100 simp)+
  have hN1: "sqrt (\<Sum>j\<le>n. ((1-(1::real)) * x j + 1 * y j)^2) = 1" using hN hy_norm by (by100 simp)
  show ?thesis
  proof (rule ext)
    fix i show "((1-(1::real)) * x i + 1 * y i) / sqrt (\<Sum>j\<le>n. ((1-1) * x j + 1 * y j)^2) = y i"
      using hN1 by (by100 simp)
  qed
qed

(** from \<S>59 Theorem 59.3: for n \<ge> 2, S^n is simply connected.

    Munkres' proof (2 steps):
    Step 1: S^n - p is homeomorphic to R^n via stereographic projection.
    Step 2: Apply Corollary 59.2 with U = S^n - p, V = S^n - q. **)

text \<open>Key fact: the normalized interpolation from x \<in> S^n-\{p\} to q never hits p.
  Proof: normalize((1-t)x + tq) = p requires x(i)=0 for all i\<ge>1, hence x = \<plusminus>p.
  Since x \<noteq> p and x = q gives the constant path q \<noteq> p.\<close>
lemma Sn_interpolation_to_q_avoids_p:
  fixes n :: nat and x :: "nat \<Rightarrow> real"
  assumes hx: "x \<in> top1_Sn n" and hxnp: "x \<noteq> (\<lambda>i. if i = 0 then 1 else 0)"
  defines "p \<equiv> \<lambda>i::nat. if i = 0 then (1::real) else 0"
      and "q \<equiv> \<lambda>i::nat. if i = 0 then (-1::real) else 0"
  shows "\<forall>t. (\<lambda>i. ((1-t) * x i + t * q i) /
          sqrt (\<Sum>j\<le>n. ((1-t) * x j + t * q j)^2)) \<noteq> p"
proof (intro allI notI)
  fix t
  let ?\<gamma> = "\<lambda>i. ((1-t) * x i + t * q i) /
          sqrt (\<Sum>j\<le>n. ((1-t) * x j + t * q j)^2)"
  assume heq: "?\<gamma> = p"
  \<comment> \<open>If \<gamma>(t) = p, then (1-t)x(i) + tq(i) = c\<cdot>p(i) for some c > 0.\<close>
  have hN_pos: "sqrt (\<Sum>j\<le>n. ((1-t) * x j + t * q j)^2) > 0"
  proof -
    have hna: "x \<noteq> (\<lambda>i. - q i)"
    proof
      assume hxnq: "x = (\<lambda>i. - q i)"
      have "(\<lambda>i::nat. - q i) = p" unfolding q_def p_def by (rule ext) (by100 simp)
      hence "x = p" using hxnq by (by100 simp)
      thus False using hxnp unfolding p_def by (by100 blast)
    qed
    \<comment> \<open>Same argument as Sn_normalized_interpolation_path.hN_pos: x \<noteq> -q \<Longrightarrow> norm > 0.\<close>
    have "\<exists>k\<le>n. (1-t) * x k + t * q k \<noteq> 0"
    proof (rule ccontr)
      assume "\<not>(\<exists>k\<le>n. (1-t) * x k + t * q k \<noteq> 0)"
      hence hall: "\<And>k. k \<le> n \<Longrightarrow> (1-t) * x k + t * q k = 0" by (by100 blast)
      have hq_zero_above: "\<And>i. i \<ge> Suc n \<Longrightarrow> q i = 0" unfolding q_def by (by100 simp)
      \<comment> \<open>Then x = -q by the hN_pos argument, contradicting hna.\<close>
      have "x = (\<lambda>i. - q i)"
      proof (cases "t = 0")
        case True hence "\<And>k. k \<le> n \<Longrightarrow> x k = 0" using hall by (by100 simp)
        hence "(\<Sum>j\<le>n. (x j)^2) = 0" by (by100 simp)
        moreover have "(\<Sum>j\<le>n. (x j)^2) = 1" using hx unfolding top1_Sn_def by (by100 blast)
        ultimately have False by (by100 linarith)
        thus ?thesis by (by100 blast)
      next
        case ht0: False show ?thesis
        proof (cases "t = 1")
          case True
          have hall_q: "\<And>k. k \<le> n \<Longrightarrow> q k = 0" using hall True by (by100 simp)
          have "0 \<le> n" using assms by (by100 linarith)
          hence "q 0 = 0" using hall_q[of 0] by (by100 simp)
          hence False unfolding q_def by (by100 simp)
          thus ?thesis by (by100 blast)
        next
          case False hence ht1: "1-t \<noteq> 0" by (by100 linarith)
          have "\<And>k. k \<le> n \<Longrightarrow> x k = -(t/(1-t)) * q k"
          proof -
            fix k assume hk: "k \<le> n"
            have "(1-t) * x k + t * q k = 0" by (rule hall[OF hk])
            hence "(1-t) * x k = -(t * q k)" by (by100 linarith)
            have "x k = (1-t) * x k / (1-t)" using ht1 by (by100 simp)
            also have "\<dots> = -(t * q k) / (1-t)" using \<open>(1-t) * x k = -(t * q k)\<close> by (by100 simp)
            finally show "x k = -(t/(1-t)) * q k" by (by100 simp)
          qed
          moreover have "\<And>i. i \<ge> Suc n \<Longrightarrow> x i = -(t/(1-t)) * q i"
          proof -
            fix i assume hi: "i \<ge> Suc n"
            have "x i = 0" using hx hi unfolding top1_Sn_def by (by100 blast)
            moreover have "q i = 0" using hq_zero_above hi by (by100 blast)
            ultimately show "x i = -(t/(1-t)) * q i" by (by100 simp)
          qed
          ultimately have hxi_all: "\<And>i. x i = -(t/(1-t)) * q i"
          proof -
            fix i
            assume hle: "\<And>k. k \<le> n \<Longrightarrow> x k = -(t/(1-t)) * q k"
               and hge: "\<And>j. j \<ge> Suc n \<Longrightarrow> x j = -(t/(1-t)) * q j"
            show "x i = -(t/(1-t)) * q i"
              using hle[of i] hge[of i] by (cases "i \<le> n") (by100 simp)+
          qed
          \<comment> \<open>From ||x||=1: (t/(1-t))^2 * ||q||^2 = 1, so (t/(1-t))^2=1, so t/(1-t)=\<plusminus>1.\<close>
          have "x = (\<lambda>i. -(t/(1-t)) * q i)" by (rule ext) (rule hxi_all)
          \<comment> \<open>Since hna: x \<noteq> -q, if t/(1-t)=1 then x=-q contradiction. So t/(1-t)=-1 and x=q.
             But then ||x||=||q||=1 and (1-t)*q+t*q=q\<noteq>0, contradicting hall.\<close>
          \<comment> \<open>||x||=1 and x=-(t/(1-t))*q with ||q||=1 gives (t/(1-t))^2=1.\<close>
          have hx_norm_loc: "(\<Sum>j\<le>n. (x j)^2) = 1" using hx unfolding top1_Sn_def by (by100 blast)
          have hq_norm_loc: "(\<Sum>j\<le>n. (q j)^2) = 1"
          proof -
            have "(\<Sum>j\<le>n. (q j)^2) = (\<Sum>j\<le>n. (if j = 0 then 1 else 0::real))"
              unfolding q_def by (intro sum.cong) (by100 simp)+
            also have "\<dots> = 1" using sum.delta'[of "{..n}" 0 "\<lambda>_. (1::real)"] assms by (by100 simp)
            finally show ?thesis .
          qed
          have "(\<Sum>j\<le>n. (x j)^2) = (\<Sum>j\<le>n. (-(t/(1-t)) * q j)^2)"
            using hxi_all by (intro sum.cong) (by100 simp)+
          also have "\<dots> = (\<Sum>j\<le>n. (t/(1-t))^2 * (q j)^2)"
            using power_mult_distrib[of "-(t/(1-t))" _ 2]
            by (intro sum.cong) (by100 simp)+
          also have "\<dots> = (t/(1-t))^2 * (\<Sum>j\<le>n. (q j)^2)"
            by (rule sum_distrib_left[symmetric])
          finally have "(t/(1-t))^2 = 1" using hx_norm_loc hq_norm_loc by (by100 simp)
          have h_sq: "(\<bar>t/(1-t)\<bar>)^2 = (1::real)^2"
            using \<open>(t/(1-t))^2 = 1\<close> power2_abs[of "t/(1-t)"] by (by100 simp)
          have "\<bar>t/(1-t)\<bar> = (1::real)"
            by (rule power2_eq_imp_eq[OF h_sq]) (by100 simp)+
          hence "t/(1-t) = 1 \<or> t/(1-t) = -1" by (by100 linarith)
          thus ?thesis
          proof
            assume ht_eq: "t/(1-t) = 1"
            have "\<And>i. x i = -q i"
            proof -
              fix i have "x i = -(t/(1-t)) * q i" by (rule hxi_all)
              thus "x i = -q i" using ht_eq by (by100 simp)
            qed
            thus ?thesis by (rule ext)
          next
            assume ht_eq: "t/(1-t) = -1"
            have "\<And>i. x i = q i"
            proof -
              fix i have "x i = -(t/(1-t)) * q i" by (rule hxi_all)
              thus "x i = q i" using ht_eq by (by100 simp)
            qed
            hence "x = q" by (rule ext)
            hence "(1-t) * q 0 + t * q 0 = 0" using hall[of 0] assms by (by100 simp)
            hence "q 0 = 0" by (by100 algebra)
            thus ?thesis unfolding q_def by (by100 simp)
          qed
        qed
      qed
      thus False using hna by (by100 blast)
    qed
    then obtain k where hk: "k \<le> n" "(1-t) * x k + t * q k \<noteq> 0" by (by100 blast)
    have "((1-t) * x k + t * q k)^2 > 0" using hk(2) by (by100 simp)
    moreover have "(\<Sum>j\<le>n. ((1-t) * x j + t * q j)^2) \<ge> ((1-t) * x k + t * q k)^2"
    proof -
      have "(\<Sum>j\<le>n. ((1-t) * x j + t * q j)^2) =
            ((1-t) * x k + t * q k)^2 + (\<Sum>j\<in>{..n}-{k}. ((1-t) * x j + t * q j)^2)"
        using sum.remove[of "{..n}" k] hk(1) by (by100 simp)
      moreover have "(\<Sum>j\<in>{..n}-{k}. ((1-t) * x j + t * q j)^2) \<ge> 0"
        by (rule sum_nonneg) (by100 simp)
      ultimately show ?thesis by (by100 linarith)
    qed
    ultimately have "(\<Sum>j\<le>n. ((1-t) * x j + t * q j)^2) > 0" by (by100 linarith)
    thus ?thesis by (by100 simp)
  qed
  let ?N = "sqrt (\<Sum>j\<le>n. ((1-t) * x j + t * q j)^2)"
  \<comment> \<open>From \<gamma>(t) = p: for each i, ((1-t)*x(i) + t*q(i)) / N = p(i).\<close>
  have hcoord: "\<And>i. ((1-t) * x i + t * q i) / ?N = p i"
  proof -
    fix i
    have "?\<gamma> i = p i" using fun_cong[OF heq, of i] by (by100 simp)
    thus "((1-t) * x i + t * q i) / ?N = p i" by (by100 simp)
  qed
  \<comment> \<open>For i \<ge> 1: p(i) = 0, so (1-t)*x(i) + t*q(i) = 0. Since q(i)=0 for i\<ge>1: (1-t)*x(i)=0.\<close>
  have hxi_zero: "\<And>i. i \<ge> 1 \<Longrightarrow> (1-t) * x i = 0"
  proof -
    fix i :: nat assume hi: "i \<ge> 1"
    have "p i = 0" unfolding p_def using hi by (by100 simp)
    hence "((1-t) * x i + t * q i) / ?N = 0" using hcoord[of i] by (by100 simp)
    hence "(1-t) * x i + t * q i = 0" using hN_pos by (by100 simp)
    moreover have "t * q i = 0" unfolding q_def using hi by (by100 simp)
    ultimately show "(1-t) * x i = 0" by (by100 linarith)
  qed
  \<comment> \<open>Case 1: t = 1. Then \<gamma>(1) = normalize(q) = q. But q \<noteq> p.\<close>
  \<comment> \<open>Case 2: t \<noteq> 1. Then x(i) = 0 for i \<ge> 1. So x = (x(0), 0, 0, ...).
     From x \<in> S^n: x(0)^2 = 1, so x = p or x = q. Since x \<noteq> p: x = q.
     But then \<gamma>(t) = normalize((1-t)q + tq) = normalize(q) = q \<noteq> p. Contradiction.\<close>
  have hq_Sn: "q \<in> top1_Sn n" unfolding q_def top1_Sn_def
  proof (intro CollectI conjI allI impI)
    fix i :: nat assume "i \<ge> Suc n"
    thus "(if i = 0 then - 1::real else 0) = 0" by (by100 simp)
  next
    have "(\<Sum>i\<le>n. (if i = 0 then - 1::real else 0)\<^sup>2) = (\<Sum>i\<le>n. (if i = 0 then 1 else 0::real))"
      by (intro sum.cong) (by100 simp)+
    also have "\<dots> = 1" using sum.delta'[of "{..n}" 0 "\<lambda>_. (1::real)"] assms by (by100 simp)
    finally show "(\<Sum>i\<le>n. (if i = 0 then - 1::real else 0)\<^sup>2) = 1" .
  qed
  have hq_norm: "(\<Sum>j\<le>n. (q j)^2) = 1" using hq_Sn unfolding top1_Sn_def by (by100 blast)
  show False
  proof (cases "t = 1")
    case True
    have hN1: "?N = 1" using True hq_norm by (by100 simp)
    have "?\<gamma> = q"
    proof (rule ext)
      fix i show "?\<gamma> i = q i" using True hN1 by (by100 simp)
    qed
    hence "p = q" using heq by (by100 simp)
    hence "p 0 = q 0" by (by100 simp)
    thus False unfolding p_def q_def by (by100 simp)
  next
    case False
    hence ht1: "1 - t \<noteq> 0" by (by100 linarith)
    have hxi0: "\<And>i. i \<ge> 1 \<Longrightarrow> x i = 0" using hxi_zero ht1 by (by100 simp)
    have hx_zero_above: "\<And>i. i \<ge> Suc n \<Longrightarrow> x i = 0"
      using hx unfolding top1_Sn_def by (by100 blast)
    have hx_norm: "(\<Sum>j\<le>n. (x j)^2) = 1" using hx unfolding top1_Sn_def by (by100 blast)
    have "x 0 ^ 2 = 1"
    proof -
      have "(\<Sum>j\<le>n. (x j)^2) = (x 0)^2"
      proof -
        have "\<And>j. j \<in> {1..n} \<Longrightarrow> (x j)^2 = 0"
        proof -
          fix j assume "j \<in> {1..n}"
          hence "j \<ge> 1" by (by100 simp)
          hence "x j = 0" by (rule hxi0)
          thus "(x j)^2 = 0" by (by100 simp)
        qed
        hence hzero: "(\<Sum>j\<in>{1..n}. (x j)^2) = 0" by (intro sum.neutral) (by100 blast)
        have "(\<Sum>j\<le>n. (x j)^2) = (\<Sum>j\<in>{0..n}. (x j)^2)"
          using atLeast0AtMost by (by100 metis)
        also have "\<dots> = (x 0)^2 + (\<Sum>j\<in>{1..n}. (x j)^2)"
        proof -
          have "0 \<le> n" using assms by (by100 linarith)
          thus ?thesis using sum.atLeast_Suc_atMost[of 0 n "\<lambda>j. (x j)^2"] by (by100 simp)
        qed
        finally have "(\<Sum>j\<le>n. (x j)^2) = (x 0)^2 + (\<Sum>j\<in>{1..n}. (x j)^2)" .
        thus ?thesis using hzero by (by100 simp)
      qed
      thus ?thesis using hx_norm by (by100 linarith)
    qed
    hence "x 0 = 1 \<or> x 0 = -1"
    proof -
      assume "x 0 ^ 2 = 1"
      have "(\<bar>x 0\<bar>)^2 = 1" using \<open>x 0 ^ 2 = 1\<close> power2_abs[of "x 0"] by (by100 simp)
      hence "\<bar>x 0\<bar> = 1"
        using power2_eq_imp_eq[of "\<bar>x 0\<bar>" 1] by (by100 simp)
      thus ?thesis by (by100 linarith)
    qed
    thus False
    proof
      assume "x 0 = 1"
      have "\<And>i. x i = p i"
      proof -
        fix i show "x i = p i"
        proof (cases "i = 0")
          case True thus ?thesis using \<open>x 0 = 1\<close> unfolding p_def by (by100 simp)
        next
          case False hence "i \<ge> 1" by (by100 linarith)
          hence "x i = 0" by (rule hxi0)
          thus ?thesis unfolding p_def using False by (by100 simp)
        qed
      qed
      hence "x = p" by (rule ext)
      thus False using hxnp unfolding p_def by (by100 blast)
    next
      assume "x 0 = -1"
      \<comment> \<open>Then x = q, and \<gamma>(t) = normalize((1-t)q + tq) = q \<noteq> p.\<close>
      have hxq: "x = q"
      proof (rule ext)
        fix i show "x i = q i"
        proof (cases "i = 0")
          case True thus ?thesis using \<open>x 0 = -1\<close> unfolding q_def by (by100 simp)
        next
          case False hence "i \<ge> 1" by (by100 linarith)
          hence "x i = 0" by (rule hxi0)
          thus ?thesis unfolding q_def using False by (by100 simp)
        qed
      qed
      have hinterp_q: "\<And>i. (1-t) * x i + t * q i = q i"
      proof -
        fix i have "(1-t) * q i + t * q i = ((1-t) + t) * q i" by (by100 algebra)
        also have "\<dots> = q i" by (by100 simp)
        finally show "(1-t) * x i + t * q i = q i" using hxq by (by100 simp)
      qed
      have hNq: "?N = sqrt (\<Sum>j\<le>n. (q j)^2)" using hinterp_q
        by (intro arg_cong[of _ _ sqrt] sum.cong) (by100 simp)+
      also have "\<dots> = 1" using hq_norm by (by100 simp)
      finally have hN_1: "?N = 1" .
      have "?\<gamma> = q"
      proof (rule ext)
        fix i show "?\<gamma> i = q i" using hinterp_q hN_1 by (by100 simp)
      qed
      hence "p = q" using heq by (by100 simp)
      hence "p 0 = q 0" by (by100 simp)
    thus False unfolding p_def q_def by (by100 simp)
    qed
  qed
qed



lemma homeomorphism_preserves_path_connected:
  assumes hhom: "top1_homeomorphism_on X TX Y TY h"
      and hpc: "top1_path_connected_on X TX"
  shows "top1_path_connected_on Y TY"
  unfolding top1_path_connected_on_def
proof (intro conjI ballI)
  show "is_topology_on Y TY"
    using hhom unfolding top1_homeomorphism_on_def by (by100 blast)
next
  fix y1 y2 assume hy1: "y1 \<in> Y" and hy2: "y2 \<in> Y"
  have hTX: "is_topology_on X TX"
    using hhom unfolding top1_homeomorphism_on_def by (by100 blast)
  have hbij: "bij_betw h X Y"
    using hhom unfolding top1_homeomorphism_on_def by (by100 blast)
  have hcont: "top1_continuous_map_on X TX Y TY h"
    using hhom unfolding top1_homeomorphism_on_def by (by100 blast)
  obtain x1 where hx1: "x1 \<in> X" "h x1 = y1"
    using hy1 hbij unfolding bij_betw_def by (by100 blast)
  obtain x2 where hx2: "x2 \<in> X" "h x2 = y2"
    using hy2 hbij unfolding bij_betw_def by (by100 blast)
  obtain f where hf: "top1_is_path_on X TX x1 x2 f"
    using hpc hx1(1) hx2(1) unfolding top1_path_connected_on_def by (by100 blast)
  \<comment> \<open>h \<circ> f is a path from y1 to y2 in Y.\<close>
  have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_path_on_def by (by100 blast)
  have hhf_cont: "top1_continuous_map_on I_set I_top Y TY (h \<circ> f)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix t assume ht: "t \<in> I_set"
    have "f t \<in> X" using hf_cont ht unfolding top1_continuous_map_on_def by (by100 blast)
    thus "(h \<circ> f) t \<in> Y" using hcont unfolding top1_continuous_map_on_def comp_def by (by100 blast)
  next
    fix V assume hV: "V \<in> TY"
    have "{x \<in> X. h x \<in> V} \<in> TX" using hcont hV unfolding top1_continuous_map_on_def by (by100 blast)
    hence "{t \<in> I_set. f t \<in> {x \<in> X. h x \<in> V}} \<in> I_top"
      using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
    moreover have "{t \<in> I_set. (h \<circ> f) t \<in> V} = {t \<in> I_set. f t \<in> {x \<in> X. h x \<in> V}}"
    proof (rule set_eqI, rule iffI)
      fix t assume "t \<in> {t \<in> I_set. (h \<circ> f) t \<in> V}"
      hence ht: "t \<in> I_set" and hv: "h (f t) \<in> V" unfolding comp_def by auto
      have "f t \<in> X" using hf_cont ht unfolding top1_continuous_map_on_def by (by100 blast)
      thus "t \<in> {t \<in> I_set. f t \<in> {x \<in> X. h x \<in> V}}" using ht hv by (by100 blast)
    next
      fix t assume "t \<in> {t \<in> I_set. f t \<in> {x \<in> X. h x \<in> V}}"
      thus "t \<in> {t \<in> I_set. (h \<circ> f) t \<in> V}" unfolding comp_def by (by100 blast)
    qed
    ultimately show "{t \<in> I_set. (h \<circ> f) t \<in> V} \<in> I_top" by simp
  qed
  have "(h \<circ> f) 0 = y1" using hf hx1(2) unfolding top1_is_path_on_def comp_def by (by100 blast)
  moreover have "(h \<circ> f) 1 = y2" using hf hx2(2) unfolding top1_is_path_on_def comp_def by (by100 blast)
  ultimately have "top1_is_path_on Y TY y1 y2 (h \<circ> f)"
    unfolding top1_is_path_on_def using hhf_cont by (by100 blast)
  thus "\<exists>f. top1_is_path_on Y TY y1 y2 f" by (by100 blast)
qed

lemma homeomorphism_preserves_simply_connected:
  assumes hhom: "top1_homeomorphism_on X TX Y TY h"
      and hsc: "top1_simply_connected_on Y TY"
  shows "top1_simply_connected_on X TX"
  unfolding top1_simply_connected_on_def
proof (intro conjI allI impI ballI)
  have hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hbij: "bij_betw h X Y"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hg: "top1_continuous_map_on Y TY X TX (inv_into X h)"
    using hhom unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hg_cont: "top1_continuous_map_on Y TY X TX (inv_into X h)" by (rule hg)
  have hinj: "inj_on h X" using hbij unfolding bij_betw_def by simp
  have hh_inv: "\<And>x. x \<in> X \<Longrightarrow> inv_into X h (h x) = x"
    by (rule inv_into_f_f[OF hinj])
  have hh_map: "\<And>x. x \<in> X \<Longrightarrow> h x \<in> Y" using hbij unfolding bij_betw_def by auto
  have hg_map: "\<And>y. y \<in> Y \<Longrightarrow> inv_into X h y \<in> X"
    using hbij unfolding bij_betw_def by (simp add: inv_into_into)
  have hg_inv: "\<And>y. y \<in> Y \<Longrightarrow> h (inv_into X h y) = y"
    using hbij unfolding bij_betw_def by (simp add: f_inv_into_f)
  \<comment> \<open>Path-connected: transfer via h and inv.\<close>
  show "top1_path_connected_on X TX"
    unfolding top1_path_connected_on_def
  proof (intro conjI ballI)
    show "is_topology_on X TX" by (rule hTX)
  next
    fix x1 x2 assume hx1: "x1 \<in> X" and hx2: "x2 \<in> X"
    have "h x1 \<in> Y" by (rule hh_map[OF hx1])
    moreover have "h x2 \<in> Y" by (rule hh_map[OF hx2])
    ultimately obtain \<alpha> where h\<alpha>: "top1_is_path_on Y TY (h x1) (h x2) \<alpha>"
      using hsc unfolding top1_simply_connected_on_def top1_path_connected_on_def by (by100 blast)
    have "top1_is_path_on X TX (inv_into X h (h x1)) (inv_into X h (h x2)) (inv_into X h \<circ> \<alpha>)"
    proof -
      have h\<alpha>_cont: "top1_continuous_map_on I_set I_top Y TY \<alpha>"
        using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
      have hinv_\<alpha>_cont: "top1_continuous_map_on I_set I_top X TX (inv_into X h \<circ> \<alpha>)"
        by (rule top1_continuous_map_on_comp[OF h\<alpha>_cont hg])
      have "(\<alpha> 0) = h x1" using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
      hence h0: "(inv_into X h \<circ> \<alpha>) 0 = inv_into X h (h x1)" by simp
      have "(\<alpha> 1) = h x2" using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
      hence h1: "(inv_into X h \<circ> \<alpha>) 1 = inv_into X h (h x2)" by simp
      show ?thesis unfolding top1_is_path_on_def using hinv_\<alpha>_cont h0 h1 by (by100 blast)
    qed
    hence "top1_is_path_on X TX x1 x2 (inv_into X h \<circ> \<alpha>)"
      using hh_inv[OF hx1] hh_inv[OF hx2] by simp
    thus "\<exists>f. top1_is_path_on X TX x1 x2 f" by (by100 blast)
  qed
next
  fix x0 f
  assume hx0: "x0 \<in> X"
  assume hf: "top1_is_loop_on X TX x0 f"
  have hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hg: "top1_continuous_map_on Y TY X TX (inv_into X h)"
      and hbij: "bij_betw h X Y"
    using hhom unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hh_map: "\<And>x. x \<in> X \<Longrightarrow> h x \<in> Y" using hbij unfolding bij_betw_def by auto
  have hinj: "inj_on h X" using hbij unfolding bij_betw_def by simp
  have hh_inv: "\<And>x. x \<in> X \<Longrightarrow> inv_into X h (h x) = x"
    by (rule inv_into_f_f[OF hinj])
  \<comment> \<open>h\<circ>f is a loop at h(x0) in Y.\<close>
  have hhf_loop: "top1_is_loop_on Y TY (h x0) (h \<circ> f)"
    using top1_continuous_map_loop_early[OF hh hf] .
  \<comment> \<open>Y simply connected: h\<circ>f is contractible.\<close>
  have hhx0: "h x0 \<in> Y" by (rule hh_map[OF hx0])
  have hhf_contract: "top1_path_homotopic_on Y TY (h x0) (h x0)
      (h \<circ> f) (top1_constant_path (h x0))"
    using hsc hhx0 hhf_loop unfolding top1_simply_connected_on_def by (by100 blast)
  \<comment> \<open>Transfer back via inv_into: f = inv\<circ>h\<circ>f is contractible.\<close>
  have hg_transfer: "top1_path_homotopic_on X TX
      (inv_into X h (h x0)) (inv_into X h (h x0))
      (inv_into X h \<circ> (h \<circ> f)) (inv_into X h \<circ> top1_constant_path (h x0))"
    by (rule continuous_preserves_path_homotopic[OF hTY hTX hg hhf_contract])
  have "inv_into X h (h x0) = x0" by (rule hh_inv[OF hx0])
  moreover have "\<forall>s\<in>I_set. (inv_into X h \<circ> (h \<circ> f)) s = f s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "f s \<in> X" using hf hs
      unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def
      by (by100 blast)
    thus "(inv_into X h \<circ> (h \<circ> f)) s = f s" by (simp add: hh_inv)
  qed
  moreover have "\<forall>s\<in>I_set. (inv_into X h \<circ> top1_constant_path (h x0)) s = top1_constant_path x0 s"
    unfolding top1_constant_path_def using hh_inv[OF hx0] by simp
  ultimately have hinv_x0: "inv_into X h (h x0) = x0"
      and hinv_f: "\<forall>s\<in>I_set. (inv_into X h \<circ> (h \<circ> f)) s = f s"
      and hinv_c: "\<forall>s\<in>I_set. (inv_into X h \<circ> top1_constant_path (h x0)) s = top1_constant_path x0 s"
    by auto
  \<comment> \<open>Extract homotopy from hg_transfer, rebuild with I_set agreement.\<close>
  obtain H where hH_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX H"
      and hH0: "\<forall>s\<in>I_set. H (s, 0) = (inv_into X h \<circ> (h \<circ> f)) s"
      and hH1: "\<forall>s\<in>I_set. H (s, 1) = (inv_into X h \<circ> top1_constant_path (h x0)) s"
      and hHL: "\<forall>t\<in>I_set. H (0, t) = inv_into X h (h x0)"
      and hHR: "\<forall>t\<in>I_set. H (1, t) = inv_into X h (h x0)"
    using hg_transfer hinv_x0 unfolding top1_path_homotopic_on_def by auto
  have hfpath: "top1_is_path_on X TX x0 x0 f"
    using hf unfolding top1_is_loop_on_def .
  have hcpath: "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_path[OF hTX hx0])
  show "top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
    unfolding top1_path_homotopic_on_def
    using hfpath hcpath hH_cont
  proof (intro conjI exI[of _ H])
    show "\<forall>s\<in>I_set. H (s, 0) = f s" using hH0 hinv_f by simp
    show "\<forall>s\<in>I_set. H (s, 1) = top1_constant_path x0 s" using hH1 hinv_c by simp
    show "\<forall>t\<in>I_set. H (0, t) = x0" using hHL hinv_x0 by simp
    show "\<forall>t\<in>I_set. H (1, t) = x0" using hHR hinv_x0 by simp
  qed auto
qed

theorem Theorem_59_3:
  assumes "n \<ge> 2"
  shows "top1_simply_connected_on (top1_Sn n)
    (subspace_topology UNIV
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))
      (top1_Sn n))"
proof -
  let ?Sn = "top1_Sn n"
  let ?TSn = "subspace_topology UNIV
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets)) ?Sn"
  \<comment> \<open>Munkres 59.3: north pole p, south pole q.\<close>
  let ?p = "\<lambda>i::nat. if i = 0 then (1::real) else 0"
  let ?q = "\<lambda>i::nat. if i = 0 then (-1::real) else 0"
  let ?U = "?Sn - {?p}" and ?V = "?Sn - {?q}"
  \<comment> \<open>Step 1: U = S^n - {p} \<cong> R^n via stereographic projection, hence simply connected.\<close>
  have hU_sc: "top1_simply_connected_on ?U (subspace_topology ?Sn ?TSn ?U)"
    unfolding top1_simply_connected_on_def
  proof (intro conjI)
    have hTSn_loc: "is_topology_on ?Sn ?TSn"
    proof -
      have "\<forall>i\<in>(UNIV::nat set). is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
        using top1_open_sets_is_topology_on_UNIV by (by100 simp)
      hence "is_topology_on (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
          (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
        by (rule top1_product_topology_on_is_topology_on)
      moreover have "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
        unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
      ultimately have "is_topology_on (UNIV::(nat\<Rightarrow>real) set)
          (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))" by (by100 simp)
      thus ?thesis by (rule subspace_topology_is_topology_on) (by100 simp)
    qed
    have hTU: "is_topology_on ?U (subspace_topology ?Sn ?TSn ?U)"
      by (rule subspace_topology_is_topology_on[OF hTSn_loc]) (by100 blast)
    show "top1_path_connected_on ?U (subspace_topology ?Sn ?TSn ?U)"
      unfolding top1_path_connected_on_def
    proof (intro conjI ballI)
      show "is_topology_on ?U (subspace_topology ?Sn ?TSn ?U)" by (rule hTU)
    next
      fix x y assume hx: "x \<in> ?U" and hy: "y \<in> ?U"
      have hx_Sn: "x \<in> ?Sn" and hx_np: "x \<noteq> ?p" using hx by (by100 blast)+
      have hy_Sn: "y \<in> ?Sn" and hy_np: "y \<noteq> ?p" using hy by (by100 blast)+
      \<comment> \<open>q \<in> S^n and q \<noteq> p.\<close>
      have hq_Sn: "?q \<in> ?Sn" unfolding top1_Sn_def
      proof (intro CollectI conjI allI impI)
        fix i :: nat assume "i \<ge> Suc n" thus "(if i = 0 then -1::real else 0) = 0" by (by100 simp)
      next
        have "(\<Sum>i\<le>n. (if i = (0::nat) then -1::real else 0)\<^sup>2) = (\<Sum>i\<le>n. (if i = 0 then 1 else 0::real))"
          by (intro sum.cong) (by100 simp)+
        also have "\<dots> = 1" using sum.delta'[of "{..n}" 0 "\<lambda>_. (1::real)"] assms by (by100 simp)
        finally show "(\<Sum>i\<le>n. (if i = (0::nat) then - 1::real else 0)\<^sup>2) = 1" .
      qed
      have hq_np: "?q \<noteq> ?p"
      proof
        assume "?q = ?p" hence "?q 0 = ?p 0" using fun_cong[of ?q ?p 0] by (by100 simp)
        thus False by (by100 simp)
      qed
      have hq_U: "?q \<in> ?U" using hq_Sn hq_np by (by100 blast)
      \<comment> \<open>x \<noteq> -q (since -q = p and x \<noteq> p).\<close>
      have hx_na: "x \<noteq> (\<lambda>i. - ?q i)"
      proof
        assume "x = (\<lambda>i. - ?q i)"
        moreover have "(\<lambda>i::nat. - ?q i) = ?p" by (rule ext) (by100 simp)
        ultimately show False using hx_np by (by100 simp)
      qed
      have hy_na: "y \<noteq> (\<lambda>i. - ?q i)"
      proof
        assume "y = (\<lambda>i. - ?q i)"
        moreover have "(\<lambda>i::nat. - ?q i) = ?p" by (rule ext) (by100 simp)
        ultimately show False using hy_np by (by100 simp)
      qed
      \<comment> \<open>Path x \<rightarrow> q on S^n via interpolation, avoids p.\<close>
      let ?\<gamma>xq = "\<lambda>t i. ((1-t) * x i + t * ?q i) / sqrt (\<Sum>j\<le>n. ((1-t) * x j + t * ?q j)^2)"
      have hpath_xq: "top1_is_path_on ?Sn ?TSn x ?q ?\<gamma>xq"
        by (rule Sn_normalized_interpolation_path[OF hx_Sn hq_Sn hx_na])
      have havoids_xq: "\<forall>t. ?\<gamma>xq t \<noteq> ?p"
        by (rule Sn_interpolation_to_q_avoids_p[OF hx_Sn hx_np])
      \<comment> \<open>Path x \<rightarrow> q is in U = S^n - {p}: maps into S^n and avoids p.\<close>
      \<comment> \<open>Similarly path y \<rightarrow> q. Concatenate reverse(y\<rightarrow>q) with x\<rightarrow>q for x\<rightarrow>q\<rightarrow>y.\<close>
      \<comment> \<open>Convert S^n path that avoids p to S^n-{p} path via codomain_shrink.\<close>
      have hU_sub: "?U \<subseteq> ?Sn" by (by100 blast)
      have hxq_cont: "top1_continuous_map_on I_set I_top ?Sn ?TSn ?\<gamma>xq"
        using hpath_xq unfolding top1_is_path_on_def by (by100 blast)
      have hxq_img: "?\<gamma>xq ` I_set \<subseteq> ?U"
      proof (intro subsetI)
        fix z assume "z \<in> ?\<gamma>xq ` I_set"
        then obtain t where ht: "t \<in> I_set" and hz: "z = ?\<gamma>xq t" by (by100 blast)
        have "z \<in> ?Sn" using hz hxq_cont ht unfolding top1_continuous_map_on_def by (by100 blast)
        moreover have "z \<noteq> ?p"
        proof -
          have "?\<gamma>xq t \<noteq> ?p" using havoids_xq by (by100 blast)
          thus ?thesis using hz by (by100 simp)
        qed
        ultimately show "z \<in> ?U" by (by100 blast)
      qed
      have hxq_U: "top1_continuous_map_on I_set I_top ?U (subspace_topology ?Sn ?TSn ?U) ?\<gamma>xq"
        by (rule top1_continuous_map_on_codomain_shrink[OF hxq_cont hxq_img hU_sub])
      have hxq0: "?\<gamma>xq 0 = x" using hpath_xq unfolding top1_is_path_on_def by (by100 blast)
      have hxq1: "?\<gamma>xq 1 = ?q" using hpath_xq unfolding top1_is_path_on_def by (by100 blast)
      have hpath_xq_U: "top1_is_path_on ?U (subspace_topology ?Sn ?TSn ?U) x ?q ?\<gamma>xq"
        unfolding top1_is_path_on_def using hxq_U hxq0 hxq1 by (by100 blast)
      \<comment> \<open>Similarly path y \<rightarrow> q in U.\<close>
      let ?\<gamma>yq = "\<lambda>t i. ((1-t) * y i + t * ?q i) / sqrt (\<Sum>j\<le>n. ((1-t) * y j + t * ?q j)^2)"
      have hpath_yq: "top1_is_path_on ?Sn ?TSn y ?q ?\<gamma>yq"
        by (rule Sn_normalized_interpolation_path[OF hy_Sn hq_Sn hy_na])
      have havoids_yq: "\<forall>t. ?\<gamma>yq t \<noteq> ?p"
        by (rule Sn_interpolation_to_q_avoids_p[OF hy_Sn hy_np])
      have hyq_cont: "top1_continuous_map_on I_set I_top ?Sn ?TSn ?\<gamma>yq"
        using hpath_yq unfolding top1_is_path_on_def by (by100 blast)
      have hyq_img: "?\<gamma>yq ` I_set \<subseteq> ?U"
      proof (intro subsetI)
        fix z assume "z \<in> ?\<gamma>yq ` I_set"
        then obtain t where ht: "t \<in> I_set" and hz: "z = ?\<gamma>yq t" by (by100 blast)
        have "z \<in> ?Sn" using hz hyq_cont ht unfolding top1_continuous_map_on_def by (by100 blast)
        moreover have "z \<noteq> ?p"
        proof -
          have "?\<gamma>yq t \<noteq> ?p" using havoids_yq by (by100 blast)
          thus ?thesis using hz by (by100 simp)
        qed
        ultimately show "z \<in> ?U" by (by100 blast)
      qed
      have hyq_U: "top1_continuous_map_on I_set I_top ?U (subspace_topology ?Sn ?TSn ?U) ?\<gamma>yq"
        by (rule top1_continuous_map_on_codomain_shrink[OF hyq_cont hyq_img hU_sub])
      have hyq0: "?\<gamma>yq 0 = y" using hpath_yq unfolding top1_is_path_on_def by (by100 blast)
      have hyq1: "?\<gamma>yq 1 = ?q" using hpath_yq unfolding top1_is_path_on_def by (by100 blast)
      have hpath_yq_U: "top1_is_path_on ?U (subspace_topology ?Sn ?TSn ?U) y ?q ?\<gamma>yq"
        unfolding top1_is_path_on_def using hyq_U hyq0 hyq1 by (by100 blast)
      \<comment> \<open>Concatenate: x \<rightarrow> q (via \<gamma>xq), then q \<rightarrow> y (via reverse of \<gamma>yq).\<close>
      have hrev_yq: "top1_is_path_on ?U (subspace_topology ?Sn ?TSn ?U) ?q y (top1_path_reverse ?\<gamma>yq)"
        by (rule top1_path_reverse_is_path[OF hpath_yq_U])
      have hconcat: "top1_is_path_on ?U (subspace_topology ?Sn ?TSn ?U) x y
          (top1_path_product ?\<gamma>xq (top1_path_reverse ?\<gamma>yq))"
        by (rule top1_path_product_is_path[OF hTU hpath_xq_U hrev_yq])
      show "\<exists>f. top1_is_path_on ?U (subspace_topology ?Sn ?TSn ?U) x y f"
        using hconcat by (by100 blast)
    qed
  next
    show "\<forall>x0\<in>?U. \<forall>f. top1_is_loop_on ?U (subspace_topology ?Sn ?TSn ?U) x0 f \<longrightarrow>
        top1_path_homotopic_on ?U (subspace_topology ?Sn ?TSn ?U) x0 x0 f (top1_constant_path x0)"
    proof (intro ballI allI impI)
      fix x0 f assume hx0: "x0 \<in> ?U" and hf: "top1_is_loop_on ?U (subspace_topology ?Sn ?TSn ?U) x0 f"
      \<comment> \<open>Contract f to q via normalize((1-t)f(s)+tq). Stays in S^n-{p} by avoids_p.
         3-strip with \<alpha>(t) = normalize((1-t)x0+tq) on both sides gives:
         f \<simeq>_{path} \<alpha> * const_q * rev(\<alpha>) \<simeq> \<alpha> * rev(\<alpha>) \<simeq> const_{x0}.\<close>
      have hx0_Sn: "x0 \<in> ?Sn" and hx0_np: "x0 \<noteq> ?p" using hx0 by (by100 blast)+
      have hq_Sn: "?q \<in> ?Sn" unfolding top1_Sn_def
      proof (intro CollectI conjI allI impI)
        fix i :: nat assume "i \<ge> Suc n" thus "?q i = 0" by (by100 simp)
      next
        have "(\<Sum>i\<le>n. (?q i)\<^sup>2) = (\<Sum>i\<le>n. (if i = 0 then 1 else 0::real))"
          by (intro sum.cong) (by100 simp)+
        also have "\<dots> = 1" using sum.delta'[of "{..n}" 0 "\<lambda>_. (1::real)"] assms by (by100 simp)
        finally show "(\<Sum>i\<le>n. (?q i)\<^sup>2) = 1" .
      qed
      have hq_np: "?q \<noteq> ?p"
        by (rule) (use fun_cong[of ?q ?p 0] in \<open>by100 simp\<close>)
      have hq_U: "?q \<in> ?U" using hq_Sn hq_np by (by100 blast)
      have hx0_na: "x0 \<noteq> (\<lambda>i. - ?q i)"
      proof assume h: "x0 = (\<lambda>i. - ?q i)"
        have "(\<lambda>i::nat. - ?q i) = ?p" by (rule ext) (by100 simp)
        thus False using h hx0_np by (by100 simp)
      qed
      \<comment> \<open>\<alpha>: path from x0 to q in U (via interpolation).\<close>
      let ?\<alpha> = "\<lambda>t i. ((1-t) * x0 i + t * ?q i) / sqrt (\<Sum>j\<le>n. ((1-t) * x0 j + t * ?q j)^2)"
      have h\<alpha>_path_Sn: "top1_is_path_on ?Sn ?TSn x0 ?q ?\<alpha>"
        by (rule Sn_normalized_interpolation_path[OF hx0_Sn hq_Sn hx0_na])
      have h\<alpha>_avoids: "\<forall>t. ?\<alpha> t \<noteq> ?p"
        by (rule Sn_interpolation_to_q_avoids_p[OF hx0_Sn hx0_np])
      \<comment> \<open>\<alpha> is a path in U.\<close>
      have h\<alpha>_U: "top1_is_path_on ?U (subspace_topology ?Sn ?TSn ?U) x0 ?q ?\<alpha>"
      proof -
        have hU_sub: "?U \<subseteq> ?Sn" by (by100 blast)
        have h_cont: "top1_continuous_map_on I_set I_top ?Sn ?TSn ?\<alpha>"
          using h\<alpha>_path_Sn unfolding top1_is_path_on_def by (by100 blast)
        have h_img: "?\<alpha> ` I_set \<subseteq> ?U"
        proof (intro subsetI)
          fix w assume "w \<in> ?\<alpha> ` I_set"
          then obtain t where "w = ?\<alpha> t" by (by100 blast)
          have "?\<alpha> t \<in> ?Sn"
            by (rule Sn_interpolation_in_Sn[OF hx0_Sn hq_Sn hx0_na])
          moreover have "?\<alpha> t \<noteq> ?p" using h\<alpha>_avoids by (by100 blast)
          ultimately show "w \<in> ?U" using \<open>w = ?\<alpha> t\<close> by (by100 simp)
        qed
        show ?thesis unfolding top1_is_path_on_def
          using top1_continuous_map_on_codomain_shrink[OF h_cont h_img hU_sub]
          h\<alpha>_path_Sn[unfolded top1_is_path_on_def] by (by100 blast)
      qed
      \<comment> \<open>The contraction G(s,t) = normalize((1-t)f(s)+tq). This is the free homotopy from f to const_q
         with both side boundaries = \<alpha>. Continuous in the subspace product topology.\<close>
      \<comment> \<open>3-strip gives f \<simeq>_{path} \<alpha> * const_q * rev(\<alpha>) in U.\<close>
      have hstrip: "top1_path_homotopic_on ?U (subspace_topology ?Sn ?TSn ?U) x0 x0 f
          (top1_path_product ?\<alpha> (top1_path_product (top1_constant_path ?q) (top1_path_reverse ?\<alpha>)))"
      proof -
        let ?TU = "subspace_topology ?Sn ?TSn ?U"
        have hTSn_h: "is_topology_on ?Sn ?TSn"
        proof -
          have "\<forall>i\<in>(UNIV::nat set). is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
            using top1_open_sets_is_topology_on_UNIV by (by100 simp)
          hence "is_topology_on (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
              (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
            by (rule top1_product_topology_on_is_topology_on)
          moreover have "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
            unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
          ultimately have "is_topology_on (UNIV::(nat\<Rightarrow>real) set)
              (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))" by (by100 simp)
          thus ?thesis by (rule subspace_topology_is_topology_on) (by100 simp)
        qed
        have hTU_here: "is_topology_on ?U ?TU"
          by (rule subspace_topology_is_topology_on[OF hTSn_h]) (by100 blast)
        have hf_path: "top1_is_path_on ?U ?TU x0 x0 f"
          using hf unfolding top1_is_loop_on_def by (by100 blast)
        \<comment> \<open>f \<simeq> const*f*const.\<close>
        have hri: "top1_path_homotopic_on ?U ?TU x0 x0 f (top1_path_product f (top1_constant_path x0))"
          by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_right_identity[OF hTU_here hf_path]])
        have hf_const: "top1_is_path_on ?U ?TU x0 x0 (top1_path_product f (top1_constant_path x0))"
          using hri unfolding top1_path_homotopic_on_def by (by100 blast)
        have hli: "top1_path_homotopic_on ?U ?TU x0 x0
            (top1_path_product f (top1_constant_path x0))
            (top1_path_product (top1_constant_path x0) (top1_path_product f (top1_constant_path x0)))"
          by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_left_identity[OF hTU_here hf_const]])
        have hf_eq: "top1_path_homotopic_on ?U ?TU x0 x0 f
            (top1_path_product (top1_constant_path x0) (top1_path_product f (top1_constant_path x0)))"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTU_here hri hli])
        \<comment> \<open>const*f*const \<simeq> \<alpha>*const_q*rev(\<alpha>) via the 3-strip.\<close>
        \<comment> \<open>Contraction: Hc(s,t) = normalize((1-t)*f(s)+t*q). Boundaries:
           Hc(s,0)=f(s), Hc(s,1)=q, Hc(0,t)=Hc(1,t)=\<alpha>(t) (since f(0)=f(1)=x0).
           3-strip G uses Hc in the middle strip, \<alpha> on both sides.\<close>
        have hG_strip: "top1_path_homotopic_on ?U ?TU x0 x0
            (top1_path_product (top1_constant_path x0) (top1_path_product f (top1_constant_path x0)))
            (top1_path_product ?\<alpha> (top1_path_product (top1_constant_path ?q) (top1_path_reverse ?\<alpha>)))"
        proof -
          \<comment> \<open>Define G: I\<times>I \<rightarrow> U.
             Strip 1 (s \<le> 1/2): G(s,t) = \<alpha>(t\<cdot>2s)
             Strip 2 (1/2 \<le> s \<le> 3/4): G(s,t) = normalize((1-t)f(4s-2)+tq)
             Strip 3 (s > 3/4): G(s,t) = \<alpha>(t\<cdot>(4-4s))\<close>
          define G :: "real \<times> real \<Rightarrow> nat \<Rightarrow> real" where
            "G = (\<lambda>(s, t).
               if s \<le> 1/2 then ?\<alpha> (t * (2*s))
               else if s \<le> 3/4 then (\<lambda>i. ((1-t) * (f (4*s-2)) i + t * ?q i) /
                   sqrt (\<Sum>j\<le>n. ((1-t) * (f (4*s-2)) j + t * ?q j)^2))
               else ?\<alpha> (t * (4 - 4*s)))"
          have hG1: "\<And>s t. s \<le> 1/2 \<Longrightarrow> G (s, t) = ?\<alpha> (t * (2*s))"
            unfolding G_def by (by100 simp)
          have hG2: "\<And>s t. \<not>(s \<le> 1/2) \<Longrightarrow> s \<le> 3/4 \<Longrightarrow> G (s, t) = (\<lambda>i. ((1-t) * (f (4*s-2)) i + t * ?q i) /
              sqrt (\<Sum>j\<le>n. ((1-t) * (f (4*s-2)) j + t * ?q j)^2))"
            unfolding G_def by (by100 simp)
          have hG3: "\<And>s t. \<not>(s \<le> 3/4) \<Longrightarrow> G (s, t) = ?\<alpha> (t * (4 - 4*s))"
            unfolding G_def by (by100 simp)
          \<comment> \<open>G is continuous on I\<times>I and maps into U. (The main technical burden.)\<close>
          have hG_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology ?U ?TU G"
          proof -
            have hG_range: "\<forall>st\<in>I_set \<times> I_set. G st \<in> ?U"
            proof (intro ballI)
              fix st assume hst: "st \<in> I_set \<times> I_set"
              obtain s t where hst_eq: "st = (s,t)" and hs: "s \<in> I_set" and ht: "t \<in> I_set"
                using hst by (by100 blast)
              show "G st \<in> ?U"
              proof (cases "s \<le> 1/2")
                case True
                have hGeq: "G st = ?\<alpha> (t * (2*s))" using hG1[OF True] hst_eq by (by100 simp)
                have "?\<alpha> (t * (2*s)) \<in> ?Sn"
                  by (rule Sn_interpolation_in_Sn[OF hx0_Sn hq_Sn hx0_na])
                hence "G st \<in> ?Sn" using hGeq by (by100 simp)
                moreover have "G st \<noteq> ?p" using hGeq h\<alpha>_avoids by (by100 simp)
                ultimately show ?thesis by (by100 blast)
              next
                case hgt: False show ?thesis
                proof (cases "s \<le> 3/4")
                  case True
                  have h4sI: "4*s-2 \<in> I_set"
                    using hgt True unfolding top1_unit_interval_def by (by100 simp)
                  have hfs_U: "f (4*s-2) \<in> ?U"
                  proof -
                    have hfc: "top1_continuous_map_on I_set I_top ?U ?TU f"
                      using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                    thus ?thesis using h4sI unfolding top1_continuous_map_on_def by (by100 blast)
                  qed
                  hence hfs_Sn: "f (4*s-2) \<in> ?Sn" and hfs_np: "f (4*s-2) \<noteq> ?p"
                    by (by100 blast)+
                  have hfs_na: "f (4*s-2) \<noteq> (\<lambda>i. - ?q i)"
                  proof assume h: "f (4*s-2) = (\<lambda>i. - ?q i)"
                    have "(\<lambda>i::nat. - ?q i) = ?p" by (rule ext) (by100 simp)
                    thus False using h hfs_np by (by100 simp)
                  qed
                  have hng: "\<not>(s \<le> 1/2)" using hgt by (by100 blast)
                  have hGeq: "G st = (\<lambda>i. ((1-t) * (f (4*s-2)) i + t * ?q i) /
                      sqrt (\<Sum>j\<le>n. ((1-t) * (f (4*s-2)) j + t * ?q j)^2))"
                    using hG2[OF hng True] hst_eq by (by100 simp)
                  have "G st \<in> ?Sn" using hGeq
                    Sn_interpolation_in_Sn[OF hfs_Sn hq_Sn hfs_na] by (by100 simp)
                  moreover have "G st \<noteq> ?p" using hGeq
                    Sn_interpolation_to_q_avoids_p[OF hfs_Sn hfs_np] by (by100 simp)
                  ultimately show ?thesis by (by100 blast)
                next
                  case False
                  have hng: "\<not>(s \<le> 3/4)" using False by (by100 blast)
                  have hGeq: "G st = ?\<alpha> (t * (4 - 4*s))" using hG3[OF hng] hst_eq by (by100 simp)
                  have "G st \<in> ?Sn" using hGeq
                    Sn_interpolation_in_Sn[OF hx0_Sn hq_Sn hx0_na] by (by100 simp)
                  moreover have "G st \<noteq> ?p" using hGeq h\<alpha>_avoids by (by100 simp)
                  ultimately show ?thesis by (by100 blast)
                qed
              qed
            qed
            have hG_cont_Sn: "top1_continuous_map_on (I_set \<times> I_set) II_topology ?Sn ?TSn G"
            proof -
              have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
                unfolding II_topology_def by (rule product_topology_on_is_topology_on)
                  (rule top1_unit_interval_topology_is_topology_on)+
              \<comment> \<open>G maps into S^n.\<close>
              have hG_Sn: "\<forall>st\<in>I_set \<times> I_set. G st \<in> ?Sn"
                using hG_range by (by100 blast)
              \<comment> \<open>Split I\<times>I into LEFT = {s \<le> 1/2} and RIGHT = {s \<ge> 1/2}.\<close>
              let ?L = "{(s::real,t::real). 0 \<le> s \<and> s \<le> 1/2 \<and> 0 \<le> t \<and> t \<le> 1}"
              let ?R = "{(s::real,t::real). 1/2 \<le> s \<and> s \<le> 1 \<and> 0 \<le> t \<and> t \<le> 1}"
              \<comment> \<open>Both closed in II_topology and cover I\<times>I.\<close>
              have hL_closed: "closedin_on (I_set \<times> I_set) II_topology ?L"
                unfolding closedin_on_def
              proof (intro conjI)
                show "?L \<subseteq> I_set \<times> I_set" unfolding top1_unit_interval_def by auto
                \<comment> \<open>Complement = {(s,t) \<in> I\<times>I | s > 1/2} is open in II_topology.\<close>
                have "(I_set \<times> I_set) - ?L = {(s,t). 1/2 < s \<and> s \<le> 1 \<and> 0 \<le> t \<and> t \<le> 1}"
                  unfolding top1_unit_interval_def by auto
                also have "... = {s \<in> I_set. s > 1/2} \<times> I_set"
                  unfolding top1_unit_interval_def by auto
                finally have hcomp_eq: "(I_set \<times> I_set) - ?L = {s \<in> I_set. s > 1/2} \<times> I_set" .
                have "{s \<in> I_set. s > 1/2} \<in> I_top"
                proof -
                  have "open {s::real. s > 1/2}" using open_greaterThan[of "1/2::real"]
                    by (simp add: greaterThan_def)
                  hence "{s::real. s > 1/2} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
                  hence "I_set \<inter> {s::real. s > 1/2} \<in> I_top"
                    unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
                  moreover have "I_set \<inter> {s::real. s > 1/2} = {s \<in> I_set. s > 1/2}" by (by100 blast)
                  ultimately show ?thesis by simp
                qed
                moreover have "I_set \<in> I_top"
                  using top1_unit_interval_topology_is_topology_on unfolding is_topology_on_def by (by100 blast)
                ultimately have "{s \<in> I_set. s > 1/2} \<times> I_set \<in> II_topology"
                  unfolding II_topology_def by (rule product_rect_open)
                thus "(I_set \<times> I_set) - ?L \<in> II_topology" using hcomp_eq by simp
              qed
              have hR_closed: "closedin_on (I_set \<times> I_set) II_topology ?R"
                unfolding closedin_on_def
              proof (intro conjI)
                show "?R \<subseteq> I_set \<times> I_set" unfolding top1_unit_interval_def by auto
                have "(I_set \<times> I_set) - ?R = {(s,t). 0 \<le> s \<and> s < 1/2 \<and> 0 \<le> t \<and> t \<le> 1}"
                  unfolding top1_unit_interval_def by auto
                also have "... = {s \<in> I_set. s < 1/2} \<times> I_set"
                  unfolding top1_unit_interval_def by auto
                finally have hcomp_eq: "(I_set \<times> I_set) - ?R = {s \<in> I_set. s < 1/2} \<times> I_set" .
                have "{s \<in> I_set. s < 1/2} \<in> I_top"
                proof -
                  have "open {s::real. s < 1/2}" using open_lessThan[of "1/2::real"]
                    by (simp add: greaterThan_def lessThan_def)
                  hence "{s::real. s < 1/2} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
                  hence "I_set \<inter> {s::real. s < 1/2} \<in> I_top"
                    unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
                  moreover have "I_set \<inter> {s::real. s < 1/2} = {s \<in> I_set. s < 1/2}" by (by100 blast)
                  ultimately show ?thesis by simp
                qed
                moreover have "I_set \<in> I_top"
                  using top1_unit_interval_topology_is_topology_on unfolding is_topology_on_def by (by100 blast)
                ultimately have "{s \<in> I_set. s < 1/2} \<times> I_set \<in> II_topology"
                  unfolding II_topology_def by (rule product_rect_open)
                thus "(I_set \<times> I_set) - ?R \<in> II_topology" using hcomp_eq by simp
              qed
              have hLR_cover: "?L \<union> ?R = I_set \<times> I_set"
                unfolding top1_unit_interval_def by auto
              \<comment> \<open>G on LEFT = \<alpha>(t\<cdot>2s), continuous via composition.\<close>
              have hG_L: "top1_continuous_map_on ?L (subspace_topology (I_set \<times> I_set) II_topology ?L) ?Sn ?TSn G"
              proof -
                have h\<alpha>_cont_Sn: "top1_continuous_map_on I_set I_top ?Sn ?TSn ?\<alpha>"
                  using h\<alpha>_path_Sn unfolding top1_is_path_on_def by (by100 blast)
                have h\<mu>_cont: "top1_continuous_map_on ?L (subspace_topology (I_set \<times> I_set) II_topology ?L)
                    I_set I_top (\<lambda>(s,t). t * (2*s))"
                proof -
                  have h_std: "continuous_on UNIV (\<lambda>(s::real,t::real). t * (2*s))"
                    by (auto intro!: continuous_intros simp: case_prod_beta)
                  have h_range: "\<forall>st\<in>?L. (\<lambda>(s,t). t * (2*s)) st \<in> I_set"
                  proof
                    fix st assume "st \<in> ?L"
                    then obtain s t where hst: "st = (s,t)" "0 \<le> s" "s \<le> 1/2" "0 \<le> t" "t \<le> 1" by auto
                    thus "(\<lambda>(s,t). t * (2*s)) st \<in> I_set" unfolding hst top1_unit_interval_def
                      by (simp add: mult_le_one)
                  qed
                  have hL_sub: "?L \<subseteq> I_set \<times> I_set" unfolding top1_unit_interval_def by auto
                  have h_cont_L: "continuous_on ?L (\<lambda>(s::real,t::real). t * (2*s))"
                    using continuous_on_subset[OF h_std] by (by100 blast)
                  show ?thesis
                    unfolding top1_continuous_map_on_def
                  proof (intro conjI ballI)
                    fix st assume hst: "st \<in> ?L"
                    show "(\<lambda>(s,t). t * (2*s)) st \<in> I_set" using h_range hst by (by100 blast)
                  next
                    fix V assume hV: "V \<in> I_top"
                    obtain W where hW: "W \<in> top1_open_sets" and hVeq: "V = I_set \<inter> W"
                      using hV unfolding top1_unit_interval_topology_def subspace_topology_def
                      by (by100 blast)
                    have hWo: "open W" using hW unfolding top1_open_sets_def by (by100 blast)
                    have hco: "continuous_on ?L (\<lambda>(s::real,t::real). t*(2*s))" by (rule h_cont_L)
                    have hpre: "\<exists>A. open A \<and> A \<inter> ?L = (\<lambda>(s,t). t*(2*s)) -` W \<inter> ?L"
                      using iffD1[OF continuous_on_open_invariant] hco hWo by (by100 blast)
                    then obtain A where hAo: "open A" and hAeq: "A \<inter> ?L = (\<lambda>(s,t). t*(2*s)) -` W \<inter> ?L"
                      by (by100 auto)
                    have "{st \<in> ?L. (\<lambda>(s,t). t*(2*s)) st \<in> V} = ?L \<inter> A"
                    proof -
                      have "{st \<in> ?L. (\<lambda>(s,t). t*(2*s)) st \<in> V} =
                            {st \<in> ?L. (\<lambda>(s,t). t*(2*s)) st \<in> W}"
                        using h_range unfolding hVeq by (by100 blast)
                      also have "\<dots> = ?L \<inter> A" using hAeq by (by100 blast)
                      finally show ?thesis .
                    qed
                    have "open A" by (rule hAo)
                    hence "A \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
                    hence "A \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
                    proof -
                      assume "A \<in> top1_open_sets"
                      have "product_topology_on (top1_open_sets::real set set) top1_open_sets
                          = (top1_open_sets :: (real\<times>real) set set)"
                        by (rule product_topology_on_open_sets_real2)
                      thus ?thesis using \<open>A \<in> top1_open_sets\<close> by (by100 simp)
                    qed
                    hence "A \<in> (top1_open_sets :: (real\<times>real) set set)"
                      using product_topology_on_open_sets_real2 by (by100 simp)
                    hence "A \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
                      using product_topology_on_open_sets_real2 by (by100 metis)
                    moreover have "II_topology = subspace_topology UNIV
                        (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
                      unfolding II_topology_def by (rule II_topology_eq_subspace)
                    ultimately have "(I_set \<times> I_set) \<inter> A \<in> II_topology"
                      unfolding subspace_topology_def by (by100 blast)
                    hence "?L \<inter> ((I_set \<times> I_set) \<inter> A) \<in> subspace_topology (I_set \<times> I_set) II_topology ?L"
                      unfolding subspace_topology_def by (by100 blast)
                    moreover have "?L \<inter> ((I_set \<times> I_set) \<inter> A) = ?L \<inter> A"
                      using hL_sub by (by100 blast)
                    ultimately have "?L \<inter> A \<in> subspace_topology (I_set \<times> I_set) II_topology ?L"
                      by (by100 simp)
                    thus "{st \<in> ?L. (\<lambda>(s,t). t*(2*s)) st \<in> V}
                        \<in> subspace_topology (I_set \<times> I_set) II_topology ?L"
                      using \<open>{st \<in> ?L. (\<lambda>(s,t). t*(2*s)) st \<in> V} = ?L \<inter> A\<close> by simp
                  qed
                qed
                have hG_eq_L: "\<forall>st\<in>?L. G st = (?\<alpha> \<circ> (\<lambda>(s,t). t*(2*s))) st"
                  using hG1 by (by100 auto)
                have hcomp: "top1_continuous_map_on ?L (subspace_topology (I_set \<times> I_set) II_topology ?L)
                    ?Sn ?TSn (?\<alpha> \<circ> (\<lambda>(s,t). t*(2*s)))"
                  by (rule top1_continuous_map_on_comp[OF h\<mu>_cont h\<alpha>_cont_Sn])
                show ?thesis unfolding top1_continuous_map_on_def
                proof (intro conjI ballI)
                  fix st assume hst: "st \<in> ?L"
                  have "G st = (?\<alpha> \<circ> (\<lambda>(s,t). t*(2*s))) st" using hG_eq_L hst by (by100 blast)
                  moreover have "(?\<alpha> \<circ> (\<lambda>(s,t). t*(2*s))) st \<in> ?Sn"
                    using hcomp hst unfolding top1_continuous_map_on_def by (by100 blast)
                  ultimately show "G st \<in> ?Sn" by (by100 simp)
                next
                  fix V assume hV: "V \<in> ?TSn"
                  have "{st \<in> ?L. (?\<alpha> \<circ> (\<lambda>(s,t). t*(2*s))) st \<in> V}
                      \<in> subspace_topology (I_set \<times> I_set) II_topology ?L"
                    using hcomp hV unfolding top1_continuous_map_on_def by (by100 blast)
                  moreover have "{st \<in> ?L. G st \<in> V} = {st \<in> ?L. (?\<alpha> \<circ> (\<lambda>(s,t). t*(2*s))) st \<in> V}"
                  proof (intro set_eqI iffI)
                    fix st assume "st \<in> {st \<in> ?L. G st \<in> V}"
                    hence "st \<in> ?L" "G st \<in> V" by (by100 blast)+
                    have "G st = (?\<alpha> \<circ> (\<lambda>(s,t). t*(2*s))) st" using hG_eq_L \<open>st \<in> ?L\<close> by (by100 blast)
                    thus "st \<in> {st \<in> ?L. (?\<alpha> \<circ> (\<lambda>(s,t). t*(2*s))) st \<in> V}"
                      using \<open>G st \<in> V\<close> \<open>st \<in> ?L\<close> by (by100 simp)
                  next
                    fix st assume "st \<in> {st \<in> ?L. (?\<alpha> \<circ> (\<lambda>(s,t). t*(2*s))) st \<in> V}"
                    hence "st \<in> ?L" "(?\<alpha> \<circ> (\<lambda>(s,t). t*(2*s))) st \<in> V" by (by100 blast)+
                    have "G st = (?\<alpha> \<circ> (\<lambda>(s,t). t*(2*s))) st" using hG_eq_L \<open>st \<in> ?L\<close> by (by100 blast)
                    thus "st \<in> {st \<in> ?L. G st \<in> V}"
                      using \<open>(?\<alpha> \<circ> (\<lambda>(s,t). t*(2*s))) st \<in> V\<close> \<open>st \<in> ?L\<close> by (by100 simp)
                  qed
                  ultimately show "{st \<in> ?L. G st \<in> V}
                      \<in> subspace_topology (I_set \<times> I_set) II_topology ?L" by simp
                qed
              qed
              \<comment> \<open>G on RIGHT: paste middle {1/2 \<le> s \<le> 3/4} and far-right {s \<ge> 3/4}.\<close>
              have hG_R: "top1_continuous_map_on ?R (subspace_topology (I_set \<times> I_set) II_topology ?R) ?Sn ?TSn G"
              proof -
                \<comment> \<open>Split R into M = {1/2 \<le> s \<le> 3/4} and FR = {3/4 \<le> s \<le> 1}.
                   On M: G = normalized interpolation. On FR: G = \<alpha>\<circ>(t*(4-4s)).\<close>
                let ?M = "{(s::real,t::real). 1/2 \<le> s \<and> s \<le> 3/4 \<and> 0 \<le> t \<and> t \<le> 1}"
                let ?FR = "{(s::real,t::real). 3/4 \<le> s \<and> s \<le> 1 \<and> 0 \<le> t \<and> t \<le> 1}"
                have hR_sub: "?R \<subseteq> I_set \<times> I_set" unfolding top1_unit_interval_def by auto
                have hTR: "is_topology_on ?R (subspace_topology (I_set \<times> I_set) II_topology ?R)"
                  by (rule subspace_topology_is_topology_on[OF hTII hR_sub])
                have hMFR_cover: "?M \<union> ?FR = ?R" by auto
                \<comment> \<open>M closed in R.\<close>
                have hM_closed: "closedin_on ?R (subspace_topology (I_set \<times> I_set) II_topology ?R) ?M"
                  unfolding closedin_on_def
                proof (intro conjI)
                  show "?M \<subseteq> ?R" by auto
                  have "?R - ?M = {(s::real,t::real). 3/4 < s \<and> s \<le> 1 \<and> 0 \<le> t \<and> t \<le> 1}" by auto
                  also have "... = ({s \<in> I_set. s > 3/4} \<times> I_set) \<inter> ?R"
                    unfolding top1_unit_interval_def by auto
                  finally have hcomp_eq: "?R - ?M = ({s \<in> I_set. s > 3/4} \<times> I_set) \<inter> ?R" .
                  have "{s \<in> I_set. s > 3/4} \<times> I_set \<in> II_topology"
                  proof -
                    have "open {s::real. s > 3/4}" using open_greaterThan[of "3/4::real"]
                      by (simp add: greaterThan_def)
                    hence "{s::real. s > 3/4} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
                    hence "I_set \<inter> {s::real. s > 3/4} \<in> I_top"
                      unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
                    moreover have "I_set \<inter> {s::real. s > 3/4} = {s \<in> I_set. s > 3/4}" by (by100 blast)
                    ultimately have "{s \<in> I_set. s > 3/4} \<in> I_top" by simp
                    moreover have "I_set \<in> I_top"
                      using top1_unit_interval_topology_is_topology_on unfolding is_topology_on_def by (by100 blast)
                    ultimately show ?thesis unfolding II_topology_def by (rule product_rect_open)
                  qed
                  hence "({s \<in> I_set. s > 3/4} \<times> I_set) \<inter> ?R \<in> subspace_topology (I_set \<times> I_set) II_topology ?R"
                    unfolding subspace_topology_def by (by100 blast)
                  thus "?R - ?M \<in> subspace_topology (I_set \<times> I_set) II_topology ?R"
                    using hcomp_eq by simp
                qed
                \<comment> \<open>FR closed in R.\<close>
                have hFR_closed: "closedin_on ?R (subspace_topology (I_set \<times> I_set) II_topology ?R) ?FR"
                  unfolding closedin_on_def
                proof (intro conjI)
                  show "?FR \<subseteq> ?R" by auto
                  have "?R - ?FR = {(s::real,t::real). 1/2 \<le> s \<and> s < 3/4 \<and> 0 \<le> t \<and> t \<le> 1}" by auto
                  also have "... = ({s \<in> I_set. s < 3/4} \<times> I_set) \<inter> ?R"
                    unfolding top1_unit_interval_def by auto
                  finally have hcomp_eq: "?R - ?FR = ({s \<in> I_set. s < 3/4} \<times> I_set) \<inter> ?R" .
                  have "{s \<in> I_set. s < 3/4} \<times> I_set \<in> II_topology"
                  proof -
                    have "open {s::real. s < 3/4}" using open_lessThan[of "3/4::real"]
                      by (simp add: greaterThan_def lessThan_def)
                    hence "{s::real. s < 3/4} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
                    hence "I_set \<inter> {s::real. s < 3/4} \<in> I_top"
                      unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
                    moreover have "I_set \<inter> {s::real. s < 3/4} = {s \<in> I_set. s < 3/4}" by (by100 blast)
                    ultimately have "{s \<in> I_set. s < 3/4} \<in> I_top" by simp
                    moreover have "I_set \<in> I_top"
                      using top1_unit_interval_topology_is_topology_on unfolding is_topology_on_def by (by100 blast)
                    ultimately show ?thesis unfolding II_topology_def by (rule product_rect_open)
                  qed
                  hence "({s \<in> I_set. s < 3/4} \<times> I_set) \<inter> ?R \<in> subspace_topology (I_set \<times> I_set) II_topology ?R"
                    unfolding subspace_topology_def by (by100 blast)
                  thus "?R - ?FR \<in> subspace_topology (I_set \<times> I_set) II_topology ?R"
                    using hcomp_eq by simp
                qed
                have hG_Sn_R: "\<forall>st\<in>?R. G st \<in> ?Sn"
                proof (intro ballI)
                  fix st assume "st \<in> ?R"
                  hence "st \<in> I_set \<times> I_set" using hR_sub by (by100 blast)
                  thus "G st \<in> ?Sn" using hG_Sn by (by100 blast)
                qed
                \<comment> \<open>G on M: normalized interpolation (s,t) \<mapsto> ((1-t)*f(4s-2)+t*q)/||...||.
                   This requires showing the normalized interpolation is jointly continuous.\<close>
                have hG_M: "top1_continuous_map_on ?M
                    (subspace_topology ?R (subspace_topology (I_set \<times> I_set) II_topology ?R) ?M) ?Sn ?TSn G"
                proof -
                  have hM_sub_R: "?M \<subseteq> ?R" by (by100 auto)
                  have hM_trans: "subspace_topology ?R (subspace_topology (I_set \<times> I_set) II_topology ?R) ?M
                      = subspace_topology (I_set \<times> I_set) II_topology ?M"
                    by (rule subspace_topology_trans[OF hM_sub_R])
                  \<comment> \<open>f range in S^n.\<close>
                  have hf_cont: "top1_continuous_map_on I_set I_top ?U ?TU f"
                    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                  have hf_in_Sn: "\<forall>u\<in>I_set. f u \<in> ?Sn"
                  proof (intro ballI)
                    fix u assume "u \<in> I_set"
                    have "f u \<in> ?U" using hf_cont \<open>u \<in> I_set\<close> unfolding top1_continuous_map_on_def by (by100 blast)
                    thus "f u \<in> ?Sn" by (by100 blast)
                  qed
                  have hM_sub: "?M \<subseteq> I_set \<times> I_set" unfolding top1_unit_interval_def by (by100 auto)
                  \<comment> \<open>Each f(u) is non-antipodal to q since f(u) \<in> U = S^n - {p} and p = -q.\<close>
                  have hf_na: "\<And>u. u \<in> I_set \<Longrightarrow> f u \<noteq> (\<lambda>i. - ?q i)"
                  proof
                    fix u assume hu: "u \<in> I_set" and h: "f u = (\<lambda>i. - ?q i)"
                    have "(\<lambda>i::nat. - ?q i) = ?p" by (rule ext) (by100 simp)
                    have "f u \<in> ?U" using hf_cont hu unfolding top1_continuous_map_on_def by (by100 blast)
                    hence "f u \<noteq> ?p" by (by100 blast)
                    thus False using h \<open>(\<lambda>i::nat. - ?q i) = ?p\<close> by (by100 simp)
                  qed
                  \<comment> \<open>4s-2 maps M into I.\<close>
                  have h4s2_range: "\<forall>st\<in>?M. 4*fst st-2 \<in> I_set"
                  proof (intro ballI)
                    fix st assume "st \<in> ?M"
                    then obtain s t where hst: "st = (s,t)" "1/2 \<le> s" "s \<le> 3/4" "0 \<le> t" "t \<le> 1" by (by100 auto)
                    show "4*fst st-2 \<in> I_set" unfolding hst top1_unit_interval_def
                      using hst by (by100 simp)
                  qed
                  \<comment> \<open>Norm N(s,t) > 0 on M: because f(4s-2) \<noteq> -q.\<close>
                  have hN_pos: "\<forall>st\<in>?M. sqrt (\<Sum>j\<le>n. ((1-snd st) * (f (4*fst st-2)) j + snd st * ?q j)^2) > 0"
                  proof (intro ballI)
                    fix st assume hst: "st \<in> ?M"
                    have hu: "4*fst st-2 \<in> I_set" using h4s2_range hst by (by100 blast)
                    have hfu_Sn: "f (4*fst st-2) \<in> ?Sn" using hf_in_Sn hu by (by100 blast)
                    have hfu_na: "f (4*fst st-2) \<noteq> (\<lambda>i. - ?q i)" using hf_na hu by (by100 blast)
                    show "sqrt (\<Sum>j\<le>n. ((1-snd st) * (f (4*fst st-2)) j + snd st * ?q j)^2) > 0"
                      by (rule Sn_interpolation_norm_pos[OF hfu_Sn hq_Sn hfu_na])
                  qed
                  \<comment> \<open>f(\<cdot>)(i) continuous as a real function on I, for each i.\<close>
                  have hfi_cont: "\<And>i. continuous_on I_set (\<lambda>u. f u i)"
                  proof -
                    fix i :: nat
                    \<comment> \<open>Step 1: f continuous I \<rightarrow> S^n in product topology.\<close>
                    have hTprod: "is_topology_on (UNIV :: (nat \<Rightarrow> real) set)
                        (top1_product_topology_on UNIV (\<lambda>_::nat. UNIV::real set) (\<lambda>_. top1_open_sets))"
                    proof -
                      have "\<forall>j\<in>(UNIV::nat set). is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
                        using top1_open_sets_is_topology_on_UNIV by (by100 blast)
                      hence "is_topology_on (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
                          (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
                        by (rule top1_product_topology_on_is_topology_on)
                      moreover have "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
                        unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
                      ultimately show ?thesis by (by100 simp)
                    qed
                    have hSn_sub_UNIV: "?Sn \<subseteq> (UNIV :: (nat \<Rightarrow> real) set)" by (by100 simp)
                    have hTSn_here: "is_topology_on ?Sn ?TSn"
                      by (rule subspace_topology_is_topology_on[OF hTprod hSn_sub_UNIV])
                    have hU_sub: "?U \<subseteq> ?Sn" by (by100 blast)
                    have hTU_here: "?TU = subspace_topology ?Sn ?TSn ?U"
                      by (by100 simp)
                    \<comment> \<open>Step 2: Compose with projection \<pi>_i: S^n \<rightarrow> R.
                       The projection is continuous from the product topology.\<close>
                    have hproj: "top1_continuous_map_on ?Sn ?TSn (UNIV::real set) top1_open_sets (\<lambda>x. x i)"
                    proof -
                      have hTop: "\<forall>j\<in>(UNIV::nat set). is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
                        using top1_open_sets_is_topology_on_UNIV by (by100 simp)
                      have hproj_PiE: "top1_continuous_map_on
                          (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
                          (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))
                          (UNIV::real set) top1_open_sets (\<lambda>x. x i)"
                        by (rule top1_continuous_map_on_product_projection[OF hTop]) (by100 simp)
                      have hPiE_eq: "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
                        unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
                      have hSn_sub: "?Sn \<subseteq> UNIV" by (by100 simp)
                      have "top1_continuous_map_on ?Sn
                          (subspace_topology UNIV (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets)) ?Sn)
                          (UNIV::real set) top1_open_sets (\<lambda>x. x i)"
                        using top1_continuous_map_on_restrict_domain_simple[OF hproj_PiE[unfolded hPiE_eq] hSn_sub_UNIV]
                        by (by100 simp)
                      thus ?thesis by (by100 simp)
                    qed
                    \<comment> \<open>Step 3: Compose f: I \<rightarrow> U \<subseteq> S^n with \<pi>_i: S^n \<rightarrow> R.\<close>
                    have hf_Sn_cont: "top1_continuous_map_on I_set I_top ?Sn ?TSn f"
                    proof -
                      have hTU_eq: "?TU = subspace_topology UNIV
                          (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets)) ?U"
                        by (rule subspace_topology_trans[OF hU_sub])
                      have hf_cont': "top1_continuous_map_on I_set I_top ?U
                          (subspace_topology UNIV (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets)) ?U) f"
                        using hf_cont unfolding hTU_eq .
                      show ?thesis
                        by (rule top1_continuous_map_on_codomain_enlarge[OF hf_cont' hU_sub hSn_sub_UNIV])
                    qed
                    have hcomp': "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets ((\<lambda>x. x i) \<circ> f)"
                      by (rule top1_continuous_map_on_comp[OF hf_Sn_cont hproj])
                    have hcomp: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (\<lambda>u. f u i)"
                      using hcomp' unfolding comp_def by (by100 simp)
                    \<comment> \<open>Step 4: Bridge top1_continuous_map_on I I_top UNIV top1_open_sets to continuous_on.\<close>
                    show "continuous_on I_set (\<lambda>u. f u i)"
                    proof (rule continuous_on_open_invariant[THEN iffD2, rule_format])
                      fix W :: "real set" assume hW: "open W"
                      have hW_os: "W \<in> top1_open_sets" using hW unfolding top1_open_sets_def by (by100 blast)
                      have hpre: "{u \<in> I_set. f u i \<in> W} \<in> I_top"
                        using hcomp hW_os unfolding top1_continuous_map_on_def by (by100 blast)
                      then obtain V where hV: "V \<in> top1_open_sets" and hpre_eq: "{u \<in> I_set. f u i \<in> W} = I_set \<inter> V"
                        unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
                      have "open V" using hV unfolding top1_open_sets_def by (by100 blast)
                      moreover have "V \<inter> I_set = (\<lambda>u. f u i) -` W \<inter> I_set"
                        using hpre_eq by (by100 blast)
                      ultimately show "\<exists>T. open T \<and> T \<inter> I_set = (\<lambda>u. f u i) -` W \<inter> I_set"
                        by (by100 blast)
                    qed
                  qed
                  \<comment> \<open>f(4s-2)(i) continuous on M:\<close>
                  have hfi_4s2_cont: "\<And>i. continuous_on ?M (\<lambda>st. f (4*fst st - 2) i)"
                  proof -
                    fix i
                    have "continuous_on ?M (\<lambda>st. fst st)" by (auto intro!: continuous_intros)
                    hence h1: "continuous_on ?M (\<lambda>st. 4*fst st - 2)"
                      by (auto intro!: continuous_intros)
                    show "continuous_on ?M (\<lambda>st. f (4*fst st - 2) i)"
                    proof (rule continuous_on_compose2[of I_set "\<lambda>u. f u i" ?M "\<lambda>st. 4*fst st-2"])
                      show "continuous_on I_set (\<lambda>u. f u i)" by (rule hfi_cont)
                      show "continuous_on ?M (\<lambda>st. 4 * fst st - 2)" by (rule h1)
                      show "(\<lambda>st. 4 * fst st - (2::real)) ` ?M \<subseteq> I_set"
                        using h4s2_range by (by100 auto)
                    qed
                  qed
                  \<comment> \<open>Each coordinate of G is continuous_on M.\<close>
                  have hcoord_cont: "\<And>i. continuous_on ?M (\<lambda>st. G st i)"
                  proof -
                    fix i
                    have hsnd_cont: "continuous_on ?M snd"
                      using continuous_on_snd[OF continuous_on_id] by (by100 simp)
                    have hnum: "continuous_on ?M (\<lambda>st. (1-snd st) * f (4*fst st-2) i + snd st * ?q i)"
                      by (intro continuous_intros hfi_4s2_cont hsnd_cont)
                    have hsumsq: "continuous_on ?M (\<lambda>st. \<Sum>j\<le>n. ((1-snd st) * f (4*fst st-2) j + snd st * ?q j)^2)"
                      by (intro continuous_intros hfi_4s2_cont hsnd_cont)
                    have hN_cont: "continuous_on ?M (\<lambda>st. sqrt (\<Sum>j\<le>n. ((1-snd st) * f (4*fst st-2) j + snd st * ?q j)^2))"
                      by (rule continuous_on_real_sqrt[OF hsumsq])
                    have hN_ne: "\<forall>st\<in>?M. sqrt (\<Sum>j\<le>n. ((1-snd st) * f (4*fst st-2) j + snd st * ?q j)^2) \<noteq> 0"
                    proof (intro ballI)
                      fix st assume "st \<in> ?M"
                      have "sqrt (\<Sum>j\<le>n. ((1-snd st) * f (4*fst st-2) j + snd st * ?q j)^2) > 0"
                        using hN_pos \<open>st \<in> ?M\<close> by (by100 blast)
                      thus "sqrt (\<Sum>j\<le>n. ((1-snd st) * f (4*fst st-2) j + snd st * ?q j)^2) \<noteq> 0"
                        by (by100 linarith)
                    qed
                    have "continuous_on ?M (\<lambda>st. ((1-snd st) * f (4*fst st-2) i + snd st * ?q i) /
                        sqrt (\<Sum>j\<le>n. ((1-snd st) * f (4*fst st-2) j + snd st * ?q j)^2))"
                      by (rule continuous_on_divide[OF hnum hN_cont hN_ne])
                    moreover have hGi_eq: "\<forall>st\<in>?M. G st i = ((1-snd st) * f (4*fst st-2) i + snd st * ?q i) /
                        sqrt (\<Sum>j\<le>n. ((1-snd st) * f (4*fst st-2) j + snd st * ?q j)^2)"
                    proof (intro ballI)
                      fix st assume hst: "st \<in> ?M"
                      obtain s t where hst_pair: "st = (s,t)" and hs1: "1/2 \<le> s" and hs2: "s \<le> 3/4"
                          and ht1: "0 \<le> t" and ht2: "t \<le> 1" using hst by auto
                      show "G st i = ((1-snd st) * f (4*fst st-2) i + snd st * ?q i) /
                          sqrt (\<Sum>j\<le>n. ((1-snd st) * f (4*fst st-2) j + snd st * ?q j)^2)"
                      proof (cases "s > 1/2")
                        case True hence hng: "\<not>(s \<le> 1/2)" by (by100 simp)
                        have hlq: "s \<le> 3/4" using hs2 by (by100 simp)
                        have "G st = (\<lambda>k. ((1-t) * (f (4*s-2)) k + t * ?q k) /
                            sqrt (\<Sum>j\<le>n. ((1-t) * (f (4*s-2)) j + t * ?q j)^2))"
                          using hG2[OF hng hlq] hst_pair by (by100 simp)
                        thus ?thesis using hst_pair by (by100 simp)
                      next
                        case False hence hs12: "s = 1/2" using hs1 by (by100 simp)
                        have hf0: "f (0::real) = x0"
                          using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                        have h4s0: "4 * s - 2 = (0::real)" using hs12 by (by100 linarith)
                        have hfx0: "f (4*s-2) = x0"
                        proof -
                          from h4s0 have "f (4*s - 2) = f 0" by (rule arg_cong)
                          thus ?thesis using hf0 by (by100 simp)
                        qed
                        \<comment> \<open>G via hG1 at s=1/2: G st = \<alpha>(t).\<close>
                        have hle: "s \<le> 1/2" using hs12 by (by100 simp)
                        have hGst: "G st i = ?\<alpha> (t * (2 * s)) i" using hG1[OF hle] hst_pair by (by100 simp)
                        have ht2s: "t * (2 * s) = t" using hs12 by (by100 simp)
                        have hG12: "G st i = ?\<alpha> t i" using hGst ht2s by (by100 simp)
                        \<comment> \<open>RHS: with f(4s-2)=x0, the formula gives \<alpha>(t)(i).\<close>
                        have hRHS: "((1-snd st) * f (4*fst st-2) i + snd st * ?q i) /
                            sqrt (\<Sum>j\<le>n. ((1-snd st) * f (4*fst st-2) j + snd st * ?q j)^2)
                            = ?\<alpha> t i"
                        proof -
                          have "fst st = s" "snd st = t" using hst_pair by (by100 simp)+
                          thus ?thesis using hfx0 by (simp only: hfx0 \<open>fst st = s\<close> \<open>snd st = t\<close>)
                        qed
                        show ?thesis using hG12 hRHS by (by100 simp)
                      qed
                    qed
                    ultimately show "continuous_on ?M (\<lambda>st. G st i)"
                    proof -
                      assume hcf: "continuous_on ?M (\<lambda>st. ((1-snd st) * f (4*fst st-2) i + snd st * ?q i) /
                          sqrt (\<Sum>j\<le>n. ((1-snd st) * f (4*fst st-2) j + snd st * ?q j)^2))"
                      assume heq: "\<forall>st\<in>?M. G st i = ((1-snd st) * f (4*fst st-2) i + snd st * ?q i) /
                          sqrt (\<Sum>j\<le>n. ((1-snd st) * f (4*fst st-2) j + snd st * ?q j)^2)"
                      show ?thesis
                      proof (rule continuous_on_cong[THEN iffD2])
                        show "?M = ?M" by (rule refl)
                        fix st assume "st \<in> ?M"
                        show "G st i = ((1-snd st) * f (4*fst st-2) i + snd st * ?q i) /
                            sqrt (\<Sum>j\<le>n. ((1-snd st) * f (4*fst st-2) j + snd st * ?q j)^2)"
                          using heq \<open>st \<in> ?M\<close> by (by100 blast)
                      next
                        show "continuous_on ?M (\<lambda>st. ((1-snd st) * f (4*fst st-2) i + snd st * ?q i) /
                            sqrt (\<Sum>j\<le>n. ((1-snd st) * f (4*fst st-2) j + snd st * ?q j)^2))"
                          by (rule hcf)
                      qed
                    qed
                  qed
                  \<comment> \<open>G maps M into S^n.\<close>
                  have hG_Sn_M: "\<forall>st\<in>?M. G st \<in> ?Sn"
                  proof (intro ballI)
                    fix st assume hst: "st \<in> ?M"
                    hence "st \<in> I_set \<times> I_set" using hM_sub by (by100 blast)
                    thus "G st \<in> ?Sn" using hG_Sn by (by100 blast)
                  qed
                  \<comment> \<open>Bridge coordinate continuity to top1_continuous_map_on via Theorem 19.6.\<close>
                  have hcoord_top: "\<And>i. top1_continuous_map_on ?M (subspace_topology (I_set \<times> I_set) II_topology ?M)
                      (UNIV::real set) top1_open_sets (\<lambda>st. G st i)"
                  proof -
                    fix i
                    have hc: "continuous_on ?M (\<lambda>st. G st i)" by (rule hcoord_cont)
                    have hrange: "\<And>st. st \<in> ?M \<Longrightarrow> G st i \<in> (UNIV::real set)" by (by100 simp)
                    \<comment> \<open>Bridge: continuous_on on M to top1_continuous_map_on with product_topology.\<close>
                    show "top1_continuous_map_on ?M (subspace_topology (I_set \<times> I_set) II_topology ?M)
                        (UNIV::real set) top1_open_sets (\<lambda>st. G st i)"
                      unfolding top1_continuous_map_on_def
                    proof (intro conjI ballI)
                      fix st assume "st \<in> ?M" thus "G st i \<in> (UNIV::real set)" by (by100 simp)
                    next
                      fix V :: "real set" assume hV: "V \<in> top1_open_sets"
                      have hVo: "open V" using hV unfolding top1_open_sets_def by (by100 blast)
                      have "\<forall>B. open B \<longrightarrow> (\<exists>T. open T \<and> T \<inter> ?M = (\<lambda>st. G st i) -` B \<inter> ?M)"
                        using iffD1[OF continuous_on_open_invariant] hc by (by100 blast)
                      then obtain W where hWo: "open W" and hWeq: "W \<inter> ?M = (\<lambda>st. G st i) -` V \<inter> ?M"
                        using hVo by (by100 auto)
                      have "{st \<in> ?M. G st i \<in> V} = ?M \<inter> W" using hWeq by (by100 blast)
                      moreover have "W \<in> (top1_open_sets :: (real\<times>real) set set)"
                        using hWo unfolding top1_open_sets_def by (by100 blast)
                      hence "W \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
                        using product_topology_on_open_sets_real2 by (by100 metis)
                      moreover have "II_topology = subspace_topology UNIV
                          (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
                        unfolding II_topology_def by (rule II_topology_eq_subspace)
                      ultimately have "(I_set \<times> I_set) \<inter> W \<in> II_topology"
                        unfolding subspace_topology_def by (by100 blast)
                      hence "?M \<inter> ((I_set \<times> I_set) \<inter> W) \<in> subspace_topology (I_set \<times> I_set) II_topology ?M"
                        unfolding subspace_topology_def by (by100 blast)
                      moreover have "?M \<inter> ((I_set \<times> I_set) \<inter> W) = ?M \<inter> W"
                        using hM_sub by (by100 blast)
                      ultimately show "{st \<in> ?M. G st i \<in> V}
                          \<in> subspace_topology (I_set \<times> I_set) II_topology ?M"
                        using \<open>{st \<in> ?M. G st i \<in> V} = ?M \<inter> W\<close> by (by100 simp)
                    qed
                  qed
                  \<comment> \<open>Apply Theorem 19.6: G continuous M \<rightarrow> UNIV with product topology.\<close>
                  have hTop_each: "\<forall>j\<in>(UNIV::nat set). is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
                    using top1_open_sets_is_topology_on_UNIV by (by100 blast)
                  have hTM: "is_topology_on ?M (subspace_topology (I_set \<times> I_set) II_topology ?M)"
                    by (rule subspace_topology_is_topology_on[OF hTII hM_sub])
                  have hG_map_PiE: "\<forall>st\<in>?M. G st \<in> top1_PiE UNIV (\<lambda>_::nat. UNIV::real set)"
                    unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
                  have hG_coords: "\<forall>i\<in>(UNIV::nat set). top1_continuous_map_on ?M
                      (subspace_topology (I_set \<times> I_set) II_topology ?M)
                      (UNIV::real set) top1_open_sets (\<lambda>st. (G st) i)"
                    using hcoord_top by (by100 blast)
                  have hG_prod: "top1_continuous_map_on ?M (subspace_topology (I_set \<times> I_set) II_topology ?M)
                      (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
                      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets)) G"
                    using iffD2[OF Theorem_19_6[OF hTM hTop_each hG_map_PiE]] hG_coords by (by100 blast)
                  have hPiE_eq: "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
                    unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
                  have hG_UNIV: "top1_continuous_map_on ?M (subspace_topology (I_set \<times> I_set) II_topology ?M)
                      (UNIV :: (nat \<Rightarrow> real) set)
                      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets)) G"
                    using hG_prod unfolding hPiE_eq .
                  \<comment> \<open>Restrict codomain to S^n.\<close>
                  have hG_img: "G ` ?M \<subseteq> ?Sn"
                  proof (intro image_subsetI)
                    fix st assume "st \<in> ?M" thus "G st \<in> ?Sn" using hG_Sn_M by (by100 blast)
                  qed
                  have hSn_sub': "?Sn \<subseteq> (UNIV :: (nat \<Rightarrow> real) set)" by (by100 simp)
                  show ?thesis unfolding hM_trans
                    by (rule top1_continuous_map_on_codomain_shrink[OF hG_UNIV hG_img hSn_sub'])
                qed
                \<comment> \<open>G on FR = \<alpha>(t*(4-4s)). Same pattern as hG_L.\<close>
                have hG_FR: "top1_continuous_map_on ?FR
                    (subspace_topology ?R (subspace_topology (I_set \<times> I_set) II_topology ?R) ?FR) ?Sn ?TSn G"
                proof -
                  have hFR_sub_R: "?FR \<subseteq> ?R" by (by100 auto)
                  have hFR_trans: "subspace_topology ?R (subspace_topology (I_set \<times> I_set) II_topology ?R) ?FR
                      = subspace_topology (I_set \<times> I_set) II_topology ?FR"
                    by (rule subspace_topology_trans[OF hFR_sub_R])
                  have h\<alpha>_cont_Sn: "top1_continuous_map_on I_set I_top ?Sn ?TSn ?\<alpha>"
                    using h\<alpha>_path_Sn unfolding top1_is_path_on_def by (by100 blast)
                  have h\<nu>_cont: "top1_continuous_map_on ?FR (subspace_topology (I_set \<times> I_set) II_topology ?FR)
                      I_set I_top (\<lambda>(s,t). t * (4 - 4*s))"
                  proof -
                    have h\<nu>_std: "continuous_on UNIV (\<lambda>(s::real,t::real). t * (4 - 4*s))"
                      by (auto intro!: continuous_intros simp: case_prod_beta)
                    have h\<nu>_range: "\<forall>st\<in>?FR. (\<lambda>(s,t). t*(4-4*s)) st \<in> I_set"
                    proof
                      fix st assume "st \<in> ?FR"
                      then obtain s t where hst: "st = (s,t)" "3/4 \<le> s" "s \<le> 1" "0 \<le> t" "t \<le> 1" by (by100 auto)
                      have "t * (4 - 4*s) \<ge> 0" using hst by (by100 simp)
                      moreover have "t * (4 - 4*s) \<le> 1"
                      proof -
                        have "4 - 4*s \<le> 1" using hst by (by100 simp)
                        moreover have "4 - 4*s \<ge> 0" using hst by (by100 simp)
                        ultimately have "t * (4-4*s) \<le> 1*1" using hst by (intro mult_mono) (by100 simp)+
                        thus ?thesis by (by100 simp)
                      qed
                      ultimately show "(\<lambda>(s,t). t*(4-4*s)) st \<in> I_set"
                        unfolding hst top1_unit_interval_def by (by100 simp)
                    qed
                    have hFR_sub': "?FR \<subseteq> I_set \<times> I_set" unfolding top1_unit_interval_def by (by100 auto)
                    have h_cont_FR: "continuous_on ?FR (\<lambda>(s::real,t::real). t*(4-4*s))"
                      using continuous_on_subset[OF h\<nu>_std] by (by100 blast)
                    show ?thesis
                      unfolding top1_continuous_map_on_def
                    proof (intro conjI ballI)
                      fix st assume hst: "st \<in> ?FR"
                      show "(\<lambda>(s,t). t * (4 - 4*s)) st \<in> I_set" using h\<nu>_range hst by (by100 blast)
                    next
                      fix V assume hV: "V \<in> I_top"
                      obtain W where hW: "W \<in> top1_open_sets" and hVeq: "V = I_set \<inter> W"
                        using hV unfolding top1_unit_interval_topology_def subspace_topology_def
                        by (by100 blast)
                      have hWo: "open W" using hW unfolding top1_open_sets_def by (by100 blast)
                      have hpre: "\<exists>A. open A \<and> A \<inter> ?FR = (\<lambda>(s,t). t*(4-4*s)) -` W \<inter> ?FR"
                        using iffD1[OF continuous_on_open_invariant] h_cont_FR hWo by (by100 blast)
                      then obtain A where hAo: "open A" and hAeq: "A \<inter> ?FR = (\<lambda>(s,t). t*(4-4*s)) -` W \<inter> ?FR"
                        by (by100 auto)
                      have "{st \<in> ?FR. (\<lambda>(s,t). t*(4-4*s)) st \<in> V} = ?FR \<inter> A"
                      proof -
                        have "{st \<in> ?FR. (\<lambda>(s,t). t*(4-4*s)) st \<in> V} =
                              {st \<in> ?FR. (\<lambda>(s,t). t*(4-4*s)) st \<in> W}"
                          using h\<nu>_range unfolding hVeq by (by100 blast)
                        also have "\<dots> = ?FR \<inter> A" using hAeq by (by100 blast)
                        finally show ?thesis .
                      qed
                      have "A \<in> (top1_open_sets :: (real\<times>real) set set)"
                        using hAo unfolding top1_open_sets_def by (by100 blast)
                      hence "A \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
                        using product_topology_on_open_sets_real2 by (by100 metis)
                      moreover have "II_topology = subspace_topology UNIV
                          (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
                        unfolding II_topology_def by (rule II_topology_eq_subspace)
                      ultimately have "(I_set \<times> I_set) \<inter> A \<in> II_topology"
                        unfolding subspace_topology_def by (by100 blast)
                      hence "?FR \<inter> ((I_set \<times> I_set) \<inter> A) \<in> subspace_topology (I_set \<times> I_set) II_topology ?FR"
                        unfolding subspace_topology_def by (by100 blast)
                      moreover have "?FR \<inter> ((I_set \<times> I_set) \<inter> A) = ?FR \<inter> A"
                        using hFR_sub' by (by100 blast)
                      ultimately have "?FR \<inter> A \<in> subspace_topology (I_set \<times> I_set) II_topology ?FR"
                        by (by100 simp)
                      thus "{st \<in> ?FR. (\<lambda>(s,t). t*(4-4*s)) st \<in> V}
                          \<in> subspace_topology (I_set \<times> I_set) II_topology ?FR"
                        using \<open>{st \<in> ?FR. (\<lambda>(s,t). t*(4-4*s)) st \<in> V} = ?FR \<inter> A\<close> by (by100 simp)
                    qed
                  qed
                  have hcomp: "top1_continuous_map_on ?FR (subspace_topology (I_set \<times> I_set) II_topology ?FR)
                      ?Sn ?TSn (?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s)))"
                    by (rule top1_continuous_map_on_comp[OF h\<nu>_cont h\<alpha>_cont_Sn])
                  have hG_eq_FR: "\<forall>st\<in>?FR. G st = (?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st"
                  proof
                    fix st assume hst: "st \<in> ?FR"
                    obtain s t where hst_eq: "st = (s,t)" by (cases st)
                    have hs: "3/4 \<le> s" "s \<le> 1" and ht: "0 \<le> t" "t \<le> 1"
                      using hst hst_eq by (by100 auto)+
                    show "G st = (?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st"
                    proof (cases "s > 3/4")
                      case True
                      hence "\<not>(s \<le> 3/4)" by (by100 simp)
                      have "G st = ?\<alpha> (t * (4 - 4*s))" using hG3[OF \<open>\<not>(s \<le> 3/4)\<close>] hst_eq by (by100 simp)
                      thus ?thesis unfolding comp_def hst_eq by (by100 simp)
                    next
                      case False hence hs34: "s = 3/4" using hs(1) by (by100 simp)
                      \<comment> \<open>At s=3/4: both G and \<alpha>\<circ>\<nu> give \<alpha>(t).\<close>
                      have hng2: "\<not> (s \<le> 1/2)" using hs34 by (by100 simp)
                      have hlq2: "s \<le> 3/4" using hs34 by (by100 simp)
                      have hf1: "f (1::real) = x0"
                        using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                      have hfx0: "f (4*s-2) = x0"
                      proof -
                        have "4 * s - 2 = (1::real)" using hs34 by (by100 simp)
                        thus ?thesis using hf1 by (by100 simp)
                      qed
                      have hG34: "G st = ?\<alpha> t"
                      proof (rule ext)
                        fix i :: nat
                        have "G st = (\<lambda>i. ((1-t) * (f (4*s-2)) i + t * ?q i) /
                            sqrt (\<Sum>j\<le>n. ((1-t) * (f (4*s-2)) j + t * ?q j)^2))"
                          using hG2[OF hng2 hlq2] hst_eq by (by100 simp)
                        hence "G st i = ((1-t) * (f (4*s-2)) i + t * ?q i) /
                            sqrt (\<Sum>j\<le>n. ((1-t) * (f (4*s-2)) j + t * ?q j)^2)"
                          by (by100 simp)
                        also have "... = ((1-t) * x0 i + t * ?q i) /
                            sqrt (\<Sum>j\<le>n. ((1-t) * x0 j + t * ?q j)^2)"
                          using hfx0 by (by100 simp)
                        finally show "G st i = ?\<alpha> t i" by (by100 simp)
                      qed
                      have h44s: "4 - 4 * s = (1::real)" using hs34 by (by100 simp)
                      have "(?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st = ?\<alpha> (t * (4 - 4*s))"
                        unfolding comp_def hst_eq by (by100 simp)
                      also have "... = ?\<alpha> (t * 1)" using h44s by (by100 simp)
                      also have "... = ?\<alpha> t" by (by100 simp)
                      finally have "(?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st = ?\<alpha> t" .
                      show ?thesis using hG34 \<open>(?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st = ?\<alpha> t\<close> by (by100 simp)
                    qed
                  qed
                  show ?thesis unfolding hFR_trans top1_continuous_map_on_def
                  proof (intro conjI ballI)
                    fix st assume hst: "st \<in> ?FR"
                    have hGeq_here: "G st = (?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st" using hG_eq_FR hst by (by100 blast)
                    have hcomp_in: "(?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st \<in> ?Sn"
                      using hcomp hst unfolding top1_continuous_map_on_def by (by100 blast)
                    show "G st \<in> ?Sn" using hcomp_in unfolding hGeq_here[symmetric] .
                  next
                    fix V assume hV: "V \<in> ?TSn"
                    have hFR_preimage_alpha: "{st \<in> ?FR. (?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st \<in> V}
                        \<in> subspace_topology (I_set \<times> I_set) II_topology ?FR"
                      using hcomp hV unfolding top1_continuous_map_on_def by (by100 blast)
                    have hFR_preimage_eq: "{st \<in> ?FR. G st \<in> V} = {st \<in> ?FR. (?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st \<in> V}"
	                    proof (intro set_eqI iffI)
	                      fix st assume "st \<in> {st \<in> ?FR. G st \<in> V}"
	                      hence hst_FR: "st \<in> ?FR" and hGst_V: "G st \<in> V" by (by100 blast)+
	                      have "G st = (?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st" using hG_eq_FR hst_FR by (by100 blast)
	                      hence hcomp_st: "(?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st \<in> V"
	                        using hGst_V by (simp only:)
	                      show "st \<in> {st \<in> ?FR. (?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st \<in> V}"
	                        using hst_FR hcomp_st by (simp only: mem_Collect_eq)
	                    next
	                      fix st assume "st \<in> {st \<in> ?FR. (?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st \<in> V}"
	                      hence hst_FR: "st \<in> ?FR"
	                        and hcomp_st: "(?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st \<in> V" by (by100 blast)+
	                      have "G st = (?\<alpha> \<circ> (\<lambda>(s,t). t*(4-4*s))) st" using hG_eq_FR hst_FR by (by100 blast)
	                      hence hG_st: "G st \<in> V"
	                        using hcomp_st by (simp only:)
	                      show "st \<in> {st \<in> ?FR. G st \<in> V}"
	                        using hst_FR hG_st by (simp only: mem_Collect_eq)
	                    qed
                    show "{st \<in> ?FR. G st \<in> V}
                        \<in> subspace_topology (I_set \<times> I_set) II_topology ?FR"
                      unfolding hFR_preimage_eq by (rule hFR_preimage_alpha)
                  qed
                qed
                show ?thesis
                  by (rule pasting_lemma_two_closed[OF hTR hTSn_h hM_closed hFR_closed hMFR_cover hG_Sn_R hG_M hG_FR])
              qed
              show ?thesis
                by (rule pasting_lemma_two_closed[OF hTII hTSn_h hL_closed hR_closed hLR_cover hG_Sn hG_L hG_R])
            qed
            have hU_sub: "?U \<subseteq> ?Sn" by (by100 blast)
            have hG_img: "G ` (I_set \<times> I_set) \<subseteq> ?U"
            proof (intro subsetI) fix w assume "w \<in> G ` (I_set \<times> I_set)"
              then obtain s t where "s \<in> I_set" "t \<in> I_set" "w = G (s,t)" by (by100 blast)
              have "G (s,t) \<in> ?U" using hG_range \<open>s \<in> I_set\<close> \<open>t \<in> I_set\<close> by (by100 blast)
              thus "w \<in> ?U" using \<open>w = G (s,t)\<close> by (by100 simp)
            qed
            show ?thesis
              by (rule top1_continuous_map_on_codomain_shrink[OF hG_cont_Sn hG_img hU_sub])
          qed
          \<comment> \<open>G boundaries.\<close>
          have h\<alpha>0_eq: "?\<alpha> 0 = x0"
            using h\<alpha>_path_Sn unfolding top1_is_path_on_def by (by100 blast)
          have hf_Sn_I: "\<And>s. s \<in> I_set \<Longrightarrow> f s \<in> ?Sn"
          proof -
            fix s assume hs: "s \<in> I_set"
            have hf_cont_U: "top1_continuous_map_on I_set I_top ?U ?TU f"
              using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
            have "f s \<in> ?U" using hf_cont_U hs unfolding top1_continuous_map_on_def by (by100 blast)
            thus "f s \<in> ?Sn" by (by100 blast)
          qed
          have hG_bottom: "\<forall>s\<in>I_set. G (s, 0) =
              top1_path_product (top1_constant_path x0) (top1_path_product f (top1_constant_path x0)) s"
          proof (intro ballI)
            fix s :: real assume hs: "s \<in> I_set"
            show "G (s, 0) = top1_path_product (top1_constant_path x0)
                (top1_path_product f (top1_constant_path x0)) s"
            proof (cases "s \<le> 1/2")
              case True
              have hG: "G (s, 0) = x0"
              proof -
                have "G (s, 0) = ?\<alpha> (0 * (2*s))" using hG1[OF True, of 0] by (by100 simp)
                thus ?thesis using h\<alpha>0_eq by (by100 simp)
              qed
              have "top1_path_product (top1_constant_path x0) (top1_path_product f (top1_constant_path x0)) s
                  = x0" using True unfolding top1_path_product_def top1_constant_path_def by (by100 simp)
              thus ?thesis using hG by (by100 simp)
            next
              case hgt: False hence hs_gt: "s > 1/2" by (by100 linarith)
              show ?thesis
              proof (cases "s \<le> 3/4")
                case True
                have h4sI: "4*s-2 \<in> I_set" using hs_gt True unfolding top1_unit_interval_def by (by100 simp)
                have hfn: "(\<Sum>j\<le>n. ((f (4*s-2)) j)^2) = 1"
                  using hf_Sn_I[OF h4sI] unfolding top1_Sn_def by (by100 blast)
                have hG: "G (s, 0) = f (4*s-2)"
                proof -
                  have hng: "\<not>(s \<le> 1/2)" using hs_gt by (by100 linarith)
                  have "G (s, 0) = (\<lambda>i. ((1-(0::real)) * (f (4*s-2)) i + 0 * ?q i) /
                      sqrt (\<Sum>j\<le>n. ((1-0) * (f (4*s-2)) j + 0 * ?q j)^2))"
                    using hG2[OF hng True, of 0] by (by100 simp)
                  hence "G (s, 0) = (\<lambda>i. (f (4*s-2)) i / sqrt (\<Sum>j\<le>n. ((f (4*s-2)) j)^2))"
                    by (by100 simp)
                  also have "\<dots> = (\<lambda>i. (f (4*s-2)) i)" using hfn by (by100 simp)
                  finally show ?thesis by (by100 simp)
                qed
                have "top1_path_product (top1_constant_path x0) (top1_path_product f (top1_constant_path x0)) s
                  = f (4*s-2)"
                proof -
                  have "2*s-1 \<le> 1/2" using True by (by100 linarith)
                  thus ?thesis using hs_gt unfolding top1_path_product_def top1_constant_path_def
                    by (by100 simp)
                qed
                thus ?thesis using hG by (by100 simp)
              next
                case False hence hs_gt2: "s > 3/4" by (by100 linarith)
                have hng: "\<not>(s \<le> 3/4)" using hs_gt2 by (by100 linarith)
                have "G (s, 0) = ?\<alpha> (0 * (4 - 4*s))" using hG3[OF hng, of 0] by (by100 simp)
                hence hG: "G (s, 0) = x0" using h\<alpha>0_eq by (by100 simp)
                have "2*s-1 > 1/2" using hs_gt2 by (by100 linarith)
                hence "top1_path_product (top1_constant_path x0) (top1_path_product f (top1_constant_path x0)) s
                  = x0" using hs_gt unfolding top1_path_product_def top1_constant_path_def by (by100 simp)
                thus ?thesis using hG by (by100 simp)
              qed
            qed
          qed
          have hG_top: "\<forall>s\<in>I_set. G (s, 1) =
              top1_path_product ?\<alpha> (top1_path_product (top1_constant_path ?q) (top1_path_reverse ?\<alpha>)) s"
          proof (intro ballI)
            fix s :: real assume hs: "s \<in> I_set"
            have hs01: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by (by100 auto)+
            have h\<alpha>1_eq: "?\<alpha> 1 = ?q"
              using h\<alpha>_path_Sn unfolding top1_is_path_on_def by (by100 blast)
            show "G (s, 1) = top1_path_product ?\<alpha>
                (top1_path_product (top1_constant_path ?q) (top1_path_reverse ?\<alpha>)) s"
            proof (cases "s \<le> 1/2")
              case True
              have "G (s, 1) = ?\<alpha> (1 * (2*s))" using hG1[OF True, of 1] by (by100 simp)
              hence hG: "G (s, 1) = ?\<alpha> (2*s)" by (by100 simp)
              have "top1_path_product ?\<alpha> (top1_path_product (top1_constant_path ?q) (top1_path_reverse ?\<alpha>)) s
                  = ?\<alpha> (2*s)" using True unfolding top1_path_product_def by (by100 simp)
              thus ?thesis using hG by (by100 simp)
            next
              case hgt: False hence hs_gt: "s > 1/2" by (by100 linarith)
              show ?thesis
              proof (cases "s \<le> 3/4")
                case True
                have hng: "\<not>(s \<le> 1/2)" using hs_gt by (by100 linarith)
                have "G (s, 1) = (\<lambda>i. ((1-(1::real)) * (f (4*s-2)) i + 1 * ?q i) /
                    sqrt (\<Sum>j\<le>n. ((1-1) * (f (4*s-2)) j + 1 * ?q j)^2))"
                  using hG2[OF hng True, of 1] by (by100 simp)
                hence "G (s, 1) = ?q"
                proof -
                  assume h: "G (s, 1) = (\<lambda>i. ((1-1) * (f (4*s-2)) i + 1 * ?q i) /
                      sqrt (\<Sum>j\<le>n. ((1-1) * (f (4*s-2)) j + 1 * ?q j)^2))"
                  have hqn: "(\<Sum>j\<le>n. (?q j)^2) = 1" using hq_Sn unfolding top1_Sn_def by (by100 blast)
                  have "(\<lambda>i. ((1-(1::real)) * (f (4*s-2)) i + 1 * ?q i) /
                      sqrt (\<Sum>j\<le>n. ((1-1) * (f (4*s-2)) j + 1 * ?q j)^2)) = ?q"
                  proof -
                    have "(\<Sum>j\<le>n. ((1-(1::real)) * (f (4*s-2)) j + 1 * ?q j)^2) = (\<Sum>j\<le>n. (?q j)^2)"
                      by (intro sum.cong arg_cong[of _ _ "\<lambda>x. x^2"]) (by100 simp)+
                    hence hN1: "sqrt (\<Sum>j\<le>n. ((1-1) * (f (4*s-2)) j + 1 * ?q j)^2) = 1" using hqn by (by100 simp)
                    show ?thesis
                    proof (rule ext)
                      fix i show "((1-1) * (f (4*s-2)) i + 1 * ?q i) /
                          sqrt (\<Sum>j\<le>n. ((1-1) * (f (4*s-2)) j + 1 * ?q j)^2) = ?q i"
                        using hN1 by (by100 simp)
                    qed
                  qed
                  thus ?thesis using h by (by100 simp)
                qed
                hence hG: "G (s, 1) = ?q" .
                have "2*s-1 \<le> 1/2" using True by (by100 linarith)
                hence "top1_path_product ?\<alpha> (top1_path_product (top1_constant_path ?q) (top1_path_reverse ?\<alpha>)) s
                    = ?q" using hs_gt unfolding top1_path_product_def top1_constant_path_def by (by100 simp)
                thus ?thesis using hG by (by100 simp)
              next
                case False hence hs_gt2: "s > 3/4" by (by100 linarith)
                have hng: "\<not>(s \<le> 3/4)" using hs_gt2 by (by100 linarith)
                have "G (s, 1) = ?\<alpha> (1 * (4 - 4*s))" using hG3[OF hng, of 1] by (by100 simp)
                hence hG: "G (s, 1) = ?\<alpha> (4 - 4*s)" by (by100 simp)
                have "2*s-1 > 1/2" using hs_gt2 by (by100 linarith)
                hence "top1_path_product ?\<alpha> (top1_path_product (top1_constant_path ?q) (top1_path_reverse ?\<alpha>)) s
                    = top1_path_reverse ?\<alpha> (2*(2*s-1)-1)"
                  using hs_gt unfolding top1_path_product_def top1_constant_path_def by (by100 simp)
                also have "\<dots> = ?\<alpha> (1 - (4*s - 3))" unfolding top1_path_reverse_def by (by100 simp)
                also have "1 - (4*s - 3) = 4 - 4*s" by (by100 algebra)
                finally show ?thesis using hG by (by100 simp)
              qed
            qed
          qed
          have hG_left: "\<forall>t\<in>I_set. G (0, t) = x0"
          proof (intro ballI)
            fix t assume "t \<in> I_set"
            have "G (0, t) = ?\<alpha> (t * 0)" using hG1[of 0 t] by (by100 simp)
            also have "t * 0 = (0::real)" by (by100 simp)
            also have "?\<alpha> 0 = x0" using h\<alpha>_path_Sn unfolding top1_is_path_on_def by (by100 blast)
            finally show "G (0, t) = x0" .
          qed
          have hG_right: "\<forall>t\<in>I_set. G (1, t) = x0"
          proof (intro ballI)
            fix t assume "t \<in> I_set"
            have hng: "\<not>((1::real) \<le> 3/4)" by (by100 simp)
            have h1: "G (1, t) = ?\<alpha> (t * (4 - 4))" using hG3[OF hng, of t] by (by100 simp)
            have h2: "t * (4 - 4) = (0::real)" by (by100 simp)
            have h3: "?\<alpha> 0 = x0" using h\<alpha>_path_Sn unfolding top1_is_path_on_def by (by100 blast)
            show "G (1, t) = x0" using h1 h2 h3 by (by100 simp)
          qed
          \<comment> \<open>Source and target are paths.\<close>
          have hbottom_path: "top1_is_path_on ?U ?TU x0 x0
              (top1_path_product (top1_constant_path x0) (top1_path_product f (top1_constant_path x0)))"
            using hf_eq unfolding top1_path_homotopic_on_def by (by100 blast)
          have htop_path: "top1_is_path_on ?U ?TU x0 x0
              (top1_path_product ?\<alpha> (top1_path_product (top1_constant_path ?q) (top1_path_reverse ?\<alpha>)))"
          proof -
            have h1: "top1_is_path_on ?U ?TU ?q x0 (top1_path_reverse ?\<alpha>)"
              by (rule top1_path_reverse_is_path[OF h\<alpha>_U])
            have hcq: "top1_is_path_on ?U ?TU ?q ?q (top1_constant_path ?q)"
              by (rule top1_constant_path_is_path[OF hTU_here hq_U])
            have h2: "top1_is_path_on ?U ?TU ?q x0 (top1_path_product (top1_constant_path ?q) (top1_path_reverse ?\<alpha>))"
              by (rule top1_path_product_is_path[OF hTU_here hcq h1])
            show ?thesis by (rule top1_path_product_is_path[OF hTU_here h\<alpha>_U h2])
          qed
          show ?thesis unfolding top1_path_homotopic_on_def
            using hbottom_path htop_path hG_cont hG_bottom hG_top hG_left hG_right
            by (intro conjI exI[of _ G]) (by100 blast)+
        qed
        show ?thesis by (rule Lemma_51_1_path_homotopic_trans[OF hTU_here hf_eq hG_strip])
      qed
      \<comment> \<open>\<alpha> * const_q * rev(\<alpha>) \<simeq> \<alpha> * rev(\<alpha>) by left identity.\<close>
      have hTSn_here: "is_topology_on ?Sn ?TSn"
      proof -
        have "\<forall>i\<in>(UNIV::nat set). is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
          using top1_open_sets_is_topology_on_UNIV by (by100 simp)
        hence "is_topology_on (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
            (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
          by (rule top1_product_topology_on_is_topology_on)
        moreover have "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
          unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
        ultimately have "is_topology_on (UNIV::(nat\<Rightarrow>real) set)
            (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))" by (by100 simp)
        thus ?thesis by (rule subspace_topology_is_topology_on) (by100 simp)
      qed
      have hTU_loc: "is_topology_on ?U (subspace_topology ?Sn ?TSn ?U)"
        by (rule subspace_topology_is_topology_on[OF hTSn_here]) (by100 blast)
      have hrev\<alpha>: "top1_is_path_on ?U (subspace_topology ?Sn ?TSn ?U) ?q x0 (top1_path_reverse ?\<alpha>)"
        by (rule top1_path_reverse_is_path[OF h\<alpha>_U])
      have hstep2a: "top1_path_homotopic_on ?U (subspace_topology ?Sn ?TSn ?U) ?q x0
          (top1_path_product (top1_constant_path ?q) (top1_path_reverse ?\<alpha>)) (top1_path_reverse ?\<alpha>)"
        by (rule Theorem_51_2_left_identity[OF hTU_loc hrev\<alpha>])
      have hstep2: "top1_path_homotopic_on ?U (subspace_topology ?Sn ?TSn ?U) x0 x0
          (top1_path_product ?\<alpha> (top1_path_product (top1_constant_path ?q) (top1_path_reverse ?\<alpha>)))
          (top1_path_product ?\<alpha> (top1_path_reverse ?\<alpha>))"
        by (rule path_homotopic_product_right[OF hTU_loc hstep2a h\<alpha>_U])
      \<comment> \<open>\<alpha> * rev(\<alpha>) \<simeq> const_{x0} by inverse law.\<close>
      have hstep3: "top1_path_homotopic_on ?U (subspace_topology ?Sn ?TSn ?U) x0 x0
          (top1_path_product ?\<alpha> (top1_path_reverse ?\<alpha>)) (top1_constant_path x0)"
        by (rule Theorem_51_2_invgerse_left[OF hTU_loc h\<alpha>_U])
      show "top1_path_homotopic_on ?U (subspace_topology ?Sn ?TSn ?U) x0 x0 f (top1_constant_path x0)"
        by (rule Lemma_51_1_path_homotopic_trans[OF hTU_loc
              Lemma_51_1_path_homotopic_trans[OF hTU_loc hstrip hstep2] hstep3])
    qed
  qed
  have hV_sc: "top1_simply_connected_on ?V (subspace_topology ?Sn ?TSn ?V)"
  proof -
    \<comment> \<open>Reflection \<phi> negating coordinate 0 is a homeomorphism V \<rightarrow> U.\<close>
    let ?\<phi> = "\<lambda>(x::nat\<Rightarrow>real). (\<lambda>i. if i = 0 then - x 0 else x i)"
    have h\<phi>_Sn: "\<And>x. x \<in> ?Sn \<Longrightarrow> ?\<phi> x \<in> ?Sn"
    proof -
      fix x assume hx: "x \<in> ?Sn"
      have hx_norm: "(\<Sum>j\<le>n. (x j)^2) = 1" using hx unfolding top1_Sn_def by (by100 blast)
      have hx_ext: "\<And>j. j \<ge> Suc n \<Longrightarrow> x j = 0" using hx unfolding top1_Sn_def by (by100 blast)
      have "(\<Sum>j\<le>n. ((if j = 0 then - x 0 else x j))^2) = (\<Sum>j\<le>n. (x j)^2)"
        by (rule sum.cong) (by100 auto)+
      hence "(\<Sum>j\<le>n. (?\<phi> x j)^2) = 1" using hx_norm by (by100 simp)
      moreover have "\<And>j. j \<ge> Suc n \<Longrightarrow> ?\<phi> x j = 0" using hx_ext by (by100 auto)
      ultimately show "?\<phi> x \<in> ?Sn" unfolding top1_Sn_def by (by100 blast)
    qed
    have h\<phi>_inv: "\<And>x. ?\<phi> (?\<phi> x) = x" by (rule ext) (by100 auto)
    have h\<phi>_p: "?\<phi> ?p = ?q" by (rule ext) (by100 simp)
    have h\<phi>_q: "?\<phi> ?q = ?p" by (rule ext) (by100 simp)
    \<comment> \<open>\<phi> maps V to U and U to V.\<close>
    have h\<phi>_VU: "\<And>x. x \<in> ?V \<Longrightarrow> ?\<phi> x \<in> ?U"
    proof -
      fix x assume hx: "x \<in> ?V"
      have "x \<in> ?Sn" "x \<noteq> ?q" using hx by (by100 blast)+
      have "?\<phi> x \<in> ?Sn" using h\<phi>_Sn \<open>x \<in> ?Sn\<close> by (by100 blast)
      moreover have "?\<phi> x \<noteq> ?p"
      proof assume h: "?\<phi> x = ?p"
        from arg_cong[OF h, of ?\<phi>] have "?\<phi> (?\<phi> x) = ?\<phi> ?p" .
        hence "x = ?q" using h\<phi>_inv h\<phi>_p by (by100 metis)
        thus False using \<open>x \<noteq> ?q\<close> by (by100 simp)
      qed
      ultimately show "?\<phi> x \<in> ?U" by (by100 blast)
    qed
    have h\<phi>_UV: "\<And>x. x \<in> ?U \<Longrightarrow> ?\<phi> x \<in> ?V"
    proof -
      fix x assume hx: "x \<in> ?U"
      have "x \<in> ?Sn" "x \<noteq> ?p" using hx by (by100 blast)+
      have "?\<phi> x \<in> ?Sn" using h\<phi>_Sn \<open>x \<in> ?Sn\<close> by (by100 blast)
      moreover have "?\<phi> x \<noteq> ?q"
      proof assume h: "?\<phi> x = ?q"
        from arg_cong[OF h, of ?\<phi>] have "?\<phi> (?\<phi> x) = ?\<phi> ?q" .
        hence "x = ?p" using h\<phi>_inv h\<phi>_q by (by100 metis)
        thus False using \<open>x \<noteq> ?p\<close> by (by100 simp)
      qed
      ultimately show "?\<phi> x \<in> ?V" by (by100 blast)
    qed
    \<comment> \<open>\<phi> is a homeomorphism V \<rightarrow> U (involution, bijective, continuous).\<close>
    \<comment> \<open>\<phi> continuous on S^n: each coordinate is a projection or negation.\<close>
    have hTop_each: "\<forall>j\<in>(UNIV::nat set). is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
      using top1_open_sets_is_topology_on_UNIV by (by100 blast)
    have hPiE_eq: "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
      unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
    have hTprod: "is_topology_on (UNIV :: (nat \<Rightarrow> real) set)
        (top1_product_topology_on UNIV (\<lambda>_::nat. UNIV::real set) (\<lambda>_. top1_open_sets))"
    proof -
      have "is_topology_on (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
          (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
        by (rule top1_product_topology_on_is_topology_on[OF hTop_each])
      thus ?thesis unfolding hPiE_eq .
    qed
    have hSn_sub: "?Sn \<subseteq> (UNIV :: (nat \<Rightarrow> real) set)" by (by100 simp)
    have hTSn_loc: "is_topology_on ?Sn ?TSn"
      by (rule subspace_topology_is_topology_on[OF hTprod hSn_sub])
    \<comment> \<open>Projection \<pi>_j is continuous S^n \<rightarrow> R.\<close>
    have hproj: "\<And>j. top1_continuous_map_on ?Sn ?TSn (UNIV::real set) top1_open_sets (\<lambda>x. x j)"
    proof -
      fix j :: nat
      have "top1_continuous_map_on (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
          (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))
          (UNIV::real set) top1_open_sets (\<lambda>x. x j)"
        by (rule top1_continuous_map_on_product_projection[OF hTop_each]) (by100 simp)
      thus "top1_continuous_map_on ?Sn ?TSn (UNIV::real set) top1_open_sets (\<lambda>x. x j)"
        using top1_continuous_map_on_restrict_domain_simple[OF _ hSn_sub]
        unfolding hPiE_eq by (by100 simp)
    qed
    \<comment> \<open>Negation uminus is continuous R \<rightarrow> R.\<close>
    have hneg_cont: "top1_continuous_map_on (UNIV::real set) top1_open_sets
        (UNIV::real set) top1_open_sets uminus"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x :: real show "- x \<in> (UNIV::real set)" by (by100 simp)
    next
      fix V :: "real set" assume "V \<in> top1_open_sets"
      hence hVo: "open V" unfolding top1_open_sets_def by (by100 blast)
      have "continuous_on UNIV (uminus :: real \<Rightarrow> real)" by (intro continuous_intros)
      hence h_inv: "\<forall>B. open B \<longrightarrow> (\<exists>T. open T \<and> T \<inter> UNIV = uminus -` B \<inter> (UNIV::real set))"
        using iffD1[OF continuous_on_open_invariant] by (by100 blast)
      then obtain W where hWo: "open W" and hWeq: "W \<inter> UNIV = uminus -` V \<inter> (UNIV::real set)"
        using hVo by (by100 auto)
      have "{x \<in> (UNIV::real set). - x \<in> V} = W" using hWeq by (by100 blast)
      thus "{x \<in> (UNIV::real set). - x \<in> V} \<in> top1_open_sets"
        using hWo unfolding top1_open_sets_def by (by100 simp)
    qed
    \<comment> \<open>\<phi>(x)(0) = -(x 0): compose projection with negation.\<close>
    have hneg0: "top1_continuous_map_on ?Sn ?TSn (UNIV::real set) top1_open_sets (\<lambda>x. - x 0)"
    proof -
      have "top1_continuous_map_on ?Sn ?TSn (UNIV::real set) top1_open_sets (uminus \<circ> (\<lambda>x. x 0))"
        by (rule top1_continuous_map_on_comp[OF hproj[of 0] hneg_cont])
      thus ?thesis unfolding comp_def by (by100 simp)
    qed
    \<comment> \<open>Each coordinate of \<phi> is continuous.\<close>
    have h\<phi>_coord: "\<And>i. top1_continuous_map_on ?Sn ?TSn (UNIV::real set) top1_open_sets (\<lambda>x. ?\<phi> x i)"
    proof -
      fix i :: nat
      show "top1_continuous_map_on ?Sn ?TSn (UNIV::real set) top1_open_sets (\<lambda>x. ?\<phi> x i)"
      proof (cases "i = 0")
        case True thus ?thesis using hneg0 by (by100 simp)
      next
        case False thus ?thesis using hproj[of i] by (by100 simp)
      qed
    qed
    \<comment> \<open>Theorem 19.6: \<phi> continuous S^n \<rightarrow> product topology.\<close>
    have h\<phi>_map_PiE: "\<forall>x\<in>?Sn. ?\<phi> x \<in> top1_PiE UNIV (\<lambda>_::nat. UNIV::real set)"
      unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
    have h\<phi>_coords: "\<forall>i\<in>(UNIV::nat set). top1_continuous_map_on ?Sn ?TSn
        (UNIV::real set) top1_open_sets (\<lambda>x. (?\<phi> x) i)"
      using h\<phi>_coord by (by100 blast)
    have h\<phi>_prod: "top1_continuous_map_on ?Sn ?TSn
        (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
        (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets)) ?\<phi>"
      using iffD2[OF Theorem_19_6[OF hTSn_loc hTop_each h\<phi>_map_PiE]] h\<phi>_coords by (by100 blast)
    have h\<phi>_UNIV: "top1_continuous_map_on ?Sn ?TSn (UNIV :: (nat \<Rightarrow> real) set)
        (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets)) ?\<phi>"
      using h\<phi>_prod unfolding hPiE_eq .
    have h\<phi>_img: "?\<phi> ` ?Sn \<subseteq> ?Sn"
      by (intro image_subsetI) (rule h\<phi>_Sn)
    have h\<phi>_cont_Sn: "top1_continuous_map_on ?Sn ?TSn ?Sn ?TSn ?\<phi>"
      by (rule top1_continuous_map_on_codomain_shrink[OF h\<phi>_UNIV h\<phi>_img hSn_sub])
    \<comment> \<open>Restrict: \<phi> continuous V \<rightarrow> U and U \<rightarrow> V.\<close>
    have hV_sub: "?V \<subseteq> ?Sn" by (by100 blast)
    have hU_sub_Sn: "?U \<subseteq> ?Sn" by (by100 blast)
    have h\<phi>_cont_V: "top1_continuous_map_on ?V (subspace_topology ?Sn ?TSn ?V)
        ?U (subspace_topology ?Sn ?TSn ?U) ?\<phi>"
    proof -
      have h1: "top1_continuous_map_on ?V (subspace_topology ?Sn ?TSn ?V) ?Sn ?TSn ?\<phi>"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF h\<phi>_cont_Sn hV_sub])
      have h2: "?\<phi> ` ?V \<subseteq> ?U"
        by (intro image_subsetI) (rule h\<phi>_VU)
      show ?thesis by (rule top1_continuous_map_on_codomain_shrink[OF h1 h2 hU_sub_Sn])
    qed
    have h\<phi>_cont_U: "top1_continuous_map_on ?U (subspace_topology ?Sn ?TSn ?U)
        ?V (subspace_topology ?Sn ?TSn ?V) ?\<phi>"
    proof -
      have h1: "top1_continuous_map_on ?U (subspace_topology ?Sn ?TSn ?U) ?Sn ?TSn ?\<phi>"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF h\<phi>_cont_Sn hU_sub_Sn])
      have h2: "?\<phi> ` ?U \<subseteq> ?V"
        by (intro image_subsetI) (rule h\<phi>_UV)
      show ?thesis by (rule top1_continuous_map_on_codomain_shrink[OF h1 h2 hV_sub])
    qed
    \<comment> \<open>Bijection V \<rightarrow> U.\<close>
    have h\<phi>_bij: "bij_betw ?\<phi> ?V ?U"
    proof (rule bij_betw_byWitness[of _ ?\<phi>])
      show "\<forall>x\<in>?V. ?\<phi> (?\<phi> x) = x" using h\<phi>_inv by (by100 blast)
      show "\<forall>y\<in>?U. ?\<phi> (?\<phi> y) = y" using h\<phi>_inv by (by100 blast)
      show "?\<phi> ` ?V \<subseteq> ?U" by (intro image_subsetI) (rule h\<phi>_VU)
      show "?\<phi> ` ?U \<subseteq> ?V" by (intro image_subsetI) (rule h\<phi>_UV)
    qed
    \<comment> \<open>inv_into V \<phi> = \<phi> on U (since \<phi> is an involution).\<close>
    have h\<phi>_inv_into: "\<And>y. y \<in> ?U \<Longrightarrow> inv_into ?V ?\<phi> y = ?\<phi> y"
    proof -
      fix y assume hy: "y \<in> ?U"
	      have h\<phi>y_V: "?\<phi> y \<in> ?V" by (rule h\<phi>_UV[OF hy])
	      have hinj: "inj_on ?\<phi> ?V" using bij_betw_imp_inj_on[OF h\<phi>_bij] .
	      show "inv_into ?V ?\<phi> y = ?\<phi> y"
	      proof -
	        have h_inv_y: "inv_into ?V ?\<phi> (?\<phi> (?\<phi> y)) = ?\<phi> y"
	          by (rule inv_into_f_eq[OF hinj h\<phi>y_V], rule refl)
	        show ?thesis using h_inv_y h\<phi>_inv[of y] by (simp only:)
	      qed
	    qed
    \<comment> \<open>Assemble the homeomorphism.\<close>
    have h\<phi>_homeo: "top1_homeomorphism_on ?V (subspace_topology ?Sn ?TSn ?V)
        ?U (subspace_topology ?Sn ?TSn ?U) ?\<phi>"
      unfolding top1_homeomorphism_on_def
    proof (intro conjI)
      show "is_topology_on ?V (subspace_topology ?Sn ?TSn ?V)"
        by (rule subspace_topology_is_topology_on[OF hTSn_loc hV_sub])
      show "is_topology_on ?U (subspace_topology ?Sn ?TSn ?U)"
        by (rule subspace_topology_is_topology_on[OF hTSn_loc hU_sub_Sn])
      show "bij_betw ?\<phi> ?V ?U" by (rule h\<phi>_bij)
      show "top1_continuous_map_on ?V (subspace_topology ?Sn ?TSn ?V) ?U (subspace_topology ?Sn ?TSn ?U) ?\<phi>"
        by (rule h\<phi>_cont_V)
      show "top1_continuous_map_on ?U (subspace_topology ?Sn ?TSn ?U) ?V (subspace_topology ?Sn ?TSn ?V)
          (inv_into ?V ?\<phi>)"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix y assume hy: "y \<in> ?U"
        have "inv_into ?V ?\<phi> y = ?\<phi> y" by (rule h\<phi>_inv_into[OF hy])
        thus "inv_into ?V ?\<phi> y \<in> ?V" using h\<phi>_UV[OF hy] by (by100 simp)
      next
        fix W assume hW: "W \<in> subspace_topology ?Sn ?TSn ?V"
        have "{y \<in> ?U. inv_into ?V ?\<phi> y \<in> W} = {y \<in> ?U. ?\<phi> y \<in> W}"
        proof (intro set_eqI iffI)
          fix y assume "y \<in> {y \<in> ?U. inv_into ?V ?\<phi> y \<in> W}"
          hence hy: "y \<in> ?U" "inv_into ?V ?\<phi> y \<in> W" by (by100 blast)+
          thus "y \<in> {y \<in> ?U. ?\<phi> y \<in> W}" using h\<phi>_inv_into[OF hy(1)] by (by100 simp)
        next
          fix y assume "y \<in> {y \<in> ?U. ?\<phi> y \<in> W}"
          hence hy: "y \<in> ?U" "?\<phi> y \<in> W" by (by100 blast)+
          thus "y \<in> {y \<in> ?U. inv_into ?V ?\<phi> y \<in> W}" using h\<phi>_inv_into[OF hy(1)] by (by100 simp)
        qed
        moreover have "{y \<in> ?U. ?\<phi> y \<in> W} \<in> subspace_topology ?Sn ?TSn ?U"
          using h\<phi>_cont_U hW unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "{y \<in> ?U. inv_into ?V ?\<phi> y \<in> W} \<in> subspace_topology ?Sn ?TSn ?U"
          by (by100 simp)
      qed
    qed
    show ?thesis by (rule homeomorphism_preserves_simply_connected[OF h\<phi>_homeo hU_sc])
  qed
  \<comment> \<open>Step 2: U, V are open in S^n.\<close>
  \<comment> \<open>U = S^n - {p} and V = S^n - {q} are open because {p}, {q} are closed in S^n
     (Hausdorff + singleton closed).\<close>
  \<comment> \<open>S^n is Hausdorff (subspace of Hausdorff product). Singletons are closed, so complements are open.\<close>
  have hProd_haus: "is_hausdorff_on (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
    by (rule Theorem_19_4_product) (simp add: top1_R_is_hausdorff)
  have hPiE_eq: "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
    unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
  have hProd_haus_UNIV: "is_hausdorff_on (UNIV :: (nat \<Rightarrow> real) set)
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
    using hProd_haus unfolding hPiE_eq .
  have hSn_sub_UNIV: "?Sn \<subseteq> (UNIV :: (nat \<Rightarrow> real) set)" by simp
  have hSn_haus: "is_hausdorff_on ?Sn ?TSn"
    using conjunct2[OF conjunct2[OF Theorem_17_11]] hProd_haus_UNIV hSn_sub_UNIV by (by100 blast)
  have hp_in_Sn: "?p \<in> ?Sn" unfolding top1_Sn_def
  proof (intro CollectI conjI allI impI)
    fix i :: nat assume "i \<ge> Suc n" thus "?p i = 0" using assms by simp
  next
    have "(\<Sum>i\<le>n. (?p i)\<^sup>2) = (\<Sum>i\<le>n. (if i = 0 then 1 else (0::real)))"
      by (rule sum.cong) simp_all
    also have "\<dots> = 1"
    proof -
      have hfin: "finite ({..n}::nat set)" by simp
      have h0n: "(0::nat) \<in> {..n}" using assms by simp
      show ?thesis using sum.delta'[OF hfin, of 0 "\<lambda>_. 1::real"] h0n by simp
    qed
    finally show "(\<Sum>i\<le>n. (?p i)\<^sup>2) = 1" .
  qed
  have hq_in_Sn: "?q \<in> ?Sn" unfolding top1_Sn_def
  proof (intro CollectI conjI allI impI)
    fix i :: nat assume "i \<ge> Suc n" thus "?q i = 0" using assms by simp
  next
    have "(\<Sum>i\<le>n. (?q i)\<^sup>2) = (\<Sum>i\<le>n. (if i = 0 then 1 else (0::real)))"
      by (rule sum.cong) (simp_all add: power2_eq_square)
    also have "\<dots> = 1"
    proof -
      have hfin: "finite ({..n}::nat set)" by simp
      have h0n: "(0::nat) \<in> {..n}" using assms by simp
      show ?thesis using sum.delta'[OF hfin, of 0 "\<lambda>_. 1::real"] h0n by simp
    qed
    finally show "(\<Sum>i\<le>n. (?q i)\<^sup>2) = 1" .
  qed
  have hp_closed: "closedin_on ?Sn ?TSn {?p}"
    by (rule singleton_closed_in_hausdorff[OF hSn_haus hp_in_Sn])
  have hq_closed: "closedin_on ?Sn ?TSn {?q}"
    by (rule singleton_closed_in_hausdorff[OF hSn_haus hq_in_Sn])
  have hU_open: "openin_on ?Sn ?TSn ?U"
    by (rule closedin_complement_openin[OF hp_closed])
  have hV_open: "openin_on ?Sn ?TSn ?V"
    by (rule closedin_complement_openin[OF hq_closed])
  \<comment> \<open>U \<union> V = S^n (every point of S^n differs from p or q).\<close>
  have hpq_ne: "?p \<noteq> ?q"
  proof -
    have "?p 0 = (1::real)" by simp
    moreover have "?q 0 = (-1::real)" by simp
    ultimately show ?thesis by (metis one_neq_neg_one)
  qed
  have hUV: "?U \<union> ?V = ?Sn" using hpq_ne by (by100 blast)
  \<comment> \<open>U \<inter> V = S^n - {p, q} is path-connected for n \<ge> 2.\<close>
  have hUV_ne: "?U \<inter> ?V \<noteq> {}"
  proof -
    \<comment> \<open>The point with x(1)=1 and x(i)=0 otherwise is in S^n (for n\<ge>2) and differs from p,q.\<close>
    let ?r = "\<lambda>i::nat. if i = 1 then (1::real) else 0"
    have hr_Sn: "?r \<in> ?Sn" unfolding top1_Sn_def
    proof (intro CollectI conjI allI impI)
      fix i :: nat assume "i \<ge> Suc n"
      hence "i \<noteq> 1" using assms by linarith
      thus "?r i = 0" by simp
    next
      have h1n: "(1::nat) \<le> n" using assms by linarith
      have "(\<Sum>i\<le>n. (?r i)\<^sup>2) = (\<Sum>i\<le>n. (if i = 1 then 1 else (0::real)))"
      proof (rule sum.cong)
        fix i assume "i \<in> {..n}"
        show "(?r i)\<^sup>2 = (if i = 1 then 1 else 0)" by simp
      qed simp
      also have "\<dots> = 1"
      proof -
        have hfin: "finite ({..n}::nat set)" by simp
        have "(\<Sum>i\<le>n. (if i = (1::nat) then (1::real) else 0))
            = (if (1::nat) \<in> {..n} then 1 else 0)"
          using sum.delta'[OF hfin, of 1 "\<lambda>_. 1::real"] by simp
        also have "\<dots> = 1" using h1n by simp
        finally show ?thesis .
      qed
      finally show "(\<Sum>i\<le>n. (?r i)\<^sup>2) = 1" .
    qed
    have hr_ne_p: "?r \<noteq> ?p"
    proof -
      have "?r 0 = (0::real)" by simp
      moreover have "?p 0 = (1::real)" by simp
      ultimately show ?thesis by (metis zero_neq_one)
    qed
    have hr_ne_q: "?r \<noteq> ?q"
    proof -
      have "?r 0 = (0::real)" by simp
      moreover have "?q 0 = (-1::real)" by simp
      ultimately show ?thesis by (metis neg_0_equal_iff_equal zero_neq_one)
    qed
    have "?r \<in> ?U \<inter> ?V" using hr_Sn hr_ne_p hr_ne_q by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  \<comment> \<open>Topology facts needed for path-connected proof.\<close>
  have hTop_each: "\<forall>i\<in>(UNIV::nat set). is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
    using top1_open_sets_is_topology_on_UNIV by simp
  have hTop_prod: "is_topology_on (top1_PiE UNIV (\<lambda>_::nat. UNIV::real set))
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
    by (rule top1_product_topology_on_is_topology_on[OF hTop_each])
  have hPiE_eq: "top1_PiE UNIV (\<lambda>_::nat. UNIV::real set) = UNIV"
    unfolding top1_PiE_def top1_Pi_def top1_extensional_def by (by100 auto)
  have hTop_UNIV: "is_topology_on (UNIV :: (nat \<Rightarrow> real) set)
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))"
    using hTop_prod unfolding hPiE_eq .
  have hTSn_top: "is_topology_on ?Sn ?TSn"
    by (rule subspace_topology_is_topology_on[OF hTop_UNIV]) simp
  have hTUV: "is_topology_on (?U \<inter> ?V) (subspace_topology ?Sn ?TSn (?U \<inter> ?V))"
    by (rule subspace_topology_is_topology_on[OF hTSn_top]) (by100 blast)
  have hUV_pc: "top1_path_connected_on (?U \<inter> ?V)
      (subspace_topology ?Sn ?TSn (?U \<inter> ?V))"
    unfolding top1_path_connected_on_def
  proof (intro conjI ballI)
    show "is_topology_on (?U \<inter> ?V) (subspace_topology ?Sn ?TSn (?U \<inter> ?V))" by (rule hTUV)
  next
    \<comment> \<open>For any x,y \<in> S^n - {p,q}, construct path x \<rightarrow> r \<rightarrow> y via great circle arcs.
       The equator point r = (\<lambda>i. if i=1 then 1 else 0) is in U \<inter> V (already proved).
       Path: \<gamma>(t) = normalize((1-t)x + tr) — well-defined since x \<noteq> -r.\<close>
    fix x y assume hx: "x \<in> ?U \<inter> ?V" and hy: "y \<in> ?U \<inter> ?V"
    have hx_Sn: "x \<in> ?Sn" and hx_np: "x \<noteq> ?p" and hx_nq: "x \<noteq> ?q"
      using hx by (by100 blast)+
    have hy_Sn: "y \<in> ?Sn" and hy_np: "y \<noteq> ?p" and hy_nq: "y \<noteq> ?q"
      using hy by (by100 blast)+
    \<comment> \<open>Use equator point r. Connect x \<rightarrow> r \<rightarrow> y via great circle arcs.
       Need x \<noteq> -r and y \<noteq> -r. If either fails, use alternate point r'.\<close>
    let ?r = "\<lambda>i::nat. if i = 1 then (1::real) else 0"
    have hr_Sn: "?r \<in> ?Sn" unfolding top1_Sn_def
    proof (intro CollectI conjI allI impI)
      fix i :: nat assume "i \<ge> Suc n"
      hence "i \<noteq> 1" using assms by (by100 linarith)
      thus "?r i = 0" by (by100 simp)
    next
      have h1n: "(1::nat) \<le> n" using assms by (by100 linarith)
      have "(\<Sum>i\<le>n. (?r i)\<^sup>2) = (\<Sum>i\<le>n. (if i = 1 then 1 else 0::real))"
        by (intro sum.cong) (by100 simp)+
      also have "\<dots> = 1" using sum.delta'[of "{..n}" 1 "\<lambda>_. (1::real)"] h1n by (by100 simp)
      finally show "(\<Sum>i\<le>n. (?r i)\<^sup>2) = 1" .
    qed
    have hr_ne_p: "?r \<noteq> ?p" by (metis zero_neq_one)
    have hr_ne_q: "?r \<noteq> ?q" by (metis neg_0_equal_iff_equal zero_neq_one)
    have hr_UV: "?r \<in> ?U \<inter> ?V" using hr_Sn hr_ne_p hr_ne_q by (by100 blast)
    have hUV_sub: "?U \<inter> ?V \<subseteq> ?Sn" by (by100 blast)
    have hpath_to_r: "\<And>z. z \<in> ?U \<inter> ?V \<Longrightarrow>
        \<exists>f. top1_is_path_on (?U \<inter> ?V) (subspace_topology ?Sn ?TSn (?U \<inter> ?V)) z ?r f"
    proof -
      fix z assume hz: "z \<in> ?U \<inter> ?V"
      have hz_Sn: "z \<in> ?Sn" and hz_np: "z \<noteq> ?p" and hz_nq: "z \<noteq> ?q" using hz by (by100 blast)+
      \<comment> \<open>The interpolation from z to any equator point e gives a path on S^n.
         We need it to also avoid p and q. For target r with z \<noteq> -r: this works
         because normalize((1-t)z+tr) = p or q forces z to have specific form
         (all coords \<ge> 2 zero), but z \<in> S^n-{p,q} and n \<ge> 2 provides enough freedom.
         If z = -r, use r' = e_2 instead, then chain r' \<rightarrow> r.\<close>
      show "\<exists>f. top1_is_path_on (?U \<inter> ?V) (subspace_topology ?Sn ?TSn (?U \<inter> ?V)) z ?r f"
      proof (cases "\<exists>k. k \<ge> 2 \<and> k \<le> n \<and> z k \<noteq> 0")
        case True
        \<comment> \<open>z has nonzero coord \<ge> 2: z \<noteq> -r since -r has coords \<ge> 2 all zero.\<close>
        have hz_na: "z \<noteq> (\<lambda>i. - ?r i)"
        proof
          assume "z = (\<lambda>i. - ?r i)"
          hence "\<And>k. k \<ge> 2 \<Longrightarrow> z k = 0" by (by100 simp)
          thus False using True by (by100 blast)
        qed
        let ?\<gamma> = "\<lambda>t i. ((1-t) * z i + t * ?r i) / sqrt (\<Sum>j\<le>n. ((1-t) * z j + t * ?r j)^2)"
        have hpath_Sn: "top1_is_path_on ?Sn ?TSn z ?r ?\<gamma>"
          by (rule Sn_normalized_interpolation_path[OF hz_Sn hr_Sn hz_na])
        \<comment> \<open>This path avoids p,q because hitting them requires z(j)=0 for j \<ge> 2, contradicting True.\<close>
        have havoids: "\<forall>t. ?\<gamma> t \<in> ?U \<inter> ?V"
        proof (intro allI)
          fix t
          have h\<gamma>_Sn: "?\<gamma> t \<in> ?Sn"
            by (rule Sn_interpolation_in_Sn[OF hz_Sn hr_Sn hz_na])
          have h\<gamma>_np: "?\<gamma> t \<noteq> ?p"
          proof
            assume heq: "?\<gamma> t = ?p"
            \<comment> \<open>For k \<ge> 2 with z(k) \<noteq> 0: p(k) = 0 and r(k) = 0, so
               ((1-t)*z(k) + t*0)/N = 0, hence (1-t)*z(k) = 0.
               If t \<noteq> 1: z(k) = 0, contradiction. If t = 1: \<gamma>(1) = r \<noteq> p.\<close>
            obtain k where hk: "k \<ge> 2" "k \<le> n" "z k \<noteq> 0" using True by (by100 blast)
            have hpk: "?p k = 0" using hk(1) by (by100 simp)
            have hrk: "?r k = 0" using hk(1) by (by100 simp)
            have hN_pos: "sqrt (\<Sum>j\<le>n. ((1-t) * z j + t * ?r j)^2) > 0"
              by (rule Sn_interpolation_norm_pos[OF hz_Sn hr_Sn hz_na])
            have "?\<gamma> t k = ?p k" using fun_cong[OF heq, of k] by (by100 simp)
            hence "((1-t) * z k + t * ?r k) / sqrt (\<Sum>j\<le>n. ((1-t) * z j + t * ?r j)^2) = 0"
              using hpk by (by100 simp)
            hence "(1-t) * z k + t * ?r k = 0" using hN_pos by (by100 simp)
            hence "(1-t) * z k = 0" using hrk by (by100 simp)
            hence "t = 1" using hk(3) using mult_eq_0_iff by (by100 simp)
            hence "?\<gamma> t = ?r" using Sn_interpolation_at_1[OF hz_Sn hr_Sn hz_na] by (by100 simp)
            thus False using heq hr_ne_p by (by100 simp)
          qed
          have h\<gamma>_nq: "?\<gamma> t \<noteq> ?q"
          proof
            assume heq: "?\<gamma> t = ?q"
            obtain k where hk: "k \<ge> 2" "k \<le> n" "z k \<noteq> 0" using True by (by100 blast)
            have hqk: "?q k = 0" using hk(1) by (by100 simp)
            have hrk: "?r k = 0" using hk(1) by (by100 simp)
            have hN_pos: "sqrt (\<Sum>j\<le>n. ((1-t) * z j + t * ?r j)^2) > 0"
              by (rule Sn_interpolation_norm_pos[OF hz_Sn hr_Sn hz_na])
            have "?\<gamma> t k = ?q k" using fun_cong[OF heq, of k] by (by100 simp)
            hence "((1-t) * z k + t * ?r k) / sqrt (\<Sum>j\<le>n. ((1-t) * z j + t * ?r j)^2) = 0"
              using hqk by (by100 simp)
            hence "(1-t) * z k = 0" using hN_pos hrk by (by100 simp)
            hence "t = 1" using hk(3) using mult_eq_0_iff by (by100 simp)
            hence "?\<gamma> t = ?r" using Sn_interpolation_at_1[OF hz_Sn hr_Sn hz_na] by (by100 simp)
            thus False using heq hr_ne_q by (by100 simp)
          qed
          show "?\<gamma> t \<in> ?U \<inter> ?V" using h\<gamma>_Sn h\<gamma>_np h\<gamma>_nq by (by100 blast)
        qed
        have "top1_is_path_on (?U \<inter> ?V) (subspace_topology ?Sn ?TSn (?U \<inter> ?V)) z ?r ?\<gamma>"
        proof -
          have h_cont: "top1_continuous_map_on I_set I_top ?Sn ?TSn ?\<gamma>"
            using hpath_Sn unfolding top1_is_path_on_def by (by100 blast)
          have h_img: "?\<gamma> ` I_set \<subseteq> ?U \<inter> ?V"
          proof (intro subsetI)
            fix w assume "w \<in> ?\<gamma> ` I_set"
            then obtain t where "w = ?\<gamma> t" by (by100 blast)
            thus "w \<in> ?U \<inter> ?V" using havoids by (by100 simp)
          qed
          show ?thesis unfolding top1_is_path_on_def
            using top1_continuous_map_on_codomain_shrink[OF h_cont h_img hUV_sub]
            hpath_Sn[unfolded top1_is_path_on_def] by (by100 blast)
        qed
        thus ?thesis by (by100 blast)
      next
        case False
        hence hzero2: "\<And>k. k \<ge> 2 \<Longrightarrow> k \<le> n \<Longrightarrow> z k = 0" by (by100 blast)
        \<comment> \<open>z(1) \<noteq> 0: if z(1) = 0, then z(i)=0 for i\<ge>1, so z = (\<plusminus>1,0,...) = p or q.\<close>
        have hz1_ne: "z 1 \<noteq> 0"
        proof
          assume "z 1 = 0"
          have "\<And>i. i \<ge> 1 \<Longrightarrow> i \<le> n \<Longrightarrow> z i = 0"
          proof -
            fix i assume "i \<ge> 1" "i \<le> n"
            show "z i = 0"
            proof (cases "i \<ge> 2")
              case True thus ?thesis using hzero2 \<open>i \<le> n\<close> by (by100 blast)
            next
              case False hence "i = 1" using \<open>i \<ge> 1\<close> by (by100 linarith)
              thus ?thesis using \<open>z 1 = 0\<close> by (by100 simp)
            qed
          qed
          hence hzi0: "\<And>i. i \<ge> 1 \<Longrightarrow> i \<le> n \<Longrightarrow> z i = 0" by (by100 simp)
          have hz_above: "\<And>i. i \<ge> Suc n \<Longrightarrow> z i = 0"
            using hz_Sn unfolding top1_Sn_def by (by100 blast)
          have hzi0_all: "\<And>i. i \<ge> 1 \<Longrightarrow> z i = 0"
          proof -
            fix i :: nat assume "i \<ge> 1"
            show "z i = 0"
            proof (cases "i \<le> n")
              case True thus ?thesis using hzi0 \<open>i \<ge> 1\<close> by (by100 blast)
            next
              case False hence "i \<ge> Suc n" by (by100 linarith)
              thus ?thesis using hz_above by (by100 blast)
            qed
          qed
          \<comment> \<open>z(0)^2 = 1 since other coords = 0.\<close>
          have hz_Sn_norm: "(\<Sum>j\<le>n. (z j)^2) = 1" using hz_Sn unfolding top1_Sn_def by (by100 blast)
          have hz0_sq: "z 0 ^ 2 = 1"
          proof -
            have "(\<Sum>j\<le>n. (z j)^2) = (\<Sum>j\<in>{0..n}. (z j)^2)"
              using atLeast0AtMost by (by100 metis)
            also have "\<dots> = (z 0)^2 + (\<Sum>j\<in>{1..n}. (z j)^2)"
            proof -
              have "0 \<le> n" using assms by (by100 linarith)
              thus ?thesis using sum.atLeast_Suc_atMost[of 0 n "\<lambda>j. (z j)^2"] by (by100 simp)
            qed
            also have "(\<Sum>j\<in>{1..n}. (z j)^2) = (\<Sum>j\<in>{1..n}. (0::real))"
            proof (intro sum.cong)
              fix j assume "j \<in> {1..n}"
              hence "j \<ge> 1" by (by100 simp)
              hence "z j = 0" using hzi0_all by (by100 blast)
              thus "(z j)^2 = (0::real)" by (by100 simp)
            qed (by100 simp)
            also have "\<dots> = 0" by (by100 simp)
            finally show ?thesis using hz_Sn_norm by (by100 linarith)
          qed
          have "(\<bar>z 0\<bar>)^2 = (1::real)^2" using hz0_sq power2_abs[of "z 0"] by (by100 simp)
          hence "\<bar>z 0\<bar> = (1::real)" by (rule power2_eq_imp_eq) (by100 simp)+
          hence "z 0 = 1 \<or> z 0 = -1" by (by100 linarith)
          thus False
          proof
            assume hz01: "z 0 = 1"
            have "\<And>i. z i = ?p i"
            proof -
              fix i show "z i = ?p i"
                using hz01 hzi0_all[of i] by (cases "i = 0") (by100 simp)+
            qed
            hence "z = ?p" by (rule ext)
            thus False using hz_np by (by100 blast)
          next
            assume hz0m1: "z 0 = -1"
            have "\<And>i. z i = ?q i"
            proof -
              fix i show "z i = ?q i"
                using hz0m1 hzi0_all[of i] by (cases "i = 0") (by100 simp)+
            qed
            hence "z = ?q" by (rule ext)
            thus False using hz_nq by (by100 blast)
          qed
        qed
        \<comment> \<open>Use r' = e_2 as stepping stone. z \<rightarrow> r' \<rightarrow> r.\<close>
        let ?r' = "\<lambda>i::nat. if i = 2 then (1::real) else 0"
        have hr'_Sn: "?r' \<in> ?Sn" unfolding top1_Sn_def
        proof (intro CollectI conjI allI impI)
          fix i :: nat assume "i \<ge> Suc n" hence "i \<noteq> 2" using assms by (by100 linarith)
          thus "?r' i = 0" by (by100 simp)
        next
          have h2n: "(2::nat) \<le> n" using assms by (by100 linarith)
          have "(\<Sum>i\<le>n. (?r' i)\<^sup>2) = (\<Sum>i\<le>n. (if i = 2 then 1 else 0::real))"
            by (intro sum.cong) (by100 simp)+
          also have "\<dots> = 1" using sum.delta'[of "{..n}" 2 "\<lambda>_. (1::real)"] h2n by (by100 simp)
          finally show "(\<Sum>i\<le>n. (?r' i)\<^sup>2) = 1" .
        qed
        have hr'_UV: "?r' \<in> ?U \<inter> ?V"
        proof -
          have "?r' \<noteq> ?p"
          proof assume h: "?r' = ?p"
            have "?r' 0 = (0::real)" by (by100 simp)
            moreover have "?p 0 = (1::real)" by (by100 simp)
            ultimately show False using h fun_cong[OF h, of 0] by (by100 simp) qed
          moreover have "?r' \<noteq> ?q"
          proof assume h: "?r' = ?q"
            have "?r' 0 = (0::real)" by (by100 simp)
            moreover have "?q 0 = (-1::real)" by (by100 simp)
            ultimately show False using fun_cong[OF h, of 0] by (by100 simp) qed
          ultimately show ?thesis using hr'_Sn by (by100 blast)
        qed
        \<comment> \<open>z \<noteq> -r' since z(1) \<noteq> 0 but (-r')(1) = 0.\<close>
        have hz_na_r': "z \<noteq> (\<lambda>i. - ?r' i)"
        proof
          assume "z = (\<lambda>i. - ?r' i)"
          hence "z 1 = - ?r' 1" using fun_cong[of z "\<lambda>i. - ?r' i" 1] by (by100 simp)
          hence "z 1 = 0" by (by100 simp)
          thus False using hz1_ne by (by100 blast)
        qed
        \<comment> \<open>r \<noteq> -r' since r(1) = 1 but (-r')(1) = 0.\<close>
        have hr_na_r': "?r \<noteq> (\<lambda>i. - ?r' i)"
        proof
          assume h: "?r = (\<lambda>i. - ?r' i)"
          have "?r 1 = (1::real)" by (by100 simp)
          moreover have "(\<lambda>i. - ?r' i) 1 = (0::real)" by (by100 simp)
          ultimately have "(1::real) = (0::real)" using fun_cong[OF h, of 1] by (by100 simp)
          thus False by (by100 simp)
        qed
        \<comment> \<open>Path z \<rightarrow> r' in U \<inter> V: interpolation avoids p,q since z(1) \<noteq> 0.\<close>
        let ?\<gamma>1 = "\<lambda>t i. ((1-t) * z i + t * ?r' i) / sqrt (\<Sum>j\<le>n. ((1-t) * z j + t * ?r' j)^2)"
        have hpath1: "top1_is_path_on ?Sn ?TSn z ?r' ?\<gamma>1"
          by (rule Sn_normalized_interpolation_path[OF hz_Sn hr'_Sn hz_na_r'])
        have havoids1: "\<forall>t. ?\<gamma>1 t \<in> ?U \<inter> ?V"
        proof (intro allI)
          fix t
          have h_Sn: "?\<gamma>1 t \<in> ?Sn" by (rule Sn_interpolation_in_Sn[OF hz_Sn hr'_Sn hz_na_r'])
          have h_np: "?\<gamma>1 t \<noteq> ?p"
          proof assume heq: "?\<gamma>1 t = ?p"
            have hN: "sqrt (\<Sum>j\<le>n. ((1-t) * z j + t * ?r' j)^2) > 0"
              by (rule Sn_interpolation_norm_pos[OF hz_Sn hr'_Sn hz_na_r'])
            have "?\<gamma>1 t 1 = ?p 1" using fun_cong[OF heq, of 1] by (by100 simp)
            hence "((1-t) * z 1 + t * ?r' 1) / sqrt (\<Sum>j\<le>n. ((1-t) * z j + t * ?r' j)^2) = 0"
              by (by100 simp)
            hence "(1-t) * z 1 = 0" using hN by (by100 simp)
            hence "t = 1" using hz1_ne using mult_eq_0_iff by (by100 simp)
            hence "?\<gamma>1 t = ?r'" using Sn_interpolation_at_1[OF hz_Sn hr'_Sn hz_na_r'] by (by100 simp)
            hence h_eq: "?p = ?r'" using heq by (by100 simp)
            have "?p 0 = (1::real)" by (by100 simp)
            moreover have "?r' 0 = (0::real)" by (by100 simp)
            ultimately have "(1::real) = (0::real)" using fun_cong[OF h_eq, of 0] by (by100 simp)
            thus False by (by100 simp)
          qed
          have h_nq: "?\<gamma>1 t \<noteq> ?q"
          proof assume heq: "?\<gamma>1 t = ?q"
            have hN: "sqrt (\<Sum>j\<le>n. ((1-t) * z j + t * ?r' j)^2) > 0"
              by (rule Sn_interpolation_norm_pos[OF hz_Sn hr'_Sn hz_na_r'])
            have "?\<gamma>1 t 1 = ?q 1" using fun_cong[OF heq, of 1] by (by100 simp)
            hence "((1-t) * z 1 + t * ?r' 1) / sqrt (\<Sum>j\<le>n. ((1-t) * z j + t * ?r' j)^2) = 0"
              by (by100 simp)
            hence "(1-t) * z 1 = 0" using hN by (by100 simp)
            hence "t = 1" using hz1_ne using mult_eq_0_iff by (by100 simp)
            hence "?\<gamma>1 t = ?r'" using Sn_interpolation_at_1[OF hz_Sn hr'_Sn hz_na_r'] by (by100 simp)
            hence h_eq: "?q = ?r'" using heq by (by100 simp)
            have "?q 0 = (-1::real)" by (by100 simp)
            moreover have "?r' 0 = (0::real)" by (by100 simp)
            ultimately have "(-1::real) = (0::real)" using fun_cong[OF h_eq, of 0] by (by100 simp)
            thus False by (by100 simp)
          qed
          show "?\<gamma>1 t \<in> ?U \<inter> ?V" using h_Sn h_np h_nq by (by100 blast)
        qed
        \<comment> \<open>Path r' \<rightarrow> r in U \<inter> V: interpolation avoids p,q since r'(2) \<noteq> 0.\<close>
        let ?\<gamma>2 = "\<lambda>t i. ((1-t) * ?r' i + t * ?r i) / sqrt (\<Sum>j\<le>n. ((1-t) * ?r' j + t * ?r j)^2)"
        have hr'_na_r: "?r' \<noteq> (\<lambda>i. - ?r i)"
        proof assume h: "?r' = (\<lambda>i. - ?r i)"
          have "?r' 2 = (1::real)" by (by100 simp)
          moreover have "(\<lambda>i. - ?r i) 2 = (0::real)" by (by100 simp)
          ultimately show False using fun_cong[OF h, of 2] by (by100 simp)
        qed
        have hpath2: "top1_is_path_on ?Sn ?TSn ?r' ?r ?\<gamma>2"
          by (rule Sn_normalized_interpolation_path[OF hr'_Sn hr_Sn hr'_na_r])
        have havoids2: "\<forall>t. ?\<gamma>2 t \<in> ?U \<inter> ?V"
        proof (intro allI)
          fix t
          have h_Sn: "?\<gamma>2 t \<in> ?Sn" by (rule Sn_interpolation_in_Sn[OF hr'_Sn hr_Sn hr'_na_r])
          have hr'2: "?r' 2 \<noteq> (0::real)" by (by100 simp)
          have h_np: "?\<gamma>2 t \<noteq> ?p"
          proof assume heq: "?\<gamma>2 t = ?p"
            have hN: "sqrt (\<Sum>j\<le>n. ((1-t) * ?r' j + t * ?r j)^2) > 0"
              by (rule Sn_interpolation_norm_pos[OF hr'_Sn hr_Sn hr'_na_r])
            have "?\<gamma>2 t 2 = ?p 2" using fun_cong[OF heq, of 2] by (by100 simp)
            hence "((1-t) * ?r' 2 + t * ?r 2) / sqrt (\<Sum>j\<le>n. ((1-t) * ?r' j + t * ?r j)^2) = 0"
              by (by100 simp)
            hence "(1-t) * ?r' 2 + t * ?r 2 = 0" using hN by (by100 simp)
            hence "(1-t) = 0" by (by100 simp)
            hence "t = 1" by (by100 linarith)
            hence "?\<gamma>2 t = ?r" using Sn_interpolation_at_1[OF hr'_Sn hr_Sn hr'_na_r] by (by100 simp)
            thus False using heq hr_ne_p by (by100 simp)
          qed
          have h_nq: "?\<gamma>2 t \<noteq> ?q"
          proof assume heq: "?\<gamma>2 t = ?q"
            have hN: "sqrt (\<Sum>j\<le>n. ((1-t) * ?r' j + t * ?r j)^2) > 0"
              by (rule Sn_interpolation_norm_pos[OF hr'_Sn hr_Sn hr'_na_r])
            have "?\<gamma>2 t 2 = ?q 2" using fun_cong[OF heq, of 2] by (by100 simp)
            hence "((1-t) * ?r' 2 + t * ?r 2) / sqrt (\<Sum>j\<le>n. ((1-t) * ?r' j + t * ?r j)^2) = 0"
              by (by100 simp)
            hence "(1-t) = 0" using hN by (by100 simp)
            hence "t = 1" by (by100 linarith)
            hence "?\<gamma>2 t = ?r" using Sn_interpolation_at_1[OF hr'_Sn hr_Sn hr'_na_r] by (by100 simp)
            thus False using heq hr_ne_q by (by100 simp)
          qed
          show "?\<gamma>2 t \<in> ?U \<inter> ?V" using h_Sn h_np h_nq by (by100 blast)
        qed
        \<comment> \<open>Chain z \<rightarrow> r' \<rightarrow> r via codomain_shrink + path_product.\<close>
        have h1_cont: "top1_continuous_map_on I_set I_top ?Sn ?TSn ?\<gamma>1"
          using hpath1 unfolding top1_is_path_on_def by (by100 blast)
        have h1_img: "?\<gamma>1 ` I_set \<subseteq> ?U \<inter> ?V"
        proof (intro subsetI)
          fix w assume "w \<in> ?\<gamma>1 ` I_set"
          then obtain t where "w = ?\<gamma>1 t" by (by100 blast)
          thus "w \<in> ?U \<inter> ?V" using havoids1 by (by100 simp)
        qed
        have h1_UV: "top1_is_path_on (?U \<inter> ?V) (subspace_topology ?Sn ?TSn (?U \<inter> ?V)) z ?r' ?\<gamma>1"
          unfolding top1_is_path_on_def
          using top1_continuous_map_on_codomain_shrink[OF h1_cont h1_img hUV_sub]
          hpath1[unfolded top1_is_path_on_def] by (by100 blast)
        have h2_cont: "top1_continuous_map_on I_set I_top ?Sn ?TSn ?\<gamma>2"
          using hpath2 unfolding top1_is_path_on_def by (by100 blast)
        have h2_img: "?\<gamma>2 ` I_set \<subseteq> ?U \<inter> ?V"
        proof (intro subsetI)
          fix w assume "w \<in> ?\<gamma>2 ` I_set"
          then obtain t where "w = ?\<gamma>2 t" by (by100 blast)
          thus "w \<in> ?U \<inter> ?V" using havoids2 by (by100 simp)
        qed
        have h2_UV: "top1_is_path_on (?U \<inter> ?V) (subspace_topology ?Sn ?TSn (?U \<inter> ?V)) ?r' ?r ?\<gamma>2"
          unfolding top1_is_path_on_def
          using top1_continuous_map_on_codomain_shrink[OF h2_cont h2_img hUV_sub]
          hpath2[unfolded top1_is_path_on_def] by (by100 blast)
        have "top1_is_path_on (?U \<inter> ?V) (subspace_topology ?Sn ?TSn (?U \<inter> ?V)) z ?r
            (top1_path_product ?\<gamma>1 ?\<gamma>2)"
          by (rule top1_path_product_is_path[OF hTUV h1_UV h2_UV])
        thus ?thesis by (by100 blast)
      qed
    qed
    then obtain fx where hfx: "top1_is_path_on (?U \<inter> ?V) (subspace_topology ?Sn ?TSn (?U \<inter> ?V)) x ?r fx"
      using hpath_to_r[OF hx] by (by100 blast)
    obtain fy where hfy: "top1_is_path_on (?U \<inter> ?V) (subspace_topology ?Sn ?TSn (?U \<inter> ?V)) y ?r fy"
      using hpath_to_r[OF hy] by (by100 blast)
    have hrev_fy: "top1_is_path_on (?U \<inter> ?V) (subspace_topology ?Sn ?TSn (?U \<inter> ?V)) ?r y
        (top1_path_reverse fy)"
      by (rule top1_path_reverse_is_path[OF hfy])
    show "\<exists>f. top1_is_path_on (?U \<inter> ?V) (subspace_topology ?Sn ?TSn (?U \<inter> ?V)) x y f"
      using top1_path_product_is_path[OF hTUV hfx hrev_fy] by (by100 blast)
  qed
  have hT_strict: "is_topology_on_strict ?Sn ?TSn"
    unfolding is_topology_on_strict_def
    using hTSn_top
  proof (intro conjI)
    show "?TSn \<subseteq> Pow ?Sn"
      unfolding subspace_topology_def by (by100 blast)
  qed simp
  \<comment> \<open>Apply Corollary 59.2.\<close>
  show ?thesis
    using Corollary_59_2[OF hT_strict hU_open hV_open hUV hUV_ne hUV_pc hU_sc hV_sc] by (by100 blast)
qed





















corollary Theorem_59_3_path_connected:
  assumes "n \<ge> 2"
  shows "top1_path_connected_on (top1_Sn n)
    (subspace_topology UNIV
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))
      (top1_Sn n))"
  using Theorem_59_3[OF assms] top1_simply_connected_on_path_connected by blast

section \<open>\<S>60 Fundamental Groups of Some Surfaces\<close>

(** from \<S>60 Theorem 60.1: \<pi>_1(X \<times> Y, (x_0, y_0)) \<cong> \<pi>_1(X, x_0) \<times> \<pi>_1(Y, y_0).
    The iso is given by the product map induced by the two projections. **)
theorem Theorem_60_1_product:
  assumes "is_topology_on_strict X TX" and "is_topology_on_strict Y TY"
      and "x0 \<in> X" and "y0 \<in> Y"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier (X \<times> Y) (product_topology_on TX TY) (x0, y0))
           (top1_fundamental_group_mul (X \<times> Y) (product_topology_on TX TY) (x0, y0))
           ((top1_fundamental_group_carrier X TX x0) \<times>
            (top1_fundamental_group_carrier Y TY y0))
           (\<lambda>(c1, c2) (d1, d2).
              (top1_fundamental_group_mul X TX x0 c1 d1,
               top1_fundamental_group_mul Y TY y0 c2 d2))"
  \<comment> \<open>Munkres 60.1: \<Phi>([f]) = (p_*([f]), q_*([f])) = ([p\<circ>f], [q\<circ>f]) where p,q are projections.\<close>
proof -
  let ?TXY = "product_topology_on TX TY"
  let ?\<Phi> = "\<lambda>c. (top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst c,
                  top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd c)"
  \<comment> \<open>Step 1: \<Phi> is well-defined and a homomorphism.\<close>
  have hTX: "is_topology_on X TX" by (rule is_topology_on_strict_imp[OF assms(1)])
  have hTY: "is_topology_on Y TY" by (rule is_topology_on_strict_imp[OF assms(2)])
  have hpi1_eq: "(pi1 :: ('a \<times> 'b) \<Rightarrow> 'a) = fst" unfolding pi1_def by (rule ext) simp
  have hpi2_eq: "(pi2 :: ('a \<times> 'b) \<Rightarrow> 'b) = snd" unfolding pi2_def by (rule ext) simp
  have hfst_cont: "top1_continuous_map_on (X \<times> Y) ?TXY X TX fst"
    using top1_continuous_pi1[OF hTX hTY] unfolding hpi1_eq .
  have hsnd_cont: "top1_continuous_map_on (X \<times> Y) ?TXY Y TY snd"
    using top1_continuous_pi2[OF hTX hTY] unfolding hpi2_eq .
  \<comment> \<open>Key fact: h \<circ> (path_product f g) = path_product (h\<circ>f) (h\<circ>g) for any h.\<close>
  have hcomp_prod: "\<And>h f g. h \<circ> (top1_path_product f g) = top1_path_product (h \<circ> f) (h \<circ> g)"
    unfolding top1_path_product_def comp_def by (rule ext) auto
  have hTXY: "is_topology_on (X \<times> Y) ?TXY"
    by (rule product_topology_on_is_topology_on[OF hTX hTY])
  \<comment> \<open>Helper: induced map on fundamental group commutes with mul.
     Uses hcomp_prod + top1_fundamental_group_mul_class + continuous_preserves_path_homotopic.\<close>
  have h\<Phi>_hom: "\<forall>c \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0).
      \<forall>d \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0).
      ?\<Phi> (top1_fundamental_group_mul (X \<times> Y) ?TXY (x0, y0) c d)
      = (\<lambda>(c1, c2) (d1, d2). (top1_fundamental_group_mul X TX x0 c1 d1,
           top1_fundamental_group_mul Y TY y0 c2 d2)) (?\<Phi> c) (?\<Phi> d)"
  proof (intro ballI)
    fix c d assume hc: "c \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
        and hd: "d \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
    obtain f where hf_loop: "top1_is_loop_on (X \<times> Y) ?TXY (x0, y0) f"
        and hc_eq: "c = {k. top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) f k}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 auto)
    obtain g where hg_loop: "top1_is_loop_on (X \<times> Y) ?TXY (x0, y0) g"
        and hd_eq: "d = {k. top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) g k}"
      using hd unfolding top1_fundamental_group_carrier_def by (by100 auto)
    have hfst_hom: "top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst
        (top1_fundamental_group_mul (X \<times> Y) ?TXY (x0, y0) c d)
      = top1_fundamental_group_mul X TX x0
          (top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst c)
          (top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst d)"
      unfolding hc_eq hd_eq by (rule induced_hom_mul[OF hTXY hTX hfst_cont _ hf_loop hg_loop]) (by100 simp)
    have hsnd_hom: "top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd
        (top1_fundamental_group_mul (X \<times> Y) ?TXY (x0, y0) c d)
      = top1_fundamental_group_mul Y TY y0
          (top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd c)
          (top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd d)"
      unfolding hc_eq hd_eq by (rule induced_hom_mul[OF hTXY hTY hsnd_cont _ hf_loop hg_loop]) (by100 simp)
    show "?\<Phi> (top1_fundamental_group_mul (X \<times> Y) ?TXY (x0, y0) c d)
      = (\<lambda>(c1, c2) (d1, d2). (top1_fundamental_group_mul X TX x0 c1 d1,
           top1_fundamental_group_mul Y TY y0 c2 d2)) (?\<Phi> c) (?\<Phi> d)"
      using hfst_hom hsnd_hom by (cases "?\<Phi> c", cases "?\<Phi> d") (by100 auto)
  qed
  \<comment> \<open>Step 2: Injectivity. If p\<circ>f \<simeq> const and q\<circ>f \<simeq> const, combine homotopies componentwise.\<close>
  have h\<Phi>_inj: "inj_on ?\<Phi> (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))"
  proof (rule inj_onI)
    fix c d assume hc: "c \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
        and hd: "d \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
        and heq: "?\<Phi> c = ?\<Phi> d"
    obtain f where hf_loop: "top1_is_loop_on (X \<times> Y) ?TXY (x0, y0) f"
        and hc_eq: "c = {k. top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) f k}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 auto)
    obtain g where hg_loop: "top1_is_loop_on (X \<times> Y) ?TXY (x0, y0) g"
        and hd_eq: "d = {k. top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) g k}"
      using hd unfolding top1_fundamental_group_carrier_def by (by100 auto)
    \<comment> \<open>Extract: fst\<circ>f path-homotopic to fst\<circ>g (from equal equiv classes).\<close>
    have hf_in_c: "f \<in> c" using hc_eq top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
    have hg_in_d: "g \<in> d" using hd_eq top1_loop_equiv_on_refl[OF hg_loop] by (by100 blast)
    have hf_cont: "top1_continuous_map_on I_set I_top (X \<times> Y) ?TXY f"
      using hf_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hg_cont: "top1_continuous_map_on I_set I_top (X \<times> Y) ?TXY g"
      using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hf0: "f 0 = (x0, y0)" "f 1 = (x0, y0)"
      using hf_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
    have hg0: "g 0 = (x0, y0)" "g 1 = (x0, y0)"
      using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
    \<comment> \<open>From \<Phi>(c)=\<Phi>(d): induced_fst([f]) = induced_fst([g]).\<close>
    have heq_fst: "top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst c
        = top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst d"
      using heq by (by100 simp)
    have heq_snd: "top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd c
        = top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd d"
      using heq by (by100 simp)
    \<comment> \<open>fst\<circ>f \<in> induced_fst(c) = induced_fst(d). Extract j \<in> d with equiv(fst\<circ>j, fst\<circ>f).
       Then fst\<circ>g \<simeq> fst\<circ>j \<simeq> fst\<circ>f, hence fst\<circ>f \<simeq> fst\<circ>g by sym.\<close>
    have hfstf_loop: "top1_is_loop_on X TX x0 (fst \<circ> f)"
      unfolding top1_is_loop_on_def top1_is_path_on_def comp_def
      using top1_continuous_map_on_comp[OF hf_cont hfst_cont] hf0 unfolding comp_def by (by100 simp)
    have hfstf_in: "fst \<circ> f \<in> top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst d"
      using heq_fst[symmetric]
      unfolding top1_fundamental_group_induced_on_def
      using hf_in_c top1_loop_equiv_on_refl[OF hfstf_loop] by (by100 blast)
    then obtain j where hj_d: "j \<in> d" and hfstj_fstf: "top1_loop_equiv_on X TX x0 (fst \<circ> j) (fst \<circ> f)"
      unfolding top1_fundamental_group_induced_on_def by (by100 blast)
    have hgj_ph: "top1_path_homotopic_on (X \<times> Y) ?TXY (x0, y0) (x0, y0) g j"
      using hj_d hd_eq unfolding top1_loop_equiv_on_def by (by100 blast)
    have hfstg_fstj: "top1_path_homotopic_on X TX x0 x0 (fst \<circ> g) (fst \<circ> j)"
      using continuous_preserves_path_homotopic[OF hTXY hTX hfst_cont hgj_ph] by (by100 simp)
    have hfstj_fstf_ph: "top1_path_homotopic_on X TX x0 x0 (fst \<circ> j) (fst \<circ> f)"
      using hfstj_fstf unfolding top1_loop_equiv_on_def by (by100 blast)
    have hfstf_equiv_fstg: "top1_path_homotopic_on X TX x0 x0 (fst \<circ> f) (fst \<circ> g)"
      by (rule Lemma_51_1_path_homotopic_sym[OF
            Lemma_51_1_path_homotopic_trans[OF hTX hfstg_fstj hfstj_fstf_ph]])
    \<comment> \<open>Same for snd.\<close>
    have hsndf_loop: "top1_is_loop_on Y TY y0 (snd \<circ> f)"
      unfolding top1_is_loop_on_def top1_is_path_on_def comp_def
      using top1_continuous_map_on_comp[OF hf_cont hsnd_cont] hf0 unfolding comp_def by (by100 simp)
    have hsndf_in: "snd \<circ> f \<in> top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd d"
      using heq_snd[symmetric]
      unfolding top1_fundamental_group_induced_on_def
      using hf_in_c top1_loop_equiv_on_refl[OF hsndf_loop] by (by100 blast)
    then obtain j2 where hj2_d: "j2 \<in> d" and hsndj2_sndf: "top1_loop_equiv_on Y TY y0 (snd \<circ> j2) (snd \<circ> f)"
      unfolding top1_fundamental_group_induced_on_def by (by100 blast)
    have hgj2_ph: "top1_path_homotopic_on (X \<times> Y) ?TXY (x0, y0) (x0, y0) g j2"
      using hj2_d hd_eq unfolding top1_loop_equiv_on_def by (by100 blast)
    have hsndg_sndj2: "top1_path_homotopic_on Y TY y0 y0 (snd \<circ> g) (snd \<circ> j2)"
      using continuous_preserves_path_homotopic[OF hTXY hTY hsnd_cont hgj2_ph] by (by100 simp)
    have hsndj2_sndf_ph: "top1_path_homotopic_on Y TY y0 y0 (snd \<circ> j2) (snd \<circ> f)"
      using hsndj2_sndf unfolding top1_loop_equiv_on_def by (by100 blast)
    have hsndf_equiv_sndg: "top1_path_homotopic_on Y TY y0 y0 (snd \<circ> f) (snd \<circ> g)"
      by (rule Lemma_51_1_path_homotopic_sym[OF
            Lemma_51_1_path_homotopic_trans[OF hTY hsndg_sndj2 hsndj2_sndf_ph]])
    \<comment> \<open>Combine componentwise: f \<simeq> g in X\<times>Y.\<close>
    have hfg_hom: "top1_path_homotopic_on (X \<times> Y) ?TXY (x0, y0) (x0, y0) f g"
    proof -
      \<comment> \<open>Extract homotopies F1, F2 from the path homotopies.\<close>
      have hfst_ph: "\<exists>F1. top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F1
          \<and> (\<forall>s\<in>I_set. F1 (s, 0) = (fst \<circ> f) s) \<and> (\<forall>s\<in>I_set. F1 (s, 1) = (fst \<circ> g) s)
          \<and> (\<forall>t\<in>I_set. F1 (0, t) = x0) \<and> (\<forall>t\<in>I_set. F1 (1, t) = x0)"
        using hfstf_equiv_fstg unfolding top1_path_homotopic_on_def by (by100 fast)
      obtain F1 where hF1cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F1"
          and hF10: "\<forall>s\<in>I_set. F1 (s, 0) = (fst \<circ> f) s" and hF11: "\<forall>s\<in>I_set. F1 (s, 1) = (fst \<circ> g) s"
          and hF1l: "\<forall>t\<in>I_set. F1 (0, t) = x0" and hF1r: "\<forall>t\<in>I_set. F1 (1, t) = x0"
        using hfst_ph by (by100 auto)
      have hsnd_ph: "\<exists>F2. top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY F2
          \<and> (\<forall>s\<in>I_set. F2 (s, 0) = (snd \<circ> f) s) \<and> (\<forall>s\<in>I_set. F2 (s, 1) = (snd \<circ> g) s)
          \<and> (\<forall>t\<in>I_set. F2 (0, t) = y0) \<and> (\<forall>t\<in>I_set. F2 (1, t) = y0)"
        using hsndf_equiv_sndg unfolding top1_path_homotopic_on_def by (by100 fast)
      obtain F2 where hF2cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY F2"
          and hF20: "\<forall>s\<in>I_set. F2 (s, 0) = (snd \<circ> f) s" and hF21: "\<forall>s\<in>I_set. F2 (s, 1) = (snd \<circ> g) s"
          and hF2l: "\<forall>t\<in>I_set. F2 (0, t) = y0" and hF2r: "\<forall>t\<in>I_set. F2 (1, t) = y0"
        using hsnd_ph by (by100 auto)
      let ?F = "\<lambda>st. (F1 st, F2 st)"
      have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
        unfolding II_topology_def by (rule product_topology_on_is_topology_on)
          (rule top1_unit_interval_topology_is_topology_on)+
      have hpi1_F: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (pi1 \<circ> ?F)"
        using hF1cont unfolding pi1_def comp_def by (by100 simp)
      have hpi2_F: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY (pi2 \<circ> ?F)"
        using hF2cont unfolding pi2_def comp_def by (by100 simp)
      have hFcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology (X \<times> Y) ?TXY ?F"
        using iffD2[OF Theorem_18_4[OF hTII hTX hTY]] hpi1_F hpi2_F by (by100 blast)
      show ?thesis unfolding top1_path_homotopic_on_def
      proof (intro conjI exI)
        show "top1_is_path_on (X \<times> Y) ?TXY (x0, y0) (x0, y0) f"
          using hf_loop unfolding top1_is_loop_on_def by (by100 blast)
        show "top1_is_path_on (X \<times> Y) ?TXY (x0, y0) (x0, y0) g"
          using hg_loop unfolding top1_is_loop_on_def by (by100 blast)
        show "top1_continuous_map_on (I_set \<times> I_set) II_topology (X \<times> Y) ?TXY ?F" by (rule hFcont)
        show "\<forall>s\<in>I_set. ?F (s, 0) = f s"
        proof (intro ballI)
          fix s assume hs: "s \<in> I_set"
          have "?F (s, 0) = ((fst \<circ> f) s, (snd \<circ> f) s)" using hF10 hF20 hs by (by100 simp)
          also have "\<dots> = (fst (f s), snd (f s))" unfolding comp_def by (by100 simp)
          also have "\<dots> = f s" by (by100 simp)
          finally show "?F (s, 0) = f s" .
        qed
        show "\<forall>s\<in>I_set. ?F (s, 1) = g s"
        proof (intro ballI)
          fix s assume hs: "s \<in> I_set"
          have "?F (s, 1) = ((fst \<circ> g) s, (snd \<circ> g) s)" using hF11 hF21 hs by (by100 simp)
          also have "\<dots> = (fst (g s), snd (g s))" unfolding comp_def by (by100 simp)
          also have "\<dots> = g s" by (by100 simp)
          finally show "?F (s, 1) = g s" .
        qed
        show "\<forall>t\<in>I_set. ?F (0, t) = (x0, y0)" using hF1l hF2l by (by100 simp)
        show "\<forall>t\<in>I_set. ?F (1, t) = (x0, y0)" using hF1r hF2r by (by100 simp)
      qed
    qed
    hence "top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) f g"
      unfolding top1_loop_equiv_on_def using hf_loop hg_loop by (by100 blast)
    hence hfg_equiv: "top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) f g"
      unfolding top1_loop_equiv_on_def using hf_loop hg_loop by (by100 blast)
    have hgf_equiv: "top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) g f"
      by (rule top1_loop_equiv_on_sym[OF hfg_equiv])
    show "c = d" unfolding hc_eq hd_eq
    proof (intro set_eqI iffI)
      fix k assume "k \<in> {k. top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) f k}"
      hence "top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) f k" by (by100 blast)
      thus "k \<in> {k. top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) g k}"
        using hgf_equiv top1_loop_equiv_on_trans[OF hTXY] by (by100 blast)
    next
      fix k assume "k \<in> {k. top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) g k}"
      hence "top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) g k" by (by100 blast)
      thus "k \<in> {k. top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) f k}"
        using hfg_equiv top1_loop_equiv_on_trans[OF hTXY] by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 3: Surjectivity. Given [g] \<in> \<pi>_1(X) and [h] \<in> \<pi>_1(Y), define f(s) = (g(s), h(s)).\<close>
  have h\<Phi>_surj: "?\<Phi> ` (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))
      = (top1_fundamental_group_carrier X TX x0) \<times>
        (top1_fundamental_group_carrier Y TY y0)"
  proof (intro set_eqI iffI)
    fix z assume "z \<in> ?\<Phi> ` (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))"
    then obtain c where hc: "c \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
        and hzc: "z = ?\<Phi> c" by (by100 blast)
    \<comment> \<open>c = [f] for some loop f at (x0,y0). Then \<Phi>(c) = ([fst\<circ>f], [snd\<circ>f]).\<close>
    \<comment> \<open>[fst\<circ>f] \<in> carrier_X and [snd\<circ>f] \<in> carrier_Y.\<close>
    obtain f where hf_loop: "top1_is_loop_on (X \<times> Y) ?TXY (x0, y0) f"
        and hc_eq: "c = {k. top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) f k}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 auto)
    have hf_cont: "top1_continuous_map_on I_set I_top (X \<times> Y) ?TXY f"
      using hf_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hf0: "f 0 = (x0, y0)" "f 1 = (x0, y0)"
      using hf_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
    have hfstf_loop: "top1_is_loop_on X TX x0 (fst \<circ> f)"
      unfolding top1_is_loop_on_def top1_is_path_on_def comp_def
      using top1_continuous_map_on_comp[OF hf_cont hfst_cont] hf0 unfolding comp_def
      by (by100 simp)
    have hsndf_loop: "top1_is_loop_on Y TY y0 (snd \<circ> f)"
      unfolding top1_is_loop_on_def top1_is_path_on_def comp_def
      using top1_continuous_map_on_comp[OF hf_cont hsnd_cont] hf0 unfolding comp_def
      by (by100 simp)
    \<comment> \<open>induced([f]) = [fst\<circ>f] \<in> carrier_X, induced([f]) = [snd\<circ>f] \<in> carrier_Y.\<close>
    \<comment> \<open>By the hind_gen pattern: induced([f]) = {k. loop_equiv(fst\<circ>f, k)}.\<close>
    have hind_eq_fst: "top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst c
        = {k. top1_loop_equiv_on X TX x0 (fst \<circ> f) k}"
    proof (intro set_eqI iffI)
      fix k assume "k \<in> top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst c"
      then obtain j where hj_in: "j \<in> c" and hk: "top1_loop_equiv_on X TX x0 (fst \<circ> j) k"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      have hfj: "top1_path_homotopic_on (X \<times> Y) ?TXY (x0, y0) (x0, y0) f j"
        using hj_in hc_eq unfolding top1_loop_equiv_on_def by (by100 blast)
      have hph: "top1_path_homotopic_on X TX x0 x0 (fst \<circ> f) (fst \<circ> j)"
        using continuous_preserves_path_homotopic[OF hTXY hTX hfst_cont hfj] by (by100 simp)
      have hj_loop: "top1_is_loop_on (X \<times> Y) ?TXY (x0, y0) j"
        using hj_in hc_eq unfolding top1_loop_equiv_on_def by (by100 blast)
      have hj_cont: "top1_continuous_map_on I_set I_top (X \<times> Y) ?TXY j"
        using hj_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      have hj0: "j 0 = (x0, y0)" "j 1 = (x0, y0)"
        using hj_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
      have hfstj_loop: "top1_is_loop_on X TX x0 (fst \<circ> j)"
        unfolding top1_is_loop_on_def top1_is_path_on_def comp_def
        using top1_continuous_map_on_comp[OF hj_cont hfst_cont] hj0 unfolding comp_def by (by100 simp)
      have "top1_loop_equiv_on X TX x0 (fst \<circ> f) (fst \<circ> j)"
        unfolding top1_loop_equiv_on_def using hfstf_loop hfstj_loop hph by (by100 blast)
      thus "k \<in> {k. top1_loop_equiv_on X TX x0 (fst \<circ> f) k}"
        using hk top1_loop_equiv_on_trans[OF hTX] by (by100 blast)
    next
      fix k assume "k \<in> {k. top1_loop_equiv_on X TX x0 (fst \<circ> f) k}"
      hence hk: "top1_loop_equiv_on X TX x0 (fst \<circ> f) k" by (by100 blast)
      have "f \<in> c" using hc_eq top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
      thus "k \<in> top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst c"
        unfolding top1_fundamental_group_induced_on_def using hk by (by100 blast)
    qed
    have hfst_in: "top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst c
        \<in> top1_fundamental_group_carrier X TX x0"
      unfolding hind_eq_fst top1_fundamental_group_carrier_def using hfstf_loop by (by100 blast)
    have hind_eq_snd: "top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd c
        = {k. top1_loop_equiv_on Y TY y0 (snd \<circ> f) k}"
    proof (intro set_eqI iffI)
      fix k assume "k \<in> top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd c"
      then obtain j where hj_in: "j \<in> c" and hk: "top1_loop_equiv_on Y TY y0 (snd \<circ> j) k"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      have hfj: "top1_path_homotopic_on (X \<times> Y) ?TXY (x0, y0) (x0, y0) f j"
        using hj_in hc_eq unfolding top1_loop_equiv_on_def by (by100 blast)
      have hph: "top1_path_homotopic_on Y TY y0 y0 (snd \<circ> f) (snd \<circ> j)"
        using continuous_preserves_path_homotopic[OF hTXY hTY hsnd_cont hfj] by (by100 simp)
      have hj_loop: "top1_is_loop_on (X \<times> Y) ?TXY (x0, y0) j"
        using hj_in hc_eq unfolding top1_loop_equiv_on_def by (by100 blast)
      have hj_cont: "top1_continuous_map_on I_set I_top (X \<times> Y) ?TXY j"
        using hj_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      have hj0: "j 0 = (x0, y0)" "j 1 = (x0, y0)"
        using hj_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
      have hsndj_loop: "top1_is_loop_on Y TY y0 (snd \<circ> j)"
        unfolding top1_is_loop_on_def top1_is_path_on_def comp_def
        using top1_continuous_map_on_comp[OF hj_cont hsnd_cont] hj0 unfolding comp_def by (by100 simp)
      have "top1_loop_equiv_on Y TY y0 (snd \<circ> f) (snd \<circ> j)"
        unfolding top1_loop_equiv_on_def using hsndf_loop hsndj_loop hph by (by100 blast)
      thus "k \<in> {k. top1_loop_equiv_on Y TY y0 (snd \<circ> f) k}"
        using hk top1_loop_equiv_on_trans[OF hTY] by (by100 blast)
    next
      fix k assume "k \<in> {k. top1_loop_equiv_on Y TY y0 (snd \<circ> f) k}"
      hence hk: "top1_loop_equiv_on Y TY y0 (snd \<circ> f) k" by (by100 blast)
      have "f \<in> c" using hc_eq top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
      thus "k \<in> top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd c"
        unfolding top1_fundamental_group_induced_on_def using hk by (by100 blast)
    qed
    have hsnd_in: "top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd c
        \<in> top1_fundamental_group_carrier Y TY y0"
      unfolding hind_eq_snd top1_fundamental_group_carrier_def using hsndf_loop by (by100 blast)
    show "z \<in> top1_fundamental_group_carrier X TX x0 \<times> top1_fundamental_group_carrier Y TY y0"
      using hfst_in hsnd_in hzc by (by100 simp)
  next
    fix z assume hz: "z \<in> top1_fundamental_group_carrier X TX x0 \<times>
        top1_fundamental_group_carrier Y TY y0"
    then obtain c1 c2 where hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
        and hc2: "c2 \<in> top1_fundamental_group_carrier Y TY y0"
        and hzp: "z = (c1, c2)" by (by100 auto)
    \<comment> \<open>c1 = [g] for some loop g at x0, c2 = [h] for some loop h at y0.\<close>
    obtain g where hg_loop: "top1_is_loop_on X TX x0 g"
        and hc1_eq: "c1 = {g'. top1_loop_equiv_on X TX x0 g g'}"
      using hc1 unfolding top1_fundamental_group_carrier_def by (by100 auto)
    obtain h where hh_loop: "top1_is_loop_on Y TY y0 h"
        and hc2_eq: "c2 = {h'. top1_loop_equiv_on Y TY y0 h h'}"
      using hc2 unfolding top1_fundamental_group_carrier_def by (by100 auto)
    \<comment> \<open>Define f(s) = (g(s), h(s)), a loop at (x0,y0) in X\<times>Y. By Theorem 18.4 continuous.
       Then \<Phi>([f]) = ([fst\<circ>f], [snd\<circ>f]) = ([g], [h]) since fst\<circ>f = g and snd\<circ>f = h.
       Uses continuous_preserves_path_homotopic for the equivalence class matching.\<close>
    let ?f = "\<lambda>s. (g s, h s)"
    have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
      using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hh_cont: "top1_continuous_map_on I_set I_top Y TY h"
      using hh_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hfst_f: "fst \<circ> ?f = g" by (rule ext) (by100 simp)
    have hsnd_f: "snd \<circ> ?f = h" by (rule ext) (by100 simp)
    have hpi1_f: "top1_continuous_map_on I_set I_top X TX (pi1 \<circ> ?f)"
      using hg_cont unfolding hfst_f hpi1_eq by (by100 simp)
    have hpi2_f: "top1_continuous_map_on I_set I_top Y TY (pi2 \<circ> ?f)"
      using hh_cont unfolding hsnd_f hpi2_eq by (by100 simp)
    have hf_cont: "top1_continuous_map_on I_set I_top (X \<times> Y) ?TXY ?f"
      using iffD2[OF Theorem_18_4[OF hTI hTX hTY]] hpi1_f hpi2_f by (by100 blast)
    have hg0: "g 0 = x0" "g 1 = x0"
      using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
    have hh0: "h 0 = y0" "h 1 = y0"
      using hh_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
    have hf_loop: "top1_is_loop_on (X \<times> Y) ?TXY (x0, y0) ?f"
      unfolding top1_is_loop_on_def top1_is_path_on_def
    proof (intro conjI)
      show "top1_continuous_map_on I_set I_top (X \<times> Y) ?TXY ?f" by (rule hf_cont)
      show "?f 0 = (x0, y0)" using hg0 hh0 by (by100 simp)
      show "?f 1 = (x0, y0)" using hg0 hh0 by (by100 simp)
    qed
    let ?cf = "{f'. top1_loop_equiv_on (X \<times> Y) ?TXY (x0, y0) ?f f'}"
    have hcf_carrier: "?cf \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
      unfolding top1_fundamental_group_carrier_def using hf_loop by (by100 blast)
    \<comment> \<open>induced_fst([f]) = [fst\<circ>f] = [g]. Key: fst\<circ>f = g, and induced preserves equiv classes.\<close>
    have hind_fst_eq: "top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst ?cf
        = {k. top1_loop_equiv_on X TX x0 g k}"
    proof (intro set_eqI iffI)
      fix k assume "k \<in> top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst ?cf"
      then obtain j where hj_in: "j \<in> ?cf" and hk: "top1_loop_equiv_on X TX x0 (fst \<circ> j) k"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      have hfj: "top1_path_homotopic_on (X \<times> Y) ?TXY (x0, y0) (x0, y0) ?f j"
        using hj_in unfolding top1_loop_equiv_on_def by (by100 blast)
      have "top1_path_homotopic_on X TX x0 x0 g (fst \<circ> j)"
        using continuous_preserves_path_homotopic[OF hTXY hTX hfst_cont hfj]
        unfolding hfst_f by (by100 simp)
      moreover have "top1_is_loop_on X TX x0 (fst \<circ> j)"
      proof -
        have hj_loop: "top1_is_loop_on (X \<times> Y) ?TXY (x0, y0) j"
          using hj_in unfolding top1_loop_equiv_on_def by (by100 blast)
        have hj_cont: "top1_continuous_map_on I_set I_top (X \<times> Y) ?TXY j"
          using hj_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        have hfstj_cont: "top1_continuous_map_on I_set I_top X TX (fst \<circ> j)"
          by (rule top1_continuous_map_on_comp[OF hj_cont hfst_cont])
        have hj0: "j 0 = (x0, y0)" "j 1 = (x0, y0)"
          using hj_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
        show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def comp_def
          using hfstj_cont hj0 unfolding comp_def by (by100 simp)
      qed
      ultimately have "top1_loop_equiv_on X TX x0 g (fst \<circ> j)"
        unfolding top1_loop_equiv_on_def using hg_loop by (by100 blast)
      thus "k \<in> {k. top1_loop_equiv_on X TX x0 g k}"
        using hk top1_loop_equiv_on_trans[OF hTX] by (by100 blast)
    next
      fix k assume "k \<in> {k. top1_loop_equiv_on X TX x0 g k}"
      hence hk: "top1_loop_equiv_on X TX x0 g k" by (by100 blast)
      have "?f \<in> ?cf" using top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
      moreover have "top1_loop_equiv_on X TX x0 (fst \<circ> ?f) k" using hk unfolding hfst_f .
      ultimately show "k \<in> top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) X TX x0 fst ?cf"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
    qed
    have hind_snd_eq: "top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd ?cf
        = {k. top1_loop_equiv_on Y TY y0 h k}"
    proof (intro set_eqI iffI)
      fix k assume "k \<in> top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd ?cf"
      then obtain j where hj_in: "j \<in> ?cf" and hk: "top1_loop_equiv_on Y TY y0 (snd \<circ> j) k"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
      have hfj: "top1_path_homotopic_on (X \<times> Y) ?TXY (x0, y0) (x0, y0) ?f j"
        using hj_in unfolding top1_loop_equiv_on_def by (by100 blast)
      have "top1_path_homotopic_on Y TY y0 y0 h (snd \<circ> j)"
        using continuous_preserves_path_homotopic[OF hTXY hTY hsnd_cont hfj]
        unfolding hsnd_f by (by100 simp)
      moreover have "top1_is_loop_on Y TY y0 (snd \<circ> j)"
      proof -
        have hj_loop: "top1_is_loop_on (X \<times> Y) ?TXY (x0, y0) j"
          using hj_in unfolding top1_loop_equiv_on_def by (by100 blast)
        have hj_cont: "top1_continuous_map_on I_set I_top (X \<times> Y) ?TXY j"
          using hj_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        have hsndj_cont: "top1_continuous_map_on I_set I_top Y TY (snd \<circ> j)"
          by (rule top1_continuous_map_on_comp[OF hj_cont hsnd_cont])
        have hj0: "j 0 = (x0, y0)" "j 1 = (x0, y0)"
          using hj_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
        show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def comp_def
          using hsndj_cont hj0 unfolding comp_def by (by100 simp)
      qed
      ultimately have "top1_loop_equiv_on Y TY y0 h (snd \<circ> j)"
        unfolding top1_loop_equiv_on_def using hh_loop by (by100 blast)
      thus "k \<in> {k. top1_loop_equiv_on Y TY y0 h k}"
        using hk top1_loop_equiv_on_trans[OF hTY] by (by100 blast)
    next
      fix k assume "k \<in> {k. top1_loop_equiv_on Y TY y0 h k}"
      hence hk: "top1_loop_equiv_on Y TY y0 h k" by (by100 blast)
      have "?f \<in> ?cf" using top1_loop_equiv_on_refl[OF hf_loop] by (by100 blast)
      moreover have "top1_loop_equiv_on Y TY y0 (snd \<circ> ?f) k" using hk unfolding hsnd_f .
      ultimately show "k \<in> top1_fundamental_group_induced_on (X \<times> Y) ?TXY (x0, y0) Y TY y0 snd ?cf"
        unfolding top1_fundamental_group_induced_on_def by (by100 blast)
    qed
    have "?\<Phi> ?cf = (c1, c2)" unfolding hind_fst_eq hind_snd_eq hc1_eq hc2_eq ..
    hence "?\<Phi> ?cf = z" using hzp by (by100 simp)
    thus "z \<in> ?\<Phi> ` (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))"
      using hcf_carrier by (by100 blast)
  qed
  \<comment> \<open>Assemble: \<Phi> is a group isomorphism.\<close>
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
  proof (intro exI conjI)
    show "top1_group_hom_on
        (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))
        (top1_fundamental_group_mul (X \<times> Y) ?TXY (x0, y0))
        (top1_fundamental_group_carrier X TX x0 \<times> top1_fundamental_group_carrier Y TY y0)
        (\<lambda>(c1, c2) (d1, d2). (top1_fundamental_group_mul X TX x0 c1 d1,
             top1_fundamental_group_mul Y TY y0 c2 d2))
        ?\<Phi>"
      unfolding top1_group_hom_on_def
    proof (intro conjI ballI)
      fix c assume hc: "c \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
      show "?\<Phi> c \<in> top1_fundamental_group_carrier X TX x0 \<times>
            top1_fundamental_group_carrier Y TY y0"
        using h\<Phi>_surj hc by (by100 blast)
    next
      fix c d assume hc: "c \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
          and hd: "d \<in> top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0)"
      show "?\<Phi> (top1_fundamental_group_mul (X \<times> Y) ?TXY (x0, y0) c d) =
          (\<lambda>(c1, c2) (d1, d2). (top1_fundamental_group_mul X TX x0 c1 d1,
             top1_fundamental_group_mul Y TY y0 c2 d2)) (?\<Phi> c) (?\<Phi> d)"
        using h\<Phi>_hom hc hd by (by100 blast)
    qed
    show "bij_betw ?\<Phi>
        (top1_fundamental_group_carrier (X \<times> Y) ?TXY (x0, y0))
        (top1_fundamental_group_carrier X TX x0 \<times> top1_fundamental_group_carrier Y TY y0)"
      unfolding bij_betw_def using h\<Phi>_inj h\<Phi>_surj by (by100 blast)
  qed
qed

section \<open>Chapter 10: Separation Theorems in the Plane\<close>
section \<open>Chapter 10: Separation Theorems in the Plane\<close>

section \<open>\<S>61 The Jordan Separation Theorem\<close>
section \<open>Chapter 10: Separation Theorems in the Plane\<close>
section \<open>Chapter 10: Separation Theorems in the Plane\<close>

section \<open>\<S>61 The Jordan Separation Theorem\<close>

text \<open>The 2-sphere S^2 as a subspace of R^3.\<close>
definition top1_S2 :: "(real \<times> real \<times> real) set" where
  "top1_S2 = {p. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1}"

definition top1_S2_topology :: "(real \<times> real \<times> real) set set" where
  "top1_S2_topology = subspace_topology UNIV
     (product_topology_on top1_open_sets
       (product_topology_on top1_open_sets top1_open_sets)) top1_S2"

text \<open>S^2 is Hausdorff (subspace of Hausdorff R^3).\<close>
lemma top1_S2_is_hausdorff:
  "is_hausdorff_on top1_S2 top1_S2_topology"
proof -
  have "top1_S2 \<subseteq> (UNIV :: (real \<times> real \<times> real) set)" by simp
  thus ?thesis unfolding top1_S2_topology_def
    using conjunct2[OF conjunct2[OF Theorem_17_11]] top1_R3_is_hausdorff by (by100 blast)
qed

text \<open>S^2 has strict topology.\<close>
lemma top1_S2_is_topology_on_strict:
  "is_topology_on_strict top1_S2 top1_S2_topology"
  unfolding is_topology_on_strict_def
proof (intro conjI)
  show "is_topology_on top1_S2 top1_S2_topology"
  proof -
    have hR3: "is_topology_on (UNIV :: (real \<times> real \<times> real) set)
        (product_topology_on top1_open_sets (product_topology_on top1_open_sets top1_open_sets))"
      using top1_R3_is_hausdorff unfolding is_hausdorff_on_def by (by100 blast)
    show ?thesis unfolding top1_S2_topology_def
      by (rule subspace_topology_is_topology_on[OF hR3]) simp
  qed
  show "top1_S2_topology \<subseteq> Pow top1_S2"
    unfolding top1_S2_topology_def subspace_topology_def by (by100 blast)
qed

text \<open>A set C separates a space X if X - C has more than one component.\<close>
definition top1_separates_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_separates_on X TX C \<longleftrightarrow>
     \<not> top1_connected_on (X - C) (subspace_topology X TX (X - C))"

lemma top1_separates_on_def_expand:
  "top1_separates_on X TX C \<Longrightarrow>
     \<not> top1_connected_on (X - C) (subspace_topology X TX (X - C))"
  unfolding top1_separates_on_def by blast

lemma top1_separates_onI:
  "\<not> top1_connected_on (X - C) (subspace_topology X TX (X - C)) \<Longrightarrow>
    top1_separates_on X TX C"
  unfolding top1_separates_on_def by blast

(** from \<S>61 Lemma 61.1: unbounded/bounded components of R^2-h(C) correspond to
    S^2-b components under a homeomorphism h: S^2-b \<rightarrow> R^2.
    If U is a component of S^2 - C not containing b, then h(U) is a BOUNDED
    component of R^2 - h(C). If U contains b, then h(U - {b}) is the UNBOUNDED
    component of R^2 - h(C). **)
text \<open>Stereographic projection: homeomorphism S^2 - {north pole} \<cong> R^2.\<close>
definition stereographic_proj :: "real \<times> real \<times> real \<Rightarrow> real \<times> real" where
  "stereographic_proj p = (fst p / (1 - snd (snd p)), fst (snd p) / (1 - snd (snd p)))"

definition north_pole :: "real \<times> real \<times> real" where
  "north_pole = (0, 0, 1)"

lemma north_pole_in_S2: "north_pole \<in> top1_S2"
  unfolding north_pole_def top1_S2_def by simp

definition stereographic_inv :: "real \<times> real \<Rightarrow> real \<times> real \<times> real" where
  "stereographic_inv q = (let u = fst q; v = snd q; d = u^2 + v^2 + 1
     in (2*u/d, 2*v/d, (u^2 + v^2 - 1)/d))"

lemma stereo_denom_pos: "(fst q)^2 + (snd q)^2 + 1 > (0::real)"
  by (smt (verit) power2_less_0 zero_less_one)

lemma stereo_denom_ne: "(fst q)^2 + (snd q)^2 + 1 \<noteq> (0::real)"
  using stereo_denom_pos[of q] by linarith

lemma stereographic_inv_in_S2:
  "stereographic_inv q \<in> top1_S2"
proof -
  let ?u = "fst q" and ?v = "snd q"
  let ?d = "?u^2 + ?v^2 + 1"
  have hd_ne: "?d \<noteq> 0" by (rule stereo_denom_ne)
  have "stereographic_inv q = (2*?u/?d, 2*?v/?d, (?u^2 + ?v^2 - 1)/?d)"
    unfolding stereographic_inv_def Let_def by simp
  moreover have "(2*?u/?d)^2 + (2*?v/?d)^2 + ((?u^2 + ?v^2 - 1)/?d)^2 = 1"
  proof -
    have "(2*?u/?d)^2 + (2*?v/?d)^2 + ((?u^2 + ?v^2 - 1)/?d)^2
        = (4*?u^2 + 4*?v^2 + (?u^2 + ?v^2 - 1)^2) / ?d^2"
      by (simp add: power_divide add_divide_distrib[symmetric])
    also have "4*?u^2 + 4*?v^2 + (?u^2 + ?v^2 - 1)^2 = ?d^2"
      by (simp add: power2_eq_square algebra_simps)
    also have "?d^2 / ?d^2 = 1" using hd_ne by simp
    finally show ?thesis .
  qed
  ultimately show ?thesis unfolding top1_S2_def by simp
qed

lemma stereographic_inv_not_north:
  "stereographic_inv q \<noteq> north_pole"
proof
  let ?u = "fst q" and ?v = "snd q"
  let ?d = "?u^2 + ?v^2 + 1"
  assume heq: "stereographic_inv q = north_pole"
  have hinv: "stereographic_inv q = (2*?u/?d, 2*?v/?d, (?u^2+?v^2-1)/?d)"
    unfolding stereographic_inv_def Let_def by simp
  have hz: "(?u^2+?v^2-1)/?d = 1"
    using heq hinv unfolding north_pole_def by simp
  have hd_ne: "?d \<noteq> 0" by (rule stereo_denom_ne)
  have "?u^2+?v^2-1 = ?d" using hz hd_ne by (simp add: field_simps)
  hence "?u^2+?v^2-1 = ?u^2+?v^2+1" by simp
  thus False by linarith
qed

lemma stereographic_proj_inv:
  assumes "p \<in> top1_S2 - {north_pole}"
  shows "stereographic_inv (stereographic_proj p) = p"
proof -
  obtain x y z where hxyz: "p = (x, y, z)" by (cases p, cases "snd p") auto
  have hp_S2: "x^2 + y^2 + z^2 = 1"
    using assms unfolding hxyz top1_S2_def by simp
  have hz_ne: "z \<noteq> 1"
  proof
    assume "z = 1"
    hence "x^2 + y^2 = 0" using hp_S2 by simp
    hence "x = 0" "y = 0" by (simp_all add: sum_power2_eq_zero_iff)
    hence "p = north_pole" unfolding hxyz north_pole_def using \<open>z = 1\<close> by simp
    thus False using assms by simp
  qed
  hence h1mz_ne: "1 - z \<noteq> 0" by simp
  let ?u = "x / (1-z)" and ?v = "y / (1-z)"
  have hproj: "stereographic_proj p = (?u, ?v)"
    unfolding stereographic_proj_def hxyz by simp
  have hd: "?u^2 + ?v^2 + 1 = 2/(1-z)"
  proof -
    have "?u^2 + ?v^2 = (x^2 + y^2) / (1-z)^2"
      by (simp add: power_divide add_divide_distrib[symmetric])
    also have "x^2 + y^2 = 1 - z^2" using hp_S2 by linarith
    also have "1 - z^2 = (1-z)*(1+z)" by (simp add: power2_eq_square algebra_simps)
    also have "(1-z)*(1+z) / (1-z)^2 = (1+z)/(1-z)"
      using h1mz_ne by (simp add: power2_eq_square nonzero_mult_div_cancel_left)
    finally have huv_eq: "?u^2 + ?v^2 = (1+z)/(1-z)" .
    have h_rhs: "(1-z)/(1-z) = (1::real)" using h1mz_ne by simp
    have "?u^2 + ?v^2 + 1 = (1+z)/(1-z) + (1-z)/(1-z)" using huv_eq h_rhs by simp
    also have "(1+z)/(1-z) + (1-z)/(1-z) = ((1+z) + (1-z)) / (1-z)"
      by (rule add_divide_distrib[symmetric])
    also have "(1+z) + (1-z) = (2::real)" by simp
    finally show ?thesis .
  qed
  have hd_ne: "?u^2 + ?v^2 + 1 \<noteq> 0"
    using hd h1mz_ne by simp
  have hd_val: "2/(1-z) \<noteq> 0" using h1mz_ne by simp
  \<comment> \<open>First component: 2*u/d = 2*(x/(1-z)) / (2/(1-z)) = x.\<close>
  have h1: "2*?u / (?u^2 + ?v^2 + 1) = x"
    unfolding hd using h1mz_ne by (simp add: field_simps)
  \<comment> \<open>Second component: 2*v/d = y.\<close>
  have h2: "2*?v / (?u^2 + ?v^2 + 1) = y"
    unfolding hd using h1mz_ne by (simp add: field_simps)
  \<comment> \<open>Third component: (u^2+v^2-1)/d.\<close>
  have h3: "(?u^2 + ?v^2 - 1) / (?u^2 + ?v^2 + 1) = z"
  proof -
    have huvm1: "?u^2 + ?v^2 - 1 = 2/(1-z) - 2" using hd by linarith
    \<comment> \<open>Goal: (2/(1-z) - 2) / (2/(1-z)) = z. Multiply both sides by 2/(1-z).\<close>
    have h2dz: "2/(1-z) \<noteq> (0::real)" using h1mz_ne by simp
    have key: "(2/(1-z) - 2) = z * (2/(1-z))"
    proof -
      have "2*(1-z)/(1-z) = (2::real)"
        using h1mz_ne nonzero_mult_div_cancel_right by (by100 blast)
      hence "2 = 2*(1-z)/(1-z)" by simp
      hence "2/(1-z) - 2 = 2/(1-z) - 2*(1-z)/(1-z)" by simp
      also have "\<dots> = (2 - 2*(1-z))/(1-z)" by (rule diff_divide_distrib[symmetric])
      also have "(2::real) - 2*(1-z) = 2*z"
        by (simp add: left_diff_distrib)
      finally have "2/(1-z) - 2 = 2*z/(1-z)" .
      also have "2*z/(1-z) = z * (2/(1-z))" by simp
      finally show ?thesis .
    qed
    have "(?u^2 + ?v^2 - 1) / (?u^2 + ?v^2 + 1) = (2/(1-z) - 2) / (2/(1-z))"
      using huvm1 hd by simp
    also have "\<dots> = z * (2/(1-z)) / (2/(1-z))" using key by simp
    also have "\<dots> = z" using h2dz by simp
    finally show ?thesis .
  qed
  show ?thesis unfolding hproj stereographic_inv_def Let_def
    using h1 h2 h3 hxyz by simp
qed

lemma stereographic_inv_proj:
  "stereographic_proj (stereographic_inv q) = q"
proof -
  let ?u = "fst q" and ?v = "snd q"
  let ?d = "?u^2 + ?v^2 + 1"
  have hd_ne: "?d \<noteq> 0" by (rule stereo_denom_ne)
  have hd_pos: "?d > 0" by (rule stereo_denom_pos)
  have hinv: "stereographic_inv q = (2*?u/?d, 2*?v/?d, (?u^2+?v^2-1)/?d)"
    unfolding stereographic_inv_def Let_def by simp
  have hz: "snd (snd (stereographic_inv q)) = (?u^2+?v^2-1)/?d"
    using hinv by simp
  have h1mz: "1 - (?u^2+?v^2-1)/?d = 2/?d"
    using hd_ne by (simp add: field_simps)
  have h2d_ne: "2/?d \<noteq> (0::real)" using hd_ne by simp
  have hx: "fst (stereographic_inv q) = 2*?u/?d"
    using hinv by simp
  have hy: "fst (snd (stereographic_inv q)) = 2*?v/?d"
    using hinv by simp
  have hfst: "fst (stereographic_proj (stereographic_inv q)) = ?u"
  proof -
    have "fst (stereographic_proj (stereographic_inv q))
        = fst (stereographic_inv q) / (1 - snd (snd (stereographic_inv q)))"
      unfolding stereographic_proj_def by simp
    also have "\<dots> = (2*?u/?d) / (2/?d)" using hx hz h1mz by simp
    also have "\<dots> = ?u" using hd_ne by (simp add: field_simps)
    finally show ?thesis .
  qed
  have hsnd: "snd (stereographic_proj (stereographic_inv q)) = ?v"
  proof -
    have "snd (stereographic_proj (stereographic_inv q))
        = fst (snd (stereographic_inv q)) / (1 - snd (snd (stereographic_inv q)))"
      unfolding stereographic_proj_def by simp
    also have "\<dots> = (2*?v/?d) / (2/?d)" using hy hz h1mz by simp
    also have "\<dots> = ?v" using hd_ne by (simp add: field_simps)
    finally show ?thesis .
  qed
  show ?thesis by (rule prod_eqI) (simp_all add: hfst hsnd)
qed

lemma stereographic_proj_homeomorphism:
  "top1_homeomorphism_on (top1_S2 - {north_pole})
     (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
     (UNIV :: (real \<times> real) set)
     (product_topology_on top1_open_sets top1_open_sets)
     stereographic_proj"
  unfolding top1_homeomorphism_on_def
proof (intro conjI)
  let ?S = "top1_S2 - {north_pole}"
  let ?TS = "subspace_topology top1_S2 top1_S2_topology ?S"
  let ?TR2 = "product_topology_on (top1_open_sets :: real set set) top1_open_sets"
  show "is_topology_on ?S ?TS"
  proof -
    have "is_topology_on top1_S2 top1_S2_topology"
      using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    thus ?thesis by (rule subspace_topology_is_topology_on) simp
  qed
  show "is_topology_on (UNIV :: (real \<times> real) set) ?TR2"
  proof -
    have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
      by (rule top1_open_sets_is_topology_on_UNIV)
    show ?thesis using product_topology_on_is_topology_on[OF hTR hTR] by simp
  qed
  show "bij_betw stereographic_proj ?S (UNIV :: (real \<times> real) set)"
    unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on stereographic_proj ?S"
    proof (rule inj_onI)
      fix a b assume "a \<in> ?S" "b \<in> ?S" "stereographic_proj a = stereographic_proj b"
      hence "stereographic_inv (stereographic_proj a) = stereographic_inv (stereographic_proj b)"
        by simp
      thus "a = b" using stereographic_proj_inv[of a] stereographic_proj_inv[of b]
          \<open>a \<in> ?S\<close> \<open>b \<in> ?S\<close> by simp
    qed
  next
    show "stereographic_proj ` ?S = UNIV"
    proof (rule set_eqI, rule iffI)
      fix q :: "real \<times> real"
      assume "q \<in> stereographic_proj ` ?S" thus "q \<in> UNIV" by simp
    next
      fix q :: "real \<times> real" assume "q \<in> UNIV"
      have hinvS: "stereographic_inv q \<in> ?S"
        using stereographic_inv_in_S2 stereographic_inv_not_north by simp
      have "stereographic_proj (stereographic_inv q) = q"
        by (rule stereographic_inv_proj)
      hence "q = stereographic_proj (stereographic_inv q)" by simp
      thus "q \<in> stereographic_proj ` ?S" using hinvS by (by100 blast)
    qed
  qed
  show "top1_continuous_map_on ?S ?TS UNIV ?TR2 stereographic_proj"
  proof -
    \<comment> \<open>stereographic_proj is continuous on S^2-{north_pole} as a rational function
       (defined wherever z \<noteq> 1, which holds on S^2-{N}).\<close>
    have hproj_cont: "continuous_on ?S stereographic_proj"
    proof -
      have "\<And>p. p \<in> ?S \<Longrightarrow> 1 - snd (snd p) \<noteq> 0"
      proof -
        fix p assume hp: "p \<in> ?S"
        show "1 - snd (snd p) \<noteq> 0"
        proof
          assume h0: "1 - snd (snd p) = 0"
          hence hz1: "snd (snd p) = 1" by simp
          have hp_S2: "p \<in> top1_S2" using hp by simp
          hence "fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1"
            unfolding top1_S2_def by simp
          hence "fst p ^ 2 + fst (snd p) ^ 2 = 0" using hz1 by simp
          hence "fst p = 0" "fst (snd p) = 0"
            by (simp_all add: sum_power2_eq_zero_iff)
          hence "p = (0, 0, 1)" using hz1
            by (cases p, cases "snd p") simp
          hence "p = north_pole" unfolding north_pole_def by simp
          thus False using hp by simp
        qed
      qed
      thus ?thesis unfolding stereographic_proj_def
        by (intro continuous_intros continuous_on_divide) auto
    qed
    show ?thesis unfolding top1_continuous_map_on_def product_topology_on_open_sets
    proof (intro conjI ballI)
      fix p assume "p \<in> ?S" thus "stereographic_proj p \<in> UNIV" by simp
    next
      fix V :: "(real \<times> real) set"
      assume hV: "V \<in> (top1_open_sets :: (real \<times> real) set set)"
      have hVo: "open V" using hV unfolding top1_open_sets_def by (by100 blast)
      \<comment> \<open>Preimage: {p \<in> S | proj(p) \<in> V} = S \<inter> proj\<inverse>(V).\<close>
      \<comment> \<open>proj\<inverse>(V) is open in S since proj is continuous_on S.\<close>
      \<comment> \<open>By continuous_on_open_invariant: \<exists>U open. proj\<inverse>(V) \<inter> S = U \<inter> S.\<close>
      have "\<exists>A. open A \<and> A \<inter> ?S = stereographic_proj -` V \<inter> ?S"
        using iffD1[OF continuous_on_open_invariant hproj_cont] hVo by (by100 blast)
      then obtain W where hWo: "open W" and hWeq: "W \<inter> ?S = stereographic_proj -` V \<inter> ?S"
        by auto
      have "{p \<in> ?S. stereographic_proj p \<in> V} = W \<inter> ?S"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {p \<in> ?S. stereographic_proj p \<in> V}"
        hence hxS: "x \<in> ?S" and hxV: "stereographic_proj x \<in> V" by (by100 blast)+
        hence "x \<in> stereographic_proj -` V \<inter> ?S" by (by100 blast)
        thus "x \<in> W \<inter> ?S" using hWeq by (by100 blast)
      next
        fix x assume hx: "x \<in> W \<inter> ?S"
        hence "x \<in> stereographic_proj -` V \<inter> ?S" using hWeq by (by100 blast)
        thus "x \<in> {p \<in> ?S. stereographic_proj p \<in> V}" by (by100 blast)
      qed
      moreover have "W \<inter> ?S \<in> ?TS"
      proof -
        have "W \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
          using hWo unfolding top1_open_sets_def by (by100 blast)
        hence hW_R3: "W \<in> product_topology_on top1_open_sets
            (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_open_sets by metis
        have "top1_S2 \<inter> W \<in> top1_S2_topology"
          unfolding top1_S2_topology_def subspace_topology_def using hW_R3 by (by100 blast)
        hence "?S \<inter> (top1_S2 \<inter> W) \<in> ?TS"
          unfolding subspace_topology_def by (by100 blast)
        moreover have "?S \<inter> (top1_S2 \<inter> W) = W \<inter> ?S" by (by100 blast)
        ultimately show ?thesis by simp
      qed
      ultimately show "{p \<in> ?S. stereographic_proj p \<in> V} \<in> ?TS" by simp
    qed
  qed
  show "top1_continuous_map_on UNIV ?TR2 ?S ?TS (inv_into ?S stereographic_proj)"
  proof -
    \<comment> \<open>inv_into agrees with stereographic_inv on UNIV.\<close>
    have hinv_eq: "\<And>q. inv_into ?S stereographic_proj q = stereographic_inv q"
    proof -
      fix q :: "real \<times> real"
      have "stereographic_inv q \<in> ?S"
        using stereographic_inv_in_S2 stereographic_inv_not_north by simp
      moreover have "stereographic_proj (stereographic_inv q) = q"
        by (rule stereographic_inv_proj)
      ultimately show "inv_into ?S stereographic_proj q = stereographic_inv q"
      proof (intro inv_into_f_eq)
        show "inj_on stereographic_proj ?S"
          by (rule inj_onI) (metis stereographic_proj_inv)
      qed
    qed
    \<comment> \<open>stereographic_inv is continuous on UNIV.\<close>
    have hinv_cont: "continuous_on UNIV stereographic_inv"
      unfolding stereographic_inv_def Let_def
      by (intro continuous_intros continuous_on_divide)
         (simp_all add: stereo_denom_ne)
    \<comment> \<open>Bridge: since inv_into = stereographic_inv on UNIV,
       and stereographic_inv is continuous_on UNIV with range in ?S,
       show top1_continuous_map_on.\<close>
    have hinv_map: "\<And>q. stereographic_inv q \<in> ?S"
      using stereographic_inv_in_S2 stereographic_inv_not_north by simp
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix q :: "real \<times> real" assume "q \<in> UNIV"
      show "inv_into ?S stereographic_proj q \<in> ?S"
        using hinv_eq hinv_map by simp
    next
      fix V assume hV: "V \<in> ?TS"
      then obtain W where hWS2: "W \<in> top1_S2_topology" and hVeq: "V = ?S \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      then obtain W' where hW'R3: "W' \<in> product_topology_on top1_open_sets
            (product_topology_on top1_open_sets top1_open_sets)"
          and hWeq: "W = top1_S2 \<inter> W'"
        unfolding top1_S2_topology_def subspace_topology_def by (by100 blast)
      have "W' \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
        using hW'R3 product_topology_on_open_sets by metis
      hence hW'open: "open W'" unfolding top1_open_sets_def by (by100 blast)
      have hVeq': "V = ?S \<inter> W'" using hVeq hWeq by (by100 blast)
      \<comment> \<open>Preimage under inv_into = preimage under stereographic_inv.\<close>
      have hpre_eq: "{q \<in> UNIV. inv_into ?S stereographic_proj q \<in> V}
          = stereographic_inv -` V"
        using hinv_eq by auto
      have "stereographic_inv -` V = stereographic_inv -` (?S \<inter> W')"
        using hVeq' by simp
      also have "\<dots> = stereographic_inv -` W'"
        using hinv_map by auto
      finally have hpre: "{q \<in> UNIV. inv_into ?S stereographic_proj q \<in> V}
          = stereographic_inv -` W'" using hpre_eq by simp
      have "open (stereographic_inv -` W')"
        by (rule open_vimage[OF hW'open hinv_cont])
      hence "stereographic_inv -` W' \<in> (top1_open_sets :: (real \<times> real) set set)"
        unfolding top1_open_sets_def by (by100 blast)
      hence "stereographic_inv -` W' \<in> ?TR2"
        using product_topology_on_open_sets_real2 by metis
      thus "{q \<in> UNIV. inv_into ?S stereographic_proj q \<in> V} \<in> ?TR2"
        using hpre by simp
    qed
  qed
qed

text \<open>Key consequence: S^2 minus any point is homeomorphic to R^2, hence simply connected.\<close>
lemma R2_simply_connected:
  "top1_simply_connected_on (UNIV :: (real \<times> real) set)
     (product_topology_on top1_open_sets top1_open_sets)"
  unfolding top1_simply_connected_on_def
proof (intro conjI allI impI ballI)
  \<comment> \<open>Part 1: R2 is path-connected. Straight line between any two points.\<close>
  show "top1_path_connected_on (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets)"
  proof -
    have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2: "is_topology_on (UNIV :: (real \<times> real) set)
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
      using product_topology_on_is_topology_on[OF hTR hTR] by simp
    have "\<forall>x\<in>(UNIV :: (real \<times> real) set). \<forall>y\<in>UNIV.
        \<exists>f. top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) x y f"
    proof (intro ballI)
      fix x y :: "real \<times> real"
      assume "x \<in> UNIV" "y \<in> UNIV"
      let ?\<gamma> = "\<lambda>t::real. ((1-t)*fst x + t*fst y, (1-t)*snd x + t*snd y)"
      have h\<gamma>_cont_univ: "continuous_on UNIV ?\<gamma>"
        by (intro continuous_intros)
      have h\<gamma>_cont: "top1_continuous_map_on I_set I_top
          (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) ?\<gamma>"
        unfolding top1_continuous_map_on_def product_topology_on_open_sets
      proof (intro conjI ballI)
        fix s assume "s \<in> I_set" thus "?\<gamma> s \<in> UNIV" by simp
      next
        fix V assume hV: "V \<in> (top1_open_sets :: (real \<times> real) set set)"
        have hVopen: "open V" using hV unfolding top1_open_sets_def by (by100 blast)
        have hpre: "open (?\<gamma> -` V)"
          by (rule open_vimage[OF hVopen h\<gamma>_cont_univ])
        have hpre_os: "?\<gamma> -` V \<in> (top1_open_sets :: real set set)"
          using hpre unfolding top1_open_sets_def by (by100 blast)
        have "{s \<in> I_set. ?\<gamma> s \<in> V} = I_set \<inter> (?\<gamma> -` V)" by (by100 auto)
        thus "{s \<in> I_set. ?\<gamma> s \<in> V} \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def
          using hpre_os by (by100 blast)
      qed
      have "?\<gamma> 0 = x" by simp
      moreover have "?\<gamma> 1 = y" by simp
      ultimately show "\<exists>f. top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) x y f"
        unfolding top1_is_path_on_def using h\<gamma>_cont by (by100 blast)
    qed
    thus ?thesis unfolding top1_path_connected_on_def using hTR2 by simp
  qed
next
  \<comment> \<open>Part 2: Every loop is nulhomotopic. Straight-line contraction H(s,t) = (1-t)*f(s) + t*x0.\<close>
  fix x0 :: "real \<times> real" and f
  assume hx0: "x0 \<in> (UNIV :: (real \<times> real) set)"
  assume hf: "top1_is_loop_on (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets) x0 f"
  \<comment> \<open>Define the straight-line homotopy.\<close>
  define H where "H = (\<lambda>(s::real, t::real). ((1-t) * fst (f s) + t * fst x0,
                                               (1-t) * snd (f s) + t * snd x0))"
  \<comment> \<open>H(s,0) = f(s), H(s,1) = x0, H(0,t) = (1-t)*f(0)+t*x0 = (1-t)*x0+t*x0 = x0,
     H(1,t) = (1-t)*f(1)+t*x0 = (1-t)*x0+t*x0 = x0 (since f is a loop).\<close>
  show "top1_path_homotopic_on (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets) x0 x0 f (top1_constant_path x0)"
  proof -
    have hfcont: "top1_continuous_map_on I_set I_top
        (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) f"
      using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hf0: "f 0 = x0" and hf1: "f 1 = x0"
      using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
    \<comment> \<open>Extract continuous_on I_set f (in standard Isabelle sense).\<close>
    have hf_cont_I: "continuous_on I_set f"
      unfolding continuous_on_open_invariant
    proof (intro allI impI)
      fix B :: "(real \<times> real) set" assume hBo: "open B"
      have hBos: "B \<in> (top1_open_sets :: (real \<times> real) set set)"
        using hBo unfolding top1_open_sets_def by (by100 blast)
      have hBprod: "B \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
        using hBos product_topology_on_open_sets_real2 by (by100 metis)
      have hpre: "{s \<in> I_set. f s \<in> B} \<in> I_top"
        using hBprod hfcont unfolding top1_continuous_map_on_def by (by100 blast)
      have hpre': "{s \<in> I_set. f s \<in> B} \<in> subspace_topology UNIV top1_open_sets I_set"
        using hpre unfolding top1_unit_interval_topology_def .
      obtain W where hW: "W \<in> (top1_open_sets :: real set set)"
          and heq: "{s \<in> I_set. f s \<in> B} = I_set \<inter> W"
        using hpre' unfolding subspace_topology_def by (by100 blast)
      have "open W" using hW unfolding top1_open_sets_def by (by100 blast)
      moreover have "W \<inter> I_set = f -` B \<inter> I_set" using heq by (by100 blast)
      ultimately show "\<exists>A. open A \<and> A \<inter> I_set = f -` B \<inter> I_set" by (by100 blast)
    qed
    have hfst_cont_I: "continuous_on I_set (fst \<circ> f)"
      by (intro continuous_on_compose[OF hf_cont_I] continuous_on_subset[OF continuous_on_fst]) auto
    have hsnd_cont_I: "continuous_on I_set (snd \<circ> f)"
      by (intro continuous_on_compose[OF hf_cont_I] continuous_on_subset[OF continuous_on_snd]) auto
    \<comment> \<open>Define straight-line homotopy using top1_slh_ext component-wise.\<close>
    define H_ext where "H_ext = (\<lambda>p::real\<times>real.
        (top1_slh_ext (fst \<circ> f) (fst x0) p,
         top1_slh_ext (snd \<circ> f) (snd x0) p))"
    have hH_cont_univ: "continuous_on UNIV H_ext"
      unfolding H_ext_def
      by (intro continuous_intros top1_slh_ext_continuous[OF hfst_cont_I]
              top1_slh_ext_continuous[OF hsnd_cont_I])
    have hH_eq: "\<And>s t. s \<in> I_set \<Longrightarrow> t \<in> I_set \<Longrightarrow>
        H_ext (s, t) = ((1-t) * fst (f s) + t * fst x0, (1-t) * snd (f s) + t * snd x0)"
    proof -
      fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set"
      have hst: "(s, t) \<in> I_set \<times> I_set" using hs ht by simp
      have "top1_slh_ext (fst \<circ> f) (fst x0) (s, t) = (1 - t) * (fst \<circ> f) s + t * fst x0"
        using top1_slh_ext_agrees[OF hst] by simp
      moreover have "top1_slh_ext (snd \<circ> f) (snd x0) (s, t) = (1 - t) * (snd \<circ> f) s + t * snd x0"
        using top1_slh_ext_agrees[OF hst] by simp
      ultimately show "H_ext (s, t) = ((1-t) * fst (f s) + t * fst x0, (1-t) * snd (f s) + t * snd x0)"
        unfolding H_ext_def comp_def by simp
    qed
    \<comment> \<open>Bridge to top1_continuous_map_on.\<close>
    have hH_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) H_ext"
      unfolding top1_continuous_map_on_def product_topology_on_open_sets
    proof (intro conjI ballI)
      fix p assume "p \<in> I_set \<times> I_set" thus "H_ext p \<in> UNIV" by simp
    next
      fix V :: "(real \<times> real) set"
      assume hV: "V \<in> (top1_open_sets :: (real \<times> real) set set)"
      have hVo: "open V" using hV unfolding top1_open_sets_def by (by100 blast)
      have hFV: "open (H_ext -` V)" by (rule open_vimage[OF hVo hH_cont_univ])
      have hFV_os: "H_ext -` V \<in> (top1_open_sets :: (real\<times>real) set set)"
        using hFV unfolding top1_open_sets_def by (by100 blast)
      have hFV_prod: "H_ext -` V \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
        using hFV_os product_topology_on_open_sets_real2 by metis
      have "(I_set \<times> I_set) \<inter> (H_ext -` V) \<in> product_topology_on I_top I_top"
        using hFV_prod unfolding II_topology_eq_subspace subspace_topology_def by (by100 blast)
      moreover have "{p \<in> I_set \<times> I_set. H_ext p \<in> V} = (I_set \<times> I_set) \<inter> (H_ext -` V)"
        by (by100 auto)
      ultimately show "{p \<in> I_set \<times> I_set. H_ext p \<in> V} \<in> II_topology"
        unfolding II_topology_def by simp
    qed
    \<comment> \<open>Boundary conditions.\<close>
    have hHs0: "\<forall>s\<in>I_set. H_ext (s, 0) = f s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "H_ext (s, 0) = ((1-0) * fst (f s) + 0 * fst x0, (1-0) * snd (f s) + 0 * snd x0)"
        using hH_eq[OF hs] by (simp add: top1_unit_interval_def)
      thus "H_ext (s, 0) = f s" by simp
    qed
    have hHs1: "\<forall>s\<in>I_set. H_ext (s, 1) = top1_constant_path x0 s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "H_ext (s, 1) = ((1-1) * fst (f s) + 1 * fst x0, (1-1) * snd (f s) + 1 * snd x0)"
        using hH_eq[OF hs] by (simp add: top1_unit_interval_def)
      thus "H_ext (s, 1) = top1_constant_path x0 s"
        unfolding top1_constant_path_def by simp
    qed
    have hH0t: "\<forall>t\<in>I_set. H_ext (0, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      have "H_ext (0, t) = ((1-t) * fst (f 0) + t * fst x0, (1-t) * snd (f 0) + t * snd x0)"
        using hH_eq[OF h0I ht] .
      also have "\<dots> = ((1-t) * fst x0 + t * fst x0, (1-t) * snd x0 + t * snd x0)"
        by (simp add: hf0)
      also have "\<dots> = x0" by (simp add: algebra_simps)
      finally show "H_ext (0, t) = x0" .
    qed
    have hH1t: "\<forall>t\<in>I_set. H_ext (1, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      have "H_ext (1, t) = ((1-t) * fst (f 1) + t * fst x0, (1-t) * snd (f 1) + t * snd x0)"
        using hH_eq[OF h1I ht] .
      also have "\<dots> = ((1-t) * fst x0 + t * fst x0, (1-t) * snd x0 + t * snd x0)"
        by (simp add: hf1)
      also have "\<dots> = x0" by (simp add: algebra_simps)
      finally show "H_ext (1, t) = x0" .
    qed
    \<comment> \<open>f and constant path are paths on UNIV.\<close>
    have hTR2: "is_topology_on (UNIV :: (real \<times> real) set)
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
    proof -
      have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
        by (rule top1_open_sets_is_topology_on_UNIV)
      show ?thesis using product_topology_on_is_topology_on[OF hTR hTR] by simp
    qed
    have hf_path: "top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) x0 x0 f"
      using hf unfolding top1_is_loop_on_def by simp
    have hc_path: "top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) x0 x0
        (top1_constant_path x0)"
      by (rule top1_constant_path_is_path[OF hTR2]) simp
    show ?thesis unfolding top1_path_homotopic_on_def
      using hf_path hc_path hH_cont hHs0 hHs1 hH0t hH1t
      by (intro conjI exI[of _ H_ext]) auto
  qed
qed


lemma S2_minus_north_pole_simply_connected:
  "top1_simply_connected_on (top1_S2 - {north_pole})
     (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
  by (rule homeomorphism_preserves_simply_connected[OF
      stereographic_proj_homeomorphism R2_simply_connected])

text \<open>Householder reflection: sends any point b \<in> S^2 to north_pole.
   When b \<noteq> N: R(p) = p - 2(v\<cdot>p)/(v\<cdot>v) * v where v = N - b = (-b1, -b2, 1-b3).
   When b = N: identity.\<close>
definition householder_S2 :: "real \<times> real \<times> real \<Rightarrow> real \<times> real \<times> real \<Rightarrow> real \<times> real \<times> real" where
  "householder_S2 b = (if b = north_pole then id
    else (let b1 = fst b; b2 = fst(snd b); b3 = snd(snd b)
      in (\<lambda>(x,y,z). let vdp = -b1*x+(-b2)*y+(1-b3)*z; c = 2*vdp/(2-2*b3)
          in (x-c*(-b1), y-c*(-b2), z-c*(1-b3)))))"

lemma householder_S2_homeo:
  assumes "b \<in> top1_S2"
  shows "top1_homeomorphism_on (top1_S2 - {b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
      (top1_S2 - {north_pole})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
      (householder_S2 b)"
proof (cases "b = north_pole")
  case True
  have "householder_S2 north_pole = id" unfolding householder_S2_def by simp
  hence hid: "\<And>x. householder_S2 b x = x" using True by simp
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
  show ?thesis unfolding True top1_homeomorphism_on_def
    using hid
  proof (intro conjI)
    show "is_topology_on (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) simp
    show "is_topology_on (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) simp
    show "bij_betw (householder_S2 north_pole) (top1_S2 - {north_pole}) (top1_S2 - {north_pole})"
      using hid True by (simp add: bij_betw_def inj_on_def)
    show "top1_continuous_map_on (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
        (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) (householder_S2 north_pole)"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume "x \<in> top1_S2 - {north_pole}" thus "householder_S2 north_pole x \<in> top1_S2 - {north_pole}"
        using hid True by simp
    next
      fix V assume hV: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
      have "{x \<in> top1_S2 - {north_pole}. householder_S2 north_pole x \<in> V} = V \<inter> (top1_S2 - {north_pole})"
        using hid True by auto
      also have "\<dots> = V"
        using hV unfolding subspace_topology_def by (by100 blast)
      finally show "{x \<in> top1_S2 - {north_pole}. householder_S2 north_pole x \<in> V} \<in>
          subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
        using hV by simp
    qed
    show "top1_continuous_map_on (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
        (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
        (inv_into (top1_S2 - {north_pole}) (householder_S2 north_pole))"
    proof -
      have hinj: "inj_on (householder_S2 north_pole) (top1_S2 - {north_pole})"
      proof (rule inj_onI)
        fix x y assume "x \<in> top1_S2 - {north_pole}" "y \<in> top1_S2 - {north_pole}"
            "householder_S2 north_pole x = householder_S2 north_pole y"
        thus "x = y" using hid True by simp
      qed
      have hinv_eq: "\<And>x. x \<in> top1_S2 - {north_pole} \<Longrightarrow>
          inv_into (top1_S2 - {north_pole}) (householder_S2 north_pole) x = x"
      proof -
        fix x assume hx: "x \<in> top1_S2 - {north_pole}"
        have "householder_S2 north_pole x = x" using hid True by simp
        thus "inv_into (top1_S2 - {north_pole}) (householder_S2 north_pole) x = x"
          using hx hinj by (intro inv_into_f_eq) auto
      qed
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x assume hx: "x \<in> top1_S2 - {north_pole}"
        show "inv_into (top1_S2 - {north_pole}) (householder_S2 north_pole) x \<in> top1_S2 - {north_pole}"
          using hinv_eq[OF hx] hx by simp
      next
        fix V assume hV: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
        have "{x \<in> top1_S2 - {north_pole}. inv_into (top1_S2 - {north_pole}) (householder_S2 north_pole) x \<in> V}
            = V \<inter> (top1_S2 - {north_pole})"
          using hinv_eq by auto
        also have "\<dots> = V" using hV unfolding subspace_topology_def by (by100 blast)
        finally show "{x \<in> top1_S2 - {north_pole}. inv_into (top1_S2 - {north_pole}) (householder_S2 north_pole) x \<in> V}
            \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
          using hV by simp
      qed
    qed
  qed
next
  case False
  \<comment> \<open>Householder reflection: v = N - b, R(p) = p - 2(v\<cdot>p)/(v\<cdot>v)*v.\<close>
  obtain b1 b2 b3 where hb_eq: "b = (b1, b2, b3)" by (cases b, cases "snd b") auto
  have hb_S2: "b1^2 + b2^2 + b3^2 = 1" using assms unfolding hb_eq top1_S2_def by simp
  have hb3_ne1: "b3 \<noteq> 1"
  proof
    assume "b3 = 1"
    hence "b1^2 + b2^2 = 0" using hb_S2 by simp
    hence "b1 = 0" "b2 = 0" by (simp_all add: sum_power2_eq_zero_iff)
    hence "b = north_pole" unfolding hb_eq north_pole_def using \<open>b3 = 1\<close> by simp
    thus False using False by simp
  qed
  \<comment> \<open>v\<cdot>v = 2 - 2*b3, which is > 0 since b3 < 1.\<close>
  have hvv: "b1^2 + b2^2 + (1-b3)^2 = 2 - 2*b3"
    using hb_S2 by (simp add: power2_eq_square algebra_simps)
  have hvv_ne: "2 - 2*b3 \<noteq> (0::real)" using hb3_ne1 by linarith
  \<comment> \<open>Define R on R^3. R is linear, hence continuous.\<close>
  define R where "R = householder_S2 b"
  have R_expand: "R = (\<lambda>(x::real,y::real,z::real).
    let vdp = -b1*x + (-b2)*y + (1-b3)*z;
        c = 2*vdp/(2 - 2*b3)
    in (x - c*(-b1), y - c*(-b2), z - c*(1-b3)))"
    unfolding R_def householder_S2_def hb_eq using False
    unfolding north_pole_def by simp
  \<comment> \<open>R maps S^2 to S^2 (isometry), R(b) = N, R is its own inverse.\<close>
  have hb12: "b1*b1 + b2*b2 = 1 - b3*b3"
    using hb_S2 by (simp add: power2_eq_square algebra_simps)
  have hR_b_N: "R b = north_pole"
  proof -
    let ?vdp = "-b1*b1 + (-b2)*b2 + (1-b3)*b3"
    have hvdp_val: "?vdp = b3 - 1" using hb_S2
      by (simp add: power2_eq_square algebra_simps)
    have hc_m1: "2*(b3-1)/(2-2*b3) = -(1::real)"
      apply (subst divide_eq_eq)
      apply (simp add: hvv_ne algebra_simps)
      apply (rule hb3_ne1)
      done
    let ?c = "2*?vdp/(2-2*b3)"
    have hc_val: "?c = -(1::real)"
      using hvdp_val hc_m1 by simp
    have "R b = (b1 - ?c*(-b1), b2 - ?c*(-b2), b3 - ?c*(1-b3))"
      unfolding R_expand hb_eq Let_def by simp
    also have "\<dots> = (b1 - (-1)*(-b1), b2 - (-1)*(-b2), b3 - (-1)*(1-b3))"
      using hc_val by simp
    also have "\<dots> = (0::real, 0, 1)" by simp
    finally show ?thesis unfolding north_pole_def .
  qed
  have hR_S2: "\<And>p. p \<in> top1_S2 \<Longrightarrow> R p \<in> top1_S2"
  proof -
    fix p assume hp: "p \<in> top1_S2"
    obtain x y z :: real where hxyz: "p = (x, y, z)" by (cases p, cases "snd p") auto
    have hp_S2: "x^2 + y^2 + z^2 = 1" using hp unfolding hxyz top1_S2_def by simp
    define vdp where "vdp = -b1*x + (-b2)*y + (1-b3)*z"
    define d where "d = (2-2*b3::real)"
    define c where "c = 2*vdp/d"
    have hd_ne: "d \<noteq> 0" unfolding d_def using hb3_ne1 by linarith
    have hvv_d: "b1^2+b2^2+(1-b3)^2 = d" unfolding d_def
      using hb_S2 by (simp add: power2_eq_square algebra_simps)
    have hcd: "c * d = 2*vdp" unfolding c_def using hd_ne by simp
    have hcancel: "c^2*d = 2*c*vdp"
    proof -
      have "c * (c * d) = c * (2*vdp)" using hcd by simp
      thus ?thesis by (simp add: power2_eq_square algebra_simps)
    qed
    have h_expand: "(x - c*(-b1))^2 + (y - c*(-b2))^2 + (z - c*(1-b3))^2
        = (x^2 + y^2 + z^2) + c^2*(b1^2+b2^2+(1-b3)^2) + 2*c*(b1*x+b2*y-(1-b3)*z)"
      by (simp add: power2_eq_square algebra_simps)
    have hvdp_neg: "b1*x+b2*y-(1-b3)*z = -vdp" unfolding vdp_def by (simp add: algebra_simps)
    have "(x - c*(-b1))^2 + (y - c*(-b2))^2 + (z - c*(1-b3))^2
        = (x^2+y^2+z^2) + c^2*d - 2*c*vdp" using h_expand hvv_d hvdp_neg by simp
    hence hiso: "(x - c*(-b1))^2 + (y - c*(-b2))^2 + (z - c*(1-b3))^2
        = (x^2+y^2+z^2)" using hcancel by linarith
    have hRp_eq: "R p = (x - c*(-b1), y - c*(-b2), z - c*(1-b3))"
    proof -
      have "R (x,y,z) = (let vdp' = -b1*x+(-b2)*y+(1-b3)*z; c' = 2*vdp'/(2-2*b3)
                         in (x-c'*(-b1), y-c'*(-b2), z-c'*(1-b3)))"
        unfolding R_expand by simp
      also have "\<dots> = (x - (2*vdp/d)*(-b1), y - (2*vdp/d)*(-b2), z - (2*vdp/d)*(1-b3))"
        unfolding Let_def vdp_def d_def by simp
      finally show ?thesis unfolding hxyz c_def .
    qed
    hence "fst (R p)^2 + fst(snd(R p))^2 + snd(snd(R p))^2 = 1"
      using hiso hp_S2 by simp
    thus "R p \<in> top1_S2" unfolding top1_S2_def by (cases "R p", cases "snd(R p)") auto
  qed
  have hR_inv: "\<And>p. R (R p) = p"
  proof -
    fix p obtain x y z :: real where hxyz: "p = (x, y, z)" by (cases p, cases "snd p") auto
    define vdp where "vdp = -b1*x + (-b2)*y + (1-b3)*z"
    define d where "d = (2-2*b3::real)"
    define c where "c = 2*vdp/d"
    have hd_ne: "d \<noteq> 0" unfolding d_def using hb3_ne1 by linarith
    have hvv_d: "b1^2+b2^2+(1-b3)^2 = d" unfolding d_def
      using hb_S2 by (simp add: power2_eq_square algebra_simps)
    have hcd: "c * d = 2*vdp" unfolding c_def using hd_ne by simp
    let ?x' = "x-c*(-b1)" and ?y' = "y-c*(-b2)" and ?z' = "z-c*(1-b3)"
    have hRp_eq: "R p = (?x', ?y', ?z')"
    proof -
      have "R (x,y,z) = (let v = -b1*x+(-b2)*y+(1-b3)*z; cc = 2*v/(2-2*b3)
                         in (x-cc*(-b1), y-cc*(-b2), z-cc*(1-b3)))"
        unfolding R_expand by simp
      also have "\<dots> = (x-(2*vdp/d)*(-b1), y-(2*vdp/d)*(-b2), z-(2*vdp/d)*(1-b3))"
        unfolding Let_def vdp_def d_def by simp
      finally show ?thesis unfolding hxyz c_def .
    qed
    define vdp' where "vdp' = -b1*?x' + (-b2)*?y' + (1-b3)*?z'"
    have "vdp' = vdp - c*(b1^2+b2^2+(1-b3)^2)"
      unfolding vdp'_def vdp_def by (simp add: power2_eq_square algebra_simps)
    hence "vdp' = vdp - c*d" using hvv_d by simp
    hence hvdp'_val: "vdp' = -vdp" using hcd by linarith
    define c' where "c' = 2*vdp'/d"
    have hc'_val: "c' = -c"
      unfolding c'_def c_def using hvdp'_val by simp
    have "R (R p) = (?x'-c'*(-b1), ?y'-c'*(-b2), ?z'-c'*(1-b3))"
    proof -
      have "R (?x', ?y', ?z') = (let v = -b1*?x'+(-b2)*?y'+(1-b3)*?z'; cc = 2*v/(2-2*b3)
                                 in (?x'-cc*(-b1), ?y'-cc*(-b2), ?z'-cc*(1-b3)))"
        unfolding R_expand by simp
      also have "\<dots> = (?x'-(2*vdp'/d)*(-b1), ?y'-(2*vdp'/d)*(-b2), ?z'-(2*vdp'/d)*(1-b3))"
        unfolding Let_def vdp'_def d_def by simp
      also have "\<dots> = (?x'-c'*(-b1), ?y'-c'*(-b2), ?z'-c'*(1-b3))"
        unfolding c'_def by simp
      finally show ?thesis using hRp_eq by simp
    qed
    also have "\<dots> = (x, y, z)" using hc'_val by simp
    finally show "R (R p) = p" unfolding hxyz .
  qed
  have hR_cont: "continuous_on UNIV R"
  proof -
    define vf :: "real \<times> real \<times> real \<Rightarrow> real" where
      "vf = (\<lambda>p. -b1*fst p + (-b2)*fst(snd p) + (1-b3)*snd(snd p))"
    define d where "d = (2-2*b3::real)"
    have hd_ne: "d \<noteq> 0" unfolding d_def using hb3_ne1 by linarith
    have hvf_cont: "continuous_on UNIV vf" unfolding vf_def by (intro continuous_intros)
    define R' :: "real \<times> real \<times> real \<Rightarrow> real \<times> real \<times> real" where
      "R' = (\<lambda>p. (fst p + 2*vf p/d*b1, fst(snd p) + 2*vf p/d*b2,
                  snd(snd p) - 2*vf p/d*(1-b3)))"
    have hR_eq: "R = R'" unfolding R_expand R'_def vf_def d_def Let_def
      by (rule ext) (simp add: case_prod_unfold)
    have "continuous_on UNIV R'" unfolding R'_def
      by (intro continuous_intros hvf_cont) (simp_all add: hd_ne)
    thus ?thesis using hR_eq by simp
  qed
  \<comment> \<open>R restricts to homeomorphism S^2 \<rightarrow> S^2.\<close>
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
  have hR_bij: "bij_betw R top1_S2 top1_S2"
    unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on R top1_S2"
      by (rule inj_onI) (metis hR_inv)
    show "R ` top1_S2 = top1_S2"
    proof (rule set_eqI, rule iffI)
      fix q assume "q \<in> R ` top1_S2"
      then obtain p where "p \<in> top1_S2" "q = R p" by blast
      thus "q \<in> top1_S2" using hR_S2 by simp
    next
      fix q assume hq: "q \<in> top1_S2"
      hence "R q \<in> top1_S2" by (rule hR_S2)
      moreover have "R (R q) = q" by (rule hR_inv)
      ultimately show "q \<in> R ` top1_S2" by (metis image_eqI)
    qed
  qed
  have hR_inv_eq: "\<And>p. p \<in> top1_S2 \<Longrightarrow> inv_into top1_S2 R p = R p"
  proof -
    fix p assume hp: "p \<in> top1_S2"
    have "R p \<in> top1_S2" by (rule hR_S2[OF hp])
    moreover have "R (R p) = p" by (rule hR_inv)
    ultimately show "inv_into top1_S2 R p = R p"
      using hR_bij unfolding bij_betw_def by (intro inv_into_f_eq) auto
  qed
  \<comment> \<open>Bridge: continuous_on UNIV R \<Rightarrow> top1_continuous_map_on S^2 TS2 S^2 TS2 R.\<close>
  have hR_top1_cont: "top1_continuous_map_on top1_S2 top1_S2_topology top1_S2 top1_S2_topology R"
  proof -
    have hR_cont_S2: "continuous_on top1_S2 R"
      using continuous_on_subset[OF hR_cont] by (by100 blast)
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix p assume "p \<in> top1_S2" thus "R p \<in> top1_S2" by (rule hR_S2)
    next
      fix V assume hV: "V \<in> top1_S2_topology"
      then obtain W where hW: "W \<in> product_topology_on top1_open_sets
            (product_topology_on top1_open_sets top1_open_sets)"
          and hVeq: "V = top1_S2 \<inter> W"
        unfolding top1_S2_topology_def subspace_topology_def by (by100 blast)
      have "W \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
        using hW product_topology_on_open_sets by metis
      hence hWopen: "open W" unfolding top1_open_sets_def by (by100 blast)
      obtain U where hUopen: "open U" and hUeq: "U \<inter> top1_S2 = R -` W \<inter> top1_S2"
        using iffD1[OF continuous_on_open_invariant hR_cont_S2] hWopen by auto
      have "{p \<in> top1_S2. R p \<in> V} = {p \<in> top1_S2. R p \<in> W}"
        unfolding hVeq using hR_S2 by (by100 auto)
      also have "\<dots> = R -` W \<inter> top1_S2" by (by100 auto)
      also have "\<dots> = U \<inter> top1_S2" using hUeq by simp
      finally have heq: "{p \<in> top1_S2. R p \<in> V} = top1_S2 \<inter> U" by (by100 blast)
      have "U \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
        using hUopen unfolding top1_open_sets_def by (by100 blast)
      hence "U \<in> product_topology_on top1_open_sets
          (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_open_sets by metis
      hence "top1_S2 \<inter> U \<in> top1_S2_topology"
        unfolding top1_S2_topology_def subspace_topology_def by (by100 blast)
      thus "{p \<in> top1_S2. R p \<in> V} \<in> top1_S2_topology" using heq by simp
    qed
  qed
  have hR_homeo: "top1_homeomorphism_on top1_S2 top1_S2_topology top1_S2 top1_S2_topology R"
    unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on top1_S2 top1_S2_topology" by (rule hTS2)
    show "is_topology_on top1_S2 top1_S2_topology" by (rule hTS2)
    show "bij_betw R top1_S2 top1_S2" by (rule hR_bij)
    show "top1_continuous_map_on top1_S2 top1_S2_topology top1_S2 top1_S2_topology R"
      by (rule hR_top1_cont)
    show "top1_continuous_map_on top1_S2 top1_S2_topology top1_S2 top1_S2_topology (inv_into top1_S2 R)"
    proof -
      have "\<And>p. p \<in> top1_S2 \<Longrightarrow> inv_into top1_S2 R p = R p" by (rule hR_inv_eq)
      hence "\<And>V. V \<in> top1_S2_topology \<Longrightarrow>
          {p \<in> top1_S2. inv_into top1_S2 R p \<in> V} = {p \<in> top1_S2. R p \<in> V}"
        by auto
      thus ?thesis using hR_top1_cont hR_S2 hR_inv_eq
        unfolding top1_continuous_map_on_def by auto
    qed
  qed
  have hR_homeo_minus: "top1_homeomorphism_on (top1_S2 - {b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
      (top1_S2 - {north_pole})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) R"
    unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) simp
    show "is_topology_on (top1_S2 - {north_pole}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
      by (rule subspace_topology_is_topology_on[OF hTS2]) simp
    show hbij: "bij_betw R (top1_S2 - {b}) (top1_S2 - {north_pole})"
      unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on R (top1_S2 - {b})"
        by (rule inj_onI) (metis hR_inv)
      show "R ` (top1_S2 - {b}) = top1_S2 - {north_pole}"
      proof (rule set_eqI, rule iffI)
        fix q assume "q \<in> R ` (top1_S2 - {b})"
        then obtain p where hp: "p \<in> top1_S2 - {b}" "q = R p" by blast
        have "q \<in> top1_S2" using hp hR_S2 by (by100 blast)
        moreover have "q \<noteq> north_pole"
        proof
          assume "q = north_pole"
          hence "R p = north_pole" using hp by simp
          hence "R (R p) = R north_pole" by simp
          hence "p = R north_pole" using hR_inv by simp
          hence "R p = R (R north_pole)" by simp
          hence "R p = north_pole" using hR_inv by simp
          hence "p = b" using hR_b_N hR_inv
            by (metis \<open>R p = north_pole\<close>)
          thus False using hp by simp
        qed
        ultimately show "q \<in> top1_S2 - {north_pole}" by simp
      next
        fix q assume hq: "q \<in> top1_S2 - {north_pole}"
        have "R q \<in> top1_S2" using hq hR_S2 by (by100 blast)
        moreover have "R q \<noteq> b"
        proof
          assume "R q = b"
          hence "R (R q) = R b" by simp
          hence "q = north_pole" using hR_inv hR_b_N by simp
          thus False using hq by simp
        qed
        ultimately have "R q \<in> top1_S2 - {b}" by simp
        moreover have "R (R q) = q" by (rule hR_inv)
        ultimately show "q \<in> R ` (top1_S2 - {b})" by (metis image_eqI)
      qed
    qed
    have hR_not_N: "\<And>p. p \<in> top1_S2 - {b} \<Longrightarrow> R p \<noteq> north_pole"
    proof -
      fix p assume hp: "p \<in> top1_S2 - {b}"
      show "R p \<noteq> north_pole"
      proof
        assume "R p = north_pole"
        hence "R p = R b" using hR_b_N by simp
        hence "p = b" by (metis hR_inv)
        thus False using hp by simp
      qed
    qed
    \<comment> \<open>Continuity: restrict hR_top1_cont to subspaces.\<close>
    show "top1_continuous_map_on (top1_S2 - {b})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
        (top1_S2 - {north_pole})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})) R"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix p assume hp: "p \<in> top1_S2 - {b}"
      thus "R p \<in> top1_S2 - {north_pole}" using hbij unfolding bij_betw_def by (by100 blast)
    next
      fix V assume hV: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
      then obtain W where hW: "W \<in> top1_S2_topology" and hVeq: "V = (top1_S2 - {north_pole}) \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      have "{p \<in> top1_S2 - {b}. R p \<in> V} = (top1_S2 - {b}) \<inter> {p \<in> top1_S2. R p \<in> W}"
        unfolding hVeq using hR_S2 hR_not_N by (by100 auto)
      moreover have "{p \<in> top1_S2. R p \<in> W} \<in> top1_S2_topology"
        using hR_top1_cont hW unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show "{p \<in> top1_S2 - {b}. R p \<in> V} \<in>
          subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
        unfolding subspace_topology_def by (by100 blast)
    qed
    \<comment> \<open>Inverse continuity: inv_into = R (involution), same as forward.\<close>
    show "top1_continuous_map_on (top1_S2 - {north_pole})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
        (top1_S2 - {b})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
        (inv_into (top1_S2 - {b}) R)"
    proof -
      have hR_not_b: "\<And>p. p \<in> top1_S2 - {north_pole} \<Longrightarrow> R p \<noteq> b"
        by (metis DiffD2 hR_b_N hR_inv singletonI)
      have hinv_R: "\<And>p. p \<in> top1_S2 - {north_pole} \<Longrightarrow>
          inv_into (top1_S2 - {b}) R p = R p"
      proof -
        fix p assume hp: "p \<in> top1_S2 - {north_pole}"
        have "R p \<in> top1_S2 - {b}"
        proof -
          have "R p \<in> top1_S2" using hp hR_S2 by (by100 blast)
          moreover have "R p \<noteq> b"
          proof
            assume "R p = b"
            hence "R (R p) = R b" by simp
            hence "p = north_pole" using hR_inv hR_b_N by simp
            thus False using hp by simp
          qed
          ultimately show ?thesis by simp
        qed
        moreover have "R (R p) = p" by (rule hR_inv)
        ultimately show "inv_into (top1_S2 - {b}) R p = R p"
          using hbij unfolding bij_betw_def by (intro inv_into_f_eq) auto
      qed
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix p assume hp: "p \<in> top1_S2 - {north_pole}"
        show "inv_into (top1_S2 - {b}) R p \<in> top1_S2 - {b}"
          using hinv_R[OF hp] hp hR_S2 hR_not_b[OF hp] by auto
      next
        fix V assume hV: "V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
        then obtain W where hW: "W \<in> top1_S2_topology" and hVeq: "V = (top1_S2 - {b}) \<inter> W"
          unfolding subspace_topology_def by (by100 blast)
        have "{p \<in> top1_S2 - {north_pole}. inv_into (top1_S2 - {b}) R p \<in> V}
            = (top1_S2 - {north_pole}) \<inter> {p \<in> top1_S2. R p \<in> W}"
          unfolding hVeq using hinv_R hR_S2 hR_not_b by auto
        moreover have "{p \<in> top1_S2. R p \<in> W} \<in> top1_S2_topology"
          using hR_top1_cont hW unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "{p \<in> top1_S2 - {north_pole}. inv_into (top1_S2 - {b}) R p \<in> V} \<in>
            subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
          unfolding subspace_topology_def by (by100 blast)
      qed
    qed
  qed
  show ?thesis using hR_homeo_minus unfolding R_def .
qed

lemma S2_minus_point_simply_connected:
  assumes "b \<in> top1_S2"
  shows "top1_simply_connected_on (top1_S2 - {b})
           (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))"
proof (cases "b = north_pole")
  case True thus ?thesis using S2_minus_north_pole_simply_connected by simp
next
  case False
  show ?thesis
    by (rule homeomorphism_preserves_simply_connected[OF
        householder_S2_homeo[OF assms] S2_minus_north_pole_simply_connected])
qed

text \<open>A simple closed curve in X: image of a continuous injective map S^1 \<rightarrow> X.
  (Moved before \<S>61 to avoid forward reference.)\<close>
definition top1_simple_closed_curve_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_simple_closed_curve_on X TX C \<longleftrightarrow>
     (\<exists>f. top1_continuous_map_on top1_S1 top1_S1_topology X TX f
          \<and> inj_on f top1_S1
          \<and> f ` top1_S1 = C)"

lemma simple_closed_curve_subset:
  "top1_simple_closed_curve_on X TX C \<Longrightarrow> C \<subseteq> X"
  unfolding top1_simple_closed_curve_on_def top1_continuous_map_on_def
  by (by100 blast)

text \<open>S^2 minus two distinct points is not simply connected (homeomorphic to R^2 - {0}).\<close>
lemma R2_minus_origin_not_simply_connected:
  "\<not> top1_simply_connected_on (UNIV - {(0::real, 0::real)})
     (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))"
proof
  assume hsc: "top1_simply_connected_on (UNIV - {(0::real, 0::real)})
     (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))"
  let ?TR2_0 = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0::real, 0::real)})"
  \<comment> \<open>Simply connected means all loops at (1,0) are contractible in R^2-{0}.\<close>
  have h10_R2: "(1::real, 0::real) \<in> UNIV - {(0, 0)}" by simp
  have h_all_trivial: "\<forall>f. top1_is_loop_on (UNIV - {(0::real, 0)}) ?TR2_0 (1, 0) f
      \<longrightarrow> top1_path_homotopic_on (UNIV - {(0, 0)}) ?TR2_0 (1, 0) (1, 0) f (top1_constant_path (1, 0))"
    using hsc h10_R2 unfolding top1_simply_connected_on_def by (by100 blast)
  \<comment> \<open>In particular, the standard loop p0(s) = (cos 2\<pi>s, sin 2\<pi>s) on S^1 \<subseteq> R^2-{0}
     is a loop at (1,0) in R^2-{0}. By simply connected, it's contractible.\<close>
  let ?p0 = "\<lambda>s::real. (cos (2 * pi * s), sin (2 * pi * s))"
  have hp0_loop_R2: "top1_is_loop_on (UNIV - {(0, 0)}) ?TR2_0 (1::real, 0::real) ?p0"
  proof -
    have hp0_R2: "\<forall>s\<in>I_set. ?p0 s \<in> UNIV - {(0::real, 0)}"
    proof
      fix s :: real assume "s \<in> I_set"
      have "cos (2 * pi * s) ^ 2 + sin (2 * pi * s) ^ 2 = 1"
        using sin_cos_squared_add[of "2 * pi * s"] by (simp add: power2_eq_square)
      hence "?p0 s \<noteq> (0, 0)"
      proof -
        assume h1: "cos (2 * pi * s) ^ 2 + sin (2 * pi * s) ^ 2 = 1"
        show ?thesis
        proof
          assume h0: "?p0 s = (0, 0)"
          hence "cos (2 * pi * s) = 0" "sin (2 * pi * s) = 0" by (simp_all add: prod_eq_iff)
          hence "cos (2 * pi * s) ^ 2 + sin (2 * pi * s) ^ 2 = 0" by simp
          thus False using h1 by simp
        qed
      qed
      thus "?p0 s \<in> UNIV - {(0, 0)}" by simp
    qed
    have hp0_cont: "continuous_on UNIV ?p0" by (intro continuous_intros)
    have hp0_cont_I: "continuous_on I_set ?p0"
      using continuous_on_subset[OF hp0_cont] by (by100 blast)
    have hp0_top1: "top1_continuous_map_on I_set I_top (UNIV - {(0::real, 0)}) ?TR2_0 ?p0"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set" thus "?p0 s \<in> UNIV - {(0::real, 0)}" using hp0_R2 by (by100 blast)
    next
      fix V assume hV: "V \<in> ?TR2_0"
      then obtain W where hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
          and hVeq: "V = (UNIV - {(0, 0)}) \<inter> W"
        unfolding subspace_topology_def by (by100 auto)
      have hWo: "open W"
      proof -
        have "W \<in> (top1_open_sets :: (real \<times> real) set set)"
          using hW product_topology_on_open_sets_real2 by (by100 metis)
        thus ?thesis unfolding top1_open_sets_def by (by100 blast)
      qed
      have "{s \<in> I_set. ?p0 s \<in> V} = I_set \<inter> ?p0 -` W"
        unfolding hVeq using hp0_R2 by (by100 auto)
      moreover have "open (?p0 -` W)"
      proof -
        have "open (?p0 -` W \<inter> UNIV)"
          using iffD1[OF continuous_on_open_vimage[OF open_UNIV] hp0_cont] hWo by (by100 blast)
        thus ?thesis by simp
      qed
      hence "?p0 -` W \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
      ultimately show "{s \<in> I_set. ?p0 s \<in> V} \<in> I_top"
        unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
    qed
    show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
      using hp0_top1 by simp
  qed
  have hp0_contractible: "top1_path_homotopic_on (UNIV - {(0, 0)}) ?TR2_0 (1, 0) (1, 0)
      ?p0 (top1_constant_path (1, 0))"
    using h_all_trivial hp0_loop_R2 by (by100 blast)
  \<comment> \<open>But p0 is also a loop on S^1 (since cos^2 + sin^2 = 1). Under the inclusion S^1 \<hookrightarrow> R^2-{0},
     p0 contractible in R^2-{0} implies p0 contractible in S^1 (by retraction r(x)=x/|x|).\<close>
  \<comment> \<open>Then π₁(S¹) would be trivial. But π₁(S¹) ≅ ℤ (Theorem_54_5). Contradiction.\<close>
  \<comment> \<open>Actually: use the retraction r(x) = x/|x| to transfer the homotopy to S^1.\<close>
  have hp0_contractible_S1: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
      ?p0 (top1_constant_path (1, 0))"
  proof -
    \<comment> \<open>Use retraction r(x) = x/|x| from R^2-{0} to S^1. r continuous, r|S^1 = id.
       hp0_contractible gives p0 ≃ const in R^2-{0}.
       Apply r: r∘p0 ≃ r∘const in S^1. r∘p0 = p0 (on S^1), r∘const = const.\<close>
    let ?norm = "\<lambda>x::real\<times>real. sqrt (fst x ^ 2 + snd x ^ 2)"
    let ?r = "\<lambda>x::real\<times>real. (fst x / ?norm x, snd x / ?norm x)"
    \<comment> \<open>r fixes S^1.\<close>
    have hr_fix: "\<And>x. x \<in> top1_S1 \<Longrightarrow> ?r x = x"
      unfolding top1_S1_def by auto
    \<comment> \<open>r maps R^2-{0} to S^1.\<close>
    have hr_S1: "\<And>x. x \<in> UNIV - {(0::real, 0)} \<Longrightarrow> ?r x \<in> top1_S1"
    proof -
      fix x :: "real \<times> real" assume hx: "x \<in> UNIV - {(0, 0)}"
      hence hx_ne: "fst x \<noteq> 0 \<or> snd x \<noteq> 0" by (auto simp: prod_eq_iff)
      hence hsum_pos: "fst x ^ 2 + snd x ^ 2 > 0"
        using sum_power2_gt_zero_iff[of "fst x" "snd x"] by blast
      hence hnorm_pos: "?norm x > 0" by simp
      have hns: "(?norm x) ^ 2 = fst x ^ 2 + snd x ^ 2"
      proof -
        have "(?norm x) ^ 2 = ?norm x * ?norm x" by (simp add: power2_eq_square)
        also have "\<dots> = \<bar>fst x ^ 2 + snd x ^ 2\<bar>" by (simp add: power2_eq_square real_sqrt_mult_self)
        also have "\<dots> = fst x ^ 2 + snd x ^ 2" using hsum_pos by simp
        finally show ?thesis .
      qed
      have hnorm_ne: "?norm x \<noteq> 0" using hnorm_pos by (by100 linarith)
      have "(fst x / ?norm x) ^ 2 + (snd x / ?norm x) ^ 2 = 1"
      proof -
        have hne: "fst x ^ 2 + snd x ^ 2 \<noteq> 0" using hsum_pos by (by100 linarith)
        have "fst x ^ 2 / (fst x ^ 2 + snd x ^ 2) + snd x ^ 2 / (fst x ^ 2 + snd x ^ 2) = 1"
          using hne by (simp add: add_divide_distrib[symmetric])
        thus ?thesis using hns by (simp add: power_divide)
      qed
      thus "?r x \<in> top1_S1" unfolding top1_S1_def by simp
    qed
    \<comment> \<open>r is continuous R^2-{0} \<rightarrow> S^1.\<close>
    have hr_cont: "top1_continuous_map_on (UNIV - {(0, 0)}) ?TR2_0
        top1_S1 top1_S1_topology ?r"
    proof -
      \<comment> \<open>r is continuous_on (UNIV - {(0,0)}) as a composition of continuous functions.\<close>
      have hr_cont_on: "continuous_on (UNIV - {(0::real, 0)}) ?r"
      proof (intro continuous_on_Pair)
        show "continuous_on (UNIV - {(0::real, 0)}) (\<lambda>x. fst x / ?norm x)"
          by (intro continuous_intros) (auto simp: sum_power2_eq_zero_iff prod_eq_iff)
        show "continuous_on (UNIV - {(0::real, 0)}) (\<lambda>x. snd x / ?norm x)"
          by (intro continuous_intros) (auto simp: sum_power2_eq_zero_iff prod_eq_iff)
      qed
      \<comment> \<open>Transfer to top1_continuous_map_on via open_vimage.\<close>
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x :: "real \<times> real" assume hx: "x \<in> UNIV - {(0, 0)}"
        show "?r x \<in> top1_S1" using hr_S1[OF hx] .
      next
        fix V assume hV: "V \<in> top1_S1_topology"
        then obtain W where hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
            and hVeq: "V = top1_S1 \<inter> W"
          unfolding top1_S1_topology_def subspace_topology_def by (by100 auto)
        have hWo: "open W"
        proof -
          have "W \<in> (top1_open_sets :: (real \<times> real) set set)"
            using hW product_topology_on_open_sets_real2 by (by100 metis)
          thus ?thesis unfolding top1_open_sets_def by (by100 blast)
        qed
        have hR2_open: "open (UNIV - {(0::real, 0::real)})"
          by (intro open_Diff open_UNIV finite_imp_closed) simp
        have hpre: "open (?r -` W \<inter> (UNIV - {(0, 0)}))"
          using iffD1[OF continuous_on_open_vimage[OF hR2_open] hr_cont_on] hWo by (by100 blast)
        have "{x \<in> UNIV - {(0, 0)}. ?r x \<in> V} = (UNIV - {(0, 0)}) \<inter> (?r -` W)"
          unfolding hVeq using hr_S1 by (by100 auto)
        also have "\<dots> = ?r -` W \<inter> (UNIV - {(0, 0)})" by (by100 blast)
        finally have "{x \<in> UNIV - {(0, 0)}. ?r x \<in> V} = ?r -` W \<inter> (UNIV - {(0, 0)})" .
        hence hopen: "open {x \<in> UNIV - {(0, 0)}. ?r x \<in> V}" using hpre by simp
        hence hopen_os: "{x \<in> UNIV - {(0, 0)}. ?r x \<in> V} \<in> top1_open_sets"
          unfolding top1_open_sets_def by (by100 blast)
        have hsub: "{x \<in> UNIV - {(0, 0)}. ?r x \<in> V} \<subseteq> UNIV - {(0, 0)}" by (by100 blast)
        have hprod: "(product_topology_on top1_open_sets top1_open_sets :: (real \<times> real) set set)
            = top1_open_sets" using product_topology_on_open_sets_real2 by simp
        show "{x \<in> UNIV - {(0, 0)}. ?r x \<in> V} \<in> ?TR2_0"
          unfolding subspace_topology_def hprod
          using hopen_os hsub by (by100 blast)
      qed
    qed
    \<comment> \<open>Apply r to the homotopy: r∘p0 ≃ r∘const.\<close>
    have hpsi_hom: "top1_path_homotopic_on top1_S1 top1_S1_topology
        (?r (1, 0)) (?r (1, 0)) (?r \<circ> ?p0) (?r \<circ> top1_constant_path (1, 0))"
    proof -
      have hTR2_0: "is_topology_on (UNIV - {(0::real, 0)}) ?TR2_0"
        by (rule subspace_topology_is_topology_on[OF
              product_topology_on_is_topology_on[OF
                top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV, simplified]]) simp
      have hTS1_local: "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF
              product_topology_on_is_topology_on[OF
                top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
                simplified]]) simp
      show ?thesis
        by (rule continuous_preserves_path_homotopic[OF hTR2_0 hTS1_local hr_cont hp0_contractible])
    qed
    \<comment> \<open>r(1,0) = (1,0), r∘p0 = p0 (on S^1), r∘const = const.\<close>
    have hr10: "?r (1, 0) = (1, 0)" by simp
    have hr_p0: "?r \<circ> ?p0 = ?p0"
    proof (rule ext)
      fix s :: real
      show "(?r \<circ> ?p0) s = ?p0 s"
      proof -
        have "cos (2 * pi * s) ^ 2 + sin (2 * pi * s) ^ 2 = 1"
          using sin_cos_squared_add[of "2 * pi * s"] by (simp add: power2_eq_square)
        hence "?p0 s \<in> top1_S1" unfolding top1_S1_def by simp
        thus ?thesis using hr_fix by (simp add: comp_def)
      qed
    qed
    have hr_const: "?r \<circ> top1_constant_path (1, 0) = top1_constant_path (1, 0)"
      by (rule ext) (simp add: top1_constant_path_def comp_def)
    show ?thesis using hpsi_hom unfolding hr10 hr_p0 hr_const .
  qed
  \<comment> \<open>p0 is the standard generator of π₁(S¹). Its contractibility gives π₁(S¹) = 0.\<close>
  \<comment> \<open>But π₁(S¹) ≅ ℤ ≠ 0 (Theorem 54.5). Actually we can derive False more directly:
     the n-fold winding (p0 for n=1) being contractible contradicts the covering theory
     argument from FTA Step 2 (hnontrivial).\<close>
  \<comment> \<open>Use Theorem_54_3: lift of p0 from 0 ends at 1. Lift of const ends at 0.
     If they're homotopic, endpoints equal by Thm 54.3. So 1=0. Contradiction.\<close>
  \<comment> \<open>Transfer p0 contractibility from S^1 to the covering R \<rightarrow> S^1.
     Lift of p0: s \<mapsto> s, ending at 1.
     Lift of const: s \<mapsto> 0, ending at 0.
     By Thm 54.3, if p0 ≃ const then 1 = 0. Contradiction.\<close>
  have hcov: "top1_covering_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
    by (rule Theorem_53_1)
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    unfolding top1_S1_topology_def
    by (rule subspace_topology_is_topology_on[OF
          product_topology_on_is_topology_on[OF
            top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
            simplified]]) simp
  have hp0: "top1_R_to_S1 0 = (1, 0)" unfolding top1_R_to_S1_def by simp
  have h0R: "(0::real) \<in> (UNIV::real set)" by simp
  have h10S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
  \<comment> \<open>p0 as a loop on S^1: ?p0(s) = (cos 2\<pi>s, sin 2\<pi>s) = top1_R_to_S1(s).\<close>
  have hp0_eq: "\<And>s. ?p0 s = top1_R_to_S1 s"
    unfolding top1_R_to_S1_def by simp
  \<comment> \<open>p0 = R_to_S1 \<circ> id. Lift of p0 from 0 is id: s \<mapsto> s, ending at 1.\<close>
  have hp0_loop_S1: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) ?p0"
  proof -
    \<comment> \<open>?p0 maps into S^1 and is continuous. Same proof as hp0_loop_R2 but for S^1 codomain.\<close>
    have hp0_S1: "\<forall>s\<in>I_set. ?p0 s \<in> top1_S1"
      unfolding top1_S1_def
    proof
      fix s :: real assume "s \<in> I_set"
      have "cos (2 * pi * s) ^ 2 + sin (2 * pi * s) ^ 2 = 1"
        using sin_cos_squared_add[of "2 * pi * s"] by (simp add: power2_eq_square)
      thus "?p0 s \<in> {p. fst p ^ 2 + snd p ^ 2 = 1}" by simp
    qed
    have hp0_cont: "continuous_on UNIV ?p0" by (intro continuous_intros)
    have hp0_top1: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology ?p0"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set" thus "?p0 s \<in> top1_S1" using hp0_S1 by (by100 blast)
    next
      fix V assume hV: "V \<in> top1_S1_topology"
      then obtain W where hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
          and hVeq: "V = top1_S1 \<inter> W"
        using hV unfolding top1_S1_topology_def subspace_topology_def by (by100 auto)
      have hWo: "open W"
      proof -
        have "W \<in> (top1_open_sets :: (real \<times> real) set set)"
          using hW product_topology_on_open_sets_real2 by (by100 metis)
        thus ?thesis unfolding top1_open_sets_def by (by100 blast)
      qed
      have "{s \<in> I_set. ?p0 s \<in> V} = I_set \<inter> ?p0 -` W"
        unfolding hVeq using hp0_S1 by (by100 auto)
      moreover have "open (?p0 -` W)"
      proof -
        have "open (?p0 -` W \<inter> UNIV)"
          using iffD1[OF continuous_on_open_vimage[OF open_UNIV] hp0_cont] hWo by (by100 blast)
        thus ?thesis by simp
      qed
      hence "?p0 -` W \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
      ultimately show "{s \<in> I_set. ?p0 s \<in> V} \<in> I_top"
        unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
    qed
    show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
      using hp0_top1 by simp
  qed
  \<comment> \<open>If p0 ≃ const on S^1, then by Thm 54.3, lift endpoints agree: 1 = 0.\<close>
  have hft_p0: "top1_is_path_on UNIV top1_open_sets 0 1 id"
  proof -
    have hid_cont: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets id"
      unfolding top1_continuous_map_on_def top1_unit_interval_topology_def
    proof (intro conjI ballI)
      fix s :: real assume "s \<in> I_set" show "id s \<in> (UNIV::real set)" by simp
    next
      fix V :: "real set" assume "V \<in> top1_open_sets"
      have "{s \<in> I_set. id s \<in> V} = I_set \<inter> V" by auto
      also have "\<dots> \<in> subspace_topology UNIV top1_open_sets I_set"
        unfolding subspace_topology_def using \<open>V \<in> top1_open_sets\<close> by (by100 blast)
      finally show "{s \<in> I_set. id s \<in> V} \<in> subspace_topology UNIV top1_open_sets I_set" .
    qed
    show ?thesis unfolding top1_is_path_on_def using hid_cont by simp
  qed
  have hft_p0_lift: "\<forall>s\<in>I_set. top1_R_to_S1 (id s) = ?p0 s"
    using hp0_eq by simp
  have hft_const: "top1_is_path_on UNIV top1_open_sets 0 0 (\<lambda>_. 0::real)"
    unfolding top1_is_path_on_def
    using top1_continuous_map_on_const[OF top1_unit_interval_topology_is_topology_on
      top1_open_sets_is_topology_on_UNIV UNIV_I] by simp
  have hft_const_lift: "\<forall>s\<in>I_set. top1_R_to_S1 ((\<lambda>_. 0::real) s) = top1_constant_path (1, 0) s"
    unfolding top1_constant_path_def top1_R_to_S1_def by simp
  have hconst_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (top1_constant_path (1, 0))"
    using top1_constant_path_is_loop[OF hTS1 h10S1] unfolding top1_is_loop_on_def .
  have hp0_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) ?p0"
    using hp0_loop_S1 unfolding top1_is_loop_on_def .
  have "1 = (0::real)"
    using conjunct1[OF Theorem_54_3[OF hcov top1_open_sets_is_topology_on_UNIV hTS1
      h0R hp0 hp0_path hconst_path hp0_contractible_S1
      hft_p0 hft_p0_lift hft_const hft_const_lift]] .
  thus False by simp
qed

lemma R2_minus_point_not_simply_connected:
  "p \<in> (UNIV :: (real \<times> real) set) \<Longrightarrow>
   \<not> top1_simply_connected_on (UNIV - {p})
     (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {p}))"
proof -
  assume "p \<in> (UNIV :: (real \<times> real) set)"
  \<comment> \<open>Translation \<tau>(x) = x - p is a homeomorphism R^2-{p} \<rightarrow> R^2-{0}.
     Simply connected is a homotopy invariant.
     R^2-{0} is not simply connected (proved above).\<close>
  \<comment> \<open>The translation \<tau> and its inverse \<tau>^{-1}(x) = x + p are both continuous
     (as polynomial maps on R^2) and bijective UNIV-{p} \<leftrightarrow> UNIV-{0}.\<close>
  show ?thesis
  proof
    assume hsc: "top1_simply_connected_on (UNIV - {p})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {p}))"
    \<comment> \<open>Translate loop around p to loop around origin.\<close>
    let ?\<tau> = "\<lambda>x::real\<times>real. (fst x - fst p, snd x - snd p)"
    \<comment> \<open>The standard loop p0 around origin, shifted to go around p.\<close>
    let ?\<gamma> = "\<lambda>s::real. (fst p + cos (2 * pi * s), snd p + sin (2 * pi * s))"
    let ?b = "(fst p + 1, snd p)"
    have hb: "?b \<in> UNIV - {p}" by (cases p) auto
    \<comment> \<open>\<gamma> maps I_set into UNIV-{p}.\<close>
    have h\<gamma>_in: "\<forall>s\<in>I_set. ?\<gamma> s \<in> UNIV - {p}"
    proof
      fix s :: real assume "s \<in> I_set"
      have "?\<gamma> s \<noteq> p"
      proof
        assume h0: "?\<gamma> s = p"
        have hc: "cos (2 * pi * s) = 0" using h0 by (cases p) auto
        have hs: "sin (2 * pi * s) = 0" using h0 by (cases p) auto
        show False using sin_cos_squared_add3[of "2 * pi * s"] hc hs by simp
      qed
      thus "?\<gamma> s \<in> UNIV - {p}" by simp
    qed
    \<comment> \<open>\<tau>\<circ>\<gamma>(s) = (cos 2\<pi>s, sin 2\<pi>s) = p0.\<close>
    have h\<tau>\<gamma>_eq: "\<And>s. ?\<tau> (?\<gamma> s) = (cos (2 * pi * s), sin (2 * pi * s))" by simp
    \<comment> \<open>\<tau> is continuous UNIV-{p} \<rightarrow> UNIV-{0}.\<close>
    let ?Tp = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {p})"
    let ?T0 = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0::real, 0::real)})"
    have h\<tau>_cont: "top1_continuous_map_on (UNIV - {p}) ?Tp (UNIV - {(0::real, 0)}) ?T0 ?\<tau>"
    proof -
      have h\<tau>_map: "\<And>x. x \<in> UNIV - {p} \<Longrightarrow> ?\<tau> x \<in> UNIV - {(0, 0)}"
        by (cases p) auto
      have h\<tau>_cont_univ: "continuous_on (UNIV - {p}) ?\<tau>"
        by (intro continuous_intros continuous_on_subset[OF _ subset_UNIV])
      show ?thesis
        by (rule top1_continuous_map_on_real2_subspace_general[OF h\<tau>_map h\<tau>_cont_univ])
    qed
    \<comment> \<open>\<gamma> is a loop at ?b in UNIV-{p}.\<close>
    have h\<gamma>_loop: "top1_is_loop_on (UNIV - {p}) ?Tp ?b ?\<gamma>"
    proof -
      have h\<gamma>_cont_univ: "continuous_on UNIV ?\<gamma>" by (intro continuous_intros)
      have h\<gamma>_cont_I: "continuous_on I_set ?\<gamma>"
        using continuous_on_subset[OF h\<gamma>_cont_univ] by (by100 blast)
      have h\<gamma>_cont_top1: "top1_continuous_map_on I_set I_top (UNIV - {p}) ?Tp ?\<gamma>"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix s assume hs: "s \<in> I_set" thus "?\<gamma> s \<in> UNIV - {p}" using h\<gamma>_in by simp
      next
        fix V assume hV: "V \<in> ?Tp"
        then obtain W where hWo: "W \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
            and hVeq: "V = (UNIV - {p}) \<inter> W"
          unfolding subspace_topology_def by (by100 blast)
        have "W \<in> (top1_open_sets :: (real \<times> real) set set)"
          using hWo product_topology_on_open_sets_real2 by metis
        hence hWopen: "open W" unfolding top1_open_sets_def by (by100 blast)
        have hpre: "open (?\<gamma> -` W)"
          by (rule open_vimage[OF hWopen h\<gamma>_cont_univ])
        have hpre_os: "?\<gamma> -` W \<in> (top1_open_sets :: real set set)"
          using hpre unfolding top1_open_sets_def by (by100 blast)
        have "{s \<in> I_set. ?\<gamma> s \<in> V} = I_set \<inter> (?\<gamma> -` W)"
          unfolding hVeq using h\<gamma>_in by (by100 blast)
        thus "{s \<in> I_set. ?\<gamma> s \<in> V} \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def
          using hpre_os by (by100 blast)
      qed
      have h0: "?\<gamma> 0 = ?b" by simp
      have h1: "?\<gamma> 1 = ?b" by simp
      show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
        using h\<gamma>_cont_top1 h0 h1 by (by100 blast)
    qed
    \<comment> \<open>Simply connected \<Rightarrow> \<gamma> is contractible.\<close>
    have h\<gamma>_contract: "top1_path_homotopic_on (UNIV - {p}) ?Tp ?b ?b ?\<gamma> (top1_constant_path ?b)"
      using hsc hb h\<gamma>_loop unfolding top1_simply_connected_on_def by (by100 blast)
    \<comment> \<open>Apply \<tau>: \<tau>\<circ>\<gamma> contractible in UNIV-{0}.\<close>
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
    proof -
      have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
        by (rule top1_open_sets_is_topology_on_UNIV)
      show ?thesis using product_topology_on_is_topology_on[OF hTR hTR] by simp
    qed
    have hTp: "is_topology_on (UNIV - {p}) ?Tp"
      by (rule subspace_topology_is_topology_on[OF hTR2]) simp
    have hT0: "is_topology_on (UNIV - {(0::real, 0)}) ?T0"
      by (rule subspace_topology_is_topology_on[OF hTR2]) simp
    have h\<tau>\<gamma>_contract: "top1_path_homotopic_on (UNIV - {(0, 0)}) ?T0
        (?\<tau> ?b) (?\<tau> ?b) (?\<tau> \<circ> ?\<gamma>) (top1_constant_path (?\<tau> ?b))"
    proof -
      have hstep: "top1_path_homotopic_on (UNIV - {(0, 0)}) ?T0
          (?\<tau> ?b) (?\<tau> ?b) (?\<tau> \<circ> ?\<gamma>) (?\<tau> \<circ> top1_constant_path ?b)"
        by (rule continuous_preserves_path_homotopic[OF hTp hT0 h\<tau>_cont h\<gamma>_contract])
      have "?\<tau> \<circ> top1_constant_path ?b = top1_constant_path (?\<tau> ?b)"
        unfolding top1_constant_path_def by (rule ext) simp
      thus ?thesis using hstep by simp
    qed
    \<comment> \<open>\<tau> ?b = (1, 0) and \<tau>\<circ>\<gamma> = p0.\<close>
    have h\<tau>b: "?\<tau> ?b = (1::real, 0::real)" by simp
    have h\<tau>\<gamma>_p0: "?\<tau> \<circ> ?\<gamma> = (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s)))"
      by (rule ext) simp
    \<comment> \<open>So p0 is contractible in UNIV-{0} at (1,0).\<close>
    have hp0_contract: "top1_path_homotopic_on (UNIV - {(0, 0)}) ?T0
        (1, 0) (1, 0) (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) (top1_constant_path (1, 0))"
      using h\<tau>\<gamma>_contract h\<tau>b h\<tau>\<gamma>_p0 by simp
    \<comment> \<open>But R^2-{0} is not simply connected: p0 is NOT contractible.\<close>
    \<comment> \<open>Transfer: UNIV-{p} simply connected \<Rightarrow> UNIV-{0} simply connected (via \<tau> and \<tau>^{-1}).\<close>
    have hsc0: "top1_simply_connected_on (UNIV - {(0::real, 0)}) ?T0"
    proof -
      let ?\<tau>inv = "\<lambda>x::real\<times>real. (fst x + fst p, snd x + snd p)"
      have h\<tau>inv_cont: "top1_continuous_map_on (UNIV - {(0, 0)}) ?T0 (UNIV - {p}) ?Tp ?\<tau>inv"
      proof -
        have hmap: "\<And>x. x \<in> UNIV - {(0::real, 0)} \<Longrightarrow> ?\<tau>inv x \<in> UNIV - {p}"
          by (cases p) auto
        have hcont: "continuous_on (UNIV - {(0::real, 0)}) ?\<tau>inv"
          by (intro continuous_intros continuous_on_subset[OF _ subset_UNIV])
        show ?thesis
          by (rule top1_continuous_map_on_real2_subspace_general[OF hmap hcont])
      qed
      show ?thesis unfolding top1_simply_connected_on_def
      proof (intro conjI allI impI ballI)
        \<comment> \<open>Path-connected: for y1, y2 in UNIV-{0}, translate to UNIV-{p},
           find path there (path-connected), translate back.\<close>
        show "top1_path_connected_on (UNIV - {(0::real, 0)}) ?T0"
          unfolding top1_path_connected_on_def
        proof (intro conjI ballI)
          show "is_topology_on (UNIV - {(0::real, 0::real)}) ?T0" by (rule hT0)
        next
          fix y1 y2 :: "real \<times> real"
          assume hy1: "y1 \<in> UNIV - {(0, 0)}" and hy2: "y2 \<in> UNIV - {(0, 0)}"
          \<comment> \<open>Translate to UNIV-{p}, find path, translate back.\<close>
          have "?\<tau>inv y1 \<in> UNIV - {p}" "?\<tau>inv y2 \<in> UNIV - {p}"
          proof -
            { fix y :: "real \<times> real" assume hy: "y \<in> UNIV - {(0::real, 0)}"
              have "?\<tau>inv y \<noteq> p"
              proof
                assume "?\<tau>inv y = p"
                hence "y = (0::real, 0)" by (cases y, cases p) simp
                thus False using hy by simp
              qed
              hence "?\<tau>inv y \<in> UNIV - {p}" by simp }
            thus "?\<tau>inv y1 \<in> UNIV - {p}" "?\<tau>inv y2 \<in> UNIV - {p}"
              using hy1 hy2 by auto
          qed
          then obtain \<alpha> where h\<alpha>: "top1_is_path_on (UNIV - {p}) ?Tp (?\<tau>inv y1) (?\<tau>inv y2) \<alpha>"
            using hsc unfolding top1_simply_connected_on_def top1_path_connected_on_def by (by100 blast)
          have h\<tau>\<alpha>: "top1_is_path_on (UNIV - {(0, 0)}) ?T0 (?\<tau> (?\<tau>inv y1)) (?\<tau> (?\<tau>inv y2)) (?\<tau> \<circ> \<alpha>)"
          proof -
            have h\<alpha>_cont: "top1_continuous_map_on I_set I_top (UNIV - {p}) ?Tp \<alpha>"
              using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
            have h\<tau>\<alpha>_cont: "top1_continuous_map_on I_set I_top (UNIV - {(0, 0)}) ?T0 (?\<tau> \<circ> \<alpha>)"
              by (rule top1_continuous_map_on_comp[OF h\<alpha>_cont h\<tau>_cont])
            have "(\<alpha> 0) = ?\<tau>inv y1" using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
            hence h0: "(?\<tau> \<circ> \<alpha>) 0 = ?\<tau> (?\<tau>inv y1)" by simp
            have "(\<alpha> 1) = ?\<tau>inv y2" using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
            hence h1: "(?\<tau> \<circ> \<alpha>) 1 = ?\<tau> (?\<tau>inv y2)" by simp
            show ?thesis unfolding top1_is_path_on_def
              using h\<tau>\<alpha>_cont h0 h1 by (by100 blast)
          qed
          have "?\<tau> (?\<tau>inv y1) = y1" "?\<tau> (?\<tau>inv y2) = y2" by simp_all
          thus "\<exists>f. top1_is_path_on (UNIV - {(0, 0)}) ?T0 y1 y2 f"
            using h\<tau>\<alpha> by (intro exI[of _ "?\<tau> \<circ> \<alpha>"]) simp
        qed
      next
        \<comment> \<open>All loops contractible: loop in UNIV-{0}, translate to UNIV-{p},
           contract (simply connected), translate back.\<close>
        fix y0 :: "real \<times> real" and g
        assume hy0: "y0 \<in> UNIV - {(0::real, 0)}"
        assume hg: "top1_is_loop_on (UNIV - {(0, 0)}) ?T0 y0 g"
        \<comment> \<open>Translate: \<tau>inv\<circ>g is a loop at \<tau>inv(y0) in UNIV-{p}.\<close>
        have h\<tau>inv_y0: "?\<tau>inv y0 \<in> UNIV - {p}"
        proof -
          have "?\<tau>inv y0 \<noteq> p"
          proof
            assume heq: "?\<tau>inv y0 = p"
            have h1: "fst y0 = 0" using heq by (cases p, cases y0) simp
            have h2: "snd y0 = 0" using heq by (cases p, cases y0) simp
            have "y0 = (0::real, 0::real)" using h1 h2 by (cases y0) simp
            thus False using hy0 by simp
          qed
          thus ?thesis by simp
        qed
        have h\<tau>inv_g: "top1_is_loop_on (UNIV - {p}) ?Tp (?\<tau>inv y0) (?\<tau>inv \<circ> g)"
          using top1_continuous_map_loop_early[OF h\<tau>inv_cont hg] by simp
        \<comment> \<open>Contract in UNIV-{p}.\<close>
        have hg_contract: "top1_path_homotopic_on (UNIV - {p}) ?Tp
            (?\<tau>inv y0) (?\<tau>inv y0) (?\<tau>inv \<circ> g) (top1_constant_path (?\<tau>inv y0))"
          using hsc h\<tau>inv_y0 h\<tau>inv_g unfolding top1_simply_connected_on_def by (by100 blast)
        \<comment> \<open>Translate back via \<tau>.\<close>
        have h\<tau>_contract: "top1_path_homotopic_on (UNIV - {(0, 0)}) ?T0
            (?\<tau> (?\<tau>inv y0)) (?\<tau> (?\<tau>inv y0))
            (?\<tau> \<circ> (?\<tau>inv \<circ> g)) (?\<tau> \<circ> top1_constant_path (?\<tau>inv y0))"
          by (rule continuous_preserves_path_homotopic[OF hTp hT0 h\<tau>_cont hg_contract])
        have h\<tau>\<tau>inv_y0: "?\<tau> (?\<tau>inv y0) = y0" by simp
        have h\<tau>\<tau>inv_g: "?\<tau> \<circ> (?\<tau>inv \<circ> g) = g" by (rule ext) simp
        have h\<tau>_const: "?\<tau> \<circ> top1_constant_path (?\<tau>inv y0) = top1_constant_path y0"
          unfolding top1_constant_path_def by (rule ext) simp
        show "top1_path_homotopic_on (UNIV - {(0, 0)}) ?T0 y0 y0 g (top1_constant_path y0)"
          using h\<tau>_contract h\<tau>\<tau>inv_y0 h\<tau>\<tau>inv_g h\<tau>_const by simp
      qed
    qed
    show False using R2_minus_origin_not_simply_connected hsc0 by (by100 blast)
  qed
qed

lemma top1_path_connected_imp_connected:
  assumes "top1_path_connected_on X TX"
  shows "top1_connected_on X TX"
proof -
  have hTX: "is_topology_on X TX" using assms unfolding top1_path_connected_on_def by (by100 blast)
  show ?thesis unfolding top1_connected_on_def
  proof (intro conjI hTX)
    show "\<nexists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain U V where hUV: "U \<in> TX" "V \<in> TX" "U \<noteq> {}" "V \<noteq> {}" "U \<inter> V = {}" "U \<union> V = X"
        by (by100 blast)
      obtain u where hu: "u \<in> U" using hUV(3) by (by100 blast)
      obtain v where hv: "v \<in> V" using hUV(4) by (by100 blast)
      have huX: "u \<in> X" using hu hUV(6) by (by100 blast)
      have hvX: "v \<in> X" using hv hUV(6) by (by100 blast)
      \<comment> \<open>By path-connectedness, \<exists>path from u to v in X.\<close>
      obtain f where hf: "top1_is_path_on X TX u v f"
        using assms huX hvX unfolding top1_path_connected_on_def by (by100 blast)
      \<comment> \<open>f: [0,1] \<rightarrow> X continuous. [0,1] connected. So f([0,1]) connected.\<close>
      have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
        using hf unfolding top1_is_path_on_def by (by100 blast)
      have hf0: "f 0 = u" and hf1: "f 1 = v"
        using hf unfolding top1_is_path_on_def by (by100 blast)+
      have hI_conn: "top1_connected_on I_set I_top"
      proof -
        have hI_01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
          by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
        have "connected {0..1::real}" by (rule connected_Icc)
        hence "connected I_set" using hI_01 by simp
        thus ?thesis
          unfolding top1_unit_interval_topology_def
          using top1_connected_on_subspace_openI by (by100 blast)
      qed
      have hI_top: "is_topology_on I_set I_top"
        using hI_conn unfolding top1_connected_on_def by (by100 blast)
      have hfI_conn: "top1_connected_on (f ` I_set) (subspace_topology X TX (f ` I_set))"
        by (rule Theorem_23_5[OF hI_top hTX hI_conn hf_cont])
      \<comment> \<open>f(I) \<subseteq> X = U \<union> V, f(I) \<inter> U \<noteq> {}, f(I) \<inter> V \<noteq> {}.\<close>
      have hfI_sub: "f ` I_set \<subseteq> X"
        using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
      have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by auto
      have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by auto
      have hfI_U: "f ` I_set \<inter> U \<noteq> {}" using hf0 h0I hu by (by100 blast)
      have hfI_V: "f ` I_set \<inter> V \<noteq> {}" using hf1 h1I hv by (by100 blast)
      \<comment> \<open>f(I) \<inter> U and f(I) \<inter> V are open in subspace topology of f(I).\<close>
      have hfI_U_open: "f ` I_set \<inter> U \<in> subspace_topology X TX (f ` I_set)"
        unfolding subspace_topology_def using hUV(1) by (by100 blast)
      have hfI_V_open: "f ` I_set \<inter> V \<in> subspace_topology X TX (f ` I_set)"
        unfolding subspace_topology_def using hUV(2) by (by100 blast)
      have hfI_disj: "(f ` I_set \<inter> U) \<inter> (f ` I_set \<inter> V) = {}" using hUV(5) by (by100 blast)
      have hfI_cover: "(f ` I_set \<inter> U) \<union> (f ` I_set \<inter> V) = f ` I_set"
        using hfI_sub hUV(6) by (by100 blast)
      \<comment> \<open>This contradicts f(I) being connected.\<close>
      have "\<exists>U' V'. U' \<in> subspace_topology X TX (f ` I_set)
          \<and> V' \<in> subspace_topology X TX (f ` I_set)
          \<and> U' \<noteq> {} \<and> V' \<noteq> {} \<and> U' \<inter> V' = {} \<and> U' \<union> V' = f ` I_set"
        apply (rule exI[of _ "f ` I_set \<inter> U"])
        apply (rule exI[of _ "f ` I_set \<inter> V"])
        using hfI_U_open hfI_V_open hfI_U hfI_V hfI_disj hfI_cover by (by100 blast)
      thus False using hfI_conn unfolding top1_connected_on_def by (by100 blast)
    qed
  qed
qed

text \<open>Helper: straight-line path in R^2.\<close>
text \<open>Helper: membership in subspace topology via explicit witness.\<close>
lemma subspace_topology_memI:
  "U \<in> T \<Longrightarrow> Y \<inter> U \<in> subspace_topology X T Y"
  unfolding subspace_topology_def by blast

lemma R2_straight_line_path:
  fixes x y :: "real \<times> real"
  defines "\<gamma> \<equiv> (\<lambda>t. ((1-t) * fst x + t * fst y, (1-t) * snd x + t * snd y))"
  shows "top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) x y \<gamma>"
  unfolding top1_is_path_on_def
proof (intro conjI)
  show "top1_continuous_map_on I_set I_top UNIV (product_topology_on top1_open_sets top1_open_sets) \<gamma>"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix t assume "t \<in> I_set" show "\<gamma> t \<in> UNIV" by simp
  next
    fix V :: "(real \<times> real) set"
    assume hV: "V \<in> product_topology_on (top1_open_sets :: real set set) (top1_open_sets :: real set set)"
    have hVo: "open V"
      using hV product_topology_on_open_sets_real2 unfolding top1_open_sets_def
      by (by100 simp)
    have "continuous_on UNIV \<gamma>" unfolding \<gamma>_def by (intro continuous_intros)
    hence "open (\<gamma> -` V)" using hVo
      by (simp add: continuous_on_open_vimage[OF open_UNIV])
    hence "\<gamma> -` V \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
    have hpre_eq: "{t \<in> I_set. \<gamma> t \<in> V} = I_set \<inter> \<gamma> -` V" by (by100 blast)
    have "I_set \<inter> \<gamma> -` V \<in> subspace_topology UNIV (top1_open_sets :: real set set) I_set"
      unfolding subspace_topology_def
      apply (rule CollectI) apply (rule exI[of _ "\<gamma> -` V"])
      using \<open>\<gamma> -` V \<in> top1_open_sets\<close> by (by100 blast)
    thus "{t \<in> I_set. \<gamma> t \<in> V} \<in> I_top"
      unfolding top1_unit_interval_topology_def hpre_eq by simp
  qed
  show "\<gamma> 0 = x" unfolding \<gamma>_def by simp
  show "\<gamma> 1 = y" unfolding \<gamma>_def by simp
qed

lemma R2_minus_point_path_connected:
  "p \<in> (UNIV :: (real \<times> real) set) \<Longrightarrow>
   top1_path_connected_on (UNIV - {p})
     (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {p}))"
proof -
  assume hp: "p \<in> (UNIV :: (real \<times> real) set)"
  let ?R2 = "product_topology_on (top1_open_sets :: real set set) top1_open_sets"
  let ?S = "UNIV - {p} :: (real \<times> real) set"
  let ?TS = "subspace_topology UNIV ?R2 ?S"
  have hTR2: "is_topology_on (UNIV :: (real \<times> real) set) ?R2"
  proof -
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    show ?thesis using product_topology_on_is_topology_on[OF hTR hTR] by simp
  qed
  have hTS: "is_topology_on ?S ?TS"
    by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
  show "top1_path_connected_on ?S ?TS"
    unfolding top1_path_connected_on_def
  proof (intro conjI hTS ballI)
    fix x y assume hx: "x \<in> ?S" and hy: "y \<in> ?S"
    hence hxp: "x \<noteq> p" and hyp: "y \<noteq> p" by auto
    \<comment> \<open>Construct path from x to y avoiding p.
       Case 1 (x = y): constant path at x avoids p since x \<noteq> p.
       Case 2 (x \<noteq> y, p not on line(x,y)): straight line x\<rightarrow>y avoids p.
       Case 3 (x \<noteq> y, p on line(x,y)): detour via z = x + perp(y-x),
         which is off line(x,y). Segment x\<rightarrow>z avoids p since intersection
         of line(x,z) with line(x,y) is only x, and x \<noteq> p. Similarly z\<rightarrow>y.\<close>
    \<comment> \<open>We construct the path and prove avoidance together.\<close>
    \<comment> \<open>Define straight-line and detour paths.\<close>
    define \<gamma>_straight where "\<gamma>_straight = (\<lambda>t::real. ((1-t) * fst x + t * fst y, (1-t) * snd x + t * snd y))"
    define dx dy where "dx = fst y - fst x" and "dy = snd y - snd x"
    define z :: "real \<times> real" where "z = (fst x - dy, snd x + dx)"
    define \<gamma>1 where "\<gamma>1 = (\<lambda>t::real. ((1-t) * fst x + t * fst z, (1-t) * snd x + t * snd z))"
    define \<gamma>2 where "\<gamma>2 = (\<lambda>t::real. ((1-t) * fst z + t * fst y, (1-t) * snd z + t * snd y))"
    define \<gamma>_detour where "\<gamma>_detour = top1_path_product \<gamma>1 \<gamma>2"
    \<comment> \<open>Collinearity test: (fst p - fst x) * dy = (snd p - snd x) * dx.\<close>
    define collinear where "collinear = ((fst p - fst x) * dy = (snd p - snd x) * dx)"
    define f where "f = (if collinear then \<gamma>_detour else \<gamma>_straight)"
    have hf_path: "top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) x y f"
    proof (cases collinear)
      case True
      hence "f = \<gamma>_detour" unfolding f_def by simp
      moreover have "top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) x y \<gamma>_detour"
        unfolding \<gamma>_detour_def by (rule top1_path_product_is_path[OF hTR2
          R2_straight_line_path[where x=x and y=z, folded \<gamma>1_def]
          R2_straight_line_path[where x=z and y=y, folded \<gamma>2_def]])
      ultimately show ?thesis by simp
    next
      case False
      hence "f = \<gamma>_straight" unfolding f_def by simp
      moreover have "top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) x y \<gamma>_straight"
        unfolding \<gamma>_straight_def by (rule R2_straight_line_path)
      ultimately show ?thesis by simp
    qed
    have hf_avoid: "\<forall>t\<in>I_set. f t \<noteq> p"
    proof (cases collinear)
      case hcol: True
      hence hf_eq: "f = \<gamma>_detour" unfolding f_def by simp
      show ?thesis
      proof (cases "x = y")
        case True
        \<comment> \<open>x = y: z = x, path is constant at x, avoids p.\<close>
        hence "z = x" unfolding z_def dx_def dy_def by (cases x) auto
        have "\<And>t. \<gamma>1 t = x" unfolding \<gamma>1_def \<open>z = x\<close>
          by (simp add: prod_eq_iff algebra_simps)
        moreover have "\<And>t. \<gamma>2 t = x" unfolding \<gamma>2_def \<open>z = x\<close> True
          by (simp add: prod_eq_iff algebra_simps)
        ultimately have "\<And>t. \<gamma>_detour t = x" unfolding \<gamma>_detour_def top1_path_product_def by auto
        thus ?thesis unfolding hf_eq using hxp by auto
      next
        case hne: False
        have hdpos: "dx^2 + dy^2 > 0"
          using hne unfolding dx_def dy_def
          by (auto simp: sum_power2_gt_zero_iff) (cases x, cases y, auto)
        \<comment> \<open>Collinear: dp1*dy = dp2*dx where dp = p - x.\<close>
        define dp1 dp2 where "dp1 = fst p - fst x" and "dp2 = snd p - snd x"
        have hcol_eq: "dp1 * dy = dp2 * dx" using hcol unfolding collinear_def dp1_def dp2_def by simp
        show ?thesis
        proof (intro ballI)
          fix t assume ht: "t \<in> I_set"
          show "f t \<noteq> p"
          proof
            assume hftp: "f t = p"
            have htr: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
            show False
            proof (cases "t \<le> 1/2")
              case True
              \<comment> \<open>First segment: \<gamma>1(2t) = x + 2t*(-dy, dx). If = p: dp = 2t*(-dy, dx).\<close>
              have "\<gamma>_detour t = \<gamma>1 (2*t)" unfolding \<gamma>_detour_def top1_path_product_def using True by simp
              hence "\<gamma>1 (2*t) = p" using hftp hf_eq by simp
              hence "fst p = fst x + 2*t*(fst z - fst x) \<and> snd p = snd x + 2*t*(snd z - snd x)"
                unfolding \<gamma>1_def by (auto simp: algebra_simps)
              hence hdp: "dp1 = -2*t*dy \<and> dp2 = 2*t*dx"
                unfolding dp1_def dp2_def z_def dx_def dy_def by (auto simp: algebra_simps)
              have "dp1 * dy = -2*t*dy*dy" using hdp by auto
              moreover have "dp2 * dx = 2*t*dx*dx" using hdp by auto
              moreover note hcol_eq
              ultimately have "-2*t*dy*dy = 2*t*dx*dx" by (by100 linarith)
              hence "2*t*dx*dx + 2*t*dy*dy = 0" by (by100 linarith)
              hence "2*t*(dx*dx + dy*dy) = 0" by (simp add: algebra_simps)
              hence "t = 0"
              proof -
                have "dx*dx + dy*dy > 0" using hdpos unfolding power2_eq_square by simp
                have "t * (dx*dx + dy*dy) = 0" using \<open>2*t*(dx*dx + dy*dy) = 0\<close> by (by100 linarith)
                hence "t = 0 \<or> dx*dx + dy*dy = 0" by (rule mult_eq_0_iff[THEN iffD1])
                thus ?thesis using \<open>dx*dx + dy*dy > 0\<close> by (by100 linarith)
              qed
              hence "p = x" using \<open>\<gamma>1 (2*t) = p\<close> unfolding \<gamma>1_def by simp
              thus False using hxp by simp
            next
              case False
              hence hge: "t \<ge> 1/2" by simp
              \<comment> \<open>Second segment: \<gamma>2(2t-1). Let s = 2t-1 \<in> [0,1].\<close>
              have "\<gamma>_detour t = \<gamma>2 (2*t - 1)" unfolding \<gamma>_detour_def top1_path_product_def using False by simp
              hence "\<gamma>2 (2*t - 1) = p" using hftp hf_eq by simp
              define s where "s = 2*t - 1"
              have hsr: "0 \<le> s" "s \<le> 1" unfolding s_def using hge htr by auto
              have "\<gamma>2 s = p" using \<open>\<gamma>2 (2*t - 1) = p\<close> s_def by simp
              hence "fst p = (1-s)*fst z + s*fst y \<and> snd p = (1-s)*snd z + s*snd y"
                unfolding \<gamma>2_def by (auto simp: algebra_simps)
              hence "dp1 = (1-s)*(fst z - fst x) + s*dx \<and> dp2 = (1-s)*(snd z - snd x) + s*dy"
                unfolding dp1_def dp2_def dx_def dy_def by (auto simp: algebra_simps)
              hence hdp: "dp1 = -(1-s)*dy + s*dx \<and> dp2 = (1-s)*dx + s*dy"
                unfolding z_def dx_def dy_def by (auto simp: algebra_simps)
              have "dp1*dy = (-(1-s)*dy + s*dx)*dy" using hdp by simp
              hence hdp1dy: "dp1*dy = -(1-s)*dy*dy + s*dx*dy" by (simp add: algebra_simps)
              have "dp2*dx = ((1-s)*dx + s*dy)*dx" using hdp by simp
              hence hdp2dx: "dp2*dx = (1-s)*dx*dx + s*dy*dx" by (simp add: algebra_simps)
              have "dp1*dy = dp2*dx" by (rule hcol_eq)
              hence "-(1-s)*dy*dy + s*dx*dy = (1-s)*dx*dx + s*dy*dx"
                using hdp1dy hdp2dx by simp
              hence "-(1-s)*dy*dy - (1-s)*dx*dx = s*dy*dx - s*dx*dy" by (by100 linarith)
              hence "-(1-s)*(dx*dx + dy*dy) = 0" by (simp add: algebra_simps)
              hence "s = 1"
              proof -
                have "dx*dx + dy*dy > 0" using hdpos unfolding power2_eq_square by simp
                have "(1-s) * (dx*dx + dy*dy) = 0"
                  using \<open>-(1-s)*(dx*dx + dy*dy) = 0\<close> by (by100 linarith)
                hence "1-s = 0 \<or> dx*dx + dy*dy = 0" by (rule mult_eq_0_iff[THEN iffD1])
                thus ?thesis using \<open>dx*dx + dy*dy > 0\<close> by (by100 linarith)
              qed
              hence "p = y" using \<open>\<gamma>2 s = p\<close> unfolding \<gamma>2_def by simp
              thus False using hyp by simp
            qed
          qed
        qed
      qed
    next
      case hncol: False
      hence hf_eq: "f = \<gamma>_straight" unfolding f_def by simp
      \<comment> \<open>Non-collinear: p not on line(x,y), so not on segment x\<rightarrow>y.\<close>
      show ?thesis
      proof (intro ballI)
        fix t assume ht: "t \<in> I_set"
        have htr: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
        show "f t \<noteq> p"
        proof
          assume "f t = p"
          hence "fst p = (1-t) * fst x + t * fst y \<and> snd p = (1-t) * snd x + t * snd y"
            unfolding hf_eq \<gamma>_straight_def by auto
          hence "fst p - fst x = t * dx \<and> snd p - snd x = t * dy"
            unfolding dx_def dy_def by (auto simp: algebra_simps)
          hence "(fst p - fst x) * dy = t * dx * dy \<and> (snd p - snd x) * dx = t * dy * dx"
            by auto
          hence "(fst p - fst x) * dy = (snd p - snd x) * dx" by (auto simp: algebra_simps)
          thus False using hncol unfolding collinear_def by simp
        qed
      qed
    qed
    \<comment> \<open>Restrict f to UNIV-{p}.\<close>
    have himg_sub: "f ` I_set \<subseteq> ?S"
    proof
      fix q assume "q \<in> f ` I_set"
      then obtain t where ht: "t \<in> I_set" "q = f t" by (by100 blast)
      thus "q \<in> ?S" using hf_avoid ht by (by100 blast)
    qed
    have hf_cont: "top1_continuous_map_on I_set I_top UNIV
        (product_topology_on top1_open_sets top1_open_sets) f"
      using hf_path unfolding top1_is_path_on_def by (by100 blast)
    have "top1_continuous_map_on I_set I_top ?S ?TS f"
    proof -
      have "\<forall>W f'. top1_continuous_map_on I_set I_top UNIV
          (product_topology_on top1_open_sets top1_open_sets) f'
          \<and> W \<subseteq> (UNIV :: (real \<times> real) set) \<and> f' ` I_set \<subseteq> W
          \<longrightarrow> top1_continuous_map_on I_set I_top W
              (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) W) f'"
      proof -
        have hTI: "is_topology_on I_set I_top"
          unfolding top1_unit_interval_topology_def
          by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV])
            (by100 simp)
        show ?thesis by (rule Theorem_18_2(5)[OF hTI hTR2 hTR2])
      qed
      from this[THEN spec, THEN spec]
      have "top1_continuous_map_on I_set I_top UNIV
          (product_topology_on top1_open_sets top1_open_sets) f
          \<and> ?S \<subseteq> UNIV \<and> f ` I_set \<subseteq> ?S
          \<longrightarrow> top1_continuous_map_on I_set I_top ?S ?TS f"
        by (by100 simp)
      thus ?thesis using hf_cont himg_sub by (by100 blast)
    qed
    moreover have "f 0 = x" using hf_path unfolding top1_is_path_on_def by (by100 blast)
    moreover have "f 1 = y" using hf_path unfolding top1_is_path_on_def by (by100 blast)
    ultimately have "top1_is_path_on ?S ?TS x y f"
      unfolding top1_is_path_on_def by (by100 blast)
    thus "\<exists>f. top1_is_path_on ?S ?TS x y f" by (by100 blast)
  qed
qed

lemma homeomorphism_comp:
  assumes "top1_homeomorphism_on X TX Y TY f"
      and "top1_homeomorphism_on Y TY Z TZ g"
  shows "top1_homeomorphism_on X TX Z TZ (g \<circ> f)"
proof -
  have hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY" and hTZ: "is_topology_on Z TZ"
      and hfbij: "bij_betw f X Y" and hgbij: "bij_betw g Y Z"
      and hf: "top1_continuous_map_on X TX Y TY f"
      and hfinv: "top1_continuous_map_on Y TY X TX (inv_into X f)"
      and hg: "top1_continuous_map_on Y TY Z TZ g"
      and hginv: "top1_continuous_map_on Z TZ Y TY (inv_into Y g)"
    using assms unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hgfbij: "bij_betw (g \<circ> f) X Z" using hfbij hgbij by (rule bij_betw_trans)
  show ?thesis unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on X TX" by (rule hTX)
    show "is_topology_on Z TZ" by (rule hTZ)
    show "bij_betw (g \<circ> f) X Z" by (rule hgfbij)
    show "top1_continuous_map_on X TX Z TZ (g \<circ> f)"
      by (rule top1_continuous_map_on_comp[OF hf hg])
    show "top1_continuous_map_on Z TZ X TX (inv_into X (g \<circ> f))"
    proof -
      have hinv_comp: "\<And>z. z \<in> Z \<Longrightarrow> inv_into X (g \<circ> f) z = (inv_into X f \<circ> inv_into Y g) z"
      proof -
        fix z assume hz: "z \<in> Z"
        have hgy: "inv_into Y g z \<in> Y"
          using hz hgbij unfolding bij_betw_def by (simp add: inv_into_into)
        have hfx: "inv_into X f (inv_into Y g z) \<in> X"
          using hgy hfbij unfolding bij_betw_def by (simp add: inv_into_into)
        have "g (f (inv_into X f (inv_into Y g z))) = g (inv_into Y g z)"
          using hgy hfbij unfolding bij_betw_def by (simp add: f_inv_into_f)
        also have "\<dots> = z"
          using hz hgbij unfolding bij_betw_def by (simp add: f_inv_into_f)
        finally have "(g \<circ> f) (inv_into X f (inv_into Y g z)) = z" by simp
        thus "inv_into X (g \<circ> f) z = (inv_into X f \<circ> inv_into Y g) z"
          using hfx hgfbij unfolding bij_betw_def
          by (intro inv_into_f_eq[OF bij_betw_imp_inj_on[OF hgfbij]]) auto
      qed
      have hinv_cont: "top1_continuous_map_on Z TZ X TX (inv_into X f \<circ> inv_into Y g)"
        by (rule top1_continuous_map_on_comp[OF hginv hfinv])
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix z assume hz: "z \<in> Z"
        show "inv_into X (g \<circ> f) z \<in> X"
          using hinv_comp[OF hz] hinv_cont hz
          unfolding top1_continuous_map_on_def by (by100 auto)
      next
        fix V assume hV: "V \<in> TX"
        have "{z \<in> Z. inv_into X (g \<circ> f) z \<in> V} = {z \<in> Z. (inv_into X f \<circ> inv_into Y g) z \<in> V}"
        proof (rule Collect_cong)
          fix z show "(z \<in> Z \<and> inv_into X (g \<circ> f) z \<in> V) = (z \<in> Z \<and> (inv_into X f \<circ> inv_into Y g) z \<in> V)"
            using hinv_comp by (cases "z \<in> Z") simp_all
        qed
        also have "\<dots> \<in> TZ" using hinv_cont hV unfolding top1_continuous_map_on_def by (by100 blast)
        finally show "{z \<in> Z. inv_into X (g \<circ> f) z \<in> V} \<in> TZ" .
      qed
    qed
  qed
qed

lemma S2_minus_point_homeo_R2:
  assumes "a \<in> top1_S2"
  shows "\<exists>h. top1_homeomorphism_on (top1_S2 - {a})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
      (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets) h"
proof (cases "a = north_pole")
  case True
  thus ?thesis using stereographic_proj_homeomorphism by auto
next
  case False
  \<comment> \<open>Compose: householder sends S^2-{a} \<rightarrow> S^2-{N}, stereographic sends S^2-{N} \<rightarrow> R^2.\<close>
  have hR: "top1_homeomorphism_on (top1_S2 - {a})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
      (top1_S2 - {north_pole})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))
      (householder_S2 a)"
    by (rule householder_S2_homeo[OF assms])
  \<comment> \<open>Compose with stereographic: stereographic_proj \<circ> householder_S2 a.\<close>
  have "top1_homeomorphism_on (top1_S2 - {a})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
      (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets)
      (stereographic_proj \<circ> householder_S2 a)"
    by (rule homeomorphism_comp[OF hR stereographic_proj_homeomorphism])
  thus ?thesis by (by100 blast)
qed

lemma homeomorphism_inverse:
  assumes "top1_homeomorphism_on X TX Y TY h"
  shows "top1_homeomorphism_on Y TY X TX (inv_into X h)"
proof -
  have hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hbij: "bij_betw h X Y"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hg: "top1_continuous_map_on Y TY X TX (inv_into X h)"
    using assms unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hgbij: "bij_betw (inv_into X h) Y X" using hbij by (rule bij_betw_inv_into)
  have hinv_inv: "\<And>x. x \<in> X \<Longrightarrow> inv_into Y (inv_into X h) x = h x"
  proof -
    fix x assume hx: "x \<in> X"
    have "h x \<in> Y" using hx hbij unfolding bij_betw_def by auto
    moreover have "inv_into X h (h x) = x"
      using hx hbij unfolding bij_betw_def by (simp add: inv_into_f_f)
    ultimately show "inv_into Y (inv_into X h) x = h x"
      by (intro inv_into_f_eq[OF bij_betw_imp_inj_on[OF hgbij]]) auto
  qed
  show ?thesis unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on Y TY" by (rule hTY)
    show "is_topology_on X TX" by (rule hTX)
    show "bij_betw (inv_into X h) Y X" by (rule hgbij)
    show "top1_continuous_map_on Y TY X TX (inv_into X h)" by (rule hg)
    show "top1_continuous_map_on X TX Y TY (inv_into Y (inv_into X h))"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume hx: "x \<in> X"
      show "inv_into Y (inv_into X h) x \<in> Y" using hinv_inv[OF hx] hx hbij
        unfolding bij_betw_def by auto
    next
      fix V assume hV: "V \<in> TY"
      have "{x \<in> X. h x \<in> V} \<in> TX"
        using hh hV unfolding top1_continuous_map_on_def by (by100 blast)
      moreover have "{x \<in> X. inv_into Y (inv_into X h) x \<in> V} = {x \<in> X. h x \<in> V}"
        (is "?L = ?R")
      proof
        show "?L \<subseteq> ?R" using hinv_inv by auto
        show "?R \<subseteq> ?L" using hinv_inv by auto
      qed
      ultimately show "{x \<in> X. inv_into Y (inv_into X h) x \<in> V} \<in> TX" by simp
    qed
  qed
qed

lemma homeomorphism_preserves_simply_connected_forward:
  assumes "top1_homeomorphism_on X TX Y TY h"
      and "top1_simply_connected_on X TX"
  shows "top1_simply_connected_on Y TY"
  by (rule homeomorphism_preserves_simply_connected[OF homeomorphism_inverse[OF assms(1)] assms(2)])

lemma homeomorphism_reflects_simply_connected:
  assumes "top1_homeomorphism_on X TX Y TY h"
      and "\<not> top1_simply_connected_on X TX"
  shows "\<not> top1_simply_connected_on Y TY"
  using homeomorphism_preserves_simply_connected[OF assms(1)] assms(2) by blast

lemma homeomorphism_restrict_point:
  assumes hhom: "top1_homeomorphism_on X TX Y TY h" and hp: "p \<in> X"
  shows "top1_homeomorphism_on (X - {p}) (subspace_topology X TX (X - {p}))
             (Y - {h p}) (subspace_topology Y TY (Y - {h p})) h"
proof -
  have hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hbij: "bij_betw h X Y"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hg: "top1_continuous_map_on Y TY X TX (inv_into X h)"
    using hhom unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hinj: "inj_on h X" using hbij unfolding bij_betw_def by simp
  have hmap: "\<And>x. x \<in> X \<Longrightarrow> h x \<in> Y" using hbij unfolding bij_betw_def by auto
  show ?thesis unfolding top1_homeomorphism_on_def
  proof (intro conjI)
    show "is_topology_on (X-{p}) (subspace_topology X TX (X-{p}))"
      by (rule subspace_topology_is_topology_on[OF hTX]) simp
    show "is_topology_on (Y-{h p}) (subspace_topology Y TY (Y-{h p}))"
      by (rule subspace_topology_is_topology_on[OF hTY]) simp
    show "bij_betw h (X-{p}) (Y-{h p})"
      unfolding bij_betw_def
    proof (intro conjI)
      show "inj_on h (X-{p})" using hinj by (rule inj_on_subset) blast
      show "h ` (X-{p}) = Y-{h p}"
      proof (rule set_eqI, rule iffI)
        fix y assume "y \<in> h ` (X-{p})"
        then obtain x where hx: "x \<in> X-{p}" "y = h x" by blast
        show "y \<in> Y-{h p}" using hx hmap hinj hp
          by (metis DiffD1 DiffD2 DiffI inj_onD singletonD singletonI)
      next
        fix y assume hy: "y \<in> Y-{h p}"
        then obtain x where hx: "x \<in> X" "h x = y"
          using hbij unfolding bij_betw_def by auto
        have "x \<noteq> p" using hx hy by auto
        thus "y \<in> h ` (X-{p})" using hx by auto
      qed
    qed
    show "top1_continuous_map_on (X-{p}) (subspace_topology X TX (X-{p}))
        (Y-{h p}) (subspace_topology Y TY (Y-{h p})) h"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume hx: "x \<in> X-{p}"
      thus "h x \<in> Y-{h p}" using hmap hinj hp by (simp add: inj_on_eq_iff)
    next
      fix V assume hV: "V \<in> subspace_topology Y TY (Y-{h p})"
      then obtain W where hW: "W \<in> TY" and hVeq: "V = (Y-{h p}) \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      have "{x \<in> X-{p}. h x \<in> V} = (X-{p}) \<inter> {x \<in> X. h x \<in> W}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> X-{p}. h x \<in> V}"
        thus "x \<in> (X-{p}) \<inter> {x \<in> X. h x \<in> W}" unfolding hVeq by (by100 blast)
      next
        fix x assume hx: "x \<in> (X-{p}) \<inter> {x \<in> X. h x \<in> W}"
        have "h x \<in> Y-{h p}" using hx hmap hinj hp by (simp add: inj_on_eq_iff)
        thus "x \<in> {x \<in> X-{p}. h x \<in> V}" unfolding hVeq using hx by (by100 blast)
      qed
      moreover have "{x \<in> X. h x \<in> W} \<in> TX"
        using hh hW unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show "{x \<in> X-{p}. h x \<in> V} \<in> subspace_topology X TX (X-{p})"
        unfolding subspace_topology_def by (by100 blast)
    qed
    show "top1_continuous_map_on (Y-{h p}) (subspace_topology Y TY (Y-{h p}))
        (X-{p}) (subspace_topology X TX (X-{p})) (inv_into (X-{p}) h)"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix y assume hy: "y \<in> Y-{h p}"
      have "inv_into X h y \<in> X" using hy hbij unfolding bij_betw_def by (simp add: inv_into_into)
      moreover have "inv_into X h y \<noteq> p"
      proof
        assume "inv_into X h y = p"
        hence "h (inv_into X h y) = h p" by simp
        hence "y = h p" using hy hbij unfolding bij_betw_def by (simp add: f_inv_into_f)
        thus False using hy by simp
      qed
      ultimately have "inv_into X h y \<in> X-{p}" by simp
      moreover have "inv_into (X-{p}) h y = inv_into X h y"
      proof (rule inv_into_f_eq[OF inj_on_subset[OF hinj]])
        show "X - {p} \<subseteq> X" by blast
        show "inv_into X h y \<in> X - {p}" by (rule \<open>inv_into X h y \<in> X - {p}\<close>)
        show "h (inv_into X h y) = y" using hy hbij unfolding bij_betw_def by (simp add: f_inv_into_f)
      qed
      ultimately show "inv_into (X-{p}) h y \<in> X-{p}" by simp
    next
      fix V assume hV: "V \<in> subspace_topology X TX (X-{p})"
      then obtain W where hW: "W \<in> TX" and hVeq: "V = (X-{p}) \<inter> W"
        unfolding subspace_topology_def by (by100 blast)
      have hinv_agree: "\<And>y. y \<in> Y-{h p} \<Longrightarrow> inv_into (X-{p}) h y = inv_into X h y"
      proof -
        fix y assume hy: "y \<in> Y-{h p}"
        have h1: "inv_into X h y \<in> X" using hy hbij unfolding bij_betw_def by (simp add: inv_into_into)
        have h2: "inv_into X h y \<noteq> p"
        proof
          assume "inv_into X h y = p"
          hence "y = h p" using hy hbij unfolding bij_betw_def by (metis f_inv_into_f DiffD1)
          thus False using hy by simp
        qed
        show "inv_into (X-{p}) h y = inv_into X h y"
          by (rule inv_into_f_eq[OF inj_on_subset[OF hinj]])
             (use h1 h2 hy hbij in \<open>auto simp: bij_betw_def f_inv_into_f\<close>)
      qed
      have "\<And>y. y \<in> Y - {h p} \<Longrightarrow> inv_into X h y \<in> X - {p}"
      proof -
        fix y assume hy: "y \<in> Y - {h p}"
        have "inv_into X h y \<in> X" using hy hbij unfolding bij_betw_def by (simp add: inv_into_into)
        moreover have "inv_into X h y \<noteq> p"
          using hy hbij unfolding bij_betw_def by (metis DiffD1 DiffD2 f_inv_into_f singletonI)
        ultimately show "inv_into X h y \<in> X - {p}" by simp
      qed
      have "{y \<in> Y-{h p}. inv_into (X-{p}) h y \<in> V}
          = (Y-{h p}) \<inter> {y \<in> Y. inv_into X h y \<in> W}"
        unfolding hVeq using hinv_agree \<open>\<And>y. y \<in> Y - {h p} \<Longrightarrow> inv_into X h y \<in> X - {p}\<close>
        by auto
      moreover have "{y \<in> Y. inv_into X h y \<in> W} \<in> TY"
        using hg hW unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show "{y \<in> Y-{h p}. inv_into (X-{p}) h y \<in> V} \<in>
          subspace_topology Y TY (Y-{h p})"
        unfolding subspace_topology_def by (by100 blast)
    qed
  qed
qed

lemma S2_minus_two_points_not_simply_connected:
  assumes "a \<in> top1_S2" and "b \<in> top1_S2" and "a \<noteq> b"
  shows "\<not> top1_simply_connected_on (top1_S2 - {a, b})
           (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b}))"
  \<comment> \<open>S^2-{a,b} \<cong> R^2-{point} via Householder+stereographic. Not sc by R2_minus_point.\<close>
proof
  assume hsc: "top1_simply_connected_on (top1_S2 - {a, b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b}))"
  \<comment> \<open>Step 1: S^2-{a} \<cong> R^2 via stereographic+Householder. Already proved for S2_minus_point_sc.\<close>
  \<comment> \<open>Step 2: Restrict to S^2-{a,b} \<cong> R^2-{point}.\<close>
  \<comment> \<open>We use the fact that S^2-{a} has a homeomorphism to R^2 (the composed map).
     Restricting by removing b from S^2-{a} removes h(b) from R^2.\<close>
  \<comment> \<open>By homeomorphism_preserves_sc applied twice, S^2-{a,b} sc \<Longrightarrow> R^2-{point} sc.\<close>
  \<comment> \<open>But R^2-{point} not sc. Contradiction.\<close>
  \<comment> \<open>For now: use S2_minus_point_sc to get that S^2-{a} ≅ R^2 (homeomorphism exists),
     then restrict.\<close>
  obtain h where hh: "top1_homeomorphism_on (top1_S2 - {a})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
      (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets) h"
    using S2_minus_point_homeo_R2[OF assms(1)] by blast
  have hb_mem: "b \<in> top1_S2 - {a}" using assms by simp
  have hh_restrict: "top1_homeomorphism_on (top1_S2 - {a} - {b})
      (subspace_topology (top1_S2 - {a}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
        (top1_S2 - {a} - {b}))
      (UNIV - {h b})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {h b})) h"
    by (rule homeomorphism_restrict_point[OF hh hb_mem])
  have hab_eq: "top1_S2 - {a} - {b} = top1_S2 - {a, b}" by (by100 blast)
  have hsub_eq: "subspace_topology (top1_S2 - {a}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
      (top1_S2 - {a, b}) = subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})"
    by (rule subspace_topology_trans) blast
  have hh_restrict': "top1_homeomorphism_on (top1_S2 - {a, b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b}))
      (UNIV - {h b})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {h b})) h"
    using hh_restrict hab_eq hsub_eq by simp
  \<comment> \<open>Transfer: S^2-{a,b} sc \<Rightarrow> R^2-{h(b)} sc. Need h^{-1} homeomorphism direction.\<close>
  have hsc_R2: "top1_simply_connected_on (UNIV - {h b})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {h b}))"
    by (rule homeomorphism_preserves_simply_connected_forward[OF hh_restrict' hsc])
  have "h b \<in> (UNIV :: (real \<times> real) set)" by simp
  show False using R2_minus_point_not_simply_connected[OF \<open>h b \<in> UNIV\<close>] hsc_R2 by (by100 blast)
qed

text \<open>Any continuous map into S^2 - {b} is nulhomotopic (since S^2-{b} is contractible).\<close>
lemma top1_mult_continuous_R2:
  "top1_continuous_map_on (UNIV :: (real \<times> real) set)
    (product_topology_on top1_open_sets top1_open_sets)
    (UNIV :: real set) top1_open_sets (\<lambda>(u,v). u * v)"
  unfolding top1_continuous_map_on_def product_topology_on_open_sets
proof (intro conjI ballI)
  fix p :: "real \<times> real" assume "p \<in> UNIV" thus "(\<lambda>(u,v). u*v) p \<in> UNIV" by simp
next
  fix V :: "real set" assume hV: "V \<in> (top1_open_sets :: real set set)"
  have hVo: "open V" using hV unfolding top1_open_sets_def by (by100 blast)
  have hcont_mult: "continuous_on UNIV (\<lambda>p::real\<times>real. fst p * snd p)"
    by (intro continuous_intros)
  have "open ((\<lambda>(u,v::real). u*v) -` V)"
  proof -
    have "(\<lambda>(u,v::real). u*v) = (\<lambda>p. fst p * snd p)" by (rule ext) (simp add: case_prod_unfold)
    thus ?thesis using open_vimage[OF hVo hcont_mult] by simp
  qed
  hence "(\<lambda>(u,v::real). u*v) -` V \<in> (top1_open_sets :: (real \<times> real) set set)"
    unfolding top1_open_sets_def by (by100 blast)
  thus "{p \<in> UNIV. (\<lambda>(u,v). u*v) p \<in> V} \<in> (top1_open_sets :: (real \<times> real) set set)"
    unfolding top1_open_sets_def by (simp add: vimage_def Collect_mono_iff)
qed

lemma map_into_R2_nulhomotopic:
  assumes hf: "top1_continuous_map_on A TA
      (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) f"
      and hTA: "is_topology_on A TA"
  shows "top1_nulhomotopic_on A TA
      (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) f"
  \<comment> \<open>R^2 is contractible: straight-line homotopy F(x,t) = (1-t)*f(x).\<close>
  unfolding top1_nulhomotopic_on_def
proof (intro bexI[of _ "(0::real, 0)"])
  let ?TR2 = "product_topology_on (top1_open_sets :: real set set) top1_open_sets"
  let ?c = "(0::real, 0)"
  \<comment> \<open>Define F(x,t) = (1-t)*f(x) = ((1-t)*fst(f x), (1-t)*snd(f x)).\<close>
  define F where "F = (\<lambda>(x::'a, t::real). ((1-t)*fst(f x), (1-t)*snd(f x)))"
  have hTR2: "is_topology_on (UNIV :: (real \<times> real) set) ?TR2"
  proof -
    have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
      by (rule top1_open_sets_is_topology_on_UNIV)
    show ?thesis using product_topology_on_is_topology_on[OF hTR hTR] by simp
  qed
  have hconst: "top1_continuous_map_on A TA (UNIV :: (real \<times> real) set) ?TR2 (\<lambda>_. ?c)"
    by (rule top1_continuous_map_on_const[OF hTA hTR2]) simp
  show "top1_homotopic_on A TA (UNIV :: (real \<times> real) set) ?TR2 f (\<lambda>_. ?c)"
    unfolding top1_homotopic_on_def
    using hf hconst
  proof (intro conjI exI[of _ F])
    show "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top)
        (UNIV :: (real \<times> real) set) ?TR2 F"
    proof -
      have hTAI: "is_topology_on (A \<times> I_set) (product_topology_on TA I_top)"
        using product_topology_on_is_topology_on[OF hTA
            top1_unit_interval_topology_is_topology_on] by simp
      have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
        by (rule top1_open_sets_is_topology_on_UNIV)
      have hpi1_eq: "(pi1 :: real \<times> real \<Rightarrow> real) = fst" unfolding pi1_def by (rule ext) simp
      have hpi2_eq: "(pi2 :: real \<times> real \<Rightarrow> real) = snd" unfolding pi2_def by (rule ext) simp
      \<comment> \<open>By Theorem 18.4: F continuous \<longleftrightarrow> fst\<circ>F and snd\<circ>F continuous.\<close>
      have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
      show ?thesis unfolding hUU[symmetric]
        unfolding Theorem_18_4[OF hTAI hTR hTR] hpi1_eq hpi2_eq
      proof (intro conjI)
        \<comment> \<open>fst \<circ> F (x,t) = (1-t)*fst(f x).\<close>
        show "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top)
            (UNIV::real set) top1_open_sets (fst \<circ> F)"
        proof -
          have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
          \<comment> \<open>fst \<circ> F (x,t) = fst(f x) * (1-t). Factor: mult \<circ> (fst\<circ>f\<circ>\<pi>1, (1-)\<circ>\<pi>2).\<close>
          \<comment> \<open>Step 1: fst\<circ>f: A \<rightarrow> R continuous.\<close>
          have hfst_f: "top1_continuous_map_on A TA (UNIV::real set) top1_open_sets (fst \<circ> f)"
          proof -
            have hfst: "top1_continuous_map_on (UNIV::(real\<times>real) set)
                (product_topology_on top1_open_sets top1_open_sets)
                (UNIV::real set) top1_open_sets pi1"
            proof -
              have "top1_continuous_map_on ((UNIV::real set) \<times> (UNIV::real set))
                  (product_topology_on top1_open_sets top1_open_sets) (UNIV::real set) top1_open_sets pi1"
                by (rule top1_continuous_pi1[OF hTR hTR])
              thus ?thesis by simp
            qed
            have "top1_continuous_map_on A TA (UNIV::real set) top1_open_sets (pi1 \<circ> f)"
              by (rule top1_continuous_map_on_comp[OF hf hfst])
            thus ?thesis unfolding hpi1_eq .
          qed
          \<comment> \<open>Step 2: fst\<circ>f\<circ>\<pi>1: A\<times>I \<rightarrow> R continuous.\<close>
          have hcomp1: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top)
              (UNIV::real set) top1_open_sets (fst \<circ> f \<circ> pi1)"
          proof -
            have hpi: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) A TA pi1"
              by (rule top1_continuous_pi1[OF hTA hTI])
            show ?thesis by (rule top1_continuous_map_on_comp[OF hpi hfst_f])
          qed
          \<comment> \<open>Step 3: (1-)\<circ>\<pi>2: A\<times>I \<rightarrow> R continuous.\<close>
          have h1mt: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (\<lambda>t. 1-t)"
          proof -
            have "top1_continuous_map_on I_set (subspace_topology UNIV top1_open_sets I_set)
                (UNIV::real set) (subspace_topology UNIV top1_open_sets UNIV) (\<lambda>t::real. 1-t)"
              by (rule top1_continuous_map_on_real_subspace_open_sets) (auto intro: continuous_intros)
            thus ?thesis unfolding top1_unit_interval_topology_def
              by (simp add: subspace_topology_UNIV_self)
          qed
          have hcomp2: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top)
              (UNIV::real set) top1_open_sets ((\<lambda>t. 1 - t) \<circ> pi2)"
          proof -
            have hpi: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) I_set I_top pi2"
              by (rule top1_continuous_pi2[OF hTA hTI])
            show ?thesis by (rule top1_continuous_map_on_comp[OF hpi h1mt])
          qed
          \<comment> \<open>Step 4: pair (fst\<circ>f\<circ>\<pi>1, (1-)\<circ>\<pi>2): A\<times>I \<rightarrow> R\<times>R by Theorem_18_4.\<close>
          define g where "g = (\<lambda>p. (fst (f (pi1 p)), (1::real) - pi2 p))"
          have hg_cont: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top)
              ((UNIV::real set) \<times> (UNIV::real set)) (product_topology_on top1_open_sets top1_open_sets) g"
            unfolding Theorem_18_4[OF hTAI hTR hTR] hpi1_eq hpi2_eq g_def
            using hcomp1 hcomp2 unfolding hpi1_eq hpi2_eq comp_def by auto
          \<comment> \<open>Step 5: fst \<circ> F = mult \<circ> g.\<close>
          have hfst_F_eq: "fst \<circ> F = (\<lambda>(u,v). u*v) \<circ> g"
            unfolding F_def g_def pi1_def pi2_def
            by (rule ext) (simp add: case_prod_unfold mult.commute)
          \<comment> \<open>Step 6: compose g with mult.\<close>
          have hmult: "top1_continuous_map_on ((UNIV::real set) \<times> (UNIV::real set))
              (product_topology_on top1_open_sets top1_open_sets)
              (UNIV::real set) top1_open_sets (\<lambda>(u,v). u*v)"
            using top1_mult_continuous_R2
            unfolding product_topology_on_open_sets_real2 by simp
          show ?thesis unfolding hfst_F_eq hUU
            by (rule top1_continuous_map_on_comp[OF hg_cont hmult])
        qed
        \<comment> \<open>snd \<circ> F (x,t) = (1-t)*snd(f x).\<close>
        show "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top)
            (UNIV::real set) top1_open_sets (snd \<circ> F)"
        proof -
          have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
          have hsnd_f: "top1_continuous_map_on A TA (UNIV::real set) top1_open_sets (snd \<circ> f)"
          proof -
            have "top1_continuous_map_on ((UNIV::real set) \<times> (UNIV::real set))
                (product_topology_on top1_open_sets top1_open_sets) (UNIV::real set) top1_open_sets pi2"
              by (rule top1_continuous_pi2[OF hTR hTR])
            hence hsnd: "top1_continuous_map_on (UNIV::(real\<times>real) set)
                (product_topology_on top1_open_sets top1_open_sets) (UNIV::real set) top1_open_sets pi2"
              by simp
            have "top1_continuous_map_on A TA (UNIV::real set) top1_open_sets (pi2 \<circ> f)"
              by (rule top1_continuous_map_on_comp[OF hf hsnd])
            thus ?thesis unfolding hpi2_eq .
          qed
          have hcomp1s: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top)
              (UNIV::real set) top1_open_sets (snd \<circ> f \<circ> pi1)"
            by (rule top1_continuous_map_on_comp[OF top1_continuous_pi1[OF hTA hTI] hsnd_f])
          define g2 where "g2 = (\<lambda>p. (snd (f (pi1 p)), (1::real) - pi2 p))"
          have hg2: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top)
              ((UNIV::real set) \<times> (UNIV::real set)) (product_topology_on top1_open_sets top1_open_sets) g2"
          proof -
            have h1mt': "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (\<lambda>t. 1-t)"
            proof -
              have "top1_continuous_map_on I_set (subspace_topology UNIV top1_open_sets I_set)
                  (UNIV::real set) (subspace_topology UNIV top1_open_sets UNIV) (\<lambda>t::real. 1-t)"
                by (rule top1_continuous_map_on_real_subspace_open_sets) (auto intro: continuous_intros)
              thus ?thesis unfolding top1_unit_interval_topology_def by (simp add: subspace_topology_UNIV_self)
            qed
            have hcomp2s: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top)
                (UNIV::real set) top1_open_sets ((\<lambda>t. 1 - t) \<circ> pi2)"
              by (rule top1_continuous_map_on_comp[OF top1_continuous_pi2[OF hTA hTI] h1mt'])
            show ?thesis unfolding Theorem_18_4[OF hTAI hTR hTR] hpi1_eq hpi2_eq g2_def
              using hcomp1s hcomp2s unfolding hpi1_eq hpi2_eq comp_def by auto
          qed
          have hsnd_F_eq: "snd \<circ> F = (\<lambda>(u,v). u*v) \<circ> g2"
            unfolding F_def g2_def pi1_def pi2_def
            by (rule ext) (simp add: case_prod_unfold mult.commute)
          have hmult': "top1_continuous_map_on ((UNIV::real set) \<times> (UNIV::real set))
              (product_topology_on top1_open_sets top1_open_sets)
              (UNIV::real set) top1_open_sets (\<lambda>(u,v). u*v)"
            using top1_mult_continuous_R2
            unfolding product_topology_on_open_sets_real2 by simp
          show ?thesis unfolding hsnd_F_eq hUU
            by (rule top1_continuous_map_on_comp[OF hg2 hmult'])
        qed
      qed
    qed
    show "\<forall>x\<in>A. F (x, 0) = f x" unfolding F_def by simp
    show "\<forall>x\<in>A. F (x, 1) = ?c" unfolding F_def by simp
  qed auto
  show "?c \<in> UNIV" by simp
qed

lemma nulhomotopic_transfer:
  assumes hhom: "top1_homeomorphism_on X TX Y TY h"
      and hnul: "top1_nulhomotopic_on A TA Y TY (h \<circ> f)"
      and hf: "top1_continuous_map_on A TA X TX f"
      and hTA: "is_topology_on A TA"
  shows "top1_nulhomotopic_on A TA X TX f"
proof -
  have hg: "top1_continuous_map_on Y TY X TX (inv_into X h)"
    using hhom unfolding top1_homeomorphism_on_def by (by100 blast)
  have hinj: "inj_on h X" using hhom unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  obtain c where hcY: "c \<in> Y"
      and hhf_hom: "top1_homotopic_on A TA Y TY (h \<circ> f) (\<lambda>_. c)"
    using hnul unfolding top1_nulhomotopic_on_def by (by100 blast)
  obtain F where hF: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) Y TY F"
      and hF0: "\<forall>x\<in>A. F (x, 0) = (h \<circ> f) x" and hF1: "\<forall>x\<in>A. F (x, 1) = c"
    using hhf_hom unfolding top1_homotopic_on_def by (by100 blast)
  define G where "G = inv_into X h \<circ> F"
  have hG: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) X TX G"
    unfolding G_def by (rule top1_continuous_map_on_comp[OF hF hg])
  have hgc: "inv_into X h c \<in> X"
    using hcY hhom unfolding top1_homeomorphism_on_def bij_betw_def by (simp add: inv_into_into)
  have hG0: "\<forall>x\<in>A. G (x, 0) = f x"
  proof
    fix x assume hx: "x \<in> A"
    have hfx: "f x \<in> X" using hf hx unfolding top1_continuous_map_on_def by (by100 blast)
    show "G (x, 0) = f x" unfolding G_def comp_def using hF0 hx
      by (simp add: inv_into_f_f[OF hinj hfx])
  qed
  have hG1: "\<forall>x\<in>A. G (x, 1) = inv_into X h c"
    unfolding G_def comp_def using hF1 by simp
  have hTX: "is_topology_on X TX"
    using hhom unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTA': "is_topology_on A TA" by (rule hTA)
  have hconst: "top1_continuous_map_on A TA X TX (\<lambda>_. inv_into X h c)"
    by (rule top1_continuous_map_on_const[OF hTA hTX hgc])
  show ?thesis unfolding top1_nulhomotopic_on_def top1_homotopic_on_def
    using hgc hf hconst hG hG0 hG1
    by (intro bexI[of _ "inv_into X h c"] conjI exI[of _ G]) auto
qed

lemma map_into_S2_minus_point_nulhomotopic:
  assumes "b \<in> top1_S2"
      and "top1_continuous_map_on A TA
             (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) f"
      and "is_topology_on A TA"
  shows "top1_nulhomotopic_on A TA
           (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) f"
proof -
  let ?S = "top1_S2 - {b}" and ?TS = "subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
  let ?TR2 = "product_topology_on (top1_open_sets :: real set set) top1_open_sets"
  obtain h where hh: "top1_homeomorphism_on ?S ?TS (UNIV :: (real \<times> real) set) ?TR2 h"
    using S2_minus_point_homeo_R2[OF assms(1)] by blast
  \<comment> \<open>h \<circ> f: A \<rightarrow> R^2 is continuous.\<close>
  have hhf: "top1_continuous_map_on A TA (UNIV :: (real \<times> real) set) ?TR2 (h \<circ> f)"
  proof -
    have "top1_continuous_map_on ?S ?TS (UNIV :: (real \<times> real) set) ?TR2 h"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    thus ?thesis by (rule top1_continuous_map_on_comp[OF assms(2)])
  qed
  \<comment> \<open>h \<circ> f is nulhomotopic in R^2 (R^2 contractible).\<close>
  have "top1_nulhomotopic_on A TA (UNIV :: (real \<times> real) set) ?TR2 (h \<circ> f)"
    by (rule map_into_R2_nulhomotopic[OF hhf assms(3)])
  \<comment> \<open>Transfer back: f is nulhomotopic in S^2-{b}.\<close>
  thus ?thesis by (rule nulhomotopic_transfer[OF hh _ assms(2) assms(3)])
qed

lemma topology_inter_open:
  assumes "is_topology_on X T" "U \<in> T" "V \<in> T"
  shows "U \<inter> V \<in> T"
proof -
  have "\<forall>F. finite F \<and> F \<noteq> {} \<and> F \<subseteq> T \<longrightarrow> \<Inter>F \<in> T"
    using assms(1) unfolding is_topology_on_def by (by100 blast)
  hence "finite {U, V} \<and> {U, V} \<noteq> {} \<and> {U, V} \<subseteq> T \<longrightarrow> \<Inter>{U, V} \<in> T"
    by (rule spec[of _ "{U, V}"])
  hence "{U, V} \<subseteq> T \<longrightarrow> \<Inter>{U, V} \<in> T" by simp
  moreover have "\<Inter>{U, V} = U \<inter> V" by simp
  ultimately show ?thesis using assms(2,3) by simp
qed



text \<open>Helper: open subsets of locally path-connected spaces are locally path-connected.\<close>
lemma open_subset_locally_path_connected:
  assumes hlpc: "top1_locally_path_connected_on X TX"
      and hUo: "U \<in> TX" and hUX: "U \<subseteq> X"
  shows "top1_locally_path_connected_on U (subspace_topology X TX U)"
proof -
  have hTX: "is_topology_on X TX" using hlpc unfolding top1_locally_path_connected_on_def by (by100 blast)
  have hTU: "is_topology_on U (subspace_topology X TX U)"
    by (rule subspace_topology_is_topology_on[OF hTX hUX])
  show ?thesis unfolding top1_locally_path_connected_on_def
  proof (intro conjI hTU ballI)
    fix x assume hx: "x \<in> U"
    show "top1_locally_path_connected_at U (subspace_topology X TX U) x"
      unfolding top1_locally_path_connected_at_def
    proof (intro allI impI)
      fix W assume hW: "neighborhood_of x U (subspace_topology X TX U) W \<and> W \<subseteq> U"
      hence hWo: "W \<in> subspace_topology X TX U" and hxW: "x \<in> W" and hWU: "W \<subseteq> U"
        unfolding neighborhood_of_def by auto
      obtain W' where hW': "W' \<in> TX" and hW_eq: "W = U \<inter> W'"
        using hWo unfolding subspace_topology_def by (by100 blast)
      \<comment> \<open>U \<inter> W' is open in X (intersection of open sets).\<close>
      have hUW'_open: "U \<inter> W' \<in> TX" by (rule topology_inter2[OF hTX hUo hW'])
      have hxUW': "x \<in> U \<inter> W'" using hxW hW_eq by simp
      \<comment> \<open>By X's lpc: \<exists> path-connected V \<in> TX with x \<in> V \<subseteq> U \<inter> W'.\<close>
      have "top1_locally_path_connected_at X TX x"
        using hlpc hx hUX unfolding top1_locally_path_connected_on_def by (by100 blast)
      hence "\<exists>V. neighborhood_of x X TX V \<and> V \<subseteq> U \<inter> W' \<and> V \<subseteq> X
           \<and> top1_path_connected_on V (subspace_topology X TX V)"
        unfolding top1_locally_path_connected_at_def
        using hUW'_open hxUW' hUX hW' unfolding neighborhood_of_def by (by100 blast)
      then obtain V where hVo: "V \<in> TX" and hxV: "x \<in> V" and hVsub: "V \<subseteq> U \<inter> W'"
          and hVX: "V \<subseteq> X" and hVpc: "top1_path_connected_on V (subspace_topology X TX V)"
        unfolding neighborhood_of_def by (by100 blast)
      \<comment> \<open>V \<subseteq> U, so V = U \<inter> V, hence V \<in> subspace_topology X TX U.\<close>
      have hVU: "V \<subseteq> U" using hVsub by (by100 blast)
      have hV_in_sub: "V \<in> subspace_topology X TX U"
      proof -
        have hUV_eq: "U \<inter> V = V" using hVU by (by100 blast)
        have "U \<inter> V \<in> subspace_topology X TX U" by (rule subspace_topology_memI[OF hVo])
        thus ?thesis using hUV_eq by simp
      qed
      \<comment> \<open>V path-connected in subspace of U.\<close>
      have hVpc_U: "top1_path_connected_on V (subspace_topology U (subspace_topology X TX U) V)"
      proof -
        have "subspace_topology U (subspace_topology X TX U) V = subspace_topology X TX V"
          by (rule subspace_topology_trans[OF hVU])
        thus ?thesis using hVpc by simp
      qed
      show "\<exists>V. neighborhood_of x U (subspace_topology X TX U) V \<and> V \<subseteq> W \<and> V \<subseteq> U
           \<and> top1_path_connected_on V (subspace_topology U (subspace_topology X TX U) V)"
        using hV_in_sub hxV hVsub hVU hVpc_U hW_eq
        unfolding neighborhood_of_def by (by100 blast)
    qed
  qed
qed


(** from \<S>61 Lemma 61.2 (Nulhomotopy lemma): any continuous map from a compact
    space A into S^2 - b whose image factors through an arc is nulhomotopic. **)
lemma Lemma_61_2_nulhomotopy:
  fixes A :: "'a set" and TA :: "'a set set" and f :: "'a \<Rightarrow> real \<times> real \<times> real"
    and b :: "real \<times> real \<times> real"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "top1_compact_on A TA"
      and "b \<in> top1_S2"
      and "top1_continuous_map_on A TA
             (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) f"
      and "\<exists>D. D \<subseteq> top1_S2 - {b} \<and> f ` A \<subseteq> D
            \<and> (\<exists>\<gamma>. top1_continuous_map_on I_set I_top D
                     (subspace_topology top1_S2 top1_S2_topology D) \<gamma>
                  \<and> inj_on \<gamma> I_set \<and> \<gamma> ` I_set = D)"
             \<comment> \<open>f factors through an arc D\<close>
  shows "top1_nulhomotopic_on A TA
           (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) f"
proof -
  \<comment> \<open>Munkres 61.2: f factors through an arc D \<subseteq> S^2-{b}.
     Step 1: An arc D is homeomorphic to [0,1], which is convex.
     Step 2: Any map into a convex set is nulhomotopic (straight-line homotopy).
     Step 3: S^2-{b} \<cong> R^2 (stereographic projection), so the nulhomotopy transfers.\<close>
  obtain D where hD: "D \<subseteq> top1_S2 - {b}" and hfD: "f ` A \<subseteq> D"
      and "\<exists>\<gamma>. inj_on \<gamma> I_set \<and> \<gamma> ` I_set = D"
    using assms(5) by (by100 auto)
  \<comment> \<open>D is contractible (homeomorphic to [0,1]).\<close>
  \<comment> \<open>S^2-{b} is contractible (homeomorphic to R^2), so any map into it is nulhomotopic.\<close>
  show ?thesis by (rule map_into_S2_minus_point_nulhomotopic[OF assms(3) assms(4)
      compact_is_topology[OF assms(2)]])
qed

lemma S2_compact_standard: "compact top1_S2"
proof -
  \<comment> \<open>S^2 = image of [0,1]^2 under \<psi>(s,t) = (sin(\<pi>s)cos(2\<pi>t), sin(\<pi>s)sin(2\<pi>t), cos(\<pi>s)).\<close>
  define \<psi> :: "real \<times> real \<Rightarrow> real \<times> real \<times> real" where
    "\<psi> = (\<lambda>(s, t). (sin (pi * s) * cos (2 * pi * t),
                     sin (pi * s) * sin (2 * pi * t),
                     cos (pi * s)))"
  have hcont: "continuous_on UNIV \<psi>"
    unfolding \<psi>_def by (auto intro!: continuous_intros simp: case_prod_beta)
  have himg: "\<psi> ` (I_set \<times> I_set) = top1_S2"
  proof (rule set_eqI, rule iffI)
    \<comment> \<open>Image \<subseteq> S^2: sin^2(\<pi>s)\<cdot>cos^2(2\<pi>t) + sin^2(\<pi>s)\<cdot>sin^2(2\<pi>t) + cos^2(\<pi>s) = sin^2+cos^2 = 1.\<close>
    fix p assume "p \<in> \<psi> ` (I_set \<times> I_set)"
    then obtain s t where hst: "s \<in> I_set" "t \<in> I_set" "p = \<psi> (s, t)" by (by100 blast)
    show "p \<in> top1_S2" unfolding hst(3) \<psi>_def top1_S2_def
      by (simp add: sin_squared_eq[symmetric] power2_eq_square algebra_simps distrib_left[symmetric])
  next
    fix p assume hp: "p \<in> top1_S2"
    obtain x y z where hp_eq: "p = (x, y, z)" by (cases p, auto)
    have hxyz: "x^2 + y^2 + z^2 = 1" using hp hp_eq unfolding top1_S2_def by simp
    have hz_sq: "z^2 \<le> 1"
    proof -
      have "x^2 \<ge> 0" "y^2 \<ge> 0" by (simp_all add: power2_eq_square)
      thus ?thesis using hxyz by linarith
    qed
    have hz_range: "-1 \<le> z" "z \<le> 1"
    proof -
      have "\<bar>z\<bar> \<le> 1" using hz_sq abs_le_square_iff[of z 1] by simp
      thus "-1 \<le> z" "z \<le> 1" by linarith+
    qed
    define s where "s = arccos z / pi"
    have hs_range: "0 \<le> s" "s \<le> 1" unfolding s_def
      using arccos_bounded[OF hz_range] pi_gt_zero by auto
    hence hs_I: "s \<in> I_set" unfolding top1_unit_interval_def by simp
    have hcos_s: "cos (pi * s) = z" unfolding s_def using pi_gt_zero hz_range by simp
    have hsin_s: "sin (pi * s) \<ge> 0" using hs_range pi_gt_zero
      by (intro sin_ge_zero) (by100 simp)+
    have hsin_s_sq: "sin (pi * s) ^ 2 = x^2 + y^2"
      using sin_squared_eq[of "pi * s"] hcos_s hxyz by (simp add: power2_eq_square algebra_simps)
    show "p \<in> \<psi> ` (I_set \<times> I_set)"
    proof (cases "sin (pi * s) = 0")
      case True
      \<comment> \<open>sin(\<pi>s)=0 \<Rightarrow> x^2+y^2=0 \<Rightarrow> x=0, y=0. \<psi>(s,0) = (0,0,cos(\<pi>s)) = (0,0,z) = p.\<close>
      have "x = 0 \<and> y = 0" using hsin_s_sq True by simp
      have "\<psi> (s, 0) = p" unfolding \<psi>_def hp_eq using hcos_s \<open>x = 0 \<and> y = 0\<close> True by simp
      have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      thus ?thesis using \<open>\<psi> (s, 0) = p\<close> hs_I \<open>0 \<in> I_set\<close> by (by100 blast)
    next
      case False hence hsin_pos: "sin (pi * s) > 0" using hsin_s by linarith
      \<comment> \<open>(x/sin(\<pi>s))^2 + (y/sin(\<pi>s))^2 = (x^2+y^2)/sin^2(\<pi>s) = 1.\<close>
      have hnorm: "(x / sin (pi * s))^2 + (y / sin (pi * s))^2 = 1"
      proof -
        have "(x / sin (pi * s))^2 + (y / sin (pi * s))^2
            = (x^2 + y^2) / (sin (pi * s))^2"
          by (simp add: power_divide add_divide_distrib)
        also have "... = (sin (pi * s))^2 / (sin (pi * s))^2" using hsin_s_sq by simp
        also have "... = 1" using hsin_pos by simp
        finally show ?thesis .
      qed
      obtain t0 where ht0: "0 \<le> t0" "t0 < 2*pi"
          "x / sin (pi * s) = cos t0" "y / sin (pi * s) = sin t0"
        using sincos_total_2pi[OF hnorm] by blast
      define t where "t = t0 / (2 * pi)"
      have ht_range: "0 \<le> t" "t < 1" unfolding t_def using ht0(1,2) pi_gt_zero by auto
      hence ht_I: "t \<in> I_set" unfolding top1_unit_interval_def by simp
      have hcos_t: "cos (2 * pi * t) = x / sin (pi * s)"
        unfolding t_def using pi_gt_zero ht0(3) by simp
      have hsin_t: "sin (2 * pi * t) = y / sin (pi * s)"
        unfolding t_def using pi_gt_zero ht0(4) by simp
      have "\<psi> (s, t) = p" unfolding \<psi>_def hp_eq
        using hcos_s hcos_t hsin_t hsin_pos by simp
      thus ?thesis using hs_I ht_I by (by100 blast)
    qed
  qed
  have "compact (I_set \<times> I_set)"
  proof -
    have hI_comp: "top1_compact_on I_set I_top"
    proof -
      have "compact {0..1::real}" by (rule compact_Icc)
      have "I_set = {0..1::real}" unfolding top1_unit_interval_def
        by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
      have "compact I_set" using \<open>compact {0..1::real}\<close> \<open>I_set = _\<close> by simp
      have "top1_compact_on I_set (subspace_topology UNIV top1_open_sets I_set)"
        using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
      thus ?thesis unfolding top1_unit_interval_topology_def by simp
    qed
    have h1: "top1_compact_on (I_set \<times> I_set) (product_topology_on I_top I_top)"
      by (rule Theorem_26_7[OF hI_comp hI_comp])
    have h2: "product_topology_on I_top I_top = II_topology" unfolding II_topology_def by simp
    have h3: "II_topology = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
        (I_set \<times> I_set)" unfolding II_topology_def by (rule II_topology_eq_subspace)
    have h4: "product_topology_on (top1_open_sets :: real set set) top1_open_sets
        = (top1_open_sets :: (real \<times> real) set set)"
      using product_topology_on_open_sets_real2 by (by100 metis)
    have "top1_compact_on (I_set \<times> I_set) II_topology"
      using h1 unfolding h2[symmetric] .
    hence "top1_compact_on (I_set \<times> I_set) (subspace_topology UNIV
        (product_topology_on (top1_open_sets :: real set set) top1_open_sets) (I_set \<times> I_set))"
      using h3 by simp
    hence "top1_compact_on (I_set \<times> I_set) (subspace_topology UNIV
        (top1_open_sets :: (real \<times> real) set set) (I_set \<times> I_set))"
      using h4 by simp
    thus ?thesis
      using top1_compact_on_subspace_UNIV_iff_compact[of "I_set \<times> I_set"] by simp
  qed
  hence "compact (\<psi> ` (I_set \<times> I_set))"
    by (rule compact_continuous_image[OF continuous_on_subset[OF hcont subset_UNIV]])
  thus ?thesis using himg by simp
qed



text \<open>Helper: homeomorphism preserves locally path-connected.\<close>
lemma homeomorphism_preserves_lpc:
  assumes hhom: "top1_homeomorphism_on X TX Y TY h"
      and hlpc: "top1_locally_path_connected_on X TX"
  shows "top1_locally_path_connected_on Y TY"
proof -
  have hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hcont: "top1_continuous_map_on X TX Y TY h"
      and hbij: "bij_betw h X Y"
    using hhom unfolding top1_homeomorphism_on_def by (by100 blast)+
  have hinv: "top1_homeomorphism_on Y TY X TX (inv_into X h)"
    by (rule homeomorphism_inverse[OF hhom])
  have hinv_cont: "top1_continuous_map_on Y TY X TX (inv_into X h)"
    using hinv unfolding top1_homeomorphism_on_def by (by100 blast)
  show ?thesis unfolding top1_locally_path_connected_on_def
  proof (intro conjI hTY ballI)
    fix y assume hy: "y \<in> Y"
    show "top1_locally_path_connected_at Y TY y"
      unfolding top1_locally_path_connected_at_def
    proof (intro allI impI)
      fix U assume hU: "neighborhood_of y Y TY U \<and> U \<subseteq> Y"
      hence hUo: "U \<in> TY" and hyU: "y \<in> U" and hUY: "U \<subseteq> Y" unfolding neighborhood_of_def by auto
      define x where "x = inv_into X h y"
      have hinj: "inj_on h X" using hbij unfolding bij_betw_def by (by100 blast)
      have hsurj: "h ` X = Y" using hbij unfolding bij_betw_def by (by100 blast)
      have "y \<in> h ` X" using hy hsurj by simp
      hence hx: "x \<in> X" unfolding x_def by (rule inv_into_into)
      have hhx: "h x = y" unfolding x_def using bij_betw_inv_into_right[OF hbij hy] by simp
      \<comment> \<open>h^{-1}(U) is open in X.\<close>
      have hpreU: "{z \<in> X. h z \<in> U} \<in> TX"
        using hcont hUo unfolding top1_continuous_map_on_def by (by100 blast)
      have hx_preU: "x \<in> {z \<in> X. h z \<in> U}" using hx hhx hyU by (by100 blast)
      \<comment> \<open>By X lpc: \<exists> path-connected W with x \<in> W \<subseteq> h^{-1}(U).\<close>
      have "top1_locally_path_connected_at X TX x"
        using hlpc hx unfolding top1_locally_path_connected_on_def by (by100 blast)
      hence "\<exists>W. neighborhood_of x X TX W \<and> W \<subseteq> {z \<in> X. h z \<in> U} \<and> W \<subseteq> X
           \<and> top1_path_connected_on W (subspace_topology X TX W)"
        unfolding top1_locally_path_connected_at_def
        using hpreU hx_preU hx unfolding neighborhood_of_def by (by100 blast)
      then obtain W where hWo: "W \<in> TX" and hxW: "x \<in> W" and hWsub: "W \<subseteq> {z \<in> X. h z \<in> U}"
          and hWX: "W \<subseteq> X" and hWpc: "top1_path_connected_on W (subspace_topology X TX W)"
        unfolding neighborhood_of_def by (by100 blast)
      \<comment> \<open>h(W) is the desired neighborhood. It's open, contains y, contained in U, path-connected.\<close>
      define V where "V = h ` W"
      have hyV: "y \<in> V" unfolding V_def using hxW hhx by (by100 blast)
      have hVU: "V \<subseteq> U" unfolding V_def using hWsub by (by100 blast)
      have hVY: "V \<subseteq> Y" unfolding V_def using hWX hbij unfolding bij_betw_def by (by100 blast)
      \<comment> \<open>V is open in Y (h maps open sets to open sets since it's a homeomorphism).\<close>
      have hVo: "V \<in> TY"
      proof -
        \<comment> \<open>h^{-1} preimage of W = {y \<in> Y. inv_into X h y \<in> W}. This is open because h^{-1} continuous.\<close>
        have "{y \<in> Y. inv_into X h y \<in> W} \<in> TY"
          using hinv_cont hWo unfolding top1_continuous_map_on_def by (by100 blast)
        moreover have "{y \<in> Y. inv_into X h y \<in> W} = h ` W"
        proof (rule set_eqI, rule iffI)
          fix y assume "y \<in> {y \<in> Y. inv_into X h y \<in> W}"
          hence hyY: "y \<in> Y" and "inv_into X h y \<in> W" by auto
          hence "h (inv_into X h y) = y" using bij_betw_inv_into_right[OF hbij hyY] by simp
          hence "y = h (inv_into X h y)" by simp
          thus "y \<in> h ` W" using \<open>inv_into X h y \<in> W\<close>
            apply (rule_tac x="inv_into X h y" in image_eqI) by auto
        next
          fix y assume "y \<in> h ` W"
          then obtain w where hw: "w \<in> W" "y = h w" by (by100 blast)
          have "w \<in> X" using hw(1) hWX by (by100 blast)
          hence "inv_into X h y = w" unfolding hw(2) using inv_into_f_f[OF hinj \<open>w \<in> X\<close>] by simp
          moreover have "y \<in> Y" using hw(2) \<open>w \<in> X\<close> hsurj by (by100 blast)
          ultimately show "y \<in> {y \<in> Y. inv_into X h y \<in> W}" using hw(1) by (by100 blast)
        qed
        ultimately show ?thesis unfolding V_def by simp
      qed
      \<comment> \<open>V is path-connected (h restricted to W is a homeomorphism W \<rightarrow> V).\<close>
      have hVpc: "top1_path_connected_on V (subspace_topology Y TY V)"
      proof -
        \<comment> \<open>h restricted to W is a homeomorphism W \<rightarrow> V. W pc \<Rightarrow> V pc.\<close>
        \<comment> \<open>Key: inv_into W h = inv_into X h on V, since W \<subseteq> X and h injective.\<close>
        have hinv_eq: "\<And>v. v \<in> V \<Longrightarrow> inv_into W h v = inv_into X h v"
        proof -
          fix v assume "v \<in> V"
          then obtain w where hw: "w \<in> W" "h w = v" unfolding V_def by (by100 blast)
          have "w \<in> X" using hw(1) hWX by (by100 blast)
          have "inv_into W h v = w"
            using inv_into_f_f[OF inj_on_subset[OF hinj hWX] hw(1)] hw(2) by simp
          moreover have "inv_into X h v = w"
            using inv_into_f_f[OF hinj \<open>w \<in> X\<close>] hw(2) by simp
          ultimately show "inv_into W h v = inv_into X h v" by simp
        qed
        have hh_restrict: "top1_homeomorphism_on W (subspace_topology X TX W) V (subspace_topology Y TY V) h"
          unfolding top1_homeomorphism_on_def
        proof (intro conjI)
          show "is_topology_on W (subspace_topology X TX W)"
            by (rule subspace_topology_is_topology_on[OF hTX hWX])
          show "is_topology_on V (subspace_topology Y TY V)"
            by (rule subspace_topology_is_topology_on[OF hTY hVY])
          show "bij_betw h W V" unfolding V_def bij_betw_def
            using inj_on_subset[OF hinj hWX] by (by100 blast)
          show "top1_continuous_map_on W (subspace_topology X TX W) V (subspace_topology Y TY V) h"
            unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix w assume "w \<in> W" thus "h w \<in> V" unfolding V_def by (by100 blast)
          next
            fix S assume hS: "S \<in> subspace_topology Y TY V"
            obtain S' where hS': "S' \<in> TY" and hS_eq: "S = V \<inter> S'"
              using hS unfolding subspace_topology_def by (by100 blast)
            have "{w \<in> W. h w \<in> S} = W \<inter> {w \<in> X. h w \<in> S'}"
              unfolding hS_eq V_def using hWX by (by100 blast)
            moreover have "{w \<in> X. h w \<in> S'} \<in> TX"
              using hcont hS' unfolding top1_continuous_map_on_def by (by100 blast)
            ultimately show "{w \<in> W. h w \<in> S} \<in> subspace_topology X TX W"
              using subspace_topology_memI by simp
          qed
          show "top1_continuous_map_on V (subspace_topology Y TY V) W (subspace_topology X TX W) (inv_into W h)"
            unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix v assume hv: "v \<in> V"
            then obtain w where "w \<in> W" "v = h w" unfolding V_def by (by100 blast)
            have "inv_into W h v = w"
              using inv_into_f_f[OF inj_on_subset[OF hinj hWX] \<open>w \<in> W\<close>] \<open>v = h w\<close> by simp
            thus "inv_into W h v \<in> W" using \<open>w \<in> W\<close> by simp
          next
            fix S assume hS: "S \<in> subspace_topology X TX W"
            obtain S' where hS': "S' \<in> TX" and hS_eq: "S = W \<inter> S'"
              using hS unfolding subspace_topology_def by (by100 blast)
            have "{v \<in> V. inv_into W h v \<in> S} = {v \<in> V. inv_into X h v \<in> S}"
              using hinv_eq by auto
            also have "... = V \<inter> {y \<in> Y. inv_into X h y \<in> S'}"
            proof (rule set_eqI, rule iffI)
              fix v assume "v \<in> {v \<in> V. inv_into X h v \<in> S}"
              hence "v \<in> V" and "inv_into X h v \<in> W \<inter> S'" using hS_eq by auto
              thus "v \<in> V \<inter> {y \<in> Y. inv_into X h y \<in> S'}" using hVY by (by100 blast)
            next
              fix v assume "v \<in> V \<inter> {y \<in> Y. inv_into X h y \<in> S'}"
              hence hv: "v \<in> V" and "inv_into X h v \<in> S'" by auto
              obtain w where "w \<in> W" "v = h w" using hv unfolding V_def by (by100 blast)
              have "w \<in> X" using \<open>w \<in> W\<close> hWX by (by100 blast)
              have "inv_into X h v = w" using inv_into_f_f[OF hinj \<open>w \<in> X\<close>] \<open>v = h w\<close> by simp
              hence "inv_into X h v \<in> W" using \<open>w \<in> W\<close> by simp
              thus "v \<in> {v \<in> V. inv_into X h v \<in> S}" using hv \<open>inv_into X h v \<in> S'\<close>
                hS_eq by (by100 blast)
            qed
            finally have "{v \<in> V. inv_into W h v \<in> S} = V \<inter> {y \<in> Y. inv_into X h y \<in> S'}" .
            moreover have "{y \<in> Y. inv_into X h y \<in> S'} \<in> TY"
              using hinv_cont hS' unfolding top1_continuous_map_on_def by (by100 blast)
            ultimately show "{v \<in> V. inv_into W h v \<in> S} \<in> subspace_topology Y TY V"
              using subspace_topology_memI by simp
          qed
        qed
        show ?thesis by (rule homeomorphism_preserves_path_connected[OF hh_restrict hWpc])
      qed
      show "\<exists>V. neighborhood_of y Y TY V \<and> V \<subseteq> U \<and> V \<subseteq> Y
           \<and> top1_path_connected_on V (subspace_topology Y TY V)"
        using hVo hyV hVU hVY hVpc unfolding neighborhood_of_def by (by100 blast)
    qed
  qed
qed




lemma R2_open_ball_path_connected:
  fixes c :: "real \<times> real" and r :: real
  assumes hr: "r > 0"
  defines "B \<equiv> {p. (fst p - fst c)^2 + (snd p - snd c)^2 < r^2}"
  shows "top1_path_connected_on B (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) B)"
proof -
  have hTR2: "is_topology_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
  proof -
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
    show ?thesis using product_topology_on_is_topology_on[OF hTR hTR] by simp
  qed
  show ?thesis unfolding top1_path_connected_on_def
  proof (intro conjI ballI)
  show "is_topology_on B (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) B)"
    by (rule subspace_topology_is_topology_on[OF hTR2]) simp
next
  fix a b assume ha: "a \<in> B" and hb: "b \<in> B"
  \<comment> \<open>The straight-line path from a to b stays in B (convexity of ball).\<close>
  define \<gamma> where "\<gamma> = (\<lambda>t::real. ((1-t) * fst a + t * fst b, (1-t) * snd a + t * snd b))"
  have h\<gamma>_path: "top1_is_path_on UNIV (product_topology_on top1_open_sets top1_open_sets) a b \<gamma>"
    unfolding \<gamma>_def by (rule R2_straight_line_path)
  \<comment> \<open>Show \<gamma>(t) \<in> B for all t \<in> [0,1] by convexity.\<close>
  have h\<gamma>_in_B: "\<forall>t\<in>I_set. \<gamma> t \<in> B"
  proof
    fix t assume ht: "t \<in> I_set"
    have htr: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
    \<comment> \<open>dist(c, \<gamma>(t))^2 = ((1-t)*(fst a - fst c) + t*(fst b - fst c))^2
         + ((1-t)*(snd a - snd c) + t*(snd b - snd c))^2.\<close>
    define da1 da2 db1 db2 where "da1 = fst a - fst c" and "da2 = snd a - snd c"
        and "db1 = fst b - fst c" and "db2 = snd b - snd c"
    have hda: "da1^2 + da2^2 < r^2" using ha unfolding B_def da1_def da2_def by simp
    have hdb: "db1^2 + db2^2 < r^2" using hb unfolding B_def db1_def db2_def by simp
    have hfst_eq: "fst (\<gamma> t) - fst c = (1-t)*da1 + t*db1"
      unfolding \<gamma>_def da1_def db1_def by (simp add: algebra_simps)
    have hsnd_eq: "snd (\<gamma> t) - snd c = (1-t)*da2 + t*db2"
      unfolding \<gamma>_def da2_def db2_def by (simp add: algebra_simps)
    \<comment> \<open>By convexity of x^2: ((1-t)*u + t*v)^2 \<le> (1-t)*u^2 + t*v^2.\<close>
    have hconv_sq: "\<And>u v. ((1-t)*u + t*v)^2 \<le> (1-t)*u^2 + t*v^2"
    proof -
      fix u v :: real
      have "((1-t)*u + t*v)^2 = (1-t)^2*u^2 + 2*(1-t)*t*u*v + t^2*v^2"
        by (simp add: power2_eq_square algebra_simps)
      also have "... \<le> (1-t)*u^2 + t*v^2"
      proof -
        \<comment> \<open>(1-t)*u^2 + t*v^2 - ((1-t)^2*u^2 + 2*(1-t)*t*u*v + t^2*v^2)
           = (1-t)*t*u^2 - 2*(1-t)*t*u*v + (1-t)*t*v^2 = (1-t)*t*(u-v)^2 \<ge> 0.\<close>
        have "(1-t)*u^2 + t*v^2 - ((1-t)^2*u^2 + 2*(1-t)*t*u*v + t^2*v^2)
            = (1-t)*t*(u-v)^2"
          by (simp add: power2_eq_square algebra_simps)
        moreover have "(1-t)*t*(u-v)^2 \<ge> 0" using htr by (auto intro: mult_nonneg_nonneg)
        ultimately show ?thesis by (by100 linarith)
      qed
      finally show "((1-t)*u + t*v)^2 \<le> (1-t)*u^2 + t*v^2" .
    qed
    have "(fst (\<gamma> t) - fst c)^2 + (snd (\<gamma> t) - snd c)^2
        = ((1-t)*da1 + t*db1)^2 + ((1-t)*da2 + t*db2)^2"
      using hfst_eq hsnd_eq by simp
    also have "... \<le> ((1-t)*da1^2 + t*db1^2) + ((1-t)*da2^2 + t*db2^2)"
      using hconv_sq[of da1 db1] hconv_sq[of da2 db2] by (by100 linarith)
    also have "... = (1-t)*(da1^2 + da2^2) + t*(db1^2 + db2^2)"
      by (simp add: algebra_simps)
    also have "... < (1-t)*r^2 + t*r^2"
    proof -
      have "(1-t) \<ge> 0" and "t \<ge> 0" using htr by auto
      \<comment> \<open>At least one of (1-t), t is > 0 (since t \<in> [0,1]).\<close>
      have "(1-t)*(da1^2+da2^2) \<le> (1-t)*r^2"
        using mult_left_mono[OF less_imp_le[OF hda] \<open>(1-t) \<ge> 0\<close>] by (by100 linarith)
      moreover have "t*(db1^2+db2^2) \<le> t*r^2"
        using mult_left_mono[OF less_imp_le[OF hdb] \<open>t \<ge> 0\<close>] by (by100 linarith)
      moreover have "(1-t)*(da1^2+da2^2) < (1-t)*r^2 \<or> t*(db1^2+db2^2) < t*r^2"
      proof (cases "t = 0")
        case True thus ?thesis using hda by simp
      next
        case False hence "t > 0" using htr by simp
        hence "t*(db1^2+db2^2) < t*r^2" using hdb by simp
        thus ?thesis by simp
      qed
      ultimately show ?thesis by linarith
    qed
    also have "... = r^2" by (simp add: algebra_simps)
    finally show "\<gamma> t \<in> B" unfolding B_def by simp
  qed
  \<comment> \<open>Restrict path to B.\<close>
  have h\<gamma>_cont: "top1_continuous_map_on I_set I_top UNIV
      (product_topology_on top1_open_sets top1_open_sets) \<gamma>"
    using h\<gamma>_path unfolding top1_is_path_on_def by (by100 blast)
  have h\<gamma>_img: "\<gamma> ` I_set \<subseteq> B" using h\<gamma>_in_B by (by100 blast)
  have hTI: "is_topology_on I_set I_top"
    unfolding top1_unit_interval_topology_def
    by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) (by100 simp)
  have h\<gamma>_cont_B: "top1_continuous_map_on I_set I_top B
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) B) \<gamma>"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix t assume "t \<in> I_set" thus "\<gamma> t \<in> B" using h\<gamma>_in_B by (by100 blast)
  next
    fix V :: "(real \<times> real) set"
    assume hV: "V \<in> subspace_topology UNIV (product_topology_on (top1_open_sets :: real set set) top1_open_sets) B"
    obtain W where hW: "W \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
        and hV_eq: "V = B \<inter> W" using hV unfolding subspace_topology_def by (by100 blast)
    have "{t \<in> I_set. \<gamma> t \<in> V} = {t \<in> I_set. \<gamma> t \<in> W} \<inter> {t \<in> I_set. \<gamma> t \<in> B}"
      unfolding hV_eq by (by100 blast)
    also have "... = {t \<in> I_set. \<gamma> t \<in> W}" using h\<gamma>_in_B by (by100 blast)
    finally have heq: "{t \<in> I_set. \<gamma> t \<in> V} = {t \<in> I_set. \<gamma> t \<in> W}" .
    have "{t \<in> I_set. \<gamma> t \<in> W} \<in> I_top"
      using h\<gamma>_cont hW unfolding top1_continuous_map_on_def by (by100 blast)
    thus "{t \<in> I_set. \<gamma> t \<in> V} \<in> I_top" using heq by simp
  qed
  have "\<gamma> 0 = a" unfolding \<gamma>_def by simp
  moreover have "\<gamma> 1 = b" unfolding \<gamma>_def by simp
  ultimately have "top1_is_path_on B
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) B) a b \<gamma>"
    unfolding top1_is_path_on_def using h\<gamma>_cont_B by (by100 blast)
  thus "\<exists>f. top1_is_path_on B
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) B) a b f"
    by (by100 blast)
  qed
qed

lemma R2_locally_path_connected:
  "top1_locally_path_connected_on (UNIV :: (real \<times> real) set)
     (product_topology_on top1_open_sets top1_open_sets)"
proof -
  let ?R2 = "product_topology_on (top1_open_sets :: real set set) top1_open_sets"
  have hTR2: "is_topology_on (UNIV :: (real \<times> real) set) ?R2"
  proof -
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
    show ?thesis using product_topology_on_is_topology_on[OF hTR hTR] by simp
  qed
  show ?thesis unfolding top1_locally_path_connected_on_def
  proof (intro conjI hTR2 ballI)
    fix x :: "real \<times> real" assume "x \<in> UNIV"
    show "top1_locally_path_connected_at UNIV ?R2 x"
      unfolding top1_locally_path_connected_at_def
    proof (intro allI impI)
      fix U assume hU: "neighborhood_of x UNIV ?R2 U \<and> U \<subseteq> UNIV"
      hence hUo: "U \<in> ?R2" and hxU: "x \<in> U" unfolding neighborhood_of_def by auto
      have hUo_std: "open U"
        using hUo product_topology_on_open_sets_real2 unfolding top1_open_sets_def by (by100 simp)
      \<comment> \<open>Get \<epsilon> > 0 with the custom "ball" B(x,\<epsilon>) \<subseteq> U.\<close>
      define Beps where "Beps = (\<lambda>\<epsilon>. {p :: real \<times> real. (fst p - fst x)^2 + (snd p - snd x)^2 < \<epsilon>^2})"
      \<comment> \<open>Every open set in R^2 contains a custom ball around each point.\<close>
      have "\<exists>\<epsilon>>0. Beps \<epsilon> \<subseteq> U"
      proof -
        \<comment> \<open>open U, x \<in> U \<Rightarrow> \<exists> open rectangle (a,b)\<times>(c,d) with x \<in> rect \<subseteq> U.\<close>
        obtain a1 b1 a2 b2 where hab: "a1 < fst x" "fst x < b1" "a2 < snd x" "snd x < b2"
            and hrect_sub: "{p :: real \<times> real. a1 < fst p \<and> fst p < b1 \<and> a2 < snd p \<and> snd p < b2} \<subseteq> U"

        proof -
          \<comment> \<open>open U, x \<in> U. By definition of product topology, \<exists> open U1, U2 with x \<in> U1\<times>U2 \<subseteq> U.\<close>
          obtain U1 U2 where hU1o: "open U1" and hU2o: "open U2"
              and hxUU: "x \<in> U1 \<times> U2" and hprod_sub: "U1 \<times> U2 \<subseteq> U"
            using open_prod_elim[OF hUo_std hxU] by blast
          have hx1: "fst x \<in> U1" and hx2: "snd x \<in> U2" using hxUU by auto
          obtain e1 where he1: "e1 > 0" and he1_sub: "\<forall>y. dist y (fst x) < e1 \<longrightarrow> y \<in> U1"
            using open_dist[THEN iffD1, OF hU1o, rule_format, OF hx1] by blast
          define a1 b1 where "a1 = fst x - e1" and "b1 = fst x + e1"
          have ha1: "a1 < fst x" and hb1: "fst x < b1" unfolding a1_def b1_def using he1 by auto
          have hab1: "{a1<..<b1} \<subseteq> U1"
          proof
            fix y assume "y \<in> {a1<..<b1}"
            hence "\<bar>y - fst x\<bar> < e1" unfolding a1_def b1_def by auto
            hence "dist y (fst x) < e1" unfolding dist_real_def by simp
            thus "y \<in> U1" using he1_sub by (by100 blast)
          qed
          obtain e2 where he2: "e2 > 0" and he2_sub: "\<forall>y. dist y (snd x) < e2 \<longrightarrow> y \<in> U2"
            using open_dist[THEN iffD1, OF hU2o, rule_format, OF hx2] by blast
          define a2 b2 where "a2 = snd x - e2" and "b2 = snd x + e2"
          have ha2: "a2 < snd x" and hb2: "snd x < b2" unfolding a2_def b2_def using he2 by auto
          have hab2: "{a2<..<b2} \<subseteq> U2"
          proof
            fix y assume "y \<in> {a2<..<b2}"
            hence "\<bar>y - snd x\<bar> < e2" unfolding a2_def b2_def by auto
            hence "dist y (snd x) < e2" unfolding dist_real_def by simp
            thus "y \<in> U2" using he2_sub by (by100 blast)
          qed
          have "{p :: real \<times> real. a1 < fst p \<and> fst p < b1 \<and> a2 < snd p \<and> snd p < b2} \<subseteq> U"
          proof
            fix p :: "real \<times> real"
            assume "p \<in> {p. a1 < fst p \<and> fst p < b1 \<and> a2 < snd p \<and> snd p < b2}"
            hence "fst p \<in> {a1<..<b1}" and "snd p \<in> {a2<..<b2}" by auto
            hence "fst p \<in> U1" and "snd p \<in> U2" using hab1 hab2 by (by100 blast)+
            hence "p \<in> U1 \<times> U2" by (cases p) auto
            thus "p \<in> U" using hprod_sub by (by100 blast)
          qed
          show ?thesis
            using that[OF ha1 hb1 ha2 hb2
              \<open>{p :: real \<times> real. a1 < fst p \<and> fst p < b1 \<and> a2 < snd p \<and> snd p < b2} \<subseteq> U\<close>]
            by simp
        qed
        define \<epsilon> where "\<epsilon> = min (min (fst x - a1) (b1 - fst x)) (min (snd x - a2) (b2 - snd x))"
        have h\<epsilon>: "\<epsilon> > 0" unfolding \<epsilon>_def using hab by auto
        have "Beps \<epsilon> \<subseteq> {p. a1 < fst p \<and> fst p < b1 \<and> a2 < snd p \<and> snd p < b2}"
        proof
          fix p assume "p \<in> Beps \<epsilon>"
          hence hdist: "(fst p - fst x)^2 + (snd p - snd x)^2 < \<epsilon>^2" unfolding Beps_def by simp
          have hfst: "(fst p - fst x)^2 < \<epsilon>^2"
          proof -
            have "(snd p - snd x)^2 \<ge> 0" by simp
            thus ?thesis using hdist by (by100 linarith)
          qed
          have hsnd: "(snd p - snd x)^2 < \<epsilon>^2"
          proof -
            have "(fst p - fst x)^2 \<ge> 0" by simp
            thus ?thesis using hdist by (by100 linarith)
          qed
          have hfst_abs: "fst x - \<epsilon> < fst p \<and> fst p < fst x + \<epsilon>"
          proof -
            have "fst p - fst x < \<epsilon> \<and> fst x - fst p < \<epsilon>"
            proof (intro conjI)
              show "fst p - fst x < \<epsilon>"
              proof (rule ccontr)
                assume "\<not> fst p - fst x < \<epsilon>"
                hence "fst p - fst x \<ge> \<epsilon>" by simp
                hence "(fst p - fst x)^2 \<ge> \<epsilon>^2" unfolding power2_eq_square
                  using mult_mono'[of \<epsilon> "fst p - fst x" \<epsilon> "fst p - fst x"] h\<epsilon> by (by100 linarith)
                thus False using hfst by (by100 linarith)
              qed
              show "fst x - fst p < \<epsilon>"
              proof (rule ccontr)
                assume "\<not> fst x - fst p < \<epsilon>"
                hence "fst x - fst p \<ge> \<epsilon>" by simp
                hence "(fst x - fst p)^2 \<ge> \<epsilon>^2" unfolding power2_eq_square
                  using mult_mono'[of \<epsilon> "fst x - fst p" \<epsilon> "fst x - fst p"] h\<epsilon> by (by100 linarith)
                moreover have "(fst x - fst p)^2 = (fst p - fst x)^2"
                  unfolding power2_eq_square by (simp add: algebra_simps)
                ultimately show False using hfst by (by100 linarith)
              qed
            qed
            thus ?thesis by (by100 linarith)
          qed
          have hsnd_abs: "snd x - \<epsilon> < snd p \<and> snd p < snd x + \<epsilon>"
          proof -
            have "snd p - snd x < \<epsilon> \<and> snd x - snd p < \<epsilon>"
            proof (intro conjI)
              show "snd p - snd x < \<epsilon>"
              proof (rule ccontr)
                assume "\<not> snd p - snd x < \<epsilon>"
                hence "snd p - snd x \<ge> \<epsilon>" by simp
                hence "(snd p - snd x)^2 \<ge> \<epsilon>^2" unfolding power2_eq_square
                  using mult_mono'[of \<epsilon> "snd p - snd x" \<epsilon> "snd p - snd x"] h\<epsilon> by (by100 linarith)
                thus False using hsnd by (by100 linarith)
              qed
              show "snd x - snd p < \<epsilon>"
              proof (rule ccontr)
                assume "\<not> snd x - snd p < \<epsilon>"
                hence "snd x - snd p \<ge> \<epsilon>" by simp
                hence "(snd x - snd p)^2 \<ge> \<epsilon>^2" unfolding power2_eq_square
                  using mult_mono'[of \<epsilon> "snd x - snd p" \<epsilon> "snd x - snd p"] h\<epsilon> by (by100 linarith)
                moreover have "(snd x - snd p)^2 = (snd p - snd x)^2"
                  unfolding power2_eq_square by (simp add: algebra_simps)
                ultimately show False using hsnd by (by100 linarith)
              qed
            qed
            thus ?thesis by (by100 linarith)
          qed
          have "a1 < fst p" using hfst_abs unfolding \<epsilon>_def by (by100 linarith)
          moreover have "fst p < b1" using hfst_abs unfolding \<epsilon>_def by (by100 linarith)
          moreover have "a2 < snd p" using hsnd_abs unfolding \<epsilon>_def by (by100 linarith)
          moreover have "snd p < b2" using hsnd_abs unfolding \<epsilon>_def by (by100 linarith)
          ultimately show "p \<in> {p. a1 < fst p \<and> fst p < b1 \<and> a2 < snd p \<and> snd p < b2}"
            by (by100 blast)
        qed
        hence "Beps \<epsilon> \<subseteq> U" using hrect_sub by (by100 blast)
        thus ?thesis using h\<epsilon> by (by100 blast)
      qed
      then obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" and hB_sub: "Beps \<epsilon> \<subseteq> U" by blast
      \<comment> \<open>Beps \<epsilon> is open in R^2.\<close>
      have hB_open: "open (Beps \<epsilon>)"
      proof -
        have "Beps \<epsilon> = (\<lambda>p :: real \<times> real. (fst p - fst x)^2 + (snd p - snd x)^2) -` {..< \<epsilon>^2}"
          unfolding Beps_def by auto
        moreover have "continuous_on UNIV (\<lambda>p :: real \<times> real. (fst p - fst x)^2 + (snd p - snd x)^2)"
          by (intro continuous_intros)
        hence "open ((\<lambda>p :: real \<times> real. (fst p - fst x)^2 + (snd p - snd x)^2) -` {..< \<epsilon>^2})"
          by (simp add: continuous_on_open_vimage[OF open_UNIV] open_lessThan)
        ultimately show ?thesis by simp
      qed
      have hB_R2: "Beps \<epsilon> \<in> ?R2"
        using hB_open product_topology_on_open_sets_real2 unfolding top1_open_sets_def by (by100 simp)
      \<comment> \<open>x \<in> Beps \<epsilon>.\<close>
      have hx_B: "x \<in> Beps \<epsilon>" unfolding Beps_def using h\<epsilon> by simp
      \<comment> \<open>Beps \<epsilon> is path-connected.\<close>
      have hB_pc: "top1_path_connected_on (Beps \<epsilon>)
          (subspace_topology UNIV ?R2 (Beps \<epsilon>))"
        unfolding Beps_def by (rule R2_open_ball_path_connected[OF h\<epsilon>])
      show "\<exists>V. neighborhood_of x UNIV ?R2 V \<and> V \<subseteq> U \<and> V \<subseteq> UNIV
           \<and> top1_path_connected_on V (subspace_topology UNIV ?R2 V)"
        apply (rule exI[of _ "Beps \<epsilon>"])
        unfolding neighborhood_of_def
        using hB_R2 hx_B hB_sub hB_pc by (by100 blast)
    qed
  qed
qed


lemma S2_locally_path_connected:
  "top1_locally_path_connected_on top1_S2 top1_S2_topology"
  unfolding top1_locally_path_connected_on_def
proof (intro conjI ballI)
  show "is_topology_on top1_S2 top1_S2_topology"
    using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
next
  fix x assume hx: "x \<in> top1_S2"
  define south where "south = (0::real, 0::real, -1::real)"
  have hs_S2: "south \<in> top1_S2" unfolding south_def top1_S2_def by simp
  have hn_S2: "north_pole \<in> top1_S2" unfolding north_pole_def top1_S2_def by simp
  have hns: "north_pole \<noteq> south" unfolding north_pole_def south_def by simp
  define b where "b = (if x \<noteq> north_pole then north_pole else south)"
  have hb_S2: "b \<in> top1_S2" unfolding b_def using hn_S2 hs_S2 by auto
  have hxb: "x \<noteq> b" unfolding b_def using hns by auto
  have hx_in: "x \<in> top1_S2 - {b}" using hx hxb by (by100 blast)
  \<comment> \<open>S^2-{b} open in S^2 and lpc (homeomorphic to R^2).\<close>
  have hS2b_open: "top1_S2 - {b} \<in> top1_S2_topology"
  proof -
    have "closedin_on top1_S2 top1_S2_topology {b}"
    proof (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff
        top1_S2_is_topology_on_strict])
      show "{b} \<subseteq> top1_S2" using hb_S2 by simp
      show "top1_compact_on {b} (subspace_topology top1_S2 top1_S2_topology {b})"
        unfolding top1_compact_on_def
      proof (intro conjI allI impI)
        show "is_topology_on {b} (subspace_topology top1_S2 top1_S2_topology {b})"
          by (rule subspace_topology_is_topology_on[OF
              is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict]]) (simp add: hb_S2)
      next
        fix C :: "(real \<times> real \<times> real) set set"
        assume hC: "C \<subseteq> subspace_topology top1_S2 top1_S2_topology {b} \<and> {b} \<subseteq> \<Union>C"
        then obtain U where "U \<in> C" "b \<in> U" by (by100 blast)
        thus "\<exists>F. finite F \<and> F \<subseteq> C \<and> {b} \<subseteq> \<Union>F"
          by (intro exI[of _ "{U}"]) simp
      qed
    qed
    thus ?thesis unfolding closedin_on_def
      using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def is_topology_on_def
      by (by100 blast)
  qed
  have hS2b_lpc: "top1_locally_path_connected_on (top1_S2 - {b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))"
  proof -
    obtain hh where hh: "top1_homeomorphism_on (top1_S2 - {b})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
        (UNIV :: (real \<times> real) set)
        (product_topology_on top1_open_sets top1_open_sets) hh"
      using S2_minus_point_homeo_R2[OF hb_S2] by blast
    show ?thesis
      by (rule homeomorphism_preserves_lpc[OF homeomorphism_inverse[OF hh] R2_locally_path_connected])
  qed
  \<comment> \<open>x \<in> S^2-{b} which is open and lpc. So x is lpc at in S^2.\<close>
  show "top1_locally_path_connected_at top1_S2 top1_S2_topology x"
    unfolding top1_locally_path_connected_at_def
  proof (intro allI impI)
    fix U assume hU: "neighborhood_of x top1_S2 top1_S2_topology U \<and> U \<subseteq> top1_S2"
    hence hUo: "U \<in> top1_S2_topology" and hxU: "x \<in> U"
      unfolding neighborhood_of_def by auto
    \<comment> \<open>U \<inter> (S^2-{b}) is a neighborhood of x in S^2-{b}.\<close>
    have hUV: "U \<inter> (top1_S2 - {b}) \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
      unfolding subspace_topology_def using hUo by (by100 blast)
    have hxUV: "x \<in> U \<inter> (top1_S2 - {b})" using hxU hx_in by (by100 blast)
    have hUV_sub: "U \<inter> (top1_S2 - {b}) \<subseteq> top1_S2 - {b}" by (by100 blast)
    have hUV_nbhd: "neighborhood_of x (top1_S2 - {b})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) (U \<inter> (top1_S2 - {b}))"
      unfolding neighborhood_of_def using hUV hxUV by (by100 blast)
    \<comment> \<open>By lpc of S^2-{b}: get path-connected W \<subseteq> U \<inter> (S^2-{b}).\<close>
    have "top1_locally_path_connected_at (top1_S2 - {b})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) x"
      using hS2b_lpc hx_in unfolding top1_locally_path_connected_on_def by (by100 blast)
    hence "\<exists>W. neighborhood_of x (top1_S2 - {b})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) W \<and>
        W \<subseteq> U \<inter> (top1_S2 - {b}) \<and> W \<subseteq> top1_S2 - {b} \<and>
        top1_path_connected_on W (subspace_topology (top1_S2 - {b})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) W)"
      unfolding top1_locally_path_connected_at_def using hUV_nbhd hUV_sub by (by100 blast)
    then obtain W where hW_nbhd: "neighborhood_of x (top1_S2 - {b})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) W"
        and hW_sub_U: "W \<subseteq> U" and hW_sub_S2b: "W \<subseteq> top1_S2 - {b}"
        and hW_pc: "top1_path_connected_on W (subspace_topology (top1_S2 - {b})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) W)"
      by (by100 blast)
    \<comment> \<open>W is open in S^2-{b}, which is open in S^2, so W is open in S^2.\<close>
    have hW_open_S2b: "\<exists>V'. V' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}) \<and> x \<in> V' \<and> V' \<subseteq> W"
      using hW_nbhd unfolding neighborhood_of_def by (by100 blast)
    then obtain W' where hW'o: "W' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
        and hxW': "x \<in> W'" and hW'W: "W' \<subseteq> W" by blast
    \<comment> \<open>W' open in S^2-{b} = S^2 \<inter> V for some V \<in> top1_S2_topology.\<close>
    obtain V' where hV': "V' \<in> top1_S2_topology" and hW'_eq: "W' = (top1_S2 - {b}) \<inter> V'"
      using hW'o unfolding subspace_topology_def by (by100 blast)
    \<comment> \<open>W' \<in> top1_S2_topology (open in S^2).\<close>
    have hTS2': "is_topology_on top1_S2 top1_S2_topology"
      using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
    have "W' \<in> top1_S2_topology"
    proof -
      have "(top1_S2 - {b}) \<inter> V' \<in> top1_S2_topology"
        by (rule topology_inter_open[OF hTS2' hS2b_open hV'])
      thus ?thesis using hW'_eq by simp
    qed
    \<comment> \<open>W' is a neighborhood of x in S^2, W' \<subseteq> W \<subseteq> U, path-connected.\<close>
    have hW_pc_S2: "top1_path_connected_on W (subspace_topology top1_S2 top1_S2_topology W)"
    proof -
      have "subspace_topology (top1_S2 - {b})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) W
        = subspace_topology top1_S2 top1_S2_topology W"
        by (rule subspace_topology_trans[OF hW_sub_S2b])
      thus ?thesis using hW_pc by simp
    qed
    have hW_sub_S2: "W \<subseteq> top1_S2" using hW_sub_S2b by (by100 blast)
    have hW_open_S2: "W \<in> top1_S2_topology"
    proof -
      \<comment> \<open>W is a neighborhood in S^2-{b}, so W open in S^2-{b}.\<close>
      have "W \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
        using hW_nbhd unfolding neighborhood_of_def by simp
      then obtain Wo where hWo: "Wo \<in> top1_S2_topology" "W = (top1_S2 - {b}) \<inter> Wo"
        unfolding subspace_topology_def by (by100 blast)
      show ?thesis using topology_inter_open[OF hTS2' hS2b_open hWo(1)] hWo(2) by simp
    qed
    have hxW: "x \<in> W" using hW_nbhd unfolding neighborhood_of_def by simp
    have hW_nbhd_S2: "neighborhood_of x top1_S2 top1_S2_topology W"
      unfolding neighborhood_of_def using hW_open_S2 hxW by simp
    show "\<exists>V. neighborhood_of x top1_S2 top1_S2_topology V \<and> V \<subseteq> U \<and> V \<subseteq> top1_S2 \<and>
        top1_path_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
      using hW_nbhd_S2 hW_sub_U hW_sub_S2 hW_pc_S2 by (by100 blast)
  qed
qed

lemma path_connected_imp_connected:
  assumes "top1_path_connected_on X TX"
  shows "top1_connected_on X TX"
proof -
  have hTX: "is_topology_on X TX" using assms unfolding top1_path_connected_on_def by (by100 blast)
  show ?thesis unfolding top1_connected_on_def
  proof (intro conjI)
    show "is_topology_on X TX" by (rule hTX)
    show "\<nexists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
    proof (rule notI)
      assume "\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X"
      then obtain U V where hU: "U \<in> TX" and hV: "V \<in> TX" and hUne: "U \<noteq> {}"
          and hVne: "V \<noteq> {}" and hdisj: "U \<inter> V = {}" and hcover: "U \<union> V = X" by blast
      obtain x where hx: "x \<in> U" using hUne by blast
      obtain y where hy: "y \<in> V" using hVne by blast
      have hxX: "x \<in> X" using hx hcover by (by100 blast)
      have hyX: "y \<in> X" using hy hcover by (by100 blast)
      obtain f where hf: "top1_is_path_on X TX x y f"
        using assms hxX hyX unfolding top1_path_connected_on_def by (by100 blast)
      \<comment> \<open>f(I) connected (continuous image of connected [0,1]). Intersects both U and V.
         But U, V separate X \<supseteq> f(I). Contradiction.\<close>
      have hfI_conn: "top1_connected_on (f ` I_set) (subspace_topology X TX (f ` I_set))"
      proof -
        have hI_top: "is_topology_on I_set I_top"
          unfolding top1_unit_interval_topology_def
          by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) simp
        have hI_conn: "top1_connected_on I_set I_top"
        proof -
          have hI_01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
            by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
          have "connected {0..1::real}" by (rule connected_Icc)
          hence "connected I_set" using hI_01 by simp
          thus ?thesis
            unfolding top1_unit_interval_topology_def
            using top1_connected_on_subspace_openI by (by100 blast)
        qed
        have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
          using hf unfolding top1_is_path_on_def by (by100 blast)
        show ?thesis by (rule Theorem_23_5[OF hI_top hTX hI_conn hf_cont])
      qed
      \<comment> \<open>f(I) \<subseteq> U \<union> V = X, f(0) = x \<in> U, f(1) = y \<in> V.
         So f(I) \<inter> U \<noteq> {} and f(I) \<inter> V \<noteq> {}.
         U \<inter> f(I) and V \<inter> f(I) are open in subspace of f(I), disjoint, cover f(I).
         This contradicts f(I) connected.\<close>
      have hfI_sub: "f ` I_set \<subseteq> X"
        using hf unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
      have "f 0 = x" using hf unfolding top1_is_path_on_def by (by100 blast)
      have "f 1 = y" using hf unfolding top1_is_path_on_def by (by100 blast)
      have h0_I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      have h1_I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      have hfU: "f ` I_set \<inter> U \<noteq> {}" using \<open>f 0 = x\<close> hx h0_I by (by100 blast)
      have hfV: "f ` I_set \<inter> V \<noteq> {}" using \<open>f 1 = y\<close> hy h1_I by (by100 blast)
      have "U \<inter> f ` I_set \<in> subspace_topology X TX (f ` I_set)"
        using hU unfolding subspace_topology_def by (by100 blast)
      moreover have "V \<inter> f ` I_set \<in> subspace_topology X TX (f ` I_set)"
        using hV unfolding subspace_topology_def by (by100 blast)
      moreover have "U \<inter> f ` I_set \<noteq> {}" using hfU by (by100 blast)
      moreover have "V \<inter> f ` I_set \<noteq> {}" using hfV by (by100 blast)
      moreover have "(U \<inter> f ` I_set) \<inter> (V \<inter> f ` I_set) = {}" using hdisj by (by100 blast)
      moreover have "(U \<inter> f ` I_set) \<union> (V \<inter> f ` I_set) = f ` I_set"
        using hfI_sub hcover by (by100 blast)
      ultimately show False using hfI_conn unfolding top1_connected_on_def by (by100 blast)
    qed
  qed
qed


lemma S2_connected: "top1_connected_on top1_S2 top1_S2_topology"
proof -
  \<comment> \<open>S^2\{N} simply connected \<Rightarrow> path connected \<Rightarrow> connected.\<close>
  have hn_S2: "north_pole \<in> top1_S2" unfolding north_pole_def top1_S2_def by simp
  have "top1_simply_connected_on (top1_S2 - {north_pole})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
    by (rule S2_minus_point_simply_connected[OF hn_S2])
  hence "top1_path_connected_on (top1_S2 - {north_pole})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
    unfolding top1_simply_connected_on_def by (by100 blast)
  hence hN_conn: "top1_connected_on (top1_S2 - {north_pole})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {north_pole}))"
    by (rule path_connected_imp_connected)
  \<comment> \<open>S^2 = closure(S^2\{N}). N is a limit point.\<close>
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
  have "top1_S2 \<subseteq> closure_on top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
  proof -
    \<comment> \<open>N \<in> closure(S^2\{N}): every closed C \<supseteq> S^2\{N} contains N.
       If C closed and C \<supseteq> S^2\{N}, then S^2\C \<subseteq> {N}. S^2\C open.
       {N} not open in S^2 (Hausdorff + |S^2| \<ge> 2 implies non-discrete).
       So S^2\C = {}, C = S^2, N \<in> C.\<close>
    have "north_pole \<in> closure_on top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
      unfolding closure_on_def
    proof (rule InterI)
      fix C' assume "C' \<in> {C. closedin_on top1_S2 top1_S2_topology C \<and> top1_S2 - {north_pole} \<subseteq> C}"
      hence hC_closed: "closedin_on top1_S2 top1_S2_topology C'" and hC_sup: "top1_S2 - {north_pole} \<subseteq> C'"
        by auto
      show "north_pole \<in> C'"
      proof -
        have hC_sub: "C' \<subseteq> top1_S2" using hC_closed unfolding closedin_on_def by (by100 blast)
        have "top1_S2 - C' \<subseteq> {north_pole}" using hC_sup by (by100 blast)
        have "top1_S2 - C' \<in> top1_S2_topology"
          using hC_closed hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
        have "top1_S2 - C' = {}"
        proof (rule ccontr)
          assume "top1_S2 - C' \<noteq> {}"
          hence "top1_S2 - C' = {north_pole}"
            using \<open>top1_S2 - C' \<subseteq> {north_pole}\<close> by (by100 blast)
          hence "{north_pole} \<in> top1_S2_topology" using \<open>top1_S2 - C' \<in> top1_S2_topology\<close> by simp
          \<comment> \<open>{N} \<in> S^2_top = subspace UNIV R^3_open S^2. So {N} = S^2 \<inter> W for open W \<subseteq> R^3.
             W open in R^3 and N \<in> W \<Rightarrow> B(N,\<epsilon>) \<subseteq> W.
             But B(N,\<epsilon>) \<inter> S^2 contains e.g. (0,sin(\<epsilon>/2),cos(\<epsilon>/2)) \<noteq> N.
             So {N} \<subsetneq> S^2 \<inter> W. Contradiction.\<close>
          \<comment> \<open>{N} = S^2 \<inter> W for open W. W contains ball B(N,\<epsilon>).
             Point (0, \<epsilon>/3, sqrt(1-(\<epsilon>/3)^2)) \<in> S^2 \<inter> B(N,\<epsilon>) and \<noteq> N.\<close>
          \<comment> \<open>{N} \<in> S^2_top means {N} = S^2 \<inter> W for open W in R^3.
             W contains B(N,\<epsilon>). Point (0, \<epsilon>/2, sqrt(1-\<epsilon>^2/4)) \<in> S^2 \<inter> B(N,\<epsilon>), \<noteq> N.\<close>
          have hR3eq: "(product_topology_on (top1_open_sets :: real set set)
              (product_topology_on (top1_open_sets :: real set set) (top1_open_sets :: real set set)))
              = (top1_open_sets :: (real \<times> real \<times> real) set set)"
            using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                  product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
          have "top1_S2_topology = subspace_topology UNIV
              (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
            unfolding top1_S2_topology_def using hR3eq by simp
          then obtain W where "W \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
              "{north_pole} = top1_S2 \<inter> W"
            using \<open>{north_pole} \<in> top1_S2_topology\<close> unfolding subspace_topology_def
            by (by100 blast)
          have "open W" using \<open>W \<in> top1_open_sets\<close> unfolding top1_open_sets_def by simp
          \<comment> \<open>W open in R^3, N \<in> W. Use open_prod_elim to get intervals around N.\<close>
          have "north_pole \<in> W" using \<open>{north_pole} = top1_S2 \<inter> W\<close> hn_S2 by (by100 blast)
          \<comment> \<open>W open in R × (R × R). Get open intervals around each coordinate of N=(0,0,1).\<close>
          obtain U1 U23 where hU1: "open U1" and hU23: "open U23"
              and "north_pole \<in> U1 \<times> U23" and "U1 \<times> U23 \<subseteq> W"
            using open_prod_elim[OF \<open>open W\<close> \<open>north_pole \<in> W\<close>] by (by100 blast)
          hence h0_U1: "(0::real) \<in> U1" unfolding north_pole_def by simp
          \<comment> \<open>U23 open, (0,1) \<in> U23. Get \<epsilon>>0 s.t. points near (0,1) in U23.\<close>
          have "(0::real, 1::real) \<in> U23" using \<open>north_pole \<in> U1 \<times> U23\<close> unfolding north_pole_def by simp
          obtain U2 U3 where hU2: "open U2" and hU3: "open U3"
              and h01_U23: "(0::real) \<in> U2" "(1::real) \<in> U3" and "U2 \<times> U3 \<subseteq> U23"
          proof -
            from open_prod_elim[OF hU23 \<open>(0::real, 1::real) \<in> U23\<close>]
            obtain A B where "open A" "open B" "(0::real, 1::real) \<in> A \<times> B" "A \<times> B \<subseteq> U23" by blast
            thus ?thesis using that by auto
          qed
          \<comment> \<open>Get \<epsilon>1 > 0 s.t. |y| < \<epsilon>1 \<Rightarrow> y \<in> U2, and \<epsilon>2 > 0 s.t. |y-1| < \<epsilon>2 \<Rightarrow> y \<in> U3.\<close>
          obtain \<epsilon>1 where h\<epsilon>1: "\<epsilon>1 > 0" "\<forall>y::real. dist y 0 < \<epsilon>1 \<longrightarrow> y \<in> U2"
          proof -
            have "\<exists>e>0. \<forall>y. dist y (0::real) < e \<longrightarrow> y \<in> U2"
              using hU2 h01_U23(1) unfolding open_dist by (by100 blast)
            thus ?thesis using that by blast
          qed
          obtain \<epsilon>2 where h\<epsilon>2: "\<epsilon>2 > 0" "\<forall>y::real. dist y 1 < \<epsilon>2 \<longrightarrow> y \<in> U3"
          proof -
            have "\<exists>e>0. \<forall>y. dist y (1::real) < e \<longrightarrow> y \<in> U3"
              using hU3 h01_U23(2) unfolding open_dist by (by100 blast)
            thus ?thesis using that by blast
          qed
          \<comment> \<open>Choose t small enough for both U2 and U3.\<close>
          define t where "t = min (min (\<epsilon>1/2) (1/2)) (sqrt \<epsilon>2)"
          have ht: "t > 0" "t \<le> 1/2" "t < \<epsilon>1" unfolding t_def using h\<epsilon>1(1) h\<epsilon>2(1) by auto
          define p where "p = (0::real, t, sqrt (1 - t^2))"
          have hp_S2: "p \<in> top1_S2" unfolding p_def top1_S2_def
          proof simp
            have "t^2 \<le> (1/2)^2" using ht(2) ht(1) by (intro power_mono) simp_all
            hence "t^2 \<le> 1/4" by (simp add: power2_eq_square)
            hence h_nneg: "1 - t^2 \<ge> 0" by simp
            show "t\<^sup>2 + (sqrt (1 - t\<^sup>2))\<^sup>2 = 1"
              using real_sqrt_pow2[OF h_nneg] by simp
          qed
          have hp_ne_N: "p \<noteq> north_pole" unfolding p_def north_pole_def using ht(1) by auto
          have "p \<in> W"
          proof -
            have "fst p \<in> U1" unfolding p_def using h0_U1 by simp
            have "fst (snd p) \<in> U2"
            proof -
              have "\<bar>t\<bar> < \<epsilon>1" using ht(3) ht(1) by simp
              thus ?thesis unfolding p_def using h\<epsilon>1(2) by simp
            qed
            have "snd (snd p) \<in> U3"
            proof -
              have "t^2 \<le> (1/2)^2" using ht(2) ht(1) by (intro power_mono) simp_all
              hence ht2_le: "t^2 \<le> 1/4" by (simp add: power2_eq_square)
              hence h_nneg: "1 - t^2 \<ge> 0" by simp
              have hsqrt_le: "sqrt (1 - t^2) \<le> 1" using real_sqrt_le_mono[of "1-t^2" 1] h_nneg by simp
              have hsqrt_ge: "sqrt (1 - t^2) \<ge> 0" using h_nneg by simp
              \<comment> \<open>dist (sqrt(1-t^2)) 1 = 1 - sqrt(1-t^2).\<close>
              have hdist_eq: "dist (sqrt (1 - t^2)) 1 = 1 - sqrt (1 - t^2)"
                using hsqrt_le by (simp add: dist_real_def)
              \<comment> \<open>1 - sqrt(1-t^2) = t^2 / (1 + sqrt(1-t^2)) < t^2.\<close>
              \<comment> \<open>Key: 1 - sqrt(1-t^2) = t^2/(1+sqrt(1-t^2)) < t^2 \<le> \<epsilon>2.\<close>
              have "t \<le> sqrt \<epsilon>2" unfolding t_def by simp
              hence "t^2 \<le> (sqrt \<epsilon>2)^2" using ht(1) h\<epsilon>2(1)
                by (intro power_mono) simp_all
              hence ht2_eps: "t^2 \<le> \<epsilon>2" using h\<epsilon>2(1) by simp
              have "dist (sqrt (1 - t^2)) 1 < \<epsilon>2"
              proof -
                have "(1 - sqrt (1 - t^2)) * (1 + sqrt (1 - t^2)) = t^2"
                  using real_sqrt_pow2[OF h_nneg] by (simp add: algebra_simps power2_eq_square)
                have "1 - t^2 > 0" using ht2_le by simp
                hence "sqrt (1 - t^2) > 0" by simp
                hence "1 + sqrt (1 - t^2) > 1" by simp
                have h_a_nneg: "1 - sqrt (1 - t^2) \<ge> 0" using hsqrt_le by simp
                have "t^2 = (1 - sqrt (1 - t^2)) * (1 + sqrt (1 - t^2))"
                  using \<open>(1 - sqrt (1 - t^2)) * (1 + sqrt (1 - t^2)) = t^2\<close> by simp
                also have "... > (1 - sqrt (1 - t^2)) * 1"
                proof (rule mult_strict_left_mono)
                  show "(1::real) < 1 + sqrt (1 - t^2)" using \<open>1 + sqrt (1 - t^2) > 1\<close> .
                  show "0 < 1 - sqrt (1 - t^2)"
                  proof -
                    have "sqrt (1 - t^2) < sqrt 1" by (rule real_sqrt_less_mono) (use \<open>1 - t^2 > 0\<close> ht(1) in simp_all)
                    thus ?thesis by simp
                  qed
                qed
                finally have "1 - sqrt (1 - t^2) < t^2" by simp
                thus ?thesis using ht2_eps hdist_eq by simp
              qed
              thus ?thesis unfolding p_def using h\<epsilon>2(2) by simp
            qed
            have "snd p \<in> U2 \<times> U3" using \<open>fst (snd p) \<in> U2\<close> \<open>snd (snd p) \<in> U3\<close>
              unfolding p_def by simp
            hence "snd p \<in> U23" using \<open>U2 \<times> U3 \<subseteq> U23\<close> by auto
            hence "p \<in> U1 \<times> U23" using \<open>fst p \<in> U1\<close>
              unfolding mem_Times_iff by simp
            thus ?thesis using \<open>U1 \<times> U23 \<subseteq> W\<close> by auto
          qed
          have "p \<in> top1_S2 \<inter> W" using hp_S2 \<open>p \<in> W\<close> by (by100 blast)
          hence "p \<in> {north_pole}" using \<open>{north_pole} = top1_S2 \<inter> W\<close> by simp
          thus False using hp_ne_N by simp
        qed
        thus ?thesis using hn_S2 by (by100 blast)
      qed
    qed
    moreover have "top1_S2 - {north_pole} \<subseteq> closure_on top1_S2 top1_S2_topology (top1_S2 - {north_pole})"
      by (rule subset_closure_on)
    ultimately show ?thesis by (by100 blast)
  qed
  have "top1_connected_on top1_S2 (subspace_topology top1_S2 top1_S2_topology top1_S2)"
    by (rule Theorem_23_4[OF hTS2 _ _ _ _ hN_conn])
       (use \<open>top1_S2 \<subseteq> closure_on top1_S2 top1_S2_topology (top1_S2 - {north_pole})\<close> in blast)+
  moreover have "subspace_topology top1_S2 top1_S2_topology top1_S2 = top1_S2_topology"
  proof -
    have "\<forall>U \<in> top1_S2_topology. U \<subseteq> top1_S2"
      using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def is_topology_on_def
      by (by100 blast)
    thus ?thesis by (rule subspace_topology_self_carrier)
  qed
  ultimately show ?thesis by simp
qed

lemma singleton_not_open_in_S2:
  assumes "x \<in> top1_S2"
  shows "{x} \<notin> top1_S2_topology"
proof
  assume hopen: "{x} \<in> top1_S2_topology"
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
  have hS2x_open: "top1_S2 - {x} \<in> top1_S2_topology"
    using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff assms]
    hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
  have "top1_S2 - {x} \<noteq> {}"
  proof -
    define y where "y = (if x = north_pole then (0::real, 0::real, -1::real) else north_pole)"
    have "y \<in> top1_S2" unfolding y_def north_pole_def top1_S2_def by auto
    have "y \<noteq> x" unfolding y_def north_pole_def by auto
    thus ?thesis using \<open>y \<in> top1_S2\<close> \<open>y \<noteq> x\<close> by (by100 blast)
  qed
  have "\<not> top1_connected_on top1_S2 top1_S2_topology"
    unfolding top1_connected_on_def
    using hTS2 hopen hS2x_open assms \<open>top1_S2 - {x} \<noteq> {}\<close> by (by100 blast)
  thus False using S2_connected by simp
qed

lemma Lemma_61_1_components_correspond:
  fixes h :: "(real \<times> real \<times> real) \<Rightarrow> (real \<times> real)" and C :: "(real \<times> real \<times> real) set"
    and b :: "real \<times> real \<times> real" and U :: "(real \<times> real \<times> real) set"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "C \<subseteq> top1_S2"
      and "top1_compact_on C (subspace_topology top1_S2 top1_S2_topology C)"
      and "b \<in> top1_S2 - C"
      and "top1_homeomorphism_on (top1_S2 - {b})
             (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
             (UNIV::(real \<times> real) set)
             (product_topology_on top1_open_sets top1_open_sets) h"
      and "top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
      and "U \<subseteq> top1_S2 - C"
      and "U \<in> top1_components_on (top1_S2 - C) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
  shows "(b \<notin> U \<longrightarrow> (\<exists>M. \<forall>x\<in>U. fst (h x) ^ 2 + snd (h x) ^ 2 \<le> M))
       \<and> (b \<in> U \<longrightarrow> (\<forall>M. \<exists>x\<in>U - {b}. fst (h x) ^ 2 + snd (h x) ^ 2 > M))"
proof -
  \<comment> \<open>Munkres 61.1: h maps components of S^2-C to components of R^2-h(C).
     Step 1: h(C) is compact (continuous image of compact), hence bounded in R^2.
     Step 2: Components of S^2-C not containing b map to bounded components of R^2-h(C)
     (since h|_{S^2-b} is a homeomorphism, connected components correspond).
     Step 3: The component containing b maps to the complement of a bounded set,
     which is unbounded.\<close>
  have hb_not_C: "b \<notin> C" using assms(4) by (by100 blast)
  hence hCb_eq: "C - {b} = C" by (by100 blast)
  have hC_sub_S2b: "C \<subseteq> top1_S2 - {b}" using assms(2) hb_not_C by (by100 blast)
  have hh_cont: "top1_continuous_map_on (top1_S2 - {b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
      UNIV (product_topology_on top1_open_sets top1_open_sets) h"
    using assms(5) unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTS2b: "is_topology_on (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))"
    using assms(5) unfolding top1_homeomorphism_on_def by (by100 blast)
  \<comment> \<open>C \<subseteq> S^2-{b}, so subspace topology on C matches.\<close>
  have hC_compact_S2b: "top1_compact_on C (subspace_topology (top1_S2 - {b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) C)"
  proof -
    have "subspace_topology (top1_S2 - {b})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) C
        = subspace_topology top1_S2 top1_S2_topology C"
      by (rule subspace_topology_trans[OF hC_sub_S2b])
    thus ?thesis using assms(3) by simp
  qed
  have hC_compact: "top1_compact_on (h ` (C - {b}))
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (h ` (C - {b})))"
  proof -
    have hTR2: "is_topology_on (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets)"
    proof -
      have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
      show ?thesis using product_topology_on_is_topology_on[OF hTR hTR] by simp
    qed
    \<comment> \<open>h restricted to C is continuous (direct proof via preimage).\<close>
    have hh_cont_C: "top1_continuous_map_on C
        (subspace_topology (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) C)
        UNIV (product_topology_on top1_open_sets top1_open_sets) h"
    proof -
      \<comment> \<open>Simplify the double-subspace topology on C.\<close>
      have htop_eq: "subspace_topology (top1_S2 - {b})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) C
          = subspace_topology top1_S2 top1_S2_topology C"
        by (rule subspace_topology_trans[OF hC_sub_S2b])
      \<comment> \<open>h continuous on S^2-{b} implies preimages of open sets are open in S^2 subspace.\<close>
      show ?thesis unfolding htop_eq top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x assume "x \<in> C" show "h x \<in> UNIV" by simp
      next
        fix V :: "(real \<times> real) set"
        assume hV: "V \<in> product_topology_on (top1_open_sets :: real set set) (top1_open_sets :: real set set)"
        \<comment> \<open>{x \<in> S^2-{b}. h x \<in> V} is open in S^2 subspace topology on S^2-{b}.\<close>
        have hpre_S2b: "{x \<in> top1_S2 - {b}. h x \<in> V}
            \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
          using hh_cont hV unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>Intersect with C: {x \<in> C. h x \<in> V} = C \<inter> {x \<in> S^2-{b}. h x \<in> V}.\<close>
        have heq: "{x \<in> C. h x \<in> V} = C \<inter> {x \<in> top1_S2 - {b}. h x \<in> V}"
          using hC_sub_S2b by (by100 blast)
        \<comment> \<open>This is in the subspace topology on C within S^2.\<close>
        obtain W where hW: "W \<in> top1_S2_topology"
            and hpre_eq: "{x \<in> top1_S2 - {b}. h x \<in> V} = (top1_S2 - {b}) \<inter> W"
          using hpre_S2b unfolding subspace_topology_def by (by100 blast)
        have "C \<inter> {x \<in> top1_S2 - {b}. h x \<in> V} = C \<inter> ((top1_S2 - {b}) \<inter> W)"
          using hpre_eq by simp
        hence "C \<inter> {x \<in> top1_S2 - {b}. h x \<in> V} = C \<inter> W"
          using hC_sub_S2b by (by100 blast)
        hence "{x \<in> C. h x \<in> V} = C \<inter> W" using heq by simp
        thus "{x \<in> C. h x \<in> V} \<in> subspace_topology top1_S2 top1_S2_topology C"
          unfolding subspace_topology_def using hW by (by100 blast)
      qed
    qed
    have "top1_compact_on (h ` C) (subspace_topology UNIV
        (product_topology_on top1_open_sets top1_open_sets) (h ` C))"
      by (rule top1_compact_on_continuous_image[OF hC_compact_S2b hTR2 hh_cont_C])
    thus ?thesis using hCb_eq by simp
  qed
  have hC_bounded: "\<exists>M. \<forall>p \<in> h ` (C - {b}). fst p ^ 2 + snd p ^ 2 \<le> M"
  proof -
    \<comment> \<open>h(C) = h(C-{b}) is compact (just proved). Compact in R^2 \<Rightarrow> bounded.\<close>
    have "compact (h ` (C - {b}))"
      using top1_compact_on_subspace_UNIV_iff_compact[of "h ` (C - {b})"]
        hC_compact product_topology_on_open_sets_real2 by (by100 simp)
    \<comment> \<open>The norm function is continuous, so its image on compact set is bounded.\<close>
    have hcont_norm: "continuous_on (h ` (C - {b})) (\<lambda>p. fst p ^ 2 + snd p ^ 2)"
      by (intro continuous_intros)
    have "compact ((\<lambda>p. fst p ^ 2 + snd p ^ 2) ` (h ` (C - {b})))"
      by (rule compact_continuous_image[OF hcont_norm \<open>compact (h ` (C - {b}))\<close>])
    define img where "img = (\<lambda>p :: real \<times> real. fst p ^ 2 + snd p ^ 2) ` (h ` (C - {b}))"
    have himg_compact: "compact img" unfolding img_def
      by (rule compact_continuous_image[OF hcont_norm \<open>compact (h ` (C - {b}))\<close>])
    show ?thesis
    proof (cases "C - {b} = {}")
      case True hence "h ` (C - {b}) = {}" by simp
      thus ?thesis by (by100 blast)
    next
      case False
      hence "h ` (C - {b}) \<noteq> {}" by simp
      hence "img \<noteq> {}" unfolding img_def by simp
      then obtain M where hM: "M \<in> img" "\<forall>t\<in>img. t \<le> M"
        using compact_attains_sup[OF himg_compact] by (by100 blast)
      have "\<forall>p \<in> h ` (C - {b}). fst p ^ 2 + snd p ^ 2 \<le> M"
      proof
        fix p assume "p \<in> h ` (C - {b})"
        hence "fst p ^ 2 + snd p ^ 2 \<in> img" unfolding img_def by (by100 blast)
        thus "fst p ^ 2 + snd p ^ 2 \<le> M" using hM(2) by (by100 blast)
      qed
      thus ?thesis by (by100 blast)
    qed
  qed
  \<comment> \<open>h restricted to (S^2-C)-{b} = S^2-C-{b} is a homeomorphism onto R^2-h(C).
     (Since h: S^2-{b} \<rightarrow> R^2 homeo and C \<subseteq> S^2-{b}, restricting to complement of C
     gives homeo (S^2-{b})-C \<rightarrow> R^2-h(C), and (S^2-{b})-C = S^2-C-{b} = (S^2-C)-{b}.)
     If b \<notin> U: U \<subseteq> (S^2-C)-{b}, h(U) is a connected subset of R^2-h(C),
     and R^2-h(C) has h(C) bounded, so bounded components are bounded.
     If b \<in> U: h(U-{b}) is connected in R^2-h(C) and "contains infinity"
     (h is stereographic from b), so it's in the unbounded component.\<close>
  show ?thesis
  proof (intro conjI impI)
    assume hb_notin: "b \<notin> U"
    \<comment> \<open>U \<subseteq> S^2-C, b \<notin> U, so U \<subseteq> S^2-C-{b} \<subseteq> S^2-{b}.
       h(U) is a connected subset of R^2-h(C). h(U) is bounded because
       U is compact... no, U is a component, not necessarily compact.
       But h(U) \<subseteq> R^2-h(C), and h(C) is compact hence bounded by M.
       The bounded components of R^2-h(C) are those contained in the ball of radius M.
       Since h(U) is connected and doesn't contain "infinity" (b \<notin> U), it must be bounded.\<close>
    show "\<exists>M. \<forall>x\<in>U. fst (h x) ^ 2 + snd (h x) ^ 2 \<le> M"
    proof -
      \<comment> \<open>Use closure_on from our custom topology framework.\<close>
      have hTS2: "is_topology_on top1_S2 top1_S2_topology"
        using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
      have hU_sub_S2: "U \<subseteq> top1_S2" using assms(7) by (by100 blast)
      \<comment> \<open>closure_on of U in S^2 contains U and is closed in S^2.\<close>
      let ?clU = "closure_on top1_S2 top1_S2_topology U"
      have hU_sub_clU: "U \<subseteq> ?clU" by (rule subset_closure_on)
      have hclU_closed: "closedin_on top1_S2 top1_S2_topology ?clU"
        by (rule closure_on_closed[OF hTS2 hU_sub_S2])
      have hclU_sub_S2: "?clU \<subseteq> top1_S2"
        using hclU_closed unfolding closedin_on_def by (by100 blast)
      \<comment> \<open>b \<notin> closure_on(U): U open component of S^2-C, b in different component.\<close>
      have "b \<notin> ?clU"
      proof
        assume hb_clU: "b \<in> ?clU"
        \<comment> \<open>b \<in> S^2-C (given: assms(4)). b is in some component V of S^2-C.
           V is open in S^2 (component of open set in lpc space).
           V \<inter> U = {} (different components). But closure_meets_open says
           b \<in> closure(U), V open, b \<in> V \<Rightarrow> V \<inter> U \<noteq> {}. Contradiction.\<close>
        have hS2C_open: "top1_S2 - C \<in> top1_S2_topology"
        proof -
          have hC_sub_S2: "C \<subseteq> top1_S2" using assms(2) by (by100 blast)
          have "closedin_on top1_S2 top1_S2_topology C"
            by (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff
                top1_S2_is_topology_on_strict hC_sub_S2 assms(3)])
          thus ?thesis unfolding closedin_on_def using hTS2 unfolding is_topology_on_def by (by100 blast)
        qed
        \<comment> \<open>The component of b in S^2-C is open (lpc space, open set).\<close>
        \<comment> \<open>Since S^2-C is open and lpc, the path component of b in S^2-C is open in S^2.
           It's disjoint from U (different components).\<close>
        \<comment> \<open>S^2-C is open and lpc. Path component of b is open and disjoint from U.\<close>
        have hS2C_lpc: "top1_locally_path_connected_on (top1_S2 - C)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
          by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hS2C_open]) simp
        have hb_S2C: "b \<in> top1_S2 - C" using assms(4) by simp
        \<comment> \<open>Path component of b in S^2-C is open in S^2-C.\<close>
        have hTS2C: "is_topology_on (top1_S2 - C) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
          by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
        define V' where "V' = top1_path_component_of_on (top1_S2 - C)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) b"
        have hV'_open_S2C: "V' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)"
          unfolding V'_def
          by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTS2C hS2C_lpc hb_S2C])
        \<comment> \<open>V' open in S^2-C \<Rightarrow> V' = (S^2-C) \<inter> W for some W \<in> top1_S2_topology. Hence V' \<in> top1_S2_topology.\<close>
        have "V' \<in> top1_S2_topology"
        proof -
          obtain W where hW: "W \<in> top1_S2_topology" and hV'_eq: "V' = (top1_S2 - C) \<inter> W"
            using hV'_open_S2C unfolding subspace_topology_def by (by100 blast)
          have "(top1_S2 - C) \<inter> W \<in> top1_S2_topology"
            by (rule topology_inter_open[OF hTS2 hS2C_open hW])
          thus ?thesis using hV'_eq by simp
        qed
        have "b \<in> V'" unfolding V'_def
          by (rule top1_path_component_of_on_self_mem[OF hTS2C hb_S2C])
        have "V' \<inter> U = {}"
        proof (rule ccontr)
          assume "\<not> ?thesis"
          then obtain z where hz: "z \<in> V'" "z \<in> U" by (by100 blast)
          \<comment> \<open>z \<in> path_comp(b) and z \<in> U. Then path_comp(z) = path_comp(b) = V'.
             But z \<in> U connected subset of S^2-C, so z's path component contains U.
             Hence U \<subseteq> V', so b \<in> V' \<supseteq> U... but b \<notin> U. Actually V' = path_comp(b),
             and z \<in> V' means path_comp(z) = path_comp(b). Since z \<in> U and U connected,
             U \<subseteq> path_comp(z) = V'. Hence b \<in> U (b \<in> V' and... no, V' might be bigger than U).\<close>
          \<comment> \<open>z \<in> V' = path_comp(b). z \<in> U \<subseteq> S^2-C. U connected.
             U \<subseteq> path_comp(z) = path_comp(b) = V' (since z \<in> V' and path comps equal if share a point).
             But also b \<in> V'. If U \<subseteq> V', and b \<in> V', this doesn't give b \<in> U directly.
             The issue: V' might contain both U and b's original component.
             But V' is a PATH component, so it IS a component. U is also a component.
             If they share z, they must be equal: U = V'. But b \<in> V' and b \<notin> U. Contradiction.\<close>
          have hU_sub_S2C: "U \<subseteq> top1_S2 - C" using assms(7) by (by100 blast)
          have hU_conn_S2C: "top1_connected_on U (subspace_topology (top1_S2 - C)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) U)"
          proof -
            have "subspace_topology (top1_S2 - C) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) U
                = subspace_topology top1_S2 top1_S2_topology U"
              by (rule subspace_topology_trans[OF hU_sub_S2C])
            thus ?thesis using assms(6) by simp
          qed
          \<comment> \<open>z \<in> U (component) and z \<in> V' (path component of b).
             By Theorem_25_5: in lpc S^2-C, path component = component.
             path_comp(z) = path_comp(b) = V' (since z \<in> V').
             component(z) contains U (z \<in> U connected \<subseteq> S^2-C).
             path_comp(z) = component(z) (Theorem_25_5 in lpc S^2-C).
             So V' = component(z) \<supseteq> U. Since also V' = path_comp(b), b \<in> V' and
             U \<subseteq> V' = component(z). But U itself is a component, so U = component(z) = V'.
             Hence b \<in> V' = U. Contradiction.\<close>
          \<comment> \<open>path_comp(z) = path_comp(b) = V' (z \<in> V' = path_comp(b)).\<close>
          have hz_in_pcb: "z \<in> top1_path_component_of_on (top1_S2 - C)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) b"
            using hz(1) V'_def by simp
          have hpz_eq: "top1_path_component_of_on (top1_S2 - C)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) z = V'"
            using top1_path_component_of_on_eq_of_mem[OF hTS2C hz_in_pcb] V'_def by simp
          \<comment> \<open>In lpc S^2-C, path_comp(z) = component(z).\<close>
          have "top1_path_component_of_on (top1_S2 - C)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) z
            = top1_component_of_on (top1_S2 - C)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) z"
          proof -
            have "z \<in> top1_S2 - C" using hz(2) hU_sub_S2C by (by100 blast)
            thus ?thesis using Theorem_25_5[OF hTS2C] hS2C_lpc by (by100 blast)
          qed
          \<comment> \<open>component(z) \<supseteq> U (z \<in> U connected).\<close>
          have "U \<subseteq> top1_component_of_on (top1_S2 - C)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) z"
            unfolding top1_component_of_on_def using hz(2) hU_sub_S2C hU_conn_S2C by (by100 blast)
          \<comment> \<open>V' = path_comp(z) = component(z) \<supseteq> U. component(z) is a component.
             U is also a component. They share z, so U = component(z) = V'.\<close>
          \<comment> \<open>V' = path_comp(b) = component(b) in lpc S^2-C.\<close>
          have hV'_eq_comp_b: "V' = top1_component_of_on (top1_S2 - C)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) b"
          proof -
            have "top1_path_component_of_on (top1_S2 - C)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) b
              = top1_component_of_on (top1_S2 - C)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) b"
              using Theorem_25_5[OF hTS2C] hS2C_lpc hb_S2C by (by100 blast)
            thus ?thesis unfolding V'_def by simp
          qed
          have hV'_comp: "V' \<in> top1_components_on (top1_S2 - C)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
            unfolding hV'_eq_comp_b top1_components_on_def using hb_S2C by (by100 blast)
          have hUV'_inter: "U \<inter> V' \<noteq> {}" using hz by (by100 blast)
          have "U = V'"
            using Theorem_25_1(2)[OF hTS2C assms(8) hV'_comp hUV'_inter] by simp
          have "b \<in> U" using \<open>U = V'\<close> \<open>b \<in> V'\<close> by simp
          thus False using hb_notin by simp
        qed
        have "V' \<subseteq> top1_S2 - C" unfolding V'_def
          by (rule top1_path_component_of_on_subset[OF hTS2C hb_S2C])
        obtain V'' where hV'': "V'' \<in> top1_S2_topology" "b \<in> V''" "V'' \<inter> U = {}" "V'' \<subseteq> top1_S2 - C"
          using \<open>V' \<in> top1_S2_topology\<close> \<open>b \<in> V'\<close> \<open>V' \<inter> U = {}\<close> \<open>V' \<subseteq> top1_S2 - C\<close> by blast
        have "V'' \<inter> U \<noteq> {}"
          by (rule closure_meets_open[OF hTS2 hU_sub_S2 hb_clU hV''(1) hV''(2)])
        thus False using hV''(3) by simp
      qed
      hence hclU_sub_S2b: "?clU \<subseteq> top1_S2 - {b}" using hclU_sub_S2 by (by100 blast)
      \<comment> \<open>closure_on(U) is compact (closed in compact S^2).\<close>
      have hS2_compact: "top1_compact_on top1_S2 top1_S2_topology"
      proof -
        have "top1_S2_topology = subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) top1_S2"
          unfolding top1_S2_topology_def
          using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
        hence "top1_compact_on top1_S2 top1_S2_topology
            = compact top1_S2"
          using top1_compact_on_subspace_UNIV_iff_compact[of top1_S2] by simp
        thus ?thesis using S2_compact_standard by simp
      qed
      have hclU_compact: "top1_compact_on ?clU (subspace_topology top1_S2 top1_S2_topology ?clU)"
        by (rule Theorem_26_2[OF hS2_compact hclU_closed])
      \<comment> \<open>h(closure_on(U)) is compact in R^2, hence bounded.\<close>
      \<comment> \<open>h continuous on S^2-{b} \<supseteq> closure_on(U), so h(closure_on(U)) compact.\<close>
      have "compact (h ` ?clU)"
      proof -
        \<comment> \<open>h continuous on S^2-{b} restricted to clU.\<close>
        have hh_cont_clU: "top1_continuous_map_on ?clU (subspace_topology top1_S2 top1_S2_topology ?clU)
            UNIV (product_topology_on top1_open_sets top1_open_sets) h"
        proof -
          have hh_S2b: "top1_continuous_map_on (top1_S2 - {b})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
              UNIV (product_topology_on top1_open_sets top1_open_sets) h"
            using assms(5) unfolding top1_homeomorphism_on_def by (by100 blast)
          have "top1_continuous_map_on ?clU (subspace_topology (top1_S2 - {b})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) ?clU)
              UNIV (product_topology_on top1_open_sets top1_open_sets) h"
            by (rule top1_continuous_map_on_restrict_domain_simple[OF hh_S2b hclU_sub_S2b])
          thus ?thesis by (simp add: subspace_topology_trans[OF hclU_sub_S2b])
        qed
        have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV] by simp
        have "top1_compact_on (h ` ?clU) (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (h ` ?clU))"
          by (rule top1_compact_on_continuous_image[OF hclU_compact hTR2 hh_cont_clU])
        hence "top1_compact_on (h ` ?clU) (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) (h ` ?clU))"
          using product_topology_on_open_sets_real2 by simp
        thus "compact (h ` ?clU)"
          using top1_compact_on_subspace_UNIV_iff_compact[of "h ` ?clU"] by simp
      qed
      then obtain M where hM: "\<forall>p \<in> h ` ?clU. fst p ^ 2 + snd p ^ 2 \<le> M"
      proof (cases "?clU = {}")
        case True thus ?thesis using that by simp
      next
        case False hence "h ` ?clU \<noteq> {}" by simp
        define img where "img = (\<lambda>p :: real \<times> real. fst p ^ 2 + snd p ^ 2) ` (h ` ?clU)"
        have himg_compact: "compact img" unfolding img_def
          by (rule compact_continuous_image) (intro continuous_intros, rule \<open>compact (h ` ?clU)\<close>)
        have "img \<noteq> {}" unfolding img_def using \<open>h ` ?clU \<noteq> {}\<close> by simp
        then obtain M where "M \<in> img" "\<forall>t\<in>img. t \<le> M"
          using compact_attains_sup[OF himg_compact] by (by100 blast)
        thus ?thesis using that unfolding img_def by (by100 blast)
      qed
      have "h ` U \<subseteq> h ` ?clU" using hU_sub_clU by (by100 blast)
      thus ?thesis using hM by (by100 blast)
    qed
  next
    assume hb_in: "b \<in> U"
    \<comment> \<open>U contains b. h(U-{b}) is connected in R^2-h(C) and "goes to infinity".
       For any M, the set {x | |h(x)| > M} \<inter> (U-{b}) is nonempty because
       h(b) = \<infinity> and U is open around b.\<close>
    show "\<forall>M. \<exists>x\<in>U - {b}. fst (h x) ^ 2 + snd (h x) ^ 2 > M"
    proof
      fix M :: real
      have hTS2: "is_topology_on top1_S2 top1_S2_topology"
        using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
      \<comment> \<open>U is open in S^2: component of open S^2-C in lpc S^2.\<close>
      have hS2C_open: "top1_S2 - C \<in> top1_S2_topology"
      proof -
        have "closedin_on top1_S2 top1_S2_topology C"
          by (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff
              top1_S2_is_topology_on_strict assms(2) assms(3)])
        thus ?thesis unfolding closedin_on_def using hTS2 unfolding is_topology_on_def by (by100 blast)
      qed
      have hTS2C: "is_topology_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
        by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
      have hS2C_lpc: "top1_locally_path_connected_on (top1_S2 - C)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
        by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hS2C_open]) simp
      \<comment> \<open>U = component(x) for some x. In lpc space, component = path_component.
         Path components are open in the subspace, hence open in S^2.\<close>
      have hU_open_S2: "U \<in> top1_S2_topology"
      proof -
        obtain x where hx: "x \<in> top1_S2 - C"
            and hU_eq: "U = top1_component_of_on (top1_S2 - C)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) x"
          using assms(8) unfolding top1_components_on_def by (by100 blast)
        have "top1_path_component_of_on (top1_S2 - C)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) x
          = top1_component_of_on (top1_S2 - C)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) x"
          using Theorem_25_5[OF hTS2C] hS2C_lpc hx by (by100 blast)
        hence hU_eq_pc: "U = top1_path_component_of_on (top1_S2 - C)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) x"
          using hU_eq by simp
        have "top1_path_component_of_on (top1_S2 - C)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) x
          \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)"
          by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTS2C hS2C_lpc hx])
        then obtain W where hW: "W \<in> top1_S2_topology" and hpc_eq: "U = (top1_S2 - C) \<inter> W"
          using hU_eq_pc unfolding subspace_topology_def by (by100 blast)
        hence "U \<in> top1_S2_topology"
          by (simp add: topology_inter_open[OF hTS2 hS2C_open hW])
        thus ?thesis .
      qed
      \<comment> \<open>K = S^2 \\ U is closed in S^2, hence compact.\<close>
      define K where "K = top1_S2 - U"
      have hU_sub_S2: "U \<subseteq> top1_S2" using assms(7) by (by100 blast)
      have hK_closed: "closedin_on top1_S2 top1_S2_topology K"
        unfolding K_def closedin_on_def
      proof (intro conjI)
        show "top1_S2 - U \<subseteq> top1_S2" by (by100 blast)
        have "top1_S2 - (top1_S2 - U) = U" using hU_sub_S2 by (by100 blast)
        thus "top1_S2 - (top1_S2 - U) \<in> top1_S2_topology" using hU_open_S2 by simp
      qed
      have hK_sub_S2b: "K \<subseteq> top1_S2 - {b}" unfolding K_def using hb_in by (by100 blast)
      have hS2_compact: "top1_compact_on top1_S2 top1_S2_topology"
      proof -
        have "top1_S2_topology = subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) top1_S2"
          unfolding top1_S2_topology_def
          using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
        hence "top1_compact_on top1_S2 top1_S2_topology = compact top1_S2"
          using top1_compact_on_subspace_UNIV_iff_compact[of top1_S2] by simp
        thus ?thesis using S2_compact_standard by simp
      qed
      have hK_compact: "top1_compact_on K (subspace_topology top1_S2 top1_S2_topology K)"
        by (rule Theorem_26_2[OF hS2_compact hK_closed])
      \<comment> \<open>h(K) compact in R^2.\<close>
      have "compact (h ` K)"
      proof -
        have hh_cont_K: "top1_continuous_map_on K (subspace_topology top1_S2 top1_S2_topology K)
            UNIV (product_topology_on top1_open_sets top1_open_sets) h"
        proof -
          have hh_S2b: "top1_continuous_map_on (top1_S2 - {b})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
              UNIV (product_topology_on top1_open_sets top1_open_sets) h"
            using assms(5) unfolding top1_homeomorphism_on_def by (by100 blast)
          have hh_K: "top1_continuous_map_on K (subspace_topology (top1_S2 - {b})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) K)
              UNIV (product_topology_on top1_open_sets top1_open_sets) h"
            by (rule top1_continuous_map_on_restrict_domain_simple[OF hh_S2b hK_sub_S2b])
          thus ?thesis by (simp add: subspace_topology_trans[OF hK_sub_S2b])
        qed
        have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV] by simp
        have "top1_compact_on (h ` K) (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (h ` K))"
          by (rule top1_compact_on_continuous_image[OF hK_compact hTR2 hh_cont_K])
        hence "top1_compact_on (h ` K) (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) (h ` K))"
          using product_topology_on_open_sets_real2 by simp
        thus "compact (h ` K)"
          using top1_compact_on_subspace_UNIV_iff_compact[of "h ` K"] by simp
      qed
      \<comment> \<open>h(K) bounded.\<close>
      then obtain N where hN: "\<forall>p \<in> h ` K. fst p ^ 2 + snd p ^ 2 \<le> N"
      proof (cases "K = {}")
        case True thus ?thesis using that by simp
      next
        case False hence "h ` K \<noteq> {}" by simp
        define img where "img = (\<lambda>p :: real \<times> real. fst p ^ 2 + snd p ^ 2) ` (h ` K)"
        have himg_compact: "compact img" unfolding img_def
          by (rule compact_continuous_image) (intro continuous_intros, rule \<open>compact (h ` K)\<close>)
        have "img \<noteq> {}" unfolding img_def using \<open>h ` K \<noteq> {}\<close> by simp
        then obtain N' where "N' \<in> img" "\<forall>t\<in>img. t \<le> N'"
          using compact_attains_sup[OF himg_compact] by (by100 blast)
        thus ?thesis using that unfolding img_def by (by100 blast)
      qed
      \<comment> \<open>h bijective on S^2-{b}, so h(U-{b}) \<union> h(K) = R^2 and h(U-{b}) \<inter> h(K) = {}.\<close>
      have hinj: "inj_on h (top1_S2 - {b})"
        using assms(5) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have hsurj: "h ` (top1_S2 - {b}) = UNIV"
        using assms(5) unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have hUb_K_partition: "U - {b} \<union> K = top1_S2 - {b}"
        unfolding K_def using assms(7) hb_in by (by100 blast)
      have hUb_K_disjoint: "(U - {b}) \<inter> K = {}"
        unfolding K_def by (by100 blast)
      have hUb_sub: "U - {b} \<subseteq> top1_S2 - {b}" using assms(7) by (by100 blast)
      \<comment> \<open>For any M, find x \<in> U-{b} with |h(x)|^2 > M.\<close>
      define R where "R = max (max M N) 0 + 1"
      define p :: "real \<times> real" where "p = (R + 1, 0)"
      have hR_pos: "R > 0" unfolding R_def by (by100 linarith)
      have hR_ge_M: "R > M" unfolding R_def by (by100 linarith)
      have hR_ge_N: "R > N" unfolding R_def by (by100 linarith)
      have hp_big: "fst p ^ 2 + snd p ^ 2 > max M N"
      proof -
        have hfst: "fst p = R + 1" and hsnd: "snd p = 0" unfolding p_def by auto
        have heq: "fst p ^ 2 + snd p ^ 2 = (R + 1) ^ 2"
          using hfst hsnd by (simp add: power2_eq_square)
        have hR1_ge_1: "R + 1 \<ge> 1" using hR_pos by (by100 linarith)
        have hR1_nn: "0 \<le> R + 1" using hR_pos by (by100 linarith)
        have "(R + 1) * (R + 1) \<ge> 1 * (R + 1)"
          by (rule mult_right_mono[OF hR1_ge_1 hR1_nn])
        hence "(R + 1) ^ 2 \<ge> R + 1" by (simp add: power2_eq_square)
        hence "(R + 1) ^ 2 > R" by (by100 linarith)
        thus ?thesis using heq hR_ge_M hR_ge_N by (by100 linarith)
      qed
      have hp_not_hK: "p \<notin> h ` K"
      proof
        assume "p \<in> h ` K"
        hence "fst p ^ 2 + snd p ^ 2 \<le> N" using hN by (by100 blast)
        thus False using hp_big by (by100 linarith)
      qed
      have "h ` (U - {b}) \<union> h ` K = h ` ((U - {b}) \<union> K)"
        by (rule image_Un[symmetric])
      also have "... = h ` (top1_S2 - {b})" using hUb_K_partition by simp
      finally have "h ` (U - {b}) \<union> h ` K = h ` (top1_S2 - {b})" .
      hence "h ` (U - {b}) \<union> h ` K = UNIV" using hsurj by simp
      have "p \<in> h ` (U - {b}) \<union> h ` K"
        using \<open>h ` (U - {b}) \<union> h ` K = UNIV\<close> by simp
      hence "p \<in> h ` (U - {b})" using hp_not_hK by (by100 blast)
      then obtain x where hx: "x \<in> U - {b}" and hhx: "h x = p" by (by100 blast)
      have "fst (h x) ^ 2 + snd (h x) ^ 2 > M"
      proof -
        have "fst (h x) ^ 2 + snd (h x) ^ 2 = fst p ^ 2 + snd p ^ 2" using hhx by simp
        thus ?thesis using hp_big by (by100 linarith)
      qed
      thus "\<exists>x\<in>U - {b}. fst (h x) ^ 2 + snd (h x) ^ 2 > M"
        using hx by (by100 blast)
    qed
  qed
qed

\<comment> \<open>Connected open delete for R^2: removing one point from a connected open set preserves connectivity.\<close>
lemma open_nonempty_R2_has_two_points:
  fixes V :: "(real \<times> real) set" and p :: "real \<times> real"
  assumes "open V" "p \<in> V"
  shows "\<exists>q \<in> V. q \<noteq> p"
proof -
  \<comment> \<open>V open in R^2 product topology. Get basic open U1\<times>U2 around p.\<close>
  obtain U1 U2 :: "real set" where "open U1" "open U2" "fst p \<in> U1" "snd p \<in> U2"
      and hU12: "U1 \<times> U2 \<subseteq> V"
  proof -
    from open_prod_elim[OF assms(1) assms(2)]
    obtain A B where "open A" "open B" "p \<in> A \<times> B" "A \<times> B \<subseteq> V" by (by100 blast)
    hence "fst p \<in> A" "snd p \<in> B" by auto
    thus ?thesis using that \<open>open A\<close> \<open>open B\<close> \<open>A \<times> B \<subseteq> V\<close> by (by100 blast)
  qed
  \<comment> \<open>U1 open real set containing fst p. It contains a point \<noteq> fst p.\<close>
  have "\<exists>x \<in> U1. x \<noteq> fst p"
  proof -
    \<comment> \<open>fst p + 1 or fst p - 1 might not be in U1 but {fst p - 1 <..< fst p + 1} is a nhd.\<close>
    \<comment> \<open>Use: open U1 means it's a union of open intervals. fst p \<in> some interval.\<close>
    have "\<exists>a b. a < fst p \<and> fst p < b \<and> {a<..<b} \<subseteq> U1"
    proof -
      \<comment> \<open>U1 is open and contains fst p. Use: open sets in R contain intervals.\<close>
      \<comment> \<open>From open_real_def + uniformity: \<exists>e>0. ball(fst p, e) \<subseteq> U1.\<close>
      have "\<exists>e>0. \<forall>y::real. \<bar>y - fst p\<bar> < e \<longrightarrow> y \<in> U1"
      proof -
        have "\<exists>e>0. \<forall>y. dist y (fst p) < e \<longrightarrow> y \<in> U1"
          using \<open>open U1\<close> \<open>fst p \<in> U1\<close> unfolding open_dist by (by100 blast)
        thus ?thesis unfolding dist_real_def by simp
      qed
      then obtain e :: real where "e > 0" and he: "\<forall>y. \<bar>y - fst p\<bar> < e \<longrightarrow> y \<in> U1" by blast
      have hsub: "{fst p - e <..< fst p + e} \<subseteq> U1"
      proof
        fix y assume "y \<in> {fst p - e <..< fst p + e}"
        hence "\<bar>y - fst p\<bar> < e" by auto
        thus "y \<in> U1" using he by simp
      qed
      have "fst p - e < fst p" using \<open>e > 0\<close> by simp
      moreover have "fst p < fst p + e" using \<open>e > 0\<close> by simp
      ultimately show ?thesis using hsub by (by100 blast)
    qed
    then obtain a b where "a < fst p" "fst p < b" "{a<..<b} \<subseteq> U1" by blast
    have "(fst p + b) / 2 \<in> {a<..<b}" using \<open>a < fst p\<close> \<open>fst p < b\<close> by simp
    moreover have "(fst p + b) / 2 \<noteq> fst p" using \<open>fst p < b\<close> by simp
    ultimately show ?thesis using \<open>{a<..<b} \<subseteq> U1\<close> by (by100 blast)
  qed
  then obtain x where "x \<in> U1" "x \<noteq> fst p" by blast
  define q where "q = (x, snd p)"
  have "q \<in> U1 \<times> U2" unfolding q_def using \<open>x \<in> U1\<close> \<open>snd p \<in> U2\<close> by simp
  hence "q \<in> V" using hU12 by (by100 blast)
  moreover have "q \<noteq> p" unfolding q_def using \<open>x \<noteq> fst p\<close> by (cases p) simp
  ultimately show ?thesis by (by100 blast)
qed

lemma interval_delete_connected_R2:
  fixes a1 b1 a2 b2 p1 p2 :: real
  assumes "a1 < p1" "p1 < b1" "a2 < p2" "p2 < b2"
  shows "connected ({a1<..<b1} \<times> {a2<..<b2} - {(p1, p2)})"
proof (rule connectedI)
  fix A B :: "(real \<times> real) set"
  assume hA: "open A" and hB: "open B"
      and hcov: "{a1<..<b1} \<times> {a2<..<b2} - {(p1,p2)} \<subseteq> A \<union> B"
      and hdisj: "A \<inter> B \<inter> ({a1<..<b1} \<times> {a2<..<b2} - {(p1,p2)}) = {}"
      and hAne: "A \<inter> ({a1<..<b1} \<times> {a2<..<b2} - {(p1,p2)}) \<noteq> {}"
      and hBne: "B \<inter> ({a1<..<b1} \<times> {a2<..<b2} - {(p1,p2)}) \<noteq> {}"
  let ?I1 = "{a1<..<b1}" and ?I2 = "{a2<..<b2}" and ?R = "{a1<..<b1} \<times> {a2<..<b2} - {(p1,p2)}"
  define y0 where "y0 = (p2 + b2) / 2"
  have hy0: "y0 \<in> ?I2" "y0 \<noteq> p2" unfolding y0_def using assms by auto
  have hL2_conn: "connected (?I1 \<times> {y0})"
    by (rule connected_Times[OF connected_Ioo connected_sing])
  have hL2_sub: "?I1 \<times> {y0} \<subseteq> ?R" using hy0 by auto
  have "A \<inter> (?I1 \<times> {y0}) = {} \<or> B \<inter> (?I1 \<times> {y0}) = {}"
    by (rule connectedD[OF hL2_conn hA hB]) (use hdisj hcov hL2_sub in auto)
  \<comment> \<open>L2 in A or B. WLOG in A (B case symmetric). Then all of ?R in A.\<close>
  moreover {
    assume "B \<inter> (?I1 \<times> {y0}) = {}"
    hence hL2A: "?I1 \<times> {y0} \<subseteq> A" using hcov hL2_sub by auto
    define x0 where "x0 = (p1 + b1) / 2"
    have hx0: "x0 \<in> ?I1" "x0 \<noteq> p1" unfolding x0_def using assms by auto
    \<comment> \<open>Vertical line {x0}\<times>I2: connected, in ?R, contains (x0,y0)\<in>A.\<close>
    have "{x0} \<times> ?I2 \<subseteq> A"
    proof -
      have "connected ({x0} \<times> ?I2)" by (rule connected_Times[OF connected_sing connected_Ioo])
      have "{x0} \<times> ?I2 \<subseteq> ?R" using hx0 by auto
      have "(x0, y0) \<in> A" using hL2A hx0(1) hy0(1) by auto
      hence "A \<inter> ({x0} \<times> ?I2) \<noteq> {}" using hy0(1) by auto
      have "A \<inter> ({x0} \<times> ?I2) = {} \<or> B \<inter> ({x0} \<times> ?I2) = {}"
        by (rule connectedD[OF \<open>connected ({x0} \<times> ?I2)\<close> hA hB])
           (use hdisj hcov \<open>{x0} \<times> ?I2 \<subseteq> ?R\<close> in auto)
      hence "B \<inter> ({x0} \<times> ?I2) = {}" using \<open>A \<inter> ({x0} \<times> ?I2) \<noteq> {}\<close> by auto
      thus ?thesis using hcov \<open>{x0} \<times> ?I2 \<subseteq> ?R\<close> by auto
    qed
    \<comment> \<open>Every (x,y)\<in>?R is in A.\<close>
    have "?R \<subseteq> A"
    proof
      fix xy assume "xy \<in> ?R"
      obtain x y where [simp]: "xy = (x,y)" and hx: "x \<in> ?I1" and hy: "y \<in> ?I2"
          and hne: "(x,y) \<noteq> (p1,p2)" using \<open>xy \<in> ?R\<close> by (by100 force)
      show "xy \<in> A"
      proof (cases "x = p1")
        case False
        have "connected ({x} \<times> ?I2)" by (rule connected_Times[OF connected_sing connected_Ioo])
        have "{x} \<times> ?I2 \<subseteq> ?R" using False hx by auto
        have "(x, y0) \<in> A" using hL2A hx hy0(1) by auto
        hence "A \<inter> ({x} \<times> ?I2) \<noteq> {}" using hy0(1) by auto
        have "A \<inter> ({x} \<times> ?I2) = {} \<or> B \<inter> ({x} \<times> ?I2) = {}"
          by (rule connectedD[OF \<open>connected ({x} \<times> ?I2)\<close> hA hB])
             (use hdisj hcov \<open>{x} \<times> ?I2 \<subseteq> ?R\<close> in auto)
        hence "{x} \<times> ?I2 \<subseteq> A"
          using \<open>A \<inter> ({x} \<times> ?I2) \<noteq> {}\<close> hcov \<open>{x} \<times> ?I2 \<subseteq> ?R\<close> by auto
        thus ?thesis using hy by auto
      next
        case True hence "y \<noteq> p2" using hne by auto
        have "connected (?I1 \<times> {y})" by (rule connected_Times[OF connected_Ioo connected_sing])
        have "?I1 \<times> {y} \<subseteq> ?R" using \<open>y \<noteq> p2\<close> hy by auto
        have "(x0, y) \<in> A" using \<open>{x0} \<times> ?I2 \<subseteq> A\<close> hy by auto
        hence "A \<inter> (?I1 \<times> {y}) \<noteq> {}" using hx0(1) by auto
        have "A \<inter> (?I1 \<times> {y}) = {} \<or> B \<inter> (?I1 \<times> {y}) = {}"
          by (rule connectedD[OF \<open>connected (?I1 \<times> {y})\<close> hA hB])
             (use hdisj hcov \<open>?I1 \<times> {y} \<subseteq> ?R\<close> in auto)
        hence "?I1 \<times> {y} \<subseteq> A"
          using \<open>A \<inter> (?I1 \<times> {y}) \<noteq> {}\<close> hcov \<open>?I1 \<times> {y} \<subseteq> ?R\<close> by auto
        thus ?thesis using hx True by auto
      qed
    qed
    hence False using hBne hdisj by auto }
  moreover {
    assume "A \<inter> (?I1 \<times> {y0}) = {}"
    \<comment> \<open>Symmetric: L2 \<subseteq> B, all of ?R \<subseteq> B, A empty.\<close>
    hence hL2B: "?I1 \<times> {y0} \<subseteq> B" using hcov hL2_sub by auto
    define x0' where "x0' = (p1 + b1) / 2"
    have hx0': "x0' \<in> ?I1" "x0' \<noteq> p1" unfolding x0'_def using assms by auto
    have "{x0'} \<times> ?I2 \<subseteq> B"
    proof -
      have "connected ({x0'} \<times> ?I2)" by (rule connected_Times[OF connected_sing connected_Ioo])
      have "{x0'} \<times> ?I2 \<subseteq> ?R" using hx0' by auto
      have "(x0', y0) \<in> B" using hL2B hx0'(1) hy0(1) by auto
      hence "B \<inter> ({x0'} \<times> ?I2) \<noteq> {}" using hy0(1) by auto
      have "A \<inter> ({x0'} \<times> ?I2) = {} \<or> B \<inter> ({x0'} \<times> ?I2) = {}"
        by (rule connectedD[OF \<open>connected ({x0'} \<times> ?I2)\<close> hA hB])
           (use hdisj hcov \<open>{x0'} \<times> ?I2 \<subseteq> ?R\<close> in auto)
      thus ?thesis using \<open>B \<inter> ({x0'} \<times> ?I2) \<noteq> {}\<close> hcov \<open>{x0'} \<times> ?I2 \<subseteq> ?R\<close> by auto
    qed
    have "?R \<subseteq> B"
    proof
      fix xy assume "xy \<in> ?R"
      obtain x y where [simp]: "xy = (x,y)" and hx: "x \<in> ?I1" and hy: "y \<in> ?I2"
          and hne: "(x,y) \<noteq> (p1,p2)" using \<open>xy \<in> ?R\<close> by (by100 force)
      show "xy \<in> B"
      proof (cases "x = p1")
        case False
        have "connected ({x} \<times> ?I2)" by (rule connected_Times[OF connected_sing connected_Ioo])
        have "{x} \<times> ?I2 \<subseteq> ?R" using False hx by auto
        have "(x, y0) \<in> B" using hL2B hx hy0(1) by auto
        hence "B \<inter> ({x} \<times> ?I2) \<noteq> {}" using hy0(1) by auto
        have "A \<inter> ({x} \<times> ?I2) = {} \<or> B \<inter> ({x} \<times> ?I2) = {}"
          by (rule connectedD[OF \<open>connected ({x} \<times> ?I2)\<close> hA hB])
             (use hdisj hcov \<open>{x} \<times> ?I2 \<subseteq> ?R\<close> in auto)
        hence "{x} \<times> ?I2 \<subseteq> B"
          using \<open>B \<inter> ({x} \<times> ?I2) \<noteq> {}\<close> hcov \<open>{x} \<times> ?I2 \<subseteq> ?R\<close> by auto
        thus ?thesis using hy by auto
      next
        case True hence "y \<noteq> p2" using hne by auto
        have "connected (?I1 \<times> {y})" by (rule connected_Times[OF connected_Ioo connected_sing])
        have "?I1 \<times> {y} \<subseteq> ?R" using \<open>y \<noteq> p2\<close> hy by auto
        have "(x0', y) \<in> B" using \<open>{x0'} \<times> ?I2 \<subseteq> B\<close> hy by auto
        hence "B \<inter> (?I1 \<times> {y}) \<noteq> {}" using hx0'(1) by auto
        have "A \<inter> (?I1 \<times> {y}) = {} \<or> B \<inter> (?I1 \<times> {y}) = {}"
          by (rule connectedD[OF \<open>connected (?I1 \<times> {y})\<close> hA hB])
             (use hdisj hcov \<open>?I1 \<times> {y} \<subseteq> ?R\<close> in auto)
        hence "?I1 \<times> {y} \<subseteq> B"
          using \<open>B \<inter> (?I1 \<times> {y}) \<noteq> {}\<close> hcov \<open>?I1 \<times> {y} \<subseteq> ?R\<close> by auto
        thus ?thesis using hx True by auto
      qed
    qed
    hence False using hAne hdisj by auto }
  ultimately show False by auto
qed

\<comment> \<open>open_rectangle_delete_connected_R2 removed (unused, unprovable for general U1,U2).
   Use connected_open_delete_R2 for the general case instead.\<close>

lemma connected_open_delete_R2:
  fixes U :: "(real \<times> real) set" and p :: "real \<times> real"
  assumes "open U" "connected U"
  shows "connected (U - {p})"
proof (cases "p \<in> U")
  case False thus ?thesis using assms(2) by (simp add: insert_absorb)
next
  case True
  \<comment> \<open>Get interval rectangle R around p with R \<subseteq> U.\<close>
  obtain A0 B0 where "open A0" "open B0" "p \<in> A0 \<times> B0" "A0 \<times> B0 \<subseteq> U"
    using open_prod_elim[OF assms(1) True] by (by100 blast)
  obtain e1 where "e1 > 0" "\<forall>y. dist (fst p) y < e1 \<longrightarrow> y \<in> A0"
  proof -
    have "\<exists>e>0. \<forall>y. dist y (fst p) < e \<longrightarrow> y \<in> A0"
      using \<open>open A0\<close> \<open>p \<in> A0 \<times> B0\<close> unfolding open_dist by auto
    thus ?thesis using that by (simp add: dist_commute) blast
  qed
  obtain e2 where "e2 > 0" "\<forall>y. dist (snd p) y < e2 \<longrightarrow> y \<in> B0"
  proof -
    have "\<exists>e>0. \<forall>y. dist y (snd p) < e \<longrightarrow> y \<in> B0"
      using \<open>open B0\<close> \<open>p \<in> A0 \<times> B0\<close> unfolding open_dist by auto
    thus ?thesis using that by (simp add: dist_commute) blast
  qed
  let ?R = "{fst p - e1 <..< fst p + e1} \<times> {snd p - e2 <..< snd p + e2}"
  have hR_sub_U: "?R \<subseteq> U"
  proof -
    have "{fst p - e1 <..< fst p + e1} \<subseteq> A0"
      using \<open>\<forall>y. dist (fst p) y < e1 \<longrightarrow> y \<in> A0\<close> by (auto simp: dist_real_def)
    moreover have "{snd p - e2 <..< snd p + e2} \<subseteq> B0"
      using \<open>\<forall>y. dist (snd p) y < e2 \<longrightarrow> y \<in> B0\<close> by (auto simp: dist_real_def)
    ultimately show ?thesis using \<open>A0 \<times> B0 \<subseteq> U\<close> by (by100 blast)
  qed
  have hR_conn: "connected (?R - {(fst p, snd p)})"
    by (rule interval_delete_connected_R2) (use \<open>e1 > 0\<close> \<open>e2 > 0\<close> in simp_all)
  hence hR_conn': "connected (?R - {p})" by simp
  \<comment> \<open>Now show U-{p} connected using connectedI.\<close>
  show ?thesis
  proof (rule connectedI)
    fix A B :: "(real \<times> real) set"
    assume hA: "open A" and hB: "open B"
        and hcov: "U - {p} \<subseteq> A \<union> B"
        and hdisj: "A \<inter> B \<inter> (U - {p}) = {}"
        and hAne: "A \<inter> (U - {p}) \<noteq> {}" and hBne: "B \<inter> (U - {p}) \<noteq> {}"
    \<comment> \<open>R-{p} connected and \<subseteq> U-{p} \<subseteq> A\<union>B. So R-{p} \<subseteq> A or R-{p} \<subseteq> B.\<close>
    have hRp_sub: "?R - {p} \<subseteq> U - {p}" using hR_sub_U by (by100 blast)
    have "A \<inter> (?R - {p}) = {} \<or> B \<inter> (?R - {p}) = {}"
      by (rule connectedD[OF hR_conn' hA hB])
         (use hdisj hcov hRp_sub in auto)
    \<comment> \<open>WLOG R-{p} disjoint from B (i.e., R-{p} \<subseteq> A).
       Then A\<union>{p} \<supseteq> R. Since R is a neighborhood of p, A\<union>{p} is open at p.
       A itself is open, so A\<union>{p} is open. B is open. A\<union>{p} and B cover U.
       (A\<union>{p})\<inter>B = {} (since A\<inter>B\<inter>(U-{p})={} and p\<notin>B as B\<inter>R\<subseteq>B\<inter>(A\<union>B)\<inter>U=... ).
       Connected U = (A\<union>{p}) \<union> B. So B = {} or A\<union>{p} = {}. B\<noteq>{}, so A\<union>{p} = U.
       But B\<inter>(U-{p}) \<noteq> {} means B\<inter>U \<noteq> {}, and B \<subseteq> U-(A\<union>{p}) = {}. Contradiction.\<close>
    moreover {
      assume "B \<inter> (?R - {p}) = {}"
      hence "?R - {p} \<subseteq> A" using hcov hRp_sub by auto
      hence "?R \<subseteq> A \<union> {p}" by (by100 blast)
      have "open ?R" by (rule open_Times[OF open_greaterThanLessThan open_greaterThanLessThan])
      have "open (A \<union> ?R)" using hA \<open>open ?R\<close> by (rule open_Un)
      have "A \<union> ?R = A \<union> {p}"
      proof -
        have "p \<in> ?R"
          using \<open>e1 > 0\<close> \<open>e2 > 0\<close> by (cases p) simp
        thus ?thesis using \<open>?R - {p} \<subseteq> A\<close> by (by100 blast)
      qed
      hence "open (A \<union> {p})" using \<open>open (A \<union> ?R)\<close> by simp
      have "p \<notin> B"
      proof
        assume "p \<in> B"
        have "\<exists>q \<in> B. q \<noteq> p" by (rule open_nonempty_R2_has_two_points[OF hB \<open>p \<in> B\<close>])
        then obtain q where "q \<in> B" "q \<noteq> p" by blast
        \<comment> \<open>B open, p \<in> B, so B contains points in R-{p}. But R-{p} \<subseteq> A.\<close>
        have "open (B \<inter> ?R)" using hB \<open>open ?R\<close> by (rule open_Int)
        have "p \<in> ?R" using \<open>e1 > 0\<close> \<open>e2 > 0\<close> by (cases p) simp
        have "p \<in> B \<inter> ?R" using \<open>p \<in> B\<close> \<open>p \<in> ?R\<close> by simp
        obtain q' where "q' \<in> B \<inter> ?R" "q' \<noteq> p"
          using open_nonempty_R2_has_two_points[OF \<open>open (B \<inter> ?R)\<close> \<open>p \<in> B \<inter> ?R\<close>] by blast
        have "B \<inter> (?R - {p}) \<noteq> {}" using \<open>q' \<in> B \<inter> ?R\<close> \<open>q' \<noteq> p\<close> by (by100 blast)
        thus False using \<open>B \<inter> (?R - {p}) = {}\<close> by simp
      qed
      have hABU: "(A \<union> {p}) \<inter> B \<inter> U = {}"
      proof -
        have "A \<inter> B \<inter> U = {}" using hdisj \<open>p \<notin> B\<close> by (by100 blast)
        thus ?thesis using \<open>p \<notin> B\<close> by (by100 blast)
      qed
      have "U \<subseteq> (A \<union> {p}) \<union> B" using hcov True by (by100 blast)
      have "(A \<union> {p}) \<inter> U = {} \<or> B \<inter> U = {}"
        by (rule connectedD[OF assms(2) \<open>open (A \<union> {p})\<close> hB hABU \<open>U \<subseteq> (A \<union> {p}) \<union> B\<close>])
      hence False using hAne hBne True by (by100 blast) }
    moreover {
      assume "A \<inter> (?R - {p}) = {}"
      hence "?R - {p} \<subseteq> B" using hcov hRp_sub by auto
      have hR_open: "open ?R" by (rule open_Times[OF open_greaterThanLessThan open_greaterThanLessThan])
      have "open (B \<union> ?R)" using hB hR_open by (rule open_Un)
      have "p \<in> ?R" using \<open>e1 > 0\<close> \<open>e2 > 0\<close> by (cases p) simp
      have "B \<union> ?R = B \<union> {p}" using \<open>?R - {p} \<subseteq> B\<close> \<open>p \<in> ?R\<close> by (by100 blast)
      hence "open (B \<union> {p})" using \<open>open (B \<union> ?R)\<close> by simp
      have "p \<notin> A"
      proof
        assume "p \<in> A"
        have "open (A \<inter> ?R)" using hA \<open>open ?R\<close> by (rule open_Int)
        have "p \<in> A \<inter> ?R" using \<open>p \<in> A\<close> \<open>p \<in> ?R\<close> by simp
        obtain q' where "q' \<in> A \<inter> ?R" "q' \<noteq> p"
          using open_nonempty_R2_has_two_points[OF \<open>open (A \<inter> ?R)\<close> \<open>p \<in> A \<inter> ?R\<close>] by blast
        have "A \<inter> (?R - {p}) \<noteq> {}" using \<open>q' \<in> A \<inter> ?R\<close> \<open>q' \<noteq> p\<close> by (by100 blast)
        thus False using \<open>A \<inter> (?R - {p}) = {}\<close> by simp
      qed
      have "A \<inter> (B \<union> {p}) \<inter> U = {}" using hdisj \<open>p \<notin> A\<close> by (by100 blast)
      have "U \<subseteq> A \<union> (B \<union> {p})" using hcov True by (by100 blast)
      have "A \<inter> U = {} \<or> (B \<union> {p}) \<inter> U = {}"
        by (rule connectedD[OF assms(2) hA \<open>open (B \<union> {p})\<close>
            \<open>A \<inter> (B \<union> {p}) \<inter> U = {}\<close> \<open>U \<subseteq> A \<union> (B \<union> {p})\<close>])
      hence False using hAne hBne True by (by100 blast) }
    ultimately show False by auto
  qed
qed

\<comment> \<open>Exterior of a ball in R^2 is connected.\<close>
\<comment> \<open>exterior_ball_connected_R2 imported from AlgTopHelpers.\<close>

text \<open>Removing a point from an open connected subset of S^2 preserves connectivity.
  This is the S^2 analogue of connected_open_delete_R2, proved via stereographic projection.\<close>
lemma connected_open_delete_S2:
  assumes "C0 \<in> top1_S2_topology" "top1_connected_on C0 (subspace_topology top1_S2 top1_S2_topology C0)"
      and "b \<in> C0" and "\<exists>c. c \<in> top1_S2 \<and> c \<notin> C0"
  shows "connected (C0 - {b})"
proof -
  obtain c where hc: "c \<in> top1_S2" "c \<notin> C0" using assms(4) by (by100 blast)
  obtain \<sigma> where h\<sigma>: "top1_homeomorphism_on (top1_S2 - {c})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {c}))
      (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) \<sigma>"
    using S2_minus_point_homeo_R2[OF hc(1)] by (by100 blast)
  have hC0_sub_S2: "C0 \<subseteq> top1_S2"
    using top1_S2_is_topology_on_strict assms(1)
    unfolding is_topology_on_strict_def is_topology_on_def by (by100 blast)
  have hC0_sub_S2c: "C0 \<subseteq> top1_S2 - {c}" using hC0_sub_S2 hc(2) by (by100 blast)
  \<comment> \<open>\<sigma>(C0) open in R^2: C0 open in S^2\{c} (subspace), \<sigma> homeomorphism (open map).\<close>
  have h\<sigma>C0_open: "open (\<sigma> ` C0)"
  proof -
    \<comment> \<open>C0 open in S^2\{c} (subspace): C0 open in S^2 and C0 \<subseteq> S^2\{c}.\<close>
    have hC0_open_S2c: "C0 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {c})"
      using assms(1) hC0_sub_S2c unfolding subspace_topology_def by (by100 blast)
    \<comment> \<open>\<sigma> open map: inv continuous \<Rightarrow> preimage of open = open = \<sigma>(open).\<close>
    have hinv_cont: "top1_continuous_map_on UNIV (product_topology_on top1_open_sets top1_open_sets)
        (top1_S2 - {c}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {c}))
        (inv_into (top1_S2 - {c}) \<sigma>)"
      using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
    have hbij: "bij_betw \<sigma> (top1_S2 - {c}) UNIV"
      using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
    have hsurj: "\<sigma> ` (top1_S2 - {c}) = UNIV" using hbij unfolding bij_betw_def by (by100 blast)
    \<comment> \<open>{y \<in> UNIV. inv y \<in> C0} = \<sigma>(C0) and is open in custom R^2 topology.\<close>
    have hpre_open: "{y \<in> UNIV. inv_into (top1_S2 - {c}) \<sigma> y \<in> C0}
        \<in> product_topology_on top1_open_sets top1_open_sets"
      using hinv_cont hC0_open_S2c unfolding top1_continuous_map_on_def by (by100 blast)
    have hpre_eq: "{y \<in> UNIV. inv_into (top1_S2 - {c}) \<sigma> y \<in> C0} = \<sigma> ` C0"
    proof (rule set_eqI, rule iffI)
      fix y assume "y \<in> {y \<in> UNIV. inv_into (top1_S2 - {c}) \<sigma> y \<in> C0}"
      hence hinv_C0: "inv_into (top1_S2 - {c}) \<sigma> y \<in> C0" by simp
      have "y \<in> \<sigma> ` (top1_S2 - {c})" using hsurj by simp
      then obtain x where hx: "x \<in> top1_S2 - {c}" "\<sigma> x = y" by (by100 blast)
      have hinj_loc: "inj_on \<sigma> (top1_S2 - {c})" using hbij unfolding bij_betw_def by (by100 blast)
      have "inv_into (top1_S2 - {c}) \<sigma> (\<sigma> x) = x"
        by (rule inv_into_f_f[OF hinj_loc hx(1)])
      hence "inv_into (top1_S2 - {c}) \<sigma> y = x" using hx(2) by simp
      hence "x \<in> C0" using hinv_C0 by simp
      thus "y \<in> \<sigma> ` C0" using hx(2) by (by100 blast)
    next
      fix y assume "y \<in> \<sigma> ` C0"
      then obtain x where hx: "x \<in> C0" "y = \<sigma> x" by (by100 blast)
      have "x \<in> top1_S2 - {c}" using hC0_sub_S2c hx(1) by (by100 blast)
      have hinj_loc: "inj_on \<sigma> (top1_S2 - {c})" using hbij unfolding bij_betw_def by (by100 blast)
      have "inv_into (top1_S2 - {c}) \<sigma> y = x"
        by (simp add: hx(2) inv_into_f_f[OF hinj_loc \<open>x \<in> top1_S2 - {c}\<close>])
      thus "y \<in> {y \<in> UNIV. inv_into (top1_S2 - {c}) \<sigma> y \<in> C0}" using hx(1) by simp
    qed
    have "\<sigma> ` C0 \<in> product_topology_on top1_open_sets top1_open_sets"
      using hpre_open hpre_eq by simp
    thus ?thesis using product_topology_on_open_sets_real2 unfolding top1_open_sets_def by (by100 simp)
  qed
  \<comment> \<open>\<sigma>(C0) connected: C0 connected (custom), bridge to standard, \<sigma> continuous.\<close>
  have h\<sigma>C0_conn: "connected (\<sigma> ` C0)"
  proof -
    \<comment> \<open>Bridge: C0 connected in custom top \<Rightarrow> connected in standard.\<close>
    have "connected C0"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology C0
          = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) C0"
      proof -
        have hR3eq: "(product_topology_on (top1_open_sets :: real set set)
            (product_topology_on (top1_open_sets :: real set set) (top1_open_sets :: real set set)))
            = (top1_open_sets :: (real \<times> real \<times> real) set set)"
          using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
        have hTS2_sub: "top1_S2_topology = subspace_topology UNIV
            (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
          unfolding top1_S2_topology_def using hR3eq by simp
        have "subspace_topology top1_S2 (subspace_topology UNIV
            (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2) C0
            = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) C0"
          by (rule subspace_topology_trans[OF hC0_sub_S2])
        thus ?thesis using hTS2_sub by simp
      qed
      hence "top1_connected_on C0 (subspace_topology UNIV
          (top1_open_sets :: (real\<times>real\<times>real) set set) C0)"
        using assms(2) by simp
      thus ?thesis using top1_connected_on_subspace_open_iff_connected by (by100 blast)
    qed
    have h\<sigma>_cont_C0: "continuous_on C0 \<sigma>"
    proof -
      have h\<sigma>_cont_cust: "top1_continuous_map_on (top1_S2 - {c})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {c}))
          UNIV (product_topology_on top1_open_sets top1_open_sets) \<sigma>"
        using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
      show ?thesis unfolding continuous_on_open_invariant
      proof (intro allI impI)
        fix V :: "(real \<times> real) set" assume "open V"
        have "V \<in> (top1_open_sets :: (real \<times> real) set set)"
          using \<open>open V\<close> unfolding top1_open_sets_def by simp
        hence "V \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
          using product_topology_on_open_sets_real2 by (by100 metis)
        hence hpre: "{x \<in> top1_S2 - {c}. \<sigma> x \<in> V} \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {c})"
          using h\<sigma>_cont_cust unfolding top1_continuous_map_on_def by (by100 blast)
        then obtain W where hW: "W \<in> top1_S2_topology" "{x \<in> top1_S2 - {c}. \<sigma> x \<in> V} = (top1_S2 - {c}) \<inter> W"
          unfolding subspace_topology_def by (by100 blast)
        have hTS2eq: "top1_S2_topology = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
          unfolding top1_S2_topology_def
          using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
        then obtain W' where hW': "W' \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)" "W = top1_S2 \<inter> W'"
          using hW(1) unfolding subspace_topology_def by (by100 blast)
        have "open W'" using hW'(1) unfolding top1_open_sets_def by simp
        have "W' \<inter> C0 = \<sigma> -` V \<inter> C0"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> W' \<inter> C0"
          hence "x \<in> C0" "x \<in> W'" by auto
          have "x \<in> top1_S2 - {c}" using hC0_sub_S2c \<open>x \<in> C0\<close> by (by100 blast)
          have "x \<in> top1_S2 \<inter> W'" using \<open>x \<in> W'\<close> \<open>x \<in> top1_S2 - {c}\<close> by (by100 blast)
          hence "x \<in> W" using hW'(2) by simp
          hence "x \<in> {x \<in> top1_S2 - {c}. \<sigma> x \<in> V}"
            using \<open>x \<in> top1_S2 - {c}\<close> hW(2) by (by100 blast)
          thus "x \<in> \<sigma> -` V \<inter> C0" using \<open>x \<in> C0\<close> by (by100 blast)
        next
          fix x assume "x \<in> \<sigma> -` V \<inter> C0"
          hence "x \<in> C0" "\<sigma> x \<in> V" by auto
          have "x \<in> top1_S2 - {c}" using hC0_sub_S2c \<open>x \<in> C0\<close> by (by100 blast)
          hence "x \<in> (top1_S2 - {c}) \<inter> W"
            using hW(2) \<open>\<sigma> x \<in> V\<close> \<open>x \<in> top1_S2 - {c}\<close> by (by100 blast)
          hence "x \<in> W" by (by100 blast)
          hence "x \<in> top1_S2 \<inter> W'" using hW'(2) by simp
          thus "x \<in> W' \<inter> C0" using \<open>x \<in> C0\<close> by (by100 blast)
        qed
        thus "\<exists>T. open T \<and> T \<inter> C0 = \<sigma> -` V \<inter> C0" using \<open>open W'\<close> by (by100 blast)
      qed
    qed
    show ?thesis using connected_continuous_image[OF h\<sigma>_cont_C0 \<open>connected C0\<close>] by simp
  qed
  \<comment> \<open>\<sigma>(C0)\{\<sigma>(b)} connected by connected_open_delete_R2.\<close>
  have "connected (\<sigma> ` C0 - {\<sigma> b})" by (rule connected_open_delete_R2[OF h\<sigma>C0_open h\<sigma>C0_conn])
  \<comment> \<open>\<sigma>(C0\{b}) = \<sigma>(C0)\{\<sigma>(b)} by injectivity.\<close>
  have hinj: "inj_on \<sigma> (top1_S2 - {c})"
    using h\<sigma> unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have "\<sigma> ` (C0 - {b}) = \<sigma> ` C0 - {\<sigma> b}"
  proof -
    have "{b} \<subseteq> C0" using assms(3) by (by100 blast)
    have "C0 - {b} \<subseteq> C0" by (by100 blast)
    have "\<sigma> ` (C0 - {b}) = \<sigma> ` C0 - \<sigma> ` {b}"
      by (rule inj_on_image_set_diff[OF inj_on_subset[OF hinj hC0_sub_S2c]
          \<open>C0 - {b} \<subseteq> C0\<close> \<open>{b} \<subseteq> C0\<close>])
    thus ?thesis by simp
  qed
  hence "connected (\<sigma> ` (C0 - {b}))" using \<open>connected (\<sigma> ` C0 - {\<sigma> b})\<close> by simp
  \<comment> \<open>C0\{b} = \<sigma>^{-1}(\<sigma>(C0\{b})). \<sigma>^{-1} continuous. connected image.\<close>
  \<comment> \<open>Actually: \<sigma> restricted to C0\{b} is a homeomorphism onto \<sigma>(C0\{b}).
     So C0\{b} homeomorphic to connected set \<Rightarrow> connected.
     Use: \<sigma>^{-1} continuous (standard) on \<sigma>(C0\{b}), image = C0\{b}.\<close>
  have h\<sigma>inv_cont: "continuous_on (\<sigma> ` (C0 - {b})) (inv_into (top1_S2 - {c}) \<sigma>)"
  proof -
    \<comment> \<open>inv continuous on UNIV from custom topology. Bridge to standard on \<sigma>(C0\{b}).\<close>
    have hinv_cust: "top1_continuous_map_on UNIV (product_topology_on top1_open_sets top1_open_sets)
        (top1_S2 - {c}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {c}))
        (inv_into (top1_S2 - {c}) \<sigma>)"
      using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
    have h\<sigma>C0b_sub: "\<sigma> ` (C0 - {b}) \<subseteq> UNIV" by simp
    show ?thesis unfolding continuous_on_open_invariant
    proof (intro allI impI)
      fix V :: "(real\<times>real\<times>real) set" assume "open V"
      have "V \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
        using \<open>open V\<close> unfolding top1_open_sets_def by simp
      \<comment> \<open>Need: {y \<in> \<sigma>(C0\{b}). inv y \<in> V} is open rel \<sigma>(C0\{b}).
         inv maps into S^2\{c}. V open in R^3.
         {y \<in> UNIV. inv y \<in> V'} for some V' in subspace of S^2\{c} is open in R^2.\<close>
      \<comment> \<open>V \<inter> (S^2\{c}) open in subspace_topology S^2 S^2_top (S^2\{c}).\<close>
      have hV_S2c: "V \<inter> (top1_S2 - {c}) \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {c})"
      proof -
        have hR3eq: "(product_topology_on (top1_open_sets :: real set set)
            (product_topology_on (top1_open_sets :: real set set) (top1_open_sets :: real set set)))
            = (top1_open_sets :: (real \<times> real \<times> real) set set)"
          using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
        have hTS2_sub: "top1_S2_topology = subspace_topology UNIV
            (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
          unfolding top1_S2_topology_def using hR3eq by simp
        have "subspace_topology top1_S2 top1_S2_topology (top1_S2 - {c})
            = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) (top1_S2 - {c})"
        proof -
          have "subspace_topology top1_S2 (subspace_topology UNIV
              (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2) (top1_S2 - {c})
              = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) (top1_S2 - {c})"
            by (rule subspace_topology_trans) blast
          thus ?thesis using hTS2_sub by simp
        qed
        moreover have "V \<inter> (top1_S2 - {c}) \<in> subspace_topology UNIV
            (top1_open_sets :: (real\<times>real\<times>real) set set) (top1_S2 - {c})"
          using \<open>V \<in> top1_open_sets\<close> unfolding subspace_topology_def by (by100 blast)
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>Preimage under inv of V \<inter> (S^2\{c}) is open in R^2 (custom = standard).\<close>
      have hinv_cont_loc: "top1_continuous_map_on UNIV (product_topology_on top1_open_sets top1_open_sets)
          (top1_S2 - {c}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {c}))
          (inv_into (top1_S2 - {c}) \<sigma>)"
        using h\<sigma> unfolding top1_homeomorphism_on_def by (by100 blast)
      have hpre: "{y \<in> UNIV. inv_into (top1_S2 - {c}) \<sigma> y \<in> V \<inter> (top1_S2 - {c})}
          \<in> product_topology_on top1_open_sets top1_open_sets"
        using hinv_cont_loc hV_S2c unfolding top1_continuous_map_on_def by (by100 blast)
      define T where "T = {y. inv_into (top1_S2 - {c}) \<sigma> y \<in> V}"
      have "open T"
      proof -
        have "T = {y \<in> UNIV. inv_into (top1_S2 - {c}) \<sigma> y \<in> V \<inter> (top1_S2 - {c})}"
        proof -
          have "\<forall>y. inv_into (top1_S2 - {c}) \<sigma> y \<in> top1_S2 - {c}"
            using hinv_cont_loc unfolding top1_continuous_map_on_def by (by100 blast)
          thus ?thesis unfolding T_def by (by100 blast)
        qed
        hence "T \<in> product_topology_on top1_open_sets top1_open_sets" using hpre by simp
        thus ?thesis using product_topology_on_open_sets_real2 unfolding top1_open_sets_def by (by100 simp)
      qed
      moreover have "T \<inter> \<sigma> ` (C0 - {b}) = inv_into (top1_S2 - {c}) \<sigma> -` V \<inter> \<sigma> ` (C0 - {b})"
        unfolding T_def by (by100 blast)
      ultimately show "\<exists>T. open T \<and> T \<inter> \<sigma> ` (C0 - {b}) = inv_into (top1_S2 - {c}) \<sigma> -` V \<inter> \<sigma> ` (C0 - {b})"
        by (by100 blast)
    qed
  qed
  have h\<sigma>inv_img: "inv_into (top1_S2 - {c}) \<sigma> ` (\<sigma> ` (C0 - {b})) = C0 - {b}"
  proof -
    have hC0b_sub: "C0 - {b} \<subseteq> top1_S2 - {c}" using hC0_sub_S2c by (by100 blast)
    show ?thesis
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> inv_into (top1_S2 - {c}) \<sigma> ` (\<sigma> ` (C0 - {b}))"
      then obtain y where hy: "y \<in> \<sigma> ` (C0 - {b})" "x = inv_into (top1_S2 - {c}) \<sigma> y" by (by100 blast)
      then obtain z where hz: "z \<in> C0 - {b}" "y = \<sigma> z" by (by100 blast)
      have "z \<in> top1_S2 - {c}" using hC0b_sub hz(1) by (by100 blast)
      have "inv_into (top1_S2 - {c}) \<sigma> (\<sigma> z) = z"
        by (rule inv_into_f_f[OF hinj \<open>z \<in> top1_S2 - {c}\<close>])
      thus "x \<in> C0 - {b}" using hy(2) hz by simp
    next
      fix x assume hx: "x \<in> C0 - {b}"
      have "x \<in> top1_S2 - {c}" using hC0b_sub hx by (by100 blast)
      have h\<sigma>x: "\<sigma> x \<in> \<sigma> ` (C0 - {b})" using hx by (by100 blast)
      have "inv_into (top1_S2 - {c}) \<sigma> (\<sigma> x) = x"
        by (rule inv_into_f_f[OF hinj \<open>x \<in> top1_S2 - {c}\<close>])
      hence "inv_into (top1_S2 - {c}) \<sigma> (\<sigma> x) \<in> inv_into (top1_S2 - {c}) \<sigma> ` (\<sigma> ` (C0 - {b}))"
        using h\<sigma>x by (by100 blast)
      thus "x \<in> inv_into (top1_S2 - {c}) \<sigma> ` (\<sigma> ` (C0 - {b}))"
        using \<open>inv_into (top1_S2 - {c}) \<sigma> (\<sigma> x) = x\<close> by simp
    qed
  qed
  show ?thesis
    using connected_continuous_image[OF h\<sigma>inv_cont \<open>connected (\<sigma> ` (C0 - {b}))\<close>]
      h\<sigma>inv_img by simp
qed

lemma connected_open_delete_S2':
  assumes "C0 \<in> top1_S2_topology" "top1_connected_on C0 (subspace_topology top1_S2 top1_S2_topology C0)"
      and "b \<in> C0" and "c \<in> top1_S2" and "c \<notin> C0"
      and "continuous_on (C0 - {b}) h" and "h ` (C0 - {b}) = S"
  shows "connected S"
proof -
  have hconn: "connected (C0 - {b})" by (rule connected_open_delete_S2[OF assms(1,2,3)]) (use assms(4,5) in blast)
  have "connected (h ` (C0 - {b}))" by (rule connected_continuous_image[OF assms(6) hconn])
  thus ?thesis using assms(7) by simp
qed

lemma continuous_compose_product_R2:
  fixes g :: "'a \<Rightarrow> real \<times> real" and \<phi> :: "(real \<times> real) \<times> real \<Rightarrow> real \<times> real"
    and A :: "'a set" and TA :: "'a set set" and S :: "(real \<times> real) set"
  assumes hg: "top1_continuous_map_on A TA (UNIV :: (real\<times>real) set)
      (product_topology_on top1_open_sets top1_open_sets) g"
      and h\<phi>: "continuous_on (UNIV \<times> I_set) \<phi>"
      and hrange: "\<forall>a\<in>A. \<forall>t\<in>I_set. \<phi> (g a, t) \<in> S"
      and hTA: "is_topology_on A TA"
  shows "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) S
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S)
      (\<lambda>xt. \<phi> (g (fst xt), snd xt))"
proof -
  let ?TR2 = "product_topology_on (top1_open_sets :: real set set) top1_open_sets"
  let ?f = "\<lambda>xt. \<phi> (g (fst xt), snd xt)"
  have hTR2eq: "?TR2 = (top1_open_sets :: (real \<times> real) set set)"
    using product_topology_on_open_sets_real2 by (by100 metis)
  have hTI: "is_topology_on I_set I_top"
    unfolding top1_unit_interval_topology_def
    by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) simp
  show ?thesis unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix xt assume "xt \<in> A \<times> I_set"
    thus "?f xt \<in> S" using hrange by auto
  next
    fix V assume hV: "V \<in> subspace_topology UNIV ?TR2 S"
    obtain W where hW: "W \<in> ?TR2" and hV_eq: "V = S \<inter> W"
      using hV unfolding subspace_topology_def by (by100 blast)
    have hW_open: "open W" using hW hTR2eq unfolding top1_open_sets_def by (by100 blast)
    obtain W' where hW'_open: "open W'"
        and hW'_eq: "\<phi> -` W \<inter> (UNIV \<times> I_set) = W' \<inter> (UNIV \<times> I_set)"
    proof -
      have hcoi: "\<forall>T. open T \<longrightarrow> (\<exists>T'. open T' \<and> T' \<inter> (UNIV \<times> I_set) = \<phi> -` T \<inter> (UNIV \<times> I_set))"
        using iffD1[OF continuous_on_open_invariant h\<phi>] by (by100 blast)
      have "\<exists>T'. open T' \<and> T' \<inter> (UNIV \<times> I_set) = \<phi> -` W \<inter> (UNIV \<times> I_set)"
        using hcoi hW_open by (by100 blast)
      then obtain T' where "open T'" "T' \<inter> (UNIV \<times> I_set) = \<phi> -` W \<inter> (UNIV \<times> I_set)" by blast
      have "\<exists>T'. open T' \<and> \<phi> -` W \<inter> (UNIV \<times> I_set) = T' \<inter> (UNIV \<times> I_set)"
        using \<open>open T'\<close> \<open>T' \<inter> (UNIV \<times> I_set) = \<phi> -` W \<inter> (UNIV \<times> I_set)\<close> by (by100 blast)
      thus ?thesis using that by (by100 blast)
    qed
    show "{xt \<in> A \<times> I_set. ?f xt \<in> V} \<in> product_topology_on TA I_top"
      unfolding product_topology_on_def topology_generated_by_basis_def
    proof (rule CollectI, intro conjI)
      show "{xt \<in> A \<times> I_set. ?f xt \<in> V} \<subseteq> UNIV" by simp
      show "\<forall>p\<in>{xt \<in> A \<times> I_set. ?f xt \<in> V}.
          \<exists>b\<in>product_basis TA I_top. p \<in> b \<and> b \<subseteq> {xt \<in> A \<times> I_set. ?f xt \<in> V}"
      proof
        fix xt assume hxt_mem: "xt \<in> {xt \<in> A \<times> I_set. ?f xt \<in> V}"
        hence ha: "fst xt \<in> A" and ht: "snd xt \<in> I_set" by auto
        have "?f xt \<in> V" using hxt_mem by simp
        hence "?f xt \<in> W" using hV_eq hrange ha ht by (by100 blast)
        hence hW'_mem: "(g (fst xt), snd xt) \<in> W'"
          using hW'_eq ht by (by100 blast)
        obtain Uy Ut where hUy_open: "open Uy" and hUt_open: "open Ut"
            and hUy_mem: "g (fst xt) \<in> Uy" and hUt_mem: "snd xt \<in> Ut"
            and hUyUt_sub: "Uy \<times> Ut \<subseteq> W'"
        proof -
          from open_prod_elim[OF hW'_open hW'_mem]
          obtain A0 B0 where hA0: "open A0" "open B0" "(g (fst xt), snd xt) \<in> A0 \<times> B0" "A0 \<times> B0 \<subseteq> W'"
            by (by100 blast)
          have "g (fst xt) \<in> A0" "snd xt \<in> B0" using hA0(3) by auto
          thus ?thesis using that hA0(1,2,4) by (by100 blast)
        qed
        have hUy_TR2: "Uy \<in> ?TR2" using hUy_open hTR2eq unfolding top1_open_sets_def by (by100 blast)
        have hpre_g: "{a \<in> A. g a \<in> Uy} \<in> TA"
          using hg hUy_TR2 unfolding top1_continuous_map_on_def by (by100 blast)
        have hUt_I: "Ut \<inter> I_set \<in> I_top"
        proof -
          have "Ut \<in> top1_open_sets" using hUt_open unfolding top1_open_sets_def by simp
          hence "I_set \<inter> Ut \<in> I_top" unfolding top1_unit_interval_topology_def
            by (rule subspace_topology_memI)
          thus ?thesis by (simp add: Int_commute)
        qed
        define B where "B = {a \<in> A. g a \<in> Uy} \<times> (Ut \<inter> I_set)"
        have hB_basis: "B \<in> product_basis TA I_top"
          unfolding B_def product_basis_def using hpre_g hUt_I by (by100 blast)
        have hB_mem: "xt \<in> B" unfolding B_def
        proof -
          have "fst xt \<in> {a \<in> A. g a \<in> Uy}" using ha hUy_mem by simp
          moreover have "snd xt \<in> Ut \<inter> I_set" using hUt_mem ht by simp
          ultimately show "xt \<in> {a \<in> A. g a \<in> Uy} \<times> (Ut \<inter> I_set)"
            using SigmaI[of "fst xt" _ "snd xt"] by (by100 force)
        qed
        have hB_sub: "B \<subseteq> {xt \<in> A \<times> I_set. ?f xt \<in> V}"
        proof
          fix yt assume "yt \<in> B"
          hence "fst yt \<in> A" "g (fst yt) \<in> Uy" "snd yt \<in> Ut" "snd yt \<in> I_set"
            unfolding B_def by auto
          hence "(g (fst yt), snd yt) \<in> Uy \<times> Ut" by simp
          hence "(g (fst yt), snd yt) \<in> W'" using hUyUt_sub by (by100 blast)
          hence "(g (fst yt), snd yt) \<in> UNIV \<times> I_set" using \<open>snd yt \<in> I_set\<close> by simp
          hence "(g (fst yt), snd yt) \<in> \<phi> -` W \<inter> (UNIV \<times> I_set)"
            using hW'_eq \<open>(g (fst yt), snd yt) \<in> W'\<close> by (by100 blast)
          hence "\<phi> (g (fst yt), snd yt) \<in> W" by simp
          moreover have "\<phi> (g (fst yt), snd yt) \<in> S"
            using hrange \<open>fst yt \<in> A\<close> \<open>snd yt \<in> I_set\<close> by simp
          ultimately have "?f yt \<in> V" using hV_eq by (by100 blast)
          have "yt \<in> A \<times> I_set"
            using \<open>fst yt \<in> A\<close> \<open>snd yt \<in> I_set\<close>
            by (metis SigmaI surjective_pairing)
          thus "yt \<in> {xt \<in> A \<times> I_set. ?f xt \<in> V}" using \<open>?f yt \<in> V\<close> by simp
        qed
        show "\<exists>b\<in>product_basis TA I_top. xt \<in> b \<and> b \<subseteq> {xt \<in> A \<times> I_set. ?f xt \<in> V}"
          using hB_basis hB_mem hB_sub by (by100 blast)
      qed
    qed
  qed
qed

\<comment> \<open>Translation homeomorphism: T(x) = pair_sub x c maps R^2-{c} \<cong> R^2-{0}.\<close>
lemma translation_homeo_R2:
  fixes c :: "real \<times> real"
  defines "T \<equiv> \<lambda>x. (fst x - fst c, snd x - snd c)"
  shows "top1_homeomorphism_on (UNIV - {c})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {c}))
      (UNIV - {(0,0)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0,0)}))
      T"
  unfolding top1_homeomorphism_on_def
proof (intro conjI)
  let ?TR2 = "product_topology_on (top1_open_sets :: real set set) top1_open_sets"
  have hTR2eq: "?TR2 = (top1_open_sets :: (real \<times> real) set set)"
    using product_topology_on_open_sets_real2 by (by100 metis)
  let ?X = "UNIV - {c}" and ?Y = "UNIV - {(0::real,0::real)}"
  let ?TX = "subspace_topology UNIV ?TR2 ?X" and ?TY = "subspace_topology UNIV ?TR2 ?Y"
  have hTR2': "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
    using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
        top1_open_sets_is_topology_on_UNIV] by simp
  show hTX: "is_topology_on ?X ?TX" by (rule subspace_topology_is_topology_on[OF hTR2']) simp
  show hTY: "is_topology_on ?Y ?TY" by (rule subspace_topology_is_topology_on[OF hTR2']) simp
  \<comment> \<open>T bijective.\<close>
  show "bij_betw T ?X ?Y" unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on T ?X" unfolding T_def inj_on_def by auto
    show "T ` ?X = ?Y"
    proof (rule set_eqI, rule iffI)
      fix y assume "y \<in> T ` ?X"
      then obtain x where hx: "x \<noteq> c" and hy: "y = T x" by (by100 blast)
      have "T x \<noteq> (0, 0)" using hx unfolding T_def
        by (cases x, cases c) simp
      thus "y \<in> ?Y" using hy by simp
    next
      fix y assume "y \<in> ?Y"
      hence "y \<noteq> (0, 0)" by simp
      define x where "x = (fst y + fst c, snd y + snd c)"
      have "x \<noteq> c" using \<open>y \<noteq> (0,0)\<close> unfolding x_def
        by (cases y, cases c) simp
      moreover have "T x = y" unfolding T_def x_def by simp
      ultimately show "y \<in> T ` ?X" by (by100 blast)
    qed
  qed
  \<comment> \<open>T continuous: standard subtraction is continuous, bridge to custom framework.\<close>
  show "top1_continuous_map_on ?X ?TX ?Y ?TY T"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix x assume "x \<in> ?X"
    thus "T x \<in> ?Y" unfolding T_def by (cases x, cases c) simp
  next
    fix V assume hV: "V \<in> ?TY"
    obtain W where hW: "W \<in> ?TR2" and hV_eq: "V = ?Y \<inter> W"
      using hV unfolding subspace_topology_def by (by100 blast)
    \<comment> \<open>W is open in R^2 (standard). T^{-1}(W) is open (standard continuous).\<close>
    have hW_open: "open W" using hW hTR2eq unfolding top1_open_sets_def by (by100 blast)
    have hTinv_open: "open {x. T x \<in> W}"
    proof -
      have "continuous_on UNIV T" unfolding T_def by (intro continuous_intros)
      hence "open (T -` W)" using hW_open
        by (simp add: continuous_on_open_vimage[OF open_UNIV])
      moreover have "{x. T x \<in> W} = T -` W" by auto
      ultimately show ?thesis by simp
    qed
    have "{x. T x \<in> W} \<in> top1_open_sets" using hTinv_open unfolding top1_open_sets_def by simp
    hence "{x. T x \<in> W} \<in> ?TR2" using hTR2eq by simp
    have "{x \<in> ?X. T x \<in> V} = ?X \<inter> {x. T x \<in> W}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> {x \<in> ?X. T x \<in> V}"
      hence "x \<in> ?X" and "T x \<in> V" by auto
      hence "T x \<in> W" using hV_eq by (by100 blast)
      thus "x \<in> ?X \<inter> {x. T x \<in> W}" using \<open>x \<in> ?X\<close> by (by100 blast)
    next
      fix x assume "x \<in> ?X \<inter> {x. T x \<in> W}"
      hence "x \<in> ?X" and "T x \<in> W" by auto
      have "T x \<in> ?Y" unfolding T_def using \<open>x \<in> ?X\<close>
        by (cases x, cases c) simp
      hence "T x \<in> V" using \<open>T x \<in> W\<close> hV_eq by (by100 blast)
      thus "x \<in> {x \<in> ?X. T x \<in> V}" using \<open>x \<in> ?X\<close> by (by100 blast)
    qed
    also have "... \<in> ?TX" by (rule subspace_topology_memI[OF \<open>{x. T x \<in> W} \<in> ?TR2\<close>])
    finally show "{x \<in> ?X. T x \<in> V} \<in> ?TX" .
  qed
  \<comment> \<open>T^{-1} continuous.\<close>
  define Tinv where "Tinv = (\<lambda>y :: real \<times> real. (fst y + fst c, snd y + snd c))"
  show "top1_continuous_map_on ?Y ?TY ?X ?TX (inv_into ?X T)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix y assume "y \<in> ?Y"
    hence "y \<noteq> (0,0)" by simp
    define x where "x = Tinv y"
    have "x \<in> ?X" unfolding x_def Tinv_def using \<open>y \<noteq> (0,0)\<close>
      by (cases y, cases c) simp
    moreover have "T x = y" unfolding T_def x_def Tinv_def by simp
    ultimately have "inv_into ?X T y = x"
      by (intro inv_into_f_eq) (auto simp: T_def inj_on_def)
    thus "inv_into ?X T y \<in> ?X" using \<open>x \<in> ?X\<close> by simp
  next
    fix U0 assume hU0: "U0 \<in> ?TX"
    obtain W where hW: "W \<in> ?TR2" and hU0_eq: "U0 = ?X \<inter> W"
      using hU0 unfolding subspace_topology_def by (by100 blast)
    have hW_open: "open W" using hW hTR2eq unfolding top1_open_sets_def by (by100 blast)
    \<comment> \<open>inv_into ?X T = Tinv on ?Y.\<close>
    have hinv_eq: "\<And>y. y \<in> ?Y \<Longrightarrow> inv_into ?X T y = Tinv y"
    proof -
      fix y assume "y \<in> ?Y"
      hence "y \<noteq> (0,0)" by simp
      have "Tinv y \<in> ?X" unfolding Tinv_def using \<open>y \<noteq> (0,0)\<close>
        by (cases y, cases c) simp
      moreover have "T (Tinv y) = y" unfolding T_def Tinv_def by simp
      ultimately show "inv_into ?X T y = Tinv y"
        by (intro inv_into_f_eq) (auto simp: T_def inj_on_def)
    qed
    have hTinv_pre_open: "open {y. Tinv y \<in> W}"
    proof -
      have "continuous_on UNIV Tinv" unfolding Tinv_def by (intro continuous_intros)
      hence "open (Tinv -` W)" using hW_open
        by (simp add: continuous_on_open_vimage[OF open_UNIV])
      moreover have "{y. Tinv y \<in> W} = Tinv -` W" by auto
      ultimately show ?thesis by simp
    qed
    have "{y. Tinv y \<in> W} \<in> top1_open_sets" using hTinv_pre_open unfolding top1_open_sets_def by simp
    hence "{y. Tinv y \<in> W} \<in> ?TR2" using hTR2eq by simp
    have "{y \<in> ?Y. inv_into ?X T y \<in> U0} = ?Y \<inter> {y. Tinv y \<in> W}"
    proof (rule set_eqI, rule iffI)
      fix y assume "y \<in> {y \<in> ?Y. inv_into ?X T y \<in> U0}"
      hence hy: "y \<in> ?Y" and "inv_into ?X T y \<in> U0" by auto
      hence "Tinv y \<in> U0" using hinv_eq by simp
      hence "Tinv y \<in> ?X \<inter> W" using hU0_eq by simp
      thus "y \<in> ?Y \<inter> {y. Tinv y \<in> W}" using hy by (by100 blast)
    next
      fix y assume "y \<in> ?Y \<inter> {y. Tinv y \<in> W}"
      hence hy: "y \<in> ?Y" and "Tinv y \<in> W" by auto
      have "Tinv y \<in> ?X" unfolding Tinv_def using hy
        by (cases y, cases c) simp
      hence "Tinv y \<in> U0" using \<open>Tinv y \<in> W\<close> hU0_eq by simp
      hence "inv_into ?X T y \<in> U0" using hinv_eq hy by simp
      thus "y \<in> {y \<in> ?Y. inv_into ?X T y \<in> U0}" using hy by simp
    qed
    also have "... \<in> ?TY" by (rule subspace_topology_memI[OF \<open>{y. Tinv y \<in> W} \<in> ?TR2\<close>])
    finally show "{y \<in> ?Y. inv_into ?X T y \<in> U0} \<in> ?TY" .
  qed
qed

definition pair_sub :: "(real \<times> real) \<Rightarrow> (real \<times> real) \<Rightarrow> (real \<times> real)" where
  "pair_sub a b = (fst a - fst b, snd a - snd b)"

definition pair_scl :: "real \<Rightarrow> (real \<times> real) \<Rightarrow> (real \<times> real)" where
  "pair_scl t a = (t * fst a, t * snd a)"

text \<open>Textbook version of Lemma 61.2: if a, b lie in the same component
  of S^2 - f(A), then f: A \<rightarrow> S^2 - {a,b} is nulhomotopic.\<close>
lemma Lemma_61_2_nulhomotopy_textbook:
  fixes A :: "'a set" and TA :: "'a set set" and f :: "'a \<Rightarrow> real \<times> real \<times> real"
    and a b :: "real \<times> real \<times> real"
  assumes hT: "is_topology_on_strict top1_S2 top1_S2_topology"
      and hcomp: "top1_compact_on A TA"
      and ha: "a \<in> top1_S2" and hb: "b \<in> top1_S2" and hab: "a \<noteq> b"
      and hf: "top1_continuous_map_on A TA
             (top1_S2 - {a, b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})) f"
      and hsame: "\<exists>C. C \<in> top1_components_on (top1_S2 - f ` A)
             (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A))
             \<and> a \<in> C \<and> b \<in> C"
  shows "top1_nulhomotopic_on A TA
           (top1_S2 - {a, b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})) f"
proof -
  \<comment> \<open>Step 1: Transfer to R^2 via stereographic projection from b.
     h: S^2-{b} \<rightarrow> R^2 homeomorphism. Set g = h \<circ> f: A \<rightarrow> R^2-{h(a)}.\<close>
  obtain h where hh: "top1_homeomorphism_on (top1_S2 - {b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
      (UNIV :: (real \<times> real) set)
      (product_topology_on top1_open_sets top1_open_sets) h"
    using S2_minus_point_homeo_R2[OF hb] by blast
  let ?ha = "h a"
  \<comment> \<open>Step 2: g = h \<circ> f maps A into R^2-{ha}. g is continuous.\<close>
  have hg_cont: "top1_continuous_map_on A TA (UNIV - {?ha})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {?ha}))
      (h \<circ> f)"
  proof -
    have hh_cont: "top1_continuous_map_on (top1_S2 - {b})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
        UNIV (product_topology_on top1_open_sets top1_open_sets) h"
      using hh unfolding top1_homeomorphism_on_def by (by100 blast)
    have hinj: "inj_on h (top1_S2 - {b})"
      using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have ha_S2b: "a \<in> top1_S2 - {b}" using ha hab by (by100 blast)
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume hx: "x \<in> A"
      have hfx: "f x \<in> top1_S2 - {a, b}" using hf hx unfolding top1_continuous_map_on_def by (by100 blast)
      hence "f x \<in> top1_S2 - {b}" by (by100 blast)
      hence "h (f x) \<in> UNIV" by simp
      moreover have "h (f x) \<noteq> ?ha"
        using hinj \<open>f x \<in> top1_S2 - {b}\<close> ha_S2b hfx unfolding inj_on_def by (by100 blast)
      ultimately show "(h \<circ> f) x \<in> UNIV - {?ha}" unfolding comp_def by (by100 blast)
    next
      fix V :: "(real \<times> real) set"
      assume hV: "V \<in> subspace_topology UNIV (product_topology_on (top1_open_sets :: real set set) top1_open_sets) (UNIV - {?ha})"
      obtain W where hW: "W \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
          and hV_eq: "V = (UNIV - {?ha}) \<inter> W"
        using hV unfolding subspace_topology_def by (by100 blast)
      \<comment> \<open>h preimage of W in S^2-{b}.\<close>
      have hpre_h: "{x \<in> top1_S2 - {b}. h x \<in> W} \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
        using hh_cont hW unfolding top1_continuous_map_on_def by (by100 blast)
      obtain U' where hU': "U' \<in> top1_S2_topology"
          and hpre_eq: "{x \<in> top1_S2 - {b}. h x \<in> W} = (top1_S2 - {b}) \<inter> U'"
        using hpre_h unfolding subspace_topology_def by (by100 blast)
      \<comment> \<open>Restrict to S^2-{a,b}: (S^2-{a,b}) \<inter> U' is in subspace topology.\<close>
      have hpre_sub: "(top1_S2 - {a,b}) \<inter> U' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a,b})"
        by (rule subspace_topology_memI[OF hU'])
      have hpre_eq2: "{x \<in> top1_S2 - {a,b}. h x \<in> W} = (top1_S2 - {a,b}) \<inter> U'"
        using hpre_eq by (by100 blast)
      have hpre_final: "{x \<in> top1_S2 - {a,b}. h x \<in> W} \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a,b})"
        using hpre_sub hpre_eq2 by simp
      \<comment> \<open>Use f's continuity to pull back.\<close>
      have "{x \<in> A. f x \<in> {y \<in> top1_S2 - {a,b}. h y \<in> W}} \<in> TA"
        using hf hpre_final unfolding top1_continuous_map_on_def by (by100 blast)
      moreover have "{x \<in> A. (h \<circ> f) x \<in> V} = {x \<in> A. f x \<in> {y \<in> top1_S2 - {a,b}. h y \<in> W}}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> A. (h \<circ> f) x \<in> V}"
        hence hxA: "x \<in> A" and "h (f x) \<in> V" unfolding comp_def by auto
        have "f x \<in> top1_S2 - {a,b}" using hf hxA unfolding top1_continuous_map_on_def by (by100 blast)
        moreover have "h (f x) \<in> W" using \<open>h (f x) \<in> V\<close> hV_eq by (by100 blast)
        ultimately show "x \<in> {x \<in> A. f x \<in> {y \<in> top1_S2 - {a,b}. h y \<in> W}}" using hxA by (by100 blast)
      next
        fix x assume "x \<in> {x \<in> A. f x \<in> {y \<in> top1_S2 - {a,b}. h y \<in> W}}"
        hence hxA: "x \<in> A" and "f x \<in> top1_S2 - {a,b}" and "h (f x) \<in> W" by auto
        have "h (f x) \<noteq> ?ha"
          using hinj \<open>f x \<in> top1_S2 - {a,b}\<close> ha_S2b unfolding inj_on_def by (by100 blast)
        thus "x \<in> {x \<in> A. (h \<circ> f) x \<in> V}" unfolding comp_def hV_eq
          using hxA \<open>h (f x) \<in> W\<close> by (by100 blast)
      qed
      ultimately show "{x \<in> A. (h \<circ> f) x \<in> V} \<in> TA" by simp
    qed
  qed
  \<comment> \<open>Step 3: g(A) = (h\<circ>f)(A) is compact, hence bounded.\<close>
  have hgA_compact: "compact ((h \<circ> f) ` A)"
  proof -
    let ?R2 = "product_topology_on (top1_open_sets :: real set set) top1_open_sets"
    have hTR2: "is_topology_on (UNIV :: (real \<times> real) set) ?R2"
    proof -
      have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
      show ?thesis using product_topology_on_is_topology_on[OF hTR hTR] by simp
    qed
    \<comment> \<open>h \<circ> f continuous into UNIV (expand range from UNIV-{ha} to UNIV).\<close>
    have hgf_cont_UNIV: "top1_continuous_map_on A TA UNIV ?R2 (h \<circ> f)"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume "x \<in> A" thus "(h \<circ> f) x \<in> UNIV" by simp
    next
      fix V :: "(real \<times> real) set" assume hV: "V \<in> ?R2"
      have "(UNIV - {?ha}) \<inter> V \<in> subspace_topology UNIV ?R2 (UNIV - {?ha})"
        by (rule subspace_topology_memI[OF hV])
      hence "V \<inter> (UNIV - {?ha}) \<in> subspace_topology UNIV ?R2 (UNIV - {?ha})"
        by (simp add: Int_commute)
      hence "{x \<in> A. (h \<circ> f) x \<in> V \<inter> (UNIV - {?ha})} \<in> TA"
        using hg_cont unfolding top1_continuous_map_on_def by (by100 blast)
      moreover have "{x \<in> A. (h \<circ> f) x \<in> V} = {x \<in> A. (h \<circ> f) x \<in> V \<inter> (UNIV - {?ha})}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> A. (h \<circ> f) x \<in> V}"
        hence "x \<in> A" and "(h \<circ> f) x \<in> V" by auto
        moreover have "(h \<circ> f) x \<in> UNIV - {?ha}"
          using hg_cont \<open>x \<in> A\<close> unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "x \<in> {x \<in> A. (h \<circ> f) x \<in> V \<inter> (UNIV - {?ha})}" by (by100 blast)
      next
        fix x assume "x \<in> {x \<in> A. (h \<circ> f) x \<in> V \<inter> (UNIV - {?ha})}"
        thus "x \<in> {x \<in> A. (h \<circ> f) x \<in> V}" by (by100 blast)
      qed
      ultimately show "{x \<in> A. (h \<circ> f) x \<in> V} \<in> TA" by simp
    qed
    have "top1_compact_on ((h \<circ> f) ` A) (subspace_topology UNIV ?R2 ((h \<circ> f) ` A))"
      by (rule top1_compact_on_continuous_image[OF hcomp hTR2 hgf_cont_UNIV])
    moreover have "?R2 = (top1_open_sets :: (real \<times> real) set set)"
      using product_topology_on_open_sets_real2 by (by100 metis)
    ultimately have "top1_compact_on ((h \<circ> f) ` A) (subspace_topology UNIV (top1_open_sets :: (real \<times> real) set set) ((h \<circ> f) ` A))"
      by simp
    thus ?thesis using top1_compact_on_subspace_UNIV_iff_compact[of "(h \<circ> f) ` A"] by simp
  qed
  then obtain M where hM: "M > 0" and hgA_bdd: "\<forall>p \<in> (h \<circ> f) ` A. fst p ^ 2 + snd p ^ 2 \<le> M ^ 2"
  proof -
    \<comment> \<open>Use compact_attains_sup on the squared-norm function, same pattern as hC_bounded.\<close>
    have hcont_sqnorm: "continuous_on ((h \<circ> f) ` A) (\<lambda>p. fst p ^ 2 + snd p ^ 2)"
      by (intro continuous_intros)
    define img where "img = (\<lambda>p :: real \<times> real. fst p ^ 2 + snd p ^ 2) ` ((h \<circ> f) ` A)"
    have himg_compact: "compact img" unfolding img_def
      by (rule compact_continuous_image[OF hcont_sqnorm hgA_compact])
    show ?thesis
    proof (cases "(h \<circ> f) ` A = {}")
      case True
      hence "\<forall>p \<in> (h \<circ> f) ` A. fst p ^ 2 + snd p ^ 2 \<le> 1" by (by100 blast)
      thus ?thesis using that[of 1] by (by100 simp)
    next
      case False
      hence "img \<noteq> {}" unfolding img_def by simp
      then obtain B where hB: "B \<in> img" "\<forall>t\<in>img. t \<le> B"
        using compact_attains_sup[OF himg_compact] by (by100 blast)
      have hB_nn: "B \<ge> 0" using hB(1) unfolding img_def by (by100 auto)
      define M where "M = sqrt B + 1"
      have hM_pos: "M > 0" unfolding M_def
      proof -
        have "sqrt B \<ge> 0" using hB_nn by simp
        thus "0 < sqrt B + 1" by (by100 linarith)
      qed
      have "\<forall>p \<in> (h \<circ> f) ` A. fst p ^ 2 + snd p ^ 2 \<le> M ^ 2"
      proof
        fix p assume hp: "p \<in> (h \<circ> f) ` A"
        have "fst p ^ 2 + snd p ^ 2 \<in> img" unfolding img_def using hp by (by100 blast)
        hence "fst p ^ 2 + snd p ^ 2 \<le> B" using hB(2) by (by100 blast)
        also have "B \<le> (sqrt B) ^ 2" using hB_nn by (by100 simp)
        also have "... \<le> M ^ 2" unfolding M_def
          using hB_nn by (simp add: power2_eq_square algebra_simps)
        finally show "fst p ^ 2 + snd p ^ 2 \<le> M ^ 2" .
      qed
      thus ?thesis using hM_pos that by blast
    qed
  qed
  \<comment> \<open>Step 4: a, b in same component of S^2-f(A) \<Rightarrow> h(a) in same component as \<infinity>
     (unbounded component) of R^2-(h\<circ>f)(A). Choose p far outside ball(0,M).\<close>
  define p :: "real \<times> real" where "p = (2*M + 1, 0)"
  have hp_far: "fst p ^ 2 + snd p ^ 2 > M ^ 2"
  proof -
    have "fst p = 2*M + 1" and "snd p = 0" unfolding p_def by auto
    hence "fst p ^ 2 + snd p ^ 2 = (2*M+1)^2"
      by (simp add: power2_eq_square)
    also have "... = 4*M^2 + 4*M + 1" by (simp add: power2_eq_square algebra_simps)
    also have "... > M^2"
    proof -
      have "3*M^2 \<ge> 0" using hM by simp
      moreover have "4*M > 0" using hM by simp
      ultimately show ?thesis by (by100 linarith)
    qed
    finally show ?thesis .
  qed
  have hp_not_in_gA: "p \<notin> (h \<circ> f) ` A"
  proof
    assume "p \<in> (h \<circ> f) ` A"
    hence "fst p ^ 2 + snd p ^ 2 \<le> M ^ 2" using hgA_bdd by (by100 blast)
    thus False using hp_far by (by100 linarith)
  qed
  \<comment> \<open>Step 5: h(a) and p are in the same component of R^2-(h\<circ>f)(A).
     (Both in unbounded component: h(a) because a,b same component maps to unbounded;
      p because |p| > M so p outside the bounded set g(A).)\<close>
  have hsame_comp_R2: "\<exists>C. C \<in> top1_components_on (UNIV - (h \<circ> f) ` A)
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - (h \<circ> f) ` A))
      \<and> ?ha \<in> C \<and> p \<in> C"
  proof -
    let ?gA = "(h \<circ> f) ` A"
    let ?S = "UNIV - ?gA :: (real \<times> real) set"
    let ?TR2 = "product_topology_on (top1_open_sets :: real set set) top1_open_sets"
    have hTR2eq: "?TR2 = (top1_open_sets :: (real \<times> real) set set)"
      using product_topology_on_open_sets_real2 by (by100 metis)
    \<comment> \<open>Step 1: Get C0 containing a,b. Show h(C0-{b}) connected in standard topology.\<close>
    obtain C0 where hC0: "C0 \<in> top1_components_on (top1_S2 - f ` A)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A))"
        and ha_C0: "a \<in> C0" and hb_C0: "b \<in> C0"
      using hsame by blast
    have hC0_sub: "C0 \<subseteq> top1_S2 - f ` A"
      using hC0 unfolding top1_components_on_def top1_component_of_on_def by (by100 blast)
    \<comment> \<open>Helper: h(U\{p}) connected when h injective continuous and h(U) open connected.\<close>
    have connected_minus_pt: "\<And>U p. continuous_on U h \<Longrightarrow> inj_on h U \<Longrightarrow> open (h ` U) \<Longrightarrow>
        connected (h ` U) \<Longrightarrow> p \<in> U \<Longrightarrow> connected (h ` (U - {p}))"
    proof -
      fix U :: "(real \<times> real \<times> real) set" and p
      assume hcont: "continuous_on U h" and hinj: "inj_on h U"
          and hopen: "open (h ` U)" and hconn: "connected (h ` U)" and hp: "p \<in> U"
      have "h ` (U - {p}) = h ` U - {h p}" using hinj hp unfolding inj_on_def by blast
      moreover have "connected (h ` U - {h p})" by (rule connected_open_delete_R2[OF hopen hconn])
      ultimately show "connected (h ` (U - {p}))" by simp
    qed
    \<comment> \<open>h(C0-{b}) connected: use connected_minus_pt.\<close>
    have himg_conn: "connected (h ` (C0 - {b}))"
    proof (cases "b \<in> C0")
      case False
      hence "C0 - {b} = C0" by (by100 blast)
      moreover have "connected C0"
      proof -
        have "top1_connected_on C0 (subspace_topology UNIV
            (top1_open_sets :: (real \<times> real \<times> real) set set) C0)"
        proof -
          have "subspace_topology top1_S2 top1_S2_topology C0 = subspace_topology UNIV
              (top1_open_sets :: (real \<times> real \<times> real) set set) C0"
          proof -
            have hC0_sub_S2: "C0 \<subseteq> top1_S2" using hC0_sub by (by100 blast)
            have "top1_S2_topology = subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) top1_S2"
              unfolding top1_S2_topology_def
              using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                    product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
            have "subspace_topology top1_S2 (subspace_topology UNIV
                (top1_open_sets :: (real \<times> real \<times> real) set set) top1_S2) C0
                = subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) C0"
              by (rule subspace_topology_trans[OF hC0_sub_S2])
            thus ?thesis
              using \<open>top1_S2_topology = subspace_topology UNIV
                  (top1_open_sets :: (real \<times> real \<times> real) set set) top1_S2\<close> by simp
          qed
          hence heq: "subspace_topology top1_S2 top1_S2_topology C0 = subspace_topology UNIV
              (top1_open_sets :: (real \<times> real \<times> real) set set) C0" .
          \<comment> \<open>hC0_conn_custom defined later; re-prove here.\<close>
          have "top1_connected_on C0 (subspace_topology top1_S2 top1_S2_topology C0)"
          proof -
            have hTS2_loc: "is_topology_on top1_S2 top1_S2_topology"
              using hT unfolding is_topology_on_strict_def by (by100 blast)
            have hTS2fA: "is_topology_on (top1_S2 - f ` A)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A))"
              by (rule subspace_topology_is_topology_on[OF hTS2_loc]) (by100 blast)
            have "top1_connected_on C0 (subspace_topology (top1_S2 - f ` A)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A)) C0)"
              by (rule Theorem_25_1(3)[OF hTS2fA hC0])
            thus ?thesis by (simp add: subspace_topology_trans[OF hC0_sub])
          qed
          thus ?thesis using heq by simp
        qed
        thus ?thesis using top1_connected_on_subspace_open_iff_connected by (by100 blast)
      qed
      moreover have "continuous_on C0 h"
      proof -
        \<comment> \<open>h continuous on S^2-{b} in custom framework. Bridge to standard.\<close>
        have hh_cont: "top1_continuous_map_on (top1_S2 - {b})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
            UNIV (product_topology_on top1_open_sets top1_open_sets) h"
          using hh unfolding top1_homeomorphism_on_def by (by100 blast)
        have hC0_sub_S2b: "C0 \<subseteq> top1_S2 - {b}" using hC0_sub False by (by100 blast)
        have hh_cont_C0: "top1_continuous_map_on C0
            (subspace_topology (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) C0)
            UNIV (product_topology_on top1_open_sets top1_open_sets) h"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hh_cont hC0_sub_S2b])
        have "subspace_topology (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) C0
            = subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) C0"
        proof -
          have "subspace_topology (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) C0
              = subspace_topology top1_S2 top1_S2_topology C0"
            by (rule subspace_topology_trans[OF hC0_sub_S2b])
          also have "... = subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) C0"
          proof -
            have "top1_S2_topology = subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) top1_S2"
              unfolding top1_S2_topology_def
              using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                    product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
            have "subspace_topology top1_S2 (subspace_topology UNIV
                (top1_open_sets :: (real \<times> real \<times> real) set set) top1_S2) C0
                = subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) C0"
            proof -
              have "C0 \<subseteq> top1_S2" using hC0_sub by (by100 blast)
              thus ?thesis by (rule subspace_topology_trans)
            qed
            thus ?thesis
              using \<open>top1_S2_topology = subspace_topology UNIV
                  (top1_open_sets :: (real \<times> real \<times> real) set set) top1_S2\<close> by simp
          qed
          finally show ?thesis .
        qed
        hence hh_cont_C0': "top1_continuous_map_on C0
            (subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) C0)
            UNIV (product_topology_on top1_open_sets top1_open_sets) h"
          using hh_cont_C0 by simp
        \<comment> \<open>Bridge: custom cont on C0 (subspace of R^3) to UNIV (R^2) \<Rightarrow> standard continuous_on.\<close>
        show ?thesis unfolding continuous_on_open_invariant
        proof (intro allI impI)
          fix V :: "(real \<times> real) set" assume hV_open: "open V"
          have "V \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
          proof -
            have "V \<in> (top1_open_sets :: (real \<times> real) set set)"
              using hV_open unfolding top1_open_sets_def by simp
            thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
          qed
          hence "{x \<in> C0. h x \<in> V} \<in> subspace_topology UNIV
              (top1_open_sets :: (real \<times> real \<times> real) set set) C0"
            using hh_cont_C0' unfolding top1_continuous_map_on_def by (by100 blast)
          then obtain W where "W \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
              and hW_eq: "{x \<in> C0. h x \<in> V} = C0 \<inter> W"
            unfolding subspace_topology_def by (by100 blast)
          have "open W" using \<open>W \<in> top1_open_sets\<close> unfolding top1_open_sets_def by simp
          moreover have "W \<inter> C0 = h -` V \<inter> C0" using hW_eq by (by100 blast)
          ultimately show "\<exists>T. open T \<and> T \<inter> C0 = h -` V \<inter> C0" by (by100 blast)
        qed
      qed
      ultimately show ?thesis
        using connected_continuous_image by simp
    next
      case True
      \<comment> \<open>b \<in> C0. h(C0-{b}) = R^2 \ h(S^2\C0). h(S^2\C0) compact. Complement connected.\<close>
      \<comment> \<open>h(C0-{b}) is open in R^2. Show connected via connected_open_delete_R2.\<close>
      \<comment> \<open>h restricted to S^2-{b} is homeomorphism. C0 open in S^2 and connected.
         h(C0-{b}) open in R^2 (homeomorphic image of open in S^2-{b}).
         C0 connected \<Rightarrow> h(C0-{b}) = h(C0 \<inter> (S^2-{b})). If C0 = S^2: h(C0-{b}) = R^2, connected. \<checkmark>
         If C0 \<subset> S^2: h(S^2-C0) nonempty. h(S^2-{b}) = R^2.
         h(C0-{b}) \<union> h(S^2-C0-{b}) = R^2 (disjoint union, both open? No, S^2-C0-{b} might not map to open set).

         Key: C0 is open connected subset of S^2 containing b. Under stereographic projection h: S^2-{b} \<rightarrow> R^2,
         h(C0-{b}) is the complement of a compact set K = h(S^2 \setminus C0) in R^2.

         Need: R^2 \setminus K connected for compact K. This follows from connected_open_delete_R2
         when K is a single point. For general compact K: standard fact.\<close>
      \<comment> \<open>h(C0-{b}) = R^2 \ K where K = h(S^2\C0) compact. Use complement_compact_connected_R2.\<close>
      have "h ` (C0 - {b}) = UNIV - h ` (top1_S2 - C0)"
      proof -
        have "bij_betw h (top1_S2 - {b}) UNIV"
          using hh unfolding top1_homeomorphism_on_def by (by100 blast)
        have hC0_sub_S2: "C0 \<subseteq> top1_S2" using hC0_sub by (by100 blast)
        have "C0 - {b} \<subseteq> top1_S2 - {b}" using hC0_sub_S2 by (by100 blast)
        have "top1_S2 - C0 \<subseteq> top1_S2 - {b}" using True by (by100 blast)
        have "(C0 - {b}) \<union> (top1_S2 - C0) = top1_S2 - {b}" using hC0_sub_S2 True by (by100 blast)
        have "(C0 - {b}) \<inter> (top1_S2 - C0) = {}" by (by100 blast)
        have hsurj: "h ` (top1_S2 - {b}) = UNIV"
          using \<open>bij_betw h (top1_S2 - {b}) UNIV\<close> unfolding bij_betw_def by (by100 blast)
        have hinj: "inj_on h (top1_S2 - {b})"
          using \<open>bij_betw h (top1_S2 - {b}) UNIV\<close> unfolding bij_betw_def by (by100 blast)
        have "h ` (top1_S2 - {b}) = h ` (C0 - {b}) \<union> h ` (top1_S2 - C0)"
          using image_Un[of h "C0 - {b}" "top1_S2 - C0"]
            \<open>(C0 - {b}) \<union> (top1_S2 - C0) = top1_S2 - {b}\<close> by simp
        moreover have "h ` (C0 - {b}) \<inter> h ` (top1_S2 - C0) = {}"
          using \<open>(C0 - {b}) \<inter> (top1_S2 - C0) = {}\<close>
            inj_on_image_Int[OF hinj \<open>C0 - {b} \<subseteq> top1_S2 - {b}\<close> \<open>top1_S2 - C0 \<subseteq> top1_S2 - {b}\<close>]
          by simp
        ultimately have "UNIV = h ` (C0 - {b}) \<union> h ` (top1_S2 - C0)" using hsurj by simp
        moreover have "h ` (C0 - {b}) \<inter> h ` (top1_S2 - C0) = {}" by fact
        ultimately show ?thesis by (by100 blast)
      qed
      have hK_compact: "compact (h ` (top1_S2 - C0))"
      proof -
        have "compact (top1_S2 - C0)"
        proof -
          \<comment> \<open>C0 open in S^2 subspace \<Rightarrow> \<exists>U open in R^3. C0 = S^2 \<inter> U.\<close>
          \<comment> \<open>S^2\C0 = S^2 \<inter> (R^3\U), intersection of two closed sets, closed.\<close>
          \<comment> \<open>Closed subset of compact S^2 \<Rightarrow> compact.\<close>
          have "closed top1_S2" by (rule compact_imp_closed[OF S2_compact_standard])
          have "closed (top1_S2 - C0)"
          proof -
            have hC0_open_S2: "C0 \<in> top1_S2_topology"
            proof -
              have hTS2: "is_topology_on top1_S2 top1_S2_topology"
                using hT unfolding is_topology_on_strict_def by (by100 blast)
              have hfA_sub_loc: "f ` A \<subseteq> top1_S2"
              proof fix x assume "x \<in> f ` A" then obtain y where "y \<in> A" "x = f y" by blast
                thus "x \<in> top1_S2" using hf unfolding top1_continuous_map_on_def by (by100 blast) qed
              have hfA_compact_loc: "top1_compact_on (f ` A) (subspace_topology top1_S2 top1_S2_topology (f ` A))"
              proof -
                have hTS2_: "is_topology_on top1_S2 top1_S2_topology"
                  using hT unfolding is_topology_on_strict_def by (by100 blast)
                have hf_S2: "top1_continuous_map_on A TA top1_S2 top1_S2_topology f"
                  unfolding top1_continuous_map_on_def proof (intro conjI ballI)
                  fix x assume "x \<in> A" thus "f x \<in> top1_S2" using hfA_sub_loc by (by100 blast) next
                  fix V assume hV: "V \<in> top1_S2_topology"
                  have "(top1_S2 - {a,b}) \<inter> V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a,b})"
                    by (rule subspace_topology_memI[OF hV])
                  hence "{x \<in> A. f x \<in> (top1_S2 - {a,b}) \<inter> V} \<in> TA"
                    using hf unfolding top1_continuous_map_on_def by (by100 blast)
                  moreover have "{x \<in> A. f x \<in> V} = {x \<in> A. f x \<in> (top1_S2 - {a,b}) \<inter> V}"
                    using hf unfolding top1_continuous_map_on_def by (by100 blast)
                  ultimately show "{x \<in> A. f x \<in> V} \<in> TA" by simp qed
                show ?thesis by (rule top1_compact_on_continuous_image[OF hcomp hTS2_ hf_S2])
              qed
              have hS2fA_open: "top1_S2 - f ` A \<in> top1_S2_topology"
              proof -
                have "closedin_on top1_S2 top1_S2_topology (f ` A)"
                  by (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff
                      top1_S2_is_topology_on_strict hfA_sub_loc hfA_compact_loc])
                thus ?thesis unfolding closedin_on_def using hTS2 unfolding is_topology_on_def by (by100 blast)
              qed
              have hTS2fA: "is_topology_on (top1_S2 - f ` A)
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A))"
                by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
              have hS2fA_lpc: "top1_locally_path_connected_on (top1_S2 - f ` A)
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A))"
                by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hS2fA_open]) simp
              obtain x where hx: "x \<in> top1_S2 - f ` A"
                  and hC0_eq: "C0 = top1_component_of_on (top1_S2 - f ` A)
                      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A)) x"
                using hC0 unfolding top1_components_on_def by (by100 blast)
              have "top1_path_component_of_on (top1_S2 - f ` A)
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A)) x
                = top1_component_of_on (top1_S2 - f ` A)
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A)) x"
                using Theorem_25_5[OF hTS2fA] hS2fA_lpc hx by (by100 blast)
              hence hC0_eq_pc: "C0 = top1_path_component_of_on (top1_S2 - f ` A)
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A)) x"
                using hC0_eq by simp
              have "top1_path_component_of_on (top1_S2 - f ` A)
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A)) x
                \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A)"
                by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTS2fA hS2fA_lpc hx])
              then obtain W where hW: "W \<in> top1_S2_topology" and hpc_eq: "C0 = (top1_S2 - f ` A) \<inter> W"
                using hC0_eq_pc unfolding subspace_topology_def by (by100 blast)
              thus ?thesis by (simp add: topology_inter_open[OF hTS2 hS2fA_open hW])
            qed
            have "top1_S2_topology = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
              unfolding top1_S2_topology_def
              using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                    product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
            then obtain W :: "(real\<times>real\<times>real) set" where hW: "W \<in> top1_open_sets" "C0 = top1_S2 \<inter> W"
              using hC0_open_S2 unfolding subspace_topology_def by blast
            have "open W" using hW(1) unfolding top1_open_sets_def by simp
            have "closed (- W)" using \<open>open W\<close> by (simp add: open_closed)
            hence "closed (UNIV - W)" by (simp add: Compl_eq_Diff_UNIV)
            have "top1_S2 - C0 = top1_S2 \<inter> (UNIV - W)" using hW(2) by blast
            thus ?thesis using \<open>closed top1_S2\<close> \<open>closed (UNIV - W)\<close>
              by (simp add: closed_Int)
          qed
          have "compact (top1_S2 \<inter> (top1_S2 - C0))"
            by (rule compact_Int_closed[OF S2_compact_standard \<open>closed (top1_S2 - C0)\<close>])
          moreover have "top1_S2 \<inter> (top1_S2 - C0) = top1_S2 - C0" by blast
          ultimately show ?thesis by simp
        qed
        have "continuous_on (top1_S2 - {b}) h"
        proof -
          have hh_cont_S2b: "top1_continuous_map_on (top1_S2 - {b})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
              UNIV (product_topology_on top1_open_sets top1_open_sets) h"
            using hh unfolding top1_homeomorphism_on_def by (by100 blast)
          \<comment> \<open>Bridge subspace to standard R^3 topology.\<close>
          have hS2b_sub: "top1_S2 - {b} \<subseteq> top1_S2" by blast
          have hR3eq: "product_topology_on (top1_open_sets :: real set set)
              (product_topology_on (top1_open_sets :: real set set) (top1_open_sets :: real set set))
              = (top1_open_sets :: (real \<times> real \<times> real) set set)"
            using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                  product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
          have "top1_S2_topology = subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) top1_S2"
            unfolding top1_S2_topology_def using hR3eq by simp
          have "subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})
              = subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) (top1_S2 - {b})"
          proof -
            have "subspace_topology top1_S2 (subspace_topology UNIV
                (top1_open_sets :: (real \<times> real \<times> real) set set) top1_S2) (top1_S2 - {b})
                = subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) (top1_S2 - {b})"
              by (rule subspace_topology_trans[OF hS2b_sub])
            thus ?thesis using \<open>top1_S2_topology = _\<close> by simp
          qed
          hence hh_R3: "top1_continuous_map_on (top1_S2 - {b})
              (subspace_topology UNIV (top1_open_sets :: (real \<times> real \<times> real) set set) (top1_S2 - {b}))
              UNIV (product_topology_on top1_open_sets top1_open_sets) h"
            using hh_cont_S2b by simp
          show ?thesis unfolding continuous_on_open_invariant
          proof (intro allI impI)
            fix V :: "(real \<times> real) set" assume hV_open: "open V"
            have "V \<in> (top1_open_sets :: (real \<times> real) set set)"
              using hV_open unfolding top1_open_sets_def by simp
            hence "V \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
              using product_topology_on_open_sets_real2 by (by100 metis)
            hence "{x \<in> top1_S2 - {b}. h x \<in> V} \<in> subspace_topology UNIV
                (top1_open_sets :: (real \<times> real \<times> real) set set) (top1_S2 - {b})"
              using hh_R3 unfolding top1_continuous_map_on_def by (by100 blast)
            then obtain W where "W \<in> (top1_open_sets :: (real \<times> real \<times> real) set set)"
                and "{x \<in> top1_S2 - {b}. h x \<in> V} = (top1_S2 - {b}) \<inter> W"
              unfolding subspace_topology_def by (by100 blast)
            have "open W" using \<open>W \<in> top1_open_sets\<close> unfolding top1_open_sets_def by simp
            moreover have "W \<inter> (top1_S2 - {b}) = h -` V \<inter> (top1_S2 - {b})"
              using \<open>{x \<in> top1_S2 - {b}. h x \<in> V} = (top1_S2 - {b}) \<inter> W\<close> by (by100 blast)
            ultimately show "\<exists>T. open T \<and> T \<inter> (top1_S2 - {b}) = h -` V \<inter> (top1_S2 - {b})" by (by100 blast)
          qed
        qed
        have "top1_S2 - C0 \<subseteq> top1_S2 - {b}" using True by (by100 blast)
        have "continuous_on (top1_S2 - C0) h"
          by (rule continuous_on_subset[OF \<open>continuous_on (top1_S2 - {b}) h\<close> \<open>top1_S2 - C0 \<subseteq> top1_S2 - {b}\<close>])
        show ?thesis
          by (rule compact_continuous_image[OF \<open>continuous_on (top1_S2 - C0) h\<close> \<open>compact (top1_S2 - C0)\<close>])
      qed
      \<comment> \<open>Use connected_open_delete_S2': C0 open connected in S^2, b \<in> C0,
         \<exists>c \<in> S^2\C0, h continuous on C0\{b} \<Rightarrow> h(C0\{b}) connected.\<close>
      have hC0_open_S2: "C0 \<in> top1_S2_topology"
      proof -
        have hTS2_l: "is_topology_on top1_S2 top1_S2_topology"
          using hT unfolding is_topology_on_strict_def by (by100 blast)
        have hfA_sub_l: "f ` A \<subseteq> top1_S2"
          using hf unfolding top1_continuous_map_on_def by (by100 blast)
        have hfA_compact_l: "top1_compact_on (f ` A) (subspace_topology top1_S2 top1_S2_topology (f ` A))"
        proof -
          have hf_S2_l: "top1_continuous_map_on A TA top1_S2 top1_S2_topology f"
            unfolding top1_continuous_map_on_def proof (intro conjI ballI)
            fix x assume "x \<in> A" thus "f x \<in> top1_S2" using hfA_sub_l by (by100 blast) next
            fix V assume hV: "V \<in> top1_S2_topology"
            have "(top1_S2 - {a,b}) \<inter> V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a,b})"
              by (rule subspace_topology_memI[OF hV])
            hence "{x \<in> A. f x \<in> (top1_S2 - {a,b}) \<inter> V} \<in> TA"
              using hf unfolding top1_continuous_map_on_def by (by100 blast)
            moreover have "{x \<in> A. f x \<in> V} = {x \<in> A. f x \<in> (top1_S2 - {a,b}) \<inter> V}"
              using hf unfolding top1_continuous_map_on_def by (by100 blast)
            ultimately show "{x \<in> A. f x \<in> V} \<in> TA" by simp qed
          show ?thesis by (rule top1_compact_on_continuous_image[OF hcomp hTS2_l hf_S2_l])
        qed
        have hS2fA_open_l: "top1_S2 - f ` A \<in> top1_S2_topology"
        proof -
          have "closedin_on top1_S2 top1_S2_topology (f ` A)"
            by (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff
                top1_S2_is_topology_on_strict hfA_sub_l hfA_compact_l])
          thus ?thesis unfolding closedin_on_def using hTS2_l unfolding is_topology_on_def by (by100 blast)
        qed
        have hTS2fA_l: "is_topology_on (top1_S2 - f ` A)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A))"
          by (rule subspace_topology_is_topology_on[OF hTS2_l]) (by100 blast)
        have hS2fA_lpc_l: "top1_locally_path_connected_on (top1_S2 - f ` A)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A))"
          by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hS2fA_open_l]) simp
        obtain x where hx: "x \<in> top1_S2 - f ` A"
            and hC0_eq: "C0 = top1_component_of_on (top1_S2 - f ` A)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A)) x"
          using hC0 unfolding top1_components_on_def by (by100 blast)
        have hC0_pc: "C0 = top1_path_component_of_on (top1_S2 - f ` A)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A)) x"
          using Theorem_25_5[OF hTS2fA_l] hS2fA_lpc_l hx hC0_eq by (by100 blast)
        have "top1_path_component_of_on (top1_S2 - f ` A)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A)) x
            \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A)"
          by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTS2fA_l hS2fA_lpc_l hx])
        then obtain W where hW: "W \<in> top1_S2_topology" and hpc_eq: "C0 = (top1_S2 - f ` A) \<inter> W"
          using hC0_pc unfolding subspace_topology_def by (by100 blast)
        show ?thesis using hpc_eq topology_inter_open[OF hTS2_l hS2fA_open_l hW] by simp
      qed
      have hC0_conn_custom: "top1_connected_on C0 (subspace_topology top1_S2 top1_S2_topology C0)"
      proof -
        have hTS2_loc: "is_topology_on top1_S2 top1_S2_topology"
          using hT unfolding is_topology_on_strict_def by (by100 blast)
        have hTS2fA: "is_topology_on (top1_S2 - f ` A)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A))"
          by (rule subspace_topology_is_topology_on[OF hTS2_loc]) (by100 blast)
        have "top1_connected_on C0 (subspace_topology (top1_S2 - f ` A)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A)) C0)"
          by (rule Theorem_25_1(3)[OF hTS2fA hC0])
        thus ?thesis by (simp add: subspace_topology_trans[OF hC0_sub])
      qed
      have hC0_sub_S2: "C0 \<subseteq> top1_S2" using hC0_sub by (by100 blast)
      have hh_cont_C0b: "continuous_on (C0 - {b}) h"
      proof -
        have hh_cont_std: "continuous_on (top1_S2 - {b}) h"
        proof -
          have hh_cont_cust: "top1_continuous_map_on (top1_S2 - {b})
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
              UNIV (product_topology_on top1_open_sets top1_open_sets) h"
            using hh unfolding top1_homeomorphism_on_def by (by100 blast)
          show ?thesis unfolding continuous_on_open_invariant
          proof (intro allI impI)
            fix V :: "(real \<times> real) set" assume "open V"
            have "V \<in> (top1_open_sets :: (real \<times> real) set set)"
              using \<open>open V\<close> unfolding top1_open_sets_def by simp
            hence "V \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
              using product_topology_on_open_sets_real2 by (by100 metis)
            hence "{x \<in> top1_S2 - {b}. h x \<in> V} \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
              using hh_cont_cust unfolding top1_continuous_map_on_def by (by100 blast)
            then obtain W where "W \<in> top1_S2_topology" "{x \<in> top1_S2 - {b}. h x \<in> V} = (top1_S2 - {b}) \<inter> W"
              unfolding subspace_topology_def by (by100 blast)
            have "top1_S2_topology = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
              unfolding top1_S2_topology_def
              using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                    product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
            then obtain W' where "W' \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)" "W = top1_S2 \<inter> W'"
              using \<open>W \<in> top1_S2_topology\<close> unfolding subspace_topology_def by (by100 blast)
            have "open W'" using \<open>W' \<in> top1_open_sets\<close> unfolding top1_open_sets_def by simp
            moreover have "W' \<inter> (top1_S2 - {b}) = h -` V \<inter> (top1_S2 - {b})"
            proof -
              have "(top1_S2 - {b}) \<inter> W = (top1_S2 - {b}) \<inter> (top1_S2 \<inter> W')"
                using \<open>W = top1_S2 \<inter> W'\<close> by simp
              hence "(top1_S2 - {b}) \<inter> W = (top1_S2 - {b}) \<inter> W'" by (by100 blast)
              hence "{x \<in> top1_S2 - {b}. h x \<in> V} = (top1_S2 - {b}) \<inter> W'"
                using \<open>{x \<in> top1_S2 - {b}. h x \<in> V} = (top1_S2 - {b}) \<inter> W\<close> by simp
              thus ?thesis by (by100 blast)
            qed
            ultimately show "\<exists>T. open T \<and> T \<inter> (top1_S2 - {b}) = h -` V \<inter> (top1_S2 - {b})" by (by100 blast)
          qed
        qed
        show ?thesis by (rule continuous_on_subset[OF hh_cont_std]) (use hC0_sub_S2 in blast)
      qed
      show ?thesis
      proof (cases "f ` A = {}")
        case True
        \<comment> \<open>f(A) = {} \<Rightarrow> C0 = S^2. h(C0\{b}) = h(S^2\{b}) = R^2 connected.\<close>
        have "h ` (top1_S2 - {b}) = UNIV"
          using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have "C0 = top1_S2"
        proof -
          have "top1_S2 - f ` A = top1_S2" using True by simp
          have hTS2_l: "is_topology_on top1_S2 top1_S2_topology"
            using hT unfolding is_topology_on_strict_def by (by100 blast)
          have hself: "\<forall>U \<in> top1_S2_topology. U \<subseteq> top1_S2"
            using top1_S2_is_topology_on_strict
            unfolding is_topology_on_strict_def is_topology_on_def by (by100 blast)
          have "subspace_topology top1_S2 top1_S2_topology top1_S2 = top1_S2_topology"
            by (rule subspace_topology_self_carrier[OF hself])
          have hC0_comp: "C0 \<in> top1_components_on top1_S2 top1_S2_topology"
            using hC0 \<open>top1_S2 - f ` A = top1_S2\<close> \<open>subspace_topology top1_S2 top1_S2_topology top1_S2 = top1_S2_topology\<close>
            by simp
          have hS2_ne: "top1_S2 \<noteq> {}" using ha by (by100 blast)
          have hS2_conn_sub: "top1_connected_on top1_S2 (subspace_topology top1_S2 top1_S2_topology top1_S2)"
            using S2_connected \<open>subspace_topology top1_S2 top1_S2_topology top1_S2 = top1_S2_topology\<close> by simp
          have "\<exists>C'\<in>top1_components_on top1_S2 top1_S2_topology. top1_S2 \<subseteq> C'"
          proof -
            have "\<exists>C'\<in>top1_components_on top1_S2 top1_S2_topology. top1_S2 \<subseteq> C'"
            proof -
              have hTS2_sub: "is_topology_on top1_S2 top1_S2_topology" by (rule hTS2_l)
              show ?thesis using Theorem_25_1(4)[OF hTS2_sub _ hS2_conn_sub hS2_ne] by simp
            qed
            thus ?thesis by simp
          qed
          then obtain C' where hC': "C' \<in> top1_components_on top1_S2 top1_S2_topology" "top1_S2 \<subseteq> C'"
            by blast
          have "C' = C0"
            by (rule Theorem_25_1(2)[OF hTS2_l hC'(1) hC0_comp])
               (use ha_C0 hC'(2) ha in blast)
          have "C0 \<subseteq> top1_S2" using hC0_sub by (by100 blast)
          thus ?thesis using hC'(2) \<open>C' = C0\<close> by (by100 blast)
        qed
        hence "C0 - {b} = top1_S2 - {b}" by simp
        hence "h ` (C0 - {b}) = UNIV" using \<open>h ` (top1_S2 - {b}) = UNIV\<close> by simp
        thus ?thesis using connected_Times[OF connected_UNIV connected_UNIV]
          by (simp add: UNIV_Times_UNIV)
      next
        case False
        then obtain c where hc: "c \<in> f ` A" by (by100 blast)
        have "c \<in> top1_S2" using hf hc unfolding top1_continuous_map_on_def by (by100 blast)
        have "c \<notin> C0" using hc hC0_sub by (by100 blast)
        show ?thesis
          by (rule connected_open_delete_S2'[OF hC0_open_S2 hC0_conn_custom True
              \<open>c \<in> top1_S2\<close> \<open>c \<notin> C0\<close> hh_cont_C0b])
             simp
      qed
    qed
    \<comment> \<open>Step 2: h(C0-{b}) \<subseteq> R^2-gA, unbounded, contains h(a).\<close>
    have himg_sub: "h ` (C0 - {b}) \<subseteq> ?S"
    proof
      fix y assume "y \<in> h ` (C0 - {b})"
      then obtain x where hx: "x \<in> C0 - {b}" and hyx: "y = h x" by blast
      have "x \<notin> f ` A" using hx hC0_sub by (by100 blast)
      have "x \<in> top1_S2 - {b}" using hx hC0_sub by (by100 blast)
      have "h x \<notin> ?gA"
      proof
        assume "h x \<in> ?gA"
        then obtain z where "z \<in> A" "h (f z) = h x" by auto
        have "f z \<in> top1_S2 - {a,b}" using hf \<open>z \<in> A\<close> unfolding top1_continuous_map_on_def by (by100 blast)
        hence "f z \<in> top1_S2 - {b}" by (by100 blast)
        have hinj_loc: "inj_on h (top1_S2 - {b})"
          using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have "f z = x"
          by (rule inj_onD[OF hinj_loc \<open>h (f z) = h x\<close> \<open>f z \<in> top1_S2 - {b}\<close> \<open>x \<in> top1_S2 - {b}\<close>])
        thus False using \<open>x \<notin> f ` A\<close> \<open>z \<in> A\<close> by (by100 blast)
      qed
      thus "y \<in> ?S" using hyx by simp
    qed
    have hha_img: "?ha \<in> h ` (C0 - {b})" using ha_C0 hab by (by100 blast)
    \<comment> \<open>h(C0-{b}) unbounded.\<close>
    have hfA_sub: "f ` A \<subseteq> top1_S2"
    proof
      fix x assume "x \<in> f ` A"
      then obtain y where "y \<in> A" "x = f y" by blast
      thus "x \<in> top1_S2" using hf unfolding top1_continuous_map_on_def by (by100 blast)
    qed
    have hfA_compact: "top1_compact_on (f ` A) (subspace_topology top1_S2 top1_S2_topology (f ` A))"
    proof -
      have hTS2: "is_topology_on top1_S2 top1_S2_topology"
        using hT unfolding is_topology_on_strict_def by (by100 blast)
      have hf_S2: "top1_continuous_map_on A TA top1_S2 top1_S2_topology f"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x assume "x \<in> A" thus "f x \<in> top1_S2" using hfA_sub by (by100 blast)
      next
        fix V assume hV: "V \<in> top1_S2_topology"
        have "(top1_S2 - {a,b}) \<inter> V \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a,b})"
          by (rule subspace_topology_memI[OF hV])
        hence "{x \<in> A. f x \<in> (top1_S2 - {a,b}) \<inter> V} \<in> TA"
          using hf unfolding top1_continuous_map_on_def by (by100 blast)
        moreover have "{x \<in> A. f x \<in> V} = {x \<in> A. f x \<in> (top1_S2 - {a,b}) \<inter> V}"
          using hf unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "{x \<in> A. f x \<in> V} \<in> TA" by simp
      qed
      show ?thesis by (rule top1_compact_on_continuous_image[OF hcomp hTS2 hf_S2])
    qed
    have hb_S2fA: "b \<in> top1_S2 - f ` A"
    proof
      show "b \<in> top1_S2" by (rule hb)
      show "b \<notin> f ` A"
      proof
        assume "b \<in> f ` A"
        then obtain y where "y \<in> A" "f y = b" by blast
        hence "f y \<in> top1_S2 - {a, b}" using hf unfolding top1_continuous_map_on_def by (by100 blast)
        thus False using \<open>f y = b\<close> by simp
      qed
    qed
    have hC0_conn_custom: "top1_connected_on C0 (subspace_topology top1_S2 top1_S2_topology C0)"
    proof -
      have hTS2_: "is_topology_on top1_S2 top1_S2_topology"
        using hT unfolding is_topology_on_strict_def by (by100 blast)
      have hTS2fA: "is_topology_on (top1_S2 - f ` A)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A))"
        by (rule subspace_topology_is_topology_on[OF hTS2_]) (by100 blast)
      have "top1_connected_on C0 (subspace_topology (top1_S2 - f ` A)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - f ` A)) C0)"
        by (rule Theorem_25_1(3)[OF hTS2fA hC0])
      thus ?thesis by (simp add: subspace_topology_trans[OF hC0_sub])
    qed
    have himg_unbdd: "\<forall>N. \<exists>q \<in> h ` (C0 - {b}). fst q ^ 2 + snd q ^ 2 > N"
      using Lemma_61_1_components_correspond[OF hT hfA_sub hfA_compact hb_S2fA hh
          hC0_conn_custom hC0_sub hC0] hb_C0 by (by100 blast)
    \<comment> \<open>Step 3: Exterior connected and in ?S.\<close>
    define ext where "ext = {x :: real \<times> real. fst x ^ 2 + snd x ^ 2 > M ^ 2}"
    have hext_conn: "connected ext" unfolding ext_def by (rule exterior_ball_connected_R2)
    have hext_sub: "ext \<subseteq> ?S"
    proof
      fix x assume "x \<in> ext"
      hence "fst x ^ 2 + snd x ^ 2 > M ^ 2" unfolding ext_def by simp
      hence "x \<notin> ?gA" using hgA_bdd by (by100 force)
      thus "x \<in> ?S" by simp
    qed
    have hp_ext: "p \<in> ext" unfolding ext_def using hp_far by simp
    \<comment> \<open>h(C0-{b}) intersects ext (unbounded image has points outside B(0,M)).\<close>
    have himg_ext_ne: "h ` (C0 - {b}) \<inter> ext \<noteq> {}"
    proof -
      obtain q where "q \<in> h ` (C0 - {b})" "fst q ^ 2 + snd q ^ 2 > M ^ 2"
        using himg_unbdd[THEN spec[of _ "M ^ 2"]] by (by100 blast)
      hence "q \<in> ext" unfolding ext_def by simp
      thus ?thesis using \<open>q \<in> h ` (C0 - {b})\<close> by (by100 blast)
    qed
    \<comment> \<open>Union connected (Theorem_23_3 analog for standard topology).\<close>
    have hunion_conn: "connected (h ` (C0 - {b}) \<union> ext)"
    proof (rule connectedI)
      fix T1 T2 :: "(real \<times> real) set"
      assume hT1: "open T1" and hT2: "open T2" and hcov: "h ` (C0 - {b}) \<union> ext \<subseteq> T1 \<union> T2"
          and hdisj: "T1 \<inter> T2 \<inter> (h ` (C0 - {b}) \<union> ext) = {}"
          and hne1: "T1 \<inter> (h ` (C0 - {b}) \<union> ext) \<noteq> {}" and hne2: "T2 \<inter> (h ` (C0 - {b}) \<union> ext) \<noteq> {}"
      \<comment> \<open>From connected components: h(C0-{b}) and ext each lie in T1 or T2.\<close>
      have himg_sub_T: "h ` (C0 - {b}) \<subseteq> T1 \<union> T2" using hcov by (by100 blast)
      have himg_disj: "T1 \<inter> T2 \<inter> h ` (C0 - {b}) = {}" using hdisj by (by100 blast)
      have "T1 \<inter> h ` (C0 - {b}) = {} \<or> T2 \<inter> h ` (C0 - {b}) = {}"
        by (rule connectedD[OF himg_conn hT1 hT2 himg_disj himg_sub_T])
      hence himg_T: "h ` (C0 - {b}) \<subseteq> T1 \<or> h ` (C0 - {b}) \<subseteq> T2"
        using himg_sub_T by (by100 blast)
      have hext_sub_T: "ext \<subseteq> T1 \<union> T2" using hcov by (by100 blast)
      have hext_disj: "T1 \<inter> T2 \<inter> ext = {}" using hdisj by (by100 blast)
      have "T1 \<inter> ext = {} \<or> T2 \<inter> ext = {}"
        by (rule connectedD[OF hext_conn hT1 hT2 hext_disj hext_sub_T])
      hence hext_T: "ext \<subseteq> T1 \<or> ext \<subseteq> T2"
        using hext_sub_T by (by100 blast)
      \<comment> \<open>Since they share a point (himg_ext_ne), they must be in the same Ti.\<close>
      obtain z where hz: "z \<in> h ` (C0 - {b})" "z \<in> ext" using himg_ext_ne by (by100 blast)
      show False
      proof (cases "h ` (C0 - {b}) \<subseteq> T1")
        case True
        hence "z \<in> T1" using hz(1) by (by100 blast)
        hence "ext \<subseteq> T1" using hext_T hdisj hz(2) by (by100 blast)
        hence "h ` (C0 - {b}) \<union> ext \<subseteq> T1" using True by (by100 blast)
        thus False using hne2 hdisj by (by100 blast)
      next
        case False
        hence "h ` (C0 - {b}) \<subseteq> T2" using himg_T by simp
        hence "z \<in> T2" using hz(1) by (by100 blast)
        hence "ext \<subseteq> T2" using hext_T hdisj hz(2) by (by100 blast)
        hence "h ` (C0 - {b}) \<union> ext \<subseteq> T2" using \<open>h ` (C0 - {b}) \<subseteq> T2\<close> by (by100 blast)
        thus False using hne1 hdisj by (by100 blast)
      qed
    qed
    \<comment> \<open>Union contains ha and p, is connected, and \<subseteq> ?S.\<close>
    have hunion_sub: "h ` (C0 - {b}) \<union> ext \<subseteq> ?S" using himg_sub hext_sub by (by100 blast)
    have hha_union: "?ha \<in> h ` (C0 - {b}) \<union> ext" using hha_img by (by100 blast)
    have hp_union: "p \<in> h ` (C0 - {b}) \<union> ext" using hp_ext by (by100 blast)
    have hunion_ne: "h ` (C0 - {b}) \<union> ext \<noteq> {}" using hha_union by (by100 blast)
    \<comment> \<open>Bridge to custom topology: connected in standard \<Rightarrow> connected in custom.\<close>
    have hunion_custom_conn: "top1_connected_on (h ` (C0 - {b}) \<union> ext)
        (subspace_topology UNIV ?TR2 (h ` (C0 - {b}) \<union> ext))"
    proof -
      have "top1_connected_on (h ` (C0 - {b}) \<union> ext)
          (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) (h ` (C0 - {b}) \<union> ext))"
        using top1_connected_on_subspace_open_iff_connected hunion_conn by (by100 blast)
      thus ?thesis using hTR2eq by simp
    qed
    \<comment> \<open>Subspace transition: from UNIV to ?S.\<close>
    have hunion_custom_conn2: "top1_connected_on (h ` (C0 - {b}) \<union> ext)
        (subspace_topology ?S (subspace_topology UNIV ?TR2 ?S) (h ` (C0 - {b}) \<union> ext))"
    proof -
      have "subspace_topology ?S (subspace_topology UNIV ?TR2 ?S) (h ` (C0 - {b}) \<union> ext)
          = subspace_topology UNIV ?TR2 (h ` (C0 - {b}) \<union> ext)"
        by (rule subspace_topology_trans[OF hunion_sub])
      thus ?thesis using hunion_custom_conn by simp
    qed
    \<comment> \<open>By Theorem_25_1(4): connected subset contained in a component.\<close>
    have hTS: "is_topology_on ?S (subspace_topology UNIV ?TR2 ?S)"
    proof -
      have "is_topology_on (UNIV :: (real\<times>real) set) ?TR2"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
            top1_open_sets_is_topology_on_UNIV] by simp
      thus ?thesis by (rule subspace_topology_is_topology_on) simp
    qed
    obtain D where hD: "D \<in> top1_components_on ?S (subspace_topology UNIV ?TR2 ?S)"
        and hunion_D: "h ` (C0 - {b}) \<union> ext \<subseteq> D"
      using Theorem_25_1(4)[OF hTS hunion_sub hunion_custom_conn2 hunion_ne] by blast
    have "?ha \<in> D" using hha_union hunion_D by (by100 blast)
    moreover have "p \<in> D" using hp_union hunion_D by (by100 blast)
    ultimately show ?thesis using hD by (by100 blast)
  qed
  \<comment> \<open>Step 6: h(a) and p in same component \<Rightarrow> path \<alpha> from h(a) to p in R^2-g(A).\<close>
  have hinj': "inj_on h (top1_S2 - {b})"
    using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
  have ha_S2b': "a \<in> top1_S2 - {b}" using ha hab by (by100 blast)
  have hha_not_gA: "?ha \<notin> (h \<circ> f) ` A"
  proof
    assume "?ha \<in> (h \<circ> f) ` A"
    then obtain x where hx: "x \<in> A" and hhx: "h (f x) = ?ha" by auto
    have hfx: "f x \<in> top1_S2 - {a,b}" using hf hx unfolding top1_continuous_map_on_def by (by100 blast)
    hence "f x \<in> top1_S2 - {b}" by (by100 blast)
    hence "f x = a" using hinj' ha_S2b' hhx unfolding inj_on_def by (by100 blast)
    hence "f x \<in> {a,b}" by simp
    thus False using hfx by (by100 blast)
  qed
  have hha_in_comp: "?ha \<in> UNIV - (h \<circ> f) ` A" using hha_not_gA by simp
  have hp_in_comp: "p \<in> UNIV - (h \<circ> f) ` A" using hp_not_in_gA by simp
  \<comment> \<open>Step 6a: The map g(\<cdot>)-p is nulhomotopic in R^2-{0}.
     Straight-line: H(x,t) = (1-t)\<cdot>g(x) - p. At t=0: g(x)-p. At t=1: -p.
     Since |g(x)| \<le> M and |p| > M, g(x)-p \<noteq> 0 and (1-t)\<cdot>g(x)-p \<noteq> 0 for t \<in> [0,1].\<close>
  \<comment> \<open>Step 6a-6c: Combined nulhomotopy argument.
     g(\<cdot>)-p nulhomotopic in R^2-{0} by straight-line.
     g(\<cdot>)-h(a) homotopic to g(\<cdot>)-p via path \<alpha> in R^2-g(A).
     Translation gives g nulhomotopic in R^2-{h(a)}.\<close>
  \<comment> \<open>Step 6a: g(\<cdot>)-p nulhomotopic in R^2-{0}. Straight-line (1-t)\<cdot>g(x)-p \<rightarrow> -p.
     Works because |(1-t)\<cdot>g(x)| \<le> M < 2M+1 = |p|, so (1-t)\<cdot>g(x) \<noteq> p.\<close>
  \<comment> \<open>Step 6b: path \<alpha> from h(a) to p in R^2-g(A). g(x)-\<alpha>(t) \<noteq> 0 since \<alpha>(t) \<notin> g(A).
     Homotopy F(x,t) = g(x)-\<alpha>(t) shows g(\<cdot>)-h(a) homotopic to g(\<cdot>)-p in R^2-{0}.
     Combined: g(\<cdot>)-h(a) nulhomotopic in R^2-{0}.\<close>
  \<comment> \<open>Step 6c: Translation by h(a): g nulhomotopic in R^2-{h(a)}.\<close>
  \<comment> \<open>Following textbook Lemma 61.2 proof exactly:
     Step 6a: Choose path \<alpha> from h(a) to p in R^2-g(A) (both in same component).
     Step 6b: G(x,t) = g(x) - \<alpha>(t) homotopy g to g(\<cdot>)-p in R^2-{0}.
     Step 6c: H(x,t) = t\<cdot>g(x) - p homotopy g(\<cdot>)-p to -p in R^2-{0}.
     Step 6d: Compose: g nulhomotopic in R^2-{0}.
     Step 6e: Translate: g nulhomotopic in R^2-{h(a)}.
     Component-wise: define sub(a,b) = (fst a - fst b, snd a - snd b),
                            scl(t,a) = (t * fst a, t * snd a).\<close>
  \<comment> \<open>Using global pair_sub and pair_scl for R^2 arithmetic.\<close>
  \<comment> \<open>Step 6a: path \<alpha> from h(a) to p in R^2-g(A).\<close>
  obtain \<alpha>R where h\<alpha>R: "top1_is_path_on (UNIV - (h \<circ> f) ` A)
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - (h \<circ> f) ` A))
      ?ha p \<alpha>R"
  proof -
    \<comment> \<open>R^2-g(A) is open (g(A) compact hence closed). Open in R^2 \<Rightarrow> lpc.
       Same component + lpc \<Rightarrow> path-connected component \<Rightarrow> path exists.\<close>
    have hgA_closed: "closedin_on (UNIV::(real\<times>real) set)
        (product_topology_on top1_open_sets top1_open_sets) ((h \<circ> f) ` A)"
    proof -
      have "closed ((h \<circ> f) ` A)" by (rule compact_imp_closed[OF hgA_compact])
      hence "open (- (h \<circ> f) ` A)" by (rule open_Compl)
      hence "open (UNIV - (h \<circ> f) ` A)" by (simp add: Compl_eq_Diff_UNIV)
      hence "(UNIV - (h \<circ> f) ` A) \<in> top1_open_sets" unfolding top1_open_sets_def by simp
      hence "(UNIV - (h \<circ> f) ` A) \<in> product_topology_on top1_open_sets top1_open_sets"
        using product_topology_on_open_sets_real2 by (by100 metis)
      thus ?thesis unfolding closedin_on_def by simp
    qed
    have hR2gA_open: "(UNIV - (h \<circ> f) ` A) \<in> product_topology_on top1_open_sets top1_open_sets"
      using hgA_closed unfolding closedin_on_def by (by100 blast)
    have hR2gA_lpc: "top1_locally_path_connected_on (UNIV - (h \<circ> f) ` A)
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - (h \<circ> f) ` A))"
      by (rule open_subset_locally_path_connected[OF R2_locally_path_connected hR2gA_open]) simp
    \<comment> \<open>In lpc space, components = path components. h(a) and p in same component \<Rightarrow> path exists.\<close>
    \<comment> \<open>Extract component CC, show it's path-connected (lpc + connected).\<close>
    obtain CC where hCC: "CC \<in> top1_components_on (UNIV - (h \<circ> f) ` A)
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - (h \<circ> f) ` A))"
        and hha_CC: "?ha \<in> CC" and hp_CC: "p \<in> CC"
      using hsame_comp_R2 by blast
    have hTR2gA: "is_topology_on (UNIV - (h \<circ> f) ` A)
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - (h \<circ> f) ` A))"
      using hR2gA_lpc unfolding top1_locally_path_connected_on_def by (by100 blast)
    \<comment> \<open>CC = component_of(ha) (CC is a component and ha \<in> CC).\<close>
    have hha_comp: "?ha \<in> UNIV - (h \<circ> f) ` A" using hha_in_comp by simp
    have hCC_eq_comp: "CC = top1_component_of_on (UNIV - (h \<circ> f) ` A)
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
          (UNIV - (h \<circ> f) ` A)) ?ha"
    proof -
      have "CC \<in> {top1_component_of_on (UNIV - (h \<circ> f) ` A)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - (h \<circ> f) ` A)) x | x. x \<in> UNIV - (h \<circ> f) ` A}"
        using hCC unfolding top1_components_on_def by simp
      then obtain x where hx: "x \<in> UNIV - (h \<circ> f) ` A"
          and hCC_x: "CC = top1_component_of_on (UNIV - (h \<circ> f) ` A)
              (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
                (UNIV - (h \<circ> f) ` A)) x" by blast
      have "?ha \<in> CC" by (rule hha_CC)
      hence "?ha \<in> top1_component_of_on (UNIV - (h \<circ> f) ` A)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - (h \<circ> f) ` A)) x" using hCC_x by simp
      \<comment> \<open>CC = component_of(x) and ha \<in> CC, so CC = component_of(ha) by as_component.\<close>
      have "CC \<in> top1_components_on (UNIV - (h \<circ> f) ` A)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - (h \<circ> f) ` A))" by (rule hCC)
      hence "CC = top1_component_of_on (UNIV - (h \<circ> f) ` A)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - (h \<circ> f) ` A)) ?ha"
        by (rule top1_component_of_on_as_component[OF hTR2gA _ hha_CC])
      thus ?thesis using hCC_x by simp
    qed
    have hCC_conn: "top1_connected_on CC
        (subspace_topology (UNIV - (h \<circ> f) ` A)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - (h \<circ> f) ` A)) CC)"
    proof -
      have hCC_eq: "CC = top1_component_of_on (UNIV - (h \<circ> f) ` A)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - (h \<circ> f) ` A)) ?ha" by (rule hCC_eq_comp)
      show ?thesis unfolding hCC_eq
        by (rule top1_component_of_on_connected[OF hTR2gA \<open>?ha \<in> UNIV - (h \<circ> f) ` A\<close>])
    qed
    have hCC_sub: "CC \<subseteq> UNIV - (h \<circ> f) ` A"
      using hCC unfolding top1_components_on_def top1_component_of_on_def by (by100 blast)
    have hCC_ne: "CC \<noteq> {}" using hha_CC by (by100 blast)
    \<comment> \<open>CC is open (component of lpc space).\<close>
    have hCC_open: "CC \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
        (UNIV - (h \<circ> f) ` A)"
    proof -
      have "?ha \<in> UNIV - (h \<circ> f) ` A" using hha_CC hCC_sub by (by100 blast)
      have "top1_path_component_of_on (UNIV - (h \<circ> f) ` A)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - (h \<circ> f) ` A))
          ?ha \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - (h \<circ> f) ` A)"
        by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTR2gA hR2gA_lpc
              \<open>?ha \<in> UNIV - (h \<circ> f) ` A\<close>])
      moreover have "top1_path_component_of_on (UNIV - (h \<circ> f) ` A)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - (h \<circ> f) ` A))
          ?ha = CC"
      proof -
        have "top1_path_component_of_on (UNIV - (h \<circ> f) ` A)
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - (h \<circ> f) ` A))
            ?ha = top1_component_of_on (UNIV - (h \<circ> f) ` A)
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - (h \<circ> f) ` A))
            ?ha"
          using Theorem_25_5[OF hTR2gA] hR2gA_lpc hha_comp by (by100 blast)
        thus ?thesis using hCC_eq_comp by simp
      qed
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>CC lpc (open subset of lpc space) + connected \<Rightarrow> path-connected.\<close>
    have hCC_lpc: "top1_locally_path_connected_on CC
        (subspace_topology (UNIV - (h \<circ> f) ` A)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - (h \<circ> f) ` A)) CC)"
      by (rule open_subset_locally_path_connected[OF hR2gA_lpc hCC_open hCC_sub])
    have hCC_pc: "top1_path_connected_on CC
        (subspace_topology (UNIV - (h \<circ> f) ` A)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - (h \<circ> f) ` A)) CC)"
    proof -
      have hTCC: "is_topology_on CC (subspace_topology (UNIV - (h \<circ> f) ` A)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - (h \<circ> f) ` A)) CC)"
        using hCC_conn unfolding top1_connected_on_def by (by100 blast)
      show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF
            hTCC hCC_conn hCC_lpc hCC_ne])
    qed
    \<comment> \<open>Path from ha to p in CC.\<close>
    obtain \<alpha>0 where h\<alpha>0: "top1_is_path_on CC
        (subspace_topology (UNIV - (h \<circ> f) ` A)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - (h \<circ> f) ` A)) CC) ?ha p \<alpha>0"
      using hCC_pc hha_CC hp_CC unfolding top1_path_connected_on_def by (by100 blast)
    \<comment> \<open>Path in CC is a path in R^2-g(A) (subspace inclusion).\<close>
    have "top1_is_path_on (UNIV - (h \<circ> f) ` A)
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - (h \<circ> f) ` A))
        ?ha p \<alpha>0"
      by (rule path_in_subspace_is_path_in_ambient[OF hTR2gA hCC_sub h\<alpha>0])
    thus ?thesis using that by blast
  qed
  \<comment> \<open>Step 6b: G(x,t) = g(x) - \<alpha>(t). Homotopy g(\<cdot>)-h(a) to g(\<cdot>)-p in R^2-{0}.\<close>
  \<comment> \<open>Step 6c: H(x,t) = t\<cdot>g(x) - p. Homotopy g(\<cdot>)-p to -p in R^2-{0}.\<close>
  \<comment> \<open>Step 6d+6e: Compose and translate.\<close>
  \<comment> \<open>Textbook Lemma 61.2 proof: two homotopies.
     G(x,t) = g(x) - \<alpha>(t): homotopy from g(\<cdot>)-ha to g(\<cdot>)-p in R^2-{0}.
     H(x,t) = t\<cdot>g(x) - p: homotopy from g(\<cdot>)-p to -p in R^2-{0}.
     Compose: g(\<cdot>)-ha nulhomotopic in R^2-{0}. Translate: g nulhomotopic in R^2-{ha}.\<close>
  \<comment> \<open>Helper: pair_sub(g(\<cdot>), p) and pair_sub(g(\<cdot>), ha) continuous from A to R^2-{0}.\<close>
  let ?Y0 = "UNIV - {(0::real,0::real)}"
  let ?TY0 = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?Y0"
  have hgsub_p_cont: "top1_continuous_map_on A TA ?Y0 ?TY0 (\<lambda>x. pair_sub ((h \<circ> f) x) p)"
  proof -
    let ?T = "\<lambda>x :: real \<times> real. (fst x - fst p, snd x - snd p)"
    have hT_homeo: "top1_homeomorphism_on (UNIV - {p})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {p}))
        ?Y0 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?Y0) ?T"
      by (rule translation_homeo_R2[of p])
    have hgf_p: "top1_continuous_map_on A TA (UNIV - {p})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {p})) (h \<circ> f)"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume "x \<in> A"
      have "(h \<circ> f) x \<noteq> p" using hp_not_in_gA \<open>x \<in> A\<close> by (by100 blast)
      thus "(h \<circ> f) x \<in> UNIV - {p}" by simp
    next
      fix V assume hV: "V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {p})"
      obtain W where hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
          and hV_eq: "V = (UNIV - {p}) \<inter> W" using hV unfolding subspace_topology_def by (by100 blast)
      have "(UNIV - {?ha}) \<inter> W \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {?ha})"
        by (rule subspace_topology_memI[OF hW])
      hence "{x \<in> A. (h \<circ> f) x \<in> (UNIV - {?ha}) \<inter> W} \<in> TA"
        using hg_cont unfolding top1_continuous_map_on_def by (by100 blast)
      moreover have "{x \<in> A. (h \<circ> f) x \<in> V} = {x \<in> A. (h \<circ> f) x \<in> (UNIV - {?ha}) \<inter> W}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> A. (h \<circ> f) x \<in> V}"
        hence "x \<in> A" "(h \<circ> f) x \<in> W" using hV_eq by auto
        moreover have "(h \<circ> f) x \<in> UNIV - {?ha}"
          using hg_cont \<open>x \<in> A\<close> unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "x \<in> {x \<in> A. (h \<circ> f) x \<in> (UNIV - {?ha}) \<inter> W}" by (by100 blast)
      next
        fix x assume "x \<in> {x \<in> A. (h \<circ> f) x \<in> (UNIV - {?ha}) \<inter> W}"
        hence "x \<in> A" "(h \<circ> f) x \<in> W" by auto
        have "(h \<circ> f) x \<noteq> p" using hp_not_in_gA \<open>x \<in> A\<close> by (by100 blast)
        thus "x \<in> {x \<in> A. (h \<circ> f) x \<in> V}" using \<open>x \<in> A\<close> \<open>(h \<circ> f) x \<in> W\<close> hV_eq by (by100 blast)
      qed
      ultimately show "{x \<in> A. (h \<circ> f) x \<in> V} \<in> TA" by simp
    qed
    have hT_cont: "top1_continuous_map_on (UNIV - {p})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {p}))
        ?Y0 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?Y0) ?T"
      using hT_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    have "top1_continuous_map_on A TA ?Y0 ?TY0 (?T \<circ> (h \<circ> f))"
      by (rule top1_continuous_map_on_comp[OF hgf_p hT_cont])
    moreover have "?T \<circ> (h \<circ> f) = (\<lambda>x. pair_sub ((h \<circ> f) x) p)"
      unfolding pair_sub_def comp_def by (rule ext) simp
    ultimately show ?thesis by simp
  qed
  have hgsub_ha_cont: "top1_continuous_map_on A TA ?Y0 ?TY0 (\<lambda>x. pair_sub ((h \<circ> f) x) ?ha)"
  proof -
    let ?T = "\<lambda>x :: real \<times> real. (fst x - fst ?ha, snd x - snd ?ha)"
    have hT_homeo: "top1_homeomorphism_on (UNIV - {?ha})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {?ha}))
        ?Y0 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?Y0) ?T"
      by (rule translation_homeo_R2[of ?ha])
    have hT_cont: "top1_continuous_map_on (UNIV - {?ha})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {?ha}))
        ?Y0 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?Y0) ?T"
      using hT_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
    have "top1_continuous_map_on A TA ?Y0 ?TY0 (?T \<circ> (h \<circ> f))"
      by (rule top1_continuous_map_on_comp[OF hg_cont hT_cont])
    moreover have "?T \<circ> (h \<circ> f) = (\<lambda>x. pair_sub ((h \<circ> f) x) ?ha)"
      unfolding pair_sub_def comp_def by (rule ext) simp
    ultimately show ?thesis by simp
  qed
  have hg_UNIV_fact: "top1_continuous_map_on A TA (UNIV :: (real\<times>real) set)
      (product_topology_on top1_open_sets top1_open_sets) (h \<circ> f)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix x assume "x \<in> A" thus "(h \<circ> f) x \<in> UNIV" by simp
  next
    let ?R2 = "product_topology_on (top1_open_sets :: real set set) top1_open_sets"
    fix V :: "(real \<times> real) set" assume hV: "V \<in> ?R2"
    have "(UNIV - {?ha}) \<inter> V \<in> subspace_topology UNIV ?R2 (UNIV - {?ha})"
      by (rule subspace_topology_memI[OF hV])
    hence "{x \<in> A. (h \<circ> f) x \<in> (UNIV - {?ha}) \<inter> V} \<in> TA"
      using hg_cont unfolding top1_continuous_map_on_def by (by100 blast)
    moreover have "{x \<in> A. (h \<circ> f) x \<in> V} = {x \<in> A. (h \<circ> f) x \<in> (UNIV - {?ha}) \<inter> V}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> {x \<in> A. (h \<circ> f) x \<in> V}"
      hence "x \<in> A" "(h \<circ> f) x \<in> V" by auto
      moreover have "(h \<circ> f) x \<in> UNIV - {?ha}"
        using hg_cont \<open>x \<in> A\<close> unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show "x \<in> {x \<in> A. (h \<circ> f) x \<in> (UNIV - {?ha}) \<inter> V}" by (by100 blast)
    next
      fix x assume "x \<in> {x \<in> A. (h \<circ> f) x \<in> (UNIV - {?ha}) \<inter> V}"
      thus "x \<in> {x \<in> A. (h \<circ> f) x \<in> V}" by (by100 blast)
    qed
    ultimately show "{x \<in> A. (h \<circ> f) x \<in> V} \<in> TA" by simp
  qed
  \<comment> \<open>Step 6b: G homotopy. g(x)-\<alpha>(t) \<in> R^2-{0} since \<alpha>(t) \<notin> g(A) but g(x) \<in> g(A).\<close>
  have hG_hom: "top1_homotopic_on A TA (UNIV - {(0,0)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0,0)}))
      (\<lambda>x. pair_sub ((h \<circ> f) x) ?ha) (\<lambda>x. pair_sub ((h \<circ> f) x) p)"
  proof -
    let ?Y = "UNIV - {(0::real,0::real)}"
    let ?TY = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?Y"
    let ?g = "h \<circ> f"
    \<comment> \<open>G(x,t) = g(x) - \<alpha>R(t). At t=0: g(x)-ha. At t=1: g(x)-p.
       G(x,t) \<in> R^2-{0} because \<alpha>R(t) \<notin> g(A) but g(x) \<in> g(A), so g(x) \<noteq> \<alpha>R(t).\<close>
    define F_G :: "'a \<Rightarrow> real \<Rightarrow> real \<times> real" where
      "F_G x t = (fst (?g x) - fst (\<alpha>R t), snd (?g x) - snd (\<alpha>R t))" for x t
    have hFG0: "\<forall>x\<in>A. F_G x 0 = pair_sub (?g x) ?ha"
    proof
      fix x assume "x \<in> A"
      have "\<alpha>R 0 = ?ha" using h\<alpha>R unfolding top1_is_path_on_def by simp
      thus "F_G x 0 = pair_sub (?g x) ?ha" unfolding F_G_def pair_sub_def by simp
    qed
    have hFG1: "\<forall>x\<in>A. F_G x 1 = pair_sub (?g x) p"
    proof
      fix x assume "x \<in> A"
      have "\<alpha>R 1 = p" using h\<alpha>R unfolding top1_is_path_on_def by simp
      thus "F_G x 1 = pair_sub (?g x) p" unfolding F_G_def pair_sub_def by simp
    qed
    \<comment> \<open>F_G maps into ?Y: g(x) \<noteq> \<alpha>R(t) since \<alpha>R(t) \<notin> g(A) but g(x) \<in> g(A).\<close>
    have hFG_Y: "\<forall>x\<in>A. \<forall>t\<in>I_set. F_G x t \<in> ?Y"
    proof (intro ballI)
      fix x t assume hx: "x \<in> A" and ht: "t \<in> I_set"
      have "\<alpha>R t \<in> UNIV - ?g ` A"
      proof -
        have "\<alpha>R t \<in> UNIV - ?g ` A"
          using h\<alpha>R ht unfolding top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
        thus ?thesis .
      qed
      hence h\<alpha>_not_gA: "\<alpha>R t \<notin> ?g ` A" by simp
      have "?g x \<in> ?g ` A" using hx by simp
      hence "?g x \<noteq> \<alpha>R t" using h\<alpha>_not_gA by auto
      hence "F_G x t \<noteq> (0, 0)" unfolding F_G_def
        by (cases "?g x", cases "\<alpha>R t") simp
      thus "F_G x t \<in> ?Y" by simp
    qed
    \<comment> \<open>Continuity via continuous_compose_product_R2.\<close>
    have hFG_cont: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) ?Y ?TY
        (\<lambda>xt. F_G (fst xt) (snd xt))"
    proof -
      define \<phi>G :: "(real \<times> real) \<times> real \<Rightarrow> real \<times> real" where
        "\<phi>G yt = (fst (fst yt) - fst (\<alpha>R (snd yt)), snd (fst yt) - snd (\<alpha>R (snd yt)))" for yt
      have hFG_eq: "\<And>x t. F_G x t = \<phi>G (?g x, t)" unfolding F_G_def \<phi>G_def by simp
      \<comment> \<open>\<alpha>R is standard-continuous on I_set (custom continuous in R^2 = standard).\<close>
      have h\<alpha>_std_cont: "continuous_on I_set \<alpha>R"
      proof -
        have h\<alpha>_custom: "top1_continuous_map_on I_set I_top (UNIV - (h \<circ> f) ` A)
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - (h \<circ> f) ` A)) \<alpha>R"
          using h\<alpha>R unfolding top1_is_path_on_def by (by100 blast)
        \<comment> \<open>Bridge: custom continuous \<Rightarrow> standard continuous.
           preimage of open W \<subseteq> R^2 under \<alpha>R intersected with I_set is open in I_top = standard.\<close>
        show ?thesis unfolding continuous_on_open_invariant
        proof (intro allI impI)
          fix W :: "(real \<times> real) set" assume hW_open: "open W"
          have hW_R2: "W \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
          proof -
            have "W \<in> (top1_open_sets :: (real \<times> real) set set)"
              using hW_open unfolding top1_open_sets_def by simp
            thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
          qed
          have "(UNIV - (h \<circ> f) ` A) \<inter> W \<in> subspace_topology UNIV
              (product_topology_on top1_open_sets top1_open_sets) (UNIV - (h \<circ> f) ` A)"
            by (rule subspace_topology_memI[OF hW_R2])
          hence hpre: "{s \<in> I_set. \<alpha>R s \<in> (UNIV - (h \<circ> f) ` A) \<inter> W} \<in> I_top"
            using h\<alpha>_custom unfolding top1_continuous_map_on_def by (by100 blast)
          have hpre_eq: "\<alpha>R -` W \<inter> I_set = {s \<in> I_set. \<alpha>R s \<in> (UNIV - (h \<circ> f) ` A) \<inter> W}"
          proof (rule set_eqI, rule iffI)
            fix s assume "s \<in> \<alpha>R -` W \<inter> I_set"
            hence "s \<in> I_set" "\<alpha>R s \<in> W" by auto
            moreover have "\<alpha>R s \<in> UNIV - (h \<circ> f) ` A"
              using h\<alpha>_custom \<open>s \<in> I_set\<close> unfolding top1_continuous_map_on_def by (by100 blast)
            ultimately show "s \<in> {s \<in> I_set. \<alpha>R s \<in> (UNIV - (h \<circ> f) ` A) \<inter> W}" by (by100 blast)
          next
            fix s assume "s \<in> {s \<in> I_set. \<alpha>R s \<in> (UNIV - (h \<circ> f) ` A) \<inter> W}"
            thus "s \<in> \<alpha>R -` W \<inter> I_set" by (by100 blast)
          qed
          \<comment> \<open>I_top is subspace topology of R, so hpre means \<exists>W'. open W' \<and> ... = W' \<inter> I.\<close>
          obtain W' where hW': "W' \<in> top1_open_sets" and hW'_eq: "{s \<in> I_set. \<alpha>R s \<in> (UNIV - (h \<circ> f) ` A) \<inter> W} = I_set \<inter> W'"
            using hpre unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
          have "open W'" using hW' unfolding top1_open_sets_def by simp
          moreover have "W' \<inter> I_set = \<alpha>R -` W \<inter> I_set"
            using hW'_eq hpre_eq by (by100 blast)
          ultimately show "\<exists>T'. open T' \<and> T' \<inter> I_set = \<alpha>R -` W \<inter> I_set" by (by100 blast)
        qed
      qed
      have h\<phi>G_cont: "continuous_on (UNIV \<times> I_set) \<phi>G"
        unfolding \<phi>G_def by (intro continuous_intros continuous_on_compose2[OF h\<alpha>_std_cont]) auto
      have hg_UNIV: "top1_continuous_map_on A TA (UNIV :: (real\<times>real) set)
          (product_topology_on top1_open_sets top1_open_sets) ?g"
        by (rule hg_UNIV_fact)
      have hTA: "is_topology_on A TA" using hcomp unfolding top1_compact_on_def by (by100 blast)
      have hresult: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) ?Y ?TY
          (\<lambda>xt. \<phi>G (?g (fst xt), snd xt))"
        by (rule continuous_compose_product_R2[OF hg_UNIV h\<phi>G_cont _ hTA])
           (use hFG_Y hFG_eq in simp)
      moreover have "\<And>xt. \<phi>G (?g (fst xt), snd xt) = F_G (fst xt) (snd xt)"
        using hFG_eq by simp
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>f0 continuous.\<close>
    have hf0: "top1_continuous_map_on A TA ?Y ?TY (\<lambda>x. pair_sub (?g x) ?ha)"
      by (rule hgsub_ha_cont)
    \<comment> \<open>f1 continuous.\<close>
    have hf1: "top1_continuous_map_on A TA ?Y ?TY (\<lambda>x. pair_sub (?g x) p)"
      by (rule hgsub_p_cont)
    show ?thesis unfolding top1_homotopic_on_def
      using hf0 hf1
    proof (intro conjI exI[of _ "\<lambda>xt. F_G (fst xt) (snd xt)"])
      show "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) ?Y ?TY
          (\<lambda>xt. F_G (fst xt) (snd xt))" by (rule hFG_cont)
      show "\<forall>x\<in>A. F_G (fst (x, 0::real)) (snd (x, 0::real)) = pair_sub (?g x) ?ha"
        using hFG0 by simp
      show "\<forall>x\<in>A. F_G (fst (x, 1::real)) (snd (x, 1::real)) = pair_sub (?g x) p"
        using hFG1 by simp
    qed
  qed
  \<comment> \<open>Step 6c: H homotopy. t\<cdot>g(x)-p \<in> R^2-{0} since |t\<cdot>g(x)| \<le> M < |p|.\<close>
  have hH_hom: "top1_homotopic_on A TA (UNIV - {(0,0)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0,0)}))
      (\<lambda>x. pair_sub ((h \<circ> f) x) p) (\<lambda>_. pair_sub (0, 0) p)"
  proof -
    let ?Y = "UNIV - {(0::real,0::real)}"
    let ?TY = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?Y"
    let ?g = "h \<circ> f"
    \<comment> \<open>The homotopy F(x,t) = ((1-t)*fst(g(x))-fst(p), (1-t)*snd(g(x))-snd(p)).\<close>
    define F :: "'a \<Rightarrow> real \<Rightarrow> real \<times> real" where
      "F x t = ((1-t) * fst (?g x) - fst p, (1-t) * snd (?g x) - snd p)" for x t
    \<comment> \<open>F(x,0) = g(x)-p, F(x,1) = -p.\<close>
    have hF0: "\<forall>x\<in>A. F x 0 = pair_sub (?g x) p"
      unfolding F_def pair_sub_def by simp
    have hF1: "\<forall>x\<in>A. F x 1 = pair_sub (0,0) p"
      unfolding F_def pair_sub_def by simp
    \<comment> \<open>F maps into ?Y: F(x,t) \<noteq> 0 because |(1-t)*g(x)| \<le> M < |p|.\<close>
    have hF_in_Y: "\<forall>x\<in>A. \<forall>t\<in>I_set. F x t \<in> ?Y"
    proof (intro ballI)
      fix x t assume hx: "x \<in> A" and ht: "t \<in> I_set"
      have hgx_bdd: "fst (?g x) ^ 2 + snd (?g x) ^ 2 \<le> M ^ 2"
        using hgA_bdd hx by (by100 blast)
      have ht01: "0 \<le> t \<and> t \<le> 1" using ht unfolding top1_unit_interval_def by simp
      have h1t: "0 \<le> 1 - t \<and> 1 - t \<le> 1" using ht01 by simp
      have "F x t \<noteq> (0, 0)"
      proof
        assume heq: "F x t = (0, 0)"
        have hfp: "fst p = (1-t) * fst (?g x)" using heq unfolding F_def by (cases "F x t") simp
        have hsp: "snd p = (1-t) * snd (?g x)" using heq unfolding F_def by (cases "F x t") simp
        have hfp2: "fst p ^ 2 = (1-t)^2 * (fst (?g x))^2"
          using hfp by (simp add: power_mult_distrib)
        have hsp2: "snd p ^ 2 = (1-t)^2 * (snd (?g x))^2"
          using hsp by (simp add: power_mult_distrib)
        have h1t2: "(1-t)^2 \<le> 1"
        proof -
          have "(1-t) * (1-t) \<le> 1 * 1"
            by (rule mult_mono) (use h1t in auto)
          thus ?thesis by (simp add: power2_eq_square)
        qed
        have "(1-t)^2 * (fst (?g x) ^ 2 + snd (?g x) ^ 2) \<le> 1 * M ^ 2"
          by (rule mult_mono[OF h1t2 hgx_bdd]) simp_all
        have "fst p ^ 2 + snd p ^ 2 \<le> M ^ 2"
          using \<open>(1-t)\<^sup>2 * (fst (?g x) ^ 2 + snd (?g x) ^ 2) \<le> 1 * M ^ 2\<close>
            hfp2 hsp2 by (simp add: algebra_simps)
        show False using \<open>fst p ^ 2 + snd p ^ 2 \<le> M ^ 2\<close> hp_far by (by100 linarith)
      qed
      thus "F x t \<in> ?Y" by simp
    qed
    \<comment> \<open>Continuity of F: need top1_continuous_map_on (A\<times>I) ... ?Y ?TY (\<lambda>(x,t). F x t).\<close>
    have hF_cont: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) ?Y ?TY
        (\<lambda>xt. F (fst xt) (snd xt))"
    proof -
      \<comment> \<open>Use continuous_compose_product_R2 with \<phi>(y,t) = ((1-t)*fst(y)-fst(p), (1-t)*snd(y)-snd(p)).\<close>
      define \<phi> :: "(real \<times> real) \<times> real \<Rightarrow> real \<times> real" where
        "\<phi> yt = ((1 - snd yt) * fst (fst yt) - fst p, (1 - snd yt) * snd (fst yt) - snd p)" for yt
      have hF_eq: "\<And>x t. F x t = \<phi> (?g x, t)" unfolding F_def \<phi>_def by simp
      have h\<phi>_cont: "continuous_on (UNIV \<times> I_set) \<phi>"
        unfolding \<phi>_def by (intro continuous_intros)
      \<comment> \<open>g continuous from A to UNIV (R^2).\<close>
      have hg_UNIV: "top1_continuous_map_on A TA (UNIV :: (real\<times>real) set)
          (product_topology_on top1_open_sets top1_open_sets) ?g"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x assume "x \<in> A" thus "?g x \<in> UNIV" by simp
      next
        fix V :: "(real\<times>real) set" assume hV: "V \<in> product_topology_on top1_open_sets top1_open_sets"
        have "(UNIV - {?ha}) \<inter> V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {?ha})"
          by (rule subspace_topology_memI[OF hV])
        hence "{x \<in> A. ?g x \<in> (UNIV - {?ha}) \<inter> V} \<in> TA"
          using hg_cont unfolding top1_continuous_map_on_def by (by100 blast)
        moreover have "{x \<in> A. ?g x \<in> V} = {x \<in> A. ?g x \<in> (UNIV - {?ha}) \<inter> V}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> {x \<in> A. ?g x \<in> V}"
          moreover have "?g x \<in> UNIV - {?ha}" if "x \<in> A" for x
            using hg_cont that unfolding top1_continuous_map_on_def by (by100 blast)
          ultimately show "x \<in> {x \<in> A. ?g x \<in> (UNIV - {?ha}) \<inter> V}" by (by100 blast)
        next
          fix x assume "x \<in> {x \<in> A. ?g x \<in> (UNIV - {?ha}) \<inter> V}"
          thus "x \<in> {x \<in> A. ?g x \<in> V}" by (by100 blast)
        qed
        ultimately show "{x \<in> A. ?g x \<in> V} \<in> TA" by simp
      qed
      have hTA: "is_topology_on A TA" using hcomp unfolding top1_compact_on_def by (by100 blast)
      have hresult: "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) ?Y
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?Y)
          (\<lambda>xt. \<phi> (?g (fst xt), snd xt))"
        by (rule continuous_compose_product_R2[OF hg_UNIV h\<phi>_cont _ hTA])
           (use hF_in_Y hF_eq in \<open>simp\<close>)
      moreover have "\<And>xt. \<phi> (?g (fst xt), snd xt) = F (fst xt) (snd xt)"
        using hF_eq by simp
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>f0 = \<lambda>x. pair_sub (g(x)) p is continuous from A to ?Y.\<close>
    have hf0_cont: "top1_continuous_map_on A TA ?Y ?TY (\<lambda>x. pair_sub (?g x) p)"
      by (rule hgsub_p_cont)
    \<comment> \<open>f1 = constant pair_sub(0,0)(p) is continuous.\<close>
    have hf1_cont: "top1_continuous_map_on A TA ?Y ?TY (\<lambda>_. pair_sub (0,0) p)"
    proof -
      have hTA: "is_topology_on A TA" using hcomp unfolding top1_compact_on_def by (by100 blast)
      have hTY: "is_topology_on ?Y ?TY"
      proof -
        have "is_topology_on (UNIV :: (real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV] by simp
        thus ?thesis by (rule subspace_topology_is_topology_on) (by100 blast)
      qed
      have "pair_sub (0,0) p \<in> ?Y"
      proof -
        have "pair_sub (0,0) p = (- fst p, - snd p)" unfolding pair_sub_def by simp
        moreover have "(- fst p, - snd p) \<noteq> (0::real, 0::real)"
          unfolding p_def using hM by simp
        ultimately show ?thesis by simp
      qed
      thus ?thesis by (rule top1_continuous_map_on_const[OF hTA hTY])
    qed
    show ?thesis unfolding top1_homotopic_on_def
    proof (intro conjI exI[of _ "\<lambda>xt. F (fst xt) (snd xt)"])
      show "top1_continuous_map_on A TA ?Y ?TY (\<lambda>x. pair_sub (?g x) p)" by (rule hf0_cont)
      show "top1_continuous_map_on A TA ?Y ?TY (\<lambda>_. pair_sub (0,0) p)" by (rule hf1_cont)
      show "top1_continuous_map_on (A \<times> I_set) (product_topology_on TA I_top) ?Y ?TY
          (\<lambda>xt. F (fst xt) (snd xt))" by (rule hF_cont)
      show "\<forall>x\<in>A. F (fst (x, 0::real)) (snd (x, 0::real)) = pair_sub (?g x) p"
        using hF0 by simp
      show "\<forall>x\<in>A. F (fst (x, 1::real)) (snd (x, 1::real)) = pair_sub (0, 0) p"
        using hF1 by simp
    qed
  qed
  \<comment> \<open>Compose: g(\<cdot>)-ha nulhomotopic in R^2-{0}.\<close>
  have "top1_nulhomotopic_on A TA (UNIV - {(0::real,0::real)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0,0)}))
      (\<lambda>x. pair_sub ((h \<circ> f) x) ?ha)"
  proof -
    let ?Y = "UNIV - {(0::real,0::real)}"
    let ?TY = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?Y"
    have hTY: "is_topology_on ?Y ?TY"
    proof -
      have "is_topology_on (UNIV :: (real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
            top1_open_sets_is_topology_on_UNIV] by simp
      thus ?thesis by (rule subspace_topology_is_topology_on) (by100 blast)
    qed
    have hTA: "is_topology_on A TA" using hcomp unfolding top1_compact_on_def by (by100 blast)
    \<comment> \<open>Compose G and H by transitivity.\<close>
    have hGH: "top1_homotopic_on A TA ?Y ?TY
        (\<lambda>x. pair_sub ((h \<circ> f) x) ?ha) (\<lambda>_. pair_sub (0, 0) p)"
      by (rule Lemma_51_1_homotopic_trans[OF hTA hTY hG_hom hH_hom])
    \<comment> \<open>pair_sub (0,0) p is a constant in Y.\<close>
    have hconst_in_Y: "pair_sub (0, 0) p \<in> ?Y"
    proof -
      have "pair_sub (0, 0) p = (- fst p, - snd p)" unfolding pair_sub_def by simp
      also have "... = (-(2*M+1), 0)" unfolding p_def by simp
      finally have "pair_sub (0, 0) p = (-(2*M+1), 0)" .
      moreover have "(-(2*M+1), (0::real)) \<noteq> (0, 0)" using hM by simp
      ultimately show ?thesis by simp
    qed
    show ?thesis unfolding top1_nulhomotopic_on_def
      using hGH hconst_in_Y by (by100 blast)
  qed
  \<comment> \<open>Translate: pair_sub (g x) ha = 0 iff g x = ha. So R^2-{0} via translation \<cong> R^2-{ha}.\<close>
  have hg_nul_R2: "top1_nulhomotopic_on A TA
      (UNIV - {?ha})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
        (UNIV - {?ha}))
      (h \<circ> f)"
  proof -
    \<comment> \<open>T(x) = pair_sub x ha maps R^2-{ha} to R^2-{0} homeomorphically.\<close>
    let ?T = "\<lambda>x :: real \<times> real. (fst x - fst ?ha, snd x - snd ?ha)"
    have hT_eq: "?T = (\<lambda>x. (fst x - fst (h a), snd x - snd (h a)))" by simp
    have hT_homeo: "top1_homeomorphism_on (UNIV - {?ha})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {?ha}))
        (UNIV - {(0,0)})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0,0)}))
        ?T"
      by (rule translation_homeo_R2[of ?ha])
    \<comment> \<open>T \<circ> (h\<circ>f) = \<lambda>x. pair_sub ((h\<circ>f)x) ha.\<close>
    have hcomp_eq: "?T \<circ> (h \<circ> f) = (\<lambda>x. pair_sub ((h \<circ> f) x) ?ha)"
      unfolding pair_sub_def comp_def by simp
    have hTA: "is_topology_on A TA" using hcomp unfolding top1_compact_on_def by (by100 blast)
    show ?thesis
      using nulhomotopic_transfer[OF hT_homeo _ hg_cont hTA]
        \<open>top1_nulhomotopic_on A TA (UNIV - {(0,0)})
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0,0)}))
            (\<lambda>x. pair_sub ((h \<circ> f) x) ?ha)\<close>
        hcomp_eq by simp
  qed
  \<comment> \<open>Step 8: Transfer via h restricted to S^2-{a,b} \<cong> R^2-{h(a)}.
     Use homeomorphism_restrict_point to get h: S^2-{a,b} \<rightarrow> R^2-{h(a)}.\<close>
  have hh_restrict: "top1_homeomorphism_on (top1_S2 - {a, b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b}))
      (UNIV - {?ha})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {?ha}))
      h"
  proof -
    have ha_in: "a \<in> top1_S2 - {b}" using ha hab by (by100 blast)
    have hhr: "top1_homeomorphism_on ((top1_S2 - {b}) - {a})
        (subspace_topology (top1_S2 - {b})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
          ((top1_S2 - {b}) - {a}))
        (UNIV - {h a})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {h a}))
        h"
      by (rule homeomorphism_restrict_point[OF hh ha_in])
    moreover have "(top1_S2 - {b}) - {a} = top1_S2 - {a, b}" by (by100 blast)
    moreover have "subspace_topology (top1_S2 - {b})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
        ((top1_S2 - {b}) - {a})
      = subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})"
    proof -
      have hsub: "top1_S2 - {a, b} \<subseteq> top1_S2 - {b}" by (by100 blast)
      have "subspace_topology (top1_S2 - {b})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
          (top1_S2 - {a, b})
        = subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})"
        by (rule subspace_topology_trans[OF hsub])
      moreover have "(top1_S2 - {b}) - {a} = top1_S2 - {a, b}" by (by100 blast)
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by simp
  qed
  have hTA_: "is_topology_on A TA" using hcomp unfolding top1_compact_on_def by (by100 blast)
  show ?thesis
    by (rule nulhomotopic_transfer[OF hh_restrict hg_nul_R2 hf hTA_])
qed

(** from \<S>61 Theorem 61.3: Jordan separation theorem for S^2.

    Munkres' proof sketch:
    Suppose for contradiction S^2 - C is path connected.
    Write C = A_1 \<union> A_2 (arcs meeting at {a, b}).
    Let X = S^2 - {a, b}, U = S^2 - A_1, V = S^2 - A_2.
    Then X = U \<union> V and U \<inter> V = S^2 - C (path connected by assumption).
    By Theorem 59.1, \<pi>_1(X, x_0) is generated by images of i_*, j_*.
    Using Lemma 61.2 (nulhomotopy), both i_* and j_* are trivial.
    So \<pi>_1(X, x_0) is trivial. But X \<cong> R^2 - {0} has nontrivial \<pi>_1. \<bottom> **)

definition top1_is_arc_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_arc_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<exists>h. top1_homeomorphism_on I_set I_top X TX h)"

lemma S1_not_simply_connected:
  "\<not> top1_simply_connected_on top1_S1 top1_S1_topology"
proof
  assume hsc: "top1_simply_connected_on top1_S1 top1_S1_topology"
  \<comment> \<open>By Theorem_54_5: \<pi>_1(S^1, (1,0)) \<cong> Z (bijection with int).\<close>
  obtain \<phi> where h\<phi>: "bij_betw \<phi> (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (UNIV::int set)"
    using Theorem_54_5 by blast
  \<comment> \<open>Simply connected \<Rightarrow> \<pi>_1 = {[const]}, i.e., carrier has exactly 1 element.\<close>
  have h10: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by simp
  have htriv: "\<forall>f. top1_is_loop_on top1_S1 top1_S1_topology (1,0) f \<longrightarrow>
      top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0) f (top1_constant_path (1,0))"
    using hsc h10 unfolding top1_simply_connected_on_def by (by100 blast)
  \<comment> \<open>So carrier = {class of const} has exactly 1 element.\<close>
  have hT_S1: "is_topology_on top1_S1 top1_S1_topology"
  proof -
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using product_topology_on_is_topology_on[OF hTR hTR] by simp
    show ?thesis unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
  qed
  have hcard1: "top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)
      = {{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (top1_constant_path (1,0)) g}}"
  proof (rule set_eqI, rule iffI)
    fix cls assume hcls: "cls \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)"
    obtain f where hf_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1,0) f"
        and hcls_eq: "cls = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) f g}"
      using hcls unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hf_const: "top1_path_homotopic_on top1_S1 top1_S1_topology (1,0) (1,0)
        f (top1_constant_path (1,0))"
      using htriv hf_loop by (by100 blast)
    have hconst_loop0: "top1_is_loop_on top1_S1 top1_S1_topology (1,0) (top1_constant_path (1,0))"
      by (rule top1_constant_path_is_loop[OF hT_S1 h10])
    have hf_equiv_const: "top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) f (top1_constant_path (1,0))"
      unfolding top1_loop_equiv_on_def using hf_loop hconst_loop0 hf_const by (by100 blast)
    have hconst_equiv_f: "top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (top1_constant_path (1,0)) f"
      by (rule top1_loop_equiv_on_sym[OF hf_equiv_const])
    have "\<And>g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) f g
        = top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (top1_constant_path (1,0)) g"
    proof -
      fix g
      show "top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) f g
          = top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (top1_constant_path (1,0)) g"
      proof (rule iffI)
        assume hfg: "top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) f g"
        show "top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (top1_constant_path (1,0)) g"
          by (rule top1_loop_equiv_on_trans[OF hT_S1 hconst_equiv_f hfg])
      next
        assume hcg: "top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (top1_constant_path (1,0)) g"
        show "top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) f g"
          by (rule top1_loop_equiv_on_trans[OF hT_S1 hf_equiv_const hcg])
      qed
    qed
    hence "cls = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (top1_constant_path (1,0)) g}"
      using hcls_eq by simp
    thus "cls \<in> {{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (top1_constant_path (1,0)) g}}"
      by (by100 blast)
  next
    fix cls assume "cls \<in> {{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (top1_constant_path (1,0)) g}}"
    hence hcls_eq: "cls = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1,0) (top1_constant_path (1,0)) g}"
      by (by100 blast)
    have hconst_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1,0) (top1_constant_path (1,0))"
      by (rule top1_constant_path_is_loop[OF hT_S1 h10])
    show "cls \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0)"
      unfolding top1_fundamental_group_carrier_def hcls_eq
      using hconst_loop by (by100 blast)
  qed
  \<comment> \<open>bij_betw \<phi> from singleton to UNIV::int is impossible.\<close>
  have "finite (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))"
    using hcard1 by simp
  moreover have "infinite (UNIV :: int set)" by simp
  moreover have "bij_betw \<phi> (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1,0))
      (UNIV :: int set)" by (rule h\<phi>)
  ultimately show False
    using bij_betw_finite by (by100 blast)
qed

lemma simple_closed_curve_arc_decomposition:
  assumes hC: "top1_simple_closed_curve_on X TX C"
      and hT: "is_topology_on_strict X TX"
      and hH: "is_hausdorff_on X TX"
  shows "\<exists>A1 A2 a b. C = A1 \<union> A2
      \<and> A1 \<inter> A2 = {a, b} \<and> a \<noteq> b
      \<and> top1_is_arc_on A1 (subspace_topology X TX A1)
      \<and> top1_is_arc_on A2 (subspace_topology X TX A2)"
proof -
  \<comment> \<open>Obtain injective continuous f: S^1 \<rightarrow> X with f(S^1) = C.\<close>
  obtain f where hf_cont: "top1_continuous_map_on top1_S1 top1_S1_topology X TX f"
      and hf_inj: "inj_on f top1_S1" and hf_img: "f ` top1_S1 = C"
    using hC unfolding top1_simple_closed_curve_on_def by (by100 blast)
  \<comment> \<open>Take a = f(1,0), b = f(-1,0). Split S^1 into upper and lower semicircles.\<close>
  let ?a = "f (1::real, 0::real)" and ?b = "f (-1::real, 0::real)"
  let ?upper = "{p \<in> top1_S1. snd p \<ge> 0}" and ?lower = "{p \<in> top1_S1. snd p \<le> 0}"
  have h10: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by simp
  have hm10: "(-1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by simp
  have hab_ne: "?a \<noteq> ?b"
  proof
    assume "?a = ?b"
    hence "(1::real,0::real) = (-1,0)" using hf_inj h10 hm10 unfolding inj_on_def by (by100 blast)
    thus False by simp
  qed
  \<comment> \<open>S^1 = upper \<union> lower, upper \<inter> lower = {(1,0), (-1,0)}.\<close>
  have hunion: "top1_S1 = ?upper \<union> ?lower" by auto
  have hinter: "?upper \<inter> ?lower = {p \<in> top1_S1. snd p = 0}"
    by auto
  have hinter_eq: "?upper \<inter> ?lower = {(1::real, 0), (-1, 0)}"
  proof -
    have "\<And>p. p \<in> ?upper \<inter> ?lower \<Longrightarrow> p \<in> {(1::real, 0), (-1, 0)}"
    proof -
      fix p assume hp: "p \<in> ?upper \<inter> ?lower"
      have hp_S1: "p \<in> top1_S1" and hge: "snd p \<ge> 0" and hle: "snd p \<le> 0"
        using hp by auto
      hence "snd p = 0" by (by100 linarith)
      hence "fst p ^ 2 = 1" using hp_S1 unfolding top1_S1_def by auto
      hence "fst p = 1 \<or> fst p = -1" by (simp add: power2_eq_1_iff)
      thus "p \<in> {(1::real, 0), (-1, 0)}" using \<open>snd p = 0\<close> by (cases p) auto
    qed
    moreover have "(1::real, 0) \<in> ?upper \<inter> ?lower" unfolding top1_S1_def by auto
    moreover have "(-1::real, 0) \<in> ?upper \<inter> ?lower" unfolding top1_S1_def by auto
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>A1 = f(upper), A2 = f(lower).\<close>
  let ?A1 = "f ` ?upper" and ?A2 = "f ` ?lower"
  have hC_decomp: "C = ?A1 \<union> ?A2" using hf_img hunion by (by100 blast)
  have hinter_img: "?A1 \<inter> ?A2 = {?a, ?b}"
  proof (rule set_eqI, rule iffI)
    fix x assume hx: "x \<in> ?A1 \<inter> ?A2"
    have hx1: "x \<in> f ` ?upper" and hx2: "x \<in> f ` ?lower" using hx by (by100 blast)+
    obtain p1 where hp1: "p1 \<in> ?upper" "f p1 = x" using hx1 by (by100 blast)
    obtain p2 where hp2: "p2 \<in> ?lower" "f p2 = x" using hx2 by (by100 blast)
    have hp1_S1: "p1 \<in> top1_S1" using hp1(1) by (by100 blast)
    have hp2_S1: "p2 \<in> top1_S1" using hp2(1) by (by100 blast)
    have "p1 = p2" using hf_inj hp1_S1 hp2_S1 hp1(2) hp2(2) unfolding inj_on_def by (by100 blast)
    hence "p1 \<in> ?upper \<inter> ?lower" using hp2(1) hp1(1) by (by100 blast)
    hence "p1 = (1, 0) \<or> p1 = (-1, 0)" using hinter_eq by (by100 blast)
    thus "x \<in> {?a, ?b}" using hp1(2) by (by100 blast)
  next
    fix x assume "x \<in> {?a, ?b}"
    hence "x = f (1,0) \<or> x = f (-1,0)" by (by100 blast)
    moreover have "(1::real,0) \<in> ?upper" and "(-1::real,0) \<in> ?upper"
        and "(1::real,0) \<in> ?lower" and "(-1::real,0) \<in> ?lower"
      unfolding top1_S1_def by auto
    ultimately show "x \<in> ?A1 \<inter> ?A2" by (by100 blast)
  qed
  \<comment> \<open>Each semicircle is an arc (homeomorphic to [0,1]).\<close>
  have hTX: "is_topology_on X TX" using hT unfolding is_topology_on_strict_def by (by100 blast)
  have hA1_arc: "top1_is_arc_on ?A1 (subspace_topology X TX ?A1)"
  proof -
    \<comment> \<open>Upper semicircle parametrization: g(t) = (cos(\<pi>t), sin(\<pi>t)) maps [0,1] \<rightarrow> upper.\<close>
    define g where "g = (\<lambda>t::real. (cos (pi * t), sin (pi * t)))"
    have hg_img: "g ` I_set = ?upper"
    proof (rule set_eqI, rule iffI)
      fix p assume "p \<in> g ` I_set"
      then obtain t where ht: "t \<in> I_set" "p = g t" by (by100 blast)
      have htr: "0 \<le> t" "t \<le> 1" using ht(1) unfolding top1_unit_interval_def by auto
      have "fst p ^ 2 + snd p ^ 2 = 1"
        unfolding ht(2) g_def by (simp add: sin_cos_squared_add2)
      moreover have "snd p = sin (pi * t)" unfolding ht(2) g_def by simp
      moreover have "sin (pi * t) \<ge> 0" using sin_ge_zero htr pi_ge_zero
        by (auto intro: mult_nonneg_nonneg)
      ultimately show "p \<in> ?upper" unfolding top1_S1_def by auto
    next
      fix p assume hp: "p \<in> ?upper"
      have hpS1: "fst p ^ 2 + snd p ^ 2 = 1" using hp unfolding top1_S1_def by auto
      have hge: "snd p \<ge> 0" using hp by (by100 simp)
      define t where "t = arccos (fst p) / pi"
      have hfst_range: "-1 \<le> fst p" "fst p \<le> 1"
      proof -
        have "snd p ^ 2 \<ge> 0" by simp
        hence hfp2: "fst p ^ 2 \<le> 1" using hpS1 by (by100 linarith)
        have "fst p \<le> 1"
        proof (rule ccontr)
          assume "\<not> fst p \<le> 1"
          hence "fst p > 1" by simp
          hence "fst p ^ 2 > 1" unfolding power2_eq_square
            using mult_strict_mono'[of 1 "fst p" 1 "fst p"] by (by100 linarith)
          thus False using hfp2 by (by100 linarith)
        qed
        moreover have "-1 \<le> fst p"
        proof (rule ccontr)
          assume "\<not> -1 \<le> fst p"
          hence "fst p < -1" by simp
          hence "(-fst p) > 1" by simp
          hence "(-fst p)^2 > 1" unfolding power2_eq_square
            using mult_strict_mono'[of 1 "-fst p" 1 "-fst p"] by (by100 linarith)
          hence "fst p ^ 2 > 1" by (simp add: power2_eq_square)
          thus False using hfp2 by (by100 linarith)
        qed
        ultimately show "-1 \<le> fst p" "fst p \<le> 1" by simp+
      qed
      have hpi_t: "pi * t = arccos (fst p)" unfolding t_def using pi_gt_zero by simp
      have ht_ge: "0 \<le> t"
      proof -
        have "0 \<le> arccos (fst p)" by (rule arccos_lbound[OF hfst_range(1) hfst_range(2)])
        thus ?thesis unfolding t_def using pi_gt_zero by (by100 simp)
      qed
      have ht_le: "t \<le> 1"
      proof -
        have "arccos (fst p) \<le> pi" by (rule arccos_ubound[OF hfst_range(1) hfst_range(2)])
        thus ?thesis unfolding t_def using pi_gt_zero by (by100 simp)
      qed
      have hcos: "cos (pi * t) = fst p"
        unfolding hpi_t using hfst_range by (rule cos_arccos)
      have hsin: "sin (pi * t) = snd p"
      proof -
        have "sin (pi * t) \<ge> 0" using sin_ge_zero ht_ge ht_le pi_ge_zero
          by (auto intro: mult_nonneg_nonneg)
        have "sin (pi * t) ^ 2 = 1 - cos (pi * t) ^ 2"
          using sin_cos_squared_add[of "pi * t"] by (by100 linarith)
        also have "... = 1 - fst p ^ 2" using hcos by simp
        also have "... = snd p ^ 2" using hpS1 by (by100 linarith)
        finally have "sin (pi * t) ^ 2 = snd p ^ 2" .
        thus "sin (pi * t) = snd p" using \<open>sin (pi * t) \<ge> 0\<close> hge
          by (simp add: power2_eq_iff_nonneg)
      qed
      have "p = g t" unfolding g_def using hcos hsin by (cases p) auto
      moreover have "t \<in> I_set" using ht_ge ht_le unfolding top1_unit_interval_def by auto
      ultimately show "p \<in> g ` I_set" by (by100 blast)
    qed
    have hg_inj: "inj_on g I_set"
    proof (rule inj_onI)
      fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and heq: "g s = g t"
      have hsr: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
      have htr: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
      from heq have hcos: "cos (pi * s) = cos (pi * t)" and hsin: "sin (pi * s) = sin (pi * t)"
        unfolding g_def by auto
      \<comment> \<open>cos is injective on [0, \<pi>].\<close>
      have hps: "0 \<le> pi * s" "pi * s \<le> pi" using hsr pi_ge_zero by auto
      have hpt: "0 \<le> pi * t" "pi * t \<le> pi" using htr pi_ge_zero by auto
      have "pi * s = pi * t"
        by (rule cos_inj_pi[OF hps(1) hps(2) hpt(1) hpt(2) hcos])
      thus "s = t" using pi_gt_zero by (by100 simp)
    qed
    have hg_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology g"
    proof -
      \<comment> \<open>g is continuous in the standard topology.\<close>
      have hg_std: "continuous_on I_set g"
        unfolding g_def by (intro continuous_intros)
      \<comment> \<open>g maps I_set to top1_S1.\<close>
      have hg_maps: "\<forall>t\<in>I_set. g t \<in> top1_S1"
      proof
        fix t assume "t \<in> I_set"
        show "g t \<in> top1_S1" unfolding g_def top1_S1_def
          by (auto simp: sin_cos_squared_add2)
      qed
      \<comment> \<open>Bridge: standard continuity implies top1 continuity for subspace topologies.\<close>
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix t assume ht: "t \<in> I_set"
        show "g t \<in> top1_S1" using hg_maps ht by (by100 blast)
      next
        fix V assume hV: "V \<in> top1_S1_topology"
        \<comment> \<open>V = top1_S1 \<inter> W for some W open in R^2.\<close>
        obtain W where hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
            and hV_eq: "V = top1_S1 \<inter> W"
          using hV unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
        have hWo: "open W" using hW product_topology_on_open_sets_real2
          unfolding top1_open_sets_def by (by100 simp)
        \<comment> \<open>{t \<in> I_set. g t \<in> V} = {t \<in> I_set. g t \<in> W} (since g maps into S^1).\<close>
        have hpre_eq: "{t \<in> I_set. g t \<in> V} = I_set \<inter> g -` W"
          using hV_eq hg_maps by (by100 blast)
        \<comment> \<open>g^{-1}(W) \<inter> I_set is open in I_set (standard continuity).\<close>
        have "open (g -` W)"
        proof -
          have "continuous_on UNIV g" unfolding g_def by (intro continuous_intros)
          thus ?thesis using hWo
            by (simp add: continuous_on_open_vimage[OF open_UNIV])
        qed
        hence "g -` W \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
        have "I_set \<inter> g -` W \<in> subspace_topology UNIV top1_open_sets I_set"
          unfolding subspace_topology_def
          apply (rule CollectI)
          apply (rule exI[of _ "g -` W"])
          using \<open>g -` W \<in> top1_open_sets\<close> by (by100 blast)
        hence "{t \<in> I_set. g t \<in> V} \<in> subspace_topology UNIV top1_open_sets I_set"
          using hpre_eq by simp
        thus "{t \<in> I_set. g t \<in> V} \<in> I_top"
          unfolding top1_unit_interval_topology_def by simp
      qed
    qed
    \<comment> \<open>f \<circ> g: [0,1] \<rightarrow> f(upper) = A1 is injective continuous.\<close>
    have hfg_cont: "top1_continuous_map_on I_set I_top X TX (f \<circ> g)"
      \<comment> \<open>Composition of g: I \<rightarrow> S^1 and f: S^1 \<rightarrow> X, both continuous.\<close>
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix t assume ht: "t \<in> I_set"
      have "g t \<in> top1_S1" using hg_cont ht unfolding top1_continuous_map_on_def by (by100 blast)
      thus "(f \<circ> g) t \<in> X" using hf_cont unfolding top1_continuous_map_on_def comp_def by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have hpre_f: "{x \<in> top1_S1. f x \<in> V} \<in> top1_S1_topology"
        using hf_cont hV unfolding top1_continuous_map_on_def by (by100 blast)
      have hpre_g: "{t \<in> I_set. g t \<in> {x \<in> top1_S1. f x \<in> V}} \<in> I_top"
        using hg_cont hpre_f unfolding top1_continuous_map_on_def by (by100 blast)
      have "{t \<in> I_set. (f \<circ> g) t \<in> V} = {t \<in> I_set. g t \<in> {x \<in> top1_S1. f x \<in> V}}"
      proof (rule set_eqI, rule iffI)
        fix t assume "t \<in> {t \<in> I_set. (f \<circ> g) t \<in> V}"
        hence ht: "t \<in> I_set" and hfgt: "f (g t) \<in> V" unfolding comp_def by auto
        have "g t \<in> top1_S1" using hg_cont ht unfolding top1_continuous_map_on_def by (by100 blast)
        thus "t \<in> {t \<in> I_set. g t \<in> {x \<in> top1_S1. f x \<in> V}}" using ht hfgt by (by100 blast)
      next
        fix t assume "t \<in> {t \<in> I_set. g t \<in> {x \<in> top1_S1. f x \<in> V}}"
        thus "t \<in> {t \<in> I_set. (f \<circ> g) t \<in> V}" unfolding comp_def by (by100 blast)
      qed
      thus "{t \<in> I_set. (f \<circ> g) t \<in> V} \<in> I_top" using hpre_g by simp
    qed
    have hfg_inj: "inj_on (f \<circ> g) I_set"
    proof (rule inj_onI)
      fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and heq: "(f \<circ> g) s = (f \<circ> g) t"
      have hgs: "g s \<in> ?upper" using hs hg_img by (by100 blast)
      have hgt: "g t \<in> ?upper" using ht hg_img by (by100 blast)
      have hgsS1: "g s \<in> top1_S1" using hgs by (by100 simp)
      have hgtS1: "g t \<in> top1_S1" using hgt by (by100 simp)
      hence "g s = g t" using hf_inj hgsS1 hgtS1 heq unfolding comp_def inj_on_def by (by100 blast)
      thus "s = t" using hg_inj hs ht unfolding inj_on_def by (by100 blast)
    qed
    have hfg_img: "(f \<circ> g) ` I_set = ?A1"
    proof -
      have "(f \<circ> g) ` I_set = f ` (g ` I_set)" by (by100 auto)
      also have "... = f ` ?upper" using hg_img by simp
      finally show ?thesis .
    qed
    \<comment> \<open>[0,1] compact, subspace of X Hausdorff. By Theorem_26_6, f\<circ>g is homeomorphism.\<close>
    have hTA1: "is_topology_on ?A1 (subspace_topology X TX ?A1)"
    proof -
      have "?A1 \<subseteq> X" using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
      thus ?thesis by (rule subspace_topology_is_topology_on[OF hTX])
    qed
    have hI_compact: "top1_compact_on I_set I_top"
    proof -
      have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
        by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
      have "compact {0..1::real}" by (rule compact_Icc)
      hence "compact I_set" using hI01 by simp
      have "top1_compact_on I_set (subspace_topology (UNIV::real set) top1_open_sets I_set)"
        using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
      thus ?thesis unfolding top1_unit_interval_topology_def by simp
    qed
    have hA1_sub: "?A1 \<subseteq> X"
    proof -
      have "\<forall>x \<in> top1_S1. f x \<in> X" using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
      moreover have "?upper \<subseteq> top1_S1" by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    have hA1_haus: "is_hausdorff_on ?A1 (subspace_topology X TX ?A1)"
      by (rule hausdorff_subspace[OF hH hA1_sub])
    have hfg_bij: "bij_betw (f \<circ> g) I_set ?A1"
      unfolding bij_betw_def using hfg_inj hfg_img by (by100 blast)
    have hI_top: "is_topology_on I_set I_top"
      using hI_compact unfolding top1_compact_on_def by (by100 blast)
    have hfg_cont_A1: "top1_continuous_map_on I_set I_top ?A1 (subspace_topology X TX ?A1) (f \<circ> g)"
    proof -
      have h_rr: "\<forall>W g. top1_continuous_map_on I_set I_top X TX g \<and> W \<subseteq> X \<and> g ` I_set \<subseteq> W
          \<longrightarrow> top1_continuous_map_on I_set I_top W (subspace_topology X TX W) g"
        by (rule Theorem_18_2(5)[OF hI_top hTX hTX])
      have h_rr_inst: "top1_continuous_map_on I_set I_top X TX (f \<circ> g)
          \<and> ?A1 \<subseteq> X \<and> (f \<circ> g) ` I_set \<subseteq> ?A1
          \<longrightarrow> top1_continuous_map_on I_set I_top ?A1 (subspace_topology X TX ?A1) (f \<circ> g)"
        using h_rr[THEN spec, THEN spec] by (by100 simp)
      thus ?thesis using hfg_cont hA1_sub hfg_img by (by100 blast)
    qed
    have hfg_homeo: "top1_homeomorphism_on I_set I_top ?A1 (subspace_topology X TX ?A1) (f \<circ> g)"
      by (rule Theorem_26_6[OF hI_top hTA1 hI_compact hA1_haus hfg_cont_A1 hfg_bij])
    have hA1_strict: "is_topology_on_strict ?A1 (subspace_topology X TX ?A1)"
      by (rule subspace_topology_is_strict[OF hT hA1_sub])
    show ?thesis unfolding top1_is_arc_on_def using hA1_strict hfg_homeo by (by100 blast)
  qed
  have hA2_arc: "top1_is_arc_on ?A2 (subspace_topology X TX ?A2)"
  proof -
    \<comment> \<open>Lower semicircle parametrization: g'(t) = (cos(\<pi>+\<pi>t), sin(\<pi>+\<pi>t)) maps [0,1] \<rightarrow> lower.\<close>
    define g' where "g' = (\<lambda>t::real. (cos (pi + pi * t), sin (pi + pi * t)))"
    have hg'_img: "g' ` I_set = ?lower"
    proof (rule set_eqI, rule iffI)
      fix p assume "p \<in> g' ` I_set"
      then obtain t where ht: "t \<in> I_set" "p = g' t" by (by100 blast)
      have htr: "0 \<le> t" "t \<le> 1" using ht(1) unfolding top1_unit_interval_def by auto
      have "fst p ^ 2 + snd p ^ 2 = 1"
        unfolding ht(2) g'_def by (simp add: sin_cos_squared_add2)
      moreover have "snd p = sin (pi + pi * t)" unfolding ht(2) g'_def by simp
      moreover have "sin (pi + pi * t) \<le> 0"
      proof -
        have "pi + pi * t \<ge> pi" using htr(1) pi_ge_zero by auto
        moreover have "pi + pi * t \<le> 2 * pi" using htr(2) pi_ge_zero by auto
        ultimately have "sin (pi + pi * t) = - sin (pi * t)"
          by (simp add: sin_add)
        moreover have "sin (pi * t) \<ge> 0"
          using sin_ge_zero htr pi_ge_zero by (auto intro: mult_nonneg_nonneg)
        ultimately show ?thesis by (by100 linarith)
      qed
      ultimately show "p \<in> ?lower" unfolding top1_S1_def by auto
    next
      fix p assume hp: "p \<in> ?lower"
      have hpS1: "fst p ^ 2 + snd p ^ 2 = 1" using hp unfolding top1_S1_def by auto
      have hle: "snd p \<le> 0" using hp by (by100 simp)
      \<comment> \<open>Find t with g'(t) = p. Use t = (arccos(fst p) - \<pi>) / \<pi> if arccos \<ge> \<pi>,
         i.e., t = (2\<pi> - arccos(fst p)) / \<pi> - 1 = 1 - arccos(fst p)/\<pi>.\<close>
      define t where "t = 1 - arccos (fst p) / pi"
      have hfst_range: "-1 \<le> fst p" "fst p \<le> 1"
      proof -
        have "snd p ^ 2 \<ge> 0" by simp
        hence hfp2: "fst p ^ 2 \<le> 1" using hpS1 by (by100 linarith)
        show "fst p \<le> 1"
        proof (rule ccontr)
          assume "\<not> fst p \<le> 1"
          hence "fst p ^ 2 > 1" unfolding power2_eq_square
            using mult_strict_mono'[of 1 "fst p" 1 "fst p"] by (by100 linarith)
          thus False using hfp2 by (by100 linarith)
        qed
        show "-1 \<le> fst p"
        proof (rule ccontr)
          assume "\<not> -1 \<le> fst p"
          hence "(-fst p) > 1" by simp
          hence "(-fst p)^2 > 1" unfolding power2_eq_square
            using mult_strict_mono'[of 1 "-fst p" 1 "-fst p"] by (by100 linarith)
          hence "fst p ^ 2 > 1" by (simp add: power2_eq_square)
          thus False using hfp2 by (by100 linarith)
        qed
      qed
      have ht_ge: "0 \<le> t"
      proof -
        have "arccos (fst p) \<le> pi" by (rule arccos_ubound[OF hfst_range(1) hfst_range(2)])
        thus ?thesis unfolding t_def using pi_gt_zero by (by100 simp)
      qed
      have ht_le: "t \<le> 1"
      proof -
        have "0 \<le> arccos (fst p)" by (rule arccos_lbound[OF hfst_range(1) hfst_range(2)])
        thus ?thesis unfolding t_def using pi_gt_zero by (by100 simp)
      qed
      have hpi_t: "pi + pi * t = 2 * pi - arccos (fst p)"
        unfolding t_def using pi_gt_zero by (simp add: field_simps)
      have hcos: "cos (pi + pi * t) = fst p"
      proof -
        have "cos (pi + pi * t) = cos (2 * pi - arccos (fst p))" using hpi_t by simp
        also have "... = cos (arccos (fst p))"
          by (simp add: cos_diff cos_int_2pin sin_int_2pin)
        also have "... = fst p" using cos_arccos[OF hfst_range(1) hfst_range(2)] .
        finally show ?thesis .
      qed
      have hsin: "sin (pi + pi * t) = snd p"
      proof -
        have "sin (pi + pi * t) \<le> 0"
        proof -
          have "sin (pi + pi * t) = - sin (pi * t)" by (simp add: sin_add)
          moreover have "sin (pi * t) \<ge> 0"
            using sin_ge_zero ht_ge ht_le pi_ge_zero by (auto intro: mult_nonneg_nonneg)
          ultimately show ?thesis by (by100 linarith)
        qed
        have "sin (pi + pi * t) ^ 2 = 1 - cos (pi + pi * t) ^ 2"
          using sin_cos_squared_add[of "pi + pi * t"] by (by100 linarith)
        also have "... = 1 - fst p ^ 2" using hcos by simp
        also have "... = snd p ^ 2" using hpS1 by (by100 linarith)
        finally have "sin (pi + pi * t) ^ 2 = snd p ^ 2" .
        have hns: "-sin (pi + pi * t) \<ge> 0" using \<open>sin (pi + pi * t) \<le> 0\<close> by (by100 linarith)
        have hnp: "-snd p \<ge> 0" using hle by (by100 linarith)
        have "(-sin (pi + pi * t)) ^ 2 = (-snd p) ^ 2"
          using \<open>sin (pi + pi * t) ^ 2 = snd p ^ 2\<close> by (simp add: power2_eq_square)
        hence "-sin (pi + pi * t) = -snd p"
          using power2_eq_iff_nonneg[OF hns hnp] by simp
        thus "sin (pi + pi * t) = snd p" by (by100 linarith)
      qed
      have "p = g' t" unfolding g'_def using hcos hsin by (cases p) auto
      moreover have "t \<in> I_set" using ht_ge ht_le unfolding top1_unit_interval_def by auto
      ultimately show "p \<in> g' ` I_set" by (by100 blast)
    qed
    have hg'_inj: "inj_on g' I_set"
    proof (rule inj_onI)
      fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and heq: "g' s = g' t"
      have hsr: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
      have htr: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
      from heq have hcos: "cos (pi + pi * s) = cos (pi + pi * t)"
        unfolding g'_def by auto
      have hps: "0 \<le> pi + pi * s" "pi + pi * s \<le> 2 * pi"
        using hsr pi_ge_zero by auto
      have hpt: "0 \<le> pi + pi * t" "pi + pi * t \<le> 2 * pi"
        using htr pi_ge_zero by auto
      \<comment> \<open>cos is injective on [\<pi>, 2\<pi>]: cos(x) = cos(y) with x, y \<in> [\<pi>, 2\<pi>] implies x = y.\<close>
      have "pi + pi * s = pi + pi * t"
      proof -
        \<comment> \<open>Use cos(\<pi>+x) = -cos(x), so cos(\<pi>+\<pi>s) = cos(\<pi>+\<pi>t) gives cos(\<pi>s) = cos(\<pi>t).\<close>
        have "cos (pi * s) = cos (pi * t)"
          using hcos by (simp add: cos_add)
        have hpsr: "0 \<le> pi * s" "pi * s \<le> pi" using hsr pi_ge_zero by auto
        have hptr: "0 \<le> pi * t" "pi * t \<le> pi" using htr pi_ge_zero by auto
        have "pi * s = pi * t"
          by (rule cos_inj_pi[OF hpsr(1) hpsr(2) hptr(1) hptr(2) \<open>cos (pi * s) = cos (pi * t)\<close>])
        thus ?thesis by simp
      qed
      thus "s = t" using pi_gt_zero by (by100 simp)
    qed
    have hg'_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology g'"
    proof -
      have hg'_std: "continuous_on I_set g'" unfolding g'_def by (intro continuous_intros)
      have hg'_maps: "\<forall>t\<in>I_set. g' t \<in> top1_S1"
      proof
        fix t assume "t \<in> I_set"
        show "g' t \<in> top1_S1" unfolding g'_def top1_S1_def
          by (auto simp: sin_cos_squared_add2)
      qed
      show ?thesis unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix t assume ht: "t \<in> I_set"
        show "g' t \<in> top1_S1" using hg'_maps ht by (by100 blast)
      next
        fix V assume hV: "V \<in> top1_S1_topology"
        obtain W where hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
            and hV_eq: "V = top1_S1 \<inter> W"
          using hV unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
        have hWo: "open W" using hW product_topology_on_open_sets_real2
          unfolding top1_open_sets_def by (by100 simp)
        have hpre_eq: "{t \<in> I_set. g' t \<in> V} = I_set \<inter> g' -` W"
          using hV_eq hg'_maps by (by100 blast)
        have "open (g' -` W)"
        proof -
          have "continuous_on UNIV g'" unfolding g'_def by (intro continuous_intros)
          thus ?thesis using hWo by (simp add: continuous_on_open_vimage[OF open_UNIV])
        qed
        hence "g' -` W \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
        have "I_set \<inter> g' -` W \<in> subspace_topology UNIV top1_open_sets I_set"
          unfolding subspace_topology_def
          apply (rule CollectI)
          apply (rule exI[of _ "g' -` W"])
          using \<open>g' -` W \<in> top1_open_sets\<close> by (by100 blast)
        hence "{t \<in> I_set. g' t \<in> V} \<in> subspace_topology UNIV top1_open_sets I_set"
          using hpre_eq by simp
        thus "{t \<in> I_set. g' t \<in> V} \<in> I_top"
          unfolding top1_unit_interval_topology_def by simp
      qed
    qed
    have hfg'_cont: "top1_continuous_map_on I_set I_top X TX (f \<circ> g')"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix t assume ht: "t \<in> I_set"
      have "g' t \<in> top1_S1" using hg'_cont ht unfolding top1_continuous_map_on_def by (by100 blast)
      thus "(f \<circ> g') t \<in> X" using hf_cont unfolding top1_continuous_map_on_def comp_def by (by100 blast)
    next
      fix V assume hV: "V \<in> TX"
      have hpre_f: "{x \<in> top1_S1. f x \<in> V} \<in> top1_S1_topology"
        using hf_cont hV unfolding top1_continuous_map_on_def by (by100 blast)
      have hpre_g: "{t \<in> I_set. g' t \<in> {x \<in> top1_S1. f x \<in> V}} \<in> I_top"
        using hg'_cont hpre_f unfolding top1_continuous_map_on_def by (by100 blast)
      have "{t \<in> I_set. (f \<circ> g') t \<in> V} = {t \<in> I_set. g' t \<in> {x \<in> top1_S1. f x \<in> V}}"
      proof (rule set_eqI, rule iffI)
        fix t assume "t \<in> {t \<in> I_set. (f \<circ> g') t \<in> V}"
        hence ht: "t \<in> I_set" and hfgt: "f (g' t) \<in> V" unfolding comp_def by auto
        have "g' t \<in> top1_S1" using hg'_cont ht unfolding top1_continuous_map_on_def by (by100 blast)
        thus "t \<in> {t \<in> I_set. g' t \<in> {x \<in> top1_S1. f x \<in> V}}" using ht hfgt by (by100 blast)
      next
        fix t assume "t \<in> {t \<in> I_set. g' t \<in> {x \<in> top1_S1. f x \<in> V}}"
        thus "t \<in> {t \<in> I_set. (f \<circ> g') t \<in> V}" unfolding comp_def by (by100 blast)
      qed
      thus "{t \<in> I_set. (f \<circ> g') t \<in> V} \<in> I_top" using hpre_g by simp
    qed
    have hfg'_inj: "inj_on (f \<circ> g') I_set"
    proof (rule inj_onI)
      fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and heq: "(f \<circ> g') s = (f \<circ> g') t"
      have hgs: "g' s \<in> ?lower" using hs hg'_img by (by100 blast)
      have hgt: "g' t \<in> ?lower" using ht hg'_img by (by100 blast)
      have hgsS1: "g' s \<in> top1_S1" using hgs by (by100 simp)
      have hgtS1: "g' t \<in> top1_S1" using hgt by (by100 simp)
      hence "g' s = g' t" using hf_inj hgsS1 heq unfolding comp_def inj_on_def by (by100 blast)
      thus "s = t" using hg'_inj hs ht unfolding inj_on_def by (by100 blast)
    qed
    have hfg'_img: "(f \<circ> g') ` I_set = ?A2"
    proof -
      have "(f \<circ> g') ` I_set = f ` (g' ` I_set)" by (by100 auto)
      also have "... = f ` ?lower" using hg'_img by simp
      finally show ?thesis .
    qed
    have hA2_sub: "?A2 \<subseteq> X"
    proof -
      have "\<forall>x \<in> top1_S1. f x \<in> X" using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
      moreover have "?lower \<subseteq> top1_S1" by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    have hA2_haus: "is_hausdorff_on ?A2 (subspace_topology X TX ?A2)"
      by (rule hausdorff_subspace[OF hH hA2_sub])
    have hTA2: "is_topology_on ?A2 (subspace_topology X TX ?A2)"
      by (rule subspace_topology_is_topology_on[OF hTX hA2_sub])
    have hfg'_bij: "bij_betw (f \<circ> g') I_set ?A2"
      unfolding bij_betw_def using hfg'_inj hfg'_img by (by100 blast)
    have hfg'_cont_A2: "top1_continuous_map_on I_set I_top ?A2 (subspace_topology X TX ?A2) (f \<circ> g')"
    proof -
      have hTI: "is_topology_on I_set I_top"
        unfolding top1_unit_interval_topology_def
        by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV])
          (by100 simp)
      have h_rr: "\<forall>W g''. top1_continuous_map_on I_set I_top X TX g''
          \<and> W \<subseteq> X \<and> g'' ` I_set \<subseteq> W
          \<longrightarrow> top1_continuous_map_on I_set I_top W (subspace_topology X TX W) g''"
        by (rule Theorem_18_2(5)[OF hTI hTX hTX])
      have h_rr_inst: "top1_continuous_map_on I_set I_top X TX (f \<circ> g')
          \<and> ?A2 \<subseteq> X \<and> (f \<circ> g') ` I_set \<subseteq> ?A2
          \<longrightarrow> top1_continuous_map_on I_set I_top ?A2 (subspace_topology X TX ?A2) (f \<circ> g')"
        using h_rr[THEN spec, THEN spec] by (by100 simp)
      thus ?thesis using hfg'_cont hA2_sub hfg'_img by (by100 blast)
    qed
    have hI_compact: "top1_compact_on I_set I_top"
    proof -
      have "compact {0..1::real}" by (rule compact_Icc)
      have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
        by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
      have "compact I_set" using \<open>compact {0..1::real}\<close> hI01 by simp
      have "top1_compact_on I_set (subspace_topology (UNIV::real set) top1_open_sets I_set)"
        using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
      thus ?thesis unfolding top1_unit_interval_topology_def by simp
    qed
    have hI_top: "is_topology_on I_set I_top"
      using hI_compact unfolding top1_compact_on_def by (by100 blast)
    have hfg'_homeo: "top1_homeomorphism_on I_set I_top ?A2 (subspace_topology X TX ?A2) (f \<circ> g')"
      by (rule Theorem_26_6[OF hI_top hTA2 hI_compact hA2_haus hfg'_cont_A2 hfg'_bij])
    have hA2_strict: "is_topology_on_strict ?A2 (subspace_topology X TX ?A2)"
      by (rule subspace_topology_is_strict[OF hT hA2_sub])
    show ?thesis unfolding top1_is_arc_on_def using hA2_strict hfg'_homeo by (by100 blast)
  qed
  show ?thesis
    using hC_decomp hinter_img hab_ne hA1_arc hA2_arc by (by100 blast)
qed

lemma S1_compact: "top1_compact_on top1_S1 top1_S1_topology"
proof -
  have hS1_img: "top1_R_to_S1 ` {0..1::real} = top1_S1"
  proof (rule set_eqI, rule iffI)
    fix p assume "p \<in> top1_R_to_S1 ` {0..1}"
    then obtain t where "t \<in> {0..1}" "p = top1_R_to_S1 t" by (by100 blast)
    thus "p \<in> top1_S1" unfolding top1_R_to_S1_def top1_S1_def
      by (auto simp: power2_eq_square[symmetric] sin_cos_squared_add2)
  next
    fix p assume "p \<in> top1_S1"
    have "p \<in> top1_R_to_S1 ` UNIV"
      using top1_covering_map_on_surj[OF Theorem_53_1] \<open>p \<in> top1_S1\<close> by (by100 blast)
    then obtain t :: real where "p = top1_R_to_S1 t" by (by100 blast)
    define t' where "t' = t - of_int \<lfloor>t\<rfloor>"
    have "t' \<ge> 0 \<and> t' < 1" unfolding t'_def by linarith
    have "top1_R_to_S1 t' = top1_R_to_S1 t"
    proof -
      have h_eq: "2 * pi * t' = 2 * pi * t - (2 * pi) * of_int \<lfloor>t\<rfloor>" unfolding t'_def by (simp add: algebra_simps)
      have hcos: "cos (2 * pi * t') = cos (2 * pi * t)"
      proof -
        have "cos (2 * pi * t') = cos (2 * pi * t - (2 * pi) * of_int \<lfloor>t\<rfloor>)" using h_eq by simp
        also have "... = cos (2 * pi * t) * cos ((2 * pi) * of_int \<lfloor>t\<rfloor>)
            + sin (2 * pi * t) * sin ((2 * pi) * of_int \<lfloor>t\<rfloor>)" by (rule cos_diff)
        also have "... = cos (2 * pi * t)" by (simp add: cos_int_2pin sin_int_2pin)
        finally show ?thesis .
      qed
      have hsin: "sin (2 * pi * t') = sin (2 * pi * t)"
      proof -
        have "sin (2 * pi * t') = sin (2 * pi * t - (2 * pi) * of_int \<lfloor>t\<rfloor>)" using h_eq by simp
        also have "... = sin (2 * pi * t) * cos ((2 * pi) * of_int \<lfloor>t\<rfloor>)
            - cos (2 * pi * t) * sin ((2 * pi) * of_int \<lfloor>t\<rfloor>)" by (rule sin_diff)
        also have "... = sin (2 * pi * t)" by (simp add: cos_int_2pin sin_int_2pin)
        finally show ?thesis .
      qed
      show ?thesis unfolding top1_R_to_S1_def using hcos hsin by (simp add: prod_eq_iff)
    qed
    hence "p = top1_R_to_S1 t'" using \<open>p = top1_R_to_S1 t\<close> by simp
    moreover have "t' \<in> {0..1}" using \<open>t' \<ge> 0 \<and> t' < 1\<close> by auto
    ultimately show "p \<in> top1_R_to_S1 ` {0..1}" by (by100 blast)
  qed
  have hcont_S1: "continuous_on {0..1::real} top1_R_to_S1"
    unfolding top1_R_to_S1_def by (intro continuous_intros)
  have "compact (top1_R_to_S1 ` {0..1::real})"
    using compact_continuous_image[OF hcont_S1] compact_Icc by simp
  hence "compact top1_S1" using hS1_img by simp
  have "top1_compact_on top1_S1 (subspace_topology (UNIV::(real\<times>real) set) top1_open_sets top1_S1)"
    using top1_compact_on_subspace_UNIV_iff_compact[of top1_S1] \<open>compact top1_S1\<close> by simp
  moreover have "(top1_open_sets::(real\<times>real) set set)
      = product_topology_on (top1_open_sets::real set set) top1_open_sets"
    using product_topology_on_open_sets_real2 by (by100 metis)
  ultimately show ?thesis unfolding top1_S1_topology_def by simp
qed

lemma simple_closed_curve_proper_subset:
  assumes "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  shows "C \<noteq> top1_S2"
proof
  assume hCeq: "C = top1_S2"
  \<comment> \<open>f: S^1 \<rightarrow> S^2 injective continuous with f(S^1) = C = S^2. So f is bijective.\<close>
  obtain f where hf_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S2 top1_S2_topology f"
      and hf_inj: "inj_on f top1_S1" and hf_img: "f ` top1_S1 = C"
    using assms unfolding top1_simple_closed_curve_on_def by (by100 blast)
  have hf_surj: "f ` top1_S1 = top1_S2" using hf_img hCeq by simp
  \<comment> \<open>f: S^1 \<rightarrow> S^2 bijective continuous (compact to Hausdorff = homeomorphism).
     If homeomorphic, removing 2 points preserves homeomorphism type.
     S^1 - {(1,0), (-1,0)} = two disjoint arcs (NOT connected).
     S^2 - {f(1,0), f(-1,0)} \<cong> R^2 - {pt} (connected, by S2_minus_point_homeo_R2).
     Contradiction: homeomorphic spaces should both be connected or not.\<close>
  \<comment> \<open>S^2 minus two points is connected (path-connected even).\<close>
  have hp1: "(1::real,0::real) \<in> top1_S1" unfolding top1_S1_def by simp
  have hp2: "(-1::real,0::real) \<in> top1_S1" unfolding top1_S1_def by simp
  have hfp1_S2: "f (1,0) \<in> top1_S2" using hf_surj hp1 by (by100 blast)
  have hfp2_S2: "f (-1,0) \<in> top1_S2" using hf_surj hp2 by (by100 blast)
  have hfp_ne: "f (1,0) \<noteq> f (-1,0)"
  proof
    assume "f (1,0) = f (-1,0)"
    hence "(1::real,0::real) = (-1,0)" using hf_inj hp1 hp2 unfolding inj_on_def by (by100 blast)
    thus False by simp
  qed
  \<comment> \<open>S^2 - {f(1,0), f(-1,0)} is path-connected (hence connected).\<close>
  have hS2_2pts_pc: "top1_path_connected_on (top1_S2 - {f(1,0), f(-1,0)})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {f(1,0), f(-1,0)}))"
  proof -
    \<comment> \<open>Step 1: S^2-{f(1,0)} \<cong> R^2.\<close>
    obtain h where hh: "top1_homeomorphism_on (top1_S2 - {f(1,0)})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {f(1,0)}))
        (UNIV :: (real \<times> real) set)
        (product_topology_on top1_open_sets top1_open_sets) h"
      using S2_minus_point_homeo_R2[OF hfp1_S2] by blast
    \<comment> \<open>Step 2: Restrict to S^2-{f(1,0),f(-1,0)} \<cong> R^2-{h(f(-1,0))}.\<close>
    have hfp2_in: "f(-1,0) \<in> top1_S2 - {f(1,0)}" using hfp2_S2 hfp_ne[symmetric] by (by100 blast)
    have hh_restrict: "top1_homeomorphism_on (top1_S2 - {f(1,0)} - {f(-1,0)})
        (subspace_topology (top1_S2 - {f(1,0)})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {f(1,0)}))
          (top1_S2 - {f(1,0)} - {f(-1,0)}))
        (UNIV - {h(f(-1,0))})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
          (UNIV - {h(f(-1,0))}))
        h"
      by (rule homeomorphism_restrict_point[OF hh hfp2_in])
    have hset_eq: "top1_S2 - {f(1,0)} - {f(-1,0)} = top1_S2 - {f(1,0), f(-1,0)}" by (by100 blast)
    have htop_eq: "subspace_topology (top1_S2 - {f(1,0)})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {f(1,0)}))
        (top1_S2 - {f(1,0), f(-1,0)})
        = subspace_topology top1_S2 top1_S2_topology (top1_S2 - {f(1,0), f(-1,0)})"
      by (rule subspace_topology_trans) (by100 blast)
    have hh2: "top1_homeomorphism_on (top1_S2 - {f(1,0), f(-1,0)})
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {f(1,0), f(-1,0)}))
        (UNIV - {h(f(-1,0))})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
          (UNIV - {h(f(-1,0))})) h"
      using hh_restrict hset_eq htop_eq by simp
    \<comment> \<open>Step 3: R^2-{h(f(-1,0))} is path-connected.\<close>
    have hR2_pc: "top1_path_connected_on (UNIV - {h(f(-1,0))})
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
          (UNIV - {h(f(-1,0))}))"
      by (rule R2_minus_point_path_connected) simp
    \<comment> \<open>Step 4: Transfer path-connected via inverse homeomorphism.\<close>
    show ?thesis
      by (rule homeomorphism_preserves_path_connected[OF homeomorphism_inverse[OF hh2] hR2_pc])
  qed
  \<comment> \<open>S^1 - {(1,0), (-1,0)} = upper \<union> lower open arcs, which are disjoint and nonempty.\<close>
  have hS1_2pts_not_conn: "\<not> top1_connected_on (top1_S1 - {(1::real,0), (-1,0)})
      (subspace_topology top1_S1 top1_S1_topology (top1_S1 - {(1,0), (-1,0)}))"
  proof
    assume hconn: "top1_connected_on (top1_S1 - {(1,0), (-1,0)})
        (subspace_topology top1_S1 top1_S1_topology (top1_S1 - {(1,0), (-1,0)}))"
    let ?S = "top1_S1 - {(1::real,0), (-1,0)}"
    let ?TS = "subspace_topology top1_S1 top1_S1_topology ?S"
    let ?U = "{p \<in> ?S. snd p > 0}" and ?V = "{p \<in> ?S. snd p < 0}"
    have hne_U: "(0::real, 1) \<in> ?U" unfolding top1_S1_def by simp
    have hne_V: "(0::real, -1) \<in> ?V" unfolding top1_S1_def by simp
    have hdisj: "?U \<inter> ?V = {}" by auto
    have hcover: "?U \<union> ?V = ?S"
    proof (rule set_eqI, rule iffI)
      fix p assume "p \<in> ?U \<union> ?V" thus "p \<in> ?S" by auto
    next
      fix p assume hp: "p \<in> ?S"
      have hp_S1: "fst p ^ 2 + snd p ^ 2 = 1" using hp unfolding top1_S1_def by auto
      have "snd p \<noteq> 0"
      proof
        assume "snd p = 0"
        hence "fst p ^ 2 = 1" using hp_S1 by simp
        hence "fst p = 1 \<or> fst p = -1" by (simp add: power2_eq_1_iff)
        thus False using hp \<open>snd p = 0\<close> by (cases p) auto
      qed
      thus "p \<in> ?U \<union> ?V" using hp by auto
    qed
    have hU_open: "?U \<in> ?TS"
    proof -
      \<comment> \<open>?TS = {?S \<inter> U | U. U \<in> top1_S1_topology}
           top1_S1_topology = {top1_S1 \<inter> V | V. V \<in> product_topology_on ...}
           Take V = {p. snd p > 0}, open in R^2.\<close>
      have ho: "open {p :: real \<times> real. snd p > 0}"
      proof -
        have "{p :: real \<times> real. snd p > 0} = UNIV \<times> {y :: real. y > 0}"
          by auto
        moreover have "open (UNIV \<times> {y :: real. y > 0})"
          by (rule open_Times) (auto simp: greaterThan_def[symmetric])
        ultimately show ?thesis by (by100 simp)
      qed
      have hV_S1top: "top1_S1 \<inter> {p :: real \<times> real. snd p > 0} \<in> top1_S1_topology"
      proof -
        have h1: "{p :: real \<times> real. snd p > 0} \<in> (top1_open_sets :: (real \<times> real) set set)"
          using ho unfolding top1_open_sets_def by (by100 blast)
        have h2: "{p :: real \<times> real. snd p > 0} \<in> product_topology_on top1_open_sets top1_open_sets"
          using h1 product_topology_on_open_sets_real2 by (by100 simp)
        thus ?thesis unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      qed
      have heq: "?U = ?S \<inter> (top1_S1 \<inter> {p :: real \<times> real. snd p > 0})"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> ?U"
        hence "x \<in> ?S" "snd x > 0" by (by100 blast)+
        moreover hence "x \<in> top1_S1" by (by100 blast)
        ultimately show "x \<in> ?S \<inter> (top1_S1 \<inter> {p. snd p > 0})" by (by100 blast)
      next
        fix x assume "x \<in> ?S \<inter> (top1_S1 \<inter> {p. snd p > 0})"
        thus "x \<in> ?U" by (by100 blast)
      qed
      show ?thesis unfolding subspace_topology_def heq
        apply (rule CollectI)
        apply (rule exI[of _ "top1_S1 \<inter> {p :: real \<times> real. snd p > 0}"])
        using hV_S1top by (by100 simp)
    qed
    have hV_open: "?V \<in> ?TS"
    proof -
      have ho: "open {p :: real \<times> real. snd p < 0}"
      proof -
        have "{p :: real \<times> real. snd p < 0} = UNIV \<times> {y :: real. y < 0}"
          by auto
        moreover have "open (UNIV \<times> {y :: real. y < 0})"
          by (rule open_Times) (auto simp: lessThan_def[symmetric])
        ultimately show ?thesis by (by100 simp)
      qed
      have hV_S1top: "top1_S1 \<inter> {p :: real \<times> real. snd p < 0} \<in> top1_S1_topology"
      proof -
        have h1: "{p :: real \<times> real. snd p < 0} \<in> (top1_open_sets :: (real \<times> real) set set)"
          using ho unfolding top1_open_sets_def by (by100 blast)
        have h2: "{p :: real \<times> real. snd p < 0} \<in> product_topology_on top1_open_sets top1_open_sets"
          using h1 product_topology_on_open_sets_real2 by (by100 simp)
        thus ?thesis unfolding top1_S1_topology_def subspace_topology_def by (by100 blast)
      qed
      have heq: "?V = ?S \<inter> (top1_S1 \<inter> {p :: real \<times> real. snd p < 0})"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> ?V"
        hence "x \<in> ?S" "snd x < 0" by (by100 blast)+
        moreover hence "x \<in> top1_S1" by (by100 blast)
        ultimately show "x \<in> ?S \<inter> (top1_S1 \<inter> {p. snd p < 0})" by (by100 blast)
      next
        fix x assume "x \<in> ?S \<inter> (top1_S1 \<inter> {p. snd p < 0})"
        thus "x \<in> ?V" by (by100 blast)
      qed
      show ?thesis unfolding subspace_topology_def heq
        apply (rule CollectI)
        apply (rule exI[of _ "top1_S1 \<inter> {p :: real \<times> real. snd p < 0}"])
        using hV_S1top by (by100 simp)
    qed
    from hconn have hno_sep: "\<nexists>U V. U \<in> ?TS \<and> V \<in> ?TS \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = ?S"
      unfolding top1_connected_on_def by (by100 blast)
    have hUne: "?U \<noteq> {}" using hne_U by (by100 blast)
    have hVne: "?V \<noteq> {}" using hne_V by (by100 blast)
    have "\<exists>U V. U \<in> ?TS \<and> V \<in> ?TS \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = ?S"
      apply (rule exI[of _ ?U])
      apply (rule exI[of _ ?V])
      apply (intro conjI)
      apply (rule hU_open) apply (rule hV_open)
      apply (rule hUne) apply (rule hVne)
      apply (rule hdisj) apply (rule hcover)
      done
    thus False using hno_sep by contradiction
  qed
  \<comment> \<open>If f: S^1 \<rightarrow> S^2 homeomorphism, then f restricts to
     S^1 - {p1,p2} \<cong> S^2 - {f(p1),f(p2)}. Connected is preserved.\<close>
  \<comment> \<open>f: S^1 \<rightarrow> S^2 is a homeomorphism (compact to Hausdorff bijection).\<close>
  have hS1_compact: "top1_compact_on top1_S1 top1_S1_topology" by (rule S1_compact)
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology"
    by (rule top1_S2_is_hausdorff)
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
  proof -
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using product_topology_on_is_topology_on[OF hTR hTR] by simp
    show ?thesis unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
  qed
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
  have hf_bij: "bij_betw f top1_S1 top1_S2"
    unfolding bij_betw_def using hf_inj hf_surj by (by100 blast)
  have hf_homeo: "top1_homeomorphism_on top1_S1 top1_S1_topology top1_S2 top1_S2_topology f"
    by (rule Theorem_26_6[OF hTS1 hTS2 hS1_compact hS2_haus hf_cont hf_bij])
  \<comment> \<open>f^{-1}: S^2 \<rightarrow> S^1 is continuous.\<close>
  have hfinv_homeo: "top1_homeomorphism_on top1_S2 top1_S2_topology top1_S1 top1_S1_topology
      (inv_into top1_S1 f)"
    by (rule homeomorphism_inverse[OF hf_homeo])
  have hfinv_cont: "top1_continuous_map_on top1_S2 top1_S2_topology top1_S1 top1_S1_topology
      (inv_into top1_S1 f)"
    using hfinv_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
  \<comment> \<open>Restrict f^{-1} to S^2-{f(1,0),f(-1,0)} \<rightarrow> S^1-{(1,0),(-1,0)}.\<close>
  let ?S2_2 = "top1_S2 - {f(1,0), f(-1,0)}" and ?S1_2 = "top1_S1 - {(1::real,0), (-1,0)}"
  have hfinv_bij: "bij_betw (inv_into top1_S1 f) top1_S2 top1_S1"
    using hfinv_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
  have hfinv_img: "inv_into top1_S1 f ` ?S2_2 = ?S1_2"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> inv_into top1_S1 f ` ?S2_2"
    then obtain y where hy: "y \<in> ?S2_2" "x = inv_into top1_S1 f y" by (by100 blast)
    have hyS2: "y \<in> top1_S2" using hy(1) by (by100 blast)
    have hxS1: "x \<in> top1_S1" using hfinv_bij hyS2 hy(2) unfolding bij_betw_def by (by100 blast)
    have "f x = y" using bij_betw_inv_into_right[OF hf_bij hyS2] hy(2) by simp
    hence "x \<noteq> (1,0) \<and> x \<noteq> (-1,0)" using hy(1) by auto
    thus "x \<in> ?S1_2" using hxS1 by (by100 blast)
  next
    fix x assume hx: "x \<in> ?S1_2"
    have hxS1: "x \<in> top1_S1" using hx by (by100 blast)
    have hfx: "f x \<in> top1_S2" using hf_surj hxS1 by (by100 blast)
    have "inv_into top1_S1 f (f x) = x"
      using inv_into_f_f[OF _ hxS1] hf_inj by (by100 blast)
    moreover have "f x \<in> ?S2_2"
    proof -
      have "f x \<noteq> f (1,0)" using hf_inj hxS1 hp1 hx unfolding inj_on_def by (by100 blast)
      moreover have "f x \<noteq> f (-1,0)" using hf_inj hxS1 hp2 hx unfolding inj_on_def by (by100 blast)
      ultimately show ?thesis using hfx by (by100 blast)
    qed
    ultimately show "x \<in> inv_into top1_S1 f ` ?S2_2"
      apply (rule_tac x="f x" in image_eqI)
      apply simp
      apply assumption
      done
  qed
  \<comment> \<open>f^{-1} restricted to S^2-2pts \<rightarrow> S^1-2pts is continuous (restriction of continuous).\<close>
  have hfinv_cont_restr: "top1_continuous_map_on ?S2_2
      (subspace_topology top1_S2 top1_S2_topology ?S2_2)
      top1_S1 top1_S1_topology (inv_into top1_S1 f)"
  proof -
    have h_sub: "?S2_2 \<subseteq> top1_S2" by (by100 blast)
    have h18: "\<forall>A f. top1_continuous_map_on top1_S2 top1_S2_topology top1_S1 top1_S1_topology f
        \<and> A \<subseteq> top1_S2
        \<longrightarrow> top1_continuous_map_on A (subspace_topology top1_S2 top1_S2_topology A)
              top1_S1 top1_S1_topology f"
      by (rule Theorem_18_2(4)[OF hTS2 hTS1 hTS1])
    show ?thesis unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume hx: "x \<in> ?S2_2"
      show "inv_into top1_S1 f x \<in> top1_S1"
        using hfinv_bij hx unfolding bij_betw_def by (by100 blast)
    next
      fix V assume hV: "V \<in> top1_S1_topology"
      have hpre: "{x \<in> top1_S2. inv_into top1_S1 f x \<in> V} \<in> top1_S2_topology"
        using hfinv_cont hV unfolding top1_continuous_map_on_def by (by100 blast)
      have "{x \<in> ?S2_2. inv_into top1_S1 f x \<in> V}
          = ?S2_2 \<inter> {x \<in> top1_S2. inv_into top1_S1 f x \<in> V}" by (by100 blast)
      thus "{x \<in> ?S2_2. inv_into top1_S1 f x \<in> V}
          \<in> subspace_topology top1_S2 top1_S2_topology ?S2_2"
        unfolding subspace_topology_def using hpre by (by100 blast)
    qed
  qed
  \<comment> \<open>S^2-2pts connected. Continuous image of connected is connected.\<close>
  have hS2_2_conn: "top1_connected_on ?S2_2
      (subspace_topology top1_S2 top1_S2_topology ?S2_2)"
    by (rule top1_path_connected_imp_connected[OF hS2_2pts_pc])
  have hTS2_2: "is_topology_on ?S2_2 (subspace_topology top1_S2 top1_S2_topology ?S2_2)"
    by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
  have hS1_2_conn: "top1_connected_on ?S1_2
      (subspace_topology top1_S1 top1_S1_topology ?S1_2)"
  proof -
    have himg_eq: "inv_into top1_S1 f ` ?S2_2 = ?S1_2" by (rule hfinv_img)
    have himg_conn: "top1_connected_on (inv_into top1_S1 f ` ?S2_2)
        (subspace_topology top1_S1 top1_S1_topology (inv_into top1_S1 f ` ?S2_2))"
      by (rule Theorem_23_5[OF hTS2_2 hTS1 hS2_2_conn hfinv_cont_restr])
    thus ?thesis using himg_eq by simp
  qed
  show False using hS1_2pts_not_conn hS1_2_conn by contradiction
qed

text \<open>Helper: paths that agree on I are path-homotopic (identity homotopy).\<close>
lemma paths_agree_on_I_path_homotopic:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX a b f"
      and heq: "\<forall>s\<in>I_set. f s = g s"
  shows "top1_path_homotopic_on X TX a b f g"
proof -
  have hg_path: "top1_is_path_on X TX a b g"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top X TX g"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix s assume "s \<in> I_set"
      thus "g s \<in> X" using heq hf unfolding top1_is_path_on_def top1_continuous_map_on_def by simp
    next
      fix V assume "V \<in> TX"
      have "{s \<in> I_set. g s \<in> V} = {s \<in> I_set. f s \<in> V}" using heq by (by100 force)
      thus "{s \<in> I_set. g s \<in> V} \<in> I_top"
        using hf \<open>V \<in> TX\<close> unfolding top1_is_path_on_def top1_continuous_map_on_def by simp
    qed
    have h0: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have h1: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    show "g 0 = a" using heq h0 hf unfolding top1_is_path_on_def by simp
    show "g 1 = b" using heq h1 hf unfolding top1_is_path_on_def by simp
  qed
  \<comment> \<open>Identity homotopy F(s,t) = f(s) = g(s). Trivially continuous (constant in t).\<close>
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = f s"
      and hFl: "\<forall>t\<in>I_set. F (0, t) = a" and hFr: "\<forall>t\<in>I_set. F (1, t) = b"
    using Lemma_51_1_path_homotopic_refl[OF hf]
    unfolding top1_path_homotopic_on_def by blast
  have "\<forall>s\<in>I_set. F (s, 1) = g s" using hF1 heq by simp
  show ?thesis unfolding top1_path_homotopic_on_def
    apply (intro conjI)
    apply (rule hf)
    apply (rule hg_path)
    apply (rule exI[of _ F])
    using hF hF0 \<open>\<forall>s\<in>I_set. F (s, 1) = g s\<close> hFl hFr
    apply (intro conjI)
    apply assumption+
    done
qed

text \<open>Helper: a loop f: I \<rightarrow> X at x0 factors through S^1 via the standard covering map.
  There exists h: S^1 \<rightarrow> X continuous with h(1,0) = x0 and f = h \<circ> top1_R_to_S1 on I.\<close>
lemma loop_factors_through_S1:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_loop_on X TX x0 f"
  shows "\<exists>h. top1_continuous_map_on top1_S1 top1_S1_topology X TX h
           \<and> h (1, 0) = x0
           \<and> (\<forall>s\<in>I_set. f s = h (top1_R_to_S1 s))"
proof -
  \<comment> \<open>top1_R_to_S1 restricted to I is a quotient map I \<rightarrow> S^1.
     (Compact \<rightarrow> Hausdorff continuous surjection is closed map, hence quotient map.)\<close>
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have hp_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology top1_R_to_S1"
  proof -
    have "top1_continuous_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
      using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
    hence "top1_continuous_map_on I_set (subspace_topology UNIV top1_open_sets I_set) top1_S1 top1_S1_topology top1_R_to_S1"
      by (rule top1_continuous_map_on_restrict_domain_simple) simp
    thus ?thesis unfolding top1_unit_interval_topology_def .
  qed
  have hp_surj: "top1_R_to_S1 ` I_set = top1_S1"
  proof (rule set_eqI, rule iffI)
    fix q assume "q \<in> top1_R_to_S1 ` I_set"
    then obtain t where "t \<in> I_set" "q = top1_R_to_S1 t" by blast
    thus "q \<in> top1_S1" using hp_cont unfolding top1_continuous_map_on_def by (by100 blast)
  next
    fix q assume "q \<in> top1_S1"
    obtain x y where hq_eq: "q = (x, y)" by (cases q)
    have hcirc: "x^2 + y^2 = 1" using \<open>q \<in> top1_S1\<close> hq_eq unfolding top1_S1_def by simp
    obtain t where "0 \<le> t" "t < 2*pi" "x = cos t" "y = sin t"
      using sincos_total_2pi[OF hcirc] by blast
    define t' where "t' = t / (2*pi)"
    have "0 \<le> t'" "t' < 1" unfolding t'_def using \<open>0 \<le> t\<close> \<open>t < 2*pi\<close> pi_gt_zero by auto
    hence "t' \<in> I_set" unfolding top1_unit_interval_def by simp
    moreover have "top1_R_to_S1 t' = q"
      unfolding top1_R_to_S1_def t'_def hq_eq using \<open>x = cos t\<close> \<open>y = sin t\<close> pi_gt_zero by simp
    ultimately show "q \<in> top1_R_to_S1 ` I_set" by (by100 blast)
  qed
  \<comment> \<open>Quotient map property: top1_R_to_S1 is a quotient map I \<rightarrow> S^1.\<close>
  have hp_quot: "top1_quotient_map_on I_set I_top top1_S1 top1_S1_topology top1_R_to_S1"
    unfolding top1_quotient_map_on_def
  proof (intro conjI)
    show "is_topology_on I_set I_top" by (rule hTI)
    show "is_topology_on top1_S1 top1_S1_topology"
      unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF
          product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
            top1_open_sets_is_topology_on_UNIV, simplified]]) simp
    show "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology top1_R_to_S1" by (rule hp_cont)
    show "top1_R_to_S1 ` I_set = top1_S1" by (rule hp_surj)
    \<comment> \<open>Quotient condition: V \<subseteq> S^1 with p^{-1}(V) open in I \<Rightarrow> V open in S^1.
       Equivalently by complement: A closed in I \<Rightarrow> p(A) closed in S^1.
       I compact, S^1 Hausdorff, p continuous \<Rightarrow> p is a closed map.\<close>
    show "\<forall>V. V \<subseteq> top1_S1 \<longrightarrow> ({x \<in> I_set. top1_R_to_S1 x \<in> V} \<in> I_top \<longrightarrow> V \<in> top1_S1_topology)"
    proof (intro allI impI)
      fix V assume hVsub: "V \<subseteq> top1_S1" and hpreV: "{x \<in> I_set. top1_R_to_S1 x \<in> V} \<in> I_top"
      \<comment> \<open>Want: V open in S^1. Equivalently: S^1-V closed in S^1.
         Since p is a closed map: p(I-p^{-1}(V)) = S^1-V is closed.\<close>
      have hI_comp: "top1_compact_on I_set I_top"
      proof -
        have "compact {0..1::real}" by (rule compact_Icc)
        have "I_set = {0..1::real}" unfolding top1_unit_interval_def
          by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
        have "compact I_set" using \<open>compact {0..1::real}\<close> \<open>I_set = _\<close> by simp
        have "top1_compact_on I_set (subspace_topology UNIV top1_open_sets I_set)"
          using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
        thus ?thesis unfolding top1_unit_interval_topology_def by simp
      qed
      have hS1_haus: "is_hausdorff_on top1_S1 top1_S1_topology"
        by (rule top1_S1_is_hausdorff)
      \<comment> \<open>I - p^{-1}(V) is closed in I (complement of open set).\<close>
      have hA_closed: "closedin_on I_set I_top (I_set - {x \<in> I_set. top1_R_to_S1 x \<in> V})"
        unfolding closedin_on_def
      proof (intro conjI)
        show "I_set - {x \<in> I_set. top1_R_to_S1 x \<in> V} \<subseteq> I_set" by (by100 blast)
        have "I_set - (I_set - {x \<in> I_set. top1_R_to_S1 x \<in> V}) = {x \<in> I_set. top1_R_to_S1 x \<in> V}"
          by (by100 blast)
        thus "I_set - (I_set - {x \<in> I_set. top1_R_to_S1 x \<in> V}) \<in> I_top" using hpreV by simp
      qed
      \<comment> \<open>p(A) is closed in S^1 (closed map property).\<close>
      have "closedin_on top1_S1 top1_S1_topology
          (top1_R_to_S1 ` (I_set - {x \<in> I_set. top1_R_to_S1 x \<in> V}))"
        by (rule compact_hausdorff_continuous_closed_map[OF hI_comp hS1_haus hp_cont hA_closed])
      \<comment> \<open>p(A) = S^1 - V.\<close>
      moreover have "top1_R_to_S1 ` (I_set - {x \<in> I_set. top1_R_to_S1 x \<in> V}) = top1_S1 - V"
      proof (rule set_eqI, rule iffI)
        fix y assume "y \<in> top1_R_to_S1 ` (I_set - {x \<in> I_set. top1_R_to_S1 x \<in> V})"
        then obtain x where hx: "x \<in> I_set" "top1_R_to_S1 x \<notin> V" "y = top1_R_to_S1 x" by (by100 blast)
        have "y \<in> top1_S1" using hx(1,3) hp_surj by (by100 blast)
        moreover have "y \<notin> V" using hx(2,3) by simp
        ultimately show "y \<in> top1_S1 - V" by (by100 blast)
      next
        fix y assume "y \<in> top1_S1 - V"
        hence "y \<in> top1_S1" "y \<notin> V" by auto
        hence "y \<in> top1_R_to_S1 ` I_set" using hp_surj by simp
        then obtain x where "x \<in> I_set" "top1_R_to_S1 x = y" by (by100 blast)
        thus "y \<in> top1_R_to_S1 ` (I_set - {x \<in> I_set. top1_R_to_S1 x \<in> V})"
          using \<open>y \<notin> V\<close> by (by100 blast)
      qed
      ultimately have "closedin_on top1_S1 top1_S1_topology (top1_S1 - V)" by simp
      \<comment> \<open>S^1 - V closed \<Rightarrow> V open.\<close>
      hence "top1_S1 - (top1_S1 - V) \<in> top1_S1_topology"
        unfolding closedin_on_def by (by100 blast)
      moreover have "top1_S1 - (top1_S1 - V) = V" using hVsub by (by100 blast)
      ultimately show "V \<in> top1_S1_topology" by simp
    qed
  qed
  \<comment> \<open>f is constant on fibers: the only non-trivial fiber is {0,1} \<mapsto> (1,0),
     and f(0) = f(1) = x0.\<close>
  have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  have hf0: "f 0 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  have hf1: "f 1 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  have hf_fiber: "\<forall>s\<in>I_set. \<forall>t\<in>I_set. top1_R_to_S1 s = top1_R_to_S1 t \<longrightarrow> f s = f t"
  proof (intro ballI impI)
    fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set" and heq: "top1_R_to_S1 s = top1_R_to_S1 t"
    \<comment> \<open>If s = t, trivial. Otherwise s,t \<in> {0,1} (the only non-trivial fiber).\<close>
    show "f s = f t"
    proof (cases "s = t")
      case True thus ?thesis by simp
    next
      case False
      \<comment> \<open>top1_R_to_S1 injective on (0,1), so s,t \<in> {0,1}.\<close>
      have "s \<in> {0, 1} \<and> t \<in> {0, 1}"
      proof -
        \<comment> \<open>R_to_S1(s) = R_to_S1(t) means (cos(2\<pi>s), sin(2\<pi>s)) = (cos(2\<pi>t), sin(2\<pi>t)).
           So 2\<pi>s \<equiv> 2\<pi>t (mod 2\<pi>), i.e., s - t is an integer.
           For s,t \<in> [0,1] with s \<noteq> t: s-t \<in> (-1,1)\{0}, only integer is \<plusminus>1... no, 0 excluded.
           Wait: s,t \<in> [0,1], s-t \<in> [-1,1]. Integer values: -1, 0, 1. Since s\<noteq>t, not 0.
           If s-t = 1: s=1, t=0. If s-t = -1: s=0, t=1.\<close>
        have "cos (2*pi*s) = cos (2*pi*t)" and "sin (2*pi*s) = sin (2*pi*t)"
          using heq unfolding top1_R_to_S1_def by auto
        have "sin (2*pi*s) = sin (2*pi*t) \<and> cos (2*pi*s) = cos (2*pi*t)"
          using \<open>cos (2*pi*s) = cos (2*pi*t)\<close> \<open>sin (2*pi*s) = sin (2*pi*t)\<close> by simp
        hence "\<exists>k::int. 2*pi*s = 2*pi*t + 2*pi * of_int k"
          unfolding sin_cos_eq_iff by simp
        hence "\<exists>k::int. s - t = of_int k"
        proof
          fix k :: int assume "2*pi*s = 2*pi*t + 2*pi * of_int k"
          hence "2*pi * (s - t) = 2*pi * of_int k" by (simp add: algebra_simps)
          hence "s - t = of_int k" using pi_gt_zero by simp
          thus "\<exists>k::int. s - t = of_int k" by blast
        qed
        then obtain k :: int where hk: "s - t = of_int k" by blast
        have hs01: "0 \<le> s" "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
        have ht01: "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
        have "of_int k \<ge> (-1::real)" "of_int k \<le> (1::real)" using hk hs01 ht01 by linarith+
        hence "k \<ge> -1" "k \<le> 1" by linarith+
        hence "k \<in> {-1, 0, 1}" by auto
        hence "k = 1 \<or> k = -1" using False hk by auto
        thus ?thesis
        proof
          assume "k = 1" hence "s = t + 1" using hk by simp
          hence "s = 1" "t = 0" using hs01 ht01 by linarith+
          thus ?thesis by simp
        next
          assume "k = -1" hence "s = t - 1" using hk by simp
          hence "s = 0" "t = 1" using hs01 ht01 by linarith+
          thus ?thesis by simp
        qed
      qed
      thus ?thesis using hf0 hf1 by auto
    qed
  qed
  have hf_range: "\<forall>s\<in>I_set. f s \<in> X"
    using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
  \<comment> \<open>Apply Theorem_22_2: quotient universal property.\<close>
  obtain h where hh_range: "\<forall>y\<in>top1_S1. h y \<in> X"
      and hh_factor: "\<forall>s\<in>I_set. h (top1_R_to_S1 s) = f s"
      and hh_cont_iff: "top1_continuous_map_on top1_S1 top1_S1_topology X TX h
          \<longleftrightarrow> top1_continuous_map_on I_set I_top X TX f"
    using Theorem_22_2[OF hp_quot hf_range hf_fiber] by blast
  have hh_cont: "top1_continuous_map_on top1_S1 top1_S1_topology X TX h"
    using hh_cont_iff hf_cont by simp
  have hh10: "h (1, 0) = x0"
  proof -
    have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    hence "h (top1_R_to_S1 0) = f 0" using hh_factor by blast
    also have "top1_R_to_S1 0 = (1, 0)" unfolding top1_R_to_S1_def by simp
    finally show ?thesis using hf0 by simp
  qed
  have hfactor: "\<forall>s\<in>I_set. f s = h (top1_R_to_S1 s)" using hh_factor by simp
  show ?thesis using hh_cont hh10 hfactor by blast
qed

theorem Theorem_61_3_JordanSeparation_S2:
  assumes hT: "is_topology_on_strict top1_S2 top1_S2_topology"
  and hC: "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  shows "top1_separates_on top1_S2 top1_S2_topology C"
proof (rule ccontr)
  assume hnot: "\<not> top1_separates_on top1_S2 top1_S2_topology C"
  \<comment> \<open>Negation: S^2 - C is connected.\<close>
  have hS2_C_connected: "top1_connected_on (top1_S2 - C)
                           (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
    using hnot unfolding top1_separates_on_def by blast
  \<comment> \<open>Decompose C = A_1 \<union> A_2 (two arcs) with common endpoints a, b.\<close>
  obtain A1 A2 a b where hC_decomp: "C = A1 \<union> A2"
      and hab: "A1 \<inter> A2 = {a, b}" and hab_ne: "a \<noteq> b"
      and hA1_arc: "top1_is_arc_on A1 (subspace_topology top1_S2 top1_S2_topology A1)"
      and hA2_arc: "top1_is_arc_on A2 (subspace_topology top1_S2 top1_S2_topology A2)"
    using simple_closed_curve_arc_decomposition[OF hC hT top1_S2_is_hausdorff] by (by100 blast)
  \<comment> \<open>Let X = S^2 - {a, b}, U = S^2 - A_1, V = S^2 - A_2.\<close>
  let ?X = "top1_S2 - {a, b}" and ?U = "top1_S2 - A1" and ?V = "top1_S2 - A2"
  \<comment> \<open>X = U \<union> V and U \<inter> V = S^2 - C (path-connected by hypothesis).\<close>
  have hX_UV: "?U \<union> ?V = ?X" using hC_decomp hab by blast
  have hUV_eq: "?U \<inter> ?V = top1_S2 - C" using hC_decomp hab by blast
  have hC_sub: "C \<subseteq> top1_S2" by (rule simple_closed_curve_subset[OF hC])
  \<comment> \<open>U, V are open in X.\<close>
  \<comment> \<open>A1, A2 are arcs (images of [0,1]), hence compact, hence closed in Hausdorff S^2.\<close>
  have hA1_closed: "closedin_on top1_S2 top1_S2_topology A1"
  proof (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff
      top1_S2_is_topology_on_strict])
    show "A1 \<subseteq> top1_S2" using hC_sub hC_decomp by (by100 blast)
    \<comment> \<open>A1 is compact: homeomorphic to [0,1] (arc), and [0,1] is compact.\<close>
    show "top1_compact_on A1 (subspace_topology top1_S2 top1_S2_topology A1)"
    proof -
      obtain h where hh: "top1_homeomorphism_on I_set I_top A1
          (subspace_topology top1_S2 top1_S2_topology A1) h"
        using hA1_arc unfolding top1_is_arc_on_def by (by100 blast)
      have hI_compact: "top1_compact_on I_set I_top"
      proof -
        have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
          by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
        have "compact I_set" unfolding hI01 by (rule compact_Icc)
        thus ?thesis
          unfolding top1_unit_interval_topology_def
          using top1_compact_on_subspace_UNIV_iff_compact[of I_set] by simp
      qed
      have hcont: "top1_continuous_map_on I_set I_top A1
          (subspace_topology top1_S2 top1_S2_topology A1) h"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have hTS2_A1: "is_topology_on A1 (subspace_topology top1_S2 top1_S2_topology A1)"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have himg: "h ` I_set = A1"
        using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "top1_compact_on (h ` I_set) (subspace_topology A1
          (subspace_topology top1_S2 top1_S2_topology A1) (h ` I_set))"
        by (rule top1_compact_on_continuous_image[OF hI_compact hTS2_A1 hcont])
      hence "top1_compact_on A1 (subspace_topology A1
          (subspace_topology top1_S2 top1_S2_topology A1) A1)"
        using himg by simp
      moreover have "subspace_topology A1 (subspace_topology top1_S2 top1_S2_topology A1) A1
          = subspace_topology top1_S2 top1_S2_topology A1"
        by (rule subspace_topology_self_carrier) (auto simp: subspace_topology_def)
      ultimately show ?thesis by simp
    qed
  qed
  have hA2_closed: "closedin_on top1_S2 top1_S2_topology A2"
  proof (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff
      top1_S2_is_topology_on_strict])
    show "A2 \<subseteq> top1_S2" using hC_sub hC_decomp by (by100 blast)
    show "top1_compact_on A2 (subspace_topology top1_S2 top1_S2_topology A2)"
    proof -
      obtain h where hh: "top1_homeomorphism_on I_set I_top A2
          (subspace_topology top1_S2 top1_S2_topology A2) h"
        using hA2_arc unfolding top1_is_arc_on_def by (by100 blast)
      have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
        by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
      have "compact I_set" unfolding hI01 by (rule compact_Icc)
      hence hI_compact: "top1_compact_on I_set I_top"
        unfolding top1_unit_interval_topology_def
        using top1_compact_on_subspace_UNIV_iff_compact[of I_set] by simp
      have hcont: "top1_continuous_map_on I_set I_top A2
          (subspace_topology top1_S2 top1_S2_topology A2) h"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have hTS2_A2: "is_topology_on A2 (subspace_topology top1_S2 top1_S2_topology A2)"
        using hh unfolding top1_homeomorphism_on_def by (by100 blast)
      have himg: "h ` I_set = A2"
        using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "top1_compact_on (h ` I_set) (subspace_topology A2
          (subspace_topology top1_S2 top1_S2_topology A2) (h ` I_set))"
        by (rule top1_compact_on_continuous_image[OF hI_compact hTS2_A2 hcont])
      hence "top1_compact_on A2 (subspace_topology A2
          (subspace_topology top1_S2 top1_S2_topology A2) A2)" using himg by simp
      moreover have "subspace_topology A2 (subspace_topology top1_S2 top1_S2_topology A2) A2
          = subspace_topology top1_S2 top1_S2_topology A2"
        by (rule subspace_topology_self_carrier) (auto simp: subspace_topology_def)
      ultimately show ?thesis by simp
    qed
  qed
  have hU_open: "openin_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) ?U"
  proof -
    have "top1_S2 - A1 \<in> top1_S2_topology"
      using closedin_complement_openin[OF hA1_closed] unfolding openin_on_def by simp
    moreover have "?U = ?X \<inter> (top1_S2 - A1)" using hC_decomp hab by (by100 blast)
    ultimately have "?U \<in> subspace_topology top1_S2 top1_S2_topology ?X"
      unfolding subspace_topology_def by (by100 blast)
    moreover have "?U \<subseteq> ?X" using hab by (by100 blast)
    ultimately show ?thesis unfolding openin_on_def by (by100 blast)
  qed
  have hV_open: "openin_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) ?V"
  proof -
    have "top1_S2 - A2 \<in> top1_S2_topology"
      using closedin_complement_openin[OF hA2_closed] unfolding openin_on_def by simp
    moreover have "?V = ?X \<inter> (top1_S2 - A2)" using hC_decomp hab by (by100 blast)
    ultimately have "?V \<in> subspace_topology top1_S2 top1_S2_topology ?X"
      unfolding subspace_topology_def by (by100 blast)
    moreover have "?V \<subseteq> ?X" using hab by (by100 blast)
    ultimately show ?thesis unfolding openin_on_def by (by100 blast)
  qed
  \<comment> \<open>U \<inter> V = S^2 - C is path-connected (connected + locally path-connected).\<close>
  have hUV_sub_X: "?U \<inter> ?V \<subseteq> ?X" using hab by (by100 blast)
  have hUV_top_eq: "subspace_topology ?X (subspace_topology top1_S2 top1_S2_topology ?X) (?U \<inter> ?V)
      = subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
    by (rule subspace_topology_trans[OF hUV_sub_X])
  have hUV_pc: "top1_path_connected_on (?U \<inter> ?V)
      (subspace_topology ?X (subspace_topology top1_S2 top1_S2_topology ?X) (?U \<inter> ?V))"
  proof -
    \<comment> \<open>S^2 - C is connected (hypothesis). Connected + locally path-connected + nonempty = pc.\<close>
    have hUV_conn: "top1_connected_on (top1_S2 - C)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
      using hS2_C_connected by simp
    have hUV_ne: "top1_S2 - C \<noteq> {}"
      using simple_closed_curve_proper_subset[OF hC] hC_sub by (by100 blast)
    have hUV_locp: "top1_locally_path_connected_on (top1_S2 - C)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
    proof -
      \<comment> \<open>Pick b \<in> C. S^2-{b} \<cong> R^2 (lpc). Transfer lpc. Restrict to open S^2-C.\<close>
      have "C \<noteq> {}"
      proof -
        obtain f where "f ` top1_S1 = C" using hC unfolding top1_simple_closed_curve_on_def by (by100 blast)
        moreover have "top1_S1 \<noteq> {}" unfolding top1_S1_def by (auto intro: exI[of _ 1] exI[of _ 0])
        ultimately show ?thesis by (by100 blast)
      qed
      then obtain b where hb: "b \<in> C" by (by100 blast)
      have hb_S2: "b \<in> top1_S2" using hb hC_sub by (by100 blast)
      obtain h_st where hh_st: "top1_homeomorphism_on (top1_S2 - {b})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))
          (UNIV :: (real \<times> real) set) (product_topology_on top1_open_sets top1_open_sets) h_st"
        using S2_minus_point_homeo_R2[OF hb_S2] by blast
      have hS2b_lpc: "top1_locally_path_connected_on (top1_S2 - {b})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b}))"
        by (rule homeomorphism_preserves_lpc[OF homeomorphism_inverse[OF hh_st] R2_locally_path_connected])
      have hS2C_sub: "top1_S2 - C \<subseteq> top1_S2 - {b}" using hb by (by100 blast)
      \<comment> \<open>S^2-C is open in S^2 (C closed: compact in Hausdorff).\<close>
      have hC_closed: "closedin_on top1_S2 top1_S2_topology C"
      proof (rule compact_in_strict_hausdorff_closedin_on[OF top1_S2_is_hausdorff
          top1_S2_is_topology_on_strict])
        show "C \<subseteq> top1_S2" by (rule hC_sub)
        show "top1_compact_on C (subspace_topology top1_S2 top1_S2_topology C)"
        proof -
          obtain f where hf_cont: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S2 top1_S2_topology f"
              and hf_img: "f ` top1_S1 = C"
            using hC unfolding top1_simple_closed_curve_on_def by (by100 blast)
          have hTS2: "is_topology_on top1_S2 top1_S2_topology"
            using top1_S2_is_topology_on_strict unfolding is_topology_on_strict_def by (by100 blast)
          have hS1_compact: "top1_compact_on top1_S1 top1_S1_topology" by (rule S1_compact)
          have "top1_compact_on (f ` top1_S1) (subspace_topology top1_S2 top1_S2_topology (f ` top1_S1))"
            by (rule top1_compact_on_continuous_image[OF hS1_compact hTS2 hf_cont])
          thus ?thesis using hf_img by simp
        qed
      qed
      have hS2C_open: "top1_S2 - C \<in> top1_S2_topology"
        using closedin_complement_openin[OF hC_closed] unfolding openin_on_def by simp
      have hS2C_open_in_S2b: "top1_S2 - C \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
      proof -
        have "(top1_S2 - {b}) \<inter> (top1_S2 - C) = top1_S2 - C" using hS2C_sub by (by100 blast)
        moreover have "(top1_S2 - {b}) \<inter> (top1_S2 - C) \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})"
          by (rule subspace_topology_memI[OF hS2C_open])
        ultimately show ?thesis by simp
      qed
      have "top1_locally_path_connected_on (top1_S2 - C)
          (subspace_topology (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) (top1_S2 - C))"
        by (rule open_subset_locally_path_connected[OF hS2b_lpc hS2C_open_in_S2b hS2C_sub])
      moreover have "subspace_topology (top1_S2 - {b}) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {b})) (top1_S2 - C)
          = subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)"
        by (rule subspace_topology_trans[OF hS2C_sub])
      ultimately show ?thesis by simp
    qed
    have hTS2C: "is_topology_on (top1_S2 - C) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
      using hUV_conn unfolding top1_connected_on_def by (by100 blast)
    have "top1_path_connected_on (top1_S2 - C)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C))"
      by (rule connected_locally_path_connected_imp_path_connected[OF hTS2C hUV_conn hUV_locp hUV_ne])
    thus ?thesis using hUV_eq hUV_top_eq by simp
  qed
  obtain x0 where hx0: "x0 \<in> ?U \<inter> ?V"
  proof -
    have "C \<noteq> top1_S2" by (rule simple_closed_curve_proper_subset[OF hC])
    hence "top1_S2 - C \<noteq> {}" using hC_sub by (by100 blast)
    hence "?U \<inter> ?V \<noteq> {}" using hUV_eq by simp
    thus ?thesis using that by (by100 blast)
  qed
  \<comment> \<open>By Theorem 59.1, \<pi>_1(X, x_0) is generated by images of i_*, j_*.\<close>
  \<comment> \<open>By Lemma 61.2 (nulhomotopy), every loop in U factors through A2 (an arc),
     hence is nulhomotopic. Similarly for V. So i_*, j_* are trivial.\<close>
  have h_pi1_X_trivial: "top1_simply_connected_on ?X
      (subspace_topology top1_S2 top1_S2_topology ?X)"
  proof -
    let ?TX = "subspace_topology top1_S2 top1_S2_topology ?X"
    have hTX_strict: "is_topology_on_strict ?X ?TX"
      by (rule subspace_topology_is_strict[OF top1_S2_is_topology_on_strict]) (by100 blast)
    have hX_pc: "top1_path_connected_on ?X ?TX"
    proof -
      have ha_S2': "a \<in> top1_S2" using hab hC_decomp hC_sub by (by100 blast)
      have hb_S2': "b \<in> top1_S2" using hab hC_decomp hC_sub by (by100 blast)
      obtain h where hh: "top1_homeomorphism_on (top1_S2 - {a})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
          (UNIV :: (real \<times> real) set)
          (product_topology_on top1_open_sets top1_open_sets) h"
        using S2_minus_point_homeo_R2[OF ha_S2'] by blast
      have hb_in: "b \<in> top1_S2 - {a}" using hb_S2' hab_ne[symmetric] by (by100 blast)
      have hh_restrict: "top1_homeomorphism_on (top1_S2 - {a} - {b})
          (subspace_topology (top1_S2 - {a})
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
            (top1_S2 - {a} - {b}))
          (UNIV - {h b})
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - {h b})) h"
        by (rule homeomorphism_restrict_point[OF hh hb_in])
      have hset_eq: "top1_S2 - {a} - {b} = top1_S2 - {a, b}" by (by100 blast)
      have htop_eq: "subspace_topology (top1_S2 - {a})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))
          (top1_S2 - {a, b}) = subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})"
        by (rule subspace_topology_trans) (by100 blast)
      have hh2: "top1_homeomorphism_on ?X ?TX (UNIV - {h b})
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - {h b})) h"
        using hh_restrict hset_eq htop_eq by simp
      have hR2_pc: "top1_path_connected_on (UNIV - {h b})
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
            (UNIV - {h b}))"
        by (rule R2_minus_point_path_connected) simp
      show ?thesis
        by (rule homeomorphism_preserves_path_connected[OF homeomorphism_inverse[OF hh2] hR2_pc])
    qed
    \<comment> \<open>Shared fact: A1 and A2 are connected (arcs = homeomorphic to [0,1]).\<close>
    have hA1_conn_S2: "top1_connected_on A1 (subspace_topology top1_S2 top1_S2_topology A1)"
    proof -
      obtain hA where "top1_homeomorphism_on I_set I_top A1
          (subspace_topology top1_S2 top1_S2_topology A1) hA"
        using hA1_arc unfolding top1_is_arc_on_def by (by100 blast)
      have hI_conn: "top1_connected_on I_set I_top"
      proof -
        have "connected {0..1::real}" by (rule connected_Icc)
        have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
          by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
        have "connected I_set" using \<open>connected {0..1::real}\<close> hI01 by simp
        have "top1_connected_on I_set (subspace_topology UNIV top1_open_sets I_set)"
          using \<open>connected I_set\<close> top1_connected_on_subspace_openI by (by100 blast)
        thus ?thesis unfolding top1_unit_interval_topology_def by simp
      qed
      have hI_top: "is_topology_on I_set I_top"
        using hI_conn unfolding top1_connected_on_def by (by100 blast)
      have hTA1: "is_topology_on A1 (subspace_topology top1_S2 top1_S2_topology A1)"
        using \<open>top1_homeomorphism_on I_set I_top A1 _ hA\<close>
          unfolding top1_homeomorphism_on_def by (by100 blast)
      have hcont: "top1_continuous_map_on I_set I_top A1
          (subspace_topology top1_S2 top1_S2_topology A1) hA"
        using \<open>top1_homeomorphism_on I_set I_top A1 _ hA\<close>
          unfolding top1_homeomorphism_on_def by (by100 blast)
      have himg: "hA ` I_set = A1"
        using \<open>top1_homeomorphism_on I_set I_top A1 _ hA\<close>
          unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "top1_connected_on (hA ` I_set) (subspace_topology A1
          (subspace_topology top1_S2 top1_S2_topology A1) (hA ` I_set))"
        by (rule Theorem_23_5[OF hI_top hTA1 hI_conn hcont])
      hence "top1_connected_on A1 (subspace_topology A1
          (subspace_topology top1_S2 top1_S2_topology A1) A1)" using himg by simp
      moreover have "subspace_topology A1 (subspace_topology top1_S2 top1_S2_topology A1) A1
          = subspace_topology top1_S2 top1_S2_topology A1"
        by (rule subspace_topology_self_carrier) (auto simp: subspace_topology_def)
      ultimately show ?thesis by simp
    qed
    have hA2_conn_S2: "top1_connected_on A2 (subspace_topology top1_S2 top1_S2_topology A2)"
    proof -
      obtain hA2 where "top1_homeomorphism_on I_set I_top A2
          (subspace_topology top1_S2 top1_S2_topology A2) hA2"
        using hA2_arc unfolding top1_is_arc_on_def by (by100 blast)
      have hI_conn2: "top1_connected_on I_set I_top"
      proof -
        have "connected {0..1::real}" by (rule connected_Icc)
        have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
          by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
        have "connected I_set" using \<open>connected {0..1::real}\<close> hI01 by simp
        have "top1_connected_on I_set (subspace_topology UNIV top1_open_sets I_set)"
          using \<open>connected I_set\<close> top1_connected_on_subspace_openI by (by100 blast)
        thus ?thesis unfolding top1_unit_interval_topology_def by simp
      qed
      have hI_top2: "is_topology_on I_set I_top"
        using hI_conn2 unfolding top1_connected_on_def by (by100 blast)
      have hTA2: "is_topology_on A2 (subspace_topology top1_S2 top1_S2_topology A2)"
        using \<open>top1_homeomorphism_on I_set I_top A2 _ hA2\<close>
          unfolding top1_homeomorphism_on_def by (by100 blast)
      have hcont2: "top1_continuous_map_on I_set I_top A2
          (subspace_topology top1_S2 top1_S2_topology A2) hA2"
        using \<open>top1_homeomorphism_on I_set I_top A2 _ hA2\<close>
          unfolding top1_homeomorphism_on_def by (by100 blast)
      have himg2: "hA2 ` I_set = A2"
        using \<open>top1_homeomorphism_on I_set I_top A2 _ hA2\<close>
          unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
      have "top1_connected_on (hA2 ` I_set) (subspace_topology A2
          (subspace_topology top1_S2 top1_S2_topology A2) (hA2 ` I_set))"
        by (rule Theorem_23_5[OF hI_top2 hTA2 hI_conn2 hcont2])
      hence "top1_connected_on A2 (subspace_topology A2
          (subspace_topology top1_S2 top1_S2_topology A2) A2)" using himg2 by simp
      moreover have "subspace_topology A2 (subspace_topology top1_S2 top1_S2_topology A2) A2
          = subspace_topology top1_S2 top1_S2_topology A2"
        by (rule subspace_topology_self_carrier) (auto simp: subspace_topology_def)
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>By Theorem 59.1, every loop at x0 decomposes into loops in U or V.\<close>
    \<comment> \<open>By Lemma 61.2 (textbook), every loop in U is nulhomotopic in X:
       A loop g in U = S^2 - A1 misses A1. Since A1 is connected and contains
       a, b, both a, b are in same component of S^2 - g(I). By Lemma_61_2_textbook,
       g is nulhomotopic in S^2 - {a,b} = X.\<close>
    have hU_nul: "\<forall>g. top1_is_loop_on ?X ?TX x0 g \<and> g ` I_set \<subseteq> ?U \<longrightarrow>
        top1_path_homotopic_on ?X ?TX x0 x0 g (top1_constant_path x0)"
    proof (intro allI impI)
      fix g assume hg: "top1_is_loop_on ?X ?TX x0 g \<and> g ` I_set \<subseteq> ?U"
      \<comment> \<open>g maps I into U = S^2 - A1. So g(I) \<inter> A1 = {}.\<close>
      have hgU: "g ` I_set \<subseteq> top1_S2 - A1" using hg by (by100 blast)
      have hgI_disj_A1: "g ` I_set \<inter> A1 = {}" using hgU by (by100 blast)
      \<comment> \<open>A1 is connected, contains a and b, and is disjoint from g(I).
         So A1 \<subseteq> S^2 - g(I), and a, b are in the same component of S^2 - g(I).\<close>
      have hA1_sub_comp: "A1 \<subseteq> top1_S2 - g ` I_set" using hgI_disj_A1
        using hC_sub hC_decomp by (by100 blast)
      have ha_in_A1: "a \<in> A1" using hab by (by100 blast)
      have hb_in_A1: "b \<in> A1" using hab by (by100 blast)
      \<comment> \<open>Since A1 is connected and contained in S^2 - g(I), a and b are in the same
         component of S^2 - g(I). By textbook Lemma 61.2, g is nulhomotopic.\<close>
      have hsame_comp: "\<exists>CC. CC \<in> top1_components_on (top1_S2 - g ` I_set)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set))
          \<and> a \<in> CC \<and> b \<in> CC"
      proof -
        \<comment> \<open>A1 is connected, A1 \<subseteq> S^2-g(I), A1 \<noteq> {}. So A1 \<subseteq> some component CC.\<close>
        have hTS2gI: "is_topology_on (top1_S2 - g ` I_set)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set))"
          by (rule subspace_topology_is_topology_on[OF
              is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict]]) (by100 blast)
        have hA1_conn_sub: "top1_connected_on A1
            (subspace_topology (top1_S2 - g ` I_set)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set)) A1)"
        proof -
          have "subspace_topology (top1_S2 - g ` I_set)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set)) A1
              = subspace_topology top1_S2 top1_S2_topology A1"
            by (rule subspace_topology_trans[OF hA1_sub_comp])
          moreover have "top1_connected_on A1 (subspace_topology top1_S2 top1_S2_topology A1)"
          proof -
            \<comment> \<open>A1 is an arc, hence homeomorphic to [0,1], which is connected.\<close>
            obtain hA where "top1_homeomorphism_on I_set I_top A1
                (subspace_topology top1_S2 top1_S2_topology A1) hA"
              using hA1_arc unfolding top1_is_arc_on_def by (by100 blast)
            \<comment> \<open>[0,1] is connected, continuous image of connected is connected.\<close>
            have hI_conn: "top1_connected_on I_set I_top"
            proof -
              have "connected {0..1::real}" by (rule connected_Icc)
              have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
                by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
              have "connected I_set" using \<open>connected {0..1::real}\<close> hI01 by simp
              thus ?thesis using top1_connected_on_subspace_openI
                unfolding top1_unit_interval_topology_def by (by100 blast)
            qed
            have hI_top: "is_topology_on I_set I_top"
              using hI_conn unfolding top1_connected_on_def by (by100 blast)
            have hTA1: "is_topology_on A1 (subspace_topology top1_S2 top1_S2_topology A1)"
              using \<open>top1_homeomorphism_on I_set I_top A1 _ hA\<close>
                unfolding top1_homeomorphism_on_def by (by100 blast)
            have hcont: "top1_continuous_map_on I_set I_top A1
                (subspace_topology top1_S2 top1_S2_topology A1) hA"
              using \<open>top1_homeomorphism_on I_set I_top A1 _ hA\<close>
                unfolding top1_homeomorphism_on_def by (by100 blast)
            have himg: "hA ` I_set = A1"
              using \<open>top1_homeomorphism_on I_set I_top A1 _ hA\<close>
                unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
            have "top1_connected_on (hA ` I_set) (subspace_topology A1
                (subspace_topology top1_S2 top1_S2_topology A1) (hA ` I_set))"
              by (rule Theorem_23_5[OF hI_top hTA1 hI_conn hcont])
            hence "top1_connected_on A1 (subspace_topology A1
                (subspace_topology top1_S2 top1_S2_topology A1) A1)" using himg by simp
            moreover have "subspace_topology A1 (subspace_topology top1_S2 top1_S2_topology A1) A1
                = subspace_topology top1_S2 top1_S2_topology A1"
              by (rule subspace_topology_self_carrier) (auto simp: subspace_topology_def)
            ultimately show ?thesis by simp
          qed
          ultimately show ?thesis by simp
        qed
        have hA1_ne: "A1 \<noteq> {}" using ha_in_A1 by (by100 blast)
        obtain CC where hCC: "CC \<in> top1_components_on (top1_S2 - g ` I_set)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set))"
            and hA1_CC: "A1 \<subseteq> CC"
          using Theorem_25_1(4)[OF hTS2gI hA1_sub_comp hA1_conn_sub hA1_ne] by (by100 blast)
        have "a \<in> CC" using hA1_CC ha_in_A1 by (by100 blast)
        moreover have "b \<in> CC" using hA1_CC hb_in_A1 by (by100 blast)
        ultimately show ?thesis using hCC by (by100 blast)
      qed
      \<comment> \<open>g: I \<rightarrow> X = S^2-{a,b}. I compact, a,b in same component of S^2-g(I).\<close>
      have hI_compact: "top1_compact_on I_set I_top"
      proof -
        have "compact {0..1::real}" by (rule compact_Icc)
        have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
          by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
        have "compact I_set" using \<open>compact {0..1::real}\<close> hI01 by simp
        have "top1_compact_on I_set (subspace_topology (UNIV::real set) top1_open_sets I_set)"
          using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
        thus ?thesis unfolding top1_unit_interval_topology_def by simp
      qed
      have hg_cont: "top1_continuous_map_on I_set I_top ?X ?TX g"
        using hg unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      have ha_S2_: "a \<in> top1_S2" using hab hC_decomp hC_sub by (by100 blast)
      have hb_S2_: "b \<in> top1_S2" using hab hC_decomp hC_sub by (by100 blast)
      \<comment> \<open>Textbook approach: factor g = h \<circ> p through S^1.
         h: S^1 \<rightarrow> U continuous with h(1,0)=x0. p = top1_R_to_S1 restricted to I.
         i \<circ> h: S^1 \<rightarrow> X nulhomotopic by Lemma 61.2 (S^1 compact, A1 connected).
         By nulhomotopic_trivializes_loops_general: (i\<circ>h)\<circ>p = g path-hom to const.\<close>
      have hTX_: "is_topology_on ?X ?TX"
        using hTX_strict unfolding is_topology_on_strict_def by (by100 blast)
      have hg_loop: "top1_is_loop_on ?X ?TX x0 g" using hg by (by100 blast)
      \<comment> \<open>Step 1: Factor g through S^1. Define h: S^1 \<rightarrow> X by h = g \<circ> (S1_to_I map).\<close>
      obtain h_S1 where hh_S1: "top1_continuous_map_on top1_S1 top1_S1_topology ?X ?TX h_S1"
          and hh_S1_10: "h_S1 (1, 0) = x0"
          and hg_factor: "\<forall>s\<in>I_set. g s = h_S1 (top1_R_to_S1 s)"
        using loop_factors_through_S1[OF hTX_ hg_loop] by (by100 blast)
      \<comment> \<open>Step 2: h_S1(S^1) \<subseteq> U (since g(I) \<subseteq> U and g = h_S1 \<circ> p, p surjective).\<close>
      have hh_S1_U: "h_S1 ` top1_S1 \<subseteq> ?U"
      proof
        fix y assume "y \<in> h_S1 ` top1_S1"
        then obtain q where hq: "q \<in> top1_S1" "y = h_S1 q" by (by100 blast)
        \<comment> \<open>q \<in> S^1 = top1_R_to_S1(R). Find t \<in> I with top1_R_to_S1(t) = q.\<close>
        have "\<exists>t\<in>I_set. top1_R_to_S1 t = q"
        proof -
          obtain x y where hq_eq: "q = (x, y)" by (cases q)
          have hcirc: "x^2 + y^2 = 1" using hq hq_eq unfolding top1_S1_def by simp
          obtain t where ht: "0 \<le> t" "t < 2 * pi" "x = cos t" "y = sin t"
            using sincos_total_2pi[OF hcirc] by blast
          define t' where "t' = t / (2 * pi)"
          have ht'_range: "0 \<le> t'" "t' < 1" unfolding t'_def using ht(1,2) pi_gt_zero by auto
          hence "t' \<in> I_set" unfolding top1_unit_interval_def by simp
          moreover have "top1_R_to_S1 t' = q"
            unfolding top1_R_to_S1_def t'_def hq_eq using ht(3,4) pi_gt_zero by simp
          ultimately show ?thesis by (by100 blast)
        qed
        then obtain t where ht: "t \<in> I_set" "top1_R_to_S1 t = q" by blast
        have "y = g t" using hg_factor ht hq(2) by simp
        moreover have "g t \<in> ?U" using hg ht(1) by (by100 blast)
        ultimately show "y \<in> ?U" by simp
      qed
      \<comment> \<open>Step 3: h_S1: S^1 \<rightarrow> X is nulhomotopic (by Lemma 61.2, S^1 compact).\<close>
      have hh_S1_nul: "top1_nulhomotopic_on top1_S1 top1_S1_topology ?X ?TX h_S1"
      proof -
        \<comment> \<open>A1 \<subseteq> S^2-h_S1(S^1) (since h_S1(S^1) \<subseteq> U = S^2-A1).\<close>
        have hA1_sub_S2: "A1 \<subseteq> top1_S2" using hC_sub hC_decomp by (by100 blast)
        have "h_S1 ` top1_S1 \<inter> A1 = {}" using hh_S1_U by (by100 blast)
        hence hA1_disj: "A1 \<subseteq> top1_S2 - h_S1 ` top1_S1"
          using hA1_sub_S2 by (by100 blast)
        \<comment> \<open>A1 connected, contains a and b, so a,b same component of S^2-h_S1(S^1).\<close>
        have hsame_S1: "\<exists>CC. CC \<in> top1_components_on (top1_S2 - h_S1 ` top1_S1)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1 ` top1_S1))
            \<and> a \<in> CC \<and> b \<in> CC"
        proof -
          have hTS2hS1: "is_topology_on (top1_S2 - h_S1 ` top1_S1)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1 ` top1_S1))"
            by (rule subspace_topology_is_topology_on[OF
                is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict]]) (by100 blast)
          have hA1_conn_sub: "top1_connected_on A1
              (subspace_topology (top1_S2 - h_S1 ` top1_S1)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1 ` top1_S1)) A1)"
          proof -
            have "subspace_topology (top1_S2 - h_S1 ` top1_S1)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1 ` top1_S1)) A1
                = subspace_topology top1_S2 top1_S2_topology A1"
              by (rule subspace_topology_trans[OF hA1_disj])
            moreover have "top1_connected_on A1 (subspace_topology top1_S2 top1_S2_topology A1)"
              by (rule hA1_conn_S2)
            ultimately show ?thesis by simp
          qed
          have hA1_ne: "A1 \<noteq> {}" using ha_in_A1 by (by100 blast)
          obtain CC where hCC: "CC \<in> top1_components_on (top1_S2 - h_S1 ` top1_S1)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1 ` top1_S1))"
              and hA1_CC: "A1 \<subseteq> CC"
            using Theorem_25_1(4)[OF hTS2hS1 hA1_disj hA1_conn_sub hA1_ne] by (by100 blast)
          show ?thesis using hCC hA1_CC ha_in_A1 hb_in_A1 by (by100 blast)
        qed
        show ?thesis
          by (rule Lemma_61_2_nulhomotopy_textbook[OF top1_S2_is_topology_on_strict
                S1_compact ha_S2_ hb_S2_ hab_ne hh_S1 hsame_S1])
      qed
      \<comment> \<open>Step 4: By nulhomotopic_trivializes_loops_general with g = h_S1,
         f = top1_R_to_S1 restricted to I (standard loop in S^1),
         get h_S1 \<circ> (top1_R_to_S1|_I) path-homotopic to constant.\<close>
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF
            product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV, simplified]]) simp
      have hstd_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1,0) (top1_R_to_S1)"
      proof -
        have hp_cont_R: "top1_continuous_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
          using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
        have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
          by (rule top1_open_sets_is_topology_on_UNIV)
        have hI_sub: "I_set \<subseteq> (UNIV::real set)" by simp
        have hp_cont_I: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology top1_R_to_S1"
          using top1_continuous_map_on_restrict_domain_simple[OF hp_cont_R hI_sub]
          unfolding top1_unit_interval_topology_def by simp
        have hp0: "top1_R_to_S1 0 = (1::real, 0::real)" unfolding top1_R_to_S1_def by simp
        have hp1: "top1_R_to_S1 1 = (1::real, 0::real)" unfolding top1_R_to_S1_def by simp
        show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
          using hp_cont_I hp0 hp1 by (by100 blast)
      qed
      have h10_S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by simp
      have "top1_path_homotopic_on ?X ?TX x0 x0 (h_S1 \<circ> top1_R_to_S1) (top1_constant_path x0)"
        by (rule nulhomotopic_trivializes_loops_general[OF hTS1 hTX_ hh_S1 hh_S1_nul hh_S1_10
              h10_S1 hstd_loop])
      \<comment> \<open>Step 5: h_S1 \<circ> top1_R_to_S1 = g on I_set.\<close>
      moreover have "top1_path_homotopic_on ?X ?TX x0 x0 g (h_S1 \<circ> top1_R_to_S1)"
      proof -
        have hg_path_: "top1_is_path_on ?X ?TX x0 x0 g"
          using hg_loop unfolding top1_is_loop_on_def by (by100 blast)
        have "\<forall>s\<in>I_set. g s = (h_S1 \<circ> top1_R_to_S1) s"
          using hg_factor unfolding comp_def by simp
        thus ?thesis by (rule paths_agree_on_I_path_homotopic[OF hTX_ hg_path_])
      qed
      ultimately show "top1_path_homotopic_on ?X ?TX x0 x0 g (top1_constant_path x0)"
        using Lemma_51_1_path_homotopic_trans[OF hTX_] by (by100 blast)
    qed
    have hV_nul: "\<forall>g. top1_is_loop_on ?X ?TX x0 g \<and> g ` I_set \<subseteq> ?V \<longrightarrow>
        top1_path_homotopic_on ?X ?TX x0 x0 g (top1_constant_path x0)"
    proof (intro allI impI)
      fix g assume hg: "top1_is_loop_on ?X ?TX x0 g \<and> g ` I_set \<subseteq> ?V"
      \<comment> \<open>g maps I into V = S^2 - A2. So g(I) \<inter> A2 = {}.\<close>
      have hgV: "g ` I_set \<subseteq> top1_S2 - A2" using hg by (by100 blast)
      have hgI_disj_A2: "g ` I_set \<inter> A2 = {}" using hgV by (by100 blast)
      have hA2_sub_S2: "A2 \<subseteq> top1_S2" using hC_sub hC_decomp by (by100 blast)
      have hA2_sub_comp: "A2 \<subseteq> top1_S2 - g ` I_set"
        using hA2_sub_S2 hgI_disj_A2 by (by100 blast)
      have ha_in_A2: "a \<in> A2" using hab by (by100 blast)
      have hb_in_A2: "b \<in> A2" using hab by (by100 blast)
      \<comment> \<open>A2 connected + A2 \<subseteq> S^2-g(I) \<Rightarrow> a, b in same component.\<close>
      have hsame_comp2: "\<exists>CC. CC \<in> top1_components_on (top1_S2 - g ` I_set)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set))
          \<and> a \<in> CC \<and> b \<in> CC"
      proof -
        have hTS2gI: "is_topology_on (top1_S2 - g ` I_set)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set))"
          by (rule subspace_topology_is_topology_on[OF
              is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict]]) (by100 blast)
        have hA2_conn_sub: "top1_connected_on A2
            (subspace_topology (top1_S2 - g ` I_set)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set)) A2)"
        proof -
          have "subspace_topology (top1_S2 - g ` I_set)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set)) A2
              = subspace_topology top1_S2 top1_S2_topology A2"
            by (rule subspace_topology_trans[OF hA2_sub_comp])
          moreover have "top1_connected_on A2 (subspace_topology top1_S2 top1_S2_topology A2)"
          proof -
            obtain hA where "top1_homeomorphism_on I_set I_top A2
                (subspace_topology top1_S2 top1_S2_topology A2) hA"
              using hA2_arc unfolding top1_is_arc_on_def by (by100 blast)
            have hI_conn: "top1_connected_on I_set I_top"
            proof -
              have "connected {0..1::real}" by (rule connected_Icc)
              have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
                by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
              have "connected I_set" using \<open>connected {0..1::real}\<close> hI01 by simp
              thus ?thesis using top1_connected_on_subspace_openI
                unfolding top1_unit_interval_topology_def by (by100 blast)
            qed
            have hI_top: "is_topology_on I_set I_top"
              using hI_conn unfolding top1_connected_on_def by (by100 blast)
            have hTA2: "is_topology_on A2 (subspace_topology top1_S2 top1_S2_topology A2)"
              using \<open>top1_homeomorphism_on I_set I_top A2 _ hA\<close>
                unfolding top1_homeomorphism_on_def by (by100 blast)
            have hcont: "top1_continuous_map_on I_set I_top A2
                (subspace_topology top1_S2 top1_S2_topology A2) hA"
              using \<open>top1_homeomorphism_on I_set I_top A2 _ hA\<close>
                unfolding top1_homeomorphism_on_def by (by100 blast)
            have himg: "hA ` I_set = A2"
              using \<open>top1_homeomorphism_on I_set I_top A2 _ hA\<close>
                unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
            have "top1_connected_on (hA ` I_set) (subspace_topology A2
                (subspace_topology top1_S2 top1_S2_topology A2) (hA ` I_set))"
              by (rule Theorem_23_5[OF hI_top hTA2 hI_conn hcont])
            hence "top1_connected_on A2 (subspace_topology A2
                (subspace_topology top1_S2 top1_S2_topology A2) A2)" using himg by simp
            moreover have "subspace_topology A2 (subspace_topology top1_S2 top1_S2_topology A2) A2
                = subspace_topology top1_S2 top1_S2_topology A2"
              by (rule subspace_topology_self_carrier) (auto simp: subspace_topology_def)
            ultimately show ?thesis by simp
          qed
          ultimately show ?thesis by simp
        qed
        have hA2_ne: "A2 \<noteq> {}" using ha_in_A2 by (by100 blast)
        obtain CC where hCC: "CC \<in> top1_components_on (top1_S2 - g ` I_set)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set))"
            and hA2_CC: "A2 \<subseteq> CC"
          using Theorem_25_1(4)[OF hTS2gI hA2_sub_comp hA2_conn_sub hA2_ne] by (by100 blast)
        have "a \<in> CC" using hA2_CC ha_in_A2 by (by100 blast)
        moreover have "b \<in> CC" using hA2_CC hb_in_A2 by (by100 blast)
        ultimately show ?thesis using hCC by (by100 blast)
      qed
      have hI_compact': "top1_compact_on I_set I_top"
      proof -
        have "compact {0..1::real}" by (rule compact_Icc)
        have hI01: "I_set = {0..1::real}" unfolding top1_unit_interval_def
          by (auto simp: atLeastAtMost_def atLeast_def atMost_def)
        have "compact I_set" using \<open>compact {0..1::real}\<close> hI01 by simp
        have "top1_compact_on I_set (subspace_topology (UNIV::real set) top1_open_sets I_set)"
          using top1_compact_on_subspace_UNIV_iff_compact[of I_set] \<open>compact I_set\<close> by simp
        thus ?thesis unfolding top1_unit_interval_topology_def by simp
      qed
      have hg_cont': "top1_continuous_map_on I_set I_top ?X ?TX g"
        using hg unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      have ha_S2_': "a \<in> top1_S2" using hab hC_decomp hC_sub by (by100 blast)
      have hb_S2_': "b \<in> top1_S2" using hab hC_decomp hC_sub by (by100 blast)
      \<comment> \<open>Same textbook S^1-factorization approach as U-side.\<close>
      have hTX_': "is_topology_on ?X ?TX"
        using hTX_strict unfolding is_topology_on_strict_def by (by100 blast)
      have hg_loop': "top1_is_loop_on ?X ?TX x0 g" using hg by (by100 blast)
      obtain h_S1' where hh_S1': "top1_continuous_map_on top1_S1 top1_S1_topology ?X ?TX h_S1'"
          and hh_S1_10': "h_S1' (1, 0) = x0"
          and hg_factor': "\<forall>s\<in>I_set. g s = h_S1' (top1_R_to_S1 s)"
        using loop_factors_through_S1[OF hTX_' hg_loop'] by (by100 blast)
      have hh_S1_nul': "top1_nulhomotopic_on top1_S1 top1_S1_topology ?X ?TX h_S1'"
      proof -
        have hA2_sub_S2: "A2 \<subseteq> top1_S2" using hC_sub hC_decomp by (by100 blast)
        have "h_S1' ` top1_S1 \<subseteq> ?V"
        proof
          fix y assume "y \<in> h_S1' ` top1_S1"
          then obtain q where hq': "q \<in> top1_S1" "y = h_S1' q" by (by100 blast)
          obtain t where ht': "t \<in> I_set" "top1_R_to_S1 t = q"
          proof -
            obtain x' y' where hq_eq: "q = (x', y')" by (cases q)
            have hcirc: "x'^2 + y'^2 = 1" using hq' hq_eq unfolding top1_S1_def by simp
            obtain t where "0 \<le> t" "t < 2 * pi" "x' = cos t" "y' = sin t"
              using sincos_total_2pi[OF hcirc] by blast
            define t' where "t' = t / (2 * pi)"
            have "0 \<le> t'" "t' < 1" unfolding t'_def using \<open>0 \<le> t\<close> \<open>t < 2*pi\<close> pi_gt_zero by auto
            hence "t' \<in> I_set" unfolding top1_unit_interval_def by simp
            moreover have "top1_R_to_S1 t' = q"
              unfolding top1_R_to_S1_def t'_def hq_eq using \<open>x' = cos t\<close> \<open>y' = sin t\<close> pi_gt_zero by simp
            ultimately show ?thesis using that by (by100 blast)
          qed
          have "y = g t" using hg_factor' ht' hq'(2) by simp
          moreover have "g t \<in> ?V" using hg ht'(1) by (by100 blast)
          ultimately show "y \<in> ?V" by simp
        qed
        hence "h_S1' ` top1_S1 \<inter> A2 = {}" by (by100 blast)
        hence hA2_disj: "A2 \<subseteq> top1_S2 - h_S1' ` top1_S1"
          using hA2_sub_S2 by (by100 blast)
        have hsame_S1': "\<exists>CC. CC \<in> top1_components_on (top1_S2 - h_S1' ` top1_S1)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1' ` top1_S1))
            \<and> a \<in> CC \<and> b \<in> CC"
        proof -
          have hTS2hS1': "is_topology_on (top1_S2 - h_S1' ` top1_S1)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1' ` top1_S1))"
            by (rule subspace_topology_is_topology_on[OF
                is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict]]) (by100 blast)
          \<comment> \<open>A2 connected: same proof structure as A1 (arc \<rightarrow> I \<rightarrow> connected).\<close>
          have hA2_conn_S2': "top1_connected_on A2 (subspace_topology top1_S2 top1_S2_topology A2)"
            by (rule hA2_conn_S2)
          have hA2_conn_sub: "top1_connected_on A2
              (subspace_topology (top1_S2 - h_S1' ` top1_S1)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1' ` top1_S1)) A2)"
          proof -
            have "subspace_topology (top1_S2 - h_S1' ` top1_S1)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1' ` top1_S1)) A2
                = subspace_topology top1_S2 top1_S2_topology A2"
              by (rule subspace_topology_trans[OF hA2_disj])
            thus ?thesis using hA2_conn_S2' by simp
          qed
          have hA2_ne: "A2 \<noteq> {}" using ha_in_A2 by (by100 blast)
          obtain CC where hCC: "CC \<in> top1_components_on (top1_S2 - h_S1' ` top1_S1)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1' ` top1_S1))"
              and hA2_CC: "A2 \<subseteq> CC"
            using Theorem_25_1(4)[OF hTS2hS1' hA2_disj hA2_conn_sub hA2_ne] by (by100 blast)
          show ?thesis using hCC hA2_CC ha_in_A2 hb_in_A2 by (by100 blast)
        qed
        show ?thesis
          by (rule Lemma_61_2_nulhomotopy_textbook[OF top1_S2_is_topology_on_strict
                S1_compact ha_S2_' hb_S2_' hab_ne hh_S1' hsame_S1'])
      qed
      have hTS1': "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF
            product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
              top1_open_sets_is_topology_on_UNIV, simplified]]) simp
      have hstd_loop': "top1_is_loop_on top1_S1 top1_S1_topology (1,0) (top1_R_to_S1)"
      proof -
        have hp_cont_R': "top1_continuous_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
          using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
        have hp_cont_I': "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology top1_R_to_S1"
          using top1_continuous_map_on_restrict_domain_simple[OF hp_cont_R']
          unfolding top1_unit_interval_topology_def by simp
        show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
          using hp_cont_I' by (simp add: top1_R_to_S1_def)
      qed
      have h10_S1': "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by simp
      have "top1_path_homotopic_on ?X ?TX x0 x0 (h_S1' \<circ> top1_R_to_S1) (top1_constant_path x0)"
        by (rule nulhomotopic_trivializes_loops_general[OF hTS1' hTX_' hh_S1' hh_S1_nul' hh_S1_10'
              h10_S1' hstd_loop'])
      moreover have "top1_path_homotopic_on ?X ?TX x0 x0 g (h_S1' \<circ> top1_R_to_S1)"
      proof -
        have hg_path_': "top1_is_path_on ?X ?TX x0 x0 g"
          using hg_loop' unfolding top1_is_loop_on_def by (by100 blast)
        have "\<forall>s\<in>I_set. g s = (h_S1' \<circ> top1_R_to_S1) s"
          using hg_factor' unfolding comp_def by simp
        thus ?thesis by (rule paths_agree_on_I_path_homotopic[OF hTX_' hg_path_'])
      qed
      ultimately show "top1_path_homotopic_on ?X ?TX x0 x0 g (top1_constant_path x0)"
        using Lemma_51_1_path_homotopic_trans[OF hTX_'] by (by100 blast)
    qed
    \<comment> \<open>By Theorem 59.1 + nulhomotopy of U/V loops, \<pi>_1(X, x0) is trivial.\<close>
    show ?thesis unfolding top1_simply_connected_on_def
    proof (intro conjI)
      show "top1_path_connected_on ?X ?TX" by (rule hX_pc)
    next
      show "\<forall>x0a\<in>?X. \<forall>f. top1_is_loop_on ?X ?TX x0a f \<longrightarrow>
          top1_path_homotopic_on ?X ?TX x0a x0a f (top1_constant_path x0a)"
      proof (intro ballI allI impI)
        fix x1 fa assume hx1: "x1 \<in> ?X" and hfa: "top1_is_loop_on ?X ?TX x1 fa"
        \<comment> \<open>If x1 = x0, use Theorem 59.1 + hU_nul + hV_nul + foldr directly.
           If x1 \<noteq> x0, conjugate by a path x0 \<rightarrow> x1 to reduce to x0 case.\<close>
        have hTX_weak: "is_topology_on ?X ?TX"
          using hTX_strict unfolding is_topology_on_strict_def by (by100 blast)
        \<comment> \<open>Since X is path-connected, connect x0 to x1.\<close>
        have hx0X: "x0 \<in> ?X"
        proof -
          have "x0 \<in> top1_S2 - C" using hx0 hUV_eq by (by100 blast)
          moreover have "{a,b} \<subseteq> C" using hab hC_decomp by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
        obtain \<gamma> where h\<gamma>: "top1_is_path_on ?X ?TX x0 x1 \<gamma>"
          using hX_pc hx0X hx1 unfolding top1_path_connected_on_def by (by100 blast)
        \<comment> \<open>Conjugate: \<gamma> * fa * rev(\<gamma>) is a loop at x0.\<close>
        have hrev\<gamma>: "top1_is_path_on ?X ?TX x1 x0 (top1_path_reverse \<gamma>)"
          by (rule top1_path_reverse_is_path[OF h\<gamma>])
        have hfa_path: "top1_is_path_on ?X ?TX x1 x1 fa"
          using hfa unfolding top1_is_loop_on_def by (by100 blast)
        have hfa_rev\<gamma>: "top1_is_path_on ?X ?TX x1 x0 (top1_path_product fa (top1_path_reverse \<gamma>))"
          by (rule top1_path_product_is_path[OF hTX_weak hfa_path hrev\<gamma>])
        let ?conj = "top1_path_product \<gamma> (top1_path_product fa (top1_path_reverse \<gamma>))"
        have hconj_path: "top1_is_path_on ?X ?TX x0 x0 ?conj"
          by (rule top1_path_product_is_path[OF hTX_weak h\<gamma> hfa_rev\<gamma>])
        have hconj_loop: "top1_is_loop_on ?X ?TX x0 ?conj"
          unfolding top1_is_loop_on_def using hconj_path by (by100 blast)
        \<comment> \<open>By Theorem 59.1, ?conj decomposes into loops in U or V at x0.\<close>
        obtain n gs where hn: "n \<ge> 1" and hgs_len: "length gs = n"
            and hgs_UV: "\<forall>i<n. top1_is_loop_on ?X ?TX x0 (gs!i)
                \<and> (gs!i ` I_set \<subseteq> ?U \<or> gs!i ` I_set \<subseteq> ?V)"
            and hgs_prod: "top1_path_homotopic_on ?X ?TX x0 x0 ?conj
                (foldr top1_path_product gs (top1_constant_path x0))"
        proof -
          have hT59: "\<forall>f. top1_is_loop_on ?X ?TX x0 f \<longrightarrow>
              (\<exists>n\<ge>1. \<exists>gs. length gs = n \<and>
                (\<forall>i<n. top1_is_loop_on ?X ?TX x0 (gs ! i) \<and>
                       (gs ! i ` I_set \<subseteq> ?U \<or> gs ! i ` I_set \<subseteq> ?V)) \<and>
                top1_path_homotopic_on ?X ?TX x0 x0 f
                  (foldr top1_path_product gs (top1_constant_path x0)))"
            by (rule Theorem_59_1[OF hTX_strict hU_open hV_open hX_UV hUV_pc hx0])
          hence "\<exists>n\<ge>1. \<exists>gs. length gs = n \<and>
                (\<forall>i<n. top1_is_loop_on ?X ?TX x0 (gs ! i) \<and>
                       (gs ! i ` I_set \<subseteq> ?U \<or> gs ! i ` I_set \<subseteq> ?V)) \<and>
                top1_path_homotopic_on ?X ?TX x0 x0 ?conj
                  (foldr top1_path_product gs (top1_constant_path x0))"
            using hconj_loop by blast
          thus ?thesis using that by blast
        qed
        \<comment> \<open>Each gi is trivial by hU_nul or hV_nul.\<close>
        have hgi_nul: "\<forall>i<n. top1_path_homotopic_on ?X ?TX x0 x0 (gs!i) (top1_constant_path x0)"
        proof (intro allI impI)
          fix i assume hi: "i < n"
          have hgi: "top1_is_loop_on ?X ?TX x0 (gs!i) \<and>
              (gs!i ` I_set \<subseteq> ?U \<or> gs!i ` I_set \<subseteq> ?V)"
            using hgs_UV hi by blast
          show "top1_path_homotopic_on ?X ?TX x0 x0 (gs!i) (top1_constant_path x0)"
          proof -
            have hgi_loop: "top1_is_loop_on ?X ?TX x0 (gs!i)" using hgi by simp
            have hUV_case: "gs!i ` I_set \<subseteq> ?U \<or> gs!i ` I_set \<subseteq> ?V" using hgi by simp
            show ?thesis
            proof (cases "gs!i ` I_set \<subseteq> ?U")
              case True
              have "top1_is_loop_on ?X ?TX x0 (gs!i) \<and> gs!i ` I_set \<subseteq> ?U"
                using hgi_loop True by simp
              thus ?thesis using hU_nul by (by100 blast)
            next
              case False
              hence "gs!i ` I_set \<subseteq> ?V" using hUV_case by simp
              have "top1_is_loop_on ?X ?TX x0 (gs!i) \<and> gs!i ` I_set \<subseteq> ?V"
                using hgi_loop \<open>gs!i ` I_set \<subseteq> ?V\<close> by simp
              thus ?thesis using hV_nul by (by100 blast)
            qed
          qed
        qed
        \<comment> \<open>Product of trivial loops is trivial.\<close>
        have hgi_nul': "\<forall>i < length gs. top1_path_homotopic_on ?X ?TX x0 x0 (gs!i) (top1_constant_path x0)"
          using hgi_nul hgs_len by simp
        have hprod_nul: "top1_path_homotopic_on ?X ?TX x0 x0
            (foldr top1_path_product gs (top1_constant_path x0)) (top1_constant_path x0)"
          by (rule foldr_path_product_nulhomotopic[OF hTX_weak hx0X hgi_nul'])
        \<comment> \<open>So conj = rev(\<gamma>) * fa * \<gamma> \<simeq> const_{x0}.\<close>
        have hconj_trivial: "top1_path_homotopic_on ?X ?TX x0 x0 ?conj (top1_constant_path x0)"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTX_weak hgs_prod hprod_nul])
        \<comment> \<open>Unconjugate: fa \<simeq> bc(\<gamma>, bc(rev(\<gamma>), fa)) \<simeq> bc(\<gamma>, const_{x0}) \<simeq> const_{x1}.\<close>
        \<comment> \<open>?conj = bc(rev(\<gamma>), fa) = \<gamma> * fa * rev(\<gamma>).\<close>
        \<comment> \<open>Step a: fa \<simeq> bc(\<gamma>, ?conj) by roundtrip.\<close>
        have hfa_roundtrip: "top1_path_homotopic_on ?X ?TX x1 x1 fa
            (top1_basepoint_change_on ?X ?TX x0 x1 (top1_path_reverse (top1_path_reverse \<gamma>))
              (top1_basepoint_change_on ?X ?TX x1 x0 (top1_path_reverse \<gamma>) fa))"
          by (rule top1_basepoint_change_roundtrip[OF hTX_weak hrev\<gamma> hfa])
        hence hfa_roundtrip': "top1_path_homotopic_on ?X ?TX x1 x1 fa
            (top1_basepoint_change_on ?X ?TX x0 x1 \<gamma>
              (top1_basepoint_change_on ?X ?TX x1 x0 (top1_path_reverse \<gamma>) fa))"
          unfolding top1_path_reverse_twice .
        \<comment> \<open>Note: bc(rev(\<gamma>), fa) = ?conj.\<close>
        have hbc_eq: "top1_basepoint_change_on ?X ?TX x1 x0 (top1_path_reverse \<gamma>) fa = ?conj"
          unfolding top1_basepoint_change_on_def top1_path_reverse_twice by (rule refl)
        \<comment> \<open>Step b: bc(\<gamma>, ?conj) \<simeq> bc(\<gamma>, const_{x0}) by congruence + ?conj \<simeq> const.\<close>
        have hconst_loop: "top1_is_loop_on ?X ?TX x0 (top1_constant_path x0)"
          by (rule top1_constant_path_is_loop[OF hTX_weak hx0X])
        have hbc_cong: "top1_path_homotopic_on ?X ?TX x1 x1
            (top1_basepoint_change_on ?X ?TX x0 x1 \<gamma> ?conj)
            (top1_basepoint_change_on ?X ?TX x0 x1 \<gamma> (top1_constant_path x0))"
          by (rule top1_basepoint_change_congruence[OF hTX_weak h\<gamma> hconj_loop hconst_loop hconj_trivial])
        \<comment> \<open>Step c: bc(\<gamma>, const_{x0}) = rev(\<gamma>) * const_{x0} * \<gamma> \<simeq> rev(\<gamma>) * \<gamma> \<simeq> const_{x1}.\<close>
        have hbc_const: "top1_basepoint_change_on ?X ?TX x0 x1 \<gamma> (top1_constant_path x0)
            = top1_path_product (top1_path_reverse \<gamma>) (top1_path_product (top1_constant_path x0) \<gamma>)"
          unfolding top1_basepoint_change_on_def by (rule refl)
        have hconst_\<gamma>: "top1_path_homotopic_on ?X ?TX x0 x1
            (top1_path_product (top1_constant_path x0) \<gamma>) \<gamma>"
          by (rule Theorem_51_2_left_identity[OF hTX_weak h\<gamma>])
        have hrev_const_\<gamma>: "top1_path_homotopic_on ?X ?TX x1 x1
            (top1_path_product (top1_path_reverse \<gamma>) (top1_path_product (top1_constant_path x0) \<gamma>))
            (top1_path_product (top1_path_reverse \<gamma>) \<gamma>)"
          by (rule path_homotopic_product_right[OF hTX_weak hconst_\<gamma> hrev\<gamma>])
        have hrev_\<gamma>_cancel: "top1_path_homotopic_on ?X ?TX x1 x1
            (top1_path_product (top1_path_reverse \<gamma>) \<gamma>) (top1_constant_path x1)"
          by (rule Theorem_51_2_invgerse_right[OF hTX_weak h\<gamma>])
        have hbc_const_trivial: "top1_path_homotopic_on ?X ?TX x1 x1
            (top1_basepoint_change_on ?X ?TX x0 x1 \<gamma> (top1_constant_path x0))
            (top1_constant_path x1)"
          unfolding hbc_const
          by (rule Lemma_51_1_path_homotopic_trans[OF hTX_weak hrev_const_\<gamma> hrev_\<gamma>_cancel])
        \<comment> \<open>Chain: fa \<simeq> bc(\<gamma>, ?conj) \<simeq> bc(\<gamma>, const) \<simeq> const_{x1}.\<close>
        have hstepA: "top1_path_homotopic_on ?X ?TX x1 x1 fa
            (top1_basepoint_change_on ?X ?TX x0 x1 \<gamma> ?conj)"
          using hfa_roundtrip' hbc_eq by simp
        have hstepB: "top1_path_homotopic_on ?X ?TX x1 x1 fa
            (top1_basepoint_change_on ?X ?TX x0 x1 \<gamma> (top1_constant_path x0))"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTX_weak hstepA hbc_cong])
        show "top1_path_homotopic_on ?X ?TX x1 x1 fa (top1_constant_path x1)"
          by (rule Lemma_51_1_path_homotopic_trans[OF hTX_weak hstepB hbc_const_trivial])
      qed
    qed
  qed
  \<comment> \<open>But X = S^2 - {a, b} \<cong> R^2 - {0} which has nontrivial \<pi>_1.\<close>
  have hC_sub: "C \<subseteq> top1_S2" by (rule simple_closed_curve_subset[OF hC])
  have ha_S2: "a \<in> top1_S2"
    using hab hC_decomp hC_sub by (by100 blast)
  have hb_S2: "b \<in> top1_S2"
    using hab hC_decomp hC_sub by (by100 blast)
  have h_pi1_X_nontrivial: "\<not> top1_simply_connected_on ?X
      (subspace_topology top1_S2 top1_S2_topology ?X)"
    by (rule S2_minus_two_points_not_simply_connected[OF ha_S2 hb_S2 hab_ne])
  show False using h_pi1_X_trivial h_pi1_X_nontrivial by contradiction
qed

\<comment> \<open>Helper: a loop in S^2-{a,b} with image in S^2-A is nulhomotopic,
   when A is connected in S^2 and contains a,b. Used in Theorem 61.3 & 61.4.\<close>
lemma loop_nulhomotopic_via_connected_obstruction:
  assumes hA_sub: "A \<subseteq> top1_S2"
      and hA_conn: "top1_connected_on A (subspace_topology top1_S2 top1_S2_topology A)"
      and ha_A: "a \<in> A" and hb_A: "b \<in> A" and hab_ne: "a \<noteq> b"
      and ha_S2: "a \<in> top1_S2" and hb_S2: "b \<in> top1_S2"
      and hTX_strict: "is_topology_on_strict (top1_S2 - {a, b})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b}))"
      and hg_loop: "top1_is_loop_on (top1_S2 - {a, b})
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})) x0 g"
      and hg_sub: "g ` I_set \<subseteq> top1_S2 - A"
      and hx0: "x0 \<in> top1_S2 - {a, b}"
  shows "top1_path_homotopic_on (top1_S2 - {a, b})
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})) x0 x0
      g (top1_constant_path x0)"
proof -
  let ?X = "top1_S2 - {a, b}"
  let ?TX = "subspace_topology top1_S2 top1_S2_topology ?X"
  have hTX: "is_topology_on ?X ?TX"
    using hTX_strict unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>g(I) disjoint from A, so A \<subseteq> S^2-g(I).\<close>
  have hg_disj: "g ` I_set \<inter> A = {}" using hg_sub by (by100 blast)
  have hA_sub_comp: "A \<subseteq> top1_S2 - g ` I_set" using hg_disj hA_sub by (by100 blast)
  \<comment> \<open>a,b in same component of S^2-g(I) (A connected, A \<subseteq> S^2-g(I), a,b \<in> A).\<close>
  have hsame_comp: "\<exists>CC. CC \<in> top1_components_on (top1_S2 - g ` I_set)
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set))
      \<and> a \<in> CC \<and> b \<in> CC"
  proof -
    have hTS2gI: "is_topology_on (top1_S2 - g ` I_set)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set))"
      by (rule subspace_topology_is_topology_on[OF
          is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict]]) (by100 blast)
    have hA_conn_sub: "top1_connected_on A
        (subspace_topology (top1_S2 - g ` I_set)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set)) A)"
    proof -
      have "subspace_topology (top1_S2 - g ` I_set)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set)) A
          = subspace_topology top1_S2 top1_S2_topology A"
        by (rule subspace_topology_trans[OF hA_sub_comp])
      thus ?thesis using hA_conn by simp
    qed
    have hA_ne: "A \<noteq> {}" using ha_A by (by100 blast)
    obtain CC where hCC: "CC \<in> top1_components_on (top1_S2 - g ` I_set)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - g ` I_set))"
        and hA_CC: "A \<subseteq> CC"
      using Theorem_25_1(4)[OF hTS2gI hA_sub_comp hA_conn_sub hA_ne] by (by100 blast)
    show ?thesis using hCC hA_CC ha_A hb_A by (by100 blast)
  qed
  \<comment> \<open>Factor g through S^1.\<close>
  obtain h_S1 where hh_S1: "top1_continuous_map_on top1_S1 top1_S1_topology ?X ?TX h_S1"
      and hh_S1_10: "h_S1 (1, 0) = x0"
      and hg_factor: "\<forall>s\<in>I_set. g s = h_S1 (top1_R_to_S1 s)"
    using loop_factors_through_S1[OF hTX hg_loop] by (by100 blast)
  \<comment> \<open>h_S1(S^1) \<subseteq> S^2-A (since g(I) \<subseteq> S^2-A and g = h_S1 \<circ> p, p surjective onto S^1).\<close>
  have hh_S1_sub: "h_S1 ` top1_S1 \<subseteq> top1_S2 - A"
  proof
    fix y assume "y \<in> h_S1 ` top1_S1"
    then obtain q where hq: "q \<in> top1_S1" "y = h_S1 q" by (by100 blast)
    have "\<exists>t\<in>I_set. top1_R_to_S1 t = q"
    proof -
      obtain x y where hq_eq: "q = (x, y)" by (cases q)
      have hcirc: "x^2 + y^2 = 1" using hq hq_eq unfolding top1_S1_def by simp
      obtain t where ht: "0 \<le> t" "t < 2 * pi" "x = cos t" "y = sin t"
        using sincos_total_2pi[OF hcirc] by blast
      define t' where "t' = t / (2 * pi)"
      have ht'_range: "0 \<le> t'" "t' < 1" unfolding t'_def using ht(1,2) pi_gt_zero by auto
      hence "t' \<in> I_set" unfolding top1_unit_interval_def by simp
      moreover have "top1_R_to_S1 t' = q"
        unfolding top1_R_to_S1_def t'_def hq_eq using ht(3,4) pi_gt_zero by simp
      ultimately show ?thesis by (by100 blast)
    qed
    then obtain t where ht: "t \<in> I_set" "top1_R_to_S1 t = q" by blast
    have "y = g t" using hg_factor ht hq(2) by simp
    moreover have "g t \<in> top1_S2 - A" using hg_sub ht(1) by (by100 blast)
    ultimately show "y \<in> top1_S2 - A" by simp
  qed
  \<comment> \<open>h_S1 nulhomotopic via Lemma 61.2.\<close>
  have hh_S1_nul: "top1_nulhomotopic_on top1_S1 top1_S1_topology ?X ?TX h_S1"
  proof -
    have "h_S1 ` top1_S1 \<inter> A = {}" using hh_S1_sub by (by100 blast)
    hence hA_disj: "A \<subseteq> top1_S2 - h_S1 ` top1_S1" using hA_sub by (by100 blast)
    have hsame_S1: "\<exists>CC. CC \<in> top1_components_on (top1_S2 - h_S1 ` top1_S1)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1 ` top1_S1))
        \<and> a \<in> CC \<and> b \<in> CC"
    proof -
      have hTS2hS1: "is_topology_on (top1_S2 - h_S1 ` top1_S1)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1 ` top1_S1))"
        by (rule subspace_topology_is_topology_on[OF
            is_topology_on_strict_imp[OF top1_S2_is_topology_on_strict]]) (by100 blast)
      have hA_conn_sub: "top1_connected_on A
          (subspace_topology (top1_S2 - h_S1 ` top1_S1)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1 ` top1_S1)) A)"
      proof -
        have "subspace_topology (top1_S2 - h_S1 ` top1_S1)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1 ` top1_S1)) A
            = subspace_topology top1_S2 top1_S2_topology A"
          by (rule subspace_topology_trans[OF hA_disj])
        thus ?thesis using hA_conn by simp
      qed
      have hA_ne: "A \<noteq> {}" using ha_A by (by100 blast)
      obtain CC where hCC: "CC \<in> top1_components_on (top1_S2 - h_S1 ` top1_S1)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - h_S1 ` top1_S1))"
          and hA_CC: "A \<subseteq> CC"
        using Theorem_25_1(4)[OF hTS2hS1 hA_disj hA_conn_sub hA_ne] by (by100 blast)
      show ?thesis using hCC hA_CC ha_A hb_A by (by100 blast)
    qed
    show ?thesis
      by (rule Lemma_61_2_nulhomotopy_textbook[OF top1_S2_is_topology_on_strict
            S1_compact ha_S2 hb_S2 hab_ne hh_S1 hsame_S1])
  qed
  \<comment> \<open>Conclude: h_S1 nulhomotopic \<Rightarrow> h_S1 \<circ> p \<simeq> const \<Rightarrow> g \<simeq> const.\<close>
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    unfolding top1_S1_topology_def
    by (rule subspace_topology_is_topology_on[OF
        product_topology_on_is_topology_on[OF top1_open_sets_is_topology_on_UNIV
          top1_open_sets_is_topology_on_UNIV, simplified]]) simp
  have hstd_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1,0) (top1_R_to_S1)"
  proof -
    have hp_cont_R: "top1_continuous_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
      using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
    have hI_sub: "I_set \<subseteq> (UNIV::real set)" by simp
    have hp_cont_I: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology top1_R_to_S1"
      using top1_continuous_map_on_restrict_domain_simple[OF hp_cont_R hI_sub]
      unfolding top1_unit_interval_topology_def by simp
    have hp0: "top1_R_to_S1 0 = (1::real, 0::real)" unfolding top1_R_to_S1_def by simp
    have hp1: "top1_R_to_S1 1 = (1::real, 0::real)" unfolding top1_R_to_S1_def by simp
    show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
      using hp_cont_I hp0 hp1 by (by100 blast)
  qed
  have h10_S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by simp
  have "top1_path_homotopic_on ?X ?TX x0 x0 (h_S1 \<circ> top1_R_to_S1) (top1_constant_path x0)"
    by (rule nulhomotopic_trivializes_loops_general[OF hTS1 hTX hh_S1 hh_S1_nul hh_S1_10
          h10_S1 hstd_loop])
  moreover have "top1_path_homotopic_on ?X ?TX x0 x0 g (h_S1 \<circ> top1_R_to_S1)"
  proof -
    have hg_path: "top1_is_path_on ?X ?TX x0 x0 g"
      using hg_loop unfolding top1_is_loop_on_def by (by100 blast)
    have "\<forall>s\<in>I_set. g s = (h_S1 \<circ> top1_R_to_S1) s"
      using hg_factor unfolding comp_def by simp
    thus ?thesis by (rule paths_agree_on_I_path_homotopic[OF hTX hg_path])
  qed
  ultimately show ?thesis
    using Lemma_51_1_path_homotopic_trans[OF hTX] by (by100 blast)
qed

(** from \<S>61 Theorem 61.4: general separation theorem for S^2 **)
theorem Theorem_61_4_general_separation:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "A1 \<subseteq> top1_S2" and "A2 \<subseteq> top1_S2"
  and "closedin_on top1_S2 top1_S2_topology A1"
  and "closedin_on top1_S2 top1_S2_topology A2"
  and "top1_connected_on A1 (subspace_topology top1_S2 top1_S2_topology A1)"
  and "top1_connected_on A2 (subspace_topology top1_S2 top1_S2_topology A2)"
  and "card (A1 \<inter> A2) = 2"
  shows "top1_separates_on top1_S2 top1_S2_topology (A1 \<union> A2)"
proof -
  \<comment> \<open>Munkres 61.4: Write C=A1\<union>A2 with A1\<inter>A2={a,b}.
     X = S^2-{a,b} \<cong> R^2-{0}, U = S^2-A1, V = S^2-A2. X=U\<union>V.\<close>
  obtain a b where hab: "A1 \<inter> A2 = {a, b}" and hab_ne: "a \<noteq> b"
    using assms(8) card_2_iff by (by100 metis)
  let ?X = "top1_S2 - {a, b}" and ?U = "top1_S2 - A1" and ?V = "top1_S2 - A2"
  \<comment> \<open>X = U \<union> V and U \<inter> V = S^2 - (A1 \<union> A2).\<close>
  have hX_UV: "?U \<union> ?V = ?X" using hab by (by100 blast)
  have hUV_eq: "?U \<inter> ?V = top1_S2 - (A1 \<union> A2)" by (by100 blast)
  \<comment> \<open>If S^2 - (A1\<union>A2) were connected, then U\<inter>V would be path-connected.\<close>
  \<comment> \<open>By Lemma 61.2, loops in U and V are nulhomotopic (they factor through arcs).\<close>
  \<comment> \<open>So \<pi>_1(X) would be trivial. But X \<cong> R^2-{0} has nontrivial \<pi>_1. Contradiction.\<close>
  \<comment> \<open>Hence S^2 - (A1 \<union> A2) is NOT connected.\<close>
  \<comment> \<open>Same argument as Theorem 61.3: if S^2-(A1\<union>A2) were connected,
     then (using locally path-connected) it would be path-connected.
     Theorem 59.1 decomposes loops in X=S^2-{a,b} into loops in U, V.
     Each is nulhomotopic by textbook Lemma 61.2 (a,b in same component via
     A1 or A2 connected). So \<pi>_1(X) trivial. But X \<cong> R^2-{0} nontrivial. Contradiction.\<close>
  have hC_sub: "A1 \<union> A2 \<subseteq> top1_S2" using assms(2,3) by (by100 blast)
  have ha_S2: "a \<in> top1_S2" using assms(2) hab by (by100 blast)
  have hb_S2: "b \<in> top1_S2" using assms(2) hab by (by100 blast)
  show ?thesis
  proof (rule ccontr)
    assume hnot: "\<not> top1_separates_on top1_S2 top1_S2_topology (A1 \<union> A2)"
    have hconn: "top1_connected_on (top1_S2 - (A1 \<union> A2))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (A1 \<union> A2)))"
      using hnot unfolding top1_separates_on_def by (by100 blast)
    \<comment> \<open>By the same argument as Theorem 61.3, \<pi>_1(S^2-{a,b}) is trivial.\<close>
    have h_trivial: "top1_simply_connected_on ?X
        (subspace_topology top1_S2 top1_S2_topology ?X)"
    proof -
      \<comment> \<open>Same argument as Theorem 61.3, using closed+connected instead of arcs.
         U = S^2-A1, V = S^2-A2. X = U\<union>V. U\<inter>V = S^2-(A1\<union>A2) connected (assumption).
         A1 closed \<Rightarrow> U open. A2 closed \<Rightarrow> V open. U\<inter>V lpc \<Rightarrow> path-connected.
         Loops in U nulhomotopic (factor through S^1 + Lemma 61.2, A1 connected).
         Loops in V nulhomotopic (same with A2).
         Theorem 59.1 \<Rightarrow> \<pi>_1(X) trivial.\<close>
      \<comment> \<open>Setup: U,V open in S^2. U\<inter>V connected \<Rightarrow> path-connected (lpc).
         X = U\<union>V. is_topology_on_strict X TX.\<close>
      have hTS2: "is_topology_on top1_S2 top1_S2_topology"
        using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
      have hU_open: "?U \<in> top1_S2_topology"
        using assms(4) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      have hV_open: "?V \<in> top1_S2_topology"
        using assms(5) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
      \<comment> \<open>U\<inter>V open in S^2, hence lpc, hence path-connected (from connected + lpc).\<close>
      have hUV_open: "?U \<inter> ?V \<in> top1_S2_topology"
        by (rule topology_inter_open[OF hTS2 hU_open hV_open])
      have hUV_lpc: "top1_locally_path_connected_on (?U \<inter> ?V)
          (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V))"
      proof -
        have "?U \<inter> ?V \<subseteq> top1_S2" by (by100 blast)
        show ?thesis by (rule open_subset_locally_path_connected[OF
            S2_locally_path_connected hUV_open \<open>?U \<inter> ?V \<subseteq> top1_S2\<close>])
      qed
      have hTUV: "is_topology_on (?U \<inter> ?V)
          (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V))"
        by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
      have hUV_conn': "top1_connected_on (?U \<inter> ?V)
          (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V))"
        using hconn hUV_eq by simp
      have hUV_ne_inner: "?U \<inter> ?V \<noteq> {}"
        proof -
          \<comment> \<open>S^2\(A1\<union>A2) nonempty. S^2 uncountable, A1\<union>A2 \<neq> S^2 (otherwise S^2 = union of
             two closed connected sets with 2-point intersection, but S^2 is simply connected
             and this would give a separation — S^2 connected!).
             Actually simpler: A1\<union>A2 is proper closed subset of S^2 (not all of S^2).
             If A1\<union>A2 = S^2: then S^2 = A1\<union>A2 connected but S^2-A1 and S^2-A2 are open,
             nonempty (A2\A1 \<noteq> {} because |A1\<inter>A2|=2 but A2 connected ...).
             Actually: if A1\<union>A2 = S^2, then S^2\(A1\<union>A2) = {}, so it IS "connected" (vacuously).
             But hconn gives connected S^2\(A1\<union>A2) = connected {}, which IS true.
             So the proof by contradiction at the outer level needs S^2\(A1\<union>A2) \<noteq> {}.\<close>
          \<comment> \<open>A1\<union>A2 \<noteq> S^2 because S^2\{a,b} is connected but A1\{a,b}, A2\{a,b}
             would partition it into two closed sets if A1\<union>A2 = S^2.\<close>
          show ?thesis
          proof (rule ccontr)
            assume "\<not> ?thesis"
            hence "?U \<inter> ?V = {}" by simp
            hence "top1_S2 - (A1 \<union> A2) = {}" using hUV_eq by simp
            hence hAA_S2: "top1_S2 \<subseteq> A1 \<union> A2"
              by (by100 blast)
            hence hAA_S2': "A1 \<union> A2 = top1_S2"
              using assms(2,3) by (by100 blast)
            \<comment> \<open>S^2\{a,b} = (A1\{a,b}) \<union> (A2\{a,b}), disjoint (since A1\<inter>A2={a,b}).
               Both are closed in S^2\{a,b} (restrictions of closed A1,A2).
               S^2\{a,b} connected. So one must be empty.
               But A1 connected with \<ge>3 points means A1\{a,b} \<noteq> {}.
               Similarly A2\{a,b} \<noteq> {}. Contradiction.\<close>
            have "A1 - {a, b} \<noteq> {}"
            proof -
              \<comment> \<open>If A1 = {a,b}, then {a,b} connected. But {a,b} with a\<noteq>b is discrete
                 (singletons open in Hausdorff subspace), hence disconnected. Contradiction.\<close>
              have "A1 \<noteq> {a, b}"
              proof
                assume "A1 = {a, b}"
                have "{a} \<in> subspace_topology top1_S2 top1_S2_topology {a, b}"
                proof -
                  have "top1_S2 - {b} \<in> top1_S2_topology"
                    using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hb_S2]
                    hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
                  moreover have "{a} = {a, b} \<inter> (top1_S2 - {b})"
                    using hab_ne ha_S2 by auto
                  ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
                qed
                have "{b} \<in> subspace_topology top1_S2 top1_S2_topology {a, b}"
                proof -
                  have "top1_S2 - {a} \<in> top1_S2_topology"
                    using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff ha_S2]
                    hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
                  moreover have "{b} = {a, b} \<inter> (top1_S2 - {a})"
                    using hab_ne hb_S2 by auto
                  ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
                qed
                have "\<not> top1_connected_on {a, b} (subspace_topology top1_S2 top1_S2_topology {a, b})"
                  unfolding top1_connected_on_def
                  using \<open>{a} \<in> _\<close> \<open>{b} \<in> _\<close> hab_ne by (by100 blast)
                thus False using assms(6) \<open>A1 = {a, b}\<close> by simp
              qed
              moreover have "{a, b} \<subseteq> A1" using hab assms(2) by (by100 blast)
              ultimately show ?thesis by (by100 blast)
            qed
            have "A2 - {a, b} \<noteq> {}"
            proof -
              have "A2 \<noteq> {a, b}"
              proof
                assume "A2 = {a, b}"
                have "{a} \<in> subspace_topology top1_S2 top1_S2_topology {a, b}"
                proof -
                  have "top1_S2 - {b} \<in> top1_S2_topology"
                    using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hb_S2]
                    hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
                  moreover have "{a} = {a, b} \<inter> (top1_S2 - {b})"
                    using hab_ne ha_S2 by auto
                  ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
                qed
                have "{b} \<in> subspace_topology top1_S2 top1_S2_topology {a, b}"
                proof -
                  have "top1_S2 - {a} \<in> top1_S2_topology"
                    using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff ha_S2]
                    hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
                  moreover have "{b} = {a, b} \<inter> (top1_S2 - {a})"
                    using hab_ne hb_S2 by auto
                  ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
                qed
                have "\<not> top1_connected_on {a, b} (subspace_topology top1_S2 top1_S2_topology {a, b})"
                  unfolding top1_connected_on_def
                  using \<open>{a} \<in> _\<close> \<open>{b} \<in> _\<close> hab_ne by (by100 blast)
                thus False using assms(7) \<open>A2 = {a, b}\<close> by simp
              qed
              moreover have "{a, b} \<subseteq> A2" using hab assms(3) by (by100 blast)
              ultimately show ?thesis by (by100 blast)
            qed
            \<comment> \<open>(A1\{a,b}) \<union> (A2\{a,b}) = S^2\{a,b} and disjoint. Both closed. Both nonempty.
               S^2\{a,b} disconnected. But S^2\{a,b} IS connected. Contradiction.\<close>
            have "connected (top1_S2 - {a, b})"
            proof -
              have h_S2a_open: "top1_S2 - {a} \<in> top1_S2_topology"
              proof -
                have "closedin_on top1_S2 top1_S2_topology {a}"
                  by (rule singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff ha_S2])
                thus ?thesis using hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
              qed
              have h_S2a_conn: "top1_connected_on (top1_S2 - {a})
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))"
                by (rule path_connected_imp_connected)
                   (use S2_minus_point_simply_connected[OF ha_S2] in
                    \<open>unfold top1_simply_connected_on_def, by100 blast\<close>)
              have "b \<in> top1_S2 - {a}" using hb_S2 hab_ne by (by100 blast)
              have "\<exists>c. c \<in> top1_S2 \<and> c \<notin> (top1_S2 - {a})" using ha_S2 by (by100 blast)
              have "connected ((top1_S2 - {a}) - {b})"
                by (rule connected_open_delete_S2[OF h_S2a_open h_S2a_conn
                    \<open>b \<in> top1_S2 - {a}\<close> \<open>\<exists>c. c \<in> top1_S2 \<and> c \<notin> (top1_S2 - {a})\<close>])
              moreover have "(top1_S2 - {a}) - {b} = top1_S2 - {a, b}" by (by100 blast)
              ultimately show ?thesis by simp
            qed
            \<comment> \<open>A1\{a,b} and A2\{a,b} are both clopen in S^2\{a,b} (standard topology).
               Both nonempty. Their union = S^2\{a,b}. So S^2\{a,b} disconnected.
               But connected (S^2\{a,b}). Contradiction.\<close>
            have hpart: "(A1 - {a, b}) \<union> (A2 - {a, b}) = top1_S2 - {a, b}"
              using hAA_S2' hab by (by100 blast)
            have hdisj_part: "(A1 - {a, b}) \<inter> (A2 - {a, b}) = {}"
              using hab by (by100 blast)
            \<comment> \<open>A1 closed in S^2 \<Rightarrow> A1\{a,b} closed in S^2\{a,b} (standard).
               Complement A2\{a,b} = (S^2\A1) \<inter> (S^2\{a,b}) open in S^2\{a,b} (standard).
               So A1\{a,b} also open (complement of closed in closed = open... no, complement of open).\<close>
            \<comment> \<open>Actually: both A1\{a,b} and A2\{a,b} are closed in standard S^2\{a,b}.
               Complement of each = the other = also closed. So both are open too (clopen).\<close>
            \<comment> \<open>A1, A2 closed in R^3 (closed in S^2 and S^2 closed in R^3).\<close>
            have "closed (A1 :: (real\<times>real\<times>real) set)"
            proof -
              have "closed top1_S2" by (rule compact_imp_closed[OF S2_compact_standard])
              \<comment> \<open>A1 closed in S^2: S^2\A1 open in S^2. S^2\A1 = S^2 \<inter> W for open W.
                 A1 = S^2 \<inter> (-W). closed S^2, closed (-W) \<Rightarrow> closed (S^2 \<inter> (-W)).\<close>
              have "top1_S2 - A1 \<in> top1_S2_topology"
                using assms(4) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
              have hR3eq: "top1_S2_topology = subspace_topology UNIV
                  (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                unfolding top1_S2_topology_def
                using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                      product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
              obtain W where "W \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
                  "top1_S2 - A1 = top1_S2 \<inter> W"
                using \<open>top1_S2 - A1 \<in> top1_S2_topology\<close> hR3eq
                unfolding subspace_topology_def by (by100 blast)
              have "open W" using \<open>W \<in> top1_open_sets\<close> unfolding top1_open_sets_def by simp
              have "A1 = top1_S2 \<inter> (- W)"
                using \<open>top1_S2 - A1 = top1_S2 \<inter> W\<close> assms(2) by (by100 blast)
              have "closed (- W)" using \<open>open W\<close> by (simp add: open_closed)
              show ?thesis using \<open>A1 = top1_S2 \<inter> (- W)\<close> \<open>closed top1_S2\<close> \<open>closed (- W)\<close>
                by (simp add: closed_Int)
            qed
            have "closed (A2 :: (real\<times>real\<times>real) set)"
            proof -
              have "closed top1_S2" by (rule compact_imp_closed[OF S2_compact_standard])
              have "top1_S2 - A2 \<in> top1_S2_topology"
                using assms(5) hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
              have hR3eq: "top1_S2_topology = subspace_topology UNIV
                  (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                unfolding top1_S2_topology_def
                using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                      product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
              obtain W where "W \<in> (top1_open_sets :: (real\<times>real\<times>real) set set)"
                  "top1_S2 - A2 = top1_S2 \<inter> W"
                using \<open>top1_S2 - A2 \<in> top1_S2_topology\<close> hR3eq
                unfolding subspace_topology_def by (by100 blast)
              have "open W" using \<open>W \<in> top1_open_sets\<close> unfolding top1_open_sets_def by simp
              have "A2 = top1_S2 \<inter> (- W)"
                using \<open>top1_S2 - A2 = top1_S2 \<inter> W\<close> assms(3) by (by100 blast)
              have "closed (- W)" using \<open>open W\<close> by (simp add: open_closed)
              show ?thesis using \<open>A2 = top1_S2 \<inter> (- W)\<close> \<open>closed top1_S2\<close> \<open>closed (- W)\<close>
                by (simp add: closed_Int)
            qed
            \<comment> \<open>-A1, -A2 open. Form a separation of S^2\{a,b}:
               S^2\{a,b} \<subseteq> (-A1) \<union> (-A2), (-A1)\<inter>(-A2)\<inter>(S^2\{a,b}) = {},
               both intersections nonempty. Contradicts connected.\<close>
            have "open (- A1)" using \<open>closed A1\<close> by (rule open_Compl)
            have "open (- A2)" using \<open>closed A2\<close> by (rule open_Compl)
            have "\<not> connected (top1_S2 - {a, b})"
              unfolding connected_def
            proof (intro notI)
              assume "\<not> (\<exists>A B. open A \<and> open B \<and> top1_S2 - {a, b} \<subseteq> A \<union> B \<and>
                  A \<inter> B \<inter> (top1_S2 - {a, b}) = {} \<and> A \<inter> (top1_S2 - {a, b}) \<noteq> {} \<and>
                  B \<inter> (top1_S2 - {a, b}) \<noteq> {})"
              \<comment> \<open>Exhibit separation: A = -A2, B = -A1.\<close>
              have h1: "top1_S2 - {a, b} \<subseteq> (- A2) \<union> (- A1)"
                using hAA_S2' hab by auto
              have h2: "(- A2) \<inter> (- A1) \<inter> (top1_S2 - {a, b}) = {}"
                using hAA_S2' by auto
              have h3: "(- A2) \<inter> (top1_S2 - {a, b}) \<noteq> {}"
                using \<open>A1 - {a, b} \<noteq> {}\<close> hAA_S2' assms(2) hab by auto
              have h4: "(- A1) \<inter> (top1_S2 - {a, b}) \<noteq> {}"
                using \<open>A2 - {a, b} \<noteq> {}\<close> hAA_S2' assms(3) hab by auto
              thus False
                using \<open>\<not> (\<exists>A B. _)\<close> \<open>open (- A1)\<close> \<open>open (- A2)\<close> h1 h2 h3 h4 by blast
            qed
            show False using \<open>connected (top1_S2 - {a, b})\<close> \<open>\<not> connected (top1_S2 - {a, b})\<close>
              by contradiction
          qed
        qed
      have hUV_pc: "top1_path_connected_on (?U \<inter> ?V)
          (subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V))"
        by (rule connected_locally_path_connected_imp_path_connected[OF
            hTUV hUV_conn' hUV_lpc hUV_ne_inner])
      \<comment> \<open>X = S^2\{a,b} is strict topology (subspace of strict S^2).\<close>
      have hTX_strict: "is_topology_on_strict ?X
          (subspace_topology top1_S2 top1_S2_topology ?X)"
        by (rule subspace_topology_is_strict[OF assms(1)]) (by100 blast)
      \<comment> \<open>U, V open in X.\<close>
      have hU_open_X: "openin_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) ?U"
      proof -
        have "?U \<subseteq> ?X" using hab by (by100 blast)
        have "?U = ?X \<inter> ?U" using hab by (by100 blast)
        hence "?U \<in> subspace_topology top1_S2 top1_S2_topology ?X"
          using hU_open unfolding subspace_topology_def by (by100 blast)
        thus ?thesis using \<open>?U \<subseteq> ?X\<close> unfolding openin_on_def by (by100 blast)
      qed
      have hV_open_X: "openin_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) ?V"
      proof -
        have "?V \<subseteq> ?X" using hab by (by100 blast)
        have "?V = ?X \<inter> ?V" using hab by (by100 blast)
        hence "?V \<in> subspace_topology top1_S2 top1_S2_topology ?X"
          using hV_open unfolding subspace_topology_def by (by100 blast)
        thus ?thesis using \<open>?V \<subseteq> ?X\<close> unfolding openin_on_def by (by100 blast)
      qed
      \<comment> \<open>U\<inter>V path-connected in X topology.\<close>
      have hUV_sub_X: "?U \<inter> ?V \<subseteq> ?X" using hab by (by100 blast)
      have hUV_pc_X: "top1_path_connected_on (?U \<inter> ?V)
          (subspace_topology ?X (subspace_topology top1_S2 top1_S2_topology ?X) (?U \<inter> ?V))"
      proof -
        have "subspace_topology ?X (subspace_topology top1_S2 top1_S2_topology ?X) (?U \<inter> ?V)
            = subspace_topology top1_S2 top1_S2_topology (?U \<inter> ?V)"
          by (rule subspace_topology_trans[OF hUV_sub_X])
        thus ?thesis using hUV_pc by simp
      qed
      \<comment> \<open>x0 \<in> U\<inter>V.\<close>
      \<comment> \<open>U\<inter>V nonempty: S^2 connected, A1,A2 closed connected with |A1\<inter>A2|=2 \<Rightarrow>
         A1\<union>A2 \<noteq> S^2 (proved inside hUV_pc via partition argument).\<close>
      have hUV_ne: "?U \<inter> ?V \<noteq> {}" by (rule hUV_ne_inner)
      obtain x0 where hx0: "x0 \<in> ?U \<inter> ?V"
        using hUV_ne by (by100 blast)
      \<comment> \<open>By Theorem 59.1: every loop in X decomposes into pieces in U and V.
         Each piece in U is nulhomotopic (via Lemma 61.2 + A1 connected).
         Each piece in V is nulhomotopic (via Lemma 61.2 + A2 connected).
         Hence every loop in X is nulhomotopic: X simply connected.\<close>
      \<comment> \<open>Core argument: every loop in X at x0 is nulhomotopic.
         Step A: decompose loop via Theorem 59.1.
         Step B: each piece gᵢ in U or V is nulhomotopic.
         Step C: product of nulhomotopic = nulhomotopic.\<close>
      show ?thesis unfolding top1_simply_connected_on_def
      proof (intro conjI)
        \<comment> \<open>Path-connected: X = U \<union> V, U,V open, U\<inter>V path-connected.\<close>
        show "top1_path_connected_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)"
        proof -
          \<comment> \<open>X = S^2\{a,b} open in S^2. S^2 lpc. Open subset of lpc = lpc.
             X connected (proved in hUV_ne_inner). Connected + lpc = path-connected.\<close>
          have hX_open: "?X \<in> top1_S2_topology"
          proof -
            have "{a,b} \<subseteq> top1_S2" using ha_S2 hb_S2 by (by100 blast)
            have "closedin_on top1_S2 top1_S2_topology {a,b}"
            proof -
              have "closedin_on top1_S2 top1_S2_topology {a}"
                by (rule singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff ha_S2])
              have "closedin_on top1_S2 top1_S2_topology {b}"
                by (rule singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hb_S2])
              show ?thesis unfolding closedin_on_def
              proof (intro conjI)
                show "{a,b} \<subseteq> top1_S2" using ha_S2 hb_S2 by (by100 blast)
                show "top1_S2 - {a,b} \<in> top1_S2_topology"
                proof -
                  have "top1_S2 - {a} \<in> top1_S2_topology"
                    using \<open>closedin_on top1_S2 top1_S2_topology {a}\<close>
                    hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
                  have "top1_S2 - {b} \<in> top1_S2_topology"
                    using \<open>closedin_on top1_S2 top1_S2_topology {b}\<close>
                    hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
                  have "top1_S2 - {a,b} = (top1_S2 - {a}) \<inter> (top1_S2 - {b})" by (by100 blast)
                  thus ?thesis using topology_inter_open[OF hTS2
                      \<open>top1_S2 - {a} \<in> top1_S2_topology\<close> \<open>top1_S2 - {b} \<in> top1_S2_topology\<close>]
                    by simp
                qed
              qed
            qed
            thus ?thesis using hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
          qed
          have hX_lpc: "top1_locally_path_connected_on ?X
              (subspace_topology top1_S2 top1_S2_topology ?X)"
          proof -
            have "?X \<subseteq> top1_S2" by (by100 blast)
            show ?thesis by (rule open_subset_locally_path_connected[OF
                S2_locally_path_connected hX_open \<open>?X \<subseteq> top1_S2\<close>])
          qed
          have hTX_is: "is_topology_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)"
            by (rule subspace_topology_is_topology_on[OF hTS2]) (by100 blast)
          have hX_conn: "top1_connected_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)"
          proof -
            have "connected (top1_S2 - {a, b})"
            proof -
              have h_S2a_open: "top1_S2 - {a} \<in> top1_S2_topology"
                using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff ha_S2]
                hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
              have h_S2a_conn: "top1_connected_on (top1_S2 - {a})
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))"
                by (rule path_connected_imp_connected)
                   (use S2_minus_point_simply_connected[OF ha_S2] in
                    \<open>unfold top1_simply_connected_on_def, by100 blast\<close>)
              have "b \<in> top1_S2 - {a}" using hb_S2 hab_ne by (by100 blast)
              have "\<exists>c. c \<in> top1_S2 \<and> c \<notin> (top1_S2 - {a})" using ha_S2 by (by100 blast)
              have "connected ((top1_S2 - {a}) - {b})"
                by (rule connected_open_delete_S2[OF h_S2a_open h_S2a_conn
                    \<open>b \<in> top1_S2 - {a}\<close> \<open>\<exists>c. c \<in> top1_S2 \<and> c \<notin> (top1_S2 - {a})\<close>])
              moreover have "(top1_S2 - {a}) - {b} = top1_S2 - {a, b}" by (by100 blast)
              ultimately show ?thesis by simp
            qed
            hence "top1_connected_on (top1_S2 - {a, b})
                (subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) (top1_S2 - {a, b}))"
              using top1_connected_on_subspace_open_iff_connected by (by100 blast)
            moreover have "subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})
                = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) (top1_S2 - {a, b})"
            proof -
              have hR3eq: "top1_S2_topology = subspace_topology UNIV
                  (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                unfolding top1_S2_topology_def
                using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                      product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
              have "subspace_topology top1_S2 (subspace_topology UNIV
                  (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2) (top1_S2 - {a, b})
                  = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) (top1_S2 - {a, b})"
                by (rule subspace_topology_trans) blast
              thus ?thesis using hR3eq by simp
            qed
            ultimately show ?thesis by simp
          qed
          have "?X \<noteq> {}" using hUV_ne hX_UV by (by100 blast)
          show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF
              hTX_is hX_conn hX_lpc \<open>?X \<noteq> {}\<close>])
        qed
        \<comment> \<open>All loops nulhomotopic: by Theorem 59.1 + Lemma 61.2.\<close>
        have hTX_weak: "is_topology_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)"
          using hTX_strict unfolding is_topology_on_strict_def by (by100 blast)
        have hx0X: "x0 \<in> ?X" using hx0 hX_UV by (by100 blast)
        \<comment> \<open>Core: all loops at x0 are nulhomotopic (59.1 decomposition + 61.2).\<close>
        have hx0_all_nul: "\<And>g. top1_is_loop_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 g \<Longrightarrow>
            top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 x0
              g (top1_constant_path x0)"
        proof -
          fix g assume hg_x0: "top1_is_loop_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 g"
          \<comment> \<open>Same structure as True case: hU_nul, hV_nul, 59.1 decomposition, foldr.\<close>
          show "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 x0
              g (top1_constant_path x0)"
          proof -
            \<comment> \<open>hU_nul for g: any loop at x0 mapping into U is nulhomotopic.\<close>
            have ha_A1: "a \<in> A1" using hab by (by100 blast)
            have hb_A1: "b \<in> A1" using hab by (by100 blast)
            have ha_A2: "a \<in> A2" using hab by (by100 blast)
            have hb_A2: "b \<in> A2" using hab by (by100 blast)
            have hU_nul_g: "\<And>h. top1_is_loop_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 h
                \<Longrightarrow> h ` I_set \<subseteq> ?U \<Longrightarrow>
                top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 x0
                  h (top1_constant_path x0)"
              using loop_nulhomotopic_via_connected_obstruction[OF assms(2) assms(6)
                  ha_A1 hb_A1 hab_ne ha_S2 hb_S2 hTX_strict] hx0X by (by100 blast)
            have hV_nul_g: "\<And>h. top1_is_loop_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 h
                \<Longrightarrow> h ` I_set \<subseteq> ?V \<Longrightarrow>
                top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 x0
                  h (top1_constant_path x0)"
              using loop_nulhomotopic_via_connected_obstruction[OF assms(3) assms(7)
                  ha_A2 hb_A2 hab_ne ha_S2 hb_S2 hTX_strict] hx0X by (by100 blast)
            obtain n gs where hn: "n \<ge> 1" and hlen: "length gs = n"
                and hgi: "\<forall>i<n. top1_is_loop_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 (gs!i)
                    \<and> (gs!i ` I_set \<subseteq> ?U \<or> gs!i ` I_set \<subseteq> ?V)"
                and hg_prod: "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 x0
                    g (foldr top1_path_product gs (top1_constant_path x0))"
            proof -
              from Theorem_59_1[OF hTX_strict hU_open_X hV_open_X hX_UV hUV_pc_X hx0, rule_format, OF hg_x0]
              obtain n' gs' where "n' \<ge> 1" "length gs' = n'"
                  "\<forall>i<n'. top1_is_loop_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 (gs' ! i) \<and>
                    (gs' ! i ` I_set \<subseteq> ?U \<or> gs' ! i ` I_set \<subseteq> ?V)"
                  "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 x0
                    g (foldr top1_path_product gs' (top1_constant_path x0))"
                by blast
              show ?thesis
              proof (rule that[of n' gs'])
                show "1 \<le> n'" using \<open>n' \<ge> 1\<close> .
                show "length gs' = n'" using \<open>length gs' = n'\<close> .
                show "\<forall>i<n'. top1_is_loop_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)
                    x0 (gs' ! i) \<and> (gs' ! i ` I_set \<subseteq> ?U \<or> gs' ! i ` I_set \<subseteq> ?V)"
                  using \<open>\<forall>i<n'. _\<close> .
                show "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)
                    x0 x0 g (foldr top1_path_product gs' (top1_constant_path x0))"
                  using \<open>top1_path_homotopic_on _ _ _ _ g _\<close> .
              qed
            qed
            have hgi_nul: "\<forall>i < length gs.
                top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 x0
                  (gs!i) (top1_constant_path x0)"
            proof (intro allI impI)
              fix i assume "i < length gs"
              hence "top1_is_loop_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 (gs!i)
                  \<and> (gs!i ` I_set \<subseteq> ?U \<or> gs!i ` I_set \<subseteq> ?V)"
                using hgi hlen by simp
              thus "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 x0
                  (gs!i) (top1_constant_path x0)"
              proof (elim conjE disjE)
                assume "top1_is_loop_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 (gs!i)"
                    "gs!i ` I_set \<subseteq> ?U"
                thus ?thesis using hU_nul_g by (by100 blast)
              next
                assume "top1_is_loop_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 (gs!i)"
                    "gs!i ` I_set \<subseteq> ?V"
                thus ?thesis using hV_nul_g by (by100 blast)
              qed
            qed
            have "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 x0
                (foldr top1_path_product gs (top1_constant_path x0)) (top1_constant_path x0)"
              by (rule foldr_path_product_nulhomotopic[OF hTX_weak hx0X hgi_nul])
            thus ?thesis using hg_prod
              Lemma_51_1_path_homotopic_trans[OF hTX_weak] by (by100 blast)
          qed
        qed
        show "\<forall>x0\<in>?X. \<forall>f. top1_is_loop_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 f \<longrightarrow>
            top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 x0
              f (top1_constant_path x0)"
        proof (intro ballI allI impI)
          fix y0 f
          assume hy0: "y0 \<in> ?X" and hf: "top1_is_loop_on ?X
              (subspace_topology top1_S2 top1_S2_topology ?X) y0 f"
          \<comment> \<open>Key: every loop g at x0 that maps into U (or V) is nulhomotopic.
             g factors through S^1 (loop_factors_through_S1). The S^1 map h satisfies:
             h(S^1) \<subseteq> U = S^2\A1, so A1 \<subseteq> S^2\h(S^1). A1 connected, {a,b} \<subseteq> A1.
             By Lemma 61.2: h nulhomotopic. By nulhomotopic_trivializes_loops_general:
             g = h\<circ>p \<simeq> const. Same for V with A2.\<close>
          \<comment> \<open>Step 1: Reduce to x0 basepoint (conjugation).\<close>
          \<comment> \<open>Step 2: Decompose via Theorem 59.1.\<close>
          \<comment> \<open>Step 3: Each piece in U/V nulhomotopic.\<close>
          \<comment> \<open>Step 4: Product of nulhomotopic = nulhomotopic.\<close>
          \<comment> \<open>Handle basepoint: if y0 = x0 use directly, else conjugate.\<close>
          have hTX_weak: "is_topology_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)"
            using hTX_strict unfolding is_topology_on_strict_def by (by100 blast)
          have hx0X: "x0 \<in> ?X" using hx0 hX_UV by (by100 blast)
          show "top1_path_homotopic_on ?X
              (subspace_topology top1_S2 top1_S2_topology ?X) y0 y0
              f (top1_constant_path y0)"
          proof (cases "y0 = x0")
            case True
            thus ?thesis using hx0_all_nul[OF hf[simplified True]] True by simp
          next
            case False
            \<comment> \<open>y0 \<noteq> x0: conjugate. Get path \<alpha>: x0 \<rightarrow> y0 in X (X path-connected).
               Then \<alpha>^{-1}*f*\<alpha> is a loop at x0, nulhomotopic by the True case.
               Hence f nulhomotopic at y0.\<close>
            \<comment> \<open>Conjugation: get \<gamma>: x0 \<rightarrow> y0. bc(\<gamma>, f) = \<gamma> * f * rev(\<gamma>) is loop at x0.
               Nulhomotopic by True case. Unconjugate via bc roundtrip.\<close>
            \<comment> \<open>Get path \<gamma>: x0 \<rightarrow> y0 (X path-connected).\<close>
            obtain \<gamma> where h\<gamma>: "top1_is_path_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 y0 \<gamma>"
            proof -
              have "top1_path_connected_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)"
              proof -
                have hX_open: "?X \<in> top1_S2_topology"
                proof -
                  have "closedin_on top1_S2 top1_S2_topology {a}"
                    by (rule singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff ha_S2])
                  have "closedin_on top1_S2 top1_S2_topology {b}"
                    by (rule singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff hb_S2])
                  have "closedin_on top1_S2 top1_S2_topology {a,b}"
                    unfolding closedin_on_def
                  proof (intro conjI)
                    show "{a,b} \<subseteq> top1_S2" using ha_S2 hb_S2 by (by100 blast)
                    show "top1_S2 - {a,b} \<in> top1_S2_topology"
                    proof -
                      have "top1_S2 - {a} \<in> top1_S2_topology"
                        using \<open>closedin_on top1_S2 top1_S2_topology {a}\<close>
                        hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
                      have "top1_S2 - {b} \<in> top1_S2_topology"
                        using \<open>closedin_on top1_S2 top1_S2_topology {b}\<close>
                        hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
                      have "top1_S2 - {a,b} = (top1_S2 - {a}) \<inter> (top1_S2 - {b})" by (by100 blast)
                      thus ?thesis using topology_inter_open[OF hTS2
                          \<open>top1_S2 - {a} \<in> top1_S2_topology\<close> \<open>top1_S2 - {b} \<in> top1_S2_topology\<close>]
                        by simp
                    qed
                  qed
                  thus ?thesis using hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
                qed
                have hX_lpc2: "top1_locally_path_connected_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)"
                  by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hX_open]) blast
                have hX_conn2: "top1_connected_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)"
                proof -
                  have "connected (top1_S2 - {a, b})"
                  proof -
                    have "top1_S2 - {a} \<in> top1_S2_topology"
                      using singleton_closed_in_hausdorff[OF top1_S2_is_hausdorff ha_S2]
                      hTS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
                    have "top1_connected_on (top1_S2 - {a})
                        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a}))"
                      by (rule path_connected_imp_connected)
                         (use S2_minus_point_simply_connected[OF ha_S2] in
                          \<open>unfold top1_simply_connected_on_def, by100 blast\<close>)
                    have "b \<in> top1_S2 - {a}" using hb_S2 hab_ne by (by100 blast)
                    have "\<exists>c. c \<in> top1_S2 \<and> c \<notin> (top1_S2 - {a})" using ha_S2 by (by100 blast)
                    have "connected ((top1_S2 - {a}) - {b})"
                      by (rule connected_open_delete_S2[OF \<open>top1_S2 - {a} \<in> top1_S2_topology\<close>
                          \<open>top1_connected_on (top1_S2 - {a}) _\<close> \<open>b \<in> top1_S2 - {a}\<close>
                          \<open>\<exists>c. _\<close>])
                    moreover have "(top1_S2 - {a}) - {b} = top1_S2 - {a, b}" by (by100 blast)
                    ultimately show ?thesis by simp
                  qed
                  hence "top1_connected_on (top1_S2 - {a, b})
                      (subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) (top1_S2 - {a, b}))"
                    using top1_connected_on_subspace_open_iff_connected by (by100 blast)
                  moreover have "subspace_topology top1_S2 top1_S2_topology (top1_S2 - {a, b})
                      = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) (top1_S2 - {a, b})"
                  proof -
                    have hR3eq: "top1_S2_topology = subspace_topology UNIV
                        (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2"
                      unfolding top1_S2_topology_def
                      using product_topology_on_open_sets[where ?'a=real and ?'b="real \<times> real"]
                            product_topology_on_open_sets[where ?'a=real and ?'b=real] by simp
                    have "subspace_topology top1_S2 (subspace_topology UNIV
                        (top1_open_sets :: (real\<times>real\<times>real) set set) top1_S2) (top1_S2 - {a, b})
                        = subspace_topology UNIV (top1_open_sets :: (real\<times>real\<times>real) set set) (top1_S2 - {a, b})"
                      by (rule subspace_topology_trans) blast
                    thus ?thesis using hR3eq by simp
                  qed
                  ultimately show ?thesis by simp
                qed
                show ?thesis by (rule connected_locally_path_connected_imp_path_connected[OF
                    hTX_weak hX_conn2 hX_lpc2]) (use hUV_ne hX_UV in blast)
              qed
              thus ?thesis using that hx0X hy0 unfolding top1_path_connected_on_def by blast
            qed
            have hrev\<gamma>: "top1_is_path_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) y0 x0 (top1_path_reverse \<gamma>)"
              by (rule top1_path_reverse_is_path[OF h\<gamma>])
            \<comment> \<open>Conjugate: bc(rev(\<gamma>), f) = \<gamma> * f * rev(\<gamma>) is loop at x0.\<close>
            let ?conj = "top1_basepoint_change_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) y0 x0 (top1_path_reverse \<gamma>) f"
            have hconj_loop: "top1_is_loop_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 ?conj"
              by (rule top1_basepoint_change_is_loop[OF hTX_weak hrev\<gamma> hf])
            \<comment> \<open>Conjugated loop nulhomotopic by hx0_all_nul.\<close>
            have hconj_triv: "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 x0
                ?conj (top1_constant_path x0)"
              by (rule hx0_all_nul[OF hconj_loop])
            \<comment> \<open>Unconjugate: f \<simeq> bc(\<gamma>, conj) by roundtrip, then congruence + constant.\<close>
            have hf_conj: "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) y0 y0 f
                (top1_basepoint_change_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 y0 \<gamma> ?conj)"
            proof -
              have "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) y0 y0 f
                  (top1_basepoint_change_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 y0
                    (top1_path_reverse (top1_path_reverse \<gamma>)) ?conj)"
                by (rule top1_basepoint_change_roundtrip[OF hTX_weak hrev\<gamma> hf])
              thus ?thesis by (simp add: top1_path_reverse_twice)
            qed
            have hconst_loop: "top1_is_loop_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 (top1_constant_path x0)"
              by (rule top1_constant_path_is_loop[OF hTX_weak hx0X])
            have hbc_cong: "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) y0 y0
                (top1_basepoint_change_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 y0 \<gamma> ?conj)
                (top1_basepoint_change_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 y0 \<gamma> (top1_constant_path x0))"
              by (rule top1_basepoint_change_congruence[OF hTX_weak h\<gamma> hconj_loop hconst_loop hconj_triv])
            have hbc_const: "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) y0 y0
                (top1_basepoint_change_on ?X (subspace_topology top1_S2 top1_S2_topology ?X) x0 y0 \<gamma> (top1_constant_path x0))
                (top1_constant_path y0)"
            proof -
              \<comment> \<open>bc(\<gamma>, const_x0) = rev(\<gamma>) * (const_x0 * \<gamma>).\<close>
              have "top1_basepoint_change_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)
                  x0 y0 \<gamma> (top1_constant_path x0)
                  = top1_path_product (top1_path_reverse \<gamma>)
                      (top1_path_product (top1_constant_path x0) \<gamma>)"
                unfolding top1_basepoint_change_on_def by simp
              \<comment> \<open>const_x0 * \<gamma> \<simeq> \<gamma> (left identity).\<close>
              have hleft: "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)
                  x0 y0 (top1_path_product (top1_constant_path x0) \<gamma>) \<gamma>"
                by (rule Theorem_51_2_left_identity[OF hTX_weak h\<gamma>])
              \<comment> \<open>rev(\<gamma>) * \<gamma> \<simeq> const_y0 (inverse right).\<close>
              have "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)
                  y0 y0 (top1_path_product (top1_path_reverse \<gamma>) \<gamma>) (top1_constant_path y0)"
                by (rule Theorem_51_2_invgerse_right[OF hTX_weak h\<gamma>])
              \<comment> \<open>rev(\<gamma>) * (const * \<gamma>) \<simeq> rev(\<gamma>) * \<gamma> (right congruence).\<close>
              have "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)
                  y0 y0 (top1_path_product (top1_path_reverse \<gamma>) (top1_path_product (top1_constant_path x0) \<gamma>))
                  (top1_path_product (top1_path_reverse \<gamma>) \<gamma>)"
                by (rule path_homotopic_product_right[OF hTX_weak hleft hrev\<gamma>])
              \<comment> \<open>Chain: bc(\<gamma>,const) = rev(\<gamma>)*(const*\<gamma>) \<simeq> rev(\<gamma>)*\<gamma> \<simeq> const_y0.\<close>
              \<comment> \<open>bc = rev(\<gamma>)*(const*\<gamma>) \<simeq> rev(\<gamma>)*\<gamma> \<simeq> const_y0.\<close>
              hence "top1_path_homotopic_on ?X (subspace_topology top1_S2 top1_S2_topology ?X)
                  y0 y0 (top1_path_product (top1_path_reverse \<gamma>) (top1_path_product (top1_constant_path x0) \<gamma>))
                  (top1_constant_path y0)"
                using \<open>top1_path_homotopic_on _ _ _ _ (top1_path_product (top1_path_reverse \<gamma>) \<gamma>) _\<close>
                  Lemma_51_1_path_homotopic_trans[OF hTX_weak]
                by (by100 blast)
              thus ?thesis
                using \<open>top1_basepoint_change_on _ _ _ _ _ _ = _\<close> by simp
            qed
            show ?thesis using hf_conj hbc_cong hbc_const
              Lemma_51_1_path_homotopic_trans[OF hTX_weak] by (by100 blast)
          qed
        qed
      qed
    qed
    have h_nontrivial: "\<not> top1_simply_connected_on ?X
        (subspace_topology top1_S2 top1_S2_topology ?X)"
      by (rule S2_minus_two_points_not_simply_connected[OF ha_S2 hb_S2 hab_ne])
    show False using h_trivial h_nontrivial by contradiction
  qed
qed



end
