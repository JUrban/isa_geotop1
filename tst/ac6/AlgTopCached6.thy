theory AlgTopCached6
  imports "AlgTopCached5.AlgTopCached5"
begin

text \<open>Reviewer-requested: connected graph has a maximal tree (Munkres Lemma 84.3).
  A maximal tree T is one where no strictly larger subtree of X is also a tree.\<close>
lemma connected_graph_has_maximal_tree:
  assumes "top1_is_graph_on X TX"
      and "top1_connected_on X TX"
      and "x0 \<in> X"
      and h\<A>X: "\<forall>A\<in>\<A>X. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and h\<A>X_cover: "\<Union>\<A>X = X"
      and h\<A>X_inter: "\<forall>A\<in>\<A>X. \<forall>B\<in>\<A>X. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and h\<A>X_coh: "\<forall>C. C \<subseteq> X \<longrightarrow>
           (closedin_on X TX C \<longleftrightarrow>
            (\<forall>A\<in>\<A>X. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
  shows "\<exists>T. top1_is_tree_on T (subspace_topology X TX T)
    \<and> T \<subseteq> X \<and> x0 \<in> T
    \<and> (\<forall>A\<in>\<A>X. A \<subseteq> T \<or> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A))
    \<and> T = \<Union>{A \<in> \<A>X. A \<subseteq> T}
    \<and> (\<forall>T'. T' \<subseteq> X \<longrightarrow> T \<subseteq> T' \<longrightarrow>
          top1_is_tree_on T' (subspace_topology X TX T') \<longrightarrow>
          (\<forall>A\<in>\<A>X. A \<subseteq> T' \<or> A \<inter> T' \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)) \<longrightarrow>
          T' = \<Union>{A \<in> \<A>X. A \<subseteq> T'} \<longrightarrow>
          T' = T)"
proof -
  \<comment> \<open>Following Munkres Lemma 84.5 (Zorn's lemma argument).
     Trees are subgraphs: each arc of X is either entirely in T or meets T at endpoints.
     Step 1: \<A> is non-empty (single arc + x0 is a subgraph-tree).
     Step 2: Chain upper bound (\<Union>C): subgraph (auto), connected (common point), SC (compact arcs).
     Step 3: Zorn gives maximal subgraph-tree.\<close>
  \<comment> \<open>Trees that are subgraphs: unions of complete arcs from \<A>X.
     Following Munkres 84.5: trees are subgraphs. The subgraph condition ensures
     each arc of X is either entirely in T or meets T only at endpoints.\<close>
  define \<A> where "\<A> = {T \<in> Pow X. top1_is_tree_on T (subspace_topology X TX T) \<and> x0 \<in> T
      \<and> (\<forall>A\<in>\<A>X. A \<subseteq> T \<or> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A))
      \<and> T = \<Union>{A \<in> \<A>X. A \<subseteq> T}}"
  have h\<A>_ne: "\<A> \<noteq> {}"
  proof -
    \<comment> \<open>x0 is in some arc A0 of \<A>X. A single arc is a subgraph-tree.\<close>
    from h\<A>X_cover assms(3) obtain A0 where hA0_AX: "A0 \<in> \<A>X" "x0 \<in> A0" by (by100 blast)
    hence hA0_arc: "top1_is_arc_on A0 (subspace_topology X TX A0)" and hA0_sub: "A0 \<subseteq> X"
      using h\<A>X by (by100 blast)+
    \<comment> \<open>A single arc is a tree: graph (single-arc graph), connected, simply connected.\<close>
    have "top1_is_tree_on A0 (subspace_topology X TX A0)"
      unfolding top1_is_tree_on_def
    proof (intro conjI)
      show "top1_connected_on A0 (subspace_topology X TX A0)"
        by (rule arc_connected[OF hA0_arc])
      show "top1_simply_connected_on A0 (subspace_topology X TX A0)"
      proof -
        \<comment> \<open>An arc is homeomorphic to [0,1]. And [0,1] is simply connected (convex: straight-line
           homotopy contracts any loop). By homeomorphism_preserves_simply_connected.\<close>
        \<comment> \<open>Step 1: [0,1] is simply connected.\<close>
        have hI_sc: "top1_simply_connected_on top1_unit_interval top1_unit_interval_topology"
        proof -
          have hI_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
            unfolding top1_unit_interval_topology_def
            by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) (by100 blast)
          \<comment> \<open>[0,1] is path-connected (for any x,y in [0,1], the line segment connects them).\<close>
          have hI_pc: "top1_path_connected_on top1_unit_interval top1_unit_interval_topology"
            unfolding top1_path_connected_on_def
          proof (intro conjI ballI)
            show "is_topology_on top1_unit_interval top1_unit_interval_topology" by (rule hI_top)
          next
            fix x y assume hx: "x \<in> top1_unit_interval" and hy: "y \<in> top1_unit_interval"
            let ?f = "\<lambda>t::real. (1 - t) * x + t * y"
            have hf_img: "\<forall>t\<in>top1_unit_interval. ?f t \<in> top1_unit_interval"
            proof (intro ballI)
              fix t assume "t \<in> top1_unit_interval"
              hence ht: "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by (by100 auto)+
              have hx': "0 \<le> x" "x \<le> 1" using hx unfolding top1_unit_interval_def by (by100 auto)+
              have hy': "0 \<le> y" "y \<le> 1" using hy unfolding top1_unit_interval_def by (by100 auto)+
              have "0 \<le> (1 - t) * x + t * y"
                using ht hx' hy' by (intro add_nonneg_nonneg mult_nonneg_nonneg; by100 linarith)
              moreover have "(1 - t) * x + t * y \<le> 1"
              proof -
                have "(1 - t) * x + t * y \<le> (1 - t) * 1 + t * 1"
                  using ht hx' hy' by (intro add_mono mult_left_mono; by100 linarith)
                thus ?thesis by (by100 simp)
              qed
              ultimately show "?f t \<in> top1_unit_interval"
                unfolding top1_unit_interval_def by (by100 auto)
            qed
            have hf_cont: "continuous_on top1_unit_interval ?f"
              by (intro continuous_intros)
            have hf_cmap: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                top1_unit_interval top1_unit_interval_topology ?f"
            proof -
              have "top1_unit_interval_topology = subspace_topology UNIV top1_open_sets top1_unit_interval"
                unfolding top1_unit_interval_topology_def by (by100 blast)
              thus ?thesis
                using top1_continuous_map_on_subspace_open_sets_on[of top1_unit_interval ?f top1_unit_interval]
                      hf_img hf_cont by (by5000 simp)
            qed
            have "?f 0 = x" by (by100 simp)
            moreover have "?f 1 = y" by (by100 simp)
            ultimately have "top1_is_path_on top1_unit_interval top1_unit_interval_topology x y ?f"
              using hf_cmap unfolding top1_is_path_on_def by (by100 blast)
            thus "\<exists>f. top1_is_path_on top1_unit_interval top1_unit_interval_topology x y f"
              by (by100 blast)
          qed
          \<comment> \<open>Every loop in [0,1] is null-homotopic (straight-line contraction).\<close>
          have hI_loops: "\<forall>x0 \<in> top1_unit_interval. \<forall>f. top1_is_loop_on top1_unit_interval top1_unit_interval_topology x0 f
              \<longrightarrow> top1_path_homotopic_on top1_unit_interval top1_unit_interval_topology x0 x0 f (top1_constant_path x0)"
          proof (intro ballI allI impI)
            fix x0 f assume hx0: "x0 \<in> top1_unit_interval"
                and hloop: "top1_is_loop_on top1_unit_interval top1_unit_interval_topology x0 f"
            \<comment> \<open>Straight-line homotopy: H(s,t) = (1-t)*f(s) + t*x0.\<close>
            let ?H = "\<lambda>p :: real \<times> real. (1 - snd p) * f (fst p) + snd p * x0"
            \<comment> \<open>H is continuous on I x I.\<close>
            have hH_cont: "top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval) II_topology
                top1_unit_interval top1_unit_interval_topology ?H"
            proof -
              have hf_cont_on: "continuous_on top1_unit_interval f"
              proof -
                have hf_cmap: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                    top1_unit_interval top1_unit_interval_topology f"
                  using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                \<comment> \<open>top1_open_sets = {U. open U}. I_top = subspace UNIV open_sets I.\<close>
                \<comment> \<open>continuous_map_on gives: preimages of subspace-open sets are subspace-open.
                   This equals continuous_on by continuous_on_open_invariant.\<close>
                show ?thesis unfolding continuous_on_topological
                proof (intro ballI allI impI)
                  fix x T assume hx: "x \<in> top1_unit_interval" and hT: "open T" and hfx: "f x \<in> T"
                  \<comment> \<open>T is open in R, so I \<inter> T is open in I_top.\<close>
                  have "T \<in> top1_open_sets" unfolding top1_open_sets_def using hT by (by100 blast)
                  hence "top1_unit_interval \<inter> T \<in> top1_unit_interval_topology"
                    unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
                  \<comment> \<open>By continuous_map_on: preimage is in I_top.\<close>
                  hence "{s \<in> top1_unit_interval. f s \<in> top1_unit_interval \<inter> T} \<in> top1_unit_interval_topology"
                    using hf_cmap unfolding top1_continuous_map_on_def by (by100 blast)
                  \<comment> \<open>Since f maps I into I, the preimage simplifies.\<close>
                  have hf_img: "\<forall>s\<in>top1_unit_interval. f s \<in> top1_unit_interval"
                    using hf_cmap unfolding top1_continuous_map_on_def by (by100 blast)
                  hence "{s \<in> top1_unit_interval. f s \<in> top1_unit_interval \<inter> T}
                      = {s \<in> top1_unit_interval. f s \<in> T}" using hf_img by (by100 blast)
                  hence hpre: "{s \<in> top1_unit_interval. f s \<in> T} \<in> top1_unit_interval_topology"
                    using \<open>{s \<in> top1_unit_interval. f s \<in> top1_unit_interval \<inter> T} \<in> top1_unit_interval_topology\<close>
                    by (by100 simp)
                  \<comment> \<open>I_top is subspace of R, so open in I_top means open_in_R intersect I.\<close>
                  from hpre obtain U where hU: "U \<in> top1_open_sets" and heq: "{s \<in> top1_unit_interval. f s \<in> T} = top1_unit_interval \<inter> U"
                    unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
                  have "open U" using hU unfolding top1_open_sets_def by (by100 blast)
                  moreover have "x \<in> {s \<in> top1_unit_interval. f s \<in> T}" using hx hfx by (by100 blast)
                  hence "x \<in> top1_unit_interval \<inter> U" using heq by (by100 simp)
                  hence "x \<in> U" by (by100 blast)
                  ultimately show "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>top1_unit_interval. y \<in> A \<longrightarrow> f y \<in> T)"
                    using heq by (by100 blast)
                qed
              qed
              have hH_img: "\<And>p. p \<in> top1_unit_interval \<times> top1_unit_interval \<Longrightarrow> ?H p \<in> top1_unit_interval"
              proof -
                fix p :: "real \<times> real" assume hp: "p \<in> top1_unit_interval \<times> top1_unit_interval"
                obtain s t where hst: "p = (s, t)" and hs: "s \<in> top1_unit_interval" and ht: "t \<in> top1_unit_interval"
                  using hp by (by100 blast)
                have ht': "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)+
                have hfs: "f s \<in> top1_unit_interval"
                  using hloop hs unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
                hence hfs': "0 \<le> f s" "f s \<le> 1" unfolding top1_unit_interval_def by (by100 auto)+
                have hx0': "0 \<le> x0" "x0 \<le> 1" using hx0 unfolding top1_unit_interval_def by (by100 auto)+
                have "0 \<le> (1 - t) * f s + t * x0"
                  using ht' hfs' hx0' by (intro add_nonneg_nonneg mult_nonneg_nonneg; by100 linarith)
                moreover have "(1 - t) * f s + t * x0 \<le> (1 - t) * 1 + t * 1"
                  using ht' hfs' hx0' by (intro add_mono mult_left_mono; by100 linarith)
                hence "(1 - t) * f s + t * x0 \<le> 1" by (by100 simp)
                ultimately show "?H p \<in> top1_unit_interval" using hst
                  unfolding top1_unit_interval_def by (by100 auto)
              qed
              have hH_cont_on: "continuous_on (top1_unit_interval \<times> top1_unit_interval) ?H"
              proof -
                let ?S = "top1_unit_interval \<times> top1_unit_interval"
                have hc_id: "continuous_on ?S (\<lambda>x. x)"
                  using continuous_on_id[of ?S] unfolding id_def by (by100 blast)
                have hc_fst: "continuous_on ?S (\<lambda>p. fst p)"
                  using continuous_on_fst[OF hc_id] by (by100 simp)
                have hc_snd: "continuous_on ?S (\<lambda>p. snd p)"
                  using continuous_on_snd[OF hc_id] by (by100 simp)
                have himg: "fst ` ?S \<subseteq> top1_unit_interval" by (by100 auto)
                have hc_f_fst: "continuous_on ?S (\<lambda>p. f (fst p))"
                  using continuous_on_compose2[OF hf_cont_on hc_fst himg] by (by100 simp)
                have hc_1mt: "continuous_on ?S (\<lambda>p. 1 - snd p)"
                  by (intro continuous_intros hc_snd hc_id)
                have hc_p1: "continuous_on ?S (\<lambda>p. (1 - snd p) * f (fst p))"
                  by (intro continuous_intros hc_1mt hc_f_fst hc_id)
                have hc_p2: "continuous_on ?S (\<lambda>p. snd p * x0)"
                  by (intro continuous_intros hc_snd hc_id)
                show ?thesis by (intro continuous_intros hc_p1 hc_p2 hc_id)
              qed
              from top1_continuous_map_on_II_to_I[OF hH_img hH_cont_on]
              show ?thesis unfolding II_topology_def by (by100 blast)
            qed
            \<comment> \<open>Boundary conditions.\<close>
            have hH0: "\<forall>s\<in>top1_unit_interval. ?H (s, 0) = f s" by (by100 simp)
            have hH1: "\<forall>s\<in>top1_unit_interval. ?H (s, 1) = x0" by (by100 simp)
            have hf0: "f 0 = x0" and hf1: "f 1 = x0"
              using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
            have hHL: "\<forall>t\<in>top1_unit_interval. ?H (0, t) = x0"
            proof (intro ballI)
              fix t :: real assume "t \<in> top1_unit_interval"
              have "?H (0, t) = (1 - t) * f 0 + t * x0" by (by100 simp)
              also have "\<dots> = (1 - t) * x0 + t * x0" using hf0 by (by100 simp)
              also have "\<dots> = ((1-t) + t) * x0" using distrib_right[of "1-t" t x0] by (by100 simp)
              also have "\<dots> = x0" by (by100 simp)
              finally show "?H (0, t) = x0" .
            qed
            have hHR: "\<forall>t\<in>top1_unit_interval. ?H (1, t) = x0"
            proof (intro ballI)
              fix t :: real assume "t \<in> top1_unit_interval"
              have "?H (1, t) = (1 - t) * f 1 + t * x0" by (by100 simp)
              also have "\<dots> = (1 - t) * x0 + t * x0" using hf1 by (by100 simp)
              also have "\<dots> = ((1-t) + t) * x0" using distrib_right[of "1-t" t x0] by (by100 simp)
              also have "\<dots> = x0" by (by100 simp)
              finally show "?H (1, t) = x0" .
            qed
            \<comment> \<open>f is a path (from loop).\<close>
            have hf_path: "top1_is_path_on top1_unit_interval top1_unit_interval_topology x0 x0 f"
              using hloop unfolding top1_is_loop_on_def by (by100 blast)
            \<comment> \<open>const_x0 is a path.\<close>
            have hconst_path: "top1_is_path_on top1_unit_interval top1_unit_interval_topology x0 x0 (top1_constant_path x0)"
              by (rule top1_constant_path_is_path[OF hI_top hx0])
            have "?H (s, 1) = top1_constant_path x0 s" for s
              unfolding top1_constant_path_def by (by100 simp)
            hence hH1': "\<forall>s\<in>top1_unit_interval. ?H (s, 1) = top1_constant_path x0 s" by (by100 blast)
            show "top1_path_homotopic_on top1_unit_interval top1_unit_interval_topology x0 x0 f (top1_constant_path x0)"
              unfolding top1_path_homotopic_on_def
              using hf_path hconst_path hH_cont hH0 hH1' hHL hHR by (by100 blast)
          qed
          show ?thesis using top1_simply_connected_from_one_point[OF hI_top hI_pc] hI_loops hI_pc
            unfolding top1_simply_connected_on_def by (by100 blast)
        qed
        \<comment> \<open>Step 2: Arc is homeomorphic to [0,1] (by definition of arc).\<close>
        obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology A0 (subspace_topology X TX A0) h"
          using hA0_arc unfolding top1_is_arc_on_def by (by100 blast)
        \<comment> \<open>Step 3: Homeomorphism preserves simply connected.\<close>
        show ?thesis using homeomorphism_preserves_simply_connected[OF hh hI_sc] by (by100 blast)
      qed
      show "top1_is_graph_on A0 (subspace_topology X TX A0)"
        unfolding top1_is_graph_on_def
      proof (intro conjI)
        let ?TA0 = "subspace_topology X TX A0"
        \<comment> \<open>Strict topology: subspace of strict is strict.\<close>
        show "is_topology_on_strict A0 ?TA0"
        proof -
          have "is_topology_on_strict X TX"
            using assms(1) unfolding top1_is_graph_on_def by (by5000 blast)
          thus ?thesis using subspace_topology_is_strict hA0_sub by (by100 blast)
        qed
        \<comment> \<open>Hausdorff: subspace of Hausdorff is Hausdorff.\<close>
        show "is_hausdorff_on A0 ?TA0"
        proof -
          have "is_hausdorff_on X TX"
            using assms(1) unfolding top1_is_graph_on_def by (by5000 blast)
          thus ?thesis
            using conjunct2[OF conjunct2[OF Theorem_17_11]] hA0_sub by (by100 blast)
        qed
        \<comment> \<open>Arc cover: {A0}.\<close>
        show "\<exists>\<A>. (\<forall>A\<in>\<A>. A \<subseteq> A0 \<and> top1_is_arc_on A (subspace_topology A0 ?TA0 A))
            \<and> \<Union>\<A> = A0
            \<and> (\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
                 A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology A0 ?TA0 A)
               \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology A0 ?TA0 B)
               \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2)
            \<and> (\<forall>C. C \<subseteq> A0 \<longrightarrow>
                 (closedin_on A0 ?TA0 C \<longleftrightarrow>
                  (\<forall>A\<in>\<A>. closedin_on A (subspace_topology A0 ?TA0 A) (A \<inter> C))))"
        proof (rule exI[of _ "{A0}"])
          have h_sub_sub: "subspace_topology A0 ?TA0 A0 = ?TA0"
          proof (rule subspace_topology_self)
            show "\<forall>U \<in> ?TA0. U \<subseteq> A0" unfolding subspace_topology_def by (by100 blast)
          qed
          have h_arc: "top1_is_arc_on A0 (subspace_topology A0 ?TA0 A0)"
            using hA0_arc h_sub_sub by (by100 simp)
          show "(\<forall>A\<in>{A0}. A \<subseteq> A0 \<and> top1_is_arc_on A (subspace_topology A0 ?TA0 A))
              \<and> \<Union>{A0} = A0
              \<and> (\<forall>A\<in>{A0}. \<forall>B\<in>{A0}. A \<noteq> B \<longrightarrow>
                   A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology A0 ?TA0 A)
                 \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology A0 ?TA0 B)
                 \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2)
              \<and> (\<forall>C. C \<subseteq> A0 \<longrightarrow>
                   (closedin_on A0 ?TA0 C \<longleftrightarrow>
                    (\<forall>A\<in>{A0}. closedin_on A (subspace_topology A0 ?TA0 A) (A \<inter> C))))"
          proof -
            have h1: "\<forall>A\<in>{A0}. A \<subseteq> A0 \<and> top1_is_arc_on A (subspace_topology A0 ?TA0 A)"
              using h_arc by (by100 blast)
            have h2: "\<Union>{A0} = A0" by (by100 blast)
            have h3: "\<forall>A\<in>{A0}. \<forall>B\<in>{A0}. A \<noteq> B \<longrightarrow>
                 A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology A0 ?TA0 A)
               \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology A0 ?TA0 B)
               \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
              by (by100 blast)
            have h4: "\<forall>C. C \<subseteq> A0 \<longrightarrow>
                 (closedin_on A0 ?TA0 C \<longleftrightarrow>
                  (\<forall>A\<in>{A0}. closedin_on A (subspace_topology A0 ?TA0 A) (A \<inter> C)))"
            proof (intro allI impI iffI ballI)
              fix C A assume hC: "C \<subseteq> A0" and hcl: "closedin_on A0 ?TA0 C" and "A \<in> {A0}"
              hence "A = A0" by (by100 blast)
              have "A0 \<inter> C = C" using hC by (by100 blast)
              thus "closedin_on A (subspace_topology A0 ?TA0 A) (A \<inter> C)"
                using \<open>A = A0\<close> h_sub_sub hcl by (by100 simp)
            next
              fix C assume hC: "C \<subseteq> A0" and "\<forall>A\<in>{A0}. closedin_on A (subspace_topology A0 ?TA0 A) (A \<inter> C)"
              hence "closedin_on A0 ?TA0 (A0 \<inter> C)" using h_sub_sub by (by100 simp)
              moreover have "A0 \<inter> C = C" using hC by (by100 blast)
              ultimately show "closedin_on A0 ?TA0 C" by (by100 simp)
            qed
            show ?thesis using h1 h2 h3 h4 by (by100 blast)
          qed
        qed
      qed
    qed
    \<comment> \<open>A0 satisfies the subgraph condition: single arc meets other arcs at endpoints.\<close>
    moreover have "\<forall>A\<in>\<A>X. A \<subseteq> A0 \<or> A \<inter> A0 \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
    proof (intro ballI)
      fix B assume "B \<in> \<A>X"
      show "B \<subseteq> A0 \<or> B \<inter> A0 \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)"
      proof (cases "B = A0")
        case True thus ?thesis by (by100 blast)
      next
        case False
        from h\<A>X_inter[rule_format, OF \<open>B \<in> \<A>X\<close> hA0_AX(1) False]
        show ?thesis by (by100 blast)
      qed
    qed
    moreover have "A0 = \<Union>{A \<in> \<A>X. A \<subseteq> A0}"
    proof -
      have "A0 \<subseteq> \<Union>{A \<in> \<A>X. A \<subseteq> A0}" using hA0_AX(1) by (by100 blast)
      moreover have "\<Union>{A \<in> \<A>X. A \<subseteq> A0} \<subseteq> A0" by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    ultimately have "A0 \<in> \<A>" using hA0_sub \<open>x0 \<in> A0\<close> unfolding \<A>_def by (by100 blast)
    thus ?thesis by (by100 blast)
  qed
  have hchain: "\<forall>C \<in> chains \<A>. \<exists>U \<in> \<A>. \<forall>X\<in>C. X \<subseteq> U"
  proof (intro ballI)
    fix C assume hC: "C \<in> chains \<A>"
    show "\<exists>U \<in> \<A>. \<forall>X\<in>C. X \<subseteq> U"
    proof (cases "C = {}")
      case True
      from h\<A>_ne obtain T0 where "T0 \<in> \<A>" by (by100 blast)
      thus ?thesis using True by (by100 blast)
    next
      case False
      \<comment> \<open>Nonempty chain: union is a tree.\<close>
      have hU_sub: "\<Union>C \<subseteq> X" using hC unfolding chains_def \<A>_def by (by100 blast)
      have hU_x0: "x0 \<in> \<Union>C"
      proof -
        from False obtain T0 where "T0 \<in> C" by (by100 blast)
        hence "T0 \<in> \<A>" using hC unfolding chains_def by (by100 blast)
        hence "x0 \<in> T0" unfolding \<A>_def by (by100 blast)
        thus ?thesis using \<open>T0 \<in> C\<close> by (by100 blast)
      qed
      \<comment> \<open>Subgraph condition for \<Union>C (proved early, needed for graph structure).\<close>
      have hU_subgraph: "\<forall>A\<in>\<A>X. A \<subseteq> \<Union>C \<or> A \<inter> \<Union>C \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
      proof (intro ballI)
        fix A assume hA_AX: "A \<in> \<A>X"
        show "A \<subseteq> \<Union>C \<or> A \<inter> \<Union>C \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
        proof (cases "A \<inter> \<Union>C \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)")
          case True thus ?thesis by (by100 blast)
        next
          case False
          then obtain p where "p \<in> A \<inter> \<Union>C" "p \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            by (by100 blast)
          then obtain Ti where "Ti \<in> C" "p \<in> Ti" by (by100 blast)
          have "Ti \<in> \<A>" using \<open>Ti \<in> C\<close> hC unfolding chains_def by (by100 blast)
          hence "\<forall>A\<in>\<A>X. A \<subseteq> Ti \<or> A \<inter> Ti \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
            unfolding \<A>_def by (by100 blast)
          from this[rule_format, OF hA_AX]
          have "A \<subseteq> Ti" using \<open>p \<in> A \<inter> \<Union>C\<close> \<open>p \<in> Ti\<close>
              \<open>p \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)\<close> by (by100 blast)
          hence "A \<subseteq> \<Union>C" using \<open>Ti \<in> C\<close> by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
      qed
      have hU_tree: "top1_is_tree_on (\<Union>C) (subspace_topology X TX (\<Union>C))"
        unfolding top1_is_tree_on_def
      proof (intro conjI)
        \<comment> \<open>Connected: union of chain of connected sets sharing x0 (Theorem 23.3).\<close>
        show "top1_connected_on (\<Union>C) (subspace_topology X TX (\<Union>C))"
        proof -
          have hX_strict: "is_topology_on_strict X TX"
            using assms(1) unfolding top1_is_graph_on_def by (by5000 blast)
          hence hX_top: "is_topology_on X TX"
            unfolding is_topology_on_strict_def by (by100 blast)
          have hC_ne_idx: "C \<noteq> {}" using False by (by100 blast)
          have hC_sub: "\<forall>T' \<in> C. T' \<subseteq> X"
            using hC unfolding chains_def \<A>_def by (by100 blast)
          have hC_conn: "\<forall>T' \<in> C. top1_connected_on T' (subspace_topology X TX T')"
          proof (intro ballI)
            fix T' assume "T' \<in> C"
            hence "T' \<in> \<A>" using hC unfolding chains_def by (by100 blast)
            hence "top1_is_tree_on T' (subspace_topology X TX T')" unfolding \<A>_def by (by100 blast)
            thus "top1_connected_on T' (subspace_topology X TX T')"
              unfolding top1_is_tree_on_def by (by100 blast)
          qed
          have hx0_all: "x0 \<in> \<Inter>(C)"
          proof (intro InterI)
            fix T' assume "T' \<in> C"
            hence "T' \<in> \<A>" using hC unfolding chains_def by (by100 blast)
            thus "x0 \<in> T'" unfolding \<A>_def by (by100 blast)
          qed
          have hx0_inter: "x0 \<in> \<Inter>((\<lambda>T'. T') ` C)" using hx0_all by (by100 simp)
          have hU_eq: "\<Union>C = (\<Union>T'\<in>C. T')" by (by100 blast)
          from Theorem_23_3[OF hX_top hC_ne_idx _ hC_conn hx0_inter]
          have "top1_connected_on (\<Union>((\<lambda>T'. T') ` C)) (subspace_topology X TX (\<Union>((\<lambda>T'. T') ` C)))"
            using hC_sub by (by100 blast)
          thus ?thesis by (by100 simp)
        qed
      next
        \<comment> \<open>Simply connected: any loop is compact, hence in some Ti (chain), hence null-homotopic.\<close>
        show "top1_simply_connected_on (\<Union>C) (subspace_topology X TX (\<Union>C))"
        proof -
          let ?U = "\<Union>C"
          let ?TU = "subspace_topology X TX ?U"
          have hX_top2: "is_topology_on X TX"
            using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by5000 blast)
          have hTU: "is_topology_on ?U ?TU"
            by (rule subspace_topology_is_topology_on[OF hX_top2 hU_sub])
          \<comment> \<open>Path-connected: for any x,y in UC, they're in some Tj (chain), which is path-connected.\<close>
          have hU_pc: "top1_path_connected_on ?U ?TU"
            unfolding top1_path_connected_on_def
          proof (intro conjI ballI)
            show "is_topology_on ?U ?TU" by (rule hTU)
          next
            fix x y assume hx: "x \<in> ?U" and hy: "y \<in> ?U"
            obtain Ti where "Ti \<in> C" "x \<in> Ti" using hx by (by100 blast)
            obtain Tj where "Tj \<in> C" "y \<in> Tj" using hy by (by100 blast)
            \<comment> \<open>C is a chain, so Ti \<subseteq> Tj or Tj \<subseteq> Ti.\<close>
            have "Ti \<subseteq> Tj \<or> Tj \<subseteq> Ti"
              using hC \<open>Ti \<in> C\<close> \<open>Tj \<in> C\<close> unfolding chains_def chain_subset_def by (by100 blast)
            then obtain Tk where "Tk \<in> C" "x \<in> Tk" "y \<in> Tk"
              using \<open>x \<in> Ti\<close> \<open>y \<in> Tj\<close> \<open>Ti \<in> C\<close> \<open>Tj \<in> C\<close> by (by100 blast)
            hence "Tk \<in> \<A>" using hC unfolding chains_def by (by100 blast)
            hence htree: "top1_is_tree_on Tk (subspace_topology X TX Tk)" unfolding \<A>_def by (by100 blast)
            hence hTk_pc: "top1_path_connected_on Tk (subspace_topology X TX Tk)"
              unfolding top1_is_tree_on_def top1_simply_connected_on_def by (by100 blast)
            hence "\<exists>f. top1_is_path_on Tk (subspace_topology X TX Tk) x y f"
              using \<open>x \<in> Tk\<close> \<open>y \<in> Tk\<close> unfolding top1_path_connected_on_def by (by100 blast)
            then obtain f where hf: "top1_is_path_on Tk (subspace_topology X TX Tk) x y f" by (by100 blast)
            \<comment> \<open>A path in Tk is also a path in UC (since Tk \<subseteq> UC \<subseteq> X).\<close>
            have hTk_sub_U: "Tk \<subseteq> ?U" using \<open>Tk \<in> C\<close> by (by100 blast)
            have "top1_is_path_on ?U ?TU x y f"
            proof -
              have hf_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  Tk (subspace_topology X TX Tk) f"
                using hf unfolding top1_is_path_on_def by (by100 blast)
              from top1_continuous_map_on_codomain_enlarge[OF hf_cont hTk_sub_U hU_sub]
              have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  ?U ?TU f" .
              moreover have "f 0 = x" and "f 1 = y" using hf unfolding top1_is_path_on_def by (by100 blast)+
              ultimately show ?thesis unfolding top1_is_path_on_def by (by100 blast)
            qed
            thus "\<exists>f. top1_is_path_on ?U ?TU x y f" by (by100 blast)
          qed
          \<comment> \<open>Every loop at x0 is null-homotopic: the loop is in some Tj (tree), hence null-homotopic.\<close>
          have hU_loops: "\<forall>f. top1_is_loop_on ?U ?TU x0 f
              \<longrightarrow> top1_path_homotopic_on ?U ?TU x0 x0 f (top1_constant_path x0)"
          proof (intro allI impI)
            fix f assume hf_loop: "top1_is_loop_on ?U ?TU x0 f"
            \<comment> \<open>Step 1: f is in some Tk (chain argument + graph compactness).\<close>
            obtain Tk where hTk_C: "Tk \<in> C" and hf_in_Tk: "top1_is_loop_on Tk (subspace_topology X TX Tk) x0 f"
            proof -
              \<comment> \<open>Munkres 84.5 chain argument: loop image compact \<rightarrow> finitely many \<A>X-arcs
                 \<rightarrow> each arc in a chain element \<rightarrow> max chain element contains all.\<close>
              \<comment> \<open>Step 1: f maps [0,1] continuously to \<Union>C.\<close>
              have hf_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  ?U ?TU f" using hf_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
              have hf0: "f 0 = x0" and hf1: "f 1 = x0"
                using hf_loop unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
              \<comment> \<open>Step 2: f([0,1]) \<subseteq> \<Union>C. Each point is in an \<A>X-arc in \<Union>C.\<close>
              have hf_img_sub: "f ` top1_unit_interval \<subseteq> ?U"
                using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
              \<comment> \<open>Step 3: Each point of f([0,1]) is in a chain element.
                 Since each Ti \<in> C is closed in X, and the chain is directed,
                 for each arc A \<in> \<A>X with A \<subseteq> \<Union>C: A is in some Ti \<in> C
                 (A has non-endpoint points in \<Union>C, some Ti contains a non-endpoint,
                 Ti's subgraph condition gives A \<subseteq> Ti).\<close>
              have harc_in_chain: "\<forall>A\<in>\<A>X. A \<subseteq> \<Union>C \<longrightarrow> (\<exists>Ti\<in>C. A \<subseteq> Ti)"
              proof (intro ballI impI)
                fix A assume "A \<in> \<A>X" "A \<subseteq> \<Union>C"
                \<comment> \<open>A is nonempty (arc). Pick any interior point p of A.\<close>
                have "A \<noteq> {}"
                proof -
                  have "top1_is_arc_on A (subspace_topology X TX A)" using h\<A>X \<open>A \<in> \<A>X\<close> by (by100 blast)
                  then obtain h' where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                      A (subspace_topology X TX A) h'" unfolding top1_is_arc_on_def by (by100 blast)
                  hence "bij_betw h' top1_unit_interval A" unfolding top1_homeomorphism_on_def by (by100 blast)
                  hence "h' ` top1_unit_interval = A" unfolding bij_betw_def by (by100 blast)
                  moreover have "0 \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
                  ultimately show ?thesis by (by100 blast)
                qed
                then obtain p where "p \<in> A" by (by100 blast)
                have "p \<in> \<Union>C" using \<open>p \<in> A\<close> \<open>A \<subseteq> \<Union>C\<close> by (by100 blast)
                then obtain Ti where "Ti \<in> C" "p \<in> Ti" by (by100 blast)
                have "Ti \<in> \<A>" using \<open>Ti \<in> C\<close> hC unfolding chains_def by (by100 blast)
                hence "\<forall>A\<in>\<A>X. A \<subseteq> Ti \<or> A \<inter> Ti \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                  unfolding \<A>_def by (by100 blast)
                from this[rule_format, OF \<open>A \<in> \<A>X\<close>]
                have "A \<subseteq> Ti \<or> A \<inter> Ti \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)" .
                show "\<exists>Ti\<in>C. A \<subseteq> Ti"
                  using \<open>A \<subseteq> Ti \<or> A \<inter> Ti \<subseteq> top1_arc_endpoints_on A _\<close>
                proof
                  assume "A \<subseteq> Ti" thus ?thesis using \<open>Ti \<in> C\<close> by (by100 blast)
                next
                  assume hep: "A \<inter> Ti \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                  \<comment> \<open>A \<subseteq> \<Union>C. A has non-endpoint points (arc is homeomorphic to [0,1]).
                     A non-endpoint point q is in some Tj \<in> C. Tj's subgraph condition gives A \<subseteq> Tj.\<close>
                  have "top1_is_arc_on A (subspace_topology X TX A)" using h\<A>X \<open>A \<in> \<A>X\<close> by (by100 blast)
                  then obtain h' where hh': "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                      A (subspace_topology X TX A) h'" unfolding top1_is_arc_on_def by (by100 blast)
                  have "bij_betw h' top1_unit_interval A" using hh' unfolding top1_homeomorphism_on_def by (by100 blast)
                  have "h' ` top1_unit_interval = A" using \<open>bij_betw h' top1_unit_interval A\<close>
                    unfolding bij_betw_def by (by100 blast)
                  have "1/2 \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
                  have "h' (1/2) \<in> A" using \<open>h' ` top1_unit_interval = A\<close> \<open>1/2 \<in> top1_unit_interval\<close>
                    by (by100 blast)
                  have hX_strict: "is_topology_on_strict X TX"
                    using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                  have hX_haus: "is_hausdorff_on X TX"
                    using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                  have "A \<subseteq> X" using h\<A>X \<open>A \<in> \<A>X\<close> by (by100 blast)
                  from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>A \<subseteq> X\<close>
                      \<open>top1_is_arc_on A _\<close> hh']
                  have hep_eq: "top1_arc_endpoints_on A (subspace_topology X TX A) = {h' 0, h' 1}" .
                  have "h' (1/2) \<notin> {h' 0, h' 1}"
                  proof -
                    have "inj_on h' top1_unit_interval"
                      using \<open>bij_betw h' top1_unit_interval A\<close> unfolding bij_betw_def by (by100 blast)
                    have "(1::real)/2 \<noteq> 0" by (by100 simp)
                    have "(1::real)/2 \<noteq> 1" by (by100 simp)
                    have "0 \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
                    have "1 \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
                    from inj_onD[OF \<open>inj_on h' top1_unit_interval\<close>, of "1/2" 0]
                    have "h' (1/2) \<noteq> h' 0" using \<open>(1::real)/2 \<noteq> 0\<close>
                        \<open>1/2 \<in> top1_unit_interval\<close> \<open>0 \<in> top1_unit_interval\<close> by (by100 blast)
                    from inj_onD[OF \<open>inj_on h' top1_unit_interval\<close>, of "1/2" 1]
                    have "h' (1/2) \<noteq> h' 1" using \<open>(1::real)/2 \<noteq> 1\<close>
                        \<open>1/2 \<in> top1_unit_interval\<close> \<open>1 \<in> top1_unit_interval\<close> by (by100 blast)
                    thus ?thesis using \<open>h' (1/2) \<noteq> h' 0\<close> \<open>h' (1/2) \<noteq> h' 1\<close> by (by100 blast)
                  qed
                  hence "h' (1/2) \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
                    using hep_eq by (by100 simp)
                  have "h' (1/2) \<in> \<Union>C" using \<open>h' (1/2) \<in> A\<close> \<open>A \<subseteq> \<Union>C\<close> by (by100 blast)
                  then obtain Tj where "Tj \<in> C" "h' (1/2) \<in> Tj" by (by100 blast)
                  have "Tj \<in> \<A>" using \<open>Tj \<in> C\<close> hC unfolding chains_def by (by100 blast)
                  hence "\<forall>A\<in>\<A>X. A \<subseteq> Tj \<or> A \<inter> Tj \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                    unfolding \<A>_def by (by100 blast)
                  from this[rule_format, OF \<open>A \<in> \<A>X\<close>]
                  have "A \<subseteq> Tj"
                    using \<open>h' (1/2) \<in> Tj\<close> \<open>h' (1/2) \<in> A\<close>
                        \<open>h' (1/2) \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
                  thus ?thesis using \<open>Tj \<in> C\<close> by (by100 blast)
                qed
              qed
              \<comment> \<open>Step 4: Each point of f([0,1]) is in a chain element via arcs.\<close>
              have "\<forall>t\<in>top1_unit_interval. \<exists>Ti\<in>C. f t \<in> Ti"
              proof (intro ballI)
                fix t assume "t \<in> top1_unit_interval"
                have "f t \<in> ?U" using hf_img_sub \<open>t \<in> top1_unit_interval\<close> by (by100 blast)
                then obtain Ti where "Ti \<in> C" "f t \<in> Ti" by (by100 blast)
                thus "\<exists>Ti\<in>C. f t \<in> Ti" by (by100 blast)
              qed
              \<comment> \<open>Step 5: By compact\_in\_graph\_finite\_arcs: f([0,1]) lies in finitely many arcs of X.
                 Use this to get finitely many \<A>X-arcs in \<Union>C, hence finitely many chain elements.\<close>
              \<comment> \<open>Since f([0,1]) \<subseteq> \<Union>C = \<Union>{A \<in> \<A>X. A \<subseteq> \<Union>C}, each point is in an \<A>X-arc \<subseteq> \<Union>C.
                 The set of such arcs meeting f([0,1]) is finite (from graph compactness argument).
                 Each such arc is in some chain element (from harc\_in\_chain).
                 Finitely many chain elements have a maximum.\<close>
              have "\<exists>Tk\<in>C. f ` top1_unit_interval \<subseteq> Tk"
              proof -
                let ?K = "f ` top1_unit_interval"
                have hfI_sub: "?K \<subseteq> X" using hf_img_sub hU_sub by (by100 blast)
                \<comment> \<open>Munkres 84.5: finite covering of f(I) by \<A>X-arcs \<subseteq> \<Union>C.
                   Interior arcs + vertex arcs give finite covering.
                   Each covering arc in a chain element. Finite \<rightarrow> max \<rightarrow> f(I) \<subseteq> max.\<close>
                \<comment> \<open>Step 1: Interior-point arcs (arcs with non-endpoint points in K) are finite.\<close>
                let ?\<A>_int = "{A \<in> \<A>X. (A - top1_arc_endpoints_on A (subspace_topology X TX A)) \<inter> ?K \<noteq> {}}"
                have h\<A>int_fin: "finite ?\<A>_int"
                proof -
                  define sel where "sel \<equiv> \<lambda>A. SOME x. x \<in> A \<and> x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A) \<and> x \<in> ?K"
                  have hsel: "\<forall>A \<in> ?\<A>_int. sel A \<in> A \<and>
                      sel A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A) \<and> sel A \<in> ?K"
                  proof (intro ballI)
                    fix A assume "A \<in> ?\<A>_int"
                    hence "\<exists>x. x \<in> A \<and> x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A) \<and> x \<in> ?K"
                      by (by100 blast)
                    from someI_ex[OF this] show "sel A \<in> A \<and>
                        sel A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A) \<and> sel A \<in> ?K"
                      unfolding sel_def .
                  qed
                  let ?B = "sel ` ?\<A>_int"
                  have hB_card: "\<forall>A'\<in>\<A>X. finite (?B \<inter> A') \<and> card (?B \<inter> A') \<le> 1"
                  proof (intro ballI conjI)
                    fix A' assume "A' \<in> \<A>X"
                    have "?B \<inter> A' \<subseteq> {sel A'}"
                    proof
                      fix x assume "x \<in> ?B \<inter> A'"
                      then obtain A where hA: "A \<in> ?\<A>_int" "x = sel A" "x \<in> A'" by (by100 blast)
                      have "A = A'"
                      proof (rule ccontr)
                        assume "A \<noteq> A'"
                        have "A \<in> \<A>X" using hA(1) by (by100 blast)
                        have "sel A \<in> A" using hsel hA(1) by (by100 blast)
                        hence "sel A \<in> A \<inter> A'" using hA(3) hA(2) by (by100 blast)
                        from h\<A>X_inter[rule_format, OF \<open>A \<in> \<A>X\<close> \<open>A' \<in> \<A>X\<close> \<open>A \<noteq> A'\<close>]
                        have "sel A \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                          using \<open>sel A \<in> A \<inter> A'\<close> by (by100 blast)
                        moreover have "sel A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
                          using hsel hA(1) by (by100 blast)
                        ultimately show False by (by100 blast)
                      qed
                      thus "x \<in> {sel A'}" using hA(2) by (by100 blast)
                    qed
                    show "finite (?B \<inter> A')" using finite_subset[OF \<open>?B \<inter> A' \<subseteq> {sel A'}\<close>] by (by100 simp)
                    show "card (?B \<inter> A') \<le> 1" using card_mono[OF _ \<open>?B \<inter> A' \<subseteq> {sel A'}\<close>] by (by100 simp)
                  qed
                  have hB_sub: "?B \<subseteq> X" using hsel h\<A>X by (by5000 blast)
                  from graph_selection_set_discrete[OF assms(1) hB_sub h\<A>X h\<A>X_cover h\<A>X_coh hB_card]
                  have hB_all_cl: "\<forall>S. S \<subseteq> ?B \<longrightarrow> closedin_on X TX S" .
                  have hB_sub_K: "?B \<subseteq> ?K" using hsel by (by100 blast)
                  have hB_fin: "finite ?B"
                  proof -
                    have hX_top_loc: "is_topology_on X TX"
                      using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by5000 blast)
                    have hB_cl_X: "closedin_on X TX ?B" using hB_all_cl by (by100 blast)
                    have hB_cl_K: "closedin_on ?K (subspace_topology X TX ?K) ?B"
                      by (rule closedin_subspace_from_ambient[OF hX_top_loc hB_cl_X hfI_sub hB_sub_K])
                    have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
                      unfolding top1_unit_interval_def top1_unit_interval_topology_def
                      using Theorem_27_1[of "0::real" 1] by (by100 simp)
                    have hfI_compact: "top1_compact_on ?K (subspace_topology X TX ?K)"
                    proof -
                      have "\<forall>t\<in>top1_unit_interval. f t \<in> X" using hfI_sub by (by100 blast)
                      have "\<forall>U\<in>TX. {t \<in> top1_unit_interval. f t \<in> U} \<in> top1_unit_interval_topology"
                      proof (intro ballI)
                        fix U assume "U \<in> TX"
                        have "U \<inter> ?U \<in> ?TU" unfolding subspace_topology_def using \<open>U \<in> TX\<close> by (by100 blast)
                        have "\<forall>V\<in>?TU. {t \<in> top1_unit_interval. f t \<in> V} \<in> top1_unit_interval_topology"
                          using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
                        hence "{t \<in> top1_unit_interval. f t \<in> U \<inter> ?U} \<in> top1_unit_interval_topology"
                          using \<open>U \<inter> ?U \<in> ?TU\<close> by (by100 blast)
                        moreover have "{t \<in> top1_unit_interval. f t \<in> U \<inter> ?U} =
                            {t \<in> top1_unit_interval. f t \<in> U}" using hf_img_sub by (by100 blast)
                        ultimately show "{t \<in> top1_unit_interval. f t \<in> U} \<in> top1_unit_interval_topology"
                          by (by100 simp)
                      qed
                      hence "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
                        unfolding top1_continuous_map_on_def
                        using \<open>\<forall>t\<in>top1_unit_interval. f t \<in> X\<close> by (by100 blast)
                      from top1_compact_on_continuous_image[OF hI_compact hX_top_loc this]
                      show ?thesis .
                    qed
                    have hB_compact: "top1_compact_on ?B (subspace_topology X TX ?B)"
                    proof -
                      from Theorem_26_2[OF hfI_compact hB_cl_K]
                      have "top1_compact_on ?B (subspace_topology ?K (subspace_topology X TX ?K) ?B)" .
                      moreover have "subspace_topology ?K (subspace_topology X TX ?K) ?B = subspace_topology X TX ?B"
                        by (rule subspace_topology_trans[OF hB_sub_K])
                      ultimately show ?thesis by (by100 simp)
                    qed
                    have hB_discrete: "\<forall>x\<in>?B. {x} \<in> subspace_topology X TX ?B"
                    proof (intro ballI)
                      fix x assume hx: "x \<in> ?B"
                      have "?B - {x} \<subseteq> ?B" by (by100 blast)
                      have "closedin_on X TX (?B - {x})" using hB_all_cl \<open>?B - {x} \<subseteq> ?B\<close> by (by100 blast)
                      hence "X - (?B - {x}) \<in> TX" using closedin_diff_open by (by100 blast)
                      have "{x} = ?B \<inter> (X - (?B - {x}))" using hx hB_sub by (by100 blast)
                      have "{x} \<in> {?B \<inter> U | U. U \<in> TX}"
                        using \<open>X - (?B - {x}) \<in> TX\<close> \<open>{x} = ?B \<inter> _\<close> by (by100 blast)
                      thus "{x} \<in> subspace_topology X TX ?B"
                        unfolding subspace_topology_def .
                    qed
                    from compact_discrete_finite[OF hB_compact hB_discrete] show ?thesis .
                  qed
                  have hsel_inj: "inj_on sel ?\<A>_int"
                  proof (rule inj_onI)
                    fix A1 A2 assume hA1: "A1 \<in> ?\<A>_int" and hA2: "A2 \<in> ?\<A>_int" and heq: "sel A1 = sel A2"
                    show "A1 = A2"
                    proof (rule ccontr)
                      assume "A1 \<noteq> A2"
                      have "A1 \<in> \<A>X" "A2 \<in> \<A>X" using hA1 hA2 by (by100 blast)+
                      have "sel A1 \<in> A1" "sel A2 \<in> A2" using hsel hA1 hA2 by (by100 blast)+
                      have "sel A1 \<in> A2" using \<open>sel A2 \<in> A2\<close> heq by (by100 simp)
                      have "sel A1 \<in> A1 \<inter> A2" using \<open>sel A1 \<in> A1\<close> \<open>sel A1 \<in> A2\<close> by (by100 blast)
                      from h\<A>X_inter[rule_format, OF \<open>A1 \<in> \<A>X\<close> \<open>A2 \<in> \<A>X\<close> \<open>A1 \<noteq> A2\<close>]
                      have "sel A1 \<in> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
                        using \<open>sel A1 \<in> A1 \<inter> A2\<close> by (by100 blast)
                      moreover have "sel A1 \<notin> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
                        using hsel hA1 by (by100 blast)
                      ultimately show False by (by100 blast)
                    qed
                  qed
                  from finite_imageD[OF hB_fin hsel_inj] show ?thesis .
                qed
                \<comment> \<open>Step 2: Vertices \<inter> K finite.\<close>
                let ?Vertices = "\<Union>A\<in>\<A>X. top1_arc_endpoints_on A (subspace_topology X TX A)"
                have hVK_fin: "finite (?Vertices \<inter> ?K)"
                proof -
                  \<comment> \<open>Vertices \<inter> A \<subseteq> endpoints(A) (\<le> 2 pts per arc). Same selection pattern.\<close>
                  have hV_sub_X: "?Vertices \<subseteq> X" using h\<A>X
                    unfolding top1_arc_endpoints_on_def by (by5000 blast)
                  have hVK_sub: "?Vertices \<inter> ?K \<subseteq> X" using hV_sub_X by (by100 blast)
                  have hVA_bound: "\<forall>A\<in>\<A>X. ?Vertices \<inter> A \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                  proof (intro ballI subsetI)
                    fix A v assume "A \<in> \<A>X" "v \<in> ?Vertices \<inter> A"
                    hence "v \<in> A" by (by100 blast)
                    from \<open>v \<in> ?Vertices \<inter> A\<close> obtain B where "B \<in> \<A>X"
                        "v \<in> top1_arc_endpoints_on B (subspace_topology X TX B)" by (by100 blast)
                    show "v \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                    proof (cases "A = B")
                      case True thus ?thesis using \<open>v \<in> top1_arc_endpoints_on B _\<close> by (by100 simp)
                    next
                      case False
                      have "v \<in> A \<inter> B" using \<open>v \<in> A\<close> \<open>v \<in> top1_arc_endpoints_on B _\<close>
                        unfolding top1_arc_endpoints_on_def by (by100 blast)
                      from h\<A>X_inter[rule_format, OF \<open>A \<in> \<A>X\<close> \<open>B \<in> \<A>X\<close> False]
                      show ?thesis using \<open>v \<in> A \<inter> B\<close> by (by100 blast)
                    qed
                  qed
                  \<comment> \<open>Every subset of Vertices \<inter> K closed in X (finite \<inter> per arc, Hausdorff).\<close>
                  have hV_all_cl: "\<forall>S. S \<subseteq> ?Vertices \<inter> ?K \<longrightarrow> closedin_on X TX S"
                  proof (intro allI impI)
                    fix S assume "S \<subseteq> ?Vertices \<inter> ?K"
                    have "S \<subseteq> X" using \<open>S \<subseteq> ?Vertices \<inter> ?K\<close> hVK_sub by (by100 blast)
                    have "\<forall>A\<in>\<A>X. closedin_on A (subspace_topology X TX A) (A \<inter> S)"
                    proof (intro ballI)
                      fix A assume "A \<in> \<A>X"
                      have "A \<inter> S \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                        using \<open>S \<subseteq> ?Vertices \<inter> ?K\<close> hVA_bound[rule_format, OF \<open>A \<in> \<A>X\<close>] by (by100 blast)
                      have "finite (top1_arc_endpoints_on A (subspace_topology X TX A))"
                      proof -
                        have "top1_is_arc_on A (subspace_topology X TX A)" using h\<A>X \<open>A \<in> \<A>X\<close> by (by100 blast)
                        then obtain h' where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                            A (subspace_topology X TX A) h'" unfolding top1_is_arc_on_def by (by100 blast)
                        have hX_strict: "is_topology_on_strict X TX"
                          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        have hX_haus: "is_hausdorff_on X TX"
                          using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        have "A \<subseteq> X" using h\<A>X \<open>A \<in> \<A>X\<close> by (by100 blast)
                        from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>A \<subseteq> X\<close>
                            \<open>top1_is_arc_on A _\<close> \<open>top1_homeomorphism_on _ _ A _ h'\<close>]
                        show ?thesis by (by100 simp)
                      qed
                      hence "finite (A \<inter> S)"
                        using finite_subset[OF \<open>A \<inter> S \<subseteq> _\<close>] by (by100 blast)
                      have "A \<subseteq> X" using h\<A>X \<open>A \<in> \<A>X\<close> by (by100 blast)
                      have hA_haus: "is_hausdorff_on A (subspace_topology X TX A)"
                      proof -
                        have "is_hausdorff_on X TX" using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                        from conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>A \<subseteq> X\<close> this show ?thesis by (by100 blast)
                      qed
                      have hA_T1: "top1_T1_on A (subspace_topology X TX A)" by (rule hausdorff_imp_T1_on[OF hA_haus])
                      have hA_top: "is_topology_on A (subspace_topology X TX A)"
                        using hA_haus unfolding is_hausdorff_on_def by (by100 blast)
                      have hAS_eq: "A \<inter> S = \<Union>((\<lambda>x. {x}) ` (A \<inter> S))" by (by100 blast)
                      have hAS_fin: "finite ((\<lambda>x. {x}) ` (A \<inter> S))" using \<open>finite (A \<inter> S)\<close> by (by100 simp)
                      have hAS_cl: "\<forall>U\<in>((\<lambda>x. {x}) ` (A \<inter> S)). closedin_on A (subspace_topology X TX A) U"
                      proof (intro ballI)
                        fix U assume "U \<in> (\<lambda>x. {x}) ` (A \<inter> S)"
                        then obtain y where "y \<in> A" "U = {y}" by (by100 blast)
                        thus "closedin_on A (subspace_topology X TX A) U"
                          using hA_T1 unfolding top1_T1_on_def by (by100 blast)
                      qed
                      from closedin_Union_finite[OF hA_top hAS_fin hAS_cl]
                      show "closedin_on A (subspace_topology X TX A) (A \<inter> S)" using hAS_eq by (by100 simp)
                    qed
                    from h\<A>X_coh[rule_format, OF \<open>S \<subseteq> X\<close>] this show "closedin_on X TX S" by (by100 blast)
                  qed
                  \<comment> \<open>Vertices \<inter> K compact+discrete \<Rightarrow> finite.\<close>
                  have hVK_cl_X: "closedin_on X TX (?Vertices \<inter> ?K)" using hV_all_cl by (by100 blast)
                  have hX_top_loc: "is_topology_on X TX"
                    using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by5000 blast)
                  have hVK_cl_K: "closedin_on ?K (subspace_topology X TX ?K) (?Vertices \<inter> ?K)"
                    by (rule closedin_subspace_from_ambient[OF hX_top_loc hVK_cl_X hfI_sub]) (by100 blast)
                  have hVK_compact': "top1_compact_on (?Vertices \<inter> ?K) (subspace_topology X TX (?Vertices \<inter> ?K))"
                  proof -
                    \<comment> \<open>Need K compact. Re-derive from hB\_fin proof.\<close>
                    have hI_compact2: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
                      unfolding top1_unit_interval_def top1_unit_interval_topology_def
                      using Theorem_27_1[of "0::real" 1] by (by100 simp)
                    have hfI_compact2: "top1_compact_on ?K (subspace_topology X TX ?K)"
                    proof -
                      have "\<forall>t\<in>top1_unit_interval. f t \<in> X" using hfI_sub by (by100 blast)
                      have "\<forall>U\<in>TX. {t \<in> top1_unit_interval. f t \<in> U} \<in> top1_unit_interval_topology"
                      proof (intro ballI)
                        fix U assume "U \<in> TX"
                        have "U \<inter> ?U \<in> ?TU" unfolding subspace_topology_def using \<open>U \<in> TX\<close> by (by100 blast)
                        have "\<forall>V\<in>?TU. {t \<in> top1_unit_interval. f t \<in> V} \<in> top1_unit_interval_topology"
                          using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
                        hence "{t \<in> top1_unit_interval. f t \<in> U \<inter> ?U} \<in> top1_unit_interval_topology"
                          using \<open>U \<inter> ?U \<in> ?TU\<close> by (by100 blast)
                        moreover have "{t \<in> top1_unit_interval. f t \<in> U \<inter> ?U} =
                            {t \<in> top1_unit_interval. f t \<in> U}" using hf_img_sub by (by100 blast)
                        ultimately show "{t \<in> top1_unit_interval. f t \<in> U} \<in> top1_unit_interval_topology"
                          by (by100 simp)
                      qed
                      hence "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX f"
                        unfolding top1_continuous_map_on_def
                        using \<open>\<forall>t\<in>top1_unit_interval. f t \<in> X\<close> by (by100 blast)
                      from top1_compact_on_continuous_image[OF hI_compact2 hX_top_loc this]
                      show ?thesis .
                    qed
                    from Theorem_26_2[OF hfI_compact2 hVK_cl_K]
                    have "top1_compact_on (?Vertices \<inter> ?K) (subspace_topology ?K (subspace_topology X TX ?K) (?Vertices \<inter> ?K))" .
                    moreover have "subspace_topology ?K (subspace_topology X TX ?K) (?Vertices \<inter> ?K) = subspace_topology X TX (?Vertices \<inter> ?K)"
                      by (rule subspace_topology_trans) (by100 blast)
                    ultimately show ?thesis by (by100 simp)
                  qed
                  have hVK_discrete: "\<forall>x\<in>?Vertices \<inter> ?K. {x} \<in> subspace_topology X TX (?Vertices \<inter> ?K)"
                  proof (intro ballI)
                    fix x assume hx: "x \<in> ?Vertices \<inter> ?K"
                    have "(?Vertices \<inter> ?K) - {x} \<subseteq> ?Vertices \<inter> ?K" by (by100 blast)
                    have "closedin_on X TX ((?Vertices \<inter> ?K) - {x})" using hV_all_cl \<open>_ - {x} \<subseteq> _\<close> by (by100 blast)
                    hence "X - ((?Vertices \<inter> ?K) - {x}) \<in> TX" using closedin_diff_open by (by100 blast)
                    have "{x} = (?Vertices \<inter> ?K) \<inter> (X - ((?Vertices \<inter> ?K) - {x}))"
                      using hx hVK_sub by (by100 blast)
                    have "{x} \<in> {(?Vertices \<inter> ?K) \<inter> U | U. U \<in> TX}"
                      using \<open>X - _ \<in> TX\<close> \<open>{x} = _ \<inter> _\<close> by (by100 blast)
                    thus "{x} \<in> subspace_topology X TX (?Vertices \<inter> ?K)"
                      unfolding subspace_topology_def .
                  qed
                  from compact_discrete_finite[OF hVK_compact' hVK_discrete] show ?thesis .
                qed
                \<comment> \<open>Step 3: For each vertex v \<in> K, pick one arc \<subseteq> \<Union>C containing v (from coverage).\<close>
                have h\<A>int_sub: "?\<A>_int \<subseteq> {A \<in> \<A>X. A \<subseteq> \<Union>C}"
                proof (intro subsetI)
                  fix A assume "A \<in> ?\<A>_int"
                  hence "A \<in> \<A>X" and "\<exists>x. x \<in> A \<and> x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A) \<and> x \<in> ?K"
                    by (by100 blast)+
                  then obtain x where "x \<in> A" "x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)" "x \<in> ?K"
                    by (by100 blast)
                  have "x \<in> \<Union>C" using \<open>x \<in> ?K\<close> hf_img_sub by (by100 blast)
                  then obtain Ti where "Ti \<in> C" "x \<in> Ti" by (by100 blast)
                  have "Ti \<in> \<A>" using \<open>Ti \<in> C\<close> hC unfolding chains_def by (by100 blast)
                  hence "\<forall>A\<in>\<A>X. A \<subseteq> Ti \<or> A \<inter> Ti \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                    unfolding \<A>_def by (by100 blast)
                  from this[rule_format, OF \<open>A \<in> \<A>X\<close>]
                  have "A \<subseteq> Ti" using \<open>x \<in> A\<close> \<open>x \<in> Ti\<close>
                      \<open>x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)\<close> by (by100 blast)
                  thus "A \<in> {A \<in> \<A>X. A \<subseteq> \<Union>C}" using \<open>A \<in> \<A>X\<close> \<open>Ti \<in> C\<close> \<open>A \<subseteq> Ti\<close> by (by100 blast)
                qed
                define vsel where "vsel \<equiv> \<lambda>v. SOME A. A \<in> \<A>X \<and> A \<subseteq> \<Union>C \<and> v \<in> A"
                have hvsel: "\<forall>v\<in>?Vertices \<inter> ?K. vsel v \<in> \<A>X \<and> vsel v \<subseteq> \<Union>C \<and> v \<in> vsel v"
                proof (intro ballI conjI)
                  fix v assume "v \<in> ?Vertices \<inter> ?K"
                  hence "v \<in> ?K" by (by100 blast)
                  hence "v \<in> \<Union>C" using hf_img_sub by (by100 blast)
                  then obtain Ti where "Ti \<in> C" "v \<in> Ti" by (by100 blast)
                  have "Ti \<in> \<A>" using \<open>Ti \<in> C\<close> hC unfolding chains_def by (by100 blast)
                  hence "Ti = \<Union>{A \<in> \<A>X. A \<subseteq> Ti}" unfolding \<A>_def by (by100 blast)
                  hence "v \<in> \<Union>{A \<in> \<A>X. A \<subseteq> Ti}" using \<open>v \<in> Ti\<close> by (by100 simp)
                  then obtain A where "A \<in> \<A>X" "A \<subseteq> Ti" "v \<in> A" by (by100 blast)
                  have "A \<subseteq> \<Union>C" using \<open>A \<subseteq> Ti\<close> \<open>Ti \<in> C\<close> by (by100 blast)
                  hence "\<exists>A. A \<in> \<A>X \<and> A \<subseteq> \<Union>C \<and> v \<in> A" using \<open>A \<in> \<A>X\<close> \<open>v \<in> A\<close> by (by100 blast)
                  from someI_ex[OF this] show "vsel v \<in> \<A>X" "vsel v \<subseteq> \<Union>C" "v \<in> vsel v"
                    unfolding vsel_def by (by100 blast)+
                qed
                let ?\<A>_vert = "vsel ` (?Vertices \<inter> ?K)"
                let ?\<A>0 = "?\<A>_int \<union> ?\<A>_vert"
                have h\<A>0_fin: "finite ?\<A>0"
                  using h\<A>int_fin hVK_fin by (by100 simp)
                have h\<A>0_sub: "?\<A>0 \<subseteq> {A \<in> \<A>X. A \<subseteq> \<Union>C}"
                  using h\<A>int_sub hvsel by (by5000 blast)
                \<comment> \<open>Step 4: \<A>0 covers K (interior arcs cover non-vertices, vertex arcs cover vertices).\<close>
                have h\<A>0_cover: "?K \<subseteq> \<Union>?\<A>0"
                proof
                  fix x assume "x \<in> ?K"
                  hence "x \<in> X" using hfI_sub by (by100 blast)
                  hence "x \<in> \<Union>\<A>X" using h\<A>X_cover by (by100 simp)
                  then obtain A where "A \<in> \<A>X" "x \<in> A" by (by100 blast)
                  show "x \<in> \<Union>?\<A>0"
                  proof (cases "x \<in> ?Vertices")
                    case True
                    have "x \<in> ?Vertices \<inter> ?K" using True \<open>x \<in> ?K\<close> by (by100 blast)
                    have "vsel x \<in> ?\<A>_vert" using \<open>x \<in> ?Vertices \<inter> ?K\<close> by (by100 blast)
                    have "x \<in> vsel x" using hvsel \<open>x \<in> ?Vertices \<inter> ?K\<close> by (by100 blast)
                    thus ?thesis using \<open>vsel x \<in> ?\<A>_vert\<close> by (by100 blast)
                  next
                    case False
                    have "x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
                    proof
                      assume "x \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                      hence "x \<in> ?Vertices" using \<open>A \<in> \<A>X\<close> by (by100 blast)
                      thus False using False by (by100 blast)
                    qed
                    hence "A \<in> ?\<A>_int" using \<open>A \<in> \<A>X\<close> \<open>x \<in> A\<close> \<open>x \<in> ?K\<close> by (by100 blast)
                    thus ?thesis using \<open>x \<in> A\<close> by (by100 blast)
                  qed
                qed
                \<comment> \<open>Step 5: Each arc in \<A>0 is in a chain element.\<close>
                have "\<forall>A\<in>?\<A>0. \<exists>Ti\<in>C. A \<subseteq> Ti"
                proof (intro ballI)
                  fix A assume "A \<in> ?\<A>0"
                  hence "A \<in> \<A>X" "A \<subseteq> \<Union>C" using h\<A>0_sub by (by100 blast)+
                  from harc_in_chain[rule_format, OF this] show "\<exists>Ti\<in>C. A \<subseteq> Ti" .
                qed
                \<comment> \<open>Step 6: Choice function + finite chain max.\<close>
                define g where "g \<equiv> \<lambda>A. SOME Ti. Ti \<in> C \<and> A \<subseteq> Ti"
                have hg: "\<forall>A\<in>?\<A>0. g A \<in> C \<and> A \<subseteq> g A"
                proof (intro ballI conjI)
                  fix A assume "A \<in> ?\<A>0"
                  hence "\<exists>Ti\<in>C. A \<subseteq> Ti" using \<open>\<forall>A\<in>?\<A>0. \<exists>Ti\<in>C. A \<subseteq> Ti\<close> by (by100 blast)
                  hence "\<exists>Ti. Ti \<in> C \<and> A \<subseteq> Ti" by (by100 blast)
                  from someI_ex[OF this] show "g A \<in> C" "A \<subseteq> g A"
                    unfolding g_def by (by100 blast)+
                qed
                let ?chain_elts = "g ` ?\<A>0"
                have hfin_ce: "finite ?chain_elts" using h\<A>0_fin by (by100 simp)
                have hce_sub: "?chain_elts \<subseteq> C" using hg by (by100 blast)
                \<comment> \<open>Finite chain max (proved via finite\_ne\_induct).\<close>
                have hfcm: "\<And>S. finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> S \<subseteq> C \<Longrightarrow>
                    (\<forall>a\<in>S. \<forall>b\<in>S. a \<subseteq> b \<or> b \<subseteq> a) \<Longrightarrow> \<exists>m\<in>S. \<forall>x\<in>S. x \<subseteq> m"
                proof -
                  fix S :: "'a set set" assume hfin: "finite S" and hne: "S \<noteq> {}"
                      and hsub: "S \<subseteq> C" and hcomp: "\<forall>a\<in>S. \<forall>b\<in>S. a \<subseteq> b \<or> b \<subseteq> a"
                  from hfin hne hcomp show "\<exists>m\<in>S. \<forall>x\<in>S. x \<subseteq> m"
                  proof (induction S rule: finite_ne_induct)
                    case (singleton x) show ?case by (by100 blast)
                  next
                    case (insert x F)
                    from insert.prems have "\<forall>a\<in>F. \<forall>b\<in>F. a \<subseteq> b \<or> b \<subseteq> a" by (by100 blast)
                    from insert.IH[OF this] obtain m where "m \<in> F" "\<forall>y\<in>F. y \<subseteq> m" by (by100 blast)
                    have "x \<subseteq> m \<or> m \<subseteq> x" using insert.prems \<open>m \<in> F\<close> by (by100 blast)
                    thus ?case
                    proof
                      assume "x \<subseteq> m"
                      hence "\<forall>y\<in>insert x F. y \<subseteq> m" using \<open>\<forall>y\<in>F. y \<subseteq> m\<close> by (by100 blast)
                      thus ?thesis using \<open>m \<in> F\<close> by (by100 blast)
                    next
                      assume "m \<subseteq> x"
                      hence "\<forall>y\<in>insert x F. y \<subseteq> x" using \<open>\<forall>y\<in>F. y \<subseteq> m\<close> by (by100 blast)
                      thus ?thesis by (by100 blast)
                    qed
                  qed
                qed
                have "\<exists>Tk \<in> C. \<forall>Ti \<in> ?chain_elts. Ti \<subseteq> Tk"
                proof (cases "?\<A>0 = {}")
                  case True
                  hence "?chain_elts = {}" by (by100 simp)
                  from hU_x0 obtain T0 where "T0 \<in> C" by (by100 blast)
                  have "\<forall>Ti\<in>?chain_elts. Ti \<subseteq> T0" using \<open>?chain_elts = {}\<close> by (by100 blast)
                  thus ?thesis using \<open>T0 \<in> C\<close> by (by100 blast)
                next
                  case False
                  hence hce_ne: "?chain_elts \<noteq> {}" by (by100 simp)
                  have "\<forall>a\<in>?chain_elts. \<forall>b\<in>?chain_elts. a \<subseteq> b \<or> b \<subseteq> a"
                  proof (intro ballI)
                    fix a b assume "a \<in> ?chain_elts" "b \<in> ?chain_elts"
                    have ha: "a \<in> C" using \<open>a \<in> ?chain_elts\<close> hce_sub by (by100 blast)
                    have hb: "b \<in> C" using \<open>b \<in> ?chain_elts\<close> hce_sub by (by100 blast)
                    thus "a \<subseteq> b \<or> b \<subseteq> a"
                      using hC ha hb unfolding chains_def chain_subset_def by (by5000 blast)
                  qed
                  from hfcm[OF hfin_ce hce_ne hce_sub this]
                  have hex: "\<exists>m\<in>?chain_elts. \<forall>x\<in>?chain_elts. x \<subseteq> m" .
                  \<comment> \<open>Workaround: define the chain\_elts set to simplify the term for automation.\<close>
                  define CE where "CE = ?chain_elts"
                  have hex': "\<exists>m\<in>CE. \<forall>x\<in>CE. x \<subseteq> m" using hex unfolding CE_def .
                  then obtain m where hm_in': "m \<in> CE" and hm_max': "\<forall>x\<in>CE. x \<subseteq> m"
                    by (by100 auto)
                  have hm_in: "m \<in> ?chain_elts" using hm_in' unfolding CE_def .
                  have hm_max: "\<forall>x\<in>?chain_elts. x \<subseteq> m" using hm_max' unfolding CE_def .
                  have "m \<in> C"
                  proof -
                    have "?chain_elts \<subseteq> C" using hce_sub .
                    thus ?thesis using \<open>m \<in> ?chain_elts\<close> by (by100 blast)
                  qed
                  show ?thesis using \<open>m \<in> C\<close> \<open>\<forall>x\<in>?chain_elts. x \<subseteq> m\<close> by (by100 blast)
                qed
                then obtain Tk where hTk_max: "Tk \<in> C" "\<forall>Ti\<in>?chain_elts. Ti \<subseteq> Tk"
                  by (by5000 auto)
                \<comment> \<open>Step 7: f(I) \<subseteq> Tk.\<close>
                have "f ` top1_unit_interval \<subseteq> Tk"
                proof
                  fix x assume "x \<in> f ` top1_unit_interval"
                  have "x \<in> ?K" using \<open>x \<in> f ` top1_unit_interval\<close> by (by100 blast)
                  from subsetD[OF h\<A>0_cover this]
                  have "x \<in> \<Union>?\<A>0" .
                  then obtain A where hA_0: "A \<in> ?\<A>0" "x \<in> A" by (by100 blast)
                  have "g A \<in> ?chain_elts" using \<open>A \<in> ?\<A>0\<close> by (by100 blast)
                  hence "g A \<subseteq> Tk" using hTk_max(2) by (by100 blast)
                  have "A \<subseteq> g A" using hg \<open>A \<in> ?\<A>0\<close> by (by100 blast)
                  thus "x \<in> Tk" using \<open>x \<in> A\<close> \<open>A \<subseteq> g A\<close> \<open>g A \<subseteq> Tk\<close> by (by100 blast)
                qed
                thus ?thesis using \<open>Tk \<in> C\<close> by (by100 blast)
              qed
              then obtain Tk where hTk: "Tk \<in> C" "f ` top1_unit_interval \<subseteq> Tk" by (by100 blast)
              \<comment> \<open>f is a loop in Tk: f continuous into Tk, f(0)=f(1)=x0.\<close>
              have hf_loop_Tk: "top1_is_loop_on Tk (subspace_topology X TX Tk) x0 f"
              proof -
                have hTk_sub: "Tk \<subseteq> X"
                  using \<open>Tk \<in> C\<close> hC unfolding chains_def \<A>_def by (by100 blast)
                have hf_cont_Tk: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                    Tk (subspace_topology X TX Tk) f"
                proof -
                  \<comment> \<open>f: I \<rightarrow> \<Union>C cont, f(I) \<subseteq> Tk. Restrict codomain: I \<rightarrow> Tk.\<close>
                  have "\<forall>t\<in>top1_unit_interval. f t \<in> Tk" using hTk(2) by (by100 blast)
                  have hTk_sub_U: "Tk \<subseteq> ?U" using \<open>Tk \<in> C\<close> by (by100 blast)
                  from continuous_map_restrict_codomain[OF hf_cont \<open>\<forall>t\<in>_. f t \<in> Tk\<close> hTk_sub_U]
                  have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                      Tk (subspace_topology ?U ?TU Tk) f" .
                  have "subspace_topology ?U ?TU Tk = subspace_topology X TX Tk"
                    by (rule subspace_topology_trans[OF hTk_sub_U])
                  thus ?thesis using \<open>top1_continuous_map_on _ _ Tk _ f\<close> by (by100 simp)
                qed
                have "x0 \<in> Tk"
                proof -
                  have "0 \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
                  hence "f 0 \<in> Tk" using hTk(2) by (by100 blast)
                  thus ?thesis using hf0 by (by100 simp)
                qed
                show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
                  using hf_cont_Tk hf0 hf1 \<open>x0 \<in> Tk\<close> by (by100 blast)
              qed
              show ?thesis using that[OF hTk(1) hf_loop_Tk] .
            qed
            \<comment> \<open>Step 2: Tk is simply connected (tree).\<close>
            have "Tk \<in> \<A>" using hTk_C hC unfolding chains_def by (by100 blast)
            hence "top1_is_tree_on Tk (subspace_topology X TX Tk)" unfolding \<A>_def by (by100 blast)
            hence "top1_simply_connected_on Tk (subspace_topology X TX Tk)"
              unfolding top1_is_tree_on_def by (by100 blast)
            hence "\<forall>x0'\<in>Tk. \<forall>g. top1_is_loop_on Tk (subspace_topology X TX Tk) x0' g
                \<longrightarrow> top1_path_homotopic_on Tk (subspace_topology X TX Tk) x0' x0' g (top1_constant_path x0')"
              unfolding top1_simply_connected_on_def by (by100 blast)
            have hx0_Tk: "x0 \<in> Tk"
            proof -
              have "Tk \<in> \<A>" using hTk_C hC unfolding chains_def by (by100 blast)
              thus ?thesis unfolding \<A>_def by (by100 blast)
            qed
            hence "top1_path_homotopic_on Tk (subspace_topology X TX Tk) x0 x0 f (top1_constant_path x0)"
              using hf_in_Tk \<open>\<forall>x0'\<in>Tk. _\<close> hx0_Tk by (by100 blast)
            \<comment> \<open>Step 3: Lift homotopy from Tk to UC.\<close>
            have hTk_sub_U: "Tk \<subseteq> ?U" using hTk_C by (by100 blast)
            \<comment> \<open>Lift: path_homotopic in Tk → path_homotopic in UC via codomain enlargement.\<close>
            have "top1_path_homotopic_on ?U ?TU x0 x0 f (top1_constant_path x0)"
            proof -
              from \<open>top1_path_homotopic_on Tk (subspace_topology X TX Tk) x0 x0 f (top1_constant_path x0)\<close>
              obtain F where hF_cont: "top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval) II_topology
                    Tk (subspace_topology X TX Tk) F"
                  and hF0: "\<forall>s\<in>top1_unit_interval. F (s, 0) = f s"
                  and hF1: "\<forall>s\<in>top1_unit_interval. F (s, 1) = top1_constant_path x0 s"
                  and hFL: "\<forall>t\<in>top1_unit_interval. F (0, t) = x0"
                  and hFR: "\<forall>t\<in>top1_unit_interval. F (1, t) = x0"
                unfolding top1_path_homotopic_on_def by (by5000 blast)
              \<comment> \<open>Enlarge codomain: F maps into Tk \<subseteq> UC, so it maps into UC.\<close>
              from top1_continuous_map_on_codomain_enlarge[OF hF_cont hTk_sub_U hU_sub]
              have "top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval) II_topology
                  ?U ?TU F" .
              \<comment> \<open>f and const_x0 are paths in UC (from the loop assumption).\<close>
              have hf_path: "top1_is_path_on ?U ?TU x0 x0 f"
                using hf_loop unfolding top1_is_loop_on_def by (by100 blast)
              have hconst_path: "top1_is_path_on ?U ?TU x0 x0 (top1_constant_path x0)"
                by (rule top1_constant_path_is_path[OF hTU hU_x0])
              show ?thesis unfolding top1_path_homotopic_on_def
                using hf_path hconst_path \<open>top1_continuous_map_on _ _ ?U ?TU F\<close> hF0 hF1 hFL hFR
                by (by100 blast)
            qed
            thus "top1_path_homotopic_on ?U ?TU x0 x0 f (top1_constant_path x0)" .
          qed
          show ?thesis using top1_simply_connected_from_one_point[OF hTU hU_pc hU_x0] hU_loops
            unfolding top1_simply_connected_on_def by (by100 blast)
        qed
      next
        \<comment> \<open>Graph: arcs of \<Union>C are {A \<in> \<A>X | A \<subseteq> \<Union>C}.
           Use subgraph\_union\_of\_arcs\_is\_graph.\<close>
        show "top1_is_graph_on (\<Union>C) (subspace_topology X TX (\<Union>C))"
        proof -
          \<comment> \<open>Coverage: \<Union>C = \<Union>{A \<in> \<A>X. A \<subseteq> \<Union>C}.\<close>
          have hUC_coverage: "\<Union>C = \<Union>{A \<in> \<A>X. A \<subseteq> \<Union>C}"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> \<Union>C"
            then obtain Ti where "Ti \<in> C" "x \<in> Ti" by (by100 blast)
            have "Ti \<in> \<A>" using \<open>Ti \<in> C\<close> hC unfolding chains_def by (by100 blast)
            hence "Ti = \<Union>{A \<in> \<A>X. A \<subseteq> Ti}" unfolding \<A>_def by (by100 blast)
            hence "x \<in> \<Union>{A \<in> \<A>X. A \<subseteq> Ti}" using \<open>x \<in> Ti\<close> by (by100 simp)
            then obtain A where "A \<in> \<A>X" "A \<subseteq> Ti" "x \<in> A" by (by100 blast)
            have "A \<subseteq> \<Union>C" using \<open>A \<subseteq> Ti\<close> \<open>Ti \<in> C\<close> by (by100 blast)
            thus "x \<in> \<Union>{A \<in> \<A>X. A \<subseteq> \<Union>C}" using \<open>A \<in> \<A>X\<close> \<open>x \<in> A\<close> by (by100 blast)
          next
            fix x assume "x \<in> \<Union>{A \<in> \<A>X. A \<subseteq> \<Union>C}" thus "x \<in> \<Union>C" by (by100 blast)
          qed
          \<comment> \<open>Use subgraph\_union\_of\_arcs\_is\_graph with ambient topology X TX.\<close>
          let ?\<A>C = "{A \<in> \<A>X. A \<subseteq> \<Union>C}"
          have h_arcs: "\<forall>A\<in>?\<A>C. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
            using h\<A>X by (by100 blast)
          have h_cover: "\<Union>?\<A>C \<subseteq> X" using h\<A>X by (by100 blast)
          have h_inter: "\<forall>A\<in>?\<A>C. \<forall>B\<in>?\<A>C. A \<noteq> B \<longrightarrow>
               A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
             \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
             \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
            using h\<A>X_inter by (by100 blast)
          have hUC_coh: "\<forall>D. D \<subseteq> \<Union>?\<A>C \<longrightarrow>
              (closedin_on (\<Union>?\<A>C) (subspace_topology X TX (\<Union>?\<A>C)) D \<longleftrightarrow>
               (\<forall>A\<in>?\<A>C. closedin_on A (subspace_topology X TX A) (A \<inter> D)))"
          proof (intro allI impI iffI ballI)
            \<comment> \<open>Forward: closed in \<Union>C \<Rightarrow> per-arc closed (Theorem\_17\_2).\<close>
            fix D A assume hD: "D \<subseteq> \<Union>?\<A>C" and hcl: "closedin_on (\<Union>?\<A>C) (subspace_topology X TX (\<Union>?\<A>C)) D"
                and "A \<in> ?\<A>C"
            have hX_top: "is_topology_on X TX"
              using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by5000 blast)
            have hA_sub_UC: "A \<subseteq> \<Union>?\<A>C" using \<open>A \<in> ?\<A>C\<close> by (by100 blast)
            have hUC_sub_X: "\<Union>?\<A>C \<subseteq> X" using h_cover .
            from Theorem_17_2[OF subspace_topology_is_topology_on[OF hX_top hUC_sub_X] hA_sub_UC]
            have "closedin_on A (subspace_topology (\<Union>?\<A>C) (subspace_topology X TX (\<Union>?\<A>C)) A)
                (A \<inter> D)" using hcl by (by100 blast)
            have "subspace_topology (\<Union>?\<A>C) (subspace_topology X TX (\<Union>?\<A>C)) A =
                subspace_topology X TX A"
              by (rule subspace_topology_trans[OF hA_sub_UC])
            thus "closedin_on A (subspace_topology X TX A) (A \<inter> D)"
              using \<open>closedin_on A _ (A \<inter> D)\<close> by (by100 simp)
          next
            \<comment> \<open>Backward: per-arc closed \<Rightarrow> closed in X \<Rightarrow> closed in \<Union>C.\<close>
            fix D assume hD: "D \<subseteq> \<Union>?\<A>C"
                and hall_coh: "\<forall>A\<in>?\<A>C. closedin_on A (subspace_topology X TX A) (A \<inter> D)"
            have hD_sub_X: "D \<subseteq> X" using hD h_cover by (by100 blast)
            \<comment> \<open>Show D closed in X via h\<A>X\_coh.\<close>
            have "\<forall>A\<in>\<A>X. closedin_on A (subspace_topology X TX A) (A \<inter> D)"
            proof (intro ballI)
              fix A assume "A \<in> \<A>X"
              show "closedin_on A (subspace_topology X TX A) (A \<inter> D)"
              proof (cases "A \<in> ?\<A>C")
                case True from hall_coh[rule_format, OF True] show ?thesis .
              next
                case False hence "A \<notin> ?\<A>C" .
                hence "\<not> A \<subseteq> \<Union>C" using \<open>A \<in> \<A>X\<close> by (by100 blast)
                from hU_subgraph[rule_format, OF \<open>A \<in> \<A>X\<close>]
                have "A \<inter> \<Union>C \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                  using \<open>\<not> A \<subseteq> \<Union>C\<close> by (by100 blast)
                have "A \<inter> D \<subseteq> A \<inter> \<Union>C" using hD hUC_coverage by (by100 blast)
                hence "A \<inter> D \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                  using \<open>A \<inter> \<Union>C \<subseteq> _\<close> by (by100 blast)
                \<comment> \<open>Finite set in Hausdorff is closed.\<close>
                have "finite (A \<inter> D)"
                proof -
                  have "finite (top1_arc_endpoints_on A (subspace_topology X TX A))"
                  proof -
                    have "top1_is_arc_on A (subspace_topology X TX A)" using h\<A>X \<open>A \<in> \<A>X\<close> by (by100 blast)
                    then obtain h' where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                        A (subspace_topology X TX A) h'" unfolding top1_is_arc_on_def by (by100 blast)
                    have "A \<subseteq> X" using h\<A>X \<open>A \<in> \<A>X\<close> by (by100 blast)
                    have hX_strict: "is_topology_on_strict X TX"
                      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                    have hX_haus: "is_hausdorff_on X TX"
                      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                    from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>A \<subseteq> X\<close>
                        \<open>top1_is_arc_on A (subspace_topology X TX A)\<close>
                        \<open>top1_homeomorphism_on _ _ A _ h'\<close>]
                    show ?thesis by (by100 simp)
                  qed
                  thus ?thesis
                    using finite_subset[OF \<open>A \<inter> D \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)\<close>]
                    by (by100 blast)
                qed
                have "A \<subseteq> X" using h\<A>X \<open>A \<in> \<A>X\<close> by (by100 blast)
                have hA_haus: "is_hausdorff_on A (subspace_topology X TX A)"
                proof -
                  have "is_hausdorff_on X TX" using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
                  from conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>A \<subseteq> X\<close> this show ?thesis by (by100 blast)
                qed
                have hA_T1: "top1_T1_on A (subspace_topology X TX A)" by (rule hausdorff_imp_T1_on[OF hA_haus])
                have hA_top: "is_topology_on A (subspace_topology X TX A)"
                  using hA_haus unfolding is_hausdorff_on_def by (by100 blast)
                have hAD_eq: "A \<inter> D = \<Union>((\<lambda>x. {x}) ` (A \<inter> D))" by (by100 blast)
                have himg_fin: "finite ((\<lambda>x. {x}) ` (A \<inter> D))" using \<open>finite (A \<inter> D)\<close> by (by100 simp)
                have himg_cl: "\<forall>U\<in>((\<lambda>x. {x}) ` (A \<inter> D)). closedin_on A (subspace_topology X TX A) U"
                proof (intro ballI)
                  fix U assume "U \<in> (\<lambda>x. {x}) ` (A \<inter> D)"
                  then obtain y where "y \<in> A" "U = {y}" by (by100 blast)
                  thus "closedin_on A (subspace_topology X TX A) U"
                    using hA_T1 unfolding top1_T1_on_def by (by100 blast)
                qed
                from closedin_Union_finite[OF hA_top himg_fin himg_cl]
                show ?thesis using hAD_eq by (by100 simp)
              qed
            qed
            from h\<A>X_coh[rule_format, OF hD_sub_X] \<open>\<forall>A\<in>\<A>X. closedin_on A _ (A \<inter> D)\<close>
            have "closedin_on X TX D" by (by100 blast)
            \<comment> \<open>D closed in X, D \<subseteq> \<Union>C \<Rightarrow> D closed in \<Union>C (Theorem\_17\_2).\<close>
            have hX_top: "is_topology_on X TX"
              using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by5000 blast)
            from Theorem_17_2[OF hX_top hU_sub]
            have "\<And>S. closedin_on (\<Union>C) (subspace_topology X TX (\<Union>C)) S \<longleftrightarrow>
                (\<exists>F. closedin_on X TX F \<and> S = F \<inter> \<Union>C)" .
            hence "closedin_on (\<Union>C) (subspace_topology X TX (\<Union>C)) D"
              using \<open>closedin_on X TX D\<close> hD hUC_coverage by (by100 blast)
            thus "closedin_on (\<Union>?\<A>C) (subspace_topology X TX (\<Union>?\<A>C)) D"
              using hUC_coverage by (by100 simp)
          qed
          have "\<Union>?\<A>C = \<Union>C" using hUC_coverage by (by100 simp)
          from subgraph_union_of_arcs_is_graph[OF assms(1) h_arcs h_cover h_inter hUC_coh]
          show ?thesis using \<open>\<Union>?\<A>C = \<Union>C\<close> by (by100 simp)
        qed
      qed
      moreover note hU_subgraph
      \<comment> \<open>Coverage: \<Union>C = \<Union>{A \<in> \<A>X. A \<subseteq> \<Union>C} (each point is in arc of some chain element).\<close>
      moreover have "\<Union>C = \<Union>{A \<in> \<A>X. A \<subseteq> \<Union>C}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> \<Union>C"
        then obtain Ti where "Ti \<in> C" "x \<in> Ti" by (by100 blast)
        have "Ti \<in> \<A>" using \<open>Ti \<in> C\<close> hC unfolding chains_def by (by100 blast)
        hence "Ti = \<Union>{A \<in> \<A>X. A \<subseteq> Ti}" unfolding \<A>_def by (by100 blast)
        hence "x \<in> \<Union>{A \<in> \<A>X. A \<subseteq> Ti}" using \<open>x \<in> Ti\<close> by (by100 simp)
        then obtain A where "A \<in> \<A>X" "A \<subseteq> Ti" "x \<in> A" by (by100 blast)
        have "A \<subseteq> \<Union>C" using \<open>A \<subseteq> Ti\<close> \<open>Ti \<in> C\<close> by (by100 blast)
        thus "x \<in> \<Union>{A \<in> \<A>X. A \<subseteq> \<Union>C}" using \<open>A \<in> \<A>X\<close> \<open>x \<in> A\<close> by (by100 blast)
      next
        fix x assume "x \<in> \<Union>{A \<in> \<A>X. A \<subseteq> \<Union>C}"
        then obtain A where "A \<in> \<A>X" "A \<subseteq> \<Union>C" "x \<in> A" by (by100 blast)
        thus "x \<in> \<Union>C" using \<open>A \<subseteq> \<Union>C\<close> by (by100 blast)
      qed
      ultimately have "\<Union>C \<in> \<A>" using hU_sub hU_x0 unfolding \<A>_def by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
  qed
  from Zorn_Lemma2[OF hchain]
  obtain M where "M \<in> \<A>" and hmax: "\<forall>X'\<in>\<A>. M \<subseteq> X' \<longrightarrow> X' = M" by (by100 blast)
  from \<open>M \<in> \<A>\<close> have hM_tree: "top1_is_tree_on M (subspace_topology X TX M)"
      and hM_sub: "M \<subseteq> X" and hM_x0: "x0 \<in> M"
    unfolding \<A>_def by (by100 blast)+
  have hM_subgraph: "\<forall>A\<in>\<A>X. A \<subseteq> M \<or> A \<inter> M \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
    using \<open>M \<in> \<A>\<close> unfolding \<A>_def by (by100 blast)
  have hM_coverage: "M = \<Union>{A \<in> \<A>X. A \<subseteq> M}"
    using \<open>M \<in> \<A>\<close> unfolding \<A>_def by (by100 blast)
  have hM_maximal: "\<forall>T'. T' \<subseteq> X \<longrightarrow> M \<subseteq> T' \<longrightarrow>
      top1_is_tree_on T' (subspace_topology X TX T') \<longrightarrow>
      (\<forall>A\<in>\<A>X. A \<subseteq> T' \<or> A \<inter> T' \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)) \<longrightarrow>
      T' = \<Union>{A \<in> \<A>X. A \<subseteq> T'} \<longrightarrow>
      T' = M"
  proof (intro allI impI)
    fix T' assume "T' \<subseteq> X" "M \<subseteq> T'" "top1_is_tree_on T' (subspace_topology X TX T')"
        "\<forall>A\<in>\<A>X. A \<subseteq> T' \<or> A \<inter> T' \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
        "T' = \<Union>{A \<in> \<A>X. A \<subseteq> T'}"
    hence "T' \<in> \<A>" unfolding \<A>_def using hM_x0 by (by100 blast)
    thus "T' = M" using hmax \<open>M \<subseteq> T'\<close> by (by100 blast)
  qed
  show ?thesis
    apply (rule exI[of _ M])
    using hM_tree hM_sub hM_x0 hM_subgraph hM_coverage hM_maximal by (by100 blast)
qed

(** NOTE: graph_quotient_by_tree_wedge_of_circles was replaced by the SvK approach
    in Theorem_84_7. The quotient construction is no longer used.
    Commenting out to reduce sorry count. The statement is preserved for reference:

    lemma graph_quotient_by_tree_wedge_of_circles:
      "top1_is_graph_on X TX \<Longrightarrow> top1_connected_on X TX \<Longrightarrow>
       top1_is_tree_on T (subspace_topology X TX T) \<Longrightarrow> T \<subseteq> X \<Longrightarrow> x0 \<in> T \<Longrightarrow>
       \<exists>(n::nat) W TW q pw. top1_is_wedge_of_circles_on W TW {..<n} pw
         \<and> top1_quotient_map_on X TX W TW q \<and> (\<forall>x\<in>T. q x = pw)"
    [sorry: Quotient construction: collapse T, non-tree edges become circles.]
**)

text \<open>Helper: an arc deformation retracts to any of its endpoints.
  Proof: [0,1] deformation retracts to \{0\} via (s,t) \<mapsto> (1-t)\<cdot>s.
  Transport via the homeomorphism h: [0,1] \<rightarrow> A.\<close>
lemma maximal_tree_reaches_all_arcs:
  fixes X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes hgraph: "top1_is_graph_on X TX"
      and hconn: "top1_connected_on X TX"
      and "x0 \<in> X"
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
      and hT_x0: "x0 \<in> T"
      and hT_max: "\<forall>T'. T' \<subseteq> X \<longrightarrow> T \<subseteq> T' \<longrightarrow> top1_is_tree_on T' (subspace_topology X TX T') \<longrightarrow>
          (\<forall>A\<in>\<A>. A \<subseteq> T' \<or> A \<inter> T' \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)) \<longrightarrow>
          T' = \<Union>{A \<in> \<A>. A \<subseteq> T'} \<longrightarrow> T' = T"
      and hT_subgraph: "\<forall>A\<in>\<A>. A \<subseteq> T \<or> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
      and hT_coverage: "T = \<Union>{A \<in> \<A>. A \<subseteq> T}"
  shows "\<forall>v\<in>X. \<exists>A\<in>\<A>. v \<in> A \<and> (\<exists>w\<in>T. w \<in> A)"
proof -
  \<comment> \<open>Munkres Theorem 84.4: Every maximal tree in a connected graph contains all vertices.
     Proof outline:
     1. Define R = union of all arcs reachable from T via chains of overlapping arcs.
     2. R is clopen in X (coherent topology: R inter A is A or empty for each arc A).
     3. By connectivity of X and R non-empty (T \<subseteq> R), R = X.
     4. Every arc A in X meets T (each arc is reachable from T).
     5. Therefore every point v in X is in some arc A that meets T.\<close>
  \<comment> \<open>Use the arc cover \<A> from the assumptions (same as the one from the graph definition).\<close>
  \<comment> \<open>Step 1: Define R = T \<union> \<Union>{A \<in> \<A> | A \<inter> T \<noteq> {} or A is reachable from T via arcs}.
     For each arc A, either A is "reachable" from T (there's a chain of overlapping arcs
     from T to A) or not. If A is reachable, all of A is in R.\<close>
  \<comment> \<open>Key property of graph arcs: if x \<in> A and x is not an endpoint of A,
     then x is not in any other arc B \<noteq> A. This means: if any point of A is in R
     (reachable set), then all of A is in R.\<close>
  \<comment> \<open>Define: an arc A \<in> \<A> is T-reachable if there exist arcs B_1,...,B_n in \<A>
     with B_1 \<inter> T \<noteq> {}, B_i \<inter> B_{i+1} \<noteq> {} for all i, B_n = A.\<close>
  define Reach where "Reach = {A \<in> \<A>. \<exists>chain. chain \<noteq> []
      \<and> last chain = A
      \<and> (\<forall>i<length chain. chain!i \<in> \<A>)
      \<and> (hd chain) \<inter> T \<noteq> {}
      \<and> (\<forall>i<length chain - 1. (chain!i) \<inter> (chain!(Suc i)) \<noteq> {})}"
  define R where "R = T \<union> \<Union>Reach"
  \<comment> \<open>Step 2: For any arc A \<in> \<A>: either A \<subseteq> R or A \<inter> R = {}.
     Proof: If A \<inter> R has a point x, then x is either in T or in some reachable arc B.
     If x is in T, then A \<inter> T \<noteq> {}, so A is reachable (chain of length 1), so A \<subseteq> R.
     If x is in some reachable arc B with B \<noteq> A, then x \<in> A \<inter> B which is a set of endpoints.
     Being a shared endpoint, x is in both A and B, so A is reachable (extend B's chain by A).
     In either case: A \<subseteq> R.\<close>
  \<comment> \<open>Key helper: if A \<in> \<A> and A \<inter> T \<noteq> {} or A shares a point with a reachable arc, then A \<in> Reach.\<close>
  have hReach_T: "\<And>A. A \<in> \<A> \<Longrightarrow> A \<inter> T \<noteq> {} \<Longrightarrow> A \<in> Reach"
  proof -
    fix A assume "A \<in> \<A>" "A \<inter> T \<noteq> {}"
    \<comment> \<open>chain = [A]: non-empty, last = A, all in \<A>, hd \<inter> T \<noteq> {}, no consecutive pair condition.\<close>
    have "([A] :: 'a set list) \<noteq> []" by (by100 simp)
    moreover have "last [A] = A" by (by100 simp)
    moreover have "\<forall>i<length [A]. [A]!i \<in> \<A>" using \<open>A \<in> \<A>\<close> by (by100 simp)
    moreover have "hd [A] \<inter> T \<noteq> {}" using \<open>A \<inter> T \<noteq> {}\<close> by (by100 simp)
    moreover have "\<forall>i<length [A] - 1. ([A]!i) \<inter> ([A]!(Suc i)) \<noteq> {}" by (by100 simp)
    ultimately have "\<exists>chain. chain \<noteq> [] \<and> last chain = A
        \<and> (\<forall>i<length chain. chain!i \<in> \<A>)
        \<and> hd chain \<inter> T \<noteq> {}
        \<and> (\<forall>i<length chain - 1. (chain!i) \<inter> (chain!(Suc i)) \<noteq> {})"
      by (rule_tac x="[A]" in exI, by100 blast)
    thus "A \<in> Reach" unfolding Reach_def using \<open>A \<in> \<A>\<close> by (by100 blast)
  qed
  have hReach_extend: "\<And>A B. A \<in> \<A> \<Longrightarrow> B \<in> Reach \<Longrightarrow> A \<inter> B \<noteq> {} \<Longrightarrow> A \<in> Reach"
  proof -
    fix A B assume hA: "A \<in> \<A>" and hB: "B \<in> Reach" and hAB: "A \<inter> B \<noteq> {}"
    from hB obtain chain where hch: "chain \<noteq> []" "last chain = B"
        "\<forall>i<length chain. chain!i \<in> \<A>"
        "hd chain \<inter> T \<noteq> {}"
        "\<forall>i<length chain - 1. (chain!i) \<inter> (chain!(Suc i)) \<noteq> {}"
      unfolding Reach_def by (by100 blast)
    \<comment> \<open>Extend chain by A: chain' = chain @ [A].\<close>
    let ?chain' = "chain @ [A]"
    have "?chain' \<noteq> []" by (by100 simp)
    moreover have "last ?chain' = A" by (by100 simp)
    moreover have "\<forall>i<length ?chain'. ?chain'!i \<in> \<A>"
    proof (intro allI impI)
      fix i assume "i < length ?chain'"
      show "?chain' ! i \<in> \<A>"
      proof (cases "i < length chain")
        case True thus ?thesis using hch(3) by (simp add: nth_append)
      next
        case False
        hence "i = length chain" using \<open>i < length ?chain'\<close> by (by100 simp)
        thus ?thesis using hA by (simp add: nth_append)
      qed
    qed
    moreover have "hd ?chain' \<inter> T \<noteq> {}" using hch(1) hch(4) by (by100 simp)
    moreover have "\<forall>i<length ?chain' - 1. (?chain'!i) \<inter> (?chain'!(Suc i)) \<noteq> {}"
    proof (intro allI impI)
      fix i assume hi: "i < length ?chain' - 1"
      show "?chain' ! i \<inter> ?chain' ! Suc i \<noteq> {}"
      proof (cases "Suc i < length chain")
        case True
        hence "i < length chain - 1" by (by100 simp)
        hence "(chain!i) \<inter> (chain!(Suc i)) \<noteq> {}" using hch(5) by (by100 blast)
        moreover have "?chain' ! i = chain ! i" using True by (simp add: nth_append)
        moreover have "?chain' ! Suc i = chain ! Suc i" using True by (simp add: nth_append)
        ultimately show ?thesis by (by100 simp)
      next
        case False
        hence hSi: "Suc i = length chain" using hi by (by100 simp)
        hence "i = length chain - 1" by (by100 simp)
        have "i < length chain" using hSi by (by100 simp)
        hence "?chain' ! i = chain ! i" by (simp add: nth_append)
        also have "\<dots> = chain ! (length chain - 1)" using \<open>i = length chain - 1\<close> by (by100 simp)
        also have "\<dots> = last chain"
          using last_conv_nth[OF hch(1)] \<open>i = length chain - 1\<close> by (by100 simp)
        also have "\<dots> = B" using hch(2) by (by100 simp)
        finally have "?chain' ! i = B" .
        moreover have "?chain' ! Suc i = A" using hSi by (simp add: nth_append)
        ultimately show ?thesis using hAB by (by100 blast)
      qed
    qed
    ultimately have "\<exists>chain'. chain' \<noteq> [] \<and> last chain' = A
        \<and> (\<forall>i<length chain'. chain'!i \<in> \<A>)
        \<and> hd chain' \<inter> T \<noteq> {}
        \<and> (\<forall>i<length chain' - 1. (chain'!i) \<inter> (chain'!(Suc i)) \<noteq> {})"
      by (rule_tac x="?chain'" in exI) (by5000 auto)
    thus "A \<in> Reach" unfolding Reach_def using hA by (by100 blast)
  qed
  have hReach_sub: "\<And>A. A \<in> Reach \<Longrightarrow> A \<subseteq> R"
    unfolding R_def Reach_def by (by100 blast)
  have hR_arc_all_or_nothing: "\<forall>A\<in>\<A>. A \<subseteq> R \<or> A \<inter> R = {}"
  proof (intro ballI, rule disjCI)
    fix A assume hA: "A \<in> \<A>" and hne: "A \<inter> R \<noteq> {}"
    \<comment> \<open>There exists x \<in> A \<inter> R.\<close>
    obtain x where "x \<in> A" "x \<in> R" using hne by (by100 blast)
    from \<open>x \<in> R\<close> have "x \<in> T \<or> x \<in> \<Union>Reach" unfolding R_def by (by100 blast)
    thus "A \<subseteq> R"
    proof
      assume "x \<in> T"
      hence "A \<inter> T \<noteq> {}" using \<open>x \<in> A\<close> by (by100 blast)
      from hReach_T[OF hA this] have "A \<in> Reach" .
      thus ?thesis using hReach_sub by (by100 blast)
    next
      assume "x \<in> \<Union>Reach"
      then obtain B where "B \<in> Reach" "x \<in> B" by (by100 blast)
      hence "A \<inter> B \<noteq> {}" using \<open>x \<in> A\<close> by (by100 blast)
      from hReach_extend[OF hA \<open>B \<in> Reach\<close> this] have "A \<in> Reach" .
      thus ?thesis using hReach_sub by (by100 blast)
    qed
  qed
  \<comment> \<open>Step 3: R is closed (coherent topology: R \<inter> A = A or \<emptyset>, both closed in A).\<close>
  have hR_sub: "R \<subseteq> X"
    unfolding R_def using hT_sub h\<A> Reach_def by (by5000 auto)
  have hTX_top: "is_topology_on X TX"
    using hgraph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
  have hA_top: "\<And>A. A \<in> \<A> \<Longrightarrow> is_topology_on A (subspace_topology X TX A)"
  proof -
    fix A assume "A \<in> \<A>"
    have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
    thus "is_topology_on A (subspace_topology X TX A)"
      by (rule subspace_topology_is_topology_on[OF hTX_top])
  qed
  have hR_closed: "closedin_on X TX R"
  proof -
    have "\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> R)"
    proof (intro ballI)
      fix A assume hA: "A \<in> \<A>"
      from hR_arc_all_or_nothing[rule_format, OF hA]
      show "closedin_on A (subspace_topology X TX A) (A \<inter> R)"
      proof
        assume "A \<subseteq> R" hence "A \<inter> R = A" by (by100 blast)
        thus ?thesis using conjunct1[OF conjunct2[OF Theorem_17_1[OF hA_top[OF hA]]]] by (by100 simp)
      next
        assume "A \<inter> R = {}"
        thus ?thesis using conjunct1[OF Theorem_17_1[OF hA_top[OF hA]]] by (by100 simp)
      qed
    qed
    thus ?thesis using h\<A>_coh hR_sub by (by100 blast)
  qed
  \<comment> \<open>Step 4: X - R is also closed (same argument: (X-R) \<inter> A = A or \<emptyset>).\<close>
  have hXR_closed: "closedin_on X TX (X - R)"
  proof -
    have "\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> (X - R))"
    proof (intro ballI)
      fix A assume "A \<in> \<A>"
      from hR_arc_all_or_nothing[rule_format, OF \<open>A \<in> \<A>\<close>]
      show "closedin_on A (subspace_topology X TX A) (A \<inter> (X - R))"
      proof
        assume "A \<subseteq> R" hence "A \<inter> (X - R) = {}" by (by100 blast)
        thus ?thesis using conjunct1[OF Theorem_17_1[OF hA_top[OF \<open>A \<in> \<A>\<close>]]] by (by100 simp)
      next
        assume "A \<inter> R = {}"
        have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
        hence "A \<inter> (X - R) = A" using \<open>A \<inter> R = {}\<close> by (by100 blast)
        thus ?thesis using conjunct1[OF conjunct2[OF Theorem_17_1[OF hA_top[OF \<open>A \<in> \<A>\<close>]]]]
          by (by100 simp)
      qed
    qed
    have "X - R \<subseteq> X" by (by100 blast)
    from h\<A>_coh have "closedin_on X TX (X - R)"
      using \<open>X - R \<subseteq> X\<close> \<open>\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> (X - R))\<close>
      by (by100 blast)
    thus ?thesis .
  qed
  \<comment> \<open>Step 5: R is non-empty (T \<subseteq> R and T contains x0).\<close>
  have hR_ne: "R \<noteq> {}" unfolding R_def using hT_x0 by (by100 blast)
  \<comment> \<open>Step 6: X is connected, R is clopen (closed and X-R is closed), R non-empty \<Rightarrow> R = X.\<close>
  have hR_eq_X: "R = X"
  proof (rule ccontr)
    assume "R \<noteq> X"
    hence hXR_ne: "X - R \<noteq> {}" using hR_sub by (by100 blast)
    \<comment> \<open>R is open: X - R is closed, so X - (X-R) = R is open.\<close>
    have hR_open: "R \<in> TX"
    proof -
      from hXR_closed have "X - (X - R) \<in> TX" unfolding closedin_on_def by (by100 blast)
      moreover have "X - (X - R) = R" using hR_sub by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>X - R is open: R is closed, so X - R is open.\<close>
    have hXR_open: "X - R \<in> TX"
      using hR_closed unfolding closedin_on_def by (by100 blast)
    \<comment> \<open>X = R \<union> (X-R), both open, disjoint, non-empty. Contradicts connectivity.\<close>
    have "R \<inter> (X - R) = {}" by (by100 blast)
    have "R \<union> (X - R) = X" using hR_sub by (by100 blast)
    from hconn have "\<not>(\<exists>U V. U \<in> TX \<and> V \<in> TX \<and> U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {} \<and> U \<union> V = X)"
      unfolding top1_connected_on_def by (by100 blast)
    thus False using hR_open hXR_open hR_ne hXR_ne \<open>R \<inter> (X - R) = {}\<close> \<open>R \<union> (X - R) = X\<close>
      by (by100 blast)
  qed
  \<comment> \<open>Step 7: Since R = X and every arc in \<A> is either in R or disjoint from R,
     every arc is in R (since \<A> covers X = R). So every arc meets T.\<close>
  show ?thesis
  proof (intro ballI)
    fix v assume "v \<in> X"
    show "\<exists>A\<in>\<A>. v \<in> A \<and> (\<exists>w\<in>T. w \<in> A)"
    proof (cases "v \<in> T")
      case True
      \<comment> \<open>v \<in> T \<subseteq> X = \<Union>\<A>, so v \<in> A for some A \<in> \<A>. And v \<in> T \<inter> A.\<close>
      then obtain A where "A \<in> \<A>" "v \<in> A" using \<open>v \<in> X\<close> assms(5) by (by100 blast)
      thus ?thesis using True by (by100 blast)
    next
      case False
      \<comment> \<open>v \<notin> T: v \<in> \<Union>Reach (from R = X).
         Need: an arc containing v that meets T.
         This requires the "all vertices in T" argument (Lemma 84.2 + Theorem 84.4).\<close>
      have "v \<in> \<Union>Reach" using \<open>v \<in> X\<close> hR_eq_X False unfolding R_def by (by100 blast)
      then obtain B where "B \<in> Reach" "v \<in> B" by (by100 blast)
      have "B \<in> \<A>" using \<open>B \<in> Reach\<close> unfolding Reach_def by (by100 blast)
      \<comment> \<open>B is reachable, so there's a chain from T to B.
         The first arc B1 in the chain meets T. Use v and B1 together.\<close>
      from \<open>B \<in> Reach\<close> obtain chain where hch: "chain \<noteq> []" "last chain = B"
          "\<forall>i<length chain. chain!i \<in> \<A>"
          "hd chain \<inter> T \<noteq> {}"
          "\<forall>i<length chain - 1. (chain!i) \<inter> (chain!(Suc i)) \<noteq> {}"
        unfolding Reach_def by (by100 blast)
      \<comment> \<open>hd chain meets T and is an arc in \<A>.\<close>
      have "hd chain \<in> \<A>"
      proof -
        have "0 < length chain" using hch(1) by (by100 simp)
        hence "chain ! 0 \<in> \<A>" using hch(3) by (by100 blast)
        moreover have "hd chain = chain ! 0" using hch(1) hd_conv_nth by (by5000 simp)
        ultimately show ?thesis by (by100 simp)
      qed
      \<comment> \<open>Every reachable arc meets T (Munkres Thm 84.4: maximal tree has all vertices).
         Proof: if B \<inter> T = {}, extract from chain the first arc A_{j-1} that
         meets T but has an endpoint p \<in> A_j where A_j \<inter> T = {}.
         Then T \<union> A_{j-1} is connected and A_{j-1} \<inter> T is a single vertex
         (Lemma 84.2). So T \<union> A_{j-1} is a larger tree. Contradicts maximality.\<close>
      have hB_meets_T: "B \<inter> T \<noteq> {}"
      proof (rule ccontr)
        assume "\<not> B \<inter> T \<noteq> {}"
        hence hBT: "B \<inter> T = {}" by (by100 blast)
        \<comment> \<open>Find j = first index with chain!j \<inter> T = {}.\<close>
        have "\<exists>j. j < length chain \<and> chain!j \<inter> T = {} \<and> (\<forall>i<j. chain!i \<inter> T \<noteq> {})"
        proof -
          \<comment> \<open>B = last chain and B \<inter> T = {}. So chain!(length chain - 1) \<inter> T = {}.\<close>
          have hlen: "length chain > 0" using hch(1) by (by100 simp)
          have "chain!(length chain - 1) = last chain"
            using last_conv_nth[OF hch(1)] by (by100 simp)
          hence "chain!(length chain - 1) = B" using hch(2) by (by100 simp)
          hence "chain!(length chain - 1) \<inter> T = {}" using hBT by (by100 simp)
          \<comment> \<open>Use Least (well-ordering): find the smallest j with chain!j \<inter> T = {}.\<close>
          let ?P = "\<lambda>j. j < length chain \<and> chain!j \<inter> T = {}"
          have "?P (length chain - 1)" using \<open>chain!(length chain - 1) \<inter> T = {}\<close> hlen by (by100 simp)
          hence "\<exists>j. ?P j" by (by100 blast)
          from LeastI_ex[OF this] have hL: "?P (Least ?P)" .
          have hL_min: "\<forall>i<Least ?P. \<not> ?P i" using not_less_Least by (by100 blast)
          hence "\<forall>i<Least ?P. i < length chain \<longrightarrow> chain!i \<inter> T \<noteq> {}" by (by100 blast)
          hence "\<forall>i<Least ?P. chain!i \<inter> T \<noteq> {}"
          proof (intro allI impI)
            fix i assume "i < Least ?P"
            hence "i < length chain" using hL by (by100 linarith)
            with \<open>\<forall>i<Least ?P. i < length chain \<longrightarrow> chain!i \<inter> T \<noteq> {}\<close> \<open>i < Least ?P\<close>
            show "chain!i \<inter> T \<noteq> {}" by (by100 blast)
          qed
          with hL show ?thesis by (by100 blast)
        qed
        then obtain j where hj: "j < length chain" "chain!j \<inter> T = {}" "\<forall>i<j. chain!i \<inter> T \<noteq> {}"
          by (by100 blast)
        \<comment> \<open>j \<ge> 1 (since hd chain \<inter> T \<noteq> {}).\<close>
        have "j \<ge> 1"
        proof (rule ccontr)
          assume "\<not> j \<ge> 1" hence "j = 0" by (by100 simp)
          hence "chain!0 \<inter> T = {}" using hj(2) by (by100 simp)
          moreover have "hd chain = chain!0" using hch(1) hd_conv_nth by (by5000 simp)
          ultimately show False using hch(4) by (by100 simp)
        qed
        hence "j - 1 < j" by (by100 simp)
        have hjm1_T: "chain!(j-1) \<inter> T \<noteq> {}" using hj(3) \<open>j - 1 < j\<close> by (by100 blast)
        have hjm1_A: "chain!(j-1) \<in> \<A>" using hch(3) \<open>j \<ge> 1\<close> hj(1) by (by100 auto)
        have hj_A: "chain!j \<in> \<A>" using hch(3) hj(1) by (by100 blast)
        \<comment> \<open>A_{j-1} and A_j overlap. The shared point p is an endpoint of both.\<close>
        have "j - 1 < length chain - 1" using hj(1) \<open>j \<ge> 1\<close> by (by100 simp)
        have "Suc (j - 1) = j" using \<open>j \<ge> 1\<close> by (by100 simp)
        have "chain!(j-1) \<inter> chain!(Suc (j-1)) \<noteq> {}"
          using hch(5) \<open>j - 1 < length chain - 1\<close> by (by100 blast)
        hence "chain!(j-1) \<inter> chain!j \<noteq> {}" using \<open>Suc (j - 1) = j\<close> by (by100 simp)
        then obtain p where "p \<in> chain!(j-1) \<inter> chain!j" by (by100 blast)
        \<comment> \<open>p \<notin> T (since p \<in> chain!j and chain!j \<inter> T = {}).\<close>
        have "p \<notin> T" using \<open>p \<in> chain!(j-1) \<inter> chain!j\<close> hj(2) by (by100 blast)
        \<comment> \<open>By subgraph assumption: A_{j-1} is either ⊆ T or meets T only at endpoints.\<close>
        from hT_subgraph[rule_format, OF hjm1_A]
        have "chain!(j-1) \<subseteq> T \<or> chain!(j-1) \<inter> T \<subseteq> top1_arc_endpoints_on (chain!(j-1)) (subspace_topology X TX (chain!(j-1)))"
          .
        hence "chain!(j-1) \<inter> T \<subseteq> top1_arc_endpoints_on (chain!(j-1)) (subspace_topology X TX (chain!(j-1)))"
        proof
          assume "chain!(j-1) \<subseteq> T"
          \<comment> \<open>Then p \<in> chain!(j-1) \<subseteq> T, contradicting p \<notin> T.\<close>
          hence "p \<in> T" using \<open>p \<in> chain!(j-1) \<inter> chain!j\<close> by (by100 blast)
          thus ?thesis using \<open>p \<notin> T\<close> by (by100 blast)
        next
          assume "chain!(j-1) \<inter> T \<subseteq> top1_arc_endpoints_on (chain!(j-1)) (subspace_topology X TX (chain!(j-1)))"
          thus ?thesis .
        qed
        \<comment> \<open>A_{j-1} \<inter> T \<subseteq> endpoints(A_{j-1}). p is an endpoint but p \<notin> T.
           So A_{j-1} \<inter> T \<subseteq> {other endpoint}. Since A_{j-1} \<inter> T \<noteq> {}, card = 1.\<close>
        have hcard1: "card (chain!(j-1) \<inter> T) = 1"
        proof -
          \<comment> \<open>p is an endpoint of A_{j-1} (from graph intersection A_{j-1} \<inter> A_j \<subseteq> endpoints).\<close>
          have hp_ep: "p \<in> top1_arc_endpoints_on (chain!(j-1)) (subspace_topology X TX (chain!(j-1)))"
          proof -
            from h\<A>_inter[rule_format, OF hjm1_A hj_A]
            have "chain!(j-1) \<noteq> chain!j \<longrightarrow>
                chain!(j-1) \<inter> chain!j \<subseteq> top1_arc_endpoints_on (chain!(j-1)) (subspace_topology X TX (chain!(j-1)))"
              by (by100 blast)
            moreover have "chain!(j-1) \<noteq> chain!j"
              using hjm1_T hj(2) by (by100 blast)
            ultimately show ?thesis using \<open>p \<in> chain!(j-1) \<inter> chain!j\<close> by (by100 blast)
          qed
          \<comment> \<open>endpoints has \<le> 2 elements. p \<in> endpoints but p \<notin> T.
             A_{j-1} \<inter> T \<subseteq> endpoints - \{p\}. Card(endpoints - \{p\}) \<le> 1.
             And A_{j-1} \<inter> T \<noteq> {}. So card = 1.\<close>
          let ?ep = "top1_arc_endpoints_on (chain!(j-1)) (subspace_topology X TX (chain!(j-1)))"
          have "chain!(j-1) \<inter> T \<subseteq> ?ep - {p}"
            using \<open>chain!(j-1) \<inter> T \<subseteq> ?ep\<close> \<open>p \<notin> T\<close> by (by100 blast)
          have "finite ?ep \<and> card ?ep \<le> 2"
          proof -
            have "top1_is_arc_on (chain!(j-1)) (subspace_topology X TX (chain!(j-1)))"
              using h\<A> hjm1_A by (by100 blast)
            then obtain h' where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                (chain!(j-1)) (subspace_topology X TX (chain!(j-1))) h'"
              unfolding top1_is_arc_on_def by (by100 blast)
            have hstrict: "is_topology_on_strict X TX"
              using hgraph unfolding top1_is_graph_on_def by (by100 blast)
            have hhaus: "is_hausdorff_on X TX"
              using hgraph unfolding top1_is_graph_on_def by (by100 blast)
            have hsub: "chain!(j-1) \<subseteq> X" using h\<A> hjm1_A by (by100 blast)
            from arc_endpoints_are_boundary[OF hstrict hhaus hsub
                \<open>top1_is_arc_on (chain!(j-1)) (subspace_topology X TX (chain!(j-1)))\<close>
                \<open>top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                    (chain!(j-1)) (subspace_topology X TX (chain!(j-1))) h'\<close>]
            have "?ep = {h' 0, h' 1}" .
            have "finite {h' 0, h' 1}" by (by100 simp)
            have "card {h' 0, h' 1} \<le> 2"
              by (cases "h' 0 = h' 1", by100 simp, by100 simp)
            thus ?thesis using \<open>?ep = {h' 0, h' 1}\<close> by (by100 simp)
          qed
          hence "card (?ep - {p}) \<le> 1" using hp_ep by (by100 auto)
          have hep_fin: "finite (?ep - {p})" using \<open>finite ?ep \<and> card ?ep \<le> 2\<close> by (by100 simp)
          from card_mono[OF hep_fin \<open>chain!(j-1) \<inter> T \<subseteq> ?ep - {p}\<close>]
          have "card (chain!(j-1) \<inter> T) \<le> card (?ep - {p})" .
          hence "card (chain!(j-1) \<inter> T) \<le> 1"
            using \<open>card (?ep - {p}) \<le> 1\<close> by (by100 linarith)
          moreover have "chain!(j-1) \<inter> T \<noteq> {}" using hjm1_T .
          have "finite (chain!(j-1) \<inter> T)"
            using finite_subset[OF \<open>chain!(j-1) \<inter> T \<subseteq> ?ep - {p}\<close> \<open>finite (?ep - {p})\<close>] .
          hence "0 < card (chain!(j-1) \<inter> T)"
            using \<open>chain!(j-1) \<inter> T \<noteq> {}\<close> by (by100 auto)
          hence "card (chain!(j-1) \<inter> T) \<ge> 1" by (by100 linarith)
          ultimately show ?thesis by (by100 simp)
        qed
        \<comment> \<open>Apply Lemma 84.2: T \<union> A_{j-1} is a tree.\<close>
        \<comment> \<open>T closed in X: by coherent topology, since T is a subgraph.\<close>
        have hT_closed: "closedin_on X TX T"
        proof -
          have "\<forall>B\<in>\<A>. closedin_on B (subspace_topology X TX B) (B \<inter> T)"
          proof (intro ballI)
            fix B assume "B \<in> \<A>"
            from hT_subgraph[rule_format, OF this]
            show "closedin_on B (subspace_topology X TX B) (B \<inter> T)"
            proof
              assume "B \<subseteq> T" hence "B \<inter> T = B" by (by100 blast)
              moreover have "closedin_on B (subspace_topology X TX B) B"
              proof -
                have "is_topology_on X TX"
                  using hgraph unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
                have "B \<subseteq> X" using h\<A> \<open>B \<in> \<A>\<close> by (by100 blast)
                from closedin_carrier[OF subspace_topology_is_topology_on[OF \<open>is_topology_on X TX\<close> \<open>B \<subseteq> X\<close>]]
                show ?thesis .
              qed
              ultimately show ?thesis by (by100 simp)
            next
              assume hBT_ep: "B \<inter> T \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)"
              \<comment> \<open>B \<inter> T is finite (subset of endpoints \<le> 2) and in Hausdorff B.\<close>
              have hB_sub: "B \<subseteq> X" using h\<A> \<open>B \<in> \<A>\<close> by (by100 blast)
              have hBT_fin: "finite (B \<inter> T)"
              proof -
                have "finite (top1_arc_endpoints_on B (subspace_topology X TX B))
                    \<and> card (top1_arc_endpoints_on B (subspace_topology X TX B)) \<le> 2"
                proof -
                  have "top1_is_arc_on B (subspace_topology X TX B)"
                    using h\<A> \<open>B \<in> \<A>\<close> by (by100 blast)
                  then obtain hB where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                      B (subspace_topology X TX B) hB"
                    unfolding top1_is_arc_on_def by (by100 blast)
                  have hstr: "is_topology_on_strict X TX"
                    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                  have hh: "is_hausdorff_on X TX"
                    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                  from arc_endpoints_are_boundary[OF hstr hh hB_sub
                      \<open>top1_is_arc_on B (subspace_topology X TX B)\<close>
                      \<open>top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                          B (subspace_topology X TX B) hB\<close>]
                  have "top1_arc_endpoints_on B (subspace_topology X TX B) = {hB 0, hB 1}" .
                  thus ?thesis by (cases "hB 0 = hB 1", by100 simp, by100 simp)
                qed
                thus ?thesis using finite_subset[OF hBT_ep] by (by100 blast)
              qed
              \<comment> \<open>Hausdorff \<Rightarrow> T1 \<Rightarrow> singletons closed \<Rightarrow> finite set closed.\<close>
              have hX_haus: "is_hausdorff_on X TX"
                using hgraph unfolding top1_is_graph_on_def by (by100 blast)
              have hB_haus: "is_hausdorff_on B (subspace_topology X TX B)"
                using conjunct2[OF conjunct2[OF Theorem_17_11]] hX_haus hB_sub by (by100 blast)
              have hB_T1: "top1_T1_on B (subspace_topology X TX B)"
                by (rule hausdorff_imp_T1_on[OF hB_haus])
              have hB_top: "is_topology_on B (subspace_topology X TX B)"
                using hB_haus unfolding is_hausdorff_on_def by (by100 blast)
              have "B \<inter> T = \<Union>((\<lambda>x. {x}) ` (B \<inter> T))" by (by100 blast)
              moreover have "finite ((\<lambda>x. {x}) ` (B \<inter> T))" using hBT_fin by (by100 simp)
              moreover have "\<forall>U\<in>((\<lambda>x. {x}) ` (B \<inter> T)). closedin_on B (subspace_topology X TX B) U"
              proof (intro ballI)
                fix U assume "U \<in> (\<lambda>x. {x}) ` (B \<inter> T)"
                then obtain y where "y \<in> B" "U = {y}" by (by100 blast)
                thus "closedin_on B (subspace_topology X TX B) U"
                  using hB_T1 unfolding top1_T1_on_def by (by100 blast)
              qed
              from closedin_Union_finite[OF hB_top
                  \<open>finite ((\<lambda>x. {x}) ` (B \<inter> T))\<close> this]
              have "closedin_on B (subspace_topology X TX B) (\<Union>((\<lambda>x. {x}) ` (B \<inter> T)))" .
              thus ?thesis using \<open>B \<inter> T = \<Union>((\<lambda>x. {x}) ` (B \<inter> T))\<close> by (by100 simp)
            qed
          qed
          thus ?thesis using h\<A>_coh hT_sub by (by100 blast)
        qed
        \<comment> \<open>T \<union> A_{j-1} is a graph: arcs = {A \<in> \<A> | A \<subseteq> T \<union> chain!(j-1)}.
           Coherent topology from X's coherent topology: for A \<notin> this set,
           A \<inter> (T \<union> chain!(j-1)) \<subseteq> endpoints (finite, hence closed). By h\<A>\_coh:
           C closed in X \<Rightarrow> C closed in T \<union> chain!(j-1).\<close>
        have hjm1_sub_X: "chain!(j-1) \<subseteq> X" using h\<A> hjm1_A by (by100 blast)
        have hTUA_sub: "T \<union> chain!(j-1) \<subseteq> X" using hT_sub hjm1_sub_X by (by100 blast)
        have hTUA_graph: "top1_is_graph_on (T \<union> chain!(j-1)) (subspace_topology X TX (T \<union> chain!(j-1)))"
        proof -
          let ?S = "T \<union> chain!(j-1)"
          let ?TS = "subspace_topology X TX ?S"
          let ?\<A>' = "{A \<in> \<A>. A \<subseteq> ?S}"
          have hX_strict: "is_topology_on_strict X TX"
            using hgraph unfolding top1_is_graph_on_def by (by100 blast)
          have hS_strict: "is_topology_on_strict ?S ?TS"
            by (rule subspace_topology_is_strict[OF hX_strict hTUA_sub])
          have hS_haus: "is_hausdorff_on ?S ?TS"
          proof -
            have "is_hausdorff_on X TX" using hgraph unfolding top1_is_graph_on_def by (by100 blast)
            from conjunct2[OF conjunct2[OF Theorem_17_11]] hTUA_sub this show ?thesis by (by100 blast)
          qed
          \<comment> \<open>Arcs: each A \<in> \<A>' is an arc of ?S.\<close>
          have h\<A>'_arcs: "\<forall>A\<in>?\<A>'. A \<subseteq> ?S \<and> top1_is_arc_on A (subspace_topology ?S ?TS A)"
          proof (intro ballI conjI)
            fix A assume hA: "A \<in> ?\<A>'"
            show "A \<subseteq> ?S" using hA by (by100 blast)
            have "A \<subseteq> X" using h\<A> hA by (by100 blast)
            have hA_arc: "top1_is_arc_on A (subspace_topology X TX A)" using h\<A> hA by (by100 blast)
            have "subspace_topology ?S ?TS A = subspace_topology X TX A"
              by (rule subspace_topology_trans[OF \<open>A \<subseteq> ?S\<close>])
            thus "top1_is_arc_on A (subspace_topology ?S ?TS A)" using hA_arc by (by100 simp)
          qed
          \<comment> \<open>Cover: \<Union>\<A>' = ?S.\<close>
          have h\<A>'_cover: "\<Union>?\<A>' = ?S"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> \<Union>?\<A>'"
            then obtain A where "A \<in> ?\<A>'" "x \<in> A" by (by100 blast)
            thus "x \<in> ?S" using \<open>A \<in> ?\<A>'\<close> by (by100 blast)
          next
            fix x assume "x \<in> ?S"
            hence "x \<in> X" using hTUA_sub by (by100 blast)
            hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
            then obtain A where hA_A: "A \<in> \<A>" "x \<in> A" by (by100 blast)
            show "x \<in> \<Union>?\<A>'"
            proof (cases "A \<subseteq> ?S")
              case True thus ?thesis using hA_A by (by100 blast)
            next
              case False
              \<comment> \<open>A \<nsubseteq> ?S. By hT\_subgraph: A \<inter> T \<subseteq> endpoints(A) (since A \<nsubseteq> T).
                 If A = chain!(j-1): but then A \<subseteq> ?S, contradiction.
                 If A \<noteq> chain!(j-1): A \<inter> chain!(j-1) \<subseteq> endpoints from h\<A>\_inter.
                 So A \<inter> ?S \<subseteq> endpoints (finite). x \<in> A \<inter> ?S so x is an endpoint.\<close>
              have "A \<noteq> chain!(j-1)" using False by (by100 blast)
              have hAT: "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
              proof -
                from hT_subgraph[rule_format, OF hA_A(1)]
                show ?thesis
                proof
                  assume "A \<subseteq> T" thus ?thesis using False by (by100 blast)
                next
                  assume "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                  thus ?thesis .
                qed
              qed
              have hAC: "A \<inter> chain!(j-1) \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                using h\<A>_inter[rule_format, OF hA_A(1) hjm1_A \<open>A \<noteq> chain!(j-1)\<close>] by (by100 blast)
              have "x \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                using \<open>x \<in> ?S\<close> hA_A(2) hAT hAC by (by100 blast)
              \<comment> \<open>x is an endpoint of A. x is also in T or chain!(j-1).
                 If x \<in> T: x is connected in T to other points. There exists B \<in> \<A> with B \<subseteq> T
                 and x \<in> B (since T is connected and contains x + paths go through arcs).
                 If x \<in> chain!(j-1): then chain!(j-1) \<in> \<A>' and x \<in> chain!(j-1).\<close>
              show ?thesis
              proof (cases "x \<in> chain!(j-1)")
                case True
                have "chain!(j-1) \<in> ?\<A>'" using hjm1_A by (by100 blast)
                thus ?thesis using True by (by100 blast)
              next
                case False
                hence "x \<in> T" using \<open>x \<in> ?S\<close> by (by100 blast)
                \<comment> \<open>x \<in> T. By hT\_coverage: T = \<Union>{A \<in> \<A>. A \<subseteq> T}.
                   So x is in some arc B \<subseteq> T \<subseteq> T \<union> chain!(j-1).\<close>
                have "x \<in> \<Union>{A \<in> \<A>. A \<subseteq> T}" using \<open>x \<in> T\<close> hT_coverage by (by100 simp)
                then obtain B where "B \<in> \<A>" "B \<subseteq> T" "x \<in> B" by (by100 blast)
                have "B \<subseteq> ?S" using \<open>B \<subseteq> T\<close> by (by100 blast)
                hence "B \<in> ?\<A>'" using \<open>B \<in> \<A>\<close> by (by100 blast)
                show ?thesis using \<open>B \<in> ?\<A>'\<close> \<open>x \<in> B\<close> by (by100 blast)
              qed
            qed
          qed
          \<comment> \<open>Intersection: from h\<A>\_inter.\<close>
          have h\<A>'_inter: "\<forall>A\<in>?\<A>'. \<forall>B\<in>?\<A>'. A \<noteq> B \<longrightarrow>
               A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?S ?TS A)
             \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?S ?TS B)
             \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
          proof (intro ballI impI)
            fix A B assume hA: "A \<in> ?\<A>'" and hB: "B \<in> ?\<A>'" and hne: "A \<noteq> B"
            have "A \<in> \<A>" "B \<in> \<A>" using hA hB by (by100 blast)+
            from h\<A>_inter[rule_format, OF this hne]
            have hinter: "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
               \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
               \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" by (by100 blast)
            have "subspace_topology ?S ?TS A = subspace_topology X TX A"
              by (rule subspace_topology_trans) (use hA in \<open>by100 blast\<close>)
            moreover have "subspace_topology ?S ?TS B = subspace_topology X TX B"
              by (rule subspace_topology_trans) (use hB in \<open>by100 blast\<close>)
            ultimately show "A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology ?S ?TS A)
               \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology ?S ?TS B)
               \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2" using hinter by (by100 simp)
          qed
          \<comment> \<open>Coherent topology: backward direction is the key.\<close>
          have h\<A>'_coh: "\<forall>D. D \<subseteq> ?S \<longrightarrow>
               (closedin_on ?S ?TS D \<longleftrightarrow>
                (\<forall>A\<in>?\<A>'. closedin_on A (subspace_topology ?S ?TS A) (A \<inter> D)))"
          proof (intro allI impI)
            fix D assume hD_sub: "D \<subseteq> ?S"
            show "closedin_on ?S ?TS D \<longleftrightarrow>
                (\<forall>A\<in>?\<A>'. closedin_on A (subspace_topology ?S ?TS A) (A \<inter> D))"
            proof (rule iffI)
              \<comment> \<open>Forward: D closed in ?S \<Rightarrow> per-arc closed.\<close>
              assume hD_cl: "closedin_on ?S ?TS D"
              show "\<forall>A\<in>?\<A>'. closedin_on A (subspace_topology ?S ?TS A) (A \<inter> D)"
              proof (intro ballI)
                fix A' assume "A' \<in> ?\<A>'"
                have "A' \<subseteq> ?S" using \<open>A' \<in> ?\<A>'\<close> by (by100 blast)
                have hTS_top: "is_topology_on ?S ?TS"
                  using hS_strict unfolding is_topology_on_strict_def by (by100 blast)
                have "subspace_topology ?S ?TS A' = subspace_topology X TX A'"
                  by (rule subspace_topology_trans) (use \<open>A' \<subseteq> ?S\<close> in \<open>by100 blast\<close>)
                from Theorem_17_2[OF hTS_top \<open>A' \<subseteq> ?S\<close>]
                show "closedin_on A' (subspace_topology ?S ?TS A') (A' \<inter> D)"
                  using hD_cl by (by100 blast)
              qed
            next
              \<comment> \<open>Backward: per-arc closed \<Rightarrow> D closed in ?S.
                 Strategy: show D closed in X (via h\<A>\_coh), then restrict to ?S.\<close>
              assume hall': "\<forall>A\<in>?\<A>'. closedin_on A (subspace_topology ?S ?TS A) (A \<inter> D)"
              have "closedin_on X TX D"
              proof -
                have hD_sub_X: "D \<subseteq> X" using hD_sub hTUA_sub by (by100 blast)
                have "\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> D)"
                proof (intro ballI)
                  fix A assume hA_A: "A \<in> \<A>"
                  show "closedin_on A (subspace_topology X TX A) (A \<inter> D)"
                  proof (cases "A \<in> ?\<A>'")
                    case True
                    have "subspace_topology ?S ?TS A = subspace_topology X TX A"
                      by (rule subspace_topology_trans) (use True in \<open>by100 blast\<close>)
                    from hall'[rule_format, OF True]
                    show ?thesis using \<open>subspace_topology ?S ?TS A = subspace_topology X TX A\<close>
                      by (by100 simp)
                  next
                    case False
                    hence "A \<notin> ?\<A>'" .
                    hence hA_not_sub: "\<not> A \<subseteq> ?S" using hA_A by (by100 blast)
                    \<comment> \<open>A \<nsubseteq> ?S. A \<inter> ?S \<subseteq> endpoints(A) (finite, hence closed).\<close>
                    have hAT_ep: "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                    proof -
                      from hT_subgraph[rule_format, OF hA_A]
                      show ?thesis
                      proof assume "A \<subseteq> T" thus ?thesis using hA_not_sub by (by100 blast)
                      next assume h: "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                        thus ?thesis .
                      qed
                    qed
                    have hAC_ep: "A \<inter> chain!(j-1) \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                    proof (cases "A = chain!(j-1)")
                      case True thus ?thesis using hA_not_sub by (by100 blast)
                    next
                      case False
                      from h\<A>_inter[rule_format, OF hA_A hjm1_A this]
                      show ?thesis by (by100 blast)
                    qed
                    have "A \<inter> D \<subseteq> A \<inter> ?S" using hD_sub by (by100 blast)
                    have "A \<inter> ?S \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                      using hAT_ep hAC_ep by (by100 blast)
                    have hAD_sub_ep: "A \<inter> D \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                      using \<open>A \<inter> D \<subseteq> A \<inter> ?S\<close> \<open>A \<inter> ?S \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)\<close>
                      by (by100 blast)
                    have hAD_fin: "finite (A \<inter> D)"
                    proof -
                      have "finite (top1_arc_endpoints_on A (subspace_topology X TX A))"
                      proof -
                        have "top1_is_arc_on A (subspace_topology X TX A)" using h\<A> hA_A by (by100 blast)
                        then obtain h' where hh': "top1_homeomorphism_on top1_unit_interval
                            top1_unit_interval_topology A (subspace_topology X TX A) h'"
                          unfolding top1_is_arc_on_def by (by100 blast)
                        have "A \<subseteq> X" using h\<A> hA_A by (by100 blast)
                        have hX_haus_loc: "is_hausdorff_on X TX"
                          using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                        from arc_endpoints_are_boundary[OF hX_strict hX_haus_loc
                            \<open>A \<subseteq> X\<close> \<open>top1_is_arc_on A (subspace_topology X TX A)\<close> hh']
                        show ?thesis by (by100 simp)
                      qed
                      thus ?thesis using finite_subset[OF hAD_sub_ep] by (by100 blast)
                    qed
                    \<comment> \<open>Finite set in Hausdorff is closed.\<close>
                    have hA_sub: "A \<subseteq> X" using h\<A> hA_A by (by100 blast)
                    have hA_haus: "is_hausdorff_on A (subspace_topology X TX A)"
                    proof -
                      have "is_hausdorff_on X TX"
                        using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                      from conjunct2[OF conjunct2[OF Theorem_17_11]] hA_sub this
                      show ?thesis by (by100 blast)
                    qed
                    have hA_T1: "top1_T1_on A (subspace_topology X TX A)"
                      by (rule hausdorff_imp_T1_on[OF hA_haus])
                    have hA_top: "is_topology_on A (subspace_topology X TX A)"
                      using hA_haus unfolding is_hausdorff_on_def by (by100 blast)
                    have hAD_eq: "A \<inter> D = \<Union>((\<lambda>x. {x}) ` (A \<inter> D))" by (by100 blast)
                    have himg_fin: "finite ((\<lambda>x. {x}) ` (A \<inter> D))" using hAD_fin by (by100 simp)
                    have himg_cl: "\<forall>U\<in>((\<lambda>x. {x}) ` (A \<inter> D)). closedin_on A (subspace_topology X TX A) U"
                    proof (intro ballI)
                      fix U assume "U \<in> (\<lambda>x. {x}) ` (A \<inter> D)"
                      then obtain y where "y \<in> A" "U = {y}" by (by100 blast)
                      thus "closedin_on A (subspace_topology X TX A) U"
                        using hA_T1 unfolding top1_T1_on_def by (by100 blast)
                    qed
                    from closedin_Union_finite[OF hA_top himg_fin himg_cl]
                    have "closedin_on A (subspace_topology X TX A) (\<Union>((\<lambda>x. {x}) ` (A \<inter> D)))" .
                    thus ?thesis using hAD_eq by (by100 simp)
                  qed
                qed
                from h\<A>_coh[rule_format, OF hD_sub_X] this
                show ?thesis by (by100 blast)
              qed
              \<comment> \<open>D closed in X, D \<subseteq> ?S, ?S \<subseteq> X \<Rightarrow> D closed in ?S.\<close>
              have hX_top: "is_topology_on X TX"
                using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
              from Theorem_17_2[OF hX_top hTUA_sub]
              have "\<And>S. closedin_on ?S ?TS S \<longleftrightarrow> (\<exists>D. closedin_on X TX D \<and> S = D \<inter> ?S)" .
              thus "closedin_on ?S ?TS D" using \<open>closedin_on X TX D\<close> hD_sub by (by100 blast)
            qed
          qed
          show ?thesis unfolding top1_is_graph_on_def
            using hS_strict hS_haus h\<A>'_arcs h\<A>'_cover h\<A>'_inter h\<A>'_coh
            by (by100 blast)
        qed
        have hjm1_sub: "chain!(j-1) \<subseteq> X" using h\<A> hjm1_A by (by100 blast)
        have hTUA_tree: "top1_is_tree_on (T \<union> chain!(j-1)) (subspace_topology X TX (T \<union> chain!(j-1)))"
          by (rule Lemma_84_2_tree_union_arc[OF hgraph hT_tree hT_sub hjm1_A h\<A>
              h\<A>_cover h\<A>_inter hjm1_T
              \<open>chain!(j-1) \<inter> T \<subseteq> top1_arc_endpoints_on (chain!(j-1)) (subspace_topology X TX (chain!(j-1)))\<close>
              hcard1 hjm1_sub hT_closed hTUA_graph])
        \<comment> \<open>T \<subsetneq> T \<union> A_{j-1} (since A_{j-1} has point p \<notin> T).\<close>
        have "T \<subset> T \<union> chain!(j-1)"
          using \<open>p \<in> chain!(j-1) \<inter> chain!j\<close> \<open>p \<notin> T\<close> by (by100 blast)
        hence "T \<noteq> T \<union> chain!(j-1)" by (by100 blast)
        \<comment> \<open>T \<union> A_{j-1} \<subseteq> X.\<close>
        have "T \<union> chain!(j-1) \<subseteq> X"
          using hT_sub hjm1_A h\<A> by (by100 blast)
        \<comment> \<open>Contradiction: T maximal but T \<subsetneq> T \<union> A_{j-1} is also a subgraph-tree.\<close>
        \<comment> \<open>T \<union> chain!(j-1) satisfies the subgraph condition.\<close>
        have hTUA_subgraph: "\<forall>A\<in>\<A>. A \<subseteq> T \<union> chain!(j-1) \<or>
            A \<inter> (T \<union> chain!(j-1)) \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
        proof (intro ballI)
          fix A assume "A \<in> \<A>"
          show "A \<subseteq> T \<union> chain!(j-1) \<or>
              A \<inter> (T \<union> chain!(j-1)) \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
          proof (cases "A \<subseteq> T")
            case True thus ?thesis by (by100 blast)
          next
            case False
            have hAT: "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
              using hT_subgraph \<open>A \<in> \<A>\<close> False by (by100 blast)
            show ?thesis
            proof (cases "A = chain!(j-1)")
              case True thus ?thesis by (by100 blast)
            next
              case False
              have "A \<inter> chain!(j-1) \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                using h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> hjm1_A False] by (by100 blast)
              thus ?thesis using hAT by (by100 blast)
            qed
          qed
        qed
        have "T \<subseteq> T \<union> chain!(j-1)" by (by100 blast)
        have hTUA_coverage: "T \<union> chain!(j-1) = \<Union>{A \<in> \<A>. A \<subseteq> T \<union> chain!(j-1)}"
        proof (rule set_eqI, rule iffI)
          fix x assume "x \<in> T \<union> chain!(j-1)"
          thus "x \<in> \<Union>{A \<in> \<A>. A \<subseteq> T \<union> chain!(j-1)}"
          proof
            assume "x \<in> T"
            hence "x \<in> \<Union>{A \<in> \<A>. A \<subseteq> T}" using hT_coverage by (by100 simp)
            then obtain A where "A \<in> \<A>" "A \<subseteq> T" "x \<in> A" by (by100 blast)
            hence "A \<subseteq> T \<union> chain!(j-1)" by (by100 blast)
            thus ?thesis using \<open>A \<in> \<A>\<close> \<open>x \<in> A\<close> by (by100 blast)
          next
            assume "x \<in> chain!(j-1)"
            have "chain!(j-1) \<in> \<A>" using hjm1_A .
            moreover have "chain!(j-1) \<subseteq> T \<union> chain!(j-1)" by (by100 blast)
            ultimately show ?thesis using \<open>x \<in> chain!(j-1)\<close> by (by100 blast)
          qed
        next
          fix x assume "x \<in> \<Union>{A \<in> \<A>. A \<subseteq> T \<union> chain!(j-1)}"
          thus "x \<in> T \<union> chain!(j-1)" by (by100 blast)
        qed
        have "T \<union> chain!(j-1) = T"
          using hT_max \<open>T \<union> chain!(j-1) \<subseteq> X\<close> \<open>T \<subseteq> T \<union> chain!(j-1)\<close> hTUA_tree hTUA_subgraph
              hTUA_coverage
          by (by100 blast)
        thus False using \<open>T \<noteq> T \<union> chain!(j-1)\<close> by (by100 blast)
      qed
      show ?thesis using \<open>B \<in> \<A>\<close> \<open>v \<in> B\<close> hB_meets_T by (by100 blast)
    qed
  qed
qed

text \<open>Helper: removing interior points of non-tree arcs from a graph gives a
  deformation retract to the remaining subgraph. This is the key building block
  for the SvK proof of Theorem 84.7.
  Proof idea: each half-arc (from splitting at the removed point) retracts to
  its tree-endpoint. The retraction is continuous by the pasting lemma.\<close>
lemma graph_remove_interior_points_sc:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes hgraph: "top1_is_graph_on X TX"
      and h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and h\<A>_cover: "\<Union>\<A> = X"
      and h\<A>_inter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
      and hT_tree: "top1_is_tree_on T (subspace_topology X TX T)"
      and hT_sub: "T \<subseteq> X"
      and hT_subgraph: "\<forall>A\<in>\<A>. A \<subseteq> T \<or> A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
      and hNT_def: "NT = {A \<in> \<A>. \<not> A \<subseteq> T}"
      and hNT_fin: "finite NT"
      and hps: "\<forall>A\<in>NT. ps A \<in> A \<and> ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
      and hvertices_T: "\<forall>A\<in>\<A>. \<forall>e\<in>top1_arc_endpoints_on A (subspace_topology X TX A). e \<in> T"
      and hx0: "x0 \<in> T"
      and hcoh_A: "\<forall>C. C \<subseteq> X \<longrightarrow>
           (closedin_on X TX C \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
  shows "top1_simply_connected_on (X - ps ` NT) (subspace_topology X TX (X - ps ` NT))"
proof -
  let ?Y = "X - ps ` NT"
  let ?TY = "subspace_topology X TX ?Y"
  have hX_strict: "is_topology_on_strict X TX"
    using hgraph unfolding top1_is_graph_on_def by (by100 blast)
  have hX_top: "is_topology_on X TX"
    using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
  have hY_sub: "?Y \<subseteq> X" by (by100 blast)
  have hTY_top: "is_topology_on ?Y ?TY"
    by (rule subspace_topology_is_topology_on[OF hX_top hY_sub])
  \<comment> \<open>T \\<subseteq> Y (interior points of non-tree arcs are not in T).\<close>
  have hT_sub_Y: "T \<subseteq> ?Y"
  proof -
    have "\<forall>A\<in>NT. ps A \<notin> T"
    proof (intro ballI)
      fix A assume "A \<in> NT"
      hence "A \<in> \<A>" "\<not> A \<subseteq> T" using hNT_def by (by100 blast)+
      from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>] \<open>\<not> A \<subseteq> T\<close>
      have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)" by (by100 blast)
      from hps[rule_format, OF \<open>A \<in> NT\<close>]
      have "ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)" by (by100 blast)
      have "ps A \<in> A" using hps[rule_format, OF \<open>A \<in> NT\<close>] by (by100 blast)
      hence "ps A \<notin> A \<inter> T" using \<open>A \<inter> T \<subseteq> _\<close> \<open>ps A \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
      thus "ps A \<notin> T" using \<open>ps A \<in> A\<close> by (by100 blast)
    qed
    thus ?thesis using hT_sub by (by100 blast)
  qed
  \<comment> \<open>Path-connected: T path-connected and everything connects to T via arcs.\<close>
  have hY_pc: "top1_path_connected_on ?Y ?TY"
    unfolding top1_path_connected_on_def
  proof (intro conjI ballI)
    show "is_topology_on ?Y ?TY" by (rule hTY_top)
  next
    fix x y assume hx: "x \<in> ?Y" and hy: "y \<in> ?Y"
    \<comment> \<open>Both x, y are in Y. Each is in T or in a path-connected piece meeting T.
       Connect each to x0 via T, then concatenate.\<close>
    \<comment> \<open>Every point of Y connected to x0 via path in Y.\<close>
    have hY_conn_x0: "\<forall>z\<in>?Y. \<exists>f. top1_is_path_on ?Y ?TY x0 z f"
    proof (intro ballI)
      fix z assume hz: "z \<in> ?Y"
      hence hz_X: "z \<in> X" using hY_sub by (by100 blast)
      \<comment> \<open>T is path-connected in T's subspace topology.\<close>
      have hT_pc: "top1_path_connected_on T (subspace_topology X TX T)"
        using hT_tree unfolding top1_is_tree_on_def top1_simply_connected_on_def by (by100 blast)
      \<comment> \<open>Lift T's path-connectedness to Y (T \\<subseteq> Y \\<subseteq> X).\\<close>
      have hT_pc_Y: "\<forall>a\<in>T. \<forall>b\<in>T. \<exists>f. top1_is_path_on ?Y ?TY a b f"
      proof (intro ballI)
        fix a b assume "a \<in> T" "b \<in> T"
        \<comment> \<open>Path from a to b in T. Lift to Y via T \\<subseteq> Y.\<close>
        from hT_pc[unfolded top1_path_connected_on_def, THEN conjunct2, rule_format, OF \<open>a \<in> T\<close> \<open>b \<in> T\<close>]
        obtain g where hg: "top1_is_path_on T (subspace_topology X TX T) a b g" by (by100 blast)
        \<comment> \<open>g maps [0,1] to T \\<subseteq> Y. Continuous in T's topology = Y's subspace topology restricted to T.\<close>
        have "\<forall>t\<in>top1_unit_interval. g t \<in> T" using hg unfolding top1_is_path_on_def
            top1_continuous_map_on_def by (by100 blast)
        hence hg_img_Y: "\<forall>t\<in>top1_unit_interval. g t \<in> ?Y" using hT_sub_Y by (by100 blast)
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?Y ?TY g"
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix t assume "t \<in> top1_unit_interval" thus "g t \<in> ?Y" using hg_img_Y by (by100 blast)
        next
          fix V assume "V \<in> ?TY"
          then obtain U0 where "U0 \<in> TX" "V = U0 \<inter> ?Y"
            unfolding subspace_topology_def by (by100 auto)
          hence "V \<subseteq> ?Y" by (by100 blast)
          then obtain U where "U \<in> TX" "V = U \<inter> ?Y" using \<open>V \<in> ?TY\<close>
            unfolding subspace_topology_def by (by100 auto)
          have "U \<inter> T \<in> subspace_topology X TX T"
            unfolding subspace_topology_def using \<open>U \<in> TX\<close> by (by100 blast)
          have hg_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              T (subspace_topology X TX T) g" using hg unfolding top1_is_path_on_def by (by100 blast)
          hence "{t \<in> top1_unit_interval. g t \<in> U \<inter> T} \<in> top1_unit_interval_topology"
            using \<open>U \<inter> T \<in> subspace_topology X TX T\<close>
            unfolding top1_continuous_map_on_def by (by100 blast)
          have "{t \<in> top1_unit_interval. g t \<in> V} = {t \<in> top1_unit_interval. g t \<in> U \<inter> T}"
          proof (rule set_eqI, rule iffI)
            fix t assume "t \<in> {t \<in> top1_unit_interval. g t \<in> V}"
            hence "t \<in> top1_unit_interval" "g t \<in> V" by (by100 blast)+
            have "g t \<in> U" "g t \<in> ?Y" using \<open>g t \<in> V\<close> \<open>V = U \<inter> ?Y\<close> by (by100 blast)+
            have "g t \<in> T"
            proof -
              have "\<forall>t\<in>top1_unit_interval. g t \<in> T"
                using hg_cont unfolding top1_continuous_map_on_def by (by100 blast)
              thus ?thesis using \<open>t \<in> top1_unit_interval\<close> by (by100 blast)
            qed
            thus "t \<in> {t \<in> top1_unit_interval. g t \<in> U \<inter> T}"
              using \<open>t \<in> top1_unit_interval\<close> \<open>g t \<in> U\<close> \<open>g t \<in> T\<close> by (by100 blast)
          next
            fix t assume "t \<in> {t \<in> top1_unit_interval. g t \<in> U \<inter> T}"
            hence "t \<in> top1_unit_interval" "g t \<in> U" "g t \<in> T" by (by100 blast)+
            have "g t \<in> ?Y" using \<open>g t \<in> T\<close> hT_sub_Y by (by100 blast)
            hence "g t \<in> V" using \<open>g t \<in> U\<close> \<open>V = U \<inter> ?Y\<close> by (by100 blast)
            thus "t \<in> {t \<in> top1_unit_interval. g t \<in> V}"
              using \<open>t \<in> top1_unit_interval\<close> by (by100 blast)
          qed
          thus "{t \<in> top1_unit_interval. g t \<in> V} \<in> top1_unit_interval_topology"
            using \<open>{t \<in> top1_unit_interval. g t \<in> U \<inter> T} \<in> _\<close> by (by100 simp)
        qed
        moreover have "g 0 = a" "g 1 = b" using hg unfolding top1_is_path_on_def by (by100 blast)+
        ultimately show "\<exists>f. top1_is_path_on ?Y ?TY a b f"
          unfolding top1_is_path_on_def using hg_img_Y by (by100 blast)
      qed
      show "\<exists>f. top1_is_path_on ?Y ?TY x0 z f"
      proof (cases "z \<in> T")
        case True
        from hT_pc_Y[rule_format, OF hx0 True] show ?thesis .
      next
        case False
        \<comment> \<open>z \\<notin> T. z is in some arc A. Construct path from z to T-endpoint, then to x0.\<close>
        have "z \<in> \<Union>\<A>" using hz_X h\<A>_cover by (by100 simp)
        then obtain A where hA: "A \<in> \<A>" "z \<in> A" by (by100 blast)
        have hA_sub: "A \<subseteq> X" using h\<A> hA(1) by (by100 blast)
        \<comment> \<open>A \\<notin> T (since z \\<in> A and z \\<notin> T), so A \\<in> NT. ps(A) removed.\<close>
        have "A \<in> NT" using hNT_def hA(1) hA(2) False by (by100 blast)
        \<comment> \<open>Get a T-endpoint of A that z is connected to (on same side of ps(A)).\\<close>
        obtain e fze where he: "e \<in> T" and hfze: "top1_is_path_on ?Y ?TY z e fze"
        proof -
          have hA_arc: "top1_is_arc_on A (subspace_topology X TX A)"
            using h\<A> hA(1) by (by100 blast)
          then obtain h0 where hh0: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
              A (subspace_topology X TX A) h0" unfolding top1_is_arc_on_def by (by100 blast)
          have hX_strict: "is_topology_on_strict X TX"
            using hgraph unfolding top1_is_graph_on_def by (by100 blast)
          have hX_haus: "is_hausdorff_on X TX"
            using hgraph unfolding top1_is_graph_on_def by (by100 blast)
          from arc_endpoints_are_boundary[OF hX_strict hX_haus hA_sub hA_arc hh0]
          have hep: "top1_arc_endpoints_on A (subspace_topology X TX A) = {h0 0, h0 1}" .
          have "h0 0 \<in> T" using hvertices_T[rule_format, OF hA(1)] hep by (by100 simp)
          have "h0 1 \<in> T" using hvertices_T[rule_format, OF hA(1)] hep by (by100 simp)
          \<comment> \<open>Path from z to nearest T-endpoint within half-arc.\<close>
          \<comment> \<open>Extract bijectivity/injectivity from h0 homeomorphism.\<close>
          have hbij: "bij_betw h0 top1_unit_interval A"
            using hh0 unfolding top1_homeomorphism_on_def by (by100 blast)
          have hinj: "inj_on h0 top1_unit_interval"
            using hbij unfolding bij_betw_def by (by100 blast)
          have himg: "h0 ` top1_unit_interval = A"
            using hbij unfolding bij_betw_def by (by100 blast)
          have hz_A: "z \<in> A" using hA(2) .
          have hz_img: "z \<in> h0 ` top1_unit_interval" using hz_A himg by (by100 simp)
          \<comment> \<open>Get s = inv(h0, z) and t0 = inv(h0, ps(A)).\<close>
          define s where "s = inv_into top1_unit_interval h0 z"
          define t0 where "t0 = inv_into top1_unit_interval h0 (ps A)"
          have hs_I: "s \<in> top1_unit_interval"
            unfolding s_def by (rule inv_into_into[OF hz_img])
          have hh0s: "h0 s = z"
            unfolding s_def by (rule f_inv_into_f[OF hz_img])
          have hpsA_A: "ps A \<in> A" using hps[rule_format, OF \<open>A \<in> NT\<close>] by (by100 blast)
          have hpsA_img: "ps A \<in> h0 ` top1_unit_interval" using hpsA_A himg by (by100 simp)
          have ht0_I: "t0 \<in> top1_unit_interval"
            unfolding t0_def by (rule inv_into_into[OF hpsA_img])
          have hh0t0: "h0 t0 = ps A"
            unfolding t0_def by (rule f_inv_into_f[OF hpsA_img])
          \<comment> \<open>s \\<noteq> t0 since z \\<in> Y but ps(A) \\<notin> Y.\<close>
          have hst0: "s \<noteq> t0"
          proof
            assume "s = t0"
            hence "z = ps A" using hh0s hh0t0 by (by100 simp)
            moreover have "ps A \<in> ps ` NT" using \<open>A \<in> NT\<close> by (by100 blast)
            ultimately have "z \<in> ps ` NT" by (by100 simp)
            moreover have "z \<in> ?Y" using hz by (by100 blast)
            ultimately show False by (by100 blast)
          qed
          \<comment> \<open>t0 \\<notin> {0,1} since ps(A) is not an endpoint.\<close>
          have hpsA_not_ep: "ps A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hps[rule_format, OF \<open>A \<in> NT\<close>] by (by100 blast)
          have ht0_not_0: "t0 \<noteq> 0"
          proof
            assume "t0 = 0"
            hence "h0 t0 = h0 0" by (by100 simp)
            hence "ps A = h0 0" using hh0t0 by (by100 simp)
            hence "ps A \<in> {h0 0, h0 1}" by (by100 blast)
            thus False using hpsA_not_ep hep by (by100 simp)
          qed
          have ht0_not_1: "t0 \<noteq> 1"
          proof
            assume "t0 = 1"
            hence "h0 t0 = h0 1" by (by100 simp)
            hence "ps A = h0 1" using hh0t0 by (by100 simp)
            hence "ps A \<in> {h0 0, h0 1}" by (by100 blast)
            thus False using hpsA_not_ep hep by (by100 simp)
          qed
          have hs_01: "0 \<le> s \<and> s \<le> 1" using hs_I unfolding top1_unit_interval_def by (by100 auto)
          have ht0_01: "0 < t0 \<and> t0 < 1"
          proof -
            have "0 \<le> t0 \<and> t0 \<le> 1" using ht0_I unfolding top1_unit_interval_def by (by100 auto)
            thus ?thesis using ht0_not_0 ht0_not_1 by (by100 linarith)
          qed
          \<comment> \<open>Key: any point on the arc not at ps(A) and not an endpoint of another arc is in Y.\<close>
          have himg_in_Y: "\<And>u. u \<in> top1_unit_interval \<Longrightarrow> u \<noteq> t0 \<Longrightarrow> h0 u \<in> ?Y"
          proof -
            fix u assume hu_I: "u \<in> top1_unit_interval" and hu_ne: "u \<noteq> t0"
            have "h0 u \<in> A" using himg hu_I by (by100 blast)
            hence "h0 u \<in> X" using hA_sub by (by100 blast)
            have "h0 u \<notin> ps ` NT"
            proof
              assume "h0 u \<in> ps ` NT"
              then obtain A' where hA': "A' \<in> NT" "h0 u = ps A'" by (by100 blast)
              show False
              proof (cases "A' = A")
                case True
                hence "h0 u = ps A" using hA'(2) by (by100 simp)
                hence "h0 u = h0 t0" using hh0t0 by (by100 simp)
                from inj_onD[OF hinj this hu_I ht0_I]
                show False using hu_ne by (by100 blast)
              next
                case hA'_ne: False
                have "A' \<in> \<A>" using hA'(1) hNT_def by (by100 blast)
                have "h0 u \<in> A" using himg hu_I by (by100 blast)
                have "ps A' \<in> A'" using hps[rule_format, OF hA'(1)] by (by100 blast)
                hence "h0 u \<in> A'" using hA'(2) by (by100 simp)
                have "h0 u \<in> A \<inter> A'" using \<open>h0 u \<in> A\<close> \<open>h0 u \<in> A'\<close> by (by100 blast)
                hence "h0 u \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                  using h\<A>_inter[rule_format, OF hA(1) \<open>A' \<in> \<A>\<close>] hA'_ne by (by100 blast)
                hence "h0 u \<in> {h0 0, h0 1}" using hep by (by100 simp)
                hence "h0 u \<in> T"
                  using \<open>h0 0 \<in> T\<close> \<open>h0 1 \<in> T\<close> by (by100 auto)
                \<comment> \<open>But ps(A') \\<notin> T.\<close>
                have "ps A' \<notin> T" using hT_sub_Y hA'(1) by (by100 blast)
                thus False using \<open>h0 u \<in> T\<close> hA'(2) by (by100 simp)
              qed
            qed
            thus "h0 u \<in> ?Y" using \<open>h0 u \<in> X\<close> by (by100 blast)
          qed
          \<comment> \<open>h0 is continuous I \\<rightarrow> X (enlarge codomain from A to X).\<close>
          have hh0_cont_A: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              A (subspace_topology X TX A) h0"
            using hh0 unfolding top1_homeomorphism_on_def by (by100 blast)
          have hh0_cont_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology X TX h0"
          proof -
            have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                X (subspace_topology X TX X) h0"
              by (rule top1_continuous_map_on_codomain_enlarge[OF hh0_cont_A hA_sub subset_refl])
            moreover have "subspace_topology X TX X = TX"
            proof (rule subspace_topology_self)
              show "\<forall>U\<in>TX. U \<subseteq> X" using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
            qed
            ultimately show ?thesis by (by100 simp)
          qed
          \<comment> \<open>Case split: s < t0 or s > t0.\<close>
          consider (lt) "s < t0" | (gt) "s > t0" using hst0 by (by100 linarith)
          then show ?thesis
          proof cases
            case lt
            \<comment> \<open>Path from z = h0(s) to h0(0) \\<in> T via \\<lambda>t. h0(s*(1-t)).\<close>
            \<comment> \<open>Use affine map \\<lambda>t. t*s : [0,1] \\<rightarrow> [0,s] then reverse.\<close>
            define g0 where "g0 = (\<lambda>t. h0 (s * (1 - t)))"
            have hg0_z: "g0 0 = z" unfolding g0_def using hh0s by (by100 simp)
            have hg0_e: "g0 1 = h0 0" unfolding g0_def by (by100 simp)
            have hg0_img_Y: "\<forall>t\<in>top1_unit_interval. g0 t \<in> ?Y"
            proof (intro ballI)
              fix t assume ht: "t \<in> top1_unit_interval"
              have ht_01: "0 \<le> t \<and> t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)
              have hst_I: "s * (1 - t) \<in> top1_unit_interval"
              proof -
                have h1: "0 \<le> 1 - t" using ht_01 by (by100 linarith)
                have "0 \<le> s * (1 - t)" using hs_01 h1
                  by (rule mult_nonneg_nonneg[OF conjunct1 _])
                moreover have "s * (1 - t) \<le> s * 1"
                proof (rule mult_left_mono)
                  show "1 - t \<le> 1" using ht_01 by (by100 linarith)
                  show "0 \<le> s" using hs_01 by (by100 linarith)
                qed
                hence "s * (1 - t) \<le> 1" using hs_01 by (by100 linarith)
                ultimately show ?thesis unfolding top1_unit_interval_def by (by100 auto)
              qed
              have "s * (1 - t) \<noteq> t0"
              proof
                assume "s * (1 - t) = t0"
                have "s * (1 - t) \<le> s"
                proof -
                  have "s * (1 - t) \<le> s * 1"
                  proof (rule mult_left_mono)
                    show "1 - t \<le> 1" using ht_01 by (by100 linarith)
                    show "0 \<le> s" using hs_01 by (by100 linarith)
                  qed
                  thus ?thesis by (by100 simp)
                qed
                hence "t0 \<le> s" using \<open>s * (1 - t) = t0\<close> by (by100 linarith)
                thus False using lt by (by100 linarith)
              qed
              thus "g0 t \<in> ?Y" unfolding g0_def using himg_in_Y[OF hst_I] by (by100 blast)
            qed
            have hg0_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?Y ?TY g0"
            proof -
              \<comment> \<open>Affine map \\<lambda>t. t*s is continuous I \\<rightarrow> I.\<close>
              have haff: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  top1_unit_interval top1_unit_interval_topology (\<lambda>t. 0 + t * (s - 0))"
                by (rule affine_map_continuous_I_to_I) (use hs_01 in linarith)+
              hence haff': "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  top1_unit_interval top1_unit_interval_topology (\<lambda>t. t * s)" by (by100 simp)
              \<comment> \<open>Reverse: \\<lambda>t. (1-t)*s = top1\\_path\\_reverse (\\<lambda>t. t*s).\<close>
              have hrev: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  top1_unit_interval top1_unit_interval_topology (top1_path_reverse (\<lambda>t. t * s))"
                by (rule top1_path_reverse_continuous[OF haff'])
              have hrev': "top1_path_reverse (\<lambda>t. t * s) = (\<lambda>t. (1 - t) * s)"
                unfolding top1_path_reverse_def by (by100 simp)
              have haff_st: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  top1_unit_interval top1_unit_interval_topology (\<lambda>t. s * (1 - t))"
              proof -
                have "\<And>t::real. (1 - t) * s = s * (1 - t)" by (rule mult.commute)
                hence "(\<lambda>t. (1 - t) * s) = (\<lambda>t::real. s * (1 - t))" by (by100 auto)
                thus ?thesis using hrev hrev' by (by100 simp)
              qed
              \<comment> \<open>Compose: h0 \\<circ> (\\<lambda>t. s*(1-t)) is continuous I \\<rightarrow> X.\<close>
              have hcomp: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  X TX (h0 \<circ> (\<lambda>t. s * (1 - t)))"
                by (rule top1_continuous_map_on_comp[OF haff_st hh0_cont_X])
              have hcomp': "(h0 \<circ> (\<lambda>t. s * (1 - t))) = g0"
                unfolding g0_def comp_def by (by100 simp)
              have hg0_cont_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  X TX g0"
                using hcomp hcomp' by (by100 simp)
              \<comment> \<open>Restrict codomain from X to Y.\<close>
              show ?thesis
                by (rule continuous_map_restrict_codomain[OF hg0_cont_X _ hY_sub])
                   (use hg0_img_Y in \<open>by100 blast\<close>)
            qed
            have hpath0: "top1_is_path_on ?Y ?TY z (h0 0) g0"
              unfolding top1_is_path_on_def using hg0_cont hg0_z hg0_e by (by100 blast)
            show ?thesis by (rule that[OF \<open>h0 0 \<in> T\<close> hpath0])
          next
            case gt
            \<comment> \<open>Path from z = h0(s) to h0(1) \\<in> T via \\<lambda>t. h0(s + (1-s)*t).\<close>
            define g1 where "g1 = (\<lambda>t. h0 (s + (1 - s) * t))"
            have hg1_z: "g1 0 = z" unfolding g1_def using hh0s by (by100 simp)
            have hg1_e: "g1 1 = h0 1" unfolding g1_def by (by100 simp)
            have hg1_img_Y: "\<forall>t\<in>top1_unit_interval. g1 t \<in> ?Y"
            proof (intro ballI)
              fix t assume ht: "t \<in> top1_unit_interval"
              have ht_01: "0 \<le> t \<and> t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)
              have hst_I: "s + (1 - s) * t \<in> top1_unit_interval"
              proof -
                have h1: "0 \<le> 1 - s" using hs_01 by (by100 linarith)
                have "0 \<le> (1 - s) * t" using h1 ht_01
                  by (rule mult_nonneg_nonneg[OF _ conjunct1])
                hence "0 \<le> s + (1 - s) * t" using hs_01 by (by100 linarith)
                moreover have "(1 - s) * t \<le> (1 - s) * 1"
                proof (rule mult_left_mono)
                  show "t \<le> 1" using ht_01 by (by100 linarith)
                  show "0 \<le> 1 - s" using hs_01 by (by100 linarith)
                qed
                hence "(1 - s) * t \<le> 1 - s" by (by100 simp)
                hence "s + (1 - s) * t \<le> 1" by (by100 linarith)
                ultimately show ?thesis unfolding top1_unit_interval_def by (by100 auto)
              qed
              have "s + (1 - s) * t \<noteq> t0"
              proof
                assume "s + (1 - s) * t = t0"
                have "s + (1 - s) * t \<ge> s"
                proof -
                  have "0 \<le> (1 - s) * t"
                    by (rule mult_nonneg_nonneg) (use hs_01 ht_01 in linarith)+
                  thus ?thesis by (by100 linarith)
                qed
                hence "t0 \<ge> s" using \<open>s + (1 - s) * t = t0\<close> by (by100 linarith)
                thus False using gt by (by100 linarith)
              qed
              thus "g1 t \<in> ?Y" unfolding g1_def using himg_in_Y[OF hst_I] by (by100 blast)
            qed
            have hg1_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?Y ?TY g1"
            proof -
              \<comment> \<open>Affine map \\<lambda>t. s + t*(1-s) is continuous I \\<rightarrow> I.\<close>
              have haff: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  top1_unit_interval top1_unit_interval_topology (\<lambda>t. s + t * (1 - s))"
                by (rule affine_map_continuous_I_to_I) (use hs_01 in linarith)+
              have haff': "\<And>t::real. s + t * (1 - s) = s + (1 - s) * t"
                by (by100 simp)
              have haff_st: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  top1_unit_interval top1_unit_interval_topology (\<lambda>t. s + (1 - s) * t)"
                using haff haff' by (by100 simp)
              \<comment> \<open>Compose: h0 \\<circ> affine is continuous I \\<rightarrow> X.\<close>
              have hcomp: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  X TX (h0 \<circ> (\<lambda>t. s + (1 - s) * t))"
                by (rule top1_continuous_map_on_comp[OF haff_st hh0_cont_X])
              have hcomp': "(h0 \<circ> (\<lambda>t. s + (1 - s) * t)) = g1"
                unfolding g1_def comp_def by (by100 simp)
              have hg1_cont_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                  X TX g1"
                using hcomp hcomp' by (by100 simp)
              \<comment> \<open>Restrict codomain from X to Y.\<close>
              show ?thesis
                by (rule continuous_map_restrict_codomain[OF hg1_cont_X _ hY_sub])
                   (use hg1_img_Y in \<open>by100 blast\<close>)
            qed
            have hpath1: "top1_is_path_on ?Y ?TY z (h0 1) g1"
              unfolding top1_is_path_on_def using hg1_cont hg1_z hg1_e by (by100 blast)
            show ?thesis by (rule that[OF \<open>h0 1 \<in> T\<close> hpath1])
          qed
        qed
        \<comment> \<open>Path from e to x0 in T \\<subseteq> Y.\<close>
        from hT_pc_Y[rule_format, OF \<open>e \<in> T\<close> hx0]
        obtain fex0 where hfex0: "top1_is_path_on ?Y ?TY e x0 fex0" by (by100 blast)
        \<comment> \<open>Path from x0 to z: reverse(fex0) * reverse(fze) = path from x0 to z.\<close>
        have hrev_fex0: "top1_is_path_on ?Y ?TY x0 e (top1_path_reverse fex0)"
          by (rule top1_path_reverse_is_path[OF hfex0])
        have hrev_fze: "top1_is_path_on ?Y ?TY e z (top1_path_reverse fze)"
          by (rule top1_path_reverse_is_path[OF hfze])
        have "top1_is_path_on ?Y ?TY x0 z (top1_path_product (top1_path_reverse fex0) (top1_path_reverse fze))"
          by (rule top1_path_product_is_path[OF hTY_top hrev_fex0 hrev_fze])
        thus ?thesis by (by100 blast)
      qed
    qed
    from hY_conn_x0[rule_format, OF hx]
    obtain fx where hfx: "top1_is_path_on ?Y ?TY x0 x fx" by (by100 blast)
    from hY_conn_x0[rule_format, OF hy]
    obtain fy where hfy: "top1_is_path_on ?Y ?TY x0 y fy" by (by100 blast)
    \<comment> \<open>Concatenate: reverse(fx) * fy gives path from x to y.\<close>
    have hfx_rev: "top1_is_path_on ?Y ?TY x x0 (top1_path_reverse fx)"
      by (rule top1_path_reverse_is_path[OF hfx])
    have hfxy: "top1_is_path_on ?Y ?TY x y (top1_path_product (top1_path_reverse fx) fy)"
      by (rule top1_path_product_is_path[OF hTY_top hfx_rev hfy])
    thus "\<exists>f. top1_is_path_on ?Y ?TY x y f" by (by100 blast)
  qed
  \<comment> \<open>All loops null-homotopic: loop avoids removed points, backtracks on half-arcs,
     hence homotopic to a loop in T. T simply connected.\<close>
  have hY_loops: "\<forall>f. top1_is_loop_on ?Y ?TY x0 f \<longrightarrow>
      top1_path_homotopic_on ?Y ?TY x0 x0 f (top1_constant_path x0)"
  proof (intro allI impI)
    fix f assume hf: "top1_is_loop_on ?Y ?TY x0 f"
    \<comment> \<open>Strategy: construct retraction r: Y \\<rightarrow> T (constant on half-arcs).
       r\\<circ>f is a loop in T. T simply connected \\<Rightarrow> r\\<circ>f null-homotopic in T.
       f is homotopic to r\\<circ>f in Y (slide along half-arcs).
       Compose: f null-homotopic.\<close>
    \<comment> \<open>Step 1: Define retraction r: Y \\<rightarrow> T.\\<close>
    \<comment> \<open>Step 2: r continuous (pasting on T + finitely many half-arcs).\\<close>
    \<comment> \<open>Step 3: r\\<circ>f loop at x0 in T, null-homotopic (T simply connected).\\<close>
    \<comment> \<open>Step 4: f \\<sim> r\\<circ>f in Y (homotopy: slide along arcs).\\<close>
    \<comment> \<open>Step 5: Lift null-homotopy from T to Y.\\<close>
    \<comment> \<open>Construct retraction r: Y \\<rightarrow> T and homotopy f \\<sim> r\\<circ>f.\\<close>
    \<comment> \<open>For each A \\<in> NT, choose a homeomorphism hA (lifted before obtain r for homotopy access).\<close>
    define hA_choice where "hA_choice \<equiv> \<lambda>A.
      SOME h. top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        A (subspace_topology X TX A) h"
    define tA where "tA \<equiv> \<lambda>A. inv_into top1_unit_interval (hA_choice A) (ps A)"
    have hhA: "\<And>A. A \<in> NT \<Longrightarrow> top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        A (subspace_topology X TX A) (hA_choice A)"
    proof -
      fix A assume "A \<in> NT"
      hence "A \<in> \<A>" using hNT_def by (by100 blast)
      hence "top1_is_arc_on A (subspace_topology X TX A)" using h\<A> by (by100 blast)
      then obtain h where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          A (subspace_topology X TX A) h" unfolding top1_is_arc_on_def by (by100 blast)
      thus "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          A (subspace_topology X TX A) (hA_choice A)"
        unfolding hA_choice_def
        by (rule someI[of "\<lambda>h. top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
            A (subspace_topology X TX A) h"])
    qed
    \<comment> \<open>Step 1-2: Retraction r (identity on T, constant on half-arcs, continuous by pasting).\<close>
    define LA where "LA \<equiv> \<lambda>A. {x \<in> A \<inter> ?Y. inv_into top1_unit_interval (hA_choice A) x \<le> tA A}"
    define RA where "RA \<equiv> \<lambda>A. {x \<in> A \<inter> ?Y. inv_into top1_unit_interval (hA_choice A) x \<ge> tA A}"
    \<comment> \<open>Closedness facts lifted for use in both retraction and homotopy proofs.\<close>
    have hT_closed_X: "closedin_on X TX T"
    proof -
      have "\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> T)"
      proof (intro ballI)
        fix Ag assume "Ag \<in> \<A>"
        have "Ag \<subseteq> X" using h\<A> \<open>Ag \<in> \<A>\<close> by (by100 blast)
        show "closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> T)"
        proof (cases "Ag \<subseteq> T")
          case True
          hence "Ag \<inter> T = Ag" by (by100 blast)
          thus ?thesis
            using closedin_carrier[OF subspace_topology_is_topology_on[OF hX_top \<open>Ag \<subseteq> X\<close>]]
            by (by100 simp)
        next
          case False
          from hT_subgraph[rule_format, OF \<open>Ag \<in> \<A>\<close>] False
          have "Ag \<inter> T \<subseteq> top1_arc_endpoints_on Ag (subspace_topology X TX Ag)" by (by100 blast)
          have harc: "top1_is_arc_on Ag (subspace_topology X TX Ag)" using h\<A> \<open>Ag \<in> \<A>\<close> by (by100 blast)
          then obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
              Ag (subspace_topology X TX Ag) h" unfolding top1_is_arc_on_def by (by100 blast)
          have hhaus: "is_hausdorff_on X TX" using hgraph unfolding top1_is_graph_on_def by (by100 blast)
          from arc_endpoints_are_boundary[OF hX_strict hhaus \<open>Ag \<subseteq> X\<close> harc hh]
          have "top1_arc_endpoints_on Ag (subspace_topology X TX Ag) = {h 0, h 1}" .
          hence "finite (top1_arc_endpoints_on Ag (subspace_topology X TX Ag))" by (by100 simp)
          from finite_subset[OF \<open>Ag \<inter> T \<subseteq> _\<close> this]
          have "finite (Ag \<inter> T)" .
          have "is_hausdorff_on Ag (subspace_topology X TX Ag)"
            using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>Ag \<subseteq> X\<close> hhaus by (by100 blast)
          show ?thesis by (rule Theorem_17_8[OF \<open>is_hausdorff_on Ag _\<close> \<open>finite (Ag \<inter> T)\<close>]) (by100 blast)
        qed
      qed
      thus ?thesis using hcoh_A[rule_format, OF hT_sub] by (by100 blast)
    qed
    have hT_closed_Y: "closedin_on ?Y ?TY T"
    proof -
      from Theorem_17_2[OF hX_top hY_sub, of T]
      show ?thesis using hT_closed_X hT_sub_Y by (by100 blast)
    qed
    have hA_closed_X: "\<forall>A\<in>NT. closedin_on X TX A"
    proof (intro ballI)
      fix A assume "A \<in> NT"
      hence "A \<in> \<A>" using hNT_def by (by100 blast)
      hence hAsub: "A \<subseteq> X" and harc: "top1_is_arc_on A (subspace_topology X TX A)"
        using h\<A> by (by100 blast)+
      then obtain h0 where hh0: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
          A (subspace_topology X TX A) h0" unfolding top1_is_arc_on_def by (by100 blast)
      have hI_cpt: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
      proof -
        have hCI: "top1_compact_on (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1)"
          by (rule top1_closed_interval_compact) (by100 linarith)
        have hCI_eq: "top1_closed_interval 0 1 = top1_unit_interval"
          unfolding top1_closed_interval_def top1_unit_interval_def by (by100 auto)
        have hIT_sub: "top1_unit_interval_topology \<subseteq> top1_closed_interval_topology 0 1"
          by (rule I_top_sub_closed_interval_top)
        show ?thesis unfolding top1_compact_on_def
        proof (intro conjI allI impI)
          show "is_topology_on top1_unit_interval top1_unit_interval_topology"
            by (rule top1_unit_interval_topology_is_topology_on)
        next
          fix Uc assume hUc: "Uc \<subseteq> top1_unit_interval_topology \<and> top1_unit_interval \<subseteq> \<Union>Uc"
          have "Uc \<subseteq> top1_closed_interval_topology 0 1" using hUc hIT_sub by (by100 blast)
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
        by (rule subspace_topology_is_topology_on[OF hX_top hAsub])
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
      have "is_hausdorff_on X TX"
        using hgraph unfolding top1_is_graph_on_def by (by100 blast)
      thus "closedin_on X TX A"
        by (rule compact_in_strict_hausdorff_closedin_on[OF _ hX_strict hAsub
            \<open>top1_compact_on A (subspace_topology X TX A)\<close>])
    qed
    have hAY_closed: "\<forall>A\<in>NT. closedin_on ?Y ?TY (A \<inter> ?Y)"
    proof (intro ballI)
      fix A assume "A \<in> NT"
      from Theorem_17_2[OF hX_top hY_sub, of "A \<inter> ?Y"]
      show "closedin_on ?Y ?TY (A \<inter> ?Y)" using hA_closed_X \<open>A \<in> NT\<close> by (by100 blast)
    qed
    obtain r where hr_cont: "top1_continuous_map_on ?Y ?TY ?Y ?TY r"
        and hr_T: "\<forall>a\<in>T. r a = a"
        and hr_img: "\<forall>x\<in>?Y. r x \<in> T"
        and hr_LA: "\<forall>A\<in>NT. \<forall>x\<in>LA A. r x = hA_choice A 0"
        and hr_RA: "\<forall>A\<in>NT. \<forall>x\<in>RA A. r x = hA_choice A 1"
    proof -
      \<comment> \<open>Define r: identity on T, nearest T-endpoint on half-arcs.\<close>
      \<comment> \<open>For each non-tree arc A \\<in> NT with homeomorphism hA:
         r(hA(s)) = hA(0) if s < tA (first half), hA(1) if s > tA (second half).
         On T: r = identity.\<close>
      \<comment> \<open>Formally: define r using if-then-else. For x \\<in> T: r(x) = x.
         For x \\<notin> T: x is in a unique arc A \\<in> NT, on one side of ps(A).
         r(x) = the T-endpoint of x's half-arc.\<close>
      \<comment> \<open>For continuity: Y = T \\<union> B where B = \\<Union>(half-arcs).
         T closed in Y, B closed in Y (finite union of closed).
         r|T = id (continuous). r|B = piecewise constant (continuous by pasting).
         r agrees on T \\<inter> B = T-endpoints. pasting\\_lemma\\_two\\_closed.\<close>
      \<comment> \<open>Define r: for x \\<in> T: r(x) = x. For x \\<notin> T: x is interior to a unique
         non-tree arc A. r(x) = the T-endpoint on x's side of ps(A).\<close>
      \<comment> \<open>Step 1: For x \\<notin> T, the unique arc and side-aware endpoint.\<close>
      have hY_decomp: "\<forall>x\<in>?Y. x \<in> T \<or> (\<exists>!A. A \<in> NT \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A))"
      proof (intro ballI)
        fix x assume "x \<in> ?Y"
        show "x \<in> T \<or> (\<exists>!A. A \<in> NT \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A))"
        proof (cases "x \<in> T")
          case True thus ?thesis by (by100 blast)
        next
          case False
          \<comment> \<open>x \\<notin> T. Find unique arc containing x as interior point.\<close>
          have "x \<in> X" using \<open>x \<in> ?Y\<close> hY_sub by (by100 blast)
          hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
          then obtain A where hA: "A \<in> \<A>" "x \<in> A" by (by100 blast)
          \<comment> \<open>A \\<notin> T (x \\<in> A, x \\<notin> T), so A \\<in> NT.\<close>
          have "A \<in> NT" using hNT_def hA(1) hA(2) False by (by100 blast)
          \<comment> \<open>x is NOT an endpoint of A (endpoints \\<in> T but x \\<notin> T).\<close>
          have "x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
          proof
            assume "x \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
            hence "x \<in> T" using hvertices_T[rule_format, OF hA(1)] by (by100 blast)
            thus False using False by (by100 blast)
          qed
          hence hx_int: "x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hA(2) by (by100 blast)
          \<comment> \<open>Uniqueness: if x interior to A' \\<noteq> A, then x \\<in> A \\<inter> A' \\<subseteq> endpoints(A). Contradiction.\<close>
          have "\<forall>A'. A' \<in> NT \<and> x \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A') \<longrightarrow> A' = A"
          proof (intro allI impI)
            fix A' assume "A' \<in> NT \<and> x \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
            hence hA': "A' \<in> \<A>" "x \<in> A'" using hNT_def by (by100 blast)+
            show "A' = A"
            proof (rule ccontr)
              assume "A' \<noteq> A"
              have "x \<in> A \<inter> A'" using hA(2) hA'(2) by (by100 blast)
              from h\<A>_inter[rule_format, OF hA(1) hA'(1) \<open>A' \<noteq> A\<close>[symmetric]]
              have "x \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                using \<open>x \<in> A \<inter> A'\<close> by (by100 blast)
              thus False using \<open>x \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
            qed
          qed
          thus ?thesis using \<open>A \<in> NT\<close> hx_int by (by100 blast)
        qed
      qed
      \<comment> \<open>Define r: side-aware retraction (hA\\_choice, tA, hhA lifted before obtain).\<close>
      define r where "r \<equiv> \<lambda>x. if x \<in> T then x else
        (let A = THE A. A \<in> NT \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A) in
         let h = hA_choice A in
         let sx = inv_into top1_unit_interval h x in
         if sx < tA A then h 0 else h 1)"
      \<comment> \<open>Step 3: r fixes T.\<close>
      have hr_T_loc: "\<forall>a\<in>T. r a = a" unfolding r_def by (by100 simp)
      \<comment> \<open>Step 4: r maps Y to T.\<close>
      have hr_img_loc: "\<forall>x\<in>?Y. r x \<in> T"
      proof (intro ballI)
        fix x assume "x \<in> ?Y"
        show "r x \<in> T"
        proof (cases "x \<in> T")
          case True thus ?thesis unfolding r_def by (by100 simp)
        next
          case False
          hence "x \<notin> T" .
          \<comment> \<open>x \\<notin> T, x \\<in> Y \\<subseteq> X. x is interior to some non-tree arc A.\<close>
          have "x \<in> X" using \<open>x \<in> ?Y\<close> hY_sub by (by100 blast)
          hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
          then obtain A where "A \<in> \<A>" "x \<in> A" by (by100 blast)
          have "A \<in> NT" using hNT_def \<open>A \<in> \<A>\<close> \<open>x \<in> A\<close> False by (by100 blast)
          have hA_sub: "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
          have hX_s: "is_topology_on_strict X TX" using hgraph unfolding top1_is_graph_on_def by (by100 blast)
          have hX_h: "is_hausdorff_on X TX" using hgraph unfolding top1_is_graph_on_def by (by100 blast)
          from hhA[OF \<open>A \<in> NT\<close>]
          have hhA_A: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
              A (subspace_topology X TX A) (hA_choice A)" .
          from arc_endpoints_are_boundary[OF hX_s hX_h hA_sub _ hhA_A]
          have hep: "top1_arc_endpoints_on A (subspace_topology X TX A) = {hA_choice A 0, hA_choice A 1}"
            using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
          have "hA_choice A 0 \<in> T" using hvertices_T[rule_format, OF \<open>A \<in> \<A>\<close>] hep by (by100 simp)
          have "hA_choice A 1 \<in> T" using hvertices_T[rule_format, OF \<open>A \<in> \<A>\<close>] hep by (by100 simp)
          \<comment> \<open>r(x) is one of the two T-endpoints.\<close>
          have "x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hvertices_T[rule_format, OF \<open>A \<in> \<A>\<close>] False by (by100 blast)
          hence "x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
            using \<open>x \<in> A\<close> by (by100 blast)
          have hA_unique: "(THE A. A \<in> NT \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = A"
          proof (rule the_equality)
            show "A \<in> NT \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
              using \<open>A \<in> NT\<close> \<open>x \<in> A - _\<close> by (by100 blast)
          next
            fix A' assume "A' \<in> NT \<and> x \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
            hence "A' \<in> \<A>" "x \<in> A'" using hNT_def by (by100 blast)+
            show "A' = A"
            proof (rule ccontr)
              assume "A' \<noteq> A"
              have "x \<in> A \<inter> A'" using \<open>x \<in> A\<close> \<open>x \<in> A'\<close> by (by100 blast)
              from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> A\<close>[symmetric]]
              have "x \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                using \<open>x \<in> A \<inter> A'\<close> by (by100 blast)
              thus False using \<open>x \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
            qed
          qed
          \<comment> \<open>r(x) = hA(0) or hA(1), both in T.\<close>
          have "r x = (if inv_into top1_unit_interval (hA_choice A) x < tA A
             then hA_choice A 0 else hA_choice A 1)"
            unfolding r_def Let_def using False hA_unique by (by100 simp)
          thus "r x \<in> T" using \<open>hA_choice A 0 \<in> T\<close> \<open>hA_choice A 1 \<in> T\<close> by (by100 auto)
        qed
      qed
      \<comment> \<open>Step 5: r is continuous (pasting\\_lemma\\_two\\_closed).\<close>
      \<comment> \<open>Retraction r is continuous. Proof via pasting\\_lemma\\_two\\_closed:
         Y = T \\<union> B where B = union of half-arcs (non-tree parts of Y).
         T closed in Y, B closed in Y. r|T = identity (continuous).
         r|B = piecewise constant per half-arc (continuous). Apply pasting.\<close>
      define B where "B = \<Union>{A \<inter> ?Y | A. A \<in> NT}"
      have hY_eq: "?Y = T \<union> B"
      proof
        show "T \<union> B \<subseteq> ?Y"
        proof -
          have "T \<subseteq> ?Y" using hT_sub_Y .
          moreover have "B \<subseteq> ?Y" unfolding B_def by (by100 blast)
          ultimately show ?thesis by (by100 blast)
        qed
      next
        show "?Y \<subseteq> T \<union> B"
        proof (intro subsetI)
          fix x assume "x \<in> ?Y"
          hence "x \<in> X" using hY_sub by (by100 blast)
          hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
          then obtain A where "A \<in> \<A>" "x \<in> A" by (by100 blast)
          show "x \<in> T \<union> B"
          proof (cases "A \<subseteq> T")
            case True thus ?thesis using \<open>x \<in> A\<close> by (by100 blast)
          next
            case False
            hence "A \<in> NT" using hNT_def \<open>A \<in> \<A>\<close> by (by100 blast)
            hence "A \<inter> ?Y \<in> {A \<inter> ?Y | A. A \<in> NT}" by (by100 blast)
            hence "x \<in> B" unfolding B_def using \<open>x \<in> A\<close> \<open>x \<in> ?Y\<close> by (by100 blast)
            thus ?thesis by (by100 blast)
          qed
        qed
      qed
      have hT_closed_X: "closedin_on X TX T"
      proof -
        \<comment> \<open>Use the coherent topology (hcoh\\_A) for our \\<A>.\<close>
        have hT_per_arc: "\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> T)"
        proof (intro ballI)
          fix Ag assume "Ag \<in> \<A>"
          have "Ag \<subseteq> X" using h\<A> \<open>Ag \<in> \<A>\<close> by (by100 blast)
          show "closedin_on Ag (subspace_topology X TX Ag) (Ag \<inter> T)"
          proof (cases "Ag \<subseteq> T")
            case True
            hence "Ag \<inter> T = Ag" by (by100 blast)
            moreover have "closedin_on Ag (subspace_topology X TX Ag) Ag"
              by (rule closedin_carrier[OF subspace_topology_is_topology_on[OF hX_top \<open>Ag \<subseteq> X\<close>]])
            ultimately show ?thesis by (by100 simp)
          next
            case False
            \<comment> \<open>Ag \\<nsubseteq> T. From hT\\_subgraph: Ag \\<cap> T \\<subseteq> endpoints(Ag).
               Endpoints = at most 2 points. Finite subset of Hausdorff = closed.\<close>
            from hT_subgraph[rule_format, OF \<open>Ag \<in> \<A>\<close>] False
            have "Ag \<inter> T \<subseteq> top1_arc_endpoints_on Ag (subspace_topology X TX Ag)" by (by100 blast)
            \<comment> \<open>Endpoints are at most 2 points, hence finite.\<close>
            have "finite (top1_arc_endpoints_on Ag (subspace_topology X TX Ag))"
            proof -
              have "top1_is_arc_on Ag (subspace_topology X TX Ag)" using h\<A> \<open>Ag \<in> \<A>\<close> by (by100 blast)
              then obtain h where "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                  Ag (subspace_topology X TX Ag) h" unfolding top1_is_arc_on_def by (by100 blast)
              have hAg_strict: "is_topology_on_strict Ag (subspace_topology X TX Ag)"
                using \<open>top1_is_arc_on Ag _\<close> unfolding top1_is_arc_on_def by (by100 blast)
              have hX_haus: "is_hausdorff_on X TX"
                using hgraph unfolding top1_is_graph_on_def by (by100 blast)
              have hAg_haus: "is_hausdorff_on Ag (subspace_topology X TX Ag)"
                using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>Ag \<subseteq> X\<close> hX_haus by (by100 blast)
              from arc_endpoints_are_boundary[OF hX_strict hX_haus \<open>Ag \<subseteq> X\<close>
                  \<open>top1_is_arc_on Ag _\<close> \<open>top1_homeomorphism_on _ _ Ag _ h\<close>]
              have "top1_arc_endpoints_on Ag (subspace_topology X TX Ag) = {h 0, h 1}" .
              thus ?thesis by (by100 simp)
            qed
            from finite_subset[OF \<open>Ag \<inter> T \<subseteq> _\<close>]
            have "finite (Ag \<inter> T)" using \<open>finite (top1_arc_endpoints_on Ag _)\<close> by (by100 blast)
            \<comment> \<open>Ag is Hausdorff (subspace of Hausdorff X). Finite subset of Hausdorff is closed.\<close>
            have hX_haus2: "is_hausdorff_on X TX"
              using hgraph unfolding top1_is_graph_on_def by (by100 blast)
            have "is_hausdorff_on Ag (subspace_topology X TX Ag)"
              using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>Ag \<subseteq> X\<close> hX_haus2 by (by100 blast)
            have "Ag \<inter> T \<subseteq> Ag" by (by100 blast)
            show ?thesis
              by (rule Theorem_17_8[OF \<open>is_hausdorff_on Ag _\<close> \<open>finite (Ag \<inter> T)\<close> \<open>Ag \<inter> T \<subseteq> Ag\<close>])
          qed
        qed
        show ?thesis using hcoh_A[rule_format, OF hT_sub] hT_per_arc by (by100 blast)
      qed
      have hT_closed_Y: "closedin_on ?Y ?TY T"
      proof -
        from Theorem_17_2[OF hX_top hY_sub, of T]
        have "closedin_on ?Y ?TY T \<longleftrightarrow> (\<exists>C. closedin_on X TX C \<and> T = C \<inter> ?Y)" .
        moreover have "T = T \<inter> ?Y" using hT_sub_Y by (by100 blast)
        ultimately show ?thesis using hT_closed_X by (by100 blast)
      qed
      \<comment> \<open>Each A \\<in> NT is closed in X (arc = compact in Hausdorff).\<close>
      have hA_closed_X: "\<forall>A\<in>NT. closedin_on X TX A"
        proof (intro ballI)
          fix A assume "A \<in> NT"
          hence "A \<in> \<A>" using hNT_def by (by100 blast)
          hence "A \<subseteq> X" "top1_is_arc_on A (subspace_topology X TX A)" using h\<A> by (by100 blast)+
          \<comment> \<open>Arc = homeomorphic image of compact [0,1] = compact. Compact in Hausdorff = closed.\<close>
          then obtain h0 where hh0: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
              A (subspace_topology X TX A) h0" unfolding top1_is_arc_on_def by (by100 blast)
          \<comment> \<open>[0,1] is compact with I\\_top (from closed\\_interval\\_compact + coarser topology).\<close>
          have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
          proof -
            have hCI_compact: "top1_compact_on (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1)"
              by (rule top1_closed_interval_compact) (by100 linarith)
            have hCI_eq: "top1_closed_interval 0 1 = top1_unit_interval"
              unfolding top1_closed_interval_def top1_unit_interval_def by (by100 auto)
            have hIT_sub: "top1_unit_interval_topology \<subseteq> top1_closed_interval_topology 0 1"
              by (rule I_top_sub_closed_interval_top)
            have hIT_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
              by (rule top1_unit_interval_topology_is_topology_on)
            show ?thesis unfolding top1_compact_on_def
            proof (intro conjI allI impI)
              show "is_topology_on top1_unit_interval top1_unit_interval_topology" by (rule hIT_top)
            next
              fix Uc assume "Uc \<subseteq> top1_unit_interval_topology \<and> top1_unit_interval \<subseteq> \<Union>Uc"
              hence hUc: "Uc \<subseteq> top1_unit_interval_topology" "top1_unit_interval \<subseteq> \<Union>Uc"
                by (by100 blast)+
              have "Uc \<subseteq> top1_closed_interval_topology 0 1" using hUc(1) hIT_sub by (by100 blast)
              moreover have "top1_closed_interval 0 1 \<subseteq> \<Union>Uc" using hUc(2) hCI_eq by (by100 simp)
              ultimately have "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> top1_closed_interval 0 1 \<subseteq> \<Union>F"
                using hCI_compact unfolding top1_compact_on_def by (by100 blast)
              thus "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> top1_unit_interval \<subseteq> \<Union>F" using hCI_eq by (by100 simp)
            qed
          qed
          \<comment> \<open>h0 continuous I \\<rightarrow> A (from homeomorphism).\<close>
          have hh0_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              A (subspace_topology X TX A) h0"
            using hh0 unfolding top1_homeomorphism_on_def by (by100 blast)
          have hTA_top: "is_topology_on A (subspace_topology X TX A)"
            by (rule subspace_topology_is_topology_on[OF hX_top \<open>A \<subseteq> X\<close>])
          \<comment> \<open>Image of compact under continuous map is compact.\<close>
          from top1_compact_on_continuous_image[OF hI_compact hTA_top hh0_cont]
          have hA_img_compact: "top1_compact_on (h0 ` top1_unit_interval)
              (subspace_topology A (subspace_topology X TX A) (h0 ` top1_unit_interval))" .
          have hh0_surj: "h0 ` top1_unit_interval = A"
            using hh0 unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
          have "subspace_topology A (subspace_topology X TX A) A = subspace_topology X TX A"
          proof (rule subspace_topology_self)
            show "\<forall>U\<in>subspace_topology X TX A. U \<subseteq> A"
            proof (intro ballI)
              fix U assume "U \<in> subspace_topology X TX A"
              then obtain V where "V \<in> TX" "U = A \<inter> V" unfolding subspace_topology_def by (by100 blast)
              thus "U \<subseteq> A" by (by100 blast)
            qed
          qed
          hence "top1_compact_on A (subspace_topology X TX A)"
            using hA_img_compact hh0_surj by (by100 simp)
          have "is_hausdorff_on X TX"
            using hgraph unfolding top1_is_graph_on_def by (by100 blast)
          thus "closedin_on X TX A"
            by (rule compact_in_strict_hausdorff_closedin_on[OF _ hX_strict \<open>A \<subseteq> X\<close>
                \<open>top1_compact_on A (subspace_topology X TX A)\<close>])
        qed
      \<comment> \<open>A \\<cap> Y closed in Y for each A \\<in> NT.\<close>
      have hAY_closed: "\<forall>A\<in>NT. closedin_on ?Y ?TY (A \<inter> ?Y)"
      proof (intro ballI)
        fix A assume "A \<in> NT"
        from Theorem_17_2[OF hX_top hY_sub, of "A \<inter> ?Y"]
        have "closedin_on ?Y ?TY (A \<inter> ?Y) \<longleftrightarrow> (\<exists>C. closedin_on X TX C \<and> A \<inter> ?Y = C \<inter> ?Y)" .
        moreover have "A \<inter> ?Y = A \<inter> ?Y" by (by100 blast)
        moreover have "closedin_on X TX A" using hA_closed_X \<open>A \<in> NT\<close> by (by100 blast)
        ultimately show "closedin_on ?Y ?TY (A \<inter> ?Y)" by (by100 blast)
      qed
      have hB_closed_Y: "closedin_on ?Y ?TY B"
      proof -
        have "B = (\<Union>A\<in>NT. A \<inter> ?Y)" unfolding B_def by (by100 blast)
        moreover have "closedin_on ?Y ?TY (\<Union>A\<in>NT. A \<inter> ?Y)"
          by (rule closedin_on_finite_indexed_Union[OF hTY_top hNT_fin])
             (use hAY_closed in \<open>by100 blast\<close>)
        ultimately show ?thesis by (by100 simp)
      qed
      have hr_img_Y: "\<forall>x\<in>?Y. r x \<in> ?Y"
        using hr_img_loc hT_sub_Y by (by100 blast)
      have hr_T_cont: "top1_continuous_map_on T (subspace_topology ?Y ?TY T) ?Y ?TY r"
      proof -
        have hTT: "is_topology_on T (subspace_topology ?Y ?TY T)"
          by (rule subspace_topology_is_topology_on[OF hTY_top hT_sub_Y])
        have hr_T_img: "\<forall>a\<in>T. r a \<in> ?Y"
        proof (intro ballI)
          fix a assume "a \<in> T"
          hence "r a = a" using hr_T_loc by (by100 auto)
          moreover have "a \<in> ?Y" using \<open>a \<in> T\<close> hT_sub_Y by (by100 blast)
          ultimately show "r a \<in> ?Y" by (by100 simp)
        qed
        have hr_T_preimg: "\<forall>V\<in>?TY. {a \<in> T. r a \<in> V} \<in> subspace_topology ?Y ?TY T"
        proof (intro ballI)
          fix V assume "V \<in> ?TY"
          have "{a \<in> T. r a \<in> V} = T \<inter> V"
          proof (rule set_eqI, rule iffI)
            fix a assume "a \<in> {a \<in> T. r a \<in> V}"
            hence "a \<in> T" "r a \<in> V" by (by100 blast)+
            hence "a \<in> V" using hr_T_loc by (by100 auto)
            thus "a \<in> T \<inter> V" using \<open>a \<in> T\<close> by (by100 blast)
          next
            fix a assume "a \<in> T \<inter> V"
            hence "a \<in> T" "a \<in> V" by (by100 blast)+
            hence "r a = a" using hr_T_loc by (by100 auto)
            hence "r a \<in> V" using \<open>a \<in> V\<close> by (by100 simp)
            thus "a \<in> {a \<in> T. r a \<in> V}" using \<open>a \<in> T\<close> by (by100 blast)
          qed
          moreover have "T \<inter> V \<in> subspace_topology ?Y ?TY T"
          proof -
            have "T \<inter> V = T \<inter> V" by (by100 blast)
            moreover have "V \<in> ?TY" using \<open>V \<in> ?TY\<close> .
            ultimately show ?thesis unfolding subspace_topology_def by (by100 auto)
          qed
          ultimately show "{a \<in> T. r a \<in> V} \<in> subspace_topology ?Y ?TY T" by (by100 simp)
        qed
        show ?thesis unfolding top1_continuous_map_on_def
          using hTT hTY_top hr_T_img hr_T_preimg by (by100 blast)
      qed
      have hAY_closed_B: "\<forall>A\<in>NT. closedin_on B (subspace_topology ?Y ?TY B) (A \<inter> ?Y)"
      proof (intro ballI)
        fix A assume "A \<in> NT"
        have hAY_sub_B: "A \<inter> ?Y \<subseteq> B" unfolding B_def using \<open>A \<in> NT\<close> by (by100 blast)
        have hB_sub_Y: "B \<subseteq> ?Y" unfolding B_def by (by100 blast)
        from Theorem_17_2[OF hTY_top hB_sub_Y, of "A \<inter> ?Y"]
        have "closedin_on B (subspace_topology ?Y ?TY B) (A \<inter> ?Y) \<longleftrightarrow>
            (\<exists>C. closedin_on ?Y ?TY C \<and> A \<inter> ?Y = C \<inter> B)" .
        moreover have "A \<inter> ?Y = (A \<inter> ?Y) \<inter> B" using hAY_sub_B by (by100 blast)
        moreover have "closedin_on ?Y ?TY (A \<inter> ?Y)" using hAY_closed \<open>A \<in> NT\<close> by (by100 blast)
        ultimately show "closedin_on B (subspace_topology ?Y ?TY B) (A \<inter> ?Y)" by (by100 blast)
      qed
      \<comment> \<open>r|B continuous. Strategy: r has finite image (endpoints of NT arcs).
         For any open V, complement of preimage = finite union of half-arcs = closed.
         Hence preimage is open.\<close>
      \<comment> \<open>Half-arcs LA, RA already defined before obtain r.\<close>
      \<comment> \<open>[0,1] compact with I\\_top.\<close>
      have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
      proof -
        have hCI_compact: "top1_compact_on (top1_closed_interval 0 1) (top1_closed_interval_topology 0 1)"
          by (rule top1_closed_interval_compact) (by100 linarith)
        have hCI_eq: "top1_closed_interval 0 1 = top1_unit_interval"
          unfolding top1_closed_interval_def top1_unit_interval_def by (by100 auto)
        have hIT_sub: "top1_unit_interval_topology \<subseteq> top1_closed_interval_topology 0 1"
          by (rule I_top_sub_closed_interval_top)
        have hIT_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
          by (rule top1_unit_interval_topology_is_topology_on)
        show ?thesis unfolding top1_compact_on_def
        proof (intro conjI allI impI)
          show "is_topology_on top1_unit_interval top1_unit_interval_topology" by (rule hIT_top)
        next
          fix Uc assume "Uc \<subseteq> top1_unit_interval_topology \<and> top1_unit_interval \<subseteq> \<Union>Uc"
          hence hUc: "Uc \<subseteq> top1_unit_interval_topology" "top1_unit_interval \<subseteq> \<Union>Uc"
            by (by100 blast)+
          have "Uc \<subseteq> top1_closed_interval_topology 0 1" using hUc(1) hIT_sub by (by100 blast)
          moreover have "top1_closed_interval 0 1 \<subseteq> \<Union>Uc" using hUc(2) hCI_eq by (by100 simp)
          ultimately have "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> top1_closed_interval 0 1 \<subseteq> \<Union>F"
            using hCI_compact unfolding top1_compact_on_def by (by100 blast)
          thus "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> top1_unit_interval \<subseteq> \<Union>F" using hCI_eq by (by100 simp)
        qed
      qed
      \<comment> \<open>Each half-arc is closed in Y (intersection of closed set with Y).\<close>
      have hLA_closed_Y: "\<forall>A\<in>NT. closedin_on ?Y ?TY (LA A)"
      proof (intro ballI)
        fix A assume "A \<in> NT"
        \<comment> \<open>LA(A) \\<subseteq> A \\<cap> Y. A \\<cap> Y closed in Y (from hAY\\_closed). LA(A) closed in A \\<cap> Y.
           Transitivity: closed in closed = closed.\<close>
        have "LA A \<subseteq> A \<inter> ?Y" unfolding LA_def by (by100 blast)
        \<comment> \<open>Show LA(A) is closed in A \\<cap> Y. Complement = RA(A) \\ LA(A) = interior of right half.
           LA = A \\<cap> Y \\<cap> {x. inv \\<le> tA}. A \\<cap> Y is a subspace.
           In A's subspace topology, {x. inv \\<le> tA} = hA([0,tA]) which is closed.\<close>
        have "closedin_on ?Y ?TY (LA A)"
        proof -
          \<comment> \<open>LA(A) = hA([0,tA]) \\<cap> Y. hA([0,tA]) closed in X. Intersection with Y closed in Y.\<close>
          have hA_sub: "A \<subseteq> X" using h\<A> \<open>A \<in> NT\<close> hNT_def by (by100 blast)
          have hhA_A: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
              A (subspace_topology X TX A) (hA_choice A)"
            using hhA \<open>A \<in> NT\<close> by (by100 blast)
          have hbij: "bij_betw (hA_choice A) top1_unit_interval A"
            using hhA_A unfolding top1_homeomorphism_on_def by (by100 blast)
          define hA_left where "hA_left = hA_choice A ` {t \<in> top1_unit_interval. t \<le> tA A}"
          have "LA A = hA_left \<inter> ?Y"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> LA A"
            hence "x \<in> A \<inter> ?Y" "inv_into top1_unit_interval (hA_choice A) x \<le> tA A"
              unfolding LA_def by (by100 blast)+
            have "x \<in> hA_choice A ` top1_unit_interval"
              using \<open>x \<in> A \<inter> ?Y\<close> hbij unfolding bij_betw_def by (by100 blast)
            have hinv_I: "inv_into top1_unit_interval (hA_choice A) x \<in> top1_unit_interval"
              by (rule inv_into_into[OF \<open>x \<in> hA_choice A ` top1_unit_interval\<close>])
            have "inv_into top1_unit_interval (hA_choice A) x \<in> {t \<in> top1_unit_interval. t \<le> tA A}"
              using hinv_I \<open>inv_into _ _ x \<le> tA A\<close> by (by100 blast)
            have "hA_choice A (inv_into top1_unit_interval (hA_choice A) x) = x"
              by (rule f_inv_into_f[OF \<open>x \<in> hA_choice A ` top1_unit_interval\<close>])
            hence "x \<in> hA_left"
            proof -
              have "x = hA_choice A (inv_into top1_unit_interval (hA_choice A) x)"
                using \<open>hA_choice A (inv_into top1_unit_interval (hA_choice A) x) = x\<close> by (by100 simp)
              thus ?thesis unfolding hA_left_def
                using \<open>inv_into _ _ x \<in> {t \<in> top1_unit_interval. t \<le> tA A}\<close> by (by100 force)
            qed
            thus "x \<in> hA_left \<inter> ?Y" using \<open>x \<in> A \<inter> ?Y\<close> by (by100 blast)
          next
            fix x assume "x \<in> hA_left \<inter> ?Y"
            hence "x \<in> hA_left" "x \<in> ?Y" by (by100 blast)+
            from \<open>x \<in> hA_left\<close> obtain t where "t \<in> top1_unit_interval" "t \<le> tA A" "x = hA_choice A t"
              unfolding hA_left_def by (by100 blast)
            have "x \<in> A" using \<open>x = hA_choice A t\<close> \<open>t \<in> top1_unit_interval\<close> hbij
              unfolding bij_betw_def by (by100 blast)
            have hinj: "inj_on (hA_choice A) top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
            have "inv_into top1_unit_interval (hA_choice A) x = t"
              using inv_into_f_f[OF hinj \<open>t \<in> top1_unit_interval\<close>] \<open>x = hA_choice A t\<close> by (by100 simp)
            hence "inv_into top1_unit_interval (hA_choice A) x \<le> tA A" using \<open>t \<le> tA A\<close> by (by100 simp)
            thus "x \<in> LA A" unfolding LA_def using \<open>x \<in> A\<close> \<open>x \<in> ?Y\<close> by (by100 blast)
          qed
          moreover have "closedin_on X TX hA_left"
          proof -
            \<comment> \<open>hA\\_left closed in A (closed map of compact to Hausdorff). A closed in X. Theorem\\_17\\_3.\<close>
            note hI_compact_loc = hI_compact
            have hA_haus: "is_hausdorff_on A (subspace_topology X TX A)"
            proof -
              have "is_hausdorff_on X TX"
                using hgraph unfolding top1_is_graph_on_def by (by100 blast)
              from conjunct2[OF conjunct2[OF Theorem_17_11]] hA_sub this
              show ?thesis by (by100 blast)
            qed
            have hh_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                A (subspace_topology X TX A) (hA_choice A)"
              using hhA_A unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>{t \\<in> I. t \\<le> tA} closed in I.\<close>
            have hC_closed: "closedin_on top1_unit_interval top1_unit_interval_topology
                {t \<in> top1_unit_interval. t \<le> tA A}"
            proof -
              \<comment> \<open>Complement = {t \\<in> I : t > tA} = I \\<cap> (tA, \\<infinity>). (tA,\\<infinity>) open in R.\<close>
              have "top1_unit_interval - {t \<in> top1_unit_interval. t \<le> tA A}
                  = {t \<in> top1_unit_interval. t > tA A}" by (by100 auto)
              moreover have "{t \<in> top1_unit_interval. t > tA A} \<in> top1_unit_interval_topology"
              proof -
                have "I_top = subspace_topology (UNIV :: real set) top1_open_sets I_set"
                  unfolding top1_unit_interval_topology_def top1_unit_interval_def
                    subspace_topology_def by (by100 auto)
                have "{x :: real. tA A < x} \<in> top1_open_sets"
                proof -
                  have "open {x :: real. tA A < x}" using open_greaterThan
                    unfolding greaterThan_def by (by100 blast)
                  thus ?thesis unfolding top1_open_sets_def by (by100 blast)
                qed
                have "{t \<in> top1_unit_interval. t > tA A} = top1_unit_interval \<inter> {x. tA A < x}"
                  by (by100 auto)
                thus ?thesis
                  using \<open>I_top = _\<close> \<open>{x. tA A < x} \<in> top1_open_sets\<close>
                  unfolding subspace_topology_def by (by100 auto)
              qed
              ultimately have "top1_unit_interval - {t \<in> top1_unit_interval. t \<le> tA A}
                  \<in> top1_unit_interval_topology" by (by100 simp)
              moreover have "{t \<in> top1_unit_interval. t \<le> tA A} \<subseteq> top1_unit_interval" by (by100 blast)
              ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
            qed
            from compact_hausdorff_continuous_closed_map[OF hI_compact_loc hA_haus hh_cont hC_closed]
            have "closedin_on A (subspace_topology X TX A) hA_left"
              unfolding hA_left_def by (by100 simp)
            have "closedin_on X TX A" using hA_closed_X \<open>A \<in> NT\<close> by (by100 blast)
            from Theorem_17_3[OF hX_top \<open>closedin_on X TX A\<close>
                \<open>closedin_on A (subspace_topology X TX A) hA_left\<close>]
            show "closedin_on X TX hA_left" .
          qed
          moreover have "closedin_on ?Y ?TY (hA_left \<inter> ?Y)"
          proof -
            from Theorem_17_2[OF hX_top hY_sub, of "hA_left \<inter> ?Y"]
            have "closedin_on ?Y ?TY (hA_left \<inter> ?Y) \<longleftrightarrow>
                (\<exists>C. closedin_on X TX C \<and> hA_left \<inter> ?Y = C \<inter> ?Y)" .
            moreover have "hA_left \<inter> ?Y = hA_left \<inter> ?Y" by (by100 blast)
            ultimately show ?thesis using \<open>closedin_on X TX hA_left\<close> by (by100 blast)
          qed
          ultimately show "closedin_on ?Y ?TY (LA A)" by (by100 simp)
        qed
        thus "closedin_on ?Y ?TY (LA A)" .
      qed
      have hRA_closed_Y: "\<forall>A\<in>NT. closedin_on ?Y ?TY (RA A)"
      proof (intro ballI)
        fix A assume "A \<in> NT"
        have "closedin_on ?Y ?TY (RA A)"
        proof -
          have hA_sub: "A \<subseteq> X" using h\<A> \<open>A \<in> NT\<close> hNT_def by (by100 blast)
          have hhA_A: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
              A (subspace_topology X TX A) (hA_choice A)"
            using hhA \<open>A \<in> NT\<close> by (by100 blast)
          have hbij: "bij_betw (hA_choice A) top1_unit_interval A"
            using hhA_A unfolding top1_homeomorphism_on_def by (by100 blast)
          define hA_right where "hA_right = hA_choice A ` {t \<in> top1_unit_interval. t \<ge> tA A}"
          have "RA A = hA_right \<inter> ?Y"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> RA A"
            hence "x \<in> A \<inter> ?Y" "inv_into top1_unit_interval (hA_choice A) x \<ge> tA A"
              unfolding RA_def by (by100 blast)+
            have "x \<in> hA_choice A ` top1_unit_interval"
              using \<open>x \<in> A \<inter> ?Y\<close> hbij unfolding bij_betw_def by (by100 blast)
            have hinv_I: "inv_into top1_unit_interval (hA_choice A) x \<in> top1_unit_interval"
              by (rule inv_into_into[OF \<open>x \<in> hA_choice A ` top1_unit_interval\<close>])
            have "hA_choice A (inv_into top1_unit_interval (hA_choice A) x) = x"
              by (rule f_inv_into_f[OF \<open>x \<in> hA_choice A ` top1_unit_interval\<close>])
            have "x = hA_choice A (inv_into top1_unit_interval (hA_choice A) x)"
              using \<open>hA_choice A (inv_into top1_unit_interval (hA_choice A) x) = x\<close> by (by100 simp)
            hence "x \<in> hA_right" unfolding hA_right_def
              using hinv_I \<open>inv_into _ _ x \<ge> tA A\<close> by (by100 force)
            thus "x \<in> hA_right \<inter> ?Y" using \<open>x \<in> A \<inter> ?Y\<close> by (by100 blast)
          next
            fix x assume "x \<in> hA_right \<inter> ?Y"
            hence "x \<in> hA_right" "x \<in> ?Y" by (by100 blast)+
            from \<open>x \<in> hA_right\<close> obtain t where "t \<in> top1_unit_interval" "t \<ge> tA A" "x = hA_choice A t"
              unfolding hA_right_def by (by100 blast)
            have "x \<in> A" using \<open>x = hA_choice A t\<close> \<open>t \<in> top1_unit_interval\<close> hbij
              unfolding bij_betw_def by (by100 blast)
            have hinj: "inj_on (hA_choice A) top1_unit_interval" using hbij unfolding bij_betw_def by (by100 blast)
            have "inv_into top1_unit_interval (hA_choice A) x = t"
              using inv_into_f_f[OF hinj \<open>t \<in> top1_unit_interval\<close>] \<open>x = hA_choice A t\<close> by (by100 simp)
            hence "inv_into top1_unit_interval (hA_choice A) x \<ge> tA A" using \<open>t \<ge> tA A\<close> by (by100 simp)
            thus "x \<in> RA A" unfolding RA_def using \<open>x \<in> A\<close> \<open>x \<in> ?Y\<close> by (by100 blast)
          qed
          moreover have "closedin_on X TX hA_right"
          proof -
            have hA_haus: "is_hausdorff_on A (subspace_topology X TX A)"
            proof -
              have "is_hausdorff_on X TX"
                using hgraph unfolding top1_is_graph_on_def by (by100 blast)
              from conjunct2[OF conjunct2[OF Theorem_17_11]] hA_sub this
              show ?thesis by (by100 blast)
            qed
            have hh_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                A (subspace_topology X TX A) (hA_choice A)"
              using hhA_A unfolding top1_homeomorphism_on_def by (by100 blast)
            have hC_closed: "closedin_on top1_unit_interval top1_unit_interval_topology
                {t \<in> top1_unit_interval. t \<ge> tA A}"
            proof -
              have "top1_unit_interval - {t \<in> top1_unit_interval. t \<ge> tA A}
                  = {t \<in> top1_unit_interval. t < tA A}" by (by100 auto)
              moreover have "{t \<in> top1_unit_interval. t < tA A} \<in> top1_unit_interval_topology"
              proof -
                have "I_top = subspace_topology (UNIV :: real set) top1_open_sets I_set"
                  unfolding top1_unit_interval_topology_def top1_unit_interval_def
                    subspace_topology_def by (by100 auto)
                have "{x :: real. x < tA A} \<in> top1_open_sets"
                proof -
                  have "open {x :: real. x < tA A}" using open_lessThan
                    unfolding lessThan_def by (by100 blast)
                  thus ?thesis unfolding top1_open_sets_def by (by100 blast)
                qed
                have "{t \<in> top1_unit_interval. t < tA A} = top1_unit_interval \<inter> {x. x < tA A}"
                  by (by100 auto)
                thus ?thesis
                  using \<open>I_top = _\<close> \<open>{x. x < tA A} \<in> top1_open_sets\<close>
                  unfolding subspace_topology_def by (by100 auto)
              qed
              ultimately have "top1_unit_interval - {t \<in> top1_unit_interval. t \<ge> tA A}
                  \<in> top1_unit_interval_topology" by (by100 simp)
              moreover have "{t \<in> top1_unit_interval. t \<ge> tA A} \<subseteq> top1_unit_interval" by (by100 blast)
              ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
            qed
            from compact_hausdorff_continuous_closed_map[OF hI_compact hA_haus hh_cont hC_closed]
            have "closedin_on A (subspace_topology X TX A) hA_right"
              unfolding hA_right_def by (by100 simp)
            have "closedin_on X TX A" using hA_closed_X \<open>A \<in> NT\<close> by (by100 blast)
            from Theorem_17_3[OF hX_top \<open>closedin_on X TX A\<close>
                \<open>closedin_on A (subspace_topology X TX A) hA_right\<close>]
            show "closedin_on X TX hA_right" .
          qed
          moreover have "closedin_on ?Y ?TY (hA_right \<inter> ?Y)"
          proof -
            from Theorem_17_2[OF hX_top hY_sub, of "hA_right \<inter> ?Y"]
            have "closedin_on ?Y ?TY (hA_right \<inter> ?Y) \<longleftrightarrow>
                (\<exists>C. closedin_on X TX C \<and> hA_right \<inter> ?Y = C \<inter> ?Y)" .
            moreover have "hA_right \<inter> ?Y = hA_right \<inter> ?Y" by (by100 blast)
            ultimately show ?thesis using \<open>closedin_on X TX hA_right\<close> by (by100 blast)
          qed
          ultimately show "closedin_on ?Y ?TY (RA A)" by (by100 simp)
        qed
        thus "closedin_on ?Y ?TY (RA A)" .
      qed
      \<comment> \<open>Half-arcs are closed in B (from closed in Y + B \\<subseteq> Y).\<close>
      have hLA_closed_B: "\<forall>A\<in>NT. closedin_on B (subspace_topology ?Y ?TY B) (LA A)"
      proof (intro ballI)
        fix A assume "A \<in> NT"
        have "LA A \<subseteq> B" unfolding LA_def B_def using \<open>A \<in> NT\<close> by (by100 blast)
        have hB_sub_Y: "B \<subseteq> ?Y" unfolding B_def by (by100 blast)
        from Theorem_17_2[OF hTY_top hB_sub_Y, of "LA A"]
        have "closedin_on B (subspace_topology ?Y ?TY B) (LA A) \<longleftrightarrow>
            (\<exists>C. closedin_on ?Y ?TY C \<and> LA A = C \<inter> B)" .
        moreover have "LA A = LA A \<inter> B" using \<open>LA A \<subseteq> B\<close> by (by100 blast)
        moreover have "closedin_on ?Y ?TY (LA A)" using hLA_closed_Y \<open>A \<in> NT\<close> by (by100 blast)
        ultimately show "closedin_on B (subspace_topology ?Y ?TY B) (LA A)" by (by100 blast)
      qed
      have hRA_closed_B: "\<forall>A\<in>NT. closedin_on B (subspace_topology ?Y ?TY B) (RA A)"
      proof (intro ballI)
        fix A assume "A \<in> NT"
        have "RA A \<subseteq> B" unfolding RA_def B_def using \<open>A \<in> NT\<close> by (by100 blast)
        have hB_sub_Y: "B \<subseteq> ?Y" unfolding B_def by (by100 blast)
        from Theorem_17_2[OF hTY_top hB_sub_Y, of "RA A"]
        have "closedin_on B (subspace_topology ?Y ?TY B) (RA A) \<longleftrightarrow>
            (\<exists>C. closedin_on ?Y ?TY C \<and> RA A = C \<inter> B)" .
        moreover have "RA A = RA A \<inter> B" using \<open>RA A \<subseteq> B\<close> by (by100 blast)
        moreover have "closedin_on ?Y ?TY (RA A)" using hRA_closed_Y \<open>A \<in> NT\<close> by (by100 blast)
        ultimately show "closedin_on B (subspace_topology ?Y ?TY B) (RA A)" by (by100 blast)
      qed
      \<comment> \<open>r maps each LA to hA(0) and each RA to hA(1).\<close>
      have hr_LA: "\<forall>A\<in>NT. \<forall>x\<in>LA A. r x = hA_choice A 0"
      proof (intro ballI)
        fix A x assume "A \<in> NT" "x \<in> LA A"
        hence "x \<in> A \<inter> ?Y" and hinv_le: "inv_into top1_unit_interval (hA_choice A) x \<le> tA A"
          unfolding LA_def by (by100 blast)+
        show "r x = hA_choice A 0"
        proof (cases "x \<in> T")
          case True
          \<comment> \<open>x \\<in> T: r(x) = x. x is an endpoint of A in T. Since x \\<in> LA, x = hA(0).\<close>
          have "r x = x" using hr_T_loc True by (by100 auto)
          moreover have "x = hA_choice A 0"
          proof -
            \<comment> \<open>x \\<in> T \\<cap> A. From hT\\_subgraph: x is an endpoint of A.\<close>
            have "A \<in> \<A>" using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
            from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>]
            have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
              using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
            hence "x \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
              using True \<open>x \<in> A \<inter> ?Y\<close> by (by100 blast)
            from hhA[OF \<open>A \<in> NT\<close>]
            have hhA_A: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                A (subspace_topology X TX A) (hA_choice A)" .
            have hA_sub: "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
            have hX_haus_loc: "is_hausdorff_on X TX"
              using hgraph unfolding top1_is_graph_on_def by (by100 blast)
            have hA_arc: "top1_is_arc_on A (subspace_topology X TX A)"
              using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
            from arc_endpoints_are_boundary[OF hX_strict hX_haus_loc hA_sub hA_arc hhA_A]
            have hep: "top1_arc_endpoints_on A (subspace_topology X TX A) = {hA_choice A 0, hA_choice A 1}" .
            hence "x = hA_choice A 0 \<or> x = hA_choice A 1"
              using \<open>x \<in> top1_arc_endpoints_on A _\<close> by (by100 auto)
            moreover have "x \<noteq> hA_choice A 1"
            proof
              assume "x = hA_choice A 1"
              \<comment> \<open>Then inv\\_into x = 1 > tA, contradicting inv\\_into \\<le> tA.\<close>
              have hbij: "bij_betw (hA_choice A) top1_unit_interval A"
                using hhA_A unfolding top1_homeomorphism_on_def by (by100 blast)
              have h1_in_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
              have "hA_choice A 1 \<in> A" using hbij h1_in_I unfolding bij_betw_def by (by100 blast)
              have h1_I: "(1::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
              have "inv_into top1_unit_interval (hA_choice A) (hA_choice A 1) = 1"
                using inv_into_f_f[OF _ h1_I] hbij unfolding bij_betw_def by (by100 blast)
              hence "inv_into top1_unit_interval (hA_choice A) x = 1"
                using \<open>x = hA_choice A 1\<close> by (by100 simp)
              moreover have "tA A < 1"
              proof -
                have "ps A \<in> hA_choice A ` top1_unit_interval"
                  using hps[rule_format, OF \<open>A \<in> NT\<close>] hbij unfolding bij_betw_def by (by100 blast)
                have "tA A \<in> top1_unit_interval"
                  unfolding tA_def by (rule inv_into_into[OF \<open>ps A \<in> hA_choice A ` top1_unit_interval\<close>])
                moreover have "tA A \<noteq> 1"
                proof
                  assume "tA A = 1"
                  hence "hA_choice A (tA A) = hA_choice A 1" by (by100 simp)
                  have "hA_choice A (tA A) = ps A"
                    unfolding tA_def
                    by (rule f_inv_into_f[OF \<open>ps A \<in> hA_choice A ` top1_unit_interval\<close>])
                  hence "ps A = hA_choice A 1"
                    using \<open>hA_choice A (tA A) = hA_choice A 1\<close> by (by100 simp)
                  hence "ps A \<in> {hA_choice A 0, hA_choice A 1}" by (by100 blast)
                  hence "ps A \<in> top1_arc_endpoints_on A (subspace_topology X TX A)" using hep by (by100 simp)
                  thus False using hps[rule_format, OF \<open>A \<in> NT\<close>] by (by100 blast)
                qed
                ultimately show ?thesis unfolding top1_unit_interval_def by (by100 auto)
              qed
              ultimately show False using hinv_le by (by100 linarith)
            qed
            ultimately show "x = hA_choice A 0" by (by100 blast)
          qed
          ultimately show ?thesis by (by100 simp)
        next
          case False
          \<comment> \<open>x \\<notin> T: from r definition, r(x) = if inv < tA then hA(0) else hA(1).
             Since x \\<in> Y and ps(A) \\<notin> Y, inv\\_into \\<noteq> tA, so inv < tA.\<close>
          have "x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hvertices_T[rule_format, OF _] False \<open>A \<in> NT\<close> hNT_def by (by100 blast)
          hence hx_int: "x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
            using \<open>x \<in> A \<inter> ?Y\<close> by (by100 blast)
          have hA_unique: "(THE A. A \<in> NT \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = A"
          proof (rule the_equality)
            show "A \<in> NT \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
              using \<open>A \<in> NT\<close> hx_int by (by100 blast)
          next
            fix A' assume "A' \<in> NT \<and> x \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
            hence "A' \<in> \<A>" "x \<in> A'" using hNT_def by (by100 blast)+
            have "A \<in> \<A>" using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
            show "A' = A"
            proof (rule ccontr)
              assume "A' \<noteq> A"
              from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> A\<close>[symmetric]]
              have "x \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                using \<open>x \<in> A \<inter> ?Y\<close> \<open>x \<in> A'\<close> by (by100 blast)
              thus False using \<open>x \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
            qed
          qed
          have "inv_into top1_unit_interval (hA_choice A) x \<noteq> tA A"
          proof
            assume heq: "inv_into top1_unit_interval (hA_choice A) x = tA A"
            have hbij_loc: "bij_betw (hA_choice A) top1_unit_interval A"
              using hhA[OF \<open>A \<in> NT\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
            have "x \<in> hA_choice A ` top1_unit_interval"
              using \<open>x \<in> A \<inter> ?Y\<close> hbij_loc unfolding bij_betw_def by (by100 blast)
            have "hA_choice A (inv_into top1_unit_interval (hA_choice A) x) = x"
              by (rule f_inv_into_f[OF \<open>x \<in> hA_choice A ` top1_unit_interval\<close>])
            hence "hA_choice A (tA A) = x" using heq by (by100 simp)
            have "ps A \<in> hA_choice A ` top1_unit_interval"
              using hps[rule_format, OF \<open>A \<in> NT\<close>] hbij_loc unfolding bij_betw_def by (by100 blast)
            have "hA_choice A (tA A) = ps A"
              unfolding tA_def by (rule f_inv_into_f[OF \<open>ps A \<in> hA_choice A ` top1_unit_interval\<close>])
            hence "x = ps A" using \<open>hA_choice A (tA A) = x\<close> by (by100 simp)
            have "ps A \<in> ps ` NT" using \<open>A \<in> NT\<close> by (by100 blast)
            hence "x \<notin> ?Y" using \<open>x = ps A\<close> by (by100 blast)
            thus False using \<open>x \<in> A \<inter> ?Y\<close> by (by100 blast)
          qed
          hence "inv_into top1_unit_interval (hA_choice A) x < tA A"
            using hinv_le by (by100 linarith)
          thus "r x = hA_choice A 0"
            unfolding r_def Let_def using False hA_unique by (by100 simp)
        qed
      qed
      have hr_RA: "\<forall>A\<in>NT. \<forall>x\<in>RA A. r x = hA_choice A 1"
      proof (intro ballI)
        fix A x assume "A \<in> NT" "x \<in> RA A"
        hence "x \<in> A \<inter> ?Y" and hinv_ge: "inv_into top1_unit_interval (hA_choice A) x \<ge> tA A"
          unfolding RA_def by (by100 blast)+
        show "r x = hA_choice A 1"
        proof (cases "x \<in> T")
          case True
          have "r x = x" using hr_T_loc True by (by100 auto)
          moreover have "x = hA_choice A 1"
          proof -
            have "A \<in> \<A>" using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
            from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>]
            have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
              using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
            hence "x \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
              using True \<open>x \<in> A \<inter> ?Y\<close> by (by100 blast)
            from hhA[OF \<open>A \<in> NT\<close>]
            have hhA_A: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                A (subspace_topology X TX A) (hA_choice A)" .
            have hA_sub: "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
            have hX_haus_loc: "is_hausdorff_on X TX"
              using hgraph unfolding top1_is_graph_on_def by (by100 blast)
            have hA_arc: "top1_is_arc_on A (subspace_topology X TX A)"
              using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
            from arc_endpoints_are_boundary[OF hX_strict hX_haus_loc hA_sub hA_arc hhA_A]
            have hep: "top1_arc_endpoints_on A (subspace_topology X TX A) = {hA_choice A 0, hA_choice A 1}" .
            hence "x = hA_choice A 0 \<or> x = hA_choice A 1"
              using \<open>x \<in> top1_arc_endpoints_on A _\<close> by (by100 auto)
            moreover have "x \<noteq> hA_choice A 0"
            proof
              assume "x = hA_choice A 0"
              have hbij: "bij_betw (hA_choice A) top1_unit_interval A"
                using hhA_A unfolding top1_homeomorphism_on_def by (by100 blast)
              have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 auto)
              have "inv_into top1_unit_interval (hA_choice A) (hA_choice A 0) = 0"
                using inv_into_f_f[OF _ h0_I] hbij unfolding bij_betw_def by (by100 blast)
              hence "inv_into top1_unit_interval (hA_choice A) x = 0"
                using \<open>x = hA_choice A 0\<close> by (by100 simp)
              moreover have "tA A > 0"
              proof -
                have "ps A \<in> hA_choice A ` top1_unit_interval"
                  using hps[rule_format, OF \<open>A \<in> NT\<close>] hbij unfolding bij_betw_def by (by100 blast)
                have "tA A \<in> top1_unit_interval"
                  unfolding tA_def by (rule inv_into_into[OF \<open>ps A \<in> hA_choice A ` top1_unit_interval\<close>])
                moreover have "tA A \<noteq> 0"
                proof
                  assume "tA A = 0"
                  hence "hA_choice A (tA A) = hA_choice A 0" by (by100 simp)
                  have "hA_choice A (tA A) = ps A"
                    unfolding tA_def by (rule f_inv_into_f[OF \<open>ps A \<in> hA_choice A ` top1_unit_interval\<close>])
                  hence "ps A = hA_choice A 0"
                    using \<open>hA_choice A (tA A) = hA_choice A 0\<close> by (by100 simp)
                  hence "ps A \<in> {hA_choice A 0, hA_choice A 1}" by (by100 blast)
                  hence "ps A \<in> top1_arc_endpoints_on A (subspace_topology X TX A)" using hep by (by100 simp)
                  thus False using hps[rule_format, OF \<open>A \<in> NT\<close>] by (by100 blast)
                qed
                ultimately show ?thesis unfolding top1_unit_interval_def by (by100 auto)
              qed
              ultimately show False using hinv_ge by (by100 linarith)
            qed
            ultimately show "x = hA_choice A 1" by (by100 blast)
          qed
          ultimately show ?thesis by (by100 simp)
        next
          case False
          have "x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hvertices_T[rule_format, OF _] False \<open>A \<in> NT\<close> hNT_def by (by100 blast)
          hence hx_int: "x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
            using \<open>x \<in> A \<inter> ?Y\<close> by (by100 blast)
          have hA_unique: "(THE A. A \<in> NT \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = A"
          proof (rule the_equality)
            show "A \<in> NT \<and> x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
              using \<open>A \<in> NT\<close> hx_int by (by100 blast)
          next
            fix A' assume "A' \<in> NT \<and> x \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
            hence "A' \<in> \<A>" "x \<in> A'" using hNT_def by (by100 blast)+
            have "A \<in> \<A>" using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
            show "A' = A"
            proof (rule ccontr)
              assume "A' \<noteq> A"
              from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> A\<close>[symmetric]]
              have "x \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                using \<open>x \<in> A \<inter> ?Y\<close> \<open>x \<in> A'\<close> by (by100 blast)
              thus False using \<open>x \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
            qed
          qed
          have "inv_into top1_unit_interval (hA_choice A) x \<noteq> tA A"
          proof
            assume heq: "inv_into top1_unit_interval (hA_choice A) x = tA A"
            have hbij_loc: "bij_betw (hA_choice A) top1_unit_interval A"
              using hhA[OF \<open>A \<in> NT\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
            have "x \<in> hA_choice A ` top1_unit_interval"
              using \<open>x \<in> A \<inter> ?Y\<close> hbij_loc unfolding bij_betw_def by (by100 blast)
            have "hA_choice A (inv_into top1_unit_interval (hA_choice A) x) = x"
              by (rule f_inv_into_f[OF \<open>x \<in> hA_choice A ` top1_unit_interval\<close>])
            hence "hA_choice A (tA A) = x" using heq by (by100 simp)
            have "ps A \<in> hA_choice A ` top1_unit_interval"
              using hps[rule_format, OF \<open>A \<in> NT\<close>] hbij_loc unfolding bij_betw_def by (by100 blast)
            have "hA_choice A (tA A) = ps A"
              unfolding tA_def by (rule f_inv_into_f[OF \<open>ps A \<in> hA_choice A ` top1_unit_interval\<close>])
            hence "x = ps A" using \<open>hA_choice A (tA A) = x\<close> by (by100 simp)
            have "ps A \<in> ps ` NT" using \<open>A \<in> NT\<close> by (by100 blast)
            hence "x \<notin> ?Y" using \<open>x = ps A\<close> by (by100 blast)
            thus False using \<open>x \<in> A \<inter> ?Y\<close> by (by100 blast)
          qed
          hence "\<not> (inv_into top1_unit_interval (hA_choice A) x < tA A)"
            using hinv_ge by (by100 linarith)
          thus "r x = hA_choice A 1"
            unfolding r_def Let_def using False hA_unique by (by100 simp)
        qed
      qed
      have hr_B_cont: "top1_continuous_map_on B (subspace_topology ?Y ?TY B) ?Y ?TY r"
      proof -
        have hBB: "is_topology_on B (subspace_topology ?Y ?TY B)"
          by (rule subspace_topology_is_topology_on[OF hTY_top])
             (use hY_eq in \<open>by100 blast\<close>)
        have hB_sub_Y: "B \<subseteq> ?Y" unfolding B_def by (by100 blast)
        have hr_B_img: "\<forall>x\<in>B. r x \<in> ?Y" using hr_img_Y hB_sub_Y by (by100 blast)
        have hr_B_preimg: "\<forall>V\<in>?TY. {x \<in> B. r x \<in> V} \<in> subspace_topology ?Y ?TY B"
        proof (intro ballI)
          fix V assume "V \<in> ?TY"
          \<comment> \<open>Complement = union of half-arcs whose r-image misses V.\<close>
          define S where "S = {A \<in> NT. hA_choice A 0 \<notin> V} \<union> {A \<in> NT. hA_choice A 1 \<notin> V}"
          \<comment> \<open>Not exactly right—need to track which SIDE is outside V.
             The complement is: \\<Union>{LA A | A \\<in> NT, hA(0) \\<notin> V} \\<cup> \\<Union>{RA A | A \\<in> NT, hA(1) \\<notin> V}.\<close>
          define compl_set where "compl_set = (\<Union>A\<in>{A\<in>NT. hA_choice A 0 \<notin> V}. LA A)
              \<union> (\<Union>A\<in>{A\<in>NT. hA_choice A 1 \<notin> V}. RA A)"
          have hcompl_eq: "B - {x \<in> B. r x \<in> V} = compl_set"
          proof (rule set_eqI, rule iffI)
            fix x assume "x \<in> B - {x \<in> B. r x \<in> V}"
            hence "x \<in> B" "r x \<notin> V" by (by100 blast)+
            \<comment> \<open>x \\<in> B = \\<Union>{A \\<cap> Y | A \\<in> NT}. So x \\<in> A \\<cap> Y for some A \\<in> NT.\<close>
            have "x \<in> (\<Union>A\<in>NT. A \<inter> ?Y)" using \<open>x \<in> B\<close> unfolding B_def by (by100 blast)
            then obtain A where "A \<in> NT" "x \<in> A \<inter> ?Y" by (by100 blast)
            \<comment> \<open>x \\<in> LA A or x \\<in> RA A.\<close>
            have "x \<in> LA A \<or> x \<in> RA A" unfolding LA_def RA_def using \<open>x \<in> A \<inter> ?Y\<close> by (by100 auto)
            thus "x \<in> compl_set"
            proof
              assume "x \<in> LA A"
              hence "r x = hA_choice A 0" using hr_LA \<open>A \<in> NT\<close> by (by100 blast)
              hence "hA_choice A 0 \<notin> V" using \<open>r x \<notin> V\<close> by (by100 simp)
              thus "x \<in> compl_set" unfolding compl_set_def using \<open>A \<in> NT\<close> \<open>x \<in> LA A\<close> by (by100 blast)
            next
              assume "x \<in> RA A"
              hence "r x = hA_choice A 1" using hr_RA \<open>A \<in> NT\<close> by (by100 blast)
              hence "hA_choice A 1 \<notin> V" using \<open>r x \<notin> V\<close> by (by100 simp)
              thus "x \<in> compl_set" unfolding compl_set_def using \<open>A \<in> NT\<close> \<open>x \<in> RA A\<close> by (by100 blast)
            qed
          next
            fix x assume "x \<in> compl_set"
            hence "x \<in> (\<Union>A\<in>{A\<in>NT. hA_choice A 0 \<notin> V}. LA A)
                \<or> x \<in> (\<Union>A\<in>{A\<in>NT. hA_choice A 1 \<notin> V}. RA A)"
              unfolding compl_set_def by (by100 blast)
            thus "x \<in> B - {x \<in> B. r x \<in> V}"
            proof
              assume "x \<in> (\<Union>A\<in>{A\<in>NT. hA_choice A 0 \<notin> V}. LA A)"
              then obtain A where "A \<in> NT" "hA_choice A 0 \<notin> V" "x \<in> LA A" by (by100 blast)
              have "x \<in> B" using \<open>x \<in> LA A\<close> unfolding LA_def B_def using \<open>A \<in> NT\<close> by (by100 blast)
              have "r x = hA_choice A 0" using hr_LA \<open>A \<in> NT\<close> \<open>x \<in> LA A\<close> by (by100 blast)
              hence "r x \<notin> V" using \<open>hA_choice A 0 \<notin> V\<close> by (by100 simp)
              thus ?thesis using \<open>x \<in> B\<close> by (by100 blast)
            next
              assume "x \<in> (\<Union>A\<in>{A\<in>NT. hA_choice A 1 \<notin> V}. RA A)"
              then obtain A where "A \<in> NT" "hA_choice A 1 \<notin> V" "x \<in> RA A" by (by100 blast)
              have "x \<in> B" using \<open>x \<in> RA A\<close> unfolding RA_def B_def using \<open>A \<in> NT\<close> by (by100 blast)
              have "r x = hA_choice A 1" using hr_RA \<open>A \<in> NT\<close> \<open>x \<in> RA A\<close> by (by100 blast)
              hence "r x \<notin> V" using \<open>hA_choice A 1 \<notin> V\<close> by (by100 simp)
              thus ?thesis using \<open>x \<in> B\<close> by (by100 blast)
            qed
          qed
          have "closedin_on B (subspace_topology ?Y ?TY B) compl_set"
          proof -
            have "finite {A\<in>NT. hA_choice A 0 \<notin> V}" using hNT_fin by (by100 simp)
            have "finite {A\<in>NT. hA_choice A 1 \<notin> V}" using hNT_fin by (by100 simp)
            have "closedin_on B (subspace_topology ?Y ?TY B) (\<Union>A\<in>{A\<in>NT. hA_choice A 0 \<notin> V}. LA A)"
              by (rule closedin_on_finite_indexed_Union[OF hBB \<open>finite {A\<in>NT. hA_choice A 0 \<notin> V}\<close>])
                 (use hLA_closed_B in \<open>by100 blast\<close>)
            moreover have "closedin_on B (subspace_topology ?Y ?TY B) (\<Union>A\<in>{A\<in>NT. hA_choice A 1 \<notin> V}. RA A)"
              by (rule closedin_on_finite_indexed_Union[OF hBB \<open>finite {A\<in>NT. hA_choice A 1 \<notin> V}\<close>])
                 (use hRA_closed_B in \<open>by100 blast\<close>)
            ultimately have "closedin_on B (subspace_topology ?Y ?TY B)
                ((\<Union>A\<in>{A\<in>NT. hA_choice A 0 \<notin> V}. LA A)
                 \<union> (\<Union>A\<in>{A\<in>NT. hA_choice A 1 \<notin> V}. RA A))"
              using closedin_Union_finite[OF hBB, of "{_, _}"] by (by100 auto)
            thus ?thesis unfolding compl_set_def .
          qed
          hence "closedin_on B (subspace_topology ?Y ?TY B) (B - {x \<in> B. r x \<in> V})"
            using hcompl_eq by (by100 simp)
          have "B - (B - {x \<in> B. r x \<in> V}) = {x \<in> B. r x \<in> V}" by (by100 blast)
          thus "{x \<in> B. r x \<in> V} \<in> subspace_topology ?Y ?TY B"
            using \<open>closedin_on B (subspace_topology ?Y ?TY B) (B - {x \<in> B. r x \<in> V})\<close>
            unfolding closedin_on_def by (by100 simp)
        qed
        show ?thesis unfolding top1_continuous_map_on_def
          using hBB hTY_top hr_B_img hr_B_preimg by (by100 blast)
      qed
      have hr_cont_loc: "top1_continuous_map_on ?Y ?TY ?Y ?TY r"
        by (rule pasting_lemma_two_closed[OF hTY_top hTY_top hT_closed_Y hB_closed_Y
               hY_eq[symmetric] hr_img_Y hr_T_cont hr_B_cont])
      show ?thesis using that[OF hr_cont_loc hr_T_loc hr_img_loc hr_LA hr_RA] .
    qed
    \<comment> \<open>Step 3: r\\<circ>f is a loop at x0 in T.\<close>
    have hrf_loop_T: "top1_is_loop_on T (subspace_topology X TX T) x0 (r \<circ> f)"
    proof -
      \<comment> \<open>f maps [0,1] to Y. r maps Y to T. Composition maps [0,1] to T.\<close>
      have hf_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?Y ?TY f"
        using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      \<comment> \<open>r\\<circ>f: [0,1] \\<rightarrow> Y continuous (composition).\<close>
      have hrf_cont_Y: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?Y ?TY (r \<circ> f)"
        by (rule top1_continuous_map_on_comp[OF hf_cont hr_cont])
      \<comment> \<open>r\\<circ>f maps to T (from hr\\_img).\<close>
      have "\<forall>t\<in>top1_unit_interval. (r \<circ> f) t \<in> T"
      proof (intro ballI)
        fix t assume "t \<in> top1_unit_interval"
        have "f t \<in> ?Y" using hf_cont unfolding top1_continuous_map_on_def
          using \<open>t \<in> top1_unit_interval\<close> by (by100 blast)
        thus "(r \<circ> f) t \<in> T" using hr_img by (by100 simp)
      qed
      \<comment> \<open>r\\<circ>f: [0,1] \\<rightarrow> T continuous (restrict codomain).\<close>
      have hrf_cont_T: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          T (subspace_topology ?Y ?TY T) (r \<circ> f)"
        using continuous_map_restrict_codomain[OF hrf_cont_Y \<open>\<forall>t\<in>_. (r \<circ> f) t \<in> T\<close> hT_sub_Y]
        by (by100 blast)
      have "subspace_topology ?Y ?TY T = subspace_topology X TX T"
        by (rule subspace_topology_trans[OF hT_sub_Y])
      hence hrf_cont_TX: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          T (subspace_topology X TX T) (r \<circ> f)"
        using hrf_cont_T by (by100 simp)
      \<comment> \<open>r(f(0)) = r(x0) = x0, r(f(1)) = x0.\<close>
      have "f 0 = x0" "f 1 = x0"
        using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
      hence "(r \<circ> f) 0 = x0" "(r \<circ> f) 1 = x0"
        using hr_T hx0 by (by100 simp)+
      show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
        using hrf_cont_TX \<open>(r \<circ> f) 0 = x0\<close> \<open>(r \<circ> f) 1 = x0\<close>
            \<open>\<forall>t\<in>top1_unit_interval. (r \<circ> f) t \<in> T\<close> hx0
        by (by100 blast)
    qed
    \<comment> \<open>Step 3b: r\\<circ>f null-homotopic in T (T simply connected).\<close>
    have hT_sc: "top1_simply_connected_on T (subspace_topology X TX T)"
      using hT_tree unfolding top1_is_tree_on_def by (by100 blast)
    have "top1_path_homotopic_on T (subspace_topology X TX T) x0 x0 (r \<circ> f) (top1_constant_path x0)"
      using hT_sc hrf_loop_T hx0 unfolding top1_simply_connected_on_def by (by100 blast)
    \<comment> \<open>Step 3c: Lift null-homotopy from T to Y (T \\<subseteq> Y, homotopy stays in T \\<subseteq> Y).\<close>
    have hrf_null_Y: "top1_path_homotopic_on ?Y ?TY x0 x0 (r \<circ> f) (top1_constant_path x0)"
    proof -
      have "subspace_topology X TX T = subspace_topology ?Y ?TY T"
        by (rule subspace_topology_trans[OF hT_sub_Y, symmetric])
      hence "top1_path_homotopic_on T (subspace_topology ?Y ?TY T) x0 x0 (r \<circ> f) (top1_constant_path x0)"
        using \<open>top1_path_homotopic_on T (subspace_topology X TX T) x0 x0 (r \<circ> f) _\<close>
        by (by100 simp)
      from path_homotopic_subspace_to_ambient[OF hTY_top hT_sub_Y _ this]
      show ?thesis by (by100 blast)
    qed
    \<comment> \<open>Step 4: f \\<sim> r\\<circ>f in Y.\<close>
    have hf_rf: "top1_path_homotopic_on ?Y ?TY x0 x0 f (r \<circ> f)"
    proof -
      \<comment> \<open>Define homotopy H(s,t): for f(s) \\<in> T, H(s,t) = f(s).
         For f(s) \\<in> A \\<cap> Y \\ T (half-arc), slide f(s) toward r(f(s)) via linear interpolation.\<close>
      define H where "H \<equiv> \<lambda>(s::real, t::real).
        if f s \<in> T then f s
        else
          (let A = THE A. A \<in> NT \<and> f s \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A) in
           let h = hA_choice A in
           let \<sigma> = inv_into top1_unit_interval h (f s) in
           let e_param = (if \<sigma> < tA A then 0 else 1) in
           h (\<sigma> + t * (e_param - \<sigma>)))"
      \<comment> \<open>H(s,0) = f(s): when t=0, \\<sigma> + 0*(e-\\<sigma>) = \\<sigma>, so h(\\<sigma>) = f(s).\<close>
      have hH0: "\<forall>s\<in>top1_unit_interval. H (s, 0) = f s"
      proof (intro ballI)
        fix s assume "s \<in> top1_unit_interval"
        show "H (s, 0) = f s"
        proof (cases "f s \<in> T")
          case True thus ?thesis unfolding H_def by (by100 simp)
        next
          case False
          \<comment> \<open>t=0: \\<sigma> + 0*(e - \\<sigma>) = \\<sigma>. h(\\<sigma>) = f(s).\<close>
          have hf_cont_loc: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?Y ?TY f"
            using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have "f s \<in> ?Y" using hf_cont_loc \<open>s \<in> top1_unit_interval\<close>
            unfolding top1_continuous_map_on_def by (by100 blast)
          \<comment> \<open>For t=0, the formula simplifies to h(inv\\_into(h, f(s))) = f(s).\<close>
          have "f s \<in> X" using \<open>f s \<in> ?Y\<close> hY_sub by (by100 blast)
          hence "f s \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
          then obtain A where "A \<in> \<A>" "f s \<in> A" by (by100 blast)
          have "A \<in> NT" using hNT_def \<open>A \<in> \<A>\<close> \<open>f s \<in> A\<close> False by (by100 blast)
          have "f s \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hvertices_T[rule_format, OF \<open>A \<in> \<A>\<close>] False by (by100 blast)
          hence hfs_int: "f s \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
            using \<open>f s \<in> A\<close> by (by100 blast)
          have hTHE_A: "(THE A. A \<in> NT \<and> f s \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = A"
          proof (rule the_equality)
            show "A \<in> NT \<and> f s \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
              using \<open>A \<in> NT\<close> hfs_int by (by100 blast)
          next
            fix A' assume "A' \<in> NT \<and> f s \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
            hence "A' \<in> \<A>" "f s \<in> A'" using hNT_def by (by100 blast)+
            show "A' = A"
            proof (rule ccontr)
              assume "A' \<noteq> A"
              from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> A\<close>[symmetric]]
              have "f s \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                using \<open>f s \<in> A\<close> \<open>f s \<in> A'\<close> by (by100 blast)
              thus False using \<open>f s \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
            qed
          qed
          have hbij_loc: "bij_betw (hA_choice A) top1_unit_interval A"
            using hhA[OF \<open>A \<in> NT\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
          have "f s \<in> hA_choice A ` top1_unit_interval"
            using \<open>f s \<in> A\<close> hbij_loc unfolding bij_betw_def by (by100 blast)
          have "hA_choice A (inv_into top1_unit_interval (hA_choice A) (f s)) = f s"
            by (rule f_inv_into_f[OF \<open>f s \<in> hA_choice A ` top1_unit_interval\<close>])
          \<comment> \<open>With t=0: \\<sigma> + 0*(e - \\<sigma>) = \\<sigma>.\<close>
          have "\<And>\<sigma> e. \<sigma> + (0::real) * (e - \<sigma>) = \<sigma>" by (by100 simp)
          show "H (s, 0) = f s" unfolding H_def Let_def
            using False hTHE_A \<open>hA_choice A (inv_into top1_unit_interval (hA_choice A) (f s)) = f s\<close>
            by (by100 simp)
        qed
      qed
      \<comment> \<open>H(s,1) = (r\\<circ>f)(s): when t=1, \\<sigma> + 1*(e-\\<sigma>) = e, so h(e) = endpoint = r(f(s)).\<close>
      have hH1: "\<forall>s\<in>top1_unit_interval. H (s, 1) = (r \<circ> f) s"
      proof (intro ballI)
        fix s assume "s \<in> top1_unit_interval"
        show "H (s, 1) = (r \<circ> f) s"
        proof (cases "f s \<in> T")
          case True
          have "H (s, 1) = f s" unfolding H_def by (by100 simp) (use True in blast)
          moreover have "(r \<circ> f) s = f s" using hr_T True by (by100 auto)
          ultimately show ?thesis by (by100 simp)
        next
          case False
          \<comment> \<open>t=1: \\<sigma> + 1*(e - \\<sigma>) = e. h(e) = h(e\\_param) = r(f(s)).\<close>
          have hf_cont_loc2: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?Y ?TY f"
            using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have "f s \<in> ?Y" using hf_cont_loc2 \<open>s \<in> top1_unit_interval\<close>
            unfolding top1_continuous_map_on_def by (by100 blast)
          have "f s \<in> X" using \<open>f s \<in> ?Y\<close> hY_sub by (by100 blast)
          hence "f s \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
          then obtain A where "A \<in> \<A>" "f s \<in> A" by (by100 blast)
          have "A \<in> NT" using hNT_def \<open>A \<in> \<A>\<close> \<open>f s \<in> A\<close> False by (by100 blast)
          have "f s \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hvertices_T[rule_format, OF \<open>A \<in> \<A>\<close>] False by (by100 blast)
          hence hfs_int: "f s \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
            using \<open>f s \<in> A\<close> by (by100 blast)
          have hTHE_A: "(THE A. A \<in> NT \<and> f s \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = A"
          proof (rule the_equality)
            show "A \<in> NT \<and> f s \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
              using \<open>A \<in> NT\<close> hfs_int by (by100 blast)
          next
            fix A' assume "A' \<in> NT \<and> f s \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
            hence "A' \<in> \<A>" "f s \<in> A'" using hNT_def by (by100 blast)+
            show "A' = A"
            proof (rule ccontr)
              assume "A' \<noteq> A"
              from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> A\<close>[symmetric]]
              have "f s \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                using \<open>f s \<in> A\<close> \<open>f s \<in> A'\<close> by (by100 blast)
              thus False using \<open>f s \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
            qed
          qed
          \<comment> \<open>With t=1: \\<sigma> + 1*(e - \\<sigma>) = e\\_param.\<close>
          have "\<And>\<sigma> e. \<sigma> + (1::real) * (e - \<sigma>) = e" by (by100 simp)
          hence "H (s, 1) = hA_choice A (if inv_into top1_unit_interval (hA_choice A) (f s) < tA A then 0 else 1)"
            unfolding H_def Let_def using False hTHE_A by (by100 simp)
          \<comment> \<open>r(f(s)) uses same branch.\<close>
          have "f s \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using \<open>f s \<notin> top1_arc_endpoints_on A _\<close> .
          have hfs_int2: "f s \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hfs_int .
          \<comment> \<open>f(s) \\<in> LA A or RA A. Use hr\\_LA / hr\\_RA.\<close>
          have "f s \<in> LA A \<or> f s \<in> RA A" unfolding LA_def RA_def
            using \<open>f s \<in> A\<close> \<open>f s \<in> ?Y\<close> by (by100 auto)
          hence "(r \<circ> f) s = (if inv_into top1_unit_interval (hA_choice A) (f s) < tA A
              then hA_choice A 0 else hA_choice A 1)"
          proof
            assume "f s \<in> LA A"
            hence "r (f s) = hA_choice A 0" using hr_LA \<open>A \<in> NT\<close> by (by100 blast)
            moreover have "inv_into top1_unit_interval (hA_choice A) (f s) \<le> tA A"
              using \<open>f s \<in> LA A\<close> unfolding LA_def by (by100 blast)
            moreover have "inv_into top1_unit_interval (hA_choice A) (f s) \<noteq> tA A"
            proof
              assume heq: "inv_into top1_unit_interval (hA_choice A) (f s) = tA A"
              have hbij_loc: "bij_betw (hA_choice A) top1_unit_interval A"
                using hhA[OF \<open>A \<in> NT\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
              have "f s \<in> hA_choice A ` top1_unit_interval"
                using \<open>f s \<in> A\<close> hbij_loc unfolding bij_betw_def by (by100 blast)
              have "hA_choice A (inv_into top1_unit_interval (hA_choice A) (f s)) = f s"
                by (rule f_inv_into_f[OF \<open>f s \<in> hA_choice A ` top1_unit_interval\<close>])
              hence "hA_choice A (tA A) = f s" using heq by (by100 simp)
              have "ps A \<in> hA_choice A ` top1_unit_interval"
                using hps[rule_format, OF \<open>A \<in> NT\<close>] hbij_loc unfolding bij_betw_def by (by100 blast)
              have "hA_choice A (tA A) = ps A"
                unfolding tA_def by (rule f_inv_into_f[OF \<open>ps A \<in> hA_choice A ` top1_unit_interval\<close>])
              hence "f s = ps A" using \<open>hA_choice A (tA A) = f s\<close> by (by100 simp)
              hence "f s \<in> ps ` NT" using \<open>A \<in> NT\<close> by (by100 blast)
              thus False using \<open>f s \<in> ?Y\<close> by (by100 blast)
            qed
            ultimately show ?thesis by (by100 auto)
          next
            assume "f s \<in> RA A"
            hence "r (f s) = hA_choice A 1" using hr_RA \<open>A \<in> NT\<close> by (by100 blast)
            moreover have "inv_into top1_unit_interval (hA_choice A) (f s) \<ge> tA A"
              using \<open>f s \<in> RA A\<close> unfolding RA_def by (by100 blast)
            ultimately show ?thesis by (by100 auto)
          qed
          thus ?thesis using \<open>H (s, 1) = _\<close> by (by100 simp)
        qed
      qed
      \<comment> \<open>H(0,t) = x0 and H(1,t) = x0: f(0)=x0 \\<in> T, so H = f(0) = x0.\<close>
      have hH_endpts: "\<forall>t\<in>top1_unit_interval. H (0, t) = x0 \<and> H (1, t) = x0"
      proof (intro ballI conjI)
        fix t assume "t \<in> top1_unit_interval"
        have "f 0 = x0" "f 1 = x0"
          using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)+
        have "x0 \<in> T" using hx0 .
        thus "H (0, t) = x0" unfolding H_def using \<open>f 0 = x0\<close> \<open>x0 \<in> T\<close> by (by100 simp)
        show "H (1, t) = x0" unfolding H_def using \<open>f 1 = x0\<close> \<open>x0 \<in> T\<close> by (by100 simp)
      qed
      \<comment> \<open>H maps to Y.\<close>
      have hH_img: "\<forall>s\<in>top1_unit_interval. \<forall>t\<in>top1_unit_interval. H (s, t) \<in> ?Y"
      proof (intro ballI)
        fix s t assume hs: "s \<in> top1_unit_interval" and ht: "t \<in> top1_unit_interval"
        show "H (s, t) \<in> ?Y"
        proof (cases "f s \<in> T")
          case True
          hence "H (s, t) = f s" unfolding H_def by (by100 simp)
          moreover have "f s \<in> ?Y" using True hT_sub_Y by (by100 blast)
          ultimately show ?thesis by (by100 simp)
        next
          case False
          \<comment> \<open>H(s,t) = h(\\<sigma> + t*(e-\\<sigma>)). Parameter stays on half-arc, in Y.\<close>
          \<comment> \<open>Find the arc, compute parameter, show it stays on half-arc.\<close>
          have hf_cont_loc3: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?Y ?TY f"
            using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have "f s \<in> ?Y" using hf_cont_loc3 hs unfolding top1_continuous_map_on_def by (by100 blast)
          have "f s \<in> X" using \<open>f s \<in> ?Y\<close> hY_sub by (by100 blast)
          hence "f s \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
          then obtain A where hA_mem: "A \<in> \<A>" "f s \<in> A" by (by100 blast)
          have hA_NT: "A \<in> NT" using hNT_def hA_mem(1) hA_mem(2) False by (by100 blast)
          have hA_sub: "A \<subseteq> X" using h\<A> hA_mem(1) by (by100 blast)
          have "f s \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hvertices_T[rule_format, OF hA_mem(1)] False by (by100 blast)
          have hTHE_A_img: "(THE A. A \<in> NT \<and> f s \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)) = A"
          proof (rule the_equality)
            show "A \<in> NT \<and> f s \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
              using hA_NT hA_mem(2) \<open>f s \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
          next
            fix A' assume "A' \<in> NT \<and> f s \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
            hence "A' \<in> \<A>" "f s \<in> A'" using hNT_def by (by100 blast)+
            show "A' = A"
            proof (rule ccontr)
              assume "A' \<noteq> A"
              from h\<A>_inter[rule_format, OF hA_mem(1) \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> A\<close>[symmetric]]
              show False using hA_mem(2) \<open>f s \<in> A'\<close> \<open>f s \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
            qed
          qed
          have hbij_A: "bij_betw (hA_choice A) top1_unit_interval A"
            using hhA[OF hA_NT] unfolding top1_homeomorphism_on_def by (by100 blast)
          have hinj_A: "inj_on (hA_choice A) top1_unit_interval"
            using hbij_A unfolding bij_betw_def by (by100 blast)
          have himg_A: "hA_choice A ` top1_unit_interval = A"
            using hbij_A unfolding bij_betw_def by (by100 blast)
          define \<sigma> where "\<sigma> = inv_into top1_unit_interval (hA_choice A) (f s)"
          define e_param where "e_param = (if \<sigma> < tA A then (0::real) else 1)"
          define param where "param = \<sigma> + t * (e_param - \<sigma>)"
          \<comment> \<open>H(s,t) = hA\\_choice A param.\<close>
          have hH_eq: "H (s, t) = hA_choice A param"
            unfolding H_def Let_def param_def e_param_def \<sigma>_def
            using False hTHE_A_img by (by100 simp)
          \<comment> \<open>\\<sigma> \\<in> [0,1].\<close>
          have "f s \<in> hA_choice A ` top1_unit_interval" using hA_mem(2) himg_A by (by100 simp)
          have h\<sigma>_I: "\<sigma> \<in> top1_unit_interval"
            unfolding \<sigma>_def by (rule inv_into_into[OF \<open>f s \<in> hA_choice A ` top1_unit_interval\<close>])
          have h\<sigma>_01: "0 \<le> \<sigma> \<and> \<sigma> \<le> 1" using h\<sigma>_I unfolding top1_unit_interval_def by (by100 auto)
          have ht_01: "0 \<le> t \<and> t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)
          \<comment> \<open>\\<sigma> \\<noteq> tA (since f(s) \\<in> Y but ps(A) = hA(tA) \\<notin> Y).\<close>
          have h\<sigma>_ne_tA: "\<sigma> \<noteq> tA A"
          proof
            assume "\<sigma> = tA A"
            have "hA_choice A \<sigma> = f s"
              unfolding \<sigma>_def by (rule f_inv_into_f[OF \<open>f s \<in> hA_choice A ` top1_unit_interval\<close>])
            have "ps A \<in> hA_choice A ` top1_unit_interval"
              using hps[rule_format, OF hA_NT] himg_A by (by100 blast)
            have "hA_choice A (tA A) = ps A"
              unfolding tA_def by (rule f_inv_into_f[OF \<open>ps A \<in> hA_choice A ` top1_unit_interval\<close>])
            hence "f s = ps A" using \<open>hA_choice A \<sigma> = f s\<close> \<open>\<sigma> = tA A\<close> by (by100 simp)
            thus False using \<open>f s \<in> ?Y\<close> hA_NT by (by100 blast)
          qed
          \<comment> \<open>param \\<in> [0,1] and param \\<noteq> tA.\<close>
          have hparam_I: "param \<in> top1_unit_interval" and hparam_ne: "param \<noteq> tA A"
          proof -
            show "param \<in> top1_unit_interval"
            proof (cases "\<sigma> < tA A")
              case True
              hence "e_param = 0" unfolding e_param_def by (by100 simp)
              hence hparam_val: "param = \<sigma> + t * (0 - \<sigma>)" unfolding param_def by (by100 simp)
              have hparam_simp: "param = \<sigma> - t * \<sigma>" using hparam_val by (by100 simp)
              have "t * \<sigma> \<le> \<sigma>"
              proof -
                have "t * \<sigma> \<le> 1 * \<sigma>" by (rule mult_right_mono) (use ht_01 h\<sigma>_01 in linarith)+
                thus ?thesis by (by100 simp)
              qed
              have "t * \<sigma> \<ge> 0"
                using ht_01 h\<sigma>_01 by (rule mult_nonneg_nonneg[OF conjunct1 conjunct1])
              have h0: "0 \<le> param" using hparam_simp \<open>t * \<sigma> \<le> \<sigma>\<close> by (by100 linarith)
              have "param \<le> \<sigma>" using hparam_simp \<open>t * \<sigma> \<ge> 0\<close> by (by100 linarith)
              hence h1: "param \<le> 1" using h\<sigma>_01 by (by100 linarith)
              show ?thesis unfolding top1_unit_interval_def using h0 h1 by (by100 auto)
            next
              case False
              hence "e_param = 1" unfolding e_param_def by (by100 simp)
              hence "param = \<sigma> + t * (1 - \<sigma>)" unfolding param_def by (by100 simp)
              moreover have "0 \<le> t * (1 - \<sigma>)"
                by (rule mult_nonneg_nonneg) (use ht_01 h\<sigma>_01 in linarith)+
              hence "0 \<le> \<sigma> + t * (1 - \<sigma>)" using h\<sigma>_01 by (by100 linarith)
              moreover have "t * (1 - \<sigma>) \<le> 1 * (1 - \<sigma>)"
                by (rule mult_right_mono) (use ht_01 h\<sigma>_01 in linarith)+
              hence "t * (1 - \<sigma>) \<le> (1 - \<sigma>)" by (by100 simp)
              hence "\<sigma> + t * (1 - \<sigma>) \<le> 1" by (by100 linarith)
              ultimately show ?thesis unfolding top1_unit_interval_def by (by100 auto)
            qed
          next
            show "param \<noteq> tA A"
            proof (cases "\<sigma> < tA A")
              case True
              hence "e_param = 0" unfolding e_param_def by (by100 simp)
              hence hparam_val: "param = \<sigma> + t * (0 - \<sigma>)" unfolding param_def by (by100 simp)
              have "param \<le> \<sigma>"
              proof -
                have "t * \<sigma> \<ge> 0" using ht_01 h\<sigma>_01 by (rule mult_nonneg_nonneg[OF conjunct1 conjunct1])
                have "param = \<sigma> - t * \<sigma>" using hparam_val by (by100 simp)
                thus ?thesis using \<open>t * \<sigma> \<ge> 0\<close> by (by100 linarith)
              qed
              hence "param < tA A" using True by (by100 linarith)
              thus ?thesis by (by100 linarith)
            next
              case False
              hence "\<sigma> > tA A" using h\<sigma>_ne_tA by (by100 linarith)
              hence "e_param = 1" unfolding e_param_def by (by100 simp)
              hence "param = \<sigma> + t * (1 - \<sigma>)" unfolding param_def by (by100 simp)
              moreover have "0 \<le> t * (1 - \<sigma>)"
                by (rule mult_nonneg_nonneg) (use ht_01 h\<sigma>_01 in linarith)+
              ultimately have "param \<ge> \<sigma>" by (by100 linarith)
              hence "param > tA A" using \<open>\<sigma> > tA A\<close> by (by100 linarith)
              thus ?thesis by (by100 linarith)
            qed
          qed
          \<comment> \<open>h(param) \\<in> A and h(param) \\<notin> ps ` NT. Same pattern as himg\\_in\\_Y.\<close>
          have "hA_choice A param \<in> A" using hparam_I himg_A by (by100 blast)
          hence "hA_choice A param \<in> X" using hA_sub by (by100 blast)
          have "hA_choice A param \<notin> ps ` NT"
          proof
            assume "hA_choice A param \<in> ps ` NT"
            then obtain A' where hA': "A' \<in> NT" "hA_choice A param = ps A'" by (by100 blast)
            show False
            proof (cases "A' = A")
              case True
              hence "hA_choice A param = ps A" using hA'(2) by (by100 simp)
              have "ps A \<in> hA_choice A ` top1_unit_interval"
                using hps[rule_format, OF hA_NT] himg_A by (by100 blast)
              have "hA_choice A (tA A) = ps A"
                unfolding tA_def by (rule f_inv_into_f[OF \<open>ps A \<in> hA_choice A ` top1_unit_interval\<close>])
              have htA_I: "tA A \<in> top1_unit_interval"
                unfolding tA_def by (rule inv_into_into[OF \<open>ps A \<in> hA_choice A ` top1_unit_interval\<close>])
              from inj_onD[OF hinj_A _ hparam_I htA_I]
              have "param = tA A" using \<open>hA_choice A param = ps A\<close> \<open>hA_choice A (tA A) = ps A\<close> by (by100 simp)
              thus False using hparam_ne by (by100 blast)
            next
              case hA'_ne: False
              have "A' \<in> \<A>" using hA'(1) hNT_def by (by100 blast)
              have "ps A' \<in> A'" using hps[rule_format, OF hA'(1)] by (by100 blast)
              hence "hA_choice A param \<in> A'" using hA'(2) by (by100 simp)
              have "hA_choice A param \<in> A \<inter> A'"
                using \<open>hA_choice A param \<in> A\<close> \<open>hA_choice A param \<in> A'\<close> by (by100 blast)
              hence "hA_choice A param \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                using h\<A>_inter[rule_format, OF hA_mem(1) \<open>A' \<in> \<A>\<close>] hA'_ne by (by100 blast)
              hence "hA_choice A param \<in> T"
                using hvertices_T[rule_format, OF hA_mem(1)] by (by100 blast)
              have "ps A' \<notin> T" using hT_sub_Y hA'(1) by (by100 blast)
              thus False using \<open>hA_choice A param \<in> T\<close> hA'(2) by (by100 simp)
            qed
          qed
          have "hA_choice A param \<in> X - ps ` NT"
            using \<open>hA_choice A param \<in> X\<close> \<open>hA_choice A param \<notin> ps ` NT\<close> by (by100 blast)
          show ?thesis using hH_eq \<open>hA_choice A param \<in> X - ps ` NT\<close> by (by100 simp)
        qed
      qed
      \<comment> \<open>H continuous.\<close>
      \<comment> \<open>H continuous via pasting: H = f on T\\<times>I (projection), sliding on B\\<times>I.
         Strategy: show H continuous on I\\<times>I by showing preimages of open sets are open.
         Actually, simpler: for each s, H(s,\\<cdot>) is a path (affine reparametrization of arc
         or constant). The joint continuity follows from the uniform definition.
         For now: sorry this final step.\<close>
      have hH_cont: "top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval)
          (product_topology_on top1_unit_interval_topology top1_unit_interval_topology) ?Y ?TY H"
      proof -
        let ?II = "top1_unit_interval \<times> top1_unit_interval"
        let ?IItop = "product_topology_on top1_unit_interval_topology top1_unit_interval_topology"
        have hII_top: "is_topology_on ?II ?IItop"
          by (rule product_topology_on_is_topology_on[OF
              top1_unit_interval_topology_is_topology_on
              top1_unit_interval_topology_is_topology_on])
        \<comment> \<open>Partition: S\\_T = f\\<inverse>(T) \\<times> I, S\\_B = f\\<inverse>(B) \\<times> I.\<close>
        define Bh where "Bh = \<Union>{A \<inter> ?Y | A. A \<in> NT}"
        have hY_eq_h: "?Y = T \<union> Bh"
        proof
          show "T \<union> Bh \<subseteq> ?Y" using hT_sub_Y unfolding Bh_def by (by100 blast)
        next
          show "?Y \<subseteq> T \<union> Bh"
          proof (intro subsetI)
            fix x assume "x \<in> ?Y"
            hence "x \<in> X" using hY_sub by (by100 blast)
            hence "x \<in> \<Union>\<A>" using h\<A>_cover by (by100 simp)
            then obtain A where "A \<in> \<A>" "x \<in> A" by (by100 blast)
            show "x \<in> T \<union> Bh"
            proof (cases "A \<subseteq> T")
              case True thus ?thesis using \<open>x \<in> A\<close> by (by100 blast)
            next
              case False
              hence "A \<in> NT" using hNT_def \<open>A \<in> \<A>\<close> by (by100 blast)
              thus ?thesis unfolding Bh_def using \<open>x \<in> A\<close> \<open>x \<in> ?Y\<close> by (by100 blast)
            qed
          qed
        qed
        define S_T where "S_T = {s \<in> top1_unit_interval. f s \<in> T} \<times> top1_unit_interval"
        define S_B where "S_B = {s \<in> top1_unit_interval. f s \<in> Bh} \<times> top1_unit_interval"
        have hf_cont_top: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?Y ?TY f"
          using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        \<comment> \<open>Use lifted closedness facts.\<close>
        note hT_closed_Y_h = hT_closed_Y
        have hBh_closed_Y: "closedin_on ?Y ?TY Bh"
        proof -
          have "Bh = (\<Union>A\<in>NT. A \<inter> ?Y)" unfolding Bh_def by (by100 blast)
          moreover have "closedin_on ?Y ?TY (\<Union>A\<in>NT. A \<inter> ?Y)"
            by (rule closedin_on_finite_indexed_Union[OF hTY_top hNT_fin])
               (use hAY_closed in \<open>by100 blast\<close>)
          ultimately show ?thesis by (by100 simp)
        qed
        \<comment> \<open>S\\_T closed: f\\<inverse>(T) closed in I (T closed in Y, f continuous).\<close>
        have hfpi1_cont: "top1_continuous_map_on ?II ?IItop ?Y ?TY (f \<circ> fst)"
        proof -
          have hpi1: "top1_continuous_map_on ?II ?IItop top1_unit_interval top1_unit_interval_topology fst"
          proof -
            from top1_continuous_pi1[OF top1_unit_interval_topology_is_topology_on
                top1_unit_interval_topology_is_topology_on]
            show ?thesis unfolding pi1_def by (by100 simp)
          qed
          show ?thesis by (rule top1_continuous_map_on_comp[OF hpi1 hf_cont_top])
        qed
        have hST_closed: "closedin_on ?II ?IItop S_T"
        proof -
          have "{p \<in> ?II. (f \<circ> fst) p \<in> T} = S_T"
            unfolding S_T_def by (by100 auto)
          moreover have "closedin_on ?II ?IItop {p \<in> ?II. (f \<circ> fst) p \<in> T}"
            by (rule continuous_preimage_closedin[OF hII_top hTY_top hfpi1_cont hT_closed_Y])
          ultimately show ?thesis by (by100 simp)
        qed
        have hSB_closed: "closedin_on ?II ?IItop S_B"
        proof -
          have "{p \<in> ?II. (f \<circ> fst) p \<in> Bh} = S_B"
            unfolding S_B_def by (by100 auto)
          moreover have "closedin_on ?II ?IItop {p \<in> ?II. (f \<circ> fst) p \<in> Bh}"
            by (rule continuous_preimage_closedin[OF hII_top hTY_top hfpi1_cont hBh_closed_Y])
          ultimately show ?thesis by (by100 simp)
        qed
        \<comment> \<open>S\\_T \\<cup> S\\_B = I\\<times>I.\<close>
        have hcover: "S_T \<union> S_B = ?II"
        proof (rule set_eqI, rule iffI)
          fix p assume "p \<in> S_T \<union> S_B"
          thus "p \<in> ?II" unfolding S_T_def S_B_def by (by100 blast)
        next
          fix p assume "p \<in> ?II"
          then obtain s t where hst: "p = (s, t)" "s \<in> top1_unit_interval" "t \<in> top1_unit_interval"
            by (by100 blast)
          have "f s \<in> ?Y" using hf_cont_top hst(2) unfolding top1_continuous_map_on_def by (by100 blast)
          hence "f s \<in> T \<union> Bh" using hY_eq_h by (by100 simp)
          hence "s \<in> {s \<in> top1_unit_interval. f s \<in> T} \<or> s \<in> {s \<in> top1_unit_interval. f s \<in> Bh}"
            using hst(2) by (by100 blast)
          thus "p \<in> S_T \<union> S_B" unfolding S_T_def S_B_def using hst by (by100 blast)
        qed
        have hH_img_II: "\<forall>p\<in>?II. H p \<in> ?Y" using hH_img by (by100 auto)
        \<comment> \<open>H on S\\_T = f o pi1, continuous.\<close>
        have hH_ST: "top1_continuous_map_on S_T (subspace_topology ?II ?IItop S_T) ?Y ?TY H"
        proof -
          have hfpi1_ST: "top1_continuous_map_on S_T (subspace_topology ?II ?IItop S_T) ?Y ?TY (f \<circ> fst)"
          proof (rule top1_continuous_map_on_restrict_domain_simple[OF hfpi1_cont])
            show "S_T \<subseteq> ?II" unfolding S_T_def by (by100 blast)
          qed
          moreover have "\<forall>p\<in>S_T. H p = (f \<circ> fst) p"
          proof (intro ballI)
            fix p assume "p \<in> S_T"
            then obtain s t where hst: "p = (s, t)" "s \<in> top1_unit_interval" "f s \<in> T"
              unfolding S_T_def by (by100 blast)
            show "H p = (f \<circ> fst) p" unfolding H_def using hst by (by100 simp)
          qed
          ultimately show ?thesis
          proof -
            assume hg_cont: "top1_continuous_map_on S_T (subspace_topology ?II ?IItop S_T) ?Y ?TY (f \<circ> fst)"
            assume heq: "\<forall>p\<in>S_T. H p = (f \<circ> fst) p"
            have hST_sub: "S_T \<subseteq> ?II" unfolding S_T_def by (by100 blast)
            have hST_top: "is_topology_on S_T (subspace_topology ?II ?IItop S_T)"
              by (rule subspace_topology_is_topology_on[OF hII_top hST_sub])
            have hH_img_ST: "\<forall>p\<in>S_T. H p \<in> ?Y"
              using heq hg_cont unfolding top1_continuous_map_on_def by (by100 auto)
            have hH_preimg_ST: "\<forall>V\<in>?TY. {p \<in> S_T. H p \<in> V} \<in> subspace_topology ?II ?IItop S_T"
            proof (intro ballI)
              fix V assume "V \<in> ?TY"
              have "{p \<in> S_T. H p \<in> V} = {p \<in> S_T. (f \<circ> fst) p \<in> V}"
                using heq by (by100 auto)
              also have "... \<in> subspace_topology ?II ?IItop S_T"
                using hg_cont \<open>V \<in> ?TY\<close> unfolding top1_continuous_map_on_def by (by100 blast)
              finally show "{p \<in> S_T. H p \<in> V} \<in> subspace_topology ?II ?IItop S_T" .
            qed
            show ?thesis unfolding top1_continuous_map_on_def
              using hST_top hTY_top hH_img_ST hH_preimg_ST by (by100 blast)
          qed
        qed
        \<comment> \<open>H on S\\_B continuous.\<close>
        \<comment> \<open>H|S\\_B continuous. Decompose S\\_B per arc, paste finitely many closed pieces.\<close>
        have hH_SB: "top1_continuous_map_on S_B (subspace_topology ?II ?IItop S_B) ?Y ?TY H"
        proof -
          have hSB_sub: "S_B \<subseteq> ?II" unfolding S_B_def by (by100 blast)
          have hSB_top: "is_topology_on S_B (subspace_topology ?II ?IItop S_B)"
            by (rule subspace_topology_is_topology_on[OF hII_top hSB_sub])
          \<comment> \<open>On S\\_B, if f(s) \\<in> T then H(s,t) = f(s) (T-endpoint, same as S\\_T branch).
             If f(s) \\<notin> T then H(s,t) = hA(\\<sigma>+t*(e-\\<sigma>)) for unique arc A.
             In both cases, H is continuous on each piece.\<close>
          \<comment> \<open>Key observation: on S\\_B, for f(s) \\<notin> T, f(s) is in exactly one arc A \\<in> NT.
             H is continuous on f\\<inverse>(A\\<cap>Y) \\<times> I for each A because it's a composition
             of continuous maps. And f\\<inverse>(A\\<cap>Y) \\<times> I are closed, finite, cover S\\_B.
             At overlaps (T-endpoints): H = f\\<circ>fst, continuous.\<close>
          \<comment> \<open>Per-arc pieces: for each A \\<in> NT, P\\_A = f\\<inverse>(A\\<cap>Y) \\<times> I.\<close>
          define PA where "PA \<equiv> \<lambda>A. {s \<in> top1_unit_interval. f s \<in> A \<inter> ?Y} \<times> top1_unit_interval"
          \<comment> \<open>Each P\\_A closed in I\\<times>I.\<close>
          have hPA_closed: "\<forall>A\<in>NT. closedin_on ?II ?IItop (PA A)"
          proof (intro ballI)
            fix A assume "A \<in> NT"
            have "closedin_on ?II ?IItop {p \<in> ?II. (f \<circ> fst) p \<in> A \<inter> ?Y}"
              by (rule continuous_preimage_closedin[OF hII_top hTY_top hfpi1_cont])
                 (use hAY_closed \<open>A \<in> NT\<close> in \<open>by100 blast\<close>)
            moreover have "{p \<in> ?II. (f \<circ> fst) p \<in> A \<inter> ?Y} = PA A"
              unfolding PA_def by (by100 auto)
            ultimately show "closedin_on ?II ?IItop (PA A)" by (by100 simp)
          qed
          \<comment> \<open>P\\_A \\<subseteq> S\\_B.\<close>
          have hPA_sub_SB: "\<forall>A\<in>NT. PA A \<subseteq> S_B"
            unfolding PA_def S_B_def Bh_def by (by100 blast)
          \<comment> \<open>S\\_B = \\<Union>{PA A | A \\<in> NT}.\<close>
          have hSB_eq: "S_B = (\<Union>A\<in>NT. PA A)"
            unfolding S_B_def PA_def Bh_def by (by100 blast)
          \<comment> \<open>H continuous on each PA A (inside S\\_B's subspace topology).\<close>
          have hH_PA: "\<forall>A\<in>NT. top1_continuous_map_on (PA A) (subspace_topology ?II ?IItop (PA A)) ?Y ?TY H"
          proof (intro ballI)
            fix A assume "A \<in> NT"
            \<comment> \<open>Decompose PA(A) into left and right halves.
               PA\\_L = f\\<inverse>(LA A) \\<times> I (\\<sigma> \\<le> tA). PA\\_R = f\\<inverse>(RA A) \\<times> I (\\<sigma> \\<ge> tA).
               PA(A) = PA\\_L \\<cup> PA\\_R. Both closed.\<close>
            define PA_L where "PA_L = {s \<in> top1_unit_interval. f s \<in> LA A} \<times> top1_unit_interval"
            define PA_R where "PA_R = {s \<in> top1_unit_interval. f s \<in> RA A} \<times> top1_unit_interval"
            define \<sigma>f where "\<sigma>f \<equiv> \<lambda>s. inv_into top1_unit_interval (hA_choice A) (f s)"
            have hhA_loc: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                A (subspace_topology X TX A) (hA_choice A)" using hhA \<open>A \<in> NT\<close> by (by100 blast)
            have hPA_eq: "PA A = PA_L \<union> PA_R"
              unfolding PA_def PA_L_def PA_R_def LA_def RA_def by (by100 auto)
            \<comment> \<open>PA\\_L closed in I\\<times>I.\<close>
            have "closedin_on ?Y ?TY (LA A)"
            proof -
              \<comment> \<open>LA(A) = hA([0,tA]) \\<cap> Y. hA([0,tA]) closed in X (compact \\<Rightarrow> closed).
                 Intersection with Y = closed in Y (Theorem\\_17\\_2).\<close>
              have "A \<in> \<A>" using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
              have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
              define hA_left where "hA_left = hA_choice A ` {t \<in> top1_unit_interval. t \<le> tA A}"
              have hbij_L: "bij_betw (hA_choice A) top1_unit_interval A"
                using hhA[OF \<open>A \<in> NT\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
              have "LA A = hA_left \<inter> ?Y"
              proof (rule set_eqI, rule iffI)
                fix x assume "x \<in> LA A"
                hence "x \<in> A \<inter> ?Y" "inv_into top1_unit_interval (hA_choice A) x \<le> tA A"
                  unfolding LA_def by (by100 blast)+
                have "x \<in> hA_choice A ` top1_unit_interval"
                  using \<open>x \<in> A \<inter> ?Y\<close> hbij_L unfolding bij_betw_def by (by100 blast)
                have "hA_choice A (inv_into top1_unit_interval (hA_choice A) x) = x"
                  by (rule f_inv_into_f[OF \<open>x \<in> hA_choice A ` top1_unit_interval\<close>])
                have "x = hA_choice A (inv_into top1_unit_interval (hA_choice A) x)"
                  using \<open>hA_choice A (inv_into top1_unit_interval (hA_choice A) x) = x\<close> by (by100 simp)
                have hinv_I: "inv_into top1_unit_interval (hA_choice A) x \<in> top1_unit_interval"
                  by (rule inv_into_into[OF \<open>x \<in> hA_choice A ` top1_unit_interval\<close>])
                hence "x \<in> hA_left" unfolding hA_left_def
                  using \<open>x = hA_choice A _\<close> hinv_I \<open>inv_into _ _ x \<le> tA A\<close> by (by100 force)
                thus "x \<in> hA_left \<inter> ?Y" using \<open>x \<in> A \<inter> ?Y\<close> by (by100 blast)
              next
                fix x assume "x \<in> hA_left \<inter> ?Y"
                then obtain t where "t \<in> top1_unit_interval" "t \<le> tA A" "x = hA_choice A t"
                  unfolding hA_left_def by (by100 blast)
                have "x \<in> A" using \<open>x = hA_choice A t\<close> \<open>t \<in> top1_unit_interval\<close> hbij_L
                  unfolding bij_betw_def by (by100 blast)
                have "inv_into top1_unit_interval (hA_choice A) x = t"
                  using inv_into_f_f[OF _ \<open>t \<in> top1_unit_interval\<close>] \<open>x = hA_choice A t\<close>
                  hbij_L unfolding bij_betw_def by (by100 blast)
                thus "x \<in> LA A" unfolding LA_def using \<open>x \<in> A\<close> \<open>x \<in> hA_left \<inter> ?Y\<close> \<open>t \<le> tA A\<close>
                  by (by100 simp)
              qed
              moreover have "closedin_on X TX hA_left"
              proof -
                have hhA_loc: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                    A (subspace_topology X TX A) (hA_choice A)" using hhA \<open>A \<in> NT\<close> by (by100 blast)
                have hh_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                    A (subspace_topology X TX A) (hA_choice A)"
                  using hhA_loc unfolding top1_homeomorphism_on_def by (by100 blast)
                have hhaus: "is_hausdorff_on X TX"
                  using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                have hA_haus: "is_hausdorff_on A (subspace_topology X TX A)"
                  using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>A \<subseteq> X\<close> hhaus by (by100 blast)
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
                    thus "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> top1_unit_interval \<subseteq> \<Union>F"
                      using hCI_eq by (by100 simp)
                  qed
                qed
                have hC_cl: "closedin_on top1_unit_interval top1_unit_interval_topology
                    {t \<in> top1_unit_interval. t \<le> tA A}"
                proof -
                  have "top1_unit_interval - {t \<in> top1_unit_interval. t \<le> tA A}
                      = {t \<in> top1_unit_interval. t > tA A}" by (by100 auto)
                  moreover have "{t \<in> top1_unit_interval. t > tA A} \<in> top1_unit_interval_topology"
                  proof -
                    have "I_top = subspace_topology (UNIV :: real set) top1_open_sets I_set"
                      unfolding top1_unit_interval_topology_def top1_unit_interval_def
                        subspace_topology_def by (by100 auto)
                    have "open {x :: real. tA A < x}" using open_greaterThan
                      unfolding greaterThan_def by (by100 blast)
                    hence "{x :: real. tA A < x} \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
                    have "{t \<in> top1_unit_interval. t > tA A} = top1_unit_interval \<inter> {x. tA A < x}"
                      by (by100 auto)
                    thus ?thesis using \<open>I_top = _\<close> \<open>{x. tA A < x} \<in> top1_open_sets\<close>
                      unfolding subspace_topology_def by (by100 blast)
                  qed
                  ultimately have "top1_unit_interval - {t \<in> top1_unit_interval. t \<le> tA A}
                      \<in> top1_unit_interval_topology" by (by100 simp)
                  moreover have "{t \<in> top1_unit_interval. t \<le> tA A} \<subseteq> top1_unit_interval" by (by100 blast)
                  ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
                qed
                from compact_hausdorff_continuous_closed_map[OF hI_cpt hA_haus hh_cont hC_cl]
                have "closedin_on A (subspace_topology X TX A) hA_left"
                  unfolding hA_left_def by (by100 simp)
                from Theorem_17_3[OF hX_top _ this]
                show ?thesis using hA_closed_X \<open>A \<in> NT\<close> by (by100 blast)
              qed
              moreover have "closedin_on ?Y ?TY (hA_left \<inter> ?Y)"
              proof -
                from Theorem_17_2[OF hX_top hY_sub, of "hA_left \<inter> ?Y"]
                show ?thesis using \<open>closedin_on X TX hA_left\<close> by (by100 blast)
              qed
              ultimately show ?thesis by (by100 simp)
            qed
            have hPA_L_closed: "closedin_on ?II ?IItop PA_L"
            proof -
              have "{p \<in> ?II. (f \<circ> fst) p \<in> LA A} = PA_L"
                unfolding PA_L_def by (by100 auto)
              moreover have "closedin_on ?II ?IItop {p \<in> ?II. (f \<circ> fst) p \<in> LA A}"
                by (rule continuous_preimage_closedin[OF hII_top hTY_top hfpi1_cont
                    \<open>closedin_on ?Y ?TY (LA A)\<close>])
              ultimately show ?thesis by (by100 simp)
            qed
            have "closedin_on ?Y ?TY (RA A)"
            proof -
              have "A \<in> \<A>" using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
              have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
              define hA_right where "hA_right = hA_choice A ` {t \<in> top1_unit_interval. t \<ge> tA A}"
              have hbij_R: "bij_betw (hA_choice A) top1_unit_interval A"
                using hhA[OF \<open>A \<in> NT\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
              have "RA A = hA_right \<inter> ?Y"
              proof (rule set_eqI, rule iffI)
                fix x assume "x \<in> RA A"
                hence "x \<in> A \<inter> ?Y" "inv_into top1_unit_interval (hA_choice A) x \<ge> tA A"
                  unfolding RA_def by (by100 blast)+
                have "x \<in> hA_choice A ` top1_unit_interval"
                  using \<open>x \<in> A \<inter> ?Y\<close> hbij_R unfolding bij_betw_def by (by100 blast)
                have "hA_choice A (inv_into top1_unit_interval (hA_choice A) x) = x"
                  by (rule f_inv_into_f[OF \<open>x \<in> hA_choice A ` top1_unit_interval\<close>])
                have "x = hA_choice A (inv_into top1_unit_interval (hA_choice A) x)"
                  using \<open>hA_choice A (inv_into top1_unit_interval (hA_choice A) x) = x\<close> by (by100 simp)
                have hinv_I: "inv_into top1_unit_interval (hA_choice A) x \<in> top1_unit_interval"
                  by (rule inv_into_into[OF \<open>x \<in> hA_choice A ` top1_unit_interval\<close>])
                hence "x \<in> hA_right" unfolding hA_right_def
                  using \<open>x = hA_choice A _\<close> hinv_I \<open>inv_into _ _ x \<ge> tA A\<close> by (by100 force)
                thus "x \<in> hA_right \<inter> ?Y" using \<open>x \<in> A \<inter> ?Y\<close> by (by100 blast)
              next
                fix x assume "x \<in> hA_right \<inter> ?Y"
                then obtain t where "t \<in> top1_unit_interval" "t \<ge> tA A" "x = hA_choice A t"
                  unfolding hA_right_def by (by100 blast)
                have "x \<in> A" using \<open>x = hA_choice A t\<close> \<open>t \<in> top1_unit_interval\<close> hbij_R
                  unfolding bij_betw_def by (by100 blast)
                have "inv_into top1_unit_interval (hA_choice A) x = t"
                  using inv_into_f_f[OF _ \<open>t \<in> top1_unit_interval\<close>] \<open>x = hA_choice A t\<close>
                  hbij_R unfolding bij_betw_def by (by100 blast)
                thus "x \<in> RA A" unfolding RA_def using \<open>x \<in> A\<close> \<open>x \<in> hA_right \<inter> ?Y\<close> \<open>t \<ge> tA A\<close>
                  by (by100 simp)
              qed
              moreover have "closedin_on X TX hA_right"
              proof -
                have hhA_loc: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                    A (subspace_topology X TX A) (hA_choice A)" using hhA \<open>A \<in> NT\<close> by (by100 blast)
                have hh_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                    A (subspace_topology X TX A) (hA_choice A)"
                  using hhA_loc unfolding top1_homeomorphism_on_def by (by100 blast)
                have hhaus: "is_hausdorff_on X TX"
                  using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                have hA_haus: "is_hausdorff_on A (subspace_topology X TX A)"
                  using conjunct2[OF conjunct2[OF Theorem_17_11]] \<open>A \<subseteq> X\<close> hhaus by (by100 blast)
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
                    thus "\<exists>F. finite F \<and> F \<subseteq> Uc \<and> top1_unit_interval \<subseteq> \<Union>F"
                      using hCI_eq by (by100 simp)
                  qed
                qed
                have hC_cl: "closedin_on top1_unit_interval top1_unit_interval_topology
                    {t \<in> top1_unit_interval. t \<ge> tA A}"
                proof -
                  have "top1_unit_interval - {t \<in> top1_unit_interval. t \<ge> tA A}
                      = {t \<in> top1_unit_interval. t < tA A}" by (by100 auto)
                  moreover have "{t \<in> top1_unit_interval. t < tA A} \<in> top1_unit_interval_topology"
                  proof -
                    have "I_top = subspace_topology (UNIV :: real set) top1_open_sets I_set"
                      unfolding top1_unit_interval_topology_def top1_unit_interval_def
                        subspace_topology_def by (by100 auto)
                    have "open {x :: real. x < tA A}" using open_lessThan
                      unfolding lessThan_def by (by100 blast)
                    hence "{x :: real. x < tA A} \<in> top1_open_sets" unfolding top1_open_sets_def by (by100 blast)
                    have "{t \<in> top1_unit_interval. t < tA A} = top1_unit_interval \<inter> {x. x < tA A}"
                      by (by100 auto)
                    thus ?thesis using \<open>I_top = _\<close> \<open>{x. x < tA A} \<in> top1_open_sets\<close>
                      unfolding subspace_topology_def by (by100 blast)
                  qed
                  ultimately have "top1_unit_interval - {t \<in> top1_unit_interval. t \<ge> tA A}
                      \<in> top1_unit_interval_topology" by (by100 simp)
                  moreover have "{t \<in> top1_unit_interval. t \<ge> tA A} \<subseteq> top1_unit_interval" by (by100 blast)
                  ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
                qed
                from compact_hausdorff_continuous_closed_map[OF hI_cpt hA_haus hh_cont hC_cl]
                have "closedin_on A (subspace_topology X TX A) hA_right"
                  unfolding hA_right_def by (by100 simp)
                from Theorem_17_3[OF hX_top _ this]
                show ?thesis using hA_closed_X \<open>A \<in> NT\<close> by (by100 blast)
              qed
              moreover have "closedin_on ?Y ?TY (hA_right \<inter> ?Y)"
              proof -
                from Theorem_17_2[OF hX_top hY_sub, of "hA_right \<inter> ?Y"]
                show ?thesis using \<open>closedin_on X TX hA_right\<close> by (by100 blast)
              qed
              ultimately show ?thesis by (by100 simp)
            qed
            have hPA_R_closed: "closedin_on ?II ?IItop PA_R"
            proof -
              have "{p \<in> ?II. (f \<circ> fst) p \<in> RA A} = PA_R"
                unfolding PA_R_def by (by100 auto)
              moreover have "closedin_on ?II ?IItop {p \<in> ?II. (f \<circ> fst) p \<in> RA A}"
                by (rule continuous_preimage_closedin[OF hII_top hTY_top hfpi1_cont
                    \<open>closedin_on ?Y ?TY (RA A)\<close>])
              ultimately show ?thesis by (by100 simp)
            qed
            have hPA_sub: "PA A \<subseteq> ?II" unfolding PA_def by (by100 blast)
            have hPA_top: "is_topology_on (PA A) (subspace_topology ?II ?IItop (PA A))"
              by (rule subspace_topology_is_topology_on[OF hII_top hPA_sub])
            have hH_img_PA: "\<forall>p\<in>PA A. H p \<in> ?Y" using hH_img_II hPA_sub by (by100 blast)
            \<comment> \<open>H on PA\\_L: H(s,t) = hA(\\<sigma>*(1-t)) where \\<sigma> = inv\\_into(hA,f(s)).
               This is a composition of continuous maps.\<close>
            \<comment> \<open>H on PA\\_L and PA\\_R: both are compositions of continuous maps.
               On PA\\_L: H(s,t) = hA(inv(hA,f(s))*(1-t)). On PA\\_R: H(s,t) = hA(inv(hA,f(s))+t*(1-inv(hA,f(s)))).
               Both follow the same pattern: hA \\<circ> g where g is affine of (inv\\<circ>f\\<circ>fst, snd).
               Key: inv\\_into(hA,\\<cdot>) continuous A \\<rightarrow> I (from homeomorphism inverse).
               For now: sorry these final two sub-sorrys.\<close>
            have hH_PA_L: "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L) ?Y ?TY H"
            proof -
              have hPA_L_sub: "PA_L \<subseteq> ?II" unfolding PA_L_def by (by100 blast)
              have hPA_L_top: "is_topology_on PA_L (subspace_topology ?II ?IItop PA_L)"
                by (rule subspace_topology_is_topology_on[OF hII_top hPA_L_sub])
              \<comment> \<open>Define the continuous function g(s,t) = hA(inv(hA,f(s)) + t*(0-inv(hA,f(s)))).
                 This equals H on PA\\_L.\<close>
              \<comment> \<open>\\<sigma>f = inv\\_into \\<circ> hA \\<circ> f already defined at outer level.\<close>
              have hinv_cont_A: "top1_continuous_map_on A (subspace_topology X TX A)
                  top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval (hA_choice A))"
                using hhA_loc unfolding top1_homeomorphism_on_def by (by100 blast)
              \<comment> \<open>Show H = g on PA\\_L and g continuous. Then transfer.\<close>
              have hH_eq_PA_L: "\<forall>p\<in>PA_L. H p = hA_choice A (\<sigma>f (fst p) + snd p * (0 - \<sigma>f (fst p)))"
              proof (intro ballI)
                fix p assume "p \<in> PA_L"
                then obtain s t where hst: "p = (s, t)" "s \<in> top1_unit_interval" "f s \<in> LA A"
                    "t \<in> top1_unit_interval"
                  unfolding PA_L_def by (by100 blast)
                have hbij_loc: "bij_betw (hA_choice A) top1_unit_interval A"
                  using hhA[OF \<open>A \<in> NT\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                have hinj_loc: "inj_on (hA_choice A) top1_unit_interval"
                  using hbij_loc unfolding bij_betw_def by (by100 blast)
                have himg_loc: "hA_choice A ` top1_unit_interval = A"
                  using hbij_loc unfolding bij_betw_def by (by100 blast)
                have "f s \<in> A" using hst(3) unfolding LA_def by (by100 blast)
                have "f s \<in> hA_choice A ` top1_unit_interval" using \<open>f s \<in> A\<close> himg_loc by (by100 simp)
                show "H p = hA_choice A (\<sigma>f (fst p) + snd p * (0 - \<sigma>f (fst p)))"
                proof (cases "f s \<in> T")
                  case True
                  \<comment> \<open>f(s) \\<in> T: \\<sigma>f(s) = 0 (endpoint hA(0)), H = f(s) = hA(0).\<close>
                  have "f s \<in> T \<inter> A" using True \<open>f s \<in> A\<close> by (by100 blast)
                  have "A \<in> \<A>" using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
                  from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>]
                  have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                    using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
                  hence "f s \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                    using \<open>f s \<in> T \<inter> A\<close> by (by100 blast)
                  \<comment> \<open>f(s) = hA(0) (since inv \\<le> tA and endpoint).\<close>
                  have h0_I: "(0::real) \<in> top1_unit_interval"
                    unfolding top1_unit_interval_def by (by100 auto)
                  have "\<sigma>f s = 0"
                  proof -
                    have "inv_into top1_unit_interval (hA_choice A) (f s) \<le> tA A"
                      using hst(3) unfolding LA_def by (by100 blast)
                    have hX_haus_L: "is_hausdorff_on X TX"
                      using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                    have hA_sub_L: "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                    have harc_L: "top1_is_arc_on A (subspace_topology X TX A)"
                      using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                    have hep_L: "top1_arc_endpoints_on A (subspace_topology X TX A) = {hA_choice A 0, hA_choice A 1}"
                      using arc_endpoints_are_boundary[OF hX_strict hX_haus_L hA_sub_L harc_L hhA_loc]
                      by (by100 simp)
                    have "f s = hA_choice A 0 \<or> f s = hA_choice A 1"
                      using \<open>f s \<in> top1_arc_endpoints_on A _\<close> hep_L by (by100 auto)
                    moreover have "f s \<noteq> hA_choice A 1"
                    proof
                      assume "f s = hA_choice A 1"
                      have h1_I: "(1::real) \<in> top1_unit_interval"
                        unfolding top1_unit_interval_def by (by100 auto)
                      have "inv_into top1_unit_interval (hA_choice A) (hA_choice A 1) = 1"
                        using inv_into_f_f[OF hinj_loc h1_I] by (by100 simp)
                      hence "\<sigma>f s = 1" using \<open>f s = hA_choice A 1\<close> unfolding \<sigma>f_def by (by100 simp)
                      have "ps A \<in> hA_choice A ` top1_unit_interval"
                        using hps[rule_format, OF \<open>A \<in> NT\<close>] himg_loc by (by100 blast)
                      have "tA A \<in> top1_unit_interval"
                        unfolding tA_def by (rule inv_into_into[OF \<open>ps A \<in> _\<close>])
                      have "tA A \<noteq> 1"
                      proof
                        assume "tA A = 1"
                        have "hA_choice A (tA A) = ps A"
                          unfolding tA_def by (rule f_inv_into_f[OF \<open>ps A \<in> _\<close>])
                        hence "ps A = hA_choice A 1" using \<open>tA A = 1\<close> by (by100 simp)
                        hence "ps A \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                          using hep_L by (by100 simp)
                        thus False using hps[rule_format, OF \<open>A \<in> NT\<close>] by (by100 blast)
                      qed
                      hence "tA A < 1" using \<open>tA A \<in> top1_unit_interval\<close>
                        unfolding top1_unit_interval_def by (by100 auto)
                      thus False using \<open>\<sigma>f s = 1\<close> \<open>inv_into _ _ (f s) \<le> tA A\<close>
                        unfolding \<sigma>f_def by (by100 linarith)
                    qed
                    ultimately have "f s = hA_choice A 0" by (by100 blast)
                    hence "inv_into top1_unit_interval (hA_choice A) (f s) = 0"
                      using inv_into_f_f[OF hinj_loc h0_I] by (by100 simp)
                    thus ?thesis unfolding \<sigma>f_def by (by100 simp)
                  qed
                  have "H p = f s" using True hst(1) unfolding H_def by (by100 simp)
                  moreover have "hA_choice A (0 + t * (0 - 0)) = hA_choice A 0" by (by100 simp)
                  moreover have "f s = hA_choice A 0"
                  proof -
                    have "hA_choice A (inv_into top1_unit_interval (hA_choice A) (f s)) = f s"
                      by (rule f_inv_into_f[OF \<open>f s \<in> hA_choice A ` top1_unit_interval\<close>])
                    thus ?thesis using \<open>\<sigma>f s = 0\<close> unfolding \<sigma>f_def by (by100 simp)
                  qed
                  ultimately show ?thesis using hst(1) \<open>\<sigma>f s = 0\<close> by (by100 simp)
                next
                  case False
                  \<comment> \<open>f(s) \\<notin> T: H uses the else branch. THE A' = A. \\<sigma> < tA, e\\_param = 0.\<close>
                  have "f s \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
                  proof -
                    have "A \<in> \<A>" using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
                    show ?thesis using hvertices_T[rule_format, OF \<open>A \<in> \<A>\<close>] False by (by100 blast)
                  qed
                  have hTHE: "(THE A'. A' \<in> NT \<and> f s \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')) = A"
                  proof (rule the_equality)
                    show "A \<in> NT \<and> f s \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
                      using \<open>A \<in> NT\<close> \<open>f s \<in> A\<close> \<open>f s \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
                  next
                    fix A' assume h: "A' \<in> NT \<and> f s \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
                    hence "A' \<in> \<A>" "f s \<in> A'" using hNT_def by (by100 blast)+
                    have "A \<in> \<A>" using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
                    show "A' = A"
                    proof (rule ccontr)
                      assume "A' \<noteq> A"
                      from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> A\<close>[symmetric]]
                      show False using \<open>f s \<in> A\<close> \<open>f s \<in> A'\<close> \<open>f s \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
                    qed
                  qed
                  have h\<sigma>_le: "\<sigma>f s \<le> tA A"
                    using hst(3) unfolding LA_def \<sigma>f_def by (by100 blast)
                  have h\<sigma>_ne: "\<sigma>f s \<noteq> tA A"
                  proof
                    assume "\<sigma>f s = tA A"
                    have "hA_choice A (\<sigma>f s) = f s"
                      unfolding \<sigma>f_def by (rule f_inv_into_f[OF \<open>f s \<in> hA_choice A ` top1_unit_interval\<close>])
                    have "ps A \<in> hA_choice A ` top1_unit_interval"
                      using hps[rule_format, OF \<open>A \<in> NT\<close>] himg_loc by (by100 blast)
                    have "hA_choice A (tA A) = ps A"
                      unfolding tA_def by (rule f_inv_into_f[OF \<open>ps A \<in> hA_choice A ` top1_unit_interval\<close>])
                    hence "f s = ps A" using \<open>hA_choice A (\<sigma>f s) = f s\<close> \<open>\<sigma>f s = tA A\<close> by (by100 simp)
                    thus False using hst(3) \<open>A \<in> NT\<close> unfolding LA_def by (by100 blast)
                  qed
                  hence h\<sigma>_lt: "\<sigma>f s < tA A" using h\<sigma>_le by (by100 linarith)
                  have "H (s, t) = (let A' = THE A'. A' \<in> NT \<and> f s \<in> A' -
                      top1_arc_endpoints_on A' (subspace_topology X TX A') in
                      let h = hA_choice A' in
                      let \<sigma> = inv_into top1_unit_interval h (f s) in
                      let ep = (if \<sigma> < tA A' then 0 else 1) in h (\<sigma> + t * (ep - \<sigma>)))"
                    unfolding H_def using False by (by100 simp)
                  hence "H (s, t) = (let h = hA_choice A in
                      let \<sigma> = inv_into top1_unit_interval h (f s) in
                      let ep = (if \<sigma> < tA A then 0 else 1) in h (\<sigma> + t * (ep - \<sigma>)))"
                    using hTHE unfolding Let_def by (by100 simp)
                  hence "H (s, t) = hA_choice A (inv_into top1_unit_interval (hA_choice A) (f s) +
                      t * ((if inv_into top1_unit_interval (hA_choice A) (f s) < tA A then 0 else 1) -
                           inv_into top1_unit_interval (hA_choice A) (f s)))"
                    unfolding Let_def by (by100 simp)
                  have "(if inv_into top1_unit_interval (hA_choice A) (f s) < tA A then (0::real) else 1) = 0"
                    using h\<sigma>_lt unfolding \<sigma>f_def by (by100 simp)
                  hence "H (s, t) = hA_choice A (\<sigma>f s + t * (0 - \<sigma>f s))"
                    using \<open>H (s, t) = hA_choice A (inv_into _ _ (f s) + t * ((if _ then 0 else 1) - _))\<close>
                    unfolding \<sigma>f_def by (by100 simp)
                  thus ?thesis using hst(1) by (by100 simp)
                qed
              qed
              have hg_cont: "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L) ?Y ?TY
                  (\<lambda>p. hA_choice A (\<sigma>f (fst p) + snd p * (0 - \<sigma>f (fst p))))"
              proof -
                have hPA_L_sub: "PA_L \<subseteq> ?II" unfolding PA_L_def by (by100 blast)
                have hPA_L_top: "is_topology_on PA_L (subspace_topology ?II ?IItop PA_L)"
                  by (rule subspace_topology_is_topology_on[OF hII_top hPA_L_sub])
                \<comment> \<open>Step 1: \\<sigma>f \\<circ> fst continuous PA\\_L \\<rightarrow> I.
                   Chain: fst cont PA\\_L \\<rightarrow> I, f cont I \\<rightarrow> Y,
                   restrict codomain to LA(A), inv\\_into(hA) cont LA(A) \\<rightarrow> I.\<close>
                have hfst_cont: "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L)
                    top1_unit_interval top1_unit_interval_topology fst"
                proof -
                  have "top1_continuous_map_on ?II ?IItop top1_unit_interval top1_unit_interval_topology fst"
                  proof -
                    from top1_continuous_pi1[OF top1_unit_interval_topology_is_topology_on
                        top1_unit_interval_topology_is_topology_on]
                    show ?thesis unfolding pi1_def by (by100 simp)
                  qed
                  from top1_continuous_map_on_restrict_domain_simple[OF this hPA_L_sub]
                  show ?thesis .
                qed
                \<comment> \<open>f \\<circ> fst maps PA\\_L into LA(A).\<close>
                have hfst_img: "\<forall>p\<in>PA_L. f (fst p) \<in> LA A"
                  unfolding PA_L_def by (by100 auto)
                \<comment> \<open>f \\<circ> fst continuous PA\\_L \\<rightarrow> Y.\<close>
                have hf_cont_here: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?Y ?TY f"
                  using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                have hffst_cont: "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L) ?Y ?TY (f \<circ> fst)"
                  by (rule top1_continuous_map_on_comp[OF hfst_cont hf_cont_here])
                \<comment> \<open>Restrict codomain to LA(A) \\<subseteq> Y.\<close>
                have hLA_sub_Y: "LA A \<subseteq> ?Y" unfolding LA_def by (by100 blast)
                have hffst_LA: "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L)
                    (LA A) (subspace_topology ?Y ?TY (LA A)) (f \<circ> fst)"
                proof (rule continuous_map_restrict_codomain[OF hffst_cont _ hLA_sub_Y])
                  show "\<forall>p\<in>PA_L. (f \<circ> fst) p \<in> LA A" using hfst_img by (by100 simp)
                qed
                \<comment> \<open>inv\\_into(hA) continuous on LA(A). Topology: sub(Y,TY,LA(A)) = sub(X,TX,LA(A)).\<close>
                have hLA_sub_A: "LA A \<subseteq> A" unfolding LA_def by (by100 blast)
                have "A \<in> \<A>" using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
                have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                have hLA_sub_X: "LA A \<subseteq> X" using hLA_sub_A \<open>A \<subseteq> X\<close> by (by100 blast)
                have "subspace_topology ?Y ?TY (LA A) = subspace_topology X TX (LA A)"
                  by (rule subspace_topology_trans[OF hLA_sub_Y])
                also have "... = subspace_topology A (subspace_topology X TX A) (LA A)"
                  by (rule subspace_topology_trans[OF hLA_sub_A, symmetric])
                finally have hLA_top_eq: "subspace_topology ?Y ?TY (LA A) =
                    subspace_topology A (subspace_topology X TX A) (LA A)" .
                \<comment> \<open>This is sorry'd; once proved, the rest follows by composition.\<close>
                \<comment> \<open>Step: inv\\_into(hA) continuous LA(A) \\<rightarrow> I.\<close>
                have hinv_cont: "top1_continuous_map_on A (subspace_topology X TX A)
                    top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval (hA_choice A))"
                  using hhA_loc unfolding top1_homeomorphism_on_def by (by100 blast)
                \<comment> \<open>Restrict domain to LA(A).\<close>
                have hinv_cont_LA: "top1_continuous_map_on (LA A) (subspace_topology A (subspace_topology X TX A) (LA A))
                    top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval (hA_choice A))"
                  by (rule top1_continuous_map_on_restrict_domain_simple[OF hinv_cont hLA_sub_A])
                \<comment> \<open>Rewrite topology: sub(A, sub(X,TX,A), LA(A)) = sub(Y, TY, LA(A)).\<close>
                hence hinv_cont_LA': "top1_continuous_map_on (LA A) (subspace_topology ?Y ?TY (LA A))
                    top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval (hA_choice A))"
                  using hLA_top_eq by (by100 simp)
                \<comment> \<open>Compose: \\<sigma>f\\<circ>fst = inv\\_into \\<circ> (f\\<circ>fst), continuous PA\\_L \\<rightarrow> I.\<close>
                have h\<sigma>f_fst_cont: "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L)
                    top1_unit_interval top1_unit_interval_topology (\<lambda>p. \<sigma>f (fst p))"
                proof -
                  from top1_continuous_map_on_comp[OF hffst_LA hinv_cont_LA']
                  have "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L)
                      top1_unit_interval top1_unit_interval_topology
                      ((inv_into top1_unit_interval (hA_choice A)) \<circ> (f \<circ> fst))" .
                  moreover have "\<And>p. ((inv_into top1_unit_interval (hA_choice A)) \<circ> (f \<circ> fst)) p = \<sigma>f (fst p)"
                    unfolding \<sigma>f_def comp_def by (by100 simp)
                  ultimately show ?thesis unfolding top1_continuous_map_on_def by (by100 auto)
                qed
                \<comment> \<open>snd continuous PA\\_L \\<rightarrow> I.\<close>
                have hsnd_cont: "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L)
                    top1_unit_interval top1_unit_interval_topology snd"
                proof -
                  have "top1_continuous_map_on ?II ?IItop top1_unit_interval top1_unit_interval_topology snd"
                  proof -
                    from top1_continuous_pi2[OF top1_unit_interval_topology_is_topology_on
                        top1_unit_interval_topology_is_topology_on]
                    show ?thesis unfolding pi2_def by (by100 simp)
                  qed
                  from top1_continuous_map_on_restrict_domain_simple[OF this hPA_L_sub]
                  show ?thesis .
                qed
                \<comment> \<open>hA continuous I \\<rightarrow> X (codomain enlarged from A to X).\<close>
                have hhA_cont_X: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                    X TX (hA_choice A)"
                proof -
                  have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                      A (subspace_topology X TX A) (hA_choice A)"
                    using hhA_loc unfolding top1_homeomorphism_on_def by (by100 blast)
                  from top1_continuous_map_on_codomain_enlarge[OF this \<open>A \<subseteq> X\<close> subset_refl]
                  have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                      X (subspace_topology X TX X) (hA_choice A)" .
                  moreover have "subspace_topology X TX X = TX"
                  proof (rule subspace_topology_self)
                    show "\<forall>U\<in>TX. U \<subseteq> X"
                      using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
                  qed
                  ultimately show ?thesis by (by100 simp)
                qed
                \<comment> \<open>Codomain restrict to Y.\<close>
                \<comment> \<open>Prove g continuous PA\\_L \\<rightarrow> X, then restrict codomain to Y.\<close>
                \<comment> \<open>Step: pair (\\<sigma>f\\<circ>fst, snd) continuous PA\\_L \\<rightarrow> I\\<times>I.\<close>
                have hpair_cont: "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L)
                    ?II ?IItop (\<lambda>p. (\<sigma>f (fst p), snd p))"
                proof -
                  have "\<And>p. pi1 ((\<lambda>p. (\<sigma>f (fst p), snd p)) p) = \<sigma>f (fst p)"
                    unfolding pi1_def by (by100 simp)
                  hence hcomp1: "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L)
                      top1_unit_interval top1_unit_interval_topology (pi1 \<circ> (\<lambda>p. (\<sigma>f (fst p), snd p)))"
                    using h\<sigma>f_fst_cont unfolding top1_continuous_map_on_def comp_def pi1_def by (by100 auto)
                  have "\<And>p. pi2 ((\<lambda>p. (\<sigma>f (fst p), snd p)) p) = snd p"
                    unfolding pi2_def by (by100 simp)
                  hence hcomp2: "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L)
                      top1_unit_interval top1_unit_interval_topology (pi2 \<circ> (\<lambda>p. (\<sigma>f (fst p), snd p)))"
                    using hsnd_cont unfolding top1_continuous_map_on_def comp_def pi2_def by (by100 auto)
                  from Theorem_18_4[OF hPA_L_top top1_unit_interval_topology_is_topology_on
                      top1_unit_interval_topology_is_topology_on,
                      of "\<lambda>p. (\<sigma>f (fst p), snd p)"]
                  show ?thesis using hcomp1 hcomp2 by (by100 blast)
                qed
                \<comment> \<open>Step: arithmetic (\\<sigma>,t) \\<mapsto> \\<sigma>+t*(0-\\<sigma>) continuous I\\<times>I \\<rightarrow> \\<R> (restrict from \\<R>\\<times>\\<R>).\<close>
                \<comment> \<open>Step: hA cont I \\<rightarrow> X.\<close>
                \<comment> \<open>Step: compose pair + arithmetic + hA.\<close>
                \<comment> \<open>The full composition: hA \\<circ> arith \\<circ> pair, all in one step.
                   arith(\\<sigma>,t) = \\<sigma>+t*(0-\\<sigma>) = \\<sigma>*(1-t). This maps I\\<times>I \\<rightarrow> I.
                   We already have: hpair\\_cont (PA\\_L \\<rightarrow> I\\<times>I), hhA\\_cont\\_X (I \\<rightarrow> X).
                   We need: arith continuous I\\<times>I \\<rightarrow> I.
                   The function is affine\\_map\\_continuous\\_I\\_to\\_I with varying a=0,b=\\<sigma>.
                   But it varies with \\<sigma>, so we can't directly use that fixed-parameter lemma.
                   Instead: use the fact that the composition lands in X (via hA) and image in Y.\<close>
                \<comment> \<open>Build the arithmetic map: (\\<sigma>,t) \\<mapsto> \\<sigma>*(1-t) continuous I\\<times>I \\<rightarrow> I.
                   Strategy: use affine\\_map\\_continuous\\_I\\_to\\_I per fixed \\<sigma>,
                   then show joint continuity via pair + arith from Lemma\\_21\\_4.\<close>
                have harith_II: "top1_continuous_map_on ?II ?IItop
                    top1_unit_interval top1_unit_interval_topology
                    (\<lambda>p. fst p + snd p * (0 - fst p))"
                proof -
                  \<comment> \<open>Use top1\\_continuous\\_map\\_on\\_II\\_to\\_I: continuous\\_on I\\<times>I f + image \\<subseteq> I \\<Rightarrow> our topology.\<close>
                  have hcont_on: "continuous_on (I_set \<times> I_set) (\<lambda>p :: real \<times> real. fst p - snd p * fst p)"
                    by (intro continuous_intros)
                  have himg: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> fst p - snd p * fst p \<in> I_set"
                  proof -
                    fix p :: "real \<times> real" assume "p \<in> I_set \<times> I_set"
                    then obtain \<sigma> t where hp: "p = (\<sigma>, t)" "\<sigma> \<in> I_set" "t \<in> I_set" by (by100 blast)
                    have h\<sigma>: "0 \<le> \<sigma>" "\<sigma> \<le> 1" using hp(2) unfolding top1_unit_interval_def by (by100 auto)+
                    have ht: "0 \<le> t" "t \<le> 1" using hp(3) unfolding top1_unit_interval_def by (by100 auto)+
                    have "t * \<sigma> \<le> 1 * \<sigma>" by (rule mult_right_mono) (use ht h\<sigma> in linarith)+
                    have "t * \<sigma> \<ge> 0" by (rule mult_nonneg_nonneg) (use ht h\<sigma> in linarith)+
                    show "fst p - snd p * fst p \<in> I_set"
                      unfolding hp(1) top1_unit_interval_def
                      using h\<sigma> \<open>t * \<sigma> \<le> _\<close> \<open>t * \<sigma> \<ge> 0\<close> by (by100 auto)
                  qed
                  from top1_continuous_map_on_II_to_I[OF _ hcont_on, unfolded II_topology_def]
                  have "top1_continuous_map_on (I_set \<times> I_set) ?IItop I_set I_top
                      (\<lambda>p. fst p - snd p * fst p)" using himg by (by100 blast)
                  moreover have "\<And>p :: real \<times> real. fst p + snd p * (0 - fst p) = fst p - snd p * fst p"
                    by (by100 simp)
                  hence "\<And>p :: real \<times> real. {q \<in> I_set \<times> I_set. fst q + snd q * (0 - fst q) \<in> V}
                      = {q \<in> I_set \<times> I_set. fst q - snd q * fst q \<in> V}" for V by (by100 auto)
                  ultimately show ?thesis unfolding top1_continuous_map_on_def by (by100 auto)
                qed
                have hg_cont_X: "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L) X TX
                    (\<lambda>p. hA_choice A (\<sigma>f (fst p) + snd p * (0 - \<sigma>f (fst p))))"
                proof -
                  \<comment> \<open>g = hA \\<circ> arith \\<circ> pair.\<close>
                  have "(\<lambda>p. hA_choice A (\<sigma>f (fst p) + snd p * (0 - \<sigma>f (fst p)))) =
                      (\<lambda>p. (hA_choice A \<circ> (\<lambda>q. fst q + snd q * (0 - fst q)) \<circ> (\<lambda>p. (\<sigma>f (fst p), snd p))) p)"
                    unfolding comp_def by (by100 simp)
                  have hstep1: "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L)
                      top1_unit_interval top1_unit_interval_topology
                      ((\<lambda>q. fst q + snd q * (0 - fst q)) \<circ> (\<lambda>p. (\<sigma>f (fst p), snd p)))"
                    by (rule top1_continuous_map_on_comp[OF hpair_cont harith_II])
                  have hstep2: "top1_continuous_map_on PA_L (subspace_topology ?II ?IItop PA_L) X TX
                      (hA_choice A \<circ> ((\<lambda>q. fst q + snd q * (0 - fst q)) \<circ> (\<lambda>p. (\<sigma>f (fst p), snd p))))"
                    by (rule top1_continuous_map_on_comp[OF hstep1 hhA_cont_X])
                  moreover have "\<And>p. (hA_choice A \<circ> ((\<lambda>q. fst q + snd q * (0 - fst q)) \<circ>
                      (\<lambda>p. (\<sigma>f (fst p), snd p)))) p =
                      hA_choice A (\<sigma>f (fst p) + snd p * (0 - \<sigma>f (fst p)))"
                    unfolding comp_def by (by100 simp)
                  ultimately show ?thesis unfolding top1_continuous_map_on_def by (by100 auto)
                qed
                have "\<forall>p\<in>PA_L. hA_choice A (\<sigma>f (fst p) + snd p * (0 - \<sigma>f (fst p))) \<in> ?Y"
                proof (intro ballI)
                  fix p assume "p \<in> PA_L"
                  hence "H p \<in> ?Y" using hH_img_PA hPA_eq by (by100 blast)
                  thus "hA_choice A (\<sigma>f (fst p) + snd p * (0 - \<sigma>f (fst p))) \<in> ?Y"
                    using hH_eq_PA_L \<open>p \<in> PA_L\<close> by (by100 auto)
                qed
                show ?thesis
                  by (rule continuous_map_restrict_codomain[OF hg_cont_X \<open>\<forall>p\<in>PA_L. _ \<in> ?Y\<close> hY_sub])
              qed
              show ?thesis
              proof -
                have "\<forall>p\<in>PA_L. H p \<in> ?Y" using hH_img_PA hPA_eq by (by100 blast)
                have "\<forall>V\<in>?TY. {p \<in> PA_L. H p \<in> V} \<in> subspace_topology ?II ?IItop PA_L"
                proof (intro ballI)
                  fix V assume "V \<in> ?TY"
                  have "{p \<in> PA_L. H p \<in> V} = {p \<in> PA_L. hA_choice A (\<sigma>f (fst p) + snd p * (0 - \<sigma>f (fst p))) \<in> V}"
                    using hH_eq_PA_L by (by100 auto)
                  also have "... \<in> subspace_topology ?II ?IItop PA_L"
                    using hg_cont \<open>V \<in> ?TY\<close> unfolding top1_continuous_map_on_def by (by100 blast)
                  finally show "{p \<in> PA_L. H p \<in> V} \<in> subspace_topology ?II ?IItop PA_L" .
                qed
                show ?thesis unfolding top1_continuous_map_on_def
                  using hPA_L_top hTY_top \<open>\<forall>p\<in>PA_L. H p \<in> ?Y\<close> \<open>\<forall>V\<in>?TY. _\<close> by (by100 blast)
              qed
            qed
            have hH_PA_R: "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R) ?Y ?TY H"
            proof -
              have hPA_R_sub: "PA_R \<subseteq> ?II" unfolding PA_R_def by (by100 blast)
              have hPA_R_top: "is_topology_on PA_R (subspace_topology ?II ?IItop PA_R)"
                by (rule subspace_topology_is_topology_on[OF hII_top hPA_R_sub])
              have hH_eq_PA_R: "\<forall>p\<in>PA_R. H p = hA_choice A (\<sigma>f (fst p) + snd p * (1 - \<sigma>f (fst p)))"
              proof (intro ballI)
                fix p assume "p \<in> PA_R"
                then obtain s t where hst: "p = (s, t)" "s \<in> top1_unit_interval" "f s \<in> RA A"
                    "t \<in> top1_unit_interval"
                  unfolding PA_R_def by (by100 blast)
                have hbij_loc: "bij_betw (hA_choice A) top1_unit_interval A"
                  using hhA[OF \<open>A \<in> NT\<close>] unfolding top1_homeomorphism_on_def by (by100 blast)
                have hinj_loc: "inj_on (hA_choice A) top1_unit_interval"
                  using hbij_loc unfolding bij_betw_def by (by100 blast)
                have himg_loc: "hA_choice A ` top1_unit_interval = A"
                  using hbij_loc unfolding bij_betw_def by (by100 blast)
                have "f s \<in> A" using hst(3) unfolding RA_def by (by100 blast)
                have "f s \<in> hA_choice A ` top1_unit_interval" using \<open>f s \<in> A\<close> himg_loc by (by100 simp)
                show "H p = hA_choice A (\<sigma>f (fst p) + snd p * (1 - \<sigma>f (fst p)))"
                proof (cases "f s \<in> T")
                  case True
                  have "f s \<in> T \<inter> A" using True \<open>f s \<in> A\<close> by (by100 blast)
                  have "A \<in> \<A>" using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
                  from hT_subgraph[rule_format, OF \<open>A \<in> \<A>\<close>]
                  have "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
                    using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
                  have h1_I: "(1::real) \<in> top1_unit_interval"
                    unfolding top1_unit_interval_def by (by100 auto)
                  have "\<sigma>f s = 1"
                  proof -
                    have "inv_into top1_unit_interval (hA_choice A) (f s) \<ge> tA A"
                      using hst(3) unfolding RA_def by (by100 blast)
                    have "f s \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                      using \<open>f s \<in> T \<inter> A\<close> \<open>A \<inter> T \<subseteq> _\<close> by (by100 blast)
                    have hX_haus_l: "is_hausdorff_on X TX"
                      using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                    have harc_l: "top1_is_arc_on A (subspace_topology X TX A)"
                      using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                    obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
                        A (subspace_topology X TX A) h" using harc_l unfolding top1_is_arc_on_def by (by100 blast)
                    have "top1_arc_endpoints_on A (subspace_topology X TX A) = {h 0, h 1}"
                      using arc_endpoints_are_boundary[OF hX_strict hX_haus_l _ harc_l hh]
                      h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                    have hep_A: "top1_arc_endpoints_on A (subspace_topology X TX A) = {hA_choice A 0, hA_choice A 1}"
                      using arc_endpoints_are_boundary[OF hX_strict hX_haus_l _ harc_l hhA_loc]
                      h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                    hence "f s = hA_choice A 0 \<or> f s = hA_choice A 1"
                      using \<open>f s \<in> top1_arc_endpoints_on A _\<close> by (by100 auto)
                    moreover have "f s \<noteq> hA_choice A 0"
                    proof
                      assume "f s = hA_choice A 0"
                      have h0_I: "(0::real) \<in> top1_unit_interval"
                        unfolding top1_unit_interval_def by (by100 auto)
                      have "inv_into top1_unit_interval (hA_choice A) (hA_choice A 0) = 0"
                        using inv_into_f_f[OF hinj_loc h0_I] by (by100 simp)
                      hence "\<sigma>f s = 0" using \<open>f s = hA_choice A 0\<close> unfolding \<sigma>f_def by (by100 simp)
                      have "ps A \<in> hA_choice A ` top1_unit_interval"
                        using hps[rule_format, OF \<open>A \<in> NT\<close>] himg_loc by (by100 blast)
                      have "tA A \<in> top1_unit_interval"
                        unfolding tA_def by (rule inv_into_into[OF \<open>ps A \<in> _\<close>])
                      have "tA A \<noteq> 0"
                      proof
                        assume "tA A = 0"
                        have "hA_choice A (tA A) = ps A"
                          unfolding tA_def by (rule f_inv_into_f[OF \<open>ps A \<in> _\<close>])
                        hence "ps A = hA_choice A 0" using \<open>tA A = 0\<close> by (by100 simp)
                        have hX_haus: "is_hausdorff_on X TX"
                          using hgraph unfolding top1_is_graph_on_def by (by100 blast)
                        have hep_A: "top1_arc_endpoints_on A (subspace_topology X TX A) = {hA_choice A 0, hA_choice A 1}"
                          using arc_endpoints_are_boundary[OF hX_strict hX_haus _ _ hhA_loc]
                          h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
                        hence "ps A \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
                          using \<open>ps A = hA_choice A 0\<close> by (by100 simp)
                        thus False using hps[rule_format, OF \<open>A \<in> NT\<close>] by (by100 blast)
                      qed
                      hence "tA A > 0" using \<open>tA A \<in> top1_unit_interval\<close>
                        unfolding top1_unit_interval_def by (by100 auto)
                      thus False using \<open>\<sigma>f s = 0\<close> \<open>inv_into _ _ (f s) \<ge> tA A\<close>
                        unfolding \<sigma>f_def by (by100 linarith)
                    qed
                    ultimately have "f s = hA_choice A 1" by (by100 blast)
                    hence "\<sigma>f s = 1" unfolding \<sigma>f_def
                      using inv_into_f_f[OF hinj_loc h1_I] by (by100 simp)
                    thus ?thesis .
                  qed
                  have "H p = f s" using True hst(1) unfolding H_def by (by100 simp)
                  moreover have "f s = hA_choice A 1"
                  proof -
                    have "hA_choice A (\<sigma>f s) = f s"
                      unfolding \<sigma>f_def by (rule f_inv_into_f[OF \<open>f s \<in> hA_choice A ` top1_unit_interval\<close>])
                    thus ?thesis using \<open>\<sigma>f s = 1\<close> by (by100 simp)
                  qed
                  moreover have "hA_choice A (1 + t * (1 - 1)) = hA_choice A 1" by (by100 simp)
                  ultimately show ?thesis using hst(1) \<open>\<sigma>f s = 1\<close> by (by100 simp)
                next
                  case False
                  have "f s \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
                  proof -
                    have "A \<in> \<A>" using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
                    show ?thesis using hvertices_T[rule_format, OF \<open>A \<in> \<A>\<close>] False by (by100 blast)
                  qed
                  have hTHE: "(THE A'. A' \<in> NT \<and> f s \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')) = A"
                  proof (rule the_equality)
                    show "A \<in> NT \<and> f s \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)"
                      using \<open>A \<in> NT\<close> \<open>f s \<in> A\<close> \<open>f s \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
                  next
                    fix A' assume h: "A' \<in> NT \<and> f s \<in> A' - top1_arc_endpoints_on A' (subspace_topology X TX A')"
                    hence "A' \<in> \<A>" "f s \<in> A'" using hNT_def by (by100 blast)+
                    have "A \<in> \<A>" using \<open>A \<in> NT\<close> hNT_def by (by100 blast)
                    show "A' = A"
                    proof (rule ccontr)
                      assume "A' \<noteq> A"
                      from h\<A>_inter[rule_format, OF \<open>A \<in> \<A>\<close> \<open>A' \<in> \<A>\<close> \<open>A' \<noteq> A\<close>[symmetric]]
                      show False using \<open>f s \<in> A\<close> \<open>f s \<in> A'\<close> \<open>f s \<notin> top1_arc_endpoints_on A _\<close> by (by100 blast)
                    qed
                  qed
                  have h\<sigma>_ge: "\<sigma>f s \<ge> tA A"
                    using hst(3) unfolding RA_def \<sigma>f_def by (by100 blast)
                  have h\<sigma>_ne: "\<sigma>f s \<noteq> tA A"
                  proof
                    assume "\<sigma>f s = tA A"
                    have "hA_choice A (\<sigma>f s) = f s"
                      unfolding \<sigma>f_def by (rule f_inv_into_f[OF \<open>f s \<in> hA_choice A ` top1_unit_interval\<close>])
                    have "ps A \<in> hA_choice A ` top1_unit_interval"
                      using hps[rule_format, OF \<open>A \<in> NT\<close>] himg_loc by (by100 blast)
                    have "hA_choice A (tA A) = ps A"
                      unfolding tA_def by (rule f_inv_into_f[OF \<open>ps A \<in> hA_choice A ` top1_unit_interval\<close>])
                    hence "f s = ps A" using \<open>hA_choice A (\<sigma>f s) = f s\<close> \<open>\<sigma>f s = tA A\<close> by (by100 simp)
                    thus False using hst(3) \<open>A \<in> NT\<close> unfolding RA_def by (by100 blast)
                  qed
                  hence h\<sigma>_gt: "\<sigma>f s > tA A" using h\<sigma>_ge by (by100 linarith)
                  hence "\<not> (\<sigma>f s < tA A)" by (by100 linarith)
                  hence "(if inv_into top1_unit_interval (hA_choice A) (f s) < tA A then (0::real) else 1) = 1"
                    unfolding \<sigma>f_def by (by100 simp)
                  have "H (s, t) = (let A' = THE A'. A' \<in> NT \<and> f s \<in> A' -
                      top1_arc_endpoints_on A' (subspace_topology X TX A') in
                      let h = hA_choice A' in
                      let \<sigma> = inv_into top1_unit_interval h (f s) in
                      let ep = (if \<sigma> < tA A' then 0 else 1) in h (\<sigma> + t * (ep - \<sigma>)))"
                    unfolding H_def using False by (by100 simp)
                  hence "H (s, t) = hA_choice A (inv_into top1_unit_interval (hA_choice A) (f s) +
                      t * ((if inv_into top1_unit_interval (hA_choice A) (f s) < tA A then 0 else 1) -
                           inv_into top1_unit_interval (hA_choice A) (f s)))"
                    using hTHE unfolding Let_def by (by100 simp)
                  hence "H (s, t) = hA_choice A (\<sigma>f s + t * (1 - \<sigma>f s))"
                    using \<open>(if inv_into _ _ (f s) < tA A then (0::real) else 1) = 1\<close>
                    unfolding \<sigma>f_def by (by100 simp)
                  thus ?thesis using hst(1) by (by100 simp)
                qed
              qed
              have hg_cont_R: "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R) ?Y ?TY
                  (\<lambda>p. hA_choice A (\<sigma>f (fst p) + snd p * (1 - \<sigma>f (fst p))))"
              proof -
                have hPA_R_sub: "PA_R \<subseteq> ?II" unfolding PA_R_def by (by100 blast)
                have hPA_R_top: "is_topology_on PA_R (subspace_topology ?II ?IItop PA_R)"
                  by (rule subspace_topology_is_topology_on[OF hII_top hPA_R_sub])
                \<comment> \<open>Same chain as PA\\_L: \\<sigma>f\\<circ>fst cont, snd cont, pair cont, arith, hA, restrict.\<close>
                have hfst_cont_R: "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R)
                    top1_unit_interval top1_unit_interval_topology fst"
                proof -
                  have "top1_continuous_map_on ?II ?IItop top1_unit_interval top1_unit_interval_topology fst"
                  proof -
                    from top1_continuous_pi1[OF top1_unit_interval_topology_is_topology_on
                        top1_unit_interval_topology_is_topology_on]
                    show ?thesis unfolding pi1_def by (by100 simp)
                  qed
                  from top1_continuous_map_on_restrict_domain_simple[OF this hPA_R_sub]
                  show ?thesis .
                qed
                have hfst_img_R: "\<forall>p\<in>PA_R. f (fst p) \<in> RA A"
                  unfolding PA_R_def by (by100 auto)
                have hf_cont_R: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?Y ?TY f"
                  using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
                have hffst_cont_R: "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R) ?Y ?TY (f \<circ> fst)"
                  by (rule top1_continuous_map_on_comp[OF hfst_cont_R hf_cont_R])
                have hRA_sub_Y: "RA A \<subseteq> ?Y" unfolding RA_def by (by100 blast)
                have hffst_RA: "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R)
                    (RA A) (subspace_topology ?Y ?TY (RA A)) (f \<circ> fst)"
                proof (rule continuous_map_restrict_codomain[OF hffst_cont_R _ hRA_sub_Y])
                  show "\<forall>p\<in>PA_R. (f \<circ> fst) p \<in> RA A" using hfst_img_R by (by100 simp)
                qed
                have hRA_sub_A: "RA A \<subseteq> A" unfolding RA_def by (by100 blast)
                have "subspace_topology ?Y ?TY (RA A) = subspace_topology A (subspace_topology X TX A) (RA A)"
                proof -
                  have "subspace_topology ?Y ?TY (RA A) = subspace_topology X TX (RA A)"
                    by (rule subspace_topology_trans[OF hRA_sub_Y])
                  also have "... = subspace_topology A (subspace_topology X TX A) (RA A)"
                    by (rule subspace_topology_trans[OF hRA_sub_A, symmetric])
                  finally show ?thesis .
                qed
                have hinv_cont_R: "top1_continuous_map_on A (subspace_topology X TX A)
                    top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval (hA_choice A))"
                  using hhA_loc unfolding top1_homeomorphism_on_def by (by100 blast)
                have hinv_cont_RA: "top1_continuous_map_on (RA A) (subspace_topology ?Y ?TY (RA A))
                    top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval (hA_choice A))"
                proof -
                  have "top1_continuous_map_on (RA A) (subspace_topology A (subspace_topology X TX A) (RA A))
                      top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval (hA_choice A))"
                    by (rule top1_continuous_map_on_restrict_domain_simple[OF hinv_cont_R hRA_sub_A])
                  thus ?thesis using \<open>subspace_topology ?Y ?TY (RA A) = _\<close> by (by100 simp)
                qed
                have h\<sigma>f_fst_cont_R: "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R)
                    top1_unit_interval top1_unit_interval_topology (\<lambda>p. \<sigma>f (fst p))"
                proof -
                  from top1_continuous_map_on_comp[OF hffst_RA hinv_cont_RA]
                  have "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R)
                      top1_unit_interval top1_unit_interval_topology
                      ((inv_into top1_unit_interval (hA_choice A)) \<circ> (f \<circ> fst))" .
                  moreover have "\<And>p. ((inv_into top1_unit_interval (hA_choice A)) \<circ> (f \<circ> fst)) p = \<sigma>f (fst p)"
                    unfolding \<sigma>f_def comp_def by (by100 simp)
                  ultimately show ?thesis unfolding top1_continuous_map_on_def by (by100 auto)
                qed
                have hsnd_cont_R: "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R)
                    top1_unit_interval top1_unit_interval_topology snd"
                proof -
                  have "top1_continuous_map_on ?II ?IItop top1_unit_interval top1_unit_interval_topology snd"
                  proof -
                    from top1_continuous_pi2[OF top1_unit_interval_topology_is_topology_on
                        top1_unit_interval_topology_is_topology_on]
                    show ?thesis unfolding pi2_def by (by100 simp)
                  qed
                  from top1_continuous_map_on_restrict_domain_simple[OF this hPA_R_sub]
                  show ?thesis .
                qed
                \<comment> \<open>Pair (\\<sigma>f\\<circ>fst, snd) continuous PA\\_R \\<rightarrow> I\\<times>I.\<close>
                have hpair_cont_R: "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R)
                    ?II ?IItop (\<lambda>p. (\<sigma>f (fst p), snd p))"
                proof -
                  have "\<And>p. pi1 ((\<lambda>p. (\<sigma>f (fst p), snd p)) p) = \<sigma>f (fst p)"
                    unfolding pi1_def by (by100 simp)
                  hence hc1: "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R)
                      top1_unit_interval top1_unit_interval_topology (pi1 \<circ> (\<lambda>p. (\<sigma>f (fst p), snd p)))"
                    using h\<sigma>f_fst_cont_R unfolding top1_continuous_map_on_def comp_def pi1_def by (by100 auto)
                  have "\<And>p. pi2 ((\<lambda>p. (\<sigma>f (fst p), snd p)) p) = snd p"
                    unfolding pi2_def by (by100 simp)
                  hence hc2: "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R)
                      top1_unit_interval top1_unit_interval_topology (pi2 \<circ> (\<lambda>p. (\<sigma>f (fst p), snd p)))"
                    using hsnd_cont_R unfolding top1_continuous_map_on_def comp_def pi2_def by (by100 auto)
                  from Theorem_18_4[OF hPA_R_top top1_unit_interval_topology_is_topology_on
                      top1_unit_interval_topology_is_topology_on,
                      of "\<lambda>p. (\<sigma>f (fst p), snd p)"]
                  show ?thesis using hc1 hc2 by (by100 blast)
                qed
                \<comment> \<open>Compose pair + arithmetic + hA \\<rightarrow> X, then restrict to Y.\<close>
                have harith_II_R: "top1_continuous_map_on ?II ?IItop
                    top1_unit_interval top1_unit_interval_topology
                    (\<lambda>p. fst p + snd p * (1 - fst p))"
                proof -
                  have hcont_on: "continuous_on (I_set \<times> I_set)
                      (\<lambda>p :: real \<times> real. fst p + snd p - snd p * fst p)"
                    by (intro continuous_intros)
                  have himg: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> fst p + snd p - snd p * fst p \<in> I_set"
                  proof -
                    fix p :: "real \<times> real" assume "p \<in> I_set \<times> I_set"
                    then obtain \<sigma> t where hp: "p = (\<sigma>, t)" "\<sigma> \<in> I_set" "t \<in> I_set" by (by100 blast)
                    have h\<sigma>: "0 \<le> \<sigma>" "\<sigma> \<le> 1" using hp(2) unfolding top1_unit_interval_def by (by100 auto)+
                    have ht: "0 \<le> t" "t \<le> 1" using hp(3) unfolding top1_unit_interval_def by (by100 auto)+
                    have "t * (1 - \<sigma>) \<ge> 0" by (rule mult_nonneg_nonneg) (use ht h\<sigma> in linarith)+
                    have hle: "t * (1 - \<sigma>) \<le> 1 * (1 - \<sigma>)" by (rule mult_right_mono) (use ht h\<sigma> in linarith)+
                    hence "t * (1 - \<sigma>) \<le> 1 - \<sigma>" by (by100 simp)
                    have "t * (1 - \<sigma>) = t - t * \<sigma>"
                      using right_diff_distrib[of t 1 \<sigma>] by (by100 simp)
                    hence "t - t * \<sigma> \<le> 1 - \<sigma>" using \<open>t * (1 - \<sigma>) \<le> 1 - \<sigma>\<close> by (by100 linarith)
                    hence "\<sigma> + t - t * \<sigma> \<le> 1" by (by100 linarith)
                    have "t * \<sigma> \<le> 1 * \<sigma>" by (rule mult_right_mono) (use ht h\<sigma> in linarith)+
                    hence "t * \<sigma> \<le> \<sigma>" by (by100 simp)
                    show "fst p + snd p - snd p * fst p \<in> I_set"
                      unfolding hp(1) top1_unit_interval_def
                      using h\<sigma> ht \<open>t * (1 - \<sigma>) \<ge> 0\<close> \<open>\<sigma> + t - t * \<sigma> \<le> 1\<close> \<open>t * \<sigma> \<le> \<sigma>\<close> by (by100 auto)
                  qed
                  have heq: "\<And>p :: real \<times> real. fst p + snd p * (1 - fst p) = fst p + snd p - snd p * fst p"
                  proof -
                    fix p :: "real \<times> real"
                    have "snd p * (1 - fst p) = snd p * 1 - snd p * fst p"
                      by (rule right_diff_distrib)
                    thus "fst p + snd p * (1 - fst p) = fst p + snd p - snd p * fst p"
                      by (by100 simp)
                  qed
                  have hcont_on': "continuous_on (I_set \<times> I_set)
                      (\<lambda>p :: real \<times> real. fst p + snd p * (1 - fst p))"
                    by (intro continuous_intros)
                  have himg': "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> fst p + snd p * (1 - fst p) \<in> I_set"
                  proof -
                    fix p :: "real \<times> real" assume hp: "p \<in> I_set \<times> I_set"
                    then obtain a b where hab: "p = (a, b)" "a \<in> I_set" "b \<in> I_set" by (by100 blast)
                    have ha: "0 \<le> a" "a \<le> 1" using hab(2) unfolding top1_unit_interval_def by (by100 auto)+
                    have hb: "0 \<le> b" "b \<le> 1" using hab(3) unfolding top1_unit_interval_def by (by100 auto)+
                    have "b * (1 - a) \<ge> 0" by (rule mult_nonneg_nonneg) (use hb ha in linarith)+
                    have "b * (1 - a) \<le> 1 * (1 - a)" by (rule mult_right_mono) (use hb ha in linarith)+
                    hence "b * (1 - a) \<le> 1 - a" by (by100 simp)
                    hence "a + b * (1 - a) \<le> 1" by (by100 linarith)
                    show "fst p + snd p * (1 - fst p) \<in> I_set" unfolding hab(1) top1_unit_interval_def
                      using ha \<open>b * (1 - a) \<ge> 0\<close> \<open>a + b * (1 - a) \<le> 1\<close> by (by100 auto)
                  qed
                  from top1_continuous_map_on_II_to_I[OF himg' hcont_on', unfolded II_topology_def]
                  show ?thesis .
                qed
                have hg_cont_X_R: "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R) X TX
                    (\<lambda>p. hA_choice A (\<sigma>f (fst p) + snd p * (1 - \<sigma>f (fst p))))"
                proof -
                  have hstep1: "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R)
                      top1_unit_interval top1_unit_interval_topology
                      ((\<lambda>q. fst q + snd q * (1 - fst q)) \<circ> (\<lambda>p. (\<sigma>f (fst p), snd p)))"
                    by (rule top1_continuous_map_on_comp[OF hpair_cont_R harith_II_R])
                  have hhA_cont_X_R: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                      X TX (hA_choice A)"
                  proof -
                    have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                        A (subspace_topology X TX A) (hA_choice A)"
                      using hhA_loc unfolding top1_homeomorphism_on_def by (by100 blast)
                    have hA_sub_R: "A \<subseteq> X" using h\<A> \<open>A \<in> NT\<close> hNT_def by (by100 blast)
                    have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
                        X (subspace_topology X TX X) (hA_choice A)"
                      by (rule top1_continuous_map_on_codomain_enlarge[OF
                          \<open>top1_continuous_map_on _ _ A (subspace_topology X TX A) _\<close> hA_sub_R subset_refl])
                    moreover have "subspace_topology X TX X = TX"
                    proof (rule subspace_topology_self)
                      show "\<forall>U\<in>TX. U \<subseteq> X"
                        using hX_strict unfolding is_topology_on_strict_def by (by100 blast)
                    qed
                    ultimately show ?thesis by (by100 simp)
                  qed
                  have hstep2: "top1_continuous_map_on PA_R (subspace_topology ?II ?IItop PA_R) X TX
                      (hA_choice A \<circ> ((\<lambda>q. fst q + snd q * (1 - fst q)) \<circ> (\<lambda>p. (\<sigma>f (fst p), snd p))))"
                    by (rule top1_continuous_map_on_comp[OF hstep1 hhA_cont_X_R])
                  moreover have "\<And>p. (hA_choice A \<circ> ((\<lambda>q. fst q + snd q * (1 - fst q)) \<circ>
                      (\<lambda>p. (\<sigma>f (fst p), snd p)))) p =
                      hA_choice A (\<sigma>f (fst p) + snd p * (1 - \<sigma>f (fst p)))"
                    unfolding comp_def by (by100 simp)
                  ultimately show ?thesis unfolding top1_continuous_map_on_def by (by100 auto)
                qed
                have "\<forall>p\<in>PA_R. hA_choice A (\<sigma>f (fst p) + snd p * (1 - \<sigma>f (fst p))) \<in> ?Y"
                proof (intro ballI)
                  fix p assume "p \<in> PA_R"
                  hence "H p \<in> ?Y" using hH_img_PA hPA_eq by (by100 blast)
                  thus "hA_choice A (\<sigma>f (fst p) + snd p * (1 - \<sigma>f (fst p))) \<in> ?Y"
                    using hH_eq_PA_R \<open>p \<in> PA_R\<close> by (by100 auto)
                qed
                show ?thesis
                  by (rule continuous_map_restrict_codomain[OF hg_cont_X_R \<open>\<forall>p\<in>PA_R. _ \<in> ?Y\<close> hY_sub])
              qed
              show ?thesis
              proof -
                have "\<forall>p\<in>PA_R. H p \<in> ?Y" using hH_img_PA hPA_eq by (by100 blast)
                have "\<forall>V\<in>?TY. {p \<in> PA_R. H p \<in> V} \<in> subspace_topology ?II ?IItop PA_R"
                proof (intro ballI)
                  fix V assume "V \<in> ?TY"
                  have "{p \<in> PA_R. H p \<in> V} = {p \<in> PA_R. hA_choice A (\<sigma>f (fst p) + snd p * (1 - \<sigma>f (fst p))) \<in> V}"
                    using hH_eq_PA_R by (by100 auto)
                  also have "... \<in> subspace_topology ?II ?IItop PA_R"
                    using hg_cont_R \<open>V \<in> ?TY\<close> unfolding top1_continuous_map_on_def by (by100 blast)
                  finally show "{p \<in> PA_R. H p \<in> V} \<in> subspace_topology ?II ?IItop PA_R" .
                qed
                show ?thesis unfolding top1_continuous_map_on_def
                  using hPA_R_top hTY_top \<open>\<forall>p\<in>PA_R. H p \<in> ?Y\<close> \<open>\<forall>V\<in>?TY. _\<close> by (by100 blast)
              qed
            qed
            \<comment> \<open>Pasting PA\\_L and PA\\_R gives H continuous on PA(A).\<close>
            \<comment> \<open>PA\\_L, PA\\_R closed in PA(A) (from closed in I\\<times>I + Theorem\\_17\\_2).\<close>
            have hPA_L_closed_PA: "closedin_on (PA A) (subspace_topology ?II ?IItop (PA A)) PA_L"
            proof -
              from Theorem_17_2[OF hII_top hPA_sub, of PA_L]
              have "closedin_on (PA A) (subspace_topology ?II ?IItop (PA A)) PA_L \<longleftrightarrow>
                  (\<exists>C. closedin_on ?II ?IItop C \<and> PA_L = C \<inter> PA A)" .
              moreover have "PA_L \<subseteq> PA A" unfolding PA_L_def PA_def LA_def by (by100 blast)
              hence "PA_L = PA_L \<inter> PA A" by (by100 blast)
              ultimately show ?thesis using hPA_L_closed by (by100 blast)
            qed
            have hPA_R_closed_PA: "closedin_on (PA A) (subspace_topology ?II ?IItop (PA A)) PA_R"
            proof -
              from Theorem_17_2[OF hII_top hPA_sub, of PA_R]
              have "closedin_on (PA A) (subspace_topology ?II ?IItop (PA A)) PA_R \<longleftrightarrow>
                  (\<exists>C. closedin_on ?II ?IItop C \<and> PA_R = C \<inter> PA A)" .
              moreover have "PA_R \<subseteq> PA A" unfolding PA_R_def PA_def RA_def by (by100 blast)
              hence "PA_R = PA_R \<inter> PA A" by (by100 blast)
              ultimately show ?thesis using hPA_R_closed by (by100 blast)
            qed
            \<comment> \<open>H continuous on PA\\_L in PA(A)'s subspace topology.\<close>
            have hH_PA_L_PA: "top1_continuous_map_on PA_L
                (subspace_topology (PA A) (subspace_topology ?II ?IItop (PA A)) PA_L) ?Y ?TY H"
            proof -
              have "subspace_topology (PA A) (subspace_topology ?II ?IItop (PA A)) PA_L
                  = subspace_topology ?II ?IItop PA_L"
                by (rule subspace_topology_trans)
                   (use hPA_eq in \<open>by100 blast\<close>)
              thus ?thesis using hH_PA_L by (by100 simp)
            qed
            have hH_PA_R_PA: "top1_continuous_map_on PA_R
                (subspace_topology (PA A) (subspace_topology ?II ?IItop (PA A)) PA_R) ?Y ?TY H"
            proof -
              have "subspace_topology (PA A) (subspace_topology ?II ?IItop (PA A)) PA_R
                  = subspace_topology ?II ?IItop PA_R"
                by (rule subspace_topology_trans)
                   (use hPA_eq in \<open>by100 blast\<close>)
              thus ?thesis using hH_PA_R by (by100 simp)
            qed
            show "top1_continuous_map_on (PA A) (subspace_topology ?II ?IItop (PA A)) ?Y ?TY H"
              by (rule pasting_lemma_two_closed[OF hPA_top hTY_top
                  hPA_L_closed_PA hPA_R_closed_PA hPA_eq[symmetric] hH_img_PA
                  hH_PA_L_PA hH_PA_R_PA])
          qed
          \<comment> \<open>Pasting for finitely many closed pieces: use induction on NT.\<close>
          \<comment> \<open>Finite pasting: S\\_B = \\<Union>{PA A | A \\<in> NT}.\<close>
          have hSB_sub_II: "S_B \<subseteq> ?II" unfolding S_B_def by (by100 blast)
          have hSB_top: "is_topology_on S_B (subspace_topology ?II ?IItop S_B)"
            by (rule subspace_topology_is_topology_on[OF hII_top hSB_sub_II])
          have hH_img_SB: "\<forall>p\<in>S_B. H p \<in> ?Y" using hH_img_II hSB_sub_II by (by100 blast)
          have hH_preimg_SB: "\<forall>V\<in>?TY. {p \<in> S_B. H p \<in> V} \<in> subspace_topology ?II ?IItop S_B"
          proof (intro ballI)
            fix V assume "V \<in> ?TY"
            \<comment> \<open>Complement: S\\_B - preimage = \\<Union>{PA A \\<cap> complement | A \\<in> NT}.\<close>
            \<comment> \<open>Actually: preimage = \\<Union>{PA A \\<cap> preimage | A \\<in> NT}.\<close>
            have "{p \<in> S_B. H p \<in> V} = (\<Union>A\<in>NT. {p \<in> PA A. H p \<in> V})"
              using hSB_eq by (by100 blast)
            \<comment> \<open>Each {p \\<in> PA A. H p \\<in> V} is open in PA A (from hH\\_PA continuous).\<close>
            \<comment> \<open>Hence = W \\<cap> PA A for some W open in I\\<times>I.\<close>
            \<comment> \<open>So the union = \\<Union>{W\\_A \\<cap> PA A | A \\<in> NT} \\<subseteq> S\\_B.\<close>
            \<comment> \<open>This is open in S\\_B iff it's the intersection of an open set with S\\_B.\<close>
            \<comment> \<open>Alternatively: complement closed. Complement = \\<Union>{PA A - preimage | A \\<in> NT}.
               Each PA A - preimage is closed in PA A (since preimage open in PA A).
               Closed in PA A + PA A closed in I\\<times>I \\<Rightarrow> closed in I\\<times>I.
               Finite union of closed = closed in I\\<times>I.
               Intersect with S\\_B: closed in S\\_B.\<close>
            have "S_B - {p \<in> S_B. H p \<in> V} = (\<Union>A\<in>NT. PA A - {p \<in> PA A. H p \<in> V})"
              using hSB_eq by (by100 blast)
            \<comment> \<open>Each PA A - preimage is closed in I\\<times>I.\<close>
            have hPA_compl_closed: "\<forall>A\<in>NT. closedin_on ?II ?IItop (PA A - {p \<in> PA A. H p \<in> V})"
            proof (intro ballI)
              fix A assume "A \<in> NT"
              have "closedin_on (PA A) (subspace_topology ?II ?IItop (PA A)) (PA A - {p \<in> PA A. H p \<in> V})"
              proof -
                have "{p \<in> PA A. H p \<in> V} \<in> subspace_topology ?II ?IItop (PA A)"
                  using hH_PA \<open>A \<in> NT\<close> \<open>V \<in> ?TY\<close> unfolding top1_continuous_map_on_def by (by100 blast)
                have "PA A \<subseteq> ?II"
                  using hPA_closed \<open>A \<in> NT\<close> unfolding closedin_on_def by (by100 blast)
                have hPA_top: "is_topology_on (PA A) (subspace_topology ?II ?IItop (PA A))"
                  by (rule subspace_topology_is_topology_on[OF hII_top \<open>PA A \<subseteq> ?II\<close>])
                have "PA A - {p \<in> PA A. H p \<in> V} \<subseteq> PA A" by (by100 blast)
                moreover have "PA A - (PA A - {p \<in> PA A. H p \<in> V}) = {p \<in> PA A. H p \<in> V}"
                  by (by100 blast)
                hence "PA A - (PA A - {p \<in> PA A. H p \<in> V}) \<in> subspace_topology ?II ?IItop (PA A)"
                  using \<open>{p \<in> PA A. H p \<in> V} \<in> _\<close> by (by100 simp)
                ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
              qed
              from Theorem_17_3[OF hII_top _ this]
              show "closedin_on ?II ?IItop (PA A - {p \<in> PA A. H p \<in> V})"
                using hPA_closed \<open>A \<in> NT\<close> by (by100 blast)
            qed
            have "closedin_on ?II ?IItop (\<Union>A\<in>NT. PA A - {p \<in> PA A. H p \<in> V})"
              by (rule closedin_on_finite_indexed_Union[OF hII_top hNT_fin])
                 (use hPA_compl_closed in \<open>by100 blast\<close>)
            hence "closedin_on ?II ?IItop (S_B - {p \<in> S_B. H p \<in> V})"
              using \<open>S_B - {p \<in> S_B. H p \<in> V} = _\<close> by (by100 simp)
            \<comment> \<open>Closed in I\\<times>I \\<cap> S\\_B = closed in S\\_B.\<close>
            from Theorem_17_2[OF hII_top hSB_sub_II, of "S_B - {p \<in> S_B. H p \<in> V}"]
            have "closedin_on S_B (subspace_topology ?II ?IItop S_B) (S_B - {p \<in> S_B. H p \<in> V})"
              using \<open>closedin_on ?II ?IItop (S_B - {p \<in> S_B. H p \<in> V})\<close> by (by100 blast)
            hence "S_B - (S_B - {p \<in> S_B. H p \<in> V}) \<in> subspace_topology ?II ?IItop S_B"
              unfolding closedin_on_def by (by100 blast)
            moreover have "S_B - (S_B - {p \<in> S_B. H p \<in> V}) = {p \<in> S_B. H p \<in> V}" by (by100 blast)
            ultimately show "{p \<in> S_B. H p \<in> V} \<in> subspace_topology ?II ?IItop S_B" by (by100 simp)
          qed
          show ?thesis unfolding top1_continuous_map_on_def
            using hSB_top hTY_top hH_img_SB hH_preimg_SB by (by100 blast)
        qed
        show ?thesis
          by (rule pasting_lemma_two_closed[OF hII_top hTY_top hST_closed hSB_closed
              hcover hH_img_II hH_ST hH_SB])
      qed
      \<comment> \<open>H continuity proved above via pasting\\_lemma\\_two\\_closed.\<close>
      \<comment> \<open>f is a loop at x0 in Y.\<close>
      have hf_path: "top1_is_path_on ?Y ?TY x0 x0 f"
        using hf unfolding top1_is_loop_on_def by (by100 blast)
      \<comment> \<open>r\\<circ>f is a loop at x0 in Y.\<close>
      have hrf_path: "top1_is_path_on ?Y ?TY x0 x0 (r \<circ> f)"
      proof -
        have hf_cont_loc: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?Y ?TY f"
          using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        have hrf_cont_loc: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology ?Y ?TY (r \<circ> f)"
          by (rule top1_continuous_map_on_comp[OF hf_cont_loc hr_cont])
        have "(r \<circ> f) 0 = x0" using hr_T hx0 hf
          unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 auto)
        have "(r \<circ> f) 1 = x0" using hr_T hx0 hf
          unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 auto)
        show ?thesis unfolding top1_is_path_on_def
          using hrf_cont_loc \<open>(r \<circ> f) 0 = x0\<close> \<open>(r \<circ> f) 1 = x0\<close> by (by100 blast)
      qed
      have hH_cont_II: "top1_continuous_map_on (I_set \<times> I_set) II_topology ?Y ?TY H"
        using hH_cont unfolding II_topology_def by (by100 simp)
      show ?thesis unfolding top1_path_homotopic_on_def
      proof (intro conjI)
        show "top1_is_path_on ?Y ?TY x0 x0 f" using hf_path .
        show "top1_is_path_on ?Y ?TY x0 x0 (r \<circ> f)" using hrf_path .
        show "\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology ?Y ?TY F
            \<and> (\<forall>s\<in>I_set. F (s, 0) = f s) \<and> (\<forall>s\<in>I_set. F (s, 1) = (r \<circ> f) s)
            \<and> (\<forall>t\<in>I_set. F (0, t) = x0) \<and> (\<forall>t\<in>I_set. F (1, t) = x0)"
          using hH_cont_II hH0 hH1 hH_endpts by (by100 blast)
      qed
    qed
    \<comment> \<open>Step 5: Compose: f \\<sim> r\\<circ>f \\<sim> const.\<close>
    show "top1_path_homotopic_on ?Y ?TY x0 x0 f (top1_constant_path x0)"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTY_top hf_rf hrf_null_Y])
  qed
  have hx0_Y: "x0 \<in> ?Y" using hx0 hT_sub_Y by (by100 blast)
  show ?thesis
    by (rule top1_simply_connected_from_one_point[OF hTY_top hY_pc hx0_Y hY_loops])
qed

end
