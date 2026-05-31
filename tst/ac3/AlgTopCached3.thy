theory AlgTopCached3
  imports "AlgTopCached2.AlgTopCached2"
begin

(* §83 Graph definitions *)
section \<open>\<S>83 Covering Spaces of a Graph\<close>

text \<open>An arc is a space homeomorphic to the closed unit interval [0, 1].\<close>


text \<open>A graph (Munkres §83): a Hausdorff space X with a collection \<A> of subspaces
  (arcs), each homeomorphic to [0,1], such that:
  (1) X is the union of all arcs in \<A>,
  (2) any two distinct arcs intersect in a set of at most two common endpoints,
  (3) the topology on X is the weak topology w.r.t. \<A> (a set is closed iff its
      intersection with each arc is closed in the arc).\<close>
definition top1_is_graph_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_graph_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     is_hausdorff_on X TX \<and>
     (\<exists>\<A>. (\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A))
        \<and> (\<Union>\<A>) = X
        \<and> (\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
             A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
           \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
           \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2)
        \<and> (\<forall>C. C \<subseteq> X \<longrightarrow>
             (closedin_on X TX C \<longleftrightarrow>
              (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))))"

text \<open>Helper: maximal connected component of a set S in topology T.\<close>
definition top1_max_conn_comp :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_max_conn_comp S TS B \<longleftrightarrow>
     B \<noteq> {} \<and> B \<subseteq> S \<and> top1_connected_on B (subspace_topology S TS B)
     \<and> (\<forall>C. C \<supseteq> B \<longrightarrow> C \<subseteq> S \<longrightarrow> top1_connected_on C (subspace_topology S TS C) \<longrightarrow> C = B)"

lemma max_conn_comp_sub: "top1_max_conn_comp S TS B \<Longrightarrow> B \<subseteq> S"
  unfolding top1_max_conn_comp_def by (by100 blast)

lemma max_conn_comp_mem: "top1_max_conn_comp S TS B \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> S"
  unfolding top1_max_conn_comp_def by (by100 blast)

lemma max_conn_comp_ne: "top1_max_conn_comp S TS B \<Longrightarrow> B \<noteq> {}"
  unfolding top1_max_conn_comp_def by (by100 blast)

text \<open>Every point of S is in some maximal connected component.\<close>
lemma max_conn_comp_covers:
  assumes "is_topology_on S TS" and "x \<in> S"
  shows "\<exists>B. top1_max_conn_comp S TS B \<and> x \<in> B"
proof -
  let ?C = "top1_component_of_on S TS x"
  have hC_sub: "?C \<subseteq> S" by (rule top1_component_of_on_subset)
  have hx_C: "x \<in> ?C" by (rule top1_component_of_on_self_mem[OF assms])
  have hC_ne: "?C \<noteq> {}" using hx_C by (by100 blast)
  have hC_conn: "top1_connected_on ?C (subspace_topology S TS ?C)"
    by (rule top1_component_of_on_connected[OF assms])
  have hC_max: "\<forall>D. D \<supseteq> ?C \<longrightarrow> D \<subseteq> S \<longrightarrow> top1_connected_on D (subspace_topology S TS D) \<longrightarrow> D = ?C"
  proof (intro allI impI)
    fix D assume hD_sup: "?C \<subseteq> D" and hD_sub: "D \<subseteq> S"
        and hD_conn: "top1_connected_on D (subspace_topology S TS D)"
    \<comment> \<open>D is connected and contains x. By Theorem 25.1, D \<subseteq> component(x) = ?C.\<close>
    have "x \<in> D" using hx_C hD_sup by (by100 blast)
    from top1_connected_subspace_subset_component_of[OF hD_sub \<open>x \<in> D\<close> hD_conn]
    have "D \<subseteq> ?C" .
    with hD_sup show "D = ?C" by (by100 blast)
  qed
  have "top1_max_conn_comp S TS ?C"
    unfolding top1_max_conn_comp_def using hC_ne hC_sub hC_conn hC_max by (by100 blast)
  thus ?thesis using hx_C by (by100 blast)
qed


(* §84 Tree definition + Lemma 83.2 infrastructure *)
section \<open>\<S>84 The Fundamental Group of a Graph\<close>

text \<open>A tree is a connected graph with no nontrivial loops (simply connected).\<close>
definition top1_is_tree_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_tree_on X TX \<longleftrightarrow>
     top1_is_graph_on X TX \<and>
     top1_connected_on X TX \<and>
     top1_simply_connected_on X TX"

text \<open>Reviewer-requested: tree is contractible (simply connected).\<close>
lemma tree_simply_connected:
  assumes "top1_is_tree_on T TT"
  shows "top1_simply_connected_on T TT"
  using assms unfolding top1_is_tree_on_def by (by100 blast)

text \<open>Helper: a compact discrete topological space is finite.
  In a discrete space, every singleton is open, so \{\{x\} | x \<in> X\} is an open cover.
  By compactness, there is a finite subcover, hence X is finite.\<close>
lemma compact_discrete_finite:
  assumes "top1_compact_on X TX"
      and "\<forall>x\<in>X. {x} \<in> TX"
  shows "finite X"
proof -
  \<comment> \<open>The singletons form an open cover of X.\<close>
  let ?U = "(\<lambda>x. {x}) ` X"
  have hU_open: "?U \<subseteq> TX"
  proof
    fix U assume "U \<in> ?U"
    then obtain x where "x \<in> X" "U = {x}" by (by100 blast)
    thus "U \<in> TX" using assms(2) by (by100 blast)
  qed
  have hU_cover: "X \<subseteq> \<Union>?U" by (by100 blast)
  \<comment> \<open>By compactness, there exists a finite subcover.\<close>
  have hTX: "is_topology_on X TX"
    using assms(1) unfolding top1_compact_on_def by (by100 blast)
  have "\<exists>F. finite F \<and> F \<subseteq> ?U \<and> X \<subseteq> \<Union>F"
  proof -
    from assms(1) have "\<forall>Uc. Uc \<subseteq> TX \<and> X \<subseteq> \<Union>Uc \<longrightarrow> (\<exists>F. finite F \<and> F \<subseteq> Uc \<and> X \<subseteq> \<Union>F)"
      unfolding top1_compact_on_def by (by100 blast)
    from this[rule_format, of ?U] hU_open hU_cover show ?thesis by (by100 blast)
  qed
  then obtain F where hF: "finite F" "F \<subseteq> ?U" "X \<subseteq> \<Union>F"
    by (by100 blast)
  \<comment> \<open>F is a finite set of singletons. Each element of F is {x} for some x.\<close>
  have "\<forall>S\<in>F. \<exists>x. S = {x}" using hF(2) by (by100 blast)
  \<comment> \<open>\<Union>F is finite (finite union of singletons).\<close>
  have "\<forall>S\<in>F. finite S" using hF(2) by (by100 blast)
  have "finite (\<Union>F)" using hF(1) \<open>\<forall>S\<in>F. finite S\<close> by (by100 blast)
  thus "finite X" using hF(3) using finite_subset by (by100 blast)
qed

text \<open>Helper: in a graph with coherent topology, if B \<subseteq> X and |B \<inter> A| \<le> 1
  for each arc A, then every subset of B is closed in X.\<close>
lemma graph_selection_set_discrete:
  assumes "top1_is_graph_on X TX"
      and "B \<subseteq> X"
      and "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and "\<Union>\<A> = X"
      and "\<forall>D. D \<subseteq> X \<longrightarrow>
           (closedin_on X TX D \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> D)))"
      and "\<forall>A\<in>\<A>. finite (B \<inter> A) \<and> card (B \<inter> A) \<le> 1"
  shows "\<forall>S. S \<subseteq> B \<longrightarrow> closedin_on X TX S"
proof (intro allI impI)
  fix S assume hS: "S \<subseteq> B"
  have hS_sub: "S \<subseteq> X" using hS assms(2) by (by100 blast)
  \<comment> \<open>By coherent topology: S closed iff S \<inter> A closed in A for all A.\<close>
  have "\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> S)"
  proof (intro ballI)
    fix A assume "A \<in> \<A>"
    \<comment> \<open>A \<inter> S \<subseteq> A \<inter> B which has \<le> 1 element.\<close>
    have "A \<inter> S \<subseteq> A \<inter> B" using hS by (by100 blast)
    have "finite (B \<inter> A) \<and> card (B \<inter> A) \<le> 1" using assms(6) \<open>A \<in> \<A>\<close> by (by100 blast)
    hence hfin: "finite (A \<inter> S)"
    proof -
      have "finite (B \<inter> A)" using \<open>finite (B \<inter> A) \<and> card (B \<inter> A) \<le> 1\<close> by (by100 blast)
      have "A \<inter> B = B \<inter> A" by (by100 blast)
      hence "finite (A \<inter> B)" using \<open>finite (B \<inter> A)\<close> by (by100 simp)
      show ?thesis using finite_subset[OF \<open>A \<inter> S \<subseteq> A \<inter> B\<close> \<open>finite (A \<inter> B)\<close>] .
    qed
    \<comment> \<open>A is Hausdorff (subspace of graph). Finite set in Hausdorff is closed.\<close>
    have hA_sub: "A \<subseteq> X" using assms(3) \<open>A \<in> \<A>\<close> by (by100 blast)
    have hA_haus: "is_hausdorff_on A (subspace_topology X TX A)"
    proof -
      have "is_hausdorff_on X TX"
        using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
      from conjunct2[OF conjunct2[OF Theorem_17_11]] this hA_sub
      show ?thesis by (by100 blast)
    qed
    have hA_T1: "top1_T1_on A (subspace_topology X TX A)"
      by (rule hausdorff_imp_T1_on[OF hA_haus])
    \<comment> \<open>Finite set is closed (union of singletons, each closed in T1).\<close>
    have "A \<inter> S \<subseteq> A" by (by100 blast)
    show "closedin_on A (subspace_topology X TX A) (A \<inter> S)"
    proof -
      have hA_top: "is_topology_on A (subspace_topology X TX A)"
        using hA_haus unfolding is_hausdorff_on_def by (by100 blast)
      have "A \<inter> S = \<Union>((\<lambda>x. {x}) ` (A \<inter> S))" by (by100 blast)
      moreover have hfin_img: "finite ((\<lambda>x. {x}) ` (A \<inter> S))" using hfin by (by100 simp)
      moreover have "\<forall>U\<in>((\<lambda>x. {x}) ` (A \<inter> S)).
          closedin_on A (subspace_topology X TX A) U"
      proof (intro ballI)
        fix U assume "U \<in> (\<lambda>x. {x}) ` (A \<inter> S)"
        then obtain x where "x \<in> A" "U = {x}" by (by100 blast)
        thus "closedin_on A (subspace_topology X TX A) U"
          using hA_T1 unfolding top1_T1_on_def by (by100 blast)
      qed
      from closedin_Union_finite[OF hA_top hfin_img this]
      have "closedin_on A (subspace_topology X TX A) (\<Union>((\<lambda>x. {x}) ` (A \<inter> S)))" .
      thus ?thesis using calculation(1) by (by100 simp)
    qed
  qed
  thus "closedin_on X TX S" using assms(5) hS_sub by (by100 blast)
qed

text \<open>Lemma 83.2 (Munkres): A compact subspace of a graph meets only finitely many arcs.
  This is needed for the chain-of-trees Zorn argument.\<close>
lemma compact_in_graph_finite_arcs:
  assumes "top1_is_graph_on X TX"
      and "K \<subseteq> X"
      and "top1_compact_on K (subspace_topology X TX K)"
  shows "\<exists>\<A>0. finite \<A>0 \<and> \<A>0 \<subseteq> {A. \<exists>\<A>. (\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A))
        \<and> (\<Union>\<A>) = X \<and> A \<in> \<A>} \<and> K \<subseteq> \<Union>\<A>0"
proof -
  \<comment> \<open>Munkres 83.2: K compact in graph X. K meets finitely many arcs.\<close>
  obtain \<A> where h\<A>: "\<forall>A\<in>\<A>. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A)"
      and h\<A>_cover: "\<Union>\<A> = X"
      and h\<A>_inter: "\<forall>A\<in>\<A>. \<forall>B\<in>\<A>. A \<noteq> B \<longrightarrow>
           A \<inter> B \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)
         \<and> A \<inter> B \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
         \<and> finite (A \<inter> B) \<and> card (A \<inter> B) \<le> 2"
      and h\<A>_coh: "\<forall>C. C \<subseteq> X \<longrightarrow>
           (closedin_on X TX C \<longleftrightarrow>
            (\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> C)))"
    using assms(1) unfolding top1_is_graph_on_def by (by5000 auto)
  \<comment> \<open>Step 1: The set of arcs meeting K is finite.
     For each arc A \<in> \<A> meeting K, pick one point x_A \<in> K \<inter> A.
     The set B = {x_A} is closed discrete in K (by the graph intersection property).
     K compact + B closed discrete \<Rightarrow> B finite \<Rightarrow> finitely many arcs.\<close>
  \<comment> \<open>Munkres 83.2: Construct finite \<A>0 covering K.
     Split K points: vertices (in arc endpoints) + interior points (in exactly one arc).
     Vertices: finitely many (closed discrete in compact K).
     Interior arcs: finitely many (selection set is closed discrete).\<close>
  \<comment> \<open>Define: vertices of X = endpoints of arcs.\<close>
  let ?Vertices = "\<Union>A\<in>\<A>. top1_arc_endpoints_on A (subspace_topology X TX A)"
  \<comment> \<open>Step 1: Interior points. For each arc A with interior points in K,
     choose one interior point x_A \<in> K \<inter> (A - endpoints(A)).
     The selection set B satisfies |B \<inter> A'| \<le> 1 for each arc A'.\<close>
  let ?\<A>_int = "{A \<in> \<A>. (A - top1_arc_endpoints_on A (subspace_topology X TX A)) \<inter> K \<noteq> {}}"
  have h\<A>int_finite: "finite ?\<A>_int"
  proof -
    \<comment> \<open>Munkres 83.2: Choose one interior point per arc in \<A>_int.
       Selection set B has |B \<inter> A'| \<le> 1 per arc \<Rightarrow> closed discrete \<Rightarrow> finite.\<close>
    have hTX: "is_topology_on X TX"
      using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
    \<comment> \<open>Step 1: Choice function f: \<A>_int \<rightarrow> K picking one interior point per arc.\<close>
    have hex: "\<forall>A \<in> ?\<A>_int. \<exists>x. x \<in> A \<and> x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A) \<and> x \<in> K"
      by (by100 blast)
    define f where "f \<equiv> \<lambda>A. SOME x. x \<in> A \<and> x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A) \<and> x \<in> K"
    have hf: "\<forall>A \<in> ?\<A>_int.
        f A \<in> A \<and> f A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A) \<and> f A \<in> K"
    proof (intro ballI)
      fix A assume "A \<in> ?\<A>_int"
      from hex[rule_format, OF this]
      have "\<exists>x. x \<in> A \<and> x \<notin> top1_arc_endpoints_on A (subspace_topology X TX A) \<and> x \<in> K" .
      from someI_ex[OF this] show "f A \<in> A \<and> f A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A) \<and> f A \<in> K"
        unfolding f_def .
    qed
    let ?B = "f ` ?\<A>_int"
    \<comment> \<open>Step 2: f is injective (interior point of A can't be in another arc's non-endpoint set).\<close>
    have hf_inj: "inj_on f ?\<A>_int"
    proof (rule inj_onI)
      fix A1 A2
      assume hA1: "A1 \<in> ?\<A>_int" and hA2: "A2 \<in> ?\<A>_int" and heq: "f A1 = f A2"
      show "A1 = A2"
      proof (rule ccontr)
        assume hne: "A1 \<noteq> A2"
        have hA1_in: "A1 \<in> \<A>" using hA1 by (by100 blast)
        have hA2_in: "A2 \<in> \<A>" using hA2 by (by100 blast)
        have "f A1 \<in> A1" using hf hA1 by (by100 blast)
        have "f A2 \<in> A2" using hf hA2 by (by100 blast)
        have "f A1 \<in> A2" using \<open>f A2 \<in> A2\<close> heq by (by100 simp)
        hence "f A1 \<in> A1 \<inter> A2" using \<open>f A1 \<in> A1\<close> by (by100 blast)
        have "A1 \<inter> A2 \<subseteq> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
          using h\<A>_inter hA1_in hA2_in hne by (by100 blast)
        hence "f A1 \<in> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
          using \<open>f A1 \<in> A1 \<inter> A2\<close> by (by100 blast)
        moreover have "f A1 \<notin> top1_arc_endpoints_on A1 (subspace_topology X TX A1)"
          using hf hA1 by (by100 blast)
        ultimately show False by (by100 blast)
      qed
    qed
    \<comment> \<open>Step 3: B has \<le> 1 point per arc.\<close>
    have hB_card: "\<forall>A'\<in>\<A>. finite (?B \<inter> A') \<and> card (?B \<inter> A') \<le> 1"
    proof (intro ballI conjI)
      fix A' assume hA': "A' \<in> \<A>"
      have hB_A': "?B \<inter> A' \<subseteq> {f A'}"
      proof
        fix x assume "x \<in> ?B \<inter> A'"
        then obtain A where hA: "A \<in> ?\<A>_int" "x = f A" "x \<in> A'" by (by100 blast)
        have "A = A'"
        proof (rule ccontr)
          assume "A \<noteq> A'"
          have "A \<in> \<A>" using hA(1) by (by100 blast)
          have "f A \<in> A" using hf hA(1) by (by100 blast)
          hence "f A \<in> A \<inter> A'" using hA(3) hA(2) by (by100 blast)
          have "A \<inter> A' \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using h\<A>_inter \<open>A \<in> \<A>\<close> hA' \<open>A \<noteq> A'\<close> by (by100 blast)
          hence "f A \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using \<open>f A \<in> A \<inter> A'\<close> by (by100 blast)
          moreover have "f A \<notin> top1_arc_endpoints_on A (subspace_topology X TX A)"
            using hf hA(1) by (by100 blast)
          ultimately show False by (by100 blast)
        qed
        thus "x \<in> {f A'}" using hA(2) by (by100 blast)
      qed
      show "finite (?B \<inter> A')"
        using finite_subset[OF hB_A'] by (by100 simp)
      show "card (?B \<inter> A') \<le> 1"
      proof -
        have "finite {f A'}" by (by100 simp)
        from card_mono[OF this hB_A'] show ?thesis by (by100 simp)
      qed
    qed
    \<comment> \<open>Step 4: Every subset of B is closed in X (by graph\_selection\_set\_discrete).\<close>
    have hB_sub: "?B \<subseteq> X"
    proof
      fix x assume "x \<in> ?B"
      then obtain A where "A \<in> ?\<A>_int" "x = f A" by (by100 blast)
      hence "A \<in> \<A>" by (by100 blast)
      have "f A \<in> A" using hf \<open>A \<in> ?\<A>_int\<close> by (by100 blast)
      have "A \<subseteq> X" using h\<A> \<open>A \<in> \<A>\<close> by (by100 blast)
      thus "x \<in> X" using \<open>x = f A\<close> \<open>f A \<in> A\<close> \<open>A \<subseteq> X\<close> by (by100 blast)
    qed
    have hB_all_closed: "\<forall>S. S \<subseteq> ?B \<longrightarrow> closedin_on X TX S"
      by (rule graph_selection_set_discrete[OF assms(1) hB_sub h\<A> h\<A>_cover h\<A>_coh hB_card])
    \<comment> \<open>Step 5: B \<subseteq> K, B closed in K.\<close>
    have hB_sub_K: "?B \<subseteq> K"
    proof
      fix x assume "x \<in> ?B"
      then obtain A where "A \<in> ?\<A>_int" "x = f A" by (by100 blast)
      thus "x \<in> K" using hf by (by100 blast)
    qed
    have hB_closed_X: "closedin_on X TX ?B" using hB_all_closed by (by100 blast)
    have hB_closed_K: "closedin_on K (subspace_topology X TX K) ?B"
      by (rule closedin_subspace_from_ambient[OF hTX hB_closed_X assms(2) hB_sub_K])
    \<comment> \<open>Step 6: B compact (closed subset of compact K).\<close>
    have hB_compact: "top1_compact_on ?B (subspace_topology K (subspace_topology X TX K) ?B)"
      by (rule Theorem_26_2[OF assms(3) hB_closed_K])
    have hB_top_eq: "subspace_topology K (subspace_topology X TX K) ?B = subspace_topology X TX ?B"
      by (rule subspace_topology_trans[OF hB_sub_K])
    have hB_compact': "top1_compact_on ?B (subspace_topology X TX ?B)"
      using hB_compact hB_top_eq by (by100 simp)
    \<comment> \<open>Step 7: B is discrete (every singleton open in subspace).\<close>
    have hB_discrete: "\<forall>x\<in>?B. {x} \<in> subspace_topology X TX ?B"
    proof (intro ballI)
      fix x assume hx: "x \<in> ?B"
      have hBmx_sub: "?B - {x} \<subseteq> ?B" by (by100 blast)
      have hBmx_cl: "closedin_on X TX (?B - {x})" using hB_all_closed hBmx_sub by (by100 blast)
      have hopen: "X - (?B - {x}) \<in> TX"
        using closedin_diff_open hBmx_cl by (by100 blast)
      have heq: "{x} = ?B \<inter> (X - (?B - {x}))" using hx hB_sub by (by100 blast)
      have "{x} \<in> {?B \<inter> U | U. U \<in> TX}"
        using hopen heq by (by100 blast)
      thus "{x} \<in> subspace_topology X TX ?B"
        unfolding subspace_topology_def .
    qed
    \<comment> \<open>Step 8: compact + discrete \<Rightarrow> finite.\<close>
    have "finite ?B" by (rule compact_discrete_finite[OF hB_compact' hB_discrete])
    \<comment> \<open>Step 9: f injective + B finite \<Rightarrow> \<A>_int finite.\<close>
    thus "finite ?\<A>_int" using finite_imageD hf_inj by (by100 blast)
  qed
  \<comment> \<open>Step 2: Vertices in K are finitely many.\<close>
  have hvert_K_finite: "finite (?Vertices \<inter> K)"
  proof -
    \<comment> \<open>Munkres 83.2: Vertices \<inter> K is closed discrete in compact K, hence finite.
       Key: for each arc A, (Vertices \<inter> K) \<inter> A \<subseteq> endpoints(A), which is finite (\<le> 2 pts).
       So every subset of Vertices \<inter> K is closed in X (coherent topology + Hausdorff).
       Hence closed discrete in K, compact \<Rightarrow> finite.\<close>
    let ?VK = "?Vertices \<inter> K"
    have hVK_sub: "?VK \<subseteq> X" using assms(2) by (by100 blast)
    have hTX: "is_topology_on X TX"
      using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
    have hTX_strict: "is_topology_on_strict X TX"
      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
    have hX_haus: "is_hausdorff_on X TX"
      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
    \<comment> \<open>Step 1: Every subset of VK is closed in X.\<close>
    have hVK_all_closed: "\<forall>S. S \<subseteq> ?VK \<longrightarrow> closedin_on X TX S"
    proof (intro allI impI)
      fix S assume hS: "S \<subseteq> ?VK"
      have hS_sub: "S \<subseteq> X" using hS hVK_sub by (by100 blast)
      \<comment> \<open>By coherent topology: show S \<inter> A closed in A for each arc A.\<close>
      have "\<forall>A\<in>\<A>. closedin_on A (subspace_topology X TX A) (A \<inter> S)"
      proof (intro ballI)
        fix A assume hA_in: "A \<in> \<A>"
        \<comment> \<open>A \<inter> S \<subseteq> endpoints(A): every vertex in A is an endpoint of A.\<close>
        have hAS_sub_ep: "A \<inter> S \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
        proof
          fix x assume hx: "x \<in> A \<inter> S"
          hence "x \<in> ?VK" using hS by (by100 blast)
          hence "x \<in> ?Vertices" by (by100 blast)
          then obtain A' where hA': "A' \<in> \<A>"
              "x \<in> top1_arc_endpoints_on A' (subspace_topology X TX A')" by (by100 blast)
          have "x \<in> A'" using hA'(2) unfolding top1_arc_endpoints_on_def by (by100 blast)
          show "x \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
          proof (cases "A' = A")
            case True thus ?thesis using hA'(2) by (by100 simp)
          next
            case False
            have "x \<in> A \<inter> A'" using hx \<open>x \<in> A'\<close> by (by100 blast)
            have "A \<inter> A' \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
              using h\<A>_inter hA_in hA'(1) False by (by100 blast)
            thus ?thesis using \<open>x \<in> A \<inter> A'\<close> by (by100 blast)
          qed
        qed
        \<comment> \<open>endpoints(A) is finite (\<le> 2 elements), so A \<inter> S is finite.\<close>
        have hA_sub: "A \<subseteq> X" using h\<A> hA_in by (by100 blast)
        have hA_arc: "top1_is_arc_on A (subspace_topology X TX A)" using h\<A> hA_in by (by100 blast)
        obtain h where hh: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
            A (subspace_topology X TX A) h"
          using hA_arc unfolding top1_is_arc_on_def by (by100 blast)
        have hep: "top1_arc_endpoints_on A (subspace_topology X TX A) = {h 0, h 1}"
          by (rule arc_endpoints_are_boundary[OF hTX_strict hX_haus hA_sub hA_arc hh])
        have hep_finite: "finite (top1_arc_endpoints_on A (subspace_topology X TX A))"
          using hep by (by100 simp)
        have hAS_finite: "finite (A \<inter> S)"
          using finite_subset[OF hAS_sub_ep hep_finite] .
        \<comment> \<open>A is Hausdorff \<Rightarrow> finite set is closed.\<close>
        have hA_haus: "is_hausdorff_on A (subspace_topology X TX A)"
          using hX_haus hA_sub conjunct2[OF conjunct2[OF Theorem_17_11]] by (by100 blast)
        have hA_T1: "top1_T1_on A (subspace_topology X TX A)"
          by (rule hausdorff_imp_T1_on[OF hA_haus])
        have hA_top: "is_topology_on A (subspace_topology X TX A)"
          using hA_haus unfolding is_hausdorff_on_def by (by100 blast)
        \<comment> \<open>Finite set = union of singletons, each closed in T1. Finite union closed.\<close>
        have hAS_eq: "A \<inter> S = \<Union>((\<lambda>x. {x}) ` (A \<inter> S))" by (by100 blast)
        moreover have "finite ((\<lambda>x. {x}) ` (A \<inter> S))" using hAS_finite by (by100 simp)
        moreover have "\<forall>U\<in>((\<lambda>x. {x}) ` (A \<inter> S)). closedin_on A (subspace_topology X TX A) U"
        proof (intro ballI)
          fix U assume "U \<in> (\<lambda>x. {x}) ` (A \<inter> S)"
          then obtain y where "y \<in> A" "U = {y}" by (by100 blast)
          thus "closedin_on A (subspace_topology X TX A) U"
            using hA_T1 unfolding top1_T1_on_def by (by100 blast)
        qed
        from closedin_Union_finite[OF hA_top \<open>finite ((\<lambda>x. {x}) ` (A \<inter> S))\<close> this]
        have "closedin_on A (subspace_topology X TX A) (\<Union>((\<lambda>x. {x}) ` (A \<inter> S)))" .
        thus "closedin_on A (subspace_topology X TX A) (A \<inter> S)"
          using hAS_eq by (by100 simp)
      qed
      thus "closedin_on X TX S" using h\<A>_coh hS_sub by (by100 blast)
    qed
    \<comment> \<open>Step 2: VK closed in K.\<close>
    have hVK_closed_X: "closedin_on X TX ?VK" using hVK_all_closed by (by100 blast)
    have hVK_sub_K: "?VK \<subseteq> K" by (by100 blast)
    have hVK_closed_K: "closedin_on K (subspace_topology X TX K) ?VK"
      by (rule closedin_subspace_from_ambient[OF hTX hVK_closed_X assms(2) hVK_sub_K])
    \<comment> \<open>Step 3: VK compact.\<close>
    have hVK_compact: "top1_compact_on ?VK (subspace_topology K (subspace_topology X TX K) ?VK)"
      by (rule Theorem_26_2[OF assms(3) hVK_closed_K])
    have hVK_top_eq: "subspace_topology K (subspace_topology X TX K) ?VK = subspace_topology X TX ?VK"
      by (rule subspace_topology_trans[OF hVK_sub_K])
    have hVK_compact': "top1_compact_on ?VK (subspace_topology X TX ?VK)"
      using hVK_compact hVK_top_eq by (by100 simp)
    \<comment> \<open>Step 4: VK discrete.\<close>
    have hVK_discrete: "\<forall>x\<in>?VK. {x} \<in> subspace_topology X TX ?VK"
    proof (intro ballI)
      fix x assume hx: "x \<in> ?VK"
      have "?VK - {x} \<subseteq> ?VK" by (by100 blast)
      have hcl: "closedin_on X TX (?VK - {x})" using hVK_all_closed \<open>?VK - {x} \<subseteq> ?VK\<close> by (by100 blast)
      have hopen: "X - (?VK - {x}) \<in> TX"
        using closedin_diff_open hcl by (by100 blast)
      have heqV: "{x} = ?VK \<inter> (X - (?VK - {x}))" using hx hVK_sub by (by100 blast)
      have "{x} \<in> {?VK \<inter> U | U. U \<in> TX}" using hopen heqV by (by100 blast)
      thus "{x} \<in> subspace_topology X TX ?VK"
        unfolding subspace_topology_def .
    qed
    \<comment> \<open>Step 5: compact + discrete \<Rightarrow> finite.\<close>
    show "finite (?Vertices \<inter> K)" by (rule compact_discrete_finite[OF hVK_compact' hVK_discrete])
  qed
  \<comment> \<open>Step 3: For each vertex v \<in> K, choose ONE arc containing v.\<close>
  have "\<exists>\<A>_vert. finite \<A>_vert \<and> \<A>_vert \<subseteq> \<A> \<and> (\<forall>v \<in> ?Vertices \<inter> K. \<exists>A \<in> \<A>_vert. v \<in> A)"
  proof -
    \<comment> \<open>For each v \<in> Vertices \<inter> K, v \<in> X = \<Union>\<A>, so v \<in> some A \<in> \<A>. Choose one.\<close>
    have "\<forall>v \<in> ?Vertices \<inter> K. \<exists>A \<in> \<A>. v \<in> A"
    proof (intro ballI)
      fix v assume "v \<in> ?Vertices \<inter> K"
      hence "v \<in> X" using assms(2) by (by100 blast)
      thus "\<exists>A \<in> \<A>. v \<in> A" using h\<A>_cover by (by100 blast)
    qed
    hence "\<exists>f. \<forall>v \<in> ?Vertices \<inter> K. f v \<in> \<A> \<and> v \<in> f v" by (by5000 metis)
    then obtain f where hf: "\<forall>v \<in> ?Vertices \<inter> K. f v \<in> \<A> \<and> v \<in> f v" by (by100 blast)
    let ?\<A>_v = "f ` (?Vertices \<inter> K)"
    have "finite ?\<A>_v" using hvert_K_finite by (by100 simp)
    moreover have "?\<A>_v \<subseteq> \<A>" using hf by (by100 blast)
    moreover have "\<forall>v \<in> ?Vertices \<inter> K. \<exists>A \<in> ?\<A>_v. v \<in> A"
      using hf by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  then obtain \<A>_vert where h\<A>v_fin: "finite \<A>_vert" and h\<A>v_sub: "\<A>_vert \<subseteq> \<A>"
    and h\<A>v_cover: "\<forall>v \<in> ?Vertices \<inter> K. \<exists>A \<in> \<A>_vert. v \<in> A" by (by100 blast)
  \<comment> \<open>Step 4: \<A>0 = \<A>_int \<union> \<A>_vert covers K.\<close>
  let ?\<A>0 = "?\<A>_int \<union> \<A>_vert"
  have "finite ?\<A>0" using h\<A>int_finite h\<A>v_fin by (by100 blast)
  moreover have "?\<A>0 \<subseteq> {A. \<exists>\<A>'. (\<forall>A\<in>\<A>'. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A))
      \<and> (\<Union>\<A>') = X \<and> A \<in> \<A>'}"
  proof
    fix A assume "A \<in> ?\<A>0"
    hence "A \<in> \<A>" using h\<A>v_sub by (by100 blast)
    show "A \<in> {A. \<exists>\<A>'. (\<forall>A\<in>\<A>'. A \<subseteq> X \<and> top1_is_arc_on A (subspace_topology X TX A))
        \<and> (\<Union>\<A>') = X \<and> A \<in> \<A>'}"
      using h\<A> h\<A>_cover \<open>A \<in> \<A>\<close> by (by5000 blast)
  qed
  moreover have "K \<subseteq> \<Union>?\<A>0"
  proof
    fix x assume "x \<in> K"
    hence "x \<in> X" using assms(2) by (by100 blast)
    then obtain A where hA: "A \<in> \<A>" "x \<in> A" using h\<A>_cover by (by100 blast)
    show "x \<in> \<Union>?\<A>0"
    proof (cases "x \<in> top1_arc_endpoints_on A (subspace_topology X TX A)")
      case True
      \<comment> \<open>x is a vertex of A, hence in Vertices \<inter> K.\<close>
      hence "x \<in> ?Vertices \<inter> K" using hA(1) \<open>x \<in> K\<close> by (by100 blast)
      from h\<A>v_cover[rule_format, OF this] obtain A' where "A' \<in> \<A>_vert" "x \<in> A'"
        by (by100 blast)
      thus ?thesis by (by100 blast)
    next
      case False
      \<comment> \<open>x is an interior point of A, so A \<in> \<A>_int.\<close>
      hence "x \<in> A - top1_arc_endpoints_on A (subspace_topology X TX A)" using hA(2) by (by100 blast)
      hence "(A - top1_arc_endpoints_on A (subspace_topology X TX A)) \<inter> K \<noteq> {}"
        using \<open>x \<in> K\<close> by (by100 blast)
      hence "A \<in> ?\<A>_int" using hA(1) by (by100 blast)
      thus ?thesis using hA(2) by (by100 blast)
    qed
  qed
  ultimately show ?thesis by (by5000 blast)
qed

(* arc_deformation_retract + Lemma 84.2 *)
lemma arc_deformation_retract_to_endpoint:
  assumes "top1_is_arc_on A TA"
      and "p \<in> top1_arc_endpoints_on A TA"
  shows "top1_deformation_retract_of_on A TA {p}"
proof -
  \<comment> \<open>Extract homeomorphism h: [0,1] \<rightarrow> A.\<close>
  from assms(1) obtain h where hh: "top1_homeomorphism_on top1_unit_interval
      top1_unit_interval_topology A TA h"
    unfolding top1_is_arc_on_def by (by100 blast)
  \<comment> \<open>p is an endpoint: p \<in> \{h(0), h(1)\}.\<close>
  have hA_strict: "is_topology_on_strict A TA"
    using assms(1) unfolding top1_is_arc_on_def by (by100 blast)
  have hA_haus: "is_hausdorff_on A TA"
  proof -
    \<comment> \<open>[0,1] Hausdorff: subspace of Hausdorff R.\<close>
    have "is_hausdorff_on (UNIV :: real set) top1_open_sets" by (rule top1_R_is_hausdorff)
    have "top1_unit_interval \<subseteq> (UNIV :: real set)" by (by100 blast)
    from conjunct2[OF conjunct2[OF Theorem_17_11]] this
        \<open>is_hausdorff_on (UNIV :: real set) top1_open_sets\<close>
    have "is_hausdorff_on top1_unit_interval (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval)"
      by (by100 blast)
    hence hI_haus: "is_hausdorff_on top1_unit_interval top1_unit_interval_topology"
      unfolding top1_unit_interval_topology_def by (by100 simp)
    \<comment> \<open>Homeomorphism preserves Hausdorff.\<close>
    from homeomorphism_inverse[OF hh]
    have "top1_homeomorphism_on A TA top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval h)" .
    from is_hausdorff_on_of_homeomorphism_on[OF this hI_haus]
    show ?thesis .
  qed
  have hA_sub_gen: "A \<subseteq> A" by (by100 blast)
  have hep: "top1_arc_endpoints_on A TA = {h 0, h 1}"
  proof -
    have "subspace_topology A TA A = TA"
    proof (rule set_eqI, rule iffI)
      fix U assume "U \<in> subspace_topology A TA A"
      then obtain V where "V \<in> TA" "U = A \<inter> V" unfolding subspace_topology_def by (by100 blast)
      have "V \<subseteq> A" using \<open>V \<in> TA\<close> hA_strict unfolding is_topology_on_strict_def by (by100 blast)
      hence "U = V" using \<open>U = A \<inter> V\<close> by (by100 blast)
      thus "U \<in> TA" using \<open>V \<in> TA\<close> by (by100 simp)
    next
      fix U assume "U \<in> TA"
      have "U \<subseteq> A" using \<open>U \<in> TA\<close> hA_strict unfolding is_topology_on_strict_def by (by100 blast)
      hence "U = A \<inter> U" by (by100 blast)
      thus "U \<in> subspace_topology A TA A"
        unfolding subspace_topology_def using \<open>U \<in> TA\<close> by (by100 blast)
    qed
    hence "top1_is_arc_on A (subspace_topology A TA A)"
      using assms(1) by (by100 simp)
    moreover have "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology A (subspace_topology A TA A) h"
      using hh \<open>subspace_topology A TA A = TA\<close> by (by100 simp)
    ultimately have "top1_arc_endpoints_on A (subspace_topology A TA A) = {h 0, h 1}"
      by (rule arc_endpoints_are_boundary[OF hA_strict hA_haus hA_sub_gen])
    thus ?thesis using \<open>subspace_topology A TA A = TA\<close> by (by100 simp)
  qed
  from assms(2) hep have hp_cases: "p = h 0 \<or> p = h 1" by (by100 blast)
  have hp_in_A: "p \<in> A" using assms(2) unfolding top1_arc_endpoints_on_def by (by100 blast)
  \<comment> \<open>Obtain h' with h'(0) = p (same as h if p=h(0), reversed if p=h(1)).\<close>
  \<comment> \<open>Then the contraction G(s,t) = (1-t)\<cdot>s collapses [0,1] to \{0\},
     and H(x,t) = h'(G(h'\<inverse>(x), t)) collapses A to \{p = h'(0)\}.\<close>
  \<comment> \<open>Step 1: [0,1] deformation retracts to \{0\} via G(s,t) = (1-t)\<cdot>s.\<close>
  define G :: "real \<times> real \<Rightarrow> real" where "G \<equiv> \<lambda>(s,t). (1 - t) * s"
  have hG_range: "\<And>p. p \<in> top1_unit_interval \<times> top1_unit_interval \<Longrightarrow> G p \<in> top1_unit_interval"
  proof -
    fix p :: "real \<times> real" assume "p \<in> top1_unit_interval \<times> top1_unit_interval"
    then obtain s t where "p = (s,t)" "0 \<le> s" "s \<le> 1" "0 \<le> t" "t \<le> 1"
      unfolding top1_unit_interval_def by (by100 auto)
    have "0 \<le> (1 - t) * s" using \<open>0 \<le> s\<close> \<open>t \<le> 1\<close> by (by100 auto)
    have "0 \<le> 1 - t" using \<open>t \<le> 1\<close> by (by100 linarith)
    have "(1 - t) * s \<le> (1 - t) * 1" using mult_left_mono[OF \<open>s \<le> 1\<close> \<open>0 \<le> 1 - t\<close>] .
    moreover have "(1 - t) * s \<le> 1"
      using order_trans[OF \<open>(1 - t) * s \<le> (1 - t) * 1\<close>] \<open>0 \<le> t\<close> by (by100 simp)
    ultimately show "G p \<in> top1_unit_interval"
      unfolding G_def \<open>p = (s,t)\<close> top1_unit_interval_def
      using \<open>0 \<le> (1 - t) * s\<close> by (by100 simp)
  qed
  have hG_cont: "continuous_on (top1_unit_interval \<times> top1_unit_interval) G"
    unfolding G_def split_def by (intro continuous_intros)
  have hG0: "\<forall>s\<in>top1_unit_interval. G (s, 0) = s" unfolding G_def by (by100 simp)
  have hG1: "\<forall>s\<in>top1_unit_interval. G (s, 1) = 0" unfolding G_def by (by100 simp)
  have hGfix: "\<forall>t\<in>top1_unit_interval. G (0, t) = 0" unfolding G_def by (by100 simp)
  \<comment> \<open>Use top1\_continuous\_map\_on\_II\_to\_I for the product topology continuity.\<close>
  have hG_top1: "top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval)
      (product_topology_on top1_unit_interval_topology top1_unit_interval_topology)
      top1_unit_interval top1_unit_interval_topology G"
  proof -
    from top1_continuous_map_on_II_to_I[OF hG_range hG_cont]
    show ?thesis unfolding top1_unit_interval_def top1_unit_interval_topology_def .
  qed
  have h0_I: "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
  have "top1_deformation_retract_of_on top1_unit_interval top1_unit_interval_topology {0}"
    unfolding top1_deformation_retract_of_on_def
  proof (intro conjI)
    show "{0::real} \<subseteq> top1_unit_interval" using h0_I by (by100 blast)
    show "\<exists>H. top1_continuous_map_on (top1_unit_interval \<times> top1_unit_interval)
        (product_topology_on top1_unit_interval_topology top1_unit_interval_topology)
        top1_unit_interval top1_unit_interval_topology H
      \<and> (\<forall>x\<in>top1_unit_interval. H (x, 0) = x)
      \<and> (\<forall>x\<in>top1_unit_interval. H (x, 1) \<in> {0::real})
      \<and> (\<forall>a\<in>{0::real}. \<forall>t\<in>top1_unit_interval. H (a, t) = a)"
      apply (rule exI[of _ G])
      using hG_top1 hG0 hG1 hGfix by (by100 blast)
  qed
  \<comment> \<open>Step 2: Transport through homeomorphism h (adjusted for which endpoint p is).
     If p = h(0): h maps 0 to p, deformation retraction of I to \{0\} gives A to \{p\}.
     If p = h(1): use reversed homeomorphism h' = h \<circ> (1-\<cdot>), h'(0) = h(1) = p.\<close>
  \<comment> \<open>The transport of deformation retraction through homeomorphism:
     If DR(X, TX, \{a\}) and homeomorphism f: X \<rightarrow> Y, then DR(Y, TY, \{f(a)\}).\<close>
  \<comment> \<open>Step 2: Transport through homeomorphism.
     Need h' with h'(0) = p. If p = h(0), use h. If p = h(1), use h \<circ> (1-\<cdot>).\<close>
  obtain h' where hh': "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology A TA h'"
      and hh'0: "h' 0 = p"
  proof (cases "p = h 0")
    case True
    thus ?thesis using that[OF hh] by (by100 simp)
  next
    case False
    hence "p = h 1" using hp_cases by (by100 blast)
    \<comment> \<open>Define h'(s) = h(1-s). This is a homeomorphism with h'(0) = h(1) = p.\<close>
    let ?h' = "h \<circ> (\<lambda>s. 1 - s)"
    \<comment> \<open>(1-\<cdot>) is a homeomorphism [0,1] \<rightarrow> [0,1] (continuous, self-inverse).\<close>
    have h_rev_homeo: "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology
        top1_unit_interval top1_unit_interval_topology (\<lambda>s. 1 - s)"
    proof -
      have hI_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
        by (rule top1_unit_interval_topology_is_topology_on)
      have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
        unfolding top1_unit_interval_def top1_unit_interval_topology_def
        using Theorem_27_1[of "0::real" 1] by (by100 simp)
      have hI_haus: "is_hausdorff_on top1_unit_interval top1_unit_interval_topology"
      proof -
        have "is_hausdorff_on (UNIV :: real set) top1_open_sets" by (rule top1_R_is_hausdorff)
        from conjunct2[OF conjunct2[OF Theorem_17_11]] _ this
        have "is_hausdorff_on top1_unit_interval (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval)"
          by (by100 blast)
        thus ?thesis unfolding top1_unit_interval_topology_def by (by100 simp)
      qed
      have h_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
          top1_unit_interval top1_unit_interval_topology (\<lambda>s. 1 - s)"
        using op_minus_continuous_on_interval
        unfolding top1_unit_interval_def top1_unit_interval_topology_def .
      have h_bij: "bij_betw (\<lambda>s::real. 1 - s) top1_unit_interval top1_unit_interval"
        unfolding bij_betw_def top1_unit_interval_def
      proof (intro conjI)
        show "inj_on (\<lambda>s::real. 1 - s) {0..1}" by (by100 auto)
        show "(\<lambda>s::real. 1 - s) ` {0..1} = {0..1}" by (by100 auto)
      qed
      from Theorem_26_6[OF hI_top hI_top hI_compact hI_haus h_cont h_bij]
      show ?thesis .
    qed
    \<comment> \<open>Compose with h: h \<circ> (1-\<cdot>) is homeomorphism.\<close>
    have "top1_homeomorphism_on top1_unit_interval top1_unit_interval_topology A TA ?h'"
    proof -
      have h_cont_comp: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology A TA ?h'"
      proof -
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            top1_unit_interval top1_unit_interval_topology (\<lambda>s. 1 - s)"
          using h_rev_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        have "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology A TA h"
          using hh unfolding top1_homeomorphism_on_def by (by100 blast)
        from top1_continuous_map_on_comp[OF
            \<open>top1_continuous_map_on top1_unit_interval top1_unit_interval_topology top1_unit_interval top1_unit_interval_topology (\<lambda>s. 1 - s)\<close>
            \<open>top1_continuous_map_on top1_unit_interval top1_unit_interval_topology A TA h\<close>]
        show ?thesis by (by100 simp)
      qed
      have h_bij_comp: "bij_betw ?h' top1_unit_interval A"
      proof -
        have "bij_betw (\<lambda>s::real. 1 - s) top1_unit_interval top1_unit_interval"
          using h_rev_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        have "bij_betw h top1_unit_interval A"
          using hh unfolding top1_homeomorphism_on_def by (by100 blast)
        from bij_betw_trans[OF \<open>bij_betw (\<lambda>s. 1 - s) top1_unit_interval top1_unit_interval\<close>
            \<open>bij_betw h top1_unit_interval A\<close>]
        show ?thesis by (by100 simp)
      qed
      have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
        unfolding top1_unit_interval_def top1_unit_interval_topology_def
        using Theorem_27_1[of "0::real" 1] by (by100 simp)
      from Theorem_26_6[OF top1_unit_interval_topology_is_topology_on _ hI_compact hA_haus h_cont_comp h_bij_comp]
      show ?thesis using hA_strict unfolding is_topology_on_strict_def by (by100 blast)
    qed
    moreover have "?h' 0 = p" using \<open>p = h 1\<close> by (by100 simp)
    ultimately show ?thesis using that by (by100 blast)
  qed
  \<comment> \<open>Now h': [0,1] \<rightarrow> A homeomorphism with h'(0) = p.
     Define H'(x,t) = h'(G(h'\<inverse>(x), t)). This is the deformation retraction of A to \{p\}.\<close>
  let ?h'inv = "inv_into top1_unit_interval h'"
  have hh'inv: "top1_homeomorphism_on A TA top1_unit_interval top1_unit_interval_topology ?h'inv"
    by (rule homeomorphism_inverse[OF hh'])
  \<comment> \<open>The deformation retraction.\<close>
  define H' where "H' \<equiv> \<lambda>(x,t). h' (G (?h'inv x, t))"
  have hh'_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology A TA h'"
    using hh' unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh'inv_cont: "top1_continuous_map_on A TA top1_unit_interval top1_unit_interval_topology ?h'inv"
    using hh'inv unfolding top1_homeomorphism_on_def by (by100 blast)
  have hh'_bij: "bij_betw h' top1_unit_interval A"
    using hh' unfolding top1_homeomorphism_on_def by (by100 blast)
  have hTA_top: "is_topology_on A TA"
    using hA_strict unfolding is_topology_on_strict_def by (by100 blast)
  have hI_top: "is_topology_on top1_unit_interval top1_unit_interval_topology"
    by (rule top1_unit_interval_topology_is_topology_on)
  \<comment> \<open>(a) H'(x,0) = x for x \<in> A.\<close>
  have hH'0: "\<forall>x\<in>A. H' (x, 0) = x"
  proof (intro ballI)
    fix x assume "x \<in> A"
    have "?h'inv x \<in> top1_unit_interval"
      using \<open>x \<in> A\<close> hh'inv unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have "G (?h'inv x, 0) = ?h'inv x" using hG0 \<open>?h'inv x \<in> top1_unit_interval\<close> by (by100 blast)
    hence "H' (x, 0) = h' (?h'inv x)" unfolding H'_def by (by100 simp)
    also have "\<dots> = x" using f_inv_into_f[of x h' top1_unit_interval] hh'_bij \<open>x \<in> A\<close>
      unfolding bij_betw_def by (by100 blast)
    finally show "H' (x, 0) = x" .
  qed
  \<comment> \<open>(b) H'(x,1) = h'(0) = p for x \<in> A.\<close>
  have hH'1: "\<forall>x\<in>A. H' (x, 1) \<in> {p}"
  proof (intro ballI)
    fix x assume "x \<in> A"
    have "?h'inv x \<in> top1_unit_interval"
      using \<open>x \<in> A\<close> hh'inv unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
    have "G (?h'inv x, 1) = 0" using hG1 \<open>?h'inv x \<in> top1_unit_interval\<close> by (by100 blast)
    hence "H' (x, 1) = h' 0" unfolding H'_def by (by100 simp)
    thus "H' (x, 1) \<in> {p}" using hh'0 by (by100 simp)
  qed
  \<comment> \<open>(c) H'(p,t) = p for t \<in> [0,1].\<close>
  have hH'fix: "\<forall>a\<in>{p}. \<forall>t\<in>top1_unit_interval. H' (a, t) = a"
  proof (intro ballI)
    fix a t assume "a \<in> {p}" "t \<in> top1_unit_interval"
    hence "a = p" by (by100 blast)
    have "?h'inv p = 0"
    proof -
      have "h' 0 = p" using hh'0 .
      have "(0::real) \<in> top1_unit_interval" unfolding top1_unit_interval_def by (by100 simp)
      have "inj_on h' top1_unit_interval" using hh'_bij unfolding bij_betw_def by (by100 blast)
      from inv_into_f_eq[OF this \<open>(0::real) \<in> top1_unit_interval\<close> \<open>h' 0 = p\<close>]
      have "?h'inv p = 0" .
      thus ?thesis .
    qed
    have "G (0, t) = 0" using hGfix \<open>t \<in> top1_unit_interval\<close> by (by100 blast)
    hence "H' (p, t) = h' 0" unfolding H'_def using \<open>?h'inv p = 0\<close> by (by100 simp)
    thus "H' (a, t) = a" using \<open>a = p\<close> hh'0 by (by100 simp)
  qed
  \<comment> \<open>(d) H' continuous: H' = h' \<circ> G \<circ> (h'inv \<times> id).\<close>
  have hH'_cont: "top1_continuous_map_on (A \<times> top1_unit_interval)
      (product_topology_on TA top1_unit_interval_topology) A TA H'"
  proof -
    let ?AI_top = "product_topology_on TA top1_unit_interval_topology"
    let ?II_top = "product_topology_on top1_unit_interval_topology top1_unit_interval_topology"
    have hAI_top: "is_topology_on (A \<times> top1_unit_interval) ?AI_top"
      by (rule product_topology_on_is_topology_on[OF hTA_top hI_top])
    \<comment> \<open>The pair map \<phi>: A\<times>I \<rightarrow> I\<times>I, \<phi>(x,t) = (h'inv(x), t), is continuous by Theorem 18.4.\<close>
    define \<phi> where "\<phi> \<equiv> \<lambda>p. (inv_into top1_unit_interval h' (fst p), snd p :: real)"
    have h\<phi>_eq: "\<And>x t. \<phi> (x, t) = (inv_into top1_unit_interval h' x, t)" unfolding \<phi>_def by (by100 simp)
    have h\<phi>_cont: "top1_continuous_map_on (A \<times> top1_unit_interval) ?AI_top
        (top1_unit_interval \<times> top1_unit_interval) ?II_top \<phi>"
    proof -
      have "top1_continuous_map_on (A \<times> top1_unit_interval) ?AI_top
          (top1_unit_interval \<times> top1_unit_interval) ?II_top \<phi>
        \<longleftrightarrow> (top1_continuous_map_on (A \<times> top1_unit_interval) ?AI_top
              top1_unit_interval top1_unit_interval_topology (pi1 \<circ> \<phi>)
           \<and> top1_continuous_map_on (A \<times> top1_unit_interval) ?AI_top
              top1_unit_interval top1_unit_interval_topology (pi2 \<circ> \<phi>))"
        by (rule Theorem_18_4[OF hAI_top hI_top hI_top])
      moreover have "pi1 \<circ> \<phi> = inv_into top1_unit_interval h' \<circ> pi1"
        unfolding \<phi>_def pi1_def by (by100 auto)
      moreover have "pi2 \<circ> \<phi> = pi2"
        unfolding \<phi>_def pi2_def by (by100 auto)
      moreover have "top1_continuous_map_on (A \<times> top1_unit_interval) ?AI_top
          top1_unit_interval top1_unit_interval_topology (inv_into top1_unit_interval h' \<circ> pi1)"
        by (rule top1_continuous_map_on_comp[OF top1_continuous_pi1[OF hTA_top hI_top] hh'inv_cont])
      moreover have "top1_continuous_map_on (A \<times> top1_unit_interval) ?AI_top
          top1_unit_interval top1_unit_interval_topology pi2"
        by (rule top1_continuous_pi2[OF hTA_top hI_top])
      ultimately show ?thesis by (by100 simp)
    qed
    \<comment> \<open>G \<circ> \<phi>: A\<times>I \<rightarrow> I continuous.\<close>
    have "top1_continuous_map_on (A \<times> top1_unit_interval) ?AI_top
        top1_unit_interval top1_unit_interval_topology (G \<circ> \<phi>)"
      by (rule top1_continuous_map_on_comp[OF h\<phi>_cont hG_top1])
    \<comment> \<open>h' \<circ> G \<circ> \<phi>: A\<times>I \<rightarrow> A continuous.\<close>
    hence "top1_continuous_map_on (A \<times> top1_unit_interval) ?AI_top A TA (h' \<circ> (G \<circ> \<phi>))"
      by (rule top1_continuous_map_on_comp[OF _ hh'_cont])
    \<comment> \<open>H' = h' \<circ> G \<circ> \<phi>.\<close>
    moreover have "\<And>p. p \<in> A \<times> top1_unit_interval \<Longrightarrow> H' p = (h' \<circ> (G \<circ> \<phi>)) p"
      unfolding H'_def \<phi>_def G_def by (by100 auto)
    ultimately have "top1_continuous_map_on (A \<times> top1_unit_interval) ?AI_top A TA (h' \<circ> (G \<circ> \<phi>))"
        and heq: "\<And>p. p \<in> A \<times> top1_unit_interval \<Longrightarrow> H' p = (h' \<circ> (G \<circ> \<phi>)) p"
      by (by100 blast)+
    \<comment> \<open>Functions that agree on the carrier have the same continuity.\<close>
    have "\<And>V. {p \<in> A \<times> top1_unit_interval. H' p \<in> V}
        = {p \<in> A \<times> top1_unit_interval. (h' \<circ> (G \<circ> \<phi>)) p \<in> V}"
      using heq by (by100 auto)
    thus ?thesis using \<open>top1_continuous_map_on (A \<times> top1_unit_interval) ?AI_top A TA (h' \<circ> (G \<circ> \<phi>))\<close>
      unfolding top1_continuous_map_on_def using heq by (by100 auto)
  qed
  show ?thesis
    unfolding top1_deformation_retract_of_on_def
    using hp_in_A hH'_cont hH'0 hH'1 hH'fix
    apply (intro conjI)
    apply (by100 blast)
    apply (rule exI[of _ H'])
    apply (intro conjI)
    apply (by100 blast)+
    done
qed

text \<open>Lemma 84.2 (Munkres): If T is a tree in X and A is an arc meeting T in a single
  vertex, then T \<union> A is a tree. Proof: T \<union> A connected (share vertex).
  Simply connected: A deformation retracts to the shared vertex, so T \<union> A
  deformation retracts to T, hence \<pi>\_1(T \<union> A) = \<pi>\_1(T) = 0.\<close>
lemma Lemma_84_2_tree_union_arc:
  assumes "top1_is_graph_on X TX"
      and "top1_is_tree_on T (subspace_topology X TX T)" and "T \<subseteq> X"
      and "A \<in> \<A>" and "\<forall>B\<in>\<A>. B \<subseteq> X \<and> top1_is_arc_on B (subspace_topology X TX B)"
      and "\<Union>\<A> = X"
      and "\<forall>B\<in>\<A>. \<forall>C\<in>\<A>. B \<noteq> C \<longrightarrow>
           B \<inter> C \<subseteq> top1_arc_endpoints_on B (subspace_topology X TX B)
         \<and> B \<inter> C \<subseteq> top1_arc_endpoints_on C (subspace_topology X TX C)
         \<and> finite (B \<inter> C) \<and> card (B \<inter> C) \<le> 2"
      and "A \<inter> T \<noteq> {}" and "A \<inter> T \<subseteq> top1_arc_endpoints_on A (subspace_topology X TX A)"
      and "card (A \<inter> T) = 1"
      and "A \<subseteq> X"
      and "closedin_on X TX T"
      and "top1_is_graph_on (T \<union> A) (subspace_topology X TX (T \<union> A))"
  shows "top1_is_tree_on (T \<union> A) (subspace_topology X TX (T \<union> A))"
proof -
  let ?TUA = "subspace_topology X TX (T \<union> A)"
  \<comment> \<open>Munkres Lemma 84.2. Three parts: graph + connected + simply connected.\<close>
  \<comment> \<open>Part 1: T \<union> A is a graph (assumed).\<close>
  have hTUA_graph: "top1_is_graph_on (T \<union> A) ?TUA" using assms(13) .
  \<comment> \<open>Part 2: T \<union> A is connected (T connected + A connected + shared vertex a).\<close>
  have hTUA_conn: "top1_connected_on (T \<union> A) ?TUA"
  proof -
    have hTX: "is_topology_on X TX"
      using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
    have hT_conn: "top1_connected_on T (subspace_topology X TX T)"
      using assms(2) unfolding top1_is_tree_on_def by (by100 blast)
    have hA_conn: "top1_connected_on A (subspace_topology X TX A)"
    proof -
      have "top1_is_arc_on A (subspace_topology X TX A)" using assms(4,5) by (by100 blast)
      thus ?thesis using arc_connected by (by100 blast)
    qed
    have hTUA_sub: "T \<union> A \<subseteq> X" using assms(3,11) by (by100 blast)
    \<comment> \<open>T and A share a point (from A \<inter> T \<noteq> {}).\<close>
    from assms(8) obtain a where "a \<in> A \<inter> T" by (by100 blast)
    hence "a \<in> T" "a \<in> A" by (by100 blast)+
    \<comment> \<open>Theorem 23.3: union of connected sets with common point is connected.\<close>
    define B :: "bool \<Rightarrow> 'a set" where "B \<equiv> \<lambda>b. if b then A else T"
    have hB_conn: "\<forall>i\<in>{True, False}. top1_connected_on (B i) (subspace_topology X TX (B i))"
      unfolding B_def using hT_conn hA_conn by (by100 auto)
    have hB_sub: "\<forall>i\<in>{True, False}. B i \<subseteq> X"
      unfolding B_def using assms(3,11) by (by100 auto)
    have "a \<in> \<Inter>(B ` {True, False})"
      unfolding B_def using \<open>a \<in> T\<close> \<open>a \<in> A\<close> by (by100 auto)
    have hY: "(\<Union>i\<in>{True, False}. B i) = T \<union> A"
      unfolding B_def by (by100 auto)
    have "{True, False} \<noteq> ({}::bool set)" by (by100 blast)
    from Theorem_23_3[OF hTX \<open>{True, False} \<noteq> {}\<close> hB_sub hB_conn \<open>a \<in> \<Inter>(B ` {True, False})\<close>]
    show ?thesis using hY by (by100 simp)
  qed
  \<comment> \<open>Part 3: T \<union> A is simply connected.
     A is contractible (arc). T \<inter> A = \{a\} (single point). So T \<union> A deformation
     retracts to T via collapsing A to a. Hence \<pi>\_1(T \<union> A) = \<pi>\_1(T) = 0.\<close>
  have hTUA_sc: "top1_simply_connected_on (T \<union> A) ?TUA"
  proof -
    \<comment> \<open>Step 1: Get endpoint a \<in> A \<inter> T.\<close>
    from assms(8,10) obtain a where ha: "a \<in> A" "a \<in> T" "A \<inter> T = {a}"
    proof -
      from card_eq_SucD[OF assms(10)[simplified]]
      obtain b B where "A \<inter> T = insert b B" "b \<notin> B" "card B = 0" "B = {}" by (by100 blast)
      hence "A \<inter> T = {b}" by (by100 simp)
      hence "b \<in> A" "b \<in> T" by (by100 blast)+
      with \<open>A \<inter> T = {b}\<close> show ?thesis using that by (by100 blast)
    qed
    have ha_ep: "a \<in> top1_arc_endpoints_on A (subspace_topology X TX A)"
    proof -
      have "a \<in> A \<inter> T" using ha(1,2) by (by100 blast)
      thus ?thesis using assms(9) by (by100 blast)
    qed
    \<comment> \<open>Step 2: A deformation retracts to \{a\}.\<close>
    have hA_arc: "top1_is_arc_on A (subspace_topology X TX A)"
      using assms(4,5) by (by100 blast)
    have hA_dr: "top1_deformation_retract_of_on A (subspace_topology X TX A) {a}"
      by (rule arc_deformation_retract_to_endpoint[OF hA_arc ha_ep])
    \<comment> \<open>Step 3: Use pasting\_deformation\_retract\_to\_subspace.
       F = \{T, A\}, A0 = T. T \<union> A deformation retracts to T.\<close>
    have hTX: "is_topology_on X TX"
      using assms(1) unfolding top1_is_graph_on_def is_topology_on_strict_def by (by100 blast)
    have hTX_strict: "is_topology_on_strict X TX"
      using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
    have hTUA_sub: "T \<union> A \<subseteq> X" using assms(3,11) by (by100 blast)
    have hTUA_strict: "is_topology_on_strict (T \<union> A) ?TUA"
      by (rule subspace_topology_is_strict[OF hTX_strict hTUA_sub])
    \<comment> \<open>T is closed in X (tree in Hausdorff graph \<Rightarrow> compact \<Rightarrow> closed; or use graph coherent topology).\<close>
    have hT_closed_X: "closedin_on X TX T" using assms(12) .
    have hA_closed_X: "closedin_on X TX A"
    proof -
      \<comment> \<open>A is an arc \<Rightarrow> compact (homeomorphic to [0,1]). Compact in Hausdorff \<Rightarrow> closed.\<close>
      have hA_arc: "top1_is_arc_on A (subspace_topology X TX A)"
        using assms(4,5) by (by100 blast)
      have hX_haus: "is_hausdorff_on X TX"
        using assms(1) unfolding top1_is_graph_on_def by (by100 blast)
      have hA_compact: "top1_compact_on A (subspace_topology X TX A)"
      proof -
        from hA_arc obtain h where hh: "top1_homeomorphism_on top1_unit_interval
            top1_unit_interval_topology A (subspace_topology X TX A) h"
          unfolding top1_is_arc_on_def by (by100 blast)
        have hh_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
            A (subspace_topology X TX A) h"
          using hh unfolding top1_homeomorphism_on_def by (by100 blast)
        have hh_surj: "h ` top1_unit_interval = A"
          using hh unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
        have hI_compact: "top1_compact_on top1_unit_interval top1_unit_interval_topology"
          unfolding top1_unit_interval_def top1_unit_interval_topology_def
          using Theorem_27_1[of "0::real" 1] by (by100 simp)
        have hA_top: "is_topology_on A (subspace_topology X TX A)"
          using hA_arc unfolding top1_is_arc_on_def is_topology_on_strict_def by (by100 blast)
        from top1_compact_on_continuous_image[OF hI_compact hA_top hh_cont]
        have "top1_compact_on (h ` top1_unit_interval) (subspace_topology A (subspace_topology X TX A) (h ` top1_unit_interval))" .
        hence "top1_compact_on A (subspace_topology A (subspace_topology X TX A) A)"
          using hh_surj by (by100 simp)
        moreover have "subspace_topology A (subspace_topology X TX A) A = subspace_topology X TX A"
          by (rule subspace_topology_trans, by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      from compact_in_hausdorff_closed[OF hX_haus hA_compact assms(11)]
      show ?thesis .
    qed
    have hT_closed_TUA: "closedin_on (T \<union> A) ?TUA T"
      by (rule closedin_subspace_from_ambient[OF hTX hT_closed_X hTUA_sub], by100 blast)
    have hA_closed_TUA: "closedin_on (T \<union> A) ?TUA A"
      by (rule closedin_subspace_from_ambient[OF hTX hA_closed_X hTUA_sub], by100 blast)
    \<comment> \<open>T deformation retracts to T (trivially: identity). But pasting lemma needs
       deformation retracts to \{a\}. Use pasting\_deformation\_retracts\_to\_point instead:
       both T and A deformation retract to \{a\} in their subspace topologies.
       But T doesn't deformation retract to \{a\} (T is not contractible in general).
       Instead, use pasting\_deformation\_retract\_to\_subspace.\<close>
    have hTUA_dr: "top1_deformation_retract_of_on (T \<union> A) ?TUA T"
    proof -
      let ?F = "{T, A}"
      have "finite ?F" by (by100 simp)
      have "T \<in> ?F" by (by100 blast)
      have "\<forall>B\<in>?F. closedin_on (T \<union> A) ?TUA B"
        using hT_closed_TUA hA_closed_TUA by (by100 blast)
      have "T \<union> A = \<Union>?F" by (by100 blast)
      have "a \<in> T" using ha(2) by (by100 simp)
      have "\<forall>B\<in>?F. a \<in> B" using ha(1,2) by (by100 blast)
      have "\<forall>B1\<in>?F. \<forall>B2\<in>?F. B1 \<noteq> B2 \<longrightarrow> B1 \<inter> B2 \<subseteq> {a}"
        using ha(3) by (by100 blast)
      have "\<forall>B\<in>?F - {T}. top1_deformation_retract_of_on B (subspace_topology (T \<union> A) ?TUA B) {a}"
      proof (intro ballI)
        fix B assume "B \<in> ?F - {T}"
        hence "B = A" by (by100 blast)
        \<comment> \<open>A deformation retracts to \{a\} in its subspace topology from X.
           But we need it in the subspace topology from T \<union> A.
           These coincide by subspace transitivity: A \<subseteq> T \<union> A \<subseteq> X.\<close>
        have "subspace_topology (T \<union> A) ?TUA A = subspace_topology X TX A"
          by (rule subspace_topology_trans, by100 blast)
        thus "top1_deformation_retract_of_on B (subspace_topology (T \<union> A) ?TUA B) {a}"
          using \<open>B = A\<close> hA_dr
              \<open>subspace_topology (T \<union> A) ?TUA A = subspace_topology X TX A\<close>
          by (by100 simp)
      qed
      from pasting_deformation_retract_to_subspace[OF hTUA_strict \<open>finite ?F\<close> \<open>T \<in> ?F\<close>
          \<open>\<forall>B\<in>?F. closedin_on (T \<union> A) ?TUA B\<close> \<open>T \<union> A = \<Union>?F\<close> \<open>a \<in> T\<close> \<open>\<forall>B\<in>?F. a \<in> B\<close>
          \<open>\<forall>B1\<in>?F. \<forall>B2\<in>?F. B1 \<noteq> B2 \<longrightarrow> B1 \<inter> B2 \<subseteq> {a}\<close> this]
      show ?thesis .
    qed
    \<comment> \<open>Step 4: T is simply connected (from tree assumption).\<close>
    have hT_sc: "top1_simply_connected_on T (subspace_topology X TX T)"
      using assms(2) unfolding top1_is_tree_on_def by (by100 blast)
    \<comment> \<open>Step 5: Deformation retract preserves simply-connectedness.\<close>
    have hTUA_top: "is_topology_on (T \<union> A) ?TUA"
      using hTUA_strict unfolding is_topology_on_strict_def by (by100 blast)
    obtain a0 where "a0 \<in> T" using assms(8) by (by100 blast)
    from Theorem_58_3[OF hTUA_dr hTUA_top \<open>a0 \<in> T\<close>]
    have "top1_groups_isomorphic_on
        (top1_fundamental_group_carrier T (subspace_topology (T \<union> A) ?TUA T) a0)
        (top1_fundamental_group_mul T (subspace_topology (T \<union> A) ?TUA T) a0)
        (top1_fundamental_group_carrier (T \<union> A) ?TUA a0)
        (top1_fundamental_group_mul (T \<union> A) ?TUA a0)" .
    \<comment> \<open>The subspace topology on T from T \<union> A = subspace topology on T from X.\<close>
    have "subspace_topology (T \<union> A) ?TUA T = subspace_topology X TX T"
      by (rule subspace_topology_trans, by100 blast)
    \<comment> \<open>T simply connected + \<pi>\_1(T) \<cong> \<pi>\_1(T \<union> A) \<Rightarrow> T \<union> A simply connected.
       T simply conn means all loops null-homotopic.
       The iso means \<pi>\_1(T \<union> A) is isomorphic to trivial group.
       Plus path-connectivity of T \<union> A \<Rightarrow> simply connected.\<close>
    \<comment> \<open>\<pi>\_1(T, a0) = \{id\} (T simply connected). Iso maps to \<pi>\_1(T \<union> A, a0).
       Hence \<pi>\_1(T \<union> A) carrier is singleton. All loops null-homotopic.
       + path connected \<Rightarrow> simply connected.\<close>
    have h\<pi>1T_trivial: "top1_fundamental_group_carrier T (subspace_topology X TX T) a0
        = {top1_fundamental_group_id T (subspace_topology X TX T) a0}"
      by (rule simply_connected_trivial_carrier[OF hT_sc \<open>a0 \<in> T\<close>])
    \<comment> \<open>The iso maps \{id\} to \<pi>\_1(T \<union> A, a0). So \<pi>\_1(T \<union> A, a0) = \{id'\}.\<close>
    have h\<pi>1TUA_trivial: "top1_fundamental_group_carrier (T \<union> A) ?TUA a0
        = {top1_fundamental_group_id (T \<union> A) ?TUA a0}"
    proof -
      \<comment> \<open>Substitute the topology equality.\<close>
      have hiso': "top1_groups_isomorphic_on
          (top1_fundamental_group_carrier T (subspace_topology X TX T) a0)
          (top1_fundamental_group_mul T (subspace_topology X TX T) a0)
          (top1_fundamental_group_carrier (T \<union> A) ?TUA a0)
          (top1_fundamental_group_mul (T \<union> A) ?TUA a0)"
        using \<open>top1_groups_isomorphic_on
            (top1_fundamental_group_carrier T (subspace_topology (T \<union> A) ?TUA T) a0)
            (top1_fundamental_group_mul T (subspace_topology (T \<union> A) ?TUA T) a0)
            (top1_fundamental_group_carrier (T \<union> A) ?TUA a0)
            (top1_fundamental_group_mul (T \<union> A) ?TUA a0)\<close>
            \<open>subspace_topology (T \<union> A) ?TUA T = subspace_topology X TX T\<close>
        by (by100 simp)
      \<comment> \<open>Extract bijection from iso.\<close>
      from hiso' obtain f where
          hf_bij: "bij_betw f (top1_fundamental_group_carrier T (subspace_topology X TX T) a0)
              (top1_fundamental_group_carrier (T \<union> A) ?TUA a0)"
        unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def by (by100 blast)
      \<comment> \<open>\<pi>\_1(T) = \{id\_T\}. Bijection of singleton = singleton.\<close>
      have "top1_fundamental_group_carrier (T \<union> A) ?TUA a0
          = f ` {top1_fundamental_group_id T (subspace_topology X TX T) a0}"
        using hf_bij h\<pi>1T_trivial unfolding bij_betw_def by (by100 auto)
      hence "top1_fundamental_group_carrier (T \<union> A) ?TUA a0
          = {f (top1_fundamental_group_id T (subspace_topology X TX T) a0)}" by (by100 simp)
      \<comment> \<open>H = \{f(e\_G)\}. Since H is a group, e\_H \<in> H = \{f(e\_G)\}. So H = \{e\_H\}.\<close>
      moreover have "top1_fundamental_group_id (T \<union> A) ?TUA a0
          \<in> top1_fundamental_group_carrier (T \<union> A) ?TUA a0"
      proof -
        have ha0_TUA: "a0 \<in> T \<union> A" using \<open>a0 \<in> T\<close> by (by100 blast)
        from top1_fundamental_group_is_group[OF hTUA_top ha0_TUA]
        show ?thesis unfolding top1_is_group_on_def by (by100 blast)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    \<comment> \<open>Trivial \<pi>\_1 + path connected \<Rightarrow> simply connected.\<close>
    have hTUA_pc: "top1_path_connected_on (T \<union> A) ?TUA"
    proof -
      \<comment> \<open>T path-connected (tree \<Rightarrow> simply connected \<Rightarrow> path connected).\<close>
      have hT_pc: "top1_path_connected_on T (subspace_topology X TX T)"
        using hT_sc unfolding top1_simply_connected_on_def by (by100 blast)
      \<comment> \<open>A path-connected (arc \<Rightarrow> connected; arc = homeo image of [0,1] \<Rightarrow> path connected).\<close>
      have hA_pc: "top1_path_connected_on A (subspace_topology X TX A)"
      proof -
        have hA_arc: "top1_is_arc_on A (subspace_topology X TX A)"
          using assms(4,5) by (by100 blast)
        from hA_arc obtain h where hh: "top1_homeomorphism_on top1_unit_interval
            top1_unit_interval_topology A (subspace_topology X TX A) h"
          unfolding top1_is_arc_on_def by (by100 blast)
        have "top1_path_connected_on top1_unit_interval top1_unit_interval_topology"
          unfolding top1_path_connected_on_def
        proof (intro conjI ballI)
          show "is_topology_on top1_unit_interval top1_unit_interval_topology"
            by (rule top1_unit_interval_topology_is_topology_on)
        next
          fix x y assume hx: "x \<in> top1_unit_interval" and hy: "y \<in> top1_unit_interval"
          \<comment> \<open>Straight-line path f(t) = (1-t)x + ty.\<close>
          let ?f = "\<lambda>t::real. (1 - t) * x + t * y"
          have hf_range: "\<forall>t\<in>top1_unit_interval. ?f t \<in> top1_unit_interval"
          proof (intro ballI)
            fix t assume ht: "t \<in> top1_unit_interval"
            hence "0 \<le> t" "t \<le> 1" unfolding top1_unit_interval_def by (by100 auto)+
            from hx have "0 \<le> x" "x \<le> 1" unfolding top1_unit_interval_def by (by100 auto)+
            from hy have "0 \<le> y" "y \<le> 1" unfolding top1_unit_interval_def by (by100 auto)+
            have h1t: "0 \<le> 1 - t" using \<open>t \<le> 1\<close> by (by100 linarith)
            have "0 \<le> (1 - t) * x" using h1t \<open>0 \<le> x\<close> by (by100 auto)
            moreover have "0 \<le> t * y" using \<open>0 \<le> t\<close> \<open>0 \<le> y\<close> by (by100 auto)
            ultimately have "0 \<le> (1 - t) * x + t * y" by (by100 linarith)
            moreover have "(1 - t) * x + t * y \<le> 1"
            proof -
              have "(1 - t) * x \<le> (1 - t) * 1"
                using mult_left_mono[OF \<open>x \<le> 1\<close> h1t] .
              moreover have "t * y \<le> t * 1"
                using mult_left_mono[OF \<open>y \<le> 1\<close> \<open>0 \<le> t\<close>] .
              ultimately have "(1 - t) * x + t * y \<le> (1 - t) * 1 + t * 1" by (by100 linarith)
              thus ?thesis by (by100 simp)
            qed
            ultimately show "?f t \<in> top1_unit_interval"
              unfolding top1_unit_interval_def by (by100 auto)
          qed
          have hf_cont: "top1_continuous_map_on top1_unit_interval top1_unit_interval_topology
              top1_unit_interval top1_unit_interval_topology ?f"
          proof -
            have "continuous_on top1_unit_interval ?f"
              by (intro continuous_intros)
            from top1_continuous_map_on_subspace_open_sets_on[OF _ this] hf_range
            have "top1_continuous_map_on top1_unit_interval
                (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval)
                top1_unit_interval
                (subspace_topology (UNIV::real set) top1_open_sets top1_unit_interval) ?f"
              by (by100 blast)
            thus ?thesis unfolding top1_unit_interval_topology_def by (by100 simp)
          qed
          have "?f 0 = x" by (by100 simp)
          moreover have "?f 1 = y" by (by100 simp)
          ultimately have "top1_is_path_on top1_unit_interval top1_unit_interval_topology x y ?f"
            unfolding top1_is_path_on_def using hf_cont by (by100 blast)
          thus "\<exists>f. top1_is_path_on top1_unit_interval top1_unit_interval_topology x y f"
            by (by100 blast)
        qed
        from homeomorphism_preserves_path_connected[OF hh this]
        show ?thesis .
      qed
      \<comment> \<open>T and A share point a. Subspace topology = X topology restricted.\<close>
      have hT_pc': "top1_path_connected_on T (subspace_topology (T \<union> A) ?TUA T)"
        using hT_pc \<open>subspace_topology (T \<union> A) ?TUA T = subspace_topology X TX T\<close> by (by100 simp)
      have hA_pc': "top1_path_connected_on A (subspace_topology (T \<union> A) ?TUA A)"
      proof -
        have "subspace_topology (T \<union> A) ?TUA A = subspace_topology X TX A"
          by (rule subspace_topology_trans, by100 blast)
        thus ?thesis using hA_pc by (by100 simp)
      qed
      from assms(8) obtain a where "a \<in> A \<inter> T" by (by100 blast)
      let ?F = "{T, A}"
      have "\<forall>B\<in>?F. B \<subseteq> T \<union> A" by (by100 blast)
      have "\<forall>B\<in>?F. top1_path_connected_on B (subspace_topology (T \<union> A) ?TUA B)"
        using hT_pc' hA_pc' by (by100 blast)
      have "\<forall>B\<in>?F. a \<in> B" using \<open>a \<in> A \<inter> T\<close> by (by100 blast)
      have "T \<union> A = \<Union>?F" by (by100 blast)
      from path_connected_finite_union_common_point[OF hTUA_top, of ?F a]
      show ?thesis
        using \<open>\<forall>B\<in>?F. B \<subseteq> T \<union> A\<close> \<open>\<forall>B\<in>?F. top1_path_connected_on B (subspace_topology (T \<union> A) ?TUA B)\<close>
            \<open>\<forall>B\<in>?F. a \<in> B\<close> \<open>T \<union> A = \<Union>?F\<close> by (by100 blast)
    qed
    have ha0_TUA: "a0 \<in> T \<union> A" using \<open>a0 \<in> T\<close> by (by100 blast)
    \<comment> \<open>Trivial \<pi>\_1 means all loops null-homotopic.\<close>
    have "\<forall>f. top1_is_loop_on (T \<union> A) ?TUA a0 f
        \<longrightarrow> top1_path_homotopic_on (T \<union> A) ?TUA a0 a0 f (top1_constant_path a0)"
    proof (intro allI impI)
      fix f assume hf: "top1_is_loop_on (T \<union> A) ?TUA a0 f"
      \<comment> \<open>[f] \<in> carrier = \{id\}, so [f] = id. f \<in> [f] = id = [const]. Hence f \<sim> const.\<close>
      let ?cf = "{g. top1_loop_equiv_on (T \<union> A) ?TUA a0 f g}"
      have "?cf \<in> top1_fundamental_group_carrier (T \<union> A) ?TUA a0"
        unfolding top1_fundamental_group_carrier_def using hf by (by100 blast)
      hence "?cf \<in> {top1_fundamental_group_id (T \<union> A) ?TUA a0}"
        using h\<pi>1TUA_trivial by (by100 simp)
      hence "?cf = top1_fundamental_group_id (T \<union> A) ?TUA a0"
        by (by100 blast)
      hence "f \<in> top1_fundamental_group_id (T \<union> A) ?TUA a0"
        using top1_loop_equiv_on_refl[OF hf] by (by100 blast)
      hence "top1_loop_equiv_on (T \<union> A) ?TUA a0 (top1_constant_path a0) f"
        unfolding top1_fundamental_group_id_def by (by100 blast)
      thus "top1_path_homotopic_on (T \<union> A) ?TUA a0 a0 f (top1_constant_path a0)"
        using top1_loop_equiv_on_sym[OF \<open>top1_loop_equiv_on (T \<union> A) ?TUA a0 (top1_constant_path a0) f\<close>]
        unfolding top1_loop_equiv_on_def by (by100 blast)
    qed
    from top1_simply_connected_from_one_point[OF hTUA_top hTUA_pc ha0_TUA this]
    show ?thesis .
  qed
  show ?thesis unfolding top1_is_tree_on_def
    using hTUA_graph hTUA_conn hTUA_sc by (by100 blast)
qed

text \<open>Theorem 84.4 (Munkres): In a connected graph, the maximal tree meets every arc.
  Proof: The set R of arcs reachable from T via chains of overlapping arcs covers all of X.
  R is clopen in X (coherent topology: R \<inter> A is either A or empty for each arc A).
  Since X is connected and R non-empty (T \<subseteq> R), R = X.
  Then every arc has an endpoint in T (otherwise T \<union> A is a larger tree, contradiction).\<close>

end
