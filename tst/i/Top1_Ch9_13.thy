theory Top1_Ch9_13
  imports Top1_Ch5_8
begin

ML \<open>
  fun method_evaluate text ctxt facts =
    NO_CONTEXT_TACTIC ctxt (Method.evaluate_runtime text ctxt facts)

  fun timed_seq name limit seq =
    Seq.make (fn () =>
      (case
         (Timeout.apply limit (fn () => Seq.pull seq) ()
           handle Timeout.TIMEOUT _ =>
             error (name ^ ": timeout after " ^
               string_of_int (Time.toMilliseconds limit) ^ " ms"))
       of
         NONE => NONE
       | SOME (st, seq') => SOME (st, timed_seq name limit seq')))
\<close>

method_setup by100 =
  \<open>
    Method.text_closure >> (fn text => fn ctxt => fn facts =>
      let
        val limit = Time.fromMilliseconds 100
        fun tac st = timed_seq "by100" limit (method_evaluate text ctxt facts st)
      in
        SIMPLE_METHOD tac facts
      end)
  \<close>
  "apply a proof method with 100ms timeout per result step"


text \<open>
  Formalization of algebraic topology from Munkres (algtop.tex), Chapters 9-14.

  Chapter 9: The Fundamental Group (§51-60)
  Chapter 10: Separation Theorems in the Plane (§61-66)
  Chapter 11: The Seifert-van Kampen Theorem (§67-73)
  Chapter 12: Classification of Surfaces (§74-78)
  Chapter 13: Classification of Covering Spaces (§79-82)
  Chapter 14: Applications to Group Theory (§83-85)

  Built on the general topology library (Top0 = Top1_Ch2 through Top1_Ch5_8).
  Uses top1_unit_interval, top1_is_path_on, top1_path_connected_on, etc.
\<close>

section \<open>\<S>51 Homotopy of Paths\<close>

text \<open>I = [0,1] is top1_unit_interval (defined in Top1_Ch3).
  We use I\<times>I with the product topology as the domain of path homotopies.\<close>

abbreviation (input) "I_top \<equiv> top1_unit_interval_topology"
abbreviation (input) "I_set \<equiv> top1_unit_interval"

text \<open>The product of euclidean open sets is the euclidean open sets on the product.\<close>
lemma product_topology_on_open_sets:
  "product_topology_on (top1_open_sets :: 'a::topological_space set set)
                       (top1_open_sets :: 'b::topological_space set set)
   = (top1_open_sets :: ('a \<times> 'b) set set)"
proof (rule set_eqI, rule iffI)
  fix W :: "('a \<times> 'b) set"
  assume hW: "W \<in> product_topology_on top1_open_sets top1_open_sets"
  have hTX: "is_topology_on (UNIV :: 'a set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
  have hTY: "is_topology_on (UNIV :: 'b set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
  have hUU: "(UNIV :: 'a set) \<times> (UNIV :: 'b set) = (UNIV :: ('a \<times> 'b) set)" by simp
  have hTP: "is_topology_on (UNIV :: ('a \<times> 'b) set) (product_topology_on top1_open_sets top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTX hTY] unfolding hUU .
  have "open W"
  proof (rule open_prod_intro)
    fix x assume hx: "x \<in> W"
    \<comment> \<open>W is in a product topology, so it contains a basis element around x.\<close>
    have "W \<subseteq> UNIV" by simp
    obtain U V where hU: "U \<in> top1_open_sets" and hV: "V \<in> top1_open_sets"
        and hxUV: "x \<in> U \<times> V" and hUVW: "U \<times> V \<subseteq> W"
    proof -
      have "W \<in> topology_generated_by_basis UNIV (product_basis top1_open_sets top1_open_sets)"
        using hW unfolding product_topology_on_def .
      hence "\<exists>b\<in>product_basis top1_open_sets top1_open_sets. x \<in> b \<and> b \<subseteq> W"
        using hx unfolding topology_generated_by_basis_def by blast
      then obtain b where hb: "b \<in> product_basis top1_open_sets top1_open_sets"
          and hxb: "x \<in> b" and hbW: "b \<subseteq> W" by blast
      obtain U' V' where hUV: "b = U' \<times> V'" and hU': "U' \<in> top1_open_sets" and hV': "V' \<in> top1_open_sets"
        using hb unfolding product_basis_def by blast
      show ?thesis using that[of U' V'] hU' hV' hxb hbW hUV by blast
    qed
    have "open U" using hU unfolding top1_open_sets_def by blast
    moreover have "open V" using hV unfolding top1_open_sets_def by blast
    ultimately show "\<exists>A B. open A \<and> open B \<and> x \<in> A \<times> B \<and> A \<times> B \<subseteq> W"
      using hxUV hUVW by blast
  qed
  thus "W \<in> top1_open_sets" unfolding top1_open_sets_def by blast
next
  fix W :: "('a \<times> 'b) set"
  assume hW: "W \<in> top1_open_sets"
  hence "open W" unfolding top1_open_sets_def by blast
  have hTX: "is_topology_on (UNIV :: 'a set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
  have hTY: "is_topology_on (UNIV :: 'b set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
  have hUU: "(UNIV :: 'a set) \<times> (UNIV :: 'b set) = (UNIV :: ('a \<times> 'b) set)" by simp
  have hTP: "is_topology_on (UNIV :: ('a \<times> 'b) set) (product_topology_on top1_open_sets top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTX hTY] unfolding hUU .
  \<comment> \<open>W = \<Union>{A \<times> B | A B. open A \<and> open B \<and> A \<times> B \<subseteq> W}.\<close>
  let ?cover = "{R. \<exists>A B. R = A \<times> B \<and> open A \<and> open B \<and> R \<subseteq> W}"
  have hW_eq: "W = \<Union>?cover"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> W"
    then obtain A B where "open A" "open B" "x \<in> A \<times> B" "A \<times> B \<subseteq> W"
      using \<open>open W\<close> open_prod_elim by blast
    thus "x \<in> \<Union>?cover" by blast
  next
    fix x assume "x \<in> \<Union>?cover" thus "x \<in> W" by auto
  qed
  \<comment> \<open>Each A \<times> B \<in> ?cover is in product_topology_on.\<close>
  have "\<forall>R\<in>?cover. R \<in> product_topology_on top1_open_sets top1_open_sets"
  proof
    fix R assume "R \<in> ?cover"
    then obtain A B where "R = A \<times> B" "open A" "open B" by blast
    hence "A \<in> top1_open_sets" "B \<in> top1_open_sets" unfolding top1_open_sets_def by blast+
    thus "R \<in> product_topology_on top1_open_sets top1_open_sets"
      using \<open>R = A \<times> B\<close> product_rect_open by blast
  qed
  \<comment> \<open>Union of topology members is in the topology.\<close>
  hence "\<Union>?cover \<in> product_topology_on top1_open_sets top1_open_sets"
    using hTP unfolding is_topology_on_def by blast
  thus "W \<in> product_topology_on top1_open_sets top1_open_sets"
    using hW_eq by simp
qed

lemmas product_topology_on_open_sets_real2 =
  product_topology_on_open_sets[where ?'a = real and ?'b = real]

text \<open>Continuity transfer: continuous_on UNIV for R \<rightarrow> subspace of R².\<close>
lemma top1_continuous_map_on_R_to_R2_subspace:
  fixes T :: "(real \<times> real) set"
  assumes hmap: "\<And>x::real. f x \<in> T"
      and hcont: "continuous_on UNIV f"
  shows "top1_continuous_map_on (UNIV::real set) top1_open_sets T
           (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) f"
  unfolding top1_continuous_map_on_def
proof (intro conjI ballI)
  fix x :: real show "f x \<in> T" by (rule hmap)
next
  fix V assume hV: "V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T"
  obtain U where hU: "U \<in> product_topology_on top1_open_sets top1_open_sets" and hVeq: "V = T \<inter> U"
    using hV unfolding subspace_topology_def by (by100 blast)
  have hU_open: "open U"
  proof -
    have "U \<in> (top1_open_sets :: (real \<times> real) set set)"
      using hU product_topology_on_open_sets_real2 by metis
    thus ?thesis unfolding top1_open_sets_def by blast
  qed
  have hfU_open: "open (f -` U)" by (rule open_vimage[OF hU_open hcont])
  have "{x. f x \<in> V} = f -` U"
  proof (rule set_eqI)
    fix x show "(x \<in> {x. f x \<in> V}) = (x \<in> f -` U)"
      using hVeq hmap[of x] by (by100 blast)
  qed
  hence "open {x. f x \<in> V}" using hfU_open by simp
  hence "{x. f x \<in> V} \<in> top1_open_sets" unfolding top1_open_sets_def by simp
  thus "{x \<in> UNIV. f x \<in> V} \<in> top1_open_sets" by simp
qed

text \<open>Continuity transfer: continuous_on S on ℝ² implies top1_continuous_map_on
  on subspace topologies. Works for any S (not just UNIV).\<close>
lemma top1_continuous_map_on_real2_subspace_general:
  fixes S :: "(real \<times> real) set" and T :: "(real \<times> real) set"
  assumes hmap: "\<And>p. p \<in> S \<Longrightarrow> f p \<in> T"
      and hcont: "continuous_on S f"
  shows "top1_continuous_map_on S
           (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S)
           T (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) f"
  unfolding top1_continuous_map_on_def
proof (intro conjI ballI)
  fix p assume "p \<in> S" thus "f p \<in> T" by (rule hmap)
next
  fix V assume hV: "V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T"
  obtain U where hU: "U \<in> product_topology_on top1_open_sets top1_open_sets" and hVeq: "V = T \<inter> U"
    using hV unfolding subspace_topology_def by (by100 auto)
  have hU_open: "open U"
  proof -
    have "U \<in> (top1_open_sets :: (real \<times> real) set set)"
      using hU product_topology_on_open_sets_real2 by (by100 metis)
    thus ?thesis unfolding top1_open_sets_def by (by100 simp)
  qed
  \<comment> \<open>continuous_on S f + open U gives open W with f\<inverse>(U) \<inter> S = W \<inter> S.\<close>
  obtain W where hW_open: "open W" and hfW: "W \<inter> S = f -` U \<inter> S"
    using hcont hU_open unfolding continuous_on_open_invariant by blast
  have "{p \<in> S. f p \<in> V} = S \<inter> W"
  proof -
    have "{p \<in> S. f p \<in> V} = S \<inter> (f -` U \<inter> f -` T)" unfolding hVeq by (by100 auto)
    also have "\<dots> = S \<inter> (f -` U)" using hmap by (by100 auto)
    also have "\<dots> = W \<inter> S" using hfW by (by100 blast)
    also have "\<dots> = S \<inter> W" by (by100 blast)
    finally show ?thesis .
  qed
  moreover have "W \<in> product_topology_on top1_open_sets top1_open_sets"
  proof -
    have "W \<in> (top1_open_sets :: (real \<times> real) set set)"
      using hW_open unfolding top1_open_sets_def by (by100 blast)
    thus ?thesis using product_topology_on_open_sets_real2 by (by100 metis)
  qed
  ultimately show "{p \<in> S. f p \<in> V} \<in>
    subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
    unfolding subspace_topology_def by (by100 blast)
qed

text \<open>Continuity transfer: continuous_on UNIV on ℝ² implies top1_continuous_map_on
  on subspace topologies (special case of the general version).\<close>
lemma top1_continuous_map_on_real2_subspace:
  fixes S :: "(real \<times> real) set" and T :: "(real \<times> real) set"
  assumes hmap: "\<And>p. p \<in> S \<Longrightarrow> f p \<in> T"
      and hcont: "continuous_on UNIV f"
  shows "top1_continuous_map_on S
           (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S)
           T (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T) f"
  unfolding top1_continuous_map_on_def
proof (intro conjI ballI)
  fix p assume "p \<in> S" thus "f p \<in> T" by (rule hmap)
next
  fix V assume hV: "V \<in> subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T"
  obtain U where hU: "U \<in> product_topology_on top1_open_sets top1_open_sets" and hVeq: "V = T \<inter> U"
    using hV unfolding subspace_topology_def by blast
  have hU_open: "open U"
  proof -
    have "U \<in> (top1_open_sets :: (real \<times> real) set set)"
      using hU product_topology_on_open_sets_real2 by metis
    thus ?thesis unfolding top1_open_sets_def by blast
  qed
  have hfU_open: "open (f -` U)" by (rule open_vimage[OF hU_open hcont])
  have "{p \<in> S. f p \<in> V} = S \<inter> (f -` U \<inter> f -` T)"
    unfolding hVeq by auto
  also have "... = S \<inter> (f -` U)"
    using hmap by auto
  finally have "{p \<in> S. f p \<in> V} = S \<inter> (f -` U)" .
  moreover have "f -` U \<in> product_topology_on top1_open_sets top1_open_sets"
  proof -
    have "f -` U \<in> (top1_open_sets :: (real \<times> real) set set)"
      using hfU_open unfolding top1_open_sets_def by blast
    thus ?thesis using product_topology_on_open_sets_real2 by metis
  qed
  ultimately show "{p \<in> S. f p \<in> V} \<in>
    subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
    unfolding subspace_topology_def by blast
qed

text \<open>Transfer from continuous_on on I\<times>I to top1_continuous_map_on with II_topology.
  Uses openin + subspace topology equivalence.\<close>
lemma top1_continuous_map_on_II_to_I:
  assumes hmap: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> f p \<in> I_set"
      and hcont: "continuous_on (I_set \<times> I_set) f"
  shows "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top f"
proof -
  show ?thesis unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix p assume "p \<in> I_set \<times> I_set" thus "f p \<in> I_set" by (rule hmap)
  next
    fix V assume hV: "V \<in> I_top"
    \<comment> \<open>V = I \<inter> W for some open W.\<close>
    obtain W where hW: "open W" and hVW: "V = I_set \<inter> W"
      using hV unfolding top1_unit_interval_topology_def subspace_topology_def
                        top1_open_sets_def by auto
    \<comment> \<open>By continuous_on_open_invariant, there exists open U with U \<inter> (I\<times>I) = f^{-1}(W) \<inter> (I\<times>I).\<close>
    obtain U where hU: "open U" and hfW: "U \<inter> (I_set \<times> I_set) = f -` W \<inter> (I_set \<times> I_set)"
      using hcont hW unfolding continuous_on_open_invariant by blast
    \<comment> \<open>U is open in R^2, so U \<in> product_topology_on top1_open_sets top1_open_sets.\<close>
    have "U \<in> (top1_open_sets :: (real \<times> real) set set)"
      using hU unfolding top1_open_sets_def by blast
    hence "U \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
      using product_topology_on_open_sets_real2 by metis
    \<comment> \<open>(I\<times>I) \<inter> U \<in> II_topology (subspace of R^2 on I\<times>I).\<close>
    hence hU_II: "(I_set \<times> I_set) \<inter> U \<in> product_topology_on I_top I_top"
    proof -
      have "U \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
        using \<open>U \<in> top1_open_sets\<close> product_topology_on_open_sets_real2 by metis
      moreover have hIeq: "product_topology_on I_top I_top
        = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
      proof -
        have hTR: "is_topology_on (UNIV :: real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
        have "product_topology_on (subspace_topology UNIV top1_open_sets I_set)
                (subspace_topology UNIV top1_open_sets I_set)
              = subspace_topology (UNIV \<times> UNIV) (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
          by (rule Theorem_16_3[OF hTR hTR])
        moreover have "(UNIV :: real set) \<times> (UNIV :: real set) = (UNIV :: (real\<times>real) set)" by simp
        moreover have "I_top = subspace_topology UNIV top1_open_sets I_set"
          unfolding top1_unit_interval_topology_def by rule
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis unfolding hIeq subspace_topology_def by blast
    qed
    have "{p \<in> I_set \<times> I_set. f p \<in> V} = (I_set \<times> I_set) \<inter> U"
    proof -
      have "{p \<in> I_set \<times> I_set. f p \<in> V} = {p \<in> I_set \<times> I_set. f p \<in> I_set \<and> f p \<in> W}"
        unfolding hVW by auto
      also have "... = f -` W \<inter> (I_set \<times> I_set)" using hmap by auto
      also have "... = U \<inter> (I_set \<times> I_set)" using hfW by simp
      also have "... = (I_set \<times> I_set) \<inter> U" by (rule Int_commute)
      finally show ?thesis .
    qed
    thus "{p \<in> I_set \<times> I_set. f p \<in> V} \<in> product_topology_on I_top I_top" using hU_II by simp
  qed
qed

text \<open>II_topology equals the subspace of R^2 on I × I.\<close>
lemma II_topology_eq_subspace:
  "product_topology_on I_top I_top =
   subspace_topology (UNIV :: (real \<times> real) set)
     (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
proof -
  have hTR: "is_topology_on (UNIV :: real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have "product_topology_on
          (subspace_topology UNIV top1_open_sets I_set)
          (subspace_topology UNIV top1_open_sets I_set)
        = subspace_topology (UNIV \<times> UNIV) (product_topology_on top1_open_sets top1_open_sets)
            (I_set \<times> I_set)"
    by (rule Theorem_16_3[OF hTR hTR])
  moreover have "(UNIV :: real set) \<times> (UNIV :: real set) = (UNIV :: (real \<times> real) set)" by simp
  moreover have "I_top = subspace_topology UNIV top1_open_sets I_set"
    unfolding top1_unit_interval_topology_def by rule
  ultimately show ?thesis by simp
qed

text \<open>The product space I \<times> I with the product topology.\<close>
definition II_topology :: "(real \<times> real) set set" where
  "II_topology = product_topology_on I_top I_top"

text \<open>Homotopy between continuous maps X \<rightarrow> Y: a continuous F: X \<times> I \<rightarrow> Y
  with F(x,0) = f(x) and F(x,1) = f'(x).\<close>
definition top1_homotopic_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_homotopic_on X TX Y TY f f' \<longleftrightarrow>
     top1_continuous_map_on X TX Y TY f \<and>
     top1_continuous_map_on X TX Y TY f' \<and>
     (\<exists>F. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F
          \<and> (\<forall>x\<in>X. F (x, 0) = f x) \<and> (\<forall>x\<in>X. F (x, 1) = f' x))"

text \<open>Path homotopy: a stronger relation between paths with fixed endpoints.
  F: I \<times> I \<rightarrow> X continuous with F(s,0) = f(s), F(s,1) = f'(s),
  F(0,t) = x0, F(1,t) = x1.\<close>
definition top1_path_homotopic_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a
  \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_path_homotopic_on X TX x0 x1 f f' \<longleftrightarrow>
     top1_is_path_on X TX x0 x1 f \<and>
     top1_is_path_on X TX x0 x1 f' \<and>
     (\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F
          \<and> (\<forall>s\<in>I_set. F (s, 0) = f s) \<and> (\<forall>s\<in>I_set. F (s, 1) = f' s)
          \<and> (\<forall>t\<in>I_set. F (0, t) = x0) \<and> (\<forall>t\<in>I_set. F (1, t) = x1))"

text \<open>Nulhomotopic: homotopic to a constant map.\<close>
definition top1_nulhomotopic_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_nulhomotopic_on X TX Y TY f \<longleftrightarrow>
     (\<exists>c\<in>Y. top1_homotopic_on X TX Y TY f (\<lambda>_. c))"

text \<open>Helper: f \<circ> pi_1 is continuous from X \<times> I \<rightarrow> Y when f: X \<rightarrow> Y is continuous.\<close>
lemma homotopy_const_continuous:
  assumes hf: "top1_continuous_map_on X TX Y TY f"
  and hTX: "is_topology_on X TX"
  shows "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
    (\<lambda>p. f (fst p))"
proof -
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
    by (rule product_topology_on_is_topology_on[OF hTX hTI])
  have hid: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
    (X \<times> I_set) (product_topology_on TX I_top) id"
    by (rule top1_continuous_map_on_id[OF hTP])
  have hpi1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX (pi1 \<circ> id)"
    using iffD1[OF Theorem_18_4[OF hTP hTX hTI] hid] by blast
  have hpi1': "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX pi1"
    using hpi1 by (simp add: comp_def)
  have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY (f \<circ> pi1)"
    by (rule top1_continuous_map_on_comp[OF hpi1' hf])
  thus ?thesis by (simp add: comp_def pi1_def)
qed

(** from \<S>51 Lemma 51.1: \<simeq> and \<simeq>_p are equivalence relations **)
lemma Lemma_51_1_homotopic_refl:
  assumes hf: "top1_continuous_map_on X TX Y TY f" and hTX: "is_topology_on X TX"
  shows "top1_homotopic_on X TX Y TY f f"
proof -
  have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
    (\<lambda>p. f (fst p))"
    by (rule homotopy_const_continuous[OF hf hTX])
  moreover have "\<forall>x\<in>X. f (fst (x, 0)) = f x" by simp
  moreover have "\<forall>x\<in>X. f (fst (x, 1)) = f x" by simp
  ultimately show ?thesis
    unfolding top1_homotopic_on_def using hf by blast
qed

text \<open>The function t \<mapsto> 1-t is continuous I \<rightarrow> I.\<close>
lemma op_minus_continuous_on_interval:
  "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
proof -
  have hmap: "\<And>x. x \<in> I_set \<Longrightarrow> 1 - x \<in> I_set"
    unfolding top1_unit_interval_def by simp
  have hcont: "continuous_on UNIV (\<lambda>t::real. 1 - t)"
    by (rule continuous_on_op_minus)
  show ?thesis
    unfolding top1_unit_interval_topology_def
    by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap hcont])
qed

text \<open>Helper: (x,t) \<mapsto> (x, 1-t) is continuous X\<times>I \<rightarrow> X\<times>I.
  Uses Theorem 18.4: map into product is continuous iff components are.\<close>
lemma flip_t_continuous_product:
  assumes hTX: "is_topology_on X TX"
  shows "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
    (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, 1 - snd p))"
proof -
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
    by (rule product_topology_on_is_topology_on[OF hTX hTI])
  let ?g = "\<lambda>p::'a \<times> real. (fst p, 1 - snd p)"
  have hid: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
    (X \<times> I_set) (product_topology_on TX I_top) id"
    by (rule top1_continuous_map_on_id[OF hTP])
  have hpi12: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX (pi1 \<circ> id)
            \<and> top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top (pi2 \<circ> id)"
    using iffD1[OF Theorem_18_4[OF hTP hTX hTI] hid] by blast
  have hpi1_eq: "(pi1 :: 'a \<times> real \<Rightarrow> 'a) = fst" unfolding pi1_def by (rule ext) simp
  have hpi2_eq: "(pi2 :: 'a \<times> real \<Rightarrow> real) = snd" unfolding pi2_def by (rule ext) simp
  have hpi1fst: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX fst"
    using hpi12 unfolding hpi1_eq by (simp add: comp_def)
  have hpi2snd: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top snd"
    using hpi12 unfolding hpi2_eq by (simp add: comp_def)
  have hc1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX (pi1 \<circ> ?g)"
  proof -
    have "pi1 \<circ> ?g = fst" unfolding hpi1_eq by auto
    thus ?thesis using hpi1fst by simp
  qed
  have hrev_snd: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top (\<lambda>p. 1 - snd p)"
  proof -
    have hrev: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
      by (rule op_minus_continuous_on_interval)
    have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top
      ((\<lambda>t. 1 - t) \<circ> snd)"
      by (rule top1_continuous_map_on_comp[OF hpi2snd hrev])
    thus ?thesis by (simp add: comp_def)
  qed
  have hc2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top (pi2 \<circ> ?g)"
  proof -
    have "pi2 \<circ> ?g = (\<lambda>p. 1 - snd p)" unfolding hpi2_eq by auto
    thus ?thesis using hrev_snd by simp
  qed
  show ?thesis
    using iffD2[OF Theorem_18_4[OF hTP hTX hTI]] hc1 hc2 by blast
qed

lemma homotopy_reverse_continuous:
  assumes hF: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F"
    and hTX: "is_topology_on X TX"
  shows "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
    (\<lambda>p. F (fst p, 1 - snd p))"
proof -
  have hflip: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
    (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, 1 - snd p))"
    by (rule flip_t_continuous_product[OF hTX])
  have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
    (F \<circ> (\<lambda>p. (fst p, 1 - snd p)))"
    by (rule top1_continuous_map_on_comp[OF hflip hF])
  thus ?thesis by (simp add: comp_def)
qed

lemma Lemma_51_1_homotopic_sym:
  assumes h: "top1_homotopic_on X TX Y TY f f'" and hTX: "is_topology_on X TX"
  shows "top1_homotopic_on X TX Y TY f' f"
proof -
  obtain F where hF: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F"
    and hF0: "\<forall>x\<in>X. F (x, 0) = f x" and hF1: "\<forall>x\<in>X. F (x, 1) = f' x"
    using h unfolding top1_homotopic_on_def by blast
  let ?G = "\<lambda>p. F (fst p, 1 - snd p)"
  have hG: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY ?G"
    by (rule homotopy_reverse_continuous[OF hF hTX])
  have hG0: "\<forall>x\<in>X. ?G (x, 0) = f' x" using hF1 by simp
  have hG1: "\<forall>x\<in>X. ?G (x, 1) = f x" using hF0 by simp
  show ?thesis
    unfolding top1_homotopic_on_def
    using h hG hG0 hG1 unfolding top1_homotopic_on_def by blast
qed

text \<open>If two functions agree on S, and one is continuous on S, so is the other.\<close>
lemma top1_continuous_map_on_agree':
  assumes "top1_continuous_map_on S TS Y TY f" and "\<forall>x\<in>S. f x = g x"
  shows "top1_continuous_map_on S TS Y TY g"
proof -
  have "\<forall>x\<in>S. g x \<in> Y" using assms unfolding top1_continuous_map_on_def by auto
  moreover have "\<forall>V\<in>TY. {x \<in> S. g x \<in> V} \<in> TS"
  proof (intro ballI)
    fix V assume "V \<in> TY"
    have "{x \<in> S. g x \<in> V} = {x \<in> S. f x \<in> V}" using assms(2) by auto
    thus "{x \<in> S. g x \<in> V} \<in> TS" using assms(1) \<open>V \<in> TY\<close> unfolding top1_continuous_map_on_def by simp
  qed
  ultimately show ?thesis unfolding top1_continuous_map_on_def by blast
qed

text \<open>Helper: concatenation of homotopies via pasting lemma.
  Given F: X\<times>I \<rightarrow> Y and F': X\<times>I \<rightarrow> Y with F(x,1) = F'(x,0), define
  G(x,t) = F(x,2t) for t\<le>1/2, G(x,t) = F'(x,2t-1) for t\<ge>1/2.\<close>
lemma homotopy_concat_continuous:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hF: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F"
      and hF': "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F'"
      and hmatch: "\<forall>x\<in>X. F (x, 1) = F' (x, 0)"
  shows "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
    (\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1))"
proof -
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have hTXI: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
    by (rule product_topology_on_is_topology_on[OF hTX hTI])
  let ?A = "X \<times> {t\<in>I_set. t \<le> 1/2}"
  let ?B = "X \<times> {t\<in>I_set. t \<ge> 1/2}"
  have hX_open: "X \<in> TX" using hTX unfolding is_topology_on_def by blast
  have hA_closed: "closedin_on (X \<times> I_set) (product_topology_on TX I_top) ?A"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?A \<subseteq> X \<times> I_set" by auto
    have "X \<times> I_set - ?A = X \<times> {t\<in>I_set. t > 1/2}" unfolding top1_unit_interval_def by auto
    also have "\<dots> \<in> product_topology_on TX I_top"
    proof -
      have "open {t :: real. t > 1/2}" by (rule open_Collect_less[OF continuous_on_const continuous_on_id])
      hence "{t :: real. t > 1/2} \<in> top1_open_sets" unfolding top1_open_sets_def by blast
      hence "I_set \<inter> {t. t > 1/2} \<in> I_top"
        unfolding top1_unit_interval_topology_def subspace_topology_def by blast
      moreover have "{t\<in>I_set. t > 1/2} = I_set \<inter> {t. t > 1/2}" by auto
      ultimately have "{t\<in>I_set. t > 1/2} \<in> I_top" by simp
      thus ?thesis by (rule product_rect_open[OF hX_open])
    qed
    finally show "X \<times> I_set - ?A \<in> product_topology_on TX I_top" .
  qed
  have hB_closed: "closedin_on (X \<times> I_set) (product_topology_on TX I_top) ?B"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?B \<subseteq> X \<times> I_set" by auto
    have "X \<times> I_set - ?B = X \<times> {t\<in>I_set. t < 1/2}" unfolding top1_unit_interval_def by auto
    also have "\<dots> \<in> product_topology_on TX I_top"
    proof -
      have "open {t :: real. t < 1/2}" by (rule open_Collect_less[OF continuous_on_id continuous_on_const])
      hence "{t :: real. t < 1/2} \<in> top1_open_sets" unfolding top1_open_sets_def by blast
      hence "I_set \<inter> {t. t < 1/2} \<in> I_top"
        unfolding top1_unit_interval_topology_def subspace_topology_def by blast
      moreover have "{t\<in>I_set. t < 1/2} = I_set \<inter> {t. t < 1/2}" by auto
      ultimately have "{t\<in>I_set. t < 1/2} \<in> I_top" by simp
      thus ?thesis by (rule product_rect_open[OF hX_open])
    qed
    finally show "X \<times> I_set - ?B \<in> product_topology_on TX I_top" .
  qed
  have hcover: "?A \<union> ?B = X \<times> I_set" unfolding top1_unit_interval_def by auto
  let ?G = "\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1)"
  have hF_range: "\<forall>p\<in>X \<times> I_set. F p \<in> Y" using hF unfolding top1_continuous_map_on_def by blast
  have hF'_range: "\<forall>p\<in>X \<times> I_set. F' p \<in> Y" using hF' unfolding top1_continuous_map_on_def by blast
  have hG_range: "\<forall>p\<in>X \<times> I_set. ?G p \<in> Y"
  proof
    fix p assume hp: "p \<in> X \<times> I_set"
    show "?G p \<in> Y"
    proof (cases "snd p \<le> 1/2")
      case True
      have "(fst p, 2 * snd p) \<in> X \<times> I_set" using hp True unfolding top1_unit_interval_def by auto
      thus ?thesis using True hF_range by simp
    next
      case False
      have "(fst p, 2 * snd p - 1) \<in> X \<times> I_set" using hp False unfolding top1_unit_interval_def by auto
      thus ?thesis using False hF'_range by simp
    qed
  qed
  \<comment> \<open>Reparametrize only 2nd component: (id_X, \<phi>) continuous from subspace to product.\<close>
  have reparam_full: "\<And>\<phi>. top1_continuous_map_on I_set I_top I_set I_top \<phi> \<Longrightarrow>
    top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
      (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, \<phi> (snd p)))"
  proof -
    fix \<phi> assume h\<phi>: "top1_continuous_map_on I_set I_top I_set I_top \<phi>"
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTP: "is_topology_on (X \<times> I_set) (product_topology_on TX I_top)"
      by (rule product_topology_on_is_topology_on[OF hTX hTI])
    have hpi1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX pi1"
      by (rule top1_continuous_pi1[OF hTX hTI])
    have hpi2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top pi2"
      by (rule top1_continuous_pi2[OF hTX hTI])
    have hphi_pi2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top (\<phi> \<circ> pi2)"
      by (rule top1_continuous_map_on_comp[OF hpi2 h\<phi>])
    have hp1_eq: "pi1 \<circ> (\<lambda>p. (fst p, \<phi> (snd p))) = pi1"
      unfolding pi1_def by (rule ext) auto
    have hp2_eq: "pi2 \<circ> (\<lambda>p. (fst p, \<phi> (snd p))) = \<phi> \<circ> pi2"
      unfolding pi2_def comp_def by (rule ext) auto
    have hp1_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX
        (pi1 \<circ> (\<lambda>p. (fst p, \<phi> (snd p))))"
      unfolding hp1_eq by (rule hpi1)
    have hp2_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) I_set I_top
        (pi2 \<circ> (\<lambda>p. (fst p, \<phi> (snd p))))"
      unfolding hp2_eq by (rule hphi_pi2)
    show "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top)
      (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, \<phi> (snd p)))"
      using iffD2[OF Theorem_18_4[OF hTP hTX hTI, of "\<lambda>p. (fst p, \<phi> (snd p))"]]
      hp1_cont hp2_cont by blast
  qed
  have reparam_snd: "\<And>S \<phi>. \<lbrakk>S \<subseteq> I_set;
    top1_continuous_map_on I_set I_top I_set I_top \<phi>\<rbrakk> \<Longrightarrow>
    top1_continuous_map_on (X \<times> S) (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) (X \<times> S))
      (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, \<phi> (snd p)))"
    by (intro top1_continuous_map_on_restrict_domain_simple[OF reparam_full]) auto \<comment> \<open>Preimage of U1\<times>U2: (X\<times>S) \<inter> (U1 \<times> \<phi>⁻¹(U2)), where \<phi>⁻¹(U2) = S \<inter> V for V \<in> I_top.
           So preimage = (X\<times>S) \<inter> (U1 \<times> V) \<in> sub (X\<times>I) (product TX I_top) (X\<times>S).\<close>
  \<comment> \<open>Clamped scaling maps I \<rightarrow> I.\<close>
  have hscale2c: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. min 1 (2*t))"
  proof -
    have hmap: "\<And>t. t \<in> I_set \<Longrightarrow> min 1 (2*t) \<in> I_set" unfolding top1_unit_interval_def by auto
    have hcont: "continuous_on UNIV (\<lambda>t::real. min 1 (2*t))" by (intro continuous_intros)
    have "top1_continuous_map_on I_set (subspace_topology UNIV top1_open_sets I_set)
            I_set (subspace_topology UNIV top1_open_sets I_set) (\<lambda>t. min 1 (2*t))"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap hcont])
    thus ?thesis unfolding top1_unit_interval_topology_def .
  qed
  have hscale2m1c: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. max 0 (2*t - 1))"
  proof -
    have hmap: "\<And>t. t \<in> I_set \<Longrightarrow> max 0 (2*t - 1) \<in> I_set" unfolding top1_unit_interval_def by auto
    have hcont: "continuous_on UNIV (\<lambda>t::real. max 0 (2*t - 1))" by (intro continuous_intros)
    have "top1_continuous_map_on I_set (subspace_topology UNIV top1_open_sets I_set)
            I_set (subspace_topology UNIV top1_open_sets I_set) (\<lambda>t. max 0 (2*t - 1))"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap hcont])
    thus ?thesis unfolding top1_unit_interval_topology_def .
  qed
  have hscale2: "top1_continuous_map_on {t\<in>I_set. t \<le> 1/2}
    (subspace_topology I_set I_top {t\<in>I_set. t \<le> 1/2}) I_set I_top (\<lambda>t. 2*t)"
  proof -
    have hmap: "\<And>t. t \<in> {t\<in>I_set. t \<le> 1/2} \<Longrightarrow> 2*t \<in> I_set" unfolding top1_unit_interval_def by auto
    have hcont: "continuous_on UNIV ((*) (2::real))" by (intro continuous_intros)
    have hraw: "top1_continuous_map_on {t\<in>I_set. t \<le> 1/2}
      (subspace_topology UNIV top1_open_sets {t\<in>I_set. t \<le> 1/2})
      I_set (subspace_topology UNIV top1_open_sets I_set) ((*) 2)"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap hcont])
    have hdom: "subspace_topology I_set I_top {t\<in>I_set. t \<le> 1/2}
              = subspace_topology UNIV top1_open_sets {t\<in>I_set. t \<le> 1/2}"
      unfolding top1_unit_interval_topology_def by (rule subspace_topology_trans) auto
    have hcod: "I_top = subspace_topology UNIV top1_open_sets I_set"
      unfolding top1_unit_interval_topology_def by rule
    have "top1_continuous_map_on {t\<in>I_set. t \<le> 1/2}
      (subspace_topology I_set I_top {t\<in>I_set. t \<le> 1/2}) I_set I_top ((*) 2)"
      using hraw hdom hcod by simp
    moreover have "((*) (2::real)) = (\<lambda>t. 2*t)" by (rule ext) simp
    ultimately show ?thesis by simp
  qed
  have hscale2m1: "top1_continuous_map_on {t\<in>I_set. t \<ge> 1/2}
    (subspace_topology I_set I_top {t\<in>I_set. t \<ge> 1/2}) I_set I_top (\<lambda>t. 2*t - 1)"
  proof -
    have hmap: "\<And>t. t \<in> {t\<in>I_set. t \<ge> 1/2} \<Longrightarrow> 2*t - 1 \<in> I_set" unfolding top1_unit_interval_def by auto
    have hcont: "continuous_on UNIV (\<lambda>t::real. 2*t - 1)" by (intro continuous_intros)
    have hraw: "top1_continuous_map_on {t\<in>I_set. t \<ge> 1/2}
      (subspace_topology UNIV top1_open_sets {t\<in>I_set. t \<ge> 1/2})
      I_set (subspace_topology UNIV top1_open_sets I_set) (\<lambda>t. 2*t - 1)"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap hcont])
    have hdom: "subspace_topology I_set I_top {t\<in>I_set. t \<ge> 1/2}
              = subspace_topology UNIV top1_open_sets {t\<in>I_set. t \<ge> 1/2}"
      unfolding top1_unit_interval_topology_def by (rule subspace_topology_trans) auto
    have hcod: "I_top = subspace_topology UNIV top1_open_sets I_set"
      unfolding top1_unit_interval_topology_def by rule
    show ?thesis using hraw hdom hcod by simp
  qed
  have hFA: "top1_continuous_map_on ?A (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?A)
    Y TY (\<lambda>p. F (fst p, 2 * snd p))"
  proof -
    have "top1_continuous_map_on ?A (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?A)
      (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, min 1 (2 * snd p)))"
      by (rule reparam_snd[OF _ hscale2c]) auto
    hence hFA_c: "top1_continuous_map_on ?A (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?A)
      Y TY (\<lambda>p. F (fst p, min 1 (2 * snd p)))"
      using top1_continuous_map_on_comp[of ?A _ _ _ "(\<lambda>p. (fst p, min 1 (2 * snd p)))" _ _ F] hF
      by (simp add: comp_def)
    show ?thesis by (rule top1_continuous_map_on_agree'[OF hFA_c])
      (auto simp: top1_unit_interval_def)
  qed
  have hGA: "top1_continuous_map_on ?A (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?A) Y TY ?G"
    by (rule top1_continuous_map_on_agree'[OF hFA]) auto
  have hFB: "top1_continuous_map_on ?B (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?B)
    Y TY (\<lambda>p. F' (fst p, 2 * snd p - 1))"
  proof -
    have "top1_continuous_map_on ?B (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?B)
      (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>p. (fst p, max 0 (2 * snd p - 1)))"
      by (rule reparam_snd[OF _ hscale2m1c]) auto
    hence hFB_c: "top1_continuous_map_on ?B (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?B)
      Y TY (\<lambda>p. F' (fst p, max 0 (2 * snd p - 1)))"
      using top1_continuous_map_on_comp[of ?B _ _ _ "(\<lambda>p. (fst p, max 0 (2 * snd p - 1)))" _ _ F'] hF'
      by (simp add: comp_def)
    show ?thesis by (rule top1_continuous_map_on_agree'[OF hFB_c])
      (auto simp: top1_unit_interval_def)
  qed
  have hGB: "top1_continuous_map_on ?B (subspace_topology (X \<times> I_set) (product_topology_on TX I_top) ?B) Y TY ?G"
  proof (rule top1_continuous_map_on_agree'[OF hFB])
    show "\<forall>p\<in>?B. F' (fst p, 2 * snd p - 1) = ?G p"
    proof
      fix p assume hp: "p \<in> ?B"
      show "F' (fst p, 2 * snd p - 1) = ?G p"
      proof (cases "snd p > 1/2")
        case True thus ?thesis by simp
      next
        case False hence "snd p = 1/2" using hp by auto
        hence "2 * snd p = 1" "2 * snd p - 1 = 0" by simp_all
        thus ?thesis using hmatch hp by auto
      qed
    qed
  qed
  show ?thesis
    by (rule pasting_lemma_two_closed[OF hTXI hTY hA_closed hB_closed hcover hG_range hGA hGB])
qed

lemma Lemma_51_1_homotopic_trans:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and h1: "top1_homotopic_on X TX Y TY f f'"
      and h2: "top1_homotopic_on X TX Y TY f' f''"
  shows "top1_homotopic_on X TX Y TY f f''"
proof -
  obtain F where hF: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F"
    and hF0: "\<forall>x\<in>X. F (x, 0) = f x" and hF1: "\<forall>x\<in>X. F (x, 1) = f' x"
    using h1 unfolding top1_homotopic_on_def by blast
  obtain F' where hF': "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F'"
    and hF'0: "\<forall>x\<in>X. F' (x, 0) = f' x" and hF'1: "\<forall>x\<in>X. F' (x, 1) = f'' x"
    using h2 unfolding top1_homotopic_on_def by blast
  have hmatch: "\<forall>x\<in>X. F (x, 1) = F' (x, 0)" using hF1 hF'0 by simp
  let ?G = "\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1)"
  have hG: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY ?G"
    by (rule homotopy_concat_continuous[OF hTX hTY hF hF' hmatch])
  have hG0: "\<forall>x\<in>X. ?G (x, 0) = f x" using hF0 by simp
  have hG1: "\<forall>x\<in>X. ?G (x, 1) = f'' x" using hF'1 by simp
  show ?thesis
    unfolding top1_homotopic_on_def
    using h1 h2 hG hG0 hG1 unfolding top1_homotopic_on_def by blast
qed

text \<open>Helper: f \<circ> pi_1 continuous from I \<times> I \<rightarrow> X when f: I \<rightarrow> X is continuous.\<close>
lemma path_homotopy_const_continuous:
  assumes hf: "top1_continuous_map_on I_set I_top X TX f"
  shows "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (\<lambda>p. f (fst p))"
proof -
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTP: "is_topology_on (I_set \<times> I_set) II_topology"
    unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  have hid: "top1_continuous_map_on (I_set \<times> I_set) II_topology
    (I_set \<times> I_set) II_topology id"
    by (rule top1_continuous_map_on_id[OF hTP])
  have hpi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top (pi1 \<circ> id)"
    unfolding II_topology_def
    using iffD1[OF Theorem_18_4[OF hTP[unfolded II_topology_def] hTI hTI] hid[unfolded II_topology_def]]
    by blast
  have hpi1': "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi1"
    using hpi1 by (simp add: comp_def)
  have "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (f \<circ> pi1)"
    by (rule top1_continuous_map_on_comp[OF hpi1' hf])
  thus ?thesis by (simp add: comp_def pi1_def)
qed

lemma Lemma_51_1_path_homotopic_refl:
  assumes hf: "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x1 f f"
proof -
  have hfc: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_path_on_def by blast
  have "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (\<lambda>p. f (fst p))"
    by (rule path_homotopy_const_continuous[OF hfc])
  moreover have "\<forall>s\<in>I_set. f (fst (s, 0)) = f s" by simp
  moreover have "\<forall>s\<in>I_set. f (fst (s, 1)) = f s" by simp
  moreover have "\<forall>t\<in>I_set. f (fst (0, t)) = x0"
    using hf unfolding top1_is_path_on_def by simp
  moreover have "\<forall>t\<in>I_set. f (fst (1, t)) = x1"
    using hf unfolding top1_is_path_on_def by simp
  ultimately show ?thesis
    unfolding top1_path_homotopic_on_def using hf by blast
qed

text \<open>Helper: if F: I\<times>I\<rightarrow>X is continuous, so is G(s,t) = F(s, 1-t).\<close>
lemma path_homotopy_reverse_continuous:
  assumes hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
  shows "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX
    (\<lambda>p. F (fst p, 1 - snd p))"
proof -
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hflip: "top1_continuous_map_on (I_set \<times> I_set) II_topology
    (I_set \<times> I_set) II_topology (\<lambda>p. (fst p, 1 - snd p))"
    unfolding II_topology_def
    by (rule flip_t_continuous_product[OF hTI])
  have "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX
    (F \<circ> (\<lambda>p. (fst p, 1 - snd p)))"
    by (rule top1_continuous_map_on_comp[OF hflip hF])
  thus ?thesis by (simp add: comp_def)
qed

lemma Lemma_51_1_path_homotopic_sym:
  assumes h: "top1_path_homotopic_on X TX x0 x1 f f'"
  shows "top1_path_homotopic_on X TX x0 x1 f' f"
proof -
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
    and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = f' s"
    and hFleft: "\<forall>t\<in>I_set. F (0, t) = x0" and hFright: "\<forall>t\<in>I_set. F (1, t) = x1"
    using h unfolding top1_path_homotopic_on_def by blast
  let ?G = "\<lambda>p. F (fst p, 1 - snd p)"
  have hG: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?G"
    by (rule path_homotopy_reverse_continuous[OF hF])
  have hG0: "\<forall>s\<in>I_set. ?G (s, 0) = f' s" using hF1 by simp
  have hG1: "\<forall>s\<in>I_set. ?G (s, 1) = f s" using hF0 by simp
  have hGleft: "\<forall>t\<in>I_set. ?G (0, t) = x0"
    using hFleft unfolding top1_unit_interval_def by simp
  have hGright: "\<forall>t\<in>I_set. ?G (1, t) = x1"
    using hFright unfolding top1_unit_interval_def by simp
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using h hG hG0 hG1 hGleft hGright unfolding top1_path_homotopic_on_def by blast
qed

text \<open>Helper: concatenation of path homotopies.

  Proof via pasting lemma (Theorem 18.3):
  A = I \<times> [0, 1/2] and B = I \<times> [1/2, 1] are closed in I \<times> I;
  F(fst p, 2\<cdot>snd p) is continuous on A; F'(fst p, 2\<cdot>snd p - 1) is
  continuous on B; they agree on A \<inter> B (where snd p = 1/2) by hmatch.\<close>

lemma top1_continuous_map_on_codomain_shrink:
  assumes hcont: "top1_continuous_map_on X TX Y TY f"
      and himg: "f ` X \<subseteq> W" and hWY: "W \<subseteq> Y"
  shows "top1_continuous_map_on X TX W (subspace_topology Y TY W) f"
  unfolding top1_continuous_map_on_def
proof (intro conjI)
  show "\<forall>x\<in>X. f x \<in> W" using himg by blast
next
  show "\<forall>V\<in>subspace_topology Y TY W. {x \<in> X. f x \<in> V} \<in> TX"
  proof
    fix V assume "V \<in> subspace_topology Y TY W"
    then obtain U where hU: "U \<in> TY" and hVeq: "V = W \<inter> U"
      unfolding subspace_topology_def by blast
    have "{x \<in> X. f x \<in> V} = {x \<in> X. f x \<in> U}"
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> {x \<in> X. f x \<in> V}" thus "x \<in> {x \<in> X. f x \<in> U}" using hVeq by blast
    next
      fix x assume hx: "x \<in> {x \<in> X. f x \<in> U}"
      hence "f x \<in> W" using himg by blast
      thus "x \<in> {x \<in> X. f x \<in> V}" using hx hVeq by blast
    qed
    also have "\<dots> \<in> TX" using hcont hU unfolding top1_continuous_map_on_def by blast
    finally show "{x \<in> X. f x \<in> V} \<in> TX" .
  qed
qed

lemma path_homotopy_concat_continuous:
  assumes hTX: "is_topology_on X TX"
      and hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hF': "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F'"
      and hmatch: "\<forall>s\<in>I_set. F (s, 1) = F' (s, 0)"
  shows "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX
    (\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1))"
proof -
  \<comment> \<open>Close sets A = I \<times> [0, 1/2] and B = I \<times> [1/2, 1].\<close>
  let ?A = "I_set \<times> {t\<in>I_set. t \<le> 1/2}"
  let ?B = "I_set \<times> {t\<in>I_set. t \<ge> 1/2}"
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hI_open: "I_set \<in> I_top" using hTI unfolding is_topology_on_def by blast
  have hA_half_closed: "closedin_on I_set I_top {t\<in>I_set. t \<le> 1/2}"
    unfolding closedin_on_def
  proof (intro conjI)
    show "{t\<in>I_set. t \<le> 1/2} \<subseteq> I_set" by auto
    have "I_set - {t\<in>I_set. t \<le> 1/2} = I_set \<inter> {s :: real. s > 1/2}"
      unfolding top1_unit_interval_def by auto
    also have "\<dots> \<in> I_top"
      unfolding top1_unit_interval_topology_def subspace_topology_def
      using open_greaterThan[of "1/2::real"]
      unfolding top1_open_sets_def greaterThan_def by blast
    finally show "I_set - {t\<in>I_set. t \<le> 1/2} \<in> I_top" .
  qed
  have hB_half_closed: "closedin_on I_set I_top {t\<in>I_set. t \<ge> 1/2}"
    unfolding closedin_on_def
  proof (intro conjI)
    show "{t\<in>I_set. t \<ge> 1/2} \<subseteq> I_set" by auto
    have "I_set - {t\<in>I_set. t \<ge> 1/2} = I_set \<inter> {s :: real. s < 1/2}"
      unfolding top1_unit_interval_def by auto
    also have "\<dots> \<in> I_top"
      unfolding top1_unit_interval_topology_def subspace_topology_def
      using open_lessThan[of "1/2::real"]
      unfolding top1_open_sets_def lessThan_def by blast
    finally show "I_set - {t\<in>I_set. t \<ge> 1/2} \<in> I_top" .
  qed
  have hA_closed: "closedin_on (I_set \<times> I_set) II_topology ?A"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?A \<subseteq> I_set \<times> I_set" by auto
    have "I_set \<times> I_set - ?A = I_set \<times> {t\<in>I_set. t > 1/2}"
      unfolding top1_unit_interval_def by auto
    also have "\<dots> \<in> II_topology"
    proof -
      have "{t\<in>I_set. t > 1/2} = I_set - {t\<in>I_set. t \<le> 1/2}"
        unfolding top1_unit_interval_def by auto
      hence "{t\<in>I_set. t > 1/2} \<in> I_top"
        using hA_half_closed unfolding closedin_on_def by simp
      thus ?thesis
        unfolding II_topology_def by (rule product_rect_open[OF hI_open])
    qed
    finally show "I_set \<times> I_set - ?A \<in> II_topology" .
  qed
  have hB_closed: "closedin_on (I_set \<times> I_set) II_topology ?B"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?B \<subseteq> I_set \<times> I_set" by auto
    have "I_set \<times> I_set - ?B = I_set \<times> {t\<in>I_set. t < 1/2}"
      unfolding top1_unit_interval_def by auto
    also have "\<dots> \<in> II_topology"
    proof -
      have "{t\<in>I_set. t < 1/2} = I_set - {t\<in>I_set. t \<ge> 1/2}"
        unfolding top1_unit_interval_def by auto
      hence "{t\<in>I_set. t < 1/2} \<in> I_top"
        using hB_half_closed unfolding closedin_on_def by simp
      thus ?thesis
        unfolding II_topology_def by (rule product_rect_open[OF hI_open])
    qed
    finally show "I_set \<times> I_set - ?B \<in> II_topology" .
  qed
  have hcover: "I_set \<times> I_set = ?A \<union> ?B"
    unfolding top1_unit_interval_def by auto
  \<comment> \<open>On A, (s,t) \<mapsto> F(s, 2t) is continuous via composition with reparametrization.\<close>
  have h\<phi>A: "top1_continuous_map_on ?A (subspace_topology (I_set \<times> I_set) II_topology ?A)
               (I_set \<times> I_set) II_topology (\<lambda>p. (fst p, 2 * snd (p::real\<times>real)))"
  proof -
    let ?\<phi> = "\<lambda>p :: real \<times> real. (fst p, 2 * snd p)"
    have hcont: "continuous_on UNIV ?\<phi>" by (intro continuous_intros)
    have hmap: "\<And>p. p \<in> ?A \<Longrightarrow> ?\<phi> p \<in> I_set \<times> I_set"
      unfolding top1_unit_interval_def by auto
    have hraw: "top1_continuous_map_on ?A
                 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?A)
                 (I_set \<times> I_set)
                 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set))
                 ?\<phi>"
      by (rule top1_continuous_map_on_real2_subspace[OF hmap hcont])
    have hAsub: "?A \<subseteq> I_set \<times> I_set" by auto
    have hdom_eq: "subspace_topology (I_set \<times> I_set) II_topology ?A
                 = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?A"
    proof -
      have "subspace_topology (I_set \<times> I_set)
              (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set))
              ?A
            = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?A"
        by (rule subspace_topology_trans[OF hAsub])
      thus ?thesis unfolding II_topology_def II_topology_eq_subspace .
    qed
    have hcod_eq: "II_topology
                 = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
      unfolding II_topology_def by (rule II_topology_eq_subspace)
    show ?thesis using hraw hdom_eq hcod_eq by simp
  qed
  have hfA: "top1_continuous_map_on ?A (subspace_topology (I_set \<times> I_set) II_topology ?A)
                                   X TX (\<lambda>p. F (fst p, 2 * snd p))"
  proof -
    have hcomp: "top1_continuous_map_on ?A (subspace_topology (I_set \<times> I_set) II_topology ?A)
            X TX (F \<circ> (\<lambda>p. (fst p, 2 * snd p)))"
      by (rule top1_continuous_map_on_comp[OF h\<phi>A hF])
    moreover have "F \<circ> (\<lambda>p. (fst p, 2 * snd p)) = (\<lambda>p. F (fst p, 2 * snd p))"
      by (rule ext) simp
    ultimately show ?thesis by simp
  qed
  have h\<phi>B: "top1_continuous_map_on ?B (subspace_topology (I_set \<times> I_set) II_topology ?B)
               (I_set \<times> I_set) II_topology (\<lambda>p. (fst p, 2 * snd (p::real\<times>real) - 1))"
  proof -
    let ?\<psi> = "\<lambda>p :: real \<times> real. (fst p, 2 * snd p - 1)"
    have hcont: "continuous_on UNIV ?\<psi>" by (intro continuous_intros)
    have hmap: "\<And>p. p \<in> ?B \<Longrightarrow> ?\<psi> p \<in> I_set \<times> I_set"
      unfolding top1_unit_interval_def by auto
    have hraw: "top1_continuous_map_on ?B
                 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?B)
                 (I_set \<times> I_set)
                 (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set))
                 ?\<psi>"
      by (rule top1_continuous_map_on_real2_subspace[OF hmap hcont])
    have hBsub: "?B \<subseteq> I_set \<times> I_set" by auto
    have hdom_eq: "subspace_topology (I_set \<times> I_set) II_topology ?B
                 = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?B"
    proof -
      have "subspace_topology (I_set \<times> I_set)
              (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set))
              ?B
            = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?B"
        by (rule subspace_topology_trans[OF hBsub])
      thus ?thesis unfolding II_topology_def II_topology_eq_subspace .
    qed
    have hcod_eq: "II_topology
                 = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
      unfolding II_topology_def by (rule II_topology_eq_subspace)
    show ?thesis using hraw hdom_eq hcod_eq by simp
  qed
  have hfB: "top1_continuous_map_on ?B (subspace_topology (I_set \<times> I_set) II_topology ?B)
                                   X TX (\<lambda>p. F' (fst p, 2 * snd p - 1))"
  proof -
    have hcomp: "top1_continuous_map_on ?B (subspace_topology (I_set \<times> I_set) II_topology ?B)
            X TX (F' \<circ> (\<lambda>p. (fst p, 2 * snd p - 1)))"
      by (rule top1_continuous_map_on_comp[OF h\<phi>B hF'])
    moreover have "F' \<circ> (\<lambda>p. (fst p, 2 * snd p - 1)) = (\<lambda>p. F' (fst p, 2 * snd p - 1))"
      by (rule ext) simp
    ultimately show ?thesis by simp
  qed
  \<comment> \<open>Agreement on A \<inter> B (where snd p = 1/2).\<close>
  have hagree: "\<forall>p\<in>?A \<inter> ?B. F (fst p, 2 * snd p) = F' (fst p, 2 * snd p - 1)"
  proof (intro ballI)
    fix p assume hp: "p \<in> ?A \<inter> ?B"
    have ht_half: "snd p = 1/2" using hp by force
    have hs: "fst p \<in> I_set" using hp by force
    have h2t: "2 * snd p = 1" using ht_half by simp
    have h2tm1: "2 * snd p - 1 = 0" using ht_half by simp
    show "F (fst p, 2 * snd p) = F' (fst p, 2 * snd p - 1)"
      using h2t h2tm1 hmatch[rule_format, OF hs] by simp
  qed
  \<comment> \<open>Apply pasting lemma.\<close>
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
    unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  let ?G = "\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1)"
  have hF_range: "\<forall>p\<in>I_set \<times> I_set. F p \<in> X"
    using hF unfolding top1_continuous_map_on_def by blast
  have hF'_range: "\<forall>p\<in>I_set \<times> I_set. F' p \<in> X"
    using hF' unfolding top1_continuous_map_on_def by blast
  have hG_range: "\<forall>p\<in>I_set \<times> I_set. ?G p \<in> X"
  proof (intro ballI)
    fix p assume hp: "p \<in> I_set \<times> I_set"
    show "?G p \<in> X"
    proof (cases "snd p \<le> 1/2")
      case True
      have hmem: "(fst p, 2 * snd p) \<in> I_set \<times> I_set"
        using hp True unfolding top1_unit_interval_def by auto
      have "?G p = F (fst p, 2 * snd p)" using True by simp
      moreover have "F (fst p, 2 * snd p) \<in> X" by (rule bspec[OF hF_range hmem])
      ultimately show ?thesis by simp
    next
      case False
      have hmem: "(fst p, 2 * snd p - 1) \<in> I_set \<times> I_set"
        using hp False unfolding top1_unit_interval_def by auto
      have "?G p = F' (fst p, 2 * snd p - 1)" using False by simp
      moreover have "F' (fst p, 2 * snd p - 1) \<in> X" by (rule bspec[OF hF'_range hmem])
      ultimately show ?thesis by simp
    qed
  qed
  have hGA: "\<forall>p\<in>?A. ?G p = F (fst p, 2 * snd p)" by auto
  have hGB: "\<forall>p\<in>?B. ?G p = F' (fst p, 2 * snd p - 1)"
  proof
    fix p assume hp: "p \<in> ?B"
    hence hge: "snd p \<ge> 1/2" by auto
    show "?G p = F' (fst p, 2 * snd p - 1)"
    proof (cases "snd p > 1/2")
      case True thus ?thesis by simp
    next
      case False
      hence "snd p = 1/2" using hge by simp
      hence h2t: "2 * snd p = 1" and h2tm1: "2 * snd p - 1 = 0" by simp_all
      have hs: "fst p \<in> I_set" using hp by auto
      show ?thesis using h2t h2tm1 hmatch[rule_format, OF hs] by simp
    qed
  qed
  have hgA: "top1_continuous_map_on ?A (subspace_topology (I_set \<times> I_set) II_topology ?A) X TX ?G"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>?A. ?G x \<in> X"
    proof
      fix x assume "x \<in> ?A"
      hence "x \<in> I_set \<times> I_set" by auto
      thus "?G x \<in> X" using hG_range by blast
    qed
  next
    show "\<forall>V\<in>TX. {x \<in> ?A. ?G x \<in> V} \<in> subspace_topology (I_set \<times> I_set) II_topology ?A"
    proof
      fix V assume hV: "V \<in> TX"
      have "{x \<in> ?A. ?G x \<in> V} = {x \<in> ?A. F (fst x, 2 * snd x) \<in> V}"
        using hGA by auto
      also have "\<dots> \<in> subspace_topology (I_set \<times> I_set) II_topology ?A"
        using hfA hV unfolding top1_continuous_map_on_def by blast
      finally show "{x \<in> ?A. ?G x \<in> V} \<in> subspace_topology (I_set \<times> I_set) II_topology ?A" .
    qed
  qed
  have hgB: "top1_continuous_map_on ?B (subspace_topology (I_set \<times> I_set) II_topology ?B) X TX ?G"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x\<in>?B. ?G x \<in> X"
    proof
      fix x assume "x \<in> ?B"
      hence "x \<in> I_set \<times> I_set" by auto
      thus "?G x \<in> X" using hG_range by blast
    qed
  next
    show "\<forall>V\<in>TX. {x \<in> ?B. ?G x \<in> V} \<in> subspace_topology (I_set \<times> I_set) II_topology ?B"
    proof
      fix V assume hV: "V \<in> TX"
      have "{x \<in> ?B. ?G x \<in> V} = {x \<in> ?B. F' (fst x, 2 * snd x - 1) \<in> V}"
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> {x \<in> ?B. ?G x \<in> V}"
        hence hxB: "x \<in> ?B" and hGV: "?G x \<in> V" by auto
        have "?G x = F' (fst x, 2 * snd x - 1)" using hGB hxB by blast
        hence "F' (fst x, 2 * snd x - 1) \<in> V" using hGV by simp
        thus "x \<in> {x \<in> ?B. F' (fst x, 2 * snd x - 1) \<in> V}" using hxB by blast
      next
        fix x assume "x \<in> {x \<in> ?B. F' (fst x, 2 * snd x - 1) \<in> V}"
        hence hxB: "x \<in> ?B" and hFV: "F' (fst x, 2 * snd x - 1) \<in> V" by auto
        have "?G x = F' (fst x, 2 * snd x - 1)" using hGB hxB by blast
        hence "?G x \<in> V" using hFV by simp
        thus "x \<in> {x \<in> ?B. ?G x \<in> V}" using hxB by blast
      qed
      also have "\<dots> \<in> subspace_topology (I_set \<times> I_set) II_topology ?B"
        using hfB hV unfolding top1_continuous_map_on_def by blast
      finally show "{x \<in> ?B. ?G x \<in> V} \<in> subspace_topology (I_set \<times> I_set) II_topology ?B" .
    qed
  qed
  show ?thesis
  proof (rule pasting_lemma_two_closed[where
      X = "I_set \<times> I_set" and TX = II_topology and Y = X and TY = TX
      and A = ?A and B = ?B and f = ?G])
    show "is_topology_on (I_set \<times> I_set) II_topology" by (rule hTII)
    show "is_topology_on X TX" by (rule hTX)
    show "closedin_on (I_set \<times> I_set) II_topology ?A" by (rule hA_closed)
    show "closedin_on (I_set \<times> I_set) II_topology ?B" by (rule hB_closed)
    show "?A \<union> ?B = I_set \<times> I_set" unfolding top1_unit_interval_def by auto
    show "\<forall>x\<in>I_set \<times> I_set. ?G x \<in> X" by (rule hG_range)
    show "top1_continuous_map_on ?A (subspace_topology (I_set \<times> I_set) II_topology ?A) X TX ?G"
      by (rule hgA)
    show "top1_continuous_map_on ?B (subspace_topology (I_set \<times> I_set) II_topology ?B) X TX ?G"
      by (rule hgB)
  qed
qed

lemma Lemma_51_1_path_homotopic_trans:
  assumes hTX: "is_topology_on X TX"
      and h1: "top1_path_homotopic_on X TX x0 x1 f f'"
      and h2: "top1_path_homotopic_on X TX x0 x1 f' f''"
  shows "top1_path_homotopic_on X TX x0 x1 f f''"
proof -
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
    and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = f' s"
    and hFleft: "\<forall>t\<in>I_set. F (0, t) = x0" and hFright: "\<forall>t\<in>I_set. F (1, t) = x1"
    using h1 unfolding top1_path_homotopic_on_def by blast
  obtain F' where hF': "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F'"
    and hF'0: "\<forall>s\<in>I_set. F' (s, 0) = f' s" and hF'1: "\<forall>s\<in>I_set. F' (s, 1) = f'' s"
    and hF'left: "\<forall>t\<in>I_set. F' (0, t) = x0" and hF'right: "\<forall>t\<in>I_set. F' (1, t) = x1"
    using h2 unfolding top1_path_homotopic_on_def by blast
  have hmatch: "\<forall>s\<in>I_set. F (s, 1) = F' (s, 0)" using hF1 hF'0 by simp
  let ?G = "\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1)"
  have hG: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?G"
    by (rule path_homotopy_concat_continuous[OF hTX hF hF' hmatch])
  have hG0: "\<forall>s\<in>I_set. ?G (s, 0) = f s" using hF0 by simp
  have hG1: "\<forall>s\<in>I_set. ?G (s, 1) = f'' s" using hF'1 by simp
  have hGleft: "\<forall>t\<in>I_set. ?G (0, t) = x0"
  proof (intro ballI)
    fix t assume ht: "t \<in> I_set"
    have htpos: "0 \<le> t" using ht unfolding top1_unit_interval_def by simp
    have htle1: "t \<le> 1" using ht unfolding top1_unit_interval_def by simp
    show "?G (0, t) = x0"
    proof (cases "t \<le> 1/2")
      case True
      have h2t: "2 * t \<in> I_set" using htpos True unfolding top1_unit_interval_def by simp
      have "?G (0, t) = F (0, 2 * t)" using True by simp
      also have "... = x0" using hFleft h2t by simp
      finally show ?thesis .
    next
      case False
      have h2t: "2 * t - 1 \<in> I_set"
        using False htle1 unfolding top1_unit_interval_def by simp
      have "?G (0, t) = F' (0, 2 * t - 1)" using False by simp
      also have "... = x0" using hF'left h2t by simp
      finally show ?thesis .
    qed
  qed
  have hGright: "\<forall>t\<in>I_set. ?G (1, t) = x1"
  proof (intro ballI)
    fix t assume ht: "t \<in> I_set"
    have htpos: "0 \<le> t" using ht unfolding top1_unit_interval_def by simp
    have htle1: "t \<le> 1" using ht unfolding top1_unit_interval_def by simp
    show "?G (1, t) = x1"
    proof (cases "t \<le> 1/2")
      case True
      have h2t: "2 * t \<in> I_set" using htpos True unfolding top1_unit_interval_def by simp
      have "?G (1, t) = F (1, 2 * t)" using True by simp
      also have "... = x1" using hFright h2t by simp
      finally show ?thesis .
    next
      case False
      have h2t: "2 * t - 1 \<in> I_set"
        using False htle1 unfolding top1_unit_interval_def by simp
      have "?G (1, t) = F' (1, 2 * t - 1)" using False by simp
      also have "... = x1" using hF'right h2t by simp
      finally show ?thesis .
    qed
  qed
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using h1 h2 hG hG0 hG1 hGleft hGright unfolding top1_path_homotopic_on_def by blast
qed

text \<open>Product of paths: f*g is f followed by g, reparameterized to [0,1].\<close>
definition top1_path_product :: "(real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a)" where
  "top1_path_product f g = (\<lambda>s. if s \<le> 1/2 then f (2 * s) else g (2 * s - 1))"

text \<open>Reverse of a path: \<bar>f(s) = f(1-s).\<close>
definition top1_path_reverse :: "(real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a)" where
  "top1_path_reverse f = (\<lambda>s. f (1 - s))"

text \<open>Constant path at a point x.\<close>
definition top1_constant_path :: "'a \<Rightarrow> (real \<Rightarrow> 'a)" where
  "top1_constant_path x = (\<lambda>_. x)"

lemma top1_path_product_at_start:
  "top1_path_product f g 0 = f 0"
  unfolding top1_path_product_def by simp

lemma top1_path_product_at_end:
  "top1_path_product f g 1 = g 1"
  unfolding top1_path_product_def by simp

lemma top1_path_product_at_half:
  "top1_path_product f g (1/2) = f 1"
  unfolding top1_path_product_def by simp

lemma top1_path_reverse_at_start:
  "top1_path_reverse f 0 = f 1"
  unfolding top1_path_reverse_def by simp

lemma top1_path_reverse_at_end:
  "top1_path_reverse f 1 = f 0"
  unfolding top1_path_reverse_def by simp

lemma top1_path_reverse_twice:
  "top1_path_reverse (top1_path_reverse f) = f"
  unfolding top1_path_reverse_def by auto

lemma top1_constant_path_value:
  "top1_constant_path x t = x"
  unfolding top1_constant_path_def by simp

text \<open>The product of paths is well-defined when endpoints match.\<close>

text \<open>Helper: the reverse path is continuous.\<close>
lemma top1_path_reverse_continuous:
  assumes hf: "top1_continuous_map_on I_set I_top X TX f"
  shows "top1_continuous_map_on I_set I_top X TX (top1_path_reverse f)"
proof -
  have hr: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>t. 1 - t)"
    by (rule op_minus_continuous_on_interval)
  have "top1_continuous_map_on I_set I_top X TX (f \<circ> (\<lambda>t. 1 - t))"
    by (rule top1_continuous_map_on_comp[OF hr hf])
  thus ?thesis
    unfolding top1_path_reverse_def by (simp add: comp_def)
qed

lemma top1_path_reverse_is_path:
  assumes hf: "top1_is_path_on X TX x0 x1 f"
  shows "top1_is_path_on X TX x1 x0 (top1_path_reverse f)"
proof -
  have hfc: "top1_continuous_map_on I_set I_top X TX f" and hf0: "f 0 = x0" and hf1: "f 1 = x1"
    using hf unfolding top1_is_path_on_def by blast+
  have hcont: "top1_continuous_map_on I_set I_top X TX (top1_path_reverse f)"
    by (rule top1_path_reverse_continuous[OF hfc])
  have hstart: "top1_path_reverse f 0 = x1"
    unfolding top1_path_reverse_def using hf1 by simp
  have hend: "top1_path_reverse f 1 = x0"
    unfolding top1_path_reverse_def using hf0 by simp
  show ?thesis
    unfolding top1_is_path_on_def using hcont hstart hend by blast
qed

text \<open>Helper: constant path is continuous.\<close>
lemma top1_constant_path_continuous:
  assumes "is_topology_on X TX" and "x \<in> X"
  shows "top1_continuous_map_on I_set I_top X TX (top1_constant_path x)"
  unfolding top1_constant_path_def
  by (rule top1_continuous_map_on_const[OF top1_unit_interval_topology_is_topology_on assms])

lemma top1_constant_path_is_path:
  assumes "is_topology_on X TX" and "x \<in> X"
  shows "top1_is_path_on X TX x x (top1_constant_path x)"
  unfolding top1_is_path_on_def top1_constant_path_def
  using top1_constant_path_continuous[OF assms]
  unfolding top1_constant_path_def by simp

text \<open>Helper: the concatenated path is continuous via the pasting lemma on [0,1/2] \<union> [1/2,1].\<close>
lemma top1_path_product_continuous:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_continuous_map_on I_set I_top X TX f"
      and hg: "top1_continuous_map_on I_set I_top X TX g"
      and hmatch: "f 1 = g 0"
  shows "top1_continuous_map_on I_set I_top X TX (top1_path_product f g)"
proof -
  let ?A = "{s\<in>I_set. s \<le> 1/2}"
  let ?B = "{s\<in>I_set. s \<ge> 1/2}"
  let ?h = "top1_path_product f g"
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have hAB: "?A \<union> ?B = I_set"
    unfolding top1_unit_interval_def by auto
  \<comment> \<open>Range: f*g maps into X.\<close>
  have hf_range: "\<forall>s\<in>I_set. f s \<in> X"
    using hf unfolding top1_continuous_map_on_def by blast
  have hg_range: "\<forall>s\<in>I_set. g s \<in> X"
    using hg unfolding top1_continuous_map_on_def by blast
  have hh_range: "\<forall>s\<in>I_set. ?h s \<in> X"
  proof (intro ballI)
    fix s assume hs: "s \<in> I_set"
    show "?h s \<in> X"
    proof (cases "s \<le> 1/2")
      case True
      have "2 * s \<in> I_set" using hs True unfolding top1_unit_interval_def by simp
      thus ?thesis unfolding top1_path_product_def using True hf_range by simp
    next
      case False
      have "2 * s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by simp
      thus ?thesis unfolding top1_path_product_def using False hg_range by simp
    qed
  qed
  \<comment> \<open>Closedness of A and B in I, and continuity on each piece — requires pasting infrastructure.\<close>
  have hA_closed: "closedin_on I_set I_top ?A"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?A \<subseteq> I_set" by auto
  next
    show "I_set - ?A \<in> I_top"
    proof -
      have heq: "I_set - ?A = I_set \<inter> {s :: real. s > 1/2}"
        unfolding top1_unit_interval_def by auto
      have hopen: "{s :: real. s > 1/2} \<in> top1_open_sets"
        unfolding top1_open_sets_def
        using open_greaterThan[of "1/2 :: real"]
        by (simp add: greaterThan_def Collect_mono_iff)
      show ?thesis
        unfolding heq top1_unit_interval_topology_def subspace_topology_def
        using hopen by blast
    qed
  qed
  have hB_closed: "closedin_on I_set I_top ?B"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?B \<subseteq> I_set" by auto
  next
    show "I_set - ?B \<in> I_top"
    proof -
      have heq: "I_set - ?B = I_set \<inter> {s :: real. s < 1/2}"
        unfolding top1_unit_interval_def by auto
      have hopen: "{s :: real. s < 1/2} \<in> top1_open_sets"
        unfolding top1_open_sets_def
        using open_lessThan[of "1/2 :: real"]
        by (simp add: lessThan_def Collect_mono_iff)
      show ?thesis
        unfolding heq top1_unit_interval_topology_def subspace_topology_def
        using hopen by blast
    qed
  qed
  have hhA: "top1_continuous_map_on ?A (subspace_topology I_set I_top ?A) X TX ?h"
  proof -
    \<comment> \<open>On A, h = f \<circ> (2\<cdot>). Scale is continuous A \<rightarrow> I.\<close>
    have hscale_map: "\<And>s. s \<in> ?A \<Longrightarrow> 2 * s \<in> I_set"
      unfolding top1_unit_interval_def by auto
    have hscale_cont: "continuous_on UNIV (\<lambda>s :: real. 2 * s)"
      by (intro continuous_intros)
    have hsub_eq: "subspace_topology I_set I_top ?A = subspace_topology UNIV top1_open_sets ?A"
      unfolding top1_unit_interval_topology_def
      by (rule subspace_topology_trans, auto)
    have hItop_eq: "I_top = subspace_topology UNIV top1_open_sets I_set"
      unfolding top1_unit_interval_topology_def by rule
    have hscale_raw: "top1_continuous_map_on ?A (subspace_topology UNIV top1_open_sets ?A)
                       I_set (subspace_topology UNIV top1_open_sets I_set) (\<lambda>s. 2 * s)"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hscale_map hscale_cont])
    have hscale: "top1_continuous_map_on ?A (subspace_topology I_set I_top ?A)
                   I_set I_top (\<lambda>s. 2 * s)"
      using hscale_raw hsub_eq hItop_eq by simp
    have hcomp: "top1_continuous_map_on ?A (subspace_topology I_set I_top ?A) X TX (f \<circ> (\<lambda>s. 2 * s))"
      by (rule top1_continuous_map_on_comp[OF hscale hf])
    \<comment> \<open>h agrees with f \<circ> (2\<cdot>) on A.\<close>
    have hfunceq: "\<And>s. s \<in> ?A \<Longrightarrow> ?h s = (f \<circ> (\<lambda>s. 2 * s)) s"
      unfolding top1_path_product_def comp_def by auto
    \<comment> \<open>h agrees with f \<circ> (2\<cdot>) on A, and that's continuous.\<close>
    show ?thesis
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      show "\<forall>s\<in>?A. ?h s \<in> X" using hh_range by auto
    next
      show "\<forall>V\<in>TX. {s \<in> ?A. ?h s \<in> V} \<in> subspace_topology I_set I_top ?A"
      proof
        fix V assume hV: "V \<in> TX"
        have "{s \<in> ?A. ?h s \<in> V} = {s \<in> ?A. (f \<circ> (\<lambda>s. 2 * s)) s \<in> V}"
          using hfunceq by auto
        also have "\<dots> \<in> subspace_topology I_set I_top ?A"
          using hcomp hV unfolding top1_continuous_map_on_def by blast
        finally show "{s \<in> ?A. ?h s \<in> V} \<in> subspace_topology I_set I_top ?A" .
      qed
    qed
  qed
  have hhB: "top1_continuous_map_on ?B (subspace_topology I_set I_top ?B) X TX ?h"
  proof -
    have hscale_map: "\<And>s. s \<in> ?B \<Longrightarrow> 2 * s - 1 \<in> I_set"
      unfolding top1_unit_interval_def by auto
    have hscale_cont: "continuous_on UNIV (\<lambda>s :: real. 2 * s - 1)"
      by (intro continuous_intros)
    have hsub_eq: "subspace_topology I_set I_top ?B = subspace_topology UNIV top1_open_sets ?B"
      unfolding top1_unit_interval_topology_def
      by (rule subspace_topology_trans, auto)
    have hItop_eq: "I_top = subspace_topology UNIV top1_open_sets I_set"
      unfolding top1_unit_interval_topology_def by rule
    have hscale_raw: "top1_continuous_map_on ?B (subspace_topology UNIV top1_open_sets ?B)
                       I_set (subspace_topology UNIV top1_open_sets I_set) (\<lambda>s. 2 * s - 1)"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hscale_map hscale_cont])
    have hscale: "top1_continuous_map_on ?B (subspace_topology I_set I_top ?B)
                   I_set I_top (\<lambda>s. 2 * s - 1)"
      using hscale_raw hsub_eq hItop_eq by simp
    have hcomp: "top1_continuous_map_on ?B (subspace_topology I_set I_top ?B) X TX (g \<circ> (\<lambda>s. 2 * s - 1))"
      by (rule top1_continuous_map_on_comp[OF hscale hg])
    have hfunceq: "\<And>s. s \<in> ?B \<Longrightarrow> ?h s = (g \<circ> (\<lambda>s. 2 * s - 1)) s"
    proof -
      fix s :: real assume hs: "s \<in> ?B"
      hence hge: "s \<ge> 1/2" by auto
      show "?h s = (g \<circ> (\<lambda>s. 2 * s - 1)) s"
      proof (cases "s > 1/2")
        case True
        hence "\<not> (s \<le> 1/2)" by simp
        thus ?thesis unfolding top1_path_product_def comp_def by simp
      next
        case False
        hence "s = 1/2" using hge by simp
        hence h2s: "2 * s = 1" and h2sm1: "2 * s - 1 = 0" by simp_all
        show ?thesis unfolding top1_path_product_def comp_def
          using h2s h2sm1 hmatch by simp
      qed
    qed
    show ?thesis
      unfolding top1_continuous_map_on_def
    proof (intro conjI)
      show "\<forall>s\<in>?B. ?h s \<in> X" using hh_range by auto
    next
      show "\<forall>V\<in>TX. {s \<in> ?B. ?h s \<in> V} \<in> subspace_topology I_set I_top ?B"
      proof
        fix V assume hV: "V \<in> TX"
        have "{s \<in> ?B. ?h s \<in> V} = {s \<in> ?B. (g \<circ> (\<lambda>s. 2 * s - 1)) s \<in> V}"
          using hfunceq by auto
        also have "\<dots> \<in> subspace_topology I_set I_top ?B"
          using hcomp hV unfolding top1_continuous_map_on_def by blast
        finally show "{s \<in> ?B. ?h s \<in> V} \<in> subspace_topology I_set I_top ?B" .
      qed
    qed
  qed
  show ?thesis
    by (rule pasting_lemma_two_closed[OF hTI hTX hA_closed hB_closed hAB hh_range hhA hhB])
qed

lemma top1_path_product_is_path:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
      and hg: "top1_is_path_on X TX x1 x2 g"
  shows "top1_is_path_on X TX x0 x2 (top1_path_product f g)"
proof -
  have hfc: "top1_continuous_map_on I_set I_top X TX f" and hf0: "f 0 = x0" and hf1: "f 1 = x1"
    using hf unfolding top1_is_path_on_def by blast+
  have hgc: "top1_continuous_map_on I_set I_top X TX g" and hg0: "g 0 = x1" and hg1: "g 1 = x2"
    using hg unfolding top1_is_path_on_def by blast+
  have hmatch: "f 1 = g 0" using hf1 hg0 by simp
  have hcont: "top1_continuous_map_on I_set I_top X TX (top1_path_product f g)"
    by (rule top1_path_product_continuous[OF hTX hfc hgc hmatch])
  have hstart: "top1_path_product f g 0 = x0"
    unfolding top1_path_product_def using hf0 by simp
  have hend: "top1_path_product f g 1 = x2"
    unfolding top1_path_product_def using hg1 by simp
  show ?thesis
    unfolding top1_is_path_on_def using hcont hstart hend by blast
qed

text \<open>If two functions agree on S, and one is continuous on S, so is the other.\<close>
lemma top1_continuous_map_on_agree:
  assumes "top1_continuous_map_on S TS Y TY f" and "\<forall>x\<in>S. f x = g x"
  shows "top1_continuous_map_on S TS Y TY g"
proof -
  have "\<forall>x\<in>S. g x \<in> Y" using assms unfolding top1_continuous_map_on_def by auto
  moreover have "\<forall>V\<in>TY. {x \<in> S. g x \<in> V} \<in> TS"
  proof (intro ballI)
    fix V assume "V \<in> TY"
    have "{x \<in> S. g x \<in> V} = {x \<in> S. f x \<in> V}" using assms(2) by auto
    thus "{x \<in> S. g x \<in> V} \<in> TS" using assms(1) \<open>V \<in> TY\<close> unfolding top1_continuous_map_on_def by simp
  qed
  ultimately show ?thesis unfolding top1_continuous_map_on_def by blast
qed

(** from \<S>51 Theorem 51.2: groupoid properties of * **)
lemma Theorem_51_2_associativity:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
      and hg: "top1_is_path_on X TX x1 x2 g"
      and hh: "top1_is_path_on X TX x2 x3 h"
  shows "top1_path_homotopic_on X TX x0 x3
    (top1_path_product f (top1_path_product g h))
    (top1_path_product (top1_path_product f g) h)"
proof -
  have hfc: "top1_continuous_map_on I_set I_top X TX f" and hf0: "f 0 = x0" and hf1: "f 1 = x1"
    using hf unfolding top1_is_path_on_def by blast+
  have hgc: "top1_continuous_map_on I_set I_top X TX g" and hg0: "g 0 = x1" and hg1: "g 1 = x2"
    using hg unfolding top1_is_path_on_def by blast+
  have hhc: "top1_continuous_map_on I_set I_top X TX h" and hh0: "h 0 = x2" and hh1: "h 1 = x3"
    using hh unfolding top1_is_path_on_def by blast+
  have hfr: "\<forall>s\<in>I_set. f s \<in> X" using hfc unfolding top1_continuous_map_on_def by blast
  have hgr: "\<forall>s\<in>I_set. g s \<in> X" using hgc unfolding top1_continuous_map_on_def by blast
  have hhr: "\<forall>s\<in>I_set. h s \<in> X" using hhc unfolding top1_continuous_map_on_def by blast
  \<comment> \<open>Homotopy: F(s,t) with piecewise linear reparametrization.
     f on [0, (1+t)/4], g on [(1+t)/4, (2+t)/4], h on [(2+t)/4, 1].
     F(s,t) = f(4s/(1+t)) if 4s \<le> 1+t;
              g(4s - 1 - t) if 1+t < 4s \<le> 2+t;
              h((4s - 2 - t)/(2 - t)) if 4s > 2+t.\<close>
  let ?F = "\<lambda>(s::real, t::real).
    if 4*s \<le> 1+t then f (4*s / (1+t))
    else if 4*s \<le> 2+t then g (4*s - 1 - t)
    else h ((4*s - 2 - t) / (2 - t))"
  have hF_range: "\<forall>p\<in>I_set \<times> I_set. ?F p \<in> X"
  proof
    fix p assume hp: "p \<in> I_set \<times> I_set"
    obtain s t where hst: "p = (s, t)" and hs: "s \<in> I_set" and ht: "t \<in> I_set"
      using hp by auto
    have hs0: "s \<ge> 0" and hs1: "s \<le> 1" and ht0: "t \<ge> 0" and ht1: "t \<le> 1"
      using hs ht unfolding top1_unit_interval_def by auto
    show "?F p \<in> X"
    proof (cases "4*s \<le> 1+t")
      case True
      have h1t_pos: "1+t > 0" using ht0 by simp
      hence "4*s / (1+t) \<ge> 0" using hs0 by simp
      moreover have "4*s / (1+t) \<le> 1" using True h1t_pos
        by (simp add: divide_le_eq)
      ultimately have "4*s / (1+t) \<in> I_set" unfolding top1_unit_interval_def by simp
      thus ?thesis using hst True hfr by simp
    next
      case False note not1 = this
      show ?thesis
      proof (cases "4*s \<le> 2+t")
        case True
        have "4*s - 1 - t \<ge> 0" using not1 by simp
        moreover have "4*s - 1 - t \<le> 1" using True by simp
        ultimately have "4*s - 1 - t \<in> I_set" unfolding top1_unit_interval_def by simp
        thus ?thesis using hst not1 True hgr by simp
      next
        case False
        have "2 - t > 0" using ht1 by simp
        have "4*s - 2 - t \<ge> 0" using False by simp
        moreover have "4*s - 2 - t \<le> 2 - t" using hs1 by simp
        ultimately have "(4*s - 2 - t) / (2 - t) \<ge> 0" using \<open>2 - t > 0\<close> by simp
        moreover have "(4*s - 2 - t) / (2 - t) \<le> 1"
          using \<open>4*s - 2 - t \<le> 2 - t\<close> \<open>2 - t > 0\<close>
          by (simp add: divide_le_eq_1_pos)
        ultimately have "(4*s - 2 - t) / (2 - t) \<in> I_set" unfolding top1_unit_interval_def by simp
        thus ?thesis using hst not1 False hhr by simp
      qed
    qed
  qed
  have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?F"
  proof -
    \<comment> \<open>Two-level pasting: first paste f,g pieces, then paste with h piece.\<close>
    let ?Cfg = "{(s,t) \<in> I_set \<times> I_set. 4*s \<le> 2+t}"
    let ?Ch = "{(s,t) \<in> I_set \<times> I_set. 4*s \<ge> 2+t}"
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
    \<comment> \<open>Closedness of Cfg and Ch.\<close>
    have hCfg_closed: "closedin_on (I_set \<times> I_set) II_topology ?Cfg"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?Cfg \<subseteq> I_set \<times> I_set" by auto
      have "I_set \<times> I_set - ?Cfg = {(s,t) \<in> I_set \<times> I_set. 4*s > 2+t}" by auto
      also have "\<dots> = (I_set \<times> I_set) \<inter> {p :: real \<times> real. 4 * fst p - snd p > 2}"
        by auto
      also have "\<dots> \<in> II_topology"
      proof -
        have "open {p :: real \<times> real. 4 * fst p - snd p > 2}"
          by (intro open_Collect_less continuous_intros)
        hence "{p :: real \<times> real. 4 * fst p - snd p > 2} \<in> (top1_open_sets :: (real\<times>real) set set)"
          unfolding top1_open_sets_def by blast
        hence "{p :: real \<times> real. 4 * fst p - snd p > 2}
               \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
          using product_topology_on_open_sets_real2 by metis
        thus ?thesis
          unfolding II_topology_def II_topology_eq_subspace subspace_topology_def by blast
      qed
      finally show "I_set \<times> I_set - ?Cfg \<in> II_topology" .
    qed
    have hCh_closed: "closedin_on (I_set \<times> I_set) II_topology ?Ch"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?Ch \<subseteq> I_set \<times> I_set" by auto
      have "I_set \<times> I_set - ?Ch = {(s,t) \<in> I_set \<times> I_set. 4*s < 2+t}" by auto
      also have "\<dots> = (I_set \<times> I_set) \<inter> {p :: real \<times> real. 4 * fst p - snd p < 2}"
        by auto
      also have "\<dots> \<in> II_topology"
      proof -
        have "open {p :: real \<times> real. 4 * fst p - snd p < 2}"
          by (intro open_Collect_less continuous_intros)
        hence "{p :: real \<times> real. 4 * fst p - snd p < 2} \<in> (top1_open_sets :: (real\<times>real) set set)"
          unfolding top1_open_sets_def by blast
        hence "{p :: real \<times> real. 4 * fst p - snd p < 2}
               \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
          using product_topology_on_open_sets_real2 by metis
        thus ?thesis
          unfolding II_topology_def II_topology_eq_subspace subspace_topology_def by blast
      qed
      finally show "I_set \<times> I_set - ?Ch \<in> II_topology" .
    qed
    have hcover: "?Cfg \<union> ?Ch = I_set \<times> I_set" by auto
    \<comment> \<open>Continuity of F on Cfg (inner pasting of f and g).\<close>
    have hFcfg: "top1_continuous_map_on ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg)
                  X TX ?F"
    proof -
      \<comment> \<open>Two clamped reparametrizations.\<close>
      let ?\<rho>f = "\<lambda>p::real\<times>real. max 0 (min 1 (4 * fst p / max 1 (1 + snd p)))"
      let ?\<rho>g = "\<lambda>p::real\<times>real. max 0 (min 1 (4 * fst p - 1 - snd p))"
      have h\<rho>f_cont: "continuous_on (I_set \<times> I_set) ?\<rho>f"
        by (intro continuous_intros continuous_on_divide) auto
      have h\<rho>f_map: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?\<rho>f p \<in> I_set"
        unfolding top1_unit_interval_def by auto
      have hf_comp: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (f \<circ> ?\<rho>f)"
        unfolding II_topology_def
        by (rule top1_continuous_map_on_comp[OF top1_continuous_map_on_II_to_I[OF h\<rho>f_map h\<rho>f_cont] hfc])
      have h\<rho>g_cont: "continuous_on (I_set \<times> I_set) ?\<rho>g" by (intro continuous_intros)
      have h\<rho>g_map: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?\<rho>g p \<in> I_set"
        unfolding top1_unit_interval_def by auto
      have hg_comp: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (g \<circ> ?\<rho>g)"
        unfolding II_topology_def
        by (rule top1_continuous_map_on_comp[OF top1_continuous_map_on_II_to_I[OF h\<rho>g_map h\<rho>g_cont] hgc])
      \<comment> \<open>Restrict + transfer.\<close>
      let ?Cf = "{(s,t) \<in> I_set \<times> I_set. 4*s \<le> 1+t}"
      let ?Cg = "{(s,t) \<in> I_set \<times> I_set. 4*s \<ge> 1+t \<and> 4*s \<le> 2+t}"
      have hCf_sub: "?Cf \<subseteq> I_set \<times> I_set" by auto
      have hCg_sub: "?Cg \<subseteq> I_set \<times> I_set" by auto
      have hf_agree: "\<forall>p\<in>?Cf. (f \<circ> ?\<rho>f) p = ?F p"
      proof
        fix p assume hp: "p \<in> ?Cf"
        obtain s t where hst: "p = (s, t)" and hs: "s \<in> I_set" and ht: "t \<in> I_set"
            and h4s: "4*s \<le> 1+t" using hp by auto
        have ht0: "t \<ge> 0" using ht unfolding top1_unit_interval_def by simp
        have hs0: "s \<ge> 0" using hs unfolding top1_unit_interval_def by simp
        have "max (1::real) (1 + t) = 1 + t" using ht0 by simp
        moreover have "4*s / (1+t) \<ge> 0" using hs0 ht0 by simp
        moreover have "4*s / (1+t) \<le> 1" using h4s ht0 by (simp add: divide_le_eq)
        ultimately have "?\<rho>f p = 4*s / (1+t)" using hst by auto
        hence lhs: "(f \<circ> ?\<rho>f) p = f (4*s / (1+t))" unfolding comp_def by simp
        have rhs: "?F p = f (4*s / (1+t))" using hst h4s by simp
        show "(f \<circ> ?\<rho>f) p = ?F p" using lhs rhs by metis
      qed
      have hg_agree: "\<forall>p\<in>?Cg. (g \<circ> ?\<rho>g) p = ?F p"
      proof
        fix p assume hp: "p \<in> ?Cg"
        obtain s t where hst: "p = (s, t)" and hs: "s \<in> I_set" and ht: "t \<in> I_set"
            and h4s_ge: "4*s \<ge> 1+t" and h4s_le: "4*s \<le> 2+t" using hp by auto
        have "4*s - 1 - t \<ge> 0" using h4s_ge by simp
        moreover have "4*s - 1 - t \<le> 1" using h4s_le by simp
        ultimately have "?\<rho>g p = 4*s - 1 - t" using hst by auto
        hence "(g \<circ> ?\<rho>g) p = g (4*s - 1 - t)" by (simp add: comp_def)
        moreover have "?F p = g (4*s - 1 - t)"
        proof (cases "4*s = 1+t")
          case True
          \<comment> \<open>Boundary: both branches give x1.\<close>
          hence "?F p = f (4*s / (1+t))" using hst by simp
          also have "... = f 1"
          proof -
            have "1 + t \<noteq> 0" using ht unfolding top1_unit_interval_def by simp
            thus ?thesis using True by (simp add: divide_simps)
          qed
          also have "... = x1" using hf1 .
          finally have l: "?F p = x1" .
          have "g (4*s - 1 - t) = g 0" using True by simp
          also have "... = x1" using hg0 .
          finally show ?thesis using l by simp
        next
          case False
          hence "4*s > 1+t" using h4s_ge by simp
          hence "\<not>(4*s \<le> 1+t)" by simp
          moreover have "4*s \<le> 2+t" using h4s_le .
          ultimately show ?thesis using hst by simp
        qed
        ultimately show "(g \<circ> ?\<rho>g) p = ?F p" by simp
      qed
      have hF_Cf: "top1_continuous_map_on ?Cf (subspace_topology (I_set \<times> I_set) II_topology ?Cf) X TX ?F"
        by (rule top1_continuous_map_on_agree[OF
             top1_continuous_map_on_restrict_domain_simple[OF hf_comp hCf_sub] hf_agree])
      have hF_Cg: "top1_continuous_map_on ?Cg (subspace_topology (I_set \<times> I_set) II_topology ?Cg) X TX ?F"
        by (rule top1_continuous_map_on_agree[OF
             top1_continuous_map_on_restrict_domain_simple[OF hg_comp hCg_sub] hg_agree])
      \<comment> \<open>Paste Cf and Cg to get Cfg.\<close>
      have "?Cf \<union> ?Cg = ?Cfg" by auto
      \<comment> \<open>Need closedness of Cf, Cg in Cfg subspace, plus the pasting lemma on Cfg.\<close>
      \<comment> \<open>Inner pasting: Cf \<union> Cg = Cfg, closedness in Cfg subspace.\<close>
      have hTcfg: "is_topology_on ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg)"
        by (rule subspace_topology_is_topology_on[OF hTII]) auto
      have hCf_closed_cfg: "closedin_on ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg) ?Cf"
        unfolding closedin_on_def
      proof (intro conjI)
        show "?Cf \<subseteq> ?Cfg" by auto
        have "?Cfg - ?Cf = ?Cfg \<inter> {(s,t) \<in> I_set \<times> I_set. 4*s > 1+t}" by auto
        also have "\<dots> \<in> subspace_topology (I_set \<times> I_set) II_topology ?Cfg"
        proof -
          have "open {p :: real \<times> real. 4 * fst p - snd p > 1}"
            by (intro open_Collect_less continuous_intros)
          hence "{p :: real \<times> real. 4 * fst p - snd p > 1} \<in> (top1_open_sets :: (real\<times>real) set set)"
            unfolding top1_open_sets_def by blast
          hence "{p :: real \<times> real. 4 * fst p - snd p > 1}
                 \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
            using product_topology_on_open_sets_real2 by metis
          hence "(I_set \<times> I_set) \<inter> {p. 4 * fst p - snd p > 1} \<in> II_topology"
            unfolding II_topology_def II_topology_eq_subspace subspace_topology_def by blast
          moreover have "{(s,t) \<in> I_set \<times> I_set. 4*s > 1+t} = (I_set \<times> I_set) \<inter> {p. 4 * fst p - snd p > 1}"
            by auto
          ultimately have "{(s,t) \<in> I_set \<times> I_set. 4*s > 1+t} \<in> II_topology" by simp
          thus ?thesis unfolding subspace_topology_def by blast
        qed
        finally show "?Cfg - ?Cf \<in> subspace_topology (I_set \<times> I_set) II_topology ?Cfg" .
      qed
      have hCg_closed_cfg: "closedin_on ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg) ?Cg"
        unfolding closedin_on_def
      proof (intro conjI)
        show "?Cg \<subseteq> ?Cfg" by auto
        have "?Cfg - ?Cg = {(s,t) \<in> I_set \<times> I_set. 4*s < 1+t}" by auto
        also have "\<dots> \<in> subspace_topology (I_set \<times> I_set) II_topology ?Cfg"
        proof -
          have "open {p :: real \<times> real. 4 * fst p - snd p < 1}"
            by (intro open_Collect_less continuous_intros)
          hence "{p :: real \<times> real. 4 * fst p - snd p < 1} \<in> (top1_open_sets :: (real\<times>real) set set)"
            unfolding top1_open_sets_def by blast
          hence "{p :: real \<times> real. 4 * fst p - snd p < 1}
                 \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
            using product_topology_on_open_sets_real2 by metis
          hence "(I_set \<times> I_set) \<inter> {p. 4 * fst p - snd p < 1} \<in> II_topology"
            unfolding II_topology_def II_topology_eq_subspace subspace_topology_def by blast
          moreover have "{(s,t) \<in> I_set \<times> I_set. 4*s < 1+t} = (I_set \<times> I_set) \<inter> {p. 4 * fst p - snd p < 1}"
            by auto
          ultimately have hopen_II: "{(s,t) \<in> I_set \<times> I_set. 4*s < 1+t} \<in> II_topology" by simp
          have "{(s,t) \<in> I_set \<times> I_set. 4*s < 1+t} = ?Cfg \<inter> {(s,t) \<in> I_set \<times> I_set. 4*s < 1+t}"
            by auto
          thus ?thesis unfolding subspace_topology_def using hopen_II by blast
        qed
        finally show "?Cfg - ?Cg \<in> subspace_topology (I_set \<times> I_set) II_topology ?Cfg" .
      qed
      have hCfCg_cover: "?Cf \<union> ?Cg = ?Cfg" by auto
      have hF_range_cfg: "\<forall>p\<in>?Cfg. ?F p \<in> X" using hF_range by auto
      \<comment> \<open>Need continuity of ?F on subspace of Cfg from Cf and Cg subspaces.\<close>
      have hCf_sub_Cfg: "?Cf \<subseteq> ?Cfg" by auto
      have hCg_sub_Cfg: "?Cg \<subseteq> ?Cfg" by auto
      have htrans_Cf: "subspace_topology ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg) ?Cf
                      = subspace_topology (I_set \<times> I_set) II_topology ?Cf"
        by (rule subspace_topology_trans[OF hCf_sub_Cfg])
      have htrans_Cg: "subspace_topology ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg) ?Cg
                      = subspace_topology (I_set \<times> I_set) II_topology ?Cg"
        by (rule subspace_topology_trans[OF hCg_sub_Cfg])
      have hF_Cf_cfg: "top1_continuous_map_on ?Cf (subspace_topology ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg) ?Cf)
                        X TX ?F"
        using hF_Cf unfolding htrans_Cf .
      have hF_Cg_cfg: "top1_continuous_map_on ?Cg (subspace_topology ?Cfg (subspace_topology (I_set \<times> I_set) II_topology ?Cfg) ?Cg)
                        X TX ?F"
        using hF_Cg unfolding htrans_Cg .
      show ?thesis
        by (rule pasting_lemma_two_closed[OF hTcfg hTX hCf_closed_cfg hCg_closed_cfg hCfCg_cover hF_range_cfg hF_Cf_cfg hF_Cg_cfg])
    qed
    \<comment> \<open>Continuity of F on Ch: h((4s-2-t)/(2-t)).\<close>
    have hFch: "top1_continuous_map_on ?Ch (subspace_topology (I_set \<times> I_set) II_topology ?Ch)
                 X TX ?F"
    proof -
      let ?\<rho> = "\<lambda>p::real\<times>real. max 0 (min 1 ((4 * fst p - 2 - snd p) / (2 - snd p)))"
      have h\<rho>_cont: "continuous_on (I_set \<times> I_set) ?\<rho>"
        by (intro continuous_intros continuous_on_divide) (auto simp: top1_unit_interval_def)
      have h\<rho>_map: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?\<rho> p \<in> I_set"
        unfolding top1_unit_interval_def by auto
      have hcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (h \<circ> ?\<rho>)"
        unfolding II_topology_def
        by (rule top1_continuous_map_on_comp[OF top1_continuous_map_on_II_to_I[OF h\<rho>_map h\<rho>_cont] hhc])
      \<comment> \<open>Restrict to Ch.\<close>
      have hCh_sub: "?Ch \<subseteq> I_set \<times> I_set" by auto
      have hcomp_restrict: "top1_continuous_map_on ?Ch (subspace_topology (I_set \<times> I_set) II_topology ?Ch)
                             X TX (h \<circ> ?\<rho>)"
        using top1_continuous_map_on_restrict_domain_simple[OF hcomp hCh_sub] .
      \<comment> \<open>h \<circ> \<rho> agrees with ?F on Ch.\<close>
      have hagree: "\<forall>p\<in>?Ch. (h \<circ> ?\<rho>) p = ?F p"
      proof
        fix p assume hp: "p \<in> ?Ch"
        obtain s t where hst: "p = (s, t)" and hs: "s \<in> I_set" and ht: "t \<in> I_set"
            and h4s: "4*s \<ge> 2+t" using hp by auto
        have hs1: "s \<le> 1" using hs unfolding top1_unit_interval_def by simp
        have ht0: "t \<ge> 0" and ht1: "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
        have h2t: "2 - t > 0" using ht1 by simp
        have hnn: "(4*s - 2 - t) \<ge> 0" using h4s by simp
        have hle: "(4*s - 2 - t) \<le> 2 - t" using hs1 by linarith
        hence hrho_val: "?\<rho> p = (4*s - 2 - t) / (2 - t)" using hst hnn hle h2t
          by (simp add: divide_le_eq)
        show "(h \<circ> ?\<rho>) p = ?F p"
        proof (cases "4*s = 2+t")
          case True
          hence "?\<rho> p = 0" using hst by simp
          hence lhs: "(h \<circ> ?\<rho>) p = h 0" by (simp add: comp_def)
          have "4*s > 1+t" using h4s ht0 by linarith
          hence "\<not>(4*s \<le> 1+t)" by simp
          hence "?F p = g (4*s - 1 - t)" using hst True by simp
          also have "... = g 1" using True by simp
          also have "... = x2" using hg1 .
          finally have rhs: "?F p = x2" .
          show ?thesis using lhs rhs hh0 by simp
        next
          case False
          hence h4s_gt: "4*s > 2+t" using h4s by simp
          hence "\<not>(4*s \<le> 1+t)" and "\<not>(4*s \<le> 2+t)" by auto
          hence "?F p = h ((4*s - 2 - t) / (2 - t))" using hst by simp
          thus ?thesis using hrho_val hst by (simp add: comp_def)
        qed
      qed
      show ?thesis by (rule top1_continuous_map_on_agree[OF hcomp_restrict hagree])
    qed
    show ?thesis
      by (rule pasting_lemma_two_closed[OF hTII hTX hCfg_closed hCh_closed hcover hF_range hFcfg hFch])
  qed
  have hF_s0: "\<forall>s\<in>I_set. ?F (s, 0) = top1_path_product (top1_path_product f g) h s"
  proof
    fix s assume hs: "s \<in> I_set"
    have hs0: "s \<ge> 0" and hs1: "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
    show "?F (s, 0) = top1_path_product (top1_path_product f g) h s"
    proof (cases "s \<le> 1/2")
      case True \<comment> \<open>(f*g)*h maps to (f*g)(2s)\<close>
      show ?thesis
      proof (cases "s \<le> 1/4")
        case True2: True \<comment> \<open>(f*g)(2s) = f(4s) since 2s \<le> 1/2\<close>
        have "4*s \<le> 1+0" using True2 by simp
        hence lhs: "?F (s, 0) = f (4*s / 1)" by simp
        have "top1_path_product (top1_path_product f g) h s
            = top1_path_product f g (2*s)" using True unfolding top1_path_product_def by simp
        also have "... = f (2*(2*s))" using True2 unfolding top1_path_product_def by simp
        also have "... = f (4*s)" by simp
        finally show ?thesis using lhs by simp
      next
        case False2: False \<comment> \<open>(f*g)(2s) = g(4s-1) since 2s > 1/2\<close>
        hence "s > 1/4" by simp
        hence "4*s > 1" by simp
        moreover have "4*s \<le> 2" using True by simp
        ultimately have lhs: "?F (s, 0) = g (4*s - 1 - 0)" by simp
        have "top1_path_product (top1_path_product f g) h s
            = top1_path_product f g (2*s)" using True unfolding top1_path_product_def by simp
        also have "... = g (2*(2*s) - 1)" using False2 unfolding top1_path_product_def by auto
        also have "... = g (4*s - 1)" by simp
        finally show ?thesis using lhs by simp
      qed
    next
      case False \<comment> \<open>(f*g)*h maps to h(2s-1)\<close>
      hence "s > 1/2" by simp
      hence "4*s > 2" by simp
      hence h4s_gt: "\<not> (4*s \<le> 1 + (0::real))" and h4s_gt2: "\<not> (4*s \<le> 2 + (0::real))" by auto
      have harith: "(4*s - 2) / (2::real) = 2*s - 1" by auto
      have "?F (s, 0) = h ((4*s - 2) / 2)"
        using h4s_gt h4s_gt2 by simp
      hence lhs: "?F (s, 0) = h (2*s - 1)" using harith by presburger
      have "top1_path_product (top1_path_product f g) h s = h (2*s - 1)"
        using False unfolding top1_path_product_def by auto
      thus ?thesis using lhs by simp
    qed
  qed
  have hF_s1: "\<forall>s\<in>I_set. ?F (s, 1) = top1_path_product f (top1_path_product g h) s"
  proof
    fix s assume hs: "s \<in> I_set"
    have hs0: "s \<ge> 0" and hs1: "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
    show "?F (s, 1) = top1_path_product f (top1_path_product g h) s"
    proof (cases "s \<le> 1/2")
      case True
      have "4*s \<le> 1 + (1::real)" using True by simp
      hence lhs: "?F (s, 1) = f (4*s / (1+1))" by simp
      have "top1_path_product f (top1_path_product g h) s = f (2*s)"
        using True unfolding top1_path_product_def by simp
      moreover have "4*s / 2 = 2*s" by simp
      ultimately show ?thesis using lhs by simp
    next
      case False
      hence "s > 1/2" by simp
      show ?thesis
      proof (cases "s \<le> 3/4")
        case True2: True
        have "4*s > 2" using \<open>s > 1/2\<close> by simp
        moreover have "4*s \<le> 2 + (1::real)" using True2 by simp
        ultimately have lhs: "?F (s, 1) = g (4*s - 1 - 1)" by simp
        have "top1_path_product f (top1_path_product g h) s
            = top1_path_product g h (2*s - 1)"
          using False unfolding top1_path_product_def by auto
        also have "... = g (2*(2*s - 1))" using True2 \<open>s > 1/2\<close>
          unfolding top1_path_product_def by auto
        also have "... = g (4*s - 2)" by simp
        finally show ?thesis using lhs by simp
      next
        case False2: False
        hence "s > 3/4" by simp
        have "4*s > 3" using \<open>s > 3/4\<close> by simp
        hence lhs: "?F (s, 1) = h ((4*s - 2 - 1) / (2 - 1))" by simp
        have "top1_path_product f (top1_path_product g h) s
            = top1_path_product g h (2*s - 1)"
          using False unfolding top1_path_product_def by auto
        also have "... = h (2*(2*s - 1) - 1)" using False2
          unfolding top1_path_product_def by auto
        also have "... = h (4*s - 3)" by simp
        finally have rhs: "top1_path_product f (top1_path_product g h) s = h (4*s - 3)" .
        have "(4*s - 3) / 1 = 4*s - 3" by simp
        thus ?thesis using lhs rhs by simp
      qed
    qed
  qed
  have hF_0t: "\<forall>t\<in>I_set. ?F (0, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "4*(0::real) \<le> 1+t" using ht unfolding top1_unit_interval_def by simp
    hence "?F (0, t) = f (0 / (1+t))" by simp
    thus "?F (0, t) = x0" using hf0 by simp
  qed
  have hF_1t: "\<forall>t\<in>I_set. ?F (1, t) = x3"
  proof
    fix t assume ht: "t \<in> I_set"
    have ht1: "t \<le> 1" using ht unfolding top1_unit_interval_def by simp
    have "4*(1::real) = 4" by simp
    moreover have "2 + t \<le> 3" using ht1 by simp
    hence "4 > 2 + t" by simp
    ultimately have lhs: "?F (1, t) = h ((4 - 2 - t) / (2 - t))" by simp
    have "2 - t > 0" using ht1 by simp
    hence "(2 - t) / (2 - t) = 1" by simp
    thus "?F (1, t) = x3" using lhs hh1 by simp
  qed
  have hgh: "top1_is_path_on X TX x1 x3 (top1_path_product g h)"
    by (rule top1_path_product_is_path[OF hTX hg hh])
  have hfg: "top1_is_path_on X TX x0 x2 (top1_path_product f g)"
    by (rule top1_path_product_is_path[OF hTX hf hg])
  have hpath_lhs: "top1_is_path_on X TX x0 x3
    (top1_path_product f (top1_path_product g h))"
    by (rule top1_path_product_is_path[OF hTX hf hgh])
  have hpath_rhs: "top1_is_path_on X TX x0 x3
    (top1_path_product (top1_path_product f g) h)"
    by (rule top1_path_product_is_path[OF hTX hfg hh])
  \<comment> \<open>Our F goes from (f*g)*h to f*(g*h), but the goal is the reverse.
      Use symmetry of path homotopy.\<close>
  have hrev: "top1_path_homotopic_on X TX x0 x3
    (top1_path_product (top1_path_product f g) h)
    (top1_path_product f (top1_path_product g h))"
    unfolding top1_path_homotopic_on_def
    using hpath_rhs hpath_lhs hF_cont hF_s0 hF_s1 hF_0t hF_1t by blast
  show ?thesis by (rule Lemma_51_1_path_homotopic_sym[OF hrev])
qed

lemma Theorem_51_2_left_identity:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x1
    (top1_path_product (top1_constant_path x0) f) f"
proof -
  have hfcont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_path_on_def by blast
  have hfrange: "\<forall>s\<in>I_set. f s \<in> X" using hfcont unfolding top1_continuous_map_on_def by blast
  have hf0: "f 0 = x0" using hf unfolding top1_is_path_on_def by blast
  have hf1: "f 1 = x1" using hf unfolding top1_is_path_on_def by blast
  \<comment> \<open>Homotopy: F(s,t) = f(max(0, (2s - 1 + t)/(1 + t))).
     At t=0: s \<le> 1/2 gives max(0, (2s-1)/1) = max(0, 2s-1) = 0, so F=f(0)=x0.
             s \<ge> 1/2 gives f(2s-1) = (e * f)(s). So F(\<cdot>,0) = e * f.
     At t=1: max(0, (2s)/2) = max(0, s) = s for s\<ge>0. So F(\<cdot>,1) = f.
     At s=0: max(0, (-1+t)/(1+t)). For t\<in>[0,1], -1+t \<le> 0, so max=0, F=f(0)=x0.
     At s=1: max(0, (1+t)/(1+t)) = max(0, 1) = 1, so F=f(1)=x1.\<close>
  let ?g = "\<lambda>(s::real, t::real). max 0 (min 1 ((2*s - 1 + t) / (1 + t)))"
  let ?F = "\<lambda>p. f (?g p)"
  have hg_range: "\<forall>s\<in>I_set. \<forall>t\<in>I_set. ?g (s, t) \<in> I_set"
    unfolding top1_unit_interval_def by auto
  have hF_range: "\<forall>p\<in>I_set \<times> I_set. ?F p \<in> X"
  proof
    fix p assume hp: "p \<in> I_set \<times> I_set"
    have "?g p \<in> I_set" using hp hg_range by auto
    thus "?F p \<in> X" using hfrange by blast
  qed
  have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?F"
  proof -
    have hg_cont: "continuous_on (I_set \<times> I_set) ?g"
    proof -
      have h1t_pos: "\<And>s t. (s, t) \<in> I_set \<times> I_set \<Longrightarrow> 1 + t > 0"
        unfolding top1_unit_interval_def by auto
      have hnum: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 2 * fst p - 1 + snd p)"
        by (intro continuous_intros)
      have hden: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 1 + snd p)"
        by (intro continuous_intros)
      have "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. (2 * fst p - 1 + snd p) / (1 + snd p))"
        by (rule continuous_on_divide[OF hnum hden])
           (auto simp: top1_unit_interval_def)
      hence "continuous_on (I_set \<times> I_set) (\<lambda>(s, t). (2*s - 1 + t) / (1 + t))"
        by (simp add: case_prod_unfold)
      hence hmin: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. min 1 ((2 * fst p - 1 + snd p) / (1 + snd p)))"
        by (intro continuous_on_min continuous_on_const) (simp add: case_prod_unfold)
      have "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. max 0 (min 1 ((2 * fst p - 1 + snd p) / (1 + snd p))))"
        by (intro continuous_on_max continuous_on_const hmin)
      thus ?thesis by (simp add: case_prod_unfold)
    qed
    have hg_top1: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top ?g"
    proof -
      have hmap: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?g p \<in> I_set" using hg_range by auto
      show ?thesis by (rule top1_continuous_map_on_II_to_I[OF hmap hg_cont])
    qed
    have hcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (f \<circ> ?g)"
      unfolding II_topology_def by (rule top1_continuous_map_on_comp[OF hg_top1 hfcont])
    moreover have "\<forall>p\<in>I_set \<times> I_set. (f \<circ> ?g) p = ?F p" by (auto simp: comp_def)
    ultimately show ?thesis
      unfolding top1_continuous_map_on_def II_topology_def
      using hF_range by auto
  qed
  have hF_s0: "\<forall>s\<in>I_set. ?F (s, 0) = top1_path_product (top1_constant_path x0) f s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "?F (s, 0) = top1_path_product (top1_constant_path x0) f s"
    proof (cases "s \<le> 1/2")
      case True
      hence "2*s - 1 + 0 = 2*s - 1" by simp
      hence "(2*s - 1) / (1 + 0) = 2*s - 1" by simp
      moreover have "2*s - 1 \<le> 0" using True by simp
      ultimately have "?g (s, 0) = 0"
        using hs unfolding top1_unit_interval_def by auto
      hence "?F (s, 0) = f 0" by simp
      also have "... = x0" using hf0 by simp
      finally have lhs: "?F (s, 0) = x0" .
      have "top1_path_product (top1_constant_path x0) f s = top1_constant_path x0 (2 * s)"
        using True unfolding top1_path_product_def by simp
      also have "... = x0" unfolding top1_constant_path_def by simp
      finally have rhs: "top1_path_product (top1_constant_path x0) f s = x0" .
      show ?thesis using lhs rhs by simp
    next
      case False
      hence hge: "s > 1/2" by simp
      hence "2*s - 1 > 0" by simp
      hence "(2*s - 1) / 1 = 2*s - 1" by simp
      moreover have "2*s - 1 \<ge> 0" using hge by simp
      moreover have "2*s - 1 \<le> 1" using hs unfolding top1_unit_interval_def by auto
      ultimately have "?g (s, 0) = 2*s - 1" using hs unfolding top1_unit_interval_def by auto
      hence h_Fs0: "?F (s, 0) = f (2*s - 1)" by simp
      have "top1_path_product (top1_constant_path x0) f s = f (2*s - 1)"
        using hge unfolding top1_path_product_def top1_constant_path_def by auto
      thus ?thesis using h_Fs0 by simp
    qed
  qed
  have hF_s1: "\<forall>s\<in>I_set. ?F (s, 1) = f s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "(2*s - 1 + 1) / (1 + 1) = s" by auto
    moreover have "s \<ge> 0" using hs unfolding top1_unit_interval_def by simp
    moreover have "s \<le> 1" using hs unfolding top1_unit_interval_def by simp
    ultimately have "?g (s, 1) = s" by auto
    thus "?F (s, 1) = f s" by simp
  qed
  have hF_0t: "\<forall>t\<in>I_set. ?F (0, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "(2*0 - 1 + t) / (1 + t) = (t - 1) / (1 + t)" by simp
    moreover have "t - 1 \<le> 0" using ht unfolding top1_unit_interval_def by simp
    moreover have "1 + t > 0" using ht unfolding top1_unit_interval_def by simp
    ultimately have "(t - 1) / (1 + t) \<le> 0" by (simp add: divide_nonpos_nonneg)
    hence "?g (0, t) = 0" by auto
    hence "?F (0, t) = f 0" by simp
    thus "?F (0, t) = x0" using hf0 by simp
  qed
  have hF_1t: "\<forall>t\<in>I_set. ?F (1, t) = x1"
  proof
    fix t assume ht: "t \<in> I_set"
    have "(2*1 - 1 + t) / (1 + t) = (1 + t) / (1 + t)" by simp
    moreover have "1 + t > 0" using ht unfolding top1_unit_interval_def by simp
    ultimately have "(1 + t) / (1 + t) = 1" by simp
    hence "?g (1, t) = 1" by auto
    hence "?F (1, t) = f 1" by simp
    thus "?F (1, t) = x1" using hf1 by simp
  qed
  have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hx0X: "x0 \<in> X" using hfrange h0I hf0 by force
  have hconst: "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_path[OF hTX hx0X])
  have hpath_ef: "top1_is_path_on X TX x0 x1 (top1_path_product (top1_constant_path x0) f)"
    by (rule top1_path_product_is_path[OF hTX hconst hf])
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hpath_ef hf hF_cont hF_s0 hF_s1 hF_0t hF_1t by blast
qed

lemma Theorem_51_2_right_identity:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_constant_path x1)) f"
proof -
  have hfcont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_path_on_def by blast
  have hfrange: "\<forall>s\<in>I_set. f s \<in> X" using hfcont unfolding top1_continuous_map_on_def by blast
  have hf0: "f 0 = x0" using hf unfolding top1_is_path_on_def by blast
  have hf1: "f 1 = x1" using hf unfolding top1_is_path_on_def by blast
  \<comment> \<open>Homotopy: F(s,t) = f(min(1, 2s/(2-t))).
     At t=0: s < 1/2 gives f(2s/2) = f(s); s = 1/2 gives f(1); s > 1/2 gives f(min(1, 2s/2)).
     Wait — use F(s,t) = f(min(1, (2s)/(1+t))).
     At t=0: min(1, 2s) — for s \<le> 1/2, f(2s); for s \<ge> 1/2, f(1) = x1.
             So F(\<cdot>, 0) = f * e_{x1}.
     At t=1: min(1, s) = s (for s \<in> [0,1]). So F(\<cdot>, 1) = f.
     At s=0: min(1, 0) = 0. F(0,t) = f(0) = x0.
     At s=1: min(1, 2/(1+t)). Since 1+t \<ge> 1, 2/(1+t) \<le> 2. Also 1+t \<le> 2, so 2/(1+t) \<ge> 1.
             So min(1, 2/(1+t)) = 1. F(1,t) = f(1) = x1.\<close>
  let ?g = "\<lambda>(s::real, t::real). min 1 (max 0 ((2*s) / (1 + t)))"
  let ?F = "\<lambda>p. f (?g p)"
  have hg_range: "\<forall>s\<in>I_set. \<forall>t\<in>I_set. ?g (s, t) \<in> I_set"
    unfolding top1_unit_interval_def by auto
  have hF_range: "\<forall>p\<in>I_set \<times> I_set. ?F p \<in> X"
  proof
    fix p assume hp: "p \<in> I_set \<times> I_set"
    have "?g p \<in> I_set" using hp hg_range by auto
    thus "?F p \<in> X" using hfrange by blast
  qed
  have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?F"
  proof -
    have hg_cont: "continuous_on (I_set \<times> I_set) ?g"
    proof -
      have hnum: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 2 * fst p)"
        by (intro continuous_intros)
      have hden: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 1 + snd p)"
        by (intro continuous_intros)
      have "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. (2 * fst p) / (1 + snd p))"
        by (rule continuous_on_divide[OF hnum hden])
           (auto simp: top1_unit_interval_def)
      hence "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. max 0 (2 * fst p / (1 + snd p)))"
        by (intro continuous_on_max continuous_on_const)
      hence "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. min 1 (max 0 (2 * fst p / (1 + snd p))))"
        by (intro continuous_on_min continuous_on_const)
      thus ?thesis by (simp add: case_prod_unfold)
    qed
    have hg_top1: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top ?g"
      by (rule top1_continuous_map_on_II_to_I) (use hg_range in auto, rule hg_cont)
    have "f \<circ> ?g = ?F" by (rule ext) (simp add: comp_def case_prod_unfold)
    hence hcomp: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX ?F"
      using top1_continuous_map_on_comp[OF hg_top1 hfcont] by simp
    show ?thesis unfolding II_topology_def using hcomp .
  qed
  have hF_s0: "\<forall>s\<in>I_set. ?F (s, 0) = top1_path_product f (top1_constant_path x1) s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "?F (s, 0) = top1_path_product f (top1_constant_path x1) s"
    proof (cases "s \<le> 1/2")
      case True
      have hs_nn: "s \<ge> 0" using hs unfolding top1_unit_interval_def by simp
      have "2*s / (1 + 0) = 2*s" by simp
      moreover have "2*s \<ge> 0" using hs_nn by simp
      moreover have "2*s \<le> 1" using True by simp
      ultimately have "?g (s, 0) = 2*s" by auto
      hence lhs: "?F (s, 0) = f (2*s)" by simp
      have "top1_path_product f (top1_constant_path x1) s = f (2*s)"
        using True unfolding top1_path_product_def by simp
      thus ?thesis using lhs by simp
    next
      case False
      hence hge: "s > 1/2" by simp
      have "2*s > 1" using hge by simp
      hence "2*s / 1 > 1" by simp
      hence "?g (s, 0) = 1" by auto
      hence lhs: "?F (s, 0) = f 1" by simp
      have "top1_path_product f (top1_constant_path x1) s = top1_constant_path x1 (2*s - 1)"
        using hge unfolding top1_path_product_def by auto
      also have "... = x1" unfolding top1_constant_path_def by simp
      also have "... = f 1" using hf1 by simp
      finally show ?thesis using lhs by simp
    qed
  qed
  have hF_s1: "\<forall>s\<in>I_set. ?F (s, 1) = f s"
  proof
    fix s assume hs: "s \<in> I_set"
    have hs_nn: "s \<ge> 0" using hs unfolding top1_unit_interval_def by simp
    have hs_le1: "s \<le> 1" using hs unfolding top1_unit_interval_def by simp
    have "(2*s) / (1 + 1) = s" by auto
    moreover have "s \<le> 1" using hs_le1 .
    moreover have "s \<ge> 0" using hs_nn .
    ultimately have "?g (s, 1) = s" by auto
    thus "?F (s, 1) = f s" by simp
  qed
  have hF_0t: "\<forall>t\<in>I_set. ?F (0, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "(2*0) / (1 + t) = 0" by simp
    hence "?g (0, t) = 0" by simp
    hence "?F (0, t) = f 0" by simp
    thus "?F (0, t) = x0" using hf0 by simp
  qed
  have hF_1t: "\<forall>t\<in>I_set. ?F (1, t) = x1"
  proof
    fix t assume ht: "t \<in> I_set"
    have ht_nn: "t \<ge> 0" using ht unfolding top1_unit_interval_def by simp
    have "1 + t > 0" using ht_nn by simp
    moreover have "2 / (1 + t) \<ge> 1" using ht unfolding top1_unit_interval_def
      by (simp add: le_divide_eq)
    ultimately have "?g (1, t) = 1" by auto
    hence "?F (1, t) = f 1" by simp
    thus "?F (1, t) = x1" using hf1 by simp
  qed
  have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hx1X: "x1 \<in> X" using hfrange h1I hf1 by force
  have hconst: "top1_is_path_on X TX x1 x1 (top1_constant_path x1)"
    by (rule top1_constant_path_is_path[OF hTX hx1X])
  have hpath_fe: "top1_is_path_on X TX x0 x1 (top1_path_product f (top1_constant_path x1))"
    by (rule top1_path_product_is_path[OF hTX hf hconst])
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hpath_fe hf hF_cont hF_s0 hF_s1 hF_0t hF_1t by blast
qed

lemma Theorem_51_2_invgerse_left:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x0
    (top1_path_product f (top1_path_reverse f)) (top1_constant_path x0)"
proof -
  have hfcont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_path_on_def by blast
  have hfrange: "\<forall>s\<in>I_set. f s \<in> X" using hfcont unfolding top1_continuous_map_on_def by blast
  have hf0: "f 0 = x0" using hf unfolding top1_is_path_on_def by blast
  have hf1: "f 1 = x1" using hf unfolding top1_is_path_on_def by blast
  \<comment> \<open>Homotopy: F(s,t) = f(max(0, min(2s, min(2-2s, 1-t)))).
     At t=0: max(0, min(2s, min(2-2s, 1))) = max(0, min(2s, 2-2s)).
             For s \<le> 1/2: min(2s, 2-2s) = 2s, F = f(2s) = (f*f^{-1})(s) piece 1.
             For s \<ge> 1/2: min(2s, 2-2s) = 2-2s, F = f(2-2s) = (f*f^{-1})(s) piece 2.
     At t=1: max(0, min(2s, min(2-2s, 0))) = max(0, 0) = 0, F = f(0) = x0.
     At s=0: max(0, min(0, min(2, 1-t))) = 0, F = f(0) = x0.
     At s=1: max(0, min(2, min(0, 1-t))) = 0, F = f(0) = x0.\<close>
  define g51 where "g51 \<equiv> \<lambda>(s::real, t::real). max 0 (min (2*s) (min (2 - 2*s) (1 - t)))"
  let ?g = g51
  let ?F = "\<lambda>p. f (?g p)"
  have hg_beta: "\<And>s t. ?g (s, t) = max 0 (min (2*s) (min (2-2*s) (1-t)))"
    unfolding g51_def by simp
  have hg_range: "\<forall>s\<in>I_set. \<forall>t\<in>I_set. ?g (s, t) \<in> I_set"
    unfolding top1_unit_interval_def unfolding g51_def by auto
  have hF_range: "\<forall>p\<in>I_set \<times> I_set. ?F p \<in> X"
  proof
    fix p assume hp: "p \<in> I_set \<times> I_set"
    have "?g p \<in> I_set" using hp hg_range by auto
    thus "?F p \<in> X" using hfrange by blast
  qed
  have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?F"
  proof -
    have hg_cont: "continuous_on (I_set \<times> I_set) ?g"
    proof -
      have h2s: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 2 * fst p)" by (intro continuous_intros)
      have h22s: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 2 - 2 * fst p)" by (intro continuous_intros)
      have h1t: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. 1 - snd p)" by (intro continuous_intros)
      have hmin1: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. min (2 - 2 * fst p) (1 - snd p))"
        by (intro continuous_on_min h22s h1t)
      have hmin2: "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. min (2 * fst p) (min (2 - 2 * fst p) (1 - snd p)))"
        by (intro continuous_on_min h2s hmin1)
      have "continuous_on (I_set \<times> I_set) (\<lambda>p::real\<times>real. max 0 (min (2 * fst p) (min (2 - 2 * fst p) (1 - snd p))))"
        by (intro continuous_on_max continuous_on_const hmin2)
      thus ?thesis unfolding g51_def by (simp only: case_prod_unfold fst_conv snd_conv)
    qed
    have hg_map: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?g p \<in> I_set"
    proof -
      fix p assume hp: "p \<in> I_set \<times> I_set"
      then obtain s t where hst: "p = (s, t)" by (cases p) blast
      have "s \<in> I_set" "t \<in> I_set" using hp hst by (by100 blast)+
      thus "?g p \<in> I_set" using hg_range hst by simp
    qed
    have hg_top1: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top ?g"
      by (rule top1_continuous_map_on_II_to_I[OF hg_map hg_cont])
    have hcomp_raw: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX (f \<circ> ?g)"
      by (rule top1_continuous_map_on_comp[OF hg_top1 hfcont])
    show ?thesis unfolding II_topology_def
      by (rule top1_continuous_map_on_agree[OF hcomp_raw])
         (simp only: comp_def g51_def case_prod_unfold fst_conv snd_conv, simp)
  qed
  have hF_s0: "\<forall>s\<in>I_set. ?F (s, 0) = top1_path_product f (top1_path_reverse f) s"
  proof
    fix s assume hs: "s \<in> I_set"
    have hs_nn: "s \<ge> 0" and hs_le1: "s \<le> 1" using hs unfolding top1_unit_interval_def by auto
    show "?F (s, 0) = top1_path_product f (top1_path_reverse f) s"
    proof (cases "s \<le> 1/2")
      case True
      have hmin: "min (2*s) (min (2 - 2*s) (1 - 0)) = 2*s" using True hs_nn by linarith
      have hg_s0: "?g (s, 0) = 2*s"
        using hg_beta[of s 0] hmin hs_nn by simp
      have lhs: "?F (s, 0) = f (2*s)" using hg_s0 by simp
      have "top1_path_product f (top1_path_reverse f) s = f (2*s)"
        using True unfolding top1_path_product_def by simp
      thus ?thesis using lhs by simp
    next
      case False
      hence hge: "s > 1/2" by simp
      have hmin: "min (2*s) (min (2 - 2*s) 1) = 2 - 2*s" using hge hs_le1 by linarith
      have h2s_nn: "2 - 2*s \<ge> 0" using hs_le1 by linarith
      have hg_s0: "?g (s, 0) = 2 - 2*s"
        using hg_beta[of s 0] hmin h2s_nn by simp
      have lhs: "?F (s, 0) = f (2 - 2*s)" using hg_s0 by simp
      have "top1_path_product f (top1_path_reverse f) s = top1_path_reverse f (2*s - 1)"
        using hge unfolding top1_path_product_def by simp
      also have "... = f (1 - (2*s - 1))" unfolding top1_path_reverse_def by simp
      also have "... = f (2 - 2*s)" by simp
      finally show ?thesis using lhs by simp
    qed
  qed
  have hF_s1: "\<forall>s\<in>I_set. ?F (s, 1) = top1_constant_path x0 s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "min (2*s) (min (2 - 2*s) (0::real)) = 0"
      using hs unfolding top1_unit_interval_def by simp
    hence "?g (s, 1) = 0" using hg_beta[of s 1] by simp
    hence "?F (s, 1) = f 0" by simp
    thus "?F (s, 1) = top1_constant_path x0 s" using hf0 unfolding top1_constant_path_def by simp
  qed
  have hF_0t: "\<forall>t\<in>I_set. ?F (0, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "?g (0, t) = 0" using hg_beta[of 0 t] by simp
    hence "?F (0, t) = f 0" by simp
    thus "?F (0, t) = x0" using hf0 by simp
  qed
  have hF_1t: "\<forall>t\<in>I_set. ?F (1, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "?g (1, t) = 0" using hg_beta[of 1 t] ht unfolding top1_unit_interval_def by auto
    hence "?F (1, t) = f 0" by simp
    thus "?F (1, t) = x0" using hf0 by simp
  qed
  have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hx0X: "x0 \<in> X" using hfrange h0I hf0 by force
  have hrev: "top1_is_path_on X TX x1 x0 (top1_path_reverse f)"
    by (rule top1_path_reverse_is_path[OF hf])
  have hpath_frev: "top1_is_path_on X TX x0 x0 (top1_path_product f (top1_path_reverse f))"
    by (rule top1_path_product_is_path[OF hTX hf hrev])
  have hconst: "top1_is_path_on X TX x0 x0 (top1_constant_path x0)"
    by (rule top1_constant_path_is_path[OF hTX hx0X])
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hpath_frev hconst hF_cont hF_s0 hF_s1 hF_0t hF_1t by blast
qed

lemma Theorem_51_2_invgerse_right:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_reverse f) f) (top1_constant_path x1)"
proof -
  \<comment> \<open>By symmetry: apply invgerse_left to the reversed path f^{-1}: x1 \<rightarrow> x0.\<close>
  have hrev: "top1_is_path_on X TX x1 x0 (top1_path_reverse f)"
    by (rule top1_path_reverse_is_path[OF hf])
  have "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_reverse f) (top1_path_reverse (top1_path_reverse f)))
    (top1_constant_path x1)"
    by (rule Theorem_51_2_invgerse_left[OF hTX hrev])
  moreover have "top1_path_reverse (top1_path_reverse f) = f"
    by (rule top1_path_reverse_twice)
  ultimately show ?thesis by simp
qed

section \<open>\<S>52 The Fundamental Group\<close>

text \<open>A loop at x0: a path starting and ending at x0.\<close>
definition top1_is_loop_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_is_loop_on X TX x0 f \<longleftrightarrow> top1_is_path_on X TX x0 x0 f"

lemma top1_is_loop_on_continuous:
  "top1_is_loop_on X TX x0 f \<Longrightarrow> top1_continuous_map_on I_set I_top X TX f"
  unfolding top1_is_loop_on_def top1_is_path_on_def by blast

lemma top1_is_loop_on_start:
  "top1_is_loop_on X TX x0 f \<Longrightarrow> f 0 = x0"
  unfolding top1_is_loop_on_def top1_is_path_on_def by blast

lemma top1_is_loop_on_end:
  "top1_is_loop_on X TX x0 f \<Longrightarrow> f 1 = x0"
  unfolding top1_is_loop_on_def top1_is_path_on_def by blast

lemma top1_constant_path_is_loop:
  assumes "is_topology_on X TX" and "x \<in> X"
  shows "top1_is_loop_on X TX x (top1_constant_path x)"
  unfolding top1_is_loop_on_def using top1_constant_path_is_path[OF assms] .

text \<open>Product of loops at x0 is a loop at x0.\<close>
lemma top1_path_product_is_loop:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_loop_on X TX x0 f" and hg: "top1_is_loop_on X TX x0 g"
  shows "top1_is_loop_on X TX x0 (top1_path_product f g)"
proof -
  have "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
  moreover have "top1_is_path_on X TX x0 x0 g" using hg unfolding top1_is_loop_on_def .
  ultimately have "top1_is_path_on X TX x0 x0 (top1_path_product f g)"
    by (rule top1_path_product_is_path[OF hTX])
  thus ?thesis unfolding top1_is_loop_on_def .
qed

text \<open>Reverse of a loop is a loop at the same basepoint.\<close>
lemma top1_path_reverse_is_loop:
  assumes hf: "top1_is_loop_on X TX x0 f"
  shows "top1_is_loop_on X TX x0 (top1_path_reverse f)"
proof -
  have "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
  hence "top1_is_path_on X TX x0 x0 (top1_path_reverse f)"
    by (rule top1_path_reverse_is_path)
  thus ?thesis unfolding top1_is_loop_on_def .
qed

text \<open>The path-homotopy equivalence class of a loop is the same as
  path-homotopy equivalence restricted to loops at x0.\<close>
definition top1_loop_equiv_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a
  \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_loop_equiv_on X TX x0 f g \<longleftrightarrow>
     top1_is_loop_on X TX x0 f \<and> top1_is_loop_on X TX x0 g
     \<and> top1_path_homotopic_on X TX x0 x0 f g"

lemma top1_loop_equiv_on_refl:
  assumes "top1_is_loop_on X TX x0 f"
  shows "top1_loop_equiv_on X TX x0 f f"
  unfolding top1_loop_equiv_on_def
  using assms Lemma_51_1_path_homotopic_refl[of X TX x0 x0 f]
  unfolding top1_is_loop_on_def by blast

lemma top1_loop_equiv_on_sym:
  assumes "top1_loop_equiv_on X TX x0 f g"
  shows "top1_loop_equiv_on X TX x0 g f"
  using assms Lemma_51_1_path_homotopic_sym[of X TX x0 x0 f g]
  unfolding top1_loop_equiv_on_def by blast

lemma top1_loop_equiv_on_trans:
  assumes hTX: "is_topology_on X TX"
      and "top1_loop_equiv_on X TX x0 f g"
      and "top1_loop_equiv_on X TX x0 g h"
  shows "top1_loop_equiv_on X TX x0 f h"
  using assms Lemma_51_1_path_homotopic_trans[OF hTX, of x0 x0 f g h]
  unfolding top1_loop_equiv_on_def by blast

text \<open>The set of loops at x0 modulo path homotopy — the carrier of pi_1(X, x0).
  Represented as equivalence classes of loops.\<close>
definition top1_fundamental_group_carrier :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a
  \<Rightarrow> (real \<Rightarrow> 'a) set set" where
  "top1_fundamental_group_carrier X TX x0 =
     { {g. top1_loop_equiv_on X TX x0 f g} | f. top1_is_loop_on X TX x0 f }"

text \<open>Group operation on \<pi>_1(X, x_0): [f] * [g] = [f * g] (path concatenation).
  Well-defined on equivalence classes via Theorem 51.2 operations.\<close>
definition top1_fundamental_group_mul ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow>
   (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a) set" where
  "top1_fundamental_group_mul X TX x0 c1 c2 =
     {h. \<exists>f\<in>c1. \<exists>g\<in>c2. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"

text \<open>Identity element of \<pi>_1(X, x_0): the equivalence class of the constant loop.\<close>
definition top1_fundamental_group_id ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) set" where
  "top1_fundamental_group_id X TX x0 =
     {g. top1_loop_equiv_on X TX x0 (top1_constant_path x0) g}"

text \<open>Inverse in \<pi>_1(X, x_0): [f] \<rightarrow> [reverse f].\<close>
definition top1_fundamental_group_invg ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'a) set" where
  "top1_fundamental_group_invg X TX x0 c =
     {h. \<exists>f\<in>c. top1_loop_equiv_on X TX x0 (top1_path_reverse f) h}"

text \<open>The induced homomorphism on \<pi>_1: for continuous h: (X, x_0) \<rightarrow> (Y, y_0),
  h_*([f]) = [h \<circ> f]. This sends an equivalence class to the class containing h \<circ> f.\<close>
definition top1_fundamental_group_induced_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> 'b
   \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'a) set \<Rightarrow> (real \<Rightarrow> 'b) set" where
  "top1_fundamental_group_induced_on X TX x0 Y TY y0 h c =
     {g. \<exists>f\<in>c. top1_loop_equiv_on Y TY y0 (h \<circ> f) g}"

text \<open>The image subgroup h_*(\<pi>_1(X, x_0)) \<subseteq> \<pi>_1(Y, y_0).\<close>
definition top1_fundamental_group_image_hom ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> 'b
   \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'b) set set" where
  "top1_fundamental_group_image_hom X TX x0 Y TY y0 h =
     (top1_fundamental_group_induced_on X TX x0 Y TY y0 h) `
       (top1_fundamental_group_carrier X TX x0)"

text \<open>Simply connected: path-connected with trivial fundamental group.
  We keep the base definition polymorphic; a strict version is given below.\<close>
definition top1_simply_connected_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_simply_connected_on X TX \<longleftrightarrow>
     top1_path_connected_on X TX \<and>
     (\<forall>x0\<in>X. \<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
        top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0))"

text \<open>Strict version: simply connected in a strict topology.\<close>
definition top1_simply_connected_strict :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_simply_connected_strict X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and> top1_simply_connected_on X TX"

lemma top1_simply_connected_strict_imp:
  "top1_simply_connected_strict X TX \<Longrightarrow> top1_simply_connected_on X TX"
  unfolding top1_simply_connected_strict_def by blast

lemma top1_simply_connected_strict_is_topology_strict:
  "top1_simply_connected_strict X TX \<Longrightarrow> is_topology_on_strict X TX"
  unfolding top1_simply_connected_strict_def by blast

lemma top1_simply_connected_on_path_connected:
  "top1_simply_connected_on X TX \<Longrightarrow> top1_path_connected_on X TX"
  unfolding top1_simply_connected_on_def by blast


text \<open>The fundamental group operation: [f]*[g] = [f*g] on equivalence classes.
  Well-defined by Theorem 51.2.\<close>

text \<open>Homomorphism induced by a continuous map h: (X, x0) \<rightarrow> (Y, y0).\<close>
definition top1_induced_homomorphism_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'b)" where
  "top1_induced_homomorphism_on X TX Y TY h f = h \<circ> f"

text \<open>Congruence: path homotopy is compatible with path product (left and right).\<close>
lemma path_homotopic_product_left:
  assumes hTX: "is_topology_on X TX"
      and hfg: "top1_path_homotopic_on X TX x0 x1 f g"
      and hh: "top1_is_path_on X TX x1 x2 h"
  shows "top1_path_homotopic_on X TX x0 x2 (top1_path_product f h) (top1_path_product g h)"
proof -
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hFs0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hFs1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hF0: "\<forall>t\<in>I_set. F (0, t) = x0" and hF1: "\<forall>t\<in>I_set. F (1, t) = x1"
    using hfg unfolding top1_path_homotopic_on_def by blast
  have hh0: "h 0 = x1" and hh1: "h 1 = x2"
    using hh unfolding top1_is_path_on_def by blast+
  have hhcont: "top1_continuous_map_on I_set I_top X TX h"
    using hh unfolding top1_is_path_on_def by blast
  \<comment> \<open>Define G(s,t) = if s \<le> 1/2 then F(2s, t) else h(2s-1).\<close>
  let ?G = "\<lambda>p::real\<times>real. if fst p \<le> 1/2 then F (2 * fst p, snd p) else h (2 * fst p - 1)"
  have hGcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?G"
  proof -
    let ?As = "{s\<in>I_set. s \<le> 1/2} \<times> I_set"
    let ?Bs = "{s\<in>I_set. s \<ge> 1/2} \<times> I_set"
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
    \<comment> \<open>Reparametrization (2s, t) continuous from As to I\<times>I.\<close>
    have h\<phi>: "top1_continuous_map_on ?As (subspace_topology (I_set \<times> I_set) II_topology ?As)
               (I_set \<times> I_set) II_topology (\<lambda>p. (2 * fst p, snd (p::real\<times>real)))"
    proof -
      have hcont: "continuous_on UNIV (\<lambda>p::real\<times>real. (2 * fst p, snd p))" by (intro continuous_intros)
      have hmap: "\<And>p. p \<in> ?As \<Longrightarrow> (2 * fst p, snd p) \<in> I_set \<times> I_set"
        unfolding top1_unit_interval_def by auto
      have hAs_sub: "?As \<subseteq> I_set \<times> I_set" by auto
      have hraw: "top1_continuous_map_on ?As
                   (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?As)
                   (I_set \<times> I_set) (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set))
                   (\<lambda>p. (2 * fst p, snd p))"
        by (rule top1_continuous_map_on_real2_subspace[OF hmap hcont])
      have hdom: "subspace_topology (I_set \<times> I_set) II_topology ?As
                = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?As"
        unfolding II_topology_def using subspace_topology_trans[OF hAs_sub] II_topology_eq_subspace by simp
      have hcod: "II_topology = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
        unfolding II_topology_def by (rule II_topology_eq_subspace)
      show ?thesis using hraw hdom hcod by simp
    qed
    have hFAs: "top1_continuous_map_on ?As (subspace_topology (I_set \<times> I_set) II_topology ?As) X TX
                 (\<lambda>p. F (2 * fst p, snd p))"
    proof -
      have "F \<circ> (\<lambda>p. (2 * fst p, snd p)) = (\<lambda>p. F (2 * fst p, snd p))" by (rule ext) simp
      thus ?thesis using top1_continuous_map_on_comp[OF h\<phi> hF] by simp
    qed
    \<comment> \<open>h(2s-1) continuous on Bs.\<close>
    have hHBs: "top1_continuous_map_on ?Bs (subspace_topology (I_set \<times> I_set) II_topology ?Bs) X TX
                 (\<lambda>p. h (2 * fst p - 1))"
    proof -
      let ?\<rho>h = "\<lambda>p::real\<times>real. max 0 (min 1 (2 * fst p - 1))"
      have h\<rho>_cont: "continuous_on (I_set \<times> I_set) ?\<rho>h" by (intro continuous_intros)
      have h\<rho>_map: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?\<rho>h p \<in> I_set"
        unfolding top1_unit_interval_def by auto
      have hcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (h \<circ> ?\<rho>h)"
        unfolding II_topology_def
        by (rule top1_continuous_map_on_comp[OF top1_continuous_map_on_II_to_I[OF h\<rho>_map h\<rho>_cont] hhcont])
      have hBs_sub: "?Bs \<subseteq> I_set \<times> I_set" by auto
      have hrestr: "top1_continuous_map_on ?Bs (subspace_topology (I_set \<times> I_set) II_topology ?Bs) X TX (h \<circ> ?\<rho>h)"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF hcomp hBs_sub])
      have hagree: "\<forall>p\<in>?Bs. (h \<circ> ?\<rho>h) p = h (2 * fst p - 1)"
      proof
        fix p assume hp: "p \<in> ?Bs"
        have "fst p \<ge> 1/2" using hp by auto
        hence "2 * fst p - 1 \<ge> 0" by simp
        moreover have "fst p \<le> 1" using hp unfolding top1_unit_interval_def by auto
        hence "2 * fst p - 1 \<le> 1" by simp
        ultimately show "(h \<circ> ?\<rho>h) p = h (2 * fst p - 1)" by (simp add: comp_def)
      qed
      show ?thesis by (rule top1_continuous_map_on_agree[OF hrestr hagree])
    qed
    \<comment> \<open>Agreement of ?G with piece functions.\<close>
    have hG_As: "top1_continuous_map_on ?As (subspace_topology (I_set \<times> I_set) II_topology ?As) X TX ?G"
    proof (rule top1_continuous_map_on_agree[OF hFAs])
      show "\<forall>p\<in>?As. F (2 * fst p, snd p) = ?G p"
      proof
        fix p assume "p \<in> ?As"
        hence "fst p \<le> 1/2" by auto
        thus "F (2 * fst p, snd p) = ?G p" by simp
      qed
    qed
    have hG_Bs: "top1_continuous_map_on ?Bs (subspace_topology (I_set \<times> I_set) II_topology ?Bs) X TX ?G"
    proof (rule top1_continuous_map_on_agree[OF hHBs])
      show "\<forall>p\<in>?Bs. h (2 * fst p - 1) = ?G p"
      proof
        fix p assume hp: "p \<in> ?Bs"
        hence hge: "fst p \<ge> 1/2" by auto
        show "h (2 * fst p - 1) = ?G p"
        proof (cases "fst p = 1/2")
          case True
          have h2fst: "2 * fst p = 1" using True by simp
          hence "?G p = F (1, snd p)" by simp
          also have "... = x1" using hF1 hp by auto
          finally have l: "?G p = x1" .
          have h2m1: "2 * fst p - 1 = (0::real)" using True by simp
          have "h (2 * fst p - 1) = h 0" using h2m1 by simp
          thus ?thesis using l hh0 by simp
        next
          case False
          hence "fst p > 1/2" using hge by simp
          hence "\<not>(fst p \<le> 1/2)" by simp
          thus ?thesis by simp
        qed
      qed
    qed
    \<comment> \<open>Closedness of As, Bs in I\<times>I.\<close>
    have hI_open: "I_set \<in> I_top" using hTI unfolding is_topology_on_def by blast
    have hAs_closed: "closedin_on (I_set \<times> I_set) II_topology ?As"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?As \<subseteq> I_set \<times> I_set" by auto
      have "I_set \<times> I_set - ?As = {s\<in>I_set. s > 1/2} \<times> I_set" unfolding top1_unit_interval_def by auto
      also have "\<dots> \<in> II_topology"
      proof -
        have "{s\<in>I_set. s > 1/2} = I_set \<inter> {s :: real. s > 1/2}"
          unfolding top1_unit_interval_def by auto
        also have "\<dots> \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def
          using open_greaterThan[of "1/2::real"] unfolding top1_open_sets_def greaterThan_def by blast
        finally have "{s\<in>I_set. s > 1/2} \<in> I_top" .
        thus ?thesis unfolding II_topology_def by (rule product_rect_open[OF _ hI_open])
      qed
      finally show "I_set \<times> I_set - ?As \<in> II_topology" .
    qed
    have hBs_closed: "closedin_on (I_set \<times> I_set) II_topology ?Bs"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?Bs \<subseteq> I_set \<times> I_set" by auto
      have "I_set \<times> I_set - ?Bs = {s\<in>I_set. s < 1/2} \<times> I_set" unfolding top1_unit_interval_def by auto
      also have "\<dots> \<in> II_topology"
      proof -
        have "{s\<in>I_set. s < 1/2} = I_set \<inter> {s :: real. s < 1/2}"
          unfolding top1_unit_interval_def by auto
        also have "\<dots> \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def
          using open_lessThan[of "1/2::real"] unfolding top1_open_sets_def lessThan_def by blast
        finally have "{s\<in>I_set. s < 1/2} \<in> I_top" .
        thus ?thesis unfolding II_topology_def by (rule product_rect_open[OF _ hI_open])
      qed
      finally show "I_set \<times> I_set - ?Bs \<in> II_topology" .
    qed
    have hcover: "?As \<union> ?Bs = I_set \<times> I_set" unfolding top1_unit_interval_def by auto
    have hG_range: "\<forall>p\<in>I_set \<times> I_set. ?G p \<in> X"
    proof
      fix p assume hp: "p \<in> I_set \<times> I_set"
      show "?G p \<in> X"
      proof (cases "fst p \<le> 1/2")
        case True
        have "(2 * fst p, snd p) \<in> I_set \<times> I_set"
          using hp True unfolding top1_unit_interval_def by auto
        thus ?thesis using True hF unfolding top1_continuous_map_on_def by simp
      next
        case False
        have "2 * fst p - 1 \<in> I_set"
          using hp False unfolding top1_unit_interval_def by auto
        thus ?thesis using False hhcont unfolding top1_continuous_map_on_def by simp
      qed
    qed
    show ?thesis
      by (rule pasting_lemma_two_closed[OF hTII hTX hAs_closed hBs_closed hcover hG_range hG_As hG_Bs])
  qed
  have hfpath: "top1_is_path_on X TX x0 x1 f"
    using hfg unfolding top1_path_homotopic_on_def by blast
  have hgpath: "top1_is_path_on X TX x0 x1 g"
    using hfg unfolding top1_path_homotopic_on_def by blast
  have hfh: "top1_is_path_on X TX x0 x2 (top1_path_product f h)"
    by (rule top1_path_product_is_path[OF hTX hfpath hh])
  have hgh: "top1_is_path_on X TX x0 x2 (top1_path_product g h)"
    by (rule top1_path_product_is_path[OF hTX hgpath hh])
  have hGs0: "\<forall>s\<in>I_set. ?G (s, 0) = top1_path_product f h s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "?G (s, 0) = top1_path_product f h s"
    proof (cases "s \<le> 1/2")
      case True
      have "2*s \<in> I_set" using hs True unfolding top1_unit_interval_def by simp
      hence "F (2*s, 0) = f (2*s)" using hFs0 by blast
      thus ?thesis using True unfolding top1_path_product_def by simp
    next
      case False thus ?thesis unfolding top1_path_product_def by simp
    qed
  qed
  have hGs1: "\<forall>s\<in>I_set. ?G (s, 1) = top1_path_product g h s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "?G (s, 1) = top1_path_product g h s"
    proof (cases "s \<le> 1/2")
      case True
      have "2*s \<in> I_set" using hs True unfolding top1_unit_interval_def by simp
      hence "F (2*s, 1) = g (2*s)" using hFs1 by blast
      thus ?thesis using True unfolding top1_path_product_def by simp
    next
      case False thus ?thesis unfolding top1_path_product_def by simp
    qed
  qed
  have hG0: "\<forall>t\<in>I_set. ?G (0, t) = x0" using hF0 by simp
  have hG1: "\<forall>t\<in>I_set. ?G (1, t) = x2" using hh1 by simp
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hfh hgh hGcont hGs0 hGs1 hG0 hG1 by blast
qed

lemma path_homotopic_product_right:
  assumes hTX: "is_topology_on X TX"
      and hfg: "top1_path_homotopic_on X TX x1 x2 f g"
      and hh: "top1_is_path_on X TX x0 x1 h"
  shows "top1_path_homotopic_on X TX x0 x2 (top1_path_product h f) (top1_path_product h g)"
proof -
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hFs0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hFs1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hF0: "\<forall>t\<in>I_set. F (0, t) = x1" and hF1: "\<forall>t\<in>I_set. F (1, t) = x2"
    using hfg unfolding top1_path_homotopic_on_def by blast
  have hhcont: "top1_continuous_map_on I_set I_top X TX h"
    using hh unfolding top1_is_path_on_def by blast
  have hh0: "h 0 = x0" and hh1: "h 1 = x1"
    using hh unfolding top1_is_path_on_def by blast+
  let ?G = "\<lambda>p::real\<times>real. if fst p \<le> 1/2 then h (2 * fst p) else F (2 * fst p - 1, snd p)"
  \<comment> \<open>Continuity by spatial pasting (same structure as path_homotopic_product_left).\<close>
  have hGcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX ?G"
  proof -
    let ?As = "{s\<in>I_set. s \<le> 1/2} \<times> I_set"
    let ?Bs = "{s\<in>I_set. s \<ge> 1/2} \<times> I_set"
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
    have hHAs: "top1_continuous_map_on ?As (subspace_topology (I_set \<times> I_set) II_topology ?As) X TX (\<lambda>p. h (2 * fst p))"
    proof -
      let ?\<rho> = "\<lambda>p::real\<times>real. max 0 (min 1 (2 * fst p))"
      have h\<rho>_map: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?\<rho> p \<in> I_set" unfolding top1_unit_interval_def by auto
      have h\<rho>_cont: "continuous_on (I_set \<times> I_set) ?\<rho>" by (intro continuous_intros)
      have hcomp: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (h \<circ> ?\<rho>)"
        unfolding II_topology_def
        by (rule top1_continuous_map_on_comp[OF top1_continuous_map_on_II_to_I[OF h\<rho>_map h\<rho>_cont] hhcont])
      hence hrestr: "top1_continuous_map_on ?As (subspace_topology (I_set \<times> I_set) II_topology ?As) X TX (h \<circ> ?\<rho>)"
        by (rule top1_continuous_map_on_restrict_domain_simple) auto
      show ?thesis by (rule top1_continuous_map_on_agree[OF hrestr]) (auto simp: comp_def top1_unit_interval_def)
    qed
    have hFBs: "top1_continuous_map_on ?Bs (subspace_topology (I_set \<times> I_set) II_topology ?Bs) X TX (\<lambda>p. F (2 * fst p - 1, snd p))"
    proof -
      have hmap: "\<And>p. p \<in> ?Bs \<Longrightarrow> (2 * fst p - 1, snd p) \<in> I_set \<times> I_set" unfolding top1_unit_interval_def by auto
      have hcont: "continuous_on UNIV (\<lambda>p::real\<times>real. (2 * fst p - 1, snd p))" by (intro continuous_intros)
      have hBs_sub: "?Bs \<subseteq> I_set \<times> I_set" by auto
      have hraw: "top1_continuous_map_on ?Bs (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?Bs)
                   (I_set \<times> I_set) (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)) (\<lambda>p. (2 * fst p - 1, snd p))"
        by (rule top1_continuous_map_on_real2_subspace[OF hmap hcont])
      have hdom: "subspace_topology (I_set \<times> I_set) II_topology ?Bs = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?Bs"
        unfolding II_topology_def using subspace_topology_trans[OF hBs_sub] II_topology_eq_subspace by simp
      have hcod: "II_topology = subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)"
        unfolding II_topology_def by (rule II_topology_eq_subspace)
      have h\<phi>: "top1_continuous_map_on ?Bs (subspace_topology (I_set \<times> I_set) II_topology ?Bs) (I_set \<times> I_set) II_topology (\<lambda>p. (2 * fst p - 1, snd p))"
        using hraw hdom hcod by simp
      show ?thesis using top1_continuous_map_on_comp[OF h\<phi> hF] by (simp add: comp_def)
    qed
    have hG_As: "top1_continuous_map_on ?As (subspace_topology (I_set \<times> I_set) II_topology ?As) X TX ?G"
      by (rule top1_continuous_map_on_agree[OF hHAs]) auto
    have hG_Bs: "top1_continuous_map_on ?Bs (subspace_topology (I_set \<times> I_set) II_topology ?Bs) X TX ?G"
    proof (rule top1_continuous_map_on_agree[OF hFBs])
      show "\<forall>p\<in>?Bs. F (2 * fst p - 1, snd p) = ?G p"
      proof
        fix p assume hp: "p \<in> ?Bs"
        show "F (2 * fst p - 1, snd p) = ?G p"
        proof (cases "fst p = 1/2")
          case True
          have h2m1: "2 * fst p - 1 = (0::real)" using True by simp
          have h2fst: "2 * fst p = (1::real)" using True by simp
          have lhs: "F (2 * fst p - 1, snd p) = x1" using h2m1 hF0 hp by auto
          have rhs: "?G p = x1" using True h2fst hh1 by simp
          show ?thesis using lhs rhs by simp
        next
          case False hence "\<not>(fst p \<le> 1/2)" using hp by auto
          thus ?thesis by simp
        qed
      qed
    qed
    have hI_open: "I_set \<in> I_top" using hTI unfolding is_topology_on_def by blast
    have hAs_closed: "closedin_on (I_set \<times> I_set) II_topology ?As"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?As \<subseteq> I_set \<times> I_set" by auto
      have "I_set \<times> I_set - ?As = {s\<in>I_set. s > 1/2} \<times> I_set" unfolding top1_unit_interval_def by auto
      also have "\<dots> \<in> II_topology"
      proof -
        have "open {s :: real. s > 1/2}" by (rule open_Collect_less[OF continuous_on_const continuous_on_id])
        hence "{s :: real. s > 1/2} \<in> top1_open_sets" unfolding top1_open_sets_def by blast
        hence "I_set \<inter> {s. s > 1/2} \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def by blast
        moreover have "{s\<in>I_set. s > 1/2} = I_set \<inter> {s. s > 1/2}" by auto
        ultimately have "{s\<in>I_set. s > 1/2} \<in> I_top" by simp
        thus ?thesis unfolding II_topology_def by (rule product_rect_open[OF _ hI_open])
      qed
      finally show "I_set \<times> I_set - ?As \<in> II_topology" .
    qed
    have hBs_closed: "closedin_on (I_set \<times> I_set) II_topology ?Bs"
      unfolding closedin_on_def
    proof (intro conjI)
      show "?Bs \<subseteq> I_set \<times> I_set" by auto
      have "I_set \<times> I_set - ?Bs = {s\<in>I_set. s < 1/2} \<times> I_set" unfolding top1_unit_interval_def by auto
      also have "\<dots> \<in> II_topology"
      proof -
        have "open {s :: real. s < 1/2}" by (rule open_Collect_less[OF continuous_on_id continuous_on_const])
        hence "{s :: real. s < 1/2} \<in> top1_open_sets" unfolding top1_open_sets_def by blast
        hence "I_set \<inter> {s. s < 1/2} \<in> I_top"
          unfolding top1_unit_interval_topology_def subspace_topology_def by blast
        moreover have "{s\<in>I_set. s < 1/2} = I_set \<inter> {s. s < 1/2}" by auto
        ultimately have "{s\<in>I_set. s < 1/2} \<in> I_top" by simp
        thus ?thesis unfolding II_topology_def by (rule product_rect_open[OF _ hI_open])
      qed
      finally show "I_set \<times> I_set - ?Bs \<in> II_topology" .
    qed
    have hcover: "?As \<union> ?Bs = I_set \<times> I_set" unfolding top1_unit_interval_def by auto
    have hG_range: "\<forall>p\<in>I_set \<times> I_set. ?G p \<in> X"
    proof
      fix p assume hp: "p \<in> I_set \<times> I_set"
      show "?G p \<in> X"
      proof (cases "fst p \<le> 1/2")
        case True
        have "2 * fst p \<in> I_set" using hp True unfolding top1_unit_interval_def by auto
        thus ?thesis using True hhcont unfolding top1_continuous_map_on_def by simp
      next
        case False
        have "(2 * fst p - 1, snd p) \<in> I_set \<times> I_set" using hp False unfolding top1_unit_interval_def by auto
        thus ?thesis using False hF unfolding top1_continuous_map_on_def by simp
      qed
    qed
    show ?thesis
      by (rule pasting_lemma_two_closed[OF hTII hTX hAs_closed hBs_closed hcover hG_range hG_As hG_Bs])
  qed
  have hfpath: "top1_is_path_on X TX x1 x2 f"
    using hfg unfolding top1_path_homotopic_on_def by blast
  have hgpath: "top1_is_path_on X TX x1 x2 g"
    using hfg unfolding top1_path_homotopic_on_def by blast
  have hhf: "top1_is_path_on X TX x0 x2 (top1_path_product h f)"
    by (rule top1_path_product_is_path[OF hTX hh hfpath])
  have hhg: "top1_is_path_on X TX x0 x2 (top1_path_product h g)"
    by (rule top1_path_product_is_path[OF hTX hh hgpath])
  have hGs0: "\<forall>s\<in>I_set. ?G (s, 0) = top1_path_product h f s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "?G (s, 0) = top1_path_product h f s"
    proof (cases "s \<le> 1/2")
      case True thus ?thesis unfolding top1_path_product_def by simp
    next
      case False
      have "2*s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by auto
      thus ?thesis using False hFs0 unfolding top1_path_product_def by simp
    qed
  qed
  have hGs1: "\<forall>s\<in>I_set. ?G (s, 1) = top1_path_product h g s"
  proof
    fix s assume hs: "s \<in> I_set"
    show "?G (s, 1) = top1_path_product h g s"
    proof (cases "s \<le> 1/2")
      case True thus ?thesis unfolding top1_path_product_def by simp
    next
      case False
      have "2*s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by auto
      thus ?thesis using False hFs1 unfolding top1_path_product_def by simp
    qed
  qed
  have hG0: "\<forall>t\<in>I_set. ?G (0, t) = x0" using hh0 by simp
  have hG1: "\<forall>t\<in>I_set. ?G (1, t) = x2" using hF1 by simp
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hhf hhg hGcont hGs0 hGs1 hG0 hG1 by blast
qed

text \<open>Helper: for path-connected spaces, nulhomotopy at one basepoint implies
  simple connectivity (nulhomotopy at all basepoints via basepoint change).\<close>
lemma top1_simply_connected_from_one_point:
  assumes hTX: "is_topology_on X TX"
      and hpc: "top1_path_connected_on X TX"
      and hx0: "x0 \<in> X"
      and hnul: "\<forall>f. top1_is_loop_on X TX x0 f \<longrightarrow>
          top1_path_homotopic_on X TX x0 x0 f (top1_constant_path x0)"
  shows "top1_simply_connected_on X TX"
  unfolding top1_simply_connected_on_def
proof (intro conjI ballI allI impI)
  show "top1_path_connected_on X TX" by (rule hpc)
next
  fix x1 f
  assume hx1: "x1 \<in> X" and hf1: "top1_is_loop_on X TX x1 f"
  \<comment> \<open>Choose path \<alpha> from x0 to x1 (path-connected). Conjugate: \<alpha>\<inverse> * f * \<alpha> is loop at x0.
     By hypothesis, \<alpha>\<inverse> * f * \<alpha> is nulhomotopic. Hence f is nulhomotopic at x1.\<close>
  obtain \<alpha> where h\<alpha>: "top1_is_path_on X TX x0 x1 \<alpha>"
    using hpc hx0 hx1 unfolding top1_path_connected_on_def by (by100 blast)
  \<comment> \<open>Conjugate loop \<alpha>\<inverse> * f * \<alpha> at x0 is nulhomotopic.\<close>
  \<comment> \<open>Conjugate: \<alpha> * f * \<alpha>\<inverse> is a loop at x0.\<close>
  let ?conj = "top1_path_product (top1_path_product \<alpha> f) (top1_path_reverse \<alpha>)"
  have h\<alpha>_rev: "top1_is_path_on X TX x1 x0 (top1_path_reverse \<alpha>)"
    by (rule top1_path_reverse_is_path[OF h\<alpha>])
  have hf_path: "top1_is_path_on X TX x1 x1 f"
    using hf1 unfolding top1_is_loop_on_def .
  have h\<alpha>f: "top1_is_path_on X TX x0 x1 (top1_path_product \<alpha> f)"
    by (rule top1_path_product_is_path[OF hTX h\<alpha> hf_path])
  have hconj_path: "top1_is_path_on X TX x0 x0 ?conj"
    by (rule top1_path_product_is_path[OF hTX h\<alpha>f h\<alpha>_rev])
  have hconj_loop: "top1_is_loop_on X TX x0 ?conj"
    unfolding top1_is_loop_on_def using hconj_path by (by100 simp)
  have hconj_nul: "top1_path_homotopic_on X TX x0 x0 ?conj (top1_constant_path x0)"
    using hnul hconj_loop by (by100 blast)
  \<comment> \<open>From conjugate nulhomotopic, extract f nulhomotopic at x1.
     Proof uses path algebra: ?conj*\<alpha> \<simeq> const*\<alpha> \<simeq> \<alpha> and ?conj*\<alpha> \<simeq> (\<alpha>*f)*const \<simeq> \<alpha>*f,
     so \<alpha>*f \<simeq> \<alpha>, then \<alpha>\<inverse>*(\<alpha>*f) \<simeq> \<alpha>\<inverse>*\<alpha> \<simeq> const and \<alpha>\<inverse>*(\<alpha>*f) \<simeq> f, hence f \<simeq> const.
     Requires: path_homotopic_product_left/right, associativity, identity, inverse.\<close>
  show "top1_path_homotopic_on X TX x1 x1 f (top1_constant_path x1)"
  proof -
    let ?\<alpha>f = "top1_path_product \<alpha> f"
    \<comment> \<open>?conj * \<alpha> \<simeq> const * \<alpha> \<simeq> \<alpha>\<close>
    have s1: "top1_path_homotopic_on X TX x0 x1 (top1_path_product ?conj \<alpha>)
        (top1_path_product (top1_constant_path x0) \<alpha>)"
      by (rule path_homotopic_product_left[OF hTX hconj_nul h\<alpha>])
    have s2: "top1_path_homotopic_on X TX x0 x1
        (top1_path_product (top1_constant_path x0) \<alpha>) \<alpha>"
      by (rule Theorem_51_2_left_identity[OF hTX h\<alpha>])
    have s12: "top1_path_homotopic_on X TX x0 x1 (top1_path_product ?conj \<alpha>) \<alpha>"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTX s1 s2])
    \<comment> \<open>?conj * \<alpha> \<simeq> \<alpha>*f by associativity + inverse + right identity\<close>
    have s3: "top1_path_homotopic_on X TX x0 x1 (top1_path_product ?conj \<alpha>)
        (top1_path_product ?\<alpha>f (top1_path_product (top1_path_reverse \<alpha>) \<alpha>))"
      by (rule Lemma_51_1_path_homotopic_sym[OF
            Theorem_51_2_associativity[OF hTX h\<alpha>f h\<alpha>_rev h\<alpha>]])
    have s4: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_path_reverse \<alpha>) \<alpha>) (top1_constant_path x1)"
      by (rule Theorem_51_2_invgerse_right[OF hTX h\<alpha>])
    have s5: "top1_path_homotopic_on X TX x0 x1
        (top1_path_product ?\<alpha>f (top1_path_product (top1_path_reverse \<alpha>) \<alpha>))
        (top1_path_product ?\<alpha>f (top1_constant_path x1))"
      by (rule path_homotopic_product_right[OF hTX s4 h\<alpha>f])
    have s6: "top1_path_homotopic_on X TX x0 x1
        (top1_path_product ?\<alpha>f (top1_constant_path x1)) ?\<alpha>f"
      by (rule Theorem_51_2_right_identity[OF hTX h\<alpha>f])
    have s35: "top1_path_homotopic_on X TX x0 x1 (top1_path_product ?conj \<alpha>) ?\<alpha>f"
    proof (rule Lemma_51_1_path_homotopic_trans[OF hTX s3])
      show "top1_path_homotopic_on X TX x0 x1
          (top1_path_product ?\<alpha>f (top1_path_product (top1_path_reverse \<alpha>) \<alpha>)) ?\<alpha>f"
        by (rule Lemma_51_1_path_homotopic_trans[OF hTX s5 s6])
    qed
    \<comment> \<open>\<alpha>*f \<simeq> \<alpha>\<close>
    have s35_sym: "top1_path_homotopic_on X TX x0 x1 ?\<alpha>f (top1_path_product ?conj \<alpha>)"
      by (rule Lemma_51_1_path_homotopic_sym[OF s35])
    have h\<alpha>f_\<alpha>: "top1_path_homotopic_on X TX x0 x1 ?\<alpha>f \<alpha>"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTX s35_sym s12])
    \<comment> \<open>\<alpha>\<inverse>*(\<alpha>*f) \<simeq> \<alpha>\<inverse>*\<alpha> \<simeq> const_x1\<close>
    have s7: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_path_reverse \<alpha>) ?\<alpha>f)
        (top1_path_product (top1_path_reverse \<alpha>) \<alpha>)"
      by (rule path_homotopic_product_right[OF hTX h\<alpha>f_\<alpha> h\<alpha>_rev])
    have s78: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_path_reverse \<alpha>) ?\<alpha>f) (top1_constant_path x1)"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTX s7 s4])
    \<comment> \<open>\<alpha>\<inverse>*(\<alpha>*f) \<simeq> (\<alpha>\<inverse>*\<alpha>)*f \<simeq> const*f \<simeq> f\<close>
    have s8a: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_path_reverse \<alpha>) ?\<alpha>f)
        (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) \<alpha>) f)"
      by (rule Theorem_51_2_associativity[OF hTX h\<alpha>_rev h\<alpha> hf_path])
    have s8b: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) \<alpha>) f)
        (top1_path_product (top1_constant_path x1) f)"
      by (rule path_homotopic_product_left[OF hTX s4 hf_path])
    have s8c: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_constant_path x1) f) f"
      by (rule Theorem_51_2_left_identity[OF hTX hf_path])
    have s8: "top1_path_homotopic_on X TX x1 x1
        (top1_path_product (top1_path_reverse \<alpha>) ?\<alpha>f) f"
    proof (rule Lemma_51_1_path_homotopic_trans[OF hTX s8a])
      show "top1_path_homotopic_on X TX x1 x1
          (top1_path_product (top1_path_product (top1_path_reverse \<alpha>) \<alpha>) f) f"
        by (rule Lemma_51_1_path_homotopic_trans[OF hTX s8b s8c])
    qed
    have s8_sym: "top1_path_homotopic_on X TX x1 x1 f
        (top1_path_product (top1_path_reverse \<alpha>) ?\<alpha>f)"
      by (rule Lemma_51_1_path_homotopic_sym[OF s8])
    show ?thesis
      by (rule Lemma_51_1_path_homotopic_trans[OF hTX s8_sym s78])
  qed
qed

text \<open>Change of basepoint map: alpha-hat([f]) = [rev-alpha * f * alpha] where alpha is a path x0 -> x1.\<close>
definition top1_basepoint_change_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> 'a
  \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a)" where
  "top1_basepoint_change_on X TX x0 x1 alpha f =
     top1_path_product (top1_path_reverse alpha) (top1_path_product f alpha)"

(** from \<S>52 Theorem 52.1 (homomorphism part): the basepoint-change map
    \<alpha>-hat preserves the path-product operation up to path homotopy.
    Combined with bijectivity this gives a group isomorphism of \<pi>_1(X, x_0)
    with \<pi>_1(X, x_1). **)
theorem Theorem_52_1:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x0 x1 alpha"
      and hf: "top1_is_loop_on X TX x0 f"
      and hg: "top1_is_loop_on X TX x0 g"
  shows "top1_path_homotopic_on X TX x1 x1
    (top1_basepoint_change_on X TX x0 x1 alpha (top1_path_product f g))
    (top1_path_product
      (top1_basepoint_change_on X TX x0 x1 alpha f)
      (top1_basepoint_change_on X TX x0 x1 alpha g))"
proof -
  let ?aR = "top1_path_reverse alpha"
  have hfp: "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
  have hgp: "top1_is_path_on X TX x0 x0 g" using hg unfolding top1_is_loop_on_def .
  have haR: "top1_is_path_on X TX x1 x0 ?aR" by (rule top1_path_reverse_is_path[OF halpha])
  have hfg: "top1_is_path_on X TX x0 x0 (top1_path_product f g)"
    by (rule top1_path_product_is_path[OF hTX hfp hgp])
  have hfa: "top1_is_path_on X TX x0 x1 (top1_path_product f alpha)"
    by (rule top1_path_product_is_path[OF hTX hfp halpha])
  have hga: "top1_is_path_on X TX x0 x1 (top1_path_product g alpha)"
    by (rule top1_path_product_is_path[OF hTX hgp halpha])
  have hfga: "top1_is_path_on X TX x0 x1 (top1_path_product (top1_path_product f g) alpha)"
    by (rule top1_path_product_is_path[OF hTX hfg halpha])
  have haR_fa: "top1_is_path_on X TX x1 x1 (top1_path_product ?aR (top1_path_product f alpha))"
    by (rule top1_path_product_is_path[OF hTX haR hfa])
  have haR_ga: "top1_is_path_on X TX x1 x1 (top1_path_product ?aR (top1_path_product g alpha))"
    by (rule top1_path_product_is_path[OF hTX haR hga])
  \<comment> \<open>Step 1: (α⁻¹*(f*α)) * (α⁻¹*(g*α)) ≃ α⁻¹ * ((f*α) * (α⁻¹*(g*α))) by assoc.\<close>
  have step1: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha))
                       (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product (top1_path_product f alpha)
                                               (top1_path_product ?aR (top1_path_product g alpha))))"
    by (rule Lemma_51_1_path_homotopic_sym[OF
         Theorem_51_2_associativity[OF hTX haR hfa haR_ga]])
  \<comment> \<open>Steps 2-6 require right congruence (h*f ≃ h*g when f ≃ g) to manipulate
     inside the α⁻¹ * (...) context. Right congruence spatial pasting is blocked
     by build time ceiling. Each step uses assoc/inv/id applied inside.\<close>
  \<comment> \<open>Step 2: α⁻¹ * ((f*α) * (α⁻¹*(g*α))) ≃ α⁻¹ * (f * (α * (α⁻¹*(g*α)))) by right cong + assoc.\<close>
  have haR_ga_path: "top1_is_path_on X TX x1 x1 (top1_path_product ?aR (top1_path_product g alpha))"
    by (rule top1_path_product_is_path[OF hTX haR hga])
  have step2_inner: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product (top1_path_product f alpha) (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product f (top1_path_product alpha (top1_path_product ?aR (top1_path_product g alpha))))"
    by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_associativity[OF hTX hfp halpha haR_ga_path]])
  have step2: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product ?aR (top1_path_product (top1_path_product f alpha) (top1_path_product ?aR (top1_path_product g alpha))))
    (top1_path_product ?aR (top1_path_product f (top1_path_product alpha (top1_path_product ?aR (top1_path_product g alpha)))))"
    by (rule path_homotopic_product_right[OF hTX step2_inner haR])
  \<comment> \<open>Step 3: α * (α⁻¹*(g*α)) ≃ (α*α⁻¹) * (g*α) by assoc.\<close>
  have step3_inner: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product alpha (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha))"
    by (rule Theorem_51_2_associativity[OF hTX halpha haR hga])
  have step3_mid: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_path_product alpha (top1_path_product ?aR (top1_path_product g alpha))))
    (top1_path_product f (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha)))"
    by (rule path_homotopic_product_right[OF hTX step3_inner hfp])
  have step3: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product ?aR (top1_path_product f (top1_path_product alpha (top1_path_product ?aR (top1_path_product g alpha)))))
    (top1_path_product ?aR (top1_path_product f (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha))))"
    by (rule path_homotopic_product_right[OF hTX step3_mid haR])
  \<comment> \<open>Step 4: (α*α⁻¹) ≃ e by inverse.\<close>
  have step4_inv: "top1_path_homotopic_on X TX x0 x0
    (top1_path_product alpha ?aR) (top1_constant_path x0)"
    by (rule Theorem_51_2_invgerse_left[OF hTX halpha])
  have step4_inner: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha))
    (top1_path_product (top1_constant_path x0) (top1_path_product g alpha))"
    by (rule path_homotopic_product_left[OF hTX step4_inv hga])
  have step4_mid: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha)))
    (top1_path_product f (top1_path_product (top1_constant_path x0) (top1_path_product g alpha)))"
    by (rule path_homotopic_product_right[OF hTX step4_inner hfp])
  have step4: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product ?aR (top1_path_product f (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha))))
    (top1_path_product ?aR (top1_path_product f (top1_path_product (top1_constant_path x0) (top1_path_product g alpha))))"
    by (rule path_homotopic_product_right[OF hTX step4_mid haR])
  \<comment> \<open>Step 5: e * (g*α) ≃ (g*α) by left identity.\<close>
  have step5_id: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product (top1_constant_path x0) (top1_path_product g alpha)) (top1_path_product g alpha)"
    by (rule Theorem_51_2_left_identity[OF hTX hga])
  have step5_mid: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_path_product (top1_constant_path x0) (top1_path_product g alpha)))
    (top1_path_product f (top1_path_product g alpha))"
    by (rule path_homotopic_product_right[OF hTX step5_id hfp])
  have step5: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product ?aR (top1_path_product f (top1_path_product (top1_constant_path x0) (top1_path_product g alpha))))
    (top1_path_product ?aR (top1_path_product f (top1_path_product g alpha)))"
    by (rule path_homotopic_product_right[OF hTX step5_mid haR])
  \<comment> \<open>Step 6: f * (g*α) ≃ (f*g) * α by assoc.\<close>
  have step6_inner: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_path_product g alpha))
    (top1_path_product (top1_path_product f g) alpha)"
    by (rule Theorem_51_2_associativity[OF hTX hfp hgp halpha])
  have step6_mid: "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_path_product g alpha))
    (top1_path_product (top1_path_product f g) alpha)"
    using step6_inner .
  have step6: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product ?aR (top1_path_product f (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product (top1_path_product f g) alpha))"
    by (rule path_homotopic_product_right[OF hTX step6_mid haR])
  \<comment> \<open>Chain: RHS ≃ step1 ≃ step2 ≃ step3 ≃ step4 ≃ step5 ≃ step6 = LHS.\<close>
  \<comment> \<open>Chain all 6 steps via transitivity.\<close>
  have chain12: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha)) (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product f (top1_path_product alpha (top1_path_product ?aR (top1_path_product g alpha)))))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX step1 step2])
  have chain123: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha)) (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product f (top1_path_product (top1_path_product alpha ?aR) (top1_path_product g alpha))))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain12 step3])
  have chain1234: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha)) (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product f (top1_path_product (top1_constant_path x0) (top1_path_product g alpha))))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain123 step4])
  have chain12345: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha)) (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product f (top1_path_product g alpha)))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain1234 step5])
  have chain123456: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha)) (top1_path_product ?aR (top1_path_product g alpha)))
    (top1_path_product ?aR (top1_path_product (top1_path_product f g) alpha))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain12345 step6])
  \<comment> \<open>The chain goes from RHS to LHS. Symmetry gives LHS ≃ RHS.\<close>
  have result: "top1_path_homotopic_on X TX x1 x1
    (top1_path_product ?aR (top1_path_product (top1_path_product f g) alpha))
    (top1_path_product (top1_path_product ?aR (top1_path_product f alpha)) (top1_path_product ?aR (top1_path_product g alpha)))"
    by (rule Lemma_51_1_path_homotopic_sym[OF chain123456])
  show ?thesis unfolding top1_basepoint_change_on_def using result .
qed

subsection \<open>Lightweight group-theoretic machinery (needed for \<S>52 onwards)\<close>

text \<open>A group is a 4-tuple (G, mul, e, invg) satisfying associativity,
  left/right identity, and left/right invgerse.
  Definitions placed here (before \<S>52) so Theorem\_52\_1\_iso can unfold them.\<close>
definition top1_is_group_on :: "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> bool" where
  "top1_is_group_on G mul e invg \<longleftrightarrow>
     e \<in> G \<and>
     (\<forall>x\<in>G. \<forall>y\<in>G. mul x y \<in> G) \<and>
     (\<forall>x\<in>G. invg x \<in> G) \<and>
     (\<forall>x\<in>G. \<forall>y\<in>G. \<forall>z\<in>G. mul (mul x y) z = mul x (mul y z)) \<and>
     (\<forall>x\<in>G. mul e x = x \<and> mul x e = x) \<and>
     (\<forall>x\<in>G. mul (invg x) x = e \<and> mul x (invg x) = e)"

text \<open>An abelian group additionally satisfies commutativity.\<close>
definition top1_is_abelian_group_on :: "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> bool" where
  "top1_is_abelian_group_on G mul e invg \<longleftrightarrow>
     top1_is_group_on G mul e invg \<and>
     (\<forall>x\<in>G. \<forall>y\<in>G. mul x y = mul y x)"

text \<open>Group homomorphism: f preserves multiplication (and hence identity and invgerse).\<close>
definition top1_group_hom_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> ('g \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_group_hom_on G mulG H mulH f \<longleftrightarrow>
     (\<forall>x\<in>G. f x \<in> H) \<and>
     (\<forall>x\<in>G. \<forall>y\<in>G. f (mulG x y) = mulH (f x) (f y))"

text \<open>Group isomorphism: bijective homomorphism.\<close>
definition top1_group_iso_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> ('g \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_group_iso_on G mulG H mulH f \<longleftrightarrow>
     top1_group_hom_on G mulG H mulH f \<and>
     bij_betw f G H"

definition top1_groups_isomorphic_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_groups_isomorphic_on G mulG H mulH \<longleftrightarrow>
     (\<exists>f. top1_group_iso_on G mulG H mulH f)"

text \<open>Helper: basepoint change preserves path homotopy (congruence).\<close>
lemma top1_basepoint_change_congruence:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x0 x1 alpha"
      and hf: "top1_is_loop_on X TX x0 f"
      and hf': "top1_is_loop_on X TX x0 f'"
      and hff': "top1_path_homotopic_on X TX x0 x0 f f'"
  shows "top1_path_homotopic_on X TX x1 x1
    (top1_basepoint_change_on X TX x0 x1 alpha f)
    (top1_basepoint_change_on X TX x0 x1 alpha f')"
  unfolding top1_basepoint_change_on_def
proof -
  have hrev: "top1_is_path_on X TX x1 x0 (top1_path_reverse alpha)"
    by (rule top1_path_reverse_is_path[OF halpha])
  \<comment> \<open>Step 1: f * \<alpha> \<simeq> f' * \<alpha> (left congruence)\<close>
  have step1: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product f alpha) (top1_path_product f' alpha)"
    by (rule path_homotopic_product_left[OF hTX hff' halpha])
  \<comment> \<open>Step 2: \<alpha>^{-1} * (f * \<alpha>) \<simeq> \<alpha>^{-1} * (f' * \<alpha>) (right congruence)\<close>
  show "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_reverse alpha) (top1_path_product f alpha))
    (top1_path_product (top1_path_reverse alpha) (top1_path_product f' alpha))"
    by (rule path_homotopic_product_right[OF hTX step1 hrev])
qed

text \<open>Helper: round-trip of basepoint change is homotopic to identity.
  \<alpha>-hat sends loops at x0 to loops at x1 via [f] \<mapsto> [\<alpha>^{-1} * f * \<alpha>].
  The round-trip via \<beta> = \<alpha>^{-1} composes to the identity on equivalence classes.\<close>
lemma top1_basepoint_change_roundtrip:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x0 x1 alpha"
      and hf: "top1_is_loop_on X TX x0 f"
  shows "top1_path_homotopic_on X TX x0 x0 f
    (top1_basepoint_change_on X TX x1 x0 (top1_path_reverse alpha)
      (top1_basepoint_change_on X TX x0 x1 alpha f))"
proof -
  let ?a = alpha and ?ra = "top1_path_reverse alpha" and ?e = "top1_constant_path x0"
  have hfp: "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
  have hra: "top1_is_path_on X TX x1 x0 ?ra"
    by (rule top1_path_reverse_is_path[OF halpha])
  have hfa: "top1_is_path_on X TX x0 x1 (top1_path_product f ?a)"
    by (rule top1_path_product_is_path[OF hTX hfp halpha])
  have hara: "top1_is_path_on X TX x0 x0 (top1_path_product ?a ?ra)"
    by (rule top1_path_product_is_path[OF hTX halpha hra])
  have hrafa: "top1_is_path_on X TX x1 x1 (top1_path_product ?ra (top1_path_product f ?a))"
    by (rule top1_path_product_is_path[OF hTX hra hfa])
  have hrafara: "top1_is_path_on X TX x1 x0
      (top1_path_product (top1_path_product ?ra (top1_path_product f ?a)) ?ra)"
    by (rule top1_path_product_is_path[OF hTX hrafa hra])
  have hx0X: "x0 \<in> X"
  proof -
    have "alpha 0 \<in> X" using halpha unfolding top1_is_path_on_def top1_continuous_map_on_def
      top1_unit_interval_def by auto
    moreover have "alpha 0 = x0" using halpha unfolding top1_is_path_on_def by blast
    ultimately show ?thesis by simp
  qed
  have he: "top1_is_path_on X TX x0 x0 ?e"
    by (rule top1_constant_path_is_path[OF hTX hx0X])
  have hefa: "top1_is_path_on X TX x0 x1 (top1_path_product ?e (top1_path_product f ?a))"
    by (rule top1_path_product_is_path[OF hTX he hfa])
  have harafa: "top1_is_path_on X TX x0 x1
      (top1_path_product (top1_path_product ?a ?ra) (top1_path_product f ?a))"
    by (rule top1_path_product_is_path[OF hTX hara hfa])
  have harafap: "top1_is_path_on X TX x0 x1
      (top1_path_product ?a (top1_path_product ?ra (top1_path_product f ?a)))"
    by (rule top1_path_product_is_path[OF hTX halpha hrafa])
  \<comment> \<open>Chain: f \<simeq> ... \<simeq> a * ((ra * (f * a)) * ra) using 7 groupoid steps.\<close>
  \<comment> \<open>Step 1: f \<simeq> f * e\<close>
  have s1: "top1_path_homotopic_on X TX x0 x0 f (top1_path_product f ?e)"
    by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_right_identity[OF hTX hfp]])
  \<comment> \<open>Step 2: f * e \<simeq> f * (a * ra)\<close>
  have hinv_sym: "top1_path_homotopic_on X TX x0 x0 ?e (top1_path_product ?a ?ra)"
    by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_invgerse_left[OF hTX halpha]])
  have s2: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product f ?e) (top1_path_product f (top1_path_product ?a ?ra))"
    by (rule path_homotopic_product_right[OF hTX hinv_sym hfp])
  \<comment> \<open>Step 3: f * (a * ra) \<simeq> (f * a) * ra\<close>
  have s3: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product f (top1_path_product ?a ?ra))
      (top1_path_product (top1_path_product f ?a) ?ra)"
    by (rule Theorem_51_2_associativity[OF hTX hfp halpha hra])
  \<comment> \<open>Step 4: (f * a) * ra \<simeq> (e * (f * a)) * ra\<close>
  have hlid_sym: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product f ?a) (top1_path_product ?e (top1_path_product f ?a))"
    by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_left_identity[OF hTX hfa]])
  have s4: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product (top1_path_product f ?a) ?ra)
      (top1_path_product (top1_path_product ?e (top1_path_product f ?a)) ?ra)"
    by (rule path_homotopic_product_left[OF hTX hlid_sym hra])
  \<comment> \<open>Step 5: (e * (f * a)) * ra \<simeq> ((a * ra) * (f * a)) * ra\<close>
  have hcong5: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product ?e (top1_path_product f ?a))
      (top1_path_product (top1_path_product ?a ?ra) (top1_path_product f ?a))"
    by (rule path_homotopic_product_left[OF hTX hinv_sym hfa])
  have s5: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product (top1_path_product ?e (top1_path_product f ?a)) ?ra)
      (top1_path_product (top1_path_product (top1_path_product ?a ?ra) (top1_path_product f ?a)) ?ra)"
    by (rule path_homotopic_product_left[OF hTX hcong5 hra])
  \<comment> \<open>Step 6: ((a * ra) * (f * a)) * ra \<simeq> (a * (ra * (f * a))) * ra\<close>
  have hassoc_sym: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product (top1_path_product ?a ?ra) (top1_path_product f ?a))
      (top1_path_product ?a (top1_path_product ?ra (top1_path_product f ?a)))"
    by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_associativity[OF hTX halpha hra hfa]])
  have s6: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product (top1_path_product (top1_path_product ?a ?ra) (top1_path_product f ?a)) ?ra)
      (top1_path_product (top1_path_product ?a (top1_path_product ?ra (top1_path_product f ?a))) ?ra)"
    by (rule path_homotopic_product_left[OF hTX hassoc_sym hra])
  \<comment> \<open>Step 7: (a * (ra * (f * a))) * ra \<simeq> a * ((ra * (f * a)) * ra)\<close>
  have s7: "top1_path_homotopic_on X TX x0 x0
      (top1_path_product (top1_path_product ?a (top1_path_product ?ra (top1_path_product f ?a))) ?ra)
      (top1_path_product ?a (top1_path_product (top1_path_product ?ra (top1_path_product f ?a)) ?ra))"
    by (rule Lemma_51_1_path_homotopic_sym[OF Theorem_51_2_associativity[OF hTX halpha hrafa hra]])
  \<comment> \<open>Chain all 7 steps.\<close>
  have chain12: "top1_path_homotopic_on X TX x0 x0 f
      (top1_path_product f (top1_path_product ?a ?ra))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX s1 s2])
  have chain123: "top1_path_homotopic_on X TX x0 x0 f
      (top1_path_product (top1_path_product f ?a) ?ra)"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain12 s3])
  have chain1234: "top1_path_homotopic_on X TX x0 x0 f
      (top1_path_product (top1_path_product ?e (top1_path_product f ?a)) ?ra)"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain123 s4])
  have chain12345: "top1_path_homotopic_on X TX x0 x0 f
      (top1_path_product (top1_path_product (top1_path_product ?a ?ra) (top1_path_product f ?a)) ?ra)"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain1234 s5])
  have chain123456: "top1_path_homotopic_on X TX x0 x0 f
      (top1_path_product (top1_path_product ?a (top1_path_product ?ra (top1_path_product f ?a))) ?ra)"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain12345 s6])
  have chain1234567: "top1_path_homotopic_on X TX x0 x0 f
      (top1_path_product ?a (top1_path_product (top1_path_product ?ra (top1_path_product f ?a)) ?ra))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX chain123456 s7])
  \<comment> \<open>The target is exactly the expanded basepoint change.\<close>
  have htarget_eq: "top1_basepoint_change_on X TX x1 x0 ?ra
      (top1_basepoint_change_on X TX x0 x1 ?a f)
    = top1_path_product ?a (top1_path_product (top1_path_product ?ra (top1_path_product f ?a)) ?ra)"
    unfolding top1_basepoint_change_on_def top1_path_reverse_twice by rule
  show ?thesis using chain1234567 unfolding htarget_eq .
qed

text \<open>Helper: basepoint change sends loops to loops.\<close>
lemma top1_basepoint_change_is_loop:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x0 x1 alpha"
      and hf: "top1_is_loop_on X TX x0 f"
  shows "top1_is_loop_on X TX x1 (top1_basepoint_change_on X TX x0 x1 alpha f)"
proof -
  have hra: "top1_is_path_on X TX x1 x0 (top1_path_reverse alpha)"
    by (rule top1_path_reverse_is_path[OF halpha])
  have hfp: "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
  have hfa: "top1_is_path_on X TX x0 x1 (top1_path_product f alpha)"
    by (rule top1_path_product_is_path[OF hTX hfp halpha])
  have hresult: "top1_is_path_on X TX x1 x1
      (top1_path_product (top1_path_reverse alpha) (top1_path_product f alpha))"
    by (rule top1_path_product_is_path[OF hTX hra hfa])
  show ?thesis unfolding top1_is_loop_on_def top1_basepoint_change_on_def
    using hresult .
qed

text \<open>Helper: basepoint change preserves loop equivalence.\<close>
lemma top1_basepoint_change_loop_equiv:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x0 x1 alpha"
      and hf: "top1_is_loop_on X TX x0 f"
      and hg: "top1_is_loop_on X TX x0 g"
      and hfg: "top1_loop_equiv_on X TX x0 f g"
  shows "top1_loop_equiv_on X TX x1
    (top1_basepoint_change_on X TX x0 x1 alpha f)
    (top1_basepoint_change_on X TX x0 x1 alpha g)"
proof -
  have hhat_f: "top1_is_loop_on X TX x1 (top1_basepoint_change_on X TX x0 x1 alpha f)"
    by (rule top1_basepoint_change_is_loop[OF hTX halpha hf])
  have hhat_g: "top1_is_loop_on X TX x1 (top1_basepoint_change_on X TX x0 x1 alpha g)"
    by (rule top1_basepoint_change_is_loop[OF hTX halpha hg])
  have hhom: "top1_path_homotopic_on X TX x1 x1
    (top1_basepoint_change_on X TX x0 x1 alpha f)
    (top1_basepoint_change_on X TX x0 x1 alpha g)"
  proof -
    have hff': "top1_path_homotopic_on X TX x0 x0 f g"
      using hfg unfolding top1_loop_equiv_on_def by blast
    show ?thesis by (rule top1_basepoint_change_congruence[OF hTX halpha hf hg hff'])
  qed
  show ?thesis unfolding top1_loop_equiv_on_def using hhat_f hhat_g hhom by blast
qed

text \<open>Helper: mul(class f, class g) = class(f*g) for the fundamental group.\<close>
lemma top1_fundamental_group_mul_class:
  assumes hTX: "is_topology_on X TX"
      and hf: "top1_is_loop_on X TX x0 f"
      and hg: "top1_is_loop_on X TX x0 g"
  shows "top1_fundamental_group_mul X TX x0
      {h. top1_loop_equiv_on X TX x0 f h}
      {h. top1_loop_equiv_on X TX x0 g h}
    = {h. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"
proof (intro set_eqI iffI)
  fix h assume "h \<in> top1_fundamental_group_mul X TX x0
      {h. top1_loop_equiv_on X TX x0 f h} {h. top1_loop_equiv_on X TX x0 g h}"
  then obtain f' g' where hf': "top1_loop_equiv_on X TX x0 f f'"
      and hg': "top1_loop_equiv_on X TX x0 g g'"
      and hfg': "top1_loop_equiv_on X TX x0 (top1_path_product f' g') h"
    unfolding top1_fundamental_group_mul_def by blast
  have hf'_path: "top1_is_path_on X TX x0 x0 f'"
    using hf' unfolding top1_loop_equiv_on_def top1_is_loop_on_def by blast
  have hff': "top1_path_homotopic_on X TX x0 x0 f f'"
    using hf' unfolding top1_loop_equiv_on_def by blast
  have hg_path: "top1_is_path_on X TX x0 x0 g"
    using hg unfolding top1_is_loop_on_def .
  have hfg_step: "top1_path_homotopic_on X TX x0 x0 (top1_path_product f g) (top1_path_product f' g)"
    by (rule path_homotopic_product_left[OF hTX hff' hg_path])
  have hgg': "top1_path_homotopic_on X TX x0 x0 g g'"
    using hg' unfolding top1_loop_equiv_on_def by blast
  have hgg_step: "top1_path_homotopic_on X TX x0 x0 (top1_path_product f' g) (top1_path_product f' g')"
    by (rule path_homotopic_product_right[OF hTX hgg' hf'_path])
  have hprod_hom: "top1_path_homotopic_on X TX x0 x0 (top1_path_product f g) (top1_path_product f' g')"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX hfg_step hgg_step])
  have hfg_loop: "top1_is_loop_on X TX x0 (top1_path_product f g)"
    unfolding top1_is_loop_on_def
    by (rule top1_path_product_is_path[OF hTX])
       (use hf hg in \<open>auto simp: top1_is_loop_on_def\<close>)
  have hfg_equiv: "top1_loop_equiv_on X TX x0 (top1_path_product f g) (top1_path_product f' g')"
    unfolding top1_loop_equiv_on_def
    using hfg_loop hfg' hprod_hom unfolding top1_loop_equiv_on_def by blast
  show "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"
    using top1_loop_equiv_on_trans[OF hTX hfg_equiv hfg'] by simp
next
  fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"
  thus "h \<in> top1_fundamental_group_mul X TX x0
      {h. top1_loop_equiv_on X TX x0 f h} {h. top1_loop_equiv_on X TX x0 g h}"
    unfolding top1_fundamental_group_mul_def
    using top1_loop_equiv_on_refl[OF hf] top1_loop_equiv_on_refl[OF hg] by blast
qed

(** Full Theorem 52.1 (group isomorphism): if X is path-connected, then
    \<pi>_1(X, x_0) \<cong> \<pi>_1(X, x_1) for any two basepoints x_0, x_1 \<in> X. **)
theorem Theorem_52_1_iso:
  assumes hTX: "is_topology_on X TX"
      and hpc: "top1_path_connected_on X TX"
      and hx0: "x0 \<in> X" and hx1: "x1 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier X TX x1)
           (top1_fundamental_group_mul X TX x1)"
proof -
  obtain alpha where halpha: "top1_is_path_on X TX x0 x1 alpha"
    using hpc hx0 hx1 unfolding top1_path_connected_on_def by blast
  let ?hat = "\<lambda>f. top1_basepoint_change_on X TX x0 x1 alpha f"
  let ?ra = "top1_path_reverse alpha"
  let ?hat_inv = "\<lambda>g. top1_basepoint_change_on X TX x1 x0 ?ra g"
  \<comment> \<open>Define \<phi> on equivalence classes.\<close>
  let ?\<phi> = "\<lambda>c. {g. \<exists>f\<in>c. top1_loop_equiv_on X TX x1 (?hat f) g}"
  \<comment> \<open>\<phi> maps carrier(x0) to carrier(x1), is a homomorphism, and is bijective.\<close>
  \<comment> \<open>Key fact: \<phi>(class f) = class(\<alpha>-hat f) for any f in class f.\<close>
  have hphi_class: "\<And>f. top1_is_loop_on X TX x0 f \<Longrightarrow>
    ?\<phi> {g. top1_loop_equiv_on X TX x0 f g} =
    {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
  proof (intro set_eqI iffI)
    fix f g assume hf: "top1_is_loop_on X TX x0 f"
    assume "g \<in> ?\<phi> {h. top1_loop_equiv_on X TX x0 f h}"
    then obtain f' where hf'_eq: "top1_loop_equiv_on X TX x0 f f'"
        and hg_eq: "top1_loop_equiv_on X TX x1 (?hat f') g" by auto
    have hf': "top1_is_loop_on X TX x0 f'" using hf'_eq unfolding top1_loop_equiv_on_def by blast
    have hhat_equiv: "top1_loop_equiv_on X TX x1 (?hat f) (?hat f')"
      by (rule top1_basepoint_change_loop_equiv[OF hTX halpha hf hf' hf'_eq])
    show "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
      using top1_loop_equiv_on_trans[OF hTX hhat_equiv hg_eq] by simp
  next
    fix f g assume hf: "top1_is_loop_on X TX x0 f"
    assume "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
    hence hg: "top1_loop_equiv_on X TX x1 (?hat f) g" by simp
    \<comment> \<open>f itself is in its own class.\<close>
    have "f \<in> {h. top1_loop_equiv_on X TX x0 f h}"
      using top1_loop_equiv_on_refl[OF hf] by simp
    moreover have "top1_loop_equiv_on X TX x1 (?hat f) g" by (rule hg)
    ultimately show "g \<in> ?\<phi> {h. top1_loop_equiv_on X TX x0 f h}" by blast
  qed
  \<comment> \<open>\<phi> maps carrier(x0) into carrier(x1).\<close>
  have hphi_range: "\<forall>c\<in>top1_fundamental_group_carrier X TX x0.
      ?\<phi> c \<in> top1_fundamental_group_carrier X TX x1"
  proof
    fix c assume "c \<in> top1_fundamental_group_carrier X TX x0"
    then obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc: "c = {g. top1_loop_equiv_on X TX x0 f g}"
      unfolding top1_fundamental_group_carrier_def by blast
    have "?\<phi> c = {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
      unfolding hc by (rule hphi_class[OF hf])
    moreover have "top1_is_loop_on X TX x1 (?hat f)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf])
    ultimately show "?\<phi> c \<in> top1_fundamental_group_carrier X TX x1"
      unfolding top1_fundamental_group_carrier_def by blast
  qed
  \<comment> \<open>Injectivity: if \<phi>(c1) = \<phi>(c2) then c1 = c2.\<close>
  have hphi_inj: "inj_on ?\<phi> (top1_fundamental_group_carrier X TX x0)"
  proof (rule inj_onI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
       and heq: "?\<phi> c1 = ?\<phi> c2"
    obtain f1 where hf1: "top1_is_loop_on X TX x0 f1"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on X TX x0 f1 g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain f2 where hf2: "top1_is_loop_on X TX x0 f2"
        and hc2_eq: "c2 = {g. top1_loop_equiv_on X TX x0 f2 g}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    have h1: "?\<phi> c1 = {g. top1_loop_equiv_on X TX x1 (?hat f1) g}"
      unfolding hc1_eq by (rule hphi_class[OF hf1])
    have h2: "?\<phi> c2 = {g. top1_loop_equiv_on X TX x1 (?hat f2) g}"
      unfolding hc2_eq by (rule hphi_class[OF hf2])
    \<comment> \<open>From \<phi>(c1) = \<phi>(c2): class(\<alpha>-hat f1) = class(\<alpha>-hat f2).\<close>
    have hhat_f1_loop: "top1_is_loop_on X TX x1 (?hat f1)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf1])
    have hclass_eq: "{g. top1_loop_equiv_on X TX x1 (?hat f1) g}
        = {g. top1_loop_equiv_on X TX x1 (?hat f2) g}"
      using h1 h2 heq by simp
    have "?hat f1 \<in> {g. top1_loop_equiv_on X TX x1 (?hat f1) g}"
      using top1_loop_equiv_on_refl[OF hhat_f1_loop] by simp
    hence "?hat f1 \<in> {g. top1_loop_equiv_on X TX x1 (?hat f2) g}"
      using hclass_eq by simp
    hence hhat_equiv: "top1_loop_equiv_on X TX x1 (?hat f2) (?hat f1)" by simp
    \<comment> \<open>By roundtrip: f1 \<simeq> \<beta>-hat(\<alpha>-hat f1) and f2 \<simeq> \<beta>-hat(\<alpha>-hat f2).\<close>
    have hra: "top1_is_path_on X TX x1 x0 ?ra" by (rule top1_path_reverse_is_path[OF halpha])
    have hrt1: "top1_path_homotopic_on X TX x0 x0 f1
        (?hat_inv (?hat f1))"
      by (rule top1_basepoint_change_roundtrip[OF hTX halpha hf1])
    have hrt2: "top1_path_homotopic_on X TX x0 x0 f2
        (?hat_inv (?hat f2))"
      by (rule top1_basepoint_change_roundtrip[OF hTX halpha hf2])
    \<comment> \<open>\<beta>-hat preserves the equiv: \<alpha>-hat f2 \<simeq> \<alpha>-hat f1 \<Rightarrow> \<beta>-hat(\<alpha>-hat f2) \<simeq> \<beta>-hat(\<alpha>-hat f1).\<close>
    have hhat_f2_loop: "top1_is_loop_on X TX x1 (?hat f2)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf2])
    have hbeta_equiv: "top1_loop_equiv_on X TX x0
        (?hat_inv (?hat f2)) (?hat_inv (?hat f1))"
      by (rule top1_basepoint_change_loop_equiv[OF hTX hra hhat_f2_loop hhat_f1_loop hhat_equiv])
    \<comment> \<open>Chain: f1 \<simeq> \<beta>(\<alpha>(f1)) \<simeq> \<beta>(\<alpha>(f2)) \<simeq> f2 (backward).\<close>
    have f1_equiv: "top1_loop_equiv_on X TX x0 f1 (?hat_inv (?hat f1))"
      unfolding top1_loop_equiv_on_def using hf1 hrt1
      top1_basepoint_change_is_loop[OF hTX hra hhat_f1_loop] by blast
    have f1_to_f2: "top1_loop_equiv_on X TX x0 f1 (?hat_inv (?hat f2))"
      using top1_loop_equiv_on_trans[OF hTX f1_equiv
        top1_loop_equiv_on_sym[OF hbeta_equiv]] .
    have f2_equiv_sym: "top1_loop_equiv_on X TX x0 (?hat_inv (?hat f2)) f2"
    proof -
      have "top1_loop_equiv_on X TX x0 f2 (?hat_inv (?hat f2))"
        unfolding top1_loop_equiv_on_def using hf2 hrt2
        top1_basepoint_change_is_loop[OF hTX hra hhat_f2_loop] by blast
      thus ?thesis by (rule top1_loop_equiv_on_sym)
    qed
    have f1f2_equiv: "top1_loop_equiv_on X TX x0 f1 f2"
      using top1_loop_equiv_on_trans[OF hTX f1_to_f2 f2_equiv_sym] .
    \<comment> \<open>Hence c1 = c2.\<close>
    show "c1 = c2"
    proof -
      have "\<And>g. top1_loop_equiv_on X TX x0 f1 g \<longleftrightarrow> top1_loop_equiv_on X TX x0 f2 g"
      proof
        fix g assume h: "top1_loop_equiv_on X TX x0 f1 g"
        show "top1_loop_equiv_on X TX x0 f2 g"
          using top1_loop_equiv_on_trans[OF hTX top1_loop_equiv_on_sym[OF f1f2_equiv] h] .
      next
        fix g assume h: "top1_loop_equiv_on X TX x0 f2 g"
        show "top1_loop_equiv_on X TX x0 f1 g"
          using top1_loop_equiv_on_trans[OF hTX f1f2_equiv h] .
      qed
      thus ?thesis unfolding hc1_eq hc2_eq by auto
    qed
  qed
  \<comment> \<open>Surjectivity: for any class at x1, there's a preimage class at x0.\<close>
  have hphi_surj: "?\<phi> ` (top1_fundamental_group_carrier X TX x0)
      = top1_fundamental_group_carrier X TX x1"
  proof (intro set_eqI iffI)
    fix d assume "d \<in> ?\<phi> ` top1_fundamental_group_carrier X TX x0"
    then obtain c where hc: "c \<in> top1_fundamental_group_carrier X TX x0" and hd: "d = ?\<phi> c"
      by blast
    show "d \<in> top1_fundamental_group_carrier X TX x1"
      using hphi_range hc hd by blast
  next
    fix d assume hd: "d \<in> top1_fundamental_group_carrier X TX x1"
    obtain h where hh: "top1_is_loop_on X TX x1 h"
        and hd_eq: "d = {g. top1_loop_equiv_on X TX x1 h g}"
      using hd unfolding top1_fundamental_group_carrier_def by blast
    have hra: "top1_is_path_on X TX x1 x0 ?ra" by (rule top1_path_reverse_is_path[OF halpha])
    let ?g = "?hat_inv h"
    have hg_loop: "top1_is_loop_on X TX x0 ?g"
      by (rule top1_basepoint_change_is_loop[OF hTX hra hh])
    have hg_class: "{f. top1_loop_equiv_on X TX x0 ?g f} \<in>
        top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hg_loop by blast
    \<comment> \<open>\<phi>(class \<beta>-hat h) = class(\<alpha>-hat(\<beta>-hat h)).\<close>
    have hphi_g: "?\<phi> {f. top1_loop_equiv_on X TX x0 ?g f}
        = {g. top1_loop_equiv_on X TX x1 (?hat ?g) g}"
      by (rule hphi_class[OF hg_loop])
    \<comment> \<open>Reverse roundtrip: h \<simeq> \<alpha>-hat(\<beta>-hat h).\<close>
    have hrev_rt: "top1_path_homotopic_on X TX x1 x1 h (?hat (?hat_inv h))"
    proof -
      have hrev_alpha_rev: "top1_path_reverse ?ra = alpha"
        by (simp add: top1_path_reverse_twice)
      have "top1_path_homotopic_on X TX x1 x1 h
          (top1_basepoint_change_on X TX x0 x1 (top1_path_reverse ?ra)
            (top1_basepoint_change_on X TX x1 x0 ?ra h))"
        by (rule top1_basepoint_change_roundtrip[OF hTX hra hh])
      thus ?thesis unfolding hrev_alpha_rev .
    qed
    \<comment> \<open>So class(\<alpha>-hat(\<beta>-hat h)) = class(h) = d.\<close>
    have hequiv: "top1_loop_equiv_on X TX x1 h (?hat ?g)"
      unfolding top1_loop_equiv_on_def
      using hh top1_basepoint_change_is_loop[OF hTX halpha hg_loop] hrev_rt by blast
    have "\<And>g. top1_loop_equiv_on X TX x1 (?hat ?g) g \<longleftrightarrow>
              top1_loop_equiv_on X TX x1 h g"
    proof
      fix g' assume h1: "top1_loop_equiv_on X TX x1 (?hat ?g) g'"
      show "top1_loop_equiv_on X TX x1 h g'"
        by (rule top1_loop_equiv_on_trans[OF hTX hequiv h1])
    next
      fix g' assume h1: "top1_loop_equiv_on X TX x1 h g'"
      have "top1_loop_equiv_on X TX x1 (?hat ?g) h"
        by (rule top1_loop_equiv_on_sym[OF hequiv])
      thus "top1_loop_equiv_on X TX x1 (?hat ?g) g'"
        by (rule top1_loop_equiv_on_trans[OF hTX _ h1])
    qed
    hence hclass_eq: "{g. top1_loop_equiv_on X TX x1 (?hat ?g) g}
        = {g. top1_loop_equiv_on X TX x1 h g}" by auto
    have "?\<phi> {f. top1_loop_equiv_on X TX x0 ?g f} = d"
      unfolding hphi_g hclass_eq hd_eq ..
    thus "d \<in> ?\<phi> ` top1_fundamental_group_carrier X TX x0"
      using hg_class by blast
  qed
  \<comment> \<open>Helper: mul(class f, class g) = class(f*g) for loops f, g at the same basepoint.\<close>
  have hmul_class: "\<And>Y TY y0 f g.
    \<lbrakk>is_topology_on Y TY; top1_is_loop_on Y TY y0 f; top1_is_loop_on Y TY y0 g\<rbrakk> \<Longrightarrow>
    top1_fundamental_group_mul Y TY y0
      {h. top1_loop_equiv_on Y TY y0 f h}
      {h. top1_loop_equiv_on Y TY y0 g h}
    = {h. top1_loop_equiv_on Y TY y0 (top1_path_product f g) h}"
    by (rule top1_fundamental_group_mul_class)
  \<comment> \<open>Homomorphism: \<phi> preserves multiplication.\<close>
  have hphi_hom: "\<forall>c1\<in>top1_fundamental_group_carrier X TX x0.
    \<forall>c2\<in>top1_fundamental_group_carrier X TX x0.
    ?\<phi> (top1_fundamental_group_mul X TX x0 c1 c2) =
    top1_fundamental_group_mul X TX x1 (?\<phi> c1) (?\<phi> c2)"
  proof (intro ballI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
    obtain f1 where hf1: "top1_is_loop_on X TX x0 f1"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on X TX x0 f1 g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain f2 where hf2: "top1_is_loop_on X TX x0 f2"
        and hc2_eq: "c2 = {g. top1_loop_equiv_on X TX x0 f2 g}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    \<comment> \<open>mul(c1, c2) = class(f1 * f2).\<close>
    have hf1f2: "top1_is_loop_on X TX x0 (top1_path_product f1 f2)"
      unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF hTX])
         (use hf1 hf2 in \<open>auto simp: top1_is_loop_on_def\<close>)
    have hmul_eq: "top1_fundamental_group_mul X TX x0 c1 c2
        = {h. top1_loop_equiv_on X TX x0 (top1_path_product f1 f2) h}"
      unfolding hc1_eq hc2_eq by (rule hmul_class[OF hTX hf1 hf2])
    \<comment> \<open>\<phi>(mul) = class(\<alpha>-hat(f1*f2)).\<close>
    have hphi_mul: "?\<phi> (top1_fundamental_group_mul X TX x0 c1 c2)
        = {g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product f1 f2)) g}"
      unfolding hmul_eq by (rule hphi_class[OF hf1f2])
    \<comment> \<open>mul(\<phi> c1, \<phi> c2) = class(\<alpha>-hat(f1) * \<alpha>-hat(f2)).\<close>
    have hhat_f1: "top1_is_loop_on X TX x1 (?hat f1)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf1])
    have hhat_f2: "top1_is_loop_on X TX x1 (?hat f2)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf2])
    have hphi_c1: "?\<phi> c1 = {g. top1_loop_equiv_on X TX x1 (?hat f1) g}"
      unfolding hc1_eq by (rule hphi_class[OF hf1])
    have hphi_c2: "?\<phi> c2 = {g. top1_loop_equiv_on X TX x1 (?hat f2) g}"
      unfolding hc2_eq by (rule hphi_class[OF hf2])
    have hmul_phi: "top1_fundamental_group_mul X TX x1 (?\<phi> c1) (?\<phi> c2)
        = {h. top1_loop_equiv_on X TX x1 (top1_path_product (?hat f1) (?hat f2)) h}"
      unfolding hphi_c1 hphi_c2 by (rule hmul_class[OF hTX hhat_f1 hhat_f2])
    \<comment> \<open>By Theorem 52.1: \<alpha>-hat(f1*f2) \<simeq> \<alpha>-hat(f1) * \<alpha>-hat(f2).\<close>
    have hThm: "top1_path_homotopic_on X TX x1 x1
        (?hat (top1_path_product f1 f2))
        (top1_path_product (?hat f1) (?hat f2))"
      by (rule Theorem_52_1[OF hTX halpha hf1 hf2])
    \<comment> \<open>Hence the classes are equal.\<close>
    have hhat_f1f2: "top1_is_loop_on X TX x1 (?hat (top1_path_product f1 f2))"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf1f2])
    have hprod_loop: "top1_is_loop_on X TX x1 (top1_path_product (?hat f1) (?hat f2))"
      unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF hTX])
         (use hhat_f1 hhat_f2 in \<open>auto simp: top1_is_loop_on_def\<close>)
    have hequiv: "top1_loop_equiv_on X TX x1
        (?hat (top1_path_product f1 f2)) (top1_path_product (?hat f1) (?hat f2))"
      unfolding top1_loop_equiv_on_def using hhat_f1f2 hprod_loop hThm by blast
    have hclass_eq: "{g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product f1 f2)) g}
        = {g. top1_loop_equiv_on X TX x1 (top1_path_product (?hat f1) (?hat f2)) g}"
    proof (intro set_eqI iffI)
      fix g assume "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product f1 f2)) g}"
      hence "top1_loop_equiv_on X TX x1 (?hat (top1_path_product f1 f2)) g" by simp
      thus "g \<in> {g. top1_loop_equiv_on X TX x1 (top1_path_product (?hat f1) (?hat f2)) g}"
        using top1_loop_equiv_on_trans[OF hTX top1_loop_equiv_on_sym[OF hequiv]] by simp
    next
      fix g assume "g \<in> {g. top1_loop_equiv_on X TX x1 (top1_path_product (?hat f1) (?hat f2)) g}"
      hence "top1_loop_equiv_on X TX x1 (top1_path_product (?hat f1) (?hat f2)) g" by simp
      thus "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product f1 f2)) g}"
        using top1_loop_equiv_on_trans[OF hTX hequiv] by simp
    qed
    show "?\<phi> (top1_fundamental_group_mul X TX x0 c1 c2) =
          top1_fundamental_group_mul X TX x1 (?\<phi> c1) (?\<phi> c2)"
      unfolding hphi_mul hmul_phi hclass_eq ..
  qed
  have hiso: "top1_group_iso_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier X TX x1)
      (top1_fundamental_group_mul X TX x1) ?\<phi>"
    unfolding top1_group_iso_on_def top1_group_hom_on_def bij_betw_def
    using hphi_range hphi_hom hphi_inj hphi_surj by blast
  show ?thesis
    unfolding top1_groups_isomorphic_on_def using hiso by blast
qed

text \<open>Path-specific version: given a specific path, the basepoint change is an iso.
  Follows from Theorem\_52\_1\_iso since a path between two points implies
  they are in a common path-component.\<close>
corollary basepoint_change_iso_via_path:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x0 x1 alpha"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier X TX x1)
           (top1_fundamental_group_mul X TX x1)"
proof -
  \<comment> \<open>Same proof as Theorem\_52\_1\_iso but starting from a given path.\<close>
  let ?hat = "\<lambda>f. top1_basepoint_change_on X TX x0 x1 alpha f"
  let ?ra = "top1_path_reverse alpha"
  let ?hat_inv = "\<lambda>g. top1_basepoint_change_on X TX x1 x0 ?ra g"
  let ?\<phi> = "\<lambda>c. {g. \<exists>f\<in>c. top1_loop_equiv_on X TX x1 (?hat f) g}"
  have hphi_class: "\<And>f. top1_is_loop_on X TX x0 f \<Longrightarrow>
    ?\<phi> {g. top1_loop_equiv_on X TX x0 f g} =
    {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
  proof (intro set_eqI iffI)
    fix f g assume hf: "top1_is_loop_on X TX x0 f"
    assume "g \<in> ?\<phi> {h. top1_loop_equiv_on X TX x0 f h}"
    then obtain f' where hf'_eq: "top1_loop_equiv_on X TX x0 f f'"
        and hg_eq: "top1_loop_equiv_on X TX x1 (?hat f') g" by auto
    have hf': "top1_is_loop_on X TX x0 f'" using hf'_eq unfolding top1_loop_equiv_on_def by blast
    show "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
      using top1_loop_equiv_on_trans[OF hTX
        top1_basepoint_change_loop_equiv[OF hTX halpha hf hf' hf'_eq] hg_eq] by simp
  next
    fix f g assume hf: "top1_is_loop_on X TX x0 f"
    assume "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat f) g}"
    thus "g \<in> ?\<phi> {h. top1_loop_equiv_on X TX x0 f h}"
      using top1_loop_equiv_on_refl[OF hf] by blast
  qed
  have hphi_range: "\<forall>c\<in>top1_fundamental_group_carrier X TX x0.
      ?\<phi> c \<in> top1_fundamental_group_carrier X TX x1"
  proof
    fix c assume "c \<in> top1_fundamental_group_carrier X TX x0"
    then obtain f where hf: "top1_is_loop_on X TX x0 f"
        and hc: "c = {g. top1_loop_equiv_on X TX x0 f g}"
      unfolding top1_fundamental_group_carrier_def by blast
    show "?\<phi> c \<in> top1_fundamental_group_carrier X TX x1"
      unfolding hc hphi_class[OF hf] top1_fundamental_group_carrier_def
      using top1_basepoint_change_is_loop[OF hTX halpha hf] by blast
  qed
  have hphi_inj: "inj_on ?\<phi> (top1_fundamental_group_carrier X TX x0)"
  proof (rule inj_onI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
       and heq: "?\<phi> c1 = ?\<phi> c2"
    obtain f1 where hf1: "top1_is_loop_on X TX x0 f1"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on X TX x0 f1 g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain f2 where hf2: "top1_is_loop_on X TX x0 f2"
        and hc2_eq: "c2 = {g. top1_loop_equiv_on X TX x0 f2 g}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    have hclass_eq: "{g. top1_loop_equiv_on X TX x1 (?hat f1) g}
        = {g. top1_loop_equiv_on X TX x1 (?hat f2) g}"
      using heq unfolding hc1_eq hc2_eq hphi_class[OF hf1] hphi_class[OF hf2] .
    have hhat_f1_loop: "top1_is_loop_on X TX x1 (?hat f1)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf1])
    have "?hat f1 \<in> {g. top1_loop_equiv_on X TX x1 (?hat f1) g}"
      using top1_loop_equiv_on_refl[OF hhat_f1_loop] by simp
    hence "?hat f1 \<in> {g. top1_loop_equiv_on X TX x1 (?hat f2) g}"
      using hclass_eq by simp
    hence hhat_equiv: "top1_loop_equiv_on X TX x1 (?hat f2) (?hat f1)" by simp
    have hra: "top1_is_path_on X TX x1 x0 ?ra" by (rule top1_path_reverse_is_path[OF halpha])
    have hhat_f2_loop: "top1_is_loop_on X TX x1 (?hat f2)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hf2])
    have hbeta_equiv: "top1_loop_equiv_on X TX x0 (?hat_inv (?hat f2)) (?hat_inv (?hat f1))"
      by (rule top1_basepoint_change_loop_equiv[OF hTX hra hhat_f2_loop hhat_f1_loop hhat_equiv])
    have f1_equiv: "top1_loop_equiv_on X TX x0 f1 (?hat_inv (?hat f1))"
      unfolding top1_loop_equiv_on_def using hf1
        top1_basepoint_change_roundtrip[OF hTX halpha hf1]
        top1_basepoint_change_is_loop[OF hTX hra hhat_f1_loop] by blast
    have f1_to_f2: "top1_loop_equiv_on X TX x0 f1 (?hat_inv (?hat f2))"
      using top1_loop_equiv_on_trans[OF hTX f1_equiv
        top1_loop_equiv_on_sym[OF hbeta_equiv]] .
    have f2_equiv_sym: "top1_loop_equiv_on X TX x0 (?hat_inv (?hat f2)) f2"
      by (rule top1_loop_equiv_on_sym)
         (unfold top1_loop_equiv_on_def, use hf2
           top1_basepoint_change_roundtrip[OF hTX halpha hf2]
           top1_basepoint_change_is_loop[OF hTX hra hhat_f2_loop] in blast)
    have f1f2_equiv: "top1_loop_equiv_on X TX x0 f1 f2"
      using top1_loop_equiv_on_trans[OF hTX f1_to_f2 f2_equiv_sym] .
    show "c1 = c2"
    proof -
      have "\<And>g. top1_loop_equiv_on X TX x0 f1 g \<longleftrightarrow> top1_loop_equiv_on X TX x0 f2 g"
      proof
        fix g assume "top1_loop_equiv_on X TX x0 f1 g"
        thus "top1_loop_equiv_on X TX x0 f2 g"
          using top1_loop_equiv_on_trans[OF hTX top1_loop_equiv_on_sym[OF f1f2_equiv]] by blast
      next
        fix g assume "top1_loop_equiv_on X TX x0 f2 g"
        thus "top1_loop_equiv_on X TX x0 f1 g"
          using top1_loop_equiv_on_trans[OF hTX f1f2_equiv] by blast
      qed
      thus ?thesis unfolding hc1_eq hc2_eq by auto
    qed
  qed
  have hphi_surj: "?\<phi> ` (top1_fundamental_group_carrier X TX x0)
      = top1_fundamental_group_carrier X TX x1"
  proof (intro set_eqI iffI)
    fix d assume "d \<in> ?\<phi> ` top1_fundamental_group_carrier X TX x0"
    thus "d \<in> top1_fundamental_group_carrier X TX x1"
      using hphi_range by blast
  next
    fix d assume hd: "d \<in> top1_fundamental_group_carrier X TX x1"
    obtain h where hh: "top1_is_loop_on X TX x1 h"
        and hd_eq: "d = {g. top1_loop_equiv_on X TX x1 h g}"
      using hd unfolding top1_fundamental_group_carrier_def by blast
    have hra: "top1_is_path_on X TX x1 x0 ?ra" by (rule top1_path_reverse_is_path[OF halpha])
    let ?g = "?hat_inv h"
    have hg_loop: "top1_is_loop_on X TX x0 ?g"
      by (rule top1_basepoint_change_is_loop[OF hTX hra hh])
    have hphi_g: "?\<phi> {f. top1_loop_equiv_on X TX x0 ?g f}
        = {g. top1_loop_equiv_on X TX x1 (?hat ?g) g}"
      by (rule hphi_class[OF hg_loop])
    have hrev_rt: "top1_path_homotopic_on X TX x1 x1 h (?hat (?hat_inv h))"
      using top1_basepoint_change_roundtrip[OF hTX hra hh]
      unfolding top1_path_reverse_twice .
    have hequiv: "top1_loop_equiv_on X TX x1 h (?hat ?g)"
      unfolding top1_loop_equiv_on_def
      using hh top1_basepoint_change_is_loop[OF hTX halpha hg_loop] hrev_rt by blast
    have hclass_eq: "{g. top1_loop_equiv_on X TX x1 (?hat ?g) g}
        = {g. top1_loop_equiv_on X TX x1 h g}"
    proof (intro set_eqI iffI)
      fix g' assume "g' \<in> {g. top1_loop_equiv_on X TX x1 (?hat ?g) g}"
      thus "g' \<in> {g. top1_loop_equiv_on X TX x1 h g}"
        using top1_loop_equiv_on_trans[OF hTX hequiv] by simp
    next
      fix g' assume "g' \<in> {g. top1_loop_equiv_on X TX x1 h g}"
      hence "top1_loop_equiv_on X TX x1 h g'" by simp
      thus "g' \<in> {g. top1_loop_equiv_on X TX x1 (?hat ?g) g}"
        using top1_loop_equiv_on_trans[OF hTX top1_loop_equiv_on_sym[OF hequiv]] by simp
    qed
    have "?\<phi> {f. top1_loop_equiv_on X TX x0 ?g f} = d"
      unfolding hphi_g hclass_eq hd_eq ..
    moreover have "{f. top1_loop_equiv_on X TX x0 ?g f} \<in>
        top1_fundamental_group_carrier X TX x0"
      unfolding top1_fundamental_group_carrier_def using hg_loop by blast
    ultimately show "d \<in> ?\<phi> ` top1_fundamental_group_carrier X TX x0" by blast
  qed
  have hmul_class: "\<And>Y TY y0 f g.
    \<lbrakk>is_topology_on Y TY; top1_is_loop_on Y TY y0 f; top1_is_loop_on Y TY y0 g\<rbrakk> \<Longrightarrow>
    top1_fundamental_group_mul Y TY y0
      {h. top1_loop_equiv_on Y TY y0 f h} {h. top1_loop_equiv_on Y TY y0 g h}
    = {h. top1_loop_equiv_on Y TY y0 (top1_path_product f g) h}"
    by (rule top1_fundamental_group_mul_class)
  have hphi_hom: "\<forall>c1\<in>top1_fundamental_group_carrier X TX x0.
    \<forall>c2\<in>top1_fundamental_group_carrier X TX x0.
    ?\<phi> (top1_fundamental_group_mul X TX x0 c1 c2) =
    top1_fundamental_group_mul X TX x1 (?\<phi> c1) (?\<phi> c2)"
  proof (intro ballI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier X TX x0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier X TX x0"
    obtain l1 where hl1: "top1_is_loop_on X TX x0 l1"
        and hc1_eq: "c1 = {g. top1_loop_equiv_on X TX x0 l1 g}"
      using hc1 unfolding top1_fundamental_group_carrier_def by blast
    obtain l2 where hl2: "top1_is_loop_on X TX x0 l2"
        and hc2_eq: "c2 = {g. top1_loop_equiv_on X TX x0 l2 g}"
      using hc2 unfolding top1_fundamental_group_carrier_def by blast
    have hl12: "top1_is_loop_on X TX x0 (top1_path_product l1 l2)"
      unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF hTX])
         (use hl1 hl2 in \<open>auto simp: top1_is_loop_on_def\<close>)
    have hmul_eq: "top1_fundamental_group_mul X TX x0 c1 c2
        = {h. top1_loop_equiv_on X TX x0 (top1_path_product l1 l2) h}"
      unfolding hc1_eq hc2_eq by (rule hmul_class[OF hTX hl1 hl2])
    have hLHS: "?\<phi> (top1_fundamental_group_mul X TX x0 c1 c2)
        = {g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product l1 l2)) g}"
      unfolding hmul_eq by (rule hphi_class[OF hl12])
    have hhat_l1: "top1_is_loop_on X TX x1 (?hat l1)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hl1])
    have hhat_l2: "top1_is_loop_on X TX x1 (?hat l2)"
      by (rule top1_basepoint_change_is_loop[OF hTX halpha hl2])
    have hphi_c1: "?\<phi> c1 = {g. top1_loop_equiv_on X TX x1 (?hat l1) g}"
      unfolding hc1_eq by (rule hphi_class[OF hl1])
    have hphi_c2: "?\<phi> c2 = {g. top1_loop_equiv_on X TX x1 (?hat l2) g}"
      unfolding hc2_eq by (rule hphi_class[OF hl2])
    have hRHS: "top1_fundamental_group_mul X TX x1 (?\<phi> c1) (?\<phi> c2)
        = {h. top1_loop_equiv_on X TX x1 (top1_path_product (?hat l1) (?hat l2)) h}"
      unfolding hphi_c1 hphi_c2 by (rule hmul_class[OF hTX hhat_l1 hhat_l2])
    have hThm: "top1_path_homotopic_on X TX x1 x1
        (?hat (top1_path_product l1 l2))
        (top1_path_product (?hat l1) (?hat l2))"
      by (rule Theorem_52_1[OF hTX halpha hl1 hl2])
    have hprod_loop: "top1_is_loop_on X TX x1 (top1_path_product (?hat l1) (?hat l2))"
      unfolding top1_is_loop_on_def
      by (rule top1_path_product_is_path[OF hTX])
         (use hhat_l1 hhat_l2 in \<open>auto simp: top1_is_loop_on_def\<close>)
    have hequiv': "top1_loop_equiv_on X TX x1
        (?hat (top1_path_product l1 l2)) (top1_path_product (?hat l1) (?hat l2))"
      unfolding top1_loop_equiv_on_def
      using top1_basepoint_change_is_loop[OF hTX halpha hl12] hprod_loop hThm by blast
    have hclass_eq': "{g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product l1 l2)) g}
        = {g. top1_loop_equiv_on X TX x1 (top1_path_product (?hat l1) (?hat l2)) g}"
    proof (intro set_eqI iffI)
      fix g assume "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product l1 l2)) g}"
      thus "g \<in> {g. top1_loop_equiv_on X TX x1 (top1_path_product (?hat l1) (?hat l2)) g}"
        using top1_loop_equiv_on_trans[OF hTX top1_loop_equiv_on_sym[OF hequiv']] by simp
    next
      fix g assume "g \<in> {g. top1_loop_equiv_on X TX x1 (top1_path_product (?hat l1) (?hat l2)) g}"
      thus "g \<in> {g. top1_loop_equiv_on X TX x1 (?hat (top1_path_product l1 l2)) g}"
        using top1_loop_equiv_on_trans[OF hTX hequiv'] by simp
    qed
    show "?\<phi> (top1_fundamental_group_mul X TX x0 c1 c2) =
          top1_fundamental_group_mul X TX x1 (?\<phi> c1) (?\<phi> c2)"
      unfolding hLHS hRHS hclass_eq' ..
  qed
  have hiso: "top1_group_iso_on
      (top1_fundamental_group_carrier X TX x0)
      (top1_fundamental_group_mul X TX x0)
      (top1_fundamental_group_carrier X TX x1)
      (top1_fundamental_group_mul X TX x1) ?\<phi>"
    unfolding top1_group_iso_on_def top1_group_hom_on_def bij_betw_def
    using hphi_range hphi_hom hphi_inj hphi_surj by blast
  show ?thesis
    unfolding top1_groups_isomorphic_on_def using hiso by blast
qed

text \<open>Functoriality of fundamental group: (k o h)_* = k_* o h_*.\<close>
(** from \<S>52 Theorem 52.4 **)
theorem Theorem_52_4_composition:
  assumes "top1_continuous_map_on X TX Y TY h"
      and "top1_continuous_map_on Y TY Z TZ k"
      and "top1_is_loop_on X TX x0 f"
  shows "top1_induced_homomorphism_on X TX Z TZ (k \<circ> h) f =
         top1_induced_homomorphism_on Y TY Z TZ k
           (top1_induced_homomorphism_on X TX Y TY h f)"
  unfolding top1_induced_homomorphism_on_def by (simp add: comp_assoc)

theorem Theorem_52_4_identity:
  assumes "top1_is_loop_on X TX x0 f"
  shows "top1_induced_homomorphism_on X TX X TX id f = f"
  unfolding top1_induced_homomorphism_on_def by simp

section \<open>\<S>53 Covering Spaces\<close>

text \<open>Evenly covered: an open U \<subseteq> B is evenly covered by p: E \<rightarrow> B if
  p\<invgerse>(U) is a disjoint union of open V\<alpha> \<subseteq> E, each mapped homeomorphically by p.
  Uses openin_on: each V is open in E and a subset of E.\<close>
definition top1_evenly_covered_on :: "'e set \<Rightarrow> 'e set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> bool" where
  "top1_evenly_covered_on E TE B TB p U \<longleftrightarrow>
     openin_on B TB U \<and>
     (\<exists>\<V>. (\<forall>V\<in>\<V>. openin_on E TE V) \<and>
          (\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}) \<and>
          {x\<in>E. p x \<in> U} = \<Union>\<V> \<and>
          (\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                       (subspace_topology B TB U) p))"

text \<open>Covering map: every point of B has a neighborhood evenly covered by p.\<close>
definition top1_covering_map_on :: "'e set \<Rightarrow> 'e set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_covering_map_on E TE B TB p \<longleftrightarrow>
     top1_continuous_map_on E TE B TB p \<and>
     p ` E = B \<and>
     (\<forall>b\<in>B. \<exists>U. b \<in> U \<and> top1_evenly_covered_on E TE B TB p U)"

lemma top1_covering_map_on_continuous:
  "top1_covering_map_on E TE B TB p \<Longrightarrow> top1_continuous_map_on E TE B TB p"
  unfolding top1_covering_map_on_def by blast

lemma top1_covering_map_on_surj:
  "top1_covering_map_on E TE B TB p \<Longrightarrow> p ` E = B"
  unfolding top1_covering_map_on_def by blast

lemma top1_covering_map_on_evenly_covered:
  "top1_covering_map_on E TE B TB p \<Longrightarrow> b \<in> B \<Longrightarrow>
    \<exists>U. b \<in> U \<and> top1_evenly_covered_on E TE B TB p U"
  unfolding top1_covering_map_on_def by blast

text \<open>Helper: evenly-covered U is open (by definition).\<close>
lemma top1_evenly_covered_on_openin_on:
  assumes "top1_evenly_covered_on E TE B TB p U"
  shows "openin_on B TB U"
proof -
  from assms have "openin_on B TB U \<and>
     (\<exists>\<V>. (\<forall>V\<in>\<V>. openin_on E TE V) \<and>
          (\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}) \<and>
          {x\<in>E. p x \<in> U} = \<Union>\<V> \<and>
          (\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                       (subspace_topology B TB U) p))"
    unfolding top1_evenly_covered_on_def .
  thus ?thesis by (rule conjunct1)
qed

text \<open>In a strict cover, every open cover point has an open neighborhood.\<close>
lemma top1_covering_map_on_strict_evenly_covered_openin:
  assumes "top1_covering_map_on E TE B TB p"
  and "b \<in> B"
  shows "\<exists>U. b \<in> U \<and> openin_on B TB U"
proof -
  obtain U where hbU: "b \<in> U" and hec: "top1_evenly_covered_on E TE B TB p U"
    using top1_covering_map_on_evenly_covered[OF assms] by blast
  have "openin_on B TB U" by (rule top1_evenly_covered_on_openin_on[OF hec])
  thus ?thesis using hbU by blast
qed

text \<open>Lifting of a continuous map: f\<tilde>: X \<rightarrow> E with p \<circ> f\<tilde> = f.\<close>
definition top1_is_lifting_on :: "'x set \<Rightarrow> 'x set set \<Rightarrow> 'e set \<Rightarrow> 'e set set
  \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> ('x \<Rightarrow> 'b) \<Rightarrow> ('x \<Rightarrow> 'e) \<Rightarrow> bool" where
  "top1_is_lifting_on X TX E TE B TB p f ftilde \<longleftrightarrow>
     top1_continuous_map_on X TX E TE ftilde \<and>
     (\<forall>x\<in>X. p (ftilde x) = f x)"

lemma top1_is_lifting_on_continuous:
  "top1_is_lifting_on X TX E TE B TB p f ftilde \<Longrightarrow>
    top1_continuous_map_on X TX E TE ftilde"
  unfolding top1_is_lifting_on_def by blast

lemma top1_is_lifting_on_covers:
  "top1_is_lifting_on X TX E TE B TB p f ftilde \<Longrightarrow>
    \<forall>x\<in>X. p (ftilde x) = f x"
  unfolding top1_is_lifting_on_def by blast

text \<open>The unit circle S^1 as a subspace of R^2.\<close>
definition top1_S1 :: "(real \<times> real) set" where
  "top1_S1 = {p. fst p ^ 2 + snd p ^ 2 = 1}"

definition top1_S1_topology :: "(real \<times> real) set set" where
  "top1_S1_topology = subspace_topology UNIV
     (product_topology_on top1_open_sets top1_open_sets) top1_S1"

text \<open>The canonical covering map p: R \<rightarrow> S^1 given by p(x) = (cos 2\<pi>x, sin 2\<pi>x).\<close>
definition top1_R_to_S1 :: "real \<Rightarrow> real \<times> real" where
  "top1_R_to_S1 x = (cos (2 * pi * x), sin (2 * pi * x))"

(** from \<S>53 Theorem 53.1: the canonical map R \<rightarrow> S^1 is a covering map.

    Munkres' proof: for U \<subseteq> S^1 the open arc with positive first coord,
    p^{-1}(U) is \<Union>_{n\<in>Z} (n - 1/4, n + 1/4). Each such interval maps
    homeomorphically to U (cos is a bijection between (-1/4,1/4) and (-\<pi>/2, \<pi>/2)
    mod 2\<pi>). The four similar arcs (positive/negative first/second coordinate) cover S^1. **)

text \<open>Helper: four open arcs covering S^1.\<close>
definition top1_S1_arc_E :: "(real \<times> real) set" where
  "top1_S1_arc_E = {(x,y). x^2 + y^2 = 1 \<and> x > 0}"
definition top1_S1_arc_W :: "(real \<times> real) set" where
  "top1_S1_arc_W = {(x,y). x^2 + y^2 = 1 \<and> x < 0}"
definition top1_S1_arc_N :: "(real \<times> real) set" where
  "top1_S1_arc_N = {(x,y). x^2 + y^2 = 1 \<and> y > 0}"
definition top1_S1_arc_S :: "(real \<times> real) set" where
  "top1_S1_arc_S = {(x,y). x^2 + y^2 = 1 \<and> y < 0}"

lemma top1_S1_arcs_cover: "top1_S1 \<subseteq> top1_S1_arc_E \<union> top1_S1_arc_W \<union> top1_S1_arc_N \<union> top1_S1_arc_S"
proof (intro subsetI)
  fix p :: "real \<times> real"
  assume hp: "p \<in> top1_S1"
  obtain x y where hpxy: "p = (x, y)" by (cases p) blast
  have heq: "x^2 + y^2 = 1" using hp hpxy unfolding top1_S1_def by simp
  have hne: "x \<noteq> 0 \<or> y \<noteq> 0" using heq by auto
  show "p \<in> top1_S1_arc_E \<union> top1_S1_arc_W \<union> top1_S1_arc_N \<union> top1_S1_arc_S"
    unfolding top1_S1_arc_E_def top1_S1_arc_W_def top1_S1_arc_N_def top1_S1_arc_S_def
    using hne heq hpxy by auto
qed

text \<open>Periodicity of the covering map: p(x + n) = p(x) for integer n.
  (Proved from cos_add/sin_add + cos_int_2pin/sin_int_2pin.)\<close>
lemma top1_R_to_S1_int_shift_early:
  "top1_R_to_S1 (x + of_int n) = top1_R_to_S1 x"
proof -
  have hc: "cos ((2 * pi) * of_int n) = 1" by (rule cos_int_2pin)
  have hs: "sin ((2 * pi) * of_int n) = 0" by (rule sin_int_2pin)
  have hexp: "2 * pi * (x + of_int n) = 2 * pi * x + (2 * pi) * of_int n"
    by (simp add: algebra_simps)
  show ?thesis unfolding top1_R_to_S1_def
    by (simp add: hexp cos_add sin_add hc hs)
qed

lemma top1_S1_arc_E_preimage:
  "{x. top1_R_to_S1 x \<in> top1_S1_arc_E} = (\<Union>n::int. {of_int n - 1/4 <..< of_int n + 1/4})"
proof (intro set_eqI iffI)
  fix x :: real
  assume hx: "x \<in> {x. top1_R_to_S1 x \<in> top1_S1_arc_E}"
  hence hcos: "cos (2 * pi * x) > 0"
    unfolding top1_R_to_S1_def top1_S1_arc_E_def by auto
  \<comment> \<open>cos(2\<pi>x) > 0 implies x \<in> (n - 1/4, n + 1/4) for n = round(x).
     Uses cos\_monotone\_0\_pi: cos strictly decreasing on [0, \<pi>].\<close>
  show "x \<in> (\<Union>n::int. {of_int n - 1/4 <..< of_int n + 1/4})"
  proof -
    let ?n = "\<lfloor>x + 1/2\<rfloor>"
    have hfloor: "of_int ?n \<le> x + 1/2" by (rule of_int_floor_le)
    have hfloor_ub: "x + 1/2 < of_int ?n + 1" using floor_correct[of "x + 1/2"] by linarith
    hence hdiff_lb: "of_int ?n - 1/2 \<le> x" and hdiff_ub: "x < of_int ?n + 1/2"
      by linarith+
    \<comment> \<open>Shift by periodicity: cos(2\<pi>(x-n)) = cos(2\<pi>x) > 0.\<close>
    have hcos_shift: "cos (2 * pi * (x - of_int ?n)) > 0"
    proof -
      let ?\<theta> = "2 * pi * (x - of_int ?n)"
      let ?k = "(2 * pi) * of_int ?n"
      have "2 * pi * x = ?\<theta> + ?k" by (simp add: algebra_simps)
      hence "cos (2 * pi * x) = cos (?\<theta> + ?k)" by simp
      also have "\<dots> = cos ?\<theta> * cos ?k - sin ?\<theta> * sin ?k" by (rule cos_add)
      also have "\<dots> = cos ?\<theta>" by (simp add: cos_int_2pin sin_int_2pin)
      finally show ?thesis using hcos by simp
    qed
    let ?\<theta> = "2 * pi * (x - of_int ?n)"
    have hpi: "0 < pi" by (rule pi_gt_zero)
    have h2pi: "0 < 2 * pi" using hpi by linarith
    have hdiff_lb_strict: "x - of_int ?n > -(1/2)"
    proof (rule ccontr)
      assume "\<not> x - of_int ?n > -(1/2)"
      hence "x - of_int ?n \<le> -(1/2)" by simp
      hence "x - of_int ?n = -(1/2)" using hdiff_lb by linarith
      hence "?\<theta> = -pi" using hpi by (simp add: field_simps)
      hence "cos ?\<theta> = -1" by simp
      thus False using hcos_shift by linarith
    qed
    have h\<theta>_lb: "?\<theta> > -pi"
    proof -
      have "-(pi) = 2 * pi * (-(1/2))" by (simp add: field_simps)
      also have "\<dots> < 2 * pi * (x - of_int ?n)"
        using hdiff_lb_strict h2pi by (intro mult_strict_left_mono) auto
      finally show ?thesis .
    qed
    have h\<theta>_ub: "?\<theta> < pi"
    proof -
      have "2 * pi * (x - of_int ?n) < 2 * pi * (1/2)"
        using hdiff_ub h2pi by (intro mult_strict_left_mono) linarith+
      also have "\<dots> = pi" by (simp add: field_simps)
      finally show ?thesis .
    qed
    \<comment> \<open>If \<theta> \<ge> \<pi>/2: cos(\<theta>) \<le> cos(\<pi>/2) = 0 by monotonicity. Contradiction.\<close>
    have hdiff_lt: "x - of_int ?n < 1/4"
    proof (rule ccontr)
      assume "\<not> x - of_int ?n < 1/4"
      hence hge: "x - of_int ?n \<ge> 1/4" by simp
      hence "?\<theta> \<ge> pi / 2"
      proof -
        have "pi / 2 = 2 * pi * (1/4)" by (simp add: field_simps)
        also have "\<dots> \<le> 2 * pi * (x - of_int ?n)"
          using hge h2pi by (intro mult_left_mono) auto
        finally show ?thesis .
      qed
      hence "cos ?\<theta> \<le> cos (pi / 2)"
        using h\<theta>_ub by (intro cos_monotone_0_pi_le[of "pi/2" ?\<theta>]) (auto simp: pi_ge_zero)
      hence "cos ?\<theta> \<le> 0" by simp
      thus False using hcos_shift by linarith
    qed
    \<comment> \<open>If \<theta> \<le> -\<pi>/2: cos(\<theta>) = cos(-\<theta>) \<le> 0. Contradiction.\<close>
    have hdiff_gt: "x - of_int ?n > -(1/4)"
    proof (rule ccontr)
      assume "\<not> x - of_int ?n > -(1/4)"
      hence hle: "x - of_int ?n \<le> -(1/4)" by simp
      hence "?\<theta> \<le> -(pi / 2)"
      proof -
        have "2 * pi * (x - of_int ?n) \<le> 2 * pi * (-(1/4))"
          using hle h2pi by (intro mult_left_mono) auto
        also have "\<dots> = -(pi / 2)" by (simp add: field_simps)
        finally show ?thesis .
      qed
      hence "-?\<theta> \<ge> pi / 2" by linarith
      moreover have "-?\<theta> \<le> pi" using h\<theta>_lb by linarith
      ultimately have "cos (-?\<theta>) \<le> cos (pi/2)"
        by (intro cos_monotone_0_pi_le[of "pi/2" "-?\<theta>"]) (auto simp: pi_ge_zero)
      hence "cos (-?\<theta>) \<le> 0" by simp
      hence "cos ?\<theta> \<le> 0" by simp
      thus False using hcos_shift by linarith
    qed
    have "of_int ?n - 1/4 < x" using hdiff_gt by linarith
    moreover have "x < of_int ?n + 1/4" using hdiff_lt by linarith
    ultimately show ?thesis by auto
  qed
next
  fix x :: real
  assume hx: "x \<in> (\<Union>n::int. {of_int n - 1/4 <..< of_int n + 1/4})"
  then obtain n :: int where hn: "of_int n - 1/4 < x" "x < of_int n + 1/4" by auto
  \<comment> \<open>x \<in> (n - 1/4, n + 1/4) implies cos(2\<pi>x) > 0.\<close>
  have hcos: "cos (2 * pi * x) > 0"
  proof -
    have hdiff_lb: "- (1/4) < x - of_int n" using hn(1) by linarith
    have hdiff_ub: "x - of_int n < 1/4" using hn(2) by linarith
    have hpi_pos: "(0::real) < 2 * pi" using pi_gt_zero by linarith
    have hd: "- (pi / 2) < 2 * pi * (x - of_int n)"
    proof -
      have "-(pi/2) = 2 * pi * (-(1/4))" by (simp add: field_simps)
      also have "\<dots> < 2 * pi * (x - of_int n)"
        using hdiff_lb hpi_pos by (intro mult_strict_left_mono) auto
      finally show ?thesis .
    qed
    have hu: "2 * pi * (x - of_int n) < pi / 2"
    proof -
      have "2 * pi * (x - of_int n) < 2 * pi * (1/4)"
        using hdiff_ub hpi_pos by (intro mult_strict_left_mono) auto
      also have "\<dots> = pi/2" by (simp add: field_simps)
      finally show ?thesis .
    qed
    have "cos (2 * pi * (x - of_int n)) > 0"
      by (rule cos_gt_zero_pi[OF hd hu])
    moreover have "cos (2 * pi * x) = cos (2 * pi * (x - of_int n))"
    proof -
      let ?\<theta> = "2 * pi * (x - of_int n)"
      let ?k = "(2 * pi) * of_int n"
      have h1: "2 * pi * x = ?\<theta> + ?k" by (simp add: algebra_simps)
      have h2: "cos (?\<theta> + ?k) = cos ?\<theta> * cos ?k - sin ?\<theta> * sin ?k"
        by (rule cos_add)
      have h3: "cos ?k = 1" by (rule cos_int_2pin)
      have h4: "sin ?k = 0" by (rule sin_int_2pin)
      show ?thesis unfolding h1 h2 h3 h4 by simp
    qed
    ultimately show ?thesis by simp
  qed
  have hcirc: "cos (2 * pi * x)^2 + sin (2 * pi * x)^2 = 1" by (simp add: sin_squared_eq)
  show "x \<in> {x. top1_R_to_S1 x \<in> top1_S1_arc_E}"
    unfolding top1_R_to_S1_def top1_S1_arc_E_def using hcos hcirc by auto
qed

text \<open>Continuity transfer for continuous_on S (partial functions).\<close>
lemma top1_continuous_map_on_subspace_open_sets_on:
  assumes hmap: "\<And>x. x \<in> S \<Longrightarrow> f x \<in> T"
      and hcont: "continuous_on S f"
  shows "top1_continuous_map_on S (subspace_topology UNIV top1_open_sets S)
                               T (subspace_topology UNIV top1_open_sets T) f"
proof -
  have "\<forall>V\<in>subspace_topology UNIV top1_open_sets T.
      {x \<in> S. f x \<in> V} \<in> subspace_topology UNIV top1_open_sets S"
  proof
    fix V assume "V \<in> subspace_topology UNIV top1_open_sets T"
    then obtain U where hUo: "open U" and hVeq: "V = T \<inter> U"
      unfolding subspace_topology_def top1_open_sets_def by (by100 auto)
    have hcoi: "\<forall>B. open B \<longrightarrow> (\<exists>A. open A \<and> A \<inter> S = f -` B \<inter> S)"
      using iffD1[OF continuous_on_open_invariant] hcont by (by100 blast)
    have "\<exists>A. open A \<and> A \<inter> S = f -` U \<inter> S" using hcoi hUo by (by100 blast)
    then obtain W where hWo: "open W" and hWeq: "W \<inter> S = f -` U \<inter> S" by (by100 blast)
    have "{x \<in> S. f x \<in> V} = S \<inter> W"
      unfolding hVeq using hmap hWeq by (by100 auto)
    thus "{x \<in> S. f x \<in> V} \<in> subspace_topology UNIV top1_open_sets S"
      unfolding subspace_topology_def top1_open_sets_def using hWo by (by100 blast)
  qed
  thus ?thesis unfolding top1_continuous_map_on_def using hmap by (by100 blast)
qed

theorem Theorem_53_1:
  "top1_covering_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
proof -
  \<comment> \<open>Munkres 53.1: p(x) = (cos 2\<pi>x, sin 2\<pi>x) is the standard covering R \<rightarrow> S^1.
     Step 1: p is continuous and surjective.\<close>
  have hp_cont: "top1_continuous_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
  proof -
    have hmap: "\<And>x::real. top1_R_to_S1 x \<in> top1_S1"
      unfolding top1_R_to_S1_def top1_S1_def by (simp add: sin_squared_eq)
    have hcont: "continuous_on UNIV top1_R_to_S1"
      unfolding top1_R_to_S1_def
      by (intro continuous_on_Pair continuous_on_compose2[OF continuous_on_cos]
              continuous_on_compose2[OF continuous_on_sin]
              continuous_on_mult continuous_on_const continuous_on_id) auto
    show ?thesis unfolding top1_S1_topology_def
      by (rule top1_continuous_map_on_R_to_R2_subspace[OF hmap hcont])
  qed
  have hp_surj: "top1_R_to_S1 ` UNIV = top1_S1"
  proof (rule set_eqI, rule iffI)
    fix p assume "p \<in> top1_R_to_S1 ` UNIV"
    then obtain x where hp: "p = top1_R_to_S1 x" by (by100 blast)
    show "p \<in> top1_S1" unfolding hp top1_R_to_S1_def top1_S1_def
      by (simp add: sin_squared_eq)
  next
    fix p assume hp: "p \<in> top1_S1"
    hence heq: "fst p ^ 2 + snd p ^ 2 = 1" unfolding top1_S1_def by (by100 simp)
    obtain \<theta> where hcos: "fst p = cos \<theta>" and hsin: "snd p = sin \<theta>"
      using sincos_total_2pi[of "fst p" "snd p"] heq by (by100 metis)
    let ?x = "\<theta> / (2 * pi)"
    have "top1_R_to_S1 ?x = (cos \<theta>, sin \<theta>)"
      unfolding top1_R_to_S1_def by (by100 simp)
    hence "top1_R_to_S1 ?x = p" using hcos hsin by (simp add: prod_eq_iff)
    thus "p \<in> top1_R_to_S1 ` UNIV" by (by100 blast)
  qed
  \<comment> \<open>Step 2: Every b \<in> S^1 has an evenly covered open neighborhood.
     Use the 4 open arcs E, N, W, S covering S^1. Each arc U_i has
     p\<inverse>(U_i) = \<Union>_n (n + open interval) — a disjoint union of sheets homeomorphic to U_i.\<close>
  \<comment> \<open>Each of the 4 arcs E,N,W,S is evenly covered. We prove arc_E; others are symmetric.\<close>
  have harc_E_ec: "top1_evenly_covered_on UNIV top1_open_sets
      top1_S1 top1_S1_topology top1_R_to_S1 top1_S1_arc_E"
  proof -
    \<comment> \<open>arc_E is open in S^1: arc_E = S^1 \<inter> {(x,y). x > 0}.\<close>
    have harc_E_open: "openin_on top1_S1 top1_S1_topology top1_S1_arc_E"
    proof -
      have heq: "top1_S1_arc_E = top1_S1 \<inter> {p::real\<times>real. fst p > 0}"
        unfolding top1_S1_arc_E_def top1_S1_def by (by100 auto)
      have hopen: "open {p::real\<times>real. fst p > 0}"
        by (rule open_Collect_less) (auto intro: continuous_intros)
      have "{p::real\<times>real. fst p > 0} \<in> (top1_open_sets::(real\<times>real) set set)"
        using hopen unfolding top1_open_sets_def by (by100 blast)
      hence "{p::real\<times>real. fst p > 0} \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
        using product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 blast)
      thus ?thesis unfolding openin_on_def top1_S1_topology_def subspace_topology_def heq
        by (by100 blast)
    qed
    \<comment> \<open>Slices: V_n = (n - 1/4, n + 1/4) for each n \<in> Z.\<close>
    define \<V> where "\<V> = (\<lambda>n::int. {of_int n - 1/4 <..< of_int n + (1/4::real)}) ` UNIV"
    \<comment> \<open>Each slice is open.\<close>
    have hV_open: "\<forall>V\<in>\<V>. openin_on UNIV (top1_open_sets::real set set) V"
      unfolding \<V>_def openin_on_def top1_open_sets_def by (by100 auto)
    \<comment> \<open>Slices pairwise disjoint.\<close>
    have hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
    proof (intro ballI impI)
      fix V V' assume "V \<in> \<V>" "V' \<in> \<V>" "V \<noteq> V'"
      then obtain n m :: int where hV: "V = {of_int n - 1/4 <..< of_int n + 1/4}"
          and hV': "V' = {of_int m - 1/4 <..< of_int m + 1/4}" and hnm: "n \<noteq> m"
        unfolding \<V>_def by blast
      have "of_int n - of_int m \<ge> (1::real) \<or> of_int m - of_int n \<ge> (1::real)"
        using hnm by linarith
      hence hgap: "of_int m + 1/4 \<le> of_int n - (1/4::real) \<or> of_int n + 1/4 \<le> of_int m - (1/4::real)"
      proof
        assume h: "of_int n - of_int m \<ge> (1::real)"
        hence "of_int m + 1/4 \<le> of_int n - (1/4::real)" by (by100 linarith)
        thus ?thesis by (by100 blast)
      next
        assume h: "of_int m - of_int n \<ge> (1::real)"
        hence "of_int n + 1/4 \<le> of_int m - (1/4::real)" by (by100 linarith)
        thus ?thesis by (by100 blast)
      qed
      show "V \<inter> V' = {}"
      proof (rule ccontr)
        assume "V \<inter> V' \<noteq> {}"
        then obtain x where "x \<in> V" "x \<in> V'" by (by100 blast)
        hence hxn: "x \<in> {of_int n - 1/4 <..< of_int n + (1/4::real)}" using hV by blast
        have hxm: "x \<in> {of_int m - 1/4 <..< of_int m + (1/4::real)}" using \<open>x \<in> V'\<close> hV' by blast
        have "of_int n - 1/4 < x" "x < of_int n + 1/4"
              "of_int m - 1/4 < x" "x < of_int m + 1/4"
          using hxn hxm by simp_all
        thus False using hgap by (by100 linarith)
      qed
    qed
    \<comment> \<open>Union = preimage.\<close>
    have hV_union: "{x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_E} = \<Union>\<V>"
      unfolding \<V>_def using top1_S1_arc_E_preimage by (by100 auto)
    \<comment> \<open>p homeomorphism on each slice.\<close>
    have hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology UNIV top1_open_sets V)
        top1_S1_arc_E (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E) top1_R_to_S1"
    proof
      fix V assume hVmem: "V \<in> \<V>"
      then obtain n :: int where hVeq: "V = {of_int n - 1/4 <..< of_int n + (1/4::real)}"
        unfolding \<V>_def by (by100 blast)
      have hpV: "\<forall>x\<in>V. top1_R_to_S1 x \<in> top1_S1_arc_E"
        using hV_union hVmem by (by100 blast)
      have hV_sub: "V \<subseteq> (UNIV::real set)" by (by100 blast)
      have harc_sub: "top1_S1_arc_E \<subseteq> top1_S1"
        unfolding top1_S1_arc_E_def top1_S1_def by (by100 auto)
      have hpV_surj: "top1_R_to_S1 ` V = top1_S1_arc_E"
      proof (intro equalityI subsetI)
        fix y assume "y \<in> top1_R_to_S1 ` V"
        thus "y \<in> top1_S1_arc_E" using hpV by (by100 blast)
      next
        fix y assume hy: "y \<in> top1_S1_arc_E"
        \<comment> \<open>y is in the preimage of arc_E, so y = p(t) for some t \<in> (m-1/4, m+1/4).\<close>
        have "y \<in> top1_S1" using hy harc_sub by (by100 blast)
        hence "y \<in> top1_R_to_S1 ` UNIV" using hp_surj by (by100 blast)
        then obtain t where hpt: "top1_R_to_S1 t = y" by (by100 blast)
        hence "t \<in> {x. top1_R_to_S1 x \<in> top1_S1_arc_E}" using hy by (by100 simp)
        hence "t \<in> (\<Union>m::int. {of_int m - 1/4 <..< of_int m + 1/4})"
          using top1_S1_arc_E_preimage by (by100 blast)
        then obtain m :: int where "t \<in> {of_int m - 1/4 <..< of_int m + 1/4}" by (by100 blast)
        \<comment> \<open>Shift by periodicity: t' = t + (n - m) is in V_n and p(t') = p(t) = y.\<close>
        let ?t' = "t + of_int (n - m)"
        have htm_lb: "of_int m - 1/4 < t" and htm_ub: "t < of_int m + 1/4"
          using \<open>t \<in> {of_int m - 1/4 <..< of_int m + 1/4}\<close> by (by100 simp)+
        hence "of_int n - 1/4 < t + of_int (n - m)" "t + of_int (n - m) < of_int n + 1/4"
          by (by100 linarith)+
        hence ht'V: "?t' \<in> V" unfolding hVeq by (by100 auto)
        have "top1_R_to_S1 ?t' = top1_R_to_S1 t"
        proof -
          show ?thesis unfolding top1_R_to_S1_def
            using cos_int_2pin[of "n - m"] sin_int_2pin[of "n - m"]
            by (simp add: distrib_left cos_add sin_add)
        qed
        hence "top1_R_to_S1 ?t' = y" using hpt by (by100 simp)
        thus "y \<in> top1_R_to_S1 ` V" using ht'V by (by100 blast)
      qed
      have hpV_inj: "inj_on top1_R_to_S1 V"
      proof (rule inj_onI)
        fix x y assume hx: "x \<in> V" and hy: "y \<in> V"
            and heq: "top1_R_to_S1 x = top1_R_to_S1 y"
        \<comment> \<open>x, y \<in> (n-1/4, n+1/4), so 2\<pi>x, 2\<pi>y \<in> (2\<pi>n-\<pi>/2, 2\<pi>n+\<pi>/2).
           sin injective on this interval \<Rightarrow> 2\<pi>x = 2\<pi>y \<Rightarrow> x = y.\<close>
        have "sin (2 * pi * x) = sin (2 * pi * y)"
          using heq unfolding top1_R_to_S1_def by (by100 simp)
        moreover have "cos (2 * pi * x) = cos (2 * pi * y)"
          using heq unfolding top1_R_to_S1_def by (by100 simp)
        moreover have "cos (2 * pi * x) > 0"
        proof -
          have "x \<in> {of_int n - 1/4 <..< of_int n + 1/4}" using hx hVeq by (by100 blast)
          hence "top1_R_to_S1 x \<in> top1_S1_arc_E" using hpV hx by (by100 blast)
          thus ?thesis unfolding top1_R_to_S1_def top1_S1_arc_E_def by (by100 simp)
        qed
        \<comment> \<open>sin \<theta>1 = sin \<theta>2 \<and> cos \<theta>1 = cos \<theta>2 \<Rightarrow> \<exists>k. \<theta>1 = \<theta>2 + 2k\<pi>.\<close>
        ultimately obtain k :: int where "2*pi*x = 2*pi*y + 2*pi*of_int k"
          using iffD1[OF sin_cos_eq_iff] by (by100 blast)
        hence "2*pi*x - 2*pi*y = 2*pi * of_int k" by (by100 linarith)
        hence "2*pi * (x - y) = 2*pi * of_int k" by (simp add: algebra_simps)
        hence "x - y = of_int k" using pi_gt_zero by (by100 simp)
        \<comment> \<open>x, y \<in> (n-1/4, n+1/4), so |x-y| < 1/2 < 1. Hence k = 0.\<close>
        moreover have "of_int n - 1/4 < x" "x < of_int n + 1/4"
            "of_int n - 1/4 < y" "y < of_int n + 1/4"
        proof -
          have "x \<in> {of_int n - 1/4 <..< of_int n + (1/4::real)}" using hx hVeq by simp
          hence "of_int n - 1/4 < x" "x < of_int n + 1/4" by simp_all
          have "y \<in> {of_int n - 1/4 <..< of_int n + (1/4::real)}" using hy hVeq by simp
          hence "of_int n - 1/4 < y" "y < of_int n + 1/4" by simp_all
          show "of_int n - 1/4 < x" "x < of_int n + 1/4"
               "of_int n - 1/4 < y" "y < of_int n + 1/4"
            by fact+
        qed
        hence "\<bar>x - y\<bar> < 1/2" by (by100 linarith)
        hence "k = 0" using \<open>x - y = of_int k\<close> by (by100 linarith)
        ultimately show "x = y" by (by100 linarith)
      qed
      have hinv_cont: "top1_continuous_map_on top1_S1_arc_E
          (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E)
          V (subspace_topology UNIV top1_open_sets V) (inv_into V top1_R_to_S1)"
      proof -
        define inv_fn :: "real \<times> real \<Rightarrow> real"
          where "inv_fn \<equiv> \<lambda>p. arctan (snd p / fst p) / (2 * pi) + of_int n"
        have hinv_co: "continuous_on top1_S1_arc_E inv_fn"
          unfolding inv_fn_def top1_S1_arc_E_def
          by (intro continuous_on_add continuous_on_const
              continuous_on_divide[OF _ continuous_on_const]
              continuous_on_compose2[OF continuous_on_arctan _ subset_UNIV]
              continuous_on_divide continuous_on_snd continuous_on_fst) (by100 auto)+
        have hinv_range: "\<And>p. p \<in> top1_S1_arc_E \<Longrightarrow> inv_fn p \<in> V"
        proof -
          fix p assume hp: "p \<in> top1_S1_arc_E"
          hence hx_pos: "fst p > 0" unfolding top1_S1_arc_E_def by (by100 auto)
          have "arctan (snd p / fst p) \<in> {-pi/2 <..< pi/2}"
            using arctan_bounded[of "snd p / fst p"] by (by100 simp)
          hence "arctan (snd p / fst p) / (2*pi) \<in> {-1/4 <..< 1/4}"
            using pi_gt_zero by (simp add: field_simps)
          thus "inv_fn p \<in> V" unfolding inv_fn_def hVeq by (by100 auto)
        qed
        have hinv_agree: "\<forall>p\<in>top1_S1_arc_E. inv_into V top1_R_to_S1 p = inv_fn p"
        proof
          fix p assume hp: "p \<in> top1_S1_arc_E"
          have hx_pos: "fst p > 0" using hp unfolding top1_S1_arc_E_def by (by100 auto)
          have hcirc: "fst p ^ 2 + snd p ^ 2 = 1" using hp unfolding top1_S1_arc_E_def by (by100 auto)
          have hinV: "inv_fn p \<in> V" using hinv_range[OF hp] .
          \<comment> \<open>Show p(inv_fn p) = p: cos(arctan(y/x)) = x and sin(arctan(y/x)) = y for x>0, x^2+y^2=1.\<close>
          have hsqrt: "sqrt (1 + (snd p / fst p)\<^sup>2) = 1 / fst p"
          proof -
            have "1 + (snd p / fst p)^2 = ((fst p)^2 + (snd p)^2) / (fst p)^2"
              using hx_pos by (simp add: field_simps power2_eq_square)
            also have "\<dots> = 1 / (fst p)^2" using hcirc by (by100 simp)
            finally have "sqrt (1 + (snd p / fst p)^2) = sqrt (1 / (fst p)^2)" by (by100 simp)
            also have "\<dots> = 1 / fst p" using hx_pos by (simp add: real_sqrt_divide)
            finally show ?thesis .
          qed
          have hcos: "cos (arctan (snd p / fst p)) = fst p"
            using cos_arctan[of "snd p / fst p"] hsqrt hx_pos by (by100 simp)
          have hsin: "sin (arctan (snd p / fst p)) = snd p"
            using sin_arctan[of "snd p / fst p"] hsqrt hx_pos by (by100 simp)
          have "top1_R_to_S1 (inv_fn p) = p"
            unfolding top1_R_to_S1_def inv_fn_def
            using hcos hsin by (simp add: distrib_left cos_add sin_add cos_int_2pin sin_int_2pin
                                          prod_eq_iff)
          thus "inv_into V top1_R_to_S1 p = inv_fn p"
            using inv_into_f_eq[OF hpV_inj hinV] by (by100 simp)
        qed
        have harc_eq: "subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E
            = subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1_arc_E"
          unfolding top1_S1_topology_def
          using subspace_topology_trans[OF harc_sub]
          by (simp add: product_topology_on_open_sets[where ?'a=real and ?'b=real])
        have "top1_continuous_map_on top1_S1_arc_E
            (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1_arc_E)
            V (subspace_topology UNIV (top1_open_sets :: real set set) V) inv_fn"
          by (rule top1_continuous_map_on_subspace_open_sets_on[OF hinv_range hinv_co])
        hence hinv_fn_cont: "top1_continuous_map_on top1_S1_arc_E
            (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E)
            V (subspace_topology UNIV top1_open_sets V) inv_fn"
          unfolding harc_eq .
        have "\<forall>p\<in>top1_S1_arc_E. inv_fn p = inv_into V top1_R_to_S1 p"
          using hinv_agree by (by100 auto)
        thus ?thesis by (rule top1_continuous_map_on_agree'[OF hinv_fn_cont])
      qed
      have hbij: "bij_betw top1_R_to_S1 V top1_S1_arc_E"
        unfolding bij_betw_def using hpV_inj hpV_surj by (by100 blast)
      have hTV: "is_topology_on V (subspace_topology UNIV top1_open_sets V)"
        by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV hV_sub])
      have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
          (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
        using product_topology_on_is_topology_on[OF
              top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
      have hTarc: "is_topology_on top1_S1_arc_E
          (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E)"
        by (rule subspace_topology_is_topology_on[OF hTS1]) (use harc_sub in \<open>by100 blast\<close>)
      have hp_V_img: "top1_R_to_S1 ` V \<subseteq> top1_S1_arc_E"
        using hpV by (by100 blast)
      have hp_V_arc: "top1_continuous_map_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_E (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E) top1_R_to_S1"
        by (rule top1_continuous_map_on_codomain_shrink[OF
              top1_continuous_map_on_restrict_domain_simple[OF hp_cont hV_sub]
              hp_V_img harc_sub])
      show "top1_homeomorphism_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_E (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_E) top1_R_to_S1"
        unfolding top1_homeomorphism_on_def
        using hTV hTarc hbij hp_V_arc hinv_cont by (by100 blast)
    qed
    show ?thesis unfolding top1_evenly_covered_on_def
      using harc_E_open hV_open hV_disj hV_union hV_homeo by (by100 blast)
  qed
  \<comment> \<open>Arcs N, W, S: symmetric to arc_E with adapted coordinates.\<close>
  have harc_N_ec: "top1_evenly_covered_on UNIV top1_open_sets
      top1_S1 top1_S1_topology top1_R_to_S1 top1_S1_arc_N"
  proof -
    \<comment> \<open>Arc N = {(x,y) \<in> S^1 | y > 0}. Preimage under p: those x with sin(2\<pi>x) > 0,
       i.e., x \<in> (n, n+1/2) for each integer n. Each slice maps homeomorphically to arc_N.
       Inverse: given (a,b) with b > 0, x = arcsin(b)/(2\<pi>) + n (or arctan-based).\<close>
    have harc_N_open: "openin_on top1_S1 top1_S1_topology top1_S1_arc_N"
    proof -
      have heq: "top1_S1_arc_N = top1_S1 \<inter> {p::real\<times>real. snd p > 0}"
        unfolding top1_S1_arc_N_def top1_S1_def by (by100 auto)
      have hopen: "open {p::real\<times>real. snd p > 0}"
        by (rule open_Collect_less) (auto intro: continuous_intros)
      have "{p::real\<times>real. snd p > 0} \<in> (top1_open_sets::(real\<times>real) set set)"
        using hopen unfolding top1_open_sets_def by (by100 blast)
      hence "{p::real\<times>real. snd p > 0} \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
        using product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 blast)
      thus ?thesis unfolding openin_on_def top1_S1_topology_def subspace_topology_def heq
        by (by100 blast)
    qed
    let ?\<V> = "{V. \<exists>n::int. V = {x::real. of_int n < x \<and> x < of_int n + 1/2}}"
    have hV_open: "\<forall>V\<in>?\<V>. openin_on (UNIV::real set) top1_open_sets V"
    proof
      fix V assume "V \<in> ?\<V>"
      then obtain n :: int where hV: "V = {x::real. of_int n < x \<and> x < of_int n + 1/2}"
        by (by100 blast)
      have "V = {of_int n <..< of_int n + 1/2}" using hV by (by100 auto)
      moreover have "open {of_int n <..< of_int n + (1/2::real)}" by (by100 simp)
      ultimately show "openin_on UNIV top1_open_sets V"
        unfolding openin_on_def top1_open_sets_def by (by100 blast)
    qed
    have hV_disj: "\<forall>V\<in>?\<V>. \<forall>V'\<in>?\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
    proof (intro ballI impI)
      fix V V' assume "V \<in> ?\<V>" "V' \<in> ?\<V>" "V \<noteq> V'"
      then obtain n where hV: "V = {x::real. of_int n < x \<and> x < of_int n + 1/2}"
        using \<open>V \<in> ?\<V>\<close> by auto
      obtain m where hV': "V' = {x::real. of_int m < x \<and> x < of_int m + 1/2}"
        using \<open>V' \<in> ?\<V>\<close> by (by100 blast)
      have hnm: "n \<noteq> m" using \<open>V \<noteq> V'\<close> hV hV' by (by100 force)
      show "V \<inter> V' = {}"
      proof (rule ccontr)
        assume "V \<inter> V' \<noteq> {}"
        then obtain x where "x \<in> V" "x \<in> V'" by (by100 blast)
        hence hx1: "of_int n < x" and hx2: "x < of_int n + (1/2::real)"
            and hx3: "of_int m < x" and hx4: "x < of_int m + (1/2::real)"
          using hV hV' by (by100 blast)+
        hence "\<bar>of_int n - of_int m\<bar> < (1::real)" by (by100 linarith)
        hence "n = m" by (by100 linarith)
        thus False using hnm by (by100 blast)
      qed
    qed
    have hV_union: "{x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_N} = \<Union>?\<V>"
    proof (intro set_eqI iffI)
      fix x :: real
      assume hx: "x \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_N}"
      hence hsin: "sin (2 * pi * x) > 0"
        unfolding top1_R_to_S1_def top1_S1_arc_N_def by (by100 auto)
      \<comment> \<open>sin(2\<pi>x) > 0 iff 2\<pi>x \<in> (2k\<pi>, (2k+1)\<pi>) iff x \<in> (k, k + 1/2) for some integer k.\<close>
      \<comment> \<open>Let n = floor(x). Then x - n \<in> [0,1) and sin(2\<pi>(x-n)) = sin(2\<pi>x) > 0.
         On [0,1), sin(2\<pi>t) > 0 iff t \<in> (0, 1/2). So x \<in> (n, n+1/2).\<close>
      define n where "n = \<lfloor>x\<rfloor>"
      have hn_le: "of_int n \<le> x" and hx_lt: "x < of_int n + 1"
        unfolding n_def by linarith+
      have hfrac: "x - of_int n \<ge> 0" "x - of_int n < 1" using hn_le hx_lt by linarith+
      \<comment> \<open>sin(2\<pi>(x-n)) = sin(2\<pi>x) by periodicity.\<close>
      have hshift: "sin (2 * pi * (x - of_int n)) = sin (2 * pi * x)"
      proof -
        have "top1_R_to_S1 x = top1_R_to_S1 (x - of_int n)"
          using top1_R_to_S1_int_shift_early[of "x - of_int n" n] by simp
        hence "snd (top1_R_to_S1 x) = snd (top1_R_to_S1 (x - of_int n))" by simp
        thus ?thesis unfolding top1_R_to_S1_def by (by100 simp)
      qed
      \<comment> \<open>sin(2\<pi>(x-n)) > 0 with x-n \<in> [0,1). On [0,1): sin(2\<pi>t) > 0 iff t \<in> (0, 1/2).
         sin(2\<pi>t) = 0 at t=0 and t=1/2; sin(2\<pi>t) > 0 on (0, 1/2); sin(2\<pi>t) < 0 on (1/2, 1).\<close>
      have hfrac_pos: "sin (2 * pi * (x - of_int n)) > 0" using hsin hshift by (by100 linarith)
      have hfrac_gt: "x - of_int n > 0"
      proof (rule ccontr)
        assume "\<not> x - of_int n > 0"
        hence "x - of_int n = 0" using hfrac by (by100 linarith)
        hence "sin (2 * pi * (x - of_int n)) = 0" by simp
        thus False using hfrac_pos by (by100 linarith)
      qed
      have hfrac_lt: "x - of_int n < 1/2"
      proof (rule ccontr)
        assume "\<not> x - of_int n < 1/2"
        hence hge: "x - of_int n \<ge> 1/2" by (by100 linarith)
        show False
        proof (cases "x - of_int n = 1/2")
          case True
          have "x - of_int n = 1/2" using True .
          hence h12: "x - of_int n = 1/2" .
          have "2 * pi * (x - of_int n) = 2 * pi * (1/2::real)" using h12 by simp
          hence "sin (2 * pi * (x - of_int n)) = sin (pi * (2 * (1/2)))" by (simp add: algebra_simps)
          also have "pi * (2 * (1/2::real)) = pi" by simp
          also have "sin pi = 0" by simp
          finally have "sin (2 * pi * (x - of_int n)) = 0" .
          thus False using hfrac_pos by (by100 linarith)
        next
          case False
          hence hgt: "x - of_int n > 1/2" using hge by (by100 linarith)
          \<comment> \<open>On (1/2, 1), sin(2\<pi>t) < 0.\<close>
          have hpi_lt: "pi < 2 * pi * (x - of_int n)"
          proof -
            have "pi = pi * (2 * (1/2::real))" by simp
            also have "\<dots> = 2 * pi * (1/2::real)" by (simp add: algebra_simps)
            also have "\<dots> < 2 * pi * (x - of_int n)"
              using hgt pi_gt_zero by (by100 simp)
            finally show ?thesis .
          qed
          have h2pi_gt: "2 * pi * (x - of_int n) < 2 * pi"
          proof -
            have "2 * pi * (x - of_int n) < 2 * pi * 1"
              using hfrac pi_gt_zero by (by100 simp)
            thus ?thesis by simp
          qed
          have "sin (2 * pi * (x - of_int n)) < 0"
            by (rule sin_lt_zero[OF hpi_lt h2pi_gt])
          thus False using hfrac_pos by (by100 linarith)
        qed
      qed
      have "x \<in> {x::real. of_int n < x \<and> x < of_int n + 1/2}"
        using hfrac_gt hfrac_lt by (by100 simp)
      thus "x \<in> \<Union>?\<V>" by (by100 blast)
    next
      fix x :: real
      assume "x \<in> \<Union>?\<V>"
      then obtain n :: int where "of_int n < x" "x < of_int n + (1/2::real)" by (by100 auto)
      have hpi: "pi > 0" by (rule pi_gt_zero)
      hence "0 < 2 * pi * x - 2 * pi * of_int n"
        using \<open>of_int n < x\<close> by (by100 simp)
      moreover have "2 * pi * x - 2 * pi * of_int n < pi"
      proof -
        have "2 * pi * x < 2 * pi * (of_int n + 1/2)"
          using \<open>x < of_int n + (1/2::real)\<close> hpi by (by100 simp)
        also have "\<dots> = 2 * pi * of_int n + pi" by (simp add: algebra_simps)
        finally show ?thesis by (by100 linarith)
      qed
      ultimately have hsin: "sin (2 * pi * x - 2 * of_int n * pi) > 0"
        by (intro sin_gt_zero) (simp add: algebra_simps)+
      \<comment> \<open>sin(2\<pi>x) = sin(2\<pi>(x-n)) > 0 from hsin and periodicity.\<close>
      have hshift: "top1_R_to_S1 x = top1_R_to_S1 (x - of_int n)"
        using top1_R_to_S1_int_shift_early[of "x - of_int n" n] by simp
      have "sin (2 * pi * x) = sin (2 * pi * (x - of_int n))"
      proof -
        have "snd (top1_R_to_S1 x) = snd (top1_R_to_S1 (x - of_int n))" using hshift by simp
        thus ?thesis unfolding top1_R_to_S1_def by (by100 simp)
      qed
      also have "\<dots> = sin (2 * pi * x - 2 * of_int n * pi)"
        by (simp add: algebra_simps)
      finally have "sin (2 * pi * x) > 0" using hsin by (by100 linarith)
      moreover have "cos (2 * pi * x) ^ 2 + sin (2 * pi * x) ^ 2 = 1" by (rule sin_cos_squared_add2)
      ultimately show "x \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_N}"
        unfolding top1_R_to_S1_def top1_S1_arc_N_def by (by100 auto)
    qed
    have hV_homeo: "\<forall>V\<in>?\<V>.
        top1_homeomorphism_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_N (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_N) top1_R_to_S1"
    proof
      fix V assume hVmem: "V \<in> ?\<V>"
      then obtain nn :: int where hVeq: "V = {x::real. of_int nn < x \<and> x < of_int nn + 1/2}"
        by (by100 auto)
      have hpV: "\<forall>x\<in>V. top1_R_to_S1 x \<in> top1_S1_arc_N"
        using hV_union hVmem by (by100 blast)
      have harc_sub: "top1_S1_arc_N \<subseteq> top1_S1"
        unfolding top1_S1_arc_N_def top1_S1_def by (by100 auto)
      \<comment> \<open>Surjectivity: p maps V onto arc_N (periodicity shift).\<close>
      have hpV_surj: "top1_R_to_S1 ` V = top1_S1_arc_N"
      proof (intro equalityI subsetI)
        fix y assume "y \<in> top1_R_to_S1 ` V" thus "y \<in> top1_S1_arc_N" using hpV by (by100 blast)
      next
        fix y assume hy: "y \<in> top1_S1_arc_N"
        have "y \<in> top1_S1" using hy harc_sub by (by100 blast)
        hence "y \<in> top1_R_to_S1 ` UNIV" using hp_surj by (by100 blast)
        then obtain t where hpt: "top1_R_to_S1 t = y" by (by100 blast)
        hence "t \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_N}" using hy by (by100 simp)
        hence "t \<in> \<Union>?\<V>" using hV_union by (by100 blast)
        then obtain m :: int where htm: "of_int m < t" "t < of_int m + (1/2::real)"
          by (by100 auto)
        let ?t' = "t + of_int (nn - m)"
        have "of_int nn < ?t'" "?t' < of_int nn + (1/2::real)" using htm by (by100 linarith)+
        hence ht'V: "?t' \<in> V" unfolding hVeq by (by100 blast)
        have "top1_R_to_S1 ?t' = top1_R_to_S1 t"
          using top1_R_to_S1_int_shift_early[of t "nn - m"] by simp
        hence "top1_R_to_S1 ?t' = y" using hpt by (by100 simp)
        thus "y \<in> top1_R_to_S1 ` V" using ht'V by (by100 blast)
      qed
      \<comment> \<open>Injectivity: sin_cos_eq_iff + interval width 1/2 < 1.\<close>
      have hpV_inj: "inj_on top1_R_to_S1 V"
      proof (rule inj_onI)
        fix x y assume hx: "x \<in> V" and hy: "y \<in> V"
            and heq: "top1_R_to_S1 x = top1_R_to_S1 y"
        have "sin (2 * pi * x) = sin (2 * pi * y)" "cos (2 * pi * x) = cos (2 * pi * y)"
          using heq unfolding top1_R_to_S1_def by (by100 simp)+
        then obtain k :: int where hk: "2*pi*x = 2*pi*y + 2*pi*of_int k"
          using iffD1[OF sin_cos_eq_iff] by (by100 blast)
        hence "2*pi * (x - y) = 2*pi * of_int k" by (simp add: algebra_simps)
        hence "x - y = of_int k" using pi_gt_zero by (by100 simp)
        moreover have "\<bar>x - y\<bar> < 1/2"
        proof -
          have "of_int nn < x" "x < of_int nn + (1/2::real)"
               "of_int nn < y" "y < of_int nn + (1/2::real)"
            using hx hy unfolding hVeq by (by100 blast)+
          thus ?thesis by (by100 linarith)
        qed
        hence "k = 0" using \<open>x - y = of_int k\<close> by (by100 linarith)
        ultimately show "x = y" by (by100 linarith)
      qed
      \<comment> \<open>Bijection.\<close>
      have hbij: "bij_betw top1_R_to_S1 V top1_S1_arc_N"
        unfolding bij_betw_def using hpV_inj hpV_surj by (by100 blast)
      \<comment> \<open>Forward continuity: restriction of p to V.\<close>
      have hp_V_img: "top1_R_to_S1 ` V \<subseteq> top1_S1_arc_N"
        using hpV by (by100 blast)
      have hV_sub: "V \<subseteq> (UNIV::real set)" by (by100 blast)
      have hp_V_cont: "top1_continuous_map_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_N (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_N) top1_R_to_S1"
        by (rule top1_continuous_map_on_codomain_shrink[OF
              top1_continuous_map_on_restrict_domain_simple[OF hp_cont hV_sub]
              hp_V_img harc_sub])
      \<comment> \<open>Inverse continuity.\<close>
      have hinv_cont: "top1_continuous_map_on top1_S1_arc_N
          (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_N)
          V (subspace_topology UNIV top1_open_sets V) (inv_into V top1_R_to_S1)"
      proof -
        define inv_fn :: "real \<times> real \<Rightarrow> real"
          where "inv_fn \<equiv> \<lambda>p. arccos (fst p) / (2 * pi) + of_int nn"
        \<comment> \<open>Continuity: arccos(fst p) continuous on arc_N since fst p \<in> [-1,1].\<close>
        have hfst_bdd: "\<forall>p\<in>top1_S1_arc_N. -1 \<le> fst p \<and> fst p \<le> 1"
        proof (intro ballI conjI)
          fix p assume hp: "p \<in> top1_S1_arc_N"
          have hcirc: "fst p ^ 2 + snd p ^ 2 = 1"
            using hp unfolding top1_S1_arc_N_def by (by100 auto)
          have "0 \<le> snd p ^ 2" by simp
          hence "fst p ^ 2 \<le> 1" using hcirc by (by100 linarith)
          show "-1 \<le> fst p"
          proof (rule ccontr)
            assume "\<not> -1 \<le> fst p"
            hence "- fst p > 1" by (by100 linarith)
            hence "(- fst p) * (- fst p) > 1 * 1"
              by (intro mult_strict_mono') (by100 linarith)+
            hence "fst p ^ 2 > 1" unfolding power2_eq_square by (by100 simp)
            thus False using \<open>fst p ^ 2 \<le> 1\<close> by (by100 linarith)
          qed
          show "fst p \<le> 1"
          proof (rule ccontr)
            assume "\<not> fst p \<le> 1"
            hence "fst p > 1" by (by100 linarith)
            hence "fst p * fst p > 1 * 1"
              by (intro mult_strict_mono') (by100 linarith)+
            hence "fst p ^ 2 > 1" unfolding power2_eq_square by (by100 simp)
            thus False using \<open>fst p ^ 2 \<le> 1\<close> by (by100 linarith)
          qed
        qed
        have hinv_co: "continuous_on top1_S1_arc_N inv_fn"
          unfolding inv_fn_def
          by (intro continuous_on_add continuous_on_const
              continuous_on_divide[OF _ continuous_on_const]
              continuous_on_arccos continuous_on_fst)
             (use hfst_bdd pi_gt_zero in \<open>by100 auto\<close>)+
        have hinv_range: "\<And>p. p \<in> top1_S1_arc_N \<Longrightarrow> inv_fn p \<in> V"
        proof -
          fix p assume hp: "p \<in> top1_S1_arc_N"
          hence hy_pos: "snd p > 0" and hcirc: "fst p ^ 2 + snd p ^ 2 = 1"
            unfolding top1_S1_arc_N_def by (by100 auto)+
          \<comment> \<open>x \<in> (-1, 1) strictly since y > 0.\<close>
          have hx_lt1: "fst p < 1"
          proof (rule ccontr)
            assume "\<not> fst p < 1" hence "fst p \<ge> 1" by (by100 linarith)
            hence "fst p * fst p \<ge> 1 * 1"
              by (intro mult_mono') (by100 linarith)+
            hence "snd p ^ 2 \<le> 0" using hcirc unfolding power2_eq_square by (by100 linarith)
            moreover have "snd p ^ 2 > 0" using hy_pos unfolding power2_eq_square
              by (intro mult_pos_pos) (by100 linarith)+
            ultimately show False by (by100 linarith)
          qed
          have hx_gt_neg1: "fst p > -1"
          proof (rule ccontr)
            assume "\<not> fst p > -1" hence "fst p \<le> -1" by (by100 linarith)
            hence "(- fst p) * (- fst p) \<ge> 1 * 1"
              by (intro mult_mono') (by100 linarith)+
            hence "snd p ^ 2 \<le> 0" using hcirc unfolding power2_eq_square by (by100 linarith)
            moreover have "snd p ^ 2 > 0" using hy_pos unfolding power2_eq_square
              by (intro mult_pos_pos) (by100 linarith)+
            ultimately show False by (by100 linarith)
          qed
          have hbdd: "0 < arccos (fst p) \<and> arccos (fst p) < pi"
            by (rule arccos_lt_bounded[OF hx_gt_neg1 hx_lt1])
          have hpi: "pi > 0" by (rule pi_gt_zero)
          have "0 < arccos (fst p) / (2 * pi)"
            using hbdd hpi by (by100 simp)
          moreover have "arccos (fst p) / (2 * pi) < 1/2"
          proof -
            have "arccos (fst p) / (2 * pi) < pi / (2 * pi)"
              using hbdd hpi by (by100 simp)
            also have "\<dots> = 1/2" using hpi by (by100 simp)
            finally show ?thesis .
          qed
          ultimately show "inv_fn p \<in> V"
            unfolding inv_fn_def hVeq by (by100 auto)
        qed
        have hinv_agree: "\<forall>p\<in>top1_S1_arc_N. inv_into V top1_R_to_S1 p = inv_fn p"
        proof
          fix p assume hp: "p \<in> top1_S1_arc_N"
          hence hy_pos: "snd p > 0" and hcirc: "fst p ^ 2 + snd p ^ 2 = 1"
            unfolding top1_S1_arc_N_def by (by100 auto)+
          have hinV: "inv_fn p \<in> V" using hinv_range[OF hp] .
          \<comment> \<open>Show top1_R_to_S1(inv_fn p) = p.\<close>
          have hx_bdd: "-1 \<le> fst p" "fst p \<le> 1"
          proof -
            have "0 \<le> snd p ^ 2" by simp
            hence "fst p ^ 2 \<le> 1" using hcirc by (by100 linarith)
            show "-1 \<le> fst p"
            proof (rule ccontr)
              assume "\<not> -1 \<le> fst p"
              hence "- fst p > 1" by (by100 linarith)
              hence "(- fst p) * (- fst p) > 1 * 1"
                by (intro mult_strict_mono') (by100 linarith)+
              hence "fst p ^ 2 > 1" unfolding power2_eq_square by (by100 simp)
              thus False using \<open>fst p ^ 2 \<le> 1\<close> by (by100 linarith)
            qed
            show "fst p \<le> 1"
            proof (rule ccontr)
              assume "\<not> fst p \<le> 1"
              hence "fst p > 1" by (by100 linarith)
              hence "fst p * fst p > 1 * 1"
                by (intro mult_strict_mono') (by100 linarith)+
              hence "fst p ^ 2 > 1" unfolding power2_eq_square by (by100 simp)
              thus False using \<open>fst p ^ 2 \<le> 1\<close> by (by100 linarith)
            qed
          qed
          have hcos: "cos (arccos (fst p)) = fst p"
            by (rule cos_arccos[OF hx_bdd])
          have hsin: "sin (arccos (fst p)) = sqrt (1 - (fst p)^2)"
            by (rule sin_arccos[OF hx_bdd])
          have hsqrt_y: "sqrt (1 - (fst p)^2) = snd p"
          proof -
            have "1 - (fst p)^2 = (snd p)^2" using hcirc by (by100 linarith)
            hence "sqrt (1 - (fst p)^2) = sqrt ((snd p)^2)" by simp
            also have "\<dots> = \<bar>snd p\<bar>" by (rule real_sqrt_abs)
            also have "\<dots> = snd p" using hy_pos by (by100 simp)
            finally show ?thesis .
          qed
          have "top1_R_to_S1 (inv_fn p) = (cos (arccos (fst p)), sin (arccos (fst p)))"
            unfolding top1_R_to_S1_def inv_fn_def
            using cos_int_2pin[of nn] sin_int_2pin[of nn]
            by (simp add: distrib_left cos_add sin_add prod_eq_iff)
          also have "\<dots> = (fst p, snd p)" using hcos hsin hsqrt_y by simp
          also have "\<dots> = p" by simp
          finally have "top1_R_to_S1 (inv_fn p) = p" .
          thus "inv_into V top1_R_to_S1 p = inv_fn p"
            using inv_into_f_eq[OF hpV_inj hinV] by (by100 simp)
        qed
        \<comment> \<open>Transfer.\<close>
        have harc_eq: "subspace_topology top1_S1 top1_S1_topology top1_S1_arc_N
            = subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1_arc_N"
          unfolding top1_S1_topology_def
          using subspace_topology_trans[OF harc_sub]
          by (simp add: product_topology_on_open_sets[where ?'a=real and ?'b=real])
        have "top1_continuous_map_on top1_S1_arc_N
            (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1_arc_N)
            V (subspace_topology UNIV (top1_open_sets :: real set set) V) inv_fn"
          by (rule top1_continuous_map_on_subspace_open_sets_on[OF hinv_range hinv_co])
        hence hinv_fn_cont: "top1_continuous_map_on top1_S1_arc_N
            (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_N)
            V (subspace_topology UNIV top1_open_sets V) inv_fn"
          unfolding harc_eq .
        have "\<forall>p\<in>top1_S1_arc_N. inv_fn p = inv_into V top1_R_to_S1 p"
          using hinv_agree by (by100 auto)
        thus ?thesis by (rule top1_continuous_map_on_agree'[OF hinv_fn_cont])
      qed
      \<comment> \<open>Assembly.\<close>
      have hV_sub: "V \<subseteq> (UNIV::real set)" by (by100 blast)
      have hTV: "is_topology_on V (subspace_topology UNIV top1_open_sets V)"
        by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV hV_sub])
      have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
          (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
        using product_topology_on_is_topology_on[OF
              top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
      have hTarc: "is_topology_on top1_S1_arc_N
          (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_N)"
        by (rule subspace_topology_is_topology_on[OF hTS1]) (use harc_sub in \<open>by100 blast\<close>)
      show "top1_homeomorphism_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_N (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_N) top1_R_to_S1"
        unfolding top1_homeomorphism_on_def
        using hTV hTarc hbij hp_V_cont hinv_cont by (by100 blast)
    qed
    show ?thesis unfolding top1_evenly_covered_on_def
      using harc_N_open hV_open hV_disj hV_union hV_homeo by (by100 blast)
  qed
  have harc_W_ec: "top1_evenly_covered_on UNIV top1_open_sets
      top1_S1 top1_S1_topology top1_R_to_S1 top1_S1_arc_W"
  proof -
    \<comment> \<open>Arc W = {(x,y) \<in> S^1 | x < 0}. Preimage: cos(2\<pi>x) < 0, i.e., x \<in> (n+1/4, n+3/4).
       Each slice maps homeomorphically to arc_W.\<close>
    have harc_W_open: "openin_on top1_S1 top1_S1_topology top1_S1_arc_W"
    proof -
      have heq: "top1_S1_arc_W = top1_S1 \<inter> {p::real\<times>real. fst p < 0}"
        unfolding top1_S1_arc_W_def top1_S1_def by (by100 auto)
      have hopen: "open {p::real\<times>real. fst p < 0}"
        by (rule open_Collect_less) (auto intro: continuous_intros)
      have "{p::real\<times>real. fst p < 0} \<in> (top1_open_sets::(real\<times>real) set set)"
        using hopen unfolding top1_open_sets_def by (by100 blast)
      hence "{p::real\<times>real. fst p < 0} \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
        using product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 blast)
      thus ?thesis unfolding openin_on_def top1_S1_topology_def subspace_topology_def heq
        by (by100 blast)
    qed
    let ?\<V> = "{V. \<exists>n::int. V = {x::real. of_int n + 1/4 < x \<and> x < of_int n + 3/4}}"
    have hV_open: "\<forall>V\<in>?\<V>. openin_on (UNIV::real set) top1_open_sets V"
    proof
      fix V assume "V \<in> ?\<V>"
      then obtain n :: int where hV: "V = {x::real. of_int n + 1/4 < x \<and> x < of_int n + 3/4}"
        by (by100 blast)
      have "V = {of_int n + 1/4 <..< of_int n + 3/4}" using hV by (by100 auto)
      moreover have "open {of_int n + 1/4 <..< of_int n + (3/4::real)}" by (by100 simp)
      ultimately show "openin_on UNIV top1_open_sets V"
        unfolding openin_on_def top1_open_sets_def by (by100 blast)
    qed
    have hV_disj: "\<forall>V\<in>?\<V>. \<forall>V'\<in>?\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
    proof (intro ballI impI)
      fix V V' assume "V \<in> ?\<V>" "V' \<in> ?\<V>" "V \<noteq> V'"
      obtain n where hV: "V = {x::real. of_int n + 1/4 < x \<and> x < of_int n + 3/4}"
        using \<open>V \<in> ?\<V>\<close> by auto
      obtain m where hV': "V' = {x::real. of_int m + 1/4 < x \<and> x < of_int m + 3/4}"
        using \<open>V' \<in> ?\<V>\<close> by auto
      have hnm: "n \<noteq> m" using \<open>V \<noteq> V'\<close> hV hV' by (by100 force)
      show "V \<inter> V' = {}"
      proof (rule ccontr)
        assume "V \<inter> V' \<noteq> {}"
        then obtain x where "x \<in> V" "x \<in> V'" by (by100 blast)
        hence "of_int n + (1/4::real) < x" "x < of_int n + (3/4::real)"
            "of_int m + (1/4::real) < x" "x < of_int m + (3/4::real)"
          using hV hV' by (by100 blast)+
        hence "\<bar>of_int n - of_int m\<bar> < (1::real)" by (by100 linarith)
        hence "n = m" by (by100 linarith)
        thus False using hnm by (by100 blast)
      qed
    qed
    have hV_union: "{x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_W} = \<Union>?\<V>"
    proof (intro set_eqI iffI)
      fix x :: real
      assume "x \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_W}"
      hence hcos: "cos (2 * pi * x) < 0"
        unfolding top1_R_to_S1_def top1_S1_arc_W_def by (by100 auto)
      \<comment> \<open>cos(2\<pi>x) < 0 iff x \<in> (n+1/4, n+3/4) for some n.\<close>
      define nn where "nn = \<lfloor>x\<rfloor>"
      have hnn_le: "of_int nn \<le> x" and hx_lt: "x < of_int nn + 1"
        unfolding nn_def by linarith+
      have hfrac: "x - of_int nn \<ge> 0" "x - of_int nn < 1" using hnn_le hx_lt by linarith+
      have hshift: "cos (2 * pi * (x - of_int nn)) = cos (2 * pi * x)"
      proof -
        have "top1_R_to_S1 x = top1_R_to_S1 (x - of_int nn)"
          using top1_R_to_S1_int_shift_early[of "x - of_int nn" nn] by simp
        hence "fst (top1_R_to_S1 x) = fst (top1_R_to_S1 (x - of_int nn))" by simp
        thus ?thesis unfolding top1_R_to_S1_def by (by100 simp)
      qed
      have hcos_neg: "cos (2 * pi * (x - of_int nn)) < 0" using hcos hshift by (by100 linarith)
      have hpi: "pi > 0" by (rule pi_gt_zero)
      \<comment> \<open>frac \<in> (1/4, 3/4) by contradiction: cos \<ge> 0 outside this range.\<close>
      have hfrac_gt14: "x - of_int nn > 1/4"
      proof (rule ccontr)
        assume "\<not> x - of_int nn > 1/4"
        hence hle: "x - of_int nn \<le> 1/4" by (by100 linarith)
        \<comment> \<open>2\<pi>(x-n) \<le> \<pi>/2 and 2\<pi>(x-n) \<ge> 0. cos \<ge> 0 on [0, \<pi>/2].\<close>
        have h_nonneg: "0 \<le> 2 * pi * (x - of_int nn)" using hfrac hpi
          by (by100 simp)
        have hge_neg: "- (pi / 2) \<le> 2 * pi * (x - of_int nn)"
          using h_nonneg hpi by (by100 linarith)
        have hle_half: "2 * pi * (x - of_int nn) \<le> pi / 2"
        proof -
          have "2 * pi * (x - of_int nn) \<le> 2 * pi * (1/4)" using hle hpi by (by100 simp)
          also have "\<dots> = pi * (2 * (1/4::real))" by (simp add: algebra_simps)
          also have "\<dots> = pi / 2" by simp
          finally show ?thesis .
        qed
        have "cos (2 * pi * (x - of_int nn)) \<ge> 0"
          by (rule cos_ge_zero[OF hge_neg hle_half])
        thus False using hcos_neg by (by100 linarith)
      qed
      have hfrac_lt34: "x - of_int nn < 3/4"
      proof (rule ccontr)
        assume "\<not> x - of_int nn < 3/4"
        hence hge: "x - of_int nn \<ge> 3/4" by (by100 linarith)
        \<comment> \<open>2\<pi>(x-n) \<in> [3\<pi>/2, 2\<pi>). cos = cos(2\<pi>-(2\<pi>(x-n))) = cos(2\<pi>(1-(x-n))),
           and 1-(x-n) \<in> (0, 1/4], so 2\<pi>(1-(x-n)) \<in> (0, \<pi>/2]. cos \<ge> 0.\<close>
        \<comment> \<open>cos(2\<pi>(x-n)) = cos(2\<pi> - 2\<pi>(x-n)) = cos(2\<pi>(1-(x-n))).
           1-(x-n) \<in> (0, 1/4], so 2\<pi>(1-(x-n)) \<in> (0, \<pi>/2], cos \<ge> 0.\<close>
        have hcos_eq: "cos (2 * pi * (x - of_int nn)) = cos (2 * pi * (1 - (x - of_int nn)))"
        proof -
          \<comment> \<open>cos(t) = cos(2\<pi> - t) by periodicity + evenness.
             cos(2\<pi>*(1-f)) = cos(2\<pi> - 2\<pi>f) = cos(-(2\<pi>f - 2\<pi>)) = cos(2\<pi>f - 2\<pi>)
             = cos(2\<pi>f - 2\<pi> + 2\<pi>) = cos(2\<pi>f).\<close>
          let ?t = "2 * pi * (x - of_int nn)"
          let ?s = "2 * pi * (1 - (x - of_int nn))"
          have "?s = - ?t + 2 * pi" by (simp add: algebra_simps)
          hence "cos ?s = cos (- ?t + 2 * pi)" by simp
          also have "\<dots> = cos (- ?t)" using cos_periodic[of "- ?t"] by (simp add: algebra_simps)
          also have "\<dots> = cos ?t" by (rule cos_minus)
          finally show ?thesis by simp
        qed
        have h1mfrac: "0 < 1 - (x - of_int nn)" "1 - (x - of_int nn) \<le> 1/4"
          using hge hfrac by linarith+
        have h_nonneg2: "0 \<le> 2 * pi * (1 - (x - of_int nn))"
          using h1mfrac hpi by (by100 simp)
        have "- (pi / 2) \<le> 2 * pi * (1 - (x - of_int nn))"
          using h_nonneg2 hpi by (by100 linarith)
        moreover have "2 * pi * (1 - (x - of_int nn)) \<le> pi / 2"
        proof -
          have "2 * pi * (1 - (x - of_int nn)) \<le> 2 * pi * (1/4)" using h1mfrac hpi by (by100 simp)
          also have "\<dots> = pi * (2 * (1/4::real))" by (simp add: algebra_simps)
          also have "\<dots> = pi / 2" by simp
          finally show ?thesis .
        qed
        ultimately have "cos (2 * pi * (1 - (x - of_int nn))) \<ge> 0" by (rule cos_ge_zero)
        have "cos (2 * pi * (x - of_int nn)) \<ge> 0" using hcos_eq \<open>cos (2 * pi * (1 - (x - of_int nn))) \<ge> 0\<close> by (by100 linarith)
        thus False using hcos_neg by (by100 linarith)
      qed
      have hx_in: "x \<in> {x::real. of_int nn + 1/4 < x \<and> x < of_int nn + 3/4}"
        using hfrac_gt14 hfrac_lt34 by (by100 simp)
      have hV_in: "{x::real. of_int nn + 1/4 < x \<and> x < of_int nn + 3/4} \<in> ?\<V>"
        by (by100 blast)
      show "x \<in> \<Union>?\<V>" using hx_in hV_in by (by100 blast)
    next
      fix x :: real assume "x \<in> \<Union>?\<V>"
      then obtain n :: int where hn1: "of_int n + (1/4::real) < x" "x < of_int n + (3/4::real)"
        by (by100 auto)
      \<comment> \<open>2\<pi>(x-n) \<in> (\<pi>/2, 3\<pi>/2), so cos < 0.\<close>
      have hcos_neg: "cos (2 * pi * (x - of_int n)) < 0"
      proof -
        have hpi: "pi > 0" by (rule pi_gt_zero)
        have harg_gt: "pi / 2 < 2 * pi * (x - of_int n)"
        proof -
          have "pi / 2 = pi * (2 * (1/4::real))" by simp
          also have "\<dots> = 2 * pi * (1/4::real)" by (simp add: algebra_simps)
          also have "\<dots> < 2 * pi * (x - of_int n)" using hn1 hpi by (by100 simp)
          finally show ?thesis .
        qed
        have harg_lt: "2 * pi * (x - of_int n) < 3 * pi / 2"
        proof -
          have "2 * pi * (x - of_int n) < 2 * pi * (3/4::real)" using hn1 hpi by (by100 simp)
          also have "\<dots> = pi * (2 * (3/4::real))" by (simp add: algebra_simps)
          also have "\<dots> = pi * (3/2)" by simp
          also have "\<dots> = 3 * pi / 2" by (by100 linarith)
          finally show ?thesis .
        qed
        \<comment> \<open>cos(t) < 0 for t \<in> (\<pi>/2, 3\<pi>/2): use cos(t) = -cos(t - \<pi>) and cos_gt_zero_pi.\<close>
        have hcmp: "cos (2 * pi * (x - of_int n) - pi) = - cos (2 * pi * (x - of_int n))"
          using cos_minus_pi[of "2 * pi * (x - of_int n)"] by (by100 linarith)
        have hlo: "- (pi/2) < 2 * pi * (x - of_int n) - pi" using harg_gt by (by100 linarith)
        have hhi: "2 * pi * (x - of_int n) - pi < pi/2" using harg_lt by (by100 linarith)
        have "cos (2 * pi * (x - of_int n) - pi) > 0"
          by (rule cos_gt_zero_pi[OF hlo hhi])
        thus ?thesis using hcmp by (by100 linarith)
      qed
      have hshift: "cos (2 * pi * x) = cos (2 * pi * (x - of_int n))"
      proof -
        have "top1_R_to_S1 x = top1_R_to_S1 (x - of_int n)"
          using top1_R_to_S1_int_shift_early[of "x - of_int n" n] by simp
        hence "fst (top1_R_to_S1 x) = fst (top1_R_to_S1 (x - of_int n))" by simp
        thus ?thesis unfolding top1_R_to_S1_def by (by100 simp)
      qed
      have "cos (2 * pi * x) < 0" using hcos_neg hshift by (by100 linarith)
      moreover have "cos (2 * pi * x) ^ 2 + sin (2 * pi * x) ^ 2 = 1"
        by (rule sin_cos_squared_add2)
      ultimately show "x \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_W}"
        unfolding top1_R_to_S1_def top1_S1_arc_W_def by (by100 auto)
    qed
    have hV_homeo: "\<forall>V\<in>?\<V>.
        top1_homeomorphism_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_W (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_W) top1_R_to_S1"
    proof
      fix V assume hVmem: "V \<in> ?\<V>"
      then obtain nn :: int where hVeq: "V = {x::real. of_int nn + 1/4 < x \<and> x < of_int nn + 3/4}"
        by (by100 auto)
      have hpV: "\<forall>x\<in>V. top1_R_to_S1 x \<in> top1_S1_arc_W"
        using hV_union hVmem by (by100 blast)
      have harc_sub: "top1_S1_arc_W \<subseteq> top1_S1"
        unfolding top1_S1_arc_W_def top1_S1_def by (by100 auto)
      have hpV_surj: "top1_R_to_S1 ` V = top1_S1_arc_W"
      proof (intro equalityI subsetI)
        fix y assume "y \<in> top1_R_to_S1 ` V" thus "y \<in> top1_S1_arc_W" using hpV by (by100 blast)
      next
        fix y assume hy: "y \<in> top1_S1_arc_W"
        have "y \<in> top1_S1" using hy harc_sub by (by100 blast)
        hence "y \<in> top1_R_to_S1 ` UNIV" using hp_surj by (by100 blast)
        then obtain t where hpt: "top1_R_to_S1 t = y" by (by100 blast)
        hence "t \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_W}" using hy by (by100 simp)
        hence "t \<in> \<Union>?\<V>" using hV_union by (by100 blast)
        then obtain m :: int where htm: "of_int m + (1/4::real) < t" "t < of_int m + (3/4::real)"
          by (by100 auto)
        let ?t' = "t + of_int (nn - m)"
        have "of_int nn + (1/4::real) < ?t'" "?t' < of_int nn + (3/4::real)"
          using htm by (by100 linarith)+
        hence ht'V: "?t' \<in> V" unfolding hVeq by (by100 blast)
        have "top1_R_to_S1 ?t' = top1_R_to_S1 t"
          using top1_R_to_S1_int_shift_early[of t "nn - m"] by simp
        hence "top1_R_to_S1 ?t' = y" using hpt by (by100 simp)
        thus "y \<in> top1_R_to_S1 ` V" using ht'V by (by100 blast)
      qed
      have hpV_inj: "inj_on top1_R_to_S1 V"
      proof (rule inj_onI)
        fix x y assume hx: "x \<in> V" and hy: "y \<in> V"
            and heq: "top1_R_to_S1 x = top1_R_to_S1 y"
        have "sin (2 * pi * x) = sin (2 * pi * y)" "cos (2 * pi * x) = cos (2 * pi * y)"
          using heq unfolding top1_R_to_S1_def by (by100 simp)+
        then obtain k :: int where hk: "2*pi*x = 2*pi*y + 2*pi*of_int k"
          using iffD1[OF sin_cos_eq_iff] by (by100 blast)
        hence "2*pi * (x - y) = 2*pi * of_int k" by (simp add: algebra_simps)
        hence "x - y = of_int k" using pi_gt_zero by (by100 simp)
        moreover have "\<bar>x - y\<bar> < 1/2"
        proof -
          have "of_int nn + (1/4::real) < x" "x < of_int nn + (3/4::real)"
               "of_int nn + (1/4::real) < y" "y < of_int nn + (3/4::real)"
            using hx hy unfolding hVeq by (by100 blast)+
          thus ?thesis by (by100 linarith)
        qed
        hence "k = 0" using \<open>x - y = of_int k\<close> by (by100 linarith)
        ultimately show "x = y" by (by100 linarith)
      qed
      have hbij: "bij_betw top1_R_to_S1 V top1_S1_arc_W"
        unfolding bij_betw_def using hpV_inj hpV_surj by (by100 blast)
      have hp_V_img: "top1_R_to_S1 ` V \<subseteq> top1_S1_arc_W"
        using hpV by (by100 blast)
      have hV_sub_W: "V \<subseteq> (UNIV::real set)" by (by100 blast)
      have hp_V_cont: "top1_continuous_map_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_W (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_W) top1_R_to_S1"
        by (rule top1_continuous_map_on_codomain_shrink[OF
              top1_continuous_map_on_restrict_domain_simple[OF hp_cont hV_sub_W]
              hp_V_img harc_sub])
      have hinv_cont: "top1_continuous_map_on top1_S1_arc_W
          (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_W)
          V (subspace_topology UNIV top1_open_sets V) (inv_into V top1_R_to_S1)"
      proof -
        \<comment> \<open>Inverse: inv_fn(x,y) = arctan(y/x)/(2\<pi>) + 1/2 + nn.
           For x < 0, arctan(y/x) \<in> (-\<pi>/2, \<pi>/2), so arctan(y/x)/(2\<pi>) \<in> (-1/4, 1/4),
           giving inv_fn \<in> (nn+1/4, nn+3/4) = V.\<close>
        define inv_fn :: "real \<times> real \<Rightarrow> real"
          where "inv_fn \<equiv> \<lambda>p. arctan (snd p / fst p) / (2 * pi) + 1/2 + of_int nn"
        have hinv_co: "continuous_on top1_S1_arc_W inv_fn"
          unfolding inv_fn_def top1_S1_arc_W_def
          by (intro continuous_on_add continuous_on_const
              continuous_on_divide[OF _ continuous_on_const]
              continuous_on_compose2[OF continuous_on_arctan _ subset_UNIV]
              continuous_on_divide continuous_on_snd continuous_on_fst) (by100 auto)+
        have hinv_range: "\<And>p. p \<in> top1_S1_arc_W \<Longrightarrow> inv_fn p \<in> V"
        proof -
          fix p assume hp: "p \<in> top1_S1_arc_W"
          hence hx_neg: "fst p < 0" unfolding top1_S1_arc_W_def by (by100 auto)
          have "arctan (snd p / fst p) \<in> {-pi/2 <..< pi/2}"
            using arctan_bounded[of "snd p / fst p"] by (by100 simp)
          hence "arctan (snd p / fst p) / (2*pi) \<in> {-1/4 <..< 1/4}"
            using pi_gt_zero by (simp add: field_simps)
          thus "inv_fn p \<in> V" unfolding inv_fn_def hVeq by (by100 auto)
        qed
        have hinv_agree: "\<forall>p\<in>top1_S1_arc_W. inv_into V top1_R_to_S1 p = inv_fn p"
        proof
          fix p assume hp: "p \<in> top1_S1_arc_W"
          hence hx_neg: "fst p < 0" and hcirc: "fst p ^ 2 + snd p ^ 2 = 1"
            unfolding top1_S1_arc_W_def by (by100 auto)+
          have hinV: "inv_fn p \<in> V" using hinv_range[OF hp] .
          \<comment> \<open>sqrt(1 + (y/x)^2) = -1/x (since x < 0).\<close>
          have hsqrt: "sqrt (1 + (snd p / fst p)\<^sup>2) = - 1 / fst p"
          proof -
            have "1 + (snd p / fst p)^2 = ((fst p)^2 + (snd p)^2) / (fst p)^2"
              using hx_neg by (simp add: field_simps power2_eq_square)
            also have "\<dots> = 1 / (fst p)^2" using hcirc by (by100 simp)
            finally have "sqrt (1 + (snd p / fst p)^2) = sqrt (1 / (fst p)^2)" by (by100 simp)
            also have "\<dots> = 1 / \<bar>fst p\<bar>" by (simp add: real_sqrt_divide)
            also have "\<dots> = - 1 / fst p" using hx_neg by (by100 simp)
            finally show ?thesis .
          qed
          have hcos_at: "cos (arctan (snd p / fst p)) = - fst p"
            using cos_arctan[of "snd p / fst p"] hsqrt hx_neg by (by100 simp)
          have hsin_at: "sin (arctan (snd p / fst p)) = - snd p"
            using sin_arctan[of "snd p / fst p"] hsqrt hx_neg by (by100 simp)
          \<comment> \<open>cos(\<pi> + arctan(y/x)) = -cos(arctan(y/x)) = x.\<close>
          have hcos: "cos (2 * pi * inv_fn p) = fst p"
          proof -
            have "2 * pi * inv_fn p = (arctan (snd p / fst p) + pi) + (2 * pi) * of_int nn"
              unfolding inv_fn_def by (simp add: algebra_simps)
            hence "cos (2 * pi * inv_fn p) = cos ((arctan (snd p / fst p) + pi) + (2 * pi) * of_int nn)" by simp
            also have "\<dots> = cos (arctan (snd p / fst p) + pi)"
              by (simp add: cos_add cos_int_2pin sin_int_2pin)
            also have "\<dots> = - cos (arctan (snd p / fst p))" by (rule cos_periodic_pi)
            also have "\<dots> = fst p" using hcos_at by (by100 linarith)
            finally show ?thesis .
          qed
          have hsin: "sin (2 * pi * inv_fn p) = snd p"
          proof -
            have "2 * pi * inv_fn p = (arctan (snd p / fst p) + pi) + (2 * pi) * of_int nn"
              unfolding inv_fn_def by (simp add: algebra_simps)
            hence "sin (2 * pi * inv_fn p) = sin ((arctan (snd p / fst p) + pi) + (2 * pi) * of_int nn)" by simp
            also have "\<dots> = sin (arctan (snd p / fst p) + pi)"
              by (simp add: sin_add cos_int_2pin sin_int_2pin)
            also have "\<dots> = - sin (arctan (snd p / fst p))"
              by (rule sin_periodic_pi)
            also have "\<dots> = snd p" using hsin_at by (by100 linarith)
            finally show ?thesis .
          qed
          have "top1_R_to_S1 (inv_fn p) = (fst p, snd p)"
            unfolding top1_R_to_S1_def using hcos hsin by (by100 simp)
          hence "top1_R_to_S1 (inv_fn p) = p" by simp
          thus "inv_into V top1_R_to_S1 p = inv_fn p"
            using inv_into_f_eq[OF hpV_inj hinV] by (by100 simp)
        qed
        have harc_eq: "subspace_topology top1_S1 top1_S1_topology top1_S1_arc_W
            = subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1_arc_W"
          unfolding top1_S1_topology_def
          using subspace_topology_trans[OF harc_sub]
          by (simp add: product_topology_on_open_sets[where ?'a=real and ?'b=real])
        have "top1_continuous_map_on top1_S1_arc_W
            (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1_arc_W)
            V (subspace_topology UNIV (top1_open_sets :: real set set) V) inv_fn"
          by (rule top1_continuous_map_on_subspace_open_sets_on[OF hinv_range hinv_co])
        hence hinv_fn_cont: "top1_continuous_map_on top1_S1_arc_W
            (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_W)
            V (subspace_topology UNIV top1_open_sets V) inv_fn"
          unfolding harc_eq .
        have "\<forall>p\<in>top1_S1_arc_W. inv_fn p = inv_into V top1_R_to_S1 p"
          using hinv_agree by (by100 auto)
        thus ?thesis by (rule top1_continuous_map_on_agree'[OF hinv_fn_cont])
      qed
      have hV_sub: "V \<subseteq> (UNIV::real set)" by (by100 blast)
      have hTV: "is_topology_on V (subspace_topology UNIV top1_open_sets V)"
        by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV hV_sub])
      have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
          (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
        using product_topology_on_is_topology_on[OF
              top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
      have hTarc: "is_topology_on top1_S1_arc_W
          (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_W)"
        by (rule subspace_topology_is_topology_on[OF hTS1]) (use harc_sub in \<open>by100 blast\<close>)
      show "top1_homeomorphism_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_W (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_W) top1_R_to_S1"
        unfolding top1_homeomorphism_on_def
        using hTV hTarc hbij hp_V_cont hinv_cont by (by100 blast)
    qed
    show ?thesis unfolding top1_evenly_covered_on_def
      using harc_W_open hV_open hV_disj hV_union hV_homeo by (by100 blast)
  qed
  have harc_S_ec: "top1_evenly_covered_on UNIV top1_open_sets
      top1_S1 top1_S1_topology top1_R_to_S1 top1_S1_arc_S"
  proof -
    \<comment> \<open>Arc S = {(x,y) \<in> S^1 | y < 0}. Preimage: sin(2\<pi>x) < 0, i.e., x \<in> (n+1/2, n+1).
       Each slice maps homeomorphically to arc_S.\<close>
    have harc_S_open: "openin_on top1_S1 top1_S1_topology top1_S1_arc_S"
    proof -
      have heq: "top1_S1_arc_S = top1_S1 \<inter> {p::real\<times>real. snd p < 0}"
        unfolding top1_S1_arc_S_def top1_S1_def by (by100 auto)
      have hopen: "open {p::real\<times>real. snd p < 0}"
        by (rule open_Collect_less) (auto intro: continuous_intros)
      have "{p::real\<times>real. snd p < 0} \<in> (top1_open_sets::(real\<times>real) set set)"
        using hopen unfolding top1_open_sets_def by (by100 blast)
      hence "{p::real\<times>real. snd p < 0} \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
        using product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 blast)
      thus ?thesis unfolding openin_on_def top1_S1_topology_def subspace_topology_def heq
        by (by100 blast)
    qed
    let ?\<V> = "{V. \<exists>n::int. V = {x::real. of_int n + 1/2 < x \<and> x < of_int n + 1}}"
    have hV_open: "\<forall>V\<in>?\<V>. openin_on (UNIV::real set) top1_open_sets V"
    proof
      fix V assume "V \<in> ?\<V>"
      then obtain n :: int where hV: "V = {x::real. of_int n + 1/2 < x \<and> x < of_int n + 1}"
        by (by100 blast)
      have "V = {of_int n + 1/2 <..< of_int n + 1}" using hV by (by100 auto)
      moreover have "open {of_int n + 1/2 <..< of_int n + (1::real)}" by (by100 simp)
      ultimately show "openin_on UNIV top1_open_sets V"
        unfolding openin_on_def top1_open_sets_def by (by100 blast)
    qed
    have hV_disj: "\<forall>V\<in>?\<V>. \<forall>V'\<in>?\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
    proof (intro ballI impI)
      fix V V' assume "V \<in> ?\<V>" "V' \<in> ?\<V>" "V \<noteq> V'"
      obtain n where hV: "V = {x::real. of_int n + 1/2 < x \<and> x < of_int n + 1}"
        using \<open>V \<in> ?\<V>\<close> by auto
      obtain m where hV': "V' = {x::real. of_int m + 1/2 < x \<and> x < of_int m + 1}"
        using \<open>V' \<in> ?\<V>\<close> by auto
      have hnm: "n \<noteq> m" using \<open>V \<noteq> V'\<close> hV hV' by (by100 force)
      show "V \<inter> V' = {}"
      proof (rule ccontr)
        assume "V \<inter> V' \<noteq> {}"
        then obtain x where "x \<in> V" "x \<in> V'" by (by100 blast)
        hence "of_int n + (1/2::real) < x" "x < of_int n + (1::real)"
            "of_int m + (1/2::real) < x" "x < of_int m + (1::real)"
          using hV hV' by (by100 blast)+
        hence "\<bar>of_int n - of_int m\<bar> < (1::real)" by (by100 linarith)
        hence "n = m" by (by100 linarith)
        thus False using hnm by (by100 blast)
      qed
    qed
    have hV_union: "{x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_S} = \<Union>?\<V>"
    proof (intro set_eqI iffI)
      fix x :: real
      assume hx: "x \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_S}"
      hence hsin: "sin (2 * pi * x) < 0"
        unfolding top1_R_to_S1_def top1_S1_arc_S_def by (by100 auto)
      define n where "n = \<lfloor>x\<rfloor>"
      have hn_le: "of_int n \<le> x" and hx_lt: "x < of_int n + 1"
        unfolding n_def by linarith+
      have hfrac: "x - of_int n \<ge> 0" "x - of_int n < 1" using hn_le hx_lt by linarith+
      have hshift: "sin (2 * pi * (x - of_int n)) = sin (2 * pi * x)"
      proof -
        have "top1_R_to_S1 x = top1_R_to_S1 (x - of_int n)"
          using top1_R_to_S1_int_shift_early[of "x - of_int n" n] by simp
        hence "snd (top1_R_to_S1 x) = snd (top1_R_to_S1 (x - of_int n))" by simp
        thus ?thesis unfolding top1_R_to_S1_def by (by100 simp)
      qed
      have hfrac_neg: "sin (2 * pi * (x - of_int n)) < 0" using hsin hshift by (by100 linarith)
      \<comment> \<open>sin(2\<pi>t) < 0 for t \<in> (1/2, 1): sin = 0 at 0 and 1/2, > 0 on (0, 1/2), < 0 on (1/2, 1).\<close>
      have hfrac_gt: "x - of_int n > 1/2"
      proof (rule ccontr)
        assume "\<not> x - of_int n > 1/2"
        hence hle: "x - of_int n \<le> 1/2" by (by100 linarith)
        show False
        proof (cases "x - of_int n = 0")
          case True thus False using hfrac_neg by simp
        next
          case False
          hence hgt0: "x - of_int n > 0" using hfrac by (by100 linarith)
          show False
          proof (cases "x - of_int n = 1/2")
            case True
            have "x - of_int n = 1/2" using True .
            have "x - of_int n = 1/2" using True .
            hence "sin (2 * pi * (x - of_int n)) = sin (pi * (2 * (1/2)))"
              by (simp add: algebra_simps)
            also have "pi * (2 * (1/2::real)) = pi" by simp
            also have "sin pi = 0" by simp
            finally have "sin (2 * pi * (x - of_int n)) = 0" .
            hence "sin (2 * pi * (x - of_int n)) = 0" by simp
            thus False using hfrac_neg by (by100 linarith)
          next
            case False
            hence hlt12: "x - of_int n < 1/2" using hle by (by100 linarith)
            have hpi: "pi > 0" by (rule pi_gt_zero)
            have "0 < 2 * pi * (x - of_int n)" using hgt0 hpi by (by100 simp)
            moreover have "2 * pi * (x - of_int n) < pi"
            proof -
              have "2 * pi * (x - of_int n) < 2 * pi * (1/2::real)" using hlt12 hpi by (by100 simp)
              also have "\<dots> = pi * (2 * (1/2::real))" by (simp add: algebra_simps)
              also have "\<dots> = pi" by simp
              finally show ?thesis .
            qed
            ultimately have "sin (2 * pi * (x - of_int n)) > 0" by (rule sin_gt_zero)
            thus False using hfrac_neg by (by100 linarith)
          qed
        qed
      qed
      have "x \<in> {x::real. of_int n + 1/2 < x \<and> x < of_int n + 1}"
        using hfrac_gt hfrac by (by100 simp)
      thus "x \<in> \<Union>?\<V>" by (by100 blast)
    next
      fix x :: real assume "x \<in> \<Union>?\<V>"
      then obtain n :: int where hn1: "of_int n + (1/2::real) < x" and hn2: "x < of_int n + 1"
        by (by100 auto)
      have hpi: "pi > 0" by (rule pi_gt_zero)
      have hpi_lt: "pi < 2 * pi * (x - of_int n)"
      proof -
        have "pi = pi * (2 * (1/2::real))" by simp
        also have "\<dots> = 2 * pi * (1/2::real)" by (simp add: algebra_simps)
        also have "\<dots> < 2 * pi * (x - of_int n)" using hn1 hpi by (by100 simp)
        finally show ?thesis .
      qed
      have h2pi_gt: "2 * pi * (x - of_int n) < 2 * pi"
      proof -
        have "2 * pi * (x - of_int n) < 2 * pi * 1" using hn2 hpi by (by100 simp)
        thus ?thesis by simp
      qed
      have hsin_neg: "sin (2 * pi * (x - of_int n)) < 0"
        by (rule sin_lt_zero[OF hpi_lt h2pi_gt])
      have hshift: "sin (2 * pi * x) = sin (2 * pi * (x - of_int n))"
      proof -
        have "top1_R_to_S1 x = top1_R_to_S1 (x - of_int n)"
          using top1_R_to_S1_int_shift_early[of "x - of_int n" n] by simp
        hence "snd (top1_R_to_S1 x) = snd (top1_R_to_S1 (x - of_int n))" by simp
        thus ?thesis unfolding top1_R_to_S1_def by (by100 simp)
      qed
      have "sin (2 * pi * x) < 0" using hsin_neg hshift by (by100 linarith)
      moreover have "cos (2 * pi * x) ^ 2 + sin (2 * pi * x) ^ 2 = 1"
        by (rule sin_cos_squared_add2)
      ultimately show "x \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_S}"
        unfolding top1_R_to_S1_def top1_S1_arc_S_def by (by100 auto)
    qed
    have hV_homeo: "\<forall>V\<in>?\<V>.
        top1_homeomorphism_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_S (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_S) top1_R_to_S1"
    proof
      fix V assume hVmem: "V \<in> ?\<V>"
      then obtain nn :: int where hVeq: "V = {x::real. of_int nn + 1/2 < x \<and> x < of_int nn + 1}"
        by (by100 auto)
      have hpV: "\<forall>x\<in>V. top1_R_to_S1 x \<in> top1_S1_arc_S"
        using hV_union hVmem by (by100 blast)
      have harc_sub: "top1_S1_arc_S \<subseteq> top1_S1"
        unfolding top1_S1_arc_S_def top1_S1_def by (by100 auto)
      have hpV_surj: "top1_R_to_S1 ` V = top1_S1_arc_S"
      proof (intro equalityI subsetI)
        fix y assume "y \<in> top1_R_to_S1 ` V" thus "y \<in> top1_S1_arc_S" using hpV by (by100 blast)
      next
        fix y assume hy: "y \<in> top1_S1_arc_S"
        have "y \<in> top1_S1" using hy harc_sub by (by100 blast)
        hence "y \<in> top1_R_to_S1 ` UNIV" using hp_surj by (by100 blast)
        then obtain t where hpt: "top1_R_to_S1 t = y" by (by100 blast)
        hence "t \<in> {x \<in> UNIV. top1_R_to_S1 x \<in> top1_S1_arc_S}" using hy by (by100 simp)
        hence "t \<in> \<Union>?\<V>" using hV_union by (by100 blast)
        then obtain m :: int where htm: "of_int m + (1/2::real) < t" "t < of_int m + (1::real)"
          by auto
        let ?t' = "t + of_int (nn - m)"
        have "of_int nn + (1/2::real) < ?t'" "?t' < of_int nn + (1::real)"
          using htm by (by100 linarith)+
        hence ht'V: "?t' \<in> V" unfolding hVeq by (by100 blast)
        have "top1_R_to_S1 ?t' = top1_R_to_S1 t"
          using top1_R_to_S1_int_shift_early[of t "nn - m"] by simp
        hence "top1_R_to_S1 ?t' = y" using hpt by (by100 simp)
        thus "y \<in> top1_R_to_S1 ` V" using ht'V by (by100 blast)
      qed
      have hpV_inj: "inj_on top1_R_to_S1 V"
      proof (rule inj_onI)
        fix x y assume hx: "x \<in> V" and hy: "y \<in> V"
            and heq: "top1_R_to_S1 x = top1_R_to_S1 y"
        have "sin (2 * pi * x) = sin (2 * pi * y)" "cos (2 * pi * x) = cos (2 * pi * y)"
          using heq unfolding top1_R_to_S1_def by (by100 simp)+
        then obtain k :: int where hk: "2*pi*x = 2*pi*y + 2*pi*of_int k"
          using iffD1[OF sin_cos_eq_iff] by (by100 blast)
        hence "2*pi * (x - y) = 2*pi * of_int k" by (simp add: algebra_simps)
        hence "x - y = of_int k" using pi_gt_zero by (by100 simp)
        moreover have "\<bar>x - y\<bar> < 1/2"
        proof -
          have "of_int nn + (1/2::real) < x" "x < of_int nn + (1::real)"
               "of_int nn + (1/2::real) < y" "y < of_int nn + (1::real)"
            using hx hy unfolding hVeq by (by100 blast)+
          thus ?thesis by (by100 linarith)
        qed
        hence "k = 0" using \<open>x - y = of_int k\<close> by (by100 linarith)
        ultimately show "x = y" by (by100 linarith)
      qed
      have hbij: "bij_betw top1_R_to_S1 V top1_S1_arc_S"
        unfolding bij_betw_def using hpV_inj hpV_surj by (by100 blast)
      have hp_V_img: "top1_R_to_S1 ` V \<subseteq> top1_S1_arc_S"
        using hpV by (by100 blast)
      have hV_sub_S: "V \<subseteq> (UNIV::real set)" by (by100 blast)
      have hp_V_cont: "top1_continuous_map_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_S (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_S) top1_R_to_S1"
        by (rule top1_continuous_map_on_codomain_shrink[OF
              top1_continuous_map_on_restrict_domain_simple[OF hp_cont hV_sub_S]
              hp_V_img harc_sub])
      have hinv_cont: "top1_continuous_map_on top1_S1_arc_S
          (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_S)
          V (subspace_topology UNIV top1_open_sets V) (inv_into V top1_R_to_S1)"
      proof -
        \<comment> \<open>Inverse: inv_fn(x,y) = 1 - arccos(x)/(2\<pi>) + nn.
           For y < 0, the angle is 2\<pi> - arccos(x), so t = (2\<pi> - arccos(x))/(2\<pi>) + nn.\<close>
        define inv_fn :: "real \<times> real \<Rightarrow> real"
          where "inv_fn \<equiv> \<lambda>p. 1 - arccos (fst p) / (2 * pi) + of_int nn"
        have hfst_bdd: "\<forall>p\<in>top1_S1_arc_S. -1 \<le> fst p \<and> fst p \<le> 1"
        proof (intro ballI conjI)
          fix p assume hp: "p \<in> top1_S1_arc_S"
          have hy_neg: "snd p < 0" and hcirc: "fst p ^ 2 + snd p ^ 2 = 1"
            using hp unfolding top1_S1_arc_S_def by (by100 auto)+
          have "0 \<le> snd p ^ 2" by simp
          hence "fst p ^ 2 \<le> 1" using hcirc by (by100 linarith)
          show "-1 \<le> fst p"
          proof (rule ccontr)
            assume "\<not> -1 \<le> fst p"
            hence "- fst p > 1" by (by100 linarith)
            hence "(- fst p) * (- fst p) > 1 * 1"
              by (intro mult_strict_mono') (by100 linarith)+
            hence "fst p ^ 2 > 1" unfolding power2_eq_square by (by100 simp)
            thus False using \<open>fst p ^ 2 \<le> 1\<close> by (by100 linarith)
          qed
          show "fst p \<le> 1"
          proof (rule ccontr)
            assume "\<not> fst p \<le> 1"
            hence "fst p > 1" by (by100 linarith)
            hence "fst p * fst p > 1 * 1"
              by (intro mult_strict_mono') (by100 linarith)+
            hence "fst p ^ 2 > 1" unfolding power2_eq_square by (by100 simp)
            thus False using \<open>fst p ^ 2 \<le> 1\<close> by (by100 linarith)
          qed
        qed
        have hinv_co: "continuous_on top1_S1_arc_S inv_fn"
          unfolding inv_fn_def
          by (intro continuous_on_add continuous_on_diff continuous_on_const
              continuous_on_divide[OF _ continuous_on_const]
              continuous_on_arccos continuous_on_fst)
             (use hfst_bdd pi_gt_zero in \<open>by100 auto\<close>)+
        have hinv_range: "\<And>p. p \<in> top1_S1_arc_S \<Longrightarrow> inv_fn p \<in> V"
        proof -
          fix p assume hp: "p \<in> top1_S1_arc_S"
          hence hy_neg: "snd p < 0" and hcirc: "fst p ^ 2 + snd p ^ 2 = 1"
            unfolding top1_S1_arc_S_def by (by100 auto)+
          have hx_strict: "-1 < fst p" "fst p < 1"
          proof -
            show "-1 < fst p"
            proof (rule ccontr)
              assume "\<not> -1 < fst p" hence "fst p \<le> -1" by (by100 linarith)
              hence "(- fst p) * (- fst p) \<ge> 1 * 1"
                by (intro mult_mono') (by100 linarith)+
              hence "snd p ^ 2 \<le> 0" using hcirc unfolding power2_eq_square by (by100 linarith)
              moreover have "snd p ^ 2 > 0" using hy_neg unfolding power2_eq_square
                by (intro mult_neg_neg) (by100 linarith)+
              ultimately show False by (by100 linarith)
            qed
            show "fst p < 1"
            proof (rule ccontr)
              assume "\<not> fst p < 1" hence "fst p \<ge> 1" by (by100 linarith)
              hence "fst p * fst p \<ge> 1 * 1"
                by (intro mult_mono') (by100 linarith)+
              hence "snd p ^ 2 \<le> 0" using hcirc unfolding power2_eq_square by (by100 linarith)
              moreover have "snd p ^ 2 > 0" using hy_neg unfolding power2_eq_square
                by (intro mult_neg_neg) (by100 linarith)+
              ultimately show False by (by100 linarith)
            qed
          qed
          have hbdd: "0 < arccos (fst p) \<and> arccos (fst p) < pi"
            by (rule arccos_lt_bounded[OF hx_strict])
          have hpi: "pi > 0" by (rule pi_gt_zero)
          have "1/2 < 1 - arccos (fst p) / (2 * pi)"
          proof -
            have "arccos (fst p) / (2 * pi) < 1/2" using hbdd hpi by (by100 simp)
            thus ?thesis by (by100 linarith)
          qed
          moreover have "1 - arccos (fst p) / (2 * pi) < 1"
            using hbdd hpi by (by100 simp)
          ultimately show "inv_fn p \<in> V"
            unfolding inv_fn_def hVeq by (by100 auto)
        qed
        have hinv_agree: "\<forall>p\<in>top1_S1_arc_S. inv_into V top1_R_to_S1 p = inv_fn p"
        proof
          fix p assume hp: "p \<in> top1_S1_arc_S"
          hence hy_neg: "snd p < 0" and hcirc: "fst p ^ 2 + snd p ^ 2 = 1"
            unfolding top1_S1_arc_S_def by (by100 auto)+
          have hinV: "inv_fn p \<in> V" using hinv_range[OF hp] .
          have hx_bdd: "-1 \<le> fst p" "fst p \<le> 1" using hfst_bdd hp by (by100 blast)+
          \<comment> \<open>cos(2\<pi> \<cdot> inv_fn) = cos(2\<pi> - arccos(x) + 2\<pi>nn) = cos(2\<pi> - arccos(x)) = cos(arccos(x)) = x.\<close>
          have hcos: "cos (2 * pi * inv_fn p) = fst p"
          proof -
            have "2 * pi * inv_fn p = (2 * pi - arccos (fst p)) + (2 * pi) * of_int nn"
              unfolding inv_fn_def by (simp add: algebra_simps)
            hence "cos (2 * pi * inv_fn p) = cos ((2 * pi - arccos (fst p)) + (2 * pi) * of_int nn)"
              by simp
            also have "\<dots> = cos (2 * pi - arccos (fst p))"
              by (simp add: cos_add cos_int_2pin sin_int_2pin)
            also have "\<dots> = cos (- arccos (fst p) + 2 * pi)" by (simp add: algebra_simps)
            also have "\<dots> = cos (- arccos (fst p))"
              using cos_periodic[of "- arccos (fst p)"] by (simp add: algebra_simps)
            also have "\<dots> = cos (arccos (fst p))" by (rule cos_minus)
            also have "\<dots> = fst p" by (rule cos_arccos[OF hx_bdd])
            finally show ?thesis .
          qed
          \<comment> \<open>sin(2\<pi> \<cdot> inv_fn) = sin(2\<pi> - arccos(x)) = -sin(arccos(x)) = -sqrt(1-x^2) = y.\<close>
          have hsin: "sin (2 * pi * inv_fn p) = snd p"
          proof -
            have "2 * pi * inv_fn p = (2 * pi - arccos (fst p)) + (2 * pi) * of_int nn"
              unfolding inv_fn_def by (simp add: algebra_simps)
            hence "sin (2 * pi * inv_fn p) = sin ((2 * pi - arccos (fst p)) + (2 * pi) * of_int nn)"
              by simp
            also have "\<dots> = sin (2 * pi - arccos (fst p))"
              by (simp add: sin_add cos_int_2pin sin_int_2pin)
            also have "\<dots> = sin (- arccos (fst p) + 2 * pi)" by (simp add: algebra_simps)
            also have "\<dots> = sin (- arccos (fst p))"
              using sin_periodic[of "- arccos (fst p)"] by (simp add: algebra_simps)
            also have "\<dots> = - sin (arccos (fst p))" by simp
            also have "\<dots> = - sqrt (1 - (fst p)^2)" by (simp add: sin_arccos[OF hx_bdd])
            also have "\<dots> = snd p"
            proof -
              have "1 - (fst p)^2 = (snd p)^2" using hcirc by (by100 linarith)
              hence "sqrt (1 - (fst p)^2) = sqrt ((snd p)^2)" by simp
              also have "\<dots> = \<bar>snd p\<bar>" by (rule real_sqrt_abs)
              also have "\<dots> = - snd p" using hy_neg by (by100 simp)
              finally show "- sqrt (1 - (fst p)^2) = snd p" by (by100 linarith)
            qed
            finally show ?thesis .
          qed
          have "top1_R_to_S1 (inv_fn p) = (fst p, snd p)"
            unfolding top1_R_to_S1_def using hcos hsin by (by100 simp)
          hence "top1_R_to_S1 (inv_fn p) = p" by simp
          thus "inv_into V top1_R_to_S1 p = inv_fn p"
            using inv_into_f_eq[OF hpV_inj hinV] by (by100 simp)
        qed
        have harc_eq: "subspace_topology top1_S1 top1_S1_topology top1_S1_arc_S
            = subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1_arc_S"
          unfolding top1_S1_topology_def
          using subspace_topology_trans[OF harc_sub]
          by (simp add: product_topology_on_open_sets[where ?'a=real and ?'b=real])
        have "top1_continuous_map_on top1_S1_arc_S
            (subspace_topology UNIV (top1_open_sets :: (real\<times>real) set set) top1_S1_arc_S)
            V (subspace_topology UNIV (top1_open_sets :: real set set) V) inv_fn"
          by (rule top1_continuous_map_on_subspace_open_sets_on[OF hinv_range hinv_co])
        hence hinv_fn_cont: "top1_continuous_map_on top1_S1_arc_S
            (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_S)
            V (subspace_topology UNIV top1_open_sets V) inv_fn"
          unfolding harc_eq .
        have "\<forall>p\<in>top1_S1_arc_S. inv_fn p = inv_into V top1_R_to_S1 p"
          using hinv_agree by (by100 auto)
        thus ?thesis by (rule top1_continuous_map_on_agree'[OF hinv_fn_cont])
      qed
      have hV_sub: "V \<subseteq> (UNIV::real set)" by (by100 blast)
      have hTV: "is_topology_on V (subspace_topology UNIV top1_open_sets V)"
        by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV hV_sub])
      have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
          (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
        using product_topology_on_is_topology_on[OF
              top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by (by100 simp)
      have hTS1: "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF hTR2]) (by100 simp)
      have hTarc: "is_topology_on top1_S1_arc_S
          (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_S)"
        by (rule subspace_topology_is_topology_on[OF hTS1]) (use harc_sub in \<open>by100 blast\<close>)
      show "top1_homeomorphism_on V (subspace_topology UNIV top1_open_sets V)
          top1_S1_arc_S (subspace_topology top1_S1 top1_S1_topology top1_S1_arc_S) top1_R_to_S1"
        unfolding top1_homeomorphism_on_def
        using hTV hTarc hbij hp_V_cont hinv_cont by (by100 blast)
    qed
    show ?thesis unfolding top1_evenly_covered_on_def
      using harc_S_open hV_open hV_disj hV_union hV_homeo by (by100 blast)
  qed
  have hp_evenly: "\<forall>b\<in>top1_S1. \<exists>U. openin_on top1_S1 top1_S1_topology U \<and> b \<in> U
      \<and> top1_evenly_covered_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1 U"
  proof
    fix b assume hb: "b \<in> top1_S1"
    have "b \<in> top1_S1_arc_E \<or> b \<in> top1_S1_arc_W \<or> b \<in> top1_S1_arc_N \<or> b \<in> top1_S1_arc_S"
      using top1_S1_arcs_cover hb by (by100 blast)
    thus "\<exists>U. openin_on top1_S1 top1_S1_topology U \<and> b \<in> U
        \<and> top1_evenly_covered_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1 U"
    proof (elim disjE)
      assume hb': "b \<in> top1_S1_arc_E"
      have "openin_on top1_S1 top1_S1_topology top1_S1_arc_E"
        using harc_E_ec unfolding top1_evenly_covered_on_def by (by100 blast)
      thus ?thesis using hb' harc_E_ec by (by100 blast)
    next
      assume hb': "b \<in> top1_S1_arc_W"
      have "openin_on top1_S1 top1_S1_topology top1_S1_arc_W"
        using harc_W_ec unfolding top1_evenly_covered_on_def by (by100 blast)
      thus ?thesis using hb' harc_W_ec by (by100 blast)
    next
      assume hb': "b \<in> top1_S1_arc_N"
      have "openin_on top1_S1 top1_S1_topology top1_S1_arc_N"
        using harc_N_ec unfolding top1_evenly_covered_on_def by (by100 blast)
      thus ?thesis using hb' harc_N_ec by (by100 blast)
    next
      assume hb': "b \<in> top1_S1_arc_S"
      have "openin_on top1_S1 top1_S1_topology top1_S1_arc_S"
        using harc_S_ec unfolding top1_evenly_covered_on_def by (by100 blast)
      thus ?thesis using hb' harc_S_ec by (by100 blast)
    qed
  qed
  show ?thesis unfolding top1_covering_map_on_def
  proof (intro conjI)
    show "top1_continuous_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
      by (rule hp_cont)
    show "top1_R_to_S1 ` UNIV = top1_S1" by (rule hp_surj)
    show "\<forall>b\<in>top1_S1. \<exists>U. b \<in> U \<and>
        top1_evenly_covered_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1 U"
    proof
      fix b assume "b \<in> top1_S1"
      then obtain U where "openin_on top1_S1 top1_S1_topology U" "b \<in> U"
          "top1_evenly_covered_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1 U"
        using hp_evenly by (by100 blast)
      thus "\<exists>U. b \<in> U \<and>
          top1_evenly_covered_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1 U"
        by (by100 blast)
    qed
  qed
qed

(** from \<S>53 Theorem 53.2: restriction of a covering map to a subspace is a covering map.
    Uses strict topology: subspace of strict is strict. **)
theorem Theorem_53_2:
  assumes "top1_covering_map_on E TE B TB p"
      and "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "B0 \<subseteq> B"
      and "E0 = {e\<in>E. p e \<in> B0}"
  shows "top1_covering_map_on E0 (subspace_topology E TE E0)
    B0 (subspace_topology B TB B0) p"
proof -
  \<comment> \<open>Munkres 53.2: restrict covering to subspace.\<close>
  have hE0sub: "E0 \<subseteq> E" using assms(5) by (by100 blast)
  have hp_cont: "top1_continuous_map_on E0 (subspace_topology E TE E0)
      B0 (subspace_topology B TB B0) p"
  proof -
    have hp_E_B: "top1_continuous_map_on E TE B TB p"
      using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
    have hp_E0_B: "top1_continuous_map_on E0 (subspace_topology E TE E0) B TB p"
      by (rule top1_continuous_map_on_restrict_domain_simple[OF hp_E_B hE0sub])
    have himg: "p ` E0 \<subseteq> B0" using assms(5) by (by100 blast)
    show ?thesis
      by (rule top1_continuous_map_on_codomain_shrink[OF hp_E0_B himg assms(4)])
  qed
  have hp_surj: "p ` E0 = B0"
  proof (rule set_eqI, rule iffI)
    fix b assume "b \<in> p ` E0"
    thus "b \<in> B0" using assms(5) by (by100 blast)
  next
    fix b assume hb: "b \<in> B0"
    have "p ` E = B" using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
    hence "\<exists>e\<in>E. p e = b" using hb assms(4) by (by100 blast)
    then obtain e where he: "e \<in> E" "p e = b" by (by100 blast)
    have "e \<in> E0" using he hb assms(5) by (by100 blast)
    thus "b \<in> p ` E0" using he by (by100 blast)
  qed
  have hp_evenly: "\<forall>b0\<in>B0. \<exists>U0. b0 \<in> U0 \<and>
      top1_evenly_covered_on E0 (subspace_topology E TE E0) B0 (subspace_topology B TB B0) p U0"
  proof
    fix b0 assume hb0: "b0 \<in> B0"
    \<comment> \<open>b0 \<in> B, so there exists evenly covered U \<ni> b0 in B.\<close>
    have hb0B: "b0 \<in> B" using hb0 assms(4) by (by100 blast)
    obtain U where hU: "b0 \<in> U" and hUec: "top1_evenly_covered_on E TE B TB p U"
      using top1_covering_map_on_evenly_covered[OF assms(1) hb0B] by (by100 blast)
    \<comment> \<open>U0 = U \<inter> B0 is open in B0. The slices V\<alpha> \<inter> E0 partition p\<inverse>(U0) \<inter> E0.\<close>
    let ?U0 = "U \<inter> B0"
    have "b0 \<in> ?U0" using hU hb0 by (by100 blast)
    moreover have "top1_evenly_covered_on E0 (subspace_topology E TE E0)
        B0 (subspace_topology B TB B0) p ?U0"
    proof -
      \<comment> \<open>From hUec: U is evenly covered by slices \<V> in E.\<close>
      obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
          and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
          and hV_union: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
          and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                           (subspace_topology B TB U) p"
        using hUec unfolding top1_evenly_covered_on_def by auto
      \<comment> \<open>Restrict slices: \<V>0 = {V \<inter> E0 | V \<in> \<V>}.\<close>
      let ?\<V>0 = "{V \<inter> E0 | V. V \<in> \<V>}"
      \<comment> \<open>Need: U \<inter> B0 is open in B0; slices are open, disjoint, partition, homeomorphic.\<close>
      show ?thesis unfolding top1_evenly_covered_on_def
      proof (intro conjI exI[of _ ?\<V>0])
        \<comment> \<open>U \<inter> B0 is open in B0.\<close>
        show "openin_on B0 (subspace_topology B TB B0) (?U0)"
        proof -
          have hUopen: "U \<in> TB"
            using hUec unfolding top1_evenly_covered_on_def openin_on_def by (by100 blast)
          have "?U0 = B0 \<inter> U" by (by100 blast)
          also have "\<dots> \<in> subspace_topology B TB B0"
            unfolding subspace_topology_def using hUopen by (by100 blast)
          finally have "?U0 \<in> subspace_topology B TB B0" .
          moreover have "?U0 \<subseteq> B0" by (by100 blast)
          ultimately show ?thesis unfolding openin_on_def by (by100 blast)
        qed
        \<comment> \<open>Restricted slices are open in E0.\<close>
        show "\<forall>V\<in>?\<V>0. openin_on E0 (subspace_topology E TE E0) V"
        proof (intro ballI)
          fix V0 assume "V0 \<in> ?\<V>0"
          then obtain V where hV: "V \<in> \<V>" and hV0eq: "V0 = V \<inter> E0" by (by100 blast)
          have hVTE: "V \<in> TE" using hV hV_open unfolding openin_on_def by (by100 blast)
          have "V0 \<in> subspace_topology E TE E0"
            unfolding subspace_topology_def hV0eq using hVTE by (by100 auto)
          moreover have "V0 \<subseteq> E0" unfolding hV0eq by (by100 blast)
          ultimately show "openin_on E0 (subspace_topology E TE E0) V0"
            unfolding openin_on_def by (by100 blast)
        qed
        \<comment> \<open>Restricted slices are pairwise disjoint.\<close>
        show "\<forall>V\<in>?\<V>0. \<forall>V'\<in>?\<V>0. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
          using hV_disj by (by100 auto)
        \<comment> \<open>Restricted slices partition p⁻¹(U \<inter> B0) \<inter> E0.\<close>
        show "{x \<in> E0. p x \<in> ?U0} = \<Union>?\<V>0"
        proof (intro set_eqI iffI)
          fix x assume "x \<in> {x \<in> E0. p x \<in> ?U0}"
          hence hxE0: "x \<in> E0" and hpxU: "p x \<in> U" and hpxB0: "p x \<in> B0" by (by100 simp)+
          have hxE: "x \<in> E" using hxE0 hE0sub by (by100 blast)
          hence "x \<in> \<Union>\<V>" using hpxU hV_union by (by100 blast)
          then obtain V where hV: "V \<in> \<V>" and hxV: "x \<in> V" by (by100 blast)
          have "x \<in> V \<inter> E0" using hxV hxE0 by (by100 blast)
          thus "x \<in> \<Union>?\<V>0" using hV by (by100 blast)
        next
          fix x assume "x \<in> \<Union>?\<V>0"
          then obtain V where hV: "V \<in> \<V>" and hxVE0: "x \<in> V \<inter> E0" by (by100 blast)
          have hxE: "x \<in> E" using hxVE0 hE0sub by (by100 blast)
          have "x \<in> \<Union>\<V>" using hV hxVE0 by (by100 blast)
          hence "x \<in> {x\<in>E. p x \<in> U}" using hV_union by (by100 simp)
          hence "p x \<in> U" by (by100 simp)
          moreover have "p x \<in> B0" using hxVE0 assms(5) by (by100 simp)
          moreover have "x \<in> E0" using hxVE0 by (by100 blast)
          ultimately show "x \<in> {x \<in> E0. p x \<in> ?U0}" by (by100 simp)
        qed
        \<comment> \<open>p restricted to each slice is a homeomorphism.\<close>
        show "\<forall>V\<in>?\<V>0. top1_homeomorphism_on V (subspace_topology E0 (subspace_topology E TE E0) V)
            ?U0 (subspace_topology B0 (subspace_topology B TB B0) ?U0) p"
        proof (intro ballI)
          fix V0 assume hV0: "V0 \<in> ?\<V>0"
          then obtain V where hV: "V \<in> \<V>" and hV0eq: "V0 = V \<inter> E0" by (by100 blast)
          have hVhomeo: "top1_homeomorphism_on V (subspace_topology E TE V) U
                (subspace_topology B TB U) p"
            using hV hV_homeo by (by100 blast)
          \<comment> \<open>Subspace topology: subspace of subspace = subspace of ambient.\<close>
          have hV0_sub_V: "V0 \<subseteq> V" using hV0eq by (by100 blast)
          have hV0_sub_E0: "V0 \<subseteq> E0" using hV0eq by (by100 blast)
          have hV_sub_E: "V \<subseteq> E"
            using hV hV_open unfolding openin_on_def by (by100 blast)
          \<comment> \<open>The homeomorphism restricted to V\<inter>E0 → U\<inter>B0.\<close>
          \<comment> \<open>Subspace of subspace = subspace of ambient.\<close>
          have hTV0: "subspace_topology E0 (subspace_topology E TE E0) V0
              = subspace_topology E TE V0"
            using subspace_topology_trans[OF hV0_sub_E0] by simp
          have hU0_sub_B0: "?U0 \<subseteq> B0" by (by100 blast)
          have hTU0: "subspace_topology B0 (subspace_topology B TB B0) ?U0
              = subspace_topology B TB ?U0"
            using subspace_topology_trans[OF hU0_sub_B0] by simp
          have hV0_sub_E: "V0 \<subseteq> E" using hV0_sub_V hV_sub_E by (by100 blast)
          \<comment> \<open>V0 = V \<inter> E0 = V \<inter> p⁻¹(B0), and p|V is bijective V → U.
             So p maps V0 to U ∩ B0 bijectively.\<close>
          have hV0_pU0: "\<forall>x\<in>V0. p x \<in> ?U0"
          proof (intro ballI)
            fix x assume "x \<in> V0"
            hence "x \<in> V" and "x \<in> E0" using hV0eq by (by100 blast)+
            have "p x \<in> U" using \<open>x \<in> V\<close> hVhomeo unfolding top1_homeomorphism_on_def bij_betw_def
              by (by100 blast)
            moreover have "p x \<in> B0" using \<open>x \<in> E0\<close> assms(5) by (by100 simp)
            ultimately show "p x \<in> ?U0" by (by100 blast)
          qed
          \<comment> \<open>V0 = V \<inter> E0 and U0 = U \<inter> B0. Subspace topologies simplify.\<close>
          have hTV0': "subspace_topology E TE V0 = subspace_topology V (subspace_topology E TE V) V0"
            using subspace_topology_trans[OF hV0_sub_V] by simp
          have hU0_sub_U: "?U0 \<subseteq> U" by (by100 blast)
          have hTU0': "subspace_topology B TB ?U0 = subspace_topology U (subspace_topology B TB U) ?U0"
            using subspace_topology_trans[OF hU0_sub_U] by simp
          show "top1_homeomorphism_on V0 (subspace_topology E0 (subspace_topology E TE E0) V0)
              ?U0 (subspace_topology B0 (subspace_topology B TB B0) ?U0) p"
            unfolding hTV0 hTU0 hTV0' hTU0'
          proof -
            let ?TV = "subspace_topology E TE V" and ?TU = "subspace_topology B TB U"
            have hTV_top: "is_topology_on V ?TV"
              using hVhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
            have hTU_top: "is_topology_on U ?TU"
              using hVhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
            have hbij: "bij_betw p V U"
              using hVhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
            have hp_cont: "top1_continuous_map_on V ?TV U ?TU p"
              using hVhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
            have hinv_cont: "top1_continuous_map_on U ?TU V ?TV (inv_into V p)"
              using hVhomeo unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>p maps V0 onto U0.\<close>
            have hpV0: "p ` V0 = ?U0"
            proof (intro equalityI subsetI)
              fix y assume "y \<in> p ` V0"
              then obtain x where hx: "x \<in> V0" and hpx: "y = p x" by (by100 blast)
              show "y \<in> ?U0" using hV0_pU0 hx hpx by (by100 blast)
            next
              fix y assume hy: "y \<in> ?U0"
              have "y \<in> U" using hy by (by100 blast)
              then obtain x where hx: "x \<in> V" and hpx: "p x = y"
                using hbij unfolding bij_betw_def by (by100 auto)
              have "x \<in> E" using hx hV_sub_E by (by100 blast)
              have "p x \<in> B0" using hy hpx by (by100 blast)
              hence "x \<in> E0" using \<open>x \<in> E\<close> assms(5) by (by100 simp)
              hence "x \<in> V0" using hx hV0eq by (by100 blast)
              thus "y \<in> p ` V0" using hpx by (by100 blast)
            qed
            have hbij0: "bij_betw p V0 ?U0"
              using bij_betw_subset[OF hbij hV0_sub_V hpV0] .
            \<comment> \<open>Continuity of restriction.\<close>
            have hp_cont_V0: "top1_continuous_map_on V0 (subspace_topology V ?TV V0) ?U0
                (subspace_topology U ?TU ?U0) p"
              by (rule top1_continuous_map_on_codomain_shrink[OF
                    top1_continuous_map_on_restrict_domain_simple[OF hp_cont hV0_sub_V]])
                 (use hV0_pU0 in \<open>by100 auto\<close>)
            \<comment> \<open>Inverse maps U0 to V0.\<close>
            have hinv_V0: "\<forall>y\<in>?U0. inv_into V p y \<in> V0"
            proof
              fix y assume hy: "y \<in> ?U0"
              have "y \<in> U" using hy by (by100 blast)
              have hxV: "inv_into V p y \<in> V"
                using \<open>y \<in> U\<close> hbij unfolding bij_betw_def by (by100 auto)
              have hpx: "p (inv_into V p y) = y"
                using \<open>y \<in> U\<close> hbij unfolding bij_betw_def by (by100 auto)
              have "inv_into V p y \<in> E" using hxV hV_sub_E by (by100 blast)
              moreover have "p (inv_into V p y) \<in> B0" using hpx hy by (by100 auto)
              ultimately have "inv_into V p y \<in> E0" using assms(5) by (by100 simp)
              thus "inv_into V p y \<in> V0" using hxV hV0eq by (by100 blast)
            qed
            \<comment> \<open>inv_into V0 p = inv_into V p on U0.\<close>
            have hinv_eq: "\<forall>y\<in>?U0. inv_into V0 p y = inv_into V p y"
            proof
              fix y assume hy: "y \<in> ?U0"
              have "inv_into V p y \<in> V0" using hinv_V0 hy by (by100 blast)
              moreover have "p (inv_into V p y) = y"
                using hy hbij unfolding bij_betw_def by (by100 auto)
              moreover have "p (inv_into V0 p y) = y"
                using hy hbij0 unfolding bij_betw_def
                by (metis f_inv_into_f IntI imageI)
              moreover have "inv_into V0 p y \<in> V0"
                using hy hbij0 unfolding bij_betw_def
                by (metis IntI inv_into_into imageI)
              ultimately show "inv_into V0 p y = inv_into V p y"
              proof -
                assume hxV0: "inv_into V p y \<in> V0"
                   and hpVy: "p (inv_into V p y) = y"
                   and hpV0y: "p (inv_into V0 p y) = y"
                   and hx0V0: "inv_into V0 p y \<in> V0"
                have "p (inv_into V0 p y) = p (inv_into V p y)" using hpVy hpV0y by simp
                moreover have "inv_into V0 p y \<in> V" using hx0V0 hV0_sub_V by (by100 blast)
                moreover have "inv_into V p y \<in> V" using hxV0 hV0_sub_V by (by100 blast)
                ultimately show ?thesis
                  using hbij unfolding bij_betw_def inj_on_def by (by100 blast)
              qed
            qed
            \<comment> \<open>Continuity of inverse restriction.\<close>
            have hinv_cont_U0: "top1_continuous_map_on ?U0 (subspace_topology U ?TU ?U0) V0
                (subspace_topology V ?TV V0) (inv_into V0 p)"
            proof -
              have h1: "top1_continuous_map_on ?U0 (subspace_topology U ?TU ?U0) V ?TV (inv_into V p)"
                by (rule top1_continuous_map_on_restrict_domain_simple[OF hinv_cont hU0_sub_U])
              have h2: "(inv_into V p) ` ?U0 \<subseteq> V0"
                using hinv_V0 by (by100 auto)
              have h3: "top1_continuous_map_on ?U0 (subspace_topology U ?TU ?U0) V0
                  (subspace_topology V ?TV V0) (inv_into V p)"
                by (rule top1_continuous_map_on_codomain_shrink[OF h1 h2 hV0_sub_V])
              have h4: "\<forall>y\<in>?U0. inv_into V p y = inv_into V0 p y"
                using hinv_eq by (by100 auto)
              show ?thesis by (rule top1_continuous_map_on_agree'[OF h3 h4])
            qed
            show "top1_homeomorphism_on V0 (subspace_topology V ?TV V0)
                ?U0 (subspace_topology U ?TU ?U0) p"
              unfolding top1_homeomorphism_on_def
              using subspace_topology_is_topology_on[OF hTV_top hV0_sub_V]
                    subspace_topology_is_topology_on[OF hTU_top hU0_sub_U]
                    hbij0 hp_cont_V0 hinv_cont_U0 by (by100 blast)
          qed
        qed
      qed
    qed
    ultimately have "b0 \<in> ?U0 \<and>
        top1_evenly_covered_on E0 (subspace_topology E TE E0) B0 (subspace_topology B TB B0) p ?U0"
      by (by100 simp)
    thus "\<exists>U0. b0 \<in> U0 \<and>
        top1_evenly_covered_on E0 (subspace_topology E TE E0) B0 (subspace_topology B TB B0) p U0"
      by (rule exI)
  qed
  show ?thesis unfolding top1_covering_map_on_def
    using hp_cont hp_surj hp_evenly by (by100 blast)
qed

(** from \<S>53 Theorem 53.3: product of covering maps is a covering map.
    Uses strict topology: product of strict is strict. **)
theorem Theorem_53_3:
  assumes "top1_covering_map_on E TE B TB p"
      and "top1_covering_map_on E' TE' B' TB' p'"
      and "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict E' TE'" and "is_topology_on_strict B' TB'"
  shows "top1_covering_map_on (E \<times> E') (product_topology_on TE TE')
    (B \<times> B') (product_topology_on TB TB') (\<lambda>(x, y). (p x, p' y))"
proof -
  \<comment> \<open>Munkres 53.3: product of covering maps.\<close>
  have hpxp_cont: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE')
      (B \<times> B') (product_topology_on TB TB') (\<lambda>(x, y). (p x, p' y))"
  proof -
    have hTE: "is_topology_on E TE" by (rule is_topology_on_strict_imp[OF assms(3)])
    have hTB: "is_topology_on B TB" by (rule is_topology_on_strict_imp[OF assms(4)])
    have hTE': "is_topology_on E' TE'" by (rule is_topology_on_strict_imp[OF assms(5)])
    have hTB': "is_topology_on B' TB'" by (rule is_topology_on_strict_imp[OF assms(6)])
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
    have hp'_cont: "top1_continuous_map_on E' TE' B' TB' p'"
      using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
    have hTEE: "is_topology_on (E \<times> E') (product_topology_on TE TE')"
      by (rule product_topology_on_is_topology_on[OF hTE hTE'])
    \<comment> \<open>p \<circ> fst : E\<times>E' \<rightarrow> B is continuous.\<close>
    have hpi1: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') E TE pi1"
      by (rule top1_continuous_pi1[OF hTE hTE'])
    have hpi1_eq: "(pi1 :: ('a \<times> 'b) \<Rightarrow> 'a) = fst" unfolding pi1_def by (rule ext) simp
    have hfst: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') E TE fst"
      using hpi1 unfolding pi1_def by (by100 simp)
    have hpfst: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') B TB (p \<circ> fst)"
      by (rule top1_continuous_map_on_comp[OF hfst hp_cont])
    \<comment> \<open>p' \<circ> snd : E\<times>E' \<rightarrow> B' is continuous.\<close>
    have hpi2: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') E' TE' pi2"
      by (rule top1_continuous_pi2[OF hTE hTE'])
    have hpi2_eq: "(pi2 :: ('a \<times> 'b) \<Rightarrow> 'b) = snd" unfolding pi2_def by (rule ext) simp
    have hsnd: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') E' TE' snd"
      using hpi2 unfolding pi2_def by (by100 simp)
    have hp'snd: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') B' TB' (p' \<circ> snd)"
      by (rule top1_continuous_map_on_comp[OF hsnd hp'_cont])
    \<comment> \<open>By Theorem 18.4: (\<lambda>(x,y). (p x, p' y)) = (\<lambda>z. (p(fst z), p'(snd z))) is continuous.\<close>
    have heq: "(\<lambda>(x, y). (p x, p' y)) = (\<lambda>z. ((p \<circ> fst) z, (p' \<circ> snd) z))"
      by (rule ext) (simp add: comp_def split_def)
    \<comment> \<open>By Theorem 18.4: pi1\<circ>f = p\<circ>fst and pi2\<circ>f = p'\<circ>snd are both continuous,
       so f = (\<lambda>(x,y). (p x, p' y)) is continuous into the product.\<close>
    have hpi1_comp: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') B TB
        (pi1 \<circ> (\<lambda>(x, y). (p x, p' y)))"
    proof -
      have "pi1 \<circ> (\<lambda>(x, y). (p x, p' y)) = p \<circ> fst"
        unfolding pi1_def comp_def by (rule ext) (simp add: split_def)
      thus ?thesis using hpfst by simp
    qed
    have hpi2_comp: "top1_continuous_map_on (E \<times> E') (product_topology_on TE TE') B' TB'
        (pi2 \<circ> (\<lambda>(x, y). (p x, p' y)))"
    proof -
      have "pi2 \<circ> (\<lambda>(x, y). (p x, p' y)) = p' \<circ> snd"
        unfolding pi2_def comp_def by (rule ext) (simp add: split_def)
      thus ?thesis using hp'snd by simp
    qed
    show ?thesis
      using iffD2[OF Theorem_18_4[OF hTEE hTB hTB']] hpi1_comp hpi2_comp by (by100 simp)
  qed
  have hpxp_surj: "(\<lambda>(x, y). (p x, p' y)) ` (E \<times> E') = B \<times> B'"
  proof -
    have hp_surj: "p ` E = B" using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
    have hp'_surj: "p' ` E' = B'" using assms(2) unfolding top1_covering_map_on_def by (by100 blast)
    show ?thesis using hp_surj hp'_surj by force
  qed
  have hpxp_evenly: "\<forall>bb\<in>B \<times> B'. \<exists>W. bb \<in> W \<and>
      top1_evenly_covered_on (E \<times> E') (product_topology_on TE TE')
        (B \<times> B') (product_topology_on TB TB') (\<lambda>(x, y). (p x, p' y)) W"
  proof
    fix bb assume hbb: "bb \<in> B \<times> B'"
    obtain b b' where hb: "b \<in> B" and hb': "b' \<in> B'" and hbb_eq: "bb = (b, b')"
      using hbb by blast
    \<comment> \<open>Take U, U' evenly covered by p, p' respectively.\<close>
    obtain U where hbU: "b \<in> U" and hUec: "top1_evenly_covered_on E TE B TB p U"
      using top1_covering_map_on_evenly_covered[OF assms(1) hb] by (by100 blast)
    obtain U' where hbU': "b' \<in> U'" and hU'ec: "top1_evenly_covered_on E' TE' B' TB' p' U'"
      using top1_covering_map_on_evenly_covered[OF assms(2) hb'] by (by100 blast)
    \<comment> \<open>U \<times> U' is evenly covered: slices are V\<alpha> \<times> V'\<beta>.\<close>
    have "bb \<in> U \<times> U' \<and>
        top1_evenly_covered_on (E \<times> E') (product_topology_on TE TE')
          (B \<times> B') (product_topology_on TB TB') (\<lambda>(x, y). (p x, p' y)) (U \<times> U')"
    proof (intro conjI)
      show "bb \<in> U \<times> U'" using hbb_eq hbU hbU' by (by100 blast)
      \<comment> \<open>Extract slices for p and p'.\<close>
      obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
          and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
          and hV_union: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
          and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V) U
                             (subspace_topology B TB U) p"
        using hUec unfolding top1_evenly_covered_on_def by auto
      obtain \<V>' where hV'_open: "\<forall>V'\<in>\<V>'. openin_on E' TE' V'"
          and hV'_disj: "\<forall>V'\<in>\<V>'. \<forall>W'\<in>\<V>'. V' \<noteq> W' \<longrightarrow> V' \<inter> W' = {}"
          and hV'_union: "{x\<in>E'. p' x \<in> U'} = \<Union>\<V>'"
          and hV'_homeo: "\<forall>V'\<in>\<V>'. top1_homeomorphism_on V' (subspace_topology E' TE' V') U'
                             (subspace_topology B' TB' U') p'"
        using hU'ec unfolding top1_evenly_covered_on_def by auto
      \<comment> \<open>Product slices: {V \<times> V' | V \<in> \<V>, V' \<in> \<V>'}.\<close>
      define \<W> where "\<W> = {V \<times> V' | V V'. V \<in> \<V> \<and> V' \<in> \<V>'}"
      show "top1_evenly_covered_on (E \<times> E') (product_topology_on TE TE')
          (B \<times> B') (product_topology_on TB TB') (\<lambda>(x, y). (p x, p' y)) (U \<times> U')"
        unfolding top1_evenly_covered_on_def
      proof (intro conjI exI[of _ \<W>])
        \<comment> \<open>U \<times> U' is open in B \<times> B'.\<close>
        have hUo: "openin_on B TB U" using hUec unfolding top1_evenly_covered_on_def by (by100 blast)
        have hU'o: "openin_on B' TB' U'" using hU'ec unfolding top1_evenly_covered_on_def by (by100 blast)
        have hUT: "U \<in> TB" using hUo unfolding openin_on_def by (by100 blast)
        have hU'T: "U' \<in> TB'" using hU'o unfolding openin_on_def by (by100 blast)
        have "U \<times> U' \<in> product_topology_on TB TB'"
          by (rule product_rect_open[OF hUT hU'T])
        moreover have "U \<times> U' \<subseteq> B \<times> B'"
          using hUo hU'o unfolding openin_on_def by (by100 blast)
        ultimately show "openin_on (B \<times> B') (product_topology_on TB TB') (U \<times> U')"
          unfolding openin_on_def by (by100 blast)
        \<comment> \<open>Each W \<in> \<W> is open in E \<times> E'.\<close>
        show "\<forall>W\<in>\<W>. openin_on (E \<times> E') (product_topology_on TE TE') W"
        proof (intro ballI)
          fix W assume "W \<in> \<W>"
          then obtain V V' where hV: "V \<in> \<V>" and hV': "V' \<in> \<V>'" and hWeq: "W = V \<times> V'"
            unfolding \<W>_def by (by100 blast)
          have hVT: "V \<in> TE" using hV_open[rule_format, OF hV] unfolding openin_on_def by (by100 blast)
          have hV'T: "V' \<in> TE'" using hV'_open[rule_format, OF hV'] unfolding openin_on_def by (by100 blast)
          have "V \<times> V' \<in> product_topology_on TE TE'" by (rule product_rect_open[OF hVT hV'T])
          moreover have "V \<times> V' \<subseteq> E \<times> E'"
            using hV_open[rule_format, OF hV] hV'_open[rule_format, OF hV'] unfolding openin_on_def
            by (by100 blast)
          ultimately show "openin_on (E \<times> E') (product_topology_on TE TE') W"
            unfolding openin_on_def hWeq by (by100 blast)
        qed
        \<comment> \<open>Pairwise disjoint.\<close>
        show "\<forall>W\<in>\<W>. \<forall>W2\<in>\<W>. W \<noteq> W2 \<longrightarrow> W \<inter> W2 = {}"
        proof (intro ballI impI)
          fix W1 W2 assume "W1 \<in> \<W>" "W2 \<in> \<W>" "W1 \<noteq> W2"
          obtain V1 V1' where hV1: "V1 \<in> \<V>" and hV1': "V1' \<in> \<V>'" and hW1: "W1 = V1 \<times> V1'"
            using \<open>W1 \<in> \<W>\<close> unfolding \<W>_def by (by100 blast)
          obtain V2 V2' where hV2: "V2 \<in> \<V>" and hV2': "V2' \<in> \<V>'" and hW2: "W2 = V2 \<times> V2'"
            using \<open>W2 \<in> \<W>\<close> unfolding \<W>_def by (by100 blast)
          have "V1 \<noteq> V2 \<or> V1' \<noteq> V2'" using \<open>W1 \<noteq> W2\<close> hW1 hW2 by (by100 blast)
          thus "W1 \<inter> W2 = {}"
          proof (elim disjE)
            assume "V1 \<noteq> V2"
            hence "V1 \<inter> V2 = {}" using hV_disj hV1 hV2 by (by100 blast)
            thus ?thesis unfolding hW1 hW2 by (by100 blast)
          next
            assume "V1' \<noteq> V2'"
            hence "V1' \<inter> V2' = {}" using hV'_disj hV1' hV2' by (by100 blast)
            thus ?thesis unfolding hW1 hW2 by (by100 blast)
          qed
        qed
        \<comment> \<open>Union = preimage.\<close>
        show "{x \<in> E \<times> E'. (\<lambda>(x, y). (p x, p' y)) x \<in> U \<times> U'} = \<Union>\<W>"
        proof (rule set_eqI)
          fix x show "(x \<in> {x \<in> E \<times> E'. (\<lambda>(x, y). (p x, p' y)) x \<in> U \<times> U'}) = (x \<in> \<Union>\<W>)"
          proof
            assume hx: "x \<in> {x \<in> E \<times> E'. (\<lambda>(x, y). (p x, p' y)) x \<in> U \<times> U'}"
            obtain a b where hab: "x = (a, b)" and ha: "a \<in> E" and hb: "b \<in> E'"
                and hpa: "p a \<in> U" and hpb: "p' b \<in> U'"
              using hx by (by100 auto)
            have "a \<in> {x\<in>E. p x \<in> U}" using ha hpa by simp
            hence "a \<in> \<Union>\<V>" using hV_union by simp
            then obtain V where hV: "V \<in> \<V>" and haV: "a \<in> V" by (by100 blast)
            have "b \<in> {x\<in>E'. p' x \<in> U'}" using hb hpb by simp
            hence "b \<in> \<Union>\<V>'" using hV'_union by simp
            then obtain V' where hV': "V' \<in> \<V>'" and hbV': "b \<in> V'" by (by100 blast)
            have "V \<times> V' \<in> \<W>" unfolding \<W>_def using hV hV' by (by100 blast)
            moreover have "x \<in> V \<times> V'" using hab haV hbV' by (by100 blast)
            ultimately show "x \<in> \<Union>\<W>" by (by100 blast)
          next
            assume "x \<in> \<Union>\<W>"
            then obtain W where "W \<in> \<W>" and "x \<in> W" by (by100 blast)
            then obtain V V' where hV: "V \<in> \<V>" and hV': "V' \<in> \<V>'" and "x \<in> V \<times> V'"
              unfolding \<W>_def by (by100 blast)
            obtain a b where hab: "x = (a, b)" and haV: "a \<in> V" and hbV': "b \<in> V'"
              using \<open>x \<in> V \<times> V'\<close> by (by100 blast)
            have "a \<in> \<Union>\<V>" using haV hV by (by100 blast)
            hence "a \<in> {x\<in>E. p x \<in> U}" using hV_union by simp
            hence ha: "a \<in> E" and hpa: "p a \<in> U" by simp_all
            have "b \<in> \<Union>\<V>'" using hbV' hV' by (by100 blast)
            hence "b \<in> {x\<in>E'. p' x \<in> U'}" using hV'_union by simp
            hence hb: "b \<in> E'" and hpb: "p' b \<in> U'" by simp_all
            show "x \<in> {x \<in> E \<times> E'. (\<lambda>(x, y). (p x, p' y)) x \<in> U \<times> U'}"
              using hab ha hb hpa hpb by (by100 auto)
          qed
        qed
        \<comment> \<open>Each slice homeomorphic to U \<times> U'.
           Product of homeomorphisms is a homeomorphism.\<close>
        show "\<forall>W\<in>\<W>. top1_homeomorphism_on W
            (subspace_topology (E \<times> E') (product_topology_on TE TE') W)
            (U \<times> U') (subspace_topology (B \<times> B') (product_topology_on TB TB') (U \<times> U'))
            (\<lambda>(x, y). (p x, p' y))"
        proof (intro ballI)
          fix W assume "W \<in> \<W>"
          then obtain V V' where hV: "V \<in> \<V>" and hV': "V' \<in> \<V>'" and hWeq: "W = V \<times> V'"
            unfolding \<W>_def by (by100 blast)
          have hVh: "top1_homeomorphism_on V (subspace_topology E TE V) U
                       (subspace_topology B TB U) p"
            using hV_homeo hV by (by100 blast)
          have hV'h: "top1_homeomorphism_on V' (subspace_topology E' TE' V') U'
                       (subspace_topology B' TB' U') p'"
            using hV'_homeo hV' by (by100 blast)
          \<comment> \<open>Product of homeomorphisms is a homeomorphism.
             Uses Theorem_16_3: product of subspace = subspace of product.\<close>
          show "top1_homeomorphism_on W
              (subspace_topology (E \<times> E') (product_topology_on TE TE') W)
              (U \<times> U') (subspace_topology (B \<times> B') (product_topology_on TB TB') (U \<times> U'))
              (\<lambda>(x, y). (p x, p' y))"
            unfolding hWeq top1_homeomorphism_on_def
          proof (intro conjI)
            have hTE: "is_topology_on E TE" by (rule is_topology_on_strict_imp[OF assms(3)])
            have hTB: "is_topology_on B TB" by (rule is_topology_on_strict_imp[OF assms(4)])
            have hTE': "is_topology_on E' TE'" by (rule is_topology_on_strict_imp[OF assms(5)])
            have hTB': "is_topology_on B' TB'" by (rule is_topology_on_strict_imp[OF assms(6)])
            have hVE: "V \<subseteq> E" using hV_open[rule_format, OF hV] unfolding openin_on_def by (by100 blast)
            have hV'E: "V' \<subseteq> E'" using hV'_open[rule_format, OF hV'] unfolding openin_on_def by (by100 blast)
            have hUB: "U \<subseteq> B"
            proof -
              have "openin_on B TB U" using hUec unfolding top1_evenly_covered_on_def by (by100 blast)
              thus ?thesis unfolding openin_on_def by (by100 blast)
            qed
            have hU'B: "U' \<subseteq> B'"
            proof -
              have "openin_on B' TB' U'" using hU'ec unfolding top1_evenly_covered_on_def by (by100 blast)
              thus ?thesis unfolding openin_on_def by (by100 blast)
            qed
            \<comment> \<open>Subspace topologies via Theorem_16_3.\<close>
            have hVV_eq: "subspace_topology (E \<times> E') (product_topology_on TE TE') (V \<times> V')
                = product_topology_on (subspace_topology E TE V) (subspace_topology E' TE' V')"
              using Theorem_16_3[OF hTE hTE'] by simp
            have hUU_eq: "subspace_topology (B \<times> B') (product_topology_on TB TB') (U \<times> U')
                = product_topology_on (subspace_topology B TB U) (subspace_topology B' TB' U')"
              using Theorem_16_3[OF hTB hTB'] by simp
            \<comment> \<open>Topology on V \<times> V'.\<close>
            show "is_topology_on (V \<times> V') (subspace_topology (E \<times> E') (product_topology_on TE TE') (V \<times> V'))"
              unfolding hVV_eq by (rule product_topology_on_is_topology_on[OF
                  subspace_topology_is_topology_on[OF hTE hVE]
                  subspace_topology_is_topology_on[OF hTE' hV'E]])
            \<comment> \<open>Topology on U \<times> U'.\<close>
            show "is_topology_on (U \<times> U') (subspace_topology (B \<times> B') (product_topology_on TB TB') (U \<times> U'))"
              unfolding hUU_eq by (rule product_topology_on_is_topology_on[OF
                  subspace_topology_is_topology_on[OF hTB hUB]
                  subspace_topology_is_topology_on[OF hTB' hU'B]])
            \<comment> \<open>Bijection.\<close>
            have hbij_p: "bij_betw p V U"
              using hVh unfolding top1_homeomorphism_on_def by (by100 blast)
            have hbij_p': "bij_betw p' V' U'"
              using hV'h unfolding top1_homeomorphism_on_def by (by100 blast)
            show "bij_betw (\<lambda>(x, y). (p x, p' y)) (V \<times> V') (U \<times> U')"
            proof -
              have hinj: "inj_on (\<lambda>(x, y). (p x, p' y)) (V \<times> V')"
              proof (rule inj_onI)
                fix a b assume ha: "a \<in> V \<times> V'" and hb: "b \<in> V \<times> V'"
                    and heq: "(case a of (x, y) \<Rightarrow> (p x, p' y)) = (case b of (x, y) \<Rightarrow> (p x, p' y))"
                obtain a1 a2 where ha12: "a = (a1, a2)" by (cases a)
                obtain b1 b2 where hb12: "b = (b1, b2)" by (cases b)
                have "p a1 = p b1" "p' a2 = p' b2" using heq ha12 hb12 by auto
                have "a1 \<in> V" "b1 \<in> V" using ha hb ha12 hb12 by auto
                have "a2 \<in> V'" "b2 \<in> V'" using ha hb ha12 hb12 by auto
                have "a1 = b1" using inj_onD[OF bij_betw_imp_inj_on[OF hbij_p]
                  \<open>p a1 = p b1\<close> \<open>a1 \<in> V\<close> \<open>b1 \<in> V\<close>] .
                moreover have "a2 = b2" using inj_onD[OF bij_betw_imp_inj_on[OF hbij_p']
                  \<open>p' a2 = p' b2\<close> \<open>a2 \<in> V'\<close> \<open>b2 \<in> V'\<close>] .
                ultimately show "a = b" using ha12 hb12 by simp
              qed
              have himg: "(\<lambda>(x, y). (p x, p' y)) ` (V \<times> V') = U \<times> U'"
                using bij_betw_imp_surj_on[OF hbij_p] bij_betw_imp_surj_on[OF hbij_p'] by force
              show ?thesis unfolding bij_betw_def using hinj himg by simp
            qed
            \<comment> \<open>Forward continuity.\<close>
            \<comment> \<open>Forward and inverse continuity: both use Theorem_18_4 + component continuity.\<close>
            have hp_cont_V: "top1_continuous_map_on V (subspace_topology E TE V)
                U (subspace_topology B TB U) p"
              using hVh unfolding top1_homeomorphism_on_def by (by100 blast)
            have hp'_cont_V': "top1_continuous_map_on V' (subspace_topology E' TE' V')
                U' (subspace_topology B' TB' U') p'"
              using hV'h unfolding top1_homeomorphism_on_def by (by100 blast)
            have hp_inv_cont: "top1_continuous_map_on U (subspace_topology B TB U)
                V (subspace_topology E TE V) (inv_into V p)"
              using hVh unfolding top1_homeomorphism_on_def by (by100 blast)
            have hp'_inv_cont: "top1_continuous_map_on U' (subspace_topology B' TB' U')
                V' (subspace_topology E' TE' V') (inv_into V' p')"
              using hV'h unfolding top1_homeomorphism_on_def by (by100 blast)
            have hTV: "is_topology_on V (subspace_topology E TE V)"
              by (rule subspace_topology_is_topology_on[OF hTE hVE])
            have hTV': "is_topology_on V' (subspace_topology E' TE' V')"
              by (rule subspace_topology_is_topology_on[OF hTE' hV'E])
            have hTU: "is_topology_on U (subspace_topology B TB U)"
              by (rule subspace_topology_is_topology_on[OF hTB hUB])
            have hTU': "is_topology_on U' (subspace_topology B' TB' U')"
              by (rule subspace_topology_is_topology_on[OF hTB' hU'B])
            have hTVV: "is_topology_on (V \<times> V') (product_topology_on (subspace_topology E TE V) (subspace_topology E' TE' V'))"
              by (rule product_topology_on_is_topology_on[OF hTV hTV'])
            show "top1_continuous_map_on (V \<times> V')
                (subspace_topology (E \<times> E') (product_topology_on TE TE') (V \<times> V'))
                (U \<times> U') (subspace_topology (B \<times> B') (product_topology_on TB TB') (U \<times> U'))
                (\<lambda>(x, y). (p x, p' y))"
              unfolding hVV_eq hUU_eq
            proof (rule iffD2[OF Theorem_18_4[OF hTVV hTU hTU']], intro conjI)
              have "pi1 \<circ> (\<lambda>(x, y). (p x, p' y)) = p \<circ> pi1"
                unfolding pi1_def by (rule ext) (simp add: split_def)
              thus "top1_continuous_map_on (V \<times> V')
                  (product_topology_on (subspace_topology E TE V) (subspace_topology E' TE' V'))
                  U (subspace_topology B TB U) (pi1 \<circ> (\<lambda>(x, y). (p x, p' y)))"
                using top1_continuous_map_on_comp[OF
                    top1_continuous_pi1[OF hTV hTV', unfolded pi1_def] hp_cont_V]
                unfolding pi1_def by simp
            next
              have "pi2 \<circ> (\<lambda>(x, y). (p x, p' y)) = p' \<circ> pi2"
                unfolding pi2_def by (rule ext) (simp add: split_def)
              thus "top1_continuous_map_on (V \<times> V')
                  (product_topology_on (subspace_topology E TE V) (subspace_topology E' TE' V'))
                  U' (subspace_topology B' TB' U') (pi2 \<circ> (\<lambda>(x, y). (p x, p' y)))"
                using top1_continuous_map_on_comp[OF
                    top1_continuous_pi2[OF hTV hTV', unfolded pi2_def] hp'_cont_V']
                unfolding pi2_def by simp
            qed
            \<comment> \<open>Inverse continuity: inv_into (V\<times>V') (p\<times>p') = (inv_into V p) \<times> (inv_into V' p').\<close>
            show "top1_continuous_map_on (U \<times> U')
                (subspace_topology (B \<times> B') (product_topology_on TB TB') (U \<times> U'))
                (V \<times> V') (subspace_topology (E \<times> E') (product_topology_on TE TE') (V \<times> V'))
                (inv_into (V \<times> V') (\<lambda>(x, y). (p x, p' y)))"
            proof -
              have hTE_l: "is_topology_on E TE" by (rule is_topology_on_strict_imp[OF assms(3)])
              have hTB_l: "is_topology_on B TB" by (rule is_topology_on_strict_imp[OF assms(4)])
              have hTE'_l: "is_topology_on E' TE'" by (rule is_topology_on_strict_imp[OF assms(5)])
              have hTB'_l: "is_topology_on B' TB'" by (rule is_topology_on_strict_imp[OF assms(6)])
              have hinj_pp: "inj_on (\<lambda>(x,y). (p x, p' y)) (V \<times> V')"
                using bij_betw_imp_inj_on[OF \<open>bij_betw (\<lambda>(x,y). (p x, p' y)) (V \<times> V') (U \<times> U')\<close>] .
              have hTUU: "is_topology_on (U \<times> U')
                  (product_topology_on (subspace_topology B TB U) (subspace_topology B' TB' U'))"
                by (rule product_topology_on_is_topology_on[OF hTU hTU'])
              \<comment> \<open>inv_into decomposes.\<close>
              have hinv_eq: "\<And>u u'. u \<in> U \<Longrightarrow> u' \<in> U' \<Longrightarrow>
                  inv_into (V \<times> V') (\<lambda>(x, y). (p x, p' y)) (u, u') = (inv_into V p u, inv_into V' p' u')"
              proof -
                fix u u' assume hu: "u \<in> U" and hu': "u' \<in> U'"
                have h1: "inv_into V p u \<in> V"
                  using bij_betw_imp_surj_on[OF hbij_p] hu by (metis imageE inv_into_into)
                have h2: "inv_into V' p' u' \<in> V'"
                  using bij_betw_imp_surj_on[OF hbij_p'] hu' by (metis imageE inv_into_into)
                have h3: "p (inv_into V p u) = u"
                  by (rule f_inv_into_f) (metis bij_betw_imp_surj_on[OF hbij_p] hu imageI)
                have h4: "p' (inv_into V' p' u') = u'"
                  by (rule f_inv_into_f) (metis bij_betw_imp_surj_on[OF hbij_p'] hu' imageI)
                show "inv_into (V \<times> V') (\<lambda>(x, y). (p x, p' y)) (u, u') = (inv_into V p u, inv_into V' p' u')"
                  by (rule inv_into_f_eq[OF hinj_pp]) (simp_all add: h1 h2 h3 h4)
              qed
              \<comment> \<open>g = (inv V p, inv V' p') is continuous by Theorem_18_4.\<close>
              have hg_cont: "top1_continuous_map_on (U \<times> U')
                  (product_topology_on (subspace_topology B TB U) (subspace_topology B' TB' U'))
                  (V \<times> V') (product_topology_on (subspace_topology E TE V) (subspace_topology E' TE' V'))
                  (\<lambda>x. (inv_into V p (fst x), inv_into V' p' (snd x)))"
              proof (rule iffD2[OF Theorem_18_4[OF hTUU hTV hTV']], intro conjI)
                have "pi1 \<circ> (\<lambda>x. (inv_into V p (fst x), inv_into V' p' (snd x))) = inv_into V p \<circ> pi1"
                  unfolding pi1_def by (rule ext) simp
                thus "top1_continuous_map_on (U \<times> U')
                    (product_topology_on (subspace_topology B TB U) (subspace_topology B' TB' U'))
                    V (subspace_topology E TE V) (pi1 \<circ> (\<lambda>x. (inv_into V p (fst x), inv_into V' p' (snd x))))"
                  using top1_continuous_map_on_comp[OF
                      top1_continuous_pi1[OF hTU hTU', unfolded pi1_def] hp_inv_cont]
                  unfolding pi1_def by simp
              next
                have "pi2 \<circ> (\<lambda>x. (inv_into V p (fst x), inv_into V' p' (snd x))) = inv_into V' p' \<circ> pi2"
                  unfolding pi2_def by (rule ext) simp
                thus "top1_continuous_map_on (U \<times> U')
                    (product_topology_on (subspace_topology B TB U) (subspace_topology B' TB' U'))
                    V' (subspace_topology E' TE' V') (pi2 \<circ> (\<lambda>x. (inv_into V p (fst x), inv_into V' p' (snd x))))"
                  using top1_continuous_map_on_comp[OF
                      top1_continuous_pi2[OF hTU hTU', unfolded pi2_def] hp'_inv_cont]
                  unfolding pi2_def by simp
              qed
              \<comment> \<open>Transfer: inv_into agrees with g on U\<times>U'.\<close>
              have "\<forall>x\<in>U \<times> U'. inv_into (V \<times> V') (\<lambda>(x, y). (p x, p' y)) x
                  = (\<lambda>x. (inv_into V p (fst x), inv_into V' p' (snd x))) x"
              proof
                fix x assume "x \<in> U \<times> U'"
                then obtain u u' where hx: "x = (u, u')" and hu: "u \<in> U" and hu': "u' \<in> U'"
                  by (by100 blast)
                show "inv_into (V \<times> V') (\<lambda>(x, y). (p x, p' y)) x
                    = (\<lambda>x. (inv_into V p (fst x), inv_into V' p' (snd x))) x"
                  unfolding hx using hinv_eq[OF hu hu'] by simp
              qed
              have hrange: "\<forall>x\<in>U \<times> U'. inv_into (V \<times> V') (\<lambda>(x, y). (p x, p' y)) x \<in> V \<times> V'"
                using \<open>\<forall>x\<in>U \<times> U'. inv_into _ _ x = _\<close> hg_cont
                unfolding top1_continuous_map_on_def by auto
              have hpreimg: "\<forall>W\<in>product_topology_on (subspace_topology E TE V) (subspace_topology E' TE' V').
                  {x \<in> U \<times> U'. inv_into (V \<times> V') (\<lambda>(x, y). (p x, p' y)) x \<in> W}
                  \<in> product_topology_on (subspace_topology B TB U) (subspace_topology B' TB' U')"
              proof
                fix W assume hW: "W \<in> product_topology_on (subspace_topology E TE V) (subspace_topology E' TE' V')"
                have "{x \<in> U \<times> U'. inv_into (V \<times> V') (\<lambda>(x, y). (p x, p' y)) x \<in> W}
                    = {x \<in> U \<times> U'. (inv_into V p (fst x), inv_into V' p' (snd x)) \<in> W}"
                proof (rule Collect_cong)
                  fix x show "(x \<in> U \<times> U' \<and> inv_into (V \<times> V') (\<lambda>(x, y). (p x, p' y)) x \<in> W)
                      = (x \<in> U \<times> U' \<and> (inv_into V p (fst x), inv_into V' p' (snd x)) \<in> W)"
                    using \<open>\<forall>x\<in>U \<times> U'. inv_into _ _ x = _\<close> by (by100 auto)
                qed
                also have "{x \<in> U \<times> U'. (inv_into V p (fst x), inv_into V' p' (snd x)) \<in> W}
                    \<in> product_topology_on (subspace_topology B TB U) (subspace_topology B' TB' U')"
                  using hg_cont hW unfolding top1_continuous_map_on_def by (by100 blast)
                finally show "{x \<in> U \<times> U'. inv_into (V \<times> V') (\<lambda>(x, y). (p x, p' y)) x \<in> W}
                    \<in> product_topology_on (subspace_topology B TB U) (subspace_topology B' TB' U')" .
              qed
              have hresult: "top1_continuous_map_on (U \<times> U')
                  (product_topology_on (subspace_topology B TB U) (subspace_topology B' TB' U'))
                  (V \<times> V') (product_topology_on (subspace_topology E TE V) (subspace_topology E' TE' V'))
                  (inv_into (V \<times> V') (\<lambda>(x, y). (p x, p' y)))"
                using hrange hpreimg unfolding top1_continuous_map_on_def by (by100 blast)
              show ?thesis using hresult unfolding hVV_eq[symmetric] hUU_eq[symmetric] .
            qed
          qed
        qed
      qed
    qed
    thus "\<exists>W. bb \<in> W \<and>
        top1_evenly_covered_on (E \<times> E') (product_topology_on TE TE')
          (B \<times> B') (product_topology_on TB TB') (\<lambda>(x, y). (p x, p' y)) W"
      by (rule exI)
  qed
  show ?thesis unfolding top1_covering_map_on_def
    using hpxp_cont hpxp_surj hpxp_evenly by blast
qed

section \<open>\<S>54 The Fundamental Group of the Circle\<close>

text \<open>Non-uniform subdivision from open cover of [0,1] (easier than Lebesgue number).
  Proof by the "creeping lemma": advance step-by-step using pointwise radii.\<close>
lemma open_cover_subdivision_01:
  assumes "\<forall>s::real. 0 \<le> s \<and> s \<le> 1 \<longrightarrow> (\<exists>U\<in>\<A>. s \<in> U \<and> (\<exists>\<epsilon>>0. {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U))"
  shows "\<exists>n::nat. n \<ge> 1 \<and> (\<exists>sub::nat \<Rightarrow> real. sub 0 = 0 \<and> sub n = 1
      \<and> (\<forall>i<n. sub i < sub (Suc i))
      \<and> (\<forall>i<n. \<exists>U\<in>\<A>. {s. sub i \<le> s \<and> s \<le> sub (Suc i) \<and> 0 \<le> s \<and> s \<le> 1} \<subseteq> U))"
proof -
  \<comment> \<open>Define A = {s \<in> [0,1]. [0,s] has a valid subdivision}.
     Show: 0 \<in> A. A is open in [0,1]. sup A \<in> A. sup A = 1.\<close>
  define A where "A = {s. 0 \<le> s \<and> s \<le> 1 \<and>
      (\<exists>n\<ge>1. \<exists>sub. sub 0 = 0 \<and> sub n = s
        \<and> (\<forall>i<n. sub i < sub (Suc i))
        \<and> (\<forall>i<n. \<exists>U\<in>\<A>. {t. sub i \<le> t \<and> t \<le> sub (Suc i) \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U))}"
  \<comment> \<open>0 \<in> A: trivial subdivision.\<close>
  \<comment> \<open>Some small positive s₁ is in A: use the cover at 0.\<close>
  obtain U0 eps0 where hU0: "U0 \<in> \<A>" and heps0: "eps0 > 0"
      and hball0: "{t. \<bar>t\<bar> < eps0 \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U0"
    using assms[rule_format, of 0] by auto
  define s1 where "s1 = min (eps0 / 2) 1"
  have hs1_pos: "s1 > 0" unfolding s1_def using heps0 by simp
  have hs1_le1: "s1 \<le> 1" unfolding s1_def by simp
  have hs1_A: "s1 \<in> A"
  proof -
    have hsub: "{t. 0 \<le> t \<and> t \<le> s1 \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U0"
    proof
      fix t assume ht: "t \<in> {t. 0 \<le> t \<and> t \<le> s1 \<and> 0 \<le> t \<and> t \<le> 1}"
      hence "0 \<le> t" "t \<le> s1" "t \<le> 1" by auto
      hence "\<bar>t\<bar> < eps0" unfolding s1_def using heps0 by auto
      thus "t \<in> U0" using hball0 \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> by auto
    qed
    show ?thesis unfolding A_def
      using hU0 hs1_pos hs1_le1 hsub
      by (intro CollectI conjI exI[of _ 1] exI[of _ "\<lambda>i. if i = 0 then 0 else s1"]) auto
  qed
  have hne: "A \<noteq> {}" using hs1_A by blast
  \<comment> \<open>A bounded above by 1.\<close>
  have hbdd: "\<forall>s\<in>A. s \<le> 1" unfolding A_def by (by100 blast)
  \<comment> \<open>Let M = Sup A.\<close>
  define M where "M = Sup A"
  have hM_le1: "M \<le> 1" unfolding M_def using hbdd hne by (intro cSup_le_iff[THEN iffD2]) auto
  have hM_ge0: "M \<ge> 0"
  proof -
    have "s1 \<le> M" unfolding M_def using hs1_A hbdd by (intro cSup_upper) auto
    thus ?thesis using hs1_pos by linarith
  qed
  \<comment> \<open>M \<in> A (closed step): M is a limit of points in A, each covered by some U.
     M itself is in some U (open), so the subdivision can be extended to M.\<close>
  have hM_A: "M \<in> A"
  proof -
    \<comment> \<open>M \<in> [0,1], so M is in some open cover element UM with Ball(M, \<epsilon>M) \<subseteq> UM.\<close>
    obtain UM epsM where hUM: "UM \<in> \<A>" and hepsM: "epsM > 0"
        and hballM: "{t. \<bar>t - M\<bar> < epsM \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> UM"
      using assms[rule_format, of M] hM_ge0 hM_le1 by auto
    \<comment> \<open>There exists s \<in> A with s > M - epsM (since M = Sup A).\<close>
    have "\<exists>s\<in>A. s > M - epsM"
    proof (rule ccontr)
      assume "\<not> (\<exists>s\<in>A. M - epsM < s)"
      hence hle: "\<forall>s\<in>A. s \<le> M - epsM" by (simp add: not_less)
      hence "M \<le> M - epsM" unfolding M_def
        by (intro cSup_least[OF hne]) blast
      thus False using hepsM by linarith
    qed
    then obtain s where hsA: "s \<in> A" and hs_gt: "s > M - epsM" by blast
    have hs_le_M: "s \<le> M" unfolding M_def using hsA hbdd by (intro cSup_upper) auto
    \<comment> \<open>If s = M, we're done.\<close>
    show "M \<in> A"
    proof (cases "s = M")
      case True thus ?thesis using hsA by simp
    next
      case False hence hs_lt_M: "s < M" using hs_le_M by linarith
      \<comment> \<open>s \<in> A and [s, M] \<subseteq> UM (since |t - M| < epsM for t \<in> [s, M]).\<close>
      have hsM_sub: "{t. s \<le> t \<and> t \<le> M \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> UM"
      proof
        fix t assume "t \<in> {t. s \<le> t \<and> t \<le> M \<and> 0 \<le> t \<and> t \<le> 1}"
        hence "s \<le> t" "t \<le> M" "0 \<le> t" "t \<le> 1" by auto
        hence "\<bar>t - M\<bar> < epsM" using hs_gt by auto
        thus "t \<in> UM" using hballM \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> by auto
      qed
      \<comment> \<open>Extend subdivision of [0,s] with [s, M] to get subdivision of [0,M].\<close>
      obtain n sub where hn: "n \<ge> 1" and hsub0: "sub 0 = (0::real)" and hsubn: "sub n = s"
          and hinc: "\<forall>i<n. sub i < sub (Suc i)"
          and hcov_sub: "\<forall>i<n. \<exists>U\<in>\<A>. {t. sub i \<le> t \<and> t \<le> sub (Suc i) \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U"
        using hsA unfolding A_def by blast
      define sub' where "sub' = (\<lambda>i. if i \<le> n then sub i else M)"
      define sub' where "sub' = (\<lambda>i. if i \<le> n then sub i else M)"
      have hsub'0: "sub' 0 = 0" unfolding sub'_def using hsub0 by simp
      have hsub'n1: "sub' (Suc n) = M" unfolding sub'_def by simp
      have hinc': "\<forall>i < Suc n. sub' i < sub' (Suc i)"
      proof (intro allI impI)
        fix i assume "i < Suc n"
        show "sub' i < sub' (Suc i)"
        proof (cases "i < n")
          case True thus ?thesis unfolding sub'_def using hinc by simp
        next
          case False hence "i = n" using \<open>i < Suc n\<close> by simp
          thus ?thesis unfolding sub'_def using hsubn hs_lt_M by simp
        qed
      qed
      have hcov': "\<forall>i < Suc n. \<exists>U\<in>\<A>. {t. sub' i \<le> t \<and> t \<le> sub' (Suc i) \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U"
      proof (intro allI impI)
        fix i assume "i < Suc n"
        show "\<exists>U\<in>\<A>. {t. sub' i \<le> t \<and> t \<le> sub' (Suc i) \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U"
        proof (cases "i < n")
          case True
          hence "sub' i = sub i" "sub' (Suc i) = sub (Suc i)" unfolding sub'_def by simp+
          thus ?thesis using hcov_sub True by simp
        next
          case False hence "i = n" using \<open>i < Suc n\<close> by simp
          hence "sub' i = s" "sub' (Suc i) = M" unfolding sub'_def using hsubn by simp+
          thus ?thesis using hUM hsM_sub by auto
        qed
      qed
      have "M \<in> A" unfolding A_def
        using hsub'0 hsub'n1 hinc' hcov' hM_ge0 hM_le1
        by (intro CollectI conjI exI[of _ "Suc n"] exI[of _ sub']) auto
      thus ?thesis .
    qed
  qed
  \<comment> \<open>M = 1 (open step): if M < 1, M is in some open U, so M + \<epsilon> \<in> A for small \<epsilon> > 0.
     But M = sup A, contradiction.\<close>
  have hM_1: "M = 1"
  proof (rule ccontr)
    assume "M \<noteq> 1" hence hM_lt1: "M < 1" using hM_le1 by linarith
    \<comment> \<open>M \<in> [0,1), so M is in some open U with Ball(M, \<epsilon>) \<subseteq> U.\<close>
    obtain UM epsM where hUM: "UM \<in> \<A>" and hepsM: "epsM > 0"
        and hballM: "{t. \<bar>t - M\<bar> < epsM \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> UM"
      using assms[rule_format, of M] hM_ge0 hM_lt1 by auto
    \<comment> \<open>Since M \<in> A, extend the subdivision to M + epsM/2.\<close>
    define M' where "M' = min (M + epsM / 2) 1"
    have hM'_gt_M: "M' > M" unfolding M'_def using hepsM hM_lt1 by linarith
    have hM'_le1: "M' \<le> 1" unfolding M'_def by linarith
    have hM'_ge0: "M' \<ge> 0" using hM_ge0 hM'_gt_M by linarith
    \<comment> \<open>[M, M'] \<subseteq> UM.\<close>
    have hMM': "{t. M \<le> t \<and> t \<le> M' \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> UM"
    proof
      fix t assume "t \<in> {t. M \<le> t \<and> t \<le> M' \<and> 0 \<le> t \<and> t \<le> 1}"
      hence "M \<le> t" "t \<le> M'" "0 \<le> t" "t \<le> 1" by auto
      hence "\<bar>t - M\<bar> < epsM" unfolding M'_def using hepsM by auto
      thus "t \<in> UM" using hballM \<open>0 \<le> t\<close> \<open>t \<le> 1\<close> by auto
    qed
    \<comment> \<open>M' \<in> A by extending the subdivision of [0,M] with [M, M'].\<close>
    have "M' \<in> A"
    proof -
      obtain n sub where hn: "n \<ge> 1" and hsub0: "sub 0 = (0::real)" and hsubn: "sub n = M"
          and hinc: "\<forall>i<n. sub i < sub (Suc i)"
          and hcov_sub: "\<forall>i<n. \<exists>U\<in>\<A>. {t. sub i \<le> t \<and> t \<le> sub (Suc i) \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U"
        using hM_A unfolding A_def by blast
      define sub' where "sub' = (\<lambda>i. if i \<le> n then sub i else M')"
      have "sub' 0 = 0" unfolding sub'_def using hsub0 by simp
      moreover have "sub' (Suc n) = M'" unfolding sub'_def by simp
      moreover have "\<forall>i < Suc n. sub' i < sub' (Suc i)"
      proof (intro allI impI)
        fix i assume "i < Suc n"
        show "sub' i < sub' (Suc i)"
        proof (cases "i < n")
          case True thus ?thesis unfolding sub'_def using hinc by simp
        next
          case False hence "i = n" using \<open>i < Suc n\<close> by simp
          thus ?thesis unfolding sub'_def using hsubn hM'_gt_M by simp
        qed
      qed
      moreover have "\<forall>i < Suc n. \<exists>U\<in>\<A>. {t. sub' i \<le> t \<and> t \<le> sub' (Suc i) \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U"
      proof (intro allI impI)
        fix i assume "i < Suc n"
        show "\<exists>U\<in>\<A>. {t. sub' i \<le> t \<and> t \<le> sub' (Suc i) \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U"
        proof (cases "i < n")
          case True
          hence "sub' i = sub i" "sub' (Suc i) = sub (Suc i)" unfolding sub'_def by simp+
          thus ?thesis using hcov_sub True by simp
        next
          case False hence "i = n" using \<open>i < Suc n\<close> by simp
          hence "sub' i = M" "sub' (Suc i) = M'" unfolding sub'_def using hsubn by simp+
          thus ?thesis using hUM hMM' by auto
        qed
      qed
      moreover have "Suc n \<ge> 1" by simp
      ultimately show ?thesis unfolding A_def using hM'_ge0 hM'_le1 by blast
    qed
    \<comment> \<open>But M' > M = Sup A, contradicting M' \<in> A.\<close>
    hence "M' \<le> M" unfolding M_def using hbdd by (intro cSup_upper) auto
    thus False using hM'_gt_M by linarith
  qed
  \<comment> \<open>From M = 1 and M \<in> A, extract the subdivision.\<close>
  have "1 \<in> A" using hM_A hM_1 by simp
  then obtain n sub where hn: "n \<ge> 1" and hsub0: "sub 0 = (0::real)" and hsubn: "sub n = 1"
      and hinc: "\<forall>i<n. sub i < sub (Suc i)"
      and hcov_sub: "\<forall>i<n. \<exists>U\<in>\<A>. {t. sub i \<le> t \<and> t \<le> sub (Suc i) \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U"
    unfolding A_def by blast
  show ?thesis using hn hsub0 hsubn hinc hcov_sub by blast
qed

text \<open>Bridge: if f: [0,1] → B is continuous (in top1 sense) and V ∈ TB is open,
  then for each s with f(s) ∈ V, there exists ε > 0 with f(Ball(s,ε) ∩ [0,1]) ⊆ V.\<close>
lemma top1_continuous_preimage_ball:
  assumes hf: "top1_continuous_map_on I_set I_top B TB f"
      and hV: "V \<in> TB" and hs: "s \<in> I_set" and hfs: "f s \<in> V"
  shows "\<exists>\<epsilon>>0. f ` {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> V"
proof -
  have hpre: "{s \<in> I_set. f s \<in> V} \<in> I_top"
    using hf hV unfolding top1_continuous_map_on_def by (by100 blast)
  \<comment> \<open>I_top = subspace_topology UNIV top1_open_sets I_set.\<close>
  obtain W where hW: "W \<in> (top1_open_sets :: real set set)" and hpre_eq: "{s \<in> I_set. f s \<in> V} = I_set \<inter> W"
    using hpre unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
  have hW_open: "open W" using hW unfolding top1_open_sets_def by (by100 blast)
  have hs_W: "s \<in> W" using hs hfs hpre_eq by (by100 blast)
  obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" and hball: "\<forall>y. dist y s < \<epsilon> \<longrightarrow> y \<in> W"
    using hW_open hs_W open_dist[of W] by blast
  have "f ` {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> V"
  proof
    fix y assume "y \<in> f ` {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1}"
    then obtain t where ht: "\<bar>t - s\<bar> < \<epsilon>" "0 \<le> t" "t \<le> 1" and hy: "y = f t" by blast
    have "dist t s < \<epsilon>" using ht unfolding dist_real_def by simp
    hence "t \<in> W" using hball by blast
    hence "t \<in> I_set \<inter> W" using ht unfolding top1_unit_interval_def by auto
    hence "t \<in> {s \<in> I_set. f s \<in> V}" using hpre_eq by simp
    thus "y \<in> V" using hy by simp
  qed
  thus ?thesis using h\<epsilon> by blast
qed

(** from \<S>54 Lemma 54.1: path-lifting lemma **)
lemma Lemma_54_1_path_lifting:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and he0: "e0 \<in> E" and hpe0: "p e0 = b0"
      and hf: "top1_is_path_on B TB b0 b1 f"
      and hTB_assm: "is_topology_on B TB"
      and hTE_assm: "is_topology_on E TE"
  shows "\<exists>ftilde. top1_is_path_on E TE e0 (ftilde 1) ftilde
    \<and> (\<forall>s\<in>I_set. p (ftilde s) = f s)"
  \<comment> \<open>Textbook proof (Munkres Lemma 54.1):
     Step 1: Cover B by evenly covered open sets U. By the Lebesgue number lemma,
     find a subdivision 0 = s₀ < ... < sₙ = 1 s.t. each f([sᵢ,sᵢ₊₁]) \<subseteq> some Uᵢ.
     Step 2: Define ftilde step by step. Set ftilde(0) = e₀. For each [sᵢ,sᵢ₊₁],
     ftilde(sᵢ) lies in some slice V₀. Define ftilde(s) = (p|V₀)\<inverse>(f(s)).
     Step 3: Pasting lemma \<Rightarrow> continuous. p \<circ> ftilde = f by construction.\<close>
proof -
  have hf_cont: "top1_continuous_map_on I_set I_top B TB f"
    using hf unfolding top1_is_path_on_def by (by100 blast)
  have hTB: "is_topology_on B TB" using hTB_assm .
  have hB_ne: "B \<noteq> {}"
  proof -
    have "f 0 = b0" using hf unfolding top1_is_path_on_def by simp
    have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have "f 0 \<in> B" using hf_cont h0I unfolding top1_continuous_map_on_def by (by100 blast)
    hence "b0 \<in> B" using hf unfolding top1_is_path_on_def by simp
    thus ?thesis by (by100 blast)
  qed
  have hTE_top: "is_topology_on E TE" using hTE_assm .
  \<comment> \<open>Step 1: Lebesgue subdivision.
     Strategy: for each s \<in> [0,1], f(s) has an evenly covered neighborhood.
     The f-preimages form an open cover of [0,1]. By compactness, finite subcover.
     The Lebesgue number of this cover gives a uniform subdivision.\<close>
  obtain n :: nat and sub :: "nat \<Rightarrow> real" where
      hn: "n \<ge> 1" and hsub0: "sub 0 = 0" and hsubn: "sub n = 1"
      and hsub_inc: "\<forall>i<n. sub i < sub (Suc i)"
      and hcovered: "\<forall>i<n. \<exists>U. openin_on B TB U
          \<and> top1_evenly_covered_on E TE B TB p U
          \<and> f ` {s\<in>I_set. sub i \<le> s \<and> s \<le> sub (Suc i)} \<subseteq> U"
  proof -
    \<comment> \<open>Step 1a: f continuous means f-preimages of open sets are open.
       Step 1b: For each s, f(s) has evenly covered neighborhood U_s open in B.
       Step 1c: f\<inverse>(U_s) open in [0,1] (by continuous_on + open_invariant).
       Step 1d: {f\<inverse>(U_s)} covers [0,1]. By compact_Icc, finite subcover.
       Step 1e: Lebesgue number \<delta> > 0. Take n = \<lceil>1/\<delta>\<rceil>+1, sub(i) = i/n.\<close>
    \<comment> \<open>The proof requires bridging between the abstract top1 topology framework and
       HOL's concrete topological space on reals. The key steps are:
       1. f continuous as continuous_on (from top1_continuous_map_on + subspace bridge)
       2. For each s, f(s) has evenly covered U (from covering map)
       3. f\<inverse>(U) open in [0,1] (continuous preimage of open)
       4. Finite subcover by compact_Icc
       5. Lebesgue number for the finite cover
       6. Uniform subdivision with mesh < Lebesgue number\<close>
    \<comment> \<open>Direct approach using HOL's compact {0..1}.
       For each s \<in> {0..1}, f(s) \<in> B, get evenly covered U_s with f(s) \<in> U_s.
       The covering gives: for each U_s, there exists open W_s in B with f(s) \<in> W_s \<subseteq> U_s.
       f\<inverse>(W_s) is open in {0..1} (by continuous_on + open_invariant).
       By compact {0..1}, finite subcover. Lebesgue number of finite cover gives \<delta>.
       Take n = \<lceil>1/\<delta>\<rceil>, sub(i) = i/n.\<close>
    \<comment> \<open>Use open_cover_subdivision_01: for each s, get ball in the preimage of an evenly covered U.\<close>
    have hf_cont: "top1_continuous_map_on I_set I_top B TB f"
      using hf unfolding top1_is_path_on_def by (by100 blast)
    have hf_B: "\<forall>s\<in>I_set. f s \<in> B" using hf_cont unfolding top1_continuous_map_on_def by (by100 blast)
    \<comment> \<open>The cover: for each s, f\<inverse>(evenly covered U) gives a ball around s.
       The bridge from top1_continuous_map_on to open balls uses:
       I_top = subspace_topology UNIV top1_open_sets I_set,
       top1_open_sets = {U. open U}, open_dist.\<close>
    \<comment> \<open>Build the cover: for each s, get ball and evenly covered U.\<close>
    have hpointwise: "\<forall>s. 0 \<le> s \<and> s \<le> 1 \<longrightarrow>
        (\<exists>\<epsilon>>0. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
             \<and> f ` {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U)"
    proof (intro allI impI)
      fix s :: real assume hs: "0 \<le> s \<and> s \<le> 1"
      have hs_I: "s \<in> I_set" using hs unfolding top1_unit_interval_def by auto
      have hfs: "f s \<in> B" using hf_B hs_I by blast
      obtain U where hbU: "f s \<in> U" and hUec: "top1_evenly_covered_on E TE B TB p U"
        using top1_covering_map_on_evenly_covered[OF hcov hfs] by (by100 blast)
      have hUopen: "openin_on B TB U" using hUec unfolding top1_evenly_covered_on_def by (by100 blast)
      hence hU_TB: "U \<in> TB" using hUopen unfolding openin_on_def by (by100 blast)
      obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" and hball: "f ` {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U"
        using top1_continuous_preimage_ball[OF hf_cont hU_TB hs_I hbU] by blast
      show "\<exists>\<epsilon>>0. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
           \<and> f ` {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U"
        using h\<epsilon> hUopen hUec hball by blast
    qed
    \<comment> \<open>Apply open_cover_subdivision_01 with hpointwise to get subdivision
       where each piece maps into an evenly covered set.
       The pointwise cover from hpointwise provides balls around each s ∈ [0,1]
       that map into evenly covered sets. The creeping lemma (open_cover_subdivision_01)
       gives a subdivision of [0,1] fine enough that each piece lies in one ball.
       Combining: each subdivision piece maps into the corresponding evenly covered set.\<close>
    \<comment> \<open>Use SOME to pick \<epsilon>(s) for each s, then build cover.\<close>
    define eps_fn where "eps_fn s = (SOME \<epsilon>. \<epsilon> > 0 \<and>
        (\<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
             \<and> f ` {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U))" for s
    have heps_spec: "\<forall>s. 0 \<le> s \<and> s \<le> 1 \<longrightarrow> eps_fn s > 0 \<and>
        (\<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
             \<and> f ` {t. \<bar>t - s\<bar> < eps_fn s \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U)"
    proof (intro allI impI)
      fix s :: real assume hs: "0 \<le> s \<and> s \<le> 1"
      have "\<exists>\<epsilon>. \<epsilon> > 0 \<and> (\<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
           \<and> f ` {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U)"
        using hpointwise[rule_format, OF hs] by (by100 blast)
      thus "eps_fn s > 0 \<and> (\<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
           \<and> f ` {t. \<bar>t - s\<bar> < eps_fn s \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U)"
        unfolding eps_fn_def by (rule someI_ex)
    qed
    define \<A>c where "\<A>c = (\<lambda>s. {t. \<bar>t - s\<bar> < eps_fn s \<and> 0 \<le> t \<and> t \<le> 1}) ` {0..1::real}"
    have hcov_hyp: "\<forall>s::real. 0 \<le> s \<and> s \<le> 1 \<longrightarrow>
        (\<exists>U\<in>\<A>c. s \<in> U \<and> (\<exists>\<epsilon>>0. {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U))"
    proof (intro allI impI)
      fix s :: real assume hs: "0 \<le> s \<and> s \<le> 1"
      have heps: "eps_fn s > 0" using heps_spec hs by (by100 blast)
      let ?U = "{t. \<bar>t - s\<bar> < eps_fn s \<and> 0 \<le> t \<and> t \<le> 1}"
      have "?U \<in> \<A>c" unfolding \<A>c_def
        apply (rule image_eqI[of _ _ s])
         apply (rule refl)
        using hs by simp
      moreover have "s \<in> ?U" using heps hs by (by100 auto)
      moreover have "\<exists>\<epsilon>>0. {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> ?U"
        using heps by (intro exI[of _ "eps_fn s"]) auto
      ultimately show "\<exists>U\<in>\<A>c. s \<in> U \<and> (\<exists>\<epsilon>>0. {t. \<bar>t - s\<bar> < \<epsilon> \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> U)"
        apply (intro bexI conjI)
          apply assumption+
        done
    qed
    obtain m sub_m where hm: "m \<ge> 1" and hsub_m0: "sub_m 0 = 0" and hsub_mn: "sub_m m = 1"
        and hinc_m: "\<forall>i<m. sub_m i < sub_m (Suc i)"
        and hcov_m: "\<forall>i<m. \<exists>U\<in>\<A>c. {s. sub_m i \<le> s \<and> s \<le> sub_m (Suc i) \<and> 0 \<le> s \<and> s \<le> 1} \<subseteq> U"
      using open_cover_subdivision_01[OF hcov_hyp] by auto
    have "\<forall>i<m. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
        \<and> f ` {s\<in>I_set. sub_m i \<le> s \<and> s \<le> sub_m (Suc i)} \<subseteq> U"
    proof (intro allI impI)
      fix i assume hi: "i < m"
      obtain A where hA: "A \<in> \<A>c" and hsub: "{s. sub_m i \<le> s \<and> s \<le> sub_m (Suc i) \<and> 0 \<le> s \<and> s \<le> 1} \<subseteq> A"
        using hcov_m hi by (by100 blast)
      \<comment> \<open>A = {t. |t-s0| < eps_fn s0 ...} for some s0 ∈ [0,1].\<close>
      obtain s0 where hs0: "s0 \<in> {0..1::real}" and hA_eq: "A = {t. \<bar>t - s0\<bar> < eps_fn s0 \<and> 0 \<le> t \<and> t \<le> 1}"
        using hA unfolding \<A>c_def by (by100 blast)
      have hs0_01: "0 \<le> s0 \<and> s0 \<le> 1" using hs0 by simp
      obtain V where hV: "openin_on B TB V \<and> top1_evenly_covered_on E TE B TB p V
          \<and> f ` {t. \<bar>t - s0\<bar> < eps_fn s0 \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> V"
        using heps_spec[rule_format, OF hs0_01] by (by100 blast)
      have hpiece_sub: "{s\<in>I_set. sub_m i \<le> s \<and> s \<le> sub_m (Suc i)} \<subseteq> A"
        using hsub unfolding top1_unit_interval_def by auto
      have "f ` {s\<in>I_set. sub_m i \<le> s \<and> s \<le> sub_m (Suc i)} \<subseteq> f ` A"
        using hpiece_sub by (by100 blast)
      also have "\<dots> = f ` {t. \<bar>t - s0\<bar> < eps_fn s0 \<and> 0 \<le> t \<and> t \<le> 1}" using hA_eq by simp
      also have "\<dots> \<subseteq> V" using hV by (by100 blast)
      finally show "\<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
          \<and> f ` {s\<in>I_set. sub_m i \<le> s \<and> s \<le> sub_m (Suc i)} \<subseteq> U"
        using hV by (by100 blast)
    qed
    thus ?thesis using hm hsub_m0 hsub_mn hinc_m that by blast
  qed
  \<comment> \<open>Step 2: Lift interval by interval by induction on the number of subintervals.
     Base: ftilde(0) = e0. Inductive step: given ftilde on [0, sub(i)],
     f([sub(i), sub(i+1)]) \<subseteq> U for some evenly covered U. ftilde(sub(i)) \<in> some slice V_0.
     Define ftilde(s) = (p|V_0)^{-1}(f(s)) for s \<in> [sub(i), sub(i+1)].
     Continuity by the pasting lemma.\<close>
  have "\<exists>ftilde. (\<forall>s\<in>I_set. ftilde s \<in> E)
      \<and> ftilde 0 = e0
      \<and> (\<forall>s\<in>I_set. p (ftilde s) = f s)
      \<and> top1_continuous_map_on I_set I_top E TE ftilde"
  proof -
    \<comment> \<open>Induction: for each k \<le> n, there exists ftk on [0, sub(k)] lifting f.
       Base: ftk = const e0 at k=0. Inductive step: extend via (p|V_0)^{-1} ∘ f.
       At k = n, sub(n) = 1, giving ftilde on [0,1] = I_set.\<close>
    \<comment> \<open>Induction on k: at each step, extend the lift by one interval.\<close>
    have "\<forall>k\<le>n. \<exists>ftk. ftk 0 = e0 \<and> (\<forall>s\<in>I_set. s \<le> sub k \<longrightarrow> ftk s \<in> E)
        \<and> (\<forall>s\<in>I_set. s \<le> sub k \<longrightarrow> p (ftk s) = f s)
        \<and> top1_continuous_map_on {s\<in>I_set. s \<le> sub k}
            (subspace_topology I_set I_top {s\<in>I_set. s \<le> sub k}) E TE ftk"
    proof (intro allI impI)
      fix k show "k \<le> n \<Longrightarrow> \<exists>ftk. ftk 0 = e0 \<and> (\<forall>s\<in>I_set. s \<le> sub k \<longrightarrow> ftk s \<in> E)
          \<and> (\<forall>s\<in>I_set. s \<le> sub k \<longrightarrow> p (ftk s) = f s)
          \<and> top1_continuous_map_on {s\<in>I_set. s \<le> sub k}
              (subspace_topology I_set I_top {s\<in>I_set. s \<le> sub k}) E TE ftk"
      proof (induction k)
        case 0
        \<comment> \<open>Base: sub 0 = 0. Only s = 0 satisfies s \<le> 0, and ftk 0 = e0.\<close>
        have hf0_eq: "f 0 = p e0" using hpe0 hf unfolding top1_is_path_on_def by simp
        have hcont0: "top1_continuous_map_on {s\<in>I_set. s \<le> sub 0}
            (subspace_topology I_set I_top {s\<in>I_set. s \<le> sub 0}) E TE (\<lambda>_. e0)"
        proof -
          have hdom: "{s\<in>I_set. s \<le> sub 0} = {0}" using hsub0 unfolding top1_unit_interval_def by auto
          have hTsub: "is_topology_on {0::real} (subspace_topology I_set I_top {0})"
            by (rule subspace_topology_is_topology_on[OF top1_unit_interval_topology_is_topology_on])
               (simp add: top1_unit_interval_def)
          have hTE: "is_topology_on E TE" using hTE_top .
          show ?thesis unfolding hdom
            by (rule top1_continuous_map_on_const[OF hTsub hTE he0])
        qed
        show ?case
          apply (intro exI[of _ "\<lambda>_. e0"] conjI allI ballI impI)
          using he0 hf0_eq hsub0 hcont0 unfolding top1_unit_interval_def by auto
      next
        case (Suc k)
        \<comment> \<open>IH: \<exists>ftk on [0, sub k]. Extend to [0, sub(Suc k)].\<close>
        have hk_le: "k \<le> n" using Suc.prems by simp
        obtain ftk where hftk0: "ftk 0 = e0"
            and hftk_E: "\<forall>s\<in>I_set. s \<le> sub k \<longrightarrow> ftk s \<in> E"
            and hftkp: "\<forall>s\<in>I_set. s \<le> sub k \<longrightarrow> p (ftk s) = f s"
            and hftk_cont: "top1_continuous_map_on {s\<in>I_set. s \<le> sub k}
                (subspace_topology I_set I_top {s\<in>I_set. s \<le> sub k}) E TE ftk"
          using Suc.IH[OF hk_le] by (by100 blast)
        \<comment> \<open>f maps [sub k, sub(Suc k)] into some evenly covered U.\<close>
        have hSk_lt: "k < n" using Suc.prems by simp
        obtain U where hUo: "openin_on B TB U"
            and hUec: "top1_evenly_covered_on E TE B TB p U"
            and hfU: "f ` {s\<in>I_set. sub k \<le> s \<and> s \<le> sub (Suc k)} \<subseteq> U"
          using hcovered[rule_format, OF hSk_lt] by (by100 blast)
        \<comment> \<open>Extend ftk using the inverse of p on the appropriate slice.\<close>
        \<comment> \<open>ftk(sub k) \<in> E, p(ftk(sub k)) = f(sub k) \<in> U.\<close>
        have hsub_mono: "\<And>i j. i \<le> j \<Longrightarrow> j \<le> n \<Longrightarrow> sub i \<le> sub j"
        proof -
          fix i j :: nat assume hij: "i \<le> j" and hjn: "j \<le> n"
          show "sub i \<le> sub j" using hij hjn
          proof (induction "j - i" arbitrary: j)
            case 0 thus ?case by simp
          next
            case (Suc d)
            hence hj_pos: "j > 0" by simp
            obtain j' where hj': "j = Suc j'" using hj_pos by (cases j) auto
            have "i \<le> j'" using Suc.hyps hj' by simp
            have "j' \<le> n" using Suc.prems hj' by simp
            have "d = j' - i" using Suc.hyps hj' by simp
            have "sub i \<le> sub j'" using Suc.hyps(1)[OF \<open>d = j' - i\<close> \<open>i \<le> j'\<close> \<open>j' \<le> n\<close>] .
            also have "sub j' < sub (Suc j')" using hsub_inc \<open>j' \<le> n\<close> Suc.prems hj' by auto
            finally show ?case using hj' by simp
          qed
        qed
        have hsubk_I: "sub k \<in> I_set"
        proof -
          have "0 \<le> sub k" using hsub_mono[of 0 k] hk_le hsub0 by simp
          moreover have "sub k \<le> 1" using hsub_mono[of k n] hk_le hsubn by simp
          ultimately show ?thesis unfolding top1_unit_interval_def by auto
        qed
        have hftk_subk: "ftk (sub k) \<in> E" using hftk_E hsubk_I by (by100 blast)
        have hpftk: "p (ftk (sub k)) = f (sub k)" using hftkp hsubk_I by (by100 blast)
        have hfsk_U: "f (sub k) \<in> U"
        proof -
          have "sub k \<in> {s\<in>I_set. sub k \<le> s \<and> s \<le> sub (Suc k)}" using hsubk_I hsub_inc hSk_lt by auto
          thus ?thesis using hfU by (by100 blast)
        qed
        \<comment> \<open>ftk(sub k) is in the preimage p\<inverse>(U), hence in some slice V₀.\<close>
        obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
            and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
            and hV_union: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
            and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
                U (subspace_topology B TB U) p"
          using hUec unfolding top1_evenly_covered_on_def by auto
        have hftk_pU: "ftk (sub k) \<in> {x\<in>E. p x \<in> U}"
          using hftk_subk hpftk hfsk_U by simp
        obtain V0 where hV0: "V0 \<in> \<V>" and hftk_V0: "ftk (sub k) \<in> V0"
          using hftk_pU hV_union by (by100 blast)
        \<comment> \<open>p|V₀ is a homeomorphism V₀ \<rightarrow> U. Its inverse maps f(s) to a lift.\<close>
        \<comment> \<open>Define ft_{k+1}(s) = ftk(s) for s \<le> sub k, (p|V₀)\<inverse>(f(s)) for s \<in> [sub k, sub(Suc k)].\<close>
        define ftk' where "ftk' s = (if s \<le> sub k then ftk s else inv_into V0 p (f s))" for s
        have hftk'0: "ftk' 0 = e0"
        proof -
          have "(0::real) \<le> sub k" using hsub_mono[of 0 k] hk_le hsub0 by simp
          thus ?thesis unfolding ftk'_def using hftk0 by simp
        qed
        \<comment> \<open>p|V₀ is bijective onto U.\<close>
        have hbij: "bij_betw p V0 U"
          using hV0 hV_homeo unfolding top1_homeomorphism_on_def by (by100 blast)
        have hV0_E: "V0 \<subseteq> E"
          using hV0 hV_union by (by100 blast)
        have hftk'_E: "\<forall>s\<in>I_set. s \<le> sub (Suc k) \<longrightarrow> ftk' s \<in> E"
        proof (intro ballI impI)
          fix s assume hs: "s \<in> I_set" and hle: "s \<le> sub (Suc k)"
          show "ftk' s \<in> E"
          proof (cases "s \<le> sub k")
            case True thus ?thesis unfolding ftk'_def using hftk_E hs by simp
          next
            case False
            hence "ftk' s = inv_into V0 p (f s)" unfolding ftk'_def by simp
            moreover have "f s \<in> U"
              using hfU hs False hle unfolding top1_unit_interval_def by auto
            have "p ` V0 = U" using hbij unfolding bij_betw_def by (by100 blast)
            hence "f s \<in> p ` V0" using \<open>f s \<in> U\<close> by simp
            hence "inv_into V0 p (f s) \<in> V0" by (rule inv_into_into)
            ultimately show ?thesis using hV0_E by auto
          qed
        qed
        have hftk'p: "\<forall>s\<in>I_set. s \<le> sub (Suc k) \<longrightarrow> p (ftk' s) = f s"
        proof (intro ballI impI)
          fix s assume hs: "s \<in> I_set" and hle: "s \<le> sub (Suc k)"
          show "p (ftk' s) = f s"
          proof (cases "s \<le> sub k")
            case True thus ?thesis unfolding ftk'_def using hftkp hs by simp
          next
            case False
            hence "ftk' s = inv_into V0 p (f s)" unfolding ftk'_def by simp
            moreover have "f s \<in> U"
              using hfU hs False hle unfolding top1_unit_interval_def by auto
            hence "p (inv_into V0 p (f s)) = f s"
              using hbij unfolding bij_betw_def by (by100 auto)
            ultimately show ?thesis by simp
          qed
        qed
        \<comment> \<open>Continuity of ftk' on [0, sub(Suc k)] by pasting lemma.\<close>
        have hftk'_cont: "top1_continuous_map_on {s\<in>I_set. s \<le> sub (Suc k)}
            (subspace_topology I_set I_top {s\<in>I_set. s \<le> sub (Suc k)}) E TE ftk'"
        proof -
          let ?Xk1 = "{s\<in>I_set. s \<le> sub (Suc k)}"
          let ?TXk1 = "subspace_topology I_set I_top ?Xk1"
          let ?A = "{s\<in>I_set. s \<le> sub k}"
          let ?B = "{s\<in>I_set. sub k \<le> s \<and> s \<le> sub (Suc k)}"
          have hXk1_sub: "?Xk1 \<subseteq> I_set" by (by100 blast)
          have hTI: "is_topology_on I_set I_top"
            by (rule top1_unit_interval_topology_is_topology_on)
          have hTXk1: "is_topology_on ?Xk1 ?TXk1"
            by (rule subspace_topology_is_topology_on[OF hTI hXk1_sub])
          have hTE': "is_topology_on E TE" using hTE_top .
          have hsk_le_sk1: "sub k \<le> sub (Suc k)" using hsub_inc hSk_lt by auto
          have hA_closed: "closedin_on ?Xk1 ?TXk1 ?A"
          proof -
            have hAsub: "?A \<subseteq> ?Xk1" using hsk_le_sk1 by auto
            have hcomp: "?Xk1 - ?A = ?Xk1 \<inter> {s\<in>I_set. sub k < s}" by auto
            have "open {s::real. sub k < s}"
              using open_greaterThan[of "sub k"] unfolding greaterThan_def by simp
            hence "{s::real. sub k < s} \<in> top1_open_sets"
              unfolding top1_open_sets_def by (by100 blast)
            hence hgr_os: "{s::real. sub k < s} \<in> top1_open_sets" .
            have hgr_I: "I_set \<inter> {s. sub k < s} \<in> I_top"
              unfolding top1_unit_interval_topology_def subspace_topology_def
              using hgr_os by (by100 blast)
            have "I_set \<inter> {s. sub k < s} = {s\<in>I_set. sub k < s}" by auto
            hence "{s\<in>I_set. sub k < s} \<in> I_top" using hgr_I by simp
            hence "?Xk1 \<inter> {s\<in>I_set. sub k < s} \<in> ?TXk1"
              unfolding subspace_topology_def by (by100 blast)
            hence "?Xk1 - ?A \<in> ?TXk1" using hcomp by simp
            moreover have "?A \<subseteq> ?Xk1" using hAsub .
            ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
          qed
          have hB_closed: "closedin_on ?Xk1 ?TXk1 ?B"
          proof -
            have hBsub: "?B \<subseteq> ?Xk1" by (by100 blast)
            have hcomp: "?Xk1 - ?B = ?Xk1 \<inter> {s\<in>I_set. s < sub k}"
            proof -
              have "sub k \<le> sub (Suc k)" using hsub_inc hSk_lt by auto
              thus ?thesis by auto
            qed
            have "open {s::real. s < sub k}"
              using open_lessThan[of "sub k"] unfolding lessThan_def by simp
            hence "{s::real. s < sub k} \<in> top1_open_sets"
              unfolding top1_open_sets_def by (by100 blast)
            hence hlt_os: "{s::real. s < sub k} \<in> top1_open_sets" .
            have hlt_I: "I_set \<inter> {s. s < sub k} \<in> I_top"
              unfolding top1_unit_interval_topology_def subspace_topology_def
              using hlt_os by (by100 blast)
            have "I_set \<inter> {s. s < sub k} = {s\<in>I_set. s < sub k}" by auto
            hence "{s\<in>I_set. s < sub k} \<in> I_top" using hlt_I by simp
            hence "?Xk1 \<inter> {s\<in>I_set. s < sub k} \<in> ?TXk1"
              unfolding subspace_topology_def by (by100 blast)
            hence "?Xk1 - ?B \<in> ?TXk1" using hcomp by simp
            moreover have "?B \<subseteq> ?Xk1" using hBsub .
            ultimately show ?thesis unfolding closedin_on_def by (by100 blast)
          qed
          have hAB: "?A \<union> ?B = ?Xk1"
          proof -
            have "sub k \<le> sub (Suc k)" using hsub_inc hSk_lt by auto
            thus ?thesis by auto
          qed
          have hrange: "\<forall>s\<in>?Xk1. ftk' s \<in> E"
          proof
            fix s assume "s \<in> ?Xk1"
            hence "s \<in> I_set" and "s \<le> sub (Suc k)" by auto
            thus "ftk' s \<in> E" using hftk'_E by (by100 blast)
          qed
          \<comment> \<open>ftk' continuous on A: equals ftk which is continuous by IH.\<close>
          have hcont_A: "top1_continuous_map_on ?A (subspace_topology ?Xk1 ?TXk1 ?A) E TE ftk'"
          proof -
            have hAsub: "?A \<subseteq> ?Xk1" using hsk_le_sk1 by auto
            have hTsub: "subspace_topology ?Xk1 ?TXk1 ?A = subspace_topology I_set I_top ?A"
              by (rule subspace_topology_trans[OF hAsub])
            \<comment> \<open>ftk' = ftk on ?A, and ftk is continuous on ?A by IH.\<close>
            have hftk'_eq: "\<forall>s\<in>?A. ftk' s = ftk s"
              unfolding ftk'_def by simp
            show ?thesis unfolding hTsub
              unfolding top1_continuous_map_on_def
            proof (intro conjI ballI)
              fix s assume "s \<in> ?A"
              thus "ftk' s \<in> E" using hftk'_eq hftk_E by auto
            next
              fix V assume "V \<in> TE"
              have "{s \<in> ?A. ftk' s \<in> V} = {s \<in> ?A. ftk s \<in> V}"
                using hftk'_eq by auto
              also have "\<dots> \<in> subspace_topology I_set I_top ?A"
                using hftk_cont \<open>V \<in> TE\<close> unfolding top1_continuous_map_on_def
                by (by100 blast)
              finally show "{s \<in> ?A. ftk' s \<in> V} \<in> subspace_topology I_set I_top ?A" .
            qed
          qed
          \<comment> \<open>ftk' continuous on B: equals inv_into V0 p \<circ> f (homeomorphism inverse \<circ> continuous).\<close>
          have hcont_B: "top1_continuous_map_on ?B (subspace_topology ?Xk1 ?TXk1 ?B) E TE ftk'"
          proof -
            have hBsub: "?B \<subseteq> ?Xk1" by (by100 blast)
            have hTBsub: "subspace_topology ?Xk1 ?TXk1 ?B = subspace_topology I_set I_top ?B"
              by (rule subspace_topology_trans[OF hBsub])
            \<comment> \<open>On B, ftk'(s) = inv_into V0 p (f s) for all s (including s = sub k,
               since ftk(sub k) = inv_into V0 p (f(sub k)) by construction).\<close>
            have hftk'_eq_inv: "\<forall>s\<in>?B. ftk' s = inv_into V0 p (f s)"
            proof
              fix s assume hs: "s \<in> ?B"
              show "ftk' s = inv_into V0 p (f s)"
              proof (cases "s \<le> sub k")
                case True
                hence "s = sub k" using hs by auto
                \<comment> \<open>ftk'(sub k) = ftk(sub k). And inv_into V0 p (f(sub k)) = ftk(sub k)
                   since ftk(sub k) \<in> V0 and p is bijective on V0.\<close>
                have "ftk' s = ftk s" unfolding ftk'_def using True by simp
                also have "\<dots> = ftk (sub k)" using \<open>s = sub k\<close> by simp
                also have "\<dots> = inv_into V0 p (f (sub k))"
                proof -
                  have "ftk (sub k) \<in> V0" using hftk_V0 .
                  have "p (ftk (sub k)) = f (sub k)" using hpftk .
                  have "inj_on p V0" using hbij unfolding bij_betw_def by (by100 blast)
                  show ?thesis using inv_into_f_f[OF \<open>inj_on p V0\<close> \<open>ftk (sub k) \<in> V0\<close>]
                      \<open>p (ftk (sub k)) = f (sub k)\<close> by simp
                qed
                finally show ?thesis using \<open>s = sub k\<close> by simp
              next
                case False
                thus ?thesis unfolding ftk'_def by simp
              qed
            qed
            \<comment> \<open>inv_into V0 p \<circ> f is continuous on B: composition of continuous functions.\<close>
            \<comment> \<open>The composition inv_into V0 p \<circ> f is continuous on B.
               We use: f continuous I_set \<rightarrow> B, inv_into V0 p continuous U \<rightarrow> V0 \<subseteq> E,
               f(B) \<subseteq> U, and composition preserves continuity.\<close>
            have hinv_cont: "top1_continuous_map_on U (subspace_topology B TB U) V0 (subspace_topology E TE V0)
                (inv_into V0 p)"
              using hV_homeo hV0 unfolding top1_homeomorphism_on_def by (by100 blast)
            \<comment> \<open>f restricted to B is continuous B \<rightarrow> U.\<close>
            have hf_B_cont: "top1_continuous_map_on ?B (subspace_topology I_set I_top ?B) U (subspace_topology B TB U) f"
            proof -
              \<comment> \<open>f maps ?B into U (from hfU).\<close>
              have hfBU: "\<forall>s\<in>?B. f s \<in> U"
                using hfU unfolding top1_unit_interval_def by auto
              \<comment> \<open>For V \<in> subspace_topology B TB U, V = U \<inter> W for some W \<in> TB.
                 {s\<in>B. f s \<in> V} = {s\<in>B. f s \<in> W} \<inter> {s\<in>B. f s \<in> U} = {s\<in>B. f s \<in> W}.\<close>
              show ?thesis unfolding top1_continuous_map_on_def
              proof (intro conjI ballI)
                fix s assume "s \<in> ?B" thus "f s \<in> U" using hfBU by (by100 blast)
              next
                fix V assume hV: "V \<in> subspace_topology B TB U"
                then obtain W where hW: "W \<in> TB" and hVeq: "V = U \<inter> W"
                  unfolding subspace_topology_def by (by100 auto)
                have "{s \<in> ?B. f s \<in> V} = {s \<in> ?B. f s \<in> W}"
                  using hVeq hfBU by (by100 auto)
                also have "\<dots> = ?B \<inter> {s \<in> I_set. f s \<in> W}" by auto
                also have "{s \<in> I_set. f s \<in> W} \<in> I_top"
                  using hf_cont hW unfolding top1_continuous_map_on_def by (by100 blast)
                hence "?B \<inter> {s \<in> I_set. f s \<in> W} \<in> subspace_topology I_set I_top ?B"
                  unfolding subspace_topology_def by (by100 blast)
                finally show "{s \<in> ?B. f s \<in> V} \<in> subspace_topology I_set I_top ?B" .
              qed
            qed
            \<comment> \<open>Compose: inv_into V0 p \<circ> f continuous B \<rightarrow> V0 \<subseteq> E.\<close>
            have hcomp_cont: "top1_continuous_map_on ?B (subspace_topology I_set I_top ?B)
                V0 (subspace_topology E TE V0) (\<lambda>s. inv_into V0 p (f s))"
            proof -
              have heq: "(\<lambda>s. inv_into V0 p (f s)) = (inv_into V0 p) \<circ> f" by (rule ext) simp
              show ?thesis unfolding heq
                by (rule top1_continuous_map_on_comp[OF hf_B_cont hinv_cont])
            qed
            \<comment> \<open>Lift from V0-topology to E-topology.\<close>
            show ?thesis unfolding hTBsub
              unfolding top1_continuous_map_on_def
            proof (intro conjI ballI)
              fix s assume hs: "s \<in> ?B"
              hence "s \<in> I_set" and "s \<le> sub (Suc k)" by auto
              thus "ftk' s \<in> E" using hftk'_E by (by100 blast)
            next
              fix V assume hV_TE: "V \<in> TE"
              \<comment> \<open>V \<inter> V0 \<in> subspace_topology E TE V0.\<close>
              have hVV0: "V \<inter> V0 \<in> subspace_topology E TE V0"
                unfolding subspace_topology_def using hV_TE by (by100 blast)
              \<comment> \<open>{s\<in>B. ftk' s \<in> V} = {s\<in>B. inv_into V0 p (f s) \<in> V \<inter> V0}
                 since inv_into V0 p (f s) \<in> V0 for s \<in> B.\<close>
              have hpreq: "{s \<in> ?B. ftk' s \<in> V} = {s \<in> ?B. inv_into V0 p (f s) \<in> V \<inter> V0}"
              proof -
                have "\<And>s. s \<in> ?B \<Longrightarrow> ftk' s = inv_into V0 p (f s)"
                  using hftk'_eq_inv by (by100 blast)
                moreover have "\<And>s. s \<in> ?B \<Longrightarrow> inv_into V0 p (f s) \<in> V0"
                proof -
                  fix s assume hs: "s \<in> ?B"
                  have "f s \<in> U" using hfU hs unfolding top1_unit_interval_def by auto
                  have "p ` V0 = U" using hbij unfolding bij_betw_def by (by100 blast)
                  hence "f s \<in> p ` V0" using \<open>f s \<in> U\<close> by simp
                  thus "inv_into V0 p (f s) \<in> V0" by (rule inv_into_into)
                qed
                ultimately show ?thesis by auto
              qed
              have "{s \<in> ?B. inv_into V0 p (f s) \<in> V \<inter> V0} \<in> subspace_topology I_set I_top ?B"
                using hcomp_cont hVV0 unfolding top1_continuous_map_on_def by (by100 blast)
              thus "{s \<in> ?B. ftk' s \<in> V} \<in> subspace_topology I_set I_top ?B"
                using hpreq by simp
            qed
          qed
          show ?thesis
            by (rule pasting_lemma_two_closed[OF hTXk1 hTE' hA_closed hB_closed hAB hrange hcont_A hcont_B])
        qed
        show ?case using hftk'0 hftk'_E hftk'p hftk'_cont by (by100 blast)
      qed
    qed
    hence "\<exists>ftilde. ftilde 0 = e0 \<and> (\<forall>s\<in>I_set. ftilde s \<in> E)
        \<and> (\<forall>s\<in>I_set. p (ftilde s) = f s)
        \<and> top1_continuous_map_on I_set I_top E TE ftilde"
    proof -
      assume h: "\<forall>k\<le>n. \<exists>ftk. ftk 0 = e0 \<and> (\<forall>s\<in>I_set. s \<le> sub k \<longrightarrow> ftk s \<in> E)
          \<and> (\<forall>s\<in>I_set. s \<le> sub k \<longrightarrow> p (ftk s) = f s)
          \<and> top1_continuous_map_on {s\<in>I_set. s \<le> sub k}
              (subspace_topology I_set I_top {s\<in>I_set. s \<le> sub k}) E TE ftk"
      obtain ftilde where hft0: "ftilde 0 = e0"
          and hftE: "\<forall>s\<in>I_set. s \<le> sub n \<longrightarrow> ftilde s \<in> E"
          and hftp: "\<forall>s\<in>I_set. s \<le> sub n \<longrightarrow> p (ftilde s) = f s"
          and hcont: "top1_continuous_map_on {s\<in>I_set. s \<le> sub n}
              (subspace_topology I_set I_top {s\<in>I_set. s \<le> sub n}) E TE ftilde"
        using h[rule_format, of n] by auto
      \<comment> \<open>Since sub n = 1, {s\<in>I_set. s \<le> sub n} = I_set.\<close>
      have hI_eq: "{s\<in>I_set. s \<le> sub n} = I_set"
        using hsubn unfolding top1_unit_interval_def by auto
      have hft_cont: "top1_continuous_map_on I_set I_top E TE ftilde"
      proof -
        have "subspace_topology I_set I_top I_set = I_top"
          unfolding top1_unit_interval_topology_def
          by (rule subspace_topology_trans) simp
        thus ?thesis using hcont hI_eq by simp
      qed
      show ?thesis using hft0 hftE hftp hft_cont hsubn
        unfolding top1_unit_interval_def by auto
    qed
    thus ?thesis by (by100 blast)
  qed
  \<comment> \<open>Assemble into path.\<close>
  then obtain ftilde where hft_mem: "\<forall>s\<in>I_set. ftilde s \<in> E"
      and hft0: "ftilde 0 = e0"
      and hftp: "\<forall>s\<in>I_set. p (ftilde s) = f s"
      and hft_cont: "top1_continuous_map_on I_set I_top E TE ftilde" by (by100 blast)
  have "top1_is_path_on E TE e0 (ftilde 1) ftilde"
    unfolding top1_is_path_on_def using hft_cont hft0 by (by100 simp)
  thus ?thesis using hftp by (by100 blast)
qed

text \<open>Helper: s \<mapsto> (s, c) is continuous I \<rightarrow> I \<times> I when c \<in> I.\<close>
lemma pair_s_const_continuous:
  assumes hc: "c \<in> I_set"
  shows "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>s. (s, c))"
proof -
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
    unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  \<comment> \<open>pi_1 ∘ (s ↦ (s, c)) = id, and pi_2 ∘ (s ↦ (s, c)) = const c; both continuous.\<close>
  have hid: "top1_continuous_map_on I_set I_top I_set I_top id"
    by (rule top1_continuous_map_on_id[OF hTI])
  have hconst_c: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>_. c)"
    by (rule top1_continuous_map_on_const[OF hTI hTI hc])
  have hpi1_eq: "(pi1 \<circ> (\<lambda>s. (s, c))) = id"
    unfolding pi1_def by (rule ext) simp
  have hpi2_eq: "(pi2 \<circ> (\<lambda>s. (s, c))) = (\<lambda>_. c)"
    unfolding pi2_def by (rule ext) simp
  have hpi1_cont: "top1_continuous_map_on I_set I_top I_set I_top (pi1 \<circ> (\<lambda>s. (s, c)))"
    using hid unfolding hpi1_eq .
  have hpi2_cont: "top1_continuous_map_on I_set I_top I_set I_top (pi2 \<circ> (\<lambda>s. (s, c)))"
    using hconst_c unfolding hpi2_eq .
  show ?thesis
    unfolding II_topology_def
    using iffD2[OF Theorem_18_4[OF hTI hTI hTI]] hpi1_cont hpi2_cont by blast
qed

text \<open>Helper: t \<mapsto> (c, t) is continuous I \<rightarrow> I \<times> I when c \<in> I.\<close>
lemma pair_const_t_continuous:
  assumes hc: "c \<in> I_set"
  shows "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>t. (c, t))"
proof -
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hid: "top1_continuous_map_on I_set I_top I_set I_top id"
    by (rule top1_continuous_map_on_id[OF hTI])
  have hconst_c: "top1_continuous_map_on I_set I_top I_set I_top (\<lambda>_. c)"
    by (rule top1_continuous_map_on_const[OF hTI hTI hc])
  have hpi1_eq: "(pi1 \<circ> (\<lambda>t. (c, t))) = (\<lambda>_. c)"
    unfolding pi1_def by (rule ext) simp
  have hpi2_eq: "(pi2 \<circ> (\<lambda>t. (c, t))) = id"
    unfolding pi2_def by (rule ext) simp
  have hpi1_cont: "top1_continuous_map_on I_set I_top I_set I_top (pi1 \<circ> (\<lambda>t. (c, t)))"
    using hconst_c unfolding hpi1_eq .
  have hpi2_cont: "top1_continuous_map_on I_set I_top I_set I_top (pi2 \<circ> (\<lambda>t. (c, t)))"
    using hid unfolding hpi2_eq .
  show ?thesis
    unfolding II_topology_def
    using iffD2[OF Theorem_18_4[OF hTI hTI hTI]] hpi1_cont hpi2_cont by (by100 blast)
qed

(** Uniqueness part of Lemma 54.1 (implicit in Munkres): given a path f in B with
    two lifts ftilde_1, ftilde_2 in E both starting at e_0, they are equal. **)
lemma Lemma_54_1_uniqueness:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and he0: "e0 \<in> E" and hpe0: "p e0 = b0"
      and hf: "top1_is_path_on B TB b0 b1 f"
      and hft1: "top1_is_path_on E TE e0 e1 ftilde_1"
      and hft1p: "(\<forall>s\<in>I_set. p (ftilde_1 s) = f s)"
      and hft2: "top1_is_path_on E TE e0 e1' ftilde_2"
      and hft2p: "(\<forall>s\<in>I_set. p (ftilde_2 s) = f s)"
  shows "\<forall>s\<in>I_set. ftilde_1 s = ftilde_2 s"
proof -
  \<comment> \<open>Munkres 54.1 uniqueness: open-closed argument on the agreement set.\<close>
  let ?S = "{s \<in> I_set. ftilde_1 s = ftilde_2 s}"
  have hS_nonempty: "0 \<in> ?S"
  proof -
    have "ftilde_1 0 = e0" using hft1 unfolding top1_is_path_on_def by simp
    moreover have "ftilde_2 0 = e0" using hft2 unfolding top1_is_path_on_def by simp
    moreover have "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    ultimately show ?thesis by simp
  qed
  have hS_open: "openin_on I_set I_top ?S"
    \<comment> \<open>For s \<in> S: f(s) \<in> some evenly covered U. ftilde_1(s) = ftilde_2(s) \<in> some slice V0.
       Near s, both lifts stay in V0 (continuity). In V0, p is injective, so they agree.\<close>
    unfolding openin_on_def
  proof (intro conjI)
    show "?S \<in> I_top"
    proof -
      have hft1_cont: "top1_continuous_map_on I_set I_top E TE ftilde_1"
        using hft1 unfolding top1_is_path_on_def by (by100 blast)
      have hft2_cont: "top1_continuous_map_on I_set I_top E TE ftilde_2"
        using hft2 unfolding top1_is_path_on_def by (by100 blast)
      have hf_cont: "top1_continuous_map_on I_set I_top B TB f"
        using hf unfolding top1_is_path_on_def by (by100 blast)
      have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
      \<comment> \<open>For each s₀ ∈ S, find an open neighborhood of s₀ contained in S.
         Strategy: for s₀ ∈ S, get evenly covered U for f(s₀).
         The point ftilde_1(s₀) = ftilde_2(s₀) ∈ some slice V₀.
         Preimage of V₀ under both lifts contains a neighborhood of s₀.
         On this neighborhood, both lifts lie in V₀ and project to the same f(s),
         so by injectivity of p|V₀, they agree.\<close>
      \<comment> \<open>It suffices to show: for each s₀ ∈ S, there exists N ∈ I_top with s₀ ∈ N ∧ N ⊆ S.\<close>
      have "\<forall>s0\<in>?S. \<exists>N\<in>I_top. s0 \<in> N \<and> N \<subseteq> ?S"
      proof (intro ballI)
        fix s0 assume hs0: "s0 \<in> ?S"
        hence hs0I: "s0 \<in> I_set" and hagree: "ftilde_1 s0 = ftilde_2 s0" by (by100 blast)+
        \<comment> \<open>f(s₀) ∈ B; get evenly covered U.\<close>
        have hfs0: "f s0 \<in> B" using hf_cont hs0I unfolding top1_continuous_map_on_def by (by100 blast)
        obtain U where hbU: "f s0 \<in> U" and hUec: "top1_evenly_covered_on E TE B TB p U"
          using top1_covering_map_on_evenly_covered[OF hcov hfs0] by (by100 blast)
        \<comment> \<open>Get slices.\<close>
        obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
            and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
            and hV_union: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
            and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
                U (subspace_topology B TB U) p"
          using hUec unfolding top1_evenly_covered_on_def by auto
        \<comment> \<open>ftilde_1(s₀) ∈ p⁻¹(U) since p(ftilde_1(s₀)) = f(s₀) ∈ U.\<close>
        have hft1_E: "ftilde_1 s0 \<in> E"
          using hft1_cont hs0I unfolding top1_continuous_map_on_def by (by100 blast)
        have hp_ft1: "p (ftilde_1 s0) \<in> U" using hft1p hs0I hbU by (by100 simp)
        have hft1_mem: "ftilde_1 s0 \<in> {x\<in>E. p x \<in> U}"
          using hft1_E hp_ft1 by (by100 blast)
        \<comment> \<open>Find slice V₀ containing ftilde_1(s₀) = ftilde_2(s₀).\<close>
        obtain V0 where hV0: "V0 \<in> \<V>" and hft1_V0: "ftilde_1 s0 \<in> V0"
          using hft1_mem hV_union by (by100 blast)
        have hft2_V0: "ftilde_2 s0 \<in> V0" using hft1_V0 hagree by simp
        \<comment> \<open>V₀ is open in E.\<close>
        have hV0_open: "V0 \<in> TE" using hV0 hV_open unfolding openin_on_def by (by100 blast)
        \<comment> \<open>Preimages of V₀ under ftilde_1 and ftilde_2 are open in I.\<close>
        have hpre1: "{s\<in>I_set. ftilde_1 s \<in> V0} \<in> I_top"
          using hft1_cont hV0_open unfolding top1_continuous_map_on_def by (by100 blast)
        have hpre2: "{s\<in>I_set. ftilde_2 s \<in> V0} \<in> I_top"
          using hft2_cont hV0_open unfolding top1_continuous_map_on_def by (by100 blast)
        \<comment> \<open>Intersection N = {s∈I. ftilde_1(s) ∈ V₀ ∧ ftilde_2(s) ∈ V₀} is open.\<close>
        let ?N = "{s\<in>I_set. ftilde_1 s \<in> V0} \<inter> {s\<in>I_set. ftilde_2 s \<in> V0}"
        have hN_open: "?N \<in> I_top"
          by (rule topology_inter2[OF hTI hpre1 hpre2])
        have hs0_N: "s0 \<in> ?N" using hs0I hft1_V0 hft2_V0 by (by100 blast)
        \<comment> \<open>On N, both lifts lie in V₀ and project to the same f(s).
           p|V₀ is a homeomorphism, hence injective. So ftilde_1(s) = ftilde_2(s).\<close>
        have hN_sub_S: "?N \<subseteq> ?S"
        proof (intro subsetI)
          fix s assume hs: "s \<in> ?N"
          hence hsI: "s \<in> I_set" and hft1s_V0: "ftilde_1 s \<in> V0" and hft2s_V0: "ftilde_2 s \<in> V0"
            by (by100 blast)+
          have hp_eq: "p (ftilde_1 s) = p (ftilde_2 s)"
          proof -
            have "p (ftilde_1 s) = f s" using hft1p hsI by (by100 blast)
            also have "\<dots> = p (ftilde_2 s)" using hft2p hsI by (by100 simp)
            finally show ?thesis .
          qed
          \<comment> \<open>p|V₀ is injective (from homeomorphism).\<close>
          have hp_inj: "inj_on p V0"
            using hV0 hV_homeo unfolding top1_homeomorphism_on_def bij_betw_def by (by100 blast)
          have "ftilde_1 s = ftilde_2 s"
            using hp_inj hft1s_V0 hft2s_V0 hp_eq unfolding inj_on_def by (by100 blast)
          thus "s \<in> ?S" using hsI by (by100 blast)
        qed
        show "\<exists>N\<in>I_top. s0 \<in> N \<and> N \<subseteq> ?S"
          by (metis (no_types, lifting) hN_open hN_sub_S hs0_N)
      qed
      \<comment> \<open>S is a union of open sets from I_top, hence open.\<close>
      hence hSeq: "?S = \<Union>{N \<in> I_top. N \<subseteq> ?S}" by (by100 blast)
      have "{N \<in> I_top. N \<subseteq> ?S} \<subseteq> I_top" by (by100 blast)
      hence "\<Union>{N \<in> I_top. N \<subseteq> ?S} \<in> I_top"
        using conjunct1[OF conjunct2[OF conjunct2[OF hTI[unfolded is_topology_on_def]]]]
        by (by100 blast)
      thus "?S \<in> I_top" using hSeq by simp
    qed
    show "?S \<subseteq> I_set" by (by100 blast)
  qed
  have hS_closed: "closedin_on I_set I_top ?S"
    unfolding closedin_on_def
  proof (intro conjI)
    show "?S \<subseteq> I_set" by (by100 blast)
  next
    \<comment> \<open>I_set - S = {s\<in>I_set. ftilde_1 s \<noteq> ftilde_2 s} is open.\<close>
    show "I_set - ?S \<in> I_top"
    proof -
      have hft1_cont: "top1_continuous_map_on I_set I_top E TE ftilde_1"
        using hft1 unfolding top1_is_path_on_def by (by100 blast)
      have hft2_cont: "top1_continuous_map_on I_set I_top E TE ftilde_2"
        using hft2 unfolding top1_is_path_on_def by (by100 blast)
      have hTI: "is_topology_on I_set I_top"
        by (rule top1_unit_interval_topology_is_topology_on)
      \<comment> \<open>For each s₀ in I_set - S, get evenly covered U for f(s₀),
         find the disjoint slices containing ftilde_1(s₀) and ftilde_2(s₀),
         preimages of these slices under ftilde_1 and ftilde_2 give open neighborhood of s₀
         on which ftilde_1 and ftilde_2 disagree.\<close>
      have hf_cont: "top1_continuous_map_on I_set I_top B TB f"
        using hf unfolding top1_is_path_on_def by (by100 blast)
      have "\<forall>s0\<in>I_set - ?S. \<exists>N\<in>I_top. s0 \<in> N \<and> N \<subseteq> I_set - ?S"
      proof (intro ballI)
        fix s0 assume hs0: "s0 \<in> I_set - ?S"
        hence hs0I: "s0 \<in> I_set" and hdisagree: "ftilde_1 s0 \<noteq> ftilde_2 s0" by (by100 blast)+
        have hfs0: "f s0 \<in> B" using hf_cont hs0I unfolding top1_continuous_map_on_def by (by100 blast)
        obtain U where hbU: "f s0 \<in> U" and hUec: "top1_evenly_covered_on E TE B TB p U"
          using top1_covering_map_on_evenly_covered[OF hcov hfs0] by (by100 blast)
        obtain \<V> where hV_open: "\<forall>V\<in>\<V>. openin_on E TE V"
            and hV_disj: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
            and hV_union: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
            and hV_homeo: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
                U (subspace_topology B TB U) p"
          using hUec unfolding top1_evenly_covered_on_def by auto
        have hft1_E: "ftilde_1 s0 \<in> E"
          using hft1_cont hs0I unfolding top1_continuous_map_on_def by (by100 blast)
        have hp_ft1: "p (ftilde_1 s0) \<in> U" using hft1p hs0I hbU by (by100 simp)
        have hft1_pU: "ftilde_1 s0 \<in> {x\<in>E. p x \<in> U}" using hft1_E hp_ft1 by (by100 blast)
        have hft2_E: "ftilde_2 s0 \<in> E"
          using hft2_cont hs0I unfolding top1_continuous_map_on_def by (by100 blast)
        have hp_ft2: "p (ftilde_2 s0) \<in> U" using hft2p hs0I hbU by (by100 simp)
        have hft2_pU: "ftilde_2 s0 \<in> {x\<in>E. p x \<in> U}" using hft2_E hp_ft2 by (by100 blast)
        obtain V1 where hV1: "V1 \<in> \<V>" and hft1_V1: "ftilde_1 s0 \<in> V1"
          using hft1_pU hV_union by (by100 blast)
        obtain V2 where hV2: "V2 \<in> \<V>" and hft2_V2: "ftilde_2 s0 \<in> V2"
          using hft2_pU hV_union by (by100 blast)
        \<comment> \<open>V1 \<noteq> V2 since ftilde_1(s0) \<noteq> ftilde_2(s0) and slices disjoint.\<close>
        have hV12_ne: "V1 \<noteq> V2"
        proof
          assume "V1 = V2"
          hence "ftilde_1 s0 \<in> V1 \<and> ftilde_2 s0 \<in> V1" using hft1_V1 hft2_V2 by simp
          hence "p (ftilde_1 s0) = p (ftilde_2 s0) \<longrightarrow> ftilde_1 s0 = ftilde_2 s0"
            using hV1 hV_homeo unfolding top1_homeomorphism_on_def bij_betw_def inj_on_def
            by (by100 blast)
          moreover have "p (ftilde_1 s0) = p (ftilde_2 s0)"
            using hft1p hft2p hs0I by (by100 simp)
          ultimately show False using hdisagree by (by100 blast)
        qed
        have hV1V2_disj: "V1 \<inter> V2 = {}" using hV_disj hV1 hV2 hV12_ne by (by100 blast)
        have hV1_open: "V1 \<in> TE" using hV1 hV_open unfolding openin_on_def by (by100 blast)
        have hV2_open: "V2 \<in> TE" using hV2 hV_open unfolding openin_on_def by (by100 blast)
        have hpre1: "{s\<in>I_set. ftilde_1 s \<in> V1} \<in> I_top"
          using hft1_cont hV1_open unfolding top1_continuous_map_on_def by (by100 blast)
        have hpre2: "{s\<in>I_set. ftilde_2 s \<in> V2} \<in> I_top"
          using hft2_cont hV2_open unfolding top1_continuous_map_on_def by (by100 blast)
        let ?N = "{s\<in>I_set. ftilde_1 s \<in> V1} \<inter> {s\<in>I_set. ftilde_2 s \<in> V2}"
        have hN_open: "?N \<in> I_top" by (rule topology_inter2[OF hTI hpre1 hpre2])
        have hs0_N: "s0 \<in> ?N" using hs0I hft1_V1 hft2_V2 by (by100 blast)
        have hN_sub: "?N \<subseteq> I_set - ?S"
        proof (intro subsetI)
          fix s assume hs: "s \<in> ?N"
          hence hsI: "s \<in> I_set" and hft1s: "ftilde_1 s \<in> V1" and hft2s: "ftilde_2 s \<in> V2"
            by (by100 blast)+
          have "ftilde_1 s \<noteq> ftilde_2 s"
          proof
            assume heq: "ftilde_1 s = ftilde_2 s"
            have "ftilde_2 s \<in> V1" using hft1s heq by simp
            hence "ftilde_2 s \<in> V1 \<inter> V2" using hft2s by (by100 blast)
            thus False using hV1V2_disj by (by100 blast)
          qed
          thus "s \<in> I_set - ?S" using hsI by (by100 blast)
        qed
        show "\<exists>N\<in>I_top. s0 \<in> N \<and> N \<subseteq> I_set - ?S"
          by (metis (no_types, lifting) hN_open hN_sub hs0_N)
      qed
      hence "I_set - ?S = \<Union>{N \<in> I_top. N \<subseteq> I_set - ?S}" by (by100 blast)
      moreover have "{N \<in> I_top. N \<subseteq> I_set - ?S} \<subseteq> I_top" by (by100 blast)
      moreover hence "\<Union>{N \<in> I_top. N \<subseteq> I_set - ?S} \<in> I_top"
        using conjunct1[OF conjunct2[OF conjunct2[OF hTI[unfolded is_topology_on_def]]]]
        by (by100 blast)
      ultimately show ?thesis by simp
    qed
  qed
  have hI_connected: "top1_connected_on I_set I_top"
    by (rule top1_unit_interval_connected)
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have "?S = I_set"
  proof -
    have hS_in_TX: "?S \<in> I_top" using hS_open unfolding openin_on_def by blast
    have hS_sub: "?S \<subseteq> I_set" by blast
    have "?S = {} \<or> ?S = I_set"
      using connected_iff_clopen[OF hTI] hI_connected hS_in_TX hS_closed by blast
    moreover have "?S \<noteq> {}" using hS_nonempty by blast
    ultimately show ?thesis by blast
  qed
  thus ?thesis by blast
qed

text \<open>Helper for Lemma 54.2: extend a continuous lift from a closed region A to A \<union> R,
  where R is a closed rectangle mapping into an evenly covered U, and A \<inter> R is connected.\<close>
lemma homotopy_lifting_rectangle_step:
  fixes A R :: "(real \<times> real) set"
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and hTII: "is_topology_on (I_set \<times> I_set) II_topology"
      and hTE: "is_topology_on E TE"
      and hA_closed: "closedin_on (I_set \<times> I_set) II_topology A"
      and hR_closed: "closedin_on (I_set \<times> I_set) II_topology R"
      and hAR_sub: "A \<union> R \<subseteq> I_set \<times> I_set"
      and hFt_A: "top1_continuous_map_on A (subspace_topology (I_set \<times> I_set) II_topology A) E TE Ftilde_A"
      and hFt_A_lift: "\<forall>x\<in>A. p (Ftilde_A x) = F x"
      and hF_R: "F ` R \<subseteq> U"
      and hUec: "top1_evenly_covered_on E TE B TB p U"
      and hC_conn: "top1_connected_on (A \<inter> R) (subspace_topology (I_set \<times> I_set) II_topology (A \<inter> R))"
      and hC_ne: "A \<inter> R \<noteq> {}"
      and hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology B TB F"
  shows "\<exists>Ftilde. top1_continuous_map_on (A \<union> R) (subspace_topology (I_set \<times> I_set) II_topology (A \<union> R)) E TE Ftilde
      \<and> (\<forall>x\<in>A \<union> R. p (Ftilde x) = F x) \<and> (\<forall>x\<in>A. Ftilde x = Ftilde_A x)"
proof -
  \<comment> \<open>Textbook: Ftilde_A(A\<inter>R) is connected, lies in p\<inverse>(U) = \<Union>slices.
     Connected \<Rightarrow> in one slice V0. Define Ftilde = (p|V0)\<inverse>\<circ>F on R.
     Agrees on A\<inter>R. Pasting gives continuity on A\<union>R.\<close>
  obtain \<V> where hVo: "\<forall>V\<in>\<V>. openin_on E TE V"
      and hVd: "\<forall>V\<in>\<V>. \<forall>V'\<in>\<V>. V \<noteq> V' \<longrightarrow> V \<inter> V' = {}"
      and hVu: "{x\<in>E. p x \<in> U} = \<Union>\<V>"
      and hVh: "\<forall>V\<in>\<V>. top1_homeomorphism_on V (subspace_topology E TE V)
              U (subspace_topology B TB U) p"
    using hUec unfolding top1_evenly_covered_on_def by (by100 auto)
  \<comment> \<open>Ftilde_A maps A\<inter>R into p\<inverse>(U): for x \<in> A\<inter>R, p(Ftilde_A(x)) = F(x) \<in> U.\<close>
  have hFtA_pU: "\<forall>x\<in>A \<inter> R. Ftilde_A x \<in> {x\<in>E. p x \<in> U}"
  proof
    fix x assume hx: "x \<in> A \<inter> R"
    have "p (Ftilde_A x) = F x" using hFt_A_lift hx by (by100 blast)
    moreover have "F x \<in> U" using hF_R hx by (by100 blast)
    moreover have "Ftilde_A x \<in> E"
      using hFt_A hx unfolding top1_continuous_map_on_def by (by100 blast)
    ultimately show "Ftilde_A x \<in> {x\<in>E. p x \<in> U}" by simp
  qed
  \<comment> \<open>Ftilde_A(A\<inter>R) is connected (continuous image of connected set).\<close>
  have hFtA_conn: "top1_connected_on (Ftilde_A ` (A \<inter> R)) (subspace_topology E TE (Ftilde_A ` (A \<inter> R)))"
  proof -
    have hAR_sub_A: "A \<inter> R \<subseteq> A" by (by100 blast)
    have hFtA_AR: "top1_continuous_map_on (A \<inter> R)
        (subspace_topology (I_set \<times> I_set) II_topology (A \<inter> R)) E TE Ftilde_A"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI)
      fix x assume "x \<in> A \<inter> R"
      thus "Ftilde_A x \<in> E" using hFt_A hAR_sub_A unfolding top1_continuous_map_on_def by (by100 blast)
    next
      fix V assume hV: "V \<in> TE"
      have "{x \<in> A \<inter> R. Ftilde_A x \<in> V} = (A \<inter> R) \<inter> {x \<in> A. Ftilde_A x \<in> V}" by (by100 auto)
      moreover have "{x \<in> A. Ftilde_A x \<in> V} \<in> subspace_topology (I_set \<times> I_set) II_topology A"
        using hFt_A hV unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show "{x \<in> A \<inter> R. Ftilde_A x \<in> V} \<in>
          subspace_topology (I_set \<times> I_set) II_topology (A \<inter> R)"
      proof -
        assume h1: "{x \<in> A \<inter> R. Ftilde_A x \<in> V} = (A \<inter> R) \<inter> {x \<in> A. Ftilde_A x \<in> V}"
        assume h2: "{x \<in> A. Ftilde_A x \<in> V} \<in> subspace_topology (I_set \<times> I_set) II_topology A"
        then obtain W where hW: "W \<in> II_topology" and heq: "{x \<in> A. Ftilde_A x \<in> V} = A \<inter> W"
          unfolding subspace_topology_def by (by100 auto)
        have "{x \<in> A \<inter> R. Ftilde_A x \<in> V} = (A \<inter> R) \<inter> W" using h1 heq by (by100 auto)
        thus ?thesis unfolding subspace_topology_def using hW by (by100 blast)
      qed
    qed
    have hAR_II: "A \<inter> R \<subseteq> I_set \<times> I_set" using hAR_sub by (by100 blast)
    have hTAR: "is_topology_on (A \<inter> R) (subspace_topology (I_set \<times> I_set) II_topology (A \<inter> R))"
      by (rule subspace_topology_is_topology_on[OF hTII hAR_II])
    show ?thesis using Theorem_23_5[OF hTAR hTE hC_conn hFtA_AR] .
  qed
  \<comment> \<open>Ftilde_A(A\<inter>R) \<subseteq> \<Union>\<V>, connected, so in one slice V0.\<close>
  have "Ftilde_A ` (A \<inter> R) \<subseteq> \<Union>\<V>"
    using hFtA_pU hVu by (by100 blast)
  then obtain V0 where hV0: "V0 \<in> \<V>" and hFtA_V0: "Ftilde_A ` (A \<inter> R) \<subseteq> V0"
  proof -
    assume hsub: "Ftilde_A ` (A \<inter> R) \<subseteq> \<Union>\<V>"
    obtain x0 where hx0: "x0 \<in> A \<inter> R" using hC_ne by (by100 blast)
    have "Ftilde_A x0 \<in> \<Union>\<V>" using hsub hx0 by (by100 blast)
    then obtain V0 where hV0: "V0 \<in> \<V>" and hx0V0: "Ftilde_A x0 \<in> V0" by (by100 blast)
    have "Ftilde_A ` (A \<inter> R) \<subseteq> V0"
    proof (rule ccontr)
      assume "\<not> Ftilde_A ` (A \<inter> R) \<subseteq> V0"
      then obtain y where hy: "y \<in> A \<inter> R" and hyV0: "Ftilde_A y \<notin> V0" by (by100 blast)
      \<comment> \<open>Ftilde_A y \<in> some other slice V1 \<noteq> V0. Then Ftilde_A(A\<inter>R) meets both V0 and (\<Union>\<V>-V0).
         Both are open in E. V0 \<inter> (\<Union>\<V>-V0) = \<emptyset> (disjoint slices). Ftilde_A(A\<inter>R) connected.
         Connected set meeting two nonempty disjoint open sets covering it \<Rightarrow> contradiction.\<close>
      have "Ftilde_A y \<in> \<Union>\<V>" using hsub hy by (by100 blast)
      have hS_V0: "Ftilde_A ` (A \<inter> R) \<inter> V0 \<noteq> {}" using hx0 hx0V0 by (by100 blast)
      have hS_rest: "Ftilde_A ` (A \<inter> R) \<inter> (\<Union>\<V> - V0) \<noteq> {}"
        using hy hyV0 \<open>Ftilde_A y \<in> \<Union>\<V>\<close> by (by100 blast)
      \<comment> \<open>V0 and (\<Union>\<V> - V0) are open in E (V0 open; complement = \<Union>other slices, open).
         Their intersection is empty (disjoint slices). This contradicts connectivity.\<close>
      have "V0 \<in> TE" using hVo hV0 unfolding openin_on_def by (by100 blast)
      have hrest_open: "\<Union>(\<V> - {V0}) \<in> TE"
      proof -
        have "\<forall>V\<in>\<V> - {V0}. V \<in> TE" using hVo unfolding openin_on_def by (by100 blast)
        hence "\<V> - {V0} \<subseteq> TE" by (by100 blast)
        thus ?thesis using hTE unfolding is_topology_on_def by (by100 blast)
      qed
      have "\<Union>(\<V> - {V0}) = \<Union>\<V> - V0"
        using hVd hV0 by (by100 blast)
      hence hcompl_open: "\<Union>\<V> - V0 \<in> TE" using hrest_open by simp
      have "V0 \<inter> (\<Union>\<V> - V0) = {}" by (by100 blast)
      \<comment> \<open>Ftilde_A(A\<inter>R) \<subseteq> V0 \<union> (\<Union>\<V>-V0) = \<Union>\<V>, meets both, connected \<Rightarrow> contradiction.\<close>
      \<comment> \<open>Ftilde_A(A\<inter>R) is connected, contained in V0 \<union> (\<Union>\<V>-V0), meets both. Contradiction.\<close>
      have himg_sub: "Ftilde_A ` (A \<inter> R) \<subseteq> V0 \<union> (\<Union>\<V> - V0)" using hsub by (by100 blast)
      have himg_E: "Ftilde_A ` (A \<inter> R) \<subseteq> E"
        using hFtA_pU by (by100 blast)
      have himg_top: "is_topology_on (Ftilde_A ` (A \<inter> R))
          (subspace_topology E TE (Ftilde_A ` (A \<inter> R)))"
        by (rule subspace_topology_is_topology_on[OF hTE himg_E])
      \<comment> \<open>V0 \<inter> img and (\<Union>\<V>-V0) \<inter> img are both open in img, nonempty, disjoint, cover img.
         This contradicts connectivity of img.\<close>
      have hV0_img: "V0 \<inter> Ftilde_A ` (A \<inter> R) \<in> subspace_topology E TE (Ftilde_A ` (A \<inter> R))"
        using \<open>V0 \<in> TE\<close> unfolding subspace_topology_def by (by100 blast)
      have hcomp_img: "(\<Union>\<V> - V0) \<inter> Ftilde_A ` (A \<inter> R) \<in> subspace_topology E TE (Ftilde_A ` (A \<inter> R))"
        using hcompl_open unfolding subspace_topology_def by (by100 blast)
      have hdisj: "V0 \<inter> Ftilde_A ` (A \<inter> R) \<inter> ((\<Union>\<V> - V0) \<inter> Ftilde_A ` (A \<inter> R)) = {}"
        by (by100 blast)
      have hcover: "V0 \<inter> Ftilde_A ` (A \<inter> R) \<union> ((\<Union>\<V> - V0) \<inter> Ftilde_A ` (A \<inter> R))
          = Ftilde_A ` (A \<inter> R)" using himg_sub by (by100 blast)
      thus False using hFtA_conn hS_V0 hS_rest hV0_img hcomp_img hdisj hcover
        unfolding top1_connected_on_def by (by100 blast)
    qed
    thus ?thesis using hV0 that by (by100 blast)
  qed
  \<comment> \<open>p|V0 is a homeomorphism V0 \<rightarrow> U, hence bijective.\<close>
  have hbij: "bij_betw p V0 U"
    using hVh hV0 unfolding top1_homeomorphism_on_def by (by100 blast)
  \<comment> \<open>Define extension: Ftilde(x) = Ftilde_A(x) for x \<in> A, inv_into V0 p (F x) for x \<in> R.\<close>
  define Ftilde where "Ftilde x = (if x \<in> A then Ftilde_A x else inv_into V0 p (F x))" for x
  \<comment> \<open>On A\<inter>R: Ftilde_A(x) = inv_into V0 p (F(x)) since Ftilde_A(x) \<in> V0 and p(Ftilde_A(x)) = F(x).\<close>
  have hagree: "\<forall>x\<in>A \<inter> R. Ftilde_A x = inv_into V0 p (F x)"
  proof
    fix x assume hx: "x \<in> A \<inter> R"
    have "Ftilde_A x \<in> V0" using hFtA_V0 hx by (by100 blast)
    moreover have "p (Ftilde_A x) = F x" using hFt_A_lift hx by (by100 blast)
    moreover have "inj_on p V0" using hbij unfolding bij_betw_def by (by100 blast)
    ultimately show "Ftilde_A x = inv_into V0 p (F x)"
      by (metis inv_into_f_f)
  qed
  \<comment> \<open>Ftilde lifts F on A\<union>R.\<close>
  have hFt_lift: "\<forall>x\<in>A \<union> R. p (Ftilde x) = F x"
  proof
    fix x assume hx: "x \<in> A \<union> R"
    show "p (Ftilde x) = F x"
    proof (cases "x \<in> A")
      case True thus ?thesis unfolding Ftilde_def using hFt_A_lift by simp
    next
      case False
      hence "x \<in> R" using hx by simp
      hence "F x \<in> U" using hF_R by (by100 blast)
      hence "F x \<in> p ` V0" using hbij unfolding bij_betw_def by (by100 blast)
      thus ?thesis unfolding Ftilde_def using False
        by (simp add: f_inv_into_f)
    qed
  qed
  \<comment> \<open>Ftilde agrees with Ftilde_A on A.\<close>
  have hFt_agree: "\<forall>x\<in>A. Ftilde x = Ftilde_A x" unfolding Ftilde_def by simp
  \<comment> \<open>Continuity by pasting: Ftilde = Ftilde_A on A (continuous), Ftilde = inv_into V0 p \<circ> F on R (continuous).
     They agree on A\<inter>R. A, R closed. Pasting gives continuity on A\<union>R.\<close>
  have hFt_cont: "top1_continuous_map_on (A \<union> R)
      (subspace_topology (I_set \<times> I_set) II_topology (A \<union> R)) E TE Ftilde"
  proof -
    have hTAR_: "is_topology_on (A \<union> R) (subspace_topology (I_set \<times> I_set) II_topology (A \<union> R))"
      by (rule subspace_topology_is_topology_on[OF hTII hAR_sub])
    have hA_cl_AR: "closedin_on (A \<union> R) (subspace_topology (I_set \<times> I_set) II_topology (A \<union> R)) A"
    proof -
      have hAsub: "A \<subseteq> A \<union> R" by (by100 blast)
      have hcomp: "(A \<union> R) - A = R - A" by (by100 blast)
      have "(I_set \<times> I_set) - A \<in> II_topology"
        using hA_closed unfolding closedin_on_def by (by100 blast)
      hence "(A \<union> R) \<inter> ((I_set \<times> I_set) - A) \<in> subspace_topology (I_set \<times> I_set) II_topology (A \<union> R)"
        unfolding subspace_topology_def by (by100 blast)
      moreover have "(A \<union> R) \<inter> ((I_set \<times> I_set) - A) = (A \<union> R) - A"
        using hAR_sub by (by100 blast)
      ultimately have "(A \<union> R) - A \<in> subspace_topology (I_set \<times> I_set) II_topology (A \<union> R)" by simp
      thus ?thesis unfolding closedin_on_def using hAsub by (by100 blast)
    qed
    have hR_cl_AR: "closedin_on (A \<union> R) (subspace_topology (I_set \<times> I_set) II_topology (A \<union> R)) R"
    proof -
      have hRsub: "R \<subseteq> A \<union> R" by (by100 blast)
      have "(I_set \<times> I_set) - R \<in> II_topology"
        using hR_closed unfolding closedin_on_def by (by100 blast)
      hence "(A \<union> R) \<inter> ((I_set \<times> I_set) - R) \<in> subspace_topology (I_set \<times> I_set) II_topology (A \<union> R)"
        unfolding subspace_topology_def by (by100 blast)
      moreover have "(A \<union> R) \<inter> ((I_set \<times> I_set) - R) = (A \<union> R) - R"
        using hAR_sub by (by100 blast)
      ultimately have "(A \<union> R) - R \<in> subspace_topology (I_set \<times> I_set) II_topology (A \<union> R)" by simp
      thus ?thesis unfolding closedin_on_def using hRsub by (by100 blast)
    qed
    have hAR_union: "A \<union> R = A \<union> R" by simp
    have hrange: "\<forall>x\<in>A \<union> R. Ftilde x \<in> E"
    proof
      fix x assume "x \<in> A \<union> R"
      show "Ftilde x \<in> E"
      proof (cases "x \<in> A")
        case True
        have "Ftilde x = Ftilde_A x" unfolding Ftilde_def using True by simp
        moreover have "Ftilde_A x \<in> E" using hFt_A True unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show ?thesis by simp
      next
        case False hence "x \<in> R" using \<open>x \<in> A \<union> R\<close> by simp
        hence "F x \<in> U" using hF_R by (by100 blast)
        hence "F x \<in> p ` V0" using hbij unfolding bij_betw_def by (by100 blast)
        hence "inv_into V0 p (F x) \<in> V0" by (rule inv_into_into)
        moreover have "V0 \<subseteq> E" using hVo hV0 unfolding openin_on_def by (by100 blast)
        ultimately show ?thesis unfolding Ftilde_def using False by (by100 auto)
      qed
    qed
    have hFt_on_A: "top1_continuous_map_on A
        (subspace_topology (A \<union> R) (subspace_topology (I_set \<times> I_set) II_topology (A \<union> R)) A) E TE Ftilde"
    proof -
      have heq: "\<forall>x\<in>A. Ftilde x = Ftilde_A x" using hFt_agree .
      have hTsub: "subspace_topology (A \<union> R) (subspace_topology (I_set \<times> I_set) II_topology (A \<union> R)) A
          = subspace_topology (I_set \<times> I_set) II_topology A"
        by (rule subspace_topology_trans) (by100 blast)
      show ?thesis unfolding hTsub top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x assume hx: "x \<in> A"
        have "Ftilde x = Ftilde_A x" using heq hx by (by100 blast)
        moreover have "Ftilde_A x \<in> E" using hFt_A hx unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "Ftilde x \<in> E" by simp
      next
        fix V assume hV: "V \<in> TE"
        have "{x\<in>A. Ftilde x \<in> V} = {x\<in>A. Ftilde_A x \<in> V}" using heq by auto
        also have "\<dots> \<in> subspace_topology (I_set \<times> I_set) II_topology A"
          using hFt_A hV unfolding top1_continuous_map_on_def by (by100 blast)
        finally show "{x\<in>A. Ftilde x \<in> V} \<in> subspace_topology (I_set \<times> I_set) II_topology A" .
      qed
    qed
    have hFt_on_R: "top1_continuous_map_on R
        (subspace_topology (A \<union> R) (subspace_topology (I_set \<times> I_set) II_topology (A \<union> R)) R) E TE Ftilde"
    proof -
      \<comment> \<open>On R: Ftilde(x) = if x\<in>A then Ftilde_A x else inv_into V0 p (F x).
         But on R-A: Ftilde = inv_into V0 p \<circ> F. On A\<inter>R: also = inv_into V0 p \<circ> F (by hagree).
         So on all of R: Ftilde = inv_into V0 p \<circ> F. This is continuous.\<close>
      have hR_eq: "\<forall>x\<in>R. Ftilde x = inv_into V0 p (F x)"
      proof
        fix x assume hx: "x \<in> R"
        show "Ftilde x = inv_into V0 p (F x)"
        proof (cases "x \<in> A")
          case True thus ?thesis unfolding Ftilde_def using hagree True hx by simp
        next
          case False thus ?thesis unfolding Ftilde_def by simp
        qed
      qed
      have hTsub: "subspace_topology (A \<union> R) (subspace_topology (I_set \<times> I_set) II_topology (A \<union> R)) R
          = subspace_topology (I_set \<times> I_set) II_topology R"
        by (rule subspace_topology_trans) (by100 blast)
      \<comment> \<open>inv_into V0 p \<circ> F is continuous on R: composition of continuous functions.\<close>
      \<comment> \<open>inv_into V0 p continuous U \<rightarrow> V0 (from homeomorphism).\<close>
      have hinv_cont: "top1_continuous_map_on U (subspace_topology B TB U)
          V0 (subspace_topology E TE V0) (inv_into V0 p)"
        using hVh hV0 unfolding top1_homeomorphism_on_def by (by100 blast)
      \<comment> \<open>F restricted to R is continuous R \<rightarrow> U.\<close>
      have hF_R_cont: "top1_continuous_map_on R (subspace_topology (I_set \<times> I_set) II_topology R)
          U (subspace_topology B TB U) F"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x assume "x \<in> R" thus "F x \<in> U" using hF_R by (by100 blast)
      next
        fix V assume "V \<in> subspace_topology B TB U"
        then obtain W where hW: "W \<in> TB" and hVeq: "V = U \<inter> W"
          unfolding subspace_topology_def by (by100 auto)
        have hR_II: "R \<subseteq> I_set \<times> I_set" using hAR_sub by (by100 blast)
        have "{x\<in>R. F x \<in> V} = R \<inter> {x\<in>I_set \<times> I_set. F x \<in> W}"
        proof -
          have "\<And>x. x \<in> R \<Longrightarrow> F x \<in> U" using hF_R by (by100 blast)
          thus ?thesis unfolding hVeq using hR_II by auto
        qed
        moreover have "{x\<in>I_set \<times> I_set. F x \<in> W} \<in> II_topology"
          using hF_cont hW unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "{x\<in>R. F x \<in> V} \<in> subspace_topology (I_set \<times> I_set) II_topology R"
          unfolding subspace_topology_def by (by100 blast)
      qed
      \<comment> \<open>Compose: inv_into V0 p \<circ> F continuous R \<rightarrow> V0 \<subseteq> E.\<close>
      have hcomp: "top1_continuous_map_on R (subspace_topology (I_set \<times> I_set) II_topology R)
          V0 (subspace_topology E TE V0) (inv_into V0 p \<circ> F)"
        by (rule top1_continuous_map_on_comp[OF hF_R_cont hinv_cont])
      \<comment> \<open>Lift from V0-topology to E-topology.\<close>
      have hV0_E: "V0 \<subseteq> E" using hVo hV0 unfolding openin_on_def by (by100 blast)
      show ?thesis unfolding hTsub top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x assume "x \<in> R"
        have "Ftilde x = inv_into V0 p (F x)" using hR_eq \<open>x \<in> R\<close> by (by100 blast)
        moreover have "(inv_into V0 p \<circ> F) x \<in> V0"
          using hcomp \<open>x \<in> R\<close> unfolding top1_continuous_map_on_def by (by100 blast)
        ultimately show "Ftilde x \<in> E" using hV0_E by (by100 auto)
      next
        fix V assume hV: "V \<in> TE"
        have hVV0: "V \<inter> V0 \<in> subspace_topology E TE V0"
          unfolding subspace_topology_def using hV by (by100 blast)
        have heq: "{x\<in>R. Ftilde x \<in> V} = {x\<in>R. (inv_into V0 p \<circ> F) x \<in> V \<inter> V0}"
        proof (rule set_eqI, simp add: comp_def)
          fix x show "(x \<in> R \<and> Ftilde x \<in> V) = (x \<in> R \<and> inv_into V0 p (F x) \<in> V \<and> inv_into V0 p (F x) \<in> V0)"
          proof (cases "x \<in> R")
            case False thus ?thesis by simp
          next
            case True
            have "Ftilde x = inv_into V0 p (F x)" using hR_eq True by (by100 blast)
            moreover have "inv_into V0 p (F x) \<in> V0"
              using hcomp True unfolding top1_continuous_map_on_def comp_def by (by100 blast)
            ultimately show ?thesis by simp
          qed
        qed
        have "{x\<in>R. (inv_into V0 p \<circ> F) x \<in> V \<inter> V0} \<in> subspace_topology (I_set \<times> I_set) II_topology R"
          using hcomp hVV0 unfolding top1_continuous_map_on_def by (by100 blast)
        thus "{x\<in>R. Ftilde x \<in> V} \<in> subspace_topology (I_set \<times> I_set) II_topology R"
          using heq by simp
      qed
    qed
    show ?thesis
      by (rule pasting_lemma_two_closed[OF hTAR_ hTE hA_cl_AR hR_cl_AR hAR_union hrange
          hFt_on_A hFt_on_R])
  qed
  show ?thesis using hFt_cont hFt_lift hFt_agree by (by100 blast)
qed

\<comment> \<open>Helper: a closed sub-interval of I is closed in the subspace topology.\<close>
lemma closedin_I_sub_interval:
  fixes a b :: real
  assumes "a \<le> b"
  shows "closedin_on I_set I_top {s\<in>I_set. a \<le> s \<and> s \<le> b}"
  unfolding closedin_on_def
proof (intro conjI)
  show "{s\<in>I_set. a \<le> s \<and> s \<le> b} \<subseteq> I_set" by (by100 blast)
  have heq: "I_set - {s\<in>I_set. a \<le> s \<and> s \<le> b} = I_set \<inter> ({s :: real. s < a} \<union> {s. s > b})"
    by (by100 auto)
  have hopen: "open ({s :: real. s < a} \<union> {s. s > b})"
  proof -
    have "open {s :: real. s < a}" using open_lessThan[of a] unfolding lessThan_def by simp
    moreover have "open {s :: real. s > b}" using open_greaterThan[of b] unfolding greaterThan_def by simp
    ultimately show ?thesis by (rule open_Un)
  qed
  show "I_set - {s\<in>I_set. a \<le> s \<and> s \<le> b} \<in> I_top"
    unfolding heq top1_unit_interval_topology_def subspace_topology_def
    using hopen unfolding top1_open_sets_def by (by100 blast)
qed

\<comment> \<open>Helper: a closed rectangle is closed in II_topology.\<close>
lemma closedin_II_rectangle:
  fixes a b c d :: real
  assumes hab: "a \<le> b" and hcd: "c \<le> d"
  shows "closedin_on (I_set \<times> I_set) II_topology
    ({s\<in>I_set. a \<le> s \<and> s \<le> b} \<times> {t\<in>I_set. c \<le> t \<and> t \<le> d})"
  unfolding closedin_on_def
proof (intro conjI)
  let ?S = "{s\<in>I_set. a \<le> s \<and> s \<le> b}" and ?T = "{t\<in>I_set. c \<le> t \<and> t \<le> d}"
  show "?S \<times> ?T \<subseteq> I_set \<times> I_set" by (by100 blast)
  have hS_cl: "closedin_on I_set I_top ?S" by (rule closedin_I_sub_interval[OF hab])
  have hT_cl: "closedin_on I_set I_top ?T" by (rule closedin_I_sub_interval[OF hcd])
  have hS_open: "I_set - ?S \<in> I_top" using hS_cl unfolding closedin_on_def by (by100 blast)
  have hT_open: "I_set - ?T \<in> I_top" using hT_cl unfolding closedin_on_def by (by100 blast)
  have hI_open: "I_set \<in> I_top"
    using top1_unit_interval_topology_is_topology_on unfolding is_topology_on_def by (by100 blast)
  have heq: "I_set \<times> I_set - ?S \<times> ?T = ((I_set - ?S) \<times> I_set) \<union> (I_set \<times> (I_set - ?T))"
    by (by100 blast)
  have h1: "(I_set - ?S) \<times> I_set \<in> II_topology"
    unfolding II_topology_def by (rule product_rect_open[OF hS_open hI_open])
  have h2: "I_set \<times> (I_set - ?T) \<in> II_topology"
    unfolding II_topology_def by (rule product_rect_open[OF hI_open hT_open])
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
    unfolding II_topology_def
    by (rule product_topology_on_is_topology_on[OF
        top1_unit_interval_topology_is_topology_on
        top1_unit_interval_topology_is_topology_on])
  have hunion: "\<forall>F\<subseteq>II_topology. \<Union>F \<in> II_topology"
    using hTII unfolding is_topology_on_def by (by100 blast)
  have "{(I_set - ?S) \<times> I_set, I_set \<times> (I_set - ?T)} \<subseteq> II_topology"
    using h1 h2 by (by100 blast)
  hence "(I_set - ?S) \<times> I_set \<union> (I_set \<times> (I_set - ?T)) \<in> II_topology"
    using hunion[rule_format, of "{(I_set - ?S) \<times> I_set, I_set \<times> (I_set - ?T)}"]
    by simp
  thus "I_set \<times> I_set - ?S \<times> ?T \<in> II_topology" unfolding heq .
qed

\<comment> \<open>Interval pigeonhole: a point in [f(0), f(m)] lies in some [f(i), f(i+1)].\<close>
lemma increasing_interval_cover:
  fixes f :: "nat \<Rightarrow> real" and x :: real and m :: nat
  assumes hm: "m \<ge> 1"
      and hf0: "f 0 \<le> x" and hfm: "x \<le> f m"
      and hinc: "\<forall>i<m. f i < f (Suc i)"
  shows "\<exists>i<m. f i \<le> x \<and> x \<le> f (Suc i)"
  using hm hfm hinc
proof (induction m)
  case 0 thus ?case by simp
next
  case (Suc m')
  \<comment> \<open>Suc.prems: (1) Suc m' \<ge> 1, (2) x \<le> f (Suc m'), (3) \<forall>i<Suc m'. f i < f (Suc i).\<close>
  have hinc': "\<forall>i<Suc m'. f i < f (Suc i)" using Suc.prems(3) .
  show ?case
  proof (cases "x \<le> f m'")
    case True
    show ?thesis
    proof (cases "m' = 0")
      case True
      have "f 0 < f (Suc 0)" using hinc' by (by100 auto)
      thus ?thesis using hf0 \<open>x \<le> f m'\<close> True by (by100 auto)
    next
      case False
      hence "m' \<ge> 1" by simp
      moreover have "\<forall>i<m'. f i < f (Suc i)" using hinc' by (by100 auto)
      ultimately obtain i where "i < m'" "f i \<le> x" "x \<le> f (Suc i)"
        using Suc.IH hf0 True by (by100 blast)
      hence "i < Suc m'" by simp
      thus ?thesis using \<open>f i \<le> x\<close> \<open>x \<le> f (Suc i)\<close> by (by100 blast)
    qed
  next
    case False
    hence "f m' \<le> x" by simp
    thus ?thesis using Suc.prems(2) by (by100 auto)
  qed
qed

\<comment> \<open>Helper: given per-s-piece t-subdivisions, derive a single m \<times> n grid.
   The t-subdivision is the common refinement (sorted union of all t-boundary points).\<close>
lemma grid_from_per_piece_subdivisions:
  fixes P :: "nat \<Rightarrow> (real set) \<Rightarrow> (real set) \<Rightarrow> bool"
  assumes hns: "ns \<ge> 1"
      and hs0: "sub_s 0 = (0::real)" and hsn: "sub_s ns = 1"
      and hsinc: "\<forall>i<ns. sub_s i < sub_s (Suc i)"
      and hstrip: "\<forall>i<ns. \<exists>nt\<ge>1. \<exists>sub_t :: nat \<Rightarrow> real. sub_t 0 = 0 \<and> sub_t nt = 1
          \<and> (\<forall>j<nt. sub_t j < sub_t (Suc j))
          \<and> (\<forall>j<nt. P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                          {t. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)})"
      and hP_mono: "\<forall>i S T T'. T' \<subseteq> T \<longrightarrow> P i S T \<longrightarrow> P i S T'"
  shows "\<exists>n\<ge>1. \<exists>sub_t' :: nat \<Rightarrow> real.
      sub_t' 0 = 0 \<and> sub_t' n = 1
      \<and> (\<forall>j<n. sub_t' j < sub_t' (Suc j))
      \<and> (\<forall>i<ns. \<forall>j<n. P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                              {t. sub_t' j \<le> t \<and> t \<le> sub_t' (Suc j)})"
proof -
  \<comment> \<open>Extract per-s-piece t-subdivisions via choice.\<close>
  obtain nt_f sub_t_f where
      hnt_f: "\<forall>i<ns. nt_f i \<ge> 1"
      and ht0_f: "\<forall>i<ns. sub_t_f i 0 = (0::real)"
      and htn_f: "\<forall>i<ns. sub_t_f i (nt_f i) = 1"
      and htinc_f: "\<forall>i<ns. \<forall>j<nt_f i. sub_t_f i j < sub_t_f i (Suc j)"
      and hcov_f: "\<forall>i<ns. \<forall>j<nt_f i. P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                          {t. sub_t_f i j \<le> t \<and> t \<le> sub_t_f i (Suc j)}"
  proof -
    define pick where "pick i = (SOME p :: nat \<times> (nat \<Rightarrow> real).
        fst p \<ge> 1 \<and> snd p 0 = 0 \<and> snd p (fst p) = 1
        \<and> (\<forall>j<fst p. snd p j < snd p (Suc j))
        \<and> (\<forall>j<fst p. P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                          {t. snd p j \<le> t \<and> t \<le> snd p (Suc j)}))" for i
    have hpick: "\<forall>i<ns. fst (pick i) \<ge> 1 \<and> snd (pick i) 0 = 0
        \<and> snd (pick i) (fst (pick i)) = 1
        \<and> (\<forall>j<fst (pick i). snd (pick i) j < snd (pick i) (Suc j))
        \<and> (\<forall>j<fst (pick i). P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                                  {t. snd (pick i) j \<le> t \<and> t \<le> snd (pick i) (Suc j)})"
    proof (intro allI impI)
      fix i assume hi: "i < ns"
      from hstrip[rule_format, OF hi] obtain nt st where
          "nt \<ge> 1" "st 0 = (0::real)" "st nt = 1"
          "\<forall>j<nt. st j < st (Suc j)"
          "\<forall>j<nt. P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)} {t. st j \<le> t \<and> t \<le> st (Suc j)}"
        by auto
      hence "\<exists>p :: nat \<times> (nat \<Rightarrow> real). fst p \<ge> 1 \<and> snd p 0 = 0 \<and> snd p (fst p) = 1
          \<and> (\<forall>j<fst p. snd p j < snd p (Suc j))
          \<and> (\<forall>j<fst p. P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                              {t. snd p j \<le> t \<and> t \<le> snd p (Suc j)})"
        by (intro exI[of _ "(nt, st)"]) simp
      thus "fst (pick i) \<ge> 1 \<and> snd (pick i) 0 = 0
          \<and> snd (pick i) (fst (pick i)) = 1
          \<and> (\<forall>j<fst (pick i). snd (pick i) j < snd (pick i) (Suc j))
          \<and> (\<forall>j<fst (pick i). P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                                      {t. snd (pick i) j \<le> t \<and> t \<le> snd (pick i) (Suc j)})"
        unfolding pick_def by (rule someI_ex)
    qed
    define nt_f where "nt_f i = fst (pick i)" for i
    define sub_t_f where "sub_t_f i = snd (pick i)" for i
    show ?thesis
      using hpick unfolding nt_f_def sub_t_f_def
      by (intro that[where nt_f=nt_f and sub_t_f=sub_t_f]) (auto simp: nt_f_def sub_t_f_def)
  qed
  \<comment> \<open>Collect all t-boundary points.\<close>
  define T_pts where "T_pts = (\<Union>i\<in>{0..<ns}. sub_t_f i ` {0..nt_f i})"
  have hT_fin: "finite T_pts" unfolding T_pts_def by simp
  have h0_T: "0 \<in> T_pts"
  proof -
    have "0 < ns" using hns by simp
    have "sub_t_f 0 0 \<in> T_pts"
      unfolding T_pts_def using \<open>0 < ns\<close> by force
    thus ?thesis using ht0_f[rule_format, OF \<open>0 < ns\<close>] by simp
  qed
  have h1_T: "1 \<in> T_pts"
  proof -
    have "0 < ns" using hns by simp
    have "sub_t_f 0 (nt_f 0) \<in> T_pts"
      unfolding T_pts_def using \<open>0 < ns\<close> by force
    thus ?thesis using htn_f[rule_format, OF \<open>0 < ns\<close>] by simp
  qed
  \<comment> \<open>Sort T_pts into a list.\<close>
  define tlist where "tlist = sorted_list_of_set T_pts"
  define n where "n = length tlist - 1"
  define sub_t' where "sub_t' j = (if j < length tlist then tlist ! j else 1)" for j
  \<comment> \<open>Properties of sorted_list_of_set.\<close>
  have hset: "set tlist = T_pts" unfolding tlist_def using hT_fin
    by (rule sorted_list_of_set(1))
  have hsort: "sorted tlist" unfolding tlist_def
    by (rule sorted_list_of_set(2))
  have hdist: "distinct tlist" unfolding tlist_def
    by (rule sorted_list_of_set(3))
  have hne: "tlist \<noteq> []" using h0_T hset by (by100 auto)
  have hlen: "length tlist \<ge> 2"
  proof -
    have "0 \<noteq> (1::real)" by simp
    hence "card {0::real, 1} = 2" by simp
    have "{0::real, 1} \<subseteq> T_pts" using h0_T h1_T by (by100 blast)
    hence "card T_pts \<ge> 2" using \<open>card {0::real, 1} = 2\<close> hT_fin
      by (metis card_mono)
    thus ?thesis using hset hdist
      by (metis distinct_card)
  qed
  have hn_pos: "n \<ge> 1" using hlen unfolding n_def by simp
  \<comment> \<open>First element is 0, last is 1.\<close>
  have hT_01: "\<forall>t\<in>T_pts. 0 \<le> t \<and> t \<le> 1"
  proof (intro ballI conjI)
    fix t assume ht: "t \<in> T_pts"
    then obtain i j where hi: "i < ns" and hj: "j \<le> nt_f i" and heq: "t = sub_t_f i j"
      unfolding T_pts_def by force
    have hfj_mono: "\<forall>a b. a \<le> b \<and> b \<le> nt_f i \<longrightarrow> sub_t_f i a \<le> sub_t_f i b"
    proof (intro allI impI)
      fix a b :: nat assume hab: "a \<le> b \<and> b \<le> nt_f i"
      show "sub_t_f i a \<le> sub_t_f i b" using hab
      proof (induction "b - a" arbitrary: b)
        case 0 thus ?case by simp
      next
        case (Suc d)
        hence "b > 0" by simp
        then obtain b' where hb': "b = Suc b'" using gr0_implies_Suc by (by100 blast)
        have "a \<le> b'" using Suc.hyps(2) hb' by simp
        have "b' \<le> nt_f i" using Suc.prems hb' by simp
        have "d = b' - a" using Suc.hyps(2) hb' by simp
        have "sub_t_f i a \<le> sub_t_f i b'"
          using Suc.hyps(1)[OF \<open>d = b' - a\<close>] \<open>a \<le> b'\<close> \<open>b' \<le> nt_f i\<close> by simp
        have "b' < nt_f i" using \<open>b' \<le> nt_f i\<close> hb' Suc.prems by simp
        have "sub_t_f i b' \<le> sub_t_f i (Suc b')"
          using htinc_f[rule_format, OF hi \<open>b' < nt_f i\<close>] by simp
        show ?case using \<open>sub_t_f i a \<le> sub_t_f i b'\<close> \<open>sub_t_f i b' \<le> sub_t_f i (Suc b')\<close>
          hb' by simp
      qed
    qed
    show "0 \<le> t" using hfj_mono[rule_format, of 0 j] hj ht0_f[rule_format, OF hi] heq by simp
    show "t \<le> 1" using hfj_mono[rule_format, of j "nt_f i"] hj htn_f[rule_format, OF hi] heq by simp
  qed
  have hsub0: "sub_t' 0 = 0"
  proof -
    have "hd tlist \<in> set tlist" using hne by (rule hd_in_set)
    hence "hd tlist \<in> T_pts" using hset by simp
    hence "hd tlist \<ge> 0" using hT_01 by (by100 blast)
    moreover have "hd tlist \<le> 0"
    proof -
      have "0 \<in> set tlist" using h0_T hset by simp
      then obtain idx where "idx < length tlist" "tlist ! idx = 0" by (metis in_set_conv_nth)
      have "tlist ! 0 \<le> tlist ! idx"
        using sorted_nth_mono[OF hsort, of 0 idx] \<open>idx < length tlist\<close> by simp
      thus ?thesis using \<open>tlist ! idx = 0\<close> hne by (simp add: hd_conv_nth)
    qed
    ultimately have "hd tlist = 0" by simp
    thus ?thesis unfolding sub_t'_def using hne by (simp add: hd_conv_nth)
  qed
  have hsubn: "sub_t' n = 1"
  proof -
    have "last tlist \<in> set tlist" using hne by (rule last_in_set)
    hence "last tlist \<in> T_pts" using hset by simp
    hence "last tlist \<le> 1" using hT_01 by (by100 blast)
    moreover have "last tlist \<ge> 1"
    proof -
      have "1 \<in> set tlist" using h1_T hset by simp
      then obtain idx where "idx < length tlist" "tlist ! idx = 1" by (metis in_set_conv_nth)
      have "tlist ! idx \<le> tlist ! (length tlist - 1)"
        using sorted_nth_mono[OF hsort, of idx "length tlist - 1"] \<open>idx < length tlist\<close> by simp
      thus ?thesis using \<open>tlist ! idx = 1\<close> hne by (simp add: last_conv_nth)
    qed
    ultimately have "last tlist = 1" by simp
    thus ?thesis unfolding sub_t'_def n_def
      using hne by (simp add: last_conv_nth)
  qed
  \<comment> \<open>Strictly increasing.\<close>
  have hsinc: "\<forall>j<n. sub_t' j < sub_t' (Suc j)"
  proof (intro allI impI)
    fix j assume hj: "j < n"
    have hj_len: "j < length tlist - 1" using hj unfolding n_def .
    hence hj1_len: "Suc j < length tlist" by simp
    have hj_len2: "j < length tlist" using hj_len hlen by simp
    have "sub_t' j = tlist ! j" unfolding sub_t'_def using hj_len2 by simp
    moreover have "sub_t' (Suc j) = tlist ! Suc j" unfolding sub_t'_def using hj1_len by simp
    moreover have "tlist ! j < tlist ! Suc j"
    proof -
      have "tlist ! j \<le> tlist ! Suc j"
        using sorted_nth_mono[OF hsort, of j "Suc j"] hj1_len by simp
      moreover have "tlist ! j \<noteq> tlist ! Suc j"
        using nth_eq_iff_index_eq[OF hdist] hj_len hj1_len by (by100 auto)
      ultimately show ?thesis by simp
    qed
    ultimately show "sub_t' j < sub_t' (Suc j)" by simp
  qed
  \<comment> \<open>Each piece [sub_t' k, sub_t'(k+1)] is contained in some piece of every subdivision.\<close>
  have hrefines: "\<forall>i<ns. \<forall>k<n. \<exists>j<nt_f i. {t. sub_t' k \<le> t \<and> t \<le> sub_t' (Suc k)}
      \<subseteq> {t. sub_t_f i j \<le> t \<and> t \<le> sub_t_f i (Suc j)}"
  proof (intro allI impI)
    fix i k assume hi: "i < ns" and hk: "k < n"
    have hk_len: "k < length tlist" using hk hlen unfolding n_def by simp
    have hSk_len: "Suc k < length tlist" using hk unfolding n_def by simp
    have hk2: "k < length tlist - 1" using hk unfolding n_def .
    \<comment> \<open>sub_t' k \<in> [0,1].\<close>
    have hsk_T: "sub_t' k \<in> T_pts"
    proof -
      have "sub_t' k = tlist ! k" unfolding sub_t'_def using hk_len by simp
      hence "sub_t' k \<in> set tlist" using hk_len by simp
      thus ?thesis using hset by simp
    qed
    have hsk_01: "0 \<le> sub_t' k \<and> sub_t' k \<le> 1" using hT_01 hsk_T by (by100 blast)
    \<comment> \<open>Find piece j of subdivision i containing sub_t' k.\<close>
    have hnt: "nt_f i \<ge> 1" using hnt_f[rule_format, OF hi] .
    have hinc_i: "\<forall>j'<nt_f i. sub_t_f i j' < sub_t_f i (Suc j')"
      using htinc_f hi by auto
    have h1: "sub_t_f i 0 \<le> sub_t' k" using ht0_f[rule_format, OF hi] hsk_01 by simp
    have h2: "sub_t' k \<le> sub_t_f i (nt_f i)" using htn_f[rule_format, OF hi] hsk_01 by simp
    obtain j where hj: "j < nt_f i"
        and hj_le: "sub_t_f i j \<le> sub_t' k"
        and hj_ge: "sub_t' k \<le> sub_t_f i (Suc j)"
    proof -
      from increasing_interval_cover[OF hnt h1 h2 hinc_i]
      obtain j' where "j' < nt_f i" "sub_t_f i j' \<le> sub_t' k" "sub_t' k \<le> sub_t_f i (Suc j')"
        by blast
      thus ?thesis using that by blast
    qed
    \<comment> \<open>Show: \<exists>j' with [sub_t' k, sub_t'(k+1)] \<subseteq> [sub_t_f i j', sub_t_f i (j'+1)].
       Case 1: sub_t' k < sub_t_f i (j+1). Use j' = j.
       Case 2: sub_t' k = sub_t_f i (j+1). Use j' = j+1 (if it exists).\<close>
    show "\<exists>j<nt_f i. {t. sub_t' k \<le> t \<and> t \<le> sub_t' (Suc k)}
        \<subseteq> {t. sub_t_f i j \<le> t \<and> t \<le> sub_t_f i (Suc j)}"
    proof (cases "sub_t' k < sub_t_f i (Suc j)")
      case True
      \<comment> \<open>sub_t_f i (j+1) > sub_t' k = tlist!k. So its position m > k, i.e., m \<ge> k+1.\<close>
      have hSj_T: "sub_t_f i (Suc j) \<in> T_pts"
        unfolding T_pts_def using hi hj by force
      hence "sub_t_f i (Suc j) \<in> set tlist" using hset by simp
      then obtain m where hm_len: "m < length tlist"
          and hm_eq: "tlist ! m = sub_t_f i (Suc j)" by (metis in_set_conv_nth)
      have "m > k"
      proof (rule ccontr)
        assume "\<not> m > k" hence "m \<le> k" by simp
        have "tlist ! m \<le> tlist ! k"
          using sorted_nth_mono[OF hsort, of m k] \<open>m \<le> k\<close> hk_len by simp
        hence "sub_t_f i (Suc j) \<le> sub_t' k"
          using hm_eq unfolding sub_t'_def using hk_len by simp
        thus False using True by simp
      qed
      hence "m \<ge> Suc k" by simp
      hence "tlist ! (Suc k) \<le> tlist ! m"
        using sorted_nth_mono[OF hsort, of "Suc k" m] hm_len by simp
      hence "sub_t' (Suc k) \<le> sub_t_f i (Suc j)"
        using hm_eq unfolding sub_t'_def using hSk_len by simp
      thus ?thesis using hj hj_le by (intro exI[of _ j]) auto
    next
      case False
      hence heq: "sub_t' k = sub_t_f i (Suc j)" using hj_ge by simp
      \<comment> \<open>sub_t' k = sub_t_f i (j+1). If j+1 = nt_f i, then sub_t' k = 1, contradiction.\<close>
      have "Suc j < nt_f i"
      proof (rule ccontr)
        assume "\<not> Suc j < nt_f i"
        hence "Suc j = nt_f i" using hj by simp
        hence "sub_t' k = 1" using heq htn_f[rule_format, OF hi] by simp
        have "sub_t' k < sub_t' (Suc k)" using hsinc hk by (by100 blast)
        hence "1 < sub_t' (Suc k)" using \<open>sub_t' k = 1\<close> by simp
        have "sub_t' (Suc k) \<in> T_pts"
        proof -
          have "sub_t' (Suc k) = tlist ! (Suc k)" unfolding sub_t'_def using hSk_len by simp
          hence "sub_t' (Suc k) \<in> set tlist" using hSk_len by simp
          thus ?thesis using hset by simp
        qed
        hence "sub_t' (Suc k) \<le> 1" using hT_01 by (by100 blast)
        thus False using \<open>1 < sub_t' (Suc k)\<close> by simp
      qed
      \<comment> \<open>Use piece j+1. Left: sub_t_f i (j+1) = sub_t' k. Right: need sub_t'(k+1) \<le> sub_t_f i (j+2).\<close>
      have hSj_lt: "Suc j < nt_f i" by (rule \<open>Suc j < nt_f i\<close>)
      have hSSj_T: "sub_t_f i (Suc (Suc j)) \<in> T_pts"
        unfolding T_pts_def using hi hSj_lt by force
      hence "sub_t_f i (Suc (Suc j)) \<in> set tlist" using hset by simp
      then obtain m2 where hm2_len: "m2 < length tlist"
          and hm2_eq: "tlist ! m2 = sub_t_f i (Suc (Suc j))" by (metis in_set_conv_nth)
      have "sub_t_f i (Suc (Suc j)) > sub_t_f i (Suc j)"
        using htinc_f[rule_format, OF hi hSj_lt] .
      hence "sub_t_f i (Suc (Suc j)) > sub_t' k" using heq by simp
      hence htm2_gt: "tlist ! m2 > tlist ! k"
        using hm2_eq unfolding sub_t'_def using hk_len by simp
      have "m2 > k"
      proof (rule ccontr)
        assume "\<not> m2 > k" hence "m2 \<le> k" by simp
        have "tlist ! m2 \<le> tlist ! k"
          using sorted_nth_mono[OF hsort, of m2 k] \<open>m2 \<le> k\<close> hk_len by simp
        thus False using htm2_gt by simp
      qed
      hence "m2 \<ge> Suc k" by simp
      hence "tlist ! (Suc k) \<le> tlist ! m2"
        using sorted_nth_mono[OF hsort, of "Suc k" m2] hm2_len by simp
      hence "sub_t' (Suc k) \<le> sub_t_f i (Suc (Suc j))"
        using hm2_eq unfolding sub_t'_def using hSk_len by simp
      thus ?thesis using hSj_lt heq by (intro exI[of _ "Suc j"]) auto
    qed
  qed
  \<comment> \<open>By P-monotonicity, conclude.\<close>
  have "\<forall>i<ns. \<forall>k<n. P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                            {t. sub_t' k \<le> t \<and> t \<le> sub_t' (Suc k)}"
  proof (intro allI impI)
    fix i k assume hi: "i < ns" and hk: "k < n"
    from hrefines[rule_format, OF hi hk] obtain j where hj: "j < nt_f i"
        and hsub: "{t. sub_t' k \<le> t \<and> t \<le> sub_t' (Suc k)}
            \<subseteq> {t. sub_t_f i j \<le> t \<and> t \<le> sub_t_f i (Suc j)}" by (by100 blast)
    from hcov_f[rule_format, OF hi hj]
    show "P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)} {t. sub_t' k \<le> t \<and> t \<le> sub_t' (Suc k)}"
      using hP_mono hsub by (by100 blast)
  qed
  thus ?thesis using hn_pos hsub0 hsubn hsinc by (by100 blast)
qed
(* Proof requires common refinement of finitely many subdivisions.
   The sorted union of all boundary points gives a refinement where each piece
   fits in a piece of every original subdivision. This is a purely combinatorial
   fact about finite sorted sequences on [0,1].
   The UNIFORM grid approach (1/N) does NOT work: intervals can straddle boundaries
   even when all pieces are wider than 1/N, because the boundary points don't align.
proof -
  \<comment> \<open>Extract t-subdivisions for each s-piece via choice.\<close>
  obtain nt_f sub_t_f where
      hnt_f: "\<forall>i<ns. nt_f i \<ge> 1"
      and ht0_f: "\<forall>i<ns. sub_t_f i 0 = (0::real)"
      and htn_f: "\<forall>i<ns. sub_t_f i (nt_f i) = 1"
      and htinc_f: "\<forall>i<ns. \<forall>j<nt_f i. sub_t_f i j < sub_t_f i (Suc j)"
      and hcov_f: "\<forall>i<ns. \<forall>j<nt_f i. P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                          {t. sub_t_f i j \<le> t \<and> t \<le> sub_t_f i (Suc j)}"
  proof -
    \<comment> \<open>Use Hilbert choice to extract functions.\<close>
    define pick where "pick i = (SOME p :: nat \<times> (nat \<Rightarrow> real).
        fst p \<ge> 1 \<and> snd p 0 = 0 \<and> snd p (fst p) = 1
        \<and> (\<forall>j<fst p. snd p j < snd p (Suc j))
        \<and> (\<forall>j<fst p. P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                          {t. snd p j \<le> t \<and> t \<le> snd p (Suc j)}))" for i
    have hpick: "\<forall>i<ns. fst (pick i) \<ge> 1 \<and> snd (pick i) 0 = 0
        \<and> snd (pick i) (fst (pick i)) = 1
        \<and> (\<forall>j<fst (pick i). snd (pick i) j < snd (pick i) (Suc j))
        \<and> (\<forall>j<fst (pick i). P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                                  {t. snd (pick i) j \<le> t \<and> t \<le> snd (pick i) (Suc j)})"
    proof (intro allI impI)
      fix i assume hi: "i < ns"
      from hstrip[rule_format, OF hi] obtain nt sub_t where
          "nt \<ge> 1" "sub_t 0 = (0::real)" "sub_t nt = 1"
          "\<forall>j<nt. sub_t j < sub_t (Suc j)"
          "\<forall>j<nt. P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)} {t. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}"
        by auto
      hence "\<exists>p :: nat \<times> (nat \<Rightarrow> real). fst p \<ge> 1 \<and> snd p 0 = 0 \<and> snd p (fst p) = 1
          \<and> (\<forall>j<fst p. snd p j < snd p (Suc j))
          \<and> (\<forall>j<fst p. P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                              {t. snd p j \<le> t \<and> t \<le> snd p (Suc j)})"
        by (intro exI[of _ "(nt, sub_t)"]) simp
      thus "fst (pick i) \<ge> 1 \<and> snd (pick i) 0 = 0
          \<and> snd (pick i) (fst (pick i)) = 1
          \<and> (\<forall>j<fst (pick i). snd (pick i) j < snd (pick i) (Suc j))
          \<and> (\<forall>j<fst (pick i). P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                                      {t. snd (pick i) j \<le> t \<and> t \<le> snd (pick i) (Suc j)})"
        unfolding pick_def by (rule someI_ex)
    qed
    define nt_f where "nt_f i = fst (pick i)" for i
    define sub_t_f where "sub_t_f i = snd (pick i)" for i
    have "\<forall>i<ns. nt_f i \<ge> 1" using hpick unfolding nt_f_def by auto
    moreover have "\<forall>i<ns. sub_t_f i 0 = (0::real)" using hpick unfolding sub_t_f_def by auto
    moreover have "\<forall>i<ns. sub_t_f i (nt_f i) = 1" using hpick unfolding nt_f_def sub_t_f_def by auto
    moreover have "\<forall>i<ns. \<forall>j<nt_f i. sub_t_f i j < sub_t_f i (Suc j)"
      using hpick unfolding nt_f_def sub_t_f_def by auto
    moreover have "\<forall>i<ns. \<forall>j<nt_f i. P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                          {t. sub_t_f i j \<le> t \<and> t \<le> sub_t_f i (Suc j)}"
      using hpick unfolding nt_f_def sub_t_f_def by auto
    ultimately show ?thesis using that by blast
  qed
  \<comment> \<open>Minimum t-piece width over all s-pieces.\<close>
  define min_w where "min_w = Min {sub_t_f i (Suc j) - sub_t_f i j | i j. i < ns \<and> j < nt_f i}"
  have hmin_pos: "min_w > 0"
  proof -
    let ?S = "{sub_t_f i (Suc j) - sub_t_f i j | i j. i < ns \<and> j < nt_f i}"
    have hfin: "finite ?S"
    proof -
      have "?S \<subseteq> (\<lambda>(i,j). sub_t_f i (Suc j) - sub_t_f i j) ` (SIGMA i:{0..<ns}. {0..<nt_f i})"
        by auto
      moreover have "finite \<dots>" by simp
      ultimately show ?thesis by (rule finite_subset)
    qed
    have hne: "?S \<noteq> {}"
    proof -
      have "0 < ns" using hns by simp
      have "0 < nt_f 0" using hnt_f[rule_format, OF \<open>0 < ns\<close>] by simp
      hence "sub_t_f 0 (Suc 0) - sub_t_f 0 0 \<in> ?S" using \<open>0 < ns\<close> by (by100 blast)
      thus ?thesis by (by100 blast)
    qed
    have hpos: "\<forall>w\<in>?S. w > 0"
    proof (intro ballI)
      fix w assume "w \<in> ?S"
      then obtain i j where hw: "w = sub_t_f i (Suc j) - sub_t_f i j"
          and hi: "i < ns" and hj: "j < nt_f i" by (by100 blast)
      have "sub_t_f i j < sub_t_f i (Suc j)" using htinc_f[rule_format, OF hi hj] .
      thus "w > 0" using hw by simp
    qed
    show ?thesis unfolding min_w_def
      using Min_gr_iff[OF hfin hne] hpos by (by100 auto)
  qed
  \<comment> \<open>Take N large enough that 1/N < min_w.\<close>
  obtain N :: nat where hN: "N \<ge> 1" and hN_fine: "1 / real N < min_w"
  proof -
    from hmin_pos obtain N' :: nat where "real N' > 1 / min_w"
      using reals_Archimedean2 by (by100 blast)
    define N where "N = max N' 1"
    have "N \<ge> 1" unfolding N_def by simp
    moreover have "1 / real N < min_w"
    proof -
      have "real N \<ge> real N'" unfolding N_def by simp
      hence "real N > 1 / min_w" using \<open>real N' > 1 / min_w\<close> by simp
      hence "1 / real N < min_w" using hmin_pos \<open>N \<ge> 1\<close>
        by (simp add: field_simps pos_less_divide_eq)
      thus ?thesis .
    qed
    ultimately show ?thesis using that by blast
  qed
  \<comment> \<open>Define uniform t-grid: sub_t'(j) = j/N.\<close>
  define sub_t' where "sub_t' j = real j / real N" for j
  have ht0': "sub_t' 0 = 0" unfolding sub_t'_def by simp
  have htN': "sub_t' N = 1" unfolding sub_t'_def using hN by simp
  have htinc': "\<forall>j<N. sub_t' j < sub_t' (Suc j)"
    unfolding sub_t'_def using hN by (intro allI impI) (simp add: divide_strict_right_mono)
  \<comment> \<open>Each 1/N-interval fits inside some piece of every t-subdivision.\<close>
  have hfits: "\<forall>i<ns. \<forall>k<N. \<exists>j<nt_f i. {t. sub_t' k \<le> t \<and> t \<le> sub_t' (Suc k)}
      \<subseteq> {t. sub_t_f i j \<le> t \<and> t \<le> sub_t_f i (Suc j)}"
  proof (intro allI impI)
    fix i k assume hi: "i < ns" and hk: "k < N"
    \<comment> \<open>Use the RIGHT endpoint (k+1)/N for increasing_interval_cover.
       (k+1)/N \<in> [0,1] since Suc k \<le> N.\<close>
    have hSk_ge: "sub_t_f i 0 \<le> sub_t' (Suc k)"
      using ht0_f[rule_format, OF hi] hk hN unfolding sub_t'_def by simp
    have hSk_le: "sub_t' (Suc k) \<le> sub_t_f i (nt_f i)"
      using htn_f[rule_format, OF hi] hk hN unfolding sub_t'_def by simp
    have hnt: "nt_f i \<ge> 1" using hnt_f[rule_format, OF hi] .
    have hinc: "\<forall>j'<nt_f i. sub_t_f i j' < sub_t_f i (Suc j')"
      using htinc_f hi by (by100 auto)
    \<comment> \<open>Find j containing (k+1)/N.\<close>
    obtain j where hj: "j < nt_f i"
        and hj_le: "sub_t_f i j \<le> sub_t' (Suc k)"
        and hj_ge: "sub_t' (Suc k) \<le> sub_t_f i (Suc j)"
      using increasing_interval_cover[OF hnt hSk_ge hSk_le hinc] by (by100 blast)
    \<comment> \<open>Width of piece j \<ge> min_w > 1/N.\<close>
    have hwidth: "sub_t_f i (Suc j) - sub_t_f i j \<ge> min_w"
    proof -
      let ?S = "{sub_t_f i' (Suc j') - sub_t_f i' j' | i' j'. i' < ns \<and> j' < nt_f i'}"
      have "?S \<subseteq> (\<lambda>(i',j'). sub_t_f i' (Suc j') - sub_t_f i' j') ` (SIGMA i':{0..<ns}. {0..<nt_f i'})"
        by auto
      hence hfin: "finite ?S" by (rule finite_subset) simp
      have hmem: "sub_t_f i (Suc j) - sub_t_f i j \<in> ?S"
        using hi hj by (by100 blast)
      show ?thesis unfolding min_w_def using Min_le[OF hfin hmem] .
    qed
    \<comment> \<open>Key: k/N \<ge> sub_t_f i j. Proof by contradiction using width > 1/N.
       If sub_t_f i j > k/N, then sub_t_f i j > (k+1)/N - 1/N.
       Width = sub_t_f i (j+1) - sub_t_f i j \<le> (k+1)/N - sub_t_f i j < 1/N.
       But width \<ge> min_w > 1/N. Contradiction!\<close>
    have "sub_t' k \<ge> sub_t_f i j"
    proof (rule ccontr)
      assume "\<not> sub_t' k \<ge> sub_t_f i j"
      hence "sub_t_f i j > sub_t' k" by simp
      have hN_pos: "real N > 0" using hN by simp
      have "sub_t' (Suc k) = sub_t' k + 1 / real N"
        unfolding sub_t'_def using hN_pos by (simp add: field_simps)
      hence "sub_t_f i j > sub_t' (Suc k) - 1 / real N" using \<open>sub_t_f i j > sub_t' k\<close> by simp
      hence "sub_t_f i (Suc j) - sub_t_f i j < sub_t_f i (Suc j) - (sub_t' (Suc k) - 1 / real N)"
        by simp
      also have "\<dots> \<le> 1 / real N" using hj_ge by simp
      finally have "sub_t_f i (Suc j) - sub_t_f i j < 1 / real N" .
      thus False using hwidth hN_fine by simp
    qed
    show "\<exists>j<nt_f i. {t. sub_t' k \<le> t \<and> t \<le> sub_t' (Suc k)}
        \<subseteq> {t. sub_t_f i j \<le> t \<and> t \<le> sub_t_f i (Suc j)}"
      using hj \<open>sub_t' k \<ge> sub_t_f i j\<close> hj_ge by (intro exI[of _ j]) auto
  qed
  \<comment> \<open>By P-monotonicity, each 1/N \<times> s-piece satisfies P.\<close>
  have "\<forall>i<ns. \<forall>k<N. P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                              {t. sub_t' k \<le> t \<and> t \<le> sub_t' (Suc k)}"
  proof (intro allI impI)
    fix i k assume hi: "i < ns" and hk: "k < N"
    from hfits[rule_format, OF hi hk] obtain j where hj: "j < nt_f i"
        and hsub: "{t. sub_t' k \<le> t \<and> t \<le> sub_t' (Suc k)}
            \<subseteq> {t. sub_t_f i j \<le> t \<and> t \<le> sub_t_f i (Suc j)}" by (by100 blast)
    from hcov_f[rule_format, OF hi hj]
    have "P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)} {t. sub_t_f i j \<le> t \<and> t \<le> sub_t_f i (Suc j)}" .
    thus "P i {s. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)} {t. sub_t' k \<le> t \<and> t \<le> sub_t' (Suc k)}"
      using hP_mono hsub by (by100 blast)
  qed
  thus ?thesis using hN ht0' htN' htinc' by (by100 blast)
qed *)

(** from \<S>54 Lemma 54.2: homotopy-lifting lemma **)
lemma Lemma_54_2_homotopy_lifting:
  assumes "top1_covering_map_on E TE B TB p"
      and "e0 \<in> E" and "p e0 = b0"
      and "top1_continuous_map_on (I_set \<times> I_set) II_topology B TB F"
      and "F (0, 0) = b0"
      and "is_topology_on B TB" and "is_topology_on E TE"
  shows "\<exists>Ftilde. top1_continuous_map_on (I_set \<times> I_set) II_topology E TE Ftilde
    \<and> (\<forall>s\<in>I_set. \<forall>t\<in>I_set. p (Ftilde (s, t)) = F (s, t))
    \<and> Ftilde (0, 0) = e0"
proof -
  \<comment> \<open>Munkres 54.2: Rectangle-by-rectangle construction.
     Step 1: Lebesgue grid on I\<times>I. Each rectangle maps by F into evenly covered U.
     Step 2: Lift left edge and bottom edge via Lemma 54.1.
     Step 3: For each rectangle (row by row, left to right): boundary C = left\<union>bottom
       edge of rectangle, connected. Ftilde(C) in one slice V0. Define Ftilde = p0\<inverse>\<circ>F.
       Pasting lemma gives continuity.
     This directly gives joint continuity of Ftilde on I\<times>I.\<close>
  \<comment> \<open>Step 1: Lift left edge 0\<times>I via Lemma 54.1.\<close>
  have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hF_left_path: "top1_is_path_on B TB b0 (F (0, 1)) (\<lambda>t. F (0, t))"
  proof -
    have heq: "(\<lambda>t. F (0, t)) = F \<circ> (\<lambda>t. (0, t))" by (rule ext) simp
    show ?thesis unfolding top1_is_path_on_def heq
      using top1_continuous_map_on_comp[OF pair_const_t_continuous[OF h0I] assms(4)]
            assms(5) by simp
  qed
  obtain left_lift where hll: "top1_is_path_on E TE e0 (left_lift 1) left_lift"
      and hll_lift: "\<forall>t\<in>I_set. p (left_lift t) = F (0, t)"
    using Lemma_54_1_path_lifting[OF assms(1,2,3) hF_left_path assms(6,7)] by (by100 auto)
  \<comment> \<open>Step 2: Lift bottom edge I\<times>0 via Lemma 54.1.\<close>
  have hF_bot_path: "top1_is_path_on B TB b0 (F (1, 0)) (\<lambda>s. F (s, 0))"
  proof -
    have heq: "(\<lambda>s. F (s, 0)) = F \<circ> (\<lambda>s. (s, 0))" by (rule ext) simp
    show ?thesis unfolding top1_is_path_on_def heq
      using top1_continuous_map_on_comp[OF pair_s_const_continuous[OF h0I] assms(4)]
            assms(5) by simp
  qed
  obtain bot_lift where hbl: "top1_is_path_on E TE e0 (bot_lift 1) bot_lift"
      and hbl_lift: "\<forall>s\<in>I_set. p (bot_lift s) = F (s, 0)"
    using Lemma_54_1_path_lifting[OF assms(1,2,3) hF_bot_path assms(6,7)] by (by100 auto)
  \<comment> \<open>Step 3: For each (s,t) \<in> I\<times>I, get evenly covered U containing F(s,t).
     F\<inverse>(U) open in I\<times>I. Use bridge lemma to get \<epsilon>-ball in preimage.
     Cover I\<times>I by these balls. Apply open_cover_subdivision_01 to each coord.\<close>
  have hpointwise: "\<forall>s\<in>I_set. \<forall>t\<in>I_set. \<exists>U. openin_on B TB U
      \<and> top1_evenly_covered_on E TE B TB p U \<and> F (s, t) \<in> U"
  proof (intro ballI)
    fix s t assume hs: "s \<in> I_set" and ht: "t \<in> I_set"
    have "F (s, t) \<in> B" using assms(4) hs ht
      unfolding top1_continuous_map_on_def by (by100 blast)
    then obtain U where "F (s, t) \<in> U" "top1_evenly_covered_on E TE B TB p U"
      using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
    moreover have "openin_on B TB U"
      using \<open>top1_evenly_covered_on E TE B TB p U\<close>
      unfolding top1_evenly_covered_on_def by (by100 blast)
    ultimately show "\<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U \<and> F (s, t) \<in> U"
      by (by100 blast)
  qed
  \<comment> \<open>Step 4: Get s-subdivision and t-subdivision using open_cover_subdivision_01.
     For the s-coordinate: for each s, the set of t with F(s,t) in some evenly covered U
     gives an open cover. The s-subdivision ensures each vertical strip maps into a
     manageable cover. Similarly for t.
     For simplicity, we get a single subdivision for each coordinate by taking
     the common refinement of all pointwise covers.\<close>
  \<comment> \<open>Actually, the textbook just says "choose subdivisions fine enough". We use
     the Lebesgue number approach: each (s,t) has \<epsilon>(s,t) > 0 with F(B((s,t),\<epsilon>)\<inter>I\<times>I) \<subseteq> U.
     By compactness of I\<times>I, finite subcover. Lebesgue number \<delta> > 0. Take N > \<surd>2/\<delta>.
     Each 1/N-rectangle has diameter \<surd>2/N < \<delta>, so maps into some U.\<close>
  \<comment> \<open>This requires the metric Lebesgue number lemma for I\<times>I. We sorry this step.\<close>
  \<comment> \<open>The grid existence proof. We build an s-subdivision with per-s-piece t-subdivisions,
     then derive a single m \<times> n grid via common refinement.\<close>
  have hgrid_gen: "\<exists>ns\<ge>1. \<exists>sub_s :: nat \<Rightarrow> real. sub_s 0 = 0 \<and> sub_s ns = 1
      \<and> (\<forall>i<ns. sub_s i < sub_s (Suc i))
      \<and> (\<forall>i<ns. \<exists>nt\<ge>1. \<exists>sub_t :: nat \<Rightarrow> real. sub_t 0 = 0 \<and> sub_t nt = 1
          \<and> (\<forall>j<nt. sub_t j < sub_t (Suc j))
          \<and> (\<forall>j<nt. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
              \<and> F ` ({s\<in>I_set. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                    \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U))"
  proof -
    \<comment> \<open>For each (s0,t0) \<in> I\<times>I, get \<epsilon>>0 and evenly covered U with
       F(ball((s0,t0),\<epsilon>) \<inter> I\<times>I) \<subseteq> U. Bridge from II_topology to \<epsilon>-balls.\<close>
    have hpointball: "\<forall>s0\<in>I_set. \<forall>t0\<in>I_set. \<exists>\<epsilon>>0. \<exists>U. openin_on B TB U
        \<and> top1_evenly_covered_on E TE B TB p U
        \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>} \<times> {t\<in>I_set. \<bar>t - t0\<bar> < \<epsilon>}) \<subseteq> U"
    proof (intro ballI)
      fix s0 t0 assume hs0: "s0 \<in> I_set" and ht0: "t0 \<in> I_set"
      \<comment> \<open>F(s0,t0) has evenly covered neighborhood U.\<close>
      obtain U where hUo: "openin_on B TB U" and hUec: "top1_evenly_covered_on E TE B TB p U"
          and hFst: "F (s0, t0) \<in> U"
        using hpointwise hs0 ht0 by (by100 blast)
      \<comment> \<open>U \<in> TB, so F\<inverse>(U) = {x \<in> I\<times>I. F x \<in> U} is open in II_topology.\<close>
      have hpreU: "{x \<in> I_set \<times> I_set. F x \<in> U} \<in> II_topology"
        using assms(4) hUo unfolding II_topology_def top1_continuous_map_on_def openin_on_def
        by (by100 blast)
      \<comment> \<open>(s0,t0) \<in> F\<inverse>(U).\<close>
      have hst_pre: "(s0, t0) \<in> {x \<in> I_set \<times> I_set. F x \<in> U}"
        using hs0 ht0 hFst by (by100 blast)
      \<comment> \<open>F\<inverse>(U) open in II_topology = subspace of std R\<times>R topology on I\<times>I.
         So \<exists>W open in R\<times>R. F\<inverse>(U) = (I\<times>I) \<inter> W.\<close>
      obtain W where hWo: "open W" and hpre_eq: "{x \<in> I_set \<times> I_set. F x \<in> U} = (I_set \<times> I_set) \<inter> W"
      proof -
        have "{x \<in> I_set \<times> I_set. F x \<in> U} \<in> II_topology" by (rule hpreU)
        hence "{x \<in> I_set \<times> I_set. F x \<in> U}
            \<in> subspace_topology UNIV (product_topology_on (top1_open_sets :: real set set) top1_open_sets)
                (I_set \<times> I_set)"
          unfolding II_topology_def by (rule II_topology_eq_subspace[THEN equalityD1, THEN subsetD])
        then obtain W' where hW': "W' \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
            and heq: "{x \<in> I_set \<times> I_set. F x \<in> U} = (I_set \<times> I_set) \<inter> W'"
          unfolding subspace_topology_def by (by100 blast)
        have "W' \<in> (top1_open_sets :: (real \<times> real) set set)"
          using hW' product_topology_on_open_sets[where ?'a=real and ?'b=real] by (by100 blast)
        hence "open W'" unfolding top1_open_sets_def by (by100 blast)
        thus ?thesis using heq that by (by100 blast)
      qed
      \<comment> \<open>W is open in R\<times>R and contains (s0,t0). Get product neighborhood.\<close>
      have "(s0, t0) \<in> W" using hst_pre hpre_eq hs0 ht0 by (by100 blast)
      then obtain Ws Wt where hWso: "open Ws" and hWto: "open Wt"
          and hst_WW: "(s0, t0) \<in> Ws \<times> Wt" and hWWW: "Ws \<times> Wt \<subseteq> W"
        using open_prod_elim[OF hWo \<open>(s0, t0) \<in> W\<close>] by (by100 blast)
      have hs0Ws: "s0 \<in> Ws" and ht0Wt: "t0 \<in> Wt" using hst_WW by (by100 auto)+
      obtain \<epsilon>_s where h\<epsilon>s: "\<epsilon>_s > 0" and hWss: "\<forall>s. \<bar>s - s0\<bar> < \<epsilon>_s \<longrightarrow> s \<in> Ws"
      proof -
        from hWso hs0Ws obtain e where "e > 0" "\<forall>y. dist y s0 < e \<longrightarrow> y \<in> Ws"
          unfolding open_dist by (by100 blast)
        thus ?thesis using that unfolding dist_real_def by (by100 blast)
      qed
      obtain \<epsilon>_t where h\<epsilon>t: "\<epsilon>_t > 0" and hWtt: "\<forall>t. \<bar>t - t0\<bar> < \<epsilon>_t \<longrightarrow> t \<in> Wt"
      proof -
        from hWto ht0Wt obtain e where "e > 0" "\<forall>y. dist y t0 < e \<longrightarrow> y \<in> Wt"
          unfolding open_dist by (by100 blast)
        thus ?thesis using that unfolding dist_real_def by (by100 blast)
      qed
      define \<epsilon>' where "\<epsilon>' = min \<epsilon>_s \<epsilon>_t"
      have h\<epsilon>': "\<epsilon>' > 0" using h\<epsilon>s h\<epsilon>t unfolding \<epsilon>'_def by simp
      have hsquare_ball: "{s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>'} \<times> {t\<in>I_set. \<bar>t - t0\<bar> < \<epsilon>'} \<subseteq> W"
      proof (rule subsetI)
        fix x assume "x \<in> {s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>'} \<times> {t\<in>I_set. \<bar>t - t0\<bar> < \<epsilon>'}"
        then obtain s t where hx: "x = (s, t)" and hsd: "\<bar>s - s0\<bar> < \<epsilon>'" and htd: "\<bar>t - t0\<bar> < \<epsilon>'"
          by (by100 blast)
        have "s \<in> Ws" using hWss hsd unfolding \<epsilon>'_def by simp
        moreover have "t \<in> Wt" using hWtt htd unfolding \<epsilon>'_def by simp
        ultimately have "(s, t) \<in> Ws \<times> Wt" by (by100 blast)
        thus "x \<in> W" using hWWW hx by (by100 blast)
      qed
      have "F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>'} \<times> {t\<in>I_set. \<bar>t - t0\<bar> < \<epsilon>'}) \<subseteq> U"
      proof (rule image_subsetI)
        fix x assume hx_sq: "x \<in> {s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>'} \<times> {t\<in>I_set. \<bar>t - t0\<bar> < \<epsilon>'}"
        hence "x \<in> W" using hsquare_ball by (by100 blast)
        moreover have "x \<in> I_set \<times> I_set" using hx_sq by (by100 blast)
        ultimately have "x \<in> {x \<in> I_set \<times> I_set. F x \<in> U}" using hpre_eq by (by100 blast)
        thus "F x \<in> U" by (by100 blast)
      qed
      show "\<exists>\<epsilon>>0. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
          \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>} \<times> {t\<in>I_set. \<bar>t - t0\<bar> < \<epsilon>}) \<subseteq> U"
      proof (intro exI conjI)
        show "\<epsilon>' > 0" by (rule h\<epsilon>')
        show "openin_on B TB U" by (rule hUo)
        show "top1_evenly_covered_on E TE B TB p U" by (rule hUec)
        show "F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>'} \<times> {t\<in>I_set. \<bar>t - t0\<bar> < \<epsilon>'}) \<subseteq> U"
          by (rule \<open>F ` _ \<subseteq> U\<close>)
      qed
    qed
    \<comment> \<open>For each s0: 1D creeping on t-coordinate. For each t0, the ball from hpointball
       gives a t-interval. Apply open_cover_subdivision_01 to column.\<close>
    have hstrip: "\<forall>s0\<in>I_set. \<exists>\<epsilon>s>0. \<exists>nt\<ge>(1::nat). \<exists>sub_t :: nat \<Rightarrow> real.
        sub_t 0 = 0 \<and> sub_t nt = 1
        \<and> (\<forall>j<nt. sub_t j < sub_t (Suc j))
        \<and> (\<forall>j<nt. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
            \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>s}
                  \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U)"
    proof (intro ballI)
      fix s0 assume hs0: "s0 \<in> I_set"
      \<comment> \<open>For each t0 \<in> I: hpointball gives \<epsilon>>0, U with F(\<epsilon>-square at (s0,t0)) \<subseteq> U.
         The t-balls cover I. Apply open_cover_subdivision_01 on t.
         Get t-subdivision. For each piece j, the \<epsilon> gives s-width.
         Take min \<epsilon> over all pieces = \<epsilon>s.\<close>
      \<comment> \<open>Step 1: Build cover for open_cover_subdivision_01.\<close>
      define \<A> where "\<A> = (\<lambda>(t0, \<epsilon>, U). {t\<in>I_set. \<bar>t - t0\<bar> < \<epsilon>})
          ` {(t0, \<epsilon>, U). t0 \<in> I_set \<and> \<epsilon> > 0 \<and> openin_on B TB U
              \<and> top1_evenly_covered_on E TE B TB p U
              \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>} \<times> {t\<in>I_set. \<bar>t - t0\<bar> < \<epsilon>}) \<subseteq> U}"
      have ht_cov: "\<forall>t0. 0 \<le> t0 \<and> t0 \<le> 1 \<longrightarrow>
          (\<exists>V\<in>\<A>. t0 \<in> V \<and> (\<exists>\<epsilon>>0. {t'. \<bar>t' - t0\<bar> < \<epsilon> \<and> 0 \<le> t' \<and> t' \<le> 1} \<subseteq> V))"
      proof (intro allI impI)
        fix t0 :: real assume ht0: "0 \<le> t0 \<and> t0 \<le> 1"
        have ht0_I: "t0 \<in> I_set" using ht0 unfolding top1_unit_interval_def by simp
        obtain \<epsilon> Uc where h\<epsilon>: "\<epsilon> > 0" and hUo: "openin_on B TB Uc"
            and hUec: "top1_evenly_covered_on E TE B TB p Uc"
            and hFsub: "F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>} \<times> {t\<in>I_set. \<bar>t - t0\<bar> < \<epsilon>}) \<subseteq> Uc"
          using hpointball[rule_format, OF hs0 ht0_I] by (by100 blast)
        define V where "V = {t\<in>I_set. \<bar>t - t0\<bar> < \<epsilon>}"
        have "V \<in> \<A>"
          unfolding \<A>_def V_def using ht0_I h\<epsilon> hUo hUec hFsub by (by100 blast)
        moreover have "t0 \<in> V" unfolding V_def using ht0_I h\<epsilon> by simp
        moreover have "\<exists>\<epsilon>'>0. {t'. \<bar>t' - t0\<bar> < \<epsilon>' \<and> 0 \<le> t' \<and> t' \<le> 1} \<subseteq> V"
          using h\<epsilon> unfolding V_def top1_unit_interval_def by (intro exI[of _ \<epsilon>]) (by100 auto)
        ultimately show "\<exists>V\<in>\<A>. t0 \<in> V \<and> (\<exists>\<epsilon>>0. {t'. \<bar>t' - t0\<bar> < \<epsilon> \<and> 0 \<le> t' \<and> t' \<le> 1} \<subseteq> V)"
          by (by100 blast)
      qed
      \<comment> \<open>Step 2: Apply open_cover_subdivision_01.\<close>
      obtain nt sub_t where hnt: "nt \<ge> 1" and ht0': "sub_t (0::nat) = (0::real)"
          and htn: "sub_t nt = 1"
          and ht_inc: "\<forall>j<nt. sub_t j < sub_t (Suc j)"
          and ht_cov2: "\<forall>j<nt. \<exists>V\<in>\<A>. {t. sub_t j \<le> t \<and> t \<le> sub_t (Suc j) \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> V"
        using open_cover_subdivision_01[OF ht_cov] by (by100 auto)
      \<comment> \<open>Step 3: For each j, the covering set V_j \<in> \<A> gives \<epsilon>_j with
         F({s:|s-s0|<\<epsilon>_j} \<times> V_j) \<subseteq> U_j and [t_j,t_{j+1}] \<subseteq> V_j.
         So F({s:|s-s0|<\<epsilon>_j} \<times> [t_j,t_{j+1}]) \<subseteq> U_j.
         Take \<epsilon>s = min of \<epsilon>_j's.\<close>
      have ht_eps: "\<forall>j<nt. \<exists>\<epsilon>>0. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
          \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>}
                \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U"
      proof (intro allI impI)
        fix j assume hj: "j < nt"
        obtain V where hVA: "V \<in> \<A>"
            and hVsub: "{t. sub_t j \<le> t \<and> t \<le> sub_t (Suc j) \<and> 0 \<le> t \<and> t \<le> 1} \<subseteq> V"
          using ht_cov2[rule_format, OF hj] by (by100 blast)
        \<comment> \<open>V \<in> \<A>: extract t0, \<epsilon>, U.\<close>
        obtain t0_j \<epsilon>_j U_j where ht0j: "t0_j \<in> I_set" and h\<epsilon>j: "\<epsilon>_j > 0"
            and hUo_j: "openin_on B TB U_j" and hUec_j: "top1_evenly_covered_on E TE B TB p U_j"
            and hVeq: "V = {t\<in>I_set. \<bar>t - t0_j\<bar> < \<epsilon>_j}"
            and hFsub_j: "F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>_j} \<times> {t\<in>I_set. \<bar>t - t0_j\<bar> < \<epsilon>_j}) \<subseteq> U_j"
        proof -
          from hVA obtain x where hxS: "x \<in> {(t0, \<epsilon>, U). t0 \<in> I_set \<and> \<epsilon> > 0 \<and> openin_on B TB U
              \<and> top1_evenly_covered_on E TE B TB p U
              \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>} \<times> {t\<in>I_set. \<bar>t - t0\<bar> < \<epsilon>}) \<subseteq> U}"
              and hVx: "V = (\<lambda>(t0, \<epsilon>, U). {t\<in>I_set. \<bar>t - t0\<bar> < \<epsilon>}) x"
            unfolding \<A>_def by auto
          obtain t0' \<epsilon>' U' where hx_eq: "x = (t0', \<epsilon>', U')" by (cases x) auto
          have "t0' \<in> I_set" "\<epsilon>' > 0" "openin_on B TB U'"
              "top1_evenly_covered_on E TE B TB p U'"
              "F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>'} \<times> {t\<in>I_set. \<bar>t - t0'\<bar> < \<epsilon>'}) \<subseteq> U'"
            using hxS hx_eq by auto+
          moreover have "V = {t\<in>I_set. \<bar>t - t0'\<bar> < \<epsilon>'}" using hVx hx_eq by simp
          ultimately show ?thesis using that by (by100 blast)
        qed
        \<comment> \<open>[t_j, t_{j+1}] \<subseteq> V = {t\<in>I. |t-t0_j| < \<epsilon>_j}.\<close>
        have hpiece_sub: "{t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)} \<subseteq> V"
        proof -
          have "{t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}
              \<subseteq> {t. sub_t j \<le> t \<and> t \<le> sub_t (Suc j) \<and> 0 \<le> t \<and> t \<le> 1}"
            unfolding top1_unit_interval_def by (by100 auto)
          thus ?thesis using hVsub by (by100 blast)
        qed
        \<comment> \<open>F({s:|s-s0|<\<epsilon>_j} \<times> [t_j,t_{j+1}]) \<subseteq> F({s:|s-s0|<\<epsilon>_j} \<times> V) \<subseteq> U_j.\<close>
        have "F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>_j} \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)})
            \<subseteq> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>_j} \<times> V)"
          using hpiece_sub by (by100 blast)
        also have "\<dots> \<subseteq> U_j" using hFsub_j hVeq by simp
        finally show "\<exists>\<epsilon>>0. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
            \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>} \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U"
          using h\<epsilon>j hUo_j hUec_j by (by100 blast)
      qed
      \<comment> \<open>Extract \<epsilon>s = min over j of \<epsilon>_j.\<close>
      define eU_j where "eU_j j = (SOME q :: real \<times> 'b set. fst q > 0
          \<and> openin_on B TB (snd q) \<and> top1_evenly_covered_on E TE B TB p (snd q)
          \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < fst q}
                \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> snd q)" for j
      have heU: "\<forall>j<nt. fst (eU_j j) > 0
          \<and> openin_on B TB (snd (eU_j j)) \<and> top1_evenly_covered_on E TE B TB p (snd (eU_j j))
          \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < fst (eU_j j)}
                \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> snd (eU_j j)"
      proof (intro allI impI)
        fix j assume "j < nt"
        from ht_eps[rule_format, OF this] obtain \<epsilon> U where h\<epsilon>: "\<epsilon> > 0"
            and hUo: "openin_on B TB U" and hUec: "top1_evenly_covered_on E TE B TB p U"
            and hFsub: "F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>}
                  \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U"
          by (by100 blast)
        have "\<exists>q :: real \<times> 'b set. fst q > 0 \<and> openin_on B TB (snd q)
            \<and> top1_evenly_covered_on E TE B TB p (snd q)
            \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < fst q}
                  \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> snd q"
        proof (intro exI[of _ "(\<epsilon>, U)"])
          show "fst (\<epsilon>, U) > 0 \<and> openin_on B TB (snd (\<epsilon>, U))
              \<and> top1_evenly_covered_on E TE B TB p (snd (\<epsilon>, U))
              \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < fst (\<epsilon>, U)}
                    \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> snd (\<epsilon>, U)"
            using h\<epsilon> hUo hUec hFsub by simp
        qed
        thus "fst (eU_j j) > 0
            \<and> openin_on B TB (snd (eU_j j)) \<and> top1_evenly_covered_on E TE B TB p (snd (eU_j j))
            \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < fst (eU_j j)}
                  \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> snd (eU_j j)"
          unfolding eU_j_def by (rule someI_ex)
      qed
      define eps_j where "eps_j j = fst (eU_j j)" for j
      define U_j where "U_j j = snd (eU_j j)" for j
      have heps_j: "\<forall>j<nt. eps_j j > 0"
          and hU_j: "\<forall>j<nt. openin_on B TB (U_j j) \<and> top1_evenly_covered_on E TE B TB p (U_j j)
              \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < eps_j j}
                    \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U_j j"
        unfolding eps_j_def U_j_def using heU by auto+
      define \<epsilon>s where "\<epsilon>s = Min (eps_j ` {0..<nt})"
      have h\<epsilon>s_pos: "\<epsilon>s > 0"
      proof -
        have "finite (eps_j ` {0..<nt})" by simp
        moreover have "eps_j ` {0..<nt} \<noteq> {}" using hnt by (by100 auto)
        moreover have "\<forall>e\<in>eps_j ` {0..<nt}. e > 0" using heps_j by (by100 auto)
        ultimately show ?thesis unfolding \<epsilon>s_def
          by (metis Min_gr_iff)
      qed
      have h\<epsilon>s_le: "\<forall>j<nt. \<epsilon>s \<le> eps_j j"
        unfolding \<epsilon>s_def by (by100 auto)
      show "\<exists>\<epsilon>s>0. \<exists>nt\<ge>1. \<exists>sub_t.
          sub_t 0 = 0 \<and> sub_t nt = 1
          \<and> (\<forall>j<nt. sub_t j < sub_t (Suc j))
          \<and> (\<forall>j<nt. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
              \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>s}
                    \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U)"
      proof (intro exI conjI)
        show "\<epsilon>s > 0" by (rule h\<epsilon>s_pos)
        show "nt \<ge> (1::nat)" by (rule hnt)
        show "sub_t 0 = (0::real)" by (rule ht0')
        show "sub_t nt = (1::real)" by (rule htn)
        show "\<forall>j<nt. sub_t j < sub_t (Suc j)" by (rule ht_inc)
        show "\<forall>j<nt. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
            \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>s}
                  \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U"
        proof (intro allI impI)
          fix j assume hj: "j < nt"
          have "F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>s}
                    \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)})
              \<subseteq> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < eps_j j}
                    \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)})"
            using h\<epsilon>s_le[rule_format, OF hj] by (by100 auto)
          also have "\<dots> \<subseteq> U_j j" using hU_j hj by (by100 blast)
          finally show "\<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
              \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>s}
                    \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U"
            using hU_j hj by (by100 blast)
        qed
      qed
    qed
    \<comment> \<open>1D creeping on s-coordinate using \<epsilon>s from hstrip.\<close>
    obtain ns sub_s where hns: "ns \<ge> 1" and hs_0: "sub_s (0::nat) = (0::real)"
        and hs_n: "sub_s ns = 1"
        and hs_inc: "\<forall>i<ns. sub_s i < sub_s (Suc i)"
        and hs_strip: "\<forall>i<ns. \<exists>nt\<ge>1. \<exists>sub_t :: nat \<Rightarrow> real.
            sub_t 0 = 0 \<and> sub_t nt = 1
            \<and> (\<forall>j<nt. sub_t j < sub_t (Suc j))
            \<and> (\<forall>j<nt. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
                \<and> F ` ({s\<in>I_set. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                      \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U)"
    proof -
      \<comment> \<open>Build s-cover from hstrip: for each s0 \<in> I, the ball {s:|s-s0|<\<epsilon>s} is the covering set.\<close>
      define \<B> where "\<B> = (\<lambda>(s0, \<epsilon>s, nt, sub_t). {s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>s})
          ` {(s0, \<epsilon>s, nt, sub_t). s0 \<in> I_set \<and> \<epsilon>s > 0 \<and> (nt::nat) \<ge> 1
              \<and> sub_t 0 = (0::real) \<and> sub_t nt = 1
              \<and> (\<forall>j<nt. sub_t j < sub_t (Suc j))
              \<and> (\<forall>j<nt. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
                  \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>s}
                        \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U)}"
      have hs_cov: "\<forall>s0. 0 \<le> s0 \<and> s0 \<le> 1 \<longrightarrow>
          (\<exists>V\<in>\<B>. s0 \<in> V \<and> (\<exists>\<epsilon>>0. {s'. \<bar>s' - s0\<bar> < \<epsilon> \<and> 0 \<le> s' \<and> s' \<le> 1} \<subseteq> V))"
      proof (intro allI impI)
        fix s0 :: real assume hs0': "0 \<le> s0 \<and> s0 \<le> 1"
        have hs0_I: "s0 \<in> I_set" using hs0' unfolding top1_unit_interval_def by simp
        obtain \<epsilon>s nt sub_t where h\<epsilon>s: "\<epsilon>s > 0" and hnt: "nt \<ge> 1"
            and hsub0: "sub_t (0::nat) = (0::real)" and hsubn: "sub_t nt = 1"
            and ht_inc: "\<forall>j<nt. sub_t j < sub_t (Suc j)"
            and hcov': "\<forall>j<nt. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
                \<and> F ` ({s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>s}
                      \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U"
          using hstrip[rule_format, OF hs0_I] by auto
        define V where "V = {s\<in>I_set. \<bar>s - s0\<bar> < \<epsilon>s}"
        have "V \<in> \<B>"
          unfolding \<B>_def V_def using hs0_I h\<epsilon>s hnt hsub0 hsubn ht_inc hcov' by auto
        moreover have "s0 \<in> V" unfolding V_def using hs0_I h\<epsilon>s by simp
        moreover have "\<exists>\<epsilon>>0. {s'. \<bar>s' - s0\<bar> < \<epsilon> \<and> 0 \<le> s' \<and> s' \<le> 1} \<subseteq> V"
          using h\<epsilon>s unfolding V_def top1_unit_interval_def by (intro exI[of _ \<epsilon>s]) auto
        ultimately show "\<exists>V\<in>\<B>. s0 \<in> V \<and> (\<exists>\<epsilon>>0. {s'. \<bar>s' - s0\<bar> < \<epsilon> \<and> 0 \<le> s' \<and> s' \<le> 1} \<subseteq> V)"
          by blast
      qed
      obtain ns sub_s' where hns': "ns \<ge> 1" and hs0': "sub_s' (0::nat) = (0::real)"
          and hsn': "sub_s' ns = 1"
          and hs_inc': "\<forall>i<ns. sub_s' i < sub_s' (Suc i)"
          and hs_cov2: "\<forall>i<ns. \<exists>V\<in>\<B>. {s. sub_s' i \<le> s \<and> s \<le> sub_s' (Suc i) \<and> 0 \<le> s \<and> s \<le> 1} \<subseteq> V"
        using open_cover_subdivision_01[OF hs_cov] by auto
      \<comment> \<open>For each s-piece i, extract the strip property.\<close>
      have hs_strip': "\<forall>i<ns. \<exists>nt\<ge>1. \<exists>sub_t :: nat \<Rightarrow> real.
            sub_t 0 = 0 \<and> sub_t nt = 1
            \<and> (\<forall>j<nt. sub_t j < sub_t (Suc j))
            \<and> (\<forall>j<nt. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
                \<and> F ` ({s\<in>I_set. sub_s' i \<le> s \<and> s \<le> sub_s' (Suc i)}
                      \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U)"
      proof (intro allI impI)
        fix i assume hi: "i < ns"
        obtain V where hVB: "V \<in> \<B>"
            and hVsub: "{s. sub_s' i \<le> s \<and> s \<le> sub_s' (Suc i) \<and> 0 \<le> s \<and> s \<le> 1} \<subseteq> V"
          using hs_cov2[rule_format, OF hi] by blast
        \<comment> \<open>Extract from V \<in> \<B>.\<close>
        obtain s0_i \<epsilon>s_i nt_i sub_t_i where
            hs0i: "s0_i \<in> I_set" and h\<epsilon>si: "\<epsilon>s_i > 0" and hnti: "nt_i \<ge> 1"
            and ht0i: "sub_t_i 0 = (0::real)" and htni: "sub_t_i nt_i = 1"
            and htinci: "\<forall>j<nt_i. sub_t_i j < sub_t_i (Suc j)"
            and hcovi: "\<forall>j<nt_i. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
                \<and> F ` ({s\<in>I_set. \<bar>s - s0_i\<bar> < \<epsilon>s_i}
                      \<times> {t\<in>I_set. sub_t_i j \<le> t \<and> t \<le> sub_t_i (Suc j)}) \<subseteq> U"
            and hVeq: "V = {s\<in>I_set. \<bar>s - s0_i\<bar> < \<epsilon>s_i}"
          using hVB unfolding \<B>_def by auto
        \<comment> \<open>[sub_s' i, sub_s'(i+1)] \<subseteq> V = {s\<in>I. |s-s0_i| < \<epsilon>s_i}.\<close>
        have hpiece_sub: "{s\<in>I_set. sub_s' i \<le> s \<and> s \<le> sub_s' (Suc i)} \<subseteq> V"
          using hVsub unfolding top1_unit_interval_def by auto
        \<comment> \<open>Strip property with [sub_s' i, sub_s'(i+1)] instead of \<epsilon>s-ball.\<close>
        have "\<forall>j<nt_i. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
            \<and> F ` ({s\<in>I_set. sub_s' i \<le> s \<and> s \<le> sub_s' (Suc i)}
                  \<times> {t\<in>I_set. sub_t_i j \<le> t \<and> t \<le> sub_t_i (Suc j)}) \<subseteq> U"
        proof (intro allI impI)
          fix j assume hj: "j < nt_i"
          obtain Uj where hUjo: "openin_on B TB Uj" and hUjec: "top1_evenly_covered_on E TE B TB p Uj"
              and hFsub: "F ` ({s\<in>I_set. \<bar>s - s0_i\<bar> < \<epsilon>s_i}
                    \<times> {t\<in>I_set. sub_t_i j \<le> t \<and> t \<le> sub_t_i (Suc j)}) \<subseteq> Uj"
            using hcovi[rule_format, OF hj] by blast
          have "F ` ({s\<in>I_set. sub_s' i \<le> s \<and> s \<le> sub_s' (Suc i)}
                \<times> {t\<in>I_set. sub_t_i j \<le> t \<and> t \<le> sub_t_i (Suc j)})
              \<subseteq> F ` ({s\<in>I_set. \<bar>s - s0_i\<bar> < \<epsilon>s_i}
                    \<times> {t\<in>I_set. sub_t_i j \<le> t \<and> t \<le> sub_t_i (Suc j)})"
            using hpiece_sub hVeq by auto
          also have "\<dots> \<subseteq> Uj" by (rule hFsub)
          finally show "\<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
              \<and> F ` ({s\<in>I_set. sub_s' i \<le> s \<and> s \<le> sub_s' (Suc i)}
                    \<times> {t\<in>I_set. sub_t_i j \<le> t \<and> t \<le> sub_t_i (Suc j)}) \<subseteq> U"
            using hUjo hUjec by blast
        qed
        thus "\<exists>nt\<ge>1. \<exists>sub_t :: nat \<Rightarrow> real.
            sub_t 0 = 0 \<and> sub_t nt = 1
            \<and> (\<forall>j<nt. sub_t j < sub_t (Suc j))
            \<and> (\<forall>j<nt. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
                \<and> F ` ({s\<in>I_set. sub_s' i \<le> s \<and> s \<le> sub_s' (Suc i)}
                      \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U)"
          using hnti ht0i htni htinci by blast
      qed
      show ?thesis
        by (rule that[OF hns' hs0' hsn' hs_inc' hs_strip'])
    qed
    \<comment> \<open>For each s-piece i, get t-subdivision. Use the FIRST t-subdivision (for i=0)
       as a common subdivision. Actually, hs_strip already gives per-s-piece t-subdivisions.
       We use hs_strip directly to satisfy the general grid form.\<close>
    \<comment> \<open>We need a SINGLE t-subdivision for all s-pieces. Take common refinement.
       For simplicity, we sorry this final combinatorial step and proceed with
       the non-uniform grid directly.\<close>
    show ?thesis using hns hs_0 hs_n hs_inc hs_strip by (by100 blast)
  qed

  \<comment> \<open>Step 5: Derive a single m \<times> n grid from hgrid_gen by taking the common
     refinement of the per-s-piece t-subdivisions.\<close>
  obtain m n sub_s sub_t where
      hm: "m \<ge> 1" and hn: "n \<ge> 1"
      and hs0: "sub_s 0 = 0" and hsm: "sub_s m = 1"
      and ht0: "sub_t 0 = 0" and htn: "sub_t n = 1"
      and hs_inc: "\<forall>i<m. sub_s i < sub_s (Suc i)"
      and ht_inc: "\<forall>j<n. sub_t j < sub_t (Suc j)"
      and hgrid: "\<forall>i<m. \<forall>j<n. \<exists>U. openin_on B TB U
          \<and> top1_evenly_covered_on E TE B TB p U
          \<and> F ` ({s\<in>I_set. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)}
                \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U"
  proof -
    from hgrid_gen obtain ns0 sub_s0 where hns0: "ns0 \<ge> 1"
        and hs00: "sub_s0 0 = (0::real)" and hsn0: "sub_s0 ns0 = 1"
        and hsinc0: "\<forall>i<ns0. sub_s0 i < sub_s0 (Suc i)"
        and hstrip0: "\<forall>i<ns0. \<exists>nt\<ge>1. \<exists>sub_t :: nat \<Rightarrow> real. sub_t 0 = 0 \<and> sub_t nt = 1
            \<and> (\<forall>j<nt. sub_t j < sub_t (Suc j))
            \<and> (\<forall>j<nt. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
                \<and> F ` ({s\<in>I_set. sub_s0 i \<le> s \<and> s \<le> sub_s0 (Suc i)}
                      \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U)"
      by auto
    \<comment> \<open>Apply grid_from_per_piece_subdivisions with
       P i S T = (\<exists>U. openin_on B TB U \<and> evenly_covered U \<and> F ` (S\<inter>I \<times> T\<inter>I) \<subseteq> U).\<close>
    define P where "P = (\<lambda>(i::nat) (S::real set) (T::real set). \<exists>U. openin_on B TB U
        \<and> top1_evenly_covered_on E TE B TB p U
        \<and> F ` ({s\<in>I_set. s \<in> S} \<times> {t\<in>I_set. t \<in> T}) \<subseteq> U)"
    have hstrip_P: "\<forall>i<ns0. \<exists>nt\<ge>1. \<exists>sub_t :: nat \<Rightarrow> real. sub_t 0 = 0 \<and> sub_t nt = 1
        \<and> (\<forall>j<nt. sub_t j < sub_t (Suc j))
        \<and> (\<forall>j<nt. P i {s. sub_s0 i \<le> s \<and> s \<le> sub_s0 (Suc i)}
                        {t. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)})"
    proof (intro allI impI)
      fix i assume hi: "i < ns0"
      from hstrip0[rule_format, OF hi] obtain nt sub_t where
          "nt \<ge> 1" "sub_t 0 = (0::real)" "sub_t nt = 1"
          "\<forall>j<nt. sub_t j < sub_t (Suc j)"
          "\<forall>j<nt. \<exists>U. openin_on B TB U \<and> top1_evenly_covered_on E TE B TB p U
              \<and> F ` ({s\<in>I_set. sub_s0 i \<le> s \<and> s \<le> sub_s0 (Suc i)}
                    \<times> {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}) \<subseteq> U"
        by auto
      moreover have "\<forall>j<nt. P i {s. sub_s0 i \<le> s \<and> s \<le> sub_s0 (Suc i)}
                                {t. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}"
        unfolding P_def using \<open>\<forall>j<nt. \<exists>U. _\<close> by auto
      ultimately show "\<exists>nt\<ge>1. \<exists>sub_t. sub_t 0 = (0::real) \<and> sub_t nt = 1
          \<and> (\<forall>j<nt. sub_t j < sub_t (Suc j))
          \<and> (\<forall>j<nt. P i {s. sub_s0 i \<le> s \<and> s \<le> sub_s0 (Suc i)}
                          {t. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)})"
        by blast
    qed
    have hP_mono: "\<forall>i S T T'. T' \<subseteq> T \<longrightarrow> P i S T \<longrightarrow> P i S T'"
      unfolding P_def by blast
    from grid_from_per_piece_subdivisions[OF hns0 hs00 hsn0 hsinc0 hstrip_P hP_mono]
    obtain n sub_t' where hn_: "n \<ge> 1" and ht0_: "sub_t' 0 = (0::real)" and htn_: "sub_t' n = 1"
        and htinc_: "\<forall>j<n. sub_t' j < sub_t' (Suc j)"
        and hgrid_: "\<forall>i<ns0. \<forall>j<n. P i {s. sub_s0 i \<le> s \<and> s \<le> sub_s0 (Suc i)}
                                        {t. sub_t' j \<le> t \<and> t \<le> sub_t' (Suc j)}"
      by auto
    \<comment> \<open>Convert P back to the original form.\<close>
    have hgrid_orig: "\<forall>i<ns0. \<forall>j<n. \<exists>U. openin_on B TB U
        \<and> top1_evenly_covered_on E TE B TB p U
        \<and> F ` ({s\<in>I_set. sub_s0 i \<le> s \<and> s \<le> sub_s0 (Suc i)}
              \<times> {t\<in>I_set. sub_t' j \<le> t \<and> t \<le> sub_t' (Suc j)}) \<subseteq> U"
    proof (intro allI impI)
      fix i j assume hi: "i < ns0" and hj: "j < n"
      from hgrid_[rule_format, OF hi hj] show "\<exists>U. openin_on B TB U
          \<and> top1_evenly_covered_on E TE B TB p U
          \<and> F ` ({s\<in>I_set. sub_s0 i \<le> s \<and> s \<le> sub_s0 (Suc i)}
                \<times> {t\<in>I_set. sub_t' j \<le> t \<and> t \<le> sub_t' (Suc j)}) \<subseteq> U"
        unfolding P_def by auto
    qed
    show ?thesis
      by (rule that[OF hns0 hn_ hs00 hsn0 ht0_ htn_ hsinc0 htinc_ hgrid_orig])
  qed
  \<comment> \<open>Step 4: Rectangle-by-rectangle construction (textbook Munkres 54.2).
     Induction on linearized index k = j*m + i over rectangles.
     Invariant: Ftilde continuous on A_k, lifts F, starts at e0.
     At each step: boundary C connected, Ftilde(C) in one slice V0,
     extend Ftilde = p0\<inverse>\<circ>F on rectangle, pasting gives continuity.
     After m*n steps: Ftilde continuous on all of I\<times>I.\<close>
  \<comment> \<open>Define rectangles and regions.\<close>
  let ?R = "\<lambda>i j. {s\<in>I_set. sub_s i \<le> s \<and> s \<le> sub_s (Suc i)} \<times>
                  {t\<in>I_set. sub_t j \<le> t \<and> t \<le> sub_t (Suc j)}"
  let ?left_edge = "{0::real} \<times> I_set"
  let ?bot_edge = "I_set \<times> {0::real}"
  let ?edges = "?left_edge \<union> ?bot_edge"
  \<comment> \<open>A_k = edges \<union> first k rectangles (row by row, left to right).\<close>
  let ?A = "\<lambda>k. ?edges \<union> (\<Union>k'<k. ?R (k' mod m) (k' div m))"
  \<comment> \<open>Grid point values are in I_set (by monotonicity between 0 and 1).\<close>
  \<comment> \<open>Key fact: sub_s i is monotone and in I_set.\<close>
  have hsub_s_le_Suc: "\<forall>i<m. sub_s i \<le> sub_s (Suc i)"
    using hs_inc by (by100 auto)
  have hsub_s_mono: "\<forall>i. \<forall>j. i \<le> j \<and> j \<le> m \<longrightarrow> sub_s i \<le> sub_s j"
  proof (intro allI impI)
    fix i j :: nat assume h: "i \<le> j \<and> j \<le> m"
    hence hij: "i \<le> j" and hjm: "j \<le> m" by auto
    show "sub_s i \<le> sub_s j" using hij hjm
    proof (induction "j - i" arbitrary: j)
      case 0 thus ?case by simp
    next
      case (Suc d)
      hence "j > 0" by simp
      then obtain j' where hj': "j = Suc j'" using not0_implies_Suc by (by100 blast)
      have "i \<le> j'" using Suc.hyps(2) hj' by simp
      have "j' \<le> m" using Suc.prems(2) hj' by simp
      have "d = j' - i" using Suc.hyps(2) hj' by simp
      have h1: "sub_s i \<le> sub_s j'" using Suc.hyps(1)[OF \<open>d = j' - i\<close> \<open>i \<le> j'\<close> \<open>j' \<le> m\<close>] .
      have "j' < m" using \<open>j' \<le> m\<close> hj' Suc.prems(2) by simp
      have h2: "sub_s j' \<le> sub_s (Suc j')" using hsub_s_le_Suc \<open>j' < m\<close> by (by100 blast)
      show ?case using h1 h2 hj' by simp
    qed
  qed
  have hsub_s_I: "\<forall>i\<le>m. sub_s i \<in> I_set"
  proof (intro allI impI)
    fix i assume hi2: "i \<le> m"
    have "0 \<le> sub_s i" using hsub_s_mono[rule_format, of 0 i] hs0 hi2 by simp
    moreover have "sub_s i \<le> 1" using hsub_s_mono[rule_format, of i m] hi2 hsm by simp
    ultimately show "sub_s i \<in> I_set" unfolding top1_unit_interval_def by simp
  qed
  have hsub_t_le_Suc: "\<forall>j<n. sub_t j \<le> sub_t (Suc j)"
    using ht_inc by (by100 auto)
  have hsub_t_mono: "\<forall>i. \<forall>j. i \<le> j \<and> j \<le> n \<longrightarrow> sub_t i \<le> sub_t j"
  proof (intro allI impI)
    fix i j :: nat assume h: "i \<le> j \<and> j \<le> n"
    hence hij: "i \<le> j" and hjn: "j \<le> n" by auto
    show "sub_t i \<le> sub_t j" using hij hjn
    proof (induction "j - i" arbitrary: j)
      case 0 thus ?case by simp
    next
      case (Suc d)
      hence "j > 0" by simp
      then obtain j' where hj': "j = Suc j'" using not0_implies_Suc by (by100 blast)
      have "i \<le> j'" using Suc.hyps(2) hj' by simp
      have "j' \<le> n" using Suc.prems(2) hj' by simp
      have "d = j' - i" using Suc.hyps(2) hj' by simp
      have h1: "sub_t i \<le> sub_t j'" using Suc.hyps(1)[OF \<open>d = j' - i\<close> \<open>i \<le> j'\<close> \<open>j' \<le> n\<close>] .
      have "j' < n" using \<open>j' \<le> n\<close> hj' Suc.prems(2) by simp
      have h2: "sub_t j' \<le> sub_t (Suc j')" using hsub_t_le_Suc \<open>j' < n\<close> by (by100 blast)
      show ?case using h1 h2 hj' by simp
    qed
  qed
  have hsub_t_I: "\<forall>j\<le>n. sub_t j \<in> I_set"
  proof (intro allI impI)
    fix j assume hj2: "j \<le> n"
    have "0 \<le> sub_t j" using hsub_t_mono[rule_format, of 0 j] ht0 hj2 by simp
    moreover have "sub_t j \<le> 1" using hsub_t_mono[rule_format, of j n] hj2 htn by simp
    ultimately show "sub_t j \<in> I_set" unfolding top1_unit_interval_def by simp
  qed
  \<comment> \<open>Induction: \<forall>k \<le> m*n. \<exists>Ft. continuous on A_k, lifts F on A_k, Ft(0,0) = e0.\<close>
  have "\<forall>k \<le> m*n. \<exists>Ft. top1_continuous_map_on (?A k)
      (subspace_topology (I_set \<times> I_set) II_topology (?A k)) E TE Ft
      \<and> (\<forall>x\<in>?A k. p (Ft x) = F x) \<and> Ft (0, 0) = e0"
  proof (intro allI impI)
    fix k show "k \<le> m*n \<Longrightarrow> \<exists>Ft. top1_continuous_map_on (?A k)
        (subspace_topology (I_set \<times> I_set) II_topology (?A k)) E TE Ft
        \<and> (\<forall>x\<in>?A k. p (Ft x) = F x) \<and> Ft (0, 0) = e0"
    proof (induction k)
      case 0
      \<comment> \<open>A_0 = edges. Ft on edges: left_lift on left edge, bot_lift on bottom.\<close>
      define Ft0 where "Ft0 = (\<lambda>(s::real, t::real). if s = 0 then left_lift t else bot_lift s)"
      \<comment> \<open>Ft0(0,0) = left_lift 0 = e0.\<close>
      have hFt0_00: "Ft0 (0, 0) = e0"
      proof -
        have "Ft0 (0, 0) = left_lift 0" unfolding Ft0_def by simp
        also have "\<dots> = e0" using hll unfolding top1_is_path_on_def by simp
        finally show ?thesis .
      qed
      \<comment> \<open>Ft0 lifts F on A_0.\<close>
      have hbl_00: "bot_lift 0 = e0"
        using hbl unfolding top1_is_path_on_def by simp
      have hFt0_lift: "\<forall>x\<in>?A 0. p (Ft0 x) = F x"
      proof (intro ballI)
        fix x assume hx: "x \<in> ?A 0"
        obtain s t where hst: "x = (s, t)" by (cases x) simp
        have "x \<in> ?left_edge \<or> x \<in> ?bot_edge" using hx by simp
        thus "p (Ft0 x) = F x"
        proof (elim disjE)
          assume "x \<in> ?left_edge"
          hence hs0: "s = 0" and ht_I: "t \<in> I_set" using hst by (by100 auto)+
          have "Ft0 x = left_lift t" unfolding Ft0_def hst hs0 by simp
          thus ?thesis using hll_lift ht_I hst hs0 by simp
        next
          assume "x \<in> ?bot_edge"
          hence hs_I: "s \<in> I_set" and ht0: "t = 0" using hst by (by100 auto)+
          show ?thesis
          proof (cases "s = 0")
            case True
            have "Ft0 x = left_lift 0" unfolding Ft0_def hst True ht0 by simp
            also have "\<dots> = e0" using hll unfolding top1_is_path_on_def by simp
            finally have "Ft0 x = e0" .
            moreover have "F x = b0" using assms(5) hst True ht0 by simp
            moreover have "p e0 = b0" using assms(3) .
            ultimately show ?thesis by simp
          next
            case False
            have "Ft0 x = bot_lift s" unfolding Ft0_def hst ht0 using False by simp
            thus ?thesis using hbl_lift hs_I hst ht0 by simp
          qed
        qed
      qed
      \<comment> \<open>Ft0 is continuous on A_0. Use pasting lemma: left_lift on left edge, bot_lift on bottom.\<close>
      have hFt0_cont: "top1_continuous_map_on (?A 0)
          (subspace_topology (I_set \<times> I_set) II_topology (?A 0)) E TE Ft0"
      proof -
        let ?TA = "subspace_topology (I_set \<times> I_set) II_topology (?A 0)"
        \<comment> \<open>On left edge, Ft0 = left_lift \<circ> snd. On bot edge, Ft0 = bot_lift \<circ> fst.\<close>
        have hFt0_left: "\<forall>x\<in>?left_edge. Ft0 x = left_lift (snd x)"
          unfolding Ft0_def by (by100 auto)
        have hFt0_bot: "\<forall>x\<in>?bot_edge. Ft0 x = bot_lift (fst x)"
        proof (intro ballI)
          fix x assume "x \<in> ?bot_edge"
          then obtain s where hs: "s \<in> I_set" and hx: "x = (s, 0 :: real)" by (by100 blast)
          show "Ft0 x = bot_lift (fst x)"
          proof (cases "s = 0")
            case True
            hence "Ft0 x = left_lift 0" unfolding Ft0_def hx by simp
            also have "\<dots> = e0" using hll unfolding top1_is_path_on_def by simp
            also have "\<dots> = bot_lift 0" using hbl_00 by simp
            finally show ?thesis using hx True by simp
          next
            case False
            thus ?thesis unfolding Ft0_def hx by simp
          qed
        qed
        \<comment> \<open>They agree on the intersection (0,0).\<close>
        have hFt0_agree: "\<forall>x\<in>?left_edge \<inter> ?bot_edge. left_lift (snd x) = bot_lift (fst x)"
        proof (intro ballI)
          fix x assume "x \<in> ?left_edge \<inter> ?bot_edge"
          hence "x = (0 :: real, 0 :: real)" by (by100 auto)
          thus "left_lift (snd x) = bot_lift (fst x)"
            using hll hbl_00 unfolding top1_is_path_on_def by simp
        qed
        \<comment> \<open>Continuity via pasting lemma on two closed sets.\<close>
        have hITop: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        have hTII2: "is_topology_on (I_set \<times> I_set) II_topology"
          unfolding II_topology_def
          by (rule product_topology_on_is_topology_on[OF hITop hITop])
        have hA0_sub: "?A 0 \<subseteq> I_set \<times> I_set" using h0I by (by100 blast)
        have hTA: "is_topology_on (?A 0) ?TA"
          by (rule subspace_topology_is_topology_on[OF hTII2 hA0_sub])
        \<comment> \<open>Both edges are closed in A_0.\<close>
        have hle_cl_II: "closedin_on (I_set \<times> I_set) II_topology ?left_edge"
          unfolding closedin_on_def
        proof (intro conjI)
          show "?left_edge \<subseteq> I_set \<times> I_set" using h0I by (by100 blast)
          have "I_set \<times> I_set - ?left_edge = {s\<in>I_set. s > 0} \<times> I_set"
            unfolding top1_unit_interval_def by (by100 auto)
          also have "\<dots> \<in> II_topology"
          proof -
            have hI_open2: "I_set \<in> I_top"
              using hITop unfolding is_topology_on_def by (by100 blast)
            have "{s\<in>I_set. s > 0} = I_set \<inter> {s :: real. 0 < s}" by (by100 auto)
            also have "\<dots> \<in> I_top"
              unfolding top1_unit_interval_topology_def subspace_topology_def
              using open_greaterThan[of "0::real"] unfolding top1_open_sets_def greaterThan_def by (by100 blast)
            finally have "{s\<in>I_set. s > 0} \<in> I_top" .
            thus ?thesis unfolding II_topology_def by (rule product_rect_open[OF _ hI_open2])
          qed
          finally show "I_set \<times> I_set - ?left_edge \<in> II_topology" .
        qed
        have hbe_cl_II: "closedin_on (I_set \<times> I_set) II_topology ?bot_edge"
          unfolding closedin_on_def
        proof (intro conjI)
          show "?bot_edge \<subseteq> I_set \<times> I_set" using h0I by (by100 blast)
          have "I_set \<times> I_set - ?bot_edge = I_set \<times> {t\<in>I_set. t > 0}"
            unfolding top1_unit_interval_def by (by100 auto)
          also have "\<dots> \<in> II_topology"
          proof -
            have hI_open2: "I_set \<in> I_top"
              using hITop unfolding is_topology_on_def by (by100 blast)
            have "{t\<in>I_set. t > 0} = I_set \<inter> {t :: real. 0 < t}" by (by100 auto)
            also have "\<dots> \<in> I_top"
              unfolding top1_unit_interval_topology_def subspace_topology_def
              using open_greaterThan[of "0::real"] unfolding top1_open_sets_def greaterThan_def by (by100 blast)
            finally have "{t\<in>I_set. t > 0} \<in> I_top" .
            thus ?thesis unfolding II_topology_def by (rule product_rect_open[OF hI_open2])
          qed
          finally show "I_set \<times> I_set - ?bot_edge \<in> II_topology" .
        qed
        have hle_cl_A: "closedin_on (?A 0) ?TA ?left_edge"
        proof -
          have heq: "?left_edge = ?left_edge \<inter> ?A 0" by (by100 blast)
          have "\<exists>C. closedin_on (I_set \<times> I_set) II_topology C \<and> ?left_edge = C \<inter> ?A 0"
            using hle_cl_II heq by (by100 blast)
          thus ?thesis using Theorem_17_2[OF hTII2 hA0_sub] by simp
        qed
        have hbe_cl_A: "closedin_on (?A 0) ?TA ?bot_edge"
        proof -
          have heq: "?bot_edge = ?bot_edge \<inter> ?A 0" by (by100 blast)
          have "\<exists>C. closedin_on (I_set \<times> I_set) II_topology C \<and> ?bot_edge = C \<inter> ?A 0"
            using hbe_cl_II heq by (by100 blast)
          thus ?thesis using Theorem_17_2[OF hTII2 hA0_sub] by simp
        qed
        \<comment> \<open>pi2 continuous from I\<times>I to I.\<close>
        have hpi2: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top snd"
          unfolding II_topology_def
          by (rule top1_continuous_pi2[OF hITop hITop, unfolded pi2_def])
        have hleft_lift_cont: "top1_continuous_map_on I_set I_top E TE left_lift"
          using hll unfolding top1_is_path_on_def by simp
        have hleft_comp: "top1_continuous_map_on (I_set \<times> I_set) II_topology E TE (left_lift \<circ> snd)"
          by (rule top1_continuous_map_on_comp[OF hpi2 hleft_lift_cont])
        \<comment> \<open>Restrict to left edge.\<close>
        have hleft_edge_sub: "?left_edge \<subseteq> I_set \<times> I_set" using h0I by (by100 blast)
        have hleft_comp_le: "top1_continuous_map_on ?left_edge
            (subspace_topology (I_set \<times> I_set) II_topology ?left_edge) E TE (left_lift \<circ> snd)"
          using Theorem_18_2(4)[OF hTII2 assms(7) assms(7), rule_format]
            hleft_comp hleft_edge_sub by (by100 blast)
        have hle_sub_A: "?left_edge \<subseteq> ?A 0" by (by100 blast)
        have hleft_sub_eq: "subspace_topology (?A 0) ?TA ?left_edge
            = subspace_topology (I_set \<times> I_set) II_topology ?left_edge"
          using subspace_topology_trans[OF hle_sub_A] by simp
        have hleft_Ft0: "top1_continuous_map_on ?left_edge
            (subspace_topology (?A 0) ?TA ?left_edge) E TE Ft0"
          using top1_continuous_map_on_cong[OF hFt0_left] hleft_comp_le
          unfolding hleft_sub_eq comp_def by (by100 blast)
        \<comment> \<open>Similarly for bot edge.\<close>
        have hpi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top fst"
          unfolding II_topology_def
          by (rule top1_continuous_pi1[OF hITop hITop, unfolded pi1_def])
        have hbot_lift_cont: "top1_continuous_map_on I_set I_top E TE bot_lift"
          using hbl unfolding top1_is_path_on_def by simp
        have hbot_comp: "top1_continuous_map_on (I_set \<times> I_set) II_topology E TE (bot_lift \<circ> fst)"
          by (rule top1_continuous_map_on_comp[OF hpi1 hbot_lift_cont])
        have hbot_edge_sub: "?bot_edge \<subseteq> I_set \<times> I_set" using h0I by (by100 blast)
        have hbot_comp_be: "top1_continuous_map_on ?bot_edge
            (subspace_topology (I_set \<times> I_set) II_topology ?bot_edge) E TE (bot_lift \<circ> fst)"
          using Theorem_18_2(4)[OF hTII2 assms(7) assms(7), rule_format]
            hbot_comp hbot_edge_sub by (by100 blast)
        have hbe_sub_A: "?bot_edge \<subseteq> ?A 0" by (by100 blast)
        have hbot_sub_eq: "subspace_topology (?A 0) ?TA ?bot_edge
            = subspace_topology (I_set \<times> I_set) II_topology ?bot_edge"
          using subspace_topology_trans[OF hbe_sub_A] by simp
        have hbot_Ft0: "top1_continuous_map_on ?bot_edge
            (subspace_topology (?A 0) ?TA ?bot_edge) E TE Ft0"
          using top1_continuous_map_on_cong[OF hFt0_bot] hbot_comp_be
          unfolding hbot_sub_eq comp_def by (by100 blast)
        \<comment> \<open>Ft0 ranges into E.\<close>
        have hFt0_range: "\<forall>x\<in>?A 0. Ft0 x \<in> E"
        proof (intro ballI)
          fix x assume "x \<in> ?A 0"
          hence "x \<in> ?left_edge \<or> x \<in> ?bot_edge" by simp
          thus "Ft0 x \<in> E"
          proof (elim disjE)
            assume "x \<in> ?left_edge"
            hence "Ft0 x = left_lift (snd x)" using hFt0_left by (by100 blast)
            moreover have "snd x \<in> I_set" using \<open>x \<in> ?left_edge\<close> by (by100 auto)
            moreover have "\<forall>t\<in>I_set. left_lift t \<in> E"
              using hll unfolding top1_is_path_on_def top1_continuous_map_on_def by simp
            ultimately show ?thesis by simp
          next
            assume "x \<in> ?bot_edge"
            hence "Ft0 x = bot_lift (fst x)" using hFt0_bot by (by100 blast)
            moreover have "fst x \<in> I_set" using \<open>x \<in> ?bot_edge\<close> by (by100 auto)
            moreover have "\<forall>s\<in>I_set. bot_lift s \<in> E"
              using hbl unfolding top1_is_path_on_def top1_continuous_map_on_def by simp
            ultimately show ?thesis by simp
          qed
        qed
        \<comment> \<open>Apply pasting lemma.\<close>
        have hA0_union: "?left_edge \<union> ?bot_edge = ?A 0" by simp
        show ?thesis
          by (rule pasting_lemma_two_closed[OF hTA assms(7)
              hle_cl_A hbe_cl_A hA0_union hFt0_range hleft_Ft0 hbot_Ft0])
      qed
      show ?case
      proof (intro exI conjI)
        show "top1_continuous_map_on (?A 0)
            (subspace_topology (I_set \<times> I_set) II_topology (?A 0)) E TE Ft0"
          by (rule hFt0_cont)
        show "\<forall>x\<in>?A 0. p (Ft0 x) = F x" by (rule hFt0_lift)
        show "Ft0 (0, 0) = e0" by (rule hFt0_00)
      qed
    next
      case (Suc k)
      \<comment> \<open>IH: \<exists>Ft on A_k. Extend to A_{Suc k} = A_k \<union> R_{k mod m, k div m}.\<close>
      have hk: "k < m * n" using Suc.prems by simp
      let ?i = "k mod m" and ?j = "k div m"
      have hi: "?i < m" using hm by simp
      have hj: "?j < n"
      proof -
        have "k div m * m \<le> k" by simp
        hence "k div m * m < m * n" using hk by (by100 linarith)
        thus ?thesis using hm by (by100 simp)
      qed
      obtain Ft_prev where hprev_cont: "top1_continuous_map_on (?A k)
          (subspace_topology (I_set \<times> I_set) II_topology (?A k)) E TE Ft_prev"
          and hprev_lift: "\<forall>x\<in>?A k. p (Ft_prev x) = F x"
          and hprev_00: "Ft_prev (0, 0) = e0"
        using Suc.IH Suc.prems by auto
      \<comment> \<open>Get evenly covered U for rectangle (i,j).\<close>
      obtain U where hUo: "openin_on B TB U"
          and hUec: "top1_evenly_covered_on E TE B TB p U"
          and hFR: "F ` ?R ?i ?j \<subseteq> U"
        using hgrid[rule_format, OF hi hj] by (by100 auto)
      \<comment> \<open>A_k and R are closed in I\<times>I. A_k \<inter> R connected. A_k \<inter> R nonempty.\<close>
      have hA_closed: "closedin_on (I_set \<times> I_set) II_topology (?A k)"
      proof -
        have hTII_here: "is_topology_on (I_set \<times> I_set) II_topology"
          unfolding II_topology_def
          by (rule product_topology_on_is_topology_on[OF
              top1_unit_interval_topology_is_topology_on
              top1_unit_interval_topology_is_topology_on])
        have hI_open: "I_set \<in> I_top"
          using top1_unit_interval_topology_is_topology_on unfolding is_topology_on_def by (by100 blast)
        \<comment> \<open>Left edge {0} \<times> I_set is closed.\<close>
        have hle_closed: "closedin_on (I_set \<times> I_set) II_topology ({0::real} \<times> I_set)"
          unfolding closedin_on_def
        proof (intro conjI)
          show "{0::real} \<times> I_set \<subseteq> I_set \<times> I_set" using h0I by (by100 blast)
          have heq: "I_set \<times> I_set - {0::real} \<times> I_set = {s\<in>I_set. s > 0} \<times> I_set"
            unfolding top1_unit_interval_def by (by100 auto)
          have "{s\<in>I_set. s > 0} = I_set \<inter> {s :: real. 0 < s}" by (by100 auto)
          also have "\<dots> \<in> I_top"
            unfolding top1_unit_interval_topology_def subspace_topology_def
            using open_greaterThan[of "0::real"] unfolding top1_open_sets_def greaterThan_def by (by100 blast)
          finally have "{s\<in>I_set. s > 0} \<in> I_top" .
          thus "I_set \<times> I_set - {0::real} \<times> I_set \<in> II_topology"
            unfolding heq II_topology_def by (rule product_rect_open[OF _ hI_open])
        qed
        \<comment> \<open>Bottom edge I_set \<times> {0} is closed.\<close>
        have hbe_closed: "closedin_on (I_set \<times> I_set) II_topology (I_set \<times> {0::real})"
          unfolding closedin_on_def
        proof (intro conjI)
          show "I_set \<times> {0::real} \<subseteq> I_set \<times> I_set" using h0I by (by100 blast)
          have heq: "I_set \<times> I_set - I_set \<times> {0::real} = I_set \<times> {t\<in>I_set. t > 0}"
            unfolding top1_unit_interval_def by (by100 auto)
          have "{t\<in>I_set. t > 0} = I_set \<inter> {t :: real. 0 < t}" by (by100 auto)
          also have "\<dots> \<in> I_top"
            unfolding top1_unit_interval_topology_def subspace_topology_def
            using open_greaterThan[of "0::real"] unfolding top1_open_sets_def greaterThan_def by (by100 blast)
          finally have "{t\<in>I_set. t > 0} \<in> I_top" .
          thus "I_set \<times> I_set - I_set \<times> {0::real} \<in> II_topology"
            unfolding heq II_topology_def by (rule product_rect_open[OF hI_open])
        qed
        \<comment> \<open>Edges are closed.\<close>
        have hedge_closed: "closedin_on (I_set \<times> I_set) II_topology ?edges"
        proof -
          have "\<forall>A\<in>{?left_edge, ?bot_edge}. closedin_on (I_set \<times> I_set) II_topology A"
            using hle_closed hbe_closed by (by100 blast)
          hence "closedin_on (I_set \<times> I_set) II_topology (\<Union>{?left_edge, ?bot_edge})"
            by (rule closedin_on_finite_Union[OF hTII_here _ finite.insertI[OF finite.insertI[OF finite.emptyI]]])
          thus ?thesis by simp
        qed
        \<comment> \<open>Each rectangle is closed.\<close>
        have hrect_closed: "\<forall>k'<k. closedin_on (I_set \<times> I_set) II_topology (?R (k' mod m) (k' div m))"
        proof (intro allI impI)
          fix k' assume hk'_lt: "k' < k"
          have hk'_lt_mn: "k' < m * n" using hk'_lt hk by simp
          have "k' mod m < m" using hm by simp
          have "k' div m < n"
          proof -
            have "m > 0" using hm by simp
            hence "k' div m < n \<longleftrightarrow> k' < n * m"
              using div_less_iff_less_mult[of m k' n] by simp
            thus ?thesis using hk'_lt_mn by (simp add: mult.commute)
          qed
          have "sub_s (k' mod m) \<le> sub_s (Suc (k' mod m))"
            using hs_inc[rule_format, OF \<open>k' mod m < m\<close>] by simp
          moreover have "sub_t (k' div m) \<le> sub_t (Suc (k' div m))"
            using ht_inc[rule_format, OF \<open>k' div m < n\<close>] by simp
          ultimately show "closedin_on (I_set \<times> I_set) II_topology (?R (k' mod m) (k' div m))"
            using closedin_II_rectangle by simp
        qed
        \<comment> \<open>Finite union of rectangles is closed.\<close>
        have "finite {k'. k' < k}" by simp
        have hrects_closed: "closedin_on (I_set \<times> I_set) II_topology (\<Union>k'<k. ?R (k' mod m) (k' div m))"
        proof -
          let ?F = "{?R (k' mod m) (k' div m) | k'. k' < k}"
          have hfin: "finite ?F" by simp
          have hcl: "\<forall>A\<in>?F. closedin_on (I_set \<times> I_set) II_topology A"
          proof (intro ballI)
            fix A assume "A \<in> ?F"
            then obtain k' where hk': "k' < k" and hAeq: "A = ?R (k' mod m) (k' div m)" by (by100 blast)
            show "closedin_on (I_set \<times> I_set) II_topology A"
              using hrect_closed[rule_format, OF hk'] hAeq by simp
          qed
          have "closedin_on (I_set \<times> I_set) II_topology (\<Union>?F)"
            by (rule closedin_on_finite_Union[OF hTII_here hcl hfin])
          moreover have "\<Union>?F = (\<Union>k'<k. ?R (k' mod m) (k' div m))" by (by100 blast)
          ultimately show ?thesis by simp
        qed
        \<comment> \<open>A_k = edges \<union> rectangles.\<close>
        have "\<forall>A\<in>{?edges, \<Union>k'<k. ?R (k' mod m) (k' div m)}. closedin_on (I_set \<times> I_set) II_topology A"
          using hedge_closed hrects_closed by (by100 blast)
        hence "closedin_on (I_set \<times> I_set) II_topology (\<Union>{?edges, \<Union>k'<k. ?R (k' mod m) (k' div m)})"
          by (rule closedin_on_finite_Union[OF hTII_here _ finite.insertI[OF finite.insertI[OF finite.emptyI]]])
        thus ?thesis by simp
      qed
      have hR_closed: "closedin_on (I_set \<times> I_set) II_topology (?R ?i ?j)"
        using closedin_II_rectangle[of "sub_s ?i" "sub_s (Suc ?i)" "sub_t ?j" "sub_t (Suc ?j)"]
              hs_inc[rule_format, OF hi] ht_inc[rule_format, OF hj] by (by100 linarith)
      have hAR_sub: "?A k \<union> ?R ?i ?j \<subseteq> I_set \<times> I_set"
      proof -
        have "{0::real} \<times> I_set \<subseteq> I_set \<times> I_set" using h0I by (by100 blast)
        moreover have "I_set \<times> {0::real} \<subseteq> I_set \<times> I_set" using h0I by (by100 blast)
        moreover have "\<forall>k'. ?R (k' mod m) (k' div m) \<subseteq> I_set \<times> I_set" by (by100 blast)
        moreover have "?R ?i ?j \<subseteq> I_set \<times> I_set" by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      have hC_conn: "top1_connected_on (?A k \<inter> ?R ?i ?j)
          (subspace_topology (I_set \<times> I_set) II_topology (?A k \<inter> ?R ?i ?j))"
      proof -
        \<comment> \<open>The boundary C = A_k \<inter> R is the left \<union> bottom edges of the rectangle.
           Textbook (Munkres p.340): "this set is the union of the left and bottom
           edges of the rectangle I_{i_0} \<times> J_{j_0}, so it is connected."\<close>
        let ?left_R = "{sub_s ?i} \<times> {t\<in>I_set. sub_t ?j \<le> t \<and> t \<le> sub_t (Suc ?j)}"
        let ?bot_R = "{s\<in>I_set. sub_s ?i \<le> s \<and> s \<le> sub_s (Suc ?i)} \<times> {sub_t ?j}"
        let ?L_shape = "?left_R \<union> ?bot_R"
        have hsi_I': "sub_s ?i \<in> I_set" using hsub_s_I[rule_format, of "?i"] hi by simp
        have htj_I': "sub_t ?j \<in> I_set" using hsub_t_I[rule_format, of "?j"] hj by simp
        have hsi1_I: "sub_s (Suc ?i) \<in> I_set" using hsub_s_I[rule_format, of "Suc ?i"] hi by simp
        have htj1_I: "sub_t (Suc ?j) \<in> I_set" using hsub_t_I[rule_format, of "Suc ?j"] hj by simp
        have hsi_le': "sub_s ?i \<le> sub_s (Suc ?i)" using hs_inc[rule_format, OF hi] by simp
        have htj_le': "sub_t ?j \<le> sub_t (Suc ?j)" using ht_inc[rule_format, OF hj] by simp
        \<comment> \<open>The L-shape equals A_k \<inter> R.\<close>
        have hC_eq: "?A k \<inter> ?R ?i ?j = ?L_shape"
        proof (rule equalityI)
          \<comment> \<open>L-shape \<subseteq> A_k \<inter> R: both edges are in R by definition; left edge is in A_k
             (either via left edge {0}\<times>I if i=0, or via previous rectangle R(i-1,j));
             bottom edge is in A_k (either via bottom edge I\<times>{0} if j=0, or via R(i,j-1)).\<close>
          show "?L_shape \<subseteq> ?A k \<inter> ?R ?i ?j"
          proof (rule subsetI)
            fix x assume "x \<in> ?L_shape"
            hence "x \<in> ?left_R \<or> x \<in> ?bot_R" by (by100 blast)
            thus "x \<in> ?A k \<inter> ?R ?i ?j"
            proof (elim disjE)
              assume hx_left: "x \<in> ?left_R"
              \<comment> \<open>x is on left edge of R, so x \<in> R.\<close>
              have "x \<in> ?R ?i ?j"
                using hx_left hsi_I' hsi_le' by (by100 blast)
              moreover have "x \<in> ?A k"
              proof (cases "?i = 0")
                case True
                hence "sub_s ?i = 0" using hs0 by simp
                hence "x \<in> ?left_edge" using hx_left by (by100 auto)
                thus ?thesis by (by100 blast)
              next
                case False
                hence hi_pos: "?i > 0" by simp
                \<comment> \<open>x is in R(i-1, j) (previous rectangle in same row).\<close>
                have hSuc_i: "Suc (?i - 1) = ?i" using hi_pos by simp
                have "k - 1 < k" using hi_pos by (cases k) simp_all
                have hk'_mod: "(k - 1) mod m = ?i - 1"
                proof -
                  have hk'_eq: "k - 1 = ?j * m + (?i - 1)" using hi_pos by simp
                  have "?i - 1 < m" using hi by simp
                  thus ?thesis using hk'_eq by (metis mod_less mod_mult_self3)
                qed
                have hk'_div: "(k - 1) div m = ?j"
                proof -
                  have hk'_eq: "k - 1 = ?j * m + (?i - 1)" using hi_pos by simp
                  have "?i - 1 < m" using hi by simp
                  have hm0: "m \<noteq> 0" using hm by simp
                  have "(?j * m + (?i - 1)) div m = ?j + (?i - 1) div m"
                    using hm0 by (rule div_mult_self3)
                  also have "(?i - 1) div m = 0" using \<open>?i - 1 < m\<close> by simp
                  finally show ?thesis using hk'_eq by simp
                qed
                have "x \<in> ?R (?i - 1) ?j"
                proof -
                  obtain s t where hst: "x = (s, t)" by (cases x) simp
                  have "s = sub_s ?i" using hx_left hst by (by100 auto)
                  have "t \<in> I_set" "sub_t ?j \<le> t" "t \<le> sub_t (Suc ?j)"
                    using hx_left hst by (by100 auto)+
                  have "sub_s (?i - 1) \<le> sub_s ?i"
                  proof -
                    have "sub_s (?i - 1) < sub_s (Suc (?i - 1))"
                      using hs_inc[rule_format, of "?i - 1"] hi by simp
                    thus ?thesis using hSuc_i by simp
                  qed
                  have "sub_s ?i \<le> sub_s (Suc (?i - 1))" using hSuc_i by simp
                  have "sub_s ?i \<in> I_set" using hsi_I' .
                  have "s \<in> {s'\<in>I_set. sub_s (?i - 1) \<le> s' \<and> s' \<le> sub_s (Suc (?i - 1))}"
                    using \<open>s = sub_s ?i\<close> \<open>sub_s ?i \<in> I_set\<close>
                        \<open>sub_s (?i - 1) \<le> sub_s ?i\<close> \<open>sub_s ?i \<le> sub_s (Suc (?i - 1))\<close>
                    by simp
                  moreover have "t \<in> {t'\<in>I_set. sub_t ?j \<le> t' \<and> t' \<le> sub_t (Suc ?j)}"
                    using \<open>t \<in> I_set\<close> \<open>sub_t ?j \<le> t\<close> \<open>t \<le> sub_t (Suc ?j)\<close> by simp
                  ultimately show ?thesis using hst by (by100 blast)
                qed
                hence "x \<in> ?R ((k-1) mod m) ((k-1) div m)"
                  using hk'_mod hk'_div by simp
                hence "x \<in> (\<Union>k'<k. ?R (k' mod m) (k' div m))"
                  using \<open>k - 1 < k\<close> by (by100 blast)
                thus ?thesis by (by100 blast)
              qed
              ultimately show ?thesis by (by100 blast)
            next
              assume hx_bot: "x \<in> ?bot_R"
              have "x \<in> ?R ?i ?j"
                using hx_bot htj_I' htj_le' by (by100 blast)
              moreover have "x \<in> ?A k"
              proof (cases "?j = 0")
                case True
                hence "sub_t ?j = 0" using ht0 by simp
                hence "x \<in> ?bot_edge" using hx_bot by (by100 auto)
                thus ?thesis by (by100 blast)
              next
                case False
                hence hj_pos: "?j > 0" by simp
                \<comment> \<open>x is in R(i, j-1) (rectangle in row below).\<close>
                have hSuc_j: "Suc (?j - 1) = ?j" using hj_pos by simp
                \<comment> \<open>Linearized index of (i, j-1) is (j-1)*m + i = k - m.\<close>
                have hk'_val: "k - m = (?j - 1) * m + ?i" using hj_pos by (simp add: diff_mult_distrib)
                have "k \<ge> m"
                proof -
                  have "m \<le> 1 * m" by simp
                  also have "1 * m \<le> ?j * m" using hj_pos by simp
                  also have "?j * m \<le> ?j * m + ?i" by simp
                  also have "?j * m + ?i = k" by simp
                  finally show ?thesis .
                qed
                have hk'_lt: "k - m < k" using hm \<open>k \<ge> m\<close> by simp
                have hk'_mod: "(k - m) mod m = ?i"
                proof -
                  have "?i < m" using hi .
                  thus ?thesis using hk'_val by (metis mod_less mod_mult_self3)
                qed
                have hk'_div: "(k - m) div m = ?j - 1"
                proof -
                  have "?i < m" using hi .
                  have hm0: "m \<noteq> 0" using hm by simp
                  have "((?j - 1) * m + ?i) div m = (?j - 1) + ?i div m"
                    using hm0 by (rule div_mult_self3)
                  also have "?i div m = 0" using \<open>?i < m\<close> by simp
                  finally show ?thesis using hk'_val by simp
                qed
                have "x \<in> ?R ?i (?j - 1)"
                proof -
                  obtain s t where hst: "x = (s, t)" by (cases x) simp
                  have "t = sub_t ?j" using hx_bot hst by (by100 auto)
                  have "s \<in> I_set" "sub_s ?i \<le> s" "s \<le> sub_s (Suc ?i)"
                    using hx_bot hst by (by100 auto)+
                  have "sub_t (?j - 1) \<le> sub_t ?j"
                  proof -
                    have "sub_t (?j - 1) < sub_t (Suc (?j - 1))"
                      using ht_inc[rule_format, of "?j - 1"] hj by simp
                    thus ?thesis using hSuc_j by simp
                  qed
                  have "sub_t ?j \<le> sub_t (Suc (?j - 1))" using hSuc_j by simp
                  have "s \<in> {s'\<in>I_set. sub_s ?i \<le> s' \<and> s' \<le> sub_s (Suc ?i)}"
                    using \<open>s \<in> I_set\<close> \<open>sub_s ?i \<le> s\<close> \<open>s \<le> sub_s (Suc ?i)\<close> by simp
                  moreover have "t \<in> {t'\<in>I_set. sub_t (?j - 1) \<le> t' \<and> t' \<le> sub_t (Suc (?j - 1))}"
                    using \<open>t = sub_t ?j\<close> htj_I' \<open>sub_t (?j - 1) \<le> sub_t ?j\<close>
                        \<open>sub_t ?j \<le> sub_t (Suc (?j - 1))\<close> by simp
                  ultimately show ?thesis using hst by (by100 blast)
                qed
                hence "x \<in> ?R ((k - m) mod m) ((k - m) div m)"
                  using hk'_mod hk'_div by simp
                hence "x \<in> (\<Union>k'<k. ?R (k' mod m) (k' div m))"
                  using hk'_lt by (by100 blast)
                thus ?thesis by (by100 blast)
              qed
              ultimately show ?thesis by (by100 blast)
            qed
          qed
        next
          \<comment> \<open>A_k \<inter> R \<subseteq> L-shape: interior of R is not in any previous region.
             A point (s,t) with sub_s i < s and sub_t j < t cannot be on edges or
             in any previous rectangle.\<close>
          show "?A k \<inter> ?R ?i ?j \<subseteq> ?L_shape"
          proof (rule subsetI)
            fix x assume hx: "x \<in> ?A k \<inter> ?R ?i ?j"
            obtain s t where hst: "x = (s, t)" by (cases x) simp
            have hx_R: "x \<in> ?R ?i ?j" using hx by (by100 blast)
            have hs_I: "s \<in> I_set" using hx_R hst by simp
            have hsi_le_s: "sub_s ?i \<le> s" using hx_R hst by simp
            have hs_le_si1: "s \<le> sub_s (Suc ?i)" using hx_R hst by simp
            have ht_I: "t \<in> I_set" using hx_R hst by simp
            have htj_le_t: "sub_t ?j \<le> t" using hx_R hst by simp
            have ht_le_tj1: "t \<le> sub_t (Suc ?j)" using hx_R hst by simp
            have hx_A: "x \<in> ?A k" using hx by (by100 blast)
            \<comment> \<open>If s = sub_s i, then x is on the left edge of R.\<close>
            \<comment> \<open>If t = sub_t j, then x is on the bottom edge of R.\<close>
            \<comment> \<open>If s > sub_s i AND t > sub_t j, then x is in the interior of R.\<close>
            show "x \<in> ?L_shape"
            proof (cases "s = sub_s ?i")
              case True thus ?thesis using ht_I htj_le_t ht_le_tj1 hst by (by100 blast)
            next
              case False
              hence hs_gt: "s > sub_s ?i" using hsi_le_s by simp
              show ?thesis
              proof (cases "t = sub_t ?j")
                case True thus ?thesis using hs_I hsi_le_s hs_le_si1 hst by (by100 blast)
              next
                case False
                hence ht_gt: "t > sub_t ?j" using htj_le_t by simp
                \<comment> \<open>Contradiction: (s,t) with s > sub_s i, t > sub_t j cannot be in A_k.\<close>
                have "\<not> (x \<in> ?left_edge)" using hs_gt hst hs0
                proof -
                  have "s > 0" using hs_gt hsub_s_mono[rule_format, of 0 "?i"] hs0 hi by simp
                  thus ?thesis using hst by (by100 auto)
                qed
                have "\<not> (x \<in> ?bot_edge)" using ht_gt hst ht0
                proof -
                  have "t > 0" using ht_gt hsub_t_mono[rule_format, of 0 "?j"] ht0 hj by simp
                  thus ?thesis using hst by (by100 auto)
                qed
                have "\<not> (\<exists>k'<k. x \<in> ?R (k' mod m) (k' div m))"
                proof (rule notI)
                  assume "\<exists>k'<k. x \<in> ?R (k' mod m) (k' div m)"
                  then obtain k' where hk'_lt: "k' < k"
                      and hx_R': "x \<in> ?R (k' mod m) (k' div m)" by (by100 blast)
                  let ?i' = "k' mod m" and ?j' = "k' div m"
                  have hi': "?i' < m" using hm by simp
                  have "s \<le> sub_s (Suc ?i')" using hx_R' hst by (by100 auto)
                  have "t \<le> sub_t (Suc ?j')" using hx_R' hst by (by100 auto)
                  have "sub_s ?i' \<le> s" using hx_R' hst by (by100 auto)
                  have "sub_t ?j' \<le> t" using hx_R' hst by (by100 auto)
                  \<comment> \<open>k' < k = j*m + i. Either j' < j, or j' = j and i' < i.\<close>
                  have "?j' < ?j \<or> (?j' = ?j \<and> ?i' < ?i)"
                  proof -
                    have "k' = ?j' * m + ?i'" by simp
                    have "k = ?j * m + ?i" by simp
                    show ?thesis
                    proof (cases "?j' < ?j")
                      case True thus ?thesis by simp
                    next
                      case False
                      have "?j' \<le> ?j"
                      proof -
                        have "?j' * m \<le> k'" by simp
                        also have "k' < k" using hk'_lt .
                        also have "k = ?j * m + ?i" by simp
                        also have "?j * m + ?i < ?j * m + m" using hi by (by100 linarith)
                        also have "?j * m + m = (?j + 1) * m" by (simp add: algebra_simps)
                        finally have "?j' * m < (?j + 1) * m" .
                        thus ?thesis
                        proof -
                          assume "?j' * m < (?j + 1) * m"
                          hence "?j' < ?j + 1"
                          proof -
                            assume h: "?j' * m < (?j + 1) * m"
                            have "m > 0" using hm by simp
                            thus ?thesis using h by (metis mult_less_cancel2)
                          qed
                          thus ?thesis by simp
                        qed
                      qed
                      hence "?j' = ?j" using False by simp
                      moreover have "?i' < ?i"
                      proof -
                        have "k' = ?j' * m + ?i'" by simp
                        hence hk'_eq: "k' = ?j * m + ?i'" using \<open>?j' = ?j\<close> by simp
                        have hk_eq2: "k = ?j * m + ?i" by simp
                        show ?thesis using hk'_lt hk'_eq hk_eq2 by (by100 linarith)
                      qed
                      ultimately show ?thesis by simp
                    qed
                  qed
                  thus False
                  proof (elim disjE conjE)
                    assume hj'_lt: "?j' < ?j"
                    \<comment> \<open>Then sub_t (Suc j') \<le> sub_t j < t, contradicting t \<le> sub_t (Suc j').\<close>
                    have "sub_t (Suc ?j') \<le> sub_t ?j"
                      using hsub_t_mono[rule_format, of "Suc ?j'" "?j"] hj'_lt hj by simp
                    hence "t \<le> sub_t ?j" using \<open>t \<le> sub_t (Suc ?j')\<close> by simp
                    thus False using ht_gt by simp
                  next
                    assume "?j' = ?j" and hi'_lt: "?i' < ?i"
                    \<comment> \<open>Then sub_s (Suc i') \<le> sub_s i < s, contradicting s \<le> sub_s (Suc i').\<close>
                    have "sub_s (Suc ?i') \<le> sub_s ?i"
                      using hsub_s_mono[rule_format, of "Suc ?i'" "?i"] hi'_lt hi by simp
                    hence "s \<le> sub_s ?i" using \<open>s \<le> sub_s (Suc ?i')\<close> by simp
                    thus False using hs_gt by simp
                  qed
                qed
                hence "x \<notin> ?A k" using \<open>\<not> (x \<in> ?left_edge)\<close> \<open>\<not> (x \<in> ?bot_edge)\<close>
                  by (by100 blast)
                thus ?thesis using hx_A by contradiction
              qed
            qed
          qed
        qed
        \<comment> \<open>The L-shape is connected: two intervals sharing the corner point (Theorem 23.3).\<close>
        have hTII_loc: "is_topology_on (I_set \<times> I_set) II_topology"
          unfolding II_topology_def
          by (rule product_topology_on_is_topology_on[OF
              top1_unit_interval_topology_is_topology_on
              top1_unit_interval_topology_is_topology_on])
        \<comment> \<open>Left edge is connected (vertical interval): {sub_s i} \<times> [sub_t j, sub_t (j+1)].\<close>
        have hITop: "is_topology_on I_set I_top"
          by (rule top1_unit_interval_topology_is_topology_on)
        have hleft_conn: "top1_connected_on ?left_R
            (subspace_topology (I_set \<times> I_set) II_topology ?left_R)"
        proof -
          let ?S1 = "{sub_s ?i}" and ?S2 = "{t\<in>I_set. sub_t ?j \<le> t \<and> t \<le> sub_t (Suc ?j)}"
          have hS1_conn: "top1_connected_on ?S1 (subspace_topology I_set I_top ?S1)"
            by (rule top1_connected_on_singleton[OF hITop hsi_I'])
          have hS2_eq: "?S2 = {sub_t ?j .. sub_t (Suc ?j)}"
          proof (rule set_eqI)
            fix t show "(t \<in> ?S2) = (t \<in> {sub_t ?j .. sub_t (Suc ?j)})"
            proof
              assume "t \<in> ?S2" thus "t \<in> {sub_t ?j .. sub_t (Suc ?j)}" by simp
            next
              assume ht_cc: "t \<in> {sub_t ?j .. sub_t (Suc ?j)}"
              hence "sub_t ?j \<le> t" "t \<le> sub_t (Suc ?j)" by simp_all
              moreover have "t \<in> I_set"
              proof -
                have "0 \<le> sub_t ?j" using htj_I' unfolding top1_unit_interval_def by simp
                have "sub_t (Suc ?j) \<le> 1" using htj1_I unfolding top1_unit_interval_def by simp
                show ?thesis unfolding top1_unit_interval_def
                  using \<open>sub_t ?j \<le> t\<close> \<open>t \<le> sub_t (Suc ?j)\<close> \<open>0 \<le> sub_t ?j\<close> \<open>sub_t (Suc ?j) \<le> 1\<close>
                  by simp
              qed
              ultimately show "t \<in> ?S2" by (by100 blast)
            qed
          qed
          have hS2_conn: "top1_connected_on ?S2 (subspace_topology I_set I_top ?S2)"
          proof -
            have "connected ?S2" unfolding hS2_eq by (rule connected_Icc)
            hence "top1_connected_on ?S2 (subspace_topology UNIV top1_open_sets ?S2)"
              by (rule top1_connected_on_subspace_openI)
            moreover have "subspace_topology I_set I_top ?S2 = subspace_topology UNIV top1_open_sets ?S2"
            proof -
              have "?S2 \<subseteq> I_set" by (by100 blast)
              hence "subspace_topology I_set (subspace_topology UNIV top1_open_sets I_set) ?S2
                  = subspace_topology UNIV top1_open_sets ?S2"
                by (rule subspace_topology_trans)
              thus ?thesis unfolding top1_unit_interval_topology_def by simp
            qed
            ultimately show ?thesis by simp
          qed
          have "top1_connected_on (?S1 \<times> ?S2)
              (product_topology_on (subspace_topology I_set I_top ?S1) (subspace_topology I_set I_top ?S2))"
            by (rule Theorem_23_6[OF
                subspace_topology_is_topology_on[OF hITop] subspace_topology_is_topology_on[OF hITop]
                hS1_conn hS2_conn])
              (simp_all add: hsi_I' htj_I' htj_le')
          moreover have "product_topology_on (subspace_topology I_set I_top ?S1) (subspace_topology I_set I_top ?S2)
              = subspace_topology (I_set \<times> I_set) (product_topology_on I_top I_top) (?S1 \<times> ?S2)"
            by (rule Theorem_16_3[OF hITop hITop])
          moreover have "product_topology_on I_top I_top = II_topology"
            unfolding II_topology_def by simp
          ultimately show ?thesis by simp
        qed
        \<comment> \<open>Bottom edge is connected (horizontal interval): [sub_s i, sub_s (i+1)] \<times> {sub_t j}.\<close>
        have hbot_conn: "top1_connected_on ?bot_R
            (subspace_topology (I_set \<times> I_set) II_topology ?bot_R)"
        proof -
          let ?S1 = "{s\<in>I_set. sub_s ?i \<le> s \<and> s \<le> sub_s (Suc ?i)}" and ?S2 = "{sub_t ?j}"
          have hS1_eq: "?S1 = {sub_s ?i .. sub_s (Suc ?i)}"
          proof (rule set_eqI)
            fix s show "(s \<in> ?S1) = (s \<in> {sub_s ?i .. sub_s (Suc ?i)})"
            proof
              assume "s \<in> ?S1" thus "s \<in> {sub_s ?i .. sub_s (Suc ?i)}" by simp
            next
              assume "s \<in> {sub_s ?i .. sub_s (Suc ?i)}"
              hence "sub_s ?i \<le> s" "s \<le> sub_s (Suc ?i)" by simp_all
              moreover have "s \<in> I_set"
              proof -
                have "0 \<le> sub_s ?i" using hsi_I' unfolding top1_unit_interval_def by simp
                have "sub_s (Suc ?i) \<le> 1" using hsi1_I unfolding top1_unit_interval_def by simp
                show ?thesis unfolding top1_unit_interval_def
                  using \<open>sub_s ?i \<le> s\<close> \<open>s \<le> sub_s (Suc ?i)\<close> \<open>0 \<le> sub_s ?i\<close> \<open>sub_s (Suc ?i) \<le> 1\<close>
                  by simp
              qed
              ultimately show "s \<in> ?S1" by (by100 blast)
            qed
          qed
          have hS1_conn: "top1_connected_on ?S1 (subspace_topology I_set I_top ?S1)"
          proof -
            have "connected ?S1" unfolding hS1_eq by (rule connected_Icc)
            hence "top1_connected_on ?S1 (subspace_topology UNIV top1_open_sets ?S1)"
              by (rule top1_connected_on_subspace_openI)
            moreover have "subspace_topology I_set I_top ?S1 = subspace_topology UNIV top1_open_sets ?S1"
            proof -
              have "?S1 \<subseteq> I_set" by (by100 blast)
              hence "subspace_topology I_set (subspace_topology UNIV top1_open_sets I_set) ?S1
                  = subspace_topology UNIV top1_open_sets ?S1"
                by (rule subspace_topology_trans)
              thus ?thesis unfolding top1_unit_interval_topology_def by simp
            qed
            ultimately show ?thesis by simp
          qed
          have hS2_conn: "top1_connected_on ?S2 (subspace_topology I_set I_top ?S2)"
            by (rule top1_connected_on_singleton[OF hITop htj_I'])
          have "top1_connected_on (?S1 \<times> ?S2)
              (product_topology_on (subspace_topology I_set I_top ?S1) (subspace_topology I_set I_top ?S2))"
            by (rule Theorem_23_6[OF
                subspace_topology_is_topology_on[OF hITop] subspace_topology_is_topology_on[OF hITop]
                hS1_conn hS2_conn])
              (simp_all add: htj_I' hsi_I' hsi_le')
          moreover have "product_topology_on (subspace_topology I_set I_top ?S1) (subspace_topology I_set I_top ?S2)
              = subspace_topology (I_set \<times> I_set) (product_topology_on I_top I_top) (?S1 \<times> ?S2)"
            by (rule Theorem_16_3[OF hITop hITop])
          moreover have "product_topology_on I_top I_top = II_topology"
            unfolding II_topology_def by simp
          ultimately show ?thesis by simp
        qed
        \<comment> \<open>They share the corner point.\<close>
        have hcorner_left: "(sub_s ?i, sub_t ?j) \<in> ?left_R"
          using hsi_I' htj_I' htj_le' by (by100 blast)
        have hcorner_bot: "(sub_s ?i, sub_t ?j) \<in> ?bot_R"
          using hsi_I' htj_I' hsi_le' by (by100 blast)
        have hcorner_inter: "(sub_s ?i, sub_t ?j) \<in> ?left_R \<inter> ?bot_R"
          using hcorner_left hcorner_bot by (by100 blast)
        \<comment> \<open>Both edges are subsets of I\<times>I.\<close>
        have hleft_sub: "?left_R \<subseteq> I_set \<times> I_set" using hsi_I' by (by100 blast)
        have hbot_sub: "?bot_R \<subseteq> I_set \<times> I_set" using htj_I' by (by100 blast)
        \<comment> \<open>Apply Theorem 23.3 with I = {0, 1}, A 0 = left_R, A 1 = bot_R.\<close>
        define A where "A = (\<lambda>i::nat. if i = 0 then ?left_R else ?bot_R)"
        have hA_sub: "\<forall>i\<in>{0::nat, 1}. A i \<subseteq> I_set \<times> I_set"
          unfolding A_def using hleft_sub hbot_sub by (by100 auto)
        have hA_conn: "\<forall>i\<in>{0::nat, 1}. top1_connected_on (A i)
            (subspace_topology (I_set \<times> I_set) II_topology (A i))"
          unfolding A_def using hleft_conn hbot_conn by (by100 auto)
        have hA_inter: "(sub_s ?i, sub_t ?j) \<in> \<Inter>(A ` {0::nat, 1})"
          unfolding A_def using hcorner_left hcorner_bot by (by100 auto)
        have "top1_connected_on (\<Union>i\<in>{0::nat, 1}. A i)
            (subspace_topology (I_set \<times> I_set) II_topology (\<Union>i\<in>{0::nat, 1}. A i))"
          by (rule Theorem_23_3[OF hTII_loc _ hA_sub hA_conn hA_inter]) simp
        moreover have "(\<Union>i\<in>{0::nat, 1}. A i) = ?L_shape"
          unfolding A_def by (by100 auto)
        ultimately have hL_conn: "top1_connected_on ?L_shape
            (subspace_topology (I_set \<times> I_set) II_topology ?L_shape)" by simp
        show ?thesis using hC_eq hL_conn by simp
      qed
      have hC_ne: "?A k \<inter> ?R ?i ?j \<noteq> {}"
      proof -
        \<comment> \<open>The corner point (sub_s i, sub_t j) is in both A_k and R.\<close>
        have hsi_I: "sub_s ?i \<in> I_set" using hsub_s_I[rule_format, of "?i"] hi by simp
        have htj_I: "sub_t ?j \<in> I_set" using hsub_t_I[rule_format, of "?j"] hj by simp
        have hsi_lt: "sub_s ?i < sub_s (Suc ?i)" using hs_inc[rule_format, OF hi] .
        have hsi_le: "sub_s ?i \<le> sub_s (Suc ?i)" using hsi_lt by simp
        have htj_lt: "sub_t ?j < sub_t (Suc ?j)" using ht_inc[rule_format, OF hj] .
        have htj_le: "sub_t ?j \<le> sub_t (Suc ?j)" using htj_lt by simp
        have hcorner_R: "(sub_s ?i, sub_t ?j) \<in> ?R ?i ?j"
          using hsi_I htj_I hsi_le htj_le by (by100 blast)
        have hcorner_A: "(sub_s ?i, sub_t ?j) \<in> ?A k"
        proof (cases "?i = 0")
          case True
          hence "sub_s ?i = 0" using hs0 by simp
          hence "(sub_s ?i, sub_t ?j) \<in> {0::real} \<times> I_set" using htj_I by (by100 blast)
          thus ?thesis by (by100 blast)
        next
          case False
          hence hi_pos: "?i > 0" by simp
          \<comment> \<open>The rectangle at (i-1, j) is previous (index k-1 < k).\<close>
          let ?k' = "k - 1"
          have hk_pos: "k > 0" using hi_pos by (cases k) simp_all
          have "?k' < k" using hk_pos by simp
          have hk_eq: "k = ?j * m + ?i" by simp
          have hk'_eq: "?k' = ?j * m + (?i - 1)" using hi_pos hk_eq by simp
          have hi_1_lt: "?i - 1 < m" using hi by simp
          have hk'_mod: "?k' mod m = ?i - 1"
          proof -
            have "(?j * m + (?i - 1)) mod m = (?i - 1) mod m"
              by (rule mod_mult_self3)
            also have "\<dots> = ?i - 1" using hi_1_lt by simp
            finally show ?thesis using hk'_eq by simp
          qed
          have hk'_div: "?k' div m = ?j"
          proof -
            have hm0: "m \<noteq> 0" using hm by simp
            have "(?j * m + (?i - 1)) div m = ?j + (?i - 1) div m"
              using hm0 by (rule div_mult_self3)
            also have "(?i - 1) div m = 0" using hi_1_lt by simp
            finally show ?thesis using hk'_eq by simp
          qed
          \<comment> \<open>Corner is in R(i-1, j) because sub_s(i-1) \<le> sub_s(i) \<le> sub_s(i).\<close>
          have "sub_s (?i - 1) \<le> sub_s ?i"
          proof -
            have "?i - 1 < m" using hi by simp
            have "sub_s (?i - 1) < sub_s (Suc (?i - 1))"
              using hs_inc[rule_format, OF \<open>?i - 1 < m\<close>] .
            also have "Suc (?i - 1) = ?i" using hi_pos by simp
            finally show ?thesis by simp
          qed
          have hSuc_i: "Suc (?i - 1) = ?i" using hi_pos by simp
          have "sub_s ?i \<le> sub_s (Suc (?i - 1))" using hSuc_i by simp
          have "(sub_s ?i, sub_t ?j) \<in> ?R (?i - 1) ?j"
          proof -
            have "sub_s ?i \<in> {s\<in>I_set. sub_s (?i - 1) \<le> s \<and> s \<le> sub_s (Suc (?i - 1))}"
              using hsi_I \<open>sub_s (?i - 1) \<le> sub_s ?i\<close> \<open>sub_s ?i \<le> sub_s (Suc (?i - 1))\<close> by simp
            moreover have "sub_t ?j \<in> {t\<in>I_set. sub_t ?j \<le> t \<and> t \<le> sub_t (Suc ?j)}"
              using htj_I htj_le by simp
            ultimately show ?thesis by (by100 blast)
          qed
          hence "(sub_s ?i, sub_t ?j) \<in> ?R (?k' mod m) (?k' div m)"
            using hk'_mod hk'_div by simp
          hence "(sub_s ?i, sub_t ?j) \<in> (\<Union>k'<k. ?R (k' mod m) (k' div m))"
            using \<open>?k' < k\<close> by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        have hcorner_both: "(sub_s ?i, sub_t ?j) \<in> ?A k \<inter> ?R ?i ?j"
          using hcorner_A hcorner_R by (by100 blast)
        show ?thesis
        proof (rule ccontr)
          assume "\<not> ?thesis" hence "?A k \<inter> ?R ?i ?j = {}" by simp
          thus False using hcorner_both by simp
        qed
      qed
      have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
        unfolding II_topology_def
        by (rule product_topology_on_is_topology_on[OF
            top1_unit_interval_topology_is_topology_on
            top1_unit_interval_topology_is_topology_on])
      \<comment> \<open>Apply homotopy_lifting_rectangle_step.\<close>
      obtain Ft_next where hnext_cont: "top1_continuous_map_on (?A k \<union> ?R ?i ?j)
          (subspace_topology (I_set \<times> I_set) II_topology (?A k \<union> ?R ?i ?j)) E TE Ft_next"
          and hnext_lift: "\<forall>x\<in>?A k \<union> ?R ?i ?j. p (Ft_next x) = F x"
          and hnext_agree: "\<forall>x\<in>?A k. Ft_next x = Ft_prev x"
        using homotopy_lifting_rectangle_step[OF assms(1) hTII assms(7)
            hA_closed hR_closed hAR_sub hprev_cont hprev_lift hFR hUec
            hC_conn hC_ne assms(4)] by auto
      \<comment> \<open>A_{Suc k} = A_k \<union> R_{i,j}.\<close>
      have hA_Suc: "?A (Suc k) = ?A k \<union> ?R ?i ?j"
      proof -
        have "(\<Union>k'<Suc k. ?R (k' mod m) (k' div m))
            = (\<Union>k'<k. ?R (k' mod m) (k' div m)) \<union> ?R (k mod m) (k div m)"
        proof (rule set_eqI)
          fix x show "(x \<in> (\<Union>k'<Suc k. ?R (k' mod m) (k' div m)))
              = (x \<in> (\<Union>k'<k. ?R (k' mod m) (k' div m)) \<union> ?R (k mod m) (k div m))"
            using less_Suc_eq by blast
        qed
        thus ?thesis by (simp add: Un_assoc)
      qed
      have "Ft_next (0, 0) = e0"
      proof -
        have "(0::real, 0::real) \<in> ?A k"
          unfolding top1_unit_interval_def by (by100 auto)
        hence "Ft_next (0, 0) = Ft_prev (0, 0)" using hnext_agree by (by100 blast)
        thus ?thesis using hprev_00 by simp
      qed
      show ?case
      proof (intro exI conjI)
        show "top1_continuous_map_on (?A (Suc k))
            (subspace_topology (I_set \<times> I_set) II_topology (?A (Suc k))) E TE Ft_next"
          using hnext_cont hA_Suc by simp
        show "\<forall>x\<in>?A (Suc k). p (Ft_next x) = F x"
          using hnext_lift hA_Suc by simp
        show "Ft_next (0, 0) = e0" using \<open>Ft_next (0, 0) = e0\<close> .
      qed
    qed
  qed
  \<comment> \<open>At k = m*n: A_{m*n} = I\<times>I.\<close>
  hence "\<exists>Ft. top1_continuous_map_on (?A (m*n))
      (subspace_topology (I_set \<times> I_set) II_topology (?A (m*n))) E TE Ft
      \<and> (\<forall>x\<in>?A (m*n). p (Ft x) = F x) \<and> Ft (0, 0) = e0"
    by simp
  moreover have "?A (m*n) = I_set \<times> I_set"
  proof (rule equalityI)
    \<comment> \<open>Forward: A(m*n) \<subseteq> I\<times>I.\<close>
    show "?A (m*n) \<subseteq> I_set \<times> I_set"
    proof (rule subsetI)
      fix x assume "x \<in> ?A (m*n)"
      hence "x \<in> ?edges \<or> x \<in> (\<Union>k'<m*n. {s\<in>I_set. sub_s (k' mod m) \<le> s \<and> s \<le> sub_s (Suc (k' mod m))}
                \<times> {t\<in>I_set. sub_t (k' div m) \<le> t \<and> t \<le> sub_t (Suc (k' div m))})"
        by (by100 auto)
      thus "x \<in> I_set \<times> I_set"
      proof (elim disjE)
        assume "x \<in> ?edges"
        hence "x \<in> ?left_edge \<or> x \<in> ?bot_edge" by (by100 auto)
        thus ?thesis using h0I by (by100 blast)
      next
        assume "x \<in> (\<Union>k'<m*n. {s\<in>I_set. sub_s (k' mod m) \<le> s \<and> s \<le> sub_s (Suc (k' mod m))}
                \<times> {t\<in>I_set. sub_t (k' div m) \<le> t \<and> t \<le> sub_t (Suc (k' div m))})"
        thus ?thesis by (by100 blast)
      qed
    qed
  next
    \<comment> \<open>Backward: I\<times>I \<subseteq> A(m*n). Each (s,t) is in some rectangle.\<close>
    show "I_set \<times> I_set \<subseteq> ?A (m*n)"
    proof (rule subsetI)
      fix x assume hx: "x \<in> I_set \<times> I_set"
      obtain s t where hst: "x = (s, t)" and hs: "s \<in> I_set" and ht: "t \<in> I_set"
        using hx by (by100 blast)
      have hs_ge: "sub_s 0 \<le> s" using hs hs0 unfolding top1_unit_interval_def by simp
      have hs_le: "s \<le> sub_s m" using hs hsm unfolding top1_unit_interval_def by simp
      have ht_ge: "sub_t 0 \<le> t" using ht ht0 unfolding top1_unit_interval_def by simp
      have ht_le: "t \<le> sub_t n" using ht htn unfolding top1_unit_interval_def by simp
      obtain i where hi: "i < m" and hsi: "sub_s i \<le> s \<and> s \<le> sub_s (Suc i)"
        using increasing_interval_cover[OF hm hs_ge hs_le hs_inc] by (by100 blast)
      obtain j where hj_: "j < n" and htj: "sub_t j \<le> t \<and> t \<le> sub_t (Suc j)"
        using increasing_interval_cover[OF hn ht_ge ht_le ht_inc] by (by100 blast)
      \<comment> \<open>Linearized index k' = j*m + i < m*n.\<close>
      have hk': "j * m + i < m * n"
      proof -
        have "j * m + i < j * m + m" using hi by simp
        also have "\<dots> = (j + 1) * m" by (simp add: algebra_simps)
        also have "\<dots> \<le> n * m"
        proof -
          have "Suc j \<le> n" using hj_ by simp
          hence "Suc j * m \<le> n * m" by (rule Nat.mult_le_mono1)
          thus ?thesis by simp
        qed
        finally show ?thesis by (simp add: mult.commute)
      qed
      have hmod: "(j * m + i) mod m = i" using hi by simp
      have hdiv: "(j * m + i) div m = j" using hi by simp
      have "(s, t) \<in> {s'\<in>I_set. sub_s i \<le> s' \<and> s' \<le> sub_s (Suc i)}
          \<times> {t'\<in>I_set. sub_t j \<le> t' \<and> t' \<le> sub_t (Suc j)}"
        using hs ht hsi htj by (by100 blast)
      hence "(s, t) \<in> {s'\<in>I_set. sub_s ((j*m+i) mod m) \<le> s' \<and> s' \<le> sub_s (Suc ((j*m+i) mod m))}
          \<times> {t'\<in>I_set. sub_t ((j*m+i) div m) \<le> t' \<and> t' \<le> sub_t (Suc ((j*m+i) div m))}"
        using hmod hdiv by simp
      hence "(s, t) \<in> (\<Union>k'<m*n. {s'\<in>I_set. sub_s (k' mod m) \<le> s' \<and> s' \<le> sub_s (Suc (k' mod m))}
          \<times> {t'\<in>I_set. sub_t (k' div m) \<le> t' \<and> t' \<le> sub_t (Suc (k' div m))})"
        using hk' by (by100 blast)
      thus "x \<in> ?A (m*n)" using hst by (by100 blast)
    qed
  qed
  ultimately show ?thesis
  proof -
    assume hAmn: "?A (m*n) = I_set \<times> I_set"
    assume "\<exists>Ft. top1_continuous_map_on (?A (m*n))
        (subspace_topology (I_set \<times> I_set) II_topology (?A (m*n))) E TE Ft
        \<and> (\<forall>x\<in>?A (m*n). p (Ft x) = F x) \<and> Ft (0, 0) = e0"
    then obtain Ft where hFt_c: "top1_continuous_map_on (?A (m*n))
        (subspace_topology (I_set \<times> I_set) II_topology (?A (m*n))) E TE Ft"
        and hFt_l: "\<forall>x\<in>?A (m*n). p (Ft x) = F x" and hFt_0: "Ft (0, 0) = e0"
      by (by100 blast)
    have hTII_loc: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def
      by (rule product_topology_on_is_topology_on[OF
          top1_unit_interval_topology_is_topology_on
          top1_unit_interval_topology_is_topology_on])
    have hsubs: "\<forall>W\<in>II_topology. W \<subseteq> I_set \<times> I_set"
    proof (intro ballI subsetI)
      fix W x assume hW: "W \<in> II_topology" and hx: "x \<in> W"
      have hW2: "W \<in> topology_generated_by_basis UNIV (product_basis I_top I_top)"
        using hW unfolding II_topology_def product_topology_on_def by simp
      then obtain b where hb: "b \<in> product_basis I_top I_top" and hxb: "x \<in> b"
        unfolding topology_generated_by_basis_def using hx by (by100 blast)
      obtain U V where hU: "U \<in> I_top" and hV: "V \<in> I_top" and hbeq: "b = U \<times> V"
        using hb unfolding product_basis_def by (by100 blast)
      have "U \<subseteq> I_set"
      proof -
        obtain W where "U = I_set \<inter> W"
          using hU unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      moreover have "V \<subseteq> I_set"
      proof -
        obtain W where "V = I_set \<inter> W"
          using hV unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
        thus ?thesis by (by100 blast)
      qed
      ultimately show "x \<in> I_set \<times> I_set" using hxb hbeq by (by100 blast)
    qed
    have "subspace_topology (I_set \<times> I_set) II_topology (I_set \<times> I_set) = II_topology"
    proof (rule set_eqI)
      fix W
      show "(W \<in> subspace_topology (I_set \<times> I_set) II_topology (I_set \<times> I_set)) = (W \<in> II_topology)"
      proof
        assume "W \<in> subspace_topology (I_set \<times> I_set) II_topology (I_set \<times> I_set)"
        then obtain U where hU: "U \<in> II_topology" and hW: "W = (I_set \<times> I_set) \<inter> U"
          unfolding subspace_topology_def by (by100 blast)
        hence "W = U" using hsubs hU by (by100 blast)
        thus "W \<in> II_topology" using hU by simp
      next
        assume hW: "W \<in> II_topology"
        have "W = (I_set \<times> I_set) \<inter> W" using hsubs hW by (by100 blast)
        thus "W \<in> subspace_topology (I_set \<times> I_set) II_topology (I_set \<times> I_set)"
          unfolding subspace_topology_def using hW by (by100 blast)
      qed
    qed
    hence "top1_continuous_map_on (I_set \<times> I_set) II_topology E TE Ft"
      using hFt_c hAmn by simp
    moreover have "\<forall>s\<in>I_set. \<forall>t\<in>I_set. p (Ft (s, t)) = F (s, t)"
      using hFt_l hAmn by (by100 auto)
    moreover have "Ft (0, 0) = e0" using hFt_0 .
    ultimately show ?thesis by (by100 blast)
  qed
qed
(** from \<S>54 Theorem 54.3: path-homotopic paths lift to path-homotopic paths.

    Munkres' proof:
    (1) By definition of path homotopy, there is F: I\<times>I \<rightarrow> B with F(s,0)=f(s),
        F(s,1)=g(s), F(0,t)=b0, F(1,t)=b1.
    (2) Lift F to Ftilde: I\<times>I \<rightarrow> E with Ftilde(0,0)=e0, p\<circ>Ftilde=F (Lemma 54.2).
    (3) Ftilde(0,t) lies in p^{-1}(b0) (fiber), which is discrete, so it is
        constantly e0. Similarly Ftilde(1,t) is constant \<Rightarrow> e1 = e1'.
    (4) Ftilde(s,0) is a lift of f starting at e0, so = ftilde (by uniqueness).
        Ftilde(s,1) is a lift of g starting at e0, so = gtilde.
    (5) Hence Ftilde is a path homotopy from ftilde to gtilde. **)
theorem Theorem_54_3:
  assumes hcov: "top1_covering_map_on E TE B TB p"
      and hTE: "is_topology_on E TE" and hTB: "is_topology_on B TB"
      and he0: "e0 \<in> E" and hpe0: "p e0 = b0"
      and hf: "top1_is_path_on B TB b0 b1 f"
      and hg: "top1_is_path_on B TB b0 b1 g"
      and hfg: "top1_path_homotopic_on B TB b0 b1 f g"
      and hft: "top1_is_path_on E TE e0 e1 ftilde"
      and hftp: "(\<forall>s\<in>I_set. p (ftilde s) = f s)"
      and hgt: "top1_is_path_on E TE e0 e1' gtilde"
      and hgtp: "(\<forall>s\<in>I_set. p (gtilde s) = g s)"
  shows "e1 = e1' \<and> top1_path_homotopic_on E TE e0 e1 ftilde gtilde"
proof -
  \<comment> \<open>Step 1: obtain a homotopy F from f to g in B by unfolding path-homotopy.\<close>
  obtain F where hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology B TB F"
             and hF_f: "\<forall>s\<in>I_set. F (s, 0) = f s"
             and hF_g: "\<forall>s\<in>I_set. F (s, 1) = g s"
             and hF_b0: "\<forall>t\<in>I_set. F (0, t) = b0"
             and hF_b1: "\<forall>t\<in>I_set. F (1, t) = b1"
    using hfg unfolding top1_path_homotopic_on_def by blast
  \<comment> \<open>Step 2: lift F to Ftilde via Lemma 54.2. F(0,0) = f(0) = b0.\<close>
  have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hF_00: "F (0, 0) = b0"
    using hF_f[rule_format, OF h0I] hf unfolding top1_is_path_on_def by simp
  obtain Ftilde where
        hFt_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology E TE Ftilde"
    and hFt_lift: "\<forall>s\<in>I_set. \<forall>t\<in>I_set. p (Ftilde (s, t)) = F (s, t)"
    and hFt_00: "Ftilde (0, 0) = e0"
    using Lemma_54_2_homotopy_lifting[OF hcov he0 hpe0 hF_cont hF_00 hTB hTE] by blast
  \<comment> \<open>Step 3: Ftilde(0,t) is constant e0; Ftilde(1,t) is constant, so e1 = e1'\<close>
  have hFt_left: "\<forall>t\<in>I_set. Ftilde (0, t) = e0"
  proof -
    have h0I0: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have hcont_left: "top1_continuous_map_on I_set I_top E TE (\<lambda>t. Ftilde (0, t))"
    proof -
      have "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>t. (0, t))"
        by (rule pair_const_t_continuous[OF h0I0])
      hence "top1_continuous_map_on I_set I_top E TE (Ftilde \<circ> (\<lambda>t. (0, t)))"
        by (rule top1_continuous_map_on_comp[OF _ hFt_cont])
      thus ?thesis by (simp add: comp_def)
    qed
    have hleft_lift: "\<forall>t\<in>I_set. p (Ftilde (0, t)) = b0"
      using hFt_lift hF_b0 h0I0 by auto
    have hpath_left: "top1_is_path_on E TE e0 (Ftilde (0, 1)) (\<lambda>t. Ftilde (0, t))"
      unfolding top1_is_path_on_def using hcont_left hFt_00 by simp
    \<comment> \<open>Constant path at b_0, lifted to constant path at e_0.\<close>
    have hb0_in_B: "b0 \<in> B"
      using hf unfolding top1_is_path_on_def top1_continuous_map_on_def
      using h0I0 by blast
    have hconst_B: "top1_is_path_on B TB b0 b0 (top1_constant_path b0)"
      by (rule top1_constant_path_is_path[OF hTB hb0_in_B])
    have hconst_E: "top1_is_path_on E TE e0 e0 (top1_constant_path e0)"
      by (rule top1_constant_path_is_path[OF hTE he0])
    have hconst_lift: "\<forall>s\<in>I_set. p (top1_constant_path e0 s) = top1_constant_path b0 s"
      unfolding top1_constant_path_def using hpe0 by simp
    have hleft_const_lift': "\<forall>s\<in>I_set. p (Ftilde (0, s)) = top1_constant_path b0 s"
      using hleft_lift unfolding top1_constant_path_def by simp
    have "\<forall>t\<in>I_set. Ftilde (0, t) = top1_constant_path e0 t"
      using Lemma_54_1_uniqueness[OF hcov he0 hpe0 hconst_B hpath_left
                                      hleft_const_lift' hconst_E hconst_lift] .
    thus ?thesis unfolding top1_constant_path_def by simp
  qed
  have hFt_right_const: "\<exists>e. \<forall>t\<in>I_set. Ftilde (1, t) = e"
  proof -
    let ?e1loc = "Ftilde (1, 0)"
    have h0I_: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have h1I_: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have hcont_right: "top1_continuous_map_on I_set I_top E TE (\<lambda>t. Ftilde (1, t))"
    proof -
      have "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>t. (1, t))"
        by (rule pair_const_t_continuous[OF h1I_])
      hence "top1_continuous_map_on I_set I_top E TE (Ftilde \<circ> (\<lambda>t. (1, t)))"
        by (rule top1_continuous_map_on_comp[OF _ hFt_cont])
      thus ?thesis by (simp add: comp_def)
    qed
    have hright_lift: "\<forall>t\<in>I_set. p (Ftilde (1, t)) = b1"
      using hFt_lift hF_b1 h1I_ by auto
    have he1_in_E: "?e1loc \<in> E"
      using hcont_right h0I_ unfolding top1_continuous_map_on_def by blast
    have hpe1: "p ?e1loc = b1" using hright_lift h0I_ by blast
    have hpath_right: "top1_is_path_on E TE ?e1loc (Ftilde (1, 1)) (\<lambda>t. Ftilde (1, t))"
      unfolding top1_is_path_on_def using hcont_right by simp
    \<comment> \<open>Constant path at b_1 in B, lifted to constant path at ?e1loc in E.\<close>
    have hb1_in_B: "b1 \<in> B" using hf unfolding top1_is_path_on_def top1_continuous_map_on_def
      using h1I_ by blast
    have hconst_B: "top1_is_path_on B TB b1 b1 (top1_constant_path b1)"
      by (rule top1_constant_path_is_path[OF hTB hb1_in_B])
    have hconst_E: "top1_is_path_on E TE ?e1loc ?e1loc (top1_constant_path ?e1loc)"
      by (rule top1_constant_path_is_path[OF hTE he1_in_E])
    have hconst_lift: "\<forall>s\<in>I_set. p (top1_constant_path ?e1loc s) = top1_constant_path b1 s"
      unfolding top1_constant_path_def using hpe1 by simp
    have hright_const_lift': "\<forall>s\<in>I_set. p (Ftilde (1, s)) = top1_constant_path b1 s"
      using hright_lift unfolding top1_constant_path_def by simp
    have "\<forall>t\<in>I_set. Ftilde (1, t) = top1_constant_path ?e1loc t"
      using Lemma_54_1_uniqueness[OF hcov he1_in_E hpe1 hconst_B hpath_right
                                      hright_const_lift' hconst_E hconst_lift] .
    hence "\<forall>t\<in>I_set. Ftilde (1, t) = ?e1loc"
      unfolding top1_constant_path_def by simp
    thus ?thesis by blast
  qed
  \<comment> \<open>Step 4: Ftilde(s,0) = ftilde and Ftilde(s,1) = gtilde by uniqueness of path lifting.\<close>
  have h0I: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  \<comment> \<open>Ftilde(·, 0) is a path in E lifting f, starting at e0.\<close>
  have hFt_bot_path: "top1_is_path_on E TE e0 (Ftilde (1, 0)) (\<lambda>s. Ftilde (s, 0))"
  proof -
    have "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>s. (s, 0))"
      by (rule pair_s_const_continuous[OF h0I])
    hence "top1_continuous_map_on I_set I_top E TE (Ftilde \<circ> (\<lambda>s. (s, 0)))"
      by (rule top1_continuous_map_on_comp[OF _ hFt_cont])
    hence "top1_continuous_map_on I_set I_top E TE (\<lambda>s. Ftilde (s, 0))"
      by (simp add: comp_def)
    thus ?thesis unfolding top1_is_path_on_def using hFt_00 by simp
  qed
  have hFt_bot_lift: "\<forall>s\<in>I_set. p (Ftilde (s, 0)) = f s"
    using hFt_lift hF_f h0I by auto
  have hFt_bot: "\<forall>s\<in>I_set. Ftilde (s, 0) = ftilde s"
    using Lemma_54_1_uniqueness[OF hcov he0 hpe0 hf hFt_bot_path hFt_bot_lift hft hftp] by blast
  \<comment> \<open>Ftilde(·, 1) is a path in E lifting g, starting at Ftilde(0,1).\<close>
  have h1I0: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hFt_top_start: "Ftilde (0, 1) = e0"
    using hFt_left h1I0 by blast
  have hFt_top_path: "top1_is_path_on E TE e0 (Ftilde (1, 1)) (\<lambda>s. Ftilde (s, 1))"
  proof -
    have h1I0: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>s. (s, 1))"
      by (rule pair_s_const_continuous[OF h1I0])
    hence "top1_continuous_map_on I_set I_top E TE (Ftilde \<circ> (\<lambda>s. (s, 1)))"
      by (rule top1_continuous_map_on_comp[OF _ hFt_cont])
    hence "top1_continuous_map_on I_set I_top E TE (\<lambda>s. Ftilde (s, 1))"
      by (simp add: comp_def)
    thus ?thesis unfolding top1_is_path_on_def using hFt_top_start by simp
  qed
  have hFt_top_lift: "\<forall>s\<in>I_set. p (Ftilde (s, 1)) = g s"
    using hFt_lift hF_g unfolding top1_unit_interval_def by auto
  have hFt_top: "\<forall>s\<in>I_set. Ftilde (s, 1) = gtilde s"
    using Lemma_54_1_uniqueness[OF hcov he0 hpe0 hg hFt_top_path hFt_top_lift hgt hgtp] by blast
  \<comment> \<open>Step 5: assemble endpoints equal and path homotopy.\<close>
  have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
  have hft_1: "ftilde 1 = e1"
    using hft unfolding top1_is_path_on_def by simp
  have hgt_1: "gtilde 1 = e1'"
    using hgt unfolding top1_is_path_on_def by simp
  \<comment> \<open>Ftilde(1, 0) = ftilde(1) = e1 and Ftilde(1, 1) = gtilde(1) = e1', and the fiber is constant.\<close>
  have heq: "e1 = e1'"
  proof -
    obtain e where hc: "\<forall>t\<in>I_set. Ftilde (1, t) = e" using hFt_right_const by blast
    have h0: "Ftilde (1, 0) = e" using hc h0I by blast
    have h1: "Ftilde (1, 1) = e" using hc h1I by blast
    have "Ftilde (1, 0) = ftilde 1" using hFt_bot h1I by blast
    hence "e1 = e" using hft_1 h0 by simp
    moreover have "Ftilde (1, 1) = gtilde 1" using hFt_top h1I by blast
    hence "e1' = e" using hgt_1 h1 by simp
    ultimately show ?thesis by simp
  qed
  have hhomo: "top1_path_homotopic_on E TE e0 e1 ftilde gtilde"
  proof -
    \<comment> \<open>Ftilde is the path homotopy: cont, boundary ftilde/gtilde, sides e0/e1.\<close>
    have hgt': "top1_is_path_on E TE e0 e1 gtilde" using hgt heq by simp
    have hFt_b0: "\<forall>s\<in>I_set. Ftilde (s, 0) = ftilde s" using hFt_bot .
    have hFt_b1: "\<forall>s\<in>I_set. Ftilde (s, 1) = gtilde s" using hFt_top .
    have hFt_l0: "\<forall>t\<in>I_set. Ftilde (0, t) = e0" using hFt_left .
    have hFt_r1: "\<forall>t\<in>I_set. Ftilde (1, t) = e1"
    proof -
      obtain e where hc: "\<forall>t\<in>I_set. Ftilde (1, t) = e" using hFt_right_const by blast
      have "Ftilde (1, 0) = e" using hc h0I by blast
      moreover have "Ftilde (1, 0) = ftilde 1" using hFt_bot h1I by blast
      ultimately have "e = e1" using hft_1 by simp
      thus ?thesis using hc by simp
    qed
    show ?thesis
      unfolding top1_path_homotopic_on_def
      using hft hgt' hFt_cont hFt_b0 hFt_b1 hFt_l0 hFt_r1 by (by100 blast)
  qed
  show ?thesis using heq hhomo by blast
qed

text \<open>Helper: continuous maps preserve path homotopy.
  If f ≃ g in X and h: X → Y is continuous, then h∘f ≃ h∘g in Y.\<close>
lemma continuous_preserves_path_homotopic:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hh: "top1_continuous_map_on X TX Y TY h"
      and hhom: "top1_path_homotopic_on X TX x0 x1 f g"
  shows "top1_path_homotopic_on Y TY (h x0) (h x1) (h \<circ> f) (h \<circ> g)"
proof -
  have hf: "top1_is_path_on X TX x0 x1 f"
    using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
  have hg: "top1_is_path_on X TX x0 x1 g"
    using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
  obtain F where hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hF0: "\<forall>s\<in>I_set. F (s, 0) = f s" and hF1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hFl: "\<forall>t\<in>I_set. F (0, t) = x0" and hFr: "\<forall>t\<in>I_set. F (1, t) = x1"
    using hhom unfolding top1_path_homotopic_on_def by (by100 auto)
  \<comment> \<open>h \<circ> F is a path homotopy from h\<circ>f to h\<circ>g in Y.\<close>
  have hhF: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY (h \<circ> F)"
    by (rule top1_continuous_map_on_comp[OF hF hh])
  have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_path_on_def by (by100 blast)
  have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
    using hg unfolding top1_is_path_on_def by (by100 blast)
  have hhf_path: "top1_is_path_on Y TY (h x0) (h x1) (h \<circ> f)"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top Y TY (h \<circ> f)"
      by (rule top1_continuous_map_on_comp[OF hf_cont hh])
    show "(h \<circ> f) 0 = h x0" using hf unfolding top1_is_path_on_def by simp
    show "(h \<circ> f) 1 = h x1" using hf unfolding top1_is_path_on_def by simp
  qed
  have hhg_path: "top1_is_path_on Y TY (h x0) (h x1) (h \<circ> g)"
    unfolding top1_is_path_on_def
  proof (intro conjI)
    show "top1_continuous_map_on I_set I_top Y TY (h \<circ> g)"
      by (rule top1_continuous_map_on_comp[OF hg_cont hh])
    show "(h \<circ> g) 0 = h x0" using hg unfolding top1_is_path_on_def by simp
    show "(h \<circ> g) 1 = h x1" using hg unfolding top1_is_path_on_def by simp
  qed
  show ?thesis unfolding top1_path_homotopic_on_def
  proof (intro conjI exI)
    show "top1_is_path_on Y TY (h x0) (h x1) (h \<circ> f)" by (rule hhf_path)
    show "top1_is_path_on Y TY (h x0) (h x1) (h \<circ> g)" by (rule hhg_path)
    show "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY (h \<circ> F)" by (rule hhF)
    show "\<forall>s\<in>I_set. (h \<circ> F) (s, 0) = (h \<circ> f) s" using hF0 by simp
    show "\<forall>s\<in>I_set. (h \<circ> F) (s, 1) = (h \<circ> g) s" using hF1 by simp
    show "\<forall>t\<in>I_set. (h \<circ> F) (0, t) = h x0" using hFl by simp
    show "\<forall>t\<in>I_set. (h \<circ> F) (1, t) = h x1" using hFr by simp
  qed
qed

text \<open>Helper: if two functions agree on I\_set, they give the same loop.\<close>
lemma loop_agree_on_I:
  assumes hf: "top1_is_loop_on X TX x0 f"
      and hagree: "\<forall>s\<in>I_set. g s = f s"
  shows "top1_is_loop_on X TX x0 g \<and> top1_path_homotopic_on X TX x0 x0 f g"
proof -
  have hf_cont: "top1_continuous_map_on I_set I_top X TX f"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast
  have hagree': "\<forall>s\<in>I_set. f s = g s" using hagree by simp
  have hg_cont: "top1_continuous_map_on I_set I_top X TX g"
    by (rule top1_continuous_map_on_agree'[OF hf_cont hagree'])
  have hf0: "f 0 = x0" and hf1: "f 1 = x0"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have h0I: "(0::real) \<in> I_set" and h1I: "(1::real) \<in> I_set"
    unfolding top1_unit_interval_def by auto
  have hg0: "g 0 = x0" using hagree h0I hf0 by simp
  have hg1: "g 1 = x0" using hagree h1I hf1 by simp
  have hg_loop: "top1_is_loop_on X TX x0 g"
    unfolding top1_is_loop_on_def top1_is_path_on_def using hg_cont hg0 hg1 by simp
  have hfg_eq: "\<forall>s\<in>I_set. f s = g s" using hagree by simp
  have "top1_path_homotopic_on X TX x0 x0 f g"
    unfolding top1_path_homotopic_on_def
  proof -
    have hf_path: "top1_is_path_on X TX x0 x0 f"
      using hf unfolding top1_is_loop_on_def .
    have hg_path: "top1_is_path_on X TX x0 x0 g"
      using hg_loop unfolding top1_is_loop_on_def .
    \<comment> \<open>Constant homotopy works since f=g on I_set. Use F(s,t) = f(s) = g(s).\<close>
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
    have hpi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi1"
      unfolding II_topology_def by (rule top1_continuous_pi1[OF hTI hTI])
    have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (f \<circ> pi1)"
      by (rule top1_continuous_map_on_comp[OF hpi1 hf_cont])
    have hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (\<lambda>p. f (fst p))"
      using hF_cont unfolding pi1_def comp_def by simp
    show "top1_is_path_on X TX x0 x0 f \<and> top1_is_path_on X TX x0 x0 g \<and>
      (\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F \<and>
           (\<forall>s\<in>I_set. F (s, 0) = f s) \<and> (\<forall>s\<in>I_set. F (s, 1) = g s) \<and>
           (\<forall>t\<in>I_set. F (0, t) = x0) \<and> (\<forall>t\<in>I_set. F (1, t) = x0))"
      using hf_path hg_path hF hfg_eq hf0 hf1 by auto
  qed
  thus ?thesis using hg_loop by blast
qed

text \<open>Helper: in a simply connected space, any two paths with the same endpoints
  are path-homotopic. Uses: gt*ft⁻¹ is a loop, simply connected → nulhomotopic,
  then path algebra gives ft ≃ gt.\<close>
lemma simply_connected_paths_homotopic:
  assumes hsc: "top1_simply_connected_on X TX"
      and hf: "top1_is_path_on X TX x0 x1 f"
      and hg: "top1_is_path_on X TX x0 x1 g"
      and hx0: "x0 \<in> X"
  shows "top1_path_homotopic_on X TX x0 x1 f g"
proof -
  have hTE: "is_topology_on X TX"
    using hsc unfolding top1_simply_connected_on_def top1_path_connected_on_def by (by100 blast)
  let ?loop = "top1_path_product g (top1_path_reverse f)"
  have hrev: "top1_is_path_on X TX x1 x0 (top1_path_reverse f)"
    by (rule top1_path_reverse_is_path[OF hf])
  have hloop_path: "top1_is_path_on X TX x0 x0 ?loop"
    by (rule top1_path_product_is_path[OF hTE hg hrev])
  have hloop: "top1_is_loop_on X TX x0 ?loop"
    unfolding top1_is_loop_on_def using hloop_path by (by100 simp)
  have hloop_nul: "top1_path_homotopic_on X TX x0 x0 ?loop (top1_constant_path x0)"
    using hsc hx0 hloop unfolding top1_simply_connected_on_def by (by100 blast)
  \<comment> \<open>(g*f⁻¹)*f ≃ const*f ≃ f and (g*f⁻¹)*f ≃ g*(f⁻¹*f) ≃ g*const ≃ g. So f ≃ g.\<close>
  have s1: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product ?loop f) (top1_path_product (top1_constant_path x0) f)"
    by (rule path_homotopic_product_left[OF hTE hloop_nul hf])
  have s2: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product (top1_constant_path x0) f) f"
    by (rule Theorem_51_2_left_identity[OF hTE hf])
  have s12: "top1_path_homotopic_on X TX x0 x1 (top1_path_product ?loop f) f"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTE s1 s2])
  have s3: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product ?loop f)
      (top1_path_product g (top1_path_product (top1_path_reverse f) f))"
    by (rule Lemma_51_1_path_homotopic_sym[OF
          Theorem_51_2_associativity[OF hTE hg hrev hf]])
  have s4: "top1_path_homotopic_on X TX x1 x1
      (top1_path_product (top1_path_reverse f) f) (top1_constant_path x1)"
    by (rule Theorem_51_2_invgerse_right[OF hTE hf])
  have s5: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product g (top1_path_product (top1_path_reverse f) f))
      (top1_path_product g (top1_constant_path x1))"
    by (rule path_homotopic_product_right[OF hTE s4 hg])
  have s6: "top1_path_homotopic_on X TX x0 x1
      (top1_path_product g (top1_constant_path x1)) g"
    by (rule Theorem_51_2_right_identity[OF hTE hg])
  have s_chain: "top1_path_homotopic_on X TX x0 x1 (top1_path_product ?loop f) g"
  proof (rule Lemma_51_1_path_homotopic_trans[OF hTE s3])
    show "top1_path_homotopic_on X TX x0 x1
        (top1_path_product g (top1_path_product (top1_path_reverse f) f)) g"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTE s5 s6])
  qed
  have s12_sym: "top1_path_homotopic_on X TX x0 x1 f (top1_path_product ?loop f)"
    by (rule Lemma_51_1_path_homotopic_sym[OF s12])
  show ?thesis by (rule Lemma_51_1_path_homotopic_trans[OF hTE s12_sym s_chain])
qed

(** from \<S>54 Theorem 54.4: lifting correspondence.
    Given a covering p : (E, e_0) \<to> (B, b_0) and E path-connected, the map
    \<Phi> : \<pi>_1(B, b_0) \<to> p\<inverse>(b_0) sending [f] to \<tilde>f(1) (where \<tilde>f is the lift
    starting at e_0) is surjective. **)
theorem Theorem_54_4_lifting_correspondence:
  assumes he0: "e0 \<in> E" and hpe0: "p e0 = b0"
      and "top1_covering_map_on E TE B TB p"
      and "top1_path_connected_on E TE"
      and "is_topology_on B TB"
  shows "\<exists>\<phi>. (\<forall>c \<in> top1_fundamental_group_carrier B TB b0.
                \<phi> c \<in> {e\<in>E. p e = b0})
           \<and> \<phi> ` (top1_fundamental_group_carrier B TB b0) = {e\<in>E. p e = b0}
           \<and> (\<forall>c \<in> top1_fundamental_group_carrier B TB b0.
                \<exists>f ft. f \<in> c \<and> top1_is_loop_on B TB b0 f
                  \<and> top1_is_path_on E TE e0 (\<phi> c) ft
                  \<and> (\<forall>s\<in>I_set. p (ft s) = f s))"
proof -
  \<comment> \<open>Munkres 54.4: Define \<phi>([f]) = ftilde(1) where ftilde lifts f starting at e0.\<close>
  \<comment> \<open>Well-defined: by Theorem 54.3, path-homotopic loops lift to same endpoint.\<close>
  have hTE: "is_topology_on E TE"
    using assms(4) unfolding top1_path_connected_on_def by (by100 blast)
  have hTB: "is_topology_on B TB" by (rule assms(5))
  have hphi_wd: "\<forall>f g. top1_is_loop_on B TB b0 f \<and> top1_is_loop_on B TB b0 g
      \<and> top1_path_homotopic_on B TB b0 b0 f g
      \<longrightarrow> (\<forall>ft gt. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s)
          \<and> top1_is_path_on E TE e0 (gt 1) gt \<and> (\<forall>s\<in>I_set. p (gt s) = g s)
          \<longrightarrow> ft 1 = gt 1)"
  proof (intro allI impI, elim conjE)
    fix f g ft gt
    assume hfl: "top1_is_loop_on B TB b0 f" and hgl: "top1_is_loop_on B TB b0 g"
        and hfg: "top1_path_homotopic_on B TB b0 b0 f g"
        and hft: "top1_is_path_on E TE e0 (ft 1) ft" and hftp: "\<forall>s\<in>I_set. p (ft s) = f s"
        and hgt: "top1_is_path_on E TE e0 (gt 1) gt" and hgtp: "\<forall>s\<in>I_set. p (gt s) = g s"
    have hf_path: "top1_is_path_on B TB b0 b0 f"
      using hfl unfolding top1_is_loop_on_def .
    have hg_path: "top1_is_path_on B TB b0 b0 g"
      using hgl unfolding top1_is_loop_on_def .
    show "ft 1 = gt 1"
      using conjunct1[OF Theorem_54_3[OF assms(3) hTE hTB he0 hpe0 hf_path hg_path hfg hft hftp hgt hgtp]]
      .
  qed
  \<comment> \<open>Surjectivity: for e1 \<in> p\<inverse>(b0), path f_tilde from e0 to e1 projects to loop at b0.\<close>
  have hphi_surj: "\<forall>e1\<in>{e\<in>E. p e = b0}. \<exists>f. top1_is_loop_on B TB b0 f \<and>
      (\<exists>ft. top1_is_path_on E TE e0 e1 ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s))"
  proof
    fix e1 assume he1: "e1 \<in> {e\<in>E. p e = b0}"
    hence he1E: "e1 \<in> E" and hpe1: "p e1 = b0" by (by100 blast)+
    \<comment> \<open>Path \<alpha> from e0 to e1 in E (path-connected).\<close>
    obtain \<alpha> where h\<alpha>: "top1_is_path_on E TE e0 e1 \<alpha>"
      using assms(4) he0 he1E unfolding top1_path_connected_on_def by (by100 auto)
    \<comment> \<open>f = p \<circ> \<alpha> is a loop at b0: f(0) = p(e0) = b0, f(1) = p(e1) = b0.\<close>
    let ?f = "p \<circ> \<alpha>"
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      using assms(3) unfolding top1_covering_map_on_def by (by100 blast)
    have h\<alpha>_cont: "top1_continuous_map_on I_set I_top E TE \<alpha>"
      using h\<alpha> unfolding top1_is_path_on_def by (by100 blast)
    have hf_cont: "top1_continuous_map_on I_set I_top B TB ?f"
      by (rule top1_continuous_map_on_comp[OF h\<alpha>_cont hp_cont])
    have hf0: "?f 0 = b0" using h\<alpha> hpe0 unfolding top1_is_path_on_def by simp
    have hf1: "?f 1 = b0" using h\<alpha> hpe1 unfolding top1_is_path_on_def by simp
    have hf_loop: "top1_is_loop_on B TB b0 ?f"
      unfolding top1_is_loop_on_def top1_is_path_on_def using hf_cont hf0 hf1 by simp
    have hft_lift: "\<forall>s\<in>I_set. p (\<alpha> s) = ?f s" by simp
    show "\<exists>f. top1_is_loop_on B TB b0 f \<and>
        (\<exists>ft. top1_is_path_on E TE e0 e1 ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s))"
      using hf_loop h\<alpha> hft_lift by (by100 blast)
  qed
  \<comment> \<open>Define \<phi>(c): pick any representative loop f from class c, lift it, take endpoint.\<close>
  let ?\<phi> = "\<lambda>c. let f = SOME f. f \<in> c \<and> top1_is_loop_on B TB b0 f in
               let ft = SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s)
               in ft 1"
  \<comment> \<open>Well-definedness from hphi_wd + existence from path-lifting.\<close>
  have hphi_mem: "\<forall>c \<in> top1_fundamental_group_carrier B TB b0.
      ?\<phi> c \<in> {e\<in>E. p e = b0}"
  proof
    fix c assume hc: "c \<in> top1_fundamental_group_carrier B TB b0"
    \<comment> \<open>c is an equivalence class {g. loop_equiv f g} for some loop f.\<close>
    obtain f0 where hf0_loop: "top1_is_loop_on B TB b0 f0"
        and hc_eq: "c = {g. top1_loop_equiv_on B TB b0 f0 g}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 auto)
    have hf0_in: "f0 \<in> c"
    proof -
      have "top1_is_path_on B TB b0 b0 f0" using hf0_loop unfolding top1_is_loop_on_def .
      hence "top1_path_homotopic_on B TB b0 b0 f0 f0"
        by (rule Lemma_51_1_path_homotopic_refl)
      hence "top1_loop_equiv_on B TB b0 f0 f0"
        unfolding top1_loop_equiv_on_def using hf0_loop by (by100 simp)
      thus ?thesis unfolding hc_eq by (by100 simp)
    qed
    \<comment> \<open>SOME picks a representative from c.\<close>
    let ?f = "SOME f. f \<in> c \<and> top1_is_loop_on B TB b0 f"
    have hf_props: "?f \<in> c \<and> top1_is_loop_on B TB b0 ?f"
      using someI_ex[of "\<lambda>f. f \<in> c \<and> top1_is_loop_on B TB b0 f"] hf0_in hf0_loop by (by100 blast)
    \<comment> \<open>Path-lift ?f to get ft.\<close>
    have hf_path: "top1_is_path_on B TB b0 b0 ?f"
      using hf_props unfolding top1_is_loop_on_def by (by100 blast)
    obtain ft0 where hft0: "top1_is_path_on E TE e0 (ft0 1) ft0"
        and hft0p: "\<forall>s\<in>I_set. p (ft0 s) = ?f s"
      using Lemma_54_1_path_lifting[OF assms(3) he0 hpe0 hf_path assms(5) hTE] by (by100 auto)
    \<comment> \<open>SOME picks a lift.\<close>
    let ?ft = "SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = ?f s)"
    have hft_props: "top1_is_path_on E TE e0 (?ft 1) ?ft \<and> (\<forall>s\<in>I_set. p (?ft s) = ?f s)"
      using someI_ex[of "\<lambda>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = ?f s)"]
        hft0 hft0p by (by100 blast)
    \<comment> \<open>ft(1) \<in> E and p(ft(1)) = f(1) = b0.\<close>
    have "?ft 1 \<in> E"
    proof -
      have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      have "top1_continuous_map_on I_set I_top E TE ?ft"
        using hft_props unfolding top1_is_path_on_def by (by100 blast)
      hence "\<forall>s\<in>I_set. ?ft s \<in> E" unfolding top1_continuous_map_on_def by (by100 blast)
      thus "?ft 1 \<in> E" using h1I by (by100 blast)
    qed
    moreover have "p (?ft 1) = b0"
    proof -
      have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      have "p (?ft 1) = ?f 1" using hft_props h1I by (by100 blast)
      also have "?f 1 = b0" using hf_props unfolding top1_is_loop_on_def top1_is_path_on_def
        by (by100 blast)
      finally show ?thesis .
    qed
    ultimately show "?\<phi> c \<in> {e\<in>E. p e = b0}" by (simp add: Let_def)
  qed
  have hphi_surj_full: "?\<phi> ` (top1_fundamental_group_carrier B TB b0) = {e\<in>E. p e = b0}"
  proof (rule set_eqI, rule iffI)
    fix e assume "e \<in> ?\<phi> ` (top1_fundamental_group_carrier B TB b0)"
    thus "e \<in> {e\<in>E. p e = b0}" using hphi_mem by (by100 blast)
  next
    fix e1 assume he1: "e1 \<in> {e\<in>E. p e = b0}"
    \<comment> \<open>By hphi_surj, \<exists>f loop whose lift reaches e1.\<close>
    obtain f0 ft0 where hf0_loop: "top1_is_loop_on B TB b0 f0"
        and hft0: "top1_is_path_on E TE e0 e1 ft0" and hft0p: "\<forall>s\<in>I_set. p (ft0 s) = f0 s"
      using hphi_surj he1 by (by100 auto)
    \<comment> \<open>The equivalence class of f0 is in the carrier.\<close>
    let ?c = "{g. top1_loop_equiv_on B TB b0 f0 g}"
    have hc_carrier: "?c \<in> top1_fundamental_group_carrier B TB b0"
      unfolding top1_fundamental_group_carrier_def using hf0_loop by (by100 blast)
    \<comment> \<open>\<phi>(?c) = e1 by well-definedness: \<phi> picks a representative and lifts it,
       and by hphi_wd, all lifts of equivalent loops end at the same point.\<close>
    have "?\<phi> ?c = e1"
    proof -
      \<comment> \<open>SOME picks f' \<in> ?c with f' a loop. f0 is such, so f' exists.\<close>
      have hf0_in_c: "f0 \<in> ?c"
      proof -
        have "top1_is_path_on B TB b0 b0 f0" using hf0_loop unfolding top1_is_loop_on_def .
        hence "top1_path_homotopic_on B TB b0 b0 f0 f0" by (rule Lemma_51_1_path_homotopic_refl)
        thus ?thesis unfolding top1_loop_equiv_on_def using hf0_loop by (by100 simp)
      qed
      let ?f' = "SOME f. f \<in> ?c \<and> top1_is_loop_on B TB b0 f"
      have hf'_props: "?f' \<in> ?c \<and> top1_is_loop_on B TB b0 ?f'"
        using someI_ex[of "\<lambda>f. f \<in> ?c \<and> top1_is_loop_on B TB b0 f"] hf0_in_c hf0_loop
        by (by100 blast)
      \<comment> \<open>f' is loop-equivalent to f0.\<close>
      have hf'_equiv: "top1_loop_equiv_on B TB b0 f0 ?f'"
        using hf'_props by simp
      hence hf0_f': "top1_path_homotopic_on B TB b0 b0 f0 ?f'"
        unfolding top1_loop_equiv_on_def by (by100 blast)
      \<comment> \<open>Lift ?f' from e0.\<close>
      have hf'_path: "top1_is_path_on B TB b0 b0 ?f'"
        using hf'_props unfolding top1_is_loop_on_def by (by100 blast)
      obtain ft' where hft': "top1_is_path_on E TE e0 (ft' 1) ft'"
          and hft'p: "\<forall>s\<in>I_set. p (ft' s) = ?f' s"
        using Lemma_54_1_path_lifting[OF assms(3) he0 hpe0 hf'_path assms(5) hTE] by (by100 auto)
      \<comment> \<open>SOME picks a lift of ?f'.\<close>
      let ?ft' = "SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = ?f' s)"
      have hft'_props: "top1_is_path_on E TE e0 (?ft' 1) ?ft' \<and> (\<forall>s\<in>I_set. p (?ft' s) = ?f' s)"
        using someI_ex[of "\<lambda>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = ?f' s)"]
          hft' hft'p by (by100 blast)
      \<comment> \<open>By hphi_wd: ft0(1) = ft'(1) since f0 \<simeq> f'.\<close>
      have "ft0 1 = ?ft' 1"
      proof -
        have hf'_loop: "top1_is_loop_on B TB b0 ?f'" using hf'_props by (by100 blast)
        have h_ft0_1: "ft0 1 = e1" using hft0 unfolding top1_is_path_on_def by simp
        have h_ft0': "top1_is_path_on E TE e0 (ft0 1) ft0"
          using hft0 h_ft0_1 by simp
        have h_ft'_path: "top1_is_path_on E TE e0 (?ft' 1) ?ft'"
          using hft'_props by (by100 blast)
        have h_ft'p: "\<forall>s\<in>I_set. p (?ft' s) = ?f' s"
          using hft'_props by (by100 blast)
        \<comment> \<open>Apply hphi_wd with f = f0, g = ?f', ft = ft0, gt = ?ft'.\<close>
        have hwd: "top1_is_loop_on B TB b0 f0 \<and> top1_is_loop_on B TB b0 ?f'
            \<and> top1_path_homotopic_on B TB b0 b0 f0 ?f'
            \<longrightarrow> (\<forall>ft gt. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f0 s)
                \<and> top1_is_path_on E TE e0 (gt 1) gt \<and> (\<forall>s\<in>I_set. p (gt s) = ?f' s)
                \<longrightarrow> ft 1 = gt 1)"
          using hphi_wd by blast
        have hpremise: "top1_is_loop_on B TB b0 f0 \<and> top1_is_loop_on B TB b0 ?f'
            \<and> top1_path_homotopic_on B TB b0 b0 f0 ?f'"
          using hf0_loop hf'_loop hf0_f' by (by100 blast)
        have hlifts: "top1_is_path_on E TE e0 (ft0 1) ft0 \<and> (\<forall>s\<in>I_set. p (ft0 s) = f0 s)
            \<and> top1_is_path_on E TE e0 (?ft' 1) ?ft' \<and> (\<forall>s\<in>I_set. p (?ft' s) = ?f' s)"
          using h_ft0' hft0p h_ft'_path h_ft'p by (by100 blast)
        show ?thesis using hwd hpremise hlifts by blast
      qed
      \<comment> \<open>ft0(1) = e1 by assumption, so ?ft'(1) = e1.\<close>
      hence "?ft' 1 = e1" using hft0 unfolding top1_is_path_on_def by simp
      \<comment> \<open>\<phi>(?c) = ?ft'(1) = e1.\<close>
      thus ?thesis by (simp add: Let_def)
    qed
    thus "e1 \<in> ?\<phi> ` (top1_fundamental_group_carrier B TB b0)"
      using hc_carrier by (by100 blast)
  qed
  \<comment> \<open>Lift characterization: \<phi>(c) is the endpoint of a lift of a representative.\<close>
  have hphi_lift: "\<forall>c\<in>top1_fundamental_group_carrier B TB b0.
      \<exists>f ft. f \<in> c \<and> top1_is_loop_on B TB b0 f
        \<and> top1_is_path_on E TE e0 (?\<phi> c) ft
        \<and> (\<forall>s\<in>I_set. p (ft s) = f s)"
  proof
    fix c assume hc: "c \<in> top1_fundamental_group_carrier B TB b0"
    obtain f0 where hf0_loop: "top1_is_loop_on B TB b0 f0"
        and hc_eq: "c = {g. top1_loop_equiv_on B TB b0 f0 g}"
      using hc unfolding top1_fundamental_group_carrier_def by (by100 auto)
    let ?f = "SOME f. f \<in> c \<and> top1_is_loop_on B TB b0 f"
    have hf_props: "?f \<in> c \<and> top1_is_loop_on B TB b0 ?f"
    proof -
      have "f0 \<in> c" unfolding hc_eq
        using top1_loop_equiv_on_refl[OF hf0_loop] by simp
      thus ?thesis using someI_ex[of "\<lambda>f. f \<in> c \<and> top1_is_loop_on B TB b0 f"] hf0_loop
        by (by100 blast)
    qed
    let ?ft = "SOME ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = ?f s)"
    have hft_props: "top1_is_path_on E TE e0 (?ft 1) ?ft \<and> (\<forall>s\<in>I_set. p (?ft s) = ?f s)"
    proof -
      have hf_path: "top1_is_path_on B TB b0 b0 ?f"
        using hf_props unfolding top1_is_loop_on_def by (by100 blast)
      obtain ft0 where "top1_is_path_on E TE e0 (ft0 1) ft0"
          "(\<forall>s\<in>I_set. p (ft0 s) = ?f s)"
        using Lemma_54_1_path_lifting[OF assms(3) he0 hpe0 hf_path assms(5) hTE] by (by100 auto)
      thus ?thesis using someI_ex[of "\<lambda>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = ?f s)"]
        by (by100 blast)
    qed
    show "\<exists>f ft. f \<in> c \<and> top1_is_loop_on B TB b0 f
        \<and> top1_is_path_on E TE e0 (?\<phi> c) ft
        \<and> (\<forall>s\<in>I_set. p (ft s) = f s)"
      using hf_props hft_props by (simp add: Let_def) blast
  qed
  show ?thesis
    apply (rule exI[of _ ?\<phi>])
    using hphi_mem hphi_surj_full hphi_lift by (by100 blast)
qed

theorem Theorem_54_4_bijective_simply_connected:
  assumes "top1_covering_map_on E TE B TB p"
      and "e0 \<in> E" and "p e0 = b0"
      and "top1_simply_connected_on E TE"
      and "is_topology_on B TB"
  shows "\<exists>\<phi>. bij_betw \<phi> (top1_fundamental_group_carrier B TB b0) {e\<in>E. p e = b0}"
proof -
  \<comment> \<open>Munkres 54.4 bijectivity: surjectivity from path-connectedness (which follows
     from simple connectivity), injectivity from simple connectivity of E.\<close>
  have hpc: "top1_path_connected_on E TE"
    using assms(4) top1_simply_connected_on_path_connected by (by100 blast)
  have hTB_outer: "is_topology_on B TB" by (rule assms(5))
  \<comment> \<open>Injectivity: if \<phi>([f])=\<phi>([g]) then lifts end at same point. E simply connected
     gives path homotopy Ftilde between lifts; p\<circ>Ftilde homotopizes f to g.\<close>
  have hinj: "\<forall>f g. top1_is_loop_on B TB b0 f \<and> top1_is_loop_on B TB b0 g \<and>
      (\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s)) \<and>
      (\<exists>gt. top1_is_path_on E TE e0 (gt 1) gt \<and> (\<forall>s\<in>I_set. p (gt s) = g s)) \<and>
      (\<forall>ft gt. top1_is_path_on E TE e0 (ft 1) ft \<longrightarrow> (\<forall>s\<in>I_set. p (ft s) = f s) \<longrightarrow>
               top1_is_path_on E TE e0 (gt 1) gt \<longrightarrow> (\<forall>s\<in>I_set. p (gt s) = g s) \<longrightarrow>
               ft 1 = gt 1)
      \<longrightarrow> top1_path_homotopic_on B TB b0 b0 f g"
  proof (intro allI impI, elim conjE)
    fix f g assume hfl: "top1_is_loop_on B TB b0 f" and hgl: "top1_is_loop_on B TB b0 g"
    assume "\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f s)"
    then obtain ft where hft: "top1_is_path_on E TE e0 (ft 1) ft" and hftp: "\<forall>s\<in>I_set. p (ft s) = f s"
      by (by100 blast)
    assume "\<exists>gt. top1_is_path_on E TE e0 (gt 1) gt \<and> (\<forall>s\<in>I_set. p (gt s) = g s)"
    then obtain gt where hgt: "top1_is_path_on E TE e0 (gt 1) gt" and hgtp: "\<forall>s\<in>I_set. p (gt s) = g s"
      by (by100 blast)
    assume "\<forall>ft gt. top1_is_path_on E TE e0 (ft 1) ft \<longrightarrow> (\<forall>s\<in>I_set. p (ft s) = f s) \<longrightarrow>
               top1_is_path_on E TE e0 (gt 1) gt \<longrightarrow> (\<forall>s\<in>I_set. p (gt s) = g s) \<longrightarrow>
               ft 1 = gt 1"
    hence hend_eq: "ft 1 = gt 1" using hft hftp hgt hgtp by (by100 blast)
    have hTE: "is_topology_on E TE" using hpc unfolding top1_path_connected_on_def by (by100 blast)
    \<comment> \<open>E simply connected: ft \<simeq> gt.\<close>
    have hft': "top1_is_path_on E TE e0 (ft 1) ft" using hft .
    have hgt': "top1_is_path_on E TE e0 (ft 1) gt" using hgt hend_eq by simp
    have "top1_path_homotopic_on E TE e0 (ft 1) ft gt"
      by (rule simply_connected_paths_homotopic[OF assms(4) hft' hgt' assms(2)])
    \<comment> \<open>Apply p: p\<circ>ft \<simeq> p\<circ>gt.\<close>
    have hp_cont: "top1_continuous_map_on E TE B TB p"
      using assms(1) unfolding top1_covering_map_on_def by (by100 blast)
    have hTB: "is_topology_on B TB" by (rule hTB_outer)
    have hpft_pgt: "top1_path_homotopic_on B TB (p e0) (p (ft 1)) (p \<circ> ft) (p \<circ> gt)"
      by (rule continuous_preserves_path_homotopic[OF hTE hTB hp_cont
            \<open>top1_path_homotopic_on E TE e0 (ft 1) ft gt\<close>])
    \<comment> \<open>p\<circ>ft = f and p\<circ>gt = g on I_set. Use loop_agree_on_I.\<close>
    have hpft_f: "\<forall>s\<in>I_set. (p \<circ> ft) s = f s" using hftp by simp
    have hpgt_g: "\<forall>s\<in>I_set. (p \<circ> gt) s = g s" using hgtp by simp
    have hpe0: "p e0 = b0" using assms(3) .
    have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have hpft1: "p (ft 1) = b0"
      using hftp h1I hfl unfolding top1_is_loop_on_def top1_is_path_on_def by simp
    have "top1_path_homotopic_on B TB b0 b0 (p \<circ> ft) (p \<circ> gt)"
      using hpft_pgt hpe0 hpft1 by simp
    \<comment> \<open>p\<circ>ft agrees with f on I_set, p\<circ>gt agrees with g. Transfer homotopy.\<close>
    have hpft_loop: "top1_is_loop_on B TB b0 (p \<circ> ft)"
      using \<open>top1_path_homotopic_on B TB b0 b0 (p \<circ> ft) (p \<circ> gt)\<close>
      unfolding top1_path_homotopic_on_def top1_is_loop_on_def by (by100 blast)
    have hf_loop_agree: "\<forall>s\<in>I_set. (p \<circ> ft) s = f s" using hftp by simp
    have hg_loop_agree: "\<forall>s\<in>I_set. (p \<circ> gt) s = g s" using hgtp by simp
    have hf_equiv_pft: "top1_path_homotopic_on B TB b0 b0 f (p \<circ> ft)"
      using conjunct2[OF loop_agree_on_I[OF hfl hf_loop_agree]] .
    have hpgt_loop: "top1_is_loop_on B TB b0 (p \<circ> gt)"
      using \<open>top1_path_homotopic_on B TB b0 b0 (p \<circ> ft) (p \<circ> gt)\<close>
      unfolding top1_path_homotopic_on_def top1_is_loop_on_def by (by100 blast)
    have hg_equiv_pgt: "top1_path_homotopic_on B TB b0 b0 g (p \<circ> gt)"
      using conjunct2[OF loop_agree_on_I[OF hgl hg_loop_agree]] .
    \<comment> \<open>Chain: f \<simeq> p\<circ>ft \<simeq> p\<circ>gt \<simeq> g.\<close>
    have hf_pft: "top1_path_homotopic_on B TB b0 b0 f (p \<circ> ft)"
      by (rule hf_equiv_pft)
    have hpft_pgt': "top1_path_homotopic_on B TB b0 b0 (p \<circ> ft) (p \<circ> gt)"
      using hpft_pgt hpe0 hpft1 by simp
    have hpgt_g': "top1_path_homotopic_on B TB b0 b0 (p \<circ> gt) g"
      by (rule Lemma_51_1_path_homotopic_sym[OF hg_equiv_pgt])
    have hf_pgt: "top1_path_homotopic_on B TB b0 b0 f (p \<circ> gt)"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTB hf_pft hpft_pgt'])
    thus "top1_path_homotopic_on B TB b0 b0 f g"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTB _ hpgt_g'])
  qed
  \<comment> \<open>From Theorem 54.4 (lifting correspondence), get surjective \<phi>.\<close>
  obtain \<phi> where h\<phi>_mem: "\<forall>c \<in> top1_fundamental_group_carrier B TB b0.
        \<phi> c \<in> {e\<in>E. p e = b0}"
      and h\<phi>_surj: "\<phi> ` (top1_fundamental_group_carrier B TB b0) = {e\<in>E. p e = b0}"
      and h\<phi>_lift: "\<forall>c \<in> top1_fundamental_group_carrier B TB b0.
        \<exists>f ft. f \<in> c \<and> top1_is_loop_on B TB b0 f
          \<and> top1_is_path_on E TE e0 (\<phi> c) ft
          \<and> (\<forall>s\<in>I_set. p (ft s) = f s)"
    using Theorem_54_4_lifting_correspondence[OF assms(2,3,1) hpc assms(5)] by (by100 auto)
  \<comment> \<open>Injectivity from hinj + lift characterization.\<close>
  have h\<phi>_inj: "inj_on \<phi> (top1_fundamental_group_carrier B TB b0)"
  proof (rule inj_onI)
    fix c1 c2
    assume hc1: "c1 \<in> top1_fundamental_group_carrier B TB b0"
       and hc2: "c2 \<in> top1_fundamental_group_carrier B TB b0"
       and heq: "\<phi> c1 = \<phi> c2"
    \<comment> \<open>Extract representatives and lifts from \<phi>'s characterization.\<close>
    obtain f1 ft1 where hf1_in: "f1 \<in> c1" and hf1_loop: "top1_is_loop_on B TB b0 f1"
        and hft1: "top1_is_path_on E TE e0 (\<phi> c1) ft1"
        and hft1p: "\<forall>s\<in>I_set. p (ft1 s) = f1 s"
      using h\<phi>_lift[rule_format, OF hc1] by (by100 blast)
    obtain f2 ft2 where hf2_in: "f2 \<in> c2" and hf2_loop: "top1_is_loop_on B TB b0 f2"
        and hft2: "top1_is_path_on E TE e0 (\<phi> c2) ft2"
        and hft2p: "\<forall>s\<in>I_set. p (ft2 s) = f2 s"
      using h\<phi>_lift[rule_format, OF hc2] by (by100 blast)
    \<comment> \<open>Lifts end at same point since \<phi>(c1) = \<phi>(c2).\<close>
    have hft1_end: "top1_is_path_on E TE e0 (\<phi> c1) ft1" using hft1 .
    have hft2_end: "top1_is_path_on E TE e0 (\<phi> c1) ft2" using hft2 heq by simp
    \<comment> \<open>Apply hinj: lifts of f1, f2 end at same point \<Rightarrow> f1 \<simeq> f2.\<close>
    have "top1_path_homotopic_on B TB b0 b0 f1 f2"
    proof -
      \<comment> \<open>Lifts ft1, ft2 end at \<phi>(c1) = \<phi>(c2), so same point.\<close>
      have hft1_1: "ft1 1 = \<phi> c1" using hft1 unfolding top1_is_path_on_def by simp
      have hft2_1: "ft2 1 = \<phi> c2" using hft2 unfolding top1_is_path_on_def by simp
      have hend_eq: "ft1 1 = ft2 1" using hft1_1 hft2_1 heq by simp
      have hft1': "top1_is_path_on E TE e0 (ft1 1) ft1"
        using hft1 hft1_1 by simp
      have hft2': "top1_is_path_on E TE e0 (ft2 1) ft2"
        using hft2 hft2_1 by simp
      \<comment> \<open>Assemble for hinj.\<close>
      have hexists_ft: "\<exists>ft. top1_is_path_on E TE e0 (ft 1) ft \<and> (\<forall>s\<in>I_set. p (ft s) = f1 s)"
        using hft1' hft1p by (by100 blast)
      have hexists_gt: "\<exists>gt. top1_is_path_on E TE e0 (gt 1) gt \<and> (\<forall>s\<in>I_set. p (gt s) = f2 s)"
        using hft2' hft2p by (by100 blast)
      have hf1_path: "top1_is_path_on B TB b0 b0 f1"
        using hf1_loop unfolding top1_is_loop_on_def .
      have hf2_path: "top1_is_path_on B TB b0 b0 f2"
        using hf2_loop unfolding top1_is_loop_on_def .
      have hcov: "top1_covering_map_on E TE B TB p"
        using assms(1) .
      have he0: "e0 \<in> E" using assms(2) .
      have hpe0: "p e0 = b0" using assms(3) .
      have hall_eq: "\<forall>ft gt. top1_is_path_on E TE e0 (ft 1) ft \<longrightarrow> (\<forall>s\<in>I_set. p (ft s) = f1 s) \<longrightarrow>
               top1_is_path_on E TE e0 (gt 1) gt \<longrightarrow> (\<forall>s\<in>I_set. p (gt s) = f2 s) \<longrightarrow>
               ft 1 = gt 1"
      proof (intro allI impI)
        fix ft gt
        assume hft: "top1_is_path_on E TE e0 (ft 1) ft" and hftp: "\<forall>s\<in>I_set. p (ft s) = f1 s"
           and hgt: "top1_is_path_on E TE e0 (gt 1) gt" and hgtp: "\<forall>s\<in>I_set. p (gt s) = f2 s"
        \<comment> \<open>ft lifts f1 from e0, ft1 also lifts f1 from e0 \<Rightarrow> ft(1) = ft1(1).\<close>
        have "ft 1 = ft1 1"
        proof -
          have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
          have "\<forall>s\<in>I_set. ft s = ft1 s"
            by (rule Lemma_54_1_uniqueness[OF hcov he0 hpe0 hf1_path hft hftp hft1' hft1p])
          thus ?thesis using h1I by (by100 blast)
        qed
        \<comment> \<open>gt lifts f2 from e0, ft2 also lifts f2 from e0 \<Rightarrow> gt(1) = ft2(1).\<close>
        moreover have "gt 1 = ft2 1"
        proof -
          have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
          have "\<forall>s\<in>I_set. gt s = ft2 s"
            by (rule Lemma_54_1_uniqueness[OF hcov he0 hpe0 hf2_path hgt hgtp hft2' hft2p])
          thus ?thesis using h1I by (by100 blast)
        qed
        ultimately show "ft 1 = gt 1" using hend_eq by simp
      qed
      show ?thesis using hinj hf1_loop hf2_loop hexists_ft hexists_gt hall_eq by blast
    qed
    \<comment> \<open>f1 \<simeq> f2 + f1 \<in> c1, f2 \<in> c2 \<Rightarrow> c1 = c2.\<close>
    obtain l1 where hl1: "top1_is_loop_on B TB b0 l1"
        and hc1_eq: "c1 = {h. top1_loop_equiv_on B TB b0 l1 h}"
      using hc1 unfolding top1_fundamental_group_carrier_def by (by100 blast)
    obtain l2 where hl2: "top1_is_loop_on B TB b0 l2"
        and hc2_eq: "c2 = {h. top1_loop_equiv_on B TB b0 l2 h}"
      using hc2 unfolding top1_fundamental_group_carrier_def by (by100 blast)
    have hf1_equiv_l1: "top1_loop_equiv_on B TB b0 l1 f1"
      using hf1_in unfolding hc1_eq by simp
    have hf2_equiv_l2: "top1_loop_equiv_on B TB b0 l2 f2"
      using hf2_in unfolding hc2_eq by simp
    have hf1_f2: "top1_loop_equiv_on B TB b0 f1 f2"
      unfolding top1_loop_equiv_on_def
      using hf1_loop hf2_loop \<open>top1_path_homotopic_on B TB b0 b0 f1 f2\<close>
      by (by100 blast)
    have hl1_l2: "top1_loop_equiv_on B TB b0 l1 l2"
      by (rule top1_loop_equiv_on_trans[OF hTB_outer
            top1_loop_equiv_on_trans[OF hTB_outer hf1_equiv_l1 hf1_f2]
            top1_loop_equiv_on_sym[OF hf2_equiv_l2]])
    show "c1 = c2"
    proof -
      have "\<And>h. top1_loop_equiv_on B TB b0 l1 h \<longleftrightarrow> top1_loop_equiv_on B TB b0 l2 h"
        using hl1_l2 top1_loop_equiv_on_trans[OF hTB_outer]
              top1_loop_equiv_on_trans[OF hTB_outer top1_loop_equiv_on_sym[OF hl1_l2]]
        by (by100 blast)
      thus ?thesis unfolding hc1_eq hc2_eq by auto
    qed
  qed
  show ?thesis unfolding bij_betw_def using h\<phi>_inj h\<phi>_surj by (by100 blast)
qed

text \<open>Helper: subspace of UNIV with top1_open_sets is top1_open_sets itself.\<close>
lemma subspace_topology_UNIV_self:
  "subspace_topology UNIV (T::'a set set) UNIV = T"
  unfolding subspace_topology_def by auto

text \<open>Helper: R is path-connected via the straight-line path t \<mapsto> (1-t)\<cdot>x + t\<cdot>y.\<close>
lemma top1_R_path_connected':
  "top1_path_connected_on (UNIV::real set) top1_open_sets"
proof -
  have hTop: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hpath: "\<forall>x::real\<in>UNIV. \<forall>y::real\<in>UNIV. \<exists>f. top1_is_path_on UNIV top1_open_sets x y f"
  proof (intro ballI)
    fix x y :: real
    assume "x \<in> UNIV" "y \<in> UNIV"
    let ?f = "\<lambda>t::real. (1-t)*x + t*y"
    have hfcont: "continuous_on UNIV ?f"
      by (intro continuous_intros)
    have hmap: "\<And>s. s \<in> I_set \<Longrightarrow> ?f s \<in> UNIV" by simp
    have hcont_sub: "top1_continuous_map_on I_set
          (subspace_topology UNIV top1_open_sets I_set)
          UNIV (subspace_topology UNIV top1_open_sets UNIV) ?f"
      by (rule top1_continuous_map_on_real_subspace_open_sets[OF hmap hfcont])
    have hI_top: "(subspace_topology UNIV top1_open_sets I_set) = I_top"
      unfolding top1_unit_interval_topology_def by rule
    have hUNIV_top: "(subspace_topology UNIV top1_open_sets UNIV) = top1_open_sets"
      by (rule subspace_topology_UNIV_self)
    have hcont: "top1_continuous_map_on I_set I_top UNIV top1_open_sets ?f"
      using hcont_sub unfolding hI_top hUNIV_top .
    have hstart: "?f 0 = x" by simp
    have hend: "?f 1 = y" by simp
    show "\<exists>f. top1_is_path_on UNIV top1_open_sets x y f"
      unfolding top1_is_path_on_def using hcont hstart hend by blast
  qed
  show ?thesis unfolding top1_path_connected_on_def using hTop hpath by simp
qed

definition top1_slh_ext :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<times> real \<Rightarrow> real" where
  "top1_slh_ext f x0 p = (1 - snd p) * f (max 0 (min 1 (fst p))) + snd p * x0"

lemma top1_slh_ext_continuous:
  assumes "continuous_on I_set f"
  shows "continuous_on UNIV (top1_slh_ext f x0)"
proof -
  have h2: "continuous_on UNIV (\<lambda>x::real. f (max 0 (min 1 x)))"
    by (rule continuous_on_compose2[OF assms]) (intro continuous_intros, auto simp: top1_unit_interval_def)
  show ?thesis unfolding top1_slh_ext_def
    by (intro continuous_intros continuous_on_compose2[OF h2 continuous_on_fst]) auto
qed

lemma top1_slh_ext_agrees:
  "p \<in> I_set \<times> I_set \<Longrightarrow>
   top1_slh_ext f x0 p = (1 - snd p) * f (fst p) + snd p * x0"
  unfolding top1_slh_ext_def top1_unit_interval_def by auto

lemma top1_continuous_map_on_II_to_UNIV:
  fixes F :: "real \<times> real \<Rightarrow> real"
  assumes "continuous_on UNIV F"
  shows "top1_continuous_map_on (I_set \<times> I_set) II_topology (UNIV::real set) top1_open_sets F"
proof -
  have "\<forall>V\<in>(top1_open_sets :: real set set). {p \<in> I_set \<times> I_set. F p \<in> V} \<in> II_topology"
  proof
    fix V :: "real set" assume "V \<in> (top1_open_sets :: real set set)"
    hence hVo: "open V" unfolding top1_open_sets_def by blast
    have hFV: "open (F -` V)" by (rule open_vimage[OF hVo assms])
    hence "F -` V \<in> (top1_open_sets :: (real\<times>real) set set)" unfolding top1_open_sets_def by blast
    hence "F -` V \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
      using product_topology_on_open_sets_real2 by metis
    hence "(I_set \<times> I_set) \<inter> (F -` V) \<in> product_topology_on I_top I_top"
      unfolding II_topology_eq_subspace subspace_topology_def by blast
    moreover have "{p \<in> I_set \<times> I_set. F p \<in> V} = (I_set \<times> I_set) \<inter> (F -` V)" by auto
    ultimately show "{p \<in> I_set \<times> I_set. F p \<in> V} \<in> II_topology" unfolding II_topology_def by simp
  qed
  thus ?thesis unfolding top1_continuous_map_on_def by simp
qed

text \<open>Helper: R is simply connected — any loop f is homotopic to constant via
  F(s, t) = (1 - t) * f(s) + t * x0 (straight-line homotopy to the basepoint).\<close>
lemma top1_R_simply_connected':
  "top1_simply_connected_on (UNIV::real set) top1_open_sets"
proof -
  have hpc: "top1_path_connected_on (UNIV::real set) top1_open_sets"
    by (rule top1_R_path_connected')
  have hloops: "\<forall>x0\<in>(UNIV::real set). \<forall>f. top1_is_loop_on UNIV top1_open_sets x0 f \<longrightarrow>
        top1_path_homotopic_on UNIV top1_open_sets x0 x0 f (top1_constant_path x0)"
  proof (intro ballI allI impI)
    fix x0 :: real and f assume hloop: "top1_is_loop_on UNIV top1_open_sets x0 f"
    have hfcont: "top1_continuous_map_on I_set I_top UNIV top1_open_sets f"
      using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by blast
    have hf0: "f 0 = x0" and hf1: "f 1 = x0"
      using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
    \<comment> \<open>Use top1_slh_ext as the homotopy (agrees with (1-t)*f(s)+t*x0 on I\<times>I).\<close>
    have hf_cont_I: "continuous_on I_set f"
      unfolding continuous_on_open_invariant
    proof (intro allI impI)
      fix B :: "real set" assume hBo: "open B"
      have "B \<in> top1_open_sets" using hBo unfolding top1_open_sets_def by blast
      hence hpre: "{s \<in> I_set. f s \<in> B} \<in> I_top"
        using hfcont unfolding top1_continuous_map_on_def by blast
      hence "{s \<in> I_set. f s \<in> B} \<in> subspace_topology UNIV top1_open_sets I_set"
        unfolding top1_unit_interval_topology_def .
      then obtain W where hW: "W \<in> top1_open_sets" and heq: "{s \<in> I_set. f s \<in> B} = I_set \<inter> W"
        unfolding subspace_topology_def by blast
      have "open W" using hW unfolding top1_open_sets_def by blast
      moreover have "W \<inter> I_set = f -` B \<inter> I_set" using heq by (by100 blast)
      ultimately show "\<exists>A. open A \<and> A \<inter> I_set = f -` B \<inter> I_set" by blast
    qed
    have hext_cont: "continuous_on UNIV (top1_slh_ext f x0)"
      by (rule top1_slh_ext_continuous[OF hf_cont_I])
    have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology UNIV top1_open_sets (top1_slh_ext f x0)"
      by (rule top1_continuous_map_on_II_to_UNIV[OF hext_cont])
    have hfpath: "top1_is_path_on UNIV top1_open_sets x0 x0 f"
      using hloop unfolding top1_is_loop_on_def .
    have hTR: "is_topology_on (UNIV :: real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hcpath: "top1_is_path_on UNIV top1_open_sets x0 x0 (top1_constant_path x0)"
      by (rule top1_constant_path_is_path[OF hTR]) simp
    have hFs0: "\<forall>s\<in>I_set. top1_slh_ext f x0 (s, 0) = f s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "top1_slh_ext f x0 (s, 0) = (1 - 0) * f s + 0 * x0"
        using top1_slh_ext_agrees[of "(s, 0)"] hs unfolding top1_unit_interval_def by auto
      thus "top1_slh_ext f x0 (s, 0) = f s" by simp
    qed
    have hFs1: "\<forall>s\<in>I_set. top1_slh_ext f x0 (s, 1) = (\<lambda>_. x0) s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "top1_slh_ext f x0 (s, 1) = (1 - 1) * f s + 1 * x0"
        using top1_slh_ext_agrees[of "(s, 1)"] hs unfolding top1_unit_interval_def by auto
      thus "top1_slh_ext f x0 (s, 1) = x0" by simp
    qed
    have hF0t: "\<forall>t\<in>I_set. top1_slh_ext f x0 (0, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have "top1_slh_ext f x0 (0, t) = (1 - t) * f 0 + t * x0"
        using top1_slh_ext_agrees[of "(0, t)"] ht unfolding top1_unit_interval_def by auto
      thus "top1_slh_ext f x0 (0, t) = x0" using hf0 by (simp add: algebra_simps)
    qed
    have hF1t: "\<forall>t\<in>I_set. top1_slh_ext f x0 (1, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have "top1_slh_ext f x0 (1, t) = (1 - t) * f 1 + t * x0"
        using top1_slh_ext_agrees[of "(1, t)"] ht unfolding top1_unit_interval_def by auto
      thus "top1_slh_ext f x0 (1, t) = x0" using hf1 by (simp add: algebra_simps)
    qed
    show "top1_path_homotopic_on UNIV top1_open_sets x0 x0 f (top1_constant_path x0)"
      unfolding top1_path_homotopic_on_def top1_constant_path_def
      using hfpath hcpath hF_cont hFs0 hFs1 hF0t hF1t
      unfolding top1_is_path_on_def top1_constant_path_def by blast
  qed
  show ?thesis
    unfolding top1_simply_connected_on_def using hpc hloops by blast
qed

text \<open>Helper: the fiber p^{-1}(b_0) of the canonical S^1 covering is Z.
  top1_R_to_S1 x = (1, 0) iff cos(2\<pi>x) = 1 and sin(2\<pi>x) = 0 iff 2\<pi>x = 2\<pi>n, i.e. x = n \<in> Z.\<close>
lemma top1_R_to_S1_fiber_is_Z':
  "{x::real. top1_R_to_S1 x = (1, 0)} = {of_int n | n. True}"
proof (intro subset_antisym subsetI)
  fix x :: real assume "x \<in> {x. top1_R_to_S1 x = (1, 0)}"
  hence hcos: "cos (2 * pi * x) = 1" and hsin: "sin (2 * pi * x) = 0"
    unfolding top1_R_to_S1_def by simp_all
  from hcos obtain n :: int where hn: "2 * pi * x = 2 * pi * of_int n"
    by (auto simp: cos_one_2pi_int)
  have "x = of_int n" using hn by simp
  thus "x \<in> {of_int n | n. True}" by blast
next
  fix x :: real assume "x \<in> {of_int n | n. True}"
  then obtain n :: int where hn: "x = of_int n" by blast
  have "cos (2 * pi * of_int n) = 1"
    using cos_int_2pin by (simp add: mult.commute)
  moreover have "sin (2 * pi * of_int n) = 0"
    using sin_int_2pin by (simp add: mult.commute)
  ultimately show "x \<in> {x. top1_R_to_S1 x = (1, 0)}"
    unfolding top1_R_to_S1_def using hn by simp
qed

text \<open>Periodicity of the covering map: p(x + n) = p(x) for integer n.
  This is the key property enabling the homomorphism proof for \<pi>_1(S^1) \<cong> Z.\<close>
lemma top1_R_to_S1_int_shift:
  "top1_R_to_S1 (x + of_int n) = top1_R_to_S1 x"
proof -
  have hexp: "2 * pi * (x + of_int n) = 2 * pi * x + (2 * pi) * of_int n"
    by (simp add: algebra_simps)
  have hc: "cos ((2 * pi) * of_int n) = 1" by (rule cos_int_2pin)
  have hs: "sin ((2 * pi) * of_int n) = 0" by (rule sin_int_2pin)
  have hcos: "cos (2 * pi * (x + of_int n)) = cos (2 * pi * x)"
    by (simp add: hexp cos_add hc hs)
  have hsin: "sin (2 * pi * (x + of_int n)) = sin (2 * pi * x)"
    by (simp add: hexp sin_add hc hs)
  show ?thesis unfolding top1_R_to_S1_def using hcos hsin by (by100 simp)
qed

lemma top1_R_to_S1_int_shift':
  "top1_R_to_S1 (of_int n + x) = top1_R_to_S1 x"
  using top1_R_to_S1_int_shift[of x n] by (simp add: add.commute)

text \<open>Key property: the translated lift f'(s) = n + f(s) covers the same base path as f.
  p(n + f(s)) = p(f(s)) by periodicity.\<close>
lemma top1_R_to_S1_translate_lift:
  "top1_R_to_S1 \<circ> (\<lambda>s. of_int n + f s) = top1_R_to_S1 \<circ> f"
  by (rule ext) (simp add: top1_R_to_S1_int_shift')

text \<open>If gtilde is a lift of g (loop at b0) starting at 0, then
  (\<lambda>s. of_int n + gtilde s) is a lift of g starting at n, by periodicity.\<close>
lemma top1_R_to_S1_translated_lift_is_lift:
  assumes hgt: "top1_is_path_on UNIV top1_open_sets (0::real) (gtilde 1) gtilde"
      and hgtp: "\<forall>s\<in>I_set. top1_R_to_S1 (gtilde s) = g s"
  shows "\<forall>s\<in>I_set. top1_R_to_S1 (of_int n + gtilde s) = g s"
  using hgtp by (simp add: top1_R_to_S1_int_shift')

text \<open>The translated lift starts at n (when gtilde starts at 0).\<close>
lemma top1_R_to_S1_translated_lift_start:
  assumes "gtilde 0 = (0::real)"
  shows "(of_int n + gtilde 0) = of_int n"
  using assms by simp

text \<open>The translated lift ends at n + gtilde(1).\<close>
lemma top1_R_to_S1_translated_lift_end:
  "(of_int n + gtilde 1) = of_int n + gtilde 1" by simp

text \<open>Helper: two elements in the same fundamental group class are loop-equivalent.\<close>
lemma fundamental_group_class_members_equiv:
  assumes hTX: "is_topology_on X TX"
      and hc: "c \<in> top1_fundamental_group_carrier X TX x0"
      and hf: "f \<in> c" and hg: "g \<in> c"
  shows "top1_loop_equiv_on X TX x0 f g"
proof -
  obtain f0 where hc_eq: "c = {h. top1_loop_equiv_on X TX x0 f0 h}"
    using hc unfolding top1_fundamental_group_carrier_def by (by100 auto)
  have hf0_f: "top1_loop_equiv_on X TX x0 f0 f" using hf hc_eq by simp
  have hf0_g: "top1_loop_equiv_on X TX x0 f0 g" using hg hc_eq by simp
  have hf_f0: "top1_loop_equiv_on X TX x0 f f0"
    by (rule top1_loop_equiv_on_sym[OF hf0_f])
  show ?thesis by (rule top1_loop_equiv_on_trans[OF hTX hf_f0 hf0_g])
qed

text \<open>Helper: fundamental group mul equals equivalence class of f*g when f \<in> c, g \<in> d.\<close>
lemma fundamental_group_mul_eq_class:
  assumes hTX: "is_topology_on X TX"
      and hc: "c \<in> top1_fundamental_group_carrier X TX x0"
      and hd: "d \<in> top1_fundamental_group_carrier X TX x0"
      and hf: "f \<in> c" and hg: "g \<in> d"
      and hfl: "top1_is_loop_on X TX x0 f" and hgl: "top1_is_loop_on X TX x0 g"
  shows "top1_fundamental_group_mul X TX x0 c d
      = {h. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"
proof -
  have hf_path: "top1_is_path_on X TX x0 x0 f" using hfl unfolding top1_is_loop_on_def .
  have hg_path: "top1_is_path_on X TX x0 x0 g" using hgl unfolding top1_is_loop_on_def .
  have hfg_loop: "top1_is_loop_on X TX x0 (top1_path_product f g)"
    unfolding top1_is_loop_on_def by (rule top1_path_product_is_path[OF hTX hf_path hg_path])
  \<comment> \<open>(\<subseteq>): if h \<in> mul c d, then \<exists>f'\<in>c, g'\<in>d with equiv(f'*g') h.
     f'≃f and g'≃g, so f'*g'≃f*g, hence equiv(f*g) h.\<close>
  have hsub1: "top1_fundamental_group_mul X TX x0 c d
      \<subseteq> {h. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"
  proof
    fix h assume hh: "h \<in> top1_fundamental_group_mul X TX x0 c d"
    then obtain f' g' where hf': "f' \<in> c" and hg': "g' \<in> d"
        and hfg'h: "top1_loop_equiv_on X TX x0 (top1_path_product f' g') h"
      unfolding top1_fundamental_group_mul_def by (by100 blast)
    have hf'_f: "top1_loop_equiv_on X TX x0 f' f"
      by (rule fundamental_group_class_members_equiv[OF hTX hc hf' hf])
    have hg'_g: "top1_loop_equiv_on X TX x0 g' g"
      by (rule fundamental_group_class_members_equiv[OF hTX hd hg' hg])
    have hf'_f_hom: "top1_path_homotopic_on X TX x0 x0 f' f"
      using hf'_f unfolding top1_loop_equiv_on_def by (by100 blast)
    have hg'_g_hom: "top1_path_homotopic_on X TX x0 x0 g' g"
      using hg'_g unfolding top1_loop_equiv_on_def by (by100 blast)
    have hf'_path: "top1_is_path_on X TX x0 x0 f'"
      using hf'_f unfolding top1_loop_equiv_on_def top1_is_loop_on_def by (by100 blast)
    have hg'_path: "top1_is_path_on X TX x0 x0 g'"
      using hg'_g unfolding top1_loop_equiv_on_def top1_is_loop_on_def by (by100 blast)
    have hf'g'_fg: "top1_path_homotopic_on X TX x0 x0
        (top1_path_product f' g') (top1_path_product f g)"
      by (rule Lemma_51_1_path_homotopic_trans[OF hTX
          path_homotopic_product_left[OF hTX hf'_f_hom hg'_path]
          path_homotopic_product_right[OF hTX hg'_g_hom hf_path]])
    have hf'g'_loop: "top1_is_loop_on X TX x0 (top1_path_product f' g')"
      unfolding top1_is_loop_on_def by (rule top1_path_product_is_path[OF hTX hf'_path hg'_path])
    have hfg_f'g': "top1_loop_equiv_on X TX x0 (top1_path_product f g) (top1_path_product f' g')"
      unfolding top1_loop_equiv_on_def using hfg_loop hf'g'_loop
        Lemma_51_1_path_homotopic_sym[OF hf'g'_fg] by (by100 blast)
    show "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"
      using top1_loop_equiv_on_trans[OF hTX hfg_f'g' hfg'h] by simp
  qed
  \<comment> \<open>(\<supseteq>): if equiv(f*g) h, take f'=f, g'=g.\<close>
  have hsub2: "{h. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}
      \<subseteq> top1_fundamental_group_mul X TX x0 c d"
  proof
    fix h assume "h \<in> {h. top1_loop_equiv_on X TX x0 (top1_path_product f g) h}"
    hence hh: "top1_loop_equiv_on X TX x0 (top1_path_product f g) h" by simp
    show "h \<in> top1_fundamental_group_mul X TX x0 c d"
      unfolding top1_fundamental_group_mul_def using hh hf hg by (by100 blast)
  qed
  show ?thesis using hsub1 hsub2 by (by100 blast)
qed

(** from \<S>54 Theorem 54.5: fundamental group of S^1 is isomorphic to Z.
    Munkres' proof: use covering p: R \<rightarrow> S^1 (Theorem 53.1). Since R is simply
    connected, the lifting correspondence (Theorem 54.4) is bijective onto
    p^{-1}(b_0) = Z. Then show it's a homomorphism. **)
theorem Theorem_54_5:
  "\<exists>\<phi>. bij_betw \<phi> (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
    (UNIV::int set)"
proof -
  have hcov: "top1_covering_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
    by (rule Theorem_53_1)
  have h0R: "(0::real) \<in> UNIV" by simp
  have hp0: "top1_R_to_S1 0 = (1, 0)"
    unfolding top1_R_to_S1_def by simp
  have hRsc: "top1_simply_connected_on (UNIV::real set) top1_open_sets"
    by (rule top1_R_simply_connected')
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
  proof -
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using product_topology_on_is_topology_on[OF hTR hTR] by simp
    show ?thesis unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR2]) simp
  qed
  obtain \<phi>' where hbij: "bij_betw \<phi>'
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      {x\<in>(UNIV::real set). top1_R_to_S1 x = (1, 0)}"
    using Theorem_54_4_bijective_simply_connected[OF hcov h0R hp0 hRsc hTS1] by blast
  have hfiber_Z: "\<exists>\<psi>. bij_betw \<psi> {x\<in>(UNIV::real set). top1_R_to_S1 x = (1, 0)} (UNIV::int set)"
  proof -
    have hfib_eq: "{x::real. top1_R_to_S1 x = (1, 0)} = {of_int n | n::int. True}"
      using top1_R_to_S1_fiber_is_Z' .
    have hinj: "inj_on (\<lambda>x::real. floor x) {x::real. top1_R_to_S1 x = (1, 0)}"
    proof (rule inj_onI)
      fix a b assume "a \<in> {x. top1_R_to_S1 x = (1, 0)}" "b \<in> {x. top1_R_to_S1 x = (1, 0)}"
      hence "\<exists>n. a = of_int n" "\<exists>n. b = of_int n" using hfib_eq by auto
      thus "floor a = floor b \<Longrightarrow> a = b" by auto
    qed
    have hsurj: "(\<lambda>x::real. floor x) ` {x::real. top1_R_to_S1 x = (1, 0)} = UNIV"
    proof
      show "(\<lambda>x::real. floor x) ` {x. top1_R_to_S1 x = (1, 0)} \<subseteq> UNIV" by simp
      show "UNIV \<subseteq> (\<lambda>x::real. floor x) ` {x. top1_R_to_S1 x = (1, 0)}"
      proof
        fix n :: int assume "n \<in> UNIV"
        have "of_int n \<in> {x::real. top1_R_to_S1 x = (1, 0)}" using hfib_eq by auto
        moreover have "floor (of_int n :: real) = n" by simp
        ultimately show "n \<in> (\<lambda>x::real. floor x) ` {x. top1_R_to_S1 x = (1, 0)}" by force
      qed
    qed
    show ?thesis using hinj hsurj unfolding bij_betw_def by auto
  qed
  obtain \<psi> where h\<psi>: "bij_betw \<psi> {x\<in>(UNIV::real set). top1_R_to_S1 x = (1, 0)} (UNIV::int set)"
    using hfiber_Z by blast
  have hcomp: "bij_betw (\<psi> \<circ> \<phi>')
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) (UNIV::int set)"
    by (rule bij_betw_trans[OF hbij h\<psi>])
  thus ?thesis by blast
qed

text \<open>The integers Z as an additive abelian group (moved here to support Theorem_54_5_iso).\<close>
definition top1_Z_group :: "int set" where
  "top1_Z_group = UNIV"

definition top1_Z_mul :: "int \<Rightarrow> int \<Rightarrow> int" where
  "top1_Z_mul a b = a + b"

definition top1_Z_id :: "int" where
  "top1_Z_id = 0"

definition top1_Z_invg :: "int \<Rightarrow> int" where
  "top1_Z_invg a = - a"

lemma top1_Z_is_abelian_group:
  "top1_is_abelian_group_on top1_Z_group top1_Z_mul top1_Z_id top1_Z_invg"
  unfolding top1_is_abelian_group_on_def top1_is_group_on_def
            top1_Z_group_def top1_Z_mul_def top1_Z_id_def top1_Z_invg_def
  by auto

(** Strengthened version: \<pi>_1(S^1, (1,0)) is isomorphic to Z as groups (not just bijective). **)
theorem Theorem_54_5_iso:
  "top1_groups_isomorphic_on
     (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
     (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
     top1_Z_group
     top1_Z_mul"
proof -
  \<comment> \<open>Munkres 54.5: Use covering p: R \<rightarrow> S^1, with R simply connected.\<close>
  \<comment> \<open>Step 1: \<phi> is bijective (from Theorem 54.4 + R simply connected).\<close>
  have hbij: "\<exists>\<phi>. bij_betw \<phi> (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (UNIV::int set)"
    using Theorem_54_5 by (by100 blast)
  \<comment> \<open>Step 2: \<phi> is a homomorphism.
     For lifts ftilde(1) = n, gtilde(1) = m, define g'(s) = n + gtilde(s).
     Since p(n + x) = p(x), g' lifts g starting at n. So ftilde * g' lifts f * g,
     ending at n + m. Hence \<phi>([f]*[g]) = n + m = \<phi>([f]) + \<phi>([g]).\<close>
  \<comment> \<open>The bijection maps endpoints of lifts to integers.
     Homomorphism: endpoints add because translated lifts concatenate.\<close>
  \<comment> \<open>We construct \<phi> from the covering map: \<phi>([f]) = lift endpoint.
     Homomorphism follows from the key lemma: translated lifts concatenate.
     Specifically: if ftilde lifts f from 0 to n, and gtilde lifts g from 0 to m,
     then (\<lambda>s. n + gtilde s) lifts g from n to n+m (using p(n+x) = p(x)),
     and ftilde * (\<lambda>s. n + gtilde s) lifts f*g from 0 to n+m.\<close>
  have hcov: "top1_covering_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
    by (rule Theorem_53_1)
  have hp0: "top1_R_to_S1 0 = (1, 0)"
    unfolding top1_R_to_S1_def by simp
  have h0R: "(0::real) \<in> (UNIV::real set)" by simp
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    unfolding top1_S1_topology_def
    by (rule subspace_topology_is_topology_on[OF
          product_topology_on_is_topology_on[OF
            top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
            simplified]]) simp
  \<comment> \<open>Step 1: Define \<phi> via lifting correspondence (already have bijection).\<close>
  \<comment> \<open>The lifting correspondence sends [f] to the endpoint of the unique lift
     starting at 0. This endpoint lies in p^{-1}(1,0) = Z.\<close>
  have hpc: "top1_path_connected_on (UNIV::real set) top1_open_sets"
    using top1_R_simply_connected' top1_simply_connected_on_path_connected by (by100 blast)
  obtain \<phi>' where h\<phi>'_mem: "\<forall>c\<in>top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0).
        \<phi>' c \<in> {e\<in>(UNIV::real set). top1_R_to_S1 e = (1, 0)}"
      and h\<phi>'_surj: "\<phi>' ` (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
        = {e\<in>(UNIV::real set). top1_R_to_S1 e = (1, 0)}"
      and h\<phi>'_lift: "\<forall>c\<in>top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0).
        \<exists>f ft. f \<in> c \<and> top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
          \<and> top1_is_path_on (UNIV::real set) top1_open_sets 0 (\<phi>' c) ft
          \<and> (\<forall>s\<in>I_set. top1_R_to_S1 (ft s) = f s)"
    using Theorem_54_4_lifting_correspondence[OF h0R hp0 hcov hpc hTS1] by (by100 auto)
  have h\<phi>'_bij: "bij_betw \<phi>'
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      {x\<in>(UNIV::real set). top1_R_to_S1 x = (1, 0)}"
    unfolding bij_betw_def
  proof (intro conjI)
    show "inj_on \<phi>' (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))"
    proof (rule inj_onI)
      fix c1 c2
      assume hc1: "c1 \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
         and hc2: "c2 \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
         and heq: "\<phi>' c1 = \<phi>' c2"
      obtain f1 ft1 where "f1 \<in> c1" and hf1l: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f1"
          and hft1: "top1_is_path_on (UNIV::real set) top1_open_sets 0 (\<phi>' c1) ft1"
          and hft1p: "\<forall>s\<in>I_set. top1_R_to_S1 (ft1 s) = f1 s"
        using h\<phi>'_lift[rule_format, OF hc1] by (by100 auto)
      obtain f2 ft2 where "f2 \<in> c2" and hf2l: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f2"
          and hft2: "top1_is_path_on (UNIV::real set) top1_open_sets 0 (\<phi>' c2) ft2"
          and hft2p: "\<forall>s\<in>I_set. top1_R_to_S1 (ft2 s) = f2 s"
        using h\<phi>'_lift[rule_format, OF hc2] by (by100 auto)
      \<comment> \<open>Since \<phi>'(c1) = \<phi>'(c2) and lifts end at same point, by Thm 54.3 f1 \<simeq> f2.\<close>
      have hft2': "top1_is_path_on (UNIV::real set) top1_open_sets 0 (\<phi>' c1) ft2"
        using hft2 heq by simp
      have hTE: "is_topology_on (UNIV::real set) top1_open_sets"
        by (rule top1_open_sets_is_topology_on_UNIV)
      have hf1_eq_f2: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f1 f2"
      proof -
        \<comment> \<open>Lifts ft1, ft2 start at 0 and end at same point (\<phi>'(c1) = \<phi>'(c2)).
           E = R is simply connected. So ft1 \<simeq> ft2 in R.
           Project: p \<circ> ft1 \<simeq> p \<circ> ft2 in S^1, i.e., f1 \<simeq> f2.\<close>
        have hft_hom: "top1_path_homotopic_on (UNIV::real set) top1_open_sets 0 (\<phi>' c1) ft1 ft2"
          by (rule simply_connected_paths_homotopic[OF top1_R_simply_connected' hft1 hft2' h0R])
        have hp_cont: "top1_continuous_map_on (UNIV::real set) top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
          using hcov unfolding top1_covering_map_on_def by (by100 blast)
        have hpft: "top1_path_homotopic_on top1_S1 top1_S1_topology (top1_R_to_S1 0) (top1_R_to_S1 (\<phi>' c1))
            (top1_R_to_S1 \<circ> ft1) (top1_R_to_S1 \<circ> ft2)"
          by (rule continuous_preserves_path_homotopic[OF hTE hTS1 hp_cont hft_hom])
        have hpft_simp: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
            (top1_R_to_S1 \<circ> ft1) (top1_R_to_S1 \<circ> ft2)"
        proof -
          have "top1_R_to_S1 0 = (1, 0)" using hp0 .
          moreover have "top1_R_to_S1 (\<phi>' c1) = (1, 0)"
            using h\<phi>'_mem[rule_format, OF hc1] by simp
          ultimately show ?thesis using hpft by simp
        qed
        \<comment> \<open>p \<circ> ft1 = f1 on I_set, p \<circ> ft2 = f2 on I_set. Transfer homotopy.\<close>
        have hpft1_f1: "\<forall>s\<in>I_set. (top1_R_to_S1 \<circ> ft1) s = f1 s" using hft1p by simp
        have hpft2_f2: "\<forall>s\<in>I_set. (top1_R_to_S1 \<circ> ft2) s = f2 s" using hft2p by simp
        have hpft1_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) (top1_R_to_S1 \<circ> ft1)"
          using hpft_simp unfolding top1_path_homotopic_on_def top1_is_loop_on_def by (by100 blast)
        have hpft2_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) (top1_R_to_S1 \<circ> ft2)"
          using hpft_simp unfolding top1_path_homotopic_on_def top1_is_loop_on_def by (by100 blast)
        have hf1_pft1: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f1 (top1_R_to_S1 \<circ> ft1)"
          using conjunct2[OF loop_agree_on_I[OF hf1l hpft1_f1]] .
        have hf2_pft2: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f2 (top1_R_to_S1 \<circ> ft2)"
          using conjunct2[OF loop_agree_on_I[OF hf2l hpft2_f2]] .
        show ?thesis
          by (rule Lemma_51_1_path_homotopic_trans[OF hTS1
              hf1_pft1
              Lemma_51_1_path_homotopic_trans[OF hTS1
                hpft_simp
                Lemma_51_1_path_homotopic_sym[OF hf2_pft2]]])
      qed
      show "c1 = c2"
      proof -
        \<comment> \<open>c1 \<in> carrier means c1 = {g. equiv f' g} for some f'. f1 \<in> c1 implies equiv f' f1.
           By transitivity, c1 = {g. equiv f1 g}. Similarly c2 = {g. equiv f2 g}.
           f1 \<simeq> f2 gives class equality.\<close>
        obtain f1' where hc1_eq: "c1 = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f1' g}"
            and hf1'_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f1'"
          using hc1 unfolding top1_fundamental_group_carrier_def by (by100 auto)
        have hf1'_f1: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f1' f1"
          using \<open>f1 \<in> c1\<close> hc1_eq by simp
        have hf1_f1': "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f1 f1'"
          by (rule top1_loop_equiv_on_sym[OF hf1'_f1])
        have hc1_f1: "c1 = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f1 g}"
          apply (rule set_eqI)
          unfolding hc1_eq mem_Collect_eq
          using top1_loop_equiv_on_trans[OF hTS1 hf1_f1'] top1_loop_equiv_on_trans[OF hTS1 hf1'_f1]
          by (by100 blast)
        obtain f2' where hc2_eq: "c2 = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f2' g}"
          using hc2 unfolding top1_fundamental_group_carrier_def by (by100 auto)
        have hf2'_f2: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f2' f2"
          using \<open>f2 \<in> c2\<close> hc2_eq by simp
        have hf2_f2': "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f2 f2'"
          by (rule top1_loop_equiv_on_sym[OF hf2'_f2])
        have hc2_f2: "c2 = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f2 g}"
          apply (rule set_eqI)
          unfolding hc2_eq mem_Collect_eq
          using top1_loop_equiv_on_trans[OF hTS1 hf2_f2'] top1_loop_equiv_on_trans[OF hTS1 hf2'_f2]
          by (by100 blast)
        \<comment> \<open>f1 \<simeq> f2 implies {g. equiv f1 g} = {g. equiv f2 g}.\<close>
        have hf1_f2_equiv: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f1 f2"
          unfolding top1_loop_equiv_on_def using hf1l hf2l hf1_eq_f2 by (by100 blast)
        have hf2_f1_equiv: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f2 f1"
          by (rule top1_loop_equiv_on_sym[OF hf1_f2_equiv])
        have hclass_eq: "{g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f1 g}
            = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f2 g}"
          apply (rule set_eqI)
          apply (rule iffI)
          using top1_loop_equiv_on_trans[OF hTS1 hf2_f1_equiv] apply (by100 blast)
          using top1_loop_equiv_on_trans[OF hTS1 hf1_f2_equiv] apply (by100 blast)
          done
        show ?thesis using hc1_f1 hc2_f2 hclass_eq by simp
      qed
    qed
  next
    show "\<phi>' ` top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)
        = {x \<in> UNIV. top1_R_to_S1 x = (1, 0)}"
      using h\<phi>'_surj by simp
  qed
  \<comment> \<open>\<phi>'([f]) is the endpoint of the lift of f. Since the endpoint is an integer,
     define \<phi>([f]) = floor(\<phi>'([f])).\<close>
  define \<phi> where "\<phi> = (\<lambda>c. \<lfloor>\<phi>' c\<rfloor>)"
  \<comment> \<open>Step 2: \<phi> is bijective (composition of bijections).\<close>
  have h\<phi>_bij: "bij_betw \<phi>
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      (UNIV::int set)"
  proof -
    have hfib: "{x::real. top1_R_to_S1 x = (1, 0)} = {of_int n |n::int. True}"
      using top1_R_to_S1_fiber_is_Z' .
    have hfloor_inj: "inj_on floor {x::real. top1_R_to_S1 x = (1, 0)}"
    proof (rule inj_onI)
      fix a b :: real
      assume "a \<in> {x. top1_R_to_S1 x = (1, 0)}" "b \<in> {x. top1_R_to_S1 x = (1, 0)}"
      hence "a \<in> {of_int n |n::int. True}" "b \<in> {of_int n |n::int. True}"
        using hfib by (by100 blast)+
      then obtain na nb :: int where hna: "a = of_int na" and hnb: "b = of_int nb"
        by (by100 auto)
      assume "\<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>"
      thus "a = b" using hna hnb by (by100 simp)
    qed
    have hfloor_surj: "floor ` {x::real. top1_R_to_S1 x = (1, 0)} = (UNIV::int set)"
    proof
      show "floor ` {x::real. top1_R_to_S1 x = (1, 0)} \<subseteq> UNIV" by (by100 simp)
    next
      show "UNIV \<subseteq> floor ` {x::real. top1_R_to_S1 x = (1, 0)}"
      proof
        fix n :: int
        have "of_int n \<in> {x::real. top1_R_to_S1 x = (1, 0)}" using hfib by (by100 auto)
        moreover have "\<lfloor>of_int n :: real\<rfloor> = n" by simp
        ultimately show "n \<in> floor ` {x::real. top1_R_to_S1 x = (1, 0)}" by (by100 force)
      qed
    qed
    have hfloor_bij: "bij_betw floor {x::real. top1_R_to_S1 x = (1, 0)} (UNIV::int set)"
      unfolding bij_betw_def using hfloor_inj hfloor_surj by (by100 blast)
    have heq: "{x \<in> (UNIV::real set). top1_R_to_S1 x = (1, 0)} = {x::real. top1_R_to_S1 x = (1, 0)}"
      by (by100 simp)
    have hcomp: "bij_betw (floor \<circ> \<phi>')
        (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) (UNIV::int set)"
      by (rule bij_betw_trans[OF h\<phi>'_bij[unfolded heq] hfloor_bij])
    have "\<phi> = floor \<circ> \<phi>'" unfolding \<phi>_def comp_def by (rule refl)
    show ?thesis using hcomp unfolding \<open>\<phi> = floor \<circ> \<phi>'\<close> .
  qed
  \<comment> \<open>Step 3: \<phi> is a homomorphism.
     Key: if lift of f from 0 ends at n and lift of g from 0 ends at m,
     then lift of f*g from 0 ends at n+m.\<close>
  have h\<phi>_hom: "\<forall>c\<in>top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0).
      \<forall>d\<in>top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0).
      \<phi> (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0) c d)
      = \<phi> c + \<phi> d"
  proof (intro ballI)
    fix c d
    assume hc: "c \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
       and hd: "d \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
    \<comment> \<open>Let f, g be representative loops. ftilde, gtilde their lifts from 0.
       n = ftilde(1) (integer), m = gtilde(1) (integer).
       Translated lift: s \<mapsto> n + gtilde(s) covers g starting at n.
       Concatenation of ftilde with translated-gtilde covers f*g from 0 to n+m.
       By uniqueness of lifts, the lift of f*g from 0 ends at n+m.
       \<phi>(c*d) = floor(n+m) = floor(n) + floor(m) = \<phi>(c) + \<phi>(d).\<close>
    \<comment> \<open>Extract lifts for c and d.\<close>
    obtain f ft where hf_in_c: "f \<in> c" and hfl: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f"
        and hft: "top1_is_path_on (UNIV::real set) top1_open_sets 0 (\<phi>' c) ft"
        and hftp: "\<forall>s\<in>I_set. top1_R_to_S1 (ft s) = f s"
      using h\<phi>'_lift[rule_format, OF hc] by (by100 auto)
    obtain g gt where hg_in_d: "g \<in> d" and hgl: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) g"
        and hgt: "top1_is_path_on (UNIV::real set) top1_open_sets 0 (\<phi>' d) gt"
        and hgtp: "\<forall>s\<in>I_set. top1_R_to_S1 (gt s) = g s"
      using h\<phi>'_lift[rule_format, OF hd] by (by100 auto)
    \<comment> \<open>n = \<phi>'(c) is an integer (in the fiber). Similarly m = \<phi>'(d).\<close>
    let ?n = "\<phi>' c" and ?m = "\<phi>' d"
    have hn_int: "\<exists>k::int. ?n = of_int k"
    proof -
      have "?n \<in> {x. top1_R_to_S1 x = (1, 0)}" using h\<phi>'_mem[rule_format, OF hc] by simp
      thus ?thesis using top1_R_to_S1_fiber_is_Z' by (by100 auto)
    qed
    have hm_int: "\<exists>k::int. ?m = of_int k"
    proof -
      have "?m \<in> {x. top1_R_to_S1 x = (1, 0)}" using h\<phi>'_mem[rule_format, OF hd] by simp
      thus ?thesis using top1_R_to_S1_fiber_is_Z' by (by100 auto)
    qed
    \<comment> \<open>Translated lift: s \<mapsto> n + gt(s) lifts g starting at n.
       p(n + gt(s)) = p(gt(s)) = g(s) by periodicity of R_to_S1.\<close>
    define tgt where "tgt s = ?n + gt s" for s
    have htgt0: "tgt 0 = ?n" unfolding tgt_def using hgt unfolding top1_is_path_on_def by simp
    have htgt1: "tgt 1 = ?n + ?m" unfolding tgt_def using hgt unfolding top1_is_path_on_def by simp
    have htgt_lift: "\<forall>s\<in>I_set. top1_R_to_S1 (tgt s) = g s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "top1_R_to_S1 (tgt s) = top1_R_to_S1 (?n + gt s)" unfolding tgt_def by simp
      also have "\<dots> = top1_R_to_S1 (gt s + ?n)" by (simp add: add.commute)
      also obtain k :: int where hk: "?n = of_int k" using hn_int by auto
      have "top1_R_to_S1 (gt s + ?n) = top1_R_to_S1 (gt s + of_int k)" using hk by simp
      also have "\<dots> = top1_R_to_S1 (gt s)" by (rule top1_R_to_S1_int_shift_early)
      also have "\<dots> = g s" using hgtp hs by simp
      finally show "top1_R_to_S1 (tgt s) = g s" .
    qed
    \<comment> \<open>tgt is continuous (translation of continuous gt).\<close>
    have htgt_cont: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets tgt"
    proof -
      have hgt_cont: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets gt"
        using hgt unfolding top1_is_path_on_def by (by100 blast)
      \<comment> \<open>tgt = (\<lambda>s. ?n + gt s) = (\<lambda>s. ?n) + gt. Translation by constant is continuous.\<close>
      \<comment> \<open>(\<lambda>s. ?n + gt s): continuous since gt is continuous and + const is continuous.\<close>
      show ?thesis unfolding tgt_def top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix s :: real assume "s \<in> I_set" show "\<phi>' c + gt s \<in> (UNIV::real set)" by simp
      next
        fix V :: "real set" assume hV: "V \<in> top1_open_sets"
        have hVo: "open V" using hV unfolding top1_open_sets_def by (by100 blast)
        \<comment> \<open>{s. n + gt(s) \<in> V} = {s. gt(s) \<in> (\<lambda>x. x - n) ` V}.\<close>
        let ?W = "(\<lambda>x::real. x - \<phi>' c) ` V"
        have hWo: "open ?W"
        proof -
          have hcont: "continuous_on UNIV (\<lambda>x::real. x + \<phi>' c)" by (intro continuous_intros)
          have "open ((\<lambda>x::real. x + \<phi>' c) -` V)"
          proof -
            have "open ((\<lambda>x::real. x + \<phi>' c) -` V \<inter> UNIV)"
              using iffD1[OF continuous_on_open_vimage[OF open_UNIV] hcont] hVo by (by100 blast)
            thus ?thesis by simp
          qed
          moreover have "(\<lambda>x::real. x + \<phi>' c) -` V = ?W" by (by100 force)
          ultimately show ?thesis by simp
        qed
        have hW_os: "?W \<in> top1_open_sets" using hWo unfolding top1_open_sets_def by (by100 blast)
        have heq: "{s \<in> I_set. \<phi>' c + gt s \<in> V} = {s \<in> I_set. gt s \<in> ?W}"
          by (by100 force)
        have "{s \<in> I_set. gt s \<in> ?W} \<in> I_top"
          using hgt_cont unfolding top1_continuous_map_on_def using hW_os by (by100 blast)
        thus "{s \<in> I_set. \<phi>' c + gt s \<in> V} \<in> I_top" using heq by simp
      qed
    qed
    have htgt_path: "top1_is_path_on (UNIV::real set) top1_open_sets ?n (?n + ?m) tgt"
      unfolding top1_is_path_on_def using htgt_cont htgt0 htgt1 by simp
    \<comment> \<open>Concatenate: h = ft * tgt lifts f*g from 0 to n+m.\<close>
    let ?h = "top1_path_product ft tgt"
    have hh_path: "top1_is_path_on (UNIV::real set) top1_open_sets 0 (?n + ?m) ?h"
    proof -
      have hft_path: "top1_is_path_on (UNIV::real set) top1_open_sets 0 ?n ft" using hft .
      show ?thesis
        by (rule top1_path_product_is_path[OF
            top1_open_sets_is_topology_on_UNIV hft_path htgt_path])
    qed
    have hh_lift: "\<forall>s\<in>I_set. top1_R_to_S1 (?h s) = top1_path_product f g s"
    proof
      fix s assume hs: "s \<in> I_set"
      show "top1_R_to_S1 (?h s) = top1_path_product f g s"
      proof (cases "s \<le> 1/2")
        case True
        hence "?h s = ft (2 * s)" unfolding top1_path_product_def by simp
        moreover have "top1_path_product f g s = f (2 * s)" unfolding top1_path_product_def using True by simp
        moreover have "2 * s \<in> I_set" using hs True unfolding top1_unit_interval_def by auto
        ultimately show ?thesis using hftp by simp
      next
        case False
        hence "?h s = tgt (2 * s - 1)" unfolding top1_path_product_def by simp
        moreover have "top1_path_product f g s = g (2 * s - 1)" unfolding top1_path_product_def using False by simp
        moreover have "2 * s - 1 \<in> I_set" using hs False unfolding top1_unit_interval_def by auto
        ultimately show ?thesis using htgt_lift by simp
      qed
    qed
    \<comment> \<open>f*g \<in> c\<cdot>d (the product class).\<close>
    have hfg_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) (top1_path_product f g)"
    proof -
      have hf_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) f"
        using hfl unfolding top1_is_loop_on_def .
      have hg_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) g"
        using hgl unfolding top1_is_loop_on_def .
      show ?thesis unfolding top1_is_loop_on_def
        by (rule top1_path_product_is_path[OF hTS1 hf_path hg_path])
    qed
    have hfg_in_cd: "top1_path_product f g \<in>
        top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0) c d"
    proof -
      \<comment> \<open>f*g ≃ f*g (reflexivity), and f \<in> c, g \<in> d.\<close>
      have hrefl: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
          (top1_path_product f g) (top1_path_product f g)"
        unfolding top1_loop_equiv_on_def
        using hfg_loop Lemma_51_1_path_homotopic_refl[OF
          hfg_loop[unfolded top1_is_loop_on_def]] by (by100 blast)
      show ?thesis unfolding top1_fundamental_group_mul_def
        using hf_in_c hg_in_d hrefl by (by100 blast)
    qed
    \<comment> \<open>c\<cdot>d is in the carrier, and \<phi>'(c\<cdot>d) is its lift endpoint.\<close>
    have hcd_carrier: "top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0) c d
        \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
    proof -
      \<comment> \<open>c\<cdot>d contains the loop f*g, so it's the equivalence class of f*g.\<close>
      have "top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0) c d
          = {h. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) (top1_path_product f g) h}"
        by (rule fundamental_group_mul_eq_class[OF hTS1 hc hd hf_in_c hg_in_d hfl hgl])
      moreover have "\<dots> \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
        unfolding top1_fundamental_group_carrier_def using hfg_loop by (by100 blast)
      ultimately show ?thesis by simp
    qed
    \<comment> \<open>The lift of f*g from 0 ends at n+m. By Theorem 54.3 well-definedness,
       \<phi>'(c\<cdot>d) = n+m.\<close>
    have h\<phi>'_cd: "\<phi>' (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0) c d) = ?n + ?m"
    proof -
      let ?cd = "top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0) c d"
      \<comment> \<open>From h\<phi>'_lift: get a representative fg and its lift ft_fg.\<close>
      obtain fg ft_fg where hfg_in: "fg \<in> ?cd"
          and hfg_l: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) fg"
          and hft_fg: "top1_is_path_on (UNIV::real set) top1_open_sets 0 (\<phi>' ?cd) ft_fg"
          and hft_fgp: "\<forall>s\<in>I_set. top1_R_to_S1 (ft_fg s) = fg s"
        using h\<phi>'_lift[rule_format, OF hcd_carrier] by (by100 auto)
      \<comment> \<open>fg and f*g are both in c\<cdot>d, hence path-homotopic.\<close>
      have hfg_hom: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) fg (top1_path_product f g)"
      proof -
        \<comment> \<open>fg and f*g are both in c\<cdot>d. In the fundamental group, c\<cdot>d is an equivalence class,
           so any two elements are loop-equivalent, hence path-homotopic.\<close>
        have "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) fg (top1_path_product f g)"
          by (rule fundamental_group_class_members_equiv[OF hTS1 hcd_carrier hfg_in hfg_in_cd])
        thus ?thesis unfolding top1_loop_equiv_on_def by (by100 blast)
      qed
      \<comment> \<open>By Theorem 54.3: lifts of path-homotopic loops from same point have same endpoint.\<close>
      have hTE: "is_topology_on (UNIV::real set) top1_open_sets"
        by (rule top1_open_sets_is_topology_on_UNIV)
      have hfg_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) fg"
        using hfg_l unfolding top1_is_loop_on_def .
      have hfg'_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (top1_path_product f g)"
        using hfg_loop unfolding top1_is_loop_on_def .
      have "\<phi>' ?cd = ?n + ?m"
        using conjunct1[OF Theorem_54_3[OF hcov hTE hTS1 h0R hp0
          hfg_path hfg'_path hfg_hom hft_fg hft_fgp hh_path hh_lift]] .
      thus ?thesis .
    qed
    \<comment> \<open>Since n, m are integers: floor(n+m) = floor(n) + floor(m).\<close>
    obtain kn :: int where hkn: "?n = of_int kn" using hn_int by auto
    obtain km :: int where hkm: "?m = of_int km" using hm_int by auto
    have hfloor_add: "\<lfloor>?n + ?m\<rfloor> = \<lfloor>?n\<rfloor> + \<lfloor>?m\<rfloor>"
      using hkn hkm by simp
    show "\<phi> (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0) c d)
        = \<phi> c + \<phi> d" unfolding \<phi>_def using h\<phi>'_cd hfloor_add by simp
  qed
  show ?thesis
    unfolding top1_groups_isomorphic_on_def top1_group_iso_on_def
      top1_group_hom_on_def top1_Z_group_def top1_Z_mul_def
    apply (intro exI[of _ \<phi>] conjI)
    using h\<phi>_bij unfolding bij_betw_def apply (by100 blast)
    using h\<phi>_hom apply (by100 blast)
    using h\<phi>_bij apply (by100 blast)
    done
qed

section \<open>\<S>55 Retractions and Fixed Points\<close>

text \<open>Retraction: r: X \<rightarrow> A continuous with r|A = id_A.\<close>
definition top1_is_retraction_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "top1_is_retraction_on X TX A r \<longleftrightarrow>
     A \<subseteq> X \<and>
     top1_continuous_map_on X TX A (subspace_topology X TX A) r \<and>
     (\<forall>a\<in>A. r a = a)"

text \<open>A is a retract of X if there exists a retraction X \<rightarrow> A.\<close>
definition top1_retract_of_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_retract_of_on X TX A \<longleftrightarrow> (\<exists>r. top1_is_retraction_on X TX A r)"

lemma top1_is_retraction_on_subset:
  assumes "top1_is_retraction_on X TX A r"
  shows "A \<subseteq> X"
  using assms unfolding top1_is_retraction_on_def by blast

lemma top1_is_retraction_on_continuous:
  assumes "top1_is_retraction_on X TX A r"
  shows "top1_continuous_map_on X TX A (subspace_topology X TX A) r"
  using assms unfolding top1_is_retraction_on_def by blast

lemma top1_is_retraction_on_fixes_A:
  assumes "top1_is_retraction_on X TX A r" and "a \<in> A"
  shows "r a = a"
  using assms unfolding top1_is_retraction_on_def by blast

text \<open>Every space is a retract of itself (via identity).\<close>
lemma top1_retract_self:
  assumes hTX: "is_topology_on X TX"
  shows "top1_retract_of_on X TX X"
proof -
  have hX: "X \<in> TX" using hTX unfolding is_topology_on_def by blast
  have hid: "top1_continuous_map_on X TX X (subspace_topology X TX X) id"
    unfolding top1_continuous_map_on_def
  proof (intro conjI)
    show "\<forall>x \<in> X. id x \<in> X" by simp
  next
    show "\<forall>V \<in> subspace_topology X TX X. {x \<in> X. id x \<in> V} \<in> TX"
    proof
      fix V assume hV: "V \<in> subspace_topology X TX X"
      then obtain U where hU: "U \<in> TX" and hVeq: "V = X \<inter> U"
        unfolding subspace_topology_def by blast
      have "X \<inter> U \<in> TX" by (rule topology_inter2[OF hTX hX hU])
      hence "V \<in> TX" using hVeq by simp
      moreover have "{x \<in> X. id x \<in> V} = V" using hVeq by auto
      ultimately show "{x \<in> X. id x \<in> V} \<in> TX" by simp
    qed
  qed
  have hret: "top1_is_retraction_on X TX X id"
    unfolding top1_is_retraction_on_def using hid by simp
  thus ?thesis unfolding top1_retract_of_on_def by blast
qed

text \<open>Helper: fst is continuous from any subspace of R^2 to R.\<close>
lemma top1_fst_continuous_R2_subspace:
  fixes S :: "(real \<times> real) set"
  shows "top1_continuous_map_on S
    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S)
    (UNIV::real set) top1_open_sets fst"
  unfolding top1_continuous_map_on_def
proof (intro conjI ballI)
  fix p assume "p \<in> S" thus "fst p \<in> (UNIV::real set)" by simp
next
  fix V :: "real set" assume hV: "V \<in> top1_open_sets"
  have hVo: "open V" using hV unfolding top1_open_sets_def by blast
  have hBxU_open: "open (V \<times> (UNIV::real set))" by (rule open_Times[OF hVo open_UNIV])
  have hBxU_prod: "V \<times> (UNIV::real set) \<in> product_topology_on top1_open_sets top1_open_sets"
  proof -
    have "V \<times> (UNIV::real set) \<in> (top1_open_sets :: (real\<times>real) set set)"
      using hBxU_open unfolding top1_open_sets_def by blast
    thus ?thesis using product_topology_on_open_sets_real2 by metis
  qed
  have "{p \<in> S. fst p \<in> V} = S \<inter> (V \<times> UNIV)" by (auto simp: mem_Times_iff prod.collapse[symmetric])
  thus "{p \<in> S. fst p \<in> V} \<in>
    subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
    unfolding subspace_topology_def using hBxU_prod by blast
qed

lemma top1_snd_continuous_R2_subspace:
  fixes S :: "(real \<times> real) set"
  shows "top1_continuous_map_on S
    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S)
    (UNIV::real set) top1_open_sets snd"
  unfolding top1_continuous_map_on_def
proof (intro conjI ballI)
  fix p assume "p \<in> S" thus "snd p \<in> (UNIV::real set)" by simp
next
  fix V :: "real set" assume hV: "V \<in> top1_open_sets"
  have hVo: "open V" using hV unfolding top1_open_sets_def by blast
  have hUxB_open: "open ((UNIV::real set) \<times> V)" by (rule open_Times[OF open_UNIV hVo])
  have hUxB_prod: "(UNIV::real set) \<times> V \<in> product_topology_on top1_open_sets top1_open_sets"
  proof -
    have "(UNIV::real set) \<times> V \<in> (top1_open_sets :: (real\<times>real) set set)"
      using hUxB_open unfolding top1_open_sets_def by blast
    thus ?thesis using product_topology_on_open_sets_real2 by metis
  qed
  have "{p \<in> S. snd p \<in> V} = S \<inter> (UNIV \<times> V)" by (auto simp: mem_Times_iff prod.collapse[symmetric])
  thus "{p \<in> S. snd p \<in> V} \<in>
    subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) S"
    unfolding subspace_topology_def using hUxB_prod by blast
qed

text \<open>Helper: restriction of continuous map to subspace domain.\<close>
lemma top1_continuous_map_on_subspace_restrict:
  assumes hcont: "top1_continuous_map_on X TX Y TY f"
      and hAX: "A \<subseteq> X"
  shows "top1_continuous_map_on A (subspace_topology X TX A) Y TY f"
  unfolding top1_continuous_map_on_def
proof (intro conjI ballI)
  fix a assume "a \<in> A"
  hence "a \<in> X" using hAX by blast
  thus "f a \<in> Y" using hcont unfolding top1_continuous_map_on_def by blast
next
  fix V assume hV: "V \<in> TY"
  have "{a \<in> X. f a \<in> V} \<in> TX"
    using hcont hV unfolding top1_continuous_map_on_def by blast
  moreover have "{a \<in> A. f a \<in> V} = A \<inter> {a \<in> X. f a \<in> V}"
    using hAX by auto
  ultimately show "{a \<in> A. f a \<in> V} \<in> subspace_topology X TX A"
    unfolding subspace_topology_def by blast
qed

text \<open>The closed disc B^2 and unit sphere S^1 as subspaces of R^2.\<close>
definition top1_B2 :: "(real \<times> real) set" where
  "top1_B2 = {p. fst p ^ 2 + snd p ^ 2 \<le> 1}"

definition top1_B2_topology :: "(real \<times> real) set set" where
  "top1_B2_topology = subspace_topology UNIV
     (product_topology_on top1_open_sets top1_open_sets) top1_B2"

text \<open>Helper: if f : X \<rightarrow> A is continuous (with subspace topology from ambient Z),
  and A \<subseteq> B \<subseteq> Z, then f : X \<rightarrow> B is also continuous (with subspace topology from Z).\<close>
lemma top1_continuous_map_on_codomain_enlarge:
  assumes hcont: "top1_continuous_map_on X TX A (subspace_topology Z TZ A) f"
      and hAB: "A \<subseteq> B" and hBZ: "B \<subseteq> Z"
  shows "top1_continuous_map_on X TX B (subspace_topology Z TZ B) f"
proof -
  have hfA: "\<forall>x\<in>X. f x \<in> A"
    using hcont unfolding top1_continuous_map_on_def by blast
  have hfB: "\<forall>x\<in>X. f x \<in> B" using hfA hAB by blast
  have hpreimage: "\<forall>V\<in>subspace_topology Z TZ B. {x\<in>X. f x \<in> V} \<in> TX"
  proof (intro ballI)
    fix V assume hV: "V \<in> subspace_topology Z TZ B"
    obtain U where hU: "U \<in> TZ" and hV_eq: "V = B \<inter> U"
      using hV unfolding subspace_topology_def by blast
    have hAU_in: "A \<inter> U \<in> subspace_topology Z TZ A"
      unfolding subspace_topology_def using hU by blast
    have hpre_eq: "{x\<in>X. f x \<in> V} = {x\<in>X. f x \<in> A \<inter> U}"
    proof (rule set_eqI)
      fix x
      show "x \<in> {x\<in>X. f x \<in> V} \<longleftrightarrow> x \<in> {x\<in>X. f x \<in> A \<inter> U}"
        using hfA hAB hV_eq by auto
    qed
    have "{x\<in>X. f x \<in> A \<inter> U} \<in> TX"
      using hcont hAU_in unfolding top1_continuous_map_on_def by blast
    thus "{x\<in>X. f x \<in> V} \<in> TX" using hpre_eq by simp
  qed
  show ?thesis
    unfolding top1_continuous_map_on_def using hfB hpreimage by blast
qed

(** from \<S>55 Lemma 55.1: if A is a retract of X, then (\<pi>_1 A, x0) \<rightarrow> (\<pi>_1 X, x0)
    is injective (induced by inclusion) **)
lemma Lemma_55_1_retract_injective:
  assumes hret: "top1_retract_of_on X TX A"
      and hx0A: "x0 \<in> A"
      and hf_loop: "top1_is_loop_on A (subspace_topology X TX A) x0 f"
      and hg_loop: "top1_is_loop_on A (subspace_topology X TX A) x0 g"
      and hfg_hom: "top1_path_homotopic_on X TX x0 x0 f g"
  shows "top1_path_homotopic_on A (subspace_topology X TX A) x0 x0 f g"
proof -
  obtain r where hr: "top1_is_retraction_on X TX A r"
    using hret unfolding top1_retract_of_on_def by blast
  have hr_cont: "top1_continuous_map_on X TX A (subspace_topology X TX A) r"
    using hr unfolding top1_is_retraction_on_def by blast
  have hr_fix: "\<forall>a\<in>A. r a = a"
    using hr unfolding top1_is_retraction_on_def by blast
  obtain F where hFcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hFs0: "\<forall>s\<in>I_set. F (s, 0) = f s"
      and hFs1: "\<forall>s\<in>I_set. F (s, 1) = g s"
      and hF0t: "\<forall>t\<in>I_set. F (0, t) = x0"
      and hF1t: "\<forall>t\<in>I_set. F (1, t) = x0"
    using hfg_hom unfolding top1_path_homotopic_on_def by blast
  have hf_path: "top1_is_path_on A (subspace_topology X TX A) x0 x0 f"
    using hf_loop unfolding top1_is_loop_on_def .
  have hg_path: "top1_is_path_on A (subspace_topology X TX A) x0 x0 g"
    using hg_loop unfolding top1_is_loop_on_def .
  let ?G = "\<lambda>p. r (F p)"
  have hGcont: "top1_continuous_map_on (I_set \<times> I_set) II_topology A (subspace_topology X TX A) ?G"
    using top1_continuous_map_on_comp[OF hFcont hr_cont] by (simp add: comp_def)
  have hf_in_A: "\<forall>s\<in>I_set. f s \<in> A"
    using hf_path unfolding top1_is_path_on_def top1_continuous_map_on_def by blast
  have hg_in_A: "\<forall>s\<in>I_set. g s \<in> A"
    using hg_path unfolding top1_is_path_on_def top1_continuous_map_on_def by blast
  have hGs0: "\<forall>s\<in>I_set. ?G (s, 0) = f s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "F (s, 0) = f s" using hs hFs0 by blast
    hence "r (F (s, 0)) = r (f s)" by simp
    also have "... = f s" using hr_fix hf_in_A hs by blast
    finally show "?G (s, 0) = f s" by simp
  qed
  have hGs1: "\<forall>s\<in>I_set. ?G (s, 1) = g s"
  proof
    fix s assume hs: "s \<in> I_set"
    have "F (s, 1) = g s" using hs hFs1 by blast
    hence "r (F (s, 1)) = r (g s)" by simp
    also have "... = g s" using hr_fix hg_in_A hs by blast
    finally show "?G (s, 1) = g s" by simp
  qed
  have hG0t: "\<forall>t\<in>I_set. ?G (0, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "F (0, t) = x0" using ht hF0t by blast
    hence "r (F (0, t)) = r x0" by simp
    also have "... = x0" using hr_fix hx0A by blast
    finally show "?G (0, t) = x0" by simp
  qed
  have hG1t: "\<forall>t\<in>I_set. ?G (1, t) = x0"
  proof
    fix t assume ht: "t \<in> I_set"
    have "F (1, t) = x0" using ht hF1t by blast
    hence "r (F (1, t)) = r x0" by simp
    also have "... = x0" using hr_fix hx0A by blast
    finally show "?G (1, t) = x0" by simp
  qed
  show ?thesis
    unfolding top1_path_homotopic_on_def
    using hf_path hg_path hGcont hGs0 hGs1 hG0t hG1t by blast
qed

text \<open>Helper: \<pi>_1(S^1) is nontrivial — follows from Theorem 54.5 since Z has \<ge> 2 elements.\<close>
lemma top1_S1_fundamental_group_nontrivial:
  "\<exists>f g. top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f
       \<and> top1_is_loop_on top1_S1 top1_S1_topology (1, 0) g
       \<and> \<not> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f g"
proof -
  obtain \<phi> where hbij: "bij_betw \<phi>
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) (UNIV::int set)"
    using Theorem_54_5 by blast
  \<comment> \<open>Since UNIV::int has \<ge> 2 elements and \<phi> is a bijection, the carrier has \<ge> 2 elements.
      Each element is an equivalence class of a loop; distinct classes give non-homotopic loops.\<close>
  obtain c1 c2 where hc1: "c1 \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
      and hc2: "c2 \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
      and hne: "c1 \<noteq> c2"
  proof -
    have "card (UNIV::int set) \<noteq> 1" by simp
    hence "card (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)) \<noteq> 1"
      using bij_betw_same_card[OF hbij] by simp
    hence "\<exists>x y. x \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)
               \<and> y \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0) \<and> x \<noteq> y"
    proof -
      have hsurj: "\<phi> ` top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0) = UNIV"
        using hbij unfolding bij_betw_def by blast
      have hinj: "inj_on \<phi> (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))"
        using hbij unfolding bij_betw_def by blast
      have h0mem: "(0::int) \<in> \<phi> ` top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
        using hsurj by blast
      obtain xa where hxa_mem: "xa \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
          and hxa: "\<phi> xa = 0"
        using h0mem by (auto simp: image_iff)
      have h1mem: "(1::int) \<in> \<phi> ` top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
        using hsurj by blast
      obtain xb where hxb_mem: "xb \<in> top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0)"
          and hxb: "\<phi> xb = 1"
        using h1mem by (auto simp: image_iff)
      have "xa \<noteq> xb" using hxa hxb by (metis zero_neq_one)
      thus ?thesis using hxa_mem hxb_mem by blast
    qed
    thus ?thesis using that by blast
  qed
  \<comment> \<open>Each class is {g. f \<simeq>_p g} for some loop f at (1,0). Pick representatives.\<close>
  obtain f where hf: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f"
      and hc1_eq: "c1 = {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f g}"
    using hc1 unfolding top1_fundamental_group_carrier_def by blast
  obtain g where hg: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) g"
      and hc2_eq: "c2 = {h. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) g h}"
    using hc2 unfolding top1_fundamental_group_carrier_def by blast
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
  proof -
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2': "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
                  (product_topology_on top1_open_sets top1_open_sets)"
      by (rule product_topology_on_is_topology_on[OF hTR hTR])
    have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using hTR2' unfolding hUU .
    show ?thesis unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR2], simp)
  qed
  \<comment> \<open>Since c1 \<ne> c2, f and g are not loop-equivalent, i.e., not path-homotopic.\<close>
  have hne_eq: "\<not> top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f g"
  proof (rule ccontr)
    assume "\<not> \<not> top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f g"
    hence heq: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f g" by simp
    have "c1 \<subseteq> c2"
    proof
      fix h assume "h \<in> c1"
      hence hfh: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f h" using hc1_eq by blast
      have hgf: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) g f"
        by (rule top1_loop_equiv_on_sym[OF heq])
      have "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) g h"
        by (rule top1_loop_equiv_on_trans[OF hTS1 hgf hfh])
      thus "h \<in> c2" using hc2_eq by blast
    qed
    moreover have "c2 \<subseteq> c1"
    proof
      fix h assume "h \<in> c2"
      hence hgh: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) g h" using hc2_eq by blast
      have "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f h"
        by (rule top1_loop_equiv_on_trans[OF hTS1 heq hgh])
      thus "h \<in> c1" using hc1_eq by blast
    qed
    ultimately have "c1 = c2" by blast
    thus False using hne by blast
  qed
  hence hnot_pho: "\<not> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f g"
    using hf hg unfolding top1_loop_equiv_on_def by blast
  show ?thesis using hf hg hnot_pho by blast
qed

text \<open>Helper: B^2 is convex.\<close>
lemma top1_B2_convex:
  assumes hp: "p \<in> top1_B2" and hq: "q \<in> top1_B2" and ht0: "0 \<le> t" and ht1: "t \<le> 1"
  shows "((1-t) * fst p + t * fst q, (1-t) * snd p + t * snd q) \<in> top1_B2"
proof -
  let ?a = "fst p" and ?b = "snd p" and ?c = "fst q" and ?d = "snd q"
  have hp2: "?a^2 + ?b^2 \<le> 1" using hp unfolding top1_B2_def by simp
  have hq2: "?c^2 + ?d^2 \<le> 1" using hq unfolding top1_B2_def by simp
  have hs: "0 \<le> 1 - t" using ht1 by simp
  \<comment> \<open>Use: ((1-t)a+tc)^2 + ((1-t)b+td)^2
       = (1-t)^2(a^2+b^2) + 2t(1-t)(ac+bd) + t^2(c^2+d^2)
       \<le> (1-t)^2 + 2t(1-t)|ac+bd| + t^2
       \<le> (1-t)^2 + 2t(1-t) + t^2 = 1.
     The last step uses |ac+bd| \<le> 1, which follows from Cauchy-Schwarz:
       |ac+bd| \<le> sqrt(a^2+b^2)*sqrt(c^2+d^2) \<le> 1.\<close>
  \<comment> \<open>Cauchy-Schwarz: (ac+bd)^2 \<le> (a^2+b^2)(c^2+d^2), from (ad-bc)^2 \<ge> 0.\<close>
  have hnn: "0 \<le> (?a * ?d - ?b * ?c)^2" by simp
  have hCS: "(?a * ?c + ?b * ?d)^2 \<le> (?a^2 + ?b^2) * (?c^2 + ?d^2)"
  proof -
    have "(?a * ?c + ?b * ?d)^2 + (?a * ?d - ?b * ?c)^2
          = (?a^2 + ?b^2) * (?c^2 + ?d^2)"
      by (simp add: power2_eq_square algebra_simps)
    thus ?thesis using hnn by linarith
  qed
  have hprod_le1: "(?a^2 + ?b^2) * (?c^2 + ?d^2) \<le> 1"
  proof -
    have "0 \<le> ?a^2 + ?b^2" by (simp add: sum_power2_ge_zero)
    thus ?thesis using hp2 hq2 by (simp add: mult_le_one)
  qed
  have hCS_le1: "(?a * ?c + ?b * ?d)^2 \<le> 1"
    using hCS hprod_le1 by linarith
  \<comment> \<open>From x^2 \<le> 1 derive -1 \<le> x \<le> 1 via (1-x)(1+x) = 1 - x^2 \<ge> 0.\<close>
  have hdiff: "0 \<le> 1 - (?a * ?c + ?b * ?d)^2" using hCS_le1 by linarith
  have hprod: "0 \<le> (1 - (?a * ?c + ?b * ?d)) * (1 + (?a * ?c + ?b * ?d))"
  proof -
    have "(1 - (?a * ?c + ?b * ?d)) * (1 + (?a * ?c + ?b * ?d))
          = 1 - (?a * ?c + ?b * ?d) * (?a * ?c + ?b * ?d)"
      by (simp add: algebra_simps)
    also have "\<dots> = 1 - (?a * ?c + ?b * ?d)^2"
      by (simp add: power2_eq_square)
    finally show ?thesis using hdiff by linarith
  qed
  have hac_le1: "?a * ?c + ?b * ?d \<le> 1"
    using hprod by (simp add: zero_le_mult_iff, linarith)
  have hac_ge: "-1 \<le> ?a * ?c + ?b * ?d"
    using hprod by (simp add: zero_le_mult_iff, linarith)
  \<comment> \<open>Main estimate: decompose 1 - LHS into three nonneg terms.\<close>
  have hgoal: "((1-t) * ?a + t * ?c)^2 + ((1-t) * ?b + t * ?d)^2 \<le> 1"
  proof -
    have hexp: "((1-t) * ?a + t * ?c)^2 + ((1-t) * ?b + t * ?d)^2
      = (1-t)^2 * (?a^2 + ?b^2) + t^2 * (?c^2 + ?d^2)
        + 2 * t * (1-t) * (?a * ?c + ?b * ?d)"
      by (simp add: power2_eq_square algebra_simps)
    have ht1: "(1-t)^2 * (?a^2 + ?b^2) \<le> (1-t)^2"
      using hp2 by (simp add: power2_eq_square mult_left_le)
    have ht2: "t^2 * (?c^2 + ?d^2) \<le> t^2"
      using hq2 by (simp add: power2_eq_square mult_left_le)
    have ht3: "2 * t * (1-t) * (?a * ?c + ?b * ?d) \<le> 2 * t * (1-t)"
      using hac_le1 hs ht0 by (simp add: mult_left_le)
    have hsum: "(1-t)^2 + t^2 + 2 * t * (1-t) = 1"
      by (simp add: power2_eq_square algebra_simps)
    show ?thesis using hexp ht1 ht2 ht3 hsum by linarith
  qed
  show ?thesis unfolding top1_B2_def using hgoal by simp
qed

text \<open>Helper: extracting continuous\_on from top1\_continuous\_map\_on for B^2 paths.\<close>
lemma top1_B2_cont_fst:
  assumes hf: "top1_continuous_map_on I_set I_top top1_B2 top1_B2_topology f"
  shows "continuous_on I_set (fst \<circ> f)"
  unfolding continuous_on_open_invariant
proof (intro allI impI)
  fix B :: "real set" assume hBo: "open B"
  have hfB2: "\<forall>s\<in>I_set. f s \<in> top1_B2"
    using hf unfolding top1_continuous_map_on_def by blast
  \<comment> \<open>B \<times> UNIV is open in R^2, hence in product_topology_on.\<close>
  have hBxU_open: "open (B \<times> (UNIV::real set))" by (rule open_Times[OF hBo open_UNIV])
  have hBxU_prod: "B \<times> (UNIV::real set) \<in> product_topology_on top1_open_sets top1_open_sets"
  proof -
    have "B \<times> (UNIV::real set) \<in> (top1_open_sets :: (real\<times>real) set set)"
      using hBxU_open unfolding top1_open_sets_def by blast
    thus ?thesis using product_topology_on_open_sets_real2 by metis
  qed
  \<comment> \<open>Intersect with B^2 to get element of B^2\_topology.\<close>
  have hV: "top1_B2 \<inter> (B \<times> UNIV) \<in> top1_B2_topology"
    unfolding top1_B2_topology_def subspace_topology_def using hBxU_prod by blast
  \<comment> \<open>Preimage under f is in I\_top.\<close>
  have hpre: "{s \<in> I_set. f s \<in> top1_B2 \<inter> (B \<times> UNIV)} \<in> I_top"
    using hf hV unfolding top1_continuous_map_on_def by blast
  \<comment> \<open>Simplify: f s \<in> B^2 \<inter> (B \<times> UNIV) iff fst(f s) \<in> B.\<close>
  have heq: "{s \<in> I_set. f s \<in> top1_B2 \<inter> (B \<times> UNIV)} = {s \<in> I_set. fst (f s) \<in> B}"
  proof (rule set_eqI)
    fix s show "s \<in> {s \<in> I_set. f s \<in> top1_B2 \<inter> (B \<times> UNIV)} \<longleftrightarrow>
                s \<in> {s \<in> I_set. fst (f s) \<in> B}"
      using hfB2 by (auto simp: mem_Times_iff prod.collapse[symmetric])
  qed
  have hpre': "{s \<in> I_set. fst (f s) \<in> B} \<in> I_top" using hpre heq by simp
  \<comment> \<open>Extract open set from I\_top = subspace\_topology.\<close>
  obtain W where hW: "W \<in> top1_open_sets" and hWeq: "{s \<in> I_set. fst (f s) \<in> B} = I_set \<inter> W"
    using hpre' unfolding top1_unit_interval_topology_def subspace_topology_def by blast
  have "open W" using hW unfolding top1_open_sets_def by blast
  moreover have "W \<inter> I_set = (fst \<circ> f) -` B \<inter> I_set" using hWeq by (auto simp: comp_def)
  ultimately show "\<exists>A. open A \<and> A \<inter> I_set = (fst \<circ> f) -` B \<inter> I_set" by blast
qed

lemma top1_B2_cont_snd:
  assumes hf: "top1_continuous_map_on I_set I_top top1_B2 top1_B2_topology f"
  shows "continuous_on I_set (snd \<circ> f)"
  unfolding continuous_on_open_invariant
proof (intro allI impI)
  fix B :: "real set" assume hBo: "open B"
  have hfB2: "\<forall>s\<in>I_set. f s \<in> top1_B2"
    using hf unfolding top1_continuous_map_on_def by blast
  have hUxB_open: "open ((UNIV::real set) \<times> B)" by (rule open_Times[OF open_UNIV hBo])
  have hUxB_prod: "(UNIV::real set) \<times> B \<in> product_topology_on top1_open_sets top1_open_sets"
  proof -
    have "(UNIV::real set) \<times> B \<in> (top1_open_sets :: (real\<times>real) set set)"
      using hUxB_open unfolding top1_open_sets_def by blast
    thus ?thesis using product_topology_on_open_sets_real2 by metis
  qed
  have hV: "top1_B2 \<inter> (UNIV \<times> B) \<in> top1_B2_topology"
    unfolding top1_B2_topology_def subspace_topology_def using hUxB_prod by blast
  have hpre: "{s \<in> I_set. f s \<in> top1_B2 \<inter> (UNIV \<times> B)} \<in> I_top"
    using hf hV unfolding top1_continuous_map_on_def by blast
  have heq: "{s \<in> I_set. f s \<in> top1_B2 \<inter> (UNIV \<times> B)} = {s \<in> I_set. snd (f s) \<in> B}"
  proof (rule set_eqI)
    fix s show "s \<in> {s \<in> I_set. f s \<in> top1_B2 \<inter> (UNIV \<times> B)} \<longleftrightarrow>
                s \<in> {s \<in> I_set. snd (f s) \<in> B}"
      using hfB2 by (auto simp: mem_Times_iff prod.collapse[symmetric])
  qed
  have hpre': "{s \<in> I_set. snd (f s) \<in> B} \<in> I_top" using hpre heq by simp
  obtain W where hW: "W \<in> top1_open_sets" and hWeq: "{s \<in> I_set. snd (f s) \<in> B} = I_set \<inter> W"
    using hpre' unfolding top1_unit_interval_topology_def subspace_topology_def by blast
  have "open W" using hW unfolding top1_open_sets_def by blast
  moreover have "W \<inter> I_set = (snd \<circ> f) -` B \<inter> I_set" using hWeq by (auto simp: comp_def)
  ultimately show "\<exists>A. open A \<and> A \<inter> I_set = (snd \<circ> f) -` B \<inter> I_set" by blast
qed

text \<open>Helper: B^2 is path-connected via straight-line paths.\<close>
lemma top1_B2_path_connected:
  "top1_path_connected_on top1_B2 top1_B2_topology"
proof -
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
  proof -
    have "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
              (product_topology_on top1_open_sets top1_open_sets)"
      by (rule product_topology_on_is_topology_on[OF hTR hTR])
    thus ?thesis by simp
  qed
  have hTB2: "is_topology_on top1_B2 top1_B2_topology"
    unfolding top1_B2_topology_def
    by (rule subspace_topology_is_topology_on[OF hTR2]) simp
  have hTI: "is_topology_on I_set I_top"
    by (rule top1_unit_interval_topology_is_topology_on)
  have hI_eq: "I_top = subspace_topology UNIV top1_open_sets I_set"
    unfolding top1_unit_interval_topology_def by rule
  have hUNIV_eq: "subspace_topology UNIV top1_open_sets (UNIV::real set) = top1_open_sets"
    by (rule subspace_topology_UNIV_self)
  have hpath: "\<forall>x\<in>top1_B2. \<forall>y\<in>top1_B2. \<exists>f. top1_is_path_on top1_B2 top1_B2_topology x y f"
  proof (intro ballI)
    fix x y :: "real \<times> real" assume hx: "x \<in> top1_B2" and hy: "y \<in> top1_B2"
    let ?f = "\<lambda>t::real. ((1-t) * fst x + t * fst y, (1-t) * snd x + t * snd y)"
    \<comment> \<open>Each component is continuous\_on UNIV.\<close>
    have hc1: "continuous_on UNIV (\<lambda>t::real. (1-t) * fst x + t * fst y)"
      by (intro continuous_intros)
    have hc2: "continuous_on UNIV (\<lambda>t::real. (1-t) * snd x + t * snd y)"
      by (intro continuous_intros)
    \<comment> \<open>Each component: top1\_continuous\_map\_on I\_set I\_top UNIV top1\_open\_sets.\<close>
    have hcm1: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets
        (\<lambda>t. (1-t) * fst x + t * fst y)"
      using top1_continuous_map_on_real_subspace_open_sets[of I_set "\<lambda>t. (1-t)*fst x + t*fst y" UNIV, OF _ hc1]
      unfolding hI_eq hUNIV_eq by auto
    have hcm2: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets
        (\<lambda>t. (1-t) * snd x + t * snd y)"
      using top1_continuous_map_on_real_subspace_open_sets[of I_set "\<lambda>t. (1-t)*snd x + t*snd y" UNIV, OF _ hc2]
      unfolding hI_eq hUNIV_eq by auto
    \<comment> \<open>pi1 \<circ> ?f and pi2 \<circ> ?f.\<close>
    have hpi1: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (pi1 \<circ> ?f)"
    proof -
      have "pi1 \<circ> ?f = (\<lambda>t. (1-t) * fst x + t * fst y)" unfolding pi1_def comp_def by auto
      thus ?thesis using hcm1 by simp
    qed
    have hpi2: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (pi2 \<circ> ?f)"
    proof -
      have "pi2 \<circ> ?f = (\<lambda>t. (1-t) * snd x + t * snd y)" unfolding pi2_def comp_def by auto
      thus ?thesis using hcm2 by simp
    qed
    \<comment> \<open>Combine via Theorem 18.4.\<close>
    have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
    have hf_cont_R2: "top1_continuous_map_on I_set I_top
        (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets) ?f"
      using iffD2[OF Theorem_18_4[OF hTI hTR hTR, of ?f]]
      using hpi1 hpi2 unfolding hUU by blast
    \<comment> \<open>Image is in B^2.\<close>
    have hf_in_B2: "\<forall>t\<in>I_set. ?f t \<in> top1_B2"
    proof
      fix t assume ht: "t \<in> I_set"
      have ht0: "0 \<le> t" and ht1: "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
      show "?f t \<in> top1_B2" by (rule top1_B2_convex[OF hx hy ht0 ht1])
    qed
    have hf_img: "?f ` I_set \<subseteq> top1_B2" using hf_in_B2 by blast
    \<comment> \<open>Restrict codomain to B^2.\<close>
    have hf_cont_B2: "top1_continuous_map_on I_set I_top top1_B2 top1_B2_topology ?f"
      using top1_continuous_map_on_codomain_shrink[OF hf_cont_R2 hf_img]
      unfolding top1_B2_topology_def by simp
    \<comment> \<open>Endpoints.\<close>
    have hstart: "?f 0 = x" by simp
    have hend: "?f 1 = y" by simp
    show "\<exists>f. top1_is_path_on top1_B2 top1_B2_topology x y f"
      unfolding top1_is_path_on_def using hf_cont_B2 hstart hend by blast
  qed
  show ?thesis unfolding top1_path_connected_on_def using hTB2 hpath by blast
qed

text \<open>Helper: B^2 is simply connected.\<close>
lemma top1_B2_simply_connected:
  "top1_simply_connected_on top1_B2 top1_B2_topology"
proof -
  have hpc: "top1_path_connected_on top1_B2 top1_B2_topology"
    by (rule top1_B2_path_connected)
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
  proof -
    have hTI: "is_topology_on I_set I_top"
      by (rule top1_unit_interval_topology_is_topology_on)
    show ?thesis
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
  qed
  have hloops: "\<forall>x0\<in>top1_B2. \<forall>f. top1_is_loop_on top1_B2 top1_B2_topology x0 f \<longrightarrow>
      top1_path_homotopic_on top1_B2 top1_B2_topology x0 x0 f (top1_constant_path x0)"
  proof (intro ballI allI impI)
    fix x0 :: "real \<times> real" and f
    assume hx0: "x0 \<in> top1_B2" and hloop: "top1_is_loop_on top1_B2 top1_B2_topology x0 f"
    have hfcont: "top1_continuous_map_on I_set I_top top1_B2 top1_B2_topology f"
      using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by blast
    have hf0: "f 0 = x0" and hf1: "f 1 = x0"
      using hloop unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
    have hf_in_B2: "\<forall>s\<in>I_set. f s \<in> top1_B2"
      using hfcont unfolding top1_continuous_map_on_def by blast
    \<comment> \<open>Build the straight-line homotopy using slh_ext for each component.\<close>
    let ?H1 = "top1_slh_ext (fst \<circ> f) (fst x0)"
    let ?H2 = "top1_slh_ext (snd \<circ> f) (snd x0)"
    let ?H = "\<lambda>p. (?H1 p, ?H2 p)"
    \<comment> \<open>Each component is continuous_on UNIV.\<close>
    have hfst_cont: "continuous_on I_set (fst \<circ> f)"
      by (rule top1_B2_cont_fst[OF hfcont])
    have hsnd_cont: "continuous_on I_set (snd \<circ> f)"
      by (rule top1_B2_cont_snd[OF hfcont])
    have hH1_cont_univ: "continuous_on UNIV ?H1"
      by (rule top1_slh_ext_continuous[OF hfst_cont])
    have hH2_cont_univ: "continuous_on UNIV ?H2"
      by (rule top1_slh_ext_continuous[OF hsnd_cont])
    \<comment> \<open>Each component is continuous II_topology \<rightarrow> top1_open_sets.\<close>
    have hH1_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::real set) top1_open_sets ?H1"
      by (rule top1_continuous_map_on_II_to_UNIV[OF hH1_cont_univ])
    have hH2_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::real set) top1_open_sets ?H2"
      by (rule top1_continuous_map_on_II_to_UNIV[OF hH2_cont_univ])
    \<comment> \<open>Combine via Theorem 18.4: pair is continuous to product topology.\<close>
    have hH_pi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::real set) top1_open_sets (pi1 \<circ> ?H)"
    proof -
      have "pi1 \<circ> ?H = ?H1" unfolding pi1_def comp_def by auto
      thus ?thesis using hH1_cont by simp
    qed
    have hH_pi2: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::real set) top1_open_sets (pi2 \<circ> ?H)"
    proof -
      have "pi2 \<circ> ?H = ?H2" unfolding pi2_def comp_def by auto
      thus ?thesis using hH2_cont by simp
    qed
    have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
    have hH_cont_R2: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets) ?H"
      using iffD2[OF Theorem_18_4[OF hTII hTR hTR, of ?H]]
      using hH_pi1 hH_pi2 unfolding hUU by blast
    \<comment> \<open>Image of I\<times>I is in B^2 (by convexity).\<close>
    have hH_in_B2: "\<forall>p\<in>I_set \<times> I_set. ?H p \<in> top1_B2"
    proof (intro ballI)
      fix p assume hp: "p \<in> I_set \<times> I_set"
      have hs: "fst p \<in> I_set" and ht: "snd p \<in> I_set" using hp by auto
      have ht0: "0 \<le> snd p" and ht1: "snd p \<le> 1"
        using ht unfolding top1_unit_interval_def by auto
      have hfp: "f (fst p) \<in> top1_B2"
        using hf_in_B2 hs by blast
      have hagree1: "?H1 p = (1 - snd p) * (fst \<circ> f) (fst p) + snd p * fst x0"
        by (rule top1_slh_ext_agrees[OF hp])
      have hagree2: "?H2 p = (1 - snd p) * (snd \<circ> f) (fst p) + snd p * snd x0"
        by (rule top1_slh_ext_agrees[OF hp])
      have "?H p = ((1 - snd p) * fst (f (fst p)) + snd p * fst x0,
                     (1 - snd p) * snd (f (fst p)) + snd p * snd x0)"
        using hagree1 hagree2 by (simp add: comp_def)
      also have "\<dots> \<in> top1_B2"
        by (rule top1_B2_convex[OF hfp hx0 ht0 ht1])
      finally show "?H p \<in> top1_B2" .
    qed
    \<comment> \<open>Restrict codomain to B^2.\<close>
    have hB2_sub: "top1_B2 \<subseteq> (UNIV::(real\<times>real) set)" by simp
    have hH_img: "?H ` (I_set \<times> I_set) \<subseteq> top1_B2"
      using hH_in_B2 by blast
    have hH_cont_B2: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        top1_B2 top1_B2_topology ?H"
      using top1_continuous_map_on_codomain_shrink[OF hH_cont_R2 hH_img hB2_sub]
      unfolding top1_B2_topology_def .
    \<comment> \<open>Boundary conditions.\<close>
    have hFs0: "\<forall>s\<in>I_set. ?H (s, 0) = f s"
    proof
      fix s assume hs: "s \<in> I_set"
      have hp: "(s, 0::real) \<in> I_set \<times> I_set"
        using hs unfolding top1_unit_interval_def by auto
      have "?H1 (s, 0) = (1 - 0) * (fst \<circ> f) s + 0 * fst x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h1: "?H1 (s, 0) = fst (f s)" by (simp add: comp_def)
      have "?H2 (s, 0) = (1 - 0) * (snd \<circ> f) s + 0 * snd x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h2: "?H2 (s, 0) = snd (f s)" by (simp add: comp_def)
      show "?H (s, 0) = f s" using h1 h2 by simp
    qed
    have hFs1: "\<forall>s\<in>I_set. ?H (s, 1) = x0"
    proof
      fix s assume hs: "s \<in> I_set"
      have hp: "(s, 1::real) \<in> I_set \<times> I_set"
        using hs unfolding top1_unit_interval_def by auto
      have "?H1 (s, 1) = (1 - 1) * (fst \<circ> f) s + 1 * fst x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h1: "?H1 (s, 1) = fst x0" by simp
      have "?H2 (s, 1) = (1 - 1) * (snd \<circ> f) s + 1 * snd x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h2: "?H2 (s, 1) = snd x0" by simp
      show "?H (s, 1) = x0" using h1 h2 by simp
    qed
    have hF0t: "\<forall>t\<in>I_set. ?H (0, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have hp: "(0::real, t) \<in> I_set \<times> I_set"
        using ht unfolding top1_unit_interval_def by auto
      have "?H1 (0, t) = (1 - t) * (fst \<circ> f) 0 + t * fst x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h1: "?H1 (0, t) = fst x0"
        using hf0 by (simp add: comp_def algebra_simps)
      have "?H2 (0, t) = (1 - t) * (snd \<circ> f) 0 + t * snd x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h2: "?H2 (0, t) = snd x0"
        using hf0 by (simp add: comp_def algebra_simps)
      show "?H (0, t) = x0" using h1 h2 by simp
    qed
    have hF1t: "\<forall>t\<in>I_set. ?H (1, t) = x0"
    proof
      fix t assume ht: "t \<in> I_set"
      have hp: "(1::real, t) \<in> I_set \<times> I_set"
        using ht unfolding top1_unit_interval_def by auto
      have "?H1 (1, t) = (1 - t) * (fst \<circ> f) 1 + t * fst x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h1: "?H1 (1, t) = fst x0"
        using hf1 by (simp add: comp_def algebra_simps)
      have "?H2 (1, t) = (1 - t) * (snd \<circ> f) 1 + t * snd x0"
        using top1_slh_ext_agrees[OF hp] by simp
      hence h2: "?H2 (1, t) = snd x0"
        using hf1 by (simp add: comp_def algebra_simps)
      show "?H (1, t) = x0" using h1 h2 by simp
    qed
    \<comment> \<open>Assemble: f is a path, constant is a path.\<close>
    have hTB2: "is_topology_on top1_B2 top1_B2_topology"
    proof -
      have hTR2': "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
                    (product_topology_on top1_open_sets top1_open_sets)"
        by (rule product_topology_on_is_topology_on[OF hTR hTR])
      show ?thesis unfolding top1_B2_topology_def
        by (rule subspace_topology_is_topology_on[OF hTR2'[unfolded hUU]]) simp
    qed
    have hfpath: "top1_is_path_on top1_B2 top1_B2_topology x0 x0 f"
      using hloop unfolding top1_is_loop_on_def .
    have hcpath: "top1_is_path_on top1_B2 top1_B2_topology x0 x0 (top1_constant_path x0)"
      by (rule top1_constant_path_is_path[OF hTB2 hx0])
    \<comment> \<open>Now the homotopy witnesses are H with II_topology.\<close>
    have hH_cont_II: "top1_continuous_map_on (I_set \<times> I_set) II_topology top1_B2 top1_B2_topology ?H"
      by (rule hH_cont_B2)
    show "top1_path_homotopic_on top1_B2 top1_B2_topology x0 x0 f (top1_constant_path x0)"
      unfolding top1_path_homotopic_on_def top1_constant_path_def
      using hfpath hcpath hH_cont_II hFs0 hFs1 hF0t hF1t
      unfolding top1_is_path_on_def top1_constant_path_def by blast
  qed
  show ?thesis
    unfolding top1_simply_connected_on_def using hpc hloops by blast
qed

(** from \<S>55 Theorem 55.2: No-retraction theorem: no retraction B^2 \<rightarrow> S^1.
    Munkres' proof: if S^1 were a retract of B^2, then the inclusion-induced
    homomorphism would be injective (Lemma 55.1). But \<pi>_1(S^1) is nontrivial
    and \<pi>_1(B^2) is trivial — contradiction. **)
theorem Theorem_55_2_no_retraction:
  "\<not> top1_retract_of_on top1_B2 top1_B2_topology top1_S1"
proof
  assume hret: "top1_retract_of_on top1_B2 top1_B2_topology top1_S1"
  \<comment> \<open>By Lemma 55.1, inclusion S^1 \<rightarrow> B^2 induces injective hom on \<pi>_1.\<close>
  \<comment> \<open>But \<pi>_1(S^1) is nontrivial and \<pi>_1(B^2) is trivial — contradiction.\<close>
  obtain f g where hf: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) f"
    and hg: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) g"
    and hne: "\<not> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f g"
    using top1_S1_fundamental_group_nontrivial by blast
  \<comment> \<open>Step 1: S^1 \<subseteq> B^2 and (1,0) is in S^1 = subspace\<close>
  have hSsub: "top1_S1 \<subseteq> top1_B2"
    unfolding top1_S1_def top1_B2_def by auto
  have hx0: "(1::real, 0::real) \<in> top1_S1"
    unfolding top1_S1_def by simp
  \<comment> \<open>Step 2: f, g are also loops in B^2 (via inclusion).\<close>
  have hS1sub_UNIV: "top1_S1 \<subseteq> UNIV" by simp
  have hB2sub_UNIV: "top1_B2 \<subseteq> UNIV" by simp
  have hf_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology f"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast
  have hg_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology g"
    using hg unfolding top1_is_loop_on_def top1_is_path_on_def by blast
  have hf_B2_cont: "top1_continuous_map_on I_set I_top top1_B2 top1_B2_topology f"
    using top1_continuous_map_on_codomain_enlarge[OF hf_cont[unfolded top1_S1_topology_def] hSsub hB2sub_UNIV]
    unfolding top1_B2_topology_def .
  have hg_B2_cont: "top1_continuous_map_on I_set I_top top1_B2 top1_B2_topology g"
    using top1_continuous_map_on_codomain_enlarge[OF hg_cont[unfolded top1_S1_topology_def] hSsub hB2sub_UNIV]
    unfolding top1_B2_topology_def .
  have hf_0: "f 0 = (1, 0)" "f 1 = (1, 0)"
    using hf unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have hg_0: "g 0 = (1, 0)" "g 1 = (1, 0)"
    using hg unfolding top1_is_loop_on_def top1_is_path_on_def by blast+
  have hf_B2: "top1_is_loop_on top1_B2 top1_B2_topology (1, 0) f"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hf_B2_cont hf_0 by blast
  have hg_B2: "top1_is_loop_on top1_B2 top1_B2_topology (1, 0) g"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hg_B2_cont hg_0 by blast
  \<comment> \<open>Step 3: Since B^2 is simply connected, f and g are path-homotopic in B^2.\<close>
  have hf_path_B2: "top1_is_path_on top1_B2 top1_B2_topology (1, 0) (1, 0) f"
    using hf_B2 unfolding top1_is_loop_on_def .
  have hg_path_B2: "top1_is_path_on top1_B2 top1_B2_topology (1, 0) (1, 0) g"
    using hg_B2 unfolding top1_is_loop_on_def .
  have hx0_B2: "(1::real, 0::real) \<in> top1_B2"
    unfolding top1_B2_def by simp
  have hf_const_B2: "top1_path_homotopic_on top1_B2 top1_B2_topology (1, 0) (1, 0)
                                             f (top1_constant_path (1, 0))"
    using top1_B2_simply_connected hf_B2 hx0_B2
    unfolding top1_simply_connected_on_def by blast
  have hg_const_B2: "top1_path_homotopic_on top1_B2 top1_B2_topology (1, 0) (1, 0)
                                             g (top1_constant_path (1, 0))"
    using top1_B2_simply_connected hg_B2 hx0_B2
    unfolding top1_simply_connected_on_def by blast
  have hg_const_sym: "top1_path_homotopic_on top1_B2 top1_B2_topology (1, 0) (1, 0)
                                              (top1_constant_path (1, 0)) g"
    by (rule Lemma_51_1_path_homotopic_sym[OF hg_const_B2])
  have hTB2: "is_topology_on top1_B2 top1_B2_topology"
  proof -
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2': "is_topology_on ((UNIV::real set) \<times> (UNIV::real set))
                  (product_topology_on top1_open_sets top1_open_sets)"
      by (rule product_topology_on_is_topology_on[OF hTR hTR])
    have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using hTR2' unfolding hUU .
    show ?thesis unfolding top1_B2_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR2], simp)
  qed
  have hfg_B2: "top1_path_homotopic_on top1_B2 top1_B2_topology (1, 0) (1, 0) f g"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTB2 hf_const_B2 hg_const_sym])
  \<comment> \<open>Step 4: Apply Lemma 55.1 to transfer path-homotopy back to S^1.\<close>
  \<comment> \<open>Identify subspace_topology top1_B2 top1_B2_topology top1_S1 with top1_S1_topology.\<close>
  have htop_eq: "subspace_topology top1_B2 top1_B2_topology top1_S1 = top1_S1_topology"
    unfolding top1_B2_topology_def top1_S1_topology_def
    by (rule subspace_topology_trans[OF hSsub])
  have hf_sub: "top1_is_loop_on top1_S1 (subspace_topology top1_B2 top1_B2_topology top1_S1) (1,0) f"
    using hf unfolding htop_eq .
  have hg_sub: "top1_is_loop_on top1_S1 (subspace_topology top1_B2 top1_B2_topology top1_S1) (1,0) g"
    using hg unfolding htop_eq .
  have hfg_sub: "top1_path_homotopic_on top1_S1 (subspace_topology top1_B2 top1_B2_topology top1_S1) (1,0) (1,0) f g"
    using Lemma_55_1_retract_injective[OF hret hx0 hf_sub hg_sub hfg_B2] .
  have hfg_S1: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f g"
    using hfg_sub unfolding htop_eq .
  show False using hne hfg_S1 by blast
qed

text \<open>Helper for Brouwer: v = f - id is continuous B^2 \<rightarrow> R^2.\<close>
lemma top1_B2_diff_continuous:
  assumes hf: "top1_continuous_map_on top1_B2 top1_B2_topology top1_B2 top1_B2_topology f"
  shows "top1_continuous_map_on top1_B2 top1_B2_topology
    (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)
    (\<lambda>x. (fst (f x) - fst x, snd (f x) - snd x))"
proof -
  have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
  have hTB2: "is_topology_on top1_B2 top1_B2_topology"
    unfolding top1_B2_topology_def
    by (rule subspace_topology_is_topology_on) (use product_topology_on_is_topology_on[OF hTR hTR] in simp_all)
  have hfst: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets fst"
    using top1_fst_continuous_R2_subspace[of top1_B2] unfolding top1_B2_topology_def .
  have hsnd: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets snd"
    using top1_snd_continuous_R2_subspace[of top1_B2] unfolding top1_B2_topology_def .
  have hfstf: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (fst \<circ> f)"
    by (rule top1_continuous_map_on_comp[OF hf hfst])
  have hsndf: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (snd \<circ> f)"
    by (rule top1_continuous_map_on_comp[OF hf hsnd])
  let ?v = "\<lambda>x::real\<times>real. (fst (f x) - fst x, snd (f x) - snd x)"
  \<comment> \<open>Each component via composition with pairing + subtraction.\<close>
  have hcomp_cont: "\<And>g h. \<lbrakk>top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets g;
      top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets h\<rbrakk> \<Longrightarrow>
    top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (\<lambda>x. g x - h x)"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI allI impI)
    fix g h :: "real \<times> real \<Rightarrow> real" and x V
    assume hg: "(\<forall>x\<in>top1_B2. g x \<in> UNIV) \<and> (\<forall>V\<in>top1_open_sets. {x \<in> top1_B2. g x \<in> V} \<in> top1_B2_topology)"
    and hh: "(\<forall>x\<in>top1_B2. h x \<in> UNIV) \<and> (\<forall>V\<in>top1_open_sets. {x \<in> top1_B2. h x \<in> V} \<in> top1_B2_topology)"
    show "g x - h x \<in> UNIV" by simp
  next
    fix g h :: "real \<times> real \<Rightarrow> real" and V :: "real set"
    assume hg: "(\<forall>x\<in>top1_B2. g x \<in> UNIV) \<and> (\<forall>V\<in>top1_open_sets. {x \<in> top1_B2. g x \<in> V} \<in> top1_B2_topology)"
    and hh: "(\<forall>x\<in>top1_B2. h x \<in> UNIV) \<and> (\<forall>V\<in>top1_open_sets. {x \<in> top1_B2. h x \<in> V} \<in> top1_B2_topology)"
    and hV: "V \<in> top1_open_sets"
    \<comment> \<open>Preimage via (g, h) and subtraction.\<close>
    have hVo: "open V" using hV unfolding top1_open_sets_def by blast
    have "open ((\<lambda>p::real\<times>real. fst p - snd p) -` V)"
    proof (rule open_vimage[OF hVo])
      show "continuous_on UNIV (\<lambda>p::real\<times>real. fst p - snd p)" by (intro continuous_intros)
    qed
    hence hW: "(\<lambda>p::real\<times>real. fst p - snd p) -` V \<in> product_topology_on top1_open_sets top1_open_sets"
    proof -
      assume "open ((\<lambda>p::real\<times>real. fst p - snd p) -` V)"
      hence "(\<lambda>p::real\<times>real. fst p - snd p) -` V \<in> (top1_open_sets :: (real\<times>real) set set)"
        unfolding top1_open_sets_def by blast
      thus ?thesis using product_topology_on_open_sets_real2 by metis
    qed
    have hpair: "top1_continuous_map_on top1_B2 top1_B2_topology
        (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)
        (\<lambda>x. (g x, h x))"
    proof -
      have hp1: "pi1 \<circ> (\<lambda>x. (g x, h x)) = g" unfolding pi1_def by (rule ext) simp
      have hp2: "pi2 \<circ> (\<lambda>x. (g x, h x)) = h" unfolding pi2_def by (rule ext) simp
      have hg_cont: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (pi1 \<circ> (\<lambda>x. (g x, h x)))"
        using hg unfolding hp1 top1_continuous_map_on_def by blast
      have hh_cont: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (pi2 \<circ> (\<lambda>x. (g x, h x)))"
        using hh unfolding hp2 top1_continuous_map_on_def by blast
      have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
      show ?thesis using iffD2[OF Theorem_18_4[OF hTB2 hTR hTR, of "\<lambda>x. (g x, h x)"]]
        hg_cont hh_cont unfolding hUU by blast
    qed
    have heq: "{x \<in> top1_B2. g x - h x \<in> V}
        = {x \<in> top1_B2. (\<lambda>x. (g x, h x)) x \<in> (\<lambda>p. fst p - snd p) -` V}"
      by auto
    show "{x \<in> top1_B2. g x - h x \<in> V} \<in> top1_B2_topology"
      unfolding heq using hpair hW unfolding top1_continuous_map_on_def by blast
  qed
  have hv1: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets
      (\<lambda>x. fst (f x) - fst x)"
    using hcomp_cont[OF hfstf hfst] by (simp add: comp_def)
  have hv2: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets
      (\<lambda>x. snd (f x) - snd x)"
    using hcomp_cont[OF hsndf hsnd] by (simp add: comp_def)
  have hpi1_v: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (pi1 \<circ> ?v)"
  proof -
    have "pi1 \<circ> ?v = (\<lambda>x. fst (f x) - fst x)" unfolding pi1_def comp_def by auto
    thus ?thesis using hv1 by simp
  qed
  have hpi2_v: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV::real set) top1_open_sets (pi2 \<circ> ?v)"
  proof -
    have "pi2 \<circ> ?v = (\<lambda>x. snd (f x) - snd x)" unfolding pi2_def comp_def by auto
    thus ?thesis using hv2 by simp
  qed
  have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
  show ?thesis using iffD2[OF Theorem_18_4[OF hTB2 hTR hTR, of ?v]]
    hpi1_v hpi2_v unfolding hUU by blast
qed

text \<open>Backward direction of Lemma 55.3: extension to B^2 implies nulhomotopic.\<close>
lemma Lemma_55_3_backward:
  fixes h :: "real \<times> real \<Rightarrow> 'a"
  assumes hh: "top1_continuous_map_on top1_S1 top1_S1_topology X TX h"
      and hTX: "is_topology_on X TX"
      and hk: "top1_continuous_map_on top1_B2 top1_B2_topology X TX k"
      and hext: "\<forall>x\<in>top1_S1. k x = h x"
  shows "top1_nulhomotopic_on top1_S1 top1_S1_topology X TX h"
proof -
  let ?c = "k (1::real, 0::real)"
  have hc_X: "?c \<in> X"
  proof -
    have "(1::real, 0::real) \<in> top1_B2" unfolding top1_B2_def by simp
    thus ?thesis using hk unfolding top1_continuous_map_on_def by blast
  qed
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
  proof -
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using product_topology_on_is_topology_on[OF hTR hTR] by simp
    show ?thesis unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR2]) simp
  qed
  have hconst: "top1_continuous_map_on top1_S1 top1_S1_topology X TX (\<lambda>_. ?c)"
    by (rule top1_continuous_map_on_const[OF hTS1 hTX hc_X])
  \<comment> \<open>The homotopy F(x,t) = k((1-t)*fst x + t, (1-t)*snd x) shrinks S^1 to (1,0).\<close>
  let ?F = "\<lambda>(x::real\<times>real, t::real). k ((1-t) * fst x + t, (1-t) * snd x)"
  have hS1_in_B2: "top1_S1 \<subseteq> top1_B2"
    unfolding top1_S1_def top1_B2_def by auto
  have h10_B2: "(1::real, 0::real) \<in> top1_B2" unfolding top1_B2_def by simp
  have hF_in_B2: "\<And>x t. x \<in> top1_S1 \<Longrightarrow> t \<in> I_set \<Longrightarrow>
    ((1-t) * fst x + t, (1-t) * snd x) \<in> top1_B2"
  proof -
    fix x :: "real \<times> real" and t :: real
    assume hx: "x \<in> top1_S1" and ht: "t \<in> I_set"
    have hxB2: "x \<in> top1_B2" using hx hS1_in_B2 by blast
    have ht0: "0 \<le> t" and ht1: "t \<le> 1" using ht unfolding top1_unit_interval_def by auto
    show "((1-t) * fst x + t, (1-t) * snd x) \<in> top1_B2"
    proof -
      have "((1-t) * fst x + t * fst (1::real, 0::real),
             (1-t) * snd x + t * snd (1::real, 0::real)) \<in> top1_B2"
        by (rule top1_B2_convex[OF hxB2 h10_B2 ht0 ht1])
      thus ?thesis by simp
    qed
  qed
  \<comment> \<open>Continuity of F: composition of polynomial \<phi> and k.\<close>
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  have hF_cont: "top1_continuous_map_on (top1_S1 \<times> I_set)
      (product_topology_on top1_S1_topology I_top) X TX ?F"
  proof -
    let ?\<phi> = "\<lambda>(x::real\<times>real, t::real). ((1-t) * fst x + t, (1-t) * snd x)"
    \<comment> \<open>\<phi> is continuous S^1\<times>I \<rightarrow> B^2 (polynomial in components).\<close>
    have h\<phi>_cont_on: "continuous_on UNIV (\<lambda>p::((real\<times>real)\<times>real). ((1 - snd p) * fst (fst p) + snd p,
                                                                    (1 - snd p) * snd (fst p)))"
      by (intro continuous_intros)
    \<comment> \<open>Transfer to custom topology via the bridge lemmas.\<close>
    have hTP: "is_topology_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)"
      by (rule product_topology_on_is_topology_on[OF hTS1 hTI])
    have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
    have hTB2: "is_topology_on top1_B2 top1_B2_topology"
      unfolding top1_B2_topology_def
      by (rule subspace_topology_is_topology_on)
         (use product_topology_on_is_topology_on[OF hTR hTR] in simp_all)
    \<comment> \<open>\<phi> maps S^1\<times>I into B^2.\<close>
    have h\<phi>_range: "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> ?\<phi> p \<in> top1_B2"
      using hF_in_B2 by auto
    \<comment> \<open>\<phi> continuous via Theorem 18.4 + fst/snd projections.\<close>
    \<comment> \<open>Each component of \<phi> is continuous to R (polynomial in coordinates).\<close>
    \<comment> \<open>General helper: if f: R^3 \<rightarrow> R is continuous_on UNIV and maps S1\<times>I to R,
       then f is continuous from product_topology to top1_open_sets.\<close>
    have poly_cont: "\<And>f. continuous_on UNIV (f :: (real\<times>real)\<times>real \<Rightarrow> real) \<Longrightarrow>
        top1_continuous_map_on (top1_S1 \<times> I_set)
          (product_topology_on top1_S1_topology I_top) (UNIV::real set) top1_open_sets f"
      unfolding top1_continuous_map_on_def
    proof (intro conjI ballI allI impI)
      fix f :: "(real\<times>real)\<times>real \<Rightarrow> real" and p V
      assume hcont: "continuous_on UNIV f"
      show "f p \<in> (UNIV::real set)" by simp
    next
      fix f :: "(real\<times>real)\<times>real \<Rightarrow> real" and V :: "real set"
      assume hcont: "continuous_on UNIV f" and hV: "V \<in> top1_open_sets"
      have hVo: "open V" using hV unfolding top1_open_sets_def by blast
      have "open (f -` V)" by (rule open_vimage[OF hVo hcont])
      hence hfV: "f -` V \<in> (top1_open_sets :: ((real\<times>real)\<times>real) set set)"
        unfolding top1_open_sets_def by blast
      \<comment> \<open>f\<inverse>(V) is open in R^3. Its intersection with S1\<times>I is open in S1\<times>I.\<close>
      have hfV_prod: "f -` V \<in> product_topology_on
          (product_topology_on top1_open_sets top1_open_sets) top1_open_sets"
      proof -
        have heq: "product_topology_on (product_topology_on (top1_open_sets::real set set)
            (top1_open_sets::real set set)) (top1_open_sets::real set set)
          = (top1_open_sets :: ((real\<times>real)\<times>real) set set)"
          using product_topology_on_open_sets_real2
                product_topology_on_open_sets[where ?'a = "real \<times> real" and ?'b = real]
          by metis
        show ?thesis unfolding heq by (rule hfV)
      qed
      have "{p \<in> top1_S1 \<times> I_set. f p \<in> V} = (top1_S1 \<times> I_set) \<inter> (f -` V)" by auto
      also have "\<dots> \<in> product_topology_on top1_S1_topology I_top"
      proof -
        have "product_topology_on top1_S1_topology I_top =
              subspace_topology ((UNIV::(real\<times>real) set) \<times> (UNIV::real set))
                (product_topology_on (product_topology_on top1_open_sets top1_open_sets) top1_open_sets)
                (top1_S1 \<times> I_set)"
        proof -
          have "product_topology_on top1_S1_topology I_top =
                product_topology_on
                  (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_S1)
                  (subspace_topology UNIV top1_open_sets I_set)"
            unfolding top1_S1_topology_def top1_unit_interval_topology_def by simp
          also have "\<dots> = subspace_topology (UNIV \<times> UNIV)
                (product_topology_on (product_topology_on top1_open_sets top1_open_sets) top1_open_sets)
                (top1_S1 \<times> I_set)"
          proof -
            have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
              using product_topology_on_is_topology_on[OF hTR hTR] by simp
            show ?thesis by (rule Theorem_16_3[OF hTR2 hTR])
          qed
          finally show ?thesis by simp
        qed
        thus ?thesis using hfV_prod unfolding subspace_topology_def by blast
      qed
      finally show "{p \<in> top1_S1 \<times> I_set. f p \<in> V} \<in>
          product_topology_on top1_S1_topology I_top" .
    qed
    have hfst_\<phi>: "top1_continuous_map_on (top1_S1 \<times> I_set)
        (product_topology_on top1_S1_topology I_top) (UNIV::real set) top1_open_sets
        (\<lambda>p. (1 - snd p) * fst (fst p) + snd p)"
      by (rule poly_cont) (intro continuous_intros)
    have hsnd_\<phi>: "top1_continuous_map_on (top1_S1 \<times> I_set)
        (product_topology_on top1_S1_topology I_top) (UNIV::real set) top1_open_sets
        (\<lambda>p. (1 - snd p) * snd (fst p))"
      by (rule poly_cont) (intro continuous_intros)
    \<comment> \<open>Combine into pair by Theorem 18.4.\<close>
    have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
      using product_topology_on_is_topology_on[OF hTR hTR] by simp
    have hpi1_eq: "pi1 \<circ> ?\<phi> = (\<lambda>p. (1 - snd p) * fst (fst p) + snd p)"
      unfolding pi1_def comp_def by (rule ext) auto
    have hpi2_eq: "pi2 \<circ> ?\<phi> = (\<lambda>p. (1 - snd p) * snd (fst p))"
      unfolding pi2_def comp_def by (rule ext) auto
    have hUU: "(UNIV::real set) \<times> (UNIV::real set) = (UNIV::(real\<times>real) set)" by simp
    have h\<phi>_R2: "top1_continuous_map_on (top1_S1 \<times> I_set)
        (product_topology_on top1_S1_topology I_top) (UNIV::(real\<times>real) set)
        (product_topology_on top1_open_sets top1_open_sets) ?\<phi>"
      using iffD2[OF Theorem_18_4[OF hTP hTR hTR, of ?\<phi>]]
            hfst_\<phi>[folded hpi1_eq] hsnd_\<phi>[folded hpi2_eq] unfolding hUU by blast
    have h\<phi>_img: "?\<phi> ` (top1_S1 \<times> I_set) \<subseteq> top1_B2"
      using h\<phi>_range by auto
    have h\<phi>_cont: "top1_continuous_map_on (top1_S1 \<times> I_set)
        (product_topology_on top1_S1_topology I_top) top1_B2 top1_B2_topology ?\<phi>"
      using top1_continuous_map_on_codomain_shrink[OF h\<phi>_R2 h\<phi>_img]
      unfolding top1_B2_topology_def by simp
    \<comment> \<open>F = k \<circ> \<phi>.\<close>
    have hF_eq: "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> ?F p = (k \<circ> ?\<phi>) p"
      by (auto simp: comp_def case_prod_beta)
    have "top1_continuous_map_on (top1_S1 \<times> I_set)
        (product_topology_on top1_S1_topology I_top) X TX (k \<circ> ?\<phi>)"
      by (rule top1_continuous_map_on_comp[OF h\<phi>_cont hk])
    thus ?thesis
      using hF_eq unfolding top1_continuous_map_on_def comp_def
      by (auto simp: case_prod_beta)
  qed
  have hF0: "\<forall>x\<in>top1_S1. ?F (x, 0) = h x"
  proof
    fix x assume hx: "x \<in> top1_S1"
    have "?F (x, 0) = k (fst x, snd x)" by simp
    also have "\<dots> = k x" by simp
    also have "\<dots> = h x" using hext hx by blast
    finally show "?F (x, 0) = h x" .
  qed
  have hF1: "\<forall>x\<in>top1_S1. ?F (x, 1) = ?c" by simp
  show ?thesis
    unfolding top1_nulhomotopic_on_def top1_homotopic_on_def
    using hc_X hh hconst hF_cont hF0 hF1 by blast
qed

(** from \<S>55 Lemma 55.3: nulhomotopic characterization **)
lemma Lemma_55_3_nulhomotopic_characterization:
  fixes h :: "real \<times> real \<Rightarrow> 'a"
  assumes hh: "top1_continuous_map_on top1_S1 top1_S1_topology X TX h"
      and hTX: "is_topology_on X TX"
  shows "top1_nulhomotopic_on top1_S1 top1_S1_topology X TX h
      \<longleftrightarrow> (\<exists>k. top1_continuous_map_on top1_B2 top1_B2_topology X TX k
               \<and> (\<forall>x\<in>top1_S1. k x = h x))"
proof (intro iffI)
  \<comment> \<open>Forward (1)\<Rightarrow>(2): nulhomotopic \<Rightarrow> extension to B^2.
     Munkres: Let H: S^1\<times>I \<rightarrow> X be homotopy from h to const. The quotient map
     \<pi>(x,t) = (1-t)x collapses S^1\<times>{1} to 0 and is otherwise injective.
     Since H is constant on S^1\<times>{1}, it factors through \<pi>, giving k: B^2 \<rightarrow> X.\<close>
  assume hnul: "top1_nulhomotopic_on top1_S1 top1_S1_topology X TX h"
  \<comment> \<open>Munkres' proof: H: S^1 \<times> I \<rightarrow> X is homotopy from h to const c.
     Define \<pi>: S^1 \<times> I \<rightarrow> B^2 by \<pi>(x,t) = (1-t)x. This maps S^1 \<times> {0} to S^1 (homeomorphically)
     and collapses S^1 \<times> {1} to {0}. Since H is constant on S^1 \<times> {1},
     H factors through \<pi>: k(\<pi>(x,t)) = H(x,t), i.e., k((1-t)x) = H(x,t).\<close>
  obtain c where hc: "c \<in> X"
      and hhom: "top1_homotopic_on top1_S1 top1_S1_topology X TX h (\<lambda>_. c)"
    using hnul unfolding top1_nulhomotopic_on_def by (by100 blast)
  obtain H where hH_cont: "top1_continuous_map_on (top1_S1 \<times> I_set)
        (product_topology_on top1_S1_topology I_top) X TX H"
      and hH0: "\<forall>x\<in>top1_S1. H (x, 0) = h x"
      and hH1: "\<forall>x\<in>top1_S1. H (x, 1) = c"
    using hhom unfolding top1_homotopic_on_def by (by100 blast)
  \<comment> \<open>Define k: B^2 \<rightarrow> X. For y \<in> B^2, write y = (1-t) \<cdot> (y/|y|) for t = 1-|y|,
     so k(y) = H(y/|y|, 1-|y|) for y \<ne> 0, and k(0) = c.\<close>
  define k where "k = (\<lambda>y. if y = (0::real, 0::real) then c
      else H ((fst y / sqrt (fst y ^ 2 + snd y ^ 2),
               snd y / sqrt (fst y ^ 2 + snd y ^ 2)),
              1 - sqrt (fst y ^ 2 + snd y ^ 2)))"
  \<comment> \<open>k extends h: for x \<in> S^1, |x| = 1, so k(x) = H(x, 0) = h(x).\<close>
  have hext: "\<forall>x\<in>top1_S1. k x = h x"
  proof
    fix x assume hx: "x \<in> top1_S1"
    have hx_eq: "fst x ^ 2 + snd x ^ 2 = 1" using hx unfolding top1_S1_def by (by100 auto)
    have hx_ne: "x \<noteq> (0, 0)"
    proof
      assume "x = (0, 0)"
      hence "fst x ^ 2 + snd x ^ 2 = 0" by simp
      thus False using hx_eq by simp
    qed
    have hsqrt: "sqrt (fst x ^ 2 + snd x ^ 2) = 1"
      using hx_eq by simp
    have "k x = H ((fst x / 1, snd x / 1), 1 - 1)"
      unfolding k_def using hx_ne hsqrt by simp
    also have "\<dots> = H (x, 0)" by simp
    also have "\<dots> = h x" using hH0 hx by (by100 blast)
    finally show "k x = h x" .
  qed
  \<comment> \<open>k is continuous: on B^2 - {0}, continuous by composition; at 0, use H(x,1) = c.\<close>
  have hk_cont: "top1_continuous_map_on top1_B2 top1_B2_topology X TX k"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    \<comment> \<open>Part 1: k maps B^2 to X.\<close>
    fix y assume hy: "y \<in> top1_B2"
    show "k y \<in> X"
    proof (cases "y = (0, 0)")
      case True thus ?thesis unfolding k_def using hc by simp
    next
      case False
      \<comment> \<open>y \<noteq> 0: k(y) = H(y/|y|, 1-|y|). Need y/|y| \<in> S^1 and 1-|y| \<in> I.\<close>
      have hy_ne: "y \<noteq> (0::real, 0::real)" by (rule False)
      have hnorm_pos: "sqrt (fst y ^ 2 + snd y ^ 2) > 0"
      proof -
        have "fst y ^ 2 + snd y ^ 2 > 0"
        proof -
          obtain a b where hab: "y = (a, b)" by (cases y)
          have "a \<noteq> 0 \<or> b \<noteq> 0" using hy_ne hab by auto
          hence "a ^ 2 > 0 \<or> b ^ 2 > 0" by auto
          hence "a ^ 2 + b ^ 2 > 0"
            by (metis zero_less_power2 add_pos_nonneg add_nonneg_pos zero_le_power2)
          thus ?thesis using hab by simp
        qed
        thus ?thesis by simp
      qed
      have hnorm_le1: "sqrt (fst y ^ 2 + snd y ^ 2) \<le> 1"
        using hy unfolding top1_B2_def by (simp add: real_le_rsqrt)
      have hunit: "(fst y / sqrt (fst y ^ 2 + snd y ^ 2),
                    snd y / sqrt (fst y ^ 2 + snd y ^ 2)) \<in> top1_S1"
        using hnorm_pos unfolding top1_S1_def
        by (auto simp: power_divide add_divide_distrib[symmetric] real_sqrt_gt_zero)
      have ht_I: "1 - sqrt (fst y ^ 2 + snd y ^ 2) \<in> I_set"
        unfolding top1_unit_interval_def using hnorm_pos hnorm_le1 by simp
      have "k y = H ((fst y / sqrt (fst y ^ 2 + snd y ^ 2),
                      snd y / sqrt (fst y ^ 2 + snd y ^ 2)),
                     1 - sqrt (fst y ^ 2 + snd y ^ 2))"
        unfolding k_def using hy_ne by simp
      moreover have "H ((fst y / sqrt (fst y ^ 2 + snd y ^ 2),
                         snd y / sqrt (fst y ^ 2 + snd y ^ 2)),
                        1 - sqrt (fst y ^ 2 + snd y ^ 2)) \<in> X"
        using hH_cont hunit ht_I unfolding top1_continuous_map_on_def by (by100 blast)
      ultimately show ?thesis by simp
    qed
  next
    \<comment> \<open>Part 2: preimage of open is open.\<close>
    fix V assume hV: "V \<in> TX"
    show "{y \<in> top1_B2. k y \<in> V} \<in> top1_B2_topology"
    proof -
      \<comment> \<open>H\<inverse>(V) is open in S^1\<times>I: from H continuous.\<close>
      have hHV: "{p \<in> top1_S1 \<times> I_set. H p \<in> V} \<in> product_topology_on top1_S1_topology I_top"
        using hH_cont hV unfolding top1_continuous_map_on_def by (by100 blast)
      \<comment> \<open>Pointwise openness: for each y0 \<in> B^2 with k(y0) \<in> V, find open nbhd.\<close>
      have hpointwise: "\<forall>y0\<in>top1_B2. k y0 \<in> V \<longrightarrow>
          (\<exists>W. open W \<and> y0 \<in> W \<and> (\<forall>y\<in>top1_B2. y \<in> W \<longrightarrow> k y \<in> V))"
      proof (intro ballI impI)
        fix y0 assume hy0: "y0 \<in> top1_B2" and hky0: "k y0 \<in> V"
        show "\<exists>W. open W \<and> y0 \<in> W \<and> (\<forall>y\<in>top1_B2. y \<in> W \<longrightarrow> k y \<in> V)"
        proof (cases "y0 = (0, 0)")
          case True
          \<comment> \<open>Case y0 = 0: k(0) = c \<in> V.\<close>
          \<comment> \<open>Step 1: S^1\<times>{1} \<subseteq> H^{-1}(V).\<close>
          have hS1_1_in_HV: "\<forall>x\<in>top1_S1. H (x, 1) \<in> V"
            using hH1 hky0 True unfolding k_def by simp
          \<comment> \<open>Step 2: S^1 is compact (image of compact [0,1] under continuous R_to_S1).\<close>
          have hS1_compact: "compact top1_S1"
          proof -
            have "top1_R_to_S1 ` {0..1::real} = top1_S1"
            proof (rule set_eqI)
              fix p show "(p \<in> top1_R_to_S1 ` {0..1}) = (p \<in> top1_S1)"
              proof
                assume "p \<in> top1_R_to_S1 ` {0..1}"
                then obtain t where ht: "t \<in> {0..1}" and hp: "p = top1_R_to_S1 t" by (by100 blast)
                show "p \<in> top1_S1" unfolding hp top1_R_to_S1_def top1_S1_def
                  by (auto simp: power2_eq_square[symmetric] sin_cos_squared_add2)
              next
                assume "p \<in> top1_S1"
                hence "fst p ^ 2 + snd p ^ 2 = 1" unfolding top1_S1_def by (by100 auto)
                \<comment> \<open>Find t with cos(2\<pi>t) = fst p, sin(2\<pi>t) = snd p, 0 \<le> t \<le> 1.\<close>
                \<comment> \<open>From surjectivity: p \<in> S^1 = R_to_S1 ` UNIV. Get t \<in> UNIV.
                   Then t' = t - floor t \<in> [0,1) and R_to_S1(t') = R_to_S1(t) = p.\<close>
                have "p \<in> top1_R_to_S1 ` UNIV"
                proof -
                  have "top1_R_to_S1 ` UNIV = top1_S1"
                    using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
                  thus ?thesis using \<open>p \<in> top1_S1\<close> by simp
                qed
                then obtain t where hp_eq: "p = top1_R_to_S1 t" by (by100 blast)
                define t' where "t' = t - of_int (floor t)"
                have ht'_01: "t' \<ge> 0 \<and> t' < 1"
                proof -
                  have "t' = frac t" unfolding t'_def frac_def by simp
                  thus ?thesis using frac_lt_1[of t] frac_ge_0[of t] by simp
                qed
                have "top1_R_to_S1 t' = top1_R_to_S1 t"
                proof -
                  have "t = t' + of_int (floor t)" unfolding t'_def by simp
                  thus ?thesis using top1_R_to_S1_int_shift_early[of t' "floor t"] by simp
                qed
                hence "p = top1_R_to_S1 t'" using hp_eq by simp
                moreover have "t' \<in> {0..1}" using ht'_01 by simp
                ultimately show "p \<in> top1_R_to_S1 ` {0..1}" by (by100 blast)
              qed
            qed
            moreover have "compact (top1_R_to_S1 ` {0..1::real})"
            proof -
              have "continuous_on {0..1::real} top1_R_to_S1"
                unfolding top1_R_to_S1_def by (intro continuous_intros)
              thus ?thesis by (rule compact_continuous_image[OF _ compact_Icc])
            qed
            ultimately show ?thesis by simp
          qed
          \<comment> \<open>Step 3: top1_compact_on S^1 S^1_topology.\<close>
          have hS1_top1_compact: "top1_compact_on top1_S1 top1_S1_topology"
          proof -
            have "top1_compact_on top1_S1
                (subspace_topology (UNIV::(real\<times>real) set) (top1_open_sets::(real\<times>real) set set) top1_S1)"
              using top1_compact_on_subspace_UNIV_iff_compact[of top1_S1] hS1_compact by simp
            moreover have "(top1_open_sets::(real\<times>real) set set)
                = product_topology_on (top1_open_sets::real set set) top1_open_sets"
              using product_topology_on_open_sets_real2 by (by100 metis)
            ultimately show ?thesis unfolding top1_S1_topology_def by simp
          qed
          \<comment> \<open>Step 4: Apply tube lemma to swapped product I \<times> S^1.\<close>
          have hITop: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
          have h1I: "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
          have hS1Top: "is_topology_on top1_S1 top1_S1_topology"
          proof -
            have hTR_: "is_topology_on (UNIV::real set) top1_open_sets"
              by (rule top1_open_sets_is_topology_on_UNIV)
            have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
              using product_topology_on_is_topology_on[OF hTR_ hTR_] by simp
            thus ?thesis unfolding top1_S1_topology_def
              by (rule subspace_topology_is_topology_on) simp
          qed
          \<comment> \<open>Swapped preimage: N = {(t,x) | H(x,t) \<in> V} open in I \<times> S^1.\<close>
          define N where "N = (\<lambda>(t,x). (x,t)) -` {p \<in> top1_S1 \<times> I_set. H p \<in> V} \<inter> (I_set \<times> top1_S1)"
          have hN_eq: "N = {(t,x). x \<in> top1_S1 \<and> t \<in> I_set \<and> H(x,t) \<in> V}" unfolding N_def by auto
          have hN_open: "N \<in> product_topology_on I_top top1_S1_topology"
          proof -
            \<comment> \<open>N is open in I \<times> S^1: for each (t,x) \<in> N, find basis rect.\<close>
            have "\<forall>p\<in>N. \<exists>b\<in>product_basis I_top top1_S1_topology. p \<in> b \<and> b \<subseteq> N"
            proof
              fix p assume "p \<in> N"
              obtain t x where hpair: "p = (t, x)" and hx: "x \<in> top1_S1" and ht: "t \<in> I_set"
                  and hHxt: "H (x, t) \<in> V" using \<open>p \<in> N\<close> unfolding hN_eq by auto
              have "(x, t) \<in> {p \<in> top1_S1 \<times> I_set. H p \<in> V}" using hx ht hHxt by simp
              \<comment> \<open>hHV: H\<inverse>(V) open in S^1\<times>I. Get basis rect containing (x,t).\<close>
              have "product_topology_on top1_S1_topology I_top =
                  topology_generated_by_basis UNIV (product_basis top1_S1_topology I_top)"
                unfolding product_topology_on_def by simp
              hence "{p \<in> top1_S1 \<times> I_set. H p \<in> V} \<in>
                  topology_generated_by_basis UNIV (product_basis top1_S1_topology I_top)"
                using hHV by simp
              hence hbasis_prop: "\<forall>q\<in>{p \<in> top1_S1 \<times> I_set. H p \<in> V}.
                  \<exists>b\<in>product_basis top1_S1_topology I_top. q \<in> b \<and> b \<subseteq> {p \<in> top1_S1 \<times> I_set. H p \<in> V}"
                unfolding topology_generated_by_basis_def by (by100 blast)
              from hbasis_prop[rule_format, OF \<open>(x, t) \<in> {p \<in> top1_S1 \<times> I_set. H p \<in> V}\<close>]
              obtain bxt where hbxt: "bxt \<in> product_basis top1_S1_topology I_top"
                  and hxt_in: "(x, t) \<in> bxt" and hbxt_sub: "bxt \<subseteq> {p \<in> top1_S1 \<times> I_set. H p \<in> V}"
                by (by100 blast)
              obtain Ux Ut where hUx: "Ux \<in> top1_S1_topology" and hUt: "Ut \<in> I_top"
                  and hbxt_eq: "bxt = Ux \<times> Ut"
                using hbxt unfolding product_basis_def by (by100 blast)
              \<comment> \<open>Swap: Ut \<times> Ux is a basis element of I \<times> S^1.\<close>
              have "Ut \<times> Ux \<in> product_basis I_top top1_S1_topology"
                unfolding product_basis_def using hUt hUx by (by100 blast)
              moreover have "p \<in> Ut \<times> Ux" using hxt_in hbxt_eq hpair by (by100 auto)
              moreover have "Ut \<times> Ux \<subseteq> N"
              proof
                fix q assume "q \<in> Ut \<times> Ux"
                obtain t' x' where hq: "q = (t', x')" and ht': "t' \<in> Ut" and hx': "x' \<in> Ux"
                  using \<open>q \<in> Ut \<times> Ux\<close> by (by100 blast)
                have "(x', t') \<in> Ux \<times> Ut" using hx' ht' by simp
                hence "(x', t') \<in> bxt" using hbxt_eq by simp
                hence "(x', t') \<in> {p \<in> top1_S1 \<times> I_set. H p \<in> V}" using hbxt_sub by (by100 blast)
                thus "q \<in> N" unfolding hN_eq hq by simp
              qed
              ultimately show "\<exists>b\<in>product_basis I_top top1_S1_topology. p \<in> b \<and> b \<subseteq> N"
                by (intro bexI[of _ "Ut \<times> Ux"] conjI) auto
            qed
            moreover have "N \<subseteq> UNIV" by simp
            ultimately show ?thesis
              unfolding product_topology_on_def topology_generated_by_basis_def by (by100 blast)
          qed
          have hslice: "{1::real} \<times> top1_S1 \<subseteq> N"
          proof -
            have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
            thus ?thesis unfolding hN_eq using hS1_1_in_HV by auto
          qed
          \<comment> \<open>Tube lemma: S^1 compact, N open in I \<times> S^1, {1} \<times> S^1 \<subseteq> N.\<close>
          obtain W_I where hWI_nbhd: "neighborhood_of (1::real) I_set I_top W_I"
              and hWI_tube: "W_I \<times> top1_S1 \<subseteq> N"
            using Lemma_26_8[OF hS1_top1_compact hITop hS1Top hN_open h1I hslice] by (by100 blast)
          \<comment> \<open>W_I is a neighborhood of 1 in I_top, so \<exists>\<epsilon>>0 with (1-\<epsilon>,1] \<subseteq> W_I.\<close>
          obtain \<epsilon> where h\<epsilon>: "\<epsilon> > 0" and h\<epsilon>_W: "\<forall>t\<in>I_set. 1 - \<epsilon> < t \<longrightarrow> t \<in> W_I"
          proof -
            have "W_I \<in> I_top" and "1 \<in> W_I"
              using hWI_nbhd unfolding neighborhood_of_def by auto
            obtain U where hUo: "open U" and hWI_eq: "W_I = I_set \<inter> U"
              using \<open>W_I \<in> I_top\<close> unfolding top1_unit_interval_topology_def subspace_topology_def
                    top1_open_sets_def by auto
            have "1 \<in> U" using \<open>1 \<in> W_I\<close> hWI_eq by simp
            obtain e where "e > 0" "\<forall>y. dist y 1 < e \<longrightarrow> y \<in> U"
              using hUo \<open>1 \<in> U\<close> unfolding open_dist by (by100 blast)
            show ?thesis
            proof (rule that[of e])
              show "e > 0" by (rule \<open>e > 0\<close>)
              show "\<forall>t\<in>I_set. 1 - e < t \<longrightarrow> t \<in> W_I"
              proof (intro ballI impI)
                fix t assume "t \<in> I_set" "1 - e < t"
                have "t \<le> 1" using \<open>t \<in> I_set\<close> unfolding top1_unit_interval_def by simp
                hence "dist t 1 < e" using \<open>1 - e < t\<close> unfolding dist_real_def by simp
                hence "t \<in> U" using \<open>\<forall>y. dist y 1 < e \<longrightarrow> y \<in> U\<close> by simp
                thus "t \<in> W_I" using \<open>t \<in> I_set\<close> hWI_eq by simp
              qed
            qed
          qed
          \<comment> \<open>Step 5: For |y| < \<epsilon>, y \<in> B^2: k(y) \<in> V.\<close>
          \<comment> \<open>If y = 0: k(0) = c \<in> V. If y \<noteq> 0: 1-|y| > 1-\<epsilon>, y/|y| \<in> S^1,
             so (1-|y|, y/|y|) \<in> W_I \<times> S^1 \<subseteq> N, i.e., H(y/|y|, 1-|y|) \<in> V, i.e., k(y) \<in> V.\<close>
          define \<epsilon>' where "\<epsilon>' = min \<epsilon> 1"
          have h\<epsilon>': "\<epsilon>' > 0" using h\<epsilon> unfolding \<epsilon>'_def by simp
          have hball: "\<forall>y\<in>top1_B2. sqrt (fst y ^ 2 + snd y ^ 2) < \<epsilon>' \<longrightarrow> k y \<in> V"
          proof (intro ballI impI)
            fix y assume hy: "y \<in> top1_B2" and hnorm: "sqrt (fst y ^ 2 + snd y ^ 2) < \<epsilon>'"
            show "k y \<in> V"
            proof (cases "y = (0, 0)")
              case True
              \<comment> \<open>y = (0,0), so k y = c. Need c \<in> V. From y0 = (0,0) and k y0 \<in> V.\<close>
              have "c \<in> V" using hky0 \<open>y0 = (0,0)\<close> unfolding k_def by simp
              thus ?thesis unfolding k_def using True by simp
            next
              case False
              let ?r = "sqrt (fst y ^ 2 + snd y ^ 2)"
              have hr_pos: "?r > 0"
              proof -
                obtain a b where hab: "y = (a, b)" by (cases y)
                have "a \<noteq> 0 \<or> b \<noteq> 0" using False hab by auto
                hence "a ^ 2 + b ^ 2 > 0"
                  by (metis zero_less_power2 add_pos_nonneg add_nonneg_pos zero_le_power2)
                thus ?thesis using hab by simp
              qed
              have hr_le1: "?r \<le> 1" using hy unfolding top1_B2_def by (simp add: real_le_rsqrt)
              have h1mr_I: "1 - ?r \<in> I_set" unfolding top1_unit_interval_def using hr_pos hr_le1 by simp
              have h1mr_W: "1 - ?r \<in> W_I"
                using h\<epsilon>_W[rule_format, OF h1mr_I] hnorm unfolding \<epsilon>'_def by simp
              have hunit: "(fst y / ?r, snd y / ?r) \<in> top1_S1"
                using hr_pos unfolding top1_S1_def
                by (auto simp: power_divide add_divide_distrib[symmetric] real_sqrt_gt_zero)
              have "(1 - ?r, (fst y / ?r, snd y / ?r)) \<in> W_I \<times> top1_S1"
                using h1mr_W hunit by simp
              hence "(1 - ?r, (fst y / ?r, snd y / ?r)) \<in> N" using hWI_tube by (by100 blast)
              hence "H ((fst y / ?r, snd y / ?r), 1 - ?r) \<in> V"
                unfolding hN_eq by simp
              thus "k y \<in> V" unfolding k_def using False by simp
            qed
          qed
          \<comment> \<open>ball(0, \<epsilon>') is open in R^2 and intersects B^2 correctly.\<close>
          have "open {y::real\<times>real. sqrt (fst y ^ 2 + snd y ^ 2) < \<epsilon>'}"
          proof -
            have hcont: "continuous_on UNIV (\<lambda>y::real\<times>real. sqrt (fst y ^ 2 + snd y ^ 2))"
              by (intro continuous_intros)
            have "{y::real\<times>real. sqrt (fst y ^ 2 + snd y ^ 2) < \<epsilon>'} =
                (\<lambda>y. sqrt (fst y ^ 2 + snd y ^ 2)) -` {..<\<epsilon>'}"
              by auto
            moreover have "open ((\<lambda>y::real\<times>real. sqrt (fst y ^ 2 + snd y ^ 2)) -` {..<\<epsilon>'})"
              using open_vimage[OF open_lessThan hcont] by simp
            ultimately show ?thesis by simp
          qed
          moreover have "(0::real,0::real) \<in> {y. sqrt (fst y ^ 2 + snd y ^ 2) < \<epsilon>'}"
            using h\<epsilon>' by simp
          moreover have "\<forall>y\<in>top1_B2. y \<in> {y. sqrt (fst y ^ 2 + snd y ^ 2) < \<epsilon>'} \<longrightarrow> k y \<in> V"
            using hball by simp
          ultimately show ?thesis using True by (by100 blast)
        next
          case False
          \<comment> \<open>Case y0 \<noteq> 0: k = H \<circ> g where g(y) = (y/|y|, 1-|y|).
             g is continuous at y0 (composition of continuous on R^2-{0}).
             H is continuous. So k is continuous at y0.
             Since k(y0) \<in> V (open), there's \<epsilon>>0 with ball(y0,\<epsilon>) \<inter> B^2 \<subseteq> k^{-1}(V).\<close>
          \<comment> \<open>Step 1: H\<inverse>(V) = (S^1\<times>I) \<inter> W0 for open W0 in R^2\<times>R.\<close>
          have hHV_sub: "{p \<in> top1_S1 \<times> I_set. H p \<in> V}
              \<in> subspace_topology (UNIV :: ((real\<times>real)\<times>real) set)
                    (product_topology_on (product_topology_on top1_open_sets top1_open_sets) top1_open_sets)
                    (top1_S1 \<times> I_set)"
          proof -
            have "product_topology_on top1_S1_topology I_top =
                subspace_topology (UNIV :: ((real\<times>real)\<times>real) set)
                  (product_topology_on (product_topology_on top1_open_sets top1_open_sets) top1_open_sets)
                  (top1_S1 \<times> I_set)"
            proof -
              have hTR_: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
                by (rule top1_open_sets_is_topology_on_UNIV)
              have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
                using product_topology_on_is_topology_on[OF hTR_ hTR_] by simp
              have "product_topology_on top1_S1_topology I_top =
                  product_topology_on
                    (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_S1)
                    (subspace_topology UNIV top1_open_sets I_set)"
                unfolding top1_S1_topology_def top1_unit_interval_topology_def by simp
              also have "\<dots> = subspace_topology (UNIV \<times> UNIV)
                  (product_topology_on (product_topology_on top1_open_sets top1_open_sets) top1_open_sets)
                  (top1_S1 \<times> I_set)"
                by (rule Theorem_16_3[OF hTR2 hTR_])
              finally show ?thesis by simp
            qed
            thus ?thesis using hHV by simp
          qed
          then obtain W0 :: "((real\<times>real)\<times>real) set" where
              hW0_prod: "W0 \<in> product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets) top1_open_sets"
              and hHV_eq: "{p \<in> top1_S1 \<times> I_set. H p \<in> V} = (top1_S1 \<times> I_set) \<inter> W0"
            unfolding subspace_topology_def by (by100 blast)
          have hW0_open: "open W0"
          proof -
            have "product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
                (top1_open_sets::real set set) = (top1_open_sets :: ((real\<times>real)\<times>real) set set)"
              using product_topology_on_open_sets[where ?'a = "real \<times> real" and ?'b = real]
                    product_topology_on_open_sets[where ?'a = real and ?'b = real] by metis
            thus ?thesis using hW0_prod unfolding top1_open_sets_def by (by100 blast)
          qed
          \<comment> \<open>Step 2: g(y) = ((fst y/r, snd y/r), 1-r) where r = sqrt(...).
             g continuous on R^2-{0}. g\<inverse>(W0) open in R^2-{0}.\<close>
          define g where "g = (\<lambda>y::real\<times>real.
              ((fst y / sqrt (fst y ^ 2 + snd y ^ 2),
                snd y / sqrt (fst y ^ 2 + snd y ^ 2)),
               1 - sqrt (fst y ^ 2 + snd y ^ 2)))"
          have hg_cont: "continuous_on (UNIV - {(0::real, 0::real)}) g"
            unfolding g_def by (intro continuous_intros) auto
          have hg_y0_W0: "g y0 \<in> W0"
          proof -
            have "g y0 \<in> top1_S1 \<times> I_set"
            proof -
              have hr_pos: "sqrt (fst y0 ^ 2 + snd y0 ^ 2) > 0"
              proof -
                obtain a b where hab: "y0 = (a, b)" by (cases y0)
                have "a \<noteq> 0 \<or> b \<noteq> 0" using False hab by auto
                hence "a ^ 2 + b ^ 2 > 0"
                  by (metis zero_less_power2 add_pos_nonneg add_nonneg_pos zero_le_power2)
                thus ?thesis using hab by simp
              qed
              have hr_le1: "sqrt (fst y0 ^ 2 + snd y0 ^ 2) \<le> 1"
                using hy0 unfolding top1_B2_def by (simp add: real_le_rsqrt)
              have "(fst y0 / sqrt (fst y0 ^ 2 + snd y0 ^ 2),
                     snd y0 / sqrt (fst y0 ^ 2 + snd y0 ^ 2)) \<in> top1_S1"
                using hr_pos unfolding top1_S1_def
                by (auto simp: power_divide add_divide_distrib[symmetric] real_sqrt_gt_zero)
              moreover have "1 - sqrt (fst y0 ^ 2 + snd y0 ^ 2) \<in> I_set"
                unfolding top1_unit_interval_def using hr_pos hr_le1 by simp
              ultimately show ?thesis unfolding g_def by simp
            qed
            moreover have "H (g y0) \<in> V"
            proof -
              have "k y0 = H ((fst y0 / sqrt (fst y0 ^ 2 + snd y0 ^ 2),
                              snd y0 / sqrt (fst y0 ^ 2 + snd y0 ^ 2)),
                             1 - sqrt (fst y0 ^ 2 + snd y0 ^ 2))"
                unfolding k_def using False by simp
              also have "\<dots> = H (g y0)" unfolding g_def by simp
              finally show ?thesis using hky0 by simp
            qed
            ultimately have "g y0 \<in> {p \<in> top1_S1 \<times> I_set. H p \<in> V}" by simp
            hence "g y0 \<in> (top1_S1 \<times> I_set) \<inter> W0" using hHV_eq by simp
            thus ?thesis by (by100 blast)
          qed
          \<comment> \<open>Step 3: g\<inverse>(W0) is open (g continuous, W0 open) and contains y0.\<close>
          have "open (g -` W0 \<inter> (UNIV - {(0, 0)}))"
            using continuous_on_open_vimage[OF open_Diff[OF open_UNIV closed_insert[OF closed_empty]]]
                  hg_cont hW0_open by blast
          moreover have "y0 \<in> g -` W0 \<inter> (UNIV - {(0, 0)})"
            using hg_y0_W0 False by simp
          moreover have "\<forall>y\<in>top1_B2. y \<in> g -` W0 \<inter> (UNIV - {(0, 0)}) \<longrightarrow> k y \<in> V"
          proof (intro ballI impI)
            fix y assume "y \<in> top1_B2" "y \<in> g -` W0 \<inter> (UNIV - {(0, 0)})"
            hence "y \<noteq> (0, 0)" and "g y \<in> W0" by auto
            have "g y \<in> top1_S1 \<times> I_set"
            proof -
              have hr_pos: "sqrt (fst y ^ 2 + snd y ^ 2) > 0"
              proof -
                obtain a b where hab: "y = (a, b)" by (cases y)
                have "a \<noteq> 0 \<or> b \<noteq> 0" using \<open>y \<noteq> (0, 0)\<close> hab by auto
                hence "a ^ 2 + b ^ 2 > 0"
                  by (metis zero_less_power2 add_pos_nonneg add_nonneg_pos zero_le_power2)
                thus ?thesis using hab by simp
              qed
              have hr_le1: "sqrt (fst y ^ 2 + snd y ^ 2) \<le> 1"
                using \<open>y \<in> top1_B2\<close> unfolding top1_B2_def by (simp add: real_le_rsqrt)
              have "(fst y / sqrt (fst y ^ 2 + snd y ^ 2),
                     snd y / sqrt (fst y ^ 2 + snd y ^ 2)) \<in> top1_S1"
                using hr_pos unfolding top1_S1_def
                by (auto simp: power_divide add_divide_distrib[symmetric] real_sqrt_gt_zero)
              moreover have "1 - sqrt (fst y ^ 2 + snd y ^ 2) \<in> I_set"
                unfolding top1_unit_interval_def using hr_pos hr_le1 by simp
              ultimately show ?thesis unfolding g_def by simp
            qed
            hence "g y \<in> {p \<in> top1_S1 \<times> I_set. H p \<in> V}"
            proof -
              have "g y \<in> (top1_S1 \<times> I_set) \<inter> W0" using \<open>g y \<in> top1_S1 \<times> I_set\<close> \<open>g y \<in> W0\<close> by simp
              thus ?thesis using hHV_eq by simp
            qed
            hence "H (g y) \<in> V" by simp
            thus "k y \<in> V" unfolding k_def g_def using \<open>y \<noteq> (0, 0)\<close> by simp
          qed
          ultimately show ?thesis by (by100 blast)
        qed
      qed
      \<comment> \<open>Union of these neighborhoods gives the open set.\<close>
      define W where "W = \<Union>{Wy. \<exists>y0\<in>top1_B2. k y0 \<in> V \<and> open Wy \<and> y0 \<in> Wy
          \<and> (\<forall>y\<in>top1_B2. y \<in> Wy \<longrightarrow> k y \<in> V)}"
      have hWo: "open W" unfolding W_def by auto
      have heq: "{y \<in> top1_B2. k y \<in> V} = top1_B2 \<inter> W"
      proof (rule set_eqI)
        fix y show "(y \<in> {y \<in> top1_B2. k y \<in> V}) = (y \<in> top1_B2 \<inter> W)"
        proof
          assume "y \<in> {y \<in> top1_B2. k y \<in> V}"
          hence hy: "y \<in> top1_B2" and hky: "k y \<in> V" by auto
          from hpointwise[rule_format, OF hy hky]
          obtain Wy where "open Wy" "y \<in> Wy" "\<forall>z\<in>top1_B2. z \<in> Wy \<longrightarrow> k z \<in> V" by blast
          hence "y \<in> W" unfolding W_def using hy hky by (by100 blast)
          thus "y \<in> top1_B2 \<inter> W" using hy by (by100 blast)
        next
          assume "y \<in> top1_B2 \<inter> W"
          hence hy: "y \<in> top1_B2" and "y \<in> W" by auto
          from \<open>y \<in> W\<close> obtain Wy where "y \<in> Wy" "\<forall>z\<in>top1_B2. z \<in> Wy \<longrightarrow> k z \<in> V"
            unfolding W_def by (by100 blast)
          thus "y \<in> {y \<in> top1_B2. k y \<in> V}" using hy by (by100 blast)
        qed
      qed
      have "W \<in> (top1_open_sets :: (real \<times> real) set set)"
        using hWo unfolding top1_open_sets_def by (by100 blast)
      hence "W \<in> product_topology_on (top1_open_sets :: real set set) top1_open_sets"
        using product_topology_on_open_sets_real2 by (by100 metis)
      thus "{y \<in> top1_B2. k y \<in> V} \<in> top1_B2_topology"
        unfolding heq top1_B2_topology_def subspace_topology_def by (by100 blast)
    qed
  qed
  show "\<exists>k. top1_continuous_map_on top1_B2 top1_B2_topology X TX k \<and> (\<forall>x\<in>top1_S1. k x = h x)"
    using hk_cont hext by (by100 blast)
next
  \<comment> \<open>Backward: extension to B^2 \<Rightarrow> nulhomotopic (Lemma_55_3_backward).\<close>
  assume "\<exists>k. top1_continuous_map_on top1_B2 top1_B2_topology X TX k \<and> (\<forall>x\<in>top1_S1. k x = h x)"
  then obtain k where hk: "top1_continuous_map_on top1_B2 top1_B2_topology X TX k"
      and hext: "\<forall>x\<in>top1_S1. k x = h x" by blast
  show "top1_nulhomotopic_on top1_S1 top1_S1_topology X TX h"
    by (rule Lemma_55_3_backward[OF hh hTX hk hext])
qed

(** from \<S>55 Corollary 55.4: inclusion S^1 \<rightarrow> R^2 - {0} is not nulhomotopic.
    Follows from Theorem 55.2 via retraction R^2 - {0} \<rightarrow> S^1 by x/|x|. **)
corollary Corollary_55_4_inclusion_not_nulhomotopic:
  shows "\<not> top1_nulhomotopic_on top1_S1 top1_S1_topology
           (UNIV - {(0, 0)})
           (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))
           (\<lambda>x. x)"
proof
  assume hnul: "top1_nulhomotopic_on top1_S1 top1_S1_topology
      (UNIV - {(0, 0)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))
      (\<lambda>x. x)"
  \<comment> \<open>Munkres 55.4: The retraction r(x) = x/|x| makes j_* injective (Lemma 55.1).
     Since \<pi>_1(S^1) is nontrivial, j_* is nontrivial, so j is not nulhomotopic.\<close>
  \<comment> \<open>Step 1: r(x) = x/|x| is a retraction R^2-0 \<rightarrow> S^1.\<close>
  have hret: "top1_retract_of_on (UNIV - {(0::real, 0::real)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))
      top1_S1"
  proof -
    let ?R2_0 = "UNIV - {(0::real, 0::real)}"
    let ?TR = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?R2_0"
    let ?norm = "\<lambda>x::real\<times>real. sqrt (fst x ^ 2 + snd x ^ 2)"
    let ?r = "\<lambda>x::real\<times>real. (fst x / ?norm x, snd x / ?norm x)"
    have hS1sub: "top1_S1 \<subseteq> ?R2_0" unfolding top1_S1_def by (by100 auto)
    have hr_map: "\<forall>x\<in>?R2_0. ?r x \<in> top1_S1"
    proof (intro ballI)
      fix x :: "real \<times> real" assume hx: "x \<in> ?R2_0"
      hence hne: "x \<noteq> (0, 0)" by (by100 blast)
      hence hpos: "fst x ^ 2 + snd x ^ 2 > 0"
        by (cases x) (auto simp: sum_power2_gt_zero_iff)
      hence hnorm_pos: "?norm x > 0" by (simp add: real_sqrt_gt_zero)
      have "fst (?r x) ^ 2 + snd (?r x) ^ 2 = 1"
      proof -
        let ?d = "fst x ^ 2 + snd x ^ 2"
        have "fst x ^ 2 / ?d + snd x ^ 2 / ?d = ?d / ?d"
          by (metis add_divide_distrib)
        also have "?d / ?d = 1" using hpos by auto
        finally have hadd: "fst x ^ 2 / ?d + snd x ^ 2 / ?d = 1" .
        have h1: "fst (?r x) = fst x / ?norm x" by simp
        have h2: "snd (?r x) = snd x / ?norm x" by simp
        have hnorm_sq: "(?norm x) ^ 2 = ?d"
          using hpos by (simp add: real_sqrt_pow2)
        show ?thesis unfolding h1 h2 power_divide hnorm_sq using hadd by simp
      qed
      thus "?r x \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    qed
    have hr_fix: "\<forall>x\<in>top1_S1. ?r x = x"
    proof (intro ballI)
      fix x :: "real \<times> real" assume hx: "x \<in> top1_S1"
      have heq: "fst x ^ 2 + snd x ^ 2 = 1" using hx unfolding top1_S1_def by (by100 simp)
      hence hnorm: "?norm x = 1" by (simp add: real_sqrt_eq_1_iff)
      show "?r x = x" using hnorm by (simp add: prod_eq_iff)
    qed
    have hr_cont: "top1_continuous_map_on ?R2_0 ?TR top1_S1
        (subspace_topology ?R2_0 ?TR top1_S1) ?r"
    proof -
      \<comment> \<open>Step 1: r is continuous_on R²-{0} using standard library.\<close>
      have hr_std: "continuous_on ?R2_0 ?r"
      proof (rule continuous_on_Pair)
        have hnorm_cont: "continuous_on ?R2_0 ?norm"
          by (intro continuous_on_compose2[OF continuous_on_real_sqrt]
              continuous_on_add continuous_on_power
              continuous_on_fst continuous_on_snd) auto
        have hnorm_nz: "\<forall>x\<in>?R2_0. ?norm x \<noteq> 0"
        proof (intro ballI)
          fix x :: "real \<times> real" assume "x \<in> ?R2_0"
          hence "x \<noteq> (0, 0)" by (by100 blast)
          hence "fst x ^ 2 + snd x ^ 2 > 0"
            by (cases x) (auto simp: sum_power2_gt_zero_iff)
          hence "?norm x > 0" by (rule real_sqrt_gt_zero)
          thus "?norm x \<noteq> 0" by (by100 linarith)
        qed
        have hfst_cont: "continuous_on ?R2_0 fst"
          by (intro continuous_intros)
        have hsnd_cont: "continuous_on ?R2_0 snd"
          by (intro continuous_intros)
        show "continuous_on ?R2_0 (\<lambda>x. fst x / ?norm x)"
          by (rule continuous_on_divide[OF hfst_cont hnorm_cont hnorm_nz])
        show "continuous_on ?R2_0 (\<lambda>x. snd x / ?norm x)"
          by (rule continuous_on_divide[OF hsnd_cont hnorm_cont hnorm_nz])
      qed
      \<comment> \<open>Step 2: Transfer to top1_continuous_map_on via general subspace lemma.\<close>
      have hr_R2: "top1_continuous_map_on ?R2_0
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?R2_0)
          top1_S1
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_S1) ?r"
        by (rule top1_continuous_map_on_real2_subspace_general[OF _ hr_std])
           (use hr_map in blast)
      \<comment> \<open>Step 3: Codomain topology: subspace of R²-{0} restricted to S¹ = subspace of R² restricted to S¹.\<close>
      have hTR_eq: "subspace_topology ?R2_0 ?TR top1_S1 =
          subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_S1"
        using subspace_topology_trans[OF hS1sub] by simp
      show ?thesis using hr_R2 unfolding hTR_eq[symmetric] .
    qed
    show ?thesis unfolding top1_retract_of_on_def top1_is_retraction_on_def
      using hS1sub hr_cont hr_fix by (by100 blast)
  qed
  \<comment> \<open>Step 2: j_* is injective (Lemma 55.1) hence nontrivial.\<close>
  \<comment> \<open>Step 3: nulhomotopic \<Rightarrow> j_* trivial (Lemma 55.3 (3)\<Rightarrow>(1)), contradicting nontrivial.\<close>
  \<comment> \<open>By retraction + Theorem 55.2 (no retract of B² to S¹) argument:
     j nulhomotopic ⟹ j extends to k: B² → R²-{0} with k|S¹ = j.
     Composing r∘k: B² → S¹ gives a retraction, contradicting Theorem 55.2.\<close>
  show False
  proof -
    let ?TR = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)})"
    have hTR2_full: "is_topology_on (UNIV::(real\<times>real) set)
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
      using product_topology_on_is_topology_on[OF
            top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV] by simp
    have hTR: "is_topology_on (UNIV - {(0::real, 0)}) ?TR"
      by (simp add: product_topology_on_open_sets
        subspace_topology_is_topology_on top1_open_sets_is_topology_on_UNIV)
    have hid_cont: "top1_continuous_map_on top1_S1 top1_S1_topology (UNIV - {(0, 0)}) ?TR (\<lambda>x. x)"
    proof -
      have hS1_sub: "top1_S1 \<subseteq> UNIV - {(0::real, 0)}" unfolding top1_S1_def by (by100 auto)
      have hid_full: "top1_continuous_map_on (UNIV - {(0::real, 0)}) ?TR (UNIV - {(0, 0)}) ?TR id"
        by (rule top1_continuous_map_on_id[OF hTR])
      have hid_restr: "top1_continuous_map_on top1_S1
          (subspace_topology (UNIV - {(0, 0)}) ?TR top1_S1) (UNIV - {(0, 0)}) ?TR id"
        by (rule top1_continuous_map_on_restrict_domain_simple[OF hid_full hS1_sub])
      have hS1_eq: "subspace_topology (UNIV - {(0, 0)}) ?TR top1_S1 = top1_S1_topology"
        unfolding top1_S1_topology_def
        using subspace_topology_trans[OF hS1_sub] by simp
      have hid_eq: "(\<lambda>x::real\<times>real. x) = id" by (rule ext) simp
      show ?thesis using hid_restr unfolding hS1_eq hid_eq[symmetric] by simp
    qed
    \<comment> \<open>nulhomotopic ⟹ extends to B².\<close>
    obtain k where hk: "top1_continuous_map_on top1_B2 top1_B2_topology (UNIV - {(0, 0)}) ?TR k"
        and hkS1: "\<forall>x\<in>top1_S1. k x = x"
      using iffD1[OF Lemma_55_3_nulhomotopic_characterization[OF hid_cont hTR] hnul] by (by100 blast)
    \<comment> \<open>r∘k: B² → S¹ is a retraction (r∘k|S¹ = r|S¹ = id), contradicting no-retraction.\<close>
    have "top1_retract_of_on top1_B2 top1_B2_topology top1_S1"
    proof -
      \<comment> \<open>From hret, get retraction r': R²-{0} → S¹.\<close>
      obtain r' where hr'_sub: "top1_S1 \<subseteq> UNIV - {(0::real, 0)}"
          and hr'_cont: "top1_continuous_map_on (UNIV - {(0, 0)}) ?TR top1_S1
              (subspace_topology (UNIV - {(0, 0)}) ?TR top1_S1) r'"
          and hr'_fix: "\<forall>a\<in>top1_S1. r' a = a"
        using hret unfolding top1_retract_of_on_def top1_is_retraction_on_def by (by100 blast)
      \<comment> \<open>r'∘k: B² → S¹ continuous (composition).\<close>
      have hrk_comp: "top1_continuous_map_on top1_B2 top1_B2_topology top1_S1
          (subspace_topology (UNIV - {(0, 0)}) ?TR top1_S1) (r' \<circ> k)"
        by (rule top1_continuous_map_on_comp[OF hk hr'_cont])
      \<comment> \<open>Subspace topology equalities.\<close>
      have hTS1_eq: "subspace_topology (UNIV - {(0, 0)}) ?TR top1_S1 = top1_S1_topology"
        unfolding top1_S1_topology_def using subspace_topology_trans[OF hr'_sub] by simp
      have hS1_B2: "top1_S1 \<subseteq> top1_B2" unfolding top1_S1_def top1_B2_def by (by100 auto)
      have hTS1_B2: "top1_S1_topology = subspace_topology top1_B2 top1_B2_topology top1_S1"
        unfolding top1_S1_topology_def top1_B2_topology_def
        using subspace_topology_trans[OF hS1_B2] by simp
      have hrk_cont: "top1_continuous_map_on top1_B2 top1_B2_topology top1_S1
          (subspace_topology top1_B2 top1_B2_topology top1_S1) (r' \<circ> k)"
        using hrk_comp unfolding hTS1_eq hTS1_B2 .
      \<comment> \<open>r'∘k fixes S¹: k(x) = x and r'(x) = x for x \<in> S¹.\<close>
      have hrk_fix: "\<forall>a\<in>top1_S1. (r' \<circ> k) a = a"
      proof (intro ballI)
        fix a assume ha: "a \<in> top1_S1"
        show "(r' \<circ> k) a = a" using hkS1 hr'_fix ha by (simp add: comp_def)
      qed
      show ?thesis unfolding top1_retract_of_on_def top1_is_retraction_on_def
        using hS1_B2 hrk_cont hrk_fix by (by100 blast)
    qed
    thus False using Theorem_55_2_no_retraction by (by100 metis)
  qed
qed

text \<open>Helper: if f is nulhomotopic and f \<simeq> g, then g is nulhomotopic.
  Proof: f \<simeq> const and g \<simeq> f (symmetry), compose homotopies (concatenation).\<close>
lemma nulhomotopic_homotopic_trans:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hnul: "top1_nulhomotopic_on X TX Y TY f"
      and hhom: "top1_homotopic_on X TX Y TY f g"
  shows "top1_nulhomotopic_on X TX Y TY g"
proof -
  obtain c where hcY: "c \<in> Y" and hfc: "top1_homotopic_on X TX Y TY f (\<lambda>_. c)"
    using hnul unfolding top1_nulhomotopic_on_def by (by100 blast)
  obtain F1 where hF1: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F1"
      and hF1_0: "\<forall>x\<in>X. F1 (x, 0) = f x" and hF1_1: "\<forall>x\<in>X. F1 (x, 1) = c"
    using hfc unfolding top1_homotopic_on_def by (by100 blast)
  \<comment> \<open>Symmetry: from f \<simeq> g, get homotopy G(x,t) = F(x,1-t) from g to f.\<close>
  obtain F2 where hF2: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F2"
      and hF2_0: "\<forall>x\<in>X. F2 (x, 0) = g x" and hF2_1: "\<forall>x\<in>X. F2 (x, 1) = f x"
  proof -
    obtain F0 where hF0: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F0"
        and hF0_0: "\<forall>x\<in>X. F0 (x, 0) = f x" and hF0_1: "\<forall>x\<in>X. F0 (x, 1) = g x"
      using hhom unfolding top1_homotopic_on_def by (by100 blast)
    let ?F2 = "\<lambda>(x, t). F0 (x, 1 - t)"
    have hF2_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY ?F2"
    proof -
      have "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
        (\<lambda>p. F0 (fst p, 1 - snd p))"
        by (rule homotopy_reverse_continuous[OF hF0 hTX])
      moreover have "(\<lambda>p. F0 (fst p, 1 - snd p)) = ?F2"
        by (rule ext) (simp add: case_prod_beta)
      ultimately show ?thesis by simp
    qed
    have "\<forall>x\<in>X. ?F2 (x, 0) = g x" using hF0_1 by (by100 simp)
    moreover have "\<forall>x\<in>X. ?F2 (x, 1) = f x" using hF0_0 by (by100 simp)
    ultimately show ?thesis using hF2_cont that by (by100 blast)
  qed
  \<comment> \<open>Concatenate F2 and F1: G(x,t) = F2(x,2t) for t\<le>1/2, F1(x,2t-1) for t>1/2.\<close>
  have hmatch: "\<forall>x\<in>X. F2 (x, 1) = F1 (x, 0)"
    using hF2_1 hF1_0 by (by100 simp)
  let ?G = "\<lambda>p. if snd p \<le> 1/2 then F2 (fst p, 2 * snd p) else F1 (fst p, 2 * snd p - 1)"
  have hG_cont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY ?G"
    by (rule homotopy_concat_continuous[OF hTX hTY hF2 hF1 hmatch])
  have hG_0: "\<forall>x\<in>X. ?G (x, 0) = g x"
    using hF2_0 by (by100 simp)
  have hG_1: "\<forall>x\<in>X. ?G (x, 1) = c"
    using hF1_1 by (by100 simp)
  have hg_cont: "top1_continuous_map_on X TX Y TY g"
    using hhom unfolding top1_homotopic_on_def by (by100 blast)
  have hconst: "top1_continuous_map_on X TX Y TY (\<lambda>_. c)"
    by (rule top1_continuous_map_on_const[OF hTX hTY hcY])
  show ?thesis
    unfolding top1_nulhomotopic_on_def top1_homotopic_on_def
    using hcY hg_cont hconst hG_cont hG_0 hG_1 by (by100 blast)
qed

text \<open>Continuity transfer: continuous_on UNIV for R³ → R² gives
  top1_continuous_map_on on S¹×I → R²-{0} when the image avoids (0,0).\<close>
lemma S1_I_to_R2_minus_0_continuous:
  fixes f :: "(real \<times> real) \<times> real \<Rightarrow> real \<times> real"
  assumes hcont: "continuous_on UNIV f"
      and hmap: "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> f p \<in> UNIV - {(0::real, 0)}"
  shows "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
      (UNIV - {(0, 0)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)})) f"
proof -
  have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
      (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTR hTR] by simp
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on[OF hTR2]) simp
  have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
  \<comment> \<open>Step 1: f maps S¹×I into R² continuously (via product topology transfer).\<close>
  have hf_R2: "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
      (UNIV::(real\<times>real) set) (product_topology_on (top1_open_sets::real set set) top1_open_sets) f"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix p show "f p \<in> (UNIV::(real\<times>real) set)" by simp
  next
    fix V assume hV: "V \<in> product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set)"
    \<comment> \<open>V is open in R².\<close>
    have hVo: "open V"
    proof -
      have "V \<in> (top1_open_sets :: (real \<times> real) set set)"
        using hV product_topology_on_open_sets_real2 by metis
      thus ?thesis unfolding top1_open_sets_def by simp
    qed
    have hfV_open: "open (f -` V)" by (rule open_vimage[OF hVo hcont])
    \<comment> \<open>f⁻¹(V) is open in R³ = (R²)×R.\<close>
    have hfV_R3: "f -` V \<in> product_topology_on
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)
        (top1_open_sets::real set set)"
    proof -
      have "f -` V \<in> (top1_open_sets :: ((real\<times>real)\<times>real) set set)"
        using hfV_open unfolding top1_open_sets_def by (by100 blast)
      thus ?thesis
        using product_topology_on_open_sets[where ?'a = "real \<times> real" and ?'b = real]
              product_topology_on_open_sets_real2 by (by100 metis)
    qed
    \<comment> \<open>(S¹×I) ∩ f⁻¹(V) is open in the product subspace topology.\<close>
    have "{p \<in> top1_S1 \<times> I_set. f p \<in> V} = (top1_S1 \<times> I_set) \<inter> (f -` V)" by auto
    also have "\<dots> \<in> product_topology_on top1_S1_topology I_top"
    proof -
      have hTP_eq: "product_topology_on top1_S1_topology I_top =
          subspace_topology (UNIV \<times> UNIV)
            (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
              (top1_open_sets::real set set))
            (top1_S1 \<times> I_set)"
      proof -
        have "product_topology_on top1_S1_topology I_top =
              product_topology_on
                (subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) top1_S1)
                (subspace_topology UNIV (top1_open_sets::real set set) I_set)"
          unfolding top1_S1_topology_def top1_unit_interval_topology_def ..
        also have "\<dots> = subspace_topology (UNIV \<times> UNIV)
            (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
              (top1_open_sets::real set set))
            (top1_S1 \<times> I_set)"
          by (rule Theorem_16_3[OF hTR2 hTR])
        finally show ?thesis .
      qed
      show ?thesis unfolding hTP_eq subspace_topology_def
        using hfV_R3 by (by100 blast)
    qed
    finally show "{p \<in> top1_S1 \<times> I_set. f p \<in> V} \<in> product_topology_on top1_S1_topology I_top" .
  qed
  \<comment> \<open>Step 2: Codomain shrink to R²-{0}.\<close>
  have himg: "f ` (top1_S1 \<times> I_set) \<subseteq> UNIV - {(0, 0)}"
  proof (intro subsetI)
    fix y assume "y \<in> f ` (top1_S1 \<times> I_set)"
    then obtain p where hp: "p \<in> top1_S1 \<times> I_set" and hy: "y = f p" by (by100 blast)
    show "y \<in> UNIV - {(0, 0)}" using hmap[OF hp] hy by (by100 simp)
  qed
  show ?thesis
    by (rule top1_continuous_map_on_codomain_shrink[OF hf_R2 himg]) simp
qed

text \<open>Reverse transfer: top1_continuous_map_on on R² subspaces implies continuous_on.\<close>
lemma top1_continuous_map_on_to_continuous_on_R2:
  fixes f :: "real \<times> real \<Rightarrow> real \<times> real"
  assumes hf: "top1_continuous_map_on S
      (subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) S)
      UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) f"
  shows "continuous_on S f"
proof -
  {
    fix U :: "(real \<times> real) set"
    assume hUo: "open U"
    have hU_os: "U \<in> (top1_open_sets :: (real\<times>real) set set)"
      using hUo unfolding top1_open_sets_def by (by100 blast)
    have hU_prod: "U \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
      using hU_os product_topology_on_open_sets_real2 by (by100 metis)
    have hpre: "{x \<in> S. f x \<in> U} \<in> subspace_topology UNIV
        (product_topology_on (top1_open_sets::real set set) top1_open_sets) S"
      using hf hU_prod unfolding top1_continuous_map_on_def by (by100 blast)
    then obtain W where hW_prod: "W \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
        and hpre_eq: "{x \<in> S. f x \<in> U} = S \<inter> W"
      unfolding subspace_topology_def by (by100 auto)
    have hW_os: "W \<in> (top1_open_sets :: (real\<times>real) set set)"
      using hW_prod product_topology_on_open_sets_real2 by (by100 metis)
    have hWo: "open W" using hW_os unfolding top1_open_sets_def by (by100 simp)
    have "\<exists>A. open A \<and> A \<inter> S = f -` U \<inter> S"
    proof (intro exI[of _ W] conjI)
      show "open W" by (rule hWo)
      show "W \<inter> S = f -` U \<inter> S"
      proof (intro set_eqI iffI)
        fix x assume "x \<in> W \<inter> S"
        hence "x \<in> S \<inter> W" by (by100 blast)
        hence "x \<in> {x \<in> S. f x \<in> U}" using hpre_eq by (by100 simp)
        thus "x \<in> f -` U \<inter> S" by (by100 simp)
      next
        fix x assume "x \<in> f -` U \<inter> S"
        hence "x \<in> S" "f x \<in> U" by (by100 simp)+
        hence "x \<in> {x \<in> S. f x \<in> U}" by (by100 simp)
        thus "x \<in> W \<inter> S" using hpre_eq by (by100 simp)
      qed
    qed
  } note hstep = this
  show ?thesis unfolding continuous_on_open_invariant
  proof (intro allI impI)
    fix B :: "(real \<times> real) set" assume "open B"
    thus "\<exists>A. open A \<and> A \<inter> S = f -` B \<inter> S" by (rule hstep)
  qed
qed

text \<open>General variant: continuous_on (S×I) for any S ⊆ R².\<close>
lemma R2_subspace_I_continuous_on_transfer:
  fixes S :: "(real \<times> real) set" and T :: "(real \<times> real) set"
    and f :: "(real \<times> real) \<times> real \<Rightarrow> real \<times> real"
  assumes hcont: "continuous_on (S \<times> I_set) f"
      and hmap: "\<And>p. p \<in> S \<times> I_set \<Longrightarrow> f p \<in> T"
  shows "top1_continuous_map_on (S \<times> I_set)
      (product_topology_on
        (subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) S)
        I_top)
      T (subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) T) f"
proof -
  have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
      (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTR hTR] by simp
  let ?TS = "subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) S"
  have hf_R2: "top1_continuous_map_on (S \<times> I_set) (product_topology_on ?TS I_top)
      (UNIV::(real\<times>real) set) (product_topology_on (top1_open_sets::real set set) top1_open_sets) f"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix p show "f p \<in> (UNIV::(real\<times>real) set)" by simp
  next
    fix V assume hV: "V \<in> product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set)"
    have hV': "V \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets" using hV .
    have hVo: "open V"
      using hV'[unfolded product_topology_on_open_sets_real2] unfolding top1_open_sets_def
      by (by100 simp)
    have hcont': "\<forall>B. open B \<longrightarrow> (\<exists>A. open A \<and> A \<inter> (S \<times> I_set) = f -` B \<inter> (S \<times> I_set))"
      using hcont unfolding continuous_on_open_invariant .
    obtain W where hWo: "open W" and hWeq: "W \<inter> (S \<times> I_set) = f -` V \<inter> (S \<times> I_set)"
      using hcont'[rule_format, OF hVo] by (by100 blast)
    have hW_R3: "W \<in> product_topology_on
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)
        (top1_open_sets::real set set)"
    proof -
      have "W \<in> (top1_open_sets :: ((real\<times>real)\<times>real) set set)"
        using hWo unfolding top1_open_sets_def by (by100 blast)
      thus ?thesis
        using product_topology_on_open_sets[where ?'a = "real \<times> real" and ?'b = real]
              product_topology_on_open_sets_real2 by (by100 metis)
    qed
    have hTP_eq: "product_topology_on ?TS I_top =
        subspace_topology (UNIV \<times> UNIV)
          (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
            (top1_open_sets::real set set))
          (S \<times> I_set)"
    proof -
      have "product_topology_on ?TS I_top =
            product_topology_on
              (subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) S)
              (subspace_topology UNIV (top1_open_sets::real set set) I_set)"
        unfolding top1_unit_interval_topology_def ..
      also have "\<dots> = subspace_topology (UNIV \<times> UNIV)
          (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
            (top1_open_sets::real set set))
          (S \<times> I_set)"
        by (rule Theorem_16_3[OF hTR2 hTR])
      finally show ?thesis .
    qed
    have "{p \<in> S \<times> I_set. f p \<in> V} = (S \<times> I_set) \<inter> W"
    proof (intro set_eqI iffI)
      fix x assume "x \<in> {p \<in> S \<times> I_set. f p \<in> V}"
      hence "x \<in> S \<times> I_set" "f x \<in> V" by (by100 simp)+
      hence "x \<in> f -` V \<inter> (S \<times> I_set)" by (by100 simp)
      thus "x \<in> (S \<times> I_set) \<inter> W" using hWeq by (by100 blast)
    next
      fix x assume "x \<in> (S \<times> I_set) \<inter> W"
      hence "x \<in> W \<inter> (S \<times> I_set)" by (by100 blast)
      hence "x \<in> f -` V \<inter> (S \<times> I_set)" using hWeq by (by100 blast)
      thus "x \<in> {p \<in> S \<times> I_set. f p \<in> V}" by (by100 simp)
    qed
    also have "\<dots> \<in> product_topology_on ?TS I_top"
    proof -
      have "S \<times> I_set \<subseteq> (UNIV::(real\<times>real) set) \<times> (UNIV::real set)" by (by100 simp)
      hence hmem: "(S \<times> I_set) \<inter> W \<in> subspace_topology
          ((UNIV::(real\<times>real) set) \<times> (UNIV::real set))
          (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
            (top1_open_sets::real set set)) (S \<times> I_set)"
        using hW_R3 unfolding subspace_topology_def by (by100 auto)
      show ?thesis using hmem unfolding hTP_eq by simp
    qed
    finally show "{p \<in> S \<times> I_set. f p \<in> V} \<in> product_topology_on ?TS I_top" .
  qed
  have himg: "f ` (S \<times> I_set) \<subseteq> T"
  proof (intro subsetI)
    fix y assume "y \<in> f ` (S \<times> I_set)"
    then obtain p where hp: "p \<in> S \<times> I_set" and hy: "y = f p" by (by100 blast)
    show "y \<in> T" using hmap[OF hp] hy by (by100 simp)
  qed
  show ?thesis
    by (rule top1_continuous_map_on_codomain_shrink[OF hf_R2 himg]) simp
qed

text \<open>Variant with continuous_on on the domain (for functions that are NOT continuous on UNIV).\<close>
lemma S1_I_to_R2_minus_0_continuous_on:
  fixes f :: "(real \<times> real) \<times> real \<Rightarrow> real \<times> real"
  assumes hcont: "continuous_on (top1_S1 \<times> I_set) f"
      and hmap: "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> f p \<in> UNIV - {(0::real, 0)}"
  shows "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
      (UNIV - {(0, 0)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)})) f"
proof -
  have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have hTR2: "is_topology_on (UNIV::(real\<times>real) set)
      (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
    using product_topology_on_is_topology_on[OF hTR hTR] by simp
  \<comment> \<open>Step 1: f maps S¹×I into R² continuously.\<close>
  have hf_R2: "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
      (UNIV::(real\<times>real) set) (product_topology_on (top1_open_sets::real set set) top1_open_sets) f"
    unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix p show "f p \<in> (UNIV::(real\<times>real) set)" by simp
  next
    fix V assume hV: "V \<in> product_topology_on (top1_open_sets::real set set) (top1_open_sets::real set set)"
    have hV': "V \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets" using hV .
    have hVo: "open V"
      using hV'[unfolded product_topology_on_open_sets_real2] unfolding top1_open_sets_def
      by (by100 simp)
    \<comment> \<open>continuous_on gives: \<exists>W open. W \<inter> (S¹×I) = f⁻¹(V) \<inter> (S¹×I).\<close>
    have hcont': "\<forall>B. open B \<longrightarrow> (\<exists>A. open A \<and> A \<inter> (top1_S1 \<times> I_set) = f -` B \<inter> (top1_S1 \<times> I_set))"
      using hcont unfolding continuous_on_open_invariant .
    obtain W where hWo: "open W" and hWeq: "W \<inter> (top1_S1 \<times> I_set) = f -` V \<inter> (top1_S1 \<times> I_set)"
      using hcont'[rule_format, OF hVo] by (by100 blast)
    \<comment> \<open>W open in R³.\<close>
    have hW_R3: "W \<in> product_topology_on
        (product_topology_on (top1_open_sets::real set set) top1_open_sets)
        (top1_open_sets::real set set)"
    proof -
      have "W \<in> (top1_open_sets :: ((real\<times>real)\<times>real) set set)"
        using hWo unfolding top1_open_sets_def by (by100 blast)
      thus ?thesis
        using product_topology_on_open_sets[where ?'a = "real \<times> real" and ?'b = real]
              product_topology_on_open_sets_real2 by (by100 metis)
    qed
    \<comment> \<open>(S¹×I) ∩ W is open in product subspace topology.\<close>
    have hTP_eq: "product_topology_on top1_S1_topology I_top =
        subspace_topology (UNIV \<times> UNIV)
          (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
            (top1_open_sets::real set set))
          (top1_S1 \<times> I_set)"
    proof -
      have "product_topology_on top1_S1_topology I_top =
            product_topology_on
              (subspace_topology UNIV (product_topology_on (top1_open_sets::real set set) top1_open_sets) top1_S1)
              (subspace_topology UNIV (top1_open_sets::real set set) I_set)"
        unfolding top1_S1_topology_def top1_unit_interval_topology_def ..
      also have "\<dots> = subspace_topology (UNIV \<times> UNIV)
          (product_topology_on (product_topology_on (top1_open_sets::real set set) top1_open_sets)
            (top1_open_sets::real set set))
          (top1_S1 \<times> I_set)"
        by (rule Theorem_16_3[OF hTR2 hTR])
      finally show ?thesis .
    qed
    have "{p \<in> top1_S1 \<times> I_set. f p \<in> V} = (top1_S1 \<times> I_set) \<inter> W"
    proof (intro set_eqI iffI)
      fix x assume "x \<in> {p \<in> top1_S1 \<times> I_set. f p \<in> V}"
      hence "x \<in> top1_S1 \<times> I_set" "f x \<in> V" by (by100 simp)+
      hence "x \<in> f -` V \<inter> (top1_S1 \<times> I_set)" by (by100 simp)
      thus "x \<in> (top1_S1 \<times> I_set) \<inter> W" using hWeq by (by100 blast)
    next
      fix x assume "x \<in> (top1_S1 \<times> I_set) \<inter> W"
      hence "x \<in> W \<inter> (top1_S1 \<times> I_set)" by (by100 blast)
      hence "x \<in> f -` V \<inter> (top1_S1 \<times> I_set)" using hWeq by (by100 blast)
      thus "x \<in> {p \<in> top1_S1 \<times> I_set. f p \<in> V}" by (by100 simp)
    qed
    also have "\<dots> \<in> product_topology_on top1_S1_topology I_top"
      unfolding hTP_eq subspace_topology_def using hW_R3 by (by100 blast)
    finally show "{p \<in> top1_S1 \<times> I_set. f p \<in> V} \<in> product_topology_on top1_S1_topology I_top" .
  qed
  \<comment> \<open>Step 2: Codomain shrink.\<close>
  have himg: "f ` (top1_S1 \<times> I_set) \<subseteq> UNIV - {(0, 0)}"
  proof (intro subsetI)
    fix y assume "y \<in> f ` (top1_S1 \<times> I_set)"
    then obtain p where hp: "p \<in> top1_S1 \<times> I_set" and hy: "y = f p" by (by100 blast)
    show "y \<in> UNIV - {(0, 0)}" using hmap[OF hp] hy by (by100 simp)
  qed
  show ?thesis
    by (rule top1_continuous_map_on_codomain_shrink[OF hf_R2 himg]) simp
qed

(** from \<S>55 Theorem 55.5: nonvanishing vector field on B^2 points outward at
    some point of S^1 (and inward at some point). **)
text \<open>Helper: a nonvanishing vector field on B² that doesn't point inward at any
  point of S¹ leads to a contradiction (because the inclusion S¹ → R²-{0} would be nulhomotopic).\<close>
lemma vector_field_must_point_inward:
  assumes "top1_continuous_map_on top1_B2 top1_B2_topology
             (UNIV::(real \<times> real) set)
             (product_topology_on top1_open_sets top1_open_sets) v"
      and "\<forall>x\<in>top1_B2. v x \<noteq> (0, 0)"
      and "\<not> (\<exists>x\<in>top1_S1. \<exists>a>0. v x = (a * fst x, a * snd x))"
  shows False
proof -
  \<comment> \<open>w = v|S^1 extends to B^2 \<rightarrow> R^2-0 (via v itself), so w is nulhomotopic.\<close>
  have hw_nul: "top1_nulhomotopic_on top1_S1 top1_S1_topology
      (UNIV - {(0, 0)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
         (UNIV - {(0, 0)}))
      (\<lambda>x. v x)"
  proof -
    let ?R2_0 = "UNIV - {(0::real, 0::real)}"
    let ?TR2_0 = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?R2_0"
    have hv_S1: "top1_continuous_map_on top1_S1 top1_S1_topology ?R2_0 ?TR2_0 (\<lambda>x. v x)"
    proof -
      have hS1_B2: "top1_S1 \<subseteq> top1_B2" unfolding top1_S1_def top1_B2_def by (by100 auto)
      have hv_B2_temp: "top1_continuous_map_on top1_B2 top1_B2_topology ?R2_0 ?TR2_0 (\<lambda>x. v x)"
      proof -
        have himg: "(\<lambda>x. v x) ` top1_B2 \<subseteq> ?R2_0" using assms(2) by (by100 auto)
        show ?thesis by (rule top1_continuous_map_on_codomain_shrink[OF assms(1) himg]) simp
      qed
      show ?thesis
      proof -
        have hrestr: "top1_continuous_map_on top1_S1
            (subspace_topology top1_B2 top1_B2_topology top1_S1) ?R2_0 ?TR2_0 (\<lambda>x. v x)"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hv_B2_temp hS1_B2])
        have hS1_eq: "subspace_topology top1_B2 top1_B2_topology top1_S1 = top1_S1_topology"
          unfolding top1_B2_topology_def top1_S1_topology_def
          using subspace_topology_trans[OF hS1_B2, of UNIV "product_topology_on top1_open_sets top1_open_sets"]
          by simp
        show ?thesis using hrestr unfolding hS1_eq .
      qed
    qed
    have hv_B2: "top1_continuous_map_on top1_B2 top1_B2_topology ?R2_0 ?TR2_0 (\<lambda>x. v x)"
    proof -
      have himg: "(\<lambda>x. v x) ` top1_B2 \<subseteq> ?R2_0"
        using assms(2) by (by100 auto)
      have hR2_sub: "?R2_0 \<subseteq> (UNIV :: (real\<times>real) set)" by simp
      show ?thesis
        by (rule top1_continuous_map_on_codomain_shrink[OF assms(1) himg hR2_sub])
    qed
    have hTR: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTR2: "is_topology_on ((UNIV::real set) \<times> (UNIV::real set)) (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
      by (rule product_topology_on_is_topology_on[OF hTR hTR])
    have hTR2': "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
      using hTR2 by simp
    have hTR2_0: "is_topology_on ?R2_0 ?TR2_0"
      by (rule subspace_topology_is_topology_on[OF hTR2']) simp
    have hext: "\<forall>x\<in>top1_S1. v x = v x" by simp
    show ?thesis by (rule Lemma_55_3_backward[OF hv_S1 hTR2_0 hv_B2 hext])
  qed
  \<comment> \<open>F(x,t) = tx + (1-t)v(x) is a homotopy from v|S^1 to inclusion j.
     F \<noteq> 0 because "no inward pointing" prevents cancellation.\<close>
  have hj_nul: "top1_nulhomotopic_on top1_S1 top1_S1_topology
      (UNIV - {(0, 0)})
      (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
         (UNIV - {(0, 0)}))
      (\<lambda>x. x)"
  proof -
    let ?R2_0' = "UNIV - {(0::real, 0::real)}"
    let ?TR2_0' = "subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) ?R2_0'"
    have hhom_v_id: "top1_homotopic_on top1_S1 top1_S1_topology ?R2_0' ?TR2_0' (\<lambda>x. v x) (\<lambda>x. x)"
    proof -
      \<comment> \<open>F(x,t) = (1-t)*v(x) - t*x is a homotopy from v to -id in R²-{0}.
         F = 0 ⟹ v(x) = t/(1-t) · x with a = t/(1-t) > 0, contradicting assms(3).\<close>
      let ?F = "\<lambda>(x::real\<times>real, t::real). ((1-t) * fst (v x) - t * fst x,
                                          (1-t) * snd (v x) - t * snd x)"
      have hF0: "\<forall>x\<in>top1_S1. ?F (x, 0) = v x"
        by (by100 simp)
      have hF1: "\<forall>x\<in>top1_S1. ?F (x, 1) = (- fst x, - snd x)"
        by (by100 simp)
      have hF_nz: "\<forall>x\<in>top1_S1. \<forall>t\<in>I_set. ?F (x, t) \<noteq> (0, 0)"
      proof (intro ballI)
        fix x :: "real \<times> real" and t :: real
        assume hx: "x \<in> top1_S1" and ht: "t \<in> I_set"
        show "?F (x, t) \<noteq> (0, 0)"
        proof (cases "t = 0")
          case True
          \<comment> \<open>F(x,0) = v(x) \<noteq> 0 since v nonvanishing on B² \<supseteq> S¹.\<close>
          have "x \<in> top1_B2" using hx unfolding top1_S1_def top1_B2_def by (by100 auto)
          hence "v x \<noteq> (0, 0)" using assms(2) by (by100 blast)
          thus ?thesis using True by (by100 simp)
        next
          case False
          hence ht_pos: "t > 0" using ht unfolding top1_unit_interval_def by (by100 simp)
          show ?thesis
          proof (cases "t = 1")
            case True
            have "fst x ^ 2 + snd x ^ 2 = 1" using hx unfolding top1_S1_def by (by100 simp)
            hence hxnz: "x \<noteq> (0, 0)" by (cases x) (auto simp: sum_power2_gt_zero_iff)
            show ?thesis using hxnz True by (simp add: prod_eq_iff)
          next
            case False2: False
            hence h1mt_pos: "1 - t > 0" using ht unfolding top1_unit_interval_def by (by100 simp)
            show ?thesis
            proof
              assume habs: "?F (x, t) = (0, 0)"
              \<comment> \<open>From (1-t)*v_i(x) - t*x_i = 0, get v_i(x) = t/(1-t) * x_i.\<close>
              have habs1: "(1 - t) * fst (v x) = t * fst x"
                using habs by (simp add: prod_eq_iff)
              have habs2: "(1 - t) * snd (v x) = t * snd x"
                using habs by (simp add: prod_eq_iff)
              have hv1: "fst (v x) = t / (1 - t) * fst x"
                using habs1 h1mt_pos by (simp add: field_simps)
              have hv2: "snd (v x) = t / (1 - t) * snd x"
                using habs2 h1mt_pos by (simp add: field_simps)
              have ha_pos: "t / (1 - t) > 0" using ht_pos h1mt_pos by (by100 simp)
              have "v x = (t / (1 - t) * fst x, t / (1 - t) * snd x)"
                using hv1 hv2 by (simp add: prod_eq_iff)
              hence "\<exists>a>0. v x = (a * fst x, a * snd x)"
                using ha_pos by (by100 blast)
              hence "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (a * fst x, a * snd x)"
                using hx by (by100 blast)
              thus False using assms(3) by (by100 blast)
            qed
          qed
        qed
      qed
      have hv_cont: "top1_continuous_map_on top1_S1 top1_S1_topology ?R2_0' ?TR2_0' (\<lambda>x. v x)"
      proof -
        have hS1_B2: "top1_S1 \<subseteq> top1_B2" unfolding top1_S1_def top1_B2_def by (by100 auto)
        have himg: "(\<lambda>x. v x) ` top1_B2 \<subseteq> ?R2_0'" using assms(2) by (by100 auto)
        have hv_B2: "top1_continuous_map_on top1_B2 top1_B2_topology ?R2_0' ?TR2_0' (\<lambda>x. v x)"
          by (rule top1_continuous_map_on_codomain_shrink[OF assms(1) himg]) simp
        have hrestr: "top1_continuous_map_on top1_S1
            (subspace_topology top1_B2 top1_B2_topology top1_S1) ?R2_0' ?TR2_0' (\<lambda>x. v x)"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hv_B2 hS1_B2])
        have hS1_eq: "subspace_topology top1_B2 top1_B2_topology top1_S1 = top1_S1_topology"
          unfolding top1_B2_topology_def top1_S1_topology_def
          using subspace_topology_trans[OF hS1_B2, of UNIV "product_topology_on top1_open_sets top1_open_sets"]
          by simp
        show ?thesis using hrestr unfolding hS1_eq .
      qed
      have hid_cont: "top1_continuous_map_on top1_S1 top1_S1_topology ?R2_0' ?TR2_0' (\<lambda>x. x)"
      proof -
        have hS1_sub: "top1_S1 \<subseteq> ?R2_0'" unfolding top1_S1_def by (by100 auto)
        have hTR2_0_full: "is_topology_on ?R2_0' ?TR2_0'"
          by (simp add: product_topology_on_open_sets subspace_topology_is_topology_on
              top1_open_sets_is_topology_on_UNIV)
        have hid_full: "top1_continuous_map_on ?R2_0' ?TR2_0' ?R2_0' ?TR2_0' id"
          by (rule top1_continuous_map_on_id[OF hTR2_0_full])
        have hid_restr: "top1_continuous_map_on top1_S1
            (subspace_topology ?R2_0' ?TR2_0' top1_S1) ?R2_0' ?TR2_0' id"
          by (rule top1_continuous_map_on_restrict_domain_simple[OF hid_full hS1_sub])
        have hS1_eq: "subspace_topology ?R2_0' ?TR2_0' top1_S1 = top1_S1_topology"
          unfolding top1_S1_topology_def using subspace_topology_trans[OF hS1_sub] by simp
        have hid_eq: "(\<lambda>x::real\<times>real. x) = id" by (rule ext) simp
        show ?thesis using hid_restr unfolding hS1_eq hid_eq[symmetric] by simp
      qed
      have hF_cont: "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
          ?R2_0' ?TR2_0' ?F"
      proof -
        \<comment> \<open>v is continuous_on B² (reverse transfer), hence on S¹.\<close>
        have hv_B2_std: "continuous_on top1_B2 v"
          using assms(1) unfolding top1_B2_topology_def
          by (rule top1_continuous_map_on_to_continuous_on_R2)
        have hS1_B2: "top1_S1 \<subseteq> top1_B2"
          unfolding top1_S1_def top1_B2_def by (by100 auto)
        have hv_S1_std: "continuous_on top1_S1 v"
          by (rule continuous_on_subset[OF hv_B2_std hS1_B2])
        \<comment> \<open>F(x,t) = ((1-t)*v₁(x)-t*x₁, (1-t)*v₂(x)-t*x₂) continuous on S¹×I.\<close>
        have hv_fst_cont: "continuous_on (top1_S1 \<times> I_set) (v \<circ> fst)"
          by (intro continuous_on_compose continuous_on_fst
              continuous_on_subset[OF hv_S1_std]) (by100 auto)
        have hfst_v: "continuous_on (top1_S1 \<times> I_set) (\<lambda>p. fst (v (fst p)))"
          by (intro continuous_on_fst[OF hv_fst_cont[unfolded comp_def]])
        have hsnd_v: "continuous_on (top1_S1 \<times> I_set) (\<lambda>p. snd (v (fst p)))"
          by (intro continuous_on_snd[OF hv_fst_cont[unfolded comp_def]])
        have hF_std: "continuous_on (top1_S1 \<times> I_set) (\<lambda>p::(real\<times>real)\<times>real.
            ((1 - snd p) * fst (v (fst p)) - snd p * fst (fst p),
             (1 - snd p) * snd (v (fst p)) - snd p * snd (fst p)))"
          by (intro continuous_on_Pair continuous_on_diff continuous_on_mult
              continuous_on_snd hfst_v hsnd_v continuous_intros)
        have hF_eq: "(\<lambda>p::(real\<times>real)\<times>real.
            ((1 - snd p) * fst (v (fst p)) - snd p * fst (fst p),
             (1 - snd p) * snd (v (fst p)) - snd p * snd (fst p)))
          = (\<lambda>p. ?F (fst p, snd p))" by (rule ext) (simp add: case_prod_beta)
        have hF_map: "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> ?F p \<in> ?R2_0'"
          using hF_nz by (by100 auto)
        have hF_map': "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> (\<lambda>p. ?F (fst p, snd p)) p \<in> ?R2_0'"
          using hF_map by (simp add: case_prod_beta)
        have hF_std': "continuous_on (top1_S1 \<times> I_set) (\<lambda>p. ?F (fst p, snd p))"
          using hF_std unfolding hF_eq .
        have "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
            ?R2_0' ?TR2_0' (\<lambda>p. ?F (fst p, snd p))"
          by (rule S1_I_to_R2_minus_0_continuous_on[OF hF_std' hF_map'])
        moreover have "(\<lambda>p::(real\<times>real)\<times>real. ?F (fst p, snd p)) = ?F"
          by (rule ext) (simp add: case_prod_beta)
        ultimately show ?thesis by simp
      qed
      \<comment> \<open>F gives v ≃ -id. Need -id ≃ id (rotation). Then v ≃ id by transitivity.\<close>
      let ?neg = "\<lambda>x::real\<times>real. (- fst x, - snd x)"
      have hneg_cont: "top1_continuous_map_on top1_S1 top1_S1_topology ?R2_0' ?TR2_0' ?neg"
      proof -
        have hneg_std: "continuous_on UNIV ?neg"
          by (intro continuous_on_Pair continuous_intros)
        have hneg_map: "\<And>x. x \<in> top1_S1 \<Longrightarrow> ?neg x \<in> ?R2_0'"
          unfolding top1_S1_def by (by100 auto)
        have hneg_R2: "top1_continuous_map_on top1_S1
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) top1_S1)
            ?R2_0' ?TR2_0' ?neg"
          by (rule top1_continuous_map_on_real2_subspace[OF hneg_map hneg_std])
        thus ?thesis unfolding top1_S1_topology_def .
      qed
      have hv_neg: "top1_homotopic_on top1_S1 top1_S1_topology ?R2_0' ?TR2_0' (\<lambda>x. v x) ?neg"
      proof -
        have hF1': "\<forall>x\<in>top1_S1. ?F (x, 1) = ?neg x" by (by100 simp)
        show ?thesis unfolding top1_homotopic_on_def
          using hv_cont hneg_cont hF_cont hF0 hF1' by (by100 blast)
      qed
      have hneg_id: "top1_homotopic_on top1_S1 top1_S1_topology ?R2_0' ?TR2_0' ?neg (\<lambda>x. x)"
      proof -
        \<comment> \<open>Rotation R(x,t) = (cos(\<pi>(1-t)) a - sin(\<pi>(1-t)) b, sin(\<pi>(1-t)) a + cos(\<pi>(1-t)) b)
           R(x,0) = (-a,-b) = -x, R(x,1) = (a,b) = x. R maps into S¹ ⊂ R²-{0}.\<close>
        let ?R = "\<lambda>(x::real\<times>real, t::real).
            (cos (pi * (1 - t)) * fst x - sin (pi * (1 - t)) * snd x,
             sin (pi * (1 - t)) * fst x + cos (pi * (1 - t)) * snd x)"
        have hR0: "\<forall>x\<in>top1_S1. ?R (x, 0) = ?neg x" by (by100 simp)
        have hR1: "\<forall>x\<in>top1_S1. ?R (x, 1) = x" by (by100 simp)
        have hR_S1: "\<forall>x\<in>top1_S1. \<forall>t\<in>I_set. ?R (x, t) \<in> top1_S1"
        proof (intro ballI)
          fix x :: "real \<times> real" and t :: real
          assume hx: "x \<in> top1_S1" and ht: "t \<in> I_set"
          have hsum: "fst x ^ 2 + snd x ^ 2 = 1" using hx unfolding top1_S1_def by (by100 simp)
          let ?c = "cos (pi * (1 - t))" and ?s = "sin (pi * (1 - t))"
          have "fst (?R (x, t)) ^ 2 + snd (?R (x, t)) ^ 2 = 1"
          proof -
            have "fst (?R (x, t)) ^ 2 + snd (?R (x, t)) ^ 2 =
                (?c * fst x - ?s * snd x) ^ 2 + (?s * fst x + ?c * snd x) ^ 2"
              by simp
            also have "\<dots> = (fst x ^ 2 + snd x ^ 2) * (?c ^ 2 + ?s ^ 2)"
              by algebra
            also have "\<dots> = 1" using hsum by simp
            finally show ?thesis .
          qed
          thus "?R (x, t) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
        qed
        have hR_R2: "\<forall>x\<in>top1_S1. \<forall>t\<in>I_set. ?R (x, t) \<in> ?R2_0'"
        proof (intro ballI)
          fix x :: "real \<times> real" and t :: real
          assume "x \<in> top1_S1" and "t \<in> I_set"
          hence "?R (x, t) \<in> top1_S1" using hR_S1 by (by100 blast)
          thus "?R (x, t) \<in> ?R2_0'" unfolding top1_S1_def by (by100 auto)
        qed
        have hR_cont: "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
            ?R2_0' ?TR2_0' ?R"
        proof -
          let ?Rf = "\<lambda>p::(real\<times>real)\<times>real.
              (cos (pi * (1 - snd p)) * fst (fst p) - sin (pi * (1 - snd p)) * snd (fst p),
               sin (pi * (1 - snd p)) * fst (fst p) + cos (pi * (1 - snd p)) * snd (fst p))"
          have hRf_eq: "?Rf = (\<lambda>p. ?R (fst p, snd p))"
            by (rule ext) (simp add: case_prod_beta)
          have hR_std: "continuous_on UNIV ?Rf"
            by (intro continuous_on_Pair continuous_intros)
          have hR_map: "\<And>p. p \<in> top1_S1 \<times> I_set \<Longrightarrow> ?Rf p \<in> UNIV - {(0, 0)}"
            using hR_R2 unfolding hRf_eq by (by100 auto)
          have "top1_continuous_map_on (top1_S1 \<times> I_set) (product_topology_on top1_S1_topology I_top)
              ?R2_0' ?TR2_0' ?Rf"
            by (rule S1_I_to_R2_minus_0_continuous[OF hR_std hR_map])
          moreover have "?Rf = ?R" unfolding hRf_eq
            by (rule ext) (simp add: case_prod_beta)
          ultimately show ?thesis by simp
        qed
        show ?thesis unfolding top1_homotopic_on_def
          using hneg_cont hid_cont hR_cont hR0 hR1 by (by100 blast)
      qed
      have hTR2_0': "is_topology_on ?R2_0' ?TR2_0'"
        by (simp add: product_topology_on_open_sets subspace_topology_is_topology_on
            top1_open_sets_is_topology_on_UNIV)
      have hTS1': "is_topology_on top1_S1 top1_S1_topology"
      proof -
        have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
        have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
          using product_topology_on_is_topology_on[OF hTR hTR] by simp
        show ?thesis unfolding top1_S1_topology_def
          by (rule subspace_topology_is_topology_on[OF hTR2]) simp
      qed
      show ?thesis
        by (rule Lemma_51_1_homotopic_trans[OF hTS1' hTR2_0' hv_neg hneg_id])
    qed
    have hTS1: "is_topology_on top1_S1 top1_S1_topology"
    proof -
      have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
      have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF hTR hTR] by simp
      show ?thesis unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF hTR2]) simp
    qed
    have hTR2_0': "is_topology_on ?R2_0' ?TR2_0'"
    proof -
      have hTR: "is_topology_on (UNIV::real set) top1_open_sets" by (rule top1_open_sets_is_topology_on_UNIV)
      have hTR2: "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on top1_open_sets top1_open_sets)"
        using product_topology_on_is_topology_on[OF hTR hTR] by simp
      show ?thesis by (rule subspace_topology_is_topology_on[OF hTR2]) simp
    qed
    show ?thesis
      by (rule nulhomotopic_homotopic_trans[OF hTS1 hTR2_0' hw_nul hhom_v_id])
  qed
  show False using Corollary_55_4_inclusion_not_nulhomotopic hj_nul by (by100 blast)
qed

theorem Theorem_55_5_vector_field:
  assumes "top1_continuous_map_on top1_B2 top1_B2_topology
             (UNIV::(real \<times> real) set)
             (product_topology_on top1_open_sets top1_open_sets) v"
      and "\<forall>x\<in>top1_B2. v x \<noteq> (0, 0)"
  shows "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (a * fst x, a * snd x)"
    and "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (-(a * fst x), -(a * snd x))"
  \<comment> \<open>Munkres Theorem 55.5: Suppose v doesn't point inward at any x\<in>S^1.
     Let w = v|S^1. Then w extends to B^2 \<rightarrow> R^2-0, so w is nulhomotopic.
     But F(x,t) = tx + (1-t)w(x) is a homotopy from w to inclusion j: S^1 \<rightarrow> R^2-0
     (F(x,t)\<noteq>0 because if tx+(1-t)w(x)=0 then w(x) = -t/(1-t) \<cdot> x points inward).
     So j is nulhomotopic, contradicting Corollary 55.4.
     For outward: apply to the vector field (x, -v(x)).\<close>
proof -
  \<comment> \<open>Inward: suppose v never points inward at any x \<in> S^1.\<close>
  have hinward: "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (a * fst x, a * snd x)"
  proof (rule ccontr)
    assume hnot: "\<not> (\<exists>x\<in>top1_S1. \<exists>a>0. v x = (a * fst x, a * snd x))"
    show False by (rule vector_field_must_point_inward[OF assms hnot])
  qed
  \<comment> \<open>Outward: apply the inward result to -v.\<close>
  have houtward: "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (-(a * fst x), -(a * snd x))"
  proof -
    \<comment> \<open>Apply the inward result to -v: -v is continuous B^2 \<rightarrow> R^2 and nonvanishing.\<close>
    let ?neg_v = "\<lambda>x. (- fst (v x), - snd (v x))"
    have hnv_cont: "top1_continuous_map_on top1_B2 top1_B2_topology UNIV
        (product_topology_on top1_open_sets top1_open_sets) ?neg_v"
    proof -
      \<comment> \<open>Negation (x,y) \<mapsto> (-x,-y) is continuous R^2 \<rightarrow> R^2.\<close>
      let ?neg = "\<lambda>p::real\<times>real. (- fst p, - snd p)"
      have hneg_cont: "continuous_on UNIV ?neg"
        by (intro continuous_on_Pair continuous_intros)
      have hneg_sub: "top1_continuous_map_on (UNIV :: (real\<times>real) set)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) UNIV)
          (UNIV :: (real\<times>real) set)
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) UNIV) ?neg"
        by (rule top1_continuous_map_on_real2_subspace) (simp_all add: hneg_cont)
      have hneg_map: "top1_continuous_map_on UNIV (product_topology_on top1_open_sets top1_open_sets)
          UNIV (product_topology_on top1_open_sets top1_open_sets) ?neg"
        using hneg_sub unfolding subspace_topology_UNIV_self .
      \<comment> \<open>-v = neg \<circ> v.\<close>
      have heq: "?neg_v = ?neg \<circ> v" by (rule ext) (simp add: comp_def)
      have hv_full: "top1_continuous_map_on top1_B2 top1_B2_topology UNIV
          (product_topology_on top1_open_sets top1_open_sets) v" using assms(1) .
      show ?thesis unfolding heq
        by (rule top1_continuous_map_on_comp[OF hv_full hneg_map])
    qed
    have hnv_nz: "\<forall>x\<in>top1_B2. ?neg_v x \<noteq> (0, 0)"
    proof (intro ballI)
      fix x assume "x \<in> top1_B2"
      hence "v x \<noteq> (0, 0)" using assms(2) by (by100 blast)
      thus "?neg_v x \<noteq> (0, 0)" by (simp add: prod_eq_iff)
    qed
    \<comment> \<open>The inward argument for -v gives: \<exists>x\<in>S^1. \<exists>a>0. -v(x) = a*x.\<close>
    have "\<exists>x\<in>top1_S1. \<exists>a>0. ?neg_v x = (a * fst x, a * snd x)"
    proof (rule ccontr)
      assume "\<not> (\<exists>x\<in>top1_S1. \<exists>a>0. ?neg_v x = (a * fst x, a * snd x))"
      thus False by (rule vector_field_must_point_inward[OF hnv_cont hnv_nz])
    qed
    then obtain x a where hx: "x \<in> top1_S1" and ha: "a > 0"
        and hva: "?neg_v x = (a * fst x, a * snd x)" by (by100 blast)
    \<comment> \<open>-v(x) = a*x means v(x) = -a*x.\<close>
    have "v x = (-(a * fst x), -(a * snd x))"
      using hva by (simp add: prod_eq_iff)
    thus ?thesis using hx ha by (by100 blast)
  qed
  show "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (a * fst x, a * snd x)" by (rule hinward)
  show "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (-(a * fst x), -(a * snd x))" by (rule houtward)
qed

(** from \<S>55 Theorem 55.6: Brouwer fixed-point theorem for the disc.
    Munkres' proof: by contradiction. If f has no fixed point, v(x) = f(x) - x
    is a nonvanishing vector field on B^2. But v cannot point outward at any
    x \<in> S^1: that would mean f(x) - x = a x with a > 0, hence f(x) = (1+a)x has
    norm > 1, contradicting f: B^2 \<rightarrow> B^2. Theorem 55.5 gives such a point \<Rightarrow> \<bottom>. **)
theorem Theorem_55_6_brouwer:
  assumes hf: "top1_continuous_map_on top1_B2 top1_B2_topology top1_B2 top1_B2_topology f"
  shows "\<exists>x\<in>top1_B2. f x = x"
proof (rule ccontr)
  assume hnofix: "\<not> (\<exists>x\<in>top1_B2. f x = x)"
  \<comment> \<open>Step 1: define v(x) = f(x) - x.\<close>
  let ?v = "\<lambda>x::real\<times>real. (fst (f x) - fst x, snd (f x) - snd x)"
  \<comment> \<open>Step 2: v is continuous B^2 \<rightarrow> R^2.\<close>
  have hv_cont: "top1_continuous_map_on top1_B2 top1_B2_topology
                  UNIV (product_topology_on top1_open_sets top1_open_sets) ?v"
    by (rule top1_B2_diff_continuous[OF hf])
  \<comment> \<open>Step 3: v is nonvanishing (from hnofix).\<close>
  have hv_nonzero: "\<forall>x\<in>top1_B2. ?v x \<noteq> (0, 0)"
  proof (intro ballI)
    fix x assume hxB2: "x \<in> top1_B2"
    have "f x \<noteq> x" using hnofix hxB2 by blast
    hence "fst (f x) \<noteq> fst x \<or> snd (f x) \<noteq> snd x"
      by (simp add: prod_eq_iff)
    thus "?v x \<noteq> (0, 0)" by auto
  qed
  \<comment> \<open>Step 4: by Theorem 55.5, some x \<in> S^1 has v(x) = a x for a > 0 (outward).\<close>
  obtain x a where hx: "x \<in> top1_S1" and ha: "a > 0"
      and hva: "?v x = (a * fst x, a * snd x)"
    using Theorem_55_5_vector_field(1)[OF hv_cont hv_nonzero] by blast
  \<comment> \<open>Step 5: then f(x) = (1+a) x. Since |x| = 1, |f(x)| = 1+a > 1, but f(x) \<in> B^2.\<close>
  have hfx: "f x = ((1 + a) * fst x, (1 + a) * snd x)"
  proof -
    have "fst (f x) - fst x = a * fst x" using hva by simp
    hence h1: "fst (f x) = (1 + a) * fst x" by (simp add: algebra_simps)
    have "snd (f x) - snd x = a * snd x" using hva by simp
    hence h2: "snd (f x) = (1 + a) * snd x" by (simp add: algebra_simps)
    show ?thesis using h1 h2 by (simp add: prod_eq_iff)
  qed
  have hx_norm: "fst x^2 + snd x^2 = 1" using hx unfolding top1_S1_def by simp
  have hfx_norm: "fst (f x)^2 + snd (f x)^2 = (1 + a)^2"
  proof -
    have h1: "fst (f x)^2 = (1 + a)^2 * fst x^2"
      using hfx by (simp add: power_mult_distrib)
    have h2: "snd (f x)^2 = (1 + a)^2 * snd x^2"
      using hfx by (simp add: power_mult_distrib)
    have "fst (f x)^2 + snd (f x)^2 = (1 + a)^2 * (fst x^2 + snd x^2)"
      using h1 h2 by (simp add: ring_distribs)
    also have "\<dots> = (1 + a)^2" using hx_norm by simp
    finally show ?thesis .
  qed
  have ha_pos: "(1 + a)^2 > 1"
  proof -
    have "(1 + a)^2 = 1 + 2*a + a^2" by (simp add: power2_sum)
    moreover have "2 * a + a^2 > 0" using ha by (simp add: add_pos_nonneg)
    ultimately show ?thesis by linarith
  qed
  hence "fst (f x)^2 + snd (f x)^2 > 1" using hfx_norm by simp
  moreover have "fst (f x)^2 + snd (f x)^2 \<le> 1"
  proof -
    have hxB2: "x \<in> top1_B2" using hx unfolding top1_S1_def top1_B2_def by simp
    have "f x \<in> top1_B2"
      using hf hxB2 unfolding top1_continuous_map_on_def by blast
    thus ?thesis unfolding top1_B2_def by simp
  qed
  ultimately show False by linarith
qed

\<comment> \<open>General homotopy tools (homotopy_induced_basepoint_change,
   nulhomotopic_trivializes_loops_general) moved before §56.\<close>

subsection \<open>General homotopy tools (needed for \<S>57 and \<S>58)\<close>


text \<open>Key: homotopy from h to k + loop l at x₀ implies h\<circ>l loop-equiv to basepoint-change of k\<circ>l.\<close>
lemma homotopy_induced_basepoint_change:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hHcont: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY H"
      and hH0: "\<forall>x\<in>X. H (x, 0) = h x" and hH1: "\<forall>x\<in>X. H (x, 1) = k x"
      and hl: "top1_is_loop_on X TX x0 l" and hx0: "x0 \<in> X"
  shows "top1_loop_equiv_on Y TY (h x0) (h \<circ> l)
    (top1_basepoint_change_on Y TY (k x0) (h x0) (top1_path_reverse (\<lambda>t. H (x0, t))) (k \<circ> l))"
proof -
  let ?\<alpha> = "\<lambda>t. H (x0, t)"
  \<comment> \<open>G(s,t) = H(l(s), t) gives: G(s,0) = h(l(s)), G(s,1) = k(l(s)),
     G(0,t) = G(1,t) = \<alpha>(t). So G is a homotopy (h\<circ>l) \<simeq> (k\<circ>l) relative to \<alpha>.\<close>
  \<comment> \<open>From this, derive: (h\<circ>l) * \<alpha> \<simeq> \<alpha> * (k\<circ>l), hence h\<circ>l \<simeq> \<alpha>⁻¹ * (k\<circ>l) * \<alpha>.\<close>
  \<comment> \<open>The full proof requires the broken-line homotopy in I×I (convexity)
     and composition with G. This is Munkres Lemma 58.4.\<close>
  \<comment> \<open>Step 1: G(s,t) = H(l(s),t) is continuous I×I → Y.\<close>
  let ?G = "\<lambda>(s::real, t::real). H (l s, t)"
  have hG_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY ?G"
  proof -
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hl_cont: "top1_continuous_map_on I_set I_top X TX l"
      using hl unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
    have hpi1: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi1"
      unfolding II_topology_def by (rule top1_continuous_pi1[OF hTI hTI])
    have hpi2: "top1_continuous_map_on (I_set \<times> I_set) II_topology I_set I_top pi2"
      unfolding II_topology_def by (rule top1_continuous_pi2[OF hTI hTI])
    have hlfst: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX (l \<circ> pi1)"
      by (rule top1_continuous_map_on_comp[OF hpi1 hl_cont])
    have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
    have heq: "(\<lambda>p. (l (pi1 p), pi2 p)) = (\<lambda>(s, t). (l s, t))"
      unfolding pi1_def pi2_def by (rule ext) (simp add: case_prod_beta)
    have hlid: "top1_continuous_map_on (I_set \<times> I_set) II_topology (X \<times> I_set)
        (product_topology_on TX I_top) (\<lambda>(s, t). (l s, t))"
    proof -
      have hT18: "\<And>f. (\<forall>c\<in>(I_set \<times> I_set). f c \<in> X \<times> I_set) \<and>
          top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX (pi1 \<circ> f) \<and>
          top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top (pi2 \<circ> f)
          \<longrightarrow> top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
              (X \<times> I_set) (product_topology_on TX I_top) f"
        using Theorem_18_4[OF hTII[unfolded II_topology_def] hTX hTI] by (by100 blast)
      have hcomp1: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) X TX
          (pi1 \<circ> (\<lambda>(s, t). (l s, t)))"
      proof -
        have "pi1 \<circ> (\<lambda>(s, t). (l s, t)) = l \<circ> pi1"
          unfolding pi1_def comp_def by (rule ext) (simp add: case_prod_beta)
        show ?thesis using hlfst unfolding \<open>pi1 \<circ> (\<lambda>(s, t). (l s, t)) = l \<circ> pi1\<close> II_topology_def .
      qed
      have hcomp2: "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top) I_set I_top
          (pi2 \<circ> (\<lambda>(s, t). (l s, t)))"
      proof -
        have "pi2 \<circ> (\<lambda>(s, t). (l s, t)) = pi2"
          unfolding pi2_def comp_def by (rule ext) (simp add: case_prod_beta)
        show ?thesis using hpi2 unfolding \<open>pi2 \<circ> (\<lambda>(s, t). (l s, t)) = pi2\<close> II_topology_def .
      qed
      have hrange: "\<forall>c\<in>(I_set \<times> I_set). (\<lambda>(s, t). (l s, t)) c \<in> X \<times> I_set"
        using hl_cont unfolding top1_continuous_map_on_def by (by100 auto)
      have "top1_continuous_map_on (I_set \<times> I_set) (product_topology_on I_top I_top)
          (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>(s, t). (l s, t))"
        using hT18 hcomp1 hcomp2 hrange by (by100 blast)
      thus ?thesis unfolding II_topology_def .
    qed
    have "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY (H \<circ> (\<lambda>(s, t). (l s, t)))"
      by (rule top1_continuous_map_on_comp[OF hlid hHcont])
    moreover have "(H \<circ> (\<lambda>(s, t). (l s, t))) = ?G"
      by (rule ext) (simp add: comp_def case_prod_beta)
    ultimately show ?thesis by simp
  qed
  have hl0: "l 0 = x0" using hl unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  have hl1: "l 1 = x0" using hl unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
  have hG_bot: "\<forall>s\<in>I_set. ?G (s, 0) = (h \<circ> l) s"
  proof (intro ballI)
    fix s assume "s \<in> I_set"
    have "l s \<in> X" using hl \<open>s \<in> I_set\<close>
      unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
    thus "?G (s, 0) = (h \<circ> l) s" using hH0 by (by100 simp)
  qed
  have hG_top: "\<forall>s\<in>I_set. ?G (s, 1) = (k \<circ> l) s"
  proof (intro ballI)
    fix s assume "s \<in> I_set"
    have "l s \<in> X" using hl \<open>s \<in> I_set\<close>
      unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def by (by100 blast)
    thus "?G (s, 1) = (k \<circ> l) s" using hH1 by (by100 simp)
  qed
  have hG_left: "\<forall>t\<in>I_set. ?G (0, t) = ?\<alpha> t"
    using hl0 by (by100 simp)
  have hG_right: "\<forall>t\<in>I_set. ?G (1, t) = ?\<alpha> t"
    using hl1 by (by100 simp)
  \<comment> \<open>Step 2: (h\<circ>l)*\<alpha> \<simeq> \<alpha>*(k\<circ>l) via broken-line homotopy in I×I.
     The convexity of I×I gives a homotopy between the two broken-line paths.\<close>
  have hprod_hom: "top1_path_homotopic_on Y TY (h x0) (k x0)
      (top1_path_product (h \<circ> l) ?\<alpha>)
      (top1_path_product ?\<alpha> (k \<circ> l))"
  proof -
    \<comment> \<open>Broken-line paths in I×I: β₁ = bottom*right, β₂ = left*top.
       G∘β₁ = (h∘l)*α, G∘β₂ = α*(k∘l).
       β₁ ≃ β₂ in I×I (convexity). Apply G.\<close>
    \<comment> \<open>Define β₁, β₂ as path products in I×I.\<close>
    let ?bottom = "\<lambda>s::real. (s, 0::real)"
    let ?right = "\<lambda>t::real. (1::real, t)"
    let ?left' = "\<lambda>t::real. (0::real, t)"
    let ?top' = "\<lambda>s::real. (s, 1::real)"
    \<comment> \<open>β₁ = bottom * right, β₂ = left * top.\<close>
    let ?\<beta>1 = "top1_path_product ?bottom ?right"
    let ?\<beta>2 = "top1_path_product ?left' ?top'"
    \<comment> \<open>β₁ and β₂ both go from (0,0) to (1,1) in I×I.
       They're path-homotopic in I×I because I×I is convex (simply connected).\<close>
    have hII_sc: "top1_simply_connected_on (I_set \<times> I_set) II_topology"
      unfolding top1_simply_connected_on_def
    proof (intro conjI)
      show "top1_path_connected_on (I_set \<times> I_set) II_topology"
        unfolding top1_path_connected_on_def
      proof (intro conjI ballI)
        show "is_topology_on (I_set \<times> I_set) II_topology"
          unfolding II_topology_def
          by (rule product_topology_on_is_topology_on[OF
                top1_unit_interval_topology_is_topology_on
                top1_unit_interval_topology_is_topology_on])
      next
        fix x y :: "real \<times> real"
        assume hx: "x \<in> I_set \<times> I_set" and hy: "y \<in> I_set \<times> I_set"
        let ?\<gamma> = "\<lambda>t::real. ((1-t) * fst x + t * fst y, (1-t) * snd x + t * snd y)"
        have hg_cont: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology ?\<gamma>"
        proof -
          have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
          have hc1_cont: "continuous_on UNIV (\<lambda>t::real. (1-t) * fst x + t * fst y)"
            by (intro continuous_intros)
          have hc2_cont: "continuous_on UNIV (\<lambda>t::real. (1-t) * snd x + t * snd y)"
            by (intro continuous_intros)
          have hc1_range: "\<And>t. t \<in> I_set \<Longrightarrow> (1-t) * fst x + t * fst y \<in> I_set"
          proof -
            fix t assume ht: "t \<in> I_set"
            have ht': "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)+
            have ha: "0 \<le> fst x" "fst x \<le> 1" using hx unfolding top1_unit_interval_def by (by100 auto)+
            have hb: "0 \<le> fst y" "fst y \<le> 1" using hy unfolding top1_unit_interval_def by (by100 auto)+
            have h0t: "0 \<le> 1 - t" using ht' by (by100 linarith)
            have h1: "0 \<le> (1-t) * fst x + t * fst y"
              using mult_nonneg_nonneg[OF h0t ha(1)] mult_nonneg_nonneg[OF ht'(1) hb(1)]
              by (by100 linarith)
            have h2: "(1-t) * fst x + t * fst y \<le> 1"
              by (rule convex_bound_le[OF ha(2) hb(2) h0t ht'(1)]) (by100 simp)
            show "(1-t) * fst x + t * fst y \<in> I_set"
              unfolding top1_unit_interval_def using h1 h2 by (by100 auto)
          qed
          have hc2_range: "\<And>t. t \<in> I_set \<Longrightarrow> (1-t) * snd x + t * snd y \<in> I_set"
          proof -
            fix t assume ht: "t \<in> I_set"
            have ht': "0 \<le> t" "t \<le> 1" using ht unfolding top1_unit_interval_def by (by100 auto)+
            have ha: "0 \<le> snd x" "snd x \<le> 1" using hx unfolding top1_unit_interval_def by (by100 auto)+
            have hb: "0 \<le> snd y" "snd y \<le> 1" using hy unfolding top1_unit_interval_def by (by100 auto)+
            have h0t: "0 \<le> 1 - t" using ht' by (by100 linarith)
            have h1: "0 \<le> (1-t) * snd x + t * snd y"
              using mult_nonneg_nonneg[OF h0t ha(1)] mult_nonneg_nonneg[OF ht'(1) hb(1)]
              by (by100 linarith)
            have h2: "(1-t) * snd x + t * snd y \<le> 1"
              by (rule convex_bound_le[OF ha(2) hb(2) h0t ht'(1)]) (by100 simp)
            show "(1-t) * snd x + t * snd y \<in> I_set"
              unfolding top1_unit_interval_def using h1 h2 by (by100 auto)
          qed
          have hc1: "top1_continuous_map_on I_set I_top I_set I_top
              (\<lambda>t. (1-t) * fst x + t * fst y)"
            unfolding top1_unit_interval_topology_def
            by (rule top1_continuous_map_on_real_subspace_open_sets[OF hc1_range hc1_cont])
          have hc2: "top1_continuous_map_on I_set I_top I_set I_top
              (\<lambda>t. (1-t) * snd x + t * snd y)"
            unfolding top1_unit_interval_topology_def
            by (rule top1_continuous_map_on_real_subspace_open_sets[OF hc2_range hc2_cont])
          have hpi1_eq: "pi1 \<circ> ?\<gamma> = (\<lambda>t. (1-t) * fst x + t * fst y)"
            unfolding pi1_def comp_def by (rule ext) simp
          have hpi2_eq: "pi2 \<circ> ?\<gamma> = (\<lambda>t. (1-t) * snd x + t * snd y)"
            unfolding pi2_def comp_def by (rule ext) simp
          show ?thesis unfolding II_topology_def
            using iffD2[OF Theorem_18_4[OF hTI hTI hTI]]
                  hc1[unfolded hpi1_eq[symmetric]] hc2[unfolded hpi2_eq[symmetric]]
            by (by100 blast)
        qed
        have hg0: "?\<gamma> 0 = x" by (simp add: prod_eq_iff)
        have hg1: "?\<gamma> 1 = y" by (simp add: prod_eq_iff)
        show "\<exists>f. top1_is_path_on (I_set \<times> I_set) II_topology x y f"
          unfolding top1_is_path_on_def using hg_cont hg0 hg1 by (by100 blast)
      qed
    next
      show "\<forall>x0\<in>I_set \<times> I_set. \<forall>f. top1_is_loop_on (I_set \<times> I_set) II_topology x0 f \<longrightarrow>
          top1_path_homotopic_on (I_set \<times> I_set) II_topology x0 x0 f (top1_constant_path x0)"
      proof (intro ballI allI impI)
        fix x0 :: "real \<times> real" and f :: "real \<Rightarrow> real \<times> real"
        assume hx0: "x0 \<in> I_set \<times> I_set" and hf: "top1_is_loop_on (I_set \<times> I_set) II_topology x0 f"
        have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
        have hTII': "is_topology_on (I_set \<times> I_set) II_topology"
          unfolding II_topology_def by (rule product_topology_on_is_topology_on[OF hTI hTI])
        \<comment> \<open>Straight-line homotopy: F(s,t) = (1-t)*f(s) + t*x0.\<close>
        let ?F = "\<lambda>(s::real, t::real). ((1-t) * fst (f s) + t * fst x0,
                                        (1-t) * snd (f s) + t * snd x0)"
        have hF_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
            (I_set \<times> I_set) II_topology ?F"
        proof -
          \<comment> \<open>Bridge: extract continuous_on from f's custom continuity.\<close>
          have hfc: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology f"
            using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
          have hfr: "\<forall>s\<in>I_set. f s \<in> I_set \<times> I_set"
            using hfc unfolding top1_continuous_map_on_def by (by100 blast)
          have hf_cont_on: "continuous_on I_set f"
          proof (unfold continuous_on_open_invariant, intro allI impI)
            fix U :: "(real \<times> real) set" assume hUo: "open U"
            have hU_top: "(I_set \<times> I_set) \<inter> U \<in> II_topology"
            proof -
              have "U \<in> (top1_open_sets :: (real\<times>real) set set)"
                using hUo unfolding top1_open_sets_def by (by100 blast)
              hence "U \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
                using product_topology_on_open_sets_real2 by (by100 metis)
              thus ?thesis unfolding II_topology_def II_topology_eq_subspace
                subspace_topology_def by (by100 blast)
            qed
            have hpre_II: "{x \<in> I_set. f x \<in> (I_set \<times> I_set) \<inter> U} \<in> I_top"
              using hfc hU_top unfolding top1_continuous_map_on_def by (by100 blast)
            have hpre_eq: "{x \<in> I_set. f x \<in> U} = {x \<in> I_set. f x \<in> (I_set \<times> I_set) \<inter> U}"
              using hfr by (by100 auto)
            have hmem: "{x \<in> I_set. f x \<in> U} \<in> I_top" using hpre_II hpre_eq by (by100 simp)
            then obtain W where hWo: "open W" and hWeq: "{x \<in> I_set. f x \<in> U} = I_set \<inter> W"
              unfolding top1_unit_interval_topology_def subspace_topology_def
                        top1_open_sets_def by (by100 auto)
            have "W \<inter> I_set = f -` U \<inter> I_set" using hWeq by (by100 blast)
            hence "open W \<and> W \<inter> I_set = f -` U \<inter> I_set" using hWo by (by100 blast)
            thus "\<exists>A. open A \<and> A \<inter> I_set = f -` U \<inter> I_set" by (by100 blast)
          qed
          \<comment> \<open>continuous_on components.\<close>
          have hfst_cont: "continuous_on I_set (\<lambda>s. fst (f s))"
            using continuous_on_fst[OF hf_cont_on] unfolding comp_def .
          have hsnd_cont: "continuous_on I_set (\<lambda>s. snd (f s))"
            using continuous_on_snd[OF hf_cont_on] unfolding comp_def .
          \<comment> \<open>F is continuous_on (work with explicit fst/snd form, then match case_prod).\<close>
          let ?F' = "\<lambda>p::real\<times>real. ((1 - snd p) * fst (f (fst p)) + snd p * fst x0,
                                      (1 - snd p) * snd (f (fst p)) + snd p * snd x0)"
          have hf_fst_co: "continuous_on (I_set \<times> I_set) (\<lambda>p. f (fst p))"
            by (rule continuous_on_compose2[OF hf_cont_on continuous_on_fst]) (by100 auto)
          have hF'_co: "continuous_on (I_set \<times> I_set) ?F'"
            by (intro continuous_on_Pair continuous_on_add continuous_on_mult
                   continuous_on_diff continuous_on_const continuous_on_fst continuous_on_snd
                   continuous_on_id hf_fst_co)
          have hF_eq: "?F' = ?F" by (rule ext) (simp add: case_prod_beta)
          have hF_co: "continuous_on (I_set \<times> I_set) ?F" using hF'_co unfolding hF_eq .
          \<comment> \<open>Range in I_set \<times> I_set (convexity).\<close>
          have hF_range: "\<And>p. p \<in> I_set \<times> I_set \<Longrightarrow> ?F p \<in> I_set \<times> I_set"
          proof -
            fix p :: "real \<times> real" assume hp: "p \<in> I_set \<times> I_set"
            have ht': "0 \<le> snd p" "snd p \<le> 1" using hp unfolding top1_unit_interval_def by (by100 auto)+
            have h0t: "0 \<le> 1 - snd p" using ht' by (by100 linarith)
            have hfs: "f (fst p) \<in> I_set \<times> I_set" using hfr hp by (by100 auto)
            have hfa: "0 \<le> fst (f (fst p))" "fst (f (fst p)) \<le> 1" using hfs unfolding top1_unit_interval_def by auto+
            have hfb: "0 \<le> snd (f (fst p))" "snd (f (fst p)) \<le> 1" using hfs unfolding top1_unit_interval_def by (by100 auto)+
            have hxa: "0 \<le> fst x0" "fst x0 \<le> 1" using hx0 unfolding top1_unit_interval_def by (by100 auto)+
            have hxb: "0 \<le> snd x0" "snd x0 \<le> 1" using hx0 unfolding top1_unit_interval_def by (by100 auto)+
            have "0 \<le> (1 - snd p) * fst (f (fst p)) + snd p * fst x0"
              using mult_nonneg_nonneg[OF h0t hfa(1)] mult_nonneg_nonneg[OF ht'(1) hxa(1)]
              by (by100 linarith)
            moreover have "(1 - snd p) * fst (f (fst p)) + snd p * fst x0 \<le> 1"
              by (rule convex_bound_le[OF hfa(2) hxa(2) h0t ht'(1)]) (by100 simp)
            moreover have "0 \<le> (1 - snd p) * snd (f (fst p)) + snd p * snd x0"
              using mult_nonneg_nonneg[OF h0t hfb(1)] mult_nonneg_nonneg[OF ht'(1) hxb(1)]
              by (by100 linarith)
            moreover have "(1 - snd p) * snd (f (fst p)) + snd p * snd x0 \<le> 1"
              by (rule convex_bound_le[OF hfb(2) hxb(2) h0t ht'(1)]) (by100 simp)
            ultimately show "?F p \<in> I_set \<times> I_set"
              unfolding top1_unit_interval_def by (simp add: case_prod_beta)
          qed
          \<comment> \<open>Transfer via subspace topology bridge.\<close>
          have "top1_continuous_map_on (I_set \<times> I_set)
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set))
            (I_set \<times> I_set)
            (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (I_set \<times> I_set)) ?F"
            by (rule top1_continuous_map_on_real2_subspace_general[OF hF_range hF_co])
          thus ?thesis unfolding II_topology_def II_topology_eq_subspace .
        qed
        have hF0: "\<forall>s\<in>I_set. ?F (s, 0) = f s"
          by (auto simp: prod_eq_iff)
        have hF1: "\<forall>s\<in>I_set. ?F (s, 1) = x0"
          by (auto simp: prod_eq_iff)
        have hf0: "f 0 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        have hf1: "f 1 = x0" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
        have hFl: "\<forall>t\<in>I_set. ?F (0, t) = x0"
          using hf0 by (auto simp: prod_eq_iff algebra_simps)
        have hFr: "\<forall>t\<in>I_set. ?F (1, t) = x0"
          using hf1 by (auto simp: prod_eq_iff algebra_simps)
        have hf_path: "top1_is_path_on (I_set \<times> I_set) II_topology x0 x0 f"
          using hf unfolding top1_is_loop_on_def by (by100 blast)
        have hconst_path: "top1_is_path_on (I_set \<times> I_set) II_topology x0 x0 (top1_constant_path x0)"
          by (rule top1_constant_path_is_path[OF hTII' hx0])
        have hF1': "\<forall>s\<in>I_set. ?F (s, 1) = top1_constant_path x0 s"
          using hF1 by (simp add: top1_constant_path_value)
        show "top1_path_homotopic_on (I_set \<times> I_set) II_topology x0 x0 f (top1_constant_path x0)"
          unfolding top1_path_homotopic_on_def
          using hf_path hconst_path hF_cont hF0 hF1' hFl hFr by (by100 blast)
      qed
    qed
    have h00: "(0::real, 0::real) \<in> I_set \<times> I_set"
      unfolding top1_unit_interval_def by (by100 simp)
    have h0I: "(0::real) \<in> I_set" and h1I: "(1::real) \<in> I_set"
      unfolding top1_unit_interval_def by (by100 simp)+
    have hTII: "is_topology_on (I_set \<times> I_set) II_topology"
      unfolding II_topology_def
      by (rule product_topology_on_is_topology_on[OF
            top1_unit_interval_topology_is_topology_on top1_unit_interval_topology_is_topology_on])
    have hbot_cont: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology ?bottom"
      by (rule pair_s_const_continuous[OF h0I])
    have hright_cont: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology ?right"
      by (rule pair_const_t_continuous[OF h1I])
    have hleft_cont: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology ?left'"
      by (rule pair_const_t_continuous[OF h0I])
    have htop_cont: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology ?top'"
      by (rule pair_s_const_continuous[OF h1I])
    have hbot_path: "top1_is_path_on (I_set \<times> I_set) II_topology (0, 0) (1, 0) ?bottom"
      unfolding top1_is_path_on_def using hbot_cont by (by100 simp)
    have hright_path: "top1_is_path_on (I_set \<times> I_set) II_topology (1, 0) (1, 1) ?right"
      unfolding top1_is_path_on_def using hright_cont by (by100 simp)
    have hleft_path: "top1_is_path_on (I_set \<times> I_set) II_topology (0, 0) (0, 1) ?left'"
      unfolding top1_is_path_on_def using hleft_cont by (by100 simp)
    have htop_path: "top1_is_path_on (I_set \<times> I_set) II_topology (0, 1) (1, 1) ?top'"
      unfolding top1_is_path_on_def using htop_cont by (by100 simp)
    have h\<beta>1_path: "top1_is_path_on (I_set \<times> I_set) II_topology (0, 0) (1, 1) ?\<beta>1"
      by (rule top1_path_product_is_path[OF hTII hbot_path hright_path])
    have h\<beta>2_path: "top1_is_path_on (I_set \<times> I_set) II_topology (0, 0) (1, 1) ?\<beta>2"
      by (rule top1_path_product_is_path[OF hTII hleft_path htop_path])
    have h\<beta>_hom: "top1_path_homotopic_on (I_set \<times> I_set) II_topology (0, 0) (1, 1) ?\<beta>1 ?\<beta>2"
      by (rule simply_connected_paths_homotopic[OF hII_sc h\<beta>1_path h\<beta>2_path h00])
    \<comment> \<open>G∘β₁ = (h∘l)*α and G∘β₂ = α*(k∘l).\<close>
    have hG\<beta>1: "\<forall>s\<in>I_set. (?G \<circ> ?\<beta>1) s = top1_path_product (h \<circ> l) ?\<alpha> s"
    proof (intro ballI)
      fix s :: real assume hs: "s \<in> I_set"
      show "(?G \<circ> ?\<beta>1) s = top1_path_product (h \<circ> l) ?\<alpha> s"
      proof (cases "s \<le> 1/2")
        case True
        have "(?G \<circ> ?\<beta>1) s = ?G (2*s, 0)"
          unfolding comp_def top1_path_product_def top1_unit_interval_def using True hs by auto
        also have "\<dots> = H (l (2*s), 0)" by simp
        also have "\<dots> = h (l (2*s))"
        proof -
          have "2*s \<in> I_set" using hs True unfolding top1_unit_interval_def by auto
          thus ?thesis using hG_bot by simp
        qed
        also have "\<dots> = (h \<circ> l) (2*s)" by simp
        also have "\<dots> = top1_path_product (h \<circ> l) ?\<alpha> s"
          unfolding top1_path_product_def using True by simp
        finally show ?thesis .
      next
        case False
        have hs_ge: "s > 1/2" using False by linarith
        have h2s1_I: "2 * s - 1 \<in> I_set"
          using hs hs_ge unfolding top1_unit_interval_def by auto
        have hLHS: "(?G \<circ> ?\<beta>1) s = H (x0, 2*s - 1)"
          unfolding comp_def top1_path_product_def top1_unit_interval_def using hs_ge hs hl1 by auto
        have hRHS: "top1_path_product (h \<circ> l) ?\<alpha> s = H (x0, 2*s - 1)"
          unfolding top1_path_product_def using hs_ge by simp
        show ?thesis using hLHS hRHS by simp
      qed
    qed
    have hG\<beta>2: "\<forall>s\<in>I_set. (?G \<circ> ?\<beta>2) s = top1_path_product ?\<alpha> (k \<circ> l) s"
    proof (intro ballI)
      fix s :: real assume hs: "s \<in> I_set"
      show "(?G \<circ> ?\<beta>2) s = top1_path_product ?\<alpha> (k \<circ> l) s"
      proof (cases "s \<le> 1/2")
        case True
        thus ?thesis unfolding comp_def top1_path_product_def case_prod_beta top1_unit_interval_def
          using hG_left hs hl0 by (by100 auto)
      next
        case False
        have hs_ge: "s > 1/2" using False by (by100 linarith)
        have h2s1_I: "2 * s - 1 \<in> I_set"
          using hs hs_ge unfolding top1_unit_interval_def by (by100 auto)
        have "(?G \<circ> ?\<beta>2) s = ?G (2*s - 1, 1)"
          unfolding comp_def top1_path_product_def case_prod_beta top1_unit_interval_def
          using hs_ge hs by (by100 auto)
        also have "\<dots> = (k \<circ> l) (2*s - 1)"
          using hG_top h2s1_I by (by100 simp)
        also have "\<dots> = top1_path_product ?\<alpha> (k \<circ> l) s"
          unfolding top1_path_product_def top1_unit_interval_def comp_def
          using hs_ge by simp
        finally show ?thesis .
      qed
    qed
    \<comment> \<open>G preserves homotopy: G∘β₁ ≃ G∘β₂.\<close>
    have "top1_path_homotopic_on Y TY (?G (0, 0)) (?G (1, 1))
        (?G \<circ> ?\<beta>1) (?G \<circ> ?\<beta>2)"
      by (rule continuous_preserves_path_homotopic[OF
            product_topology_on_is_topology_on[OF
              top1_unit_interval_topology_is_topology_on
              top1_unit_interval_topology_is_topology_on,
              unfolded II_topology_def[symmetric]]
            hTY hG_cont h\<beta>_hom])
    \<comment> \<open>?G(0,0) = H(x₀,0) = h(x₀), ?G(1,1) = H(x₀,1) = k(x₀).\<close>
    hence hGhom: "top1_path_homotopic_on Y TY (h x0) (k x0) (?G \<circ> ?\<beta>1) (?G \<circ> ?\<beta>2)"
      using hH0 hH1 hx0 hl0 hl1 by (by100 simp)
    \<comment> \<open>Transfer via agreement on I: G∘β₁ agrees with (h∘l)*α, etc.\<close>
    show ?thesis unfolding top1_path_homotopic_on_def
    proof -
      from hGhom obtain F where
          hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY F"
          and hF0: "\<forall>s\<in>I_set. F (s, 0) = (?G \<circ> ?\<beta>1) s"
          and hF1: "\<forall>s\<in>I_set. F (s, 1) = (?G \<circ> ?\<beta>2) s"
          and hFl: "\<forall>t\<in>I_set. F (0, t) = h x0"
          and hFr: "\<forall>t\<in>I_set. F (1, t) = k x0"
      proof -
        obtain F' where hF': "top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY F'"
            "\<forall>s\<in>I_set. F' (s, 0) = (?G \<circ> ?\<beta>1) s" "\<forall>s\<in>I_set. F' (s, 1) = (?G \<circ> ?\<beta>2) s"
            "\<forall>t\<in>I_set. F' (0, t) = h x0" "\<forall>t\<in>I_set. F' (1, t) = k x0"
          using hGhom unfolding top1_path_homotopic_on_def by auto
        show ?thesis by (rule that[OF hF'(1) hF'(2) hF'(3) hF'(4) hF'(5)])
      qed
      have hF0': "\<forall>s\<in>I_set. F (s, 0) = top1_path_product (h \<circ> l) ?\<alpha> s"
        using hF0 hG\<beta>1 by (by100 simp)
      have hF1': "\<forall>s\<in>I_set. F (s, 1) = top1_path_product ?\<alpha> (k \<circ> l) s"
        using hF1 hG\<beta>2 by (by100 simp)
      show "top1_is_path_on Y TY (h x0) (k x0) (top1_path_product (h \<circ> l) ?\<alpha>)
          \<and> top1_is_path_on Y TY (h x0) (k x0) (top1_path_product ?\<alpha> (k \<circ> l))
          \<and> (\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY F
              \<and> (\<forall>s\<in>I_set. F (s, 0) = top1_path_product (h \<circ> l) ?\<alpha> s)
              \<and> (\<forall>s\<in>I_set. F (s, 1) = top1_path_product ?\<alpha> (k \<circ> l) s)
              \<and> (\<forall>t\<in>I_set. F (0, t) = h x0)
              \<and> (\<forall>t\<in>I_set. F (1, t) = k x0))"
      proof (intro conjI)
        \<comment> \<open>is_path_on for path products: follows from G∘β being paths + pointwise agreement.\<close>
        have hGb1_path: "top1_is_path_on Y TY (h x0) (k x0) (?G \<circ> ?\<beta>1)"
          using hGhom unfolding top1_path_homotopic_on_def by (by100 blast)
        have hGb2_path: "top1_is_path_on Y TY (h x0) (k x0) (?G \<circ> ?\<beta>2)"
          using hGhom unfolding top1_path_homotopic_on_def by (by100 blast)
        have hGb1_cont: "top1_continuous_map_on I_set I_top Y TY (?G \<circ> ?\<beta>1)"
          using hGb1_path unfolding top1_is_path_on_def by (by100 blast)
        have hGb2_cont: "top1_continuous_map_on I_set I_top Y TY (?G \<circ> ?\<beta>2)"
          using hGb2_path unfolding top1_is_path_on_def by (by100 blast)
        have hprod1_cont: "top1_continuous_map_on I_set I_top Y TY (top1_path_product (h \<circ> l) ?\<alpha>)"
          by (rule top1_continuous_map_on_agree'[OF hGb1_cont hG\<beta>1])
        have hprod2_cont: "top1_continuous_map_on I_set I_top Y TY (top1_path_product ?\<alpha> (k \<circ> l))"
          by (rule top1_continuous_map_on_agree'[OF hGb2_cont hG\<beta>2])
        show "top1_is_path_on Y TY (h x0) (k x0) (top1_path_product (h \<circ> l) ?\<alpha>)"
          using hGb1_path hG\<beta>1 hprod1_cont unfolding top1_is_path_on_def
          by (simp add: hl0 hl1 top1_path_product_at_end top1_path_product_at_start)
        show "top1_is_path_on Y TY (h x0) (k x0) (top1_path_product ?\<alpha> (k \<circ> l))"
          using hGb2_path hG\<beta>2 hprod2_cont unfolding top1_is_path_on_def
          by (simp add: hH0 hl1 hx0 top1_path_product_at_end top1_path_product_at_start)
        show "\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology Y TY F
            \<and> (\<forall>s\<in>I_set. F (s, 0) = top1_path_product (h \<circ> l) ?\<alpha> s)
            \<and> (\<forall>s\<in>I_set. F (s, 1) = top1_path_product ?\<alpha> (k \<circ> l) s)
            \<and> (\<forall>t\<in>I_set. F (0, t) = h x0)
            \<and> (\<forall>t\<in>I_set. F (1, t) = k x0)"
          using hF hF0' hF1' hFl hFr by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Step 3: From (h\<circ>l)*\<alpha> \<simeq> \<alpha>*(k\<circ>l), derive h\<circ>l \<simeq> \<alpha>⁻¹*(k\<circ>l)*\<alpha>.\<close>
  have h0I': "(0::real) \<in> I_set" and h1I': "(1::real) \<in> I_set"
    unfolding top1_unit_interval_def by (by100 simp)+
  \<comment> \<open>First establish \<alpha> is a path h(x0) \<rightarrow> k(x0), using G restricted to s=0.\<close>
  have h\<alpha>_cont: "top1_continuous_map_on I_set I_top Y TY ?\<alpha>"
  proof -
    have "top1_continuous_map_on I_set I_top Y TY (?G \<circ> (\<lambda>t. (0::real, t)))"
      by (rule top1_continuous_map_on_comp[OF pair_const_t_continuous[OF h0I'] hG_cont])
    moreover have "\<forall>t\<in>I_set. (?G \<circ> (\<lambda>t. (0, t))) t = ?\<alpha> t"
      using hG_left by (by100 auto)
    ultimately show ?thesis by (rule top1_continuous_map_on_agree')
  qed
  have h\<alpha>_path: "top1_is_path_on Y TY (h x0) (k x0) ?\<alpha>"
    unfolding top1_is_path_on_def using h\<alpha>_cont hH0 hH1 hx0 by (by100 auto)
  have hrev\<alpha>_path: "top1_is_path_on Y TY (k x0) (h x0) (top1_path_reverse ?\<alpha>)"
    by (rule top1_path_reverse_is_path[OF h\<alpha>_path])
  \<comment> \<open>h\<circ>l is a loop at h(x0): via G restricted to t=0.\<close>
  have hhl_cont: "top1_continuous_map_on I_set I_top Y TY (h \<circ> l)"
  proof -
    have "top1_continuous_map_on I_set I_top Y TY (?G \<circ> (\<lambda>s. (s, 0::real)))"
      by (rule top1_continuous_map_on_comp[OF pair_s_const_continuous[OF h0I'] hG_cont])
    moreover have "\<forall>s\<in>I_set. (?G \<circ> (\<lambda>s. (s, 0))) s = (h \<circ> l) s"
      using hG_bot by (by100 auto)
    ultimately show ?thesis by (rule top1_continuous_map_on_agree')
  qed
  have hhl_loop: "top1_is_loop_on Y TY (h x0) (h \<circ> l)"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hhl_cont hl0 hl1 by (by100 auto)
  have hhl_path: "top1_is_path_on Y TY (h x0) (h x0) (h \<circ> l)"
    using hhl_loop unfolding top1_is_loop_on_def by blast
  \<comment> \<open>k\<circ>l is a loop at k(x0): via G restricted to t=1.\<close>
  have hkl_cont: "top1_continuous_map_on I_set I_top Y TY (k \<circ> l)"
  proof -
    have "top1_continuous_map_on I_set I_top Y TY (?G \<circ> (\<lambda>s. (s, 1::real)))"
      by (rule top1_continuous_map_on_comp[OF pair_s_const_continuous[OF h1I'] hG_cont])
    moreover have "\<forall>s\<in>I_set. (?G \<circ> (\<lambda>s. (s, 1))) s = (k \<circ> l) s"
      using hG_top by (by100 auto)
    ultimately show ?thesis by (rule top1_continuous_map_on_agree')
  qed
  have hkl_loop: "top1_is_loop_on Y TY (k x0) (k \<circ> l)"
    unfolding top1_is_loop_on_def top1_is_path_on_def
    using hkl_cont hl0 hl1 by (by100 auto)
  have hkl_path: "top1_is_path_on Y TY (k x0) (k x0) (k \<circ> l)"
    using hkl_loop unfolding top1_is_loop_on_def by blast
  \<comment> \<open>Path algebra chain: h\<circ>l \<simeq> \<alpha>*((k\<circ>l)*(rev \<alpha>)).\<close>
  \<comment> \<open>(1) Right-compose hprod_hom with rev \<alpha>.\<close>
  have pa1: "top1_path_homotopic_on Y TY (h x0) (h x0)
    (top1_path_product (top1_path_product (h \<circ> l) ?\<alpha>) (top1_path_reverse ?\<alpha>))
    (top1_path_product (top1_path_product ?\<alpha> (k \<circ> l)) (top1_path_reverse ?\<alpha>))"
    by (rule path_homotopic_product_left[OF hTY hprod_hom hrev\<alpha>_path])
  \<comment> \<open>(2) Associativity: (h\<circ>l)*(\<alpha>*(rev\<alpha>)) \<simeq> ((h\<circ>l)*\<alpha>)*(rev\<alpha>).\<close>
  have pa2: "top1_path_homotopic_on Y TY (h x0) (h x0)
    (top1_path_product (h \<circ> l) (top1_path_product ?\<alpha> (top1_path_reverse ?\<alpha>)))
    (top1_path_product (top1_path_product (h \<circ> l) ?\<alpha>) (top1_path_reverse ?\<alpha>))"
    by (rule Theorem_51_2_associativity[OF hTY hhl_path h\<alpha>_path hrev\<alpha>_path])
  \<comment> \<open>(3) \<alpha>*(rev\<alpha>) \<simeq> const_{h(x0)}.\<close>
  have pa3: "top1_path_homotopic_on Y TY (h x0) (h x0)
    (top1_path_product ?\<alpha> (top1_path_reverse ?\<alpha>)) (top1_constant_path (h x0))"
    by (rule Theorem_51_2_invgerse_left[OF hTY h\<alpha>_path])
  \<comment> \<open>(4) (h\<circ>l)*(\<alpha>*(rev\<alpha>)) \<simeq> (h\<circ>l)*const (right product).\<close>
  have pa4: "top1_path_homotopic_on Y TY (h x0) (h x0)
    (top1_path_product (h \<circ> l) (top1_path_product ?\<alpha> (top1_path_reverse ?\<alpha>)))
    (top1_path_product (h \<circ> l) (top1_constant_path (h x0)))"
    by (rule path_homotopic_product_right[OF hTY pa3 hhl_path])
  \<comment> \<open>(5) (h\<circ>l)*const \<simeq> h\<circ>l (right identity).\<close>
  have pa5: "top1_path_homotopic_on Y TY (h x0) (h x0)
    (top1_path_product (h \<circ> l) (top1_constant_path (h x0))) (h \<circ> l)"
    by (rule Theorem_51_2_right_identity[OF hTY hhl_path])
  \<comment> \<open>(6) Associativity on right: \<alpha>*((k\<circ>l)*(rev\<alpha>)) \<simeq> (\<alpha>*(k\<circ>l))*(rev\<alpha>).\<close>
  have pa6: "top1_path_homotopic_on Y TY (h x0) (h x0)
    (top1_path_product ?\<alpha> (top1_path_product (k \<circ> l) (top1_path_reverse ?\<alpha>)))
    (top1_path_product (top1_path_product ?\<alpha> (k \<circ> l)) (top1_path_reverse ?\<alpha>))"
    by (rule Theorem_51_2_associativity[OF hTY h\<alpha>_path hkl_path hrev\<alpha>_path])
  \<comment> \<open>Chain by transitivity: h\<circ>l \<simeq> (h\<circ>l)*const (pa5 sym)
     \<simeq> (h\<circ>l)*(\<alpha>*(rev\<alpha>)) (pa4 sym) \<simeq> ((h\<circ>l)*\<alpha>)*(rev\<alpha>) (pa2)
     \<simeq> (\<alpha>*(k\<circ>l))*(rev\<alpha>) (pa1) \<simeq> \<alpha>*((k\<circ>l)*(rev\<alpha>)) (pa6 sym).\<close>
  have c1: "top1_path_homotopic_on Y TY (h x0) (h x0) (h \<circ> l)
    (top1_path_product (h \<circ> l) (top1_constant_path (h x0)))"
    by (rule Lemma_51_1_path_homotopic_sym[OF pa5])
  have c2: "top1_path_homotopic_on Y TY (h x0) (h x0) (h \<circ> l)
    (top1_path_product (h \<circ> l) (top1_path_product ?\<alpha> (top1_path_reverse ?\<alpha>)))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTY c1
          Lemma_51_1_path_homotopic_sym[OF pa4]])
  have c3: "top1_path_homotopic_on Y TY (h x0) (h x0) (h \<circ> l)
    (top1_path_product (top1_path_product (h \<circ> l) ?\<alpha>) (top1_path_reverse ?\<alpha>))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTY c2 pa2])
  have c4: "top1_path_homotopic_on Y TY (h x0) (h x0) (h \<circ> l)
    (top1_path_product (top1_path_product ?\<alpha> (k \<circ> l)) (top1_path_reverse ?\<alpha>))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTY c3 pa1])
  have c5: "top1_path_homotopic_on Y TY (h x0) (h x0) (h \<circ> l)
    (top1_path_product ?\<alpha> (top1_path_product (k \<circ> l) (top1_path_reverse ?\<alpha>)))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTY c4
          Lemma_51_1_path_homotopic_sym[OF pa6]])
  \<comment> \<open>rev(rev \<alpha>) = \<alpha>, so target = \<alpha>*((k\<circ>l)*(rev \<alpha>)).\<close>
  have htarget_eq: "top1_basepoint_change_on Y TY (k x0) (h x0) (top1_path_reverse ?\<alpha>) (k \<circ> l)
    = top1_path_product ?\<alpha> (top1_path_product (k \<circ> l) (top1_path_reverse ?\<alpha>))"
    unfolding top1_basepoint_change_on_def top1_path_reverse_twice by (rule refl)
  \<comment> \<open>The target is a loop (path from h(x0) to h(x0)).\<close>
  have hkl_rev\<alpha>_path: "top1_is_path_on Y TY (k x0) (h x0)
    (top1_path_product (k \<circ> l) (top1_path_reverse ?\<alpha>))"
    by (rule top1_path_product_is_path[OF hTY hkl_path hrev\<alpha>_path])
  have htarget_path: "top1_is_path_on Y TY (h x0) (h x0)
    (top1_path_product ?\<alpha> (top1_path_product (k \<circ> l) (top1_path_reverse ?\<alpha>)))"
    by (rule top1_path_product_is_path[OF hTY h\<alpha>_path hkl_rev\<alpha>_path])
  have htarget_loop: "top1_is_loop_on Y TY (h x0)
    (top1_basepoint_change_on Y TY (k x0) (h x0) (top1_path_reverse ?\<alpha>) (k \<circ> l))"
    unfolding top1_is_loop_on_def htarget_eq using htarget_path by blast
  show ?thesis unfolding top1_loop_equiv_on_def
    using hhl_loop htarget_loop c5[unfolded htarget_eq[symmetric]] by blast
qed


text \<open>Double basepoint change = single basepoint change along composed path.\<close>
lemma double_basepoint_change_equiv:
  assumes hTX: "is_topology_on X TX"
      and halpha: "top1_is_path_on X TX x1 x2 alpha"
      and hbeta: "top1_is_path_on X TX x0 x1 beta"
      and hf: "top1_is_loop_on X TX x0 f"
  shows "top1_loop_equiv_on X TX x2
    (top1_basepoint_change_on X TX x1 x2 alpha
      (top1_basepoint_change_on X TX x0 x1 beta f))
    (top1_basepoint_change_on X TX x0 x2
      (top1_path_product beta alpha) f)"
proof -
  let ?ra = "top1_path_reverse alpha" and ?rb = "top1_path_reverse beta"
  let ?ba = "top1_path_product beta alpha"
  let ?fp = "top1_is_path_on X TX"
  have hfp: "?fp x0 x0 f" using hf unfolding top1_is_loop_on_def .
  have hra: "?fp x2 x1 ?ra" by (rule top1_path_reverse_is_path[OF halpha])
  have hrb: "?fp x1 x0 ?rb" by (rule top1_path_reverse_is_path[OF hbeta])
  have hba: "?fp x0 x2 ?ba" by (rule top1_path_product_is_path[OF hTX hbeta halpha])
  \<comment> \<open>rev(\<beta>*\<alpha>) = rev(\<alpha>) * rev(\<beta>) (definitional equality).\<close>
  have ha0: "alpha 0 = x1" and ha1: "alpha 1 = x2"
    using halpha unfolding top1_is_path_on_def by (by100 blast)+
  have hb0: "beta 0 = x0" and hb1: "beta 1 = x1"
    using hbeta unfolding top1_is_path_on_def by (by100 blast)+
  have hrev_prod: "top1_path_reverse ?ba = top1_path_product ?ra ?rb"
  proof (rule ext)
    fix s :: real
    show "top1_path_reverse ?ba s = top1_path_product ?ra ?rb s"
      unfolding top1_path_reverse_def top1_path_product_def
      using ha0 hb1 by (simp add: field_simps)
  qed
  \<comment> \<open>Unfold basepoint_change_on_def.\<close>
  have hlhs_eq: "top1_basepoint_change_on X TX x1 x2 alpha
      (top1_basepoint_change_on X TX x0 x1 beta f)
    = top1_path_product ?ra (top1_path_product
        (top1_path_product ?rb (top1_path_product f beta)) alpha)"
    unfolding top1_basepoint_change_on_def by (rule refl)
  have hrhs_eq: "top1_basepoint_change_on X TX x0 x2 ?ba f
    = top1_path_product (top1_path_product ?ra ?rb) (top1_path_product f ?ba)"
    unfolding top1_basepoint_change_on_def hrev_prod by (rule refl)
  \<comment> \<open>Both sides are path-homotopic via repeated associativity:
     ra * ((rb * (f * \<beta>)) * \<alpha>) \<simeq> (ra * rb) * (f * (\<beta> * \<alpha>)).\<close>
  \<comment> \<open>Path facts for associativity.\<close>
  have hfb: "?fp x0 x1 (top1_path_product f beta)"
    by (rule top1_path_product_is_path[OF hTX hfp hbeta])
  have hfba: "?fp x0 x2 (top1_path_product f ?ba)"
    by (rule top1_path_product_is_path[OF hTX hfp hba])
  have hrb_fba: "?fp x1 x2 (top1_path_product ?rb (top1_path_product f ?ba))"
    by (rule top1_path_product_is_path[OF hTX hrb hfba])
  \<comment> \<open>Step 1: (rb*(f*\<beta>))*\<alpha> \<simeq> rb*((f*\<beta>)*\<alpha>) [sym of assoc].\<close>
  have s1: "top1_path_homotopic_on X TX x1 x2
    (top1_path_product (top1_path_product ?rb (top1_path_product f beta)) alpha)
    (top1_path_product ?rb (top1_path_product (top1_path_product f beta) alpha))"
    by (rule Lemma_51_1_path_homotopic_sym[OF
          Theorem_51_2_associativity[OF hTX hrb hfb halpha]])
  \<comment> \<open>Step 2: (f*\<beta>)*\<alpha> \<simeq> f*(\<beta>*\<alpha>) [sym of assoc].\<close>
  have s2: "top1_path_homotopic_on X TX x0 x2
    (top1_path_product (top1_path_product f beta) alpha)
    (top1_path_product f ?ba)"
    by (rule Lemma_51_1_path_homotopic_sym[OF
          Theorem_51_2_associativity[OF hTX hfp hbeta halpha]])
  \<comment> \<open>Lift step 2 through rb: rb*((f*\<beta>)*\<alpha>) \<simeq> rb*(f*(\<beta>*\<alpha>)).\<close>
  have s2': "top1_path_homotopic_on X TX x1 x2
    (top1_path_product ?rb (top1_path_product (top1_path_product f beta) alpha))
    (top1_path_product ?rb (top1_path_product f ?ba))"
    by (rule path_homotopic_product_right[OF hTX s2 hrb])
  \<comment> \<open>Combine steps 1+2: (rb*(f*\<beta>))*\<alpha> \<simeq> rb*(f*ba).\<close>
  have s12: "top1_path_homotopic_on X TX x1 x2
    (top1_path_product (top1_path_product ?rb (top1_path_product f beta)) alpha)
    (top1_path_product ?rb (top1_path_product f ?ba))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX s1 s2'])
  \<comment> \<open>Lift s12 through ra: ra*((rb*(f*\<beta>))*\<alpha>) \<simeq> ra*(rb*(f*ba)).\<close>
  have s12': "top1_path_homotopic_on X TX x2 x2
    (top1_path_product ?ra (top1_path_product (top1_path_product ?rb (top1_path_product f beta)) alpha))
    (top1_path_product ?ra (top1_path_product ?rb (top1_path_product f ?ba)))"
    by (rule path_homotopic_product_right[OF hTX s12 hra])
  \<comment> \<open>Step 3: ra*(rb*(f*ba)) \<simeq> (ra*rb)*(f*ba) [assoc].\<close>
  have s3: "top1_path_homotopic_on X TX x2 x2
    (top1_path_product ?ra (top1_path_product ?rb (top1_path_product f ?ba)))
    (top1_path_product (top1_path_product ?ra ?rb) (top1_path_product f ?ba))"
    by (rule Theorem_51_2_associativity[OF hTX hra hrb hfba])
  \<comment> \<open>Full chain: LHS \<simeq> RHS.\<close>
  have hchain: "top1_path_homotopic_on X TX x2 x2
    (top1_path_product ?ra (top1_path_product (top1_path_product ?rb (top1_path_product f beta)) alpha))
    (top1_path_product (top1_path_product ?ra ?rb) (top1_path_product f ?ba))"
    by (rule Lemma_51_1_path_homotopic_trans[OF hTX s12' s3])
  have hbc_bf: "top1_is_loop_on X TX x1 (top1_basepoint_change_on X TX x0 x1 beta f)"
    by (rule top1_basepoint_change_is_loop[OF hTX hbeta hf])
  have hlhs_loop: "top1_is_loop_on X TX x2
    (top1_basepoint_change_on X TX x1 x2 alpha (top1_basepoint_change_on X TX x0 x1 beta f))"
    by (rule top1_basepoint_change_is_loop[OF hTX halpha hbc_bf])
  have hrhs_loop: "top1_is_loop_on X TX x2
    (top1_basepoint_change_on X TX x0 x2 ?ba f)"
    by (rule top1_basepoint_change_is_loop[OF hTX hba hf])
  have hchain': "top1_path_homotopic_on X TX x2 x2
    (top1_basepoint_change_on X TX x1 x2 alpha (top1_basepoint_change_on X TX x0 x1 beta f))
    (top1_basepoint_change_on X TX x0 x2 ?ba f)"
    using hchain unfolding hlhs_eq hrhs_eq .
  show ?thesis unfolding top1_loop_equiv_on_def
    using hlhs_loop hrhs_loop hchain' by (by100 blast)
qed

section \<open>\<S>57 The Borsuk-Ulam Theorem\<close>

text \<open>Antipode-preserving map on the plane: h(-x) = -h(x) pointwise.\<close>
definition top1_antipode_preserving_S1 :: "(real \<times> real \<Rightarrow> real \<times> real) \<Rightarrow> bool" where
  "top1_antipode_preserving_S1 h \<longleftrightarrow>
     (\<forall>x y. h (-x, -y) = (- fst (h (x, y)), - snd (h (x, y))))"

text \<open>General version: if g: X \<rightarrow> Y is continuous, nulhomotopic, g(x0) = y0,
  and f is a loop at x0 in X, then g \<circ> f \<simeq> const_{y0} in Y.\<close>
lemma nulhomotopic_trivializes_loops_general:
  assumes hTX: "is_topology_on X TX" and hTY: "is_topology_on Y TY"
      and hg: "top1_continuous_map_on X TX Y TY g"
      and hgnul: "top1_nulhomotopic_on X TX Y TY g"
      and hgx0: "g x0 = y0" and hx0: "x0 \<in> X"
      and hf: "top1_is_loop_on X TX x0 f"
  shows "top1_path_homotopic_on Y TY y0 y0 (g \<circ> f) (top1_constant_path y0)"
proof -
  obtain c where hcY: "c \<in> Y"
      and hhom: "top1_homotopic_on X TX Y TY g (\<lambda>_. c)"
    using hgnul unfolding top1_nulhomotopic_on_def by (by100 blast)
  obtain H where hHcont: "top1_continuous_map_on (X \<times> I_set)
          (product_topology_on TX I_top) Y TY H"
      and hH0: "\<forall>x\<in>X. H (x, 0) = g x"
      and hH1: "\<forall>x\<in>X. H (x, 1) = c"
    using hhom unfolding top1_homotopic_on_def by (by100 blast)
  have hH1': "\<forall>x\<in>X. H (x, 1) = (\<lambda>_. c) x" using hH1 by (by100 simp)
  note hbc = homotopy_induced_basepoint_change[OF hTX hTY hHcont hH0 hH1' hf hx0]
  have hbc': "top1_loop_equiv_on Y TY (g x0) (g \<circ> f)
      (top1_basepoint_change_on Y TY c (g x0)
         (top1_path_reverse (\<lambda>t. H (x0, t))) (top1_constant_path c))"
  proof -
    have "(\<lambda>_. c) \<circ> f = top1_constant_path c"
      by (rule ext) (simp add: top1_constant_path_def comp_def)
    thus ?thesis using hbc by simp
  qed
  \<comment> \<open>Path algebra: bc(rev(\<alpha>), const_c) \<simeq> const_{g(x0)}. Same as nulhomotopic_trivializes_loops.\<close>
  \<comment> \<open>Path algebra: show bc(rev(\<alpha>), const_c) \<simeq> const_{g(x0)}.\<close>
  let ?\<alpha> = "\<lambda>t. H (x0, t)"
  have h\<alpha>_path: "top1_is_path_on Y TY (g x0) c ?\<alpha>"
  proof -
    have hTI: "is_topology_on I_set I_top" by (rule top1_unit_interval_topology_is_topology_on)
    have hp1: "pi1 \<circ> (\<lambda>t. (x0, t)) = (\<lambda>_. x0)" unfolding pi1_def by (rule ext) simp
    have hp2: "pi2 \<circ> (\<lambda>t. (x0, t)) = id" unfolding pi2_def by (rule ext) simp
    have hpair: "top1_continuous_map_on I_set I_top (X \<times> I_set) (product_topology_on TX I_top) (\<lambda>t. (x0, t))"
      using iffD2[OF Theorem_18_4[OF hTI hTX hTI]]
            top1_continuous_map_on_const[OF hTI hTX hx0, folded hp1]
            top1_continuous_map_on_id[OF hTI, folded hp2] by (by100 blast)
    have h\<alpha>_cont: "top1_continuous_map_on I_set I_top Y TY ?\<alpha>"
      using top1_continuous_map_on_comp[OF hpair hHcont] by (simp add: comp_def)
    show ?thesis unfolding top1_is_path_on_def using h\<alpha>_cont
      by (auto simp: hH0[rule_format, OF hx0] hH1[rule_format, OF hx0])
  qed
  have hra: "top1_is_path_on Y TY c (g x0) (top1_path_reverse ?\<alpha>)"
    by (rule top1_path_reverse_is_path[OF h\<alpha>_path])
  have hconst_c: "top1_is_loop_on Y TY c (top1_constant_path c)"
    by (rule top1_constant_path_is_loop[OF hTY hcY])
  have hbc_def: "top1_basepoint_change_on Y TY c (g x0)
      (top1_path_reverse ?\<alpha>) (top1_constant_path c)
    = top1_path_product ?\<alpha> (top1_path_product (top1_constant_path c) (top1_path_reverse ?\<alpha>))"
    unfolding top1_basepoint_change_on_def top1_path_reverse_twice by (rule refl)
  have hchain: "top1_path_homotopic_on Y TY (g x0) (g x0)
      (top1_basepoint_change_on Y TY c (g x0)
         (top1_path_reverse ?\<alpha>) (top1_constant_path c))
      (top1_constant_path (g x0))"
    using Lemma_51_1_path_homotopic_trans[OF hTY
        path_homotopic_product_right[OF hTY Theorem_51_2_left_identity[OF hTY hra] h\<alpha>_path,
          unfolded hbc_def[symmetric]]
        Theorem_51_2_invgerse_left[OF hTY h\<alpha>_path]] .
  have hgx0_Y: "g x0 \<in> Y" using hg hx0 unfolding top1_continuous_map_on_def by (by100 blast)
  have hbc_is_const: "top1_loop_equiv_on Y TY (g x0)
      (top1_basepoint_change_on Y TY c (g x0) (top1_path_reverse ?\<alpha>) (top1_constant_path c))
      (top1_constant_path (g x0))"
    unfolding top1_loop_equiv_on_def
    using top1_basepoint_change_is_loop[OF hTY hra hconst_c]
          top1_constant_path_is_loop[OF hTY hgx0_Y]
          hchain by (by100 blast)
  have hresult: "top1_loop_equiv_on Y TY (g x0) (g \<circ> f)
      (top1_constant_path (g x0))"
    by (rule top1_loop_equiv_on_trans[OF hTY hbc' hbc_is_const])
  have "top1_path_homotopic_on Y TY (g x0) (g x0)
      (g \<circ> f) (top1_constant_path (g x0))"
    using hresult unfolding top1_loop_equiv_on_def by (by100 blast)
  thus ?thesis using hgx0 by simp
qed
section \<open>\<S>56 The Fundamental Theorem of Algebra\<close>

text \<open>Following Munkres' proof in 4 steps via the fundamental group of S^1:
  Step 1: f(z) = z^n on S^1 induces the "multiplication by n" homomorphism
          on pi_1(S^1), which is injective for n > 0.
  Step 2: g(z) = z^n as map S^1 -> R^2 - {0} is not nulhomotopic.
  Step 3: If |a_{n-1}| + ... + |a_0| < 1, the monic polynomial has a root in B^2.
  Step 4: General case by substitution x = cy with c large enough.\<close>

text \<open>Polymorphic subspace continuity transfer: if f is continuous_on UNIV
  and maps S to T, then f is top1_continuous_map_on with subspace topologies.\<close>
lemma top1_continuous_map_on_subspace_open_sets:
  assumes hmap: "\<And>x. x \<in> S \<Longrightarrow> f x \<in> T"
      and hcont: "continuous_on UNIV f"
  shows "top1_continuous_map_on S (subspace_topology UNIV top1_open_sets S)
                               T (subspace_topology UNIV top1_open_sets T) f"
proof -
  have h1: "\<forall>x\<in>S. f x \<in> T" using hmap by (by100 blast)
  have h2: "\<forall>V\<in>subspace_topology UNIV top1_open_sets T.
      {x \<in> S. f x \<in> V} \<in> subspace_topology UNIV top1_open_sets S"
  proof
    fix V assume "V \<in> subspace_topology UNIV top1_open_sets T"
    then obtain U where hUos: "U \<in> top1_open_sets" and hVeq: "V = T \<inter> U"
      unfolding subspace_topology_def by (by100 auto)
    have hUo: "open U" using hUos unfolding top1_open_sets_def by (by100 blast)
    have "open (f -` U \<inter> UNIV)"
      using iffD1[OF continuous_on_open_vimage[OF open_UNIV] hcont] hUo by (by100 blast)
    hence hWo: "open (f -` U)" by (by100 simp)
    have "{x \<in> S. f x \<in> V} = S \<inter> (f -` U)"
      unfolding hVeq using hmap by (by100 auto)
    moreover have "(f -` U) \<in> top1_open_sets"
      using hWo unfolding top1_open_sets_def by (by100 blast)
    ultimately show "{x \<in> S. f x \<in> V} \<in> subspace_topology UNIV top1_open_sets S"
      unfolding subspace_topology_def by (by100 blast)
  qed
  show ?thesis unfolding top1_continuous_map_on_def using h1 h2 by (by100 blast)
qed

text \<open>The complex unit circle.\<close>
definition top1_S1_complex :: "complex set" where
  "top1_S1_complex = {z. cmod z = 1}"

definition top1_S1_complex_topology :: "complex set set" where
  "top1_S1_complex_topology = subspace_topology UNIV top1_open_sets top1_S1_complex"

text \<open>The punctured complex plane C - {0}, same topology as ambient.\<close>
definition top1_C_minus_0 :: "complex set" where
  "top1_C_minus_0 = UNIV - {0}"

definition top1_C_minus_0_topology :: "complex set set" where
  "top1_C_minus_0_topology = subspace_topology UNIV top1_open_sets top1_C_minus_0"

(** Step 1: induced homomorphism of f(z) = z^n on S^1 is multiplication by n.

    Munkres' proof: the standard loop p_0(s) = e^{2\<pi>is} corresponds to 1 \<in> Z.
    Its image f \<circ> p_0(s) = e^{2\<pi>ins} lifts to s \<mapsto> ns, which corresponds to n.
    So f_* is multiplication by n on \<pi>_1(S^1, b_0) \<cong> Z, hence injective for n > 0.

    Here we only record the essential injectivity consequence: if two loops
    become path-homotopic after composition with z^n, then they were already
    path-homotopic. **)
\<comment> \<open>Helper: \<psi> = (Re, Im) is continuous S^1_complex \<rightarrow> S^1.\<close>
lemma psi_continuous_S1:
  "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
      top1_S1 top1_S1_topology (\<lambda>z. (Re z, Im z))"
proof -
  have h\<psi>_map: "\<And>z. z \<in> top1_S1_complex \<Longrightarrow> (Re z, Im z) \<in> top1_S1"
    unfolding top1_S1_complex_def top1_S1_def by (auto simp: cmod_def)
  have h\<psi>_cont_univ: "continuous_on UNIV (\<lambda>z::complex. (Re z, Im z))"
    by (intro continuous_intros)
  show ?thesis unfolding top1_continuous_map_on_def
  proof (intro conjI ballI)
    fix z assume "z \<in> top1_S1_complex" thus "(Re z, Im z) \<in> top1_S1" by (rule h\<psi>_map)
  next
    fix V assume hV: "V \<in> top1_S1_topology"
    then obtain W where hWo: "W \<in> product_topology_on (top1_open_sets::real set set) top1_open_sets"
        and hVeq: "V = top1_S1 \<inter> W"
      unfolding top1_S1_topology_def subspace_topology_def by auto
    have hWopen: "open W"
      using hWo product_topology_on_open_sets_real2 unfolding top1_open_sets_def by (by100 blast)
    have hpre_open: "open ((\<lambda>z::complex. (Re z, Im z)) -` W)"
    proof -
      have "open ((\<lambda>z::complex. (Re z, Im z)) -` W \<inter> UNIV)"
        using iffD1[OF continuous_on_open_vimage[OF open_UNIV] h\<psi>_cont_univ] hWopen by (by100 blast)
      thus ?thesis by simp
    qed
    have "{z \<in> top1_S1_complex. (Re z, Im z) \<in> V} =
        top1_S1_complex \<inter> ((\<lambda>z. (Re z, Im z)) -` W)"
      unfolding hVeq using h\<psi>_map by auto
    thus "{z \<in> top1_S1_complex. (Re z, Im z) \<in> V} \<in> top1_S1_complex_topology"
      unfolding top1_S1_complex_topology_def subspace_topology_def
      using hpre_open unfolding top1_open_sets_def by (by100 blast)
  qed
qed

\<comment> \<open>Helper: continuous map preserves loops.\<close>
lemma top1_continuous_map_loop_early:
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

\<comment> \<open>Step 1a: z^n is continuous on S^1 (polynomial, sorry-free).\<close>
lemma Theorem_56_1_step_1_cont:
  fixes n :: nat
  assumes hn: "n > 0"
  shows "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
                               top1_S1_complex top1_S1_complex_topology (\<lambda>z. z^n)"
  unfolding top1_S1_complex_topology_def
  by (rule top1_continuous_map_on_subspace_open_sets)
     (auto simp: top1_S1_complex_def norm_power intro: continuous_intros)

\<comment> \<open>Step 1b: z^n induces injective map on \<pi>_1(S^1) (requires \<pi>_1(S^1) \<cong> Z).\<close>
lemma Theorem_56_1_step_1_inj:
  fixes n :: nat
  assumes hn: "n > 0"
  shows "\<forall>f g. top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f
              \<and> top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 g
              \<and> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1
                   (\<lambda>s. (f s)^n) (\<lambda>s. (g s)^n)
              \<longrightarrow> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1 f g"
  \<comment> \<open>Proof: \<pi>_1(S^1) \<cong> Z. The z^n map induces an endomorphism of Z.
     Any endomorphism of Z is ×m for some m. If m = 0, then z^n induces
     the trivial homomorphism, so z^n is nulhomotopic as S^1 \<rightarrow> S^1.
     Then z^n : S^1 \<rightarrow> C-{0} (via inclusion) is also nulhomotopic.
     But Step 2 says z^n : S^1 \<rightarrow> C-{0} is NOT nulhomotopic. Contradiction.
     So m \<noteq> 0, hence ×m is injective on Z, hence (z^n)_* is injective.\<close>
proof (intro allI impI, elim conjE)
  fix f g
  assume hf: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f"
  assume hg: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 g"
  assume hfgn: "top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1
       (\<lambda>s. (f s)^n) (\<lambda>s. (g s)^n)"
  \<comment> \<open>Under \<pi>_1(S^1_complex) \<cong> Z: [f] = k, [g] = l.
     [(f)^n] = (z^n)_*(k) = m*k, [(g)^n] = m*l.
     hfgn says m*k = m*l. Need m \<noteq> 0.
     If m = 0: z^n trivial on \<pi>_1 \<Rightarrow> z^n nulhomotopic \<Rightarrow> z^n:S^1\<rightarrow>C-{0} nulhomotopic.
     But Step 2: NOT nulhomotopic. Contradiction. So m \<noteq> 0, k = l, f ~ g.\<close>
  \<comment> \<open>Transfer via \<psi>(z) = (Re z, Im z) to S^1 (pair topology).\<close>
  let ?\<psi> = "\<lambda>z::complex. (Re z, Im z)"
  \<comment> \<open>Lift \<psi> \<circ> f to R via covering map R_to_S1. Let endpoint = k (integer).\<close>
  \<comment> \<open>Then \<psi>((f s)^n) = R_to_S1(n * ftilde(s)), so lift of \<psi> \<circ> f^n ends at n*k.\<close>
  \<comment> \<open>Similarly for g: lift ends at l, lift of g^n ends at n*l.\<close>
  \<comment> \<open>f^n ~ g^n \<Rightarrow> lifts have same endpoint: n*k = n*l.\<close>
  \<comment> \<open>n > 0 \<Rightarrow> k = l \<Rightarrow> f ~ g.\<close>
  \<comment> \<open>Setup: covering map R \<rightarrow> S^1, \<psi> bridge.\<close>
  have hcov: "top1_covering_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
    by (rule Theorem_53_1)
  have h0R: "(0::real) \<in> (UNIV::real set)" by simp
  have hp0: "top1_R_to_S1 0 = (1::real, 0::real)"
    unfolding top1_R_to_S1_def by simp
  have hTS1: "is_topology_on top1_S1 top1_S1_topology"
  proof -
    have hTR_: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have "is_topology_on (UNIV::(real\<times>real) set) (product_topology_on (top1_open_sets::real set set) top1_open_sets)"
      using product_topology_on_is_topology_on[OF hTR_ hTR_] by simp
    thus ?thesis unfolding top1_S1_topology_def by (rule subspace_topology_is_topology_on) simp
  qed
  \<comment> \<open>Transfer loops via \<psi> to S^1 (pair topology).\<close>
  have h\<psi>_cont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
      top1_S1 top1_S1_topology ?\<psi>"
    by (rule psi_continuous_S1)
  have h\<psi>_1: "?\<psi> 1 = (1::real, 0::real)" by simp
  have h\<psi>f_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) (?\<psi> \<circ> f)"
    using top1_continuous_map_loop_early[OF h\<psi>_cont hf] h\<psi>_1 by simp
  have h\<psi>g_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) (?\<psi> \<circ> g)"
    using top1_continuous_map_loop_early[OF h\<psi>_cont hg] h\<psi>_1 by simp
  \<comment> \<open>Lift \<psi>\<circ>f to R. Get ftilde with R_to_S1(ftilde(s)) = \<psi>(f(s)), ftilde(0)=0.\<close>
  have hTE: "is_topology_on (UNIV::real set) (top1_open_sets::real set set)"
    by (rule top1_open_sets_is_topology_on_UNIV)
  have h\<psi>f_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (?\<psi> \<circ> f)"
    using h\<psi>f_loop unfolding top1_is_loop_on_def by simp
  obtain ftilde where hft_path: "top1_is_path_on UNIV top1_open_sets 0 (ftilde 1) ftilde"
      and hft_lift: "\<forall>s\<in>I_set. top1_R_to_S1 (ftilde s) = (?\<psi> \<circ> f) s"
    using Lemma_54_1_path_lifting[OF hcov h0R hp0 h\<psi>f_path hTS1 hTE] by (by100 blast)
  have h\<psi>g_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (?\<psi> \<circ> g)"
    using h\<psi>g_loop unfolding top1_is_loop_on_def by simp
  obtain gtilde where hgt_path: "top1_is_path_on UNIV top1_open_sets 0 (gtilde 1) gtilde"
      and hgt_lift: "\<forall>s\<in>I_set. top1_R_to_S1 (gtilde s) = (?\<psi> \<circ> g) s"
    using Lemma_54_1_path_lifting[OF hcov h0R hp0 h\<psi>g_path hTS1 hTE] by (by100 blast)
  \<comment> \<open>Key: n*ftilde lifts \<psi>\<circ>(f^n). By DeMoivre: cis(\<theta>)^n = cis(n\<theta>),
     so R_to_S1(n*ftilde(s)) = \<psi>((f s)^n).\<close>
  have hft_n_lift: "\<forall>s\<in>I_set. top1_R_to_S1 (n * ftilde s) = ?\<psi> ((f s)^n)"
  proof
    fix s assume hs: "s \<in> I_set"
    \<comment> \<open>f(s) = cis(2\<pi> * ftilde(s)) since R_to_S1(ftilde s) = \<psi>(f s) and |f s| = 1.\<close>
    have hfs_S1: "f s \<in> top1_S1_complex"
      using hf unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def
      using hs by (by100 blast)
    have hfs_norm: "cmod (f s) = 1" using hfs_S1 unfolding top1_S1_complex_def by simp
    have hRs: "top1_R_to_S1 (ftilde s) = (Re (f s), Im (f s))"
      using hft_lift hs by simp
    hence hcos: "cos (2 * pi * ftilde s) = Re (f s)"
      and hsin: "sin (2 * pi * ftilde s) = Im (f s)"
      unfolding top1_R_to_S1_def by auto
    \<comment> \<open>f(s) = cis(2\<pi> * ftilde s).\<close>
    have hfs_cis: "f s = cis (2 * pi * ftilde s)"
    proof (rule complex_eqI)
      show "Re (f s) = Re (cis (2 * pi * ftilde s))" using hcos by simp
      show "Im (f s) = Im (cis (2 * pi * ftilde s))" using hsin by simp
    qed
    \<comment> \<open>(f s)^n = cis(2\<pi> * n * ftilde s) by DeMoivre.\<close>
    have "(f s)^n = cis (2 * pi * ftilde s) ^ n" using hfs_cis by simp
    also have "\<dots> = cis (n * (2 * pi * ftilde s))" by (rule DeMoivre)
    also have "n * (2 * pi * ftilde s) = 2 * pi * (n * ftilde s)"
      by (simp add: algebra_simps)
    finally have hfn_cis: "(f s)^n = cis (2 * pi * (n * ftilde s))" .
    \<comment> \<open>\<psi>((f s)^n) = (cos(2\<pi>*n*ftilde s), sin(2\<pi>*n*ftilde s)) = R_to_S1(n*ftilde s).\<close>
    show "top1_R_to_S1 (n * ftilde s) = ?\<psi> ((f s)^n)"
      unfolding top1_R_to_S1_def hfn_cis by simp
  qed
  have hgt_n_lift: "\<forall>s\<in>I_set. top1_R_to_S1 (n * gtilde s) = ?\<psi> ((g s)^n)"
  proof
    fix s assume hs: "s \<in> I_set"
    have hgs_S1: "g s \<in> top1_S1_complex"
      using hg unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def
      using hs by (by100 blast)
    have hgs_norm: "cmod (g s) = 1" using hgs_S1 unfolding top1_S1_complex_def by simp
    have hRs: "top1_R_to_S1 (gtilde s) = (Re (g s), Im (g s))"
      using hgt_lift hs by simp
    hence hcos: "cos (2 * pi * gtilde s) = Re (g s)"
      and hsin: "sin (2 * pi * gtilde s) = Im (g s)"
      unfolding top1_R_to_S1_def by auto
    have "g s = cis (2 * pi * gtilde s)"
      by (rule complex_eqI) (simp_all add: hcos hsin)
    hence "(g s)^n = cis (2 * pi * (n * gtilde s))"
      by (simp add: DeMoivre algebra_simps)
    thus "top1_R_to_S1 (n * gtilde s) = ?\<psi> ((g s)^n)"
      unfolding top1_R_to_S1_def by simp
  qed
  \<comment> \<open>f^n ~ g^n \<Rightarrow> \<psi>\<circ>(f^n) ~ \<psi>\<circ>(g^n) in S^1.
     Their lifts (n*ftilde and n*gtilde) have the same endpoint.
     n*ftilde(1) = n*gtilde(1), i.e., n*k = n*l. Since n > 0: k = l.\<close>
  have "ftilde 1 = gtilde 1"
  proof -
    \<comment> \<open>\<psi>\<circ>(f^n) ~ \<psi>\<circ>(g^n) in S^1 (from f^n ~ g^n and \<psi> continuous).\<close>
    have hTS1c: "is_topology_on top1_S1_complex top1_S1_complex_topology"
      unfolding top1_S1_complex_topology_def
      by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) simp
    have h\<psi>fn_hom: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
        (?\<psi> \<circ> (\<lambda>s. (f s)^n)) (?\<psi> \<circ> (\<lambda>s. (g s)^n))"
      using continuous_preserves_path_homotopic[OF hTS1c hTS1 h\<psi>_cont hfgn] h\<psi>_1 by simp
    \<comment> \<open>n*ftilde lifts \<psi>\<circ>(f^n), n*gtilde lifts \<psi>\<circ>(g^n).\<close>
    \<comment> \<open>By Theorem_54_3: path-homotopic lifts starting at same point have same endpoint.\<close>
    have hscale: "top1_continuous_map_on UNIV top1_open_sets UNIV top1_open_sets (\<lambda>x::real. real n * x)"
        unfolding top1_continuous_map_on_def
      proof (intro conjI ballI)
        fix x :: real show "real n * x \<in> UNIV" by simp
      next
        fix V :: "real set" assume "V \<in> top1_open_sets"
        hence "open V" unfolding top1_open_sets_def by (by100 blast)
        have "continuous_on UNIV (\<lambda>x::real. real n * x)" by (intro continuous_intros)
        from iffD1[OF continuous_on_open_vimage[OF open_UNIV] this, rule_format, OF \<open>open V\<close>]
        have "open ((\<lambda>x::real. real n * x) -` V \<inter> UNIV)" .
        hence "open ((\<lambda>x::real. real n * x) -` V)" by simp
        hence "open {x::real. real n * x \<in> V}" by (simp add: vimage_def)
        thus "{x \<in> UNIV. real n * x \<in> V} \<in> top1_open_sets"
          unfolding top1_open_sets_def by simp
      qed
    have hft_n_path: "top1_is_path_on UNIV top1_open_sets (0::real) (real n * ftilde 1) (\<lambda>s. real n * ftilde s)"
    proof -
      have "top1_continuous_map_on I_set I_top UNIV top1_open_sets ftilde"
        using hft_path unfolding top1_is_path_on_def by simp
      hence "top1_continuous_map_on I_set I_top UNIV top1_open_sets (\<lambda>s. real n * ftilde s)"
      proof -
        have "(\<lambda>s. real n * ftilde s) = (\<lambda>x. real n * x) \<circ> ftilde" by (rule ext) simp
        thus ?thesis using top1_continuous_map_on_comp[OF
            \<open>top1_continuous_map_on I_set I_top UNIV top1_open_sets ftilde\<close> hscale] by simp
      qed
      moreover have "ftilde 0 = 0" using hft_path unfolding top1_is_path_on_def by simp
      ultimately show ?thesis unfolding top1_is_path_on_def by simp
    qed
    have hgt_n_path: "top1_is_path_on UNIV top1_open_sets (0::real) (real n * gtilde 1) (\<lambda>s. real n * gtilde s)"
    proof -
      have "top1_continuous_map_on I_set I_top UNIV top1_open_sets gtilde"
        using hgt_path unfolding top1_is_path_on_def by simp
      hence "top1_continuous_map_on I_set I_top UNIV top1_open_sets (\<lambda>s. real n * gtilde s)"
      proof -
        have "(\<lambda>s. real n * gtilde s) = (\<lambda>x. real n * x) \<circ> gtilde" by (rule ext) simp
        thus ?thesis using top1_continuous_map_on_comp[OF
            \<open>top1_continuous_map_on I_set I_top UNIV top1_open_sets gtilde\<close> hscale] by simp
      qed
      moreover have "gtilde 0 = 0" using hgt_path unfolding top1_is_path_on_def by simp
      ultimately show ?thesis unfolding top1_is_path_on_def by simp
    qed
    \<comment> \<open>n*ftilde is a lift of \<psi>\<circ>(f^n): R_to_S1(n*ftilde s) = \<psi>((f s)^n).\<close>
    \<comment> \<open>By Theorem_54_3: since \<psi>\<circ>(f^n) ~ \<psi>\<circ>(g^n), their lifts have same endpoint.\<close>
    have "n * ftilde 1 = n * gtilde 1"
    proof -
      have hTS1c: "is_topology_on top1_S1_complex top1_S1_complex_topology"
        unfolding top1_S1_complex_topology_def
        by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) simp
      \<comment> \<open>\<psi>\<circ>(f^n) and \<psi>\<circ>(g^n) are loops at (1,0) in S^1.\<close>
      have hzn_cont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
          top1_S1_complex top1_S1_complex_topology (\<lambda>z. z^n)"
        by (rule Theorem_56_1_step_1_cont[OF hn])
      have hfn_loop: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 (\<lambda>s. (f s)^n)"
      proof -
        have "(\<lambda>s. (f s)^n) = (\<lambda>z. z^n) \<circ> f" by (rule ext) simp
        thus ?thesis using top1_continuous_map_loop_early[OF hzn_cont hf]
          by simp
      qed
      have hgn_loop: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 (\<lambda>s. (g s)^n)"
      proof -
        have "(\<lambda>s. (g s)^n) = (\<lambda>z. z^n) \<circ> g" by (rule ext) simp
        thus ?thesis using top1_continuous_map_loop_early[OF hzn_cont hg]
          by simp
      qed
      have h\<psi>fn_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) (?\<psi> \<circ> (\<lambda>s. (f s)^n))"
        using top1_continuous_map_loop_early[OF h\<psi>_cont hfn_loop] h\<psi>_1 by simp
      have h\<psi>gn_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) (?\<psi> \<circ> (\<lambda>s. (g s)^n))"
        using top1_continuous_map_loop_early[OF h\<psi>_cont hgn_loop] h\<psi>_1 by simp
      have h\<psi>fn_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (?\<psi> \<circ> (\<lambda>s. (f s)^n))"
        using h\<psi>fn_loop unfolding top1_is_loop_on_def by simp
      have h\<psi>gn_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (?\<psi> \<circ> (\<lambda>s. (g s)^n))"
        using h\<psi>gn_loop unfolding top1_is_loop_on_def by simp
      \<comment> \<open>\<psi>\<circ>(f^n) ~ \<psi>\<circ>(g^n) from f^n ~ g^n and \<psi> continuous.\<close>
      have h\<psi>fn_hom: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
          (?\<psi> \<circ> (\<lambda>s. (f s)^n)) (?\<psi> \<circ> (\<lambda>s. (g s)^n))"
        using continuous_preserves_path_homotopic[OF hTS1c hTS1 h\<psi>_cont hfgn] h\<psi>_1 by simp
      \<comment> \<open>Lift conditions.\<close>
      have hft_n_lift': "\<forall>s\<in>I_set. top1_R_to_S1 (real n * ftilde s) = (?\<psi> \<circ> (\<lambda>s. (f s)^n)) s"
        using hft_n_lift by (simp add: comp_def)
      have hgt_n_lift': "\<forall>s\<in>I_set. top1_R_to_S1 (real n * gtilde s) = (?\<psi> \<circ> (\<lambda>s. (g s)^n)) s"
        using hgt_n_lift by (simp add: comp_def)
      \<comment> \<open>Apply Theorem_54_3.\<close>
      from Theorem_54_3[OF hcov hTE hTS1 h0R hp0
          h\<psi>fn_path h\<psi>gn_path h\<psi>fn_hom
          hft_n_path hft_n_lift' hgt_n_path hgt_n_lift']
      show ?thesis by simp
    qed
    thus "ftilde 1 = gtilde 1" using hn by simp
  qed
  \<comment> \<open>Lifts with same endpoint \<Rightarrow> loops path-homotopic (Theorem_54_3 reverse).\<close>
  \<comment> \<open>Lifts ftilde, gtilde have same endpoint. By Theorem_54_3 (uniqueness part):
     if two paths lift the same loop and start at the same point and end at the same point,
     they are path-homotopic, hence the original loops are path-homotopic.
     Actually, we need the CONVERSE direction: same lift endpoints \<Rightarrow> homotopic.
     This uses: R simply connected, so ftilde ~ gtilde (in R), hence p\<circ>ftilde ~ p\<circ>gtilde,
     i.e., \<psi>\<circ>f ~ \<psi>\<circ>g.\<close>
  \<comment> \<open>From ftilde(1) = gtilde(1) and R simply connected:
     ftilde ~ gtilde in R (all paths with same endpoints are homotopic).
     Then R_to_S1 \<circ> ftilde ~ R_to_S1 \<circ> gtilde in S^1.
     R_to_S1 \<circ> ftilde = \<psi> \<circ> f on I_set, so \<psi> \<circ> f ~ \<psi> \<circ> g.
     Transfer back via \<psi>^{-1}: f ~ g in S^1_complex.\<close>
  show "top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1 f g"
  proof -
    \<comment> \<open>Step 1: R simply connected \<Rightarrow> ftilde ~ gtilde.\<close>
    have hgt_path': "top1_is_path_on UNIV top1_open_sets 0 (ftilde 1) gtilde"
      using hgt_path \<open>ftilde 1 = gtilde 1\<close> by simp
    have hft_gt_hom: "top1_path_homotopic_on UNIV top1_open_sets 0 (ftilde 1) ftilde gtilde"
      by (rule simply_connected_paths_homotopic[OF top1_R_simply_connected' hft_path hgt_path' h0R])
    \<comment> \<open>Step 2: R_to_S1 continuous \<Rightarrow> R_to_S1\<circ>ftilde ~ R_to_S1\<circ>gtilde in S^1.\<close>
    have hp_cont: "top1_continuous_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
      using hcov unfolding top1_covering_map_on_def by (by100 blast)
    have "top1_path_homotopic_on top1_S1 top1_S1_topology
        (top1_R_to_S1 0) (top1_R_to_S1 (ftilde 1))
        (top1_R_to_S1 \<circ> ftilde) (top1_R_to_S1 \<circ> gtilde)"
      by (rule continuous_preserves_path_homotopic[OF hTE hTS1 hp_cont hft_gt_hom])
    \<comment> \<open>Simplify: R_to_S1(0) = (1,0). R_to_S1(ftilde 1) = \<psi>(f 1) = \<psi>(1) = (1,0).\<close>
    moreover have "top1_R_to_S1 0 = (1::real, 0::real)" by (rule hp0)
    moreover have "top1_R_to_S1 (ftilde 1) = (1::real, 0::real)"
    proof -
      have "(1::real) \<in> I_set" unfolding top1_unit_interval_def by simp
      have "top1_R_to_S1 (ftilde 1) = (?\<psi> \<circ> f) 1"
        using hft_lift \<open>(1::real) \<in> I_set\<close> by (by100 blast)
      moreover have "f 1 = 1" using hf unfolding top1_is_loop_on_def top1_is_path_on_def by (by100 blast)
      ultimately show ?thesis by simp
    qed
    ultimately have h\<psi>fg_hom: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
        (top1_R_to_S1 \<circ> ftilde) (top1_R_to_S1 \<circ> gtilde)" by simp
    \<comment> \<open>Step 3: R_to_S1 \<circ> ftilde = \<psi> \<circ> f on I_set, similarly for g.
       Path homotopy depends only on values on I_set, so \<psi> \<circ> f ~ \<psi> \<circ> g.\<close>
    \<comment> \<open>Step 3: R_to_S1\<circ>ftilde agrees with \<psi>\<circ>f on I_set (from hft_lift).
       Similarly for g. The homotopy H between R_to_S1\<circ>ftilde and R_to_S1\<circ>gtilde
       also works for \<psi>\<circ>f and \<psi>\<circ>g since they agree on I_set.\<close>
    have "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) (?\<psi> \<circ> f) (?\<psi> \<circ> g)"
    proof -
      have hRft_eq: "\<forall>s\<in>I_set. (top1_R_to_S1 \<circ> ftilde) s = (?\<psi> \<circ> f) s"
        using hft_lift by (simp add: comp_def)
      have hRgt_eq: "\<forall>s\<in>I_set. (top1_R_to_S1 \<circ> gtilde) s = (?\<psi> \<circ> g) s"
        using hgt_lift by (simp add: comp_def)
      \<comment> \<open>Extract homotopy H from h\<psi>fg_hom (R_to_S1 versions).\<close>
      obtain H where hH_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
              top1_S1 top1_S1_topology H"
          and hH0: "\<forall>s\<in>I_set. H (s, 0) = (top1_R_to_S1 \<circ> ftilde) s"
          and hH1: "\<forall>s\<in>I_set. H (s, 1) = (top1_R_to_S1 \<circ> gtilde) s"
          and hH_left: "\<forall>t\<in>I_set. H (0, t) = (1, 0)"
          and hH_right: "\<forall>t\<in>I_set. H (1, t) = (1, 0)"
        using h\<psi>fg_hom unfolding top1_path_homotopic_on_def by auto
      \<comment> \<open>H(s,0) = R_to_S1(ftilde s) = \<psi>(f s) on I_set. Same for H(s,1) and g.\<close>
      have "\<forall>s\<in>I_set. H (s, 0) = (?\<psi> \<circ> f) s" using hH0 hRft_eq by simp
      moreover have "\<forall>s\<in>I_set. H (s, 1) = (?\<psi> \<circ> g) s" using hH1 hRgt_eq by simp
      \<comment> \<open>So H is a homotopy from \<psi>\<circ>f to \<psi>\<circ>g.\<close>
      ultimately have "\<forall>s\<in>I_set. H (s, 0) = (?\<psi> \<circ> f) s"
          and "\<forall>s\<in>I_set. H (s, 1) = (?\<psi> \<circ> g) s" by auto
      show ?thesis unfolding top1_path_homotopic_on_def
        using h\<psi>f_path h\<psi>g_path hH_cont
              \<open>\<forall>s\<in>I_set. H (s, 0) = (?\<psi> \<circ> f) s\<close>
              \<open>\<forall>s\<in>I_set. H (s, 1) = (?\<psi> \<circ> g) s\<close>
              hH_left hH_right
        by (intro conjI exI[of _ H]) auto
    qed
    \<comment> \<open>Step 4: Transfer back from S^1 to S^1_complex via \<psi>^{-1}.\<close>
    \<comment> \<open>\<psi>^{-1}(a,b) = Complex a b. Continuous S^1 \<rightarrow> S^1_complex.\<close>
    thus ?thesis
    proof -
      assume h\<psi>fg: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) (?\<psi> \<circ> f) (?\<psi> \<circ> g)"
      \<comment> \<open>\<psi>^{-1}(a,b) = Complex a b is continuous S^1 \<rightarrow> S^1_complex.\<close>
      let ?\<psi>inv = "\<lambda>p::real\<times>real. Complex (fst p) (snd p)"
      have h\<psi>inv_cont: "top1_continuous_map_on top1_S1 top1_S1_topology
          top1_S1_complex top1_S1_complex_topology ?\<psi>inv"
      proof -
        have h\<psi>inv_map: "\<And>p. p \<in> top1_S1 \<Longrightarrow> ?\<psi>inv p \<in> top1_S1_complex"
          unfolding top1_S1_def top1_S1_complex_def by (auto simp: cmod_def)
        have hcont_univ: "continuous_on UNIV (\<lambda>p::real\<times>real. Complex (fst p) (snd p))"
          by (intro continuous_intros)
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix p assume "p \<in> top1_S1" thus "?\<psi>inv p \<in> top1_S1_complex"
            by (rule h\<psi>inv_map)
        next
          fix V assume hV: "V \<in> top1_S1_complex_topology"
          then obtain W where hWo: "W \<in> (top1_open_sets :: complex set set)"
              and hVeq: "V = top1_S1_complex \<inter> W"
            unfolding top1_S1_complex_topology_def subspace_topology_def by (by100 auto)
          have hWopen: "open W" using hWo unfolding top1_open_sets_def by (by100 simp)
          have hpre_open: "open ((\<lambda>p::real\<times>real. Complex (fst p) (snd p)) -` W)"
          proof -
            have "open ((\<lambda>p::real\<times>real. Complex (fst p) (snd p)) -` W \<inter> UNIV)"
              using iffD1[OF continuous_on_open_vimage[OF open_UNIV] hcont_univ] hWopen
              by (by100 blast)
            thus ?thesis by simp
          qed
          have "{p \<in> top1_S1. ?\<psi>inv p \<in> V} =
              top1_S1 \<inter> ((\<lambda>p. Complex (fst p) (snd p)) -` W)"
            unfolding hVeq using h\<psi>inv_map by (by100 auto)
          thus "{p \<in> top1_S1. ?\<psi>inv p \<in> V} \<in> top1_S1_topology"
            unfolding top1_S1_topology_def subspace_topology_def
            using hpre_open product_topology_on_open_sets_real2
            unfolding top1_open_sets_def by (by100 blast)
        qed
      qed
      have hTS1c': "is_topology_on top1_S1_complex top1_S1_complex_topology"
        unfolding top1_S1_complex_topology_def
        by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV]) simp
      have h\<psi>inv_1: "?\<psi>inv (1, 0) = (1::complex)"
        by (rule complex_eqI) simp_all
      have h\<psi>inv_\<psi>: "\<And>z::complex. ?\<psi>inv (?\<psi> z) = z"
        by (rule complex_eqI) simp_all
      have h\<psi>inv_\<psi>_f: "?\<psi>inv \<circ> (?\<psi> \<circ> f) = f"
        by (rule ext) (simp add: h\<psi>inv_\<psi>)
      have h\<psi>inv_\<psi>_g: "?\<psi>inv \<circ> (?\<psi> \<circ> g) = g"
        by (rule ext) (simp add: h\<psi>inv_\<psi>)
      have hstep: "top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology
          (?\<psi>inv (1, 0)) (?\<psi>inv (1, 0)) (?\<psi>inv \<circ> (?\<psi> \<circ> f)) (?\<psi>inv \<circ> (?\<psi> \<circ> g))"
        by (rule continuous_preserves_path_homotopic[OF hTS1 hTS1c' h\<psi>inv_cont h\<psi>fg])
      show ?thesis using hstep unfolding h\<psi>inv_1 h\<psi>inv_\<psi>_f h\<psi>inv_\<psi>_g .
    qed
  qed
qed

\<comment> \<open>Combined (for backward compatibility).\<close>
lemma Theorem_56_1_step_1:
  fixes n :: nat
  assumes hn: "n > 0"
  shows "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
                               top1_S1_complex top1_S1_complex_topology (\<lambda>z. z^n)
       \<and> (\<forall>f g. top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f
              \<and> top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 g
              \<and> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1
                   (\<lambda>s. (f s)^n) (\<lambda>s. (g s)^n)
              \<longrightarrow> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1 f g)"
  using Theorem_56_1_step_1_cont[OF hn] Theorem_56_1_step_1_inj[OF hn] by blast

(** Step 2: z^n as S^1 \<rightarrow> C - {0} is not nulhomotopic.

    Munkres' proof: g = j \<circ> f where j: S^1 \<hookrightarrow> C-{0} is inclusion and f = z^n.
    Since S^1 is a retract of C-{0} (retraction r(z) = z/|z|), j_* is injective.
    By Step 1, f_* is injective. So g_* = j_* \<circ> f_* is injective, hence nontrivial,
    hence g is not nulhomotopic. **)
lemma Theorem_56_1_step_2:
  fixes n :: nat
  assumes hn: "n > 0"
  shows "\<not> top1_nulhomotopic_on top1_S1_complex top1_S1_complex_topology
            top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n)"
proof
  assume hnul: "top1_nulhomotopic_on top1_S1_complex top1_S1_complex_topology
      top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n)"
  \<comment> \<open>S^1 is a retract of C - {0} via r(z) = z/|z|. So j: S^1 \<hookrightarrow> C-{0} induces
     j_* injective. f = z^n induces f_* injective (Step 1).
     g = j \<circ> f: S^1 \<rightarrow> C-{0} induces g_* = j_* \<circ> f_* injective, hence nontrivial.\<close>
  \<comment> \<open>j_* injective: retraction r(z)=z/|z| of C-{0} onto S^1.\<close>
  have hj_inj: "\<forall>f g. top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f
      \<and> top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 g
      \<and> top1_path_homotopic_on top1_C_minus_0 top1_C_minus_0_topology 1 1 f g
      \<longrightarrow> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1 f g"
  proof (intro allI impI)
    fix f g
    assume hfg: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f
        \<and> top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 g
        \<and> top1_path_homotopic_on top1_C_minus_0 top1_C_minus_0_topology 1 1 f g"
    have hf_loop: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f"
      using hfg by (by100 blast)
    have hg_loop: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 g"
      using hfg by (by100 blast)
    have hhom: "top1_path_homotopic_on top1_C_minus_0 top1_C_minus_0_topology 1 1 f g"
      using hfg by (by100 blast)
    \<comment> \<open>Extract the homotopy H in C-{0}.\<close>
    have hhom_unf: "top1_is_path_on top1_C_minus_0 top1_C_minus_0_topology 1 1 f
        \<and> top1_is_path_on top1_C_minus_0 top1_C_minus_0_topology 1 1 g
        \<and> (\<exists>F. top1_continuous_map_on (I_set \<times> I_set) II_topology top1_C_minus_0 top1_C_minus_0_topology F
            \<and> (\<forall>s\<in>I_set. F (s, 0) = f s) \<and> (\<forall>s\<in>I_set. F (s, 1) = g s)
            \<and> (\<forall>t\<in>I_set. F (0, t) = 1) \<and> (\<forall>t\<in>I_set. F (1, t) = 1))"
      using hhom unfolding top1_path_homotopic_on_def by (by100 blast)
    obtain H where hH_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        top1_C_minus_0 top1_C_minus_0_topology H"
      and hH0: "\<forall>s\<in>I_set. H (s, 0) = f s"
      and hH1: "\<forall>s\<in>I_set. H (s, 1) = g s"
      and hH_left: "\<forall>t\<in>I_set. H (0, t) = (1::complex)"
      and hH_right: "\<forall>t\<in>I_set. H (1, t) = (1::complex)"
      using conjunct2[OF conjunct2[OF hhom_unf]] by (by100 auto)
    \<comment> \<open>Retraction r(z) = sgn z = z/|z|.\<close>
    \<comment> \<open>sgn fixes S^1: |z|=1 implies sgn z = z/1 = z.\<close>
    have hr_fix: "\<And>z::complex. z \<in> top1_S1_complex \<Longrightarrow> sgn z = z"
    proof -
      fix z :: complex assume hz: "z \<in> top1_S1_complex"
      have "norm z = 1" using hz unfolding top1_S1_complex_def by (by100 simp)
      hence "z \<noteq> 0" by (by100 auto)
      show "sgn z = z" using \<open>norm z = 1\<close>
        by (simp add: sgn_div_norm)
    qed
    \<comment> \<open>sgn maps C-{0} to S^1: |sgn z| = 1 for z \<noteq> 0.\<close>
    have hr_S1: "\<And>z::complex. z \<in> top1_C_minus_0 \<Longrightarrow> sgn z \<in> top1_S1_complex"
    proof -
      fix z :: complex assume hz: "z \<in> top1_C_minus_0"
      hence "z \<noteq> 0" unfolding top1_C_minus_0_def by (by100 blast)
      hence "norm (sgn z) = 1" by (simp add: norm_sgn)
      thus "sgn z \<in> top1_S1_complex" unfolding top1_S1_complex_def by simp
    qed
    \<comment> \<open>sgn is continuous C-{0} \<rightarrow> S^1 (as top1_continuous_map_on).\<close>
    have hr_cont: "top1_continuous_map_on top1_C_minus_0 top1_C_minus_0_topology
        top1_S1_complex top1_S1_complex_topology (sgn :: complex \<Rightarrow> complex)"
    proof -
      have hsgn_cont: "continuous_on (UNIV - {0::complex}) sgn"
        by (intro continuous_on_sgn continuous_on_id) (by100 simp)
      have hmaps: "\<forall>x\<in>top1_C_minus_0. sgn x \<in> top1_S1_complex"
        using hr_S1 by simp
      have hpreimg: "\<forall>V\<in>top1_S1_complex_topology.
          {x \<in> top1_C_minus_0. sgn x \<in> V} \<in> top1_C_minus_0_topology"
      proof
        fix V assume hV: "V \<in> top1_S1_complex_topology"
        obtain W where hWo: "W \<in> top1_open_sets" and hVeq: "V = top1_S1_complex \<inter> W"
          using hV unfolding top1_S1_complex_topology_def subspace_topology_def by (by100 auto)
        have hWopen: "open W" using hWo unfolding top1_open_sets_def by (by100 blast)
        \<comment> \<open>sgn\<inverse>(W) \<inter> (UNIV-{0}) is open since sgn continuous on UNIV-{0}.\<close>
        have hC0_open: "open (UNIV - {0::complex})" by (by100 auto)
        have hpreW: "open (sgn -` W \<inter> (UNIV - {0::complex}))"
          using iffD1[OF continuous_on_open_vimage[OF hC0_open] hsgn_cont, rule_format, OF hWopen] .
        have heq: "{x \<in> top1_C_minus_0. sgn x \<in> V} = top1_C_minus_0 \<inter> (sgn -` W \<inter> (UNIV - {0::complex}))"
        proof -
          have "\<And>x. x \<in> top1_C_minus_0 \<Longrightarrow> sgn x \<in> top1_S1_complex"
            using hmaps by (by100 blast)
          thus ?thesis unfolding hVeq top1_C_minus_0_def by (by100 auto)
        qed
        have "sgn -` W \<inter> (UNIV - {0::complex}) \<in> top1_open_sets"
          using hpreW unfolding top1_open_sets_def by (by100 blast)
        thus "{x \<in> top1_C_minus_0. sgn x \<in> V} \<in> top1_C_minus_0_topology"
          unfolding heq top1_C_minus_0_topology_def subspace_topology_def by (by100 blast)
      qed
      show ?thesis unfolding top1_continuous_map_on_def
        using hmaps hpreimg by (by100 blast)
    qed
    \<comment> \<open>sgn \<circ> H is continuous I \<times> I \<rightarrow> S^1, by composition.\<close>
    have hrH_cont: "top1_continuous_map_on (I_set \<times> I_set) II_topology
        top1_S1_complex top1_S1_complex_topology (sgn \<circ> H)"
      by (rule top1_continuous_map_on_comp[OF hH_cont hr_cont])
    \<comment> \<open>f(s) \<in> S^1, so sgn(f(s)) = f(s); similarly for g. sgn(1) = 1.\<close>
    have hf_S1: "\<And>s. s \<in> I_set \<Longrightarrow> f s \<in> top1_S1_complex"
      using hf_loop unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def
      by (by100 blast)
    have hg_S1: "\<And>s. s \<in> I_set \<Longrightarrow> g s \<in> top1_S1_complex"
      using hg_loop unfolding top1_is_loop_on_def top1_is_path_on_def top1_continuous_map_on_def
      by (by100 blast)
    have hrH0: "\<forall>s\<in>I_set. (sgn \<circ> H) (s, 0) = f s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "(sgn \<circ> H) (s, 0) = sgn (H (s, 0))" by simp
      also have "\<dots> = sgn (f s)" using hH0 hs by simp
      also have "\<dots> = f s" using hr_fix hf_S1[OF hs] by simp
      finally show "(sgn \<circ> H) (s, 0) = f s" .
    qed
    have hrH1: "\<forall>s\<in>I_set. (sgn \<circ> H) (s, 1) = g s"
    proof
      fix s assume hs: "s \<in> I_set"
      have "(sgn \<circ> H) (s, 1) = sgn (g s)" using hH1 hs by simp
      also have "\<dots> = g s" using hr_fix hg_S1[OF hs] by simp
      finally show "(sgn \<circ> H) (s, 1) = g s" .
    qed
    have hsgn1: "sgn (1::complex) = 1"
      by (simp add: sgn_div_norm)
    have hrH_left: "\<forall>t\<in>I_set. (sgn \<circ> H) (0, t) = (1::complex)"
    proof
      fix t assume ht: "t \<in> I_set"
      show "(sgn \<circ> H) (0, t) = 1" using hH_left ht hsgn1 by simp
    qed
    have hrH_right: "\<forall>t\<in>I_set. (sgn \<circ> H) (1, t) = (1::complex)"
    proof
      fix t assume ht: "t \<in> I_set"
      show "(sgn \<circ> H) (1, t) = 1" using hH_right ht hsgn1 by simp
    qed
    \<comment> \<open>Assemble the path homotopy in S^1.\<close>
    have hf_path: "top1_is_path_on top1_S1_complex top1_S1_complex_topology 1 1 f"
      using hf_loop unfolding top1_is_loop_on_def by simp
    have hg_path: "top1_is_path_on top1_S1_complex top1_S1_complex_topology 1 1 g"
      using hg_loop unfolding top1_is_loop_on_def by simp
    show "top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1 f g"
      unfolding top1_path_homotopic_on_def
      using hf_path hg_path hrH_cont hrH0 hrH1 hrH_left hrH_right by (by100 blast)
  qed
  \<comment> \<open>g_* nontrivial contradicts g being nulhomotopic.\<close>
  \<comment> \<open>z^n nulhomotopic in C-{0} \<Rightarrow> for all loops f at 1, z^n \<circ> f ≃ const in C-{0}.
     By j_inj, z^n \<circ> f ≃ const in S^1. But z^n not nulhomotopic in S^1 (Step 1).\<close>
  \<comment> \<open>Actually: hnul says z^n (as S^1 \<rightarrow> C-{0}) is nulhomotopic.
     Since z^n: S^1 \<rightarrow> S^1 \<subseteq> C-{0}, nulhomotopic in C-{0} means
     (\<lambda>z. z^n) ≃ const in C-{0}.
     By hj_inj: homotopic in C-{0} \<Rightarrow> homotopic in S^1.
     Specifically, for any f with z^n \<circ> f ≃ const in C-{0}, by j_inj get in S^1.
     But this needs more structure than just the two facts.\<close>
  \<comment> \<open>Step-by-step: nulhomotopy gives h ≃ const in C-{0} for all loops;
     j_inj transfers to S^1; contradicts Step 1 (z^n nontrivial on π₁(S¹)).\<close>
  \<comment> \<open>From hnul: z^n nulhomotopic, so for all loops f at 1, (z^n) \<circ> f ≃ const in C-{0}.\<close>
  have hnul_all: "\<forall>f. top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f
      \<longrightarrow> top1_path_homotopic_on top1_C_minus_0 top1_C_minus_0_topology 1 1
            ((\<lambda>z. z^n) \<circ> f) (top1_constant_path 1)"
  proof (intro allI impI)
    fix f assume hf: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f"
    have hTS1c: "is_topology_on top1_S1_complex top1_S1_complex_topology"
      unfolding top1_S1_complex_topology_def
      by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV])
         (simp add: top1_S1_complex_def)
    have hTC0: "is_topology_on top1_C_minus_0 top1_C_minus_0_topology"
      unfolding top1_C_minus_0_topology_def
      by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV])
         (simp add: top1_C_minus_0_def)
    have hg_cont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n)"
    proof -
      \<comment> \<open>z^n: S^1 \<rightarrow> S^1 continuous (from Step 1). S^1 \<subseteq> C-{0} since norm = 1 \<noteq> 0.\<close>
      have hS1_sub_C0: "top1_S1_complex \<subseteq> top1_C_minus_0"
        unfolding top1_S1_complex_def top1_C_minus_0_def by (by100 auto)
      have hzn_S1: "\<And>z::complex. z \<in> top1_S1_complex \<Longrightarrow> z^n \<in> top1_S1_complex"
        unfolding top1_S1_complex_def using assms by (simp add: norm_power)
      have hzn_C0: "\<And>z::complex. z \<in> top1_S1_complex \<Longrightarrow> z^n \<in> top1_C_minus_0"
        using hzn_S1 hS1_sub_C0 by (by100 blast)
      \<comment> \<open>z^n continuous UNIV \<rightarrow> UNIV, restrict to S^1 \<rightarrow> C-{0}.\<close>
      have hzn_cont_univ: "continuous_on UNIV (\<lambda>z::complex. z^n)"
        by (intro continuous_intros)
      show ?thesis
        unfolding top1_S1_complex_topology_def top1_C_minus_0_topology_def
        by (rule top1_continuous_map_on_subspace_open_sets[OF hzn_C0 hzn_cont_univ])
    qed
    have h1_S1: "(1::complex) \<in> top1_S1_complex" unfolding top1_S1_complex_def by simp
    have hg1: "(\<lambda>z::complex. z^n) 1 = (1::complex)" using assms by simp
    show "top1_path_homotopic_on top1_C_minus_0 top1_C_minus_0_topology 1 1
        ((\<lambda>z. z^n) \<circ> f) (top1_constant_path 1)"
      by (rule nulhomotopic_trivializes_loops_general[OF hTS1c hTC0 hg_cont hnul hg1 h1_S1 hf])
  qed
  \<comment> \<open>By hj_inj: transfer to S^1.\<close>
  have hnul_S1: "\<forall>f. top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f
      \<longrightarrow> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1
            ((\<lambda>z. z^n) \<circ> f) (top1_constant_path 1)"
  proof (intro allI impI)
    fix f assume hf: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f"
    \<comment> \<open>z^n \<circ> f is a loop in S^1 (since z^n maps S^1 to S^1) and in C-{0} (since S^1 \<subseteq> C-{0}).\<close>
    have "top1_path_homotopic_on top1_C_minus_0 top1_C_minus_0_topology 1 1
        ((\<lambda>z. z^n) \<circ> f) (top1_constant_path 1)"
      using hnul_all hf by (by100 blast)
    \<comment> \<open>By hj_inj: homotopic in C-{0} implies homotopic in S^1.\<close>
    have hznf_loop: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 ((\<lambda>z. z^n) \<circ> f)"
    proof -
      have hf_path: "top1_is_path_on top1_S1_complex top1_S1_complex_topology 1 1 f"
        using hf unfolding top1_is_loop_on_def by (by100 blast)
      have hf_cont: "top1_continuous_map_on I_set I_top top1_S1_complex top1_S1_complex_topology f"
        using hf_path unfolding top1_is_path_on_def by (by100 blast)
      have hcont_step1: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
          top1_S1_complex top1_S1_complex_topology (\<lambda>z. z^n)"
        using Theorem_56_1_step_1_cont[OF hn] .
      have hcomp: "top1_continuous_map_on I_set I_top top1_S1_complex top1_S1_complex_topology
          ((\<lambda>z. z^n) \<circ> f)"
        by (rule top1_continuous_map_on_comp[OF hf_cont hcont_step1])
      have h0: "((\<lambda>z::complex. z^n) \<circ> f) 0 = 1" using hf unfolding top1_is_loop_on_def top1_is_path_on_def
        using hn by simp
      have h1: "((\<lambda>z::complex. z^n) \<circ> f) 1 = 1" using hf unfolding top1_is_loop_on_def top1_is_path_on_def
        using hn by simp
      show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
        using hcomp h0 h1 by (by100 simp)
    qed
    have hconst_loop: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 (top1_constant_path 1)"
    proof -
      have hTS1c': "is_topology_on top1_S1_complex top1_S1_complex_topology"
        unfolding top1_S1_complex_topology_def
        by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV])
           (simp add: top1_S1_complex_def)
      have h1_S1': "(1::complex) \<in> top1_S1_complex" unfolding top1_S1_complex_def by simp
      show ?thesis by (rule top1_constant_path_is_loop[OF hTS1c' h1_S1'])
    qed
    show "top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1
        ((\<lambda>z. z^n) \<circ> f) (top1_constant_path 1)"
      using hj_inj hznf_loop hconst_loop
            \<open>top1_path_homotopic_on top1_C_minus_0 top1_C_minus_0_topology 1 1
                ((\<lambda>z. z^n) \<circ> f) (top1_constant_path 1)\<close>
      by (by100 blast)
  qed
  \<comment> \<open>But Step 1 says z^n_* is injective on π₁(S^1), so z^n is not nulhomotopic in S^1.\<close>
  have hnontrivial: "\<not> (\<forall>f. top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f
      \<longrightarrow> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1
            ((\<lambda>z. z^n) \<circ> f) (top1_constant_path 1))"
  proof
    assume hnul_S1': "\<forall>f. top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 f
        \<longrightarrow> top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1
              ((\<lambda>z. z^n) \<circ> f) (top1_constant_path 1)"
    \<comment> \<open>The standard loop p_0(s) = cis(2\<pi>s) is a loop on S^1_complex at 1.\<close>
    let ?p0 = "\<lambda>s::real. cis (2 * pi * s)"
    have hp0_loop: "top1_is_loop_on top1_S1_complex top1_S1_complex_topology 1 ?p0"
    proof -
      have hp0_S1: "\<And>s. cmod (cis (2 * pi * s)) = 1" by simp
      have hp0_mem: "\<forall>s\<in>I_set. ?p0 s \<in> top1_S1_complex"
        unfolding top1_S1_complex_def using hp0_S1 by simp
      have hp0_cont_univ: "continuous_on UNIV (\<lambda>s::real. cis (2 * pi * s))"
        by (intro continuous_intros)
      have hp0_cont: "top1_continuous_map_on I_set I_top top1_S1_complex top1_S1_complex_topology ?p0"
        unfolding top1_S1_complex_topology_def
        apply (simp add: hp0_cont_univ hp0_mem
          top1_continuous_map_on_subspace_open_sets
          top1_unit_interval_topology_def)
        done
      show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
        using hp0_cont by simp
    qed
    \<comment> \<open>z^n \<circ> p_0(s) = cis(2\<pi>ns). If \<simeq> const, then its real covering lift ends at 0.
       But the lift of cis(2\<pi>ns) from 0 is s \<mapsto> ns, ending at n \<neq> 0. Contradiction.\<close>
    have hzp0_const: "top1_path_homotopic_on top1_S1_complex top1_S1_complex_topology 1 1
        ((\<lambda>z. z^n) \<circ> ?p0) (top1_constant_path 1)"
      using hnul_S1' hp0_loop by (by100 blast)
    \<comment> \<open>This contradicts the nontriviality of the n-fold winding on S^1.\<close>
    \<comment> \<open>Using the covering map R \<rightarrow> S^1: lift of n-fold winding ends at n \<noteq> 0.\<close>
    \<comment> \<open>Transfer to real S^1 via (Re,Im): the n-fold winding on real S^1 is
       w_n(s) = top1_R_to_S1(ns) = (cos 2\<pi>ns, sin 2\<pi>ns).
       If cis(2\<pi>ns) \<simeq> const on S^1_complex, then w_n \<simeq> const on S^1.
       But lift of w_n via covering R \<rightarrow> S^1 is s \<mapsto> ns, ending at n.
       Lift of const is s \<mapsto> 0, ending at 0. By Theorem 54.3, n = 0. Contradiction.\<close>
    \<comment> \<open>The n-fold winding on real S^1.\<close>
    let ?wn = "\<lambda>s. top1_R_to_S1 (real n * s)"
    \<comment> \<open>w_n is a loop at (1,0) on S^1.\<close>
    have hwn_loop: "top1_is_loop_on top1_S1 top1_S1_topology (1, 0) ?wn"
    proof -
      have hwn0: "?wn 0 = (1, 0)" unfolding top1_R_to_S1_def by simp
      have hwn1: "?wn 1 = (1, 0)"
      proof -
        have "top1_R_to_S1 (real n * 1) = top1_R_to_S1 (0 + of_int (int n))"
          by simp
        also have "\<dots> = top1_R_to_S1 0" by (rule top1_R_to_S1_int_shift_early)
        also have "\<dots> = (1, 0)" unfolding top1_R_to_S1_def by simp
        finally show ?thesis by simp
      qed
      have hwn_S1: "\<And>s. ?wn s \<in> top1_S1"
        unfolding top1_R_to_S1_def top1_S1_def by (by100 auto)
      have hwn_cont: "top1_continuous_map_on I_set I_top top1_S1 top1_S1_topology ?wn"
      proof -
        \<comment> \<open>?wn = R_to_S1 \<circ> (\<lambda>s. n*s). Both are continuous.\<close>
        have heq: "?wn = top1_R_to_S1 \<circ> (\<lambda>s. real n * s)" by (rule ext) simp
        have hlin_cont: "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (\<lambda>s. real n * s)"
        proof -
          have hcont: "continuous_on UNIV (\<lambda>s::real. real n * s)" by (intro continuous_intros)
          show ?thesis unfolding top1_continuous_map_on_def
          proof (intro conjI ballI)
            fix s :: real assume "s \<in> I_set" show "real n * s \<in> (UNIV::real set)" by simp
          next
            fix V :: "real set" assume hV: "V \<in> top1_open_sets"
            have hVo: "open V" using hV unfolding top1_open_sets_def by (by100 blast)
            have "open ((\<lambda>s::real. real n * s) -` V)"
            proof -
              have "open ((\<lambda>s::real. real n * s) -` V \<inter> UNIV)"
                using iffD1[OF continuous_on_open_vimage[OF open_UNIV] hcont] hVo by (by100 blast)
              thus ?thesis by simp
            qed
            hence "(\<lambda>s::real. real n * s) -` V \<in> top1_open_sets"
              unfolding top1_open_sets_def by (by100 blast)
            thus "{s \<in> I_set. real n * s \<in> V} \<in> I_top"
              unfolding top1_unit_interval_topology_def subspace_topology_def by (by100 blast)
          qed
        qed
        have hp_cont: "top1_continuous_map_on (UNIV::real set) top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
          using Theorem_53_1 unfolding top1_covering_map_on_def by (by100 blast)
        show ?thesis unfolding heq
          by (rule top1_continuous_map_on_comp[OF hlin_cont hp_cont])
      qed
      show ?thesis unfolding top1_is_loop_on_def top1_is_path_on_def
        using hwn_cont hwn0 hwn1 by simp
    qed
    \<comment> \<open>If cis(2\<pi>ns) \<simeq> const_1 on S^1_complex, transfer to: w_n \<simeq> const on S^1.\<close>
    have hwn_const: "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
        ?wn (top1_constant_path (1, 0))"
    proof -
      \<comment> \<open>The map \<psi>(z) = (Re z, Im z) is a homeomorphism S^1_complex \<rightarrow> S^1.
         cis(2\<pi>ns) = \<psi>\<inverse>(w_n(s)), so w_n = \<psi> \<circ> cis(2\<pi>ns).
         hzp0_const gives cis(2\<pi>ns) \<simeq> const_1 in S^1_complex.
         Applying \<psi>: w_n \<simeq> \<psi>(const_1) = const_{(1,0)} in S^1.\<close>
      let ?\<psi> = "\<lambda>z::complex. (Re z, Im z)"
      \<comment> \<open>w_n = \<psi> \<circ> (\<lambda>s. z^n \<circ> p0 s) since R_to_S1(ns) = (cos 2\<pi>ns, sin 2\<pi>ns) = (Re(cis(2\<pi>ns)), Im(cis(2\<pi>ns))).\<close>
      have hwn_eq: "\<And>s. ?wn s = ?\<psi> (((\<lambda>z. z^n) \<circ> ?p0) s)"
        unfolding top1_R_to_S1_def comp_def
        by (simp add: DeMoivre algebra_simps)
      have hconst_eq: "\<And>s. top1_constant_path (1::real, 0::real) s = ?\<psi> (top1_constant_path (1::complex) s)"
        unfolding top1_constant_path_def by simp
      \<comment> \<open>\<psi> is continuous S^1_complex \<rightarrow> S^1.\<close>
      have h\<psi>_cont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
          top1_S1 top1_S1_topology ?\<psi>"
      proof -
        have h\<psi>_map: "\<And>z. z \<in> top1_S1_complex \<Longrightarrow> ?\<psi> z \<in> top1_S1"
          unfolding top1_S1_complex_def top1_S1_def
          by (auto simp: cmod_def)
        have h\<psi>_cont_univ: "continuous_on UNIV (\<lambda>z::complex. (Re z, Im z))"
          by (intro continuous_intros)
        \<comment> \<open>For open V in top1_S1_topology, preimage under \<psi> is open in top1_S1_complex_topology.\<close>
        show ?thesis unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix z assume "z \<in> top1_S1_complex" thus "?\<psi> z \<in> top1_S1" by (rule h\<psi>_map)
        next
          fix V assume hV: "V \<in> top1_S1_topology"
          then obtain W where hWo: "W \<in> product_topology_on top1_open_sets top1_open_sets"
              and hVeq: "V = top1_S1 \<inter> W"
            using hV unfolding top1_S1_topology_def subspace_topology_def by (by100 auto)
          \<comment> \<open>W is open in R^2. ?\<psi>\<inverse>(W) is open in C (by continuity of Re, Im).\<close>
          have hWopen: "open W"
          proof -
            have "W \<in> (top1_open_sets :: (real \<times> real) set set)"
              using hWo product_topology_on_open_sets_real2 by (by100 metis)
            thus ?thesis unfolding top1_open_sets_def by (by100 blast)
          qed
          have hpre_open: "open (?\<psi> -` W)"
          proof -
            have "open (?\<psi> -` W \<inter> UNIV)"
              using iffD1[OF continuous_on_open_vimage[OF open_UNIV] h\<psi>_cont_univ] hWopen by (by100 blast)
            thus ?thesis by simp
          qed
          have hpre_os: "?\<psi> -` W \<in> top1_open_sets"
            using hpre_open unfolding top1_open_sets_def by (by100 blast)
          have "{z \<in> top1_S1_complex. ?\<psi> z \<in> V} = top1_S1_complex \<inter> (?\<psi> -` W)"
            unfolding hVeq using h\<psi>_map by (by100 auto)
          thus "{z \<in> top1_S1_complex. ?\<psi> z \<in> V} \<in> top1_S1_complex_topology"
            unfolding top1_S1_complex_topology_def subspace_topology_def
            using hpre_os by (by100 blast)
        qed
      qed
      \<comment> \<open>Apply \<psi> to the homotopy: \<psi>\<circ>(z^n \<circ> p0) \<simeq> \<psi>\<circ>const_1 in S^1.\<close>
      have hTS1_loc: "is_topology_on top1_S1 top1_S1_topology"
        unfolding top1_S1_topology_def
        by (rule subspace_topology_is_topology_on[OF
              product_topology_on_is_topology_on[OF
                top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
                simplified]]) simp
      have hTS1c: "is_topology_on top1_S1_complex top1_S1_complex_topology"
        unfolding top1_S1_complex_topology_def
        by (rule subspace_topology_is_topology_on[OF top1_open_sets_is_topology_on_UNIV])
           (simp add: top1_S1_complex_def)
      have hpsi_hom: "top1_path_homotopic_on top1_S1 top1_S1_topology
          (?\<psi> 1) (?\<psi> 1) (?\<psi> \<circ> ((\<lambda>z. z^n) \<circ> ?p0)) (?\<psi> \<circ> top1_constant_path 1)"
        by (rule continuous_preserves_path_homotopic[OF hTS1c hTS1_loc h\<psi>_cont hzp0_const])
      \<comment> \<open>Simplify: \<psi>(1) = (1,0), \<psi>\<circ>(z^n\<circ>p0) = wn, \<psi>\<circ>const_1 = const_{(1,0)}.\<close>
      have h\<psi>1: "?\<psi> (1::complex) = (1::real, 0::real)" by simp
      have hwn_psi: "?\<psi> \<circ> ((\<lambda>z. z^n) \<circ> ?p0) = ?wn"
        by (rule ext) (simp add: hwn_eq)
      have hconst_psi: "?\<psi> \<circ> top1_constant_path (1::complex) = top1_constant_path (1::real, 0::real)"
        by (rule ext) (simp add: top1_constant_path_def)
      show ?thesis using hpsi_hom unfolding h\<psi>1 hwn_psi hconst_psi .
    qed
    \<comment> \<open>Lift of w_n from 0: s \<mapsto> n*s, a path in R from 0 to n.\<close>
    have hft_wn: "top1_is_path_on (UNIV::real set) top1_open_sets 0 (real n) (\<lambda>s. real n * s)"
      unfolding top1_is_path_on_def
    proof (intro conjI)
      show "top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets (\<lambda>s. real n * s)"
      proof -
        have hcont: "continuous_on UNIV (\<lambda>s::real. real n * s)" by (intro continuous_intros)
        show ?thesis
          unfolding top1_continuous_map_on_def
        proof (intro conjI ballI)
          fix s :: real assume "s \<in> I_set" show "real n * s \<in> (UNIV::real set)" by simp
        next
          fix V :: "real set" assume hV: "V \<in> top1_open_sets"
          have hVo: "open V" using hV unfolding top1_open_sets_def by (by100 blast)
          have "open ((\<lambda>s::real. real n * s) -` V \<inter> UNIV)"
            using iffD1[OF continuous_on_open_vimage[OF open_UNIV] hcont] hVo by (by100 blast)
          hence hpre: "open ((\<lambda>s::real. real n * s) -` V)" by simp
          have hpre_os: "(\<lambda>s::real. real n * s) -` V \<in> top1_open_sets"
            using hpre unfolding top1_open_sets_def by (by100 blast)
          have "{s \<in> I_set. real n * s \<in> V} = I_set \<inter> ((\<lambda>s. real n * s) -` V)" by (by100 auto)
          thus "{s \<in> I_set. real n * s \<in> V} \<in> I_top"
            unfolding top1_unit_interval_topology_def subspace_topology_def
            using hpre_os by (by100 blast)
        qed
      qed
      show "(\<lambda>s::real. real n * s) 0 = 0" by simp
      show "(\<lambda>s::real. real n * s) 1 = real n" by simp
    qed
    have hft_wn_lift: "\<forall>s\<in>I_set. top1_R_to_S1 (real n * s) = ?wn s" by simp
    \<comment> \<open>Lift of const from 0: s \<mapsto> 0, a path in R from 0 to 0.\<close>
    have hft_const: "top1_is_path_on (UNIV::real set) top1_open_sets 0 0 (\<lambda>_. 0::real)"
      unfolding top1_is_path_on_def
      using top1_continuous_map_on_const[OF
        top1_unit_interval_topology_is_topology_on
        top1_open_sets_is_topology_on_UNIV UNIV_I] by simp
    have hft_const_lift: "\<forall>s\<in>I_set. top1_R_to_S1 ((\<lambda>_. 0::real) s) = top1_constant_path (1, 0) s"
      unfolding top1_constant_path_def top1_R_to_S1_def by simp
    \<comment> \<open>By Theorem 54.3: lifts of homotopic paths from same start have same endpoint.\<close>
    have hTS1': "is_topology_on top1_S1 top1_S1_topology"
      unfolding top1_S1_topology_def
      by (rule subspace_topology_is_topology_on[OF
            product_topology_on_is_topology_on[OF
              top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV,
              simplified]]) simp
    have hcov': "top1_covering_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
      by (rule Theorem_53_1)
    have hp0': "top1_R_to_S1 0 = (1, 0)" unfolding top1_R_to_S1_def by simp
    have h0R': "(0::real) \<in> (UNIV::real set)" by simp
    have h10S1: "(1::real, 0::real) \<in> top1_S1" unfolding top1_S1_def by (by100 simp)
    have hwn_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) ?wn"
      using hwn_loop unfolding top1_is_loop_on_def .
    have hconst_path: "top1_is_path_on top1_S1 top1_S1_topology (1, 0) (1, 0) (top1_constant_path (1, 0))"
      using top1_constant_path_is_loop[OF hTS1' h10S1] unfolding top1_is_loop_on_def .
    have "real n = (0::real)"
      using conjunct1[OF Theorem_54_3[OF hcov'
        top1_open_sets_is_topology_on_UNIV hTS1' h0R' hp0'
        hwn_path hconst_path hwn_const
        hft_wn hft_wn_lift hft_const hft_const_lift]] .
    thus False using hn by simp
  qed
  show False using hnul_S1 hnontrivial by (by100 blast)
qed

(** Step 3: FTA for polynomials with |a_{n-1}| + ... + |a_0| < 1.

    Munkres' proof: by contradiction. If there is no root in B^2, define
    k: B^2 \<rightarrow> C - {0} by k(z) = z^n + \<Sum> a_k z^k. Let h = k|_{S^1}. Since
    h extends over B^2, h is nulhomotopic. But F(z,t) = z^n + t*(\<Sum> a_k z^k)
    is a homotopy from g = z^n (Step 2: NOT nulhomotopic) to h in C - {0};
    F(z,t) \<ne> 0 because |F| \<ge> 1 - t*(\<Sum>|a_k|) > 0. Contradiction. **)
lemma Theorem_56_1_step_3:
  fixes a :: "nat \<Rightarrow> complex" and n :: nat
  assumes hn: "n > 0"
  and hbound: "(\<Sum>k<n. cmod (a k)) < 1"
  shows "\<exists>z. cmod z \<le> 1 \<and> z^n + (\<Sum>k<n. a k * z^k) = 0"
proof (rule ccontr)
  assume hno: "\<not> (\<exists>z. cmod z \<le> 1 \<and> z^n + (\<Sum>k<n. a k * z^k) = 0)"
  \<comment> \<open>Define k: B^2 \<rightarrow> C-{0} by k(z) = z^n + \<Sum> a_j z^j.\<close>
  let ?k = "\<lambda>z::complex. z^n + (\<Sum>j<n. a j * z^j)"
  have hk_nonzero: "\<And>z. cmod z \<le> 1 \<Longrightarrow> ?k z \<noteq> 0" using hno by blast
  \<comment> \<open>Let h be k restricted to S^1.\<close>
  let ?h = "\<lambda>z::complex. ?k z"
  \<comment> \<open>h is nulhomotopic in C-{0} because it extends to B^2 \<rightarrow> C-{0}.\<close>
  have hh_nulhomo: "top1_nulhomotopic_on top1_S1_complex top1_S1_complex_topology
                       top1_C_minus_0 top1_C_minus_0_topology ?h"
  proof -
    \<comment> \<open>Homotopy H(z,t) = k((1-t)*z) contracts S^1 to the point k(0).\<close>
    let ?H = "\<lambda>(z::complex, t::real). ?k ((1 - complex_of_real t) * z)"
    have hk0_nz: "?k 0 \<noteq> 0" using hk_nonzero[of 0] by simp
    have hk0_C: "?k 0 \<in> top1_C_minus_0" using hk0_nz unfolding top1_C_minus_0_def by (by100 blast)
    \<comment> \<open>H(z,0) = k(z) = h(z), H(z,1) = k(0).\<close>
    have hH0: "\<forall>z\<in>top1_S1_complex. ?H (z, 0) = ?h z" by (simp add: case_prod_beta)
    have hH1: "\<forall>z\<in>top1_S1_complex. ?H (z, 1) = ?k 0" by (simp add: case_prod_beta)
    \<comment> \<open>H maps S^1 \<times> I to C-{0}: (1-t)*z \<in> B^2 when z \<in> S^1, t \<in> I.\<close>
    have hH_range: "\<And>p. p \<in> top1_S1_complex \<times> I_set \<Longrightarrow> ?H p \<in> top1_C_minus_0"
    proof -
      fix p assume hp: "p \<in> top1_S1_complex \<times> I_set"
      have hz: "cmod (fst p) = 1" using hp unfolding top1_S1_complex_def by (by100 auto)
      have ht: "snd p \<in> I_set" using hp by (by100 auto)
      have ht0: "0 \<le> snd p" and ht1: "snd p \<le> 1"
        using ht unfolding top1_unit_interval_def by (by100 auto)+
      have "cmod ((1 - complex_of_real (snd p)) * fst p) = cmod (1 - complex_of_real (snd p))"
        using hz by (simp add: norm_mult)
      also have "\<dots> = \<bar>1 - snd p\<bar>"
        by (metis norm_of_real of_real_1 of_real_diff)
      finally have "cmod ((1 - complex_of_real (snd p)) * fst p) = \<bar>1 - snd p\<bar>" .
      also have "\<dots> = 1 - snd p" using ht0 ht1 by (by100 auto)
      also have "\<dots> \<le> 1" using ht0 by (by100 linarith)
      finally have "cmod ((1 - complex_of_real (snd p)) * fst p) \<le> 1" .
      hence "?k ((1 - complex_of_real (snd p)) * fst p) \<noteq> 0"
        by (rule hk_nonzero)
      thus "?H p \<in> top1_C_minus_0" unfolding top1_C_minus_0_def
        by (simp add: case_prod_beta)
    qed
    \<comment> \<open>H is continuous (polynomial composed with affine map).\<close>
    have hH_std: "continuous_on UNIV (\<lambda>p::complex\<times>real. ?k ((1 - complex_of_real (snd p)) * fst p))"
      by (intro continuous_intros)
    have hH_cont_univ: "continuous_on UNIV ?H"
      using hH_std by (simp add: case_prod_beta)
    \<comment> \<open>Transfer to custom topologies.\<close>
    have hdom_eq: "product_topology_on top1_S1_complex_topology I_top
        = subspace_topology UNIV (top1_open_sets :: (complex \<times> real) set set)
            (top1_S1_complex \<times> I_set)"
    proof -
      have "product_topology_on top1_S1_complex_topology I_top
          = product_topology_on
              (subspace_topology UNIV (top1_open_sets::complex set set) top1_S1_complex)
              (subspace_topology UNIV (top1_open_sets::real set set) I_set)"
        unfolding top1_S1_complex_topology_def top1_unit_interval_topology_def by (rule refl)
      also have "\<dots> = subspace_topology (UNIV \<times> UNIV)
          (product_topology_on (top1_open_sets::complex set set) (top1_open_sets::real set set))
          (top1_S1_complex \<times> I_set)"
        by (rule Theorem_16_3[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV])
      also have "\<dots> = subspace_topology UNIV (top1_open_sets :: (complex \<times> real) set set)
          (top1_S1_complex \<times> I_set)"
        by (simp add: product_topology_on_open_sets)
      finally show ?thesis .
    qed
    have hH_top: "top1_continuous_map_on (top1_S1_complex \<times> I_set)
        (product_topology_on top1_S1_complex_topology I_top)
        top1_C_minus_0 top1_C_minus_0_topology ?H"
    proof -
      have "top1_continuous_map_on (top1_S1_complex \<times> I_set)
          (subspace_topology UNIV (top1_open_sets :: (complex \<times> real) set set) (top1_S1_complex \<times> I_set))
          top1_C_minus_0 (subspace_topology UNIV (top1_open_sets :: complex set set) top1_C_minus_0) ?H"
        by (rule top1_continuous_map_on_subspace_open_sets[OF hH_range hH_cont_univ])
      thus ?thesis unfolding hdom_eq top1_C_minus_0_topology_def .
    qed
    \<comment> \<open>h is continuous (polynomial on S^1 to C-{0}).\<close>
    have hh_cont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology ?h"
      unfolding top1_S1_complex_topology_def top1_C_minus_0_topology_def
    proof (rule top1_continuous_map_on_subspace_open_sets)
      fix z assume "z \<in> top1_S1_complex"
      hence "cmod z = 1" unfolding top1_S1_complex_def by (by100 simp)
      hence "cmod z \<le> 1" by (by100 simp)
      hence "?k z \<noteq> 0" by (rule hk_nonzero)
      thus "?h z \<in> top1_C_minus_0" unfolding top1_C_minus_0_def by (by100 blast)
    next
      show "continuous_on UNIV ?h" by (intro continuous_intros)
    qed
    \<comment> \<open>const_{k(0)} is continuous.\<close>
    have hconst_cont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology (\<lambda>_. ?k 0)"
      unfolding top1_S1_complex_topology_def top1_C_minus_0_topology_def
      by (rule top1_continuous_map_on_subspace_open_sets)
         (use hk0_C in \<open>auto simp: top1_C_minus_0_def intro: continuous_intros\<close>)
    \<comment> \<open>Assembly: homotopic h const → nulhomotopic.\<close>
    have "top1_homotopic_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology ?h (\<lambda>_. ?k 0)"
      unfolding top1_homotopic_on_def using hh_cont hconst_cont hH_top hH0 hH1
      by (by100 blast)
    thus ?thesis unfolding top1_nulhomotopic_on_def using hk0_C by (by100 blast)
  qed
  \<comment> \<open>Homotopy F(z,t) = z^n + t*\<Sum>a_j z^j from g=z^n to h, all in C-{0}.\<close>
  let ?F = "\<lambda>(z::complex, t::real). z^n + complex_of_real t * (\<Sum>j<n. a j * z^j)"
  have hF_nonzero: "\<And>z t. cmod z = 1 \<Longrightarrow> t \<in> I_set \<Longrightarrow>
     z^n + complex_of_real t * (\<Sum>j<n. a j * z^j) \<noteq> 0"
    \<comment> \<open>Munkres inequality: |F| \<ge> 1 - t(\<Sum>|a_k|) > 0 since t \<le> 1 and \<Sum>|a_k| < 1.\<close>
  proof -
    fix z :: complex and t :: real
    assume hz: "cmod z = 1" and ht: "t \<in> I_set"
    have ht0: "t \<ge> 0" using ht unfolding top1_unit_interval_def by simp
    have ht1: "t \<le> 1" using ht unfolding top1_unit_interval_def by simp
    have hzn: "cmod (z^n) = 1" using hz by (simp add: norm_power)
    have h_sum_bound: "cmod (\<Sum>j<n. a j * z^j) \<le> (\<Sum>j<n. cmod (a j))"
    proof -
      have "cmod (\<Sum>j<n. a j * z^j) \<le> (\<Sum>j<n. cmod (a j * z^j))"
        by (rule norm_sum)
      also have "\<dots> = (\<Sum>j<n. cmod (a j) * (cmod z)^j)"
        by (simp add: norm_mult norm_power)
      also have "\<dots> = (\<Sum>j<n. cmod (a j))" using hz by simp
      finally show ?thesis .
    qed
    have ht_sum: "t * (\<Sum>j<n. cmod (a j)) < 1"
    proof (cases "(\<Sum>j<n. cmod (a j)) = 0")
      case True thus ?thesis by simp
    next
      case False
      have hpos: "(\<Sum>j<n. cmod (a j)) > 0"
        using False sum_nonneg[of "{..<n}" "\<lambda>j. cmod (a j)"] by simp
      have "t * (\<Sum>j<n. cmod (a j)) \<le> 1 * (\<Sum>j<n. cmod (a j))"
        using ht1 hpos by (simp add: mult_right_mono)
      also have "\<dots> < 1" using hbound by simp
      finally show ?thesis .
    qed
    have hF_abs: "cmod (z^n + complex_of_real t * (\<Sum>j<n. a j * z^j))
                \<ge> 1 - t * (\<Sum>j<n. cmod (a j))"
    proof -
      let ?A = "z^n"
      let ?B = "complex_of_real t * (\<Sum>j<n. a j * z^j)"
      have htri: "cmod ?A \<le> cmod (?A + ?B) + cmod ?B"
        using norm_triangle_ineq4[of "?A + ?B" ?B] by (simp add: norm_minus_commute)
      have hnormB: "cmod ?B = t * cmod (\<Sum>j<n. a j * z^j)"
        by (simp add: norm_mult ht0)
      have hB_le: "cmod ?B \<le> t * (\<Sum>j<n. cmod (a j))"
        using hnormB h_sum_bound ht0 by (simp add: mult_left_mono)
      show ?thesis using htri hzn hB_le by linarith
    qed
    have "1 - t * (\<Sum>j<n. cmod (a j)) > 0" using ht_sum by simp
    hence "cmod (z^n + complex_of_real t * (\<Sum>j<n. a j * z^j)) > 0" using hF_abs by linarith
    thus "z^n + complex_of_real t * (\<Sum>j<n. a j * z^j) \<noteq> 0" by auto
  qed
  have hF_cont: "top1_continuous_map_on (top1_S1_complex \<times> I_set)
                   (product_topology_on top1_S1_complex_topology I_top)
                   top1_C_minus_0 top1_C_minus_0_topology ?F"
  proof -
    have hF_std: "continuous_on UNIV (\<lambda>p::complex\<times>real. fst p^n +
        complex_of_real (snd p) * (\<Sum>j<n. a j * fst p^j))"
      by (intro continuous_intros)
    have hF_range: "\<And>p. p \<in> top1_S1_complex \<times> I_set \<Longrightarrow> ?F p \<in> top1_C_minus_0"
    proof -
      fix p assume hp: "p \<in> top1_S1_complex \<times> I_set"
      have "cmod (fst p) = 1" using hp unfolding top1_S1_complex_def by (by100 auto)
      have "snd p \<in> I_set" using hp by (by100 auto)
      have "?F p \<noteq> 0" using hF_nonzero[OF \<open>cmod (fst p) = 1\<close> \<open>snd p \<in> I_set\<close>]
        by (simp add: case_prod_beta)
      thus "?F p \<in> top1_C_minus_0" unfolding top1_C_minus_0_def by (by100 blast)
    qed
    have hdom_eq: "product_topology_on top1_S1_complex_topology I_top
        = subspace_topology UNIV (top1_open_sets :: (complex \<times> real) set set)
            (top1_S1_complex \<times> I_set)"
    proof -
      have "product_topology_on top1_S1_complex_topology I_top
          = product_topology_on
              (subspace_topology UNIV (top1_open_sets::complex set set) top1_S1_complex)
              (subspace_topology UNIV (top1_open_sets::real set set) I_set)"
        unfolding top1_S1_complex_topology_def top1_unit_interval_topology_def by (rule refl)
      also have "\<dots> = subspace_topology (UNIV \<times> UNIV)
          (product_topology_on (top1_open_sets::complex set set) (top1_open_sets::real set set))
          (top1_S1_complex \<times> I_set)"
        by (rule Theorem_16_3[OF top1_open_sets_is_topology_on_UNIV top1_open_sets_is_topology_on_UNIV])
      also have "\<dots> = subspace_topology UNIV (top1_open_sets :: (complex \<times> real) set set)
          (top1_S1_complex \<times> I_set)"
        by (simp add: product_topology_on_open_sets)
      finally show ?thesis .
    qed
    have hF_cont_univ: "continuous_on UNIV ?F"
      using hF_std by (simp add: case_prod_beta comp_def)
    have "top1_continuous_map_on (top1_S1_complex \<times> I_set)
        (subspace_topology UNIV (top1_open_sets :: (complex \<times> real) set set) (top1_S1_complex \<times> I_set))
        top1_C_minus_0 (subspace_topology UNIV (top1_open_sets :: complex set set) top1_C_minus_0) ?F"
      by (rule top1_continuous_map_on_subspace_open_sets[OF hF_range hF_cont_univ])
    thus ?thesis unfolding hdom_eq top1_C_minus_0_topology_def .
  qed
  \<comment> \<open>g(z) = z^n is NOT nulhomotopic by Step 2, but would be nulhomotopic via F.\<close>
  have hg_notnull: "\<not> top1_nulhomotopic_on top1_S1_complex top1_S1_complex_topology
                       top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n)"
    using Theorem_56_1_step_2[OF hn] .
  have hg_nulhomo: "top1_nulhomotopic_on top1_S1_complex top1_S1_complex_topology
                       top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n)"
  proof -
    have hTR_c: "is_topology_on (UNIV::complex set) top1_open_sets"
      by (rule top1_open_sets_is_topology_on_UNIV)
    have hTS1c: "is_topology_on top1_S1_complex top1_S1_complex_topology"
      unfolding top1_S1_complex_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR_c]) simp
    have hTC0: "is_topology_on top1_C_minus_0 top1_C_minus_0_topology"
      unfolding top1_C_minus_0_topology_def
      by (rule subspace_topology_is_topology_on[OF hTR_c]) simp
    \<comment> \<open>F(z,0) = z^n, F(z,1) = h(z).\<close>
    have hF0: "\<forall>z\<in>top1_S1_complex. ?F (z, 0) = z^n"
      by (simp add: case_prod_beta)
    have hF1: "\<forall>z\<in>top1_S1_complex. ?F (z, 1) = ?h z"
      by (simp add: case_prod_beta)
    \<comment> \<open>z^n is continuous S^1 \<rightarrow> C-{0} (polynomial, nonvanishing on S^1).\<close>
    have hg_cont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n)"
      unfolding top1_S1_complex_topology_def top1_C_minus_0_topology_def
      by (rule top1_continuous_map_on_subspace_open_sets)
         (auto simp: top1_S1_complex_def top1_C_minus_0_def norm_power hn
               intro: continuous_intros)
    \<comment> \<open>h is continuous (from nulhomotopic).\<close>
    have hh_cont: "top1_continuous_map_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology ?h"
      using hh_nulhomo unfolding top1_nulhomotopic_on_def top1_homotopic_on_def by (by100 blast)
    \<comment> \<open>F gives homotopy from z^n to h.\<close>
    have hhom_g_h: "top1_homotopic_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n) ?h"
      unfolding top1_homotopic_on_def
      using hg_cont hh_cont hF_cont hF0 hF1 by (by100 blast)
    \<comment> \<open>Symmetry: h ≃ z^n.\<close>
    have hhom_h_g: "top1_homotopic_on top1_S1_complex top1_S1_complex_topology
        top1_C_minus_0 top1_C_minus_0_topology ?h (\<lambda>z. z^n)"
      by (rule Lemma_51_1_homotopic_sym[OF hhom_g_h hTS1c])
    \<comment> \<open>Transitivity: h nulhomotopic + h ≃ z^n \<Rightarrow> z^n nulhomotopic.\<close>
    show ?thesis
      by (rule nulhomotopic_homotopic_trans[OF hTS1c hTC0 hh_nulhomo hhom_h_g])
  qed
  show False using hg_notnull hg_nulhomo by blast
qed

(** Step 4: FTA general case: any monic polynomial has a root.
    Reduction: substitute x = cy for large c to reduce to Step 3.
    This is the statement of Theorem_56_1 proper in Munkres. **)
theorem Theorem_56_1_FTA:
  fixes a :: "nat \<Rightarrow> complex" and n :: nat
  assumes "n > 0"
  shows "\<exists>z. z^n + (\<Sum>k<n. a k * z^k) = 0"
proof -
  \<comment> \<open>Munkres Step 4: Choose c large so that \<Sum> |a_k/c^{n-k}| < 1.\<close>
  \<comment> \<open>Substitute x = cy: equation becomes y^n + \<Sum> (a_k / c^{n-k}) y^k = 0.\<close>
  \<comment> \<open>By Step 3, there's a root y_0 with |y_0| \<le> 1; then x_0 = c y_0 is a root.\<close>
  \<comment> \<open>Pick c = max 1 (1 + 2 * n * \<Sum> cmod (a k)). Then c \<ge> 1 and c > 2 n M where
      M = \<Sum> cmod (a k), so each term cmod(a k)/c^(n-k) \<le> cmod(a k)/c < M/(2nM) = 1/(2n)
      when M > 0, giving sum < 1/2 < 1. When M = 0 each cmod(a k) = 0, sum = 0 < 1.\<close>
  define M where "M = (\<Sum>k<n. cmod (a k))"
  define c where "c = M + 1"
  have hM: "M \<ge> 0" unfolding M_def by (simp add: sum_nonneg)
  have hc: "c > 0" unfolding c_def using hM by simp
  have hc_ge1: "c \<ge> 1" unfolding c_def using hM by simp
  have hc_pow_ge: "\<forall>k<n. c ^ (n - k) \<ge> c"
  proof (intro allI impI)
    fix k assume hk: "k < n"
    have hge1: "n - k \<ge> 1" using hk by simp
    have "c ^ 1 \<le> c ^ (n - k)"
      by (rule power_increasing[OF hge1 hc_ge1])
    thus "c ^ (n - k) \<ge> c" by simp
  qed
  have hsum_small: "(\<Sum>k<n. cmod (a k) / c ^ (n - k)) < 1"
  proof -
    have h_each: "\<forall>k<n. cmod (a k) / c ^ (n - k) \<le> cmod (a k) / c"
    proof (intro allI impI)
      fix k assume hk: "k < n"
      have hcpos: "c ^ (n - k) > 0" using hc by (simp add: zero_less_power)
      have hcpow_ge_c: "c ^ (n - k) \<ge> c" using hc_pow_ge hk by blast
      have hak: "cmod (a k) \<ge> 0" by simp
      show "cmod (a k) / c ^ (n - k) \<le> cmod (a k) / c"
        using hc hcpos hcpow_ge_c hak by (simp add: frac_le)
    qed
    have h_sum_le: "(\<Sum>k<n. cmod (a k) / c ^ (n - k)) \<le> (\<Sum>k<n. cmod (a k) / c)"
      by (rule sum_mono, simp add: h_each)
    also have "(\<Sum>k<n. cmod (a k) / c) = M / c"
      unfolding M_def by (simp add: sum_divide_distrib)
    also have "\<dots> < 1"
    proof -
      have "M / c < 1 \<longleftrightarrow> M < c" using hc by (simp add: divide_less_eq)
      moreover have "M < c" unfolding c_def by simp
      ultimately show ?thesis by blast
    qed
    finally show "(\<Sum>k<n. cmod (a k) / c ^ (n - k)) < 1" .
  qed
  \<comment> \<open>New coefficients a'_k = a_k / c^{n-k}.\<close>
  let ?a' = "\<lambda>k. a k / complex_of_real (c ^ (n - k))"
  have h_cmod_eq: "\<forall>k<n. cmod (?a' k) = cmod (a k) / c ^ (n - k)"
    using hc by (simp add: norm_divide norm_power)
  have hbound': "(\<Sum>k<n. cmod (?a' k)) < 1"
    using h_cmod_eq hsum_small by simp
  obtain y where hy: "cmod y \<le> 1" and hroot': "y^n + (\<Sum>k<n. ?a' k * y^k) = 0"
    using Theorem_56_1_step_3[OF assms hbound'] by blast
  let ?x = "complex_of_real c * y"
  let ?cc = "complex_of_real c"
  have hcc_nz: "?cc \<noteq> 0" using hc by simp
  \<comment> \<open>Term-wise identity: c^n * (a k / c^(n-k) * y^k) = a k * (c*y)^k when k<n.\<close>
  have h_term: "\<And>k. k < n \<Longrightarrow> ?cc^n * (?a' k * y^k) = a k * ?x^k"
  proof -
    fix k :: nat assume hk: "k < n"
    have hpow_split: "?cc^n = ?cc^(n-k) * ?cc^k"
      using hk by (simp add: power_add[symmetric])
    have hpow_eq: "?cc^(n-k) = complex_of_real (c^(n-k))" by simp
    have "?cc^n * (?a' k * y^k) = ?cc^(n-k) * ?cc^k * (a k / complex_of_real (c^(n-k)) * y^k)"
      using hpow_split by simp
    also have "\<dots> = ?cc^k * (a k * y^k)"
      using hpow_eq hcc_nz by (simp add: field_simps power_not_zero)
    also have "\<dots> = a k * ?x^k"
      by (simp add: power_mult_distrib mult.commute mult.left_commute)
    finally show "?cc^n * (?a' k * y^k) = a k * ?x^k" .
  qed
  have h_cn_sum: "?cc^n * (\<Sum>k<n. ?a' k * y^k) = (\<Sum>k<n. a k * ?x^k)"
  proof -
    have "?cc^n * (\<Sum>k<n. ?a' k * y^k) = (\<Sum>k<n. ?cc^n * (?a' k * y^k))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = (\<Sum>k<n. a k * ?x^k)"
      by (rule sum.cong, simp, rule h_term, simp)
    finally show ?thesis .
  qed
  have hxn_eq: "?x^n = ?cc^n * y^n" by (simp add: power_mult_distrib)
  \<comment> \<open>Multiply root equation by c^n to get x-root equation.\<close>
  have "?cc^n * (y^n + (\<Sum>k<n. ?a' k * y^k)) = 0" using hroot' by simp
  hence "?cc^n * y^n + ?cc^n * (\<Sum>k<n. ?a' k * y^k) = 0"
    by (simp add: distrib_left)
  hence "?x^n + (\<Sum>k<n. a k * ?x^k) = 0"
    using hxn_eq h_cn_sum by simp
  thus ?thesis by blast
qed

text \<open>Original form (FTA for arbitrary polynomials with nonzero leading coefficient).\<close>
corollary Theorem_56_1_FTA_leading:
  fixes a :: "nat \<Rightarrow> complex" and n :: nat
  assumes "n > 0" and "a n \<noteq> 0"
  shows "\<exists>z. (\<Sum>k\<le>n. a k * z^k) = 0"
proof -
  \<comment> \<open>Divide by a n to get monic form.\<close>
  let ?b = "\<lambda>k. a k / a n"
  have hbn: "?b n = 1" using assms(2) by simp
  have "\<exists>z. z^n + (\<Sum>k<n. ?b k * z^k) = 0"
    by (rule Theorem_56_1_FTA[OF assms(1)])
  then obtain z where hroot_monic: "z^n + (\<Sum>k<n. ?b k * z^k) = 0"
    by blast
  \<comment> \<open>This z is a root of the original polynomial too.\<close>
  have h_split: "(\<Sum>k\<le>n. a k * z^k) = (\<Sum>k<n. a k * z^k) + a n * z^n"
    by (simp add: lessThan_Suc_atMost[symmetric] sum.lessThan_Suc)
  have h_factor: "(\<Sum>k<n. a k * z^k) = a n * (\<Sum>k<n. ?b k * z^k)"
    by (simp add: sum_distrib_left assms(2) field_simps)
  have "(\<Sum>k\<le>n. a k * z^k) = a n * (z^n + (\<Sum>k<n. ?b k * z^k))"
    using h_split h_factor by (simp add: distrib_left mult.commute)
  thus ?thesis using hroot_monic assms(2) by fastforce
qed



text \<open>Specialized version for S^1 \<rightarrow> S^1.\<close>
lemma nulhomotopic_trivializes_loops:
  assumes hg: "top1_continuous_map_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology g"
      and hgnul: "top1_nulhomotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology g"
      and hg10: "g (1, 0) = (1::real, 0::real)"
      and hf: "top1_is_loop_on top1_S1 top1_S1_topology (1::real, 0::real) f"
  shows "top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0)
      (g \<circ> f) (top1_constant_path (1, 0))"
proof -
  \<comment> \<open>From nulhomotopy, extract c and homotopy H. Apply homotopy_induced_basepoint_change
     to get g\<circ>f ≃ bc(rev(\<alpha>), const_c) at g(1,0) = (1,0), where \<alpha>(t) = H((1,0),t).
     Then show bc(rev(\<alpha>), const_c) ≃ const by path algebra.\<close>
  obtain c where hcS1: "c \<in> top1_S1"
      and hhom: "top1_homotopic_on top1_S1 top1_S1_topology top1_S1 top1_S1_topology g (\<lambda>_. c)"
    using hgnul unfolding top1_nulhomotopic_on_def by (by100 blast)
  obtain H where hHcont: "top1_continuous_map_on (top1_S1 \<times> I_set)
          (product_topology_on top1_S1_topology I_top) top1_S1 top1_S1_topology H"
      and hH0: "\<forall>x\<in>top1_S1. H (x, 0) = g x"
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
  have hbc': "top1_loop_equiv_on top1_S1 top1_S1_topology (g (1, 0)) (g \<circ> f)
      (top1_basepoint_change_on top1_S1 top1_S1_topology c (g (1, 0))
         (top1_path_reverse (\<lambda>t. H ((1, 0), t))) (top1_constant_path c))"
  proof -
    have "(\<lambda>_. c) \<circ> f = top1_constant_path c"
      by (rule ext) (simp add: top1_constant_path_def comp_def)
    thus ?thesis using hbc by simp
  qed
  \<comment> \<open>From hbc', g \<circ> f ≃ bc(rev(\<alpha>), const_c) at g(1,0).
     Path algebra gives bc(rev(\<alpha>), const_c) ≃ const_{g(1,0)}:
       bc = \<alpha> * (const_c * rev(\<alpha>)), const_c * rev(\<alpha>) ≃ rev(\<alpha>) (left id),
       \<alpha> * rev(\<alpha>) ≃ const_{g(1,0)} (inverse).
     Same as the proof in hh_trivial_at_h10 (lines 9734-9790 of the True case).\<close>
  \<comment> \<open>Path algebra: show bc(rev(\<alpha>), const_c) ≃ const_{g(1,0)}, then chain with hbc'.\<close>
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
  have h\<alpha>_path: "top1_is_path_on top1_S1 top1_S1_topology (g (1, 0)) c ?\<alpha>"
    unfolding top1_is_path_on_def using h\<alpha>_cont
    by (auto simp: hH0[rule_format, OF h10S1] hH1[rule_format, OF h10S1])
  have hra: "top1_is_path_on top1_S1 top1_S1_topology c (g (1, 0)) (top1_path_reverse ?\<alpha>)"
    by (rule top1_path_reverse_is_path[OF h\<alpha>_path])
  have hconst_c: "top1_is_loop_on top1_S1 top1_S1_topology c (top1_constant_path c)"
    by (rule top1_constant_path_is_loop[OF hTS1 hcS1])
  have hbc_def: "top1_basepoint_change_on top1_S1 top1_S1_topology c (g (1, 0))
      (top1_path_reverse ?\<alpha>) (top1_constant_path c)
    = top1_path_product ?\<alpha> (top1_path_product (top1_constant_path c) (top1_path_reverse ?\<alpha>))"
    unfolding top1_basepoint_change_on_def top1_path_reverse_twice by (rule refl)
  have hchain: "top1_path_homotopic_on top1_S1 top1_S1_topology (g (1, 0)) (g (1, 0))
      (top1_basepoint_change_on top1_S1 top1_S1_topology c (g (1, 0))
         (top1_path_reverse ?\<alpha>) (top1_constant_path c))
      (top1_constant_path (g (1, 0)))"
    using Lemma_51_1_path_homotopic_trans[OF hTS1
        path_homotopic_product_right[OF hTS1 Theorem_51_2_left_identity[OF hTS1 hra] h\<alpha>_path,
          unfolded hbc_def[symmetric]]
        Theorem_51_2_invgerse_left[OF hTS1 h\<alpha>_path]] .
  have hbc_is_const: "top1_loop_equiv_on top1_S1 top1_S1_topology (g (1, 0))
      (top1_basepoint_change_on top1_S1 top1_S1_topology c (g (1, 0))
         (top1_path_reverse ?\<alpha>) (top1_constant_path c))
      (top1_constant_path (g (1, 0)))"
  proof -
    have hg10_S1: "g (1, 0) \<in> top1_S1"
      using hg h10S1 unfolding top1_continuous_map_on_def by (by100 blast)
    show ?thesis unfolding top1_loop_equiv_on_def
      using top1_basepoint_change_is_loop[OF hTS1 hra hconst_c]
            top1_constant_path_is_loop[OF hTS1 hg10_S1]
            hchain by (by100 blast)
  qed
  have hresult: "top1_loop_equiv_on top1_S1 top1_S1_topology (g (1, 0)) (g \<circ> f)
      (top1_constant_path (g (1, 0)))"
    by (rule top1_loop_equiv_on_trans[OF hTS1 hbc' hbc_is_const])
  have "top1_path_homotopic_on top1_S1 top1_S1_topology (g (1, 0)) (g (1, 0))
      (g \<circ> f) (top1_constant_path (g (1, 0)))"
    using hresult unfolding top1_loop_equiv_on_def by (by100 blast)
  thus ?thesis using hg10 by simp
qed

end
