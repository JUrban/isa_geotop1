theory AlgTop
  imports Top1_Ch5_8
begin

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

text \<open>Helper: concatenation of homotopies via pasting lemma.
  Given F: X\<times>I \<rightarrow> Y and F': X\<times>I \<rightarrow> Y with F(x,1) = F'(x,0), define
  G(x,t) = F(x,2t) for t\<le>1/2, G(x,t) = F'(x,2t-1) for t\<ge>1/2.\<close>
lemma homotopy_concat_continuous:
  assumes hF: "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F"
      and hF': "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY F'"
      and hmatch: "\<forall>x\<in>X. F (x, 1) = F' (x, 0)"
  shows "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY
    (\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1))"
  \<comment> \<open>Proof structure identical to path_homotopy_concat_continuous but for X \<times> I \<rightarrow> Y.\<close>
  sorry

lemma Lemma_51_1_homotopic_trans:
  assumes h1: "top1_homotopic_on X TX Y TY f f'"
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
    by (rule homotopy_concat_continuous[OF hF hF' hmatch])
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
lemma path_homotopy_concat_continuous:
  assumes hF: "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F"
      and hF': "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX F'"
      and hmatch: "\<forall>s\<in>I_set. F (s, 1) = F' (s, 0)"
  shows "top1_continuous_map_on (I_set \<times> I_set) II_topology X TX
    (\<lambda>p. if snd p \<le> 1/2 then F (fst p, 2 * snd p) else F' (fst p, 2 * snd p - 1))"
proof -
  \<comment> \<open>Close sets A = I \<times> [0, 1/2] and B = I \<times> [1/2, 1].\<close>
  let ?A = "I_set \<times> {t\<in>I_set. t \<le> 1/2}"
  let ?B = "I_set \<times> {t\<in>I_set. t \<ge> 1/2}"
  have hA_closed: "closedin_on (I_set \<times> I_set) II_topology ?A" sorry
  have hB_closed: "closedin_on (I_set \<times> I_set) II_topology ?B" sorry
  have hcover: "I_set \<times> I_set = ?A \<union> ?B"
    unfolding top1_unit_interval_def by auto
  \<comment> \<open>On A, (s,t) \<mapsto> F(s, 2t) is continuous.\<close>
  have hfA: "top1_continuous_map_on ?A (subspace_topology (I_set \<times> I_set) II_topology ?A)
                                   X TX (\<lambda>p. F (fst p, 2 * snd p))" sorry
  \<comment> \<open>On B, (s,t) \<mapsto> F'(s, 2t-1) is continuous.\<close>
  have hfB: "top1_continuous_map_on ?B (subspace_topology (I_set \<times> I_set) II_topology ?B)
                                   X TX (\<lambda>p. F' (fst p, 2 * snd p - 1))" sorry
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
  \<comment> \<open>Apply pasting lemma (Theorem 18.3).\<close>
  show ?thesis sorry
qed

lemma Lemma_51_1_path_homotopic_trans:
  assumes h1: "top1_path_homotopic_on X TX x0 x1 f f'"
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
    by (rule path_homotopy_concat_continuous[OF hF hF' hmatch])
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
  assumes "top1_continuous_map_on I_set I_top X TX f"
      and "top1_continuous_map_on I_set I_top X TX g"
      and "f 1 = g 0"
  shows "top1_continuous_map_on I_set I_top X TX (top1_path_product f g)"
  sorry

lemma top1_path_product_is_path:
  assumes hf: "top1_is_path_on X TX x0 x1 f"
      and hg: "top1_is_path_on X TX x1 x2 g"
  shows "top1_is_path_on X TX x0 x2 (top1_path_product f g)"
proof -
  have hfc: "top1_continuous_map_on I_set I_top X TX f" and hf0: "f 0 = x0" and hf1: "f 1 = x1"
    using hf unfolding top1_is_path_on_def by blast+
  have hgc: "top1_continuous_map_on I_set I_top X TX g" and hg0: "g 0 = x1" and hg1: "g 1 = x2"
    using hg unfolding top1_is_path_on_def by blast+
  have hmatch: "f 1 = g 0" using hf1 hg0 by simp
  have hcont: "top1_continuous_map_on I_set I_top X TX (top1_path_product f g)"
    by (rule top1_path_product_continuous[OF hfc hgc hmatch])
  have hstart: "top1_path_product f g 0 = x0"
    unfolding top1_path_product_def using hf0 by simp
  have hend: "top1_path_product f g 1 = x2"
    unfolding top1_path_product_def using hg1 by simp
  show ?thesis
    unfolding top1_is_path_on_def using hcont hstart hend by blast
qed

(** from \<S>51 Theorem 51.2: groupoid properties of * **)
lemma Theorem_51_2_associativity:
  assumes "top1_is_path_on X TX x0 x1 f"
      and "top1_is_path_on X TX x1 x2 g"
      and "top1_is_path_on X TX x2 x3 h"
  shows "top1_path_homotopic_on X TX x0 x3
    (top1_path_product f (top1_path_product g h))
    (top1_path_product (top1_path_product f g) h)"
  sorry

lemma Theorem_51_2_left_identity:
  assumes "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x1
    (top1_path_product (top1_constant_path x0) f) f"
  sorry

lemma Theorem_51_2_right_identity:
  assumes "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x1
    (top1_path_product f (top1_constant_path x1)) f"
  sorry

lemma Theorem_51_2_invgerse_left:
  assumes "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x0 x0
    (top1_path_product f (top1_path_reverse f)) (top1_constant_path x0)"
  sorry

lemma Theorem_51_2_invgerse_right:
  assumes "top1_is_path_on X TX x0 x1 f"
  shows "top1_path_homotopic_on X TX x1 x1
    (top1_path_product (top1_path_reverse f) f) (top1_constant_path x1)"
  sorry

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
  assumes hf: "top1_is_loop_on X TX x0 f" and hg: "top1_is_loop_on X TX x0 g"
  shows "top1_is_loop_on X TX x0 (top1_path_product f g)"
proof -
  have "top1_is_path_on X TX x0 x0 f" using hf unfolding top1_is_loop_on_def .
  moreover have "top1_is_path_on X TX x0 x0 g" using hg unfolding top1_is_loop_on_def .
  ultimately have "top1_is_path_on X TX x0 x0 (top1_path_product f g)"
    by (rule top1_path_product_is_path)
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
  assumes "top1_loop_equiv_on X TX x0 f g"
      and "top1_loop_equiv_on X TX x0 g h"
  shows "top1_loop_equiv_on X TX x0 f h"
  using assms Lemma_51_1_path_homotopic_trans[of X TX x0 x0 f g h]
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
  assumes "top1_is_path_on X TX x0 x1 alpha"
      and "top1_is_loop_on X TX x0 f"
      and "top1_is_loop_on X TX x0 g"
  shows "top1_path_homotopic_on X TX x1 x1
    (top1_basepoint_change_on X TX x0 x1 alpha (top1_path_product f g))
    (top1_path_product
      (top1_basepoint_change_on X TX x0 x1 alpha f)
      (top1_basepoint_change_on X TX x0 x1 alpha g))"
  sorry

(** Full Theorem 52.1 (group isomorphism): if X is path-connected, then
    \<pi>_1(X, x_0) \<cong> \<pi>_1(X, x_1) for any two basepoints x_0, x_1 \<in> X. **)
theorem Theorem_52_1_iso:
  assumes "is_topology_on_strict X TX"
      and "top1_path_connected_on X TX"
      and "x0 \<in> X" and "x1 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier X TX x1)
           (top1_fundamental_group_mul X TX x1)"
  sorry

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

lemma top1_S1_arc_E_preimage:
  "{x. top1_R_to_S1 x \<in> top1_S1_arc_E} = (\<Union>n::int. {of_int n - 1/4 <..< of_int n + 1/4})"
  \<comment> \<open>Proof: top1_R_to_S1 x \<in> arc_E iff cos(2\<pi>x) > 0 iff x \<in> (n - 1/4, n + 1/4) for some n.\<close>
  sorry

theorem Theorem_53_1:
  "top1_covering_map_on UNIV top1_open_sets top1_S1 top1_S1_topology top1_R_to_S1"
  \<comment> \<open>Per Munkres: each open arc is evenly covered by p, and the four arcs cover S^1.\<close>
  sorry

(** from \<S>53 Theorem 53.2: restriction of a covering map to a subspace is a covering map.
    Uses strict topology: subspace of strict is strict. **)
theorem Theorem_53_2:
  assumes "top1_covering_map_on E TE B TB p"
      and "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "B0 \<subseteq> B"
      and "E0 = {e\<in>E. p e \<in> B0}"
  shows "top1_covering_map_on E0 (subspace_topology E TE E0)
    B0 (subspace_topology B TB B0) p"
  sorry

(** from \<S>53 Theorem 53.3: product of covering maps is a covering map.
    Uses strict topology: product of strict is strict. **)
theorem Theorem_53_3:
  assumes "top1_covering_map_on E TE B TB p"
      and "top1_covering_map_on E' TE' B' TB' p'"
      and "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict E' TE'" and "is_topology_on_strict B' TB'"
  shows "top1_covering_map_on (E \<times> E') (product_topology_on TE TE')
    (B \<times> B') (product_topology_on TB TB') (\<lambda>(x, y). (p x, p' y))"
  sorry

section \<open>\<S>54 The Fundamental Group of the Circle\<close>

(** from \<S>54 Lemma 54.1: path-lifting lemma **)
lemma Lemma_54_1_path_lifting:
  assumes "top1_covering_map_on E TE B TB p"
      and "e0 \<in> E" and "p e0 = b0"
      and "top1_is_path_on B TB b0 b1 f"
  shows "\<exists>ftilde. top1_is_path_on E TE e0 (ftilde 1) ftilde
    \<and> (\<forall>s\<in>I_set. p (ftilde s) = f s)"
  sorry

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
    using iffD2[OF Theorem_18_4[OF hTI hTI hTI]] hpi1_cont hpi2_cont by blast
qed

(** Uniqueness part of Lemma 54.1 (implicit in Munkres): given a path f in B with
    two lifts ftilde_1, ftilde_2 in E both starting at e_0, they are equal. **)
lemma Lemma_54_1_uniqueness:
  assumes "top1_covering_map_on E TE B TB p"
      and "e0 \<in> E" and "p e0 = b0"
      and "top1_is_path_on B TB b0 b1 f"
      and "top1_is_path_on E TE e0 e1 ftilde_1"
      and "(\<forall>s\<in>I_set. p (ftilde_1 s) = f s)"
      and "top1_is_path_on E TE e0 e1' ftilde_2"
      and "(\<forall>s\<in>I_set. p (ftilde_2 s) = f s)"
  shows "\<forall>s\<in>I_set. ftilde_1 s = ftilde_2 s"
  sorry

(** from \<S>54 Lemma 54.2: homotopy-lifting lemma **)
lemma Lemma_54_2_homotopy_lifting:
  assumes "top1_covering_map_on E TE B TB p"
      and "e0 \<in> E" and "p e0 = b0"
      and "top1_continuous_map_on (I_set \<times> I_set) II_topology B TB F"
      and "F (0, 0) = b0"
  shows "\<exists>Ftilde. top1_continuous_map_on (I_set \<times> I_set) II_topology E TE Ftilde
    \<and> (\<forall>s\<in>I_set. \<forall>t\<in>I_set. p (Ftilde (s, t)) = F (s, t))
    \<and> Ftilde (0, 0) = e0"
  sorry

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
    using Lemma_54_2_homotopy_lifting[OF hcov he0 hpe0 hF_cont hF_00] by blast
  \<comment> \<open>Step 3: Ftilde(0,t) is constant e0; Ftilde(1,t) is constant, so e1 = e1'\<close>
  have hFt_left: "\<forall>t\<in>I_set. Ftilde (0, t) = e0"
  proof -
    have h0I0: "(0::real) \<in> I_set" unfolding top1_unit_interval_def by simp
    have hpair: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>t. (0, t))"
      by (rule pair_const_t_continuous[OF h0I0])
    have hcomp: "top1_continuous_map_on I_set I_top E TE (Ftilde \<circ> (\<lambda>t. (0, t)))"
      by (rule top1_continuous_map_on_comp[OF hpair hFt_cont])
    have hcont_left: "top1_continuous_map_on I_set I_top E TE (\<lambda>t. Ftilde (0, t))"
      using hcomp by (simp add: comp_def)
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
    have hpair: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>t. (1, t))"
      by (rule pair_const_t_continuous[OF h1I_])
    have hcomp: "top1_continuous_map_on I_set I_top E TE (Ftilde \<circ> (\<lambda>t. (1, t)))"
      by (rule top1_continuous_map_on_comp[OF hpair hFt_cont])
    have hcont_right: "top1_continuous_map_on I_set I_top E TE (\<lambda>t. Ftilde (1, t))"
      using hcomp by (simp add: comp_def)
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
    have hpair: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>s. (s, 0))"
      by (rule pair_s_const_continuous[OF h0I])
    have hcomp: "top1_continuous_map_on I_set I_top E TE (Ftilde \<circ> (\<lambda>s. (s, 0)))"
      by (rule top1_continuous_map_on_comp[OF hpair hFt_cont])
    have hcont: "top1_continuous_map_on I_set I_top E TE (\<lambda>s. Ftilde (s, 0))"
      using hcomp by (simp add: comp_def)
    show ?thesis
      unfolding top1_is_path_on_def using hcont hFt_00 by simp
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
    have hpair: "top1_continuous_map_on I_set I_top (I_set \<times> I_set) II_topology (\<lambda>s. (s, 1))"
      by (rule pair_s_const_continuous[OF h1I0])
    have hcomp: "top1_continuous_map_on I_set I_top E TE (Ftilde \<circ> (\<lambda>s. (s, 1)))"
      by (rule top1_continuous_map_on_comp[OF hpair hFt_cont])
    have hcont: "top1_continuous_map_on I_set I_top E TE (\<lambda>s. Ftilde (s, 1))"
      using hcomp by (simp add: comp_def)
    show ?thesis
      unfolding top1_is_path_on_def using hcont hFt_top_start by simp
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
      using hft hgt' hFt_cont hFt_b0 hFt_b1 hFt_l0 hFt_r1 by blast
  qed
  show ?thesis using heq hhomo by blast
qed

(** from \<S>54 Theorem 54.4: lifting correspondence.
    Given a covering p : (E, e_0) \<to> (B, b_0) and E path-connected, the map
    \<Phi> : \<pi>_1(B, b_0) \<to> p\<inverse>(b_0) sending [f] to \<tilde>f(1) (where \<tilde>f is the lift
    starting at e_0) is surjective. **)
theorem Theorem_54_4_lifting_correspondence:
  assumes he0: "e0 \<in> E" and hpe0: "p e0 = b0"
      and "top1_covering_map_on E TE B TB p"
      and "top1_path_connected_on E TE"
  shows "\<exists>\<phi>. (\<forall>c \<in> top1_fundamental_group_carrier B TB b0.
                \<phi> c \<in> {e\<in>E. p e = b0})
           \<and> \<phi> ` (top1_fundamental_group_carrier B TB b0) = {e\<in>E. p e = b0}"
  sorry

theorem Theorem_54_4_bijective_simply_connected:
  assumes "top1_covering_map_on E TE B TB p"
      and "e0 \<in> E" and "p e0 = b0"
      and "top1_simply_connected_on E TE"
  shows "\<exists>\<phi>. bij_betw \<phi> (top1_fundamental_group_carrier B TB b0) {e\<in>E. p e = b0}"
  sorry

text \<open>Helper: R is path-connected via the straight-line path t \<mapsto> (1-t)\<cdot>x + t\<cdot>y.\<close>
lemma top1_R_path_connected':
  "top1_path_connected_on (UNIV::real set) top1_open_sets"
  \<comment> \<open>Straight-line paths between any two reals.\<close>
  sorry

text \<open>Helper: R is simply connected — any loop f is homotopic to constant via
  F(s, t) = (1 - t) * f(s) + t * x0 (straight-line homotopy to the basepoint).\<close>
lemma top1_R_simply_connected':
  "top1_simply_connected_on (UNIV::real set) top1_open_sets"
  \<comment> \<open>R is convex; use straight-line homotopy F(s,t) = (1-t)*f(s) + t*x0.\<close>
  sorry

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
  obtain \<phi>' where hbij: "bij_betw \<phi>'
      (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
      {x\<in>(UNIV::real set). top1_R_to_S1 x = (1, 0)}"
    using Theorem_54_4_bijective_simply_connected[OF hcov h0R hp0 hRsc] by blast
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

(** Strengthened version: \<pi>_1(S^1, (1,0)) is isomorphic to Z as groups (not just bijective). **)
theorem Theorem_54_5_iso:
  "top1_groups_isomorphic_on
     (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
     (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
     top1_Z_group
     top1_Z_mul"
  sorry

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
  assumes "is_topology_on X TX"
  shows "top1_retract_of_on X TX X"
  sorry

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
  assumes "top1_retract_of_on X TX A"
      and "x0 \<in> A"
      and "top1_is_loop_on A (subspace_topology X TX A) x0 f"
      and "top1_is_loop_on A (subspace_topology X TX A) x0 g"
      and "top1_path_homotopic_on X TX x0 x0 f g"
  shows "top1_path_homotopic_on A (subspace_topology X TX A) x0 x0 f g"
  sorry

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
        by (rule top1_loop_equiv_on_trans[OF hgf hfh])
      thus "h \<in> c2" using hc2_eq by blast
    qed
    moreover have "c2 \<subseteq> c1"
    proof
      fix h assume "h \<in> c2"
      hence hgh: "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) g h" using hc2_eq by blast
      have "top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0) f h"
        by (rule top1_loop_equiv_on_trans[OF heq hgh])
      thus "h \<in> c1" using hc1_eq by blast
    qed
    ultimately have "c1 = c2" by blast
    thus False using hne by blast
  qed
  hence hnot_pho: "\<not> top1_path_homotopic_on top1_S1 top1_S1_topology (1, 0) (1, 0) f g"
    using hf hg unfolding top1_loop_equiv_on_def by blast
  show ?thesis using hf hg hnot_pho by blast
qed

text \<open>Helper: B^2 is simply connected.\<close>
lemma top1_B2_simply_connected:
  "top1_simply_connected_on top1_B2 top1_B2_topology"
  sorry  \<comment> \<open>B^2 is convex, so any two paths are straight-line path-homotopic\<close>

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
  have hfg_B2: "top1_path_homotopic_on top1_B2 top1_B2_topology (1, 0) (1, 0) f g"
    by (rule Lemma_51_1_path_homotopic_trans[OF hf_const_B2 hg_const_sym])
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

(** from \<S>55 Lemma 55.3: nulhomotopic characterization **)
lemma Lemma_55_3_nulhomotopic_characterization:
  fixes h :: "real \<times> real \<Rightarrow> 'a"
  assumes "top1_continuous_map_on top1_S1 top1_S1_topology X TX h"
  shows "top1_nulhomotopic_on top1_S1 top1_S1_topology X TX h
      \<longleftrightarrow> (\<exists>k. top1_continuous_map_on top1_B2 top1_B2_topology X TX k
               \<and> (\<forall>x\<in>top1_S1. k x = h x))"
  sorry  \<comment> \<open>equivalence (1) \<Leftrightarrow> (2) of Lemma 55.3\<close>

(** from \<S>55 Corollary 55.4: inclusion S^1 \<rightarrow> R^2 - {0} is not nulhomotopic.
    Follows from Theorem 55.2 via retraction R^2 - {0} \<rightarrow> S^1 by x/|x|. **)
corollary Corollary_55_4_inclusion_not_nulhomotopic:
  shows "\<not> top1_nulhomotopic_on top1_S1 top1_S1_topology
           (UNIV - {(0, 0)})
           (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))
           (\<lambda>x. x)"
  sorry

(** from \<S>55 Theorem 55.5: nonvanishing vector field on B^2 points outward at
    some point of S^1 (and inward at some point). **)
theorem Theorem_55_5_vector_field:
  assumes "top1_continuous_map_on top1_B2 top1_B2_topology
             (UNIV::(real \<times> real) set)
             (product_topology_on top1_open_sets top1_open_sets) v"
      and "\<forall>x\<in>top1_B2. v x \<noteq> (0, 0)"
  shows "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (a * fst x, a * snd x)"
    and "\<exists>x\<in>top1_S1. \<exists>a>0. v x = (-(a * fst x), -(a * snd x))"
  sorry  \<comment> \<open>Munkres proof via Lemma 55.3 and Corollary 55.4\<close>

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
    sorry
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

section \<open>\<S>56 The Fundamental Theorem of Algebra\<close>

text \<open>Following Munkres' proof in 4 steps via the fundamental group of S^1:
  Step 1: f(z) = z^n on S^1 induces the "multiplication by n" homomorphism
          on pi_1(S^1), which is injective for n > 0.
  Step 2: g(z) = z^n as map S^1 -> R^2 - {0} is not nulhomotopic.
  Step 3: If |a_{n-1}| + ... + |a_0| < 1, the monic polynomial has a root in B^2.
  Step 4: General case by substitution x = cy with c large enough.\<close>

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
  \<comment> \<open>Uses Theorem 54.5: \<pi>_1(S^1) \<cong> Z; f_* corresponds to multiplication by n.\<close>
  sorry

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
  \<comment> \<open>Uses: S^1 is a retract of C - {0} via r(z) = z/|z|; induced maps are injective.\<close>
  sorry

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
                       top1_C_minus_0 top1_C_minus_0_topology ?h" sorry
  \<comment> \<open>Homotopy F(z,t) = z^n + t*\<Sum>a_j z^j from g=z^n to h, all in C-{0}.\<close>
  let ?F = "\<lambda>(z::complex, t::real). z^n + complex_of_real t * (\<Sum>j<n. a j * z^j)"
  have hF_cont: "top1_continuous_map_on (top1_S1_complex \<times> I_set)
                   (product_topology_on top1_S1_complex_topology I_top)
                   top1_C_minus_0 top1_C_minus_0_topology ?F" sorry
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
  \<comment> \<open>g(z) = z^n is NOT nulhomotopic by Step 2, but would be nulhomotopic via F.\<close>
  have hg_notnull: "\<not> top1_nulhomotopic_on top1_S1_complex top1_S1_complex_topology
                       top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n)"
    using Theorem_56_1_step_2[OF hn] .
  have hg_nulhomo: "top1_nulhomotopic_on top1_S1_complex top1_S1_complex_topology
                       top1_C_minus_0 top1_C_minus_0_topology (\<lambda>z. z^n)"
    \<comment> \<open>F homotopies g to h; hh_nulhomo gives h to const; transitivity gives g nulhomotopic.\<close>
    sorry
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

section \<open>\<S>57 The Borsuk-Ulam Theorem\<close>

text \<open>Antipode-preserving map on the plane: h(-x) = -h(x) pointwise.\<close>
definition top1_antipode_preserving_S1 :: "(real \<times> real \<Rightarrow> real \<times> real) \<Rightarrow> bool" where
  "top1_antipode_preserving_S1 h \<longleftrightarrow>
     (\<forall>x y. h (-x, -y) = (- fst (h (x, y)), - snd (h (x, y))))"

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
  sorry

(** from *\<S>57 Theorem 57.2: no continuous antipode-preserving S^2 \<rightarrow> S^1.
    Munkres' proof: if g: S^2 \<rightarrow> S^1 is antipode-preserving, then h = g|S^1
    (equator) is antipode-preserving S^1 \<rightarrow> S^1, not nulhomotopic by 57.1.
    But g extends h over the upper hemisphere \<cong> B^2, so h IS nulhomotopic.
    Contradiction.

    (Stated as part of Theorem 57.3 below using an inline S^2 set, since
     top1_S2 is defined later in the file.) **)

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
  \<comment> \<open>Define g: S^2 \<rightarrow> S^1 by g(x) = (f(x) - f(-x)) / ||f(x) - f(-x)||.\<close>
  \<comment> \<open>Then g is continuous and antipode-preserving, contradicting Theorem 57.2.\<close>
  show False sorry
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
  assumes "top1_continuous_map_on X TX Y TY h"
      and "top1_continuous_map_on X TX Y TY k"
      and "h x0 = y0" and "k x0 = y0"
      and "\<exists>H. top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) Y TY H
              \<and> (\<forall>x\<in>X. H (x, 0) = h x) \<and> (\<forall>x\<in>X. H (x, 1) = k x)
              \<and> (\<forall>t\<in>I_set. H (x0, t) = y0)"
      and "top1_is_loop_on X TX x0 f"
  shows "top1_path_homotopic_on Y TY y0 y0
           (top1_induced_homomorphism_on X TX Y TY h f)
           (top1_induced_homomorphism_on X TX Y TY k f)"
  \<comment> \<open>Munkres: H \<circ> (f \<times> id) gives the needed path homotopy.\<close>
  sorry

(** from \<S>58 Lemma 58.5: if A \<subseteq> X, H : X\<times>I \<rightarrow> X is a homotopy from id_X
    to some map k : X \<rightarrow> X with H(a, t) \<in> A for all a \<in> A and t \<in> I,
    and \<alpha>(t) = H(x_0, t) is the "base-tracking" path from x_0 to k(x_0),
    then the basepoint-change \<alpha>\<^sup>\<hat> commutes with the induced map on \<pi>_1. **)
lemma Lemma_58_5_basepoint_change:
  fixes X :: "'a set" and TX :: "'a set set" and A :: "'a set"
    and H :: "'a \<times> real \<Rightarrow> 'a" and k :: "'a \<Rightarrow> 'a" and x0 :: 'a
  assumes "is_topology_on_strict X TX"
      and "A \<subseteq> X"
      and "top1_continuous_map_on (X \<times> I_set) (product_topology_on TX I_top) X TX H"
      and "\<forall>x\<in>X. H (x, 0) = x"
      and "\<forall>x\<in>X. H (x, 1) = k x"
      and "\<forall>a\<in>A. \<forall>t\<in>I_set. H (a, t) \<in> A"
      and "x0 \<in> A"
  shows "top1_is_path_on X TX x0 (k x0) (\<lambda>t. H (x0, t))"
  \<comment> \<open>The tracking path \<alpha>(t) = H(x_0, t) goes from x_0 to k(x_0);
      the basepoint-change \<alpha>-hat then commutes with k_* appropriately.\<close>
  sorry

(** from \<S>58 Theorem 58.7: a homotopy equivalence induces an isomorphism of fundamental groups.
    The strict version is trivially related.

    Munkres' proof (sketch):
    Given f and g as homotopy invgerses, Lemma 58.1 gives that (g o f)_* equals id_*
    and (f o g)_* equals id_*, so f_* and g_* are mutual invgerses in a suitable sense.
    Hence f_* is a bijection onto pi_1(Y, f x_0). **)
theorem Theorem_58_7:
  assumes "top1_homotopy_equivalence_on X TX Y TY f g" and "x0 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier Y TY (f x0))
           (top1_fundamental_group_mul Y TY (f x0))"
  sorry

(** from \<S>58 Theorem 58.3: deformation retract induces isomorphism of fundamental groups.

    Munkres' proof: if A is a deformation retract of X via H, then the
    inclusion j: A \<hookrightarrow> X and the retraction r: X \<rightarrow> A = H(\<cdot>, 1) are homotopy
    invgerses. By Theorem 58.7, any homotopy equivalence induces an iso on \<pi>_1. **)
theorem Theorem_58_3:
  assumes hdef: "top1_deformation_retract_of_on X TX A" and hx0: "x0 \<in> A"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier A (subspace_topology X TX A) x0)
           (top1_fundamental_group_mul A (subspace_topology X TX A) x0)
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)"
  \<comment> \<open>By homotopy equivalence j : A \<hookrightarrow> X and r = H(\<cdot>, 1) : X \<rightarrow> A; apply Theorem 58.7.\<close>
  sorry

(** from \<S>58 Theorem 58.2: inclusion S^1 \<rightarrow> R^2-0 induces isomorphism of fundamental groups.

    Munkres' proof: S^1 is a deformation retract of R^2 - 0 via
    H(x, t) = (1-t)x + t(x/||x||). By Theorem 58.3, the inclusion induces
    an isomorphism of fundamental groups. **)
theorem Theorem_58_2_inclusion_iso:
  "top1_groups_isomorphic_on
    (top1_fundamental_group_carrier top1_S1 top1_S1_topology (1, 0))
    (top1_fundamental_group_mul top1_S1 top1_S1_topology (1, 0))
    (top1_fundamental_group_carrier
       (UNIV - {(0, 0)})
       (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))
       (1, 0))
    (top1_fundamental_group_mul
       (UNIV - {(0, 0)})
       (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) (UNIV - {(0, 0)}))
       (1, 0))"
  \<comment> \<open>By Theorem 58.3, it suffices to show S^1 is a deformation retract of R^2 - 0.\<close>
  sorry

corollary Theorem_58_7_strict:
  assumes "is_topology_on_strict X TX" and "is_topology_on_strict Y TY"
    and "top1_homotopy_equivalence_on X TX Y TY f g" and "x0 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_fundamental_group_carrier Y TY (f x0))
           (top1_fundamental_group_mul Y TY (f x0))"
  using Theorem_58_7[OF assms(3) assms(4)] by blast

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
  sorry

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
  \<comment> \<open>Follows from Theorem 59.1 since both i_*, j_* are trivial.\<close>
  sorry

(** from \<S>59 Theorem 59.3: for n \<ge> 2, S^n is simply connected.

    Munkres' proof (2 steps):
    Step 1: S^n - p is homeomorphic to R^n via stereographic projection.
    Step 2: Apply Corollary 59.2 with U = S^n - p, V = S^n - q. **)
theorem Theorem_59_3:
  assumes "n \<ge> 2"
  shows "top1_simply_connected_on (top1_Sn n)
    (subspace_topology UNIV
      (top1_product_topology_on UNIV (\<lambda>_. UNIV) (\<lambda>_. top1_open_sets))
      (top1_Sn n))"
  sorry

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
  sorry

section \<open>Chapter 10: Separation Theorems in the Plane\<close>

section \<open>\<S>61 The Jordan Separation Theorem\<close>

text \<open>The 2-sphere S^2 as a subspace of R^3.\<close>
definition top1_S2 :: "(real \<times> real \<times> real) set" where
  "top1_S2 = {p. fst p ^ 2 + fst (snd p) ^ 2 + snd (snd p) ^ 2 = 1}"

definition top1_S2_topology :: "(real \<times> real \<times> real) set set" where
  "top1_S2_topology = subspace_topology UNIV
     (product_topology_on top1_open_sets
       (product_topology_on top1_open_sets top1_open_sets)) top1_S2"

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
  shows "(b \<notin> U \<longrightarrow> (\<exists>M. \<forall>x\<in>U. fst (h x) ^ 2 + snd (h x) ^ 2 \<le> M))
       \<and> (b \<in> U \<longrightarrow> (\<forall>M. \<exists>x\<in>U - {b}. fst (h x) ^ 2 + snd (h x) ^ 2 > M))"
  sorry

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
  sorry

(** from \<S>61 Theorem 61.3: Jordan separation theorem for S^2.

    Munkres' proof sketch:
    Suppose for contradiction S^2 - C is path connected.
    Write C = A_1 \<union> A_2 (arcs meeting at {a, b}).
    Let X = S^2 - {a, b}, U = S^2 - A_1, V = S^2 - A_2.
    Then X = U \<union> V and U \<inter> V = S^2 - C (path connected by assumption).
    By Theorem 59.1, \<pi>_1(X, x_0) is generated by images of i_*, j_*.
    Using Lemma 61.2 (nulhomotopy), both i_* and j_* are trivial.
    So \<pi>_1(X, x_0) is trivial. But X \<cong> R^2 - {0} has nontrivial \<pi>_1. \<bottom> **)
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
  \<comment> \<open>Decompose C = A_1 \<union> A_2 with endpoints a, b; apply §59.1 + Lemma 61.2.\<close>
  \<comment> \<open>Then \<pi>_1(S^2 - a - b) would be trivial, contradicting \<pi>_1(R^2 - 0) nontrivial.\<close>
  show False sorry
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
  sorry

section \<open>*\<S>62 Invariance of Domain\<close>

text \<open>Invariance of domain in R^2: an open injective continuous map R^2 \<rightarrow> R^2
  has open image, and its invgerse is continuous.\<close>

(** from *\<S>62 Theorem 62.3: Invariance of Domain in R^2. **)
theorem Theorem_62_3_invgariance_of_domain:
  fixes U :: "(real \<times> real) set" and f :: "real \<times> real \<Rightarrow> real \<times> real"
  assumes "U \<in> product_topology_on top1_open_sets top1_open_sets"
      and "top1_continuous_map_on U
             (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) U)
             UNIV (product_topology_on top1_open_sets top1_open_sets) f"
      and "inj_on f U"
  shows "f ` U \<in> product_topology_on top1_open_sets top1_open_sets"
  sorry

section \<open>\<S>63 The Jordan Curve Theorem\<close>

text \<open>A simple closed curve in X: image of a continuous injective map S^1 \<rightarrow> X.\<close>
definition top1_simple_closed_curve_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "top1_simple_closed_curve_on X TX C \<longleftrightarrow>
     (\<exists>f. top1_continuous_map_on top1_S1 top1_S1_topology X TX f
          \<and> inj_on f top1_S1
          \<and> f ` top1_S1 = C)"

(** from \<S>63 Theorem 63.1: if X = U \<union> V with U \<inter> V = A \<union> B (disjoint open),
    and alpha: a to b in U, beta: b to a in V, then the loop f = alpha * beta is
    nontrivial in pi_1(X, a) (plus further properties: homotopy lifts, f^m and f^k
    are nonconjugate when the components are different). Used in Munkres' proof of
    the Jordan Curve Theorem. **)
theorem Theorem_63_1_loop_nontrivial:
  assumes "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "U \<inter> V = A \<union> B" and "A \<inter> B = {}"
      and "openin_on X TX A" and "openin_on X TX B"
      and "a \<in> A" and "b \<in> B"
      and "top1_is_path_on U (subspace_topology X TX U) a b alpha"
      and "top1_is_path_on V (subspace_topology X TX V) b a beta"
  shows "\<not> top1_path_homotopic_on X TX a a
           (top1_path_product alpha beta) (top1_constant_path a)"
  sorry

(** from \<S>63 Theorem 63.2: an arc D in S^2 does not separate S^2.
    Munkres' proof: by contradiction + Theorem 63.1; use that \<pi>_1(S^2) is trivial. **)
theorem Theorem_63_2_arc_no_separation:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "D \<subseteq> top1_S2"
  and "top1_is_arc_on D (subspace_topology top1_S2 top1_S2_topology D)"
  shows "\<not> top1_separates_on top1_S2 top1_S2_topology D"
  sorry

(** from \<S>63 Theorem 63.3: general non-separation theorem. **)
theorem Theorem_63_3_general_nonseparation:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "closedin_on top1_S2 top1_S2_topology D1"
  and "closedin_on top1_S2 top1_S2_topology D2"
  and "top1_simply_connected_on (top1_S2 - (D1 \<inter> D2))
         (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (D1 \<inter> D2)))"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology D1"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology D2"
  shows "\<not> top1_separates_on top1_S2 top1_S2_topology (D1 \<union> D2)"
  sorry

(** from \<S>63 Theorem 63.4: Jordan Curve Theorem.

    Munkres' proof: use Theorem 61.3 (separation) + locally connected property +
    Theorem 63.1 argument to show at most 2 components. Each component has C as
    boundary by an auxiliary argument.

    NB: Currently stated for C \<subseteq> R^2 (as in the original formalization). **)
theorem Theorem_63_4_JordanCurve:
  fixes C :: "(real \<times> real) set"
  assumes "top1_simple_closed_curve_on
    UNIV (product_topology_on top1_open_sets top1_open_sets) C"
  shows "\<exists>U V. U \<noteq> {} \<and> V \<noteq> {}
    \<and> U \<inter> V = {} \<and> U \<union> V = UNIV - C
    \<and> top1_path_connected_on U
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) U)
    \<and> top1_path_connected_on V
        (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) V)
    \<comment> \<open>One component is bounded (interior), the other unbounded (exterior).\<close>
    \<and> (\<exists>M. \<forall>p\<in>U. fst p ^ 2 + snd p ^ 2 \<le> M)
    \<and> (\<forall>M. \<exists>p\<in>V. fst p ^ 2 + snd p ^ 2 > M)
    \<comment> \<open>Both components have C as boundary.\<close>
    \<and> closure U = U \<union> C
    \<and> closure V = V \<union> C"
  sorry

(** from \<S>63 Theorem 63.5: two closed-connected sets C1, C2 with |C1\<inter>C2|=2 and neither separates S^2 imply C1\<union>C2 separates into exactly two components. **)
theorem Theorem_63_5_two_closed_connected:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "closedin_on top1_S2 top1_S2_topology C1"
  and "closedin_on top1_S2 top1_S2_topology C2"
  and "top1_connected_on C1 (subspace_topology top1_S2 top1_S2_topology C1)"
  and "top1_connected_on C2 (subspace_topology top1_S2 top1_S2_topology C2)"
  and "card (C1 \<inter> C2) = 2"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology C1"
  and "\<not> top1_separates_on top1_S2 top1_S2_topology C2"
  shows "\<exists>U V. U \<noteq> {} \<and> V \<noteq> {} \<and> U \<inter> V = {}
    \<and> U \<union> V = top1_S2 - (C1 \<union> C2)
    \<and> top1_connected_on U
        (subspace_topology top1_S2 top1_S2_topology U)
    \<and> top1_connected_on V
        (subspace_topology top1_S2 top1_S2_topology V)"
  \<comment> \<open>Exactly two components (U and V), not just 'not connected'.\<close>
  sorry

section \<open>\<S>65 The Winding Number of a Simple Closed Curve\<close>

text \<open>The winding number of a loop f in R^2-{0} around the origin.
  Munkres' definition: lift the loop (cos 2\<pi>t, sin 2\<pi>t)-valued normalization
  f/|f| to a path \<tilde>f in R via the covering p: R \<rightarrow> S^1, p(x) = (cos 2\<pi>x, sin 2\<pi>x),
  and define winding number = \<tilde>f(1) - \<tilde>f(0). This is an integer since f is a loop.\<close>
definition top1_winding_number_on ::
  "(real \<Rightarrow> real \<times> real) \<Rightarrow> int" where
  "top1_winding_number_on f =
     (SOME n::int.
        \<exists>ftilde. top1_continuous_map_on I_set I_top (UNIV::real set) top1_open_sets ftilde
              \<and> (\<forall>s\<in>I_set. top1_R_to_S1 (ftilde s)
                   = (fst (f s) / sqrt (fst (f s)^2 + snd (f s)^2),
                      snd (f s) / sqrt (fst (f s)^2 + snd (f s)^2)))
              \<and> n = \<lfloor>ftilde 1 - ftilde 0\<rfloor>)"

(** from \<S>65 Lemma 65.1: for K_4 subspace of S^2 with vertices a_1, ..., a_4 and
    closed-curve edge C = a_1 a_2 a_3 a_4 a_1, and interior points p, q of opposite
    edges a_1 a_3 and a_2 a_4, the loop traversing C is nontrivial in \<pi>_1(S^2-p-q, x_0). **)
lemma Lemma_65_1_K4_subgraph:
  fixes a1 a2 a3 a4 :: "real \<times> real \<times> real"
    and e12 e23 e34 e41 e13 e24 :: "(real \<times> real \<times> real) set"
    and C :: "(real \<times> real \<times> real) set"
    and p q :: "real \<times> real \<times> real"
    and f :: "real \<Rightarrow> real \<times> real \<times> real"
    and x0 :: "real \<times> real \<times> real"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      \<comment> \<open>K_4 structure: 4 distinct vertices on S^2, plus 6 arcs between them.\<close>
      and "card {a1, a2, a3, a4} = 4"
      and "{a1, a2, a3, a4} \<subseteq> top1_S2"
      \<comment> \<open>All 6 arcs are subsets of S^2.\<close>
      and "e12 \<subseteq> top1_S2" and "e23 \<subseteq> top1_S2" and "e34 \<subseteq> top1_S2"
      and "e41 \<subseteq> top1_S2" and "e13 \<subseteq> top1_S2" and "e24 \<subseteq> top1_S2"
      and "top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      and "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      and "top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      and "top1_is_arc_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
      and "top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
      and "top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
      and "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1,a2}"
      and "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2,a3}"
      and "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3,a4}"
      and "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a4,a1}"
      and "top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1,a3}"
      and "top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2,a4}"
      \<comment> \<open>p, q are interior points of the two 'diagonal' edges.\<close>
      and "p \<in> e13 - {a1, a3}" and "q \<in> e24 - {a2, a4}"
      \<comment> \<open>C is the 4-cycle a_1 a_2 a_3 a_4 a_1.\<close>
      and "C = e12 \<union> e23 \<union> e34 \<union> e41"
      \<comment> \<open>f is a loop at x_0 in S^2-{p,q} whose image is C.\<close>
      and "top1_is_loop_on (top1_S2 - {p} - {q})
             (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) x0 f"
      and "f ` I_set = C"
  shows "\<not> top1_path_homotopic_on (top1_S2 - {p} - {q})
           (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q}))
           x0 x0 f (top1_constant_path x0)"
  sorry

(** from \<S>65 Theorem 65.2: inclusion C \<rightarrow> S^2 - p - q induces fundamental group iso **)
theorem Theorem_65_2:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
  and "top1_simple_closed_curve_on top1_S2 top1_S2_topology C"
  and "p \<in> top1_S2 - C" and "q \<in> top1_S2 - C"
  \<comment> \<open>p, q in different path-components of S^2 - C (stronger than 'not connected').\<close>
  and "\<not> (\<exists>f. top1_is_path_on (top1_S2 - C)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - C)) p q f)"
  and "c0 \<in> C"
  shows "top1_groups_isomorphic_on
    (top1_fundamental_group_carrier C (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_mul C (subspace_topology top1_S2 top1_S2_topology C) c0)
    (top1_fundamental_group_carrier (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)
    (top1_fundamental_group_mul (top1_S2 - {p} - {q})
       (subspace_topology top1_S2 top1_S2_topology (top1_S2 - {p} - {q})) c0)"
  \<comment> \<open>Uses Lemma 65.1 + Jordan Curve Theorem.\<close>
  sorry

section \<open>Chapter 11: The Seifert-van Kampen Theorem\<close>

subsection \<open>Lightweight group-theoretic machinery\<close>

text \<open>A group is a 4-tuple (G, mul, e, invg) satisfying associativity,
  left/right identity, and left/right invgerse.\<close>
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

text \<open>Group homomorphism: f preserves multiplication (and hence identity & invgerse).\<close>
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

text \<open>Normal subgroup: N \<subseteq> G is a subgroup closed under conjugation.\<close>
definition top1_normal_subgroup_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> bool" where
  "top1_normal_subgroup_on G mul e invg N \<longleftrightarrow>
     N \<subseteq> G \<and>
     top1_is_group_on N mul e invg \<and>
     (\<forall>g\<in>G. \<forall>n\<in>N. mul (mul g n) (invg g) \<in> N)"

text \<open>Kernel of a homomorphism is a normal subgroup.\<close>
definition top1_group_kernel_on ::
  "'g set \<Rightarrow> 'h \<Rightarrow> ('g \<Rightarrow> 'h) \<Rightarrow> 'g set" where
  "top1_group_kernel_on G eH f = {x\<in>G. f x = eH}"

text \<open>Image of a group under a homomorphism.\<close>
definition top1_group_image_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'h) \<Rightarrow> 'h set" where
  "top1_group_image_on G f = f ` G"

text \<open>Quotient group G/N: cosets g N under the product (gN)(hN) = (gh)N.
  Modelled as a set of equivalence classes.\<close>
definition top1_group_coset_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g \<Rightarrow> 'g set" where
  "top1_group_coset_on G mul N g = {mul g n | n. n \<in> N}"

definition top1_quotient_group_carrier_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set set" where
  "top1_quotient_group_carrier_on G mul N = {top1_group_coset_on G mul N g | g. g \<in> G}"

text \<open>Multiplication on cosets: (gN)(hN) = (gh)N, computed as set product.\<close>
definition top1_quotient_group_mul_on ::
  "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "top1_quotient_group_mul_on mul C1 C2 = {mul g h | g h. g \<in> C1 \<and> h \<in> C2}"

text \<open>Iterated product in a group (g * g * ... * g, n times).\<close>
fun top1_group_pow :: "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> nat \<Rightarrow> 'g" where
  "top1_group_pow mul e x 0 = e"
| "top1_group_pow mul e x (Suc n) = mul x (top1_group_pow mul e x n)"

text \<open>Product of a word in (G \<union> G\<inverse>): each letter is (g, b) where b=True means g
  contributes g to the product, and b=False means invg(g) contributes. For an empty
  word the result is the identity e.\<close>
fun top1_group_word_product ::
  "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> ('g \<times> bool) list \<Rightarrow> 'g" where
  "top1_group_word_product mul e invg [] = e"
| "top1_group_word_product mul e invg ((x, True) # ws)
     = mul x (top1_group_word_product mul e invg ws)"
| "top1_group_word_product mul e invg ((x, False) # ws)
     = mul (invg x) (top1_group_word_product mul e invg ws)"

text \<open>A word in ('g \<times> bool) list is reduced if no adjacent pair (x, b) (x, \<not>b) appears
  (which would represent x \<cdot> x\<inverse> or x\<inverse> \<cdot> x, cancelling to e).\<close>
fun top1_is_reduced_word ::
  "('g \<times> bool) list \<Rightarrow> bool" where
  "top1_is_reduced_word [] = True"
| "top1_is_reduced_word [_] = True"
| "top1_is_reduced_word ((x, b) # (y, c) # ws)
     = ((x \<noteq> y \<or> b = c) \<and> top1_is_reduced_word ((y, c) # ws))"

text \<open>Subgroup generated by a subset S \<subseteq> G.\<close>
definition top1_subgroup_generated_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "top1_subgroup_generated_on G mul e invg S =
     \<Inter> { H. S \<subseteq> H \<and> H \<subseteq> G \<and> top1_is_group_on H mul e invg }"

definition top1_normal_subgroup_generated_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "top1_normal_subgroup_generated_on G mul e invg S =
     \<Inter> { N. S \<subseteq> N \<and> top1_normal_subgroup_on G mul e invg N }"

text \<open>Free group on a set S: a group F(S) with \<iota>: S \<hookrightarrow> F(S) such that:
  (1) \<iota> is injective,
  (2) \<iota>(S) generates F(S), and
  (3) no non-empty reduced word in \<iota>(S) \<union> \<iota>(S)\<inverse> equals e (the freeness condition).
  Together, (2)+(3) are equivalent to the universal extension property.\<close>
definition top1_is_free_group_full_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> ('s \<Rightarrow> 'g) \<Rightarrow> 's set \<Rightarrow> bool" where
  "top1_is_free_group_full_on G mul e invg \<iota> S \<longleftrightarrow>
     top1_is_group_on G mul e invg \<and>
     (\<forall>s\<in>S. \<iota> s \<in> G) \<and>
     inj_on \<iota> S \<and>
     G = top1_subgroup_generated_on G mul e invg (\<iota> ` S) \<and>
     (\<forall>ws :: ('s \<times> bool) list.
        ws \<noteq> [] \<longrightarrow>
        top1_is_reduced_word (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<longrightarrow>
        (\<forall>i<length ws. fst (ws!i) \<in> S) \<longrightarrow>
        top1_group_word_product mul e invg (map (\<lambda>(s, b). (\<iota> s, b)) ws) \<noteq> e)"

text \<open>External universal property for free groups: for a specific test type,
  any function S \<rightarrow> H extends uniquely to a homomorphism G \<rightarrow> H.\<close>
definition top1_free_group_universal_prop ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> ('s \<Rightarrow> 'g) \<Rightarrow> 's set \<Rightarrow>
   'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> 'h \<Rightarrow> ('h \<Rightarrow> 'h) \<Rightarrow> ('s \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_free_group_universal_prop G mul \<iota> S H mulH eH invgH \<phi> \<longleftrightarrow>
     top1_is_group_on H mulH eH invgH \<and> (\<forall>s\<in>S. \<phi> s \<in> H) \<longrightarrow>
     (\<exists>!\<psi>. top1_group_hom_on G mul H mulH \<psi>
        \<and> (\<forall>s\<in>S. \<psi> (\<iota> s) = \<phi> s))"

text \<open>Free abelian group on a set S: abelian group G together with \<iota>: S \<hookrightarrow> G such that
  (1) \<iota> is injective, (2) \<iota>(S) generates G, and
  (3) no non-trivial finitely-supported integer combination of \<iota>(S) equals e.
  Condition (3) is the abelian freeness: for any nonzero c : S \<rightarrow> int with finite
  support, the product over s of \<iota>(s) raised to c(s) is not e.\<close>
definition top1_is_free_abelian_group_full_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> ('s \<Rightarrow> 'g) \<Rightarrow> 's set \<Rightarrow> bool" where
  "top1_is_free_abelian_group_full_on G mul e invg \<iota> S \<longleftrightarrow>
     top1_is_abelian_group_on G mul e invg \<and>
     (\<forall>s\<in>S. \<iota> s \<in> G) \<and>
     inj_on \<iota> S \<and>
     G = top1_subgroup_generated_on G mul e invg (\<iota> ` S) \<and>
     (\<forall>c :: 's \<Rightarrow> int.
        finite {s\<in>S. c s \<noteq> 0} \<longrightarrow>
        (\<exists>s\<in>S. c s \<noteq> 0) \<longrightarrow>
        foldr mul (map (\<lambda>s.
            if c s \<ge> 0 then top1_group_pow mul e (\<iota> s) (nat (c s))
            else top1_group_pow mul e (invg (\<iota> s)) (nat (- c s)))
          (SOME xs. set xs = {s\<in>S. c s \<noteq> 0} \<and> distinct xs)) e
        \<noteq> e)"

text \<open>Group presentation: G is presented by generators S modulo relations R.
  Relations are reduced words in S \<union> S\<inverse> (type ('s \<times> bool) list, as for free groups).
  G \<cong> F(S)/\<langle>\<langle>R\<rangle>\<rangle> means: there is a free group F on S and a surjective homomorphism
  \<pi>: F \<rightarrow> G whose kernel is the normal subgroup of F generated by the images of
  the relator words (computed via top1_group_word_product).\<close>
definition top1_group_presented_by_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g)
   \<Rightarrow> 's set \<Rightarrow> (('s \<times> bool) list set) \<Rightarrow> bool" where
  "top1_group_presented_by_on G mul e invg S R \<longleftrightarrow>
     top1_is_group_on G mul e invg \<and>
     (\<exists>(F::'g set) mulF eF invgF \<iota> \<pi>.
        top1_is_free_group_full_on F mulF eF invgF \<iota> S
      \<and> top1_group_hom_on F mulF G mul \<pi>
      \<and> \<pi> ` F = G
      \<and> top1_group_kernel_on F e \<pi>
           = top1_normal_subgroup_generated_on F mulF eF invgF
               {r. \<exists>w\<in>R. r = top1_group_word_product mulF eF invgF
                            (map (\<lambda>(s, b). (\<iota> s, b)) w)})"

text \<open>Free product of a family of groups (Munkres §68): a group (G, mul, e, invg)
  with injective homomorphisms \<iota>_\<alpha>: G_\<alpha> \<hookrightarrow> G (one per index \<alpha>\<in>J), such that:
  (1) the images \<iota>_\<alpha>(G_\<alpha>) generate G, and
  (2) any non-empty reduced product of elements (alternating between different
      \<iota>_\<alpha>(G_\<alpha>\<setminus>{e_\<alpha>})) is not the identity of G.
  The last conjunct encodes (2): word = list of (index, element) pairs where
  each element differs from its group's identity and consecutive indices differ;
  its product in G is not e.\<close>
definition top1_is_free_product_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow>
   ('i \<Rightarrow> 'gg set) \<Rightarrow> ('i \<Rightarrow> 'gg \<Rightarrow> 'gg \<Rightarrow> 'gg) \<Rightarrow>
   ('i \<Rightarrow> 'gg \<Rightarrow> 'g) \<Rightarrow> 'i set \<Rightarrow> bool" where
  "top1_is_free_product_on G mul e invg GG mulGG \<iota>fam J \<longleftrightarrow>
     top1_is_group_on G mul e invg \<and>
     (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<iota>fam \<alpha> x \<in> G) \<and>
     (\<forall>\<alpha>\<in>J. \<forall>x\<in>GG \<alpha>. \<forall>y\<in>GG \<alpha>.
        \<iota>fam \<alpha> (mulGG \<alpha> x y) = mul (\<iota>fam \<alpha> x) (\<iota>fam \<alpha> y)) \<and>
     (\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (GG \<alpha>)) \<and>
     G = top1_subgroup_generated_on G mul e invg (\<Union>\<alpha>\<in>J. \<iota>fam \<alpha> ` GG \<alpha>) \<and>
     (\<forall>indices word.
        length indices = length word \<longrightarrow>
        length indices > 0 \<longrightarrow>
        (\<forall>i<length indices. indices!i \<in> J \<and> word!i \<in> GG (indices!i)
                          \<and> \<iota>fam (indices!i) (word!i) \<noteq> e) \<longrightarrow>
        (\<forall>i. i + 1 < length indices \<longrightarrow> indices!i \<noteq> indices!(i+1)) \<longrightarrow>
        foldr mul (map (\<lambda>i. \<iota>fam (indices!i) (word!i)) [0..<length indices]) e \<noteq> e)"

text \<open>The integers Z as an additive abelian group.\<close>
definition top1_Z_group :: "int set" where
  "top1_Z_group = UNIV"

definition top1_Z_mul :: "int \<Rightarrow> int \<Rightarrow> int" where
  "top1_Z_mul a b = a + b"

definition top1_Z_id :: "int" where
  "top1_Z_id = 0"

definition top1_Z_invg :: "int \<Rightarrow> int" where
  "top1_Z_invg a = - a"

text \<open>The cyclic group Z/nZ with modular addition.\<close>
definition top1_Zn_group :: "nat \<Rightarrow> int set" where
  "top1_Zn_group n = {0..<int n}"

definition top1_Zn_mul :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "top1_Zn_mul n a b = (a + b) mod int n"

definition top1_Zn_id :: "int" where
  "top1_Zn_id = 0"

definition top1_Zn_invg :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "top1_Zn_invg n a = (int n - a) mod int n"

text \<open>The torsion subgroup of an abelian group.\<close>
definition top1_torsion_subgroup_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> 'g set" where
  "top1_torsion_subgroup_on G mul e =
     {x\<in>G. \<exists>n. n > 0 \<and> top1_group_pow mul e x n = e}"

text \<open>Commutator [a, b] = a b a\<inverse> b\<inverse> in a group.\<close>
definition top1_group_commutator_on ::
  "('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> 'g" where
  "top1_group_commutator_on mul invg a b = mul (mul (mul a b) (invg a)) (invg b)"

text \<open>The commutator subgroup [G, G] generated by all commutators [a, b].\<close>
definition top1_commutator_subgroup_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set" where
  "top1_commutator_subgroup_on G mul e invg =
     top1_subgroup_generated_on G mul e invg
       { top1_group_commutator_on mul invg a b | a b. a \<in> G \<and> b \<in> G }"

text \<open>Normalizer of H in G: N(H) = {g \<in> G | gHg\<inverse> = H}.\<close>
definition top1_normalizer_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set" where
  "top1_normalizer_on G mul invg H =
     {g \<in> G. {mul (mul g h) (invg g) | h. h \<in> H} = H}"

text \<open>H is the abelianization of G: H = G/[G, G] with the induced abelian structure.
  Equivalently, H is an abelian group together with a surjective homomorphism
  \<phi>: G \<rightarrow> H whose kernel is [G, G] (the commutator subgroup).\<close>
definition top1_is_abelianization_of ::
  "'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> 'h \<Rightarrow> ('h \<Rightarrow> 'h) \<Rightarrow>
   'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g \<Rightarrow> ('g \<Rightarrow> 'g) \<Rightarrow>
   ('g \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi> \<longleftrightarrow>
     top1_is_abelian_group_on H mulH eH invgH \<and>
     top1_is_group_on G mul e invg \<and>
     top1_group_hom_on G mul H mulH \<phi> \<and>
     \<phi> ` G = H \<and>
     top1_group_kernel_on G eH \<phi> = top1_commutator_subgroup_on G mul e invg"

section \<open>\<S>67 Direct Sums of Abelian Groups\<close>

text \<open>External direct sum: the set of finitely-supported functions J \<rightarrow> \<Union>G_\<alpha>.\<close>
text \<open>External direct sum: the set of finitely-supported functions f : J \<rightarrow> \<Union>_\<alpha> G_\<alpha>
  with f \<alpha> \<in> G_\<alpha> and f \<alpha> = e_\<alpha> (the identity of G_\<alpha>) for all but finitely many \<alpha>.\<close>
definition top1_direct_sum_carrier ::
  "'i set \<Rightarrow> ('i \<Rightarrow> 'g set) \<Rightarrow> ('i \<Rightarrow> 'g) \<Rightarrow> ('i \<Rightarrow> 'g) set" where
  "top1_direct_sum_carrier J G eFam =
     {f. (\<forall>i\<in>J. f i \<in> G i) \<and> (\<forall>i. i \<notin> J \<longrightarrow> f i = eFam i) \<and>
         finite {i\<in>J. f i \<noteq> eFam i}}"

text \<open>H is an (internal) direct sum of the abelian groups {G_\<alpha>}_{\<alpha>\<in>J} along
  injections \<iota>fam_\<alpha>: G_\<alpha> \<hookrightarrow> H iff H is abelian and the natural map from the
  external direct sum to H (sending f to the finite product \<Prod>_\<alpha> \<iota>fam_\<alpha>(f \<alpha>))
  is a group isomorphism whose restriction to the \<alpha>-th 'axis' is \<iota>fam_\<alpha>.\<close>
definition top1_is_direct_sum_of_on ::
  "'h set \<Rightarrow> ('h \<Rightarrow> 'h \<Rightarrow> 'h) \<Rightarrow> 'h \<Rightarrow> ('h \<Rightarrow> 'h) \<Rightarrow>
   'i set \<Rightarrow> ('i \<Rightarrow> 'g set) \<Rightarrow> ('i \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow>
   ('i \<Rightarrow> 'g) \<Rightarrow> ('i \<Rightarrow> 'g \<Rightarrow> 'h) \<Rightarrow> bool" where
  "top1_is_direct_sum_of_on H mulH eH invgH J G mulG eG \<iota>fam \<longleftrightarrow>
     top1_is_abelian_group_on H mulH eH invgH \<and>
     (\<forall>\<alpha>\<in>J. top1_group_hom_on (G \<alpha>) (mulG \<alpha>) H mulH (\<iota>fam \<alpha>)) \<and>
     (\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (G \<alpha>)) \<and>
     (\<exists>\<Phi>. top1_group_iso_on
            (top1_direct_sum_carrier J G eG)
            (\<lambda>f g. \<lambda>\<alpha>. if \<alpha> \<in> J then mulG \<alpha> (f \<alpha>) (g \<alpha>) else eG \<alpha>)
            H mulH \<Phi>
          \<and> (\<forall>\<alpha>\<in>J. \<forall>x\<in>G \<alpha>. \<Phi> (\<lambda>\<beta>. if \<beta> = \<alpha> then x else eG \<beta>) = \<iota>fam \<alpha> x))"

(** from \<S>67 Theorem 67.4: existence of external direct sum of abelian groups.
    The direct sum (finitely-supported coordinate-wise functions) is an abelian group,
    equipped with natural injections \<iota>fam_\<alpha> : G_\<alpha> \<hookrightarrow> \<oplus>_\<alpha> G_\<alpha>. **)
theorem Theorem_67_4_direct_sum_exists:
  assumes "\<forall>\<alpha>\<in>(J::'i set). top1_is_abelian_group_on (G \<alpha>::'g set) (mul \<alpha>) (e \<alpha>) (invg \<alpha>)"
  shows "\<exists>\<iota>fam.
           top1_is_abelian_group_on
             (top1_direct_sum_carrier J G e)
             (\<lambda>f g. \<lambda>\<alpha>. if \<alpha> \<in> J then mul \<alpha> (f \<alpha>) (g \<alpha>) else e \<alpha>)
             e
             (\<lambda>f. \<lambda>\<alpha>. if \<alpha> \<in> J then invg \<alpha> (f \<alpha>) else e \<alpha>)
         \<and> (\<forall>\<alpha>\<in>J. top1_group_hom_on (G \<alpha>) (mul \<alpha>)
               (top1_direct_sum_carrier J G e)
               (\<lambda>f g. \<lambda>\<beta>. if \<beta> \<in> J then mul \<beta> (f \<beta>) (g \<beta>) else e \<beta>)
               (\<iota>fam \<alpha>))
         \<and> (\<forall>\<alpha>\<in>J. inj_on (\<iota>fam \<alpha>) (G \<alpha>))
         \<and> (\<forall>\<alpha>\<in>J. \<forall>x\<in>G \<alpha>. \<iota>fam \<alpha> x \<alpha> = x \<and>
              (\<forall>\<beta>. \<beta> \<noteq> \<alpha> \<longrightarrow> \<iota>fam \<alpha> x \<beta> = e \<beta>))"
  sorry

(** from \<S>67 Theorem 67.6: uniqueness of external direct sum.
    If (H_1, \<iota>_1) and (H_2, \<iota>_2) are both direct sums of a family {G_\<alpha>}_{\<alpha>\<in>J} of
    abelian groups (with injective homomorphisms \<iota>_i_\<alpha>: G_\<alpha> \<rightarrow> H_i making H_i the
    internal direct sum of their images), then H_1 \<cong> H_2 as abelian groups. **)
theorem Theorem_67_6_direct_sum_unique:
  fixes J :: "'i set"
    and G :: "'i \<Rightarrow> 'g set" and mul :: "'i \<Rightarrow> 'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and eG :: "'i \<Rightarrow> 'g"
    and H1 H2 :: "'h set" and mulH1 mulH2 :: "'h \<Rightarrow> 'h \<Rightarrow> 'h"
    and eH1 eH2 :: 'h and invgH1 invgH2 :: "'h \<Rightarrow> 'h"
    and \<iota>fam1 \<iota>fam2 :: "'i \<Rightarrow> 'g \<Rightarrow> 'h"
  assumes "top1_is_direct_sum_of_on H1 mulH1 eH1 invgH1 J G mul eG \<iota>fam1"
      and "top1_is_direct_sum_of_on H2 mulH2 eH2 invgH2 J G mul eG \<iota>fam2"
  shows "top1_groups_isomorphic_on H1 mulH1 H2 mulH2"
  sorry

(** from \<S>67 Theorem 67.8: rank of free abelian group is well-defined.
    Any two bases of a free abelian group have the same cardinality. **)
theorem Theorem_67_8_rank_unique:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and iota1 :: "'s1 \<Rightarrow> 'g" and S1 :: "'s1 set"
    and iota2 :: "'s2 \<Rightarrow> 'g" and S2 :: "'s2 set"
  assumes "top1_is_free_abelian_group_full_on G mul e invg iota1 S1"
      and "top1_is_free_abelian_group_full_on G mul e invg iota2 S2"
  shows "\<exists>f. bij_betw f S1 S2"
  \<comment> \<open>S1 and S2 have the same cardinality (as sets): there's a bijection S1 \<rightarrow> S2.
     Note: we cannot use 'card S1 = card S2' because Isabelle's card returns 0 for
     infinite sets, making the statement trivial for infinite-rank free abelian groups.\<close>
  sorry

section \<open>\<S>68 Free Products of Groups\<close>

text \<open>Reduced words in a free product G_1 * G_2.\<close>
text \<open>Reduced words in the free product G_1 * G_2: non-empty alternating sequences
  w_1 w_2 ... w_n where each w_i is in G_1 \<setminus> {e_1} or G_2 \<setminus> {e_2}, and
  consecutive w_i's come from different factors.\<close>
definition top1_free_product_carrier ::
  "'g set \<Rightarrow> 'g \<Rightarrow> 'g set \<Rightarrow> 'g \<Rightarrow> (('g \<times> bool) list) set" where
  "top1_free_product_carrier G1 e1 G2 e2 =
     {ws. (\<forall>i<length ws.
              (snd (ws!i) \<longrightarrow> fst (ws!i) \<in> G1 \<and> fst (ws!i) \<noteq> e1)
            \<and> (\<not> snd (ws!i) \<longrightarrow> fst (ws!i) \<in> G2 \<and> fst (ws!i) \<noteq> e2))
        \<and> (\<forall>i. i+1 < length ws \<longrightarrow> snd (ws!i) \<noteq> snd (ws!(i+1)))}"
     \<comment> \<open>The boolean flag indicates which factor each element belongs to.
         Empty list represents the identity.\<close>

(** from \<S>68 Theorem 68.2: given a family of groups, a free product exists. **)
theorem Theorem_68_2_free_product_exists:
  assumes "\<forall>\<alpha>\<in>(J::'i set). top1_is_group_on (GG \<alpha>::'gg set) (mulGG \<alpha>) (eGG \<alpha>) (invgGG \<alpha>)"
  shows "\<exists>(G::'gg set) mul e invg \<iota>fam.
           top1_is_free_product_on G mul e invg GG mulGG \<iota>fam J"
  sorry

(** from \<S>68 Theorem 68.4: uniqueness of free product — any two
    free products of the same family are isomorphic. **)
theorem Theorem_68_4_free_product_unique:
  assumes "top1_is_free_product_on (G1::'g set) mul1 e1 invg1 GG mulGG \<iota>1 J"
      and "top1_is_free_product_on (G2::'g set) mul2 e2 invg2 GG mulGG \<iota>2 J"
  shows "top1_groups_isomorphic_on G1 mul1 G2 mul2"
  sorry

(** from \<S>68 Theorem 68.7: if G = G_1 * G_2 is a free product and N_i \<lhd> G_i are
    normal, then (G_1 * G_2) / \<langle>\<langle>N_1 \<union> N_2\<rangle>\<rangle> \<cong> (G_1/N_1) * (G_2/N_2). **)
theorem Theorem_68_7_quotient_free_product:
  fixes G1 G2 :: "'g set"
    and mul1 mul2 :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e1 e2 :: 'g
    and invg1 invg2 :: "'g \<Rightarrow> 'g"
    and N1 N2 :: "'g set"
  assumes "top1_is_group_on G1 mul1 e1 invg1"
      and "top1_is_group_on G2 mul2 e2 invg2"
      and "top1_normal_subgroup_on G1 mul1 e1 invg1 N1"
      and "top1_normal_subgroup_on G2 mul2 e2 invg2 N2"
  shows "\<exists>(FP::'f set) mulFP eFP invgFP \<iota>fam12
          (FPQ::'fq set) mulFPQ eFPQ invgFPQ \<iota>famQ.
           top1_is_free_product_on FP mulFP eFP invgFP
             (\<lambda>i::nat. if i = 0 then G1 else G2)
             (\<lambda>i. if i = 0 then mul1 else mul2)
             \<iota>fam12 {0, 1}
         \<and> top1_is_free_product_on FPQ mulFPQ eFPQ invgFPQ
             (\<lambda>i::nat. if i = 0
                       then top1_quotient_group_carrier_on G1 mul1 N1
                       else top1_quotient_group_carrier_on G2 mul2 N2)
             (\<lambda>i::nat. top1_quotient_group_mul_on (if i = 0 then mul1 else mul2))
             \<iota>famQ {0, 1}
         \<and> top1_groups_isomorphic_on
             (top1_quotient_group_carrier_on FP mulFP
                (top1_normal_subgroup_generated_on FP mulFP eFP invgFP
                   (\<iota>fam12 0 ` N1 \<union> \<iota>fam12 1 ` N2)))
             (top1_quotient_group_mul_on mulFP)
             FPQ mulFPQ"
  sorry

section \<open>\<S>69 Free Groups\<close>

text \<open>A free group on a set S is a group G together with \<iota>: S \<hookrightarrow> G such that
  \<iota>(S) generates G, \<iota> is injective, and (externally) for any group H and
  function \<phi>: S \<rightarrow> H there is a unique homomorphism \<psi>: G \<rightarrow> H with \<psi> \<circ> \<iota> = \<phi>.
  See top1_is_free_group_full_on (intrinsic) and top1_free_group_universal_prop
  (external) above.\<close>

(** from \<S>69 Theorem 69.2: free product of free groups on S1, S2 (disjoint)
    is the free group on S1 \<union> S2. **)
theorem Theorem_69_2:
  fixes G1 G2 :: "'g set"
    and mul1 mul2 :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e1 e2 :: 'g
    and invg1 invg2 :: "'g \<Rightarrow> 'g"
    and \<iota>1 \<iota>2 :: "'s \<Rightarrow> 'g"
    and S1 S2 :: "'s set"
  assumes "top1_is_free_group_full_on G1 mul1 e1 invg1 \<iota>1 S1"
      and "top1_is_free_group_full_on G2 mul2 e2 invg2 \<iota>2 S2"
      and "S1 \<inter> S2 = {}"
  shows "\<exists>(FP::'f set) mulFP eFP invgFP \<iota>fam12 \<iota>S12.
           top1_is_free_product_on FP mulFP eFP invgFP
             (\<lambda>i::nat. if i = 0 then G1 else G2)
             (\<lambda>i. if i = 0 then mul1 else mul2)
             \<iota>fam12 {0, 1}
         \<and> top1_is_free_group_full_on FP mulFP eFP invgFP \<iota>S12 (S1 \<union> S2)
         \<and> (\<forall>s\<in>S1. \<iota>S12 s = \<iota>fam12 0 (\<iota>1 s))
         \<and> (\<forall>s\<in>S2. \<iota>S12 s = \<iota>fam12 1 (\<iota>2 s))"
  sorry

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
  shows "\<exists>(H::'h set) mulH eH invgH \<phi> \<iota>H.
           top1_is_abelianization_of H mulH eH invgH G mul e invg \<phi>
         \<and> top1_is_free_abelian_group_full_on H mulH eH invgH \<iota>H S
         \<and> (\<forall>s\<in>S. \<iota>H s = \<phi> (\<iota> s))"
  sorry

section \<open>\<S>70 The Seifert-van Kampen Theorem\<close>

section \<open>\<S>71 The Fundamental Group of a Wedge of Circles\<close>

text \<open>A wedge of circles at a common point p (Munkres §71): a Hausdorff space X
  with a family \<C>_\<alpha> (\<alpha>\<in>J) of subspaces, each homeomorphic to S^1, pairwise
  intersecting only at p, whose union is X. The topology on X is the weak
  topology: a set is closed iff its intersection with each C_\<alpha> is closed.\<close>
definition top1_is_wedge_of_circles_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'i set \<Rightarrow> 'a \<Rightarrow> bool" where
  "top1_is_wedge_of_circles_on X TX J p \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     is_hausdorff_on X TX \<and>
     p \<in> X \<and>
     (\<exists>C. (\<forall>\<alpha>\<in>J. C \<alpha> \<subseteq> X \<and> p \<in> C \<alpha>
             \<and> (\<exists>h. top1_homeomorphism_on top1_S1 top1_S1_topology
                      (C \<alpha>) (subspace_topology X TX (C \<alpha>)) h))
        \<and> (\<Union>\<alpha>\<in>J. C \<alpha>) = X
        \<and> (\<forall>\<alpha>\<in>J. \<forall>\<beta>\<in>J. \<alpha> \<noteq> \<beta> \<longrightarrow> C \<alpha> \<inter> C \<beta> = {p})
        \<and> (\<forall>D. D \<subseteq> X \<longrightarrow>
             (closedin_on X TX D \<longleftrightarrow>
              (\<forall>\<alpha>\<in>J. closedin_on (C \<alpha>) (subspace_topology X TX (C \<alpha>)) (C \<alpha> \<inter> D)))))"

text \<open>A polygonal region in R^2 with n \<ge> 3 sides: a closed convex polygon, i.e.,
  the convex hull of n vertices v_0, ..., v_{n-1} that are pairwise distinct and
  in convex position (no vertex lies in the convex hull of the others).
  The three conjuncts of the definition are: (i) vertices pairwise distinct,
  (ii) convex position (no vertex is a convex combination of the others),
  (iii) P is the convex hull as convex combinations of the vertices.\<close>
definition top1_is_polygonal_region_on :: "(real \<times> real) set \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_polygonal_region_on P n \<longleftrightarrow>
     n \<ge> 3 \<and>
     (\<exists>vx vy :: nat \<Rightarrow> real.
        (\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j))
      \<and> (\<forall>k<n. \<not> (\<exists>coeffs. (\<forall>i<n. i \<noteq> k \<longrightarrow> coeffs i \<ge> 0)
                          \<and> coeffs k = 0
                          \<and> (\<Sum>i<n. coeffs i) = 1
                          \<and> vx k = (\<Sum>i<n. coeffs i * vx i)
                          \<and> vy k = (\<Sum>i<n. coeffs i * vy i)))
      \<and> P = {(x, y) | x y.
                \<exists>coeffs. (\<forall>i<n. coeffs i \<ge> 0)
                       \<and> (\<Sum>i<n. coeffs i) = 1
                       \<and> x = (\<Sum>i<n. coeffs i * vx i)
                       \<and> y = (\<Sum>i<n. coeffs i * vy i)})"

text \<open>Edge scheme: a word w = y_1 y_2 ... y_n where each y_i is (label, orientation)
  specifying how boundary edges of a polygonal region are identified. Orientation
  True means forward, False means reversed.\<close>
type_synonym 'a top1_edge_scheme = "('a \<times> bool) list"

text \<open>X is the quotient space obtained from a polygonal region P (with n = length
  scheme sides, labelled by the scheme) by identifying boundary edges as the scheme
  specifies. The existential witnesses are: the polygonal region P; the quotient
  map q : P \<rightarrow> X; and the edge parametrization edge : nat \<Rightarrow> real \<Rightarrow> P (edge i
  parametrizes the i-th side of P). The conjuncts assert:
  (i) P is a polygonal region with length(scheme) sides;
  (ii) q is a quotient map;
  (iii) each edge i maps I into P;
  (iv) two edges with the same label are identified compatibly with their
      orientation (same bool \<Rightarrow> direct identification t\<sim>t; opposite bool \<Rightarrow>
      reversed identification t\<sim>1-t);
  (v) interior points of P (not on any scheme edge) have trivial q-fibre.\<close>
definition top1_quotient_of_scheme_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> 'b top1_edge_scheme \<Rightarrow> bool" where
  "top1_quotient_of_scheme_on X TX scheme \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<exists>P q (vx::nat\<Rightarrow>real) (vy::nat\<Rightarrow>real).
        top1_is_polygonal_region_on P (length scheme)
      \<and> top1_quotient_map_on P
          (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P) X TX q
      \<comment> \<open>vx, vy are the polygon vertices, pairwise distinct and in convex position.\<close>
      \<and> (\<forall>i<length scheme. \<forall>j<length scheme.
             i \<noteq> j \<longrightarrow> (vx i, vy i) \<noteq> (vx j, vy j))
      \<and> (\<forall>i<length scheme. (vx i, vy i) \<in> P)
      \<comment> \<open>Vertices are in cyclic order: non-adjacent edges don't share interior points.\<close>
      \<and> (\<forall>i<length scheme. \<forall>j<length scheme.
            i \<noteq> j \<longrightarrow> Suc i mod length scheme \<noteq> j \<longrightarrow> i \<noteq> Suc j mod length scheme \<longrightarrow>
            (\<forall>s\<in>{0<..<1}. \<forall>t\<in>{0<..<1}.
               ((1-s) * vx i + s * vx (Suc i mod length scheme),
                (1-s) * vy i + s * vy (Suc i mod length scheme))
             \<noteq> ((1-t) * vx j + t * vx (Suc j mod length scheme),
                (1-t) * vy j + t * vy (Suc j mod length scheme))))
      \<comment> \<open>The i-th edge is the segment from (vx i, vy i) to (vx ((i+1) mod n), vy ...).
          Same-label edges are identified with compatible orientation.\<close>
      \<and> (\<forall>i<length scheme. \<forall>j<length scheme.
            fst (scheme!i) = fst (scheme!j) \<longrightarrow>
            (\<forall>t\<in>I_set.
               q ((1-t) * vx i + t * vx (Suc i mod length scheme),
                  (1-t) * vy i + t * vy (Suc i mod length scheme))
             = (if snd (scheme!i) = snd (scheme!j)
                then q ((1-t) * vx j + t * vx (Suc j mod length scheme),
                        (1-t) * vy j + t * vy (Suc j mod length scheme))
                else q (t * vx j + (1-t) * vx (Suc j mod length scheme),
                        t * vy j + (1-t) * vy (Suc j mod length scheme)))))
      \<comment> \<open>Interior points (not on any boundary edge) have singleton q-fibre.\<close>
      \<and> (\<forall>p\<in>P. (\<forall>i<length scheme. \<forall>t\<in>I_set.
                    p \<noteq> ((1-t) * vx i + t * vx (Suc i mod length scheme),
                          (1-t) * vy i + t * vy (Suc i mod length scheme)))
               \<longrightarrow> (\<forall>p'\<in>P. q p = q p' \<longrightarrow> p = p')))"

text \<open>X is a polygonal quotient: there exists some scheme that produces X.\<close>
definition top1_is_polygonal_quotient_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_polygonal_quotient_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<exists>scheme::(nat \<times> bool) list. top1_quotient_of_scheme_on X TX scheme)"

text \<open>Standard scheme for the n-fold torus: a_1 b_1 a_1\<inverse> b_1\<inverse> \<cdots> a_n b_n a_n\<inverse> b_n\<inverse>,
  i.e. a 4n-sided polygon with this edge-identification word.\<close>
definition top1_n_torus_scheme :: "nat \<Rightarrow> (nat \<times> bool) list" where
  "top1_n_torus_scheme n =
     concat (map (\<lambda>i. [(2*i, True), (2*i+1, True), (2*i, False), (2*i+1, False)]) [0..<n])"

text \<open>Standard scheme for the m-fold projective plane: a_1 a_1 a_2 a_2 \<cdots> a_m a_m,
  a 2m-sided polygon.\<close>
definition top1_m_projective_scheme :: "nat \<Rightarrow> (nat \<times> bool) list" where
  "top1_m_projective_scheme m =
     concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<m])"

text \<open>n-fold torus T_n = quotient of a 4n-gon by the standard torus scheme.\<close>
definition top1_is_n_fold_torus_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_n_fold_torus_on X TX n \<longleftrightarrow>
     n > 0 \<and> top1_quotient_of_scheme_on X TX (top1_n_torus_scheme n)"

text \<open>n-fold dunce cap: quotient of B^2 where on S^1, q(z) = q(z') iff z' is a
  rotation of z by a multiple of 2\<pi>/n; on the interior, q is injective; interior
  and boundary orbits are separated.  The resulting space has \<pi>_1 = Z/nZ.\<close>
definition top1_is_dunce_cap_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_dunce_cap_on X TX n \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     n > 0 \<and>
     (\<exists>q. top1_quotient_map_on top1_B2 top1_B2_topology X TX q
        \<and> (\<forall>z\<in>top1_S1. \<forall>z'\<in>top1_S1.
              q z = q z' \<longleftrightarrow>
              (\<exists>k::nat. k < n \<and>
                 z' = (cos (2*pi*real k/real n) * fst z
                         - sin (2*pi*real k/real n) * snd z,
                       sin (2*pi*real k/real n) * fst z
                         + cos (2*pi*real k/real n) * snd z)))
        \<and> inj_on q (top1_B2 - top1_S1)
        \<and> (\<forall>z\<in>top1_B2 - top1_S1. \<forall>z'\<in>top1_S1. q z \<noteq> q z'))"

text \<open>m-fold projective plane P_m: quotient of a 2m-gon by the scheme a_1 a_1 ... a_m a_m.
  For m = 1 this would require a 2-gon (not a valid polygonal region, which requires
  n \<ge> 3), so we handle m = 1 separately: P_1 = real projective plane RP^2 = quotient
  of B^2 by antipodal identification on S^1 = the 2-fold dunce cap.\<close>
definition top1_is_m_fold_projective_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_is_m_fold_projective_on X TX m \<longleftrightarrow>
     (m = 1 \<and> top1_is_dunce_cap_on X TX (2::nat)) \<or>
     (m \<ge> 2 \<and> top1_quotient_of_scheme_on X TX (top1_m_projective_scheme m))"

text \<open>The torus T² = S¹ × S¹ (the 1-fold torus in Munkres' sense).\<close>
definition top1_is_torus_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_torus_on X TX \<longleftrightarrow>
     top1_is_n_fold_torus_on X TX 1"

text \<open>The standard closed 2-simplex {(x, y). x \<ge> 0 \<and> y \<ge> 0 \<and> x + y \<le> 1}.\<close>
definition top1_standard_simplex :: "(real \<times> real) set" where
  "top1_standard_simplex = {p. fst p \<ge> 0 \<and> snd p \<ge> 0 \<and> fst p + snd p \<le> 1}"

definition top1_standard_simplex_topology :: "(real \<times> real) set set" where
  "top1_standard_simplex_topology =
     subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets)
       top1_standard_simplex"

text \<open>Edges of the standard simplex (the three line segments on its boundary).\<close>
definition top1_standard_simplex_edges :: "(real \<times> real) set set" where
  "top1_standard_simplex_edges =
     { {p\<in>top1_standard_simplex. fst p = 0},
       {p\<in>top1_standard_simplex. snd p = 0},
       {p\<in>top1_standard_simplex. fst p + snd p = 1} }"

text \<open>Vertices of the standard simplex.\<close>
definition top1_standard_simplex_vertices :: "(real \<times> real) set" where
  "top1_standard_simplex_vertices = {(0, 0), (1, 0), (0, 1)}"

text \<open>Triangulable: X has a triangulation — a finite collection \<T> of closed subspaces,
  each homeomorphic to a 2-simplex, covering X, such that any two distinct triangles
  intersect in either \<emptyset>, a common vertex, or a common edge (the common-face property).
  We express the common-face condition via the homeomorphism images.\<close>
definition top1_is_triangulable_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_triangulable_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<exists>(\<T> :: 'a set set) (h :: 'a set \<Rightarrow> (real \<times> real) \<Rightarrow> 'a).
        finite \<T>
      \<and> (\<Union>\<T>) = X
      \<and> (\<forall>T\<in>\<T>. T \<subseteq> X \<and> closedin_on X TX T
            \<and> top1_homeomorphism_on
                 top1_standard_simplex top1_standard_simplex_topology
                 T (subspace_topology X TX T) (h T))
      \<and> (\<forall>T1\<in>\<T>. \<forall>T2\<in>\<T>. T1 \<noteq> T2 \<longrightarrow>
            T1 \<inter> T2 = {}
          \<or> (\<exists>v1 v2. v1 \<in> top1_standard_simplex_vertices \<and>
                     v2 \<in> top1_standard_simplex_vertices \<and>
                     T1 \<inter> T2 = {h T1 v1} \<and> {h T1 v1} = {h T2 v2})
          \<or> (\<exists>E1\<in>top1_standard_simplex_edges. \<exists>E2\<in>top1_standard_simplex_edges.
                 T1 \<inter> T2 = h T1 ` E1 \<and> h T1 ` E1 = h T2 ` E2)))"

text \<open>Elementary scheme operations (Munkres §76): inductive rewrite rules on edge
  schemes preserving the resulting quotient topology. Munkres defines:
  (i) cyclic permutation (rotate), (ii) cancellation of aa\<inverse> (when length \<ge> 5),
  (iii) relabel one letter to a new fresh letter (and consistently flip the bool),
  (iv) cut: replace w_1 w_2 by w_1 c c\<inverse> w_2 for a fresh letter c, (v) paste: the
  reverse of cut when edges form an adjacent pair, (vi) inverse: flip an edge.\<close>
inductive top1_elementary_scheme_operation ::
  "'a top1_edge_scheme \<Rightarrow> 'a top1_edge_scheme \<Rightarrow> bool" where
    refl:     "top1_elementary_scheme_operation s s"
  | sym:      "top1_elementary_scheme_operation s t \<Longrightarrow>
               top1_elementary_scheme_operation t s"
  | trans:    "\<lbrakk>top1_elementary_scheme_operation s t;
                top1_elementary_scheme_operation t u\<rbrakk> \<Longrightarrow>
               top1_elementary_scheme_operation s u"
  | rotate:   "top1_elementary_scheme_operation (xs @ ys) (ys @ xs)"
  | cancel:   "top1_elementary_scheme_operation
                 (xs @ [(a, b), (a, \<not> b)] @ ys)
                 (xs @ ys)"
  | relabel:  "\<lbrakk>a \<notin> fst ` set s; a \<noteq> c\<rbrakk> \<Longrightarrow>
               top1_elementary_scheme_operation
                 s
                 (map (\<lambda>(x, b). (if x = c then a else x, b)) s)"
  | invert:   "top1_elementary_scheme_operation
                 s
                 (rev (map (\<lambda>(x, b). (x, \<not> b)) s))"
  | cut:      "\<lbrakk>c \<notin> fst ` set (xs @ ys)\<rbrakk> \<Longrightarrow>
               top1_elementary_scheme_operation
                 (xs @ ys)
                 (xs @ [(c, True), (c, False)] @ ys)"

text \<open>Subgroup index: H has index k in G iff there are exactly k left cosets g H.
  We represent the set of left cosets directly (does not require H to be normal).\<close>
definition top1_left_cosets_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> 'g set set" where
  "top1_left_cosets_on G mul H = { top1_group_coset_on G mul H g | g. g \<in> G }"

definition top1_subgroup_has_index_on ::
  "'g set \<Rightarrow> ('g \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g set \<Rightarrow> nat \<Rightarrow> bool" where
  "top1_subgroup_has_index_on G mul H k \<longleftrightarrow>
     finite (top1_left_cosets_on G mul H) \<and>
     card (top1_left_cosets_on G mul H) = k"
     \<comment> \<open>Finite index only. Infinite-index subgroups are expressed by negating this
         predicate (or by asserting infinite (top1_left_cosets_on ...)), not by k = 0.\<close>


(** from \<S>71 Theorem 71.1: finite wedge of circles has free fundamental group
    generated by the individual circle loops. **)
theorem Theorem_71_1_wedge_of_circles_finite:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and p :: 'a
  assumes "top1_is_wedge_of_circles_on X TX {..<n} p"
  shows "\<exists>(G::'g set) mul e invg (\<iota>::nat \<Rightarrow> 'g).
           top1_is_free_group_full_on G mul e invg \<iota> {..<n}
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX p)
             (top1_fundamental_group_mul X TX p)"
  sorry

(** from \<S>71 Theorem 71.3: arbitrary (possibly infinite) wedge of circles. **)
theorem Theorem_71_3_wedge_of_circles_general:
  fixes J :: "'i set" and X :: "'a set" and TX :: "'a set set" and p :: 'a
  assumes "top1_is_wedge_of_circles_on X TX J p"
  shows "\<exists>(G::'g set) mul e invg (\<iota>::'i \<Rightarrow> 'g).
           top1_is_free_group_full_on G mul e invg \<iota> J
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX p)
             (top1_fundamental_group_mul X TX p)"
  sorry

section \<open>\<S>72 Adjoining a Two-Cell\<close>

(** from \<S>72 Theorem 72.1: attaching a 2-cell kills the homotopy class of
    the attaching map. There exists an isomorphism \<pi>_1(X, a) \<cong>
    \<pi>_1(A, a) / normal-closure(k_*[p]) where p is the standard loop of S^1
    and k : S^1 \<rightarrow> A is the restriction of h : B^2 \<rightarrow> X to the boundary. **)
theorem Theorem_72_1_attaching_two_cell:
  fixes X :: "'a set" and TX :: "'a set set" and A :: "'a set"
    and h :: "real \<times> real \<Rightarrow> 'a" and a :: 'a
  assumes "is_topology_on_strict X TX"
      and "is_hausdorff_on X TX"
      and "closedin_on X TX A"
      and "top1_path_connected_on A (subspace_topology X TX A)"
      and "top1_continuous_map_on top1_B2 top1_B2_topology X TX h"
      and "a \<in> A"
      \<comment> \<open>h restricted to Int(B²) = B² - S¹ is a homeomorphism onto X - A.\<close>
      and "top1_homeomorphism_on
             (top1_B2 - top1_S1)
             (subspace_topology top1_B2 top1_B2_topology (top1_B2 - top1_S1))
             (X - A)
             (subspace_topology X TX (X - A))
             h"
      and "h ` top1_S1 \<subseteq> A"
      and "h (1, 0) = a"
  shows "\<exists>\<iota>.
            top1_continuous_map_on top1_S1 top1_S1_topology A
                 (subspace_topology X TX A) \<iota>
          \<and> (\<forall>z\<in>top1_S1. \<iota> z = h z)
          \<and> top1_groups_isomorphic_on
                (top1_fundamental_group_carrier X TX a)
                (top1_fundamental_group_mul X TX a)
                (top1_quotient_group_carrier_on
                   (top1_fundamental_group_carrier A (subspace_topology X TX A) a)
                   (top1_fundamental_group_mul A (subspace_topology X TX A) a)
                   (top1_normal_subgroup_generated_on
                      (top1_fundamental_group_carrier A (subspace_topology X TX A) a)
                      (top1_fundamental_group_mul A (subspace_topology X TX A) a)
                      (top1_fundamental_group_id A (subspace_topology X TX A) a)
                      (top1_fundamental_group_invg A (subspace_topology X TX A) a)
                      \<comment> \<open>Relator: the image under \<iota>_* of the class of the standard
                          S^1 loop p(s) = (cos 2\<pi>s, sin 2\<pi>s) based at (1, 0). This
                          class is {g. loop_equiv_on S^1 ((1,0)) p g} — the
                          equivalence class of p in \<pi>_1(S^1, (1,0)).\<close>
                      {top1_fundamental_group_induced_on top1_S1 top1_S1_topology (1, 0)
                         A (subspace_topology X TX A) a \<iota>
                         {g. top1_loop_equiv_on top1_S1 top1_S1_topology (1, 0)
                               (\<lambda>s. (cos (2 * pi * s), sin (2 * pi * s))) g}}))
                (top1_quotient_group_mul_on
                   (top1_fundamental_group_mul A (subspace_topology X TX A) a))"
  \<comment> \<open>\<iota> is k = h|S^1. \<pi>_1(X, a) \<cong> \<pi>_1(A, a) / \<langle>\<langle>[k\<circ>p]\<rangle>\<rangle> with coset product,
      where p is the standard S^1 loop and k\<circ>p is a loop in A.\<close>
  sorry

section \<open>\<S>73 Fundamental Groups of the Torus and the Dunce Cap\<close>

(** from \<S>73 Theorem 73.1: \<pi>_1(torus) has presentation <\<alpha>, \<beta> | \<alpha>\<beta>\<alpha>^{-1}\<beta>^{-1}>,
    i.e. is isomorphic to the free abelian group Z \<times> Z on 2 generators. **)
theorem Theorem_73_1_torus_presentation:
  fixes T_torus :: "'a set" and TT :: "'a set set" and x0 :: 'a
  assumes "top1_is_torus_on T_torus TT"
      and "x0 \<in> T_torus"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier T_torus TT x0)
           (top1_fundamental_group_mul T_torus TT x0)
           (UNIV::(int \<times> int) set)
           (\<lambda>(a1, a2) (b1, b2). (a1 + b1, a2 + b2))"
  sorry

(** from \<S>73 Theorem 73.4: the n-fold dunce cap has fundamental group Z/nZ. **)
theorem Theorem_73_4_dunce_cap:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "n > 0"
      and "top1_is_dunce_cap_on X TX n"
      and "x0 \<in> X"
  shows "top1_groups_isomorphic_on
           (top1_fundamental_group_carrier X TX x0)
           (top1_fundamental_group_mul X TX x0)
           (top1_Zn_group n)
           (top1_Zn_mul n)"
  sorry

(** from \<S>70 Theorem 70.2 (Seifert-van Kampen, classical version): if X = U \<union> V
    with U, V, U \<inter> V open and path-connected, then \<pi>_1(X, x_0) is isomorphic to
    the free product of \<pi>_1(U, x_0) and \<pi>_1(V, x_0) amalgamated over \<pi>_1(U \<inter> V, x_0).
    Equivalently, the images i_*(\<pi>_1(U)) and j_*(\<pi>_1(V)) generate \<pi>_1(X), and the
    kernel of the natural surjection is the normal subgroup generated by elements
    of the form (i_1)_*(\<gamma>) \<cdot> ((i_2)_*(\<gamma>))^{-1} for \<gamma> \<in> \<pi>_1(U \<inter> V). **)
theorem Theorem_70_2_SvK:
  assumes "is_topology_on_strict X TX" and "openin_on X TX U" and "openin_on X TX V"
      and "U \<union> V = X"
      and "top1_path_connected_on (U \<inter> V) (subspace_topology X TX (U \<inter> V))"
      and "top1_path_connected_on U (subspace_topology X TX U)"
      and "top1_path_connected_on V (subspace_topology X TX V)"
      and "x0 \<in> U \<inter> V"
  shows "\<exists>(FP::'f set) mulFP eFP invgFP \<iota>fam.
           top1_is_free_product_on FP mulFP eFP invgFP
             (\<lambda>i::nat. if i = 0
                then top1_fundamental_group_carrier U (subspace_topology X TX U) x0
                else top1_fundamental_group_carrier V (subspace_topology X TX V) x0)
             (\<lambda>i. if i = 0
                then top1_fundamental_group_mul U (subspace_topology X TX U) x0
                else top1_fundamental_group_mul V (subspace_topology X TX V) x0)
             \<iota>fam {0, 1}
         \<and> top1_groups_isomorphic_on
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             (top1_quotient_group_carrier_on FP mulFP
                (top1_normal_subgroup_generated_on FP mulFP eFP invgFP
                   { mulFP (\<iota>fam 0 (top1_fundamental_group_induced_on
                        (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0
                        U (subspace_topology X TX U) x0 (\<lambda>x. x) c))
                          (invgFP (\<iota>fam 1 (top1_fundamental_group_induced_on
                            (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0
                            V (subspace_topology X TX V) x0 (\<lambda>x. x) c)))
                    | c. c \<in> top1_fundamental_group_carrier
                           (U \<inter> V) (subspace_topology X TX (U \<inter> V)) x0 }))
             (top1_quotient_group_mul_on mulFP)"
  \<comment> \<open>Seifert-van Kampen: \<pi>_1(X, x_0) \<cong> (\<pi>_1(U) \<star> \<pi>_1(V)) / \<langle>\<langle>{i_1(\<gamma>) \<cdot> i_2(\<gamma>)\<inverse> |
      \<gamma> \<in> \<pi>_1(U\<inter>V)}\<rangle>\<rangle>: the amalgamated free product over \<pi>_1(U\<inter>V).\<close>
  sorry

section \<open>Chapter 12: Classification of Surfaces\<close>

text \<open>Surface: a connected, Hausdorff, compact 2-manifold.
  A 2-manifold is a space where every point has a neighborhood homeomorphic
  to an open subset of R^2.\<close>
definition top1_is_2_manifold_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_2_manifold_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     is_hausdorff_on X TX \<and>
     (\<forall>x\<in>X. \<exists>U (V :: (real \<times> real) set) h.
        x \<in> U \<and> openin_on X TX U \<and>
        V \<in> product_topology_on top1_open_sets top1_open_sets \<and>
        top1_homeomorphism_on U (subspace_topology X TX U) V
          (subspace_topology UNIV
             (product_topology_on top1_open_sets top1_open_sets) V)
          h)"
     \<comment> \<open>Munkres's definition of an n-manifold requires Hausdorff (and second countable,
         but that's implied by compact + locally Euclidean for our surface case).\<close>

definition top1_is_surface_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_surface_on X TX \<longleftrightarrow>
     top1_is_2_manifold_on X TX \<and>
     top1_connected_on X TX \<and>
     is_hausdorff_on X TX \<and>
     top1_compact_on X TX \<and>
     X \<noteq> {}"
     \<comment> \<open>Non-emptiness is required: classification theorem §77.5 says a surface is
         S^2, T_n, or P_m, none of which are empty. Without X \<noteq> {}, the empty set
         would vacuously satisfy locally-Euclidean and falsify §77.5.\<close>

section \<open>\<S>74 Fundamental Groups of Surfaces\<close>

\<comment> \<open>Unused undefined placeholders top1_n_fold_torus and top1_m_fold_projective
    removed. Use top1_is_n_fold_torus_on and top1_is_m_fold_projective_on predicates
    (defined earlier) on a space (X, TX) instead.\<close>

(** from \<S>74 Theorem 74.1: polygonal quotients are compact Hausdorff **)
theorem Theorem_74_1_polygon_quotient_compact_hausdorff:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "is_topology_on_strict X TX"
  and "top1_is_polygonal_quotient_on X TX"
  shows "top1_compact_on X TX \<and> is_hausdorff_on X TX"
  sorry

(** from \<S>74 Theorem 74.3: fundamental group of n-fold torus T_n has the
    presentation \<langle>a_1, b_1, \<dots>, a_n, b_n | [a_1,b_1]\<cdots>[a_n,b_n]\<rangle>.
    The single relator is the product (a_1 b_1 a_1\<inverse> b_1\<inverse>)\<cdots>(a_n b_n a_n\<inverse> b_n\<inverse>).
    We index generators 0, 1, ..., 2n-1 as a_i := 2i, b_i := 2i+1. **)
theorem Theorem_74_3_fund_group_n_torus:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_n_fold_torus_on X TX n"
      and "x0 \<in> X"
  shows "\<exists>(G::'g set) mul e invg.
           top1_group_presented_by_on G mul e invg ({..<2*n}::nat set)
             { concat (map (\<lambda>i. [(2*i, True), (2*i+1, True),
                                   (2*i, False), (2*i+1, False)]) [0..<n]) }
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)"
  sorry

(** from \<S>74 Theorem 74.4: \<pi>_1(P_m) has presentation \<langle>a_1, \<dots>, a_m | a_1\<^sup>2 \<cdots> a_m\<^sup>2\<rangle>.
    The single relator is (a_1 a_1)(a_2 a_2)\<cdots>(a_m a_m). **)
theorem Theorem_74_4_fund_group_m_projective:
  fixes m :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_m_fold_projective_on X TX m"
      and "x0 \<in> X"
  shows "\<exists>(G::'g set) mul e invg.
           top1_group_presented_by_on G mul e invg ({..<m}::nat set)
             { concat (map (\<lambda>i. [(i, True), (i, True)]) [0..<m]) }
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)"
  sorry

section \<open>\<S>76 Cutting and Pasting\<close>

(** from \<S>76: elementary operations on schemes preserve the resulting quotient space.
    If X1 is the quotient space induced by scheme1 and X2 by scheme2, and scheme2
    is obtained from scheme1 via an elementary operation, then X1 \<cong> X2. **)
theorem Theorem_76_elementary_operations:
  fixes scheme1 scheme2 :: "('a \<times> bool) list"
    and X1 X2 :: "'x set" and TX1 TX2 :: "'x set set"
  assumes "is_topology_on_strict X1 TX1" and "is_topology_on_strict X2 TX2"
      and "top1_elementary_scheme_operation scheme1 scheme2"
      and "top1_quotient_of_scheme_on X1 TX1 scheme1
         \<and> top1_quotient_of_scheme_on X2 TX2 scheme2"
  shows "\<exists>h. top1_homeomorphism_on X1 TX1 X2 TX2 h"
  sorry

section \<open>\<S>75 Homology of Surfaces\<close>

(** from \<S>75 Theorem 75.1: H_1(X, x_0) is the abelianization of \<pi>_1(X, x_0).
    There exists an abelian group H together with a surjective homomorphism
    \<pi>_1(X, x_0) \<rightarrow> H whose kernel is the commutator subgroup of \<pi>_1. **)
theorem Theorem_75_1_H1_abelianization:
  fixes X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  shows "\<exists>(H::'h set) mulH eH invgH \<phi>.
           top1_is_abelianization_of H mulH eH invgH
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             (top1_fundamental_group_id X TX x0)
             (top1_fundamental_group_invg X TX x0)
             \<phi>"
  sorry

(** from \<S>75 Theorem 75.3: H_1 of n-fold torus is free abelian of rank 2n.
    The abelianization of \<pi>_1(T_n) is free abelian on 2n generators. **)
theorem Theorem_75_3_H1_n_torus:
  fixes n :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_n_fold_torus_on X TX n"
      and "x0 \<in> X"
  shows "\<exists>(H::'h set) mulH eH invgH \<iota>_S \<phi>.
           top1_is_abelianization_of H mulH eH invgH
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             (top1_fundamental_group_id X TX x0)
             (top1_fundamental_group_invg X TX x0)
             \<phi>
         \<and> top1_is_free_abelian_group_full_on H mulH eH invgH
             (\<iota>_S::nat \<Rightarrow> 'h) {..<2*n}"
  sorry

(** from \<S>75 Theorem 75.4: H_1(m-fold projective plane):
    torsion subgroup is Z/2, free part is Z^{m-1}.
    Stated as: H = K \<oplus> Torsion(H) internally, where K \<subseteq> H is free abelian of rank m-1. **)
theorem Theorem_75_4_H1_m_projective:
  fixes m :: nat and X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_m_fold_projective_on X TX m"
      and "x0 \<in> X"
  shows "\<exists>(H::'h set) mulH eH invgH \<phi>.
           top1_is_abelianization_of H mulH eH invgH
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)
             (top1_fundamental_group_id X TX x0)
             (top1_fundamental_group_invg X TX x0)
             \<phi>
         \<and> card (top1_torsion_subgroup_on H mulH eH) = 2
         \<and> (\<exists>(K::'h set) (\<iota>_S::nat \<Rightarrow> 'h).
              K \<subseteq> H
            \<and> top1_is_free_abelian_group_full_on K mulH eH invgH \<iota>_S {..<m-1}
            \<and> K \<inter> top1_torsion_subgroup_on H mulH eH = {eH}
            \<and> (\<forall>h\<in>H. \<exists>k\<in>K. \<exists>t\<in>top1_torsion_subgroup_on H mulH eH.
                  h = mulH k t))"
  sorry

section \<open>*\<S>78 Constructing Compact Surfaces\<close>

(** from \<S>78 Theorem 78.1: compact triangulable surfaces are quotients of
    triangular regions by edge pasting. **)
theorem Theorem_78_1_triangulable_surface:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_is_surface_on X TX"
      and "top1_is_triangulable_on X TX"
  shows "\<exists>(\<T> :: (real \<times> real) set set) q.
           finite \<T>
         \<and> \<T> \<noteq> {}
         \<and> (\<forall>T \<in> \<T>. top1_is_polygonal_region_on T 3)
         \<comment> \<open>q on each triangle is continuous (not necessarily surjective).\<close>
         \<and> (\<forall>T \<in> \<T>. top1_continuous_map_on T
              (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) T)
              X TX q)
         \<comment> \<open>Together the triangles' images cover X.\<close>
         \<and> (\<Union>T\<in>\<T>. q ` T) = X
         \<comment> \<open>X has the final (quotient) topology w.r.t. q from the disjoint union of T's:
            U \<subseteq> X is open iff its pre-image in every triangle is open there.\<close>
         \<and> (\<forall>U. U \<subseteq> X \<longrightarrow>
             (U \<in> TX \<longleftrightarrow>
              (\<forall>T\<in>\<T>. {p\<in>T. q p \<in> U} \<in>
                subspace_topology UNIV
                  (product_topology_on top1_open_sets top1_open_sets) T)))"
  \<comment> \<open>\<T> is a finite collection of triangular regions; q edge-pastes them to form X.\<close>
  sorry

(** from \<S>78 Theorem 78.2: connected compact triangulable surfaces are
    quotients of a single polygonal region. **)
theorem Theorem_78_2_connected_polygonal_quotient:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_is_surface_on X TX"
      and "top1_connected_on X TX"
      and "top1_is_triangulable_on X TX"
  shows "\<exists>(P :: (real \<times> real) set) n q.
           top1_is_polygonal_region_on P n
         \<and> top1_quotient_map_on P
             (subspace_topology UNIV (product_topology_on top1_open_sets top1_open_sets) P)
             X TX q"
  \<comment> \<open>P is a polygonal region with n sides, q : P \<rightarrow> X is the edge-pasting quotient map.\<close>
  sorry

section \<open>\<S>77 The Classification Theorem\<close>

(** from \<S>77 Theorem 77.5: Classification theorem for compact surfaces.
    Every compact connected triangulable surface is homeomorphic to either:
    - the sphere S^2,
    - the n-fold torus T_n for some n \<ge> 1, or
    - the m-fold projective plane P_m for some m \<ge> 1. **)
theorem Theorem_77_5_classification:
  fixes X :: "'a set" and TX :: "'a set set"
  assumes "top1_is_surface_on X TX"
      and "top1_is_triangulable_on X TX"
  shows "(\<exists>h. top1_homeomorphism_on X TX top1_S2 top1_S2_topology h)
       \<or> (\<exists>n > 0. \<exists>(T_n::'a set) TT h.
             top1_is_n_fold_torus_on T_n TT n
           \<and> top1_homeomorphism_on X TX T_n TT h)
       \<or> (\<exists>m > 0. \<exists>(P_m::'a set) TP h.
             top1_is_m_fold_projective_on P_m TP m
           \<and> top1_homeomorphism_on X TX P_m TP h)"
  sorry

section \<open>Chapter 13: Classification of Covering Spaces\<close>

text \<open>Equivalence of covering spaces: homeomorphism commuting with covering maps.\<close>
definition top1_equivalent_coverings_on :: "'e set \<Rightarrow> 'e set set \<Rightarrow> 'e' set \<Rightarrow> 'e' set set
  \<Rightarrow> 'b set \<Rightarrow> 'b set set \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> ('e' \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_equivalent_coverings_on E TE E' TE' B TB p p' \<longleftrightarrow>
     top1_covering_map_on E TE B TB p \<and>
     top1_covering_map_on E' TE' B TB p' \<and>
     (\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e))"

(** from \<S>79 Theorem 79.2: pointed covering equivalence iff fundamental group
    images coincide. **)
theorem Theorem_79_2:
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict E' TE'"
      and "top1_covering_map_on E TE B TB p" and "p e0 = b0"
      and "top1_covering_map_on E' TE' B TB p'" and "p' e0' = b0"
      and "top1_path_connected_on E TE" and "top1_path_connected_on E' TE'"
      and "top1_locally_path_connected_on E TE" and "top1_locally_path_connected_on E' TE'"
  shows "(\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)
             \<and> h e0 = e0') \<longleftrightarrow>
         top1_fundamental_group_image_hom E TE e0 B TB b0 p
           = top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'"
  sorry

(** from \<S>79 Theorem 79.4: coverings are equivalent iff their subgroup images
    in \<pi>_1(B) are conjugate. **)
theorem Theorem_79_4:
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict E' TE'"
      and "top1_covering_map_on E TE B TB p" and "p e0 = b0"
      and "top1_covering_map_on E' TE' B TB p'" and "p' e0' = b0"
      and "top1_path_connected_on E TE" and "top1_path_connected_on E' TE'"
      and "top1_locally_path_connected_on E TE" and "top1_locally_path_connected_on E' TE'"
  shows "(\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)) \<longleftrightarrow>
         (\<exists>c \<in> top1_fundamental_group_carrier B TB b0.
            top1_fundamental_group_image_hom E' TE' e0' B TB b0 p'
            = (\<lambda>H. (top1_fundamental_group_mul B TB b0 c)
                ` ((\<lambda>h. top1_fundamental_group_mul B TB b0 h
                          (top1_fundamental_group_invg B TB b0 c)) ` H))
                (top1_fundamental_group_image_hom E TE e0 B TB b0 p))"
  \<comment> \<open>p_*(\<pi>_1(E, e_0)) and p'_*(\<pi>_1(E', e_0')) are conjugate subgroups of \<pi>_1(B, b_0).\<close>
  sorry

section \<open>\<S>79 Equivalence of Covering Spaces\<close>

\<comment> \<open>Theorems 79.2 and 79.4 are already above; this section heading organizes them.\<close>

section \<open>\<S>80 The Universal Covering Space\<close>

text \<open>A universal covering space is a simply connected covering space of B.\<close>
definition top1_is_universal_covering_on :: "'e set \<Rightarrow> 'e set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> bool" where
  "top1_is_universal_covering_on E TE B TB p \<longleftrightarrow>
     top1_covering_map_on E TE B TB p \<and>
     top1_simply_connected_on E TE"

(** from \<S>80: any two universal covering spaces are equivalent (via Theorem 79.4). **)
theorem Theorem_80_1_universal_unique:
  assumes "is_topology_on_strict B TB"
      and "top1_is_universal_covering_on E TE B TB p"
      and "top1_is_universal_covering_on E' TE' B TB p'"
      and "is_topology_on_strict E TE" and "is_topology_on_strict E' TE'"
      and "top1_path_connected_on E TE" and "top1_path_connected_on E' TE'"
      and "top1_locally_path_connected_on E TE" and "top1_locally_path_connected_on E' TE'"
      and "p e0 = b0" and "p' e0' = b0"
  shows "\<exists>h. top1_homeomorphism_on E TE E' TE' h \<and> (\<forall>e\<in>E. p' (h e) = p e)"
  \<comment> \<open>By Theorem 79.4: simply connected E gives trivial subgroup p_*(\<pi>_1 E) = {1};
      same for E'; and {1} is conjugate to itself.\<close>
  sorry

(** from \<S>80 Theorem 80.3: universal covering factors through any covering **)
theorem Theorem_80_3_universal:
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "is_topology_on_strict Y TY"
      and "top1_covering_map_on E TE B TB p"
      and "top1_simply_connected_on E TE"
      and "top1_covering_map_on Y TY B TB r"
  shows "\<exists>q. top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
  sorry

text \<open>Strict version of Theorem_80_3 — same statement but with simply_connected_strict.\<close>
corollary Theorem_80_3_universal_strict:
  assumes "top1_simply_connected_strict E TE"
      and "is_topology_on_strict B TB"
      and "is_topology_on_strict Y TY"
      and "top1_covering_map_on E TE B TB p"
      and "top1_covering_map_on Y TY B TB r"
  shows "\<exists>q. top1_covering_map_on E TE Y TY q \<and> (\<forall>e\<in>E. r (q e) = p e)"
  using Theorem_80_3_universal[of E TE B TB Y TY p r]
    top1_simply_connected_strict_imp[OF assms(1)]
    top1_simply_connected_strict_is_topology_strict[OF assms(1)]
    assms(2-5) by blast

section \<open>*\<S>81 Covering Transformations\<close>

text \<open>A covering transformation of p : E \<rightarrow> B is a homeomorphism h : E \<rightarrow> E
  with p \<circ> h = p. The group of covering transformations acts on the fiber.\<close>
definition top1_covering_transformation_on :: "'e set \<Rightarrow> 'e set set \<Rightarrow> 'b set \<Rightarrow> 'b set set
  \<Rightarrow> ('e \<Rightarrow> 'b) \<Rightarrow> ('e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "top1_covering_transformation_on E TE B TB p h \<longleftrightarrow>
     top1_homeomorphism_on E TE E TE h \<and> (\<forall>e\<in>E. p (h e) = p e)"

(** from *\<S>81 Theorem 81.2: the group of covering transformations Cov(p) is
    isomorphic to N(H)/H, where H = p_*(\<pi>_1(E, e_0)) and N(H) is its normalizer
    in \<pi>_1(B, b_0). **)
theorem Theorem_81_2_covering_group_iso:
  fixes E :: "'e set" and TE :: "'e set set"
    and B :: "'b set" and TB :: "'b set set"
    and p :: "'e \<Rightarrow> 'b" and b0 :: 'b and e0 :: 'e
  assumes "is_topology_on_strict E TE" and "is_topology_on_strict B TB"
      and "top1_covering_map_on E TE B TB p"
      and "top1_path_connected_on E TE"
      and "top1_locally_path_connected_on E TE"
      and "e0 \<in> E" and "p e0 = b0"
  shows "\<exists>(Cov::('e \<Rightarrow> 'e) set) eC invgC.
           Cov = {h. top1_covering_transformation_on E TE B TB p h}
         \<and> top1_is_group_on Cov (\<lambda>h k e. h (k e)) eC invgC
         \<and> top1_groups_isomorphic_on Cov (\<lambda>h k e. h (k e))
             (top1_quotient_group_carrier_on
                (top1_normalizer_on
                   (top1_fundamental_group_carrier B TB b0)
                   (top1_fundamental_group_mul B TB b0)
                   (top1_fundamental_group_invg B TB b0)
                   (top1_fundamental_group_image_hom E TE e0 B TB b0 p))
                (top1_fundamental_group_mul B TB b0)
                (top1_fundamental_group_image_hom E TE e0 B TB b0 p))
             (top1_quotient_group_mul_on (top1_fundamental_group_mul B TB b0))"
  sorry

section \<open>\<S>82 Existence of Covering Spaces\<close>

text \<open>Semilocally simply connected: every point has a neighborhood U such that
  every loop in U is nulhomotopic in X.\<close>
definition top1_semilocally_simply_connected_on ::
  "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_semilocally_simply_connected_on X TX \<longleftrightarrow>
     (\<forall>x\<in>X. \<exists>U. openin_on X TX U \<and> x \<in> U \<and>
        (\<forall>f. top1_is_loop_on U (subspace_topology X TX U) x f \<longrightarrow>
             top1_path_homotopic_on X TX x x f (top1_constant_path x)))"

(** from \<S>82 Theorem 82.1: existence of covering space for any subgroup.
    Given a subgroup H \<le> \<pi>_1(B, b_0), there exists a connected, locally path-connected
    covering (E, p) with a base-point e_0 over b_0 such that p_*(\<pi>_1(E, e_0)) = H. **)
theorem Theorem_82_1_covering_existence:
  assumes "is_topology_on_strict B TB"
      and "top1_path_connected_on B TB"
      and "top1_locally_path_connected_on B TB"
      and "top1_semilocally_simply_connected_on B TB"
      and "b0 \<in> B"
      and "H \<subseteq> top1_fundamental_group_carrier B TB b0"
      \<comment> \<open>H must be a subgroup, not just a subset.\<close>
      and "top1_is_group_on H
             (top1_fundamental_group_mul B TB b0)
             (top1_fundamental_group_id B TB b0)
             (top1_fundamental_group_invg B TB b0)"
  shows "\<exists>E TE p e0. is_topology_on_strict E TE
    \<and> top1_covering_map_on E TE B TB p
    \<and> top1_path_connected_on E TE
    \<and> top1_locally_path_connected_on E TE
    \<and> e0 \<in> E \<and> p e0 = b0
    \<and> top1_fundamental_group_image_hom E TE e0 B TB b0 p = H"
  sorry

section \<open>Chapter 14: Applications to Group Theory\<close>

section \<open>\<S>83 Covering Spaces of a Graph\<close>

text \<open>An arc is a space homeomorphic to the closed unit interval [0, 1].\<close>
definition top1_is_arc_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_arc_on X TX \<longleftrightarrow>
     is_topology_on_strict X TX \<and>
     (\<exists>h. top1_homeomorphism_on I_set I_top X TX h)"

text \<open>Endpoints of an arc A are the two (distinct) points p, q such that
  A - p and A - q are both connected.\<close>
definition top1_arc_endpoints_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a set" where
  "top1_arc_endpoints_on A TA =
     {p. p \<in> A \<and> top1_connected_on (A - {p}) (subspace_topology A TA (A - {p}))}"

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

(** from \<S>83 Theorem 83.2: any covering space of a graph is itself a graph. **)
theorem Theorem_83_2_covering_of_graph_is_graph:
  assumes "top1_is_graph_on B TB"
      and "top1_covering_map_on E TE B TB p"
  shows "top1_is_graph_on E TE"
  sorry

section \<open>\<S>84 The Fundamental Group of a Graph\<close>

text \<open>A tree is a connected graph with no nontrivial loops (simply connected).\<close>
definition top1_is_tree_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "top1_is_tree_on X TX \<longleftrightarrow>
     top1_is_graph_on X TX \<and>
     top1_connected_on X TX \<and>
     top1_simply_connected_on X TX"

(** from \<S>84 Theorem 84.7: the fundamental group of a connected graph is free.
    Specifically, \<pi>_1(X, x_0) is isomorphic to a free group on a set of generators
    (one per loop in a spanning-tree complement). **)
theorem Theorem_84_7_fund_group_graph_is_free:
  fixes X :: "'a set" and TX :: "'a set set" and x0 :: 'a
  assumes "top1_is_graph_on X TX"
      and "top1_connected_on X TX"
      and "x0 \<in> X"
  shows "\<exists>(G::'g set) mul e invg (\<iota>::'s \<Rightarrow> 'g) S.
           top1_is_free_group_full_on G mul e invg \<iota> S
         \<and> top1_groups_isomorphic_on G mul
             (top1_fundamental_group_carrier X TX x0)
             (top1_fundamental_group_mul X TX x0)"
  sorry

section \<open>\<S>85 Subgroups of Free Groups\<close>

(** from \<S>85 Theorem 85.1 (Nielsen-Schreier): subgroups of free groups are free.
    If G is free on S and H \<le> G is a subgroup, then H is free on some set S'. **)
theorem Theorem_85_1_Nielsen_Schreier:
  fixes G :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and \<iota> :: "'s \<Rightarrow> 'g" and S :: "'s set"
    and H :: "'g set"
  assumes "top1_is_free_group_full_on G mul e invg \<iota> S"
      and "top1_is_group_on H mul e invg"
      and "H \<subseteq> G"
  shows "\<exists>(\<iota>H::'t \<Rightarrow> 'g) SH.
           top1_is_free_group_full_on H mul e invg \<iota>H SH"
  sorry

(** from \<S>85 Theorem 85.3: Schreier index formula.
    If F is free on n+1 generators and H \<le> F has finite index k in F, then H
    is free on kn+1 generators. **)
theorem Theorem_85_3_Schreier_index:
  fixes F :: "'g set" and mul :: "'g \<Rightarrow> 'g \<Rightarrow> 'g"
    and e :: 'g and invg :: "'g \<Rightarrow> 'g"
    and \<iota>F :: "'s \<Rightarrow> 'g" and S :: "'s set"
    and H :: "'g set"
    and n k :: nat
  assumes "top1_is_free_group_full_on F mul e invg \<iota>F S"
      and "card S = n + 1"
      and "H \<subseteq> F"
      and "top1_is_group_on H mul e invg"
      and "top1_subgroup_has_index_on F mul H k"
  shows "\<exists>(\<iota>H::'t \<Rightarrow> 'g) SH.
           top1_is_free_group_full_on H mul e invg \<iota>H SH
         \<and> card SH = k * n + 1"
  sorry

end
