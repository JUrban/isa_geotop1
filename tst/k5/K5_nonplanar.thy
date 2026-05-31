theory K5_nonplanar
imports AlgIsoFixed.AlgIsoFixed
begin

lemma arc_endpoints_subset:
  "top1_arc_endpoints_on A TA \<subseteq> A"
  unfolding top1_arc_endpoints_on_def by blast

text \<open>K4 separation with e14 naming. Calls K4 lemma via [OF assms] (fast).\<close>
lemma K5_K4_sep:
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      "card {a1, a2, a3, a4 :: real \<times> real \<times> real} = 4"
      "{a1, a2, a3, a4} \<subseteq> top1_S2"
      "e12 \<subseteq> top1_S2" "e23 \<subseteq> top1_S2" "e34 \<subseteq> top1_S2"
      "e14 \<subseteq> top1_S2" "e13 \<subseteq> top1_S2" "e24 \<subseteq> top1_S2"
      "top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      "top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      "top1_is_arc_on e14 (subspace_topology top1_S2 top1_S2_topology e14)"
      "top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
      "top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
      "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1,a2}"
      "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2,a3}"
      "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3,a4}"
      "top1_arc_endpoints_on e14 (subspace_topology top1_S2 top1_S2_topology e14) = {a4,a1}"
      "top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1,a3}"
      "top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2,a4}"
      "e12 \<inter> e34 = {}" "e23 \<inter> e14 = {}"
      "e12 \<inter> e23 = {a2}" "e23 \<inter> e34 = {a3}"
      "e34 \<inter> e14 = {a4}" "e14 \<inter> e12 = {a1}"
      "e13 \<inter> e12 = {a1}" "e13 \<inter> e23 = {a3}"
      "e13 \<inter> e34 = {a3}" "e13 \<inter> e14 = {a1}"
      "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      "e24 \<inter> e12 = {a2}" "e24 \<inter> e23 = {a2}"
      "e24 \<inter> e34 = {a4}" "e24 \<inter> e14 = {a4}"
  shows "\<exists>U1 U2 U3 U4.
      U1 \<noteq> {} \<and> U2 \<noteq> {} \<and> U3 \<noteq> {} \<and> U4 \<noteq> {}
      \<and> U1 \<inter> U2 = {} \<and> U1 \<inter> U3 = {} \<and> U1 \<inter> U4 = {}
      \<and> U2 \<inter> U3 = {} \<and> U2 \<inter> U4 = {} \<and> U3 \<inter> U4 = {}
      \<and> U1 \<union> U2 \<union> U3 \<union> U4 = top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e14 \<union> e13 \<union> e24)
      \<and> top1_connected_on U1 (subspace_topology top1_S2 top1_S2_topology U1)
      \<and> top1_connected_on U2 (subspace_topology top1_S2 top1_S2_topology U2)
      \<and> top1_connected_on U3 (subspace_topology top1_S2 top1_S2_topology U3)
      \<and> top1_connected_on U4 (subspace_topology top1_S2 top1_S2_topology U4)"
  by (rule Lemma_64_3_K4_four_components[OF assms])

text \<open>Strengthened K4: same as Lemma\_64\_3 but adds boundary info
  (no component closure contains all 4 vertices).\<close>
lemma K4_four_components_with_boundary:
  fixes a1 a2 a3 a4 :: "real \<times> real \<times> real"
    and e12 e23 e34 e41 e13 e24 :: "(real \<times> real \<times> real) set"
  assumes "is_topology_on_strict top1_S2 top1_S2_topology"
      and "card {a1, a2, a3, a4} = 4"
      and "{a1, a2, a3, a4} \<subseteq> top1_S2"
      and "e12 \<subseteq> top1_S2" "e23 \<subseteq> top1_S2" "e34 \<subseteq> top1_S2"
      and "e41 \<subseteq> top1_S2" "e13 \<subseteq> top1_S2" "e24 \<subseteq> top1_S2"
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
      \<comment> \<open>K_4 planarity: arcs only intersect at shared vertices.\<close>
      and "e12 \<inter> e34 = {}" and "e23 \<inter> e41 = {}"
      and "e12 \<inter> e23 = {a2}" and "e23 \<inter> e34 = {a3}"
      and "e34 \<inter> e41 = {a4}" and "e41 \<inter> e12 = {a1}"
      and "e13 \<inter> e12 = {a1}" and "e13 \<inter> e23 = {a3}"
      and "e13 \<inter> e34 = {a3}" and "e13 \<inter> e41 = {a1}"
      and "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      and "e24 \<inter> e12 = {a2}" and "e24 \<inter> e23 = {a2}"
      and "e24 \<inter> e34 = {a4}" and "e24 \<inter> e41 = {a4}"
  shows "\<exists>U1 U2 U3 U4.
      U1 \<noteq> {} \<and> U2 \<noteq> {} \<and> U3 \<noteq> {} \<and> U4 \<noteq> {}
      \<and> U1 \<inter> U2 = {} \<and> U1 \<inter> U3 = {} \<and> U1 \<inter> U4 = {}
      \<and> U2 \<inter> U3 = {} \<and> U2 \<inter> U4 = {} \<and> U3 \<inter> U4 = {}
      \<and> U1 \<union> U2 \<union> U3 \<union> U4 = top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e41 \<union> e13 \<union> e24)
      \<and> top1_connected_on U1 (subspace_topology top1_S2 top1_S2_topology U1)
      \<and> top1_connected_on U2 (subspace_topology top1_S2 top1_S2_topology U2)
      \<and> top1_connected_on U3 (subspace_topology top1_S2 top1_S2_topology U3)
      \<and> top1_connected_on U4 (subspace_topology top1_S2 top1_S2_topology U4)
      \<and> U1 \<in> top1_S2_topology \<and> U2 \<in> top1_S2_topology
      \<and> U3 \<in> top1_S2_topology \<and> U4 \<in> top1_S2_topology
      \<comment> \<open>Munkres Lemma 64.3: exact boundary (closure) characterization.\<close>
      \<and> closure_on top1_S2 top1_S2_topology U1 = U1 \<union> (e12 \<union> e23 \<union> e13)
      \<and> closure_on top1_S2 top1_S2_topology U2 = U2 \<union> (e13 \<union> e41 \<union> e34)
      \<and> ((closure_on top1_S2 top1_S2_topology U3 = U3 \<union> (e12 \<union> e41 \<union> e24)
          \<and> closure_on top1_S2 top1_S2_topology U4 = U4 \<union> (e23 \<union> e34 \<union> e24))
        \<or> (closure_on top1_S2 top1_S2_topology U3 = U3 \<union> (e23 \<union> e34 \<union> e24)
          \<and> closure_on top1_S2 top1_S2_topology U4 = U4 \<union> (e12 \<union> e41 \<union> e24)))"
proof -
  \<comment> \<open>Extract vertex distinctness.\<close>
  have hdist: "a1 \<noteq> a2" "a1 \<noteq> a3" "a1 \<noteq> a4" "a2 \<noteq> a3" "a2 \<noteq> a4" "a3 \<noteq> a4"
  proof -
    from assms(2) have hc4: "card {a1, a2, a3, a4} = 4" .
    { assume h: "a1 = a2"
      have "{a1, a2, a3, a4} = {a1, a3, a4}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a1 \<noteq> a2" by (by100 blast)
    { assume h: "a1 = a3"
      have "{a1, a2, a3, a4} = {a1, a2, a4}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a1 \<noteq> a3" by (by100 blast)
    { assume h: "a1 = a4"
      have "{a1, a2, a3, a4} = {a1, a2, a3}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a1 \<noteq> a4" by (by100 blast)
    { assume h: "a2 = a3"
      have "{a1, a2, a3, a4} = {a1, a2, a4}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a2 \<noteq> a3" by (by100 blast)
    { assume h: "a2 = a4"
      have "{a1, a2, a3, a4} = {a1, a2, a3}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a2 \<noteq> a4" by (by100 blast)
    { assume h: "a3 = a4"
      have "{a1, a2, a3, a4} = {a1, a2, a3}" using h by (by100 blast)
      hence "card {a1, a2, a3, a4} \<le> 3" using card_three_le by (by100 simp)
      hence False using hc4 by (by100 simp) }
    thus "a3 \<noteq> a4" by (by100 blast)
  qed
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology"
    by (rule top1_S2_is_hausdorff)
  have hS2_strict: "is_topology_on_strict top1_S2 top1_S2_topology"
    by (rule assms(1))
  have hTopS2: "is_topology_on top1_S2 top1_S2_topology"
    using assms(1) unfolding is_topology_on_strict_def by (by100 blast)
  \<comment> \<open>Step 1: Form theta space. A = e12 \<union> e23, B = e13, C = e41 \<union> e34.\<close>
  let ?A = "e12 \<union> e23" and ?B = "e13" and ?C = "e41 \<union> e34"
  let ?Y = "?A \<union> ?B \<union> ?C"
  \<comment> \<open>A is an arc from a1 to a3 (via concatenation at a2).\<close>
  have ha2_ep12: "a2 \<in> top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
    using assms(16) by (by100 blast)
  have ha2_ep23: "a2 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
    using assms(17) by (by100 blast)
  have hA_arc: "top1_is_arc_on ?A (subspace_topology top1_S2 top1_S2_topology ?A)"
    by (rule arcs_concatenation_is_arc[OF hS2_strict hS2_haus assms(10) assms(4)
        assms(11) assms(5) assms(24) ha2_ep12 ha2_ep23])
  have hA_ep: "top1_arc_endpoints_on ?A (subspace_topology top1_S2 top1_S2_topology ?A) = {a1, a3}"
    by (rule arc_concat_endpoints[OF hS2_strict hS2_haus assms(10) assms(4)
        assms(11) assms(5) assms(24) ha2_ep12 ha2_ep23 assms(16) assms(17) hdist(1) hdist(4)])
  have hA_sub: "?A \<subseteq> top1_S2" using assms(4,5) by (by100 blast)
  \<comment> \<open>C is an arc from a1 to a3 (via concatenation at a4).\<close>
  have he41_e34_int: "e41 \<inter> e34 = {a4}" using assms(26) by (by100 blast)
  have ha4_ep41: "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
    using assms(19) by (by100 blast)
  have ha4_ep34: "a4 \<in> top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
    using assms(18) by (by100 blast)
  have hC_arc: "top1_is_arc_on ?C (subspace_topology top1_S2 top1_S2_topology ?C)"
    by (rule arcs_concatenation_is_arc[OF hS2_strict hS2_haus assms(13) assms(7)
        assms(12) assms(6) he41_e34_int ha4_ep41 ha4_ep34])
  have ha4_ne_a3: "a4 \<noteq> a3" using hdist(6) by (by100 blast)
  \<comment> \<open>Reorder endpoints for unification: {a4,a1} \<rightarrow> {a1,a4}, {a3,a4} \<rightarrow> {a4,a3}.\<close>
  have hep_e41: "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a1, a4}"
    using assms(19) by (by100 force)
  have hep_e34: "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a4, a3}"
    using assms(18) by (by100 force)
  have hC_ep: "top1_arc_endpoints_on ?C (subspace_topology top1_S2 top1_S2_topology ?C) = {a1, a3}"
    by (rule arc_concat_endpoints[OF hS2_strict hS2_haus assms(13) assms(7)
        assms(12) assms(6) he41_e34_int ha4_ep41 ha4_ep34 hep_e41 hep_e34 hdist(3) ha4_ne_a3])
  have hC_sub: "?C \<subseteq> top1_S2" using assms(6,7) by (by100 blast)
  \<comment> \<open>Intersection conditions for theta space.\<close>
  have hAB_int: "?A \<inter> ?B = {a1, a3}"
    using assms(28) assms(29) by (by100 blast)
  have hBC_int: "?B \<inter> ?C = {a1, a3}"
    using assms(31) assms(30) by (by100 blast)
  have hAC_int: "?A \<inter> ?C = {a1, a3}"
    using assms(27) assms(22) assms(23) assms(25) by (by100 blast)
  \<comment> \<open>Step 2: Apply Lemma 64.1 to get 3 components.\<close>
  obtain U V W where hUVW:
      "U \<noteq> {}" "V \<noteq> {}" "W \<noteq> {}"
      "U \<inter> V = {}" "V \<inter> W = {}" "U \<inter> W = {}"
      "U \<union> V \<union> W = top1_S2 - (?A \<union> ?B \<union> ?C)"
      "top1_connected_on U (subspace_topology top1_S2 top1_S2_topology U)"
      "top1_connected_on V (subspace_topology top1_S2 top1_S2_topology V)"
      "top1_connected_on W (subspace_topology top1_S2 top1_S2_topology W)"
      "U \<in> top1_S2_topology" "V \<in> top1_S2_topology" "W \<in> top1_S2_topology"
    using Lemma_64_1_theta_space_three_components[OF assms(1) hA_sub assms(8) hC_sub
        hA_arc assms(14) hC_arc hdist(2) hAB_int hBC_int hAC_int hA_ep assms(20) hC_ep]
    by (by100 metis)
  \<comment> \<open>Step 3: Identify which theta component contains e24-{a2,a4}.
     Use JCT on A\<union>B and B\<union>C to get 2-component decompositions, then boundary arguments.\<close>
  \<comment> \<open>A\<union>B is SCC.\<close>
  have hAB_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (?A \<union> ?B)"
    by (rule arcs_form_simple_closed_curve[OF hS2_strict hS2_haus hA_arc hA_sub
        assms(14) assms(8) hAB_int hdist(2) hA_ep assms(20)])
  \<comment> \<open>Apply Theorem_63_5 to A and B (as separate arcs) to get 2 components of S2-(A\<union>B).\<close>
  have hA_closed: "closedin_on top1_S2 top1_S2_topology ?A"
    by (rule arc_in_S2_closed[OF hA_sub hA_arc])
  have hB_closed: "closedin_on top1_S2 top1_S2_topology ?B"
    by (rule arc_in_S2_closed[OF assms(8) assms(14)])
  have hA_conn: "top1_connected_on ?A (subspace_topology top1_S2 top1_S2_topology ?A)"
    using arc_connected[OF hA_arc] .
  have hB_conn: "top1_connected_on ?B (subspace_topology top1_S2 top1_S2_topology ?B)"
    using arc_connected[OF assms(14)] .
  have hA_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?A"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) hA_sub hA_arc])
  have hB_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?B"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) assms(8) assms(14)])
  have hAB_card: "card (?A \<inter> ?B) = 2"
    using hAB_int hdist(2) by (by100 simp)
  \<comment> \<open>Get raw components, then choose labels so C-{a1,a3} \<subseteq> P2.\<close>
  have hCm_conn: "top1_connected_on (?C - {a1, a3})
      (subspace_topology top1_S2 top1_S2_topology (?C - {a1, a3}))"
    by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus hC_sub hC_arc hC_ep hdist(2)])
  have hCm_sub_AB: "?C - {a1, a3} \<subseteq> top1_S2 - (?A \<union> ?B)"
  proof -
    have "?C \<inter> (?A \<union> ?B) \<subseteq> {a1, a3}"
    proof -
      have "?C \<inter> ?A = {a1, a3}" using hAC_int by (by100 blast)
      moreover have "?C \<inter> ?B = {a1, a3}" using hBC_int by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    thus ?thesis using hC_sub by (by100 blast)
  qed
  have hCm_ne: "?C - {a1, a3} \<noteq> {}"
  proof -
    have "a4 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "a4 \<in> ?C" by (by100 blast)
    moreover have "a4 \<notin> {a1, a3}" using hdist(3) hdist(6) by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  obtain P1_raw P2_raw where hP_raw: "P1_raw \<noteq> {}" "P2_raw \<noteq> {}" "P1_raw \<inter> P2_raw = {}"
      "P1_raw \<union> P2_raw = top1_S2 - (?A \<union> ?B)"
      "top1_connected_on P1_raw (subspace_topology top1_S2 top1_S2_topology P1_raw)"
      "top1_connected_on P2_raw (subspace_topology top1_S2 top1_S2_topology P2_raw)"
    using Theorem_63_5_two_closed_connected[OF assms(1) hA_closed hB_closed
        hA_conn hB_conn hAB_card hA_no_sep hB_no_sep]
    by (by100 force)
  \<comment> \<open>P1\_raw, P2\_raw are open (via S2\_component helper + maximality from Jordan).\<close>
  have hAB_closed_loc: "closedin_on top1_S2 top1_S2_topology (?A \<union> ?B)"
    by (rule closedin_on_Un[OF hTopS2 hA_closed hB_closed])
  have hAB_compl_open_loc: "top1_S2 - (?A \<union> ?B) \<in> top1_S2_topology"
    using hAB_closed_loc unfolding closedin_on_def by (by100 blast)
  have hAB_not_conn: "\<not> top1_connected_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))"
    using Theorem_61_3_JordanSeparation_S2[OF assms(1) hAB_scc]
    unfolding top1_separates_on_def by (by100 blast)
  have hP1r_open: "P1_raw \<in> top1_S2_topology" and hP2r_open: "P2_raw \<in> top1_S2_topology"
    using S2_two_component_open[OF hAB_compl_open_loc _ hP_raw(1,2,3,4,5,6) hAB_not_conn]
    by (by100 blast)+
  \<comment> \<open>With P1\_raw, P2\_raw open, form separation and apply Lemma\_23\_2.\<close>
  have hCm_in_raw: "?C - {a1, a3} \<subseteq> P1_raw \<or> ?C - {a1, a3} \<subseteq> P2_raw"
  proof -
    have hTAB_loc: "is_topology_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))"
      by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
    have hP1r_oAB: "P1_raw \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
    proof -
      have "P1_raw = (top1_S2 - (?A \<union> ?B)) \<inter> P1_raw" using hP_raw(4) by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hP1r_open by (by100 blast)
    qed
    have hP2r_oAB: "P2_raw \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
    proof -
      have "P2_raw = (top1_S2 - (?A \<union> ?B)) \<inter> P2_raw" using hP_raw(4) by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hP2r_open by (by100 blast)
    qed
    have hAB_sep: "top1_is_separation_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P1_raw P2_raw"
      unfolding top1_is_separation_on_def
      using hP1r_oAB hP2r_oAB hP_raw(1,2,3,4) by (by100 blast)
    have hCm_sub: "?C - {a1, a3} \<subseteq> top1_S2 - (?A \<union> ?B)"
      using hCm_sub_AB .
    have hCm_conn_AB: "top1_connected_on (?C - {a1, a3})
        (subspace_topology (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
            (?C - {a1, a3}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology (?C - {a1, a3}) =
          subspace_topology (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
              (?C - {a1, a3})"
        using subspace_topology_trans[of "?C - {a1, a3}" "top1_S2 - (?A \<union> ?B)" top1_S2 top1_S2_topology]
            hCm_sub by (by100 simp)
      thus ?thesis using hCm_conn by (by100 simp)
    qed
    from Lemma_23_2[OF hTAB_loc hAB_sep hCm_sub hCm_conn_AB]
    show ?thesis by (by100 blast)
  qed
  obtain P1 P2 where hP: "P1 \<noteq> {}" "P2 \<noteq> {}" "P1 \<inter> P2 = {}"
      "P1 \<union> P2 = top1_S2 - (?A \<union> ?B)"
      "top1_connected_on P1 (subspace_topology top1_S2 top1_S2_topology P1)"
      "top1_connected_on P2 (subspace_topology top1_S2 top1_S2_topology P2)"
      and hCm_in_P2: "?C - {a1, a3} \<subseteq> P2"
  proof -
    from hCm_in_raw show ?thesis
    proof
      assume "?C - {a1, a3} \<subseteq> P1_raw"
      show ?thesis
        by (rule that[of P2_raw P1_raw])
          (use hP_raw \<open>?C - {a1, a3} \<subseteq> P1_raw\<close> in \<open>by100 blast\<close>)+
    next
      assume "?C - {a1, a3} \<subseteq> P2_raw"
      show ?thesis
        by (rule that[of P1_raw P2_raw])
          (use hP_raw \<open>?C - {a1, a3} \<subseteq> P2_raw\<close> in \<open>by100 blast\<close>)+
    qed
  qed
  \<comment> \<open>Both P1, P2 are open (components of open set S2-(A\<union>B)).\<close>
  have hAB_closed_S2: "closedin_on top1_S2 top1_S2_topology (?A \<union> ?B)"
    by (rule closedin_on_Un[OF hTopS2 hA_closed hB_closed])
  have hAB_compl_open: "top1_S2 - (?A \<union> ?B) \<in> top1_S2_topology"
    using hAB_closed_S2 unfolding closedin_on_def by (by100 blast)
  \<comment> \<open>Components P1, P2 are open: they are path components of the open set S2-(A\<union>B),
     which is lpc (S2 is lpc, open subsets of lpc are lpc).\<close>
  \<comment> \<open>Key: S2-(A\<union>B) is open lpc, so connected components are open.\<close>
  have hAB_open_lpc: "top1_locally_path_connected_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))"
    by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hAB_compl_open])
       (by100 blast)
  have hTAB: "is_topology_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))"
    by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
  obtain x_P where hx_P: "x_P \<in> P1" using hP(1) by (by100 blast)
  have hx_P_W: "x_P \<in> top1_S2 - (?A \<union> ?B)" using hx_P hP(4) by (by100 blast)
  \<comment> \<open>Establish P1 = path\_component(x\_P) at outer scope for reuse.\<close>
  have hP1_sub_AB: "P1 \<subseteq> top1_S2 - (?A \<union> ?B)" using hP(4) by (by100 blast)
  have hP1_conn_AB: "top1_connected_on P1
      (subspace_topology (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P1)"
  proof -
    have "subspace_topology top1_S2 top1_S2_topology P1 =
        subspace_topology (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P1"
      using subspace_topology_trans[of P1 "top1_S2 - (?A \<union> ?B)" top1_S2 top1_S2_topology]
          hP1_sub_AB by (by100 simp)
    thus ?thesis using hP(5) by (by100 simp)
  qed
  have hP1_eq_comp: "P1 = top1_component_of_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
  proof -
    have hP1_sub_comp: "P1 \<subseteq> top1_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
      by (rule top1_connected_subspace_subset_component_of[OF hP1_sub_AB hx_P hP1_conn_AB])
    have hcomp_sub_P1: "top1_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P \<subseteq> P1"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain y where hy: "y \<in> top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P" "y \<notin> P1"
        by (by100 blast)
      have "y \<in> top1_S2 - (?A \<union> ?B)"
        using hy(1) top1_component_of_on_subset[of "top1_S2 - (?A \<union> ?B)"] by (by100 blast)
      hence "y \<in> P2" using hP(4) hy(2) by (by100 blast)
      have hP2_sub: "P2 \<subseteq> top1_S2 - (?A \<union> ?B)" using hP(4) by (by100 blast)
      have hP2_conn_sub: "top1_connected_on P2
          (subspace_topology (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P2)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology P2 =
            subspace_topology (top1_S2 - (?A \<union> ?B))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) P2"
          using subspace_topology_trans[of P2 "top1_S2 - (?A \<union> ?B)" top1_S2 top1_S2_topology]
              hP2_sub by (by100 simp)
        thus ?thesis using hP(6) by (by100 simp)
      qed
      have "P2 \<subseteq> top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) y"
        by (rule top1_connected_subspace_subset_component_of[OF hP2_sub \<open>y \<in> P2\<close> hP2_conn_sub])
      moreover have "top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) y =
          top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
        by (rule top1_component_of_on_eq_of_mem[OF hTAB hy(1)])
      ultimately have "P1 \<union> P2 \<subseteq> top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
        using hP1_sub_comp by (by100 blast)
      moreover have "top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P \<subseteq>
          top1_S2 - (?A \<union> ?B)"
        by (rule top1_component_of_on_subset)
      ultimately have "top1_S2 - (?A \<union> ?B) = top1_component_of_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
        using hP(4) by (by100 blast)
      have hcomp_conn: "top1_connected_on
          (top1_component_of_on (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P)
          (subspace_topology (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
              (top1_component_of_on (top1_S2 - (?A \<union> ?B))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P))"
        by (rule top1_component_of_on_connected[OF hTAB hx_P_W])
      hence "top1_connected_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology (top1_S2 - (?A \<union> ?B))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
              (top1_S2 - (?A \<union> ?B)))"
        using \<open>top1_S2 - (?A \<union> ?B) = top1_component_of_on _ _ x_P\<close> by (by100 simp)
      moreover have "subspace_topology (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
          (top1_S2 - (?A \<union> ?B)) =
          subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
        using subspace_topology_trans[of "top1_S2 - (?A \<union> ?B)" "top1_S2 - (?A \<union> ?B)"
            top1_S2 top1_S2_topology] by (by100 simp)
      ultimately have "top1_connected_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))" by (by100 simp)
      moreover have "\<not> top1_connected_on (top1_S2 - (?A \<union> ?B))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))"
        using Theorem_61_3_JordanSeparation_S2[OF assms(1) hAB_scc]
        unfolding top1_separates_on_def by (by100 blast)
      ultimately show False by (by100 blast)
    qed
    from hP1_sub_comp hcomp_sub_P1 show ?thesis by (by100 blast)
  qed
  have hP1_eq_pc: "P1 = top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
  proof -
    from conjunct2[OF Theorem_25_5[OF hTAB]]
    have "\<forall>z \<in> top1_S2 - (?A \<union> ?B).
        top1_locally_path_connected_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) \<longrightarrow>
        top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) z =
        top1_component_of_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) z" by (by100 blast)
    hence "top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P =
        top1_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
      using hAB_open_lpc hx_P_W by (by100 metis)
    thus ?thesis using hP1_eq_comp by (by100 simp)
  qed
  \<comment> \<open>Helper: open-in-subspace-of-open implies open-in-S2.\<close>
  have open_in_sub_imp_open: "\<And>W P. W \<in> top1_S2_topology \<Longrightarrow>
      P \<in> subspace_topology top1_S2 top1_S2_topology W \<Longrightarrow> P \<in> top1_S2_topology"
  proof -
    fix W P assume hW: "W \<in> top1_S2_topology" and hP_sub: "P \<in> subspace_topology top1_S2 top1_S2_topology W"
    from hP_sub obtain V where hV: "V \<in> top1_S2_topology" "P = W \<inter> V"
      unfolding subspace_topology_def by (by100 blast)
    have "finite {W, V}" by (by100 simp)
    moreover have "{W, V} \<noteq> {}" by (by100 simp)
    moreover have "{W, V} \<subseteq> top1_S2_topology" using hW hV(1) by (by100 blast)
    ultimately have "\<Inter>{W, V} \<in> top1_S2_topology"
      using hTopS2 unfolding is_topology_on_def by (by100 blast)
    moreover have "\<Inter>{W, V} = W \<inter> V" by (by100 blast)
    ultimately show "P \<in> top1_S2_topology" using hV(2) by (by100 simp)
  qed
  have hP1_open: "P1 \<in> top1_S2_topology"
  proof -
    have "top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P \<in>
        subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
      by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTAB hAB_open_lpc hx_P_W])
    hence "P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
      using hP1_eq_pc by (by100 simp)
    thus ?thesis by (rule open_in_sub_imp_open[OF hAB_compl_open])
  qed
  \<comment> \<open>P2 = complement of P1 in S2-(A\<union>B). Since P1 is a path component and lpc, complement is open.\<close>
  have hP2_open: "P2 \<in> top1_S2_topology"
  proof -
    have hP2_eq: "P2 = (top1_S2 - (?A \<union> ?B)) -
        top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P"
      using hP(3,4) hP1_eq_pc by (by100 blast)
    have "(top1_S2 - (?A \<union> ?B)) -
        top1_path_component_of_on (top1_S2 - (?A \<union> ?B))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))) x_P \<in>
        subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
      by (rule top1_path_component_of_on_complement_open_if_locally_path_connected[OF hTAB hAB_open_lpc hx_P_W])
    hence "P2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B))"
      using hP2_eq by (by100 simp)
    thus ?thesis by (rule open_in_sub_imp_open[OF hAB_compl_open])
  qed
  \<comment> \<open>C-{a1,a3} \<subseteq> P2 was established in the obtain above.\<close>
  \<comment> \<open>closure(P1) = P1 \<union> (A\<union>B), using simple_closed_curve_boundary_meets_component.\<close>
  have hcl_P1: "closure_on top1_S2 top1_S2_topology P1 = P1 \<union> (?A \<union> ?B)"
  proof (rule set_eqI, rule iffI)
    fix z assume "z \<in> closure_on top1_S2 top1_S2_topology P1"
    \<comment> \<open>cl(P1) \<subseteq> P1 \<union> (A\<union>B): P2 open \<Rightarrow> S2-P2 closed \<Rightarrow> cl(P1) \<subseteq> S2-P2 = P1\<union>(A\<union>B).\<close>
    have hP1_AB_eq: "P1 \<union> (?A \<union> ?B) = top1_S2 - P2"
    proof -
      have hP1_sub_S2: "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      have "top1_S2 - P2 = (top1_S2 - (P1 \<union> P2)) \<union> P1" using hP(3) hP1_sub_S2 by (by100 force)
      also have "\<dots> = (?A \<union> ?B) \<union> P1"
      proof -
        have "top1_S2 - (P1 \<union> P2) = top1_S2 - (top1_S2 - (?A \<union> ?B))" using hP(4) by (by100 blast)
        also have "\<dots> = ?A \<union> ?B"
        proof -
          have "?A \<union> ?B \<subseteq> top1_S2" using hA_sub assms(8) by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        finally show ?thesis by (by100 simp)
      qed
      finally show ?thesis by (by100 blast)
    qed
    moreover have hcl_S2_P2: "closedin_on top1_S2 top1_S2_topology (top1_S2 - P2)"
    proof -
      have hP2_sub_S2: "P2 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      have hsub: "top1_S2 - P2 \<subseteq> top1_S2" by (by100 blast)
      have hcompl: "top1_S2 - (top1_S2 - P2) = P2" using hP2_sub_S2 by (by100 blast)
      show ?thesis unfolding closedin_on_def
        apply (rule conjI[OF hsub])
        using hcompl hP2_open by (by100 simp)
    qed
    moreover have "P1 \<subseteq> top1_S2 - P2"
    proof -
      have "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      thus ?thesis using hP(3) by (by100 blast)
    qed
    ultimately have "closure_on top1_S2 top1_S2_topology P1 \<subseteq> top1_S2 - P2"
      using closure_on_subset_of_closed[OF hcl_S2_P2] by (by100 blast)
    hence "closure_on top1_S2 top1_S2_topology P1 \<subseteq> P1 \<union> (?A \<union> ?B)"
      using hP1_AB_eq by (by100 blast)
    thus "z \<in> P1 \<union> (?A \<union> ?B)" using \<open>z \<in> closure_on top1_S2 top1_S2_topology P1\<close> by (by100 blast)
  next
    fix z assume "z \<in> P1 \<union> (?A \<union> ?B)"
    hence "z \<in> P1 \<or> z \<in> ?A \<union> ?B" by (by100 blast)
    thus "z \<in> closure_on top1_S2 top1_S2_topology P1"
    proof
      assume "z \<in> P1"
      thus ?thesis using subset_closure_on[of P1 top1_S2 top1_S2_topology] by (by100 blast)
    next
      assume "z \<in> ?A \<union> ?B"
      hence "z \<in> top1_S2" using hA_sub assms(8) by (by100 blast)
      have hP1_sub_S2: "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      show "z \<in> closure_on top1_S2 top1_S2_topology P1"
      proof (rule iffD2[OF Theorem_17_5a[OF hTopS2 \<open>z \<in> top1_S2\<close> hP1_sub_S2]])
        show "\<forall>U. neighborhood_of z top1_S2 top1_S2_topology U \<longrightarrow> intersects U P1"
        proof (intro allI impI)
          fix V assume hV: "neighborhood_of z top1_S2 top1_S2_topology V"
          hence hV_open: "V \<in> top1_S2_topology" and hzV: "z \<in> V"
            unfolding neighborhood_of_def by (by100 blast)+
          have "V \<inter> P1 \<noteq> {}"
            by (rule simple_closed_curve_boundary_meets_component[OF assms(1) hAB_scc hP(5) hP(6)
                hP(3) hP(4) hP(1) hP(2) hP1_open hP2_open \<open>z \<in> ?A \<union> ?B\<close> hV_open hzV])
          thus "intersects V P1" unfolding intersects_def by (by100 blast)
        qed
      qed
    qed
  qed
  \<comment> \<open>a4 \<notin> A\<union>B: from intersection assumptions and distinctness.\<close>
  have ha4_not_AB: "a4 \<notin> ?A \<union> ?B"
  proof -
    \<comment> \<open>a4 \<in> e34, e12\<inter>e34 = {}, so a4 \<notin> e12.\<close>
    have ha4_e34: "a4 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
    have "a4 \<notin> e12" using assms(22) ha4_e34 by (by100 blast)
    \<comment> \<open>a4 \<in> e23\<inter>e34 = {a3}, but a4 \<noteq> a3, so a4 \<notin> e23.\<close>
    moreover have "a4 \<notin> e23"
    proof assume "a4 \<in> e23"
      hence "a4 \<in> e23 \<inter> e34" using ha4_e34 by (by100 blast)
      hence "a4 = a3" using assms(25) by (by100 blast)
      thus False using hdist(6) by (by100 blast)
    qed
    \<comment> \<open>a4 \<in> e41, e13\<inter>e41 = {a1}, a4 \<noteq> a1, so a4 \<notin> e13.\<close>
    moreover have ha4_e41: "a4 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
    moreover have "a4 \<notin> e13"
    proof assume "a4 \<in> e13"
      hence "a4 \<in> e13 \<inter> e41" using ha4_e41 by (by100 blast)
      hence "a4 = a1" using assms(31) by (by100 blast)
      thus False using hdist(3) by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>e24-{a2,a4} cannot lie in P1: a4 \<in> closure(e24-{a2,a4}) but a4 \<notin> P1\<union>(A\<union>B).\<close>
  have ha4_in_cl_e24: "a4 \<in> closure_on top1_S2 top1_S2_topology (e24 - {a2, a4})"
    by (rule arc_endpoint_in_closure_of_interior(2)[OF hS2_strict hS2_haus assms(9) assms(15) assms(21) hdist(5)])
  have he24_not_P1: "\<not>(e24 - {a2, a4} \<subseteq> P1)"
  proof
    assume h: "e24 - {a2, a4} \<subseteq> P1"
    have "closure_on top1_S2 top1_S2_topology (e24 - {a2, a4}) \<subseteq>
        closure_on top1_S2 top1_S2_topology P1"
      by (rule closure_on_mono[OF h])
    hence "a4 \<in> closure_on top1_S2 top1_S2_topology P1"
      using ha4_in_cl_e24 by (by100 blast)
    hence "a4 \<in> P1 \<union> (?A \<union> ?B)" using hcl_P1 by (by100 blast)
    moreover have "a4 \<notin> P1"
    proof -
      have ha4_e41: "a4 \<in> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have "a4 \<in> ?C - {a1, a3}" using ha4_e41 hdist(3) hdist(6) by (by100 blast)
      hence "a4 \<in> P2" using hCm_in_P2 by (by100 blast)
      thus ?thesis using hP(3) by (by100 blast)
    qed
    ultimately have "a4 \<in> ?A \<union> ?B" by (by100 blast)
    thus False using ha4_not_AB by (by100 blast)
  qed
  \<comment> \<open>Similarly for B\<union>C: get R1, R2 from Theorem_63_5.\<close>
  have hBC_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (?B \<union> ?C)"
    by (rule arcs_form_simple_closed_curve[OF hS2_strict hS2_haus assms(14) assms(8)
        hC_arc hC_sub hBC_int hdist(2) assms(20) hC_ep])
  have hC_closed: "closedin_on top1_S2 top1_S2_topology ?C"
    by (rule arc_in_S2_closed[OF hC_sub hC_arc])
  have hC_conn: "top1_connected_on ?C (subspace_topology top1_S2 top1_S2_topology ?C)"
    using arc_connected[OF hC_arc] .
  have hC_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?C"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) hC_sub hC_arc])
  have hBC_card: "card (?B \<inter> ?C) = 2"
    using hBC_int hdist(2) by (by100 simp)
  \<comment> \<open>Get raw components for S2-(B\<union>C), then choose labels so A-{a1,a3} \<subseteq> R2.\<close>
  have hAm_sub_BC: "?A - {a1, a3} \<subseteq> top1_S2 - (?B \<union> ?C)"
  proof -
    have "?A \<inter> (?B \<union> ?C) \<subseteq> {a1, a3}" using hAB_int hAC_int by (by100 blast)
    thus ?thesis using hA_sub by (by100 blast)
  qed
  have hAm_in_raw_pre: "\<exists>R1' R2'. R1' \<noteq> {} \<and> R2' \<noteq> {} \<and> R1' \<inter> R2' = {}
      \<and> R1' \<union> R2' = top1_S2 - (?B \<union> ?C)
      \<and> top1_connected_on R1' (subspace_topology top1_S2 top1_S2_topology R1')
      \<and> top1_connected_on R2' (subspace_topology top1_S2 top1_S2_topology R2')"
    using Theorem_63_5_two_closed_connected[OF assms(1) hB_closed hC_closed
        hB_conn hC_conn hBC_card hB_no_sep hC_no_sep] by (by100 metis)
  obtain R1 R2 where hR: "R1 \<noteq> {}" "R2 \<noteq> {}" "R1 \<inter> R2 = {}"
      "R1 \<union> R2 = top1_S2 - (?B \<union> ?C)"
      "top1_connected_on R1 (subspace_topology top1_S2 top1_S2_topology R1)"
      "top1_connected_on R2 (subspace_topology top1_S2 top1_S2_topology R2)"
      and hAm_in_R2: "?A - {a1, a3} \<subseteq> R2"
  proof -
    from hAm_in_raw_pre obtain R1' R2' where hR': "R1' \<noteq> {}" "R2' \<noteq> {}" "R1' \<inter> R2' = {}"
        "R1' \<union> R2' = top1_S2 - (?B \<union> ?C)"
        "top1_connected_on R1' (subspace_topology top1_S2 top1_S2_topology R1')"
        "top1_connected_on R2' (subspace_topology top1_S2 top1_S2_topology R2')" by (by100 metis)
    have hBC_closed_loc: "closedin_on top1_S2 top1_S2_topology (?B \<union> ?C)"
      by (rule closedin_on_Un[OF hTopS2 hB_closed hC_closed])
    have hBC_compl_open_loc: "top1_S2 - (?B \<union> ?C) \<in> top1_S2_topology"
      using hBC_closed_loc unfolding closedin_on_def by (by100 blast)
    have hBC_not_conn: "\<not> top1_connected_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
      using Theorem_61_3_JordanSeparation_S2[OF assms(1) hBC_scc]
      unfolding top1_separates_on_def by (by100 blast)
    have hR1'_open: "R1' \<in> top1_S2_topology" and hR2'_open: "R2' \<in> top1_S2_topology"
      using S2_two_component_open[OF hBC_compl_open_loc _ hR'(1,2,3,4,5,6) hBC_not_conn]
      by (by100 blast)+
    have hTBC_loc: "is_topology_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
      by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
    have hR1'_oBC: "R1' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
    proof -
      have "R1' = (top1_S2 - (?B \<union> ?C)) \<inter> R1'" using hR'(4) by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hR1'_open by (by100 blast)
    qed
    have hR2'_oBC: "R2' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
    proof -
      have "R2' = (top1_S2 - (?B \<union> ?C)) \<inter> R2'" using hR'(4) by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hR2'_open by (by100 blast)
    qed
    have hBC_sep: "top1_is_separation_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R1' R2'"
      unfolding top1_is_separation_on_def
      using hR1'_oBC hR2'_oBC hR'(1,2,3,4) by (by100 blast)
    have hAm_conn_BC: "top1_connected_on (?A - {a1, a3})
        (subspace_topology (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))
            (?A - {a1, a3}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology (?A - {a1, a3}) =
          subspace_topology (top1_S2 - (?B \<union> ?C))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))
              (?A - {a1, a3})"
        using subspace_topology_trans[of "?A - {a1, a3}" "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
            hAm_sub_BC by (by100 simp)
      thus ?thesis using arc_minus_endpoints_connected[OF hS2_strict hS2_haus hA_sub hA_arc hA_ep hdist(2)]
        by (by100 simp)
    qed
    have hAm_raw: "?A - {a1, a3} \<subseteq> R1' \<or> ?A - {a1, a3} \<subseteq> R2'"
      using Lemma_23_2[OF hTBC_loc hBC_sep hAm_sub_BC hAm_conn_BC] by (by100 blast)
    from hAm_raw show ?thesis
    proof
      assume "?A - {a1, a3} \<subseteq> R1'"
      show ?thesis
        by (rule that[of R2' R1'])
          (use hR' \<open>?A - {a1, a3} \<subseteq> R1'\<close> in \<open>by100 blast\<close>)+
    next
      assume "?A - {a1, a3} \<subseteq> R2'"
      show ?thesis
        by (rule that[of R1' R2'])
          (use hR' \<open>?A - {a1, a3} \<subseteq> R2'\<close> in \<open>by100 blast\<close>)+
    qed
  qed
  have hBC_closed_S2: "closedin_on top1_S2 top1_S2_topology (?B \<union> ?C)"
    by (rule closedin_on_Un[OF hTopS2 hB_closed hC_closed])
  have hBC_compl_open: "top1_S2 - (?B \<union> ?C) \<in> top1_S2_topology"
    using hBC_closed_S2 unfolding closedin_on_def by (by100 blast)
  have hBC_open_lpc: "top1_locally_path_connected_on (top1_S2 - (?B \<union> ?C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
    by (rule open_subset_locally_path_connected[OF S2_locally_path_connected hBC_compl_open])
       (by100 blast)
  have hTBC: "is_topology_on (top1_S2 - (?B \<union> ?C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
    by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
  obtain x_R where hx_R: "x_R \<in> R1" using hR(1) by (by100 blast)
  have hx_R_W: "x_R \<in> top1_S2 - (?B \<union> ?C)" using hx_R hR(4) by (by100 blast)
  \<comment> \<open>R1 = component\_of(x\_R) in S2-(B\<union>C). Same contradiction argument as for P1.\<close>
  have hR1_eq_comp: "R1 = top1_component_of_on (top1_S2 - (?B \<union> ?C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
  proof -
    have hR1_sub_BC: "R1 \<subseteq> top1_S2 - (?B \<union> ?C)" using hR(4) by (by100 blast)
    have hR1_conn_BC: "top1_connected_on R1
        (subspace_topology (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R1)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology R1 =
          subspace_topology (top1_S2 - (?B \<union> ?C))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R1"
        using subspace_topology_trans[of R1 "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
            hR1_sub_BC by (by100 simp)
      thus ?thesis using hR(5) by (by100 simp)
    qed
    have "R1 \<subseteq> top1_component_of_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
      by (rule top1_connected_subspace_subset_component_of[OF hR1_sub_BC hx_R hR1_conn_BC])
    moreover have "top1_component_of_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R \<subseteq> R1"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain y where hy: "y \<in> top1_component_of_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R" "y \<notin> R1"
        by (by100 blast)
      have "y \<in> top1_S2 - (?B \<union> ?C)"
        using hy(1) top1_component_of_on_subset[of "top1_S2 - (?B \<union> ?C)"] by (by100 blast)
      hence "y \<in> R2" using hR(4) hy(2) by (by100 blast)
      have hR2_sub: "R2 \<subseteq> top1_S2 - (?B \<union> ?C)" using hR(4) by (by100 blast)
      have hR2_conn_sub: "top1_connected_on R2
          (subspace_topology (top1_S2 - (?B \<union> ?C))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R2)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology R2 =
            subspace_topology (top1_S2 - (?B \<union> ?C))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) R2"
          using subspace_topology_trans[of R2 "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
              hR2_sub by (by100 simp)
        thus ?thesis using hR(6) by (by100 simp)
      qed
      have "R2 \<subseteq> top1_component_of_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
        using top1_connected_subspace_subset_component_of[OF hR2_sub \<open>y \<in> R2\<close> hR2_conn_sub]
            top1_component_of_on_eq_of_mem[OF hTBC hy(1)] by (by100 simp)
      hence "R1 \<union> R2 \<subseteq> top1_component_of_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
        using \<open>R1 \<subseteq> top1_component_of_on _ _ x_R\<close> by (by100 blast)
      hence "top1_S2 - (?B \<union> ?C) = top1_component_of_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
        using hR(4) top1_component_of_on_subset[of "top1_S2 - (?B \<union> ?C)"] by (by100 blast)
      hence "top1_connected_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
      proof -
        have "top1_connected_on
            (top1_component_of_on (top1_S2 - (?B \<union> ?C))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R)
            (subspace_topology (top1_S2 - (?B \<union> ?C))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))
                (top1_component_of_on (top1_S2 - (?B \<union> ?C))
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R))"
          by (rule top1_component_of_on_connected[OF hTBC hx_R_W])
        thus ?thesis
          using \<open>top1_S2 - (?B \<union> ?C) = top1_component_of_on _ _ x_R\<close>
              subspace_topology_trans[of "top1_S2 - (?B \<union> ?C)" "top1_S2 - (?B \<union> ?C)"
                  top1_S2 top1_S2_topology] by (by100 simp)
      qed
      moreover have "\<not> top1_connected_on (top1_S2 - (?B \<union> ?C))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C)))"
        using Theorem_61_3_JordanSeparation_S2[OF assms(1) hBC_scc]
        unfolding top1_separates_on_def by (by100 blast)
      ultimately show False by (by100 blast)
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  have hR1_eq_pc: "R1 = top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
  proof -
    from conjunct2[OF Theorem_25_5[OF hTBC]]
    have "\<forall>z \<in> top1_S2 - (?B \<union> ?C).
        top1_locally_path_connected_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) \<longrightarrow>
        top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) z =
        top1_component_of_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) z" by (by100 blast)
    thus ?thesis using hR1_eq_comp hBC_open_lpc hx_R_W by (by100 metis)
  qed
  have hR1_open: "R1 \<in> top1_S2_topology"
  proof -
    have "top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R \<in>
        subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
      by (rule top1_path_component_of_on_open_if_locally_path_connected[OF hTBC hBC_open_lpc hx_R_W])
    hence "R1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
      using hR1_eq_pc by (by100 simp)
    thus ?thesis by (rule open_in_sub_imp_open[OF hBC_compl_open])
  qed
  have hR2_open: "R2 \<in> top1_S2_topology"
  proof -
    have "R2 = (top1_S2 - (?B \<union> ?C)) -
        top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R"
      using hR(3,4) hR1_eq_pc by (by100 blast)
    moreover have "(top1_S2 - (?B \<union> ?C)) -
        top1_path_component_of_on (top1_S2 - (?B \<union> ?C))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) x_R \<in>
        subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
      by (rule top1_path_component_of_on_complement_open_if_locally_path_connected[OF hTBC hBC_open_lpc hx_R_W])
    ultimately have "R2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))"
      by (by100 simp)
    thus ?thesis by (rule open_in_sub_imp_open[OF hBC_compl_open])
  qed
  \<comment> \<open>hAm\_in\_R2 was established in the obtain above.\<close>
  have hcl_R1: "closure_on top1_S2 top1_S2_topology R1 = R1 \<union> (?B \<union> ?C)"
  proof (rule set_eqI, rule iffI)
    fix z assume "z \<in> closure_on top1_S2 top1_S2_topology R1"
    have hR1_BC_eq: "R1 \<union> (?B \<union> ?C) = top1_S2 - R2"
    proof -
      have hR1_sub_S2: "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      have "top1_S2 - R2 = (top1_S2 - (R1 \<union> R2)) \<union> R1" using hR(3) hR1_sub_S2 by (by100 force)
      also have "\<dots> = (?B \<union> ?C) \<union> R1"
      proof -
        have "top1_S2 - (R1 \<union> R2) = top1_S2 - (top1_S2 - (?B \<union> ?C))" using hR(4) by (by100 blast)
        also have "\<dots> = ?B \<union> ?C"
        proof -
          have "?B \<union> ?C \<subseteq> top1_S2" using assms(8) hC_sub by (by100 blast)
          thus ?thesis by (by100 blast)
        qed
        finally show ?thesis by (by100 simp)
      qed
      finally show ?thesis by (by100 blast)
    qed
    have hcl_S2_R2: "closedin_on top1_S2 top1_S2_topology (top1_S2 - R2)"
    proof -
      have hR2_sub_S2: "R2 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      have hsub: "top1_S2 - R2 \<subseteq> top1_S2" by (by100 blast)
      have hcompl: "top1_S2 - (top1_S2 - R2) = R2" using hR2_sub_S2 by (by100 blast)
      show ?thesis unfolding closedin_on_def
        apply (rule conjI[OF hsub])
        using hcompl hR2_open by (by100 simp)
    qed
    have "R1 \<subseteq> top1_S2 - R2"
    proof -
      have "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      thus ?thesis using hR(3) by (by100 blast)
    qed
    hence "closure_on top1_S2 top1_S2_topology R1 \<subseteq> top1_S2 - R2"
      using closure_on_subset_of_closed[OF hcl_S2_R2] by (by100 blast)
    hence "closure_on top1_S2 top1_S2_topology R1 \<subseteq> R1 \<union> (?B \<union> ?C)"
      using hR1_BC_eq by (by100 blast)
    thus "z \<in> R1 \<union> (?B \<union> ?C)" using \<open>z \<in> closure_on top1_S2 top1_S2_topology R1\<close> by (by100 blast)
  next
    fix z assume "z \<in> R1 \<union> (?B \<union> ?C)"
    hence "z \<in> R1 \<or> z \<in> ?B \<union> ?C" by (by100 blast)
    thus "z \<in> closure_on top1_S2 top1_S2_topology R1"
    proof
      assume "z \<in> R1"
      thus ?thesis using subset_closure_on[of R1 top1_S2 top1_S2_topology] by (by100 blast)
    next
      assume "z \<in> ?B \<union> ?C"
      hence "z \<in> top1_S2" using assms(8) hC_sub by (by100 blast)
      have hR1_sub_S2: "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      show "z \<in> closure_on top1_S2 top1_S2_topology R1"
      proof (rule iffD2[OF Theorem_17_5a[OF hTopS2 \<open>z \<in> top1_S2\<close> hR1_sub_S2]])
        show "\<forall>U. neighborhood_of z top1_S2 top1_S2_topology U \<longrightarrow> intersects U R1"
        proof (intro allI impI)
          fix V assume hV: "neighborhood_of z top1_S2 top1_S2_topology V"
          hence hV_open: "V \<in> top1_S2_topology" and hzV: "z \<in> V"
            unfolding neighborhood_of_def by (by100 blast)+
          have "V \<inter> R1 \<noteq> {}"
            by (rule simple_closed_curve_boundary_meets_component[OF assms(1) hBC_scc hR(5) hR(6)
                hR(3) hR(4) hR(1) hR(2) hR1_open hR2_open \<open>z \<in> ?B \<union> ?C\<close> hV_open hzV])
          thus "intersects V R1" unfolding intersects_def by (by100 blast)
        qed
      qed
    qed
  qed
  \<comment> \<open>a2 \<notin> B\<union>C.\<close>
  have ha2_not_BC: "a2 \<notin> ?B \<union> ?C"
  proof -
    have ha2_e12: "a2 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    \<comment> \<open>a2 \<in> e12, e13\<inter>e12 = {a1}, a2 \<noteq> a1, so a2 \<notin> e13.\<close>
    have "a2 \<notin> e13"
    proof assume "a2 \<in> e13"
      hence "a2 \<in> e13 \<inter> e12" using ha2_e12 by (by100 blast)
      hence "a2 = a1" using assms(28) by (by100 blast)
      thus False using hdist(1) by (by100 blast)
    qed
    moreover have "a2 \<notin> e41"
    proof assume "a2 \<in> e41"
      hence "a2 \<in> e41 \<inter> e12" using ha2_e12 by (by100 blast)
      hence "a2 = a1" using assms(27) by (by100 blast)
      thus False using hdist(1) by (by100 blast)
    qed
    \<comment> \<open>a2 \<in> e12, e12\<inter>e34 = {}, so a2 \<notin> e34.\<close>
    moreover have "a2 \<notin> e34" using assms(22) ha2_e12 by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  have ha2_in_cl_e24: "a2 \<in> closure_on top1_S2 top1_S2_topology (e24 - {a2, a4})"
    by (rule arc_endpoint_in_closure_of_interior(1)[OF hS2_strict hS2_haus assms(9) assms(15) assms(21) hdist(5)])
  have he24_not_R1: "\<not>(e24 - {a2, a4} \<subseteq> R1)"
  proof
    assume h: "e24 - {a2, a4} \<subseteq> R1"
    have "closure_on top1_S2 top1_S2_topology (e24 - {a2, a4}) \<subseteq>
        closure_on top1_S2 top1_S2_topology R1"
      by (rule closure_on_mono[OF h])
    hence "a2 \<in> closure_on top1_S2 top1_S2_topology R1"
      using ha2_in_cl_e24 by (by100 blast)
    hence "a2 \<in> R1 \<union> (?B \<union> ?C)" using hcl_R1 by (by100 blast)
    moreover have "a2 \<notin> R1"
    proof -
      have ha2_e12: "a2 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have "a2 \<in> ?A - {a1, a3}" using ha2_e12 hdist(1) hdist(4) by (by100 blast)
      hence "a2 \<in> R2" using hAm_in_R2 by (by100 blast)
      thus ?thesis using hR(3) by (by100 blast)
    qed
    ultimately have "a2 \<in> ?B \<union> ?C" by (by100 blast)
    thus False using ha2_not_BC by (by100 blast)
  qed
  \<comment> \<open>Step 4: P1 and R1 are each theta components, and they are distinct.\<close>
  \<comment> \<open>P1 \<subseteq> S2-(A\<union>B) and P1 \<inter> (C-{a1,a3}) = {} (since C-{a1,a3} \<subseteq> P2), so P1 \<subseteq> S2-Y.\<close>
  have hP1_sub_Y_compl: "P1 \<subseteq> top1_S2 - ?Y"
  proof -
    have "P1 \<subseteq> top1_S2 - (?A \<union> ?B)" using hP(4) by (by100 blast)
    moreover have "P1 \<inter> (?C - {a1, a3}) = {}" using hCm_in_P2 hP(3) by (by100 blast)
    moreover have "{a1, a3} \<subseteq> ?A \<union> ?B" using hAB_int by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  have hR1_sub_Y_compl: "R1 \<subseteq> top1_S2 - ?Y"
  proof -
    have "R1 \<subseteq> top1_S2 - (?B \<union> ?C)" using hR(4) by (by100 blast)
    moreover have "R1 \<inter> (?A - {a1, a3}) = {}" using hAm_in_R2 hR(3) by (by100 blast)
    moreover have "{a1, a3} \<subseteq> ?B \<union> ?C" using hBC_int by (by100 blast)
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>P1 is connected \<subseteq> S2-Y = U\<union>V\<union>W (disjoint open), so P1 \<subseteq> one of U,V,W.\<close>
  \<comment> \<open>Since P1 is a component of S2-(A\<union>B) \<supseteq> S2-Y, and U,V,W are components of S2-Y,
     P1 is exactly one of U,V,W. Similarly R1.\<close>
  \<comment> \<open>U, V, W are open in S2: Y is closed, S2-Y is open lpc, components are open.\<close>
  have hY_closed: "closedin_on top1_S2 top1_S2_topology ?Y"
  proof -
    have hAC_closed: "closedin_on top1_S2 top1_S2_topology (?A \<union> ?C)"
      by (rule closedin_on_Un[OF hTopS2 hA_closed hC_closed])
    have hABC_closed: "closedin_on top1_S2 top1_S2_topology ((?A \<union> ?C) \<union> ?B)"
      by (rule closedin_on_Un[OF hTopS2 hAC_closed hB_closed])
    moreover have "?Y = (?A \<union> ?C) \<union> ?B" by (by100 blast)
    ultimately show ?thesis by (by100 simp)
  qed
  have hY_compl_open: "top1_S2 - ?Y \<in> top1_S2_topology"
    using hY_closed unfolding closedin_on_def by (by100 blast)
  \<comment> \<open>NEW APPROACH: P1 is a connected component of S2-Y, hence equals one of U,V,W.
     Key: S2-Y = P1 \<union> (P2 \<inter> (S2-Y)) where both pieces are open in S2-Y.\<close>
  have hP2_cap_Y: "P2 \<inter> (top1_S2 - ?Y) = (top1_S2 - ?Y) - P1"
    using hP1_sub_Y_compl hP(3,4) hUVW(7) by (by100 blast)
  have hP1_open_in_Y: "P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
  proof -
    have "P1 = (top1_S2 - ?Y) \<inter> P1" using hP1_sub_Y_compl by (by100 blast)
    thus ?thesis unfolding subspace_topology_def using hP1_open by (by100 blast)
  qed
  have hVW_open_in_Y: "(top1_S2 - ?Y) - P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
  proof -
    have "(top1_S2 - ?Y) - P1 = (top1_S2 - ?Y) \<inter> P2"
      using hP1_sub_Y_compl hP(3,4) hUVW(7) by (by100 blast)
    also have "\<dots> = (top1_S2 - ?Y) \<inter> (top1_S2 \<inter> P2)" using hP(4) by (by100 blast)
    finally show ?thesis unfolding subspace_topology_def using hP2_open by (by100 blast)
  qed
  \<comment> \<open>P1 is a connected component of S2-Y (maximal connected: any connected superset
     in S2-Y would cross the P1/(P2\<inter>S2-Y) separation).\<close>
  have hP1_is_comp: "P1 = U \<or> P1 = V \<or> P1 = W"
  proof -
    \<comment> \<open>P1 connected \<subseteq> U\<union>V\<union>W. By partition, P1 \<subseteq> U or V or W.\<close>
    \<comment> \<open>Conversely, if P1 \<subseteq> U and U \<noteq> P1, then \<exists>z \<in> U-P1. z \<in> P2\<inter>(S2-Y).
       But U is connected and meets both P1 and P2\<inter>(S2-Y), which are open in S2-Y.
       That contradicts U's connectivity.\<close>
    have hP1_in_UVW: "P1 \<subseteq> U \<union> V \<union> W" using hP1_sub_Y_compl hUVW(7) by (by100 blast)
    \<comment> \<open>P1 is connected, P1 \<subseteq> S2-Y which is separated as P1 \<union> (S2-Y-P1).
       Any connected subset of S2-Y is in P1 or in S2-Y-P1.\<close>
    have hTY: "is_topology_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))"
      by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
    have hVW_ne: "(top1_S2 - ?Y) - P1 \<noteq> {}"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence hP1_eq_Y: "top1_S2 - ?Y \<subseteq> P1" by (by100 blast)
      \<comment> \<open>P1 connected \<subseteq> U\<union>V\<union>W (disjoint open). Lemma\_23\_2 on {U, V\<union>W}: P1 \<subseteq> U or V\<union>W.\<close>
      have hVW_open_loc: "V \<union> W \<in> top1_S2_topology"
      proof -
        from hTopS2 have "\<And>S. S \<subseteq> top1_S2_topology \<Longrightarrow> \<Union>S \<in> top1_S2_topology"
          unfolding is_topology_on_def by (by100 blast)
        from this[of "{V, W}"] hUVW(12,13) have "\<Union>{V, W} \<in> top1_S2_topology" by (by100 blast)
        moreover have "\<Union>{V, W} = V \<union> W" by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      have hU_oY: "U \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
      proof -
        have "U \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
        hence "U = (top1_S2 - ?Y) \<inter> U" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hUVW(11) by (by100 blast)
      qed
      have hVW_oY: "V \<union> W \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
      proof -
        have "V \<union> W \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
        hence "V \<union> W = (top1_S2 - ?Y) \<inter> (V \<union> W)" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hVW_open_loc by (by100 blast)
      qed
      have hU_VW_sep: "top1_is_separation_on (top1_S2 - ?Y)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U (V \<union> W)"
      proof -
        have "U \<inter> (V \<union> W) = {}" using hUVW(4,6) by (by100 blast)
        moreover have "U \<union> (V \<union> W) = top1_S2 - ?Y" using hUVW(7) by (by100 blast)
        moreover have "V \<union> W \<noteq> {}" using hUVW(2) by (by100 blast)
        ultimately show ?thesis unfolding top1_is_separation_on_def
          using hU_oY hVW_oY hUVW(1) by (by100 blast)
      qed
      have hP1_conn_Y: "top1_connected_on P1
          (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology P1 =
            subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1"
          using subspace_topology_trans[of P1 "top1_S2 - ?Y" top1_S2 top1_S2_topology]
              hP1_sub_Y_compl by (by100 simp)
        thus ?thesis using hP(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hTY hU_VW_sep hP1_sub_Y_compl hP1_conn_Y]
      have "P1 \<subseteq> U \<or> P1 \<subseteq> V \<union> W" by (by100 blast)
      thus False
      proof
        assume "P1 \<subseteq> U"
        hence "V \<subseteq> P1" using hP1_eq_Y hUVW(7) by (by100 blast)
        hence "V \<subseteq> U" using \<open>P1 \<subseteq> U\<close> by (by100 blast)
        hence "V \<inter> U \<noteq> {}" using hUVW(2) by (by100 blast)
        thus False using hUVW(4) by (by100 blast)
      next
        assume "P1 \<subseteq> V \<union> W"
        hence "U \<subseteq> P1" using hP1_eq_Y hUVW(7) by (by100 blast)
        hence "U \<subseteq> V \<union> W" using \<open>P1 \<subseteq> V \<union> W\<close> by (by100 blast)
        hence "U \<inter> (V \<union> W) \<noteq> {}" using hUVW(1) by (by100 blast)
        moreover have "U \<inter> (V \<union> W) = {}" using hUVW(4,6) by (by100 blast)
        ultimately show False by (by100 blast)
      qed
    qed
    have hY_sep: "top1_is_separation_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))
        P1 ((top1_S2 - ?Y) - P1)"
      unfolding top1_is_separation_on_def
      using hP1_open_in_Y hVW_open_in_Y hP(1) hVW_ne hP1_sub_Y_compl by (by100 blast)
    \<comment> \<open>Each of U, V, W is connected \<subseteq> S2-Y. By Lemma\_23\_2, each \<subseteq> P1 or \<subseteq> (S2-Y)-P1.\<close>
    \<comment> \<open>Each of U,V,W connected \<subseteq> S2-Y. By Lemma\_23\_2, each \<subseteq> P1 or (S2-Y)-P1.\<close>
    have hU_conn_Y: "top1_connected_on U
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U)"
    proof -
      have "U \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "subspace_topology top1_S2 top1_S2_topology U =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U"
        using subspace_topology_trans[of U "top1_S2 - ?Y" top1_S2 top1_S2_topology] by (by100 simp)
      thus ?thesis using hUVW(8) by (by100 simp)
    qed
    have hU_sub_Y: "U \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
    have hU_side: "U \<subseteq> P1 \<or> U \<subseteq> (top1_S2 - ?Y) - P1"
      using Lemma_23_2[OF hTY hY_sep hU_sub_Y hU_conn_Y] by (by100 blast)
    have hV_conn_Y: "top1_connected_on V
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) V)"
    proof -
      have "V \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "subspace_topology top1_S2 top1_S2_topology V =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) V"
        using subspace_topology_trans[of V "top1_S2 - ?Y" top1_S2 top1_S2_topology] by (by100 simp)
      thus ?thesis using hUVW(9) by (by100 simp)
    qed
    have hV_sub_Y: "V \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
    have hV_side: "V \<subseteq> P1 \<or> V \<subseteq> (top1_S2 - ?Y) - P1"
      using Lemma_23_2[OF hTY hY_sep hV_sub_Y hV_conn_Y] by (by100 blast)
    have hW_conn_Y: "top1_connected_on W
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) W)"
    proof -
      have "W \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "subspace_topology top1_S2 top1_S2_topology W =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) W"
        using subspace_topology_trans[of W "top1_S2 - ?Y" top1_S2 top1_S2_topology] by (by100 simp)
      thus ?thesis using hUVW(10) by (by100 simp)
    qed
    have hW_sub_Y: "W \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
    have hW_side: "W \<subseteq> P1 \<or> W \<subseteq> (top1_S2 - ?Y) - P1"
      using Lemma_23_2[OF hTY hY_sep hW_sub_Y hW_conn_Y] by (by100 blast)
    \<comment> \<open>P1 = component\_of\_{S2-Y}(x\_P): use containment in P1's component of S2-(A\<union>B).\<close>
    have hP1_comp_Y: "P1 = top1_component_of_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
    proof -
      have hP1_sub_Y: "P1 \<subseteq> top1_S2 - ?Y" by (rule hP1_sub_Y_compl)
      have hP1_conn_Y: "top1_connected_on P1
          (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology P1 =
            subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1"
          using subspace_topology_trans[of P1 "top1_S2 - ?Y" top1_S2 top1_S2_topology] hP1_sub_Y
          by (by100 simp)
        thus ?thesis using hP(5) by (by100 simp)
      qed
      have "P1 \<subseteq> top1_component_of_on (top1_S2 - ?Y)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
        by (rule top1_connected_subspace_subset_component_of[OF hP1_sub_Y hx_P hP1_conn_Y])
      moreover have "top1_component_of_on (top1_S2 - ?Y)
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P \<subseteq> P1"
      proof -
        \<comment> \<open>comp\_{S2-Y}(x\_P) \<subseteq> comp\_{S2-(A\<union>B)}(x\_P) = P1.\<close>
        have "top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P \<subseteq>
            top1_S2 - ?Y" by (rule top1_component_of_on_subset)
        moreover have "top1_connected_on (top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)
            (subspace_topology top1_S2 top1_S2_topology (top1_component_of_on (top1_S2 - ?Y)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P))"
        proof -
          have hconn_sub: "top1_connected_on (top1_component_of_on (top1_S2 - ?Y)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)
              (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))
                  (top1_component_of_on (top1_S2 - ?Y)
                      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P))"
            by (rule top1_component_of_on_connected[OF hTY])
               (use hx_P hP1_sub_Y in \<open>by100 blast\<close>)
          thus ?thesis
            using subspace_topology_trans[of "top1_component_of_on (top1_S2 - ?Y)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
                "top1_S2 - ?Y" top1_S2 top1_S2_topology]
                top1_component_of_on_subset[of "top1_S2 - ?Y"] by (by100 simp)
        qed
        moreover have "x_P \<in> top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
          by (rule top1_component_of_on_self_mem[OF hTY]) (use hx_P hP1_sub_Y in \<open>by100 blast\<close>)
        moreover have "top1_S2 - ?Y \<subseteq> top1_S2 - (?A \<union> ?B)" by (by100 blast)
        ultimately have hsub_AB: "top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P \<subseteq> top1_S2 - (?A \<union> ?B)"
          and hconn_AB: "top1_connected_on (top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)
            (subspace_topology top1_S2 top1_S2_topology (top1_component_of_on (top1_S2 - ?Y)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P))"
          and hxP_in_comp: "x_P \<in> top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
          by (by100 blast)+
        have hconn_AB': "top1_connected_on (top1_component_of_on (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)
            (subspace_topology (top1_S2 - (?A \<union> ?B))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
                (top1_component_of_on (top1_S2 - ?Y)
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P))"
        proof -
          have "subspace_topology top1_S2 top1_S2_topology (top1_component_of_on (top1_S2 - ?Y)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P) =
              subspace_topology (top1_S2 - (?A \<union> ?B))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?A \<union> ?B)))
                  (top1_component_of_on (top1_S2 - ?Y)
                      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P)"
            using subspace_topology_trans[of "top1_component_of_on (top1_S2 - ?Y)
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) x_P"
                "top1_S2 - (?A \<union> ?B)" top1_S2 top1_S2_topology] hsub_AB by (by100 simp)
          thus ?thesis using hconn_AB by (by100 simp)
        qed
        show ?thesis
          using top1_connected_subspace_subset_component_of[OF hsub_AB hxP_in_comp hconn_AB']
              hP1_eq_comp by (by100 simp)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    \<comment> \<open>U,V,W open (hUVW(11,12,13)) + disjoint + P1 connected \<subseteq> U\<union>V\<union>W \<Rightarrow> P1 \<subseteq> one.
       Then that one \<subseteq> P1 (from hU/V/W\_side). So P1 = that one.\<close>
    \<comment> \<open>P1 connected \<subseteq> U\<union>V\<union>W with U,V,W pairwise disjoint and open in S2.
       By connectivity, P1 must be \<subseteq> one of them. Then that one \<subseteq> P1 from side facts.\<close>
    \<comment> \<open>P1 connected \<subseteq> U\<union>V\<union>W (disjoint open). By Lemma\_23\_2 applied twice.\<close>
    \<comment> \<open>Form separation {U, V\<union>W} of S2-Y.\<close>
    have hU_open_Y: "U \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "U = (top1_S2 - ?Y) \<inter> U" using hU_sub_Y by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hUVW(11) by (by100 blast)
    qed
    have hVW_open_Y: "V \<union> W \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "V \<union> W = (top1_S2 - ?Y) \<inter> (V \<union> W)" using hV_sub_Y hW_sub_Y by (by100 blast)
      moreover have "V \<union> W \<in> top1_S2_topology"
      proof -
        from hTopS2 have hunion: "\<And>U. U \<subseteq> top1_S2_topology \<Longrightarrow> \<Union>U \<in> top1_S2_topology"
          unfolding is_topology_on_def by (by100 blast)
        have "{V, W} \<subseteq> top1_S2_topology" using hUVW(12,13) by (by100 blast)
        from hunion[OF this] have "\<Union>{V, W} \<in> top1_S2_topology" .
        moreover have "\<Union>{V, W} = V \<union> W" by (by100 blast)
        ultimately show ?thesis by (by100 simp)
      qed
      ultimately show ?thesis unfolding subspace_topology_def by (by100 blast)
    qed
    have hUVW_sep: "top1_is_separation_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U (V \<union> W)"
    proof -
      have "U \<inter> (V \<union> W) = {}" using hUVW(4,6) by (by100 blast)
      moreover have "U \<union> (V \<union> W) = top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      moreover have "V \<union> W \<noteq> {}" using hUVW(2) by (by100 blast)
      ultimately show ?thesis unfolding top1_is_separation_on_def
        using hU_open_Y hVW_open_Y hUVW(1) by (by100 blast)
    qed
    \<comment> \<open>P1 connected in S2-Y, Lemma\_23\_2 gives P1 \<subseteq> U or P1 \<subseteq> V\<union>W.\<close>
    have hP1_conn_Y_full: "top1_connected_on P1
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology P1 =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1"
        using subspace_topology_trans[of P1 "top1_S2 - ?Y" top1_S2 top1_S2_topology]
            hP1_sub_Y_compl by (by100 simp)
      thus ?thesis using hP(5) by (by100 simp)
    qed
    from Lemma_23_2[OF hTY hUVW_sep hP1_sub_Y_compl hP1_conn_Y_full]
    have "P1 \<subseteq> U \<or> P1 \<subseteq> V \<union> W" by (by100 blast)
    thus ?thesis
    proof
      assume hPU: "P1 \<subseteq> U"
      \<comment> \<open>U \<subseteq> P1: from hU\_side, x\_P \<in> U (since P1 \<subseteq> U and x\_P \<in> P1).\<close>
      have "x_P \<in> U" using hPU hx_P by (by100 blast)
      hence "U \<inter> P1 \<noteq> {}" using hx_P by (by100 blast)
      hence "U \<subseteq> P1" using hU_side by (by100 force)
      thus ?thesis using hPU by (by100 blast)
    next
      assume "P1 \<subseteq> V \<union> W"
      \<comment> \<open>Apply Lemma\_23\_2 again: separation {V, W} of V\<union>W.\<close>
      have hV_open_VW: "V \<in> subspace_topology top1_S2 top1_S2_topology (V \<union> W)"
      proof -
        have "V = (V \<union> W) \<inter> V" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hUVW(12) by (by100 blast)
      qed
      have hW_open_VW: "W \<in> subspace_topology top1_S2 top1_S2_topology (V \<union> W)"
      proof -
        have "W = (V \<union> W) \<inter> W" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hUVW(13) by (by100 blast)
      qed
      have hTVW: "is_topology_on (V \<union> W)
          (subspace_topology top1_S2 top1_S2_topology (V \<union> W))"
        by (rule subspace_topology_is_topology_on[OF hTopS2])
           (use hV_sub_Y hW_sub_Y in \<open>by100 blast\<close>)
      have hVW_sep: "top1_is_separation_on (V \<union> W)
          (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) V W"
        unfolding top1_is_separation_on_def
        using hV_open_VW hW_open_VW hUVW(2,3,5) by (by100 blast)
      have hP1_sub_VW: "P1 \<subseteq> V \<union> W" by (rule \<open>P1 \<subseteq> V \<union> W\<close>)
      have hP1_conn_VW: "top1_connected_on P1
          (subspace_topology (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) P1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology P1 =
            subspace_topology (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) P1"
          using subspace_topology_trans[of P1 "V \<union> W" top1_S2 top1_S2_topology]
              hP1_sub_VW by (by100 simp)
        thus ?thesis using hP(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hTVW hVW_sep hP1_sub_VW hP1_conn_VW]
      have "P1 \<subseteq> V \<or> P1 \<subseteq> W" by (by100 blast)
      thus ?thesis
      proof
        assume hPV: "P1 \<subseteq> V"
        have "x_P \<in> V" using hPV hx_P by (by100 blast)
        hence "V \<inter> P1 \<noteq> {}" using hx_P by (by100 blast)
        hence "V \<subseteq> P1" using hV_side by (by100 force)
        thus ?thesis using hPV by (by100 blast)
      next
        assume hPW: "P1 \<subseteq> W"
        have "x_P \<in> W" using hPW hx_P by (by100 blast)
        hence "W \<inter> P1 \<noteq> {}" using hx_P by (by100 blast)
        hence "W \<subseteq> P1" using hW_side by (by100 force)
        thus ?thesis using hPW by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>Same argument for R1.\<close>
  have hR1_is_comp: "R1 = U \<or> R1 = V \<or> R1 = W"
  proof -
    have hR1_in_UVW: "R1 \<subseteq> U \<union> V \<union> W" using hR1_sub_Y_compl hUVW(7) by (by100 blast)
    \<comment> \<open>Same 2\<times>Lemma\_23\_2 approach. Re-derive shared infrastructure.\<close>
    have hTYr: "is_topology_on (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))"
      by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
    have hVW_open_r: "V \<union> W \<in> top1_S2_topology"
    proof -
      from hTopS2 have "\<And>S. S \<subseteq> top1_S2_topology \<Longrightarrow> \<Union>S \<in> top1_S2_topology"
        unfolding is_topology_on_def by (by100 blast)
      from this[of "{V, W}"] hUVW(12,13) have "\<Union>{V, W} \<in> top1_S2_topology" by (by100 blast)
      moreover have "\<Union>{V, W} = V \<union> W" by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hU_oY: "U \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "U \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "U = (top1_S2 - ?Y) \<inter> U" by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hUVW(11) by (by100 blast)
    qed
    have hVW_oY: "V \<union> W \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "V \<union> W \<subseteq> top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      hence "V \<union> W = (top1_S2 - ?Y) \<inter> (V \<union> W)" by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hVW_open_r by (by100 blast)
    qed
    have hUVW_sr: "top1_is_separation_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) U (V \<union> W)"
    proof -
      have "U \<inter> (V \<union> W) = {}" using hUVW(4,6) by (by100 blast)
      moreover have "U \<union> (V \<union> W) = top1_S2 - ?Y" using hUVW(7) by (by100 blast)
      moreover have "V \<union> W \<noteq> {}" using hUVW(2) by (by100 blast)
      ultimately show ?thesis unfolding top1_is_separation_on_def
        using hU_oY hVW_oY hUVW(1) by (by100 blast)
    qed
    have hR1_cY: "top1_connected_on R1
        (subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) R1)"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology R1 =
          subspace_topology (top1_S2 - ?Y) (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) R1"
        using subspace_topology_trans[of R1 "top1_S2 - ?Y" top1_S2 top1_S2_topology]
            hR1_sub_Y_compl by (by100 simp)
      thus ?thesis using hR(5) by (by100 simp)
    qed
    from Lemma_23_2[OF hTYr hUVW_sr hR1_sub_Y_compl hR1_cY]
    have "R1 \<subseteq> U \<or> R1 \<subseteq> V \<union> W" by (by100 blast)
    thus ?thesis
    proof
      assume hRU: "R1 \<subseteq> U"
      have "U \<subseteq> R1"
      proof -
        have "x_R \<in> U" using hRU hx_R by (by100 blast)
        have hU_sub_BC: "U \<subseteq> top1_S2 - (?B \<union> ?C)"
          using hR1_sub_Y_compl hUVW(7) by (by100 blast)
        have hU_conn_BC: "top1_connected_on U
            (subspace_topology (top1_S2 - (?B \<union> ?C))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) U)"
        proof -
          have "subspace_topology top1_S2 top1_S2_topology U =
              subspace_topology (top1_S2 - (?B \<union> ?C))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) U"
            using subspace_topology_trans[of U "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
                hU_sub_BC by (by100 simp)
          thus ?thesis using hUVW(8) by (by100 simp)
        qed
        from top1_connected_subspace_subset_component_of[OF hU_sub_BC \<open>x_R \<in> U\<close> hU_conn_BC]
        show ?thesis using hR1_eq_comp by (by100 simp)
      qed
      thus ?thesis using hRU by (by100 blast)
    next
      assume "R1 \<subseteq> V \<union> W"
      have hTVWr: "is_topology_on (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W))"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (use hUVW(7) in \<open>by100 blast\<close>)
      have hVW_sr: "top1_is_separation_on (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) V W"
      proof -
        have "V = (V \<union> W) \<inter> V" by (by100 blast)
        hence hVo: "V \<in> subspace_topology top1_S2 top1_S2_topology (V \<union> W)"
          unfolding subspace_topology_def using hUVW(12) by (by100 blast)
        have "W = (V \<union> W) \<inter> W" by (by100 blast)
        hence hWo: "W \<in> subspace_topology top1_S2 top1_S2_topology (V \<union> W)"
          unfolding subspace_topology_def using hUVW(13) by (by100 blast)
        show ?thesis unfolding top1_is_separation_on_def
          using hVo hWo hUVW(2,3,5) by (by100 blast)
      qed
      have hR1_cVW: "top1_connected_on R1
          (subspace_topology (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) R1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology R1 =
            subspace_topology (V \<union> W) (subspace_topology top1_S2 top1_S2_topology (V \<union> W)) R1"
          using subspace_topology_trans[of R1 "V \<union> W" top1_S2 top1_S2_topology]
              \<open>R1 \<subseteq> V \<union> W\<close> by (by100 simp)
        thus ?thesis using hR(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hTVWr hVW_sr \<open>R1 \<subseteq> V \<union> W\<close> hR1_cVW]
      have "R1 \<subseteq> V \<or> R1 \<subseteq> W" by (by100 blast)
      thus ?thesis
      proof
        assume "R1 \<subseteq> V"
        have "V \<subseteq> R1"
        proof -
          have "x_R \<in> V" using \<open>R1 \<subseteq> V\<close> hx_R by (by100 blast)
          have hV_sub_BC: "V \<subseteq> top1_S2 - (?B \<union> ?C)"
            using hR1_sub_Y_compl hUVW(7) by (by100 blast)
          have hV_conn_BC: "top1_connected_on V
              (subspace_topology (top1_S2 - (?B \<union> ?C))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) V)"
          proof -
            have "subspace_topology top1_S2 top1_S2_topology V =
                subspace_topology (top1_S2 - (?B \<union> ?C))
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) V"
              using subspace_topology_trans[of V "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
                  hV_sub_BC by (by100 simp)
            thus ?thesis using hUVW(9) by (by100 simp)
          qed
          from top1_connected_subspace_subset_component_of[OF hV_sub_BC \<open>x_R \<in> V\<close> hV_conn_BC]
          show ?thesis using hR1_eq_comp by (by100 simp)
        qed
        thus ?thesis using \<open>R1 \<subseteq> V\<close> by (by100 blast)
      next
        assume "R1 \<subseteq> W"
        have "W \<subseteq> R1"
        proof -
          have "x_R \<in> W" using \<open>R1 \<subseteq> W\<close> hx_R by (by100 blast)
          have hW_sub_BC: "W \<subseteq> top1_S2 - (?B \<union> ?C)"
            using hR1_sub_Y_compl hUVW(7) by (by100 blast)
          have hW_conn_BC: "top1_connected_on W
              (subspace_topology (top1_S2 - (?B \<union> ?C))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) W)"
          proof -
            have "subspace_topology top1_S2 top1_S2_topology W =
                subspace_topology (top1_S2 - (?B \<union> ?C))
                    (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?B \<union> ?C))) W"
              using subspace_topology_trans[of W "top1_S2 - (?B \<union> ?C)" top1_S2 top1_S2_topology]
                  hW_sub_BC by (by100 simp)
            thus ?thesis using hUVW(10) by (by100 simp)
          qed
          from top1_connected_subspace_subset_component_of[OF hW_sub_BC \<open>x_R \<in> W\<close> hW_conn_BC]
          show ?thesis using hR1_eq_comp by (by100 simp)
        qed
        thus ?thesis using \<open>R1 \<subseteq> W\<close> by (by100 blast)
      qed
    qed
  qed
  \<comment> \<open>P1 \<noteq> R1: closure(P1) = P1\<union>(A\<union>B), closure(R1) = R1\<union>(B\<union>C).
     If P1 = R1 then closure(P1) \<subseteq> (A\<union>B) \<inter> (B\<union>C) gives boundary \<subseteq> B, contradicting
     that an open nonempty subset of S2 has boundary larger than an arc.\<close>
  have hP1_ne_R1: "P1 \<noteq> R1"
  proof
    assume "P1 = R1"
    \<comment> \<open>closure(P1) = P1\<union>(A\<union>B), closure(R1) = R1\<union>(B\<union>C). If equal:
       P1\<union>(A\<union>B) = P1\<union>(B\<union>C), so (A\<union>B) \<subseteq> P1\<union>(B\<union>C) and (B\<union>C) \<subseteq> P1\<union>(A\<union>B).
       Hence A-B \<subseteq> P1\<union>C and C-B \<subseteq> P1\<union>A. But P1 \<subseteq> S2-Y, A,C \<subseteq> Y, P1 \<inter> Y = {}.
       So A-B \<subseteq> C and C-B \<subseteq> A. Combined with A\<inter>C = {a1,a3} and B endpoints = {a1,a3}:
       A-{a1,a3} \<subseteq> C, but A \<inter> C = {a1,a3}, so A-{a1,a3} \<subseteq> C \<inter> A = {a1,a3}.
       Hence A \<subseteq> {a1,a3} \<union> B. But A is an arc with \<ge> 3 points. Contradiction.\<close>
    have "closure_on top1_S2 top1_S2_topology P1 = closure_on top1_S2 top1_S2_topology R1"
      using \<open>P1 = R1\<close> by (by100 simp)
    hence "P1 \<union> (?A \<union> ?B) = P1 \<union> (?B \<union> ?C)" using hcl_P1 hcl_R1 \<open>P1 = R1\<close> by (by100 simp)
    hence "?A \<subseteq> P1 \<union> ?B \<union> ?C" by (by100 blast)
    moreover have "P1 \<inter> ?A = {}" using hP1_sub_Y_compl by (by100 blast)
    ultimately have hA_sub_BC: "?A \<subseteq> ?B \<union> ?C" by (by100 blast)
    \<comment> \<open>But A \<inter> (B\<union>C) = (A\<inter>B) \<union> (A\<inter>C) = {a1,a3} \<union> {a1,a3} = {a1,a3}.\<close>
    have "?A \<inter> (?B \<union> ?C) \<subseteq> {a1, a3}" using hAB_int hAC_int by (by100 blast)
    hence "?A \<subseteq> {a1, a3}" using hA_sub_BC by (by100 blast)
    \<comment> \<open>But A = e12 \<union> e23 has \<ge> 3 points (it's an arc).\<close>
    moreover have "a2 \<in> ?A" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
    moreover have "a2 \<notin> {a1, a3}" using hdist(1,4) by (by100 blast)
    ultimately show False by (by100 blast)
  qed
  \<comment> \<open>e24-{a2,a4} lies in the third component (not P1, not R1).\<close>
  have he24_conn: "top1_connected_on (e24 - {a2, a4})
      (subspace_topology top1_S2 top1_S2_topology (e24 - {a2, a4}))"
    by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus assms(9) assms(15) assms(21) hdist(5)])
  \<comment> \<open>e24 \<inter> Y = {a2, a4}: from intersection assumptions.\<close>
  have he24_Y_int: "e24 \<inter> ?Y = {a2, a4}"
  proof -
    \<comment> \<open>e24 \<inter> (e12\<union>e23\<union>e13\<union>e41\<union>e34)
       = (e24\<inter>e12) \<union> (e24\<inter>e23) \<union> (e24\<inter>e13) \<union> (e24\<inter>e41) \<union> (e24\<inter>e34)\<close>
    have "e24 \<inter> e13 = {}"
    proof -
      have ha2_e12: "a2 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have ha1_e12: "a1 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have ha1_not_e24: "a1 \<notin> e24"
      proof assume "a1 \<in> e24"
        hence "a1 \<in> e24 \<inter> e12" using ha1_e12 by (by100 blast)
        hence "a1 = a2" using assms(33) by (by100 blast)
        thus False using hdist(1) by (by100 blast)
      qed
      have ha3_e23: "a3 \<in> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
      have ha3_not_e24: "a3 \<notin> e24"
      proof assume "a3 \<in> e24"
        hence "a3 \<in> e24 \<inter> e23" using ha3_e23 by (by100 blast)
        hence "a3 = a2" using assms(34) by (by100 blast)
        thus False using hdist(4) by (by100 blast)
      qed
      \<comment> \<open>a2 \<notin> e13: from ha2_not_BC. a4 \<notin> e13: from ha4_not_AB.\<close>
      have "a2 \<notin> e13" using ha2_not_BC by (by100 blast)
      moreover have "a4 \<notin> e13" using ha4_not_AB by (by100 blast)
      ultimately have "\<forall>x \<in> {a1,a2,a3,a4}. x \<notin> e24 \<inter> e13"
        using ha1_not_e24 ha3_not_e24 by (by100 blast)
      thus ?thesis using assms(32) by (by100 blast)
    qed
    hence he24_e13: "e24 \<inter> e13 = {}" .
    have "e24 \<inter> ?Y = (e24 \<inter> e12) \<union> (e24 \<inter> e23) \<union> (e24 \<inter> e13) \<union> (e24 \<inter> e41) \<union> (e24 \<inter> e34)"
      by (by100 blast)
    also have "\<dots> = {a2} \<union> {a2} \<union> {} \<union> {a4} \<union> {a4}"
      using assms(33,34,35,36) he24_e13 by (by100 simp)
    also have "\<dots> = {a2, a4}" by (by100 blast)
    finally show ?thesis .
  qed
  have ha2_in_Y: "a2 \<in> ?Y"
    using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have ha4_in_Y: "a4 \<in> ?Y"
    using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have he24_in_Y_compl: "e24 - {a2, a4} \<subseteq> top1_S2 - ?Y"
    using he24_Y_int assms(9) by (by100 blast)
  \<comment> \<open>Let T be the theta component \<noteq> P1, \<noteq> R1.\<close>
  obtain T where hT_is: "T \<in> {U, V, W}" "T \<noteq> P1" "T \<noteq> R1"
      and hT_conn: "top1_connected_on T (subspace_topology top1_S2 top1_S2_topology T)"
      and hT_ne: "T \<noteq> {}"
      and hT_union: "P1 \<union> R1 \<union> T = top1_S2 - ?Y"
      and hT_disj: "P1 \<inter> T = {}" "R1 \<inter> T = {}"
  proof -
    \<comment> \<open>Define T as (S2-Y) - P1 - R1. Show it has all required properties.\<close>
    define T0 where "T0 = (top1_S2 - ?Y) - P1 - R1"
    have hT0_in: "T0 \<in> {U, V, W}"
    proof -
      have hUVW_union: "top1_S2 - ?Y = U \<union> V \<union> W" using hUVW(7) by (by100 blast)
      have hT0_alt: "T0 = (U \<union> V \<union> W) - P1 - R1" unfolding T0_def using hUVW_union by (by100 blast)
      \<comment> \<open>Case split: P1=U,V,W and R1=U,V,W; the remainder is T0.\<close>
      from hP1_is_comp show ?thesis
      proof (elim disjE)
        assume "P1 = U" from hR1_is_comp show ?thesis
        proof (elim disjE)
          assume "R1 = U" thus ?thesis using \<open>P1 = U\<close> hP1_ne_R1 by (by100 blast)
        next assume "R1 = V"
          have "T0 = W" using hT0_alt \<open>P1 = U\<close> \<open>R1 = V\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        next assume "R1 = W"
          have "T0 = V" using hT0_alt \<open>P1 = U\<close> \<open>R1 = W\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        qed
      next
        assume "P1 = V" from hR1_is_comp show ?thesis
        proof (elim disjE)
          assume "R1 = U"
          have "T0 = W" using hT0_alt \<open>P1 = V\<close> \<open>R1 = U\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        next assume "R1 = V" thus ?thesis using \<open>P1 = V\<close> hP1_ne_R1 by (by100 blast)
        next assume "R1 = W"
          have "T0 = U" using hT0_alt \<open>P1 = V\<close> \<open>R1 = W\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        qed
      next
        assume "P1 = W" from hR1_is_comp show ?thesis
        proof (elim disjE)
          assume "R1 = U"
          have "T0 = V" using hT0_alt \<open>P1 = W\<close> \<open>R1 = U\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        next assume "R1 = V"
          have "T0 = U" using hT0_alt \<open>P1 = W\<close> \<open>R1 = V\<close> hUVW(4,5,6) by (by100 force)
          thus ?thesis by (by100 blast)
        next assume "R1 = W" thus ?thesis using \<open>P1 = W\<close> hP1_ne_R1 by (by100 blast)
        qed
      qed
    qed
    have hT0_ne_P1: "T0 \<noteq> P1"
    proof -
      have "P1 \<inter> T0 = {}" using T0_def by (by100 blast)
      thus ?thesis using hP(1) by (by100 blast)
    qed
    have hT0_ne_R1: "T0 \<noteq> R1"
    proof -
      have "R1 \<inter> T0 = {}" using T0_def by (by100 blast)
      thus ?thesis using hR(1) by (by100 blast)
    qed
    have "top1_connected_on T0 (subspace_topology top1_S2 top1_S2_topology T0)"
      using hT0_in hUVW(8,9,10) by (by100 blast)
    moreover have "T0 \<noteq> {}" using hT0_in hUVW(1,2,3) by (by100 blast)
    moreover have "P1 \<union> R1 \<union> T0 = top1_S2 - ?Y"
    proof -
      have hT0e: "T0 = (top1_S2 - ?Y) - P1 - R1" by (rule T0_def)
      show ?thesis
      proof (rule set_eqI, rule iffI)
        fix x assume "x \<in> P1 \<union> R1 \<union> T0"
        hence "x \<in> P1 \<or> x \<in> R1 \<or> x \<in> T0" by (by100 blast)
        thus "x \<in> top1_S2 - ?Y"
        proof (elim disjE)
          assume "x \<in> P1" thus ?thesis using hP1_sub_Y_compl by (by100 blast)
        next assume "x \<in> R1" thus ?thesis using hR1_sub_Y_compl by (by100 blast)
        next assume "x \<in> T0" thus ?thesis using hT0e by (by100 blast)
        qed
      next
        fix x assume "x \<in> top1_S2 - ?Y"
        thus "x \<in> P1 \<union> R1 \<union> T0" using hT0e by (by100 blast)
      qed
    qed
    moreover have "P1 \<inter> T0 = {}" using T0_def by (by100 blast)
    moreover have "R1 \<inter> T0 = {}" using T0_def by (by100 blast)
    ultimately show ?thesis by (rule that[OF hT0_in hT0_ne_P1 hT0_ne_R1])
  qed
  have hP1R1_disj: "P1 \<inter> R1 = {}"
  proof -
    from hP1_is_comp show ?thesis
    proof (elim disjE)
      assume "P1 = U" from hR1_is_comp show ?thesis
      proof (elim disjE)
        assume "R1 = U" thus ?thesis using hP1_ne_R1 \<open>P1 = U\<close> by (by100 blast)
      next assume "R1 = V" thus ?thesis using \<open>P1 = U\<close> hUVW(4) by (by100 blast)
      next assume "R1 = W" thus ?thesis using \<open>P1 = U\<close> hUVW(6) by (by100 blast)
      qed
    next
      assume "P1 = V" from hR1_is_comp show ?thesis
      proof (elim disjE)
        assume "R1 = U" thus ?thesis using \<open>P1 = V\<close> hUVW(4) by (by100 blast)
      next assume "R1 = V" thus ?thesis using hP1_ne_R1 \<open>P1 = V\<close> by (by100 blast)
      next assume "R1 = W" thus ?thesis using \<open>P1 = V\<close> hUVW(5) by (by100 blast)
      qed
    next
      assume "P1 = W" from hR1_is_comp show ?thesis
      proof (elim disjE)
        assume "R1 = U" thus ?thesis using \<open>P1 = W\<close> hUVW(6) by (by100 blast)
      next assume "R1 = V" thus ?thesis using \<open>P1 = W\<close> hUVW(5) by (by100 blast)
      next assume "R1 = W" thus ?thesis using hP1_ne_R1 \<open>P1 = W\<close> by (by100 blast)
      qed
    qed
  qed
  have he24_in_T: "e24 - {a2, a4} \<subseteq> T"
  proof -
    \<comment> \<open>e24-{a2,a4} connected \<subseteq> P1\<union>R1\<union>T (disjoint open). By Lemma\_23\_2 approach: in one.\<close>
    have "e24 - {a2, a4} \<subseteq> P1 \<union> R1 \<union> T" using he24_in_Y_compl hT_union by (by100 blast)
    \<comment> \<open>Not \<subseteq> P1 (he24\_not\_P1). Not \<subseteq> R1 (he24\_not\_R1). Hence \<subseteq> T.\<close>
    \<comment> \<open>P1, R1, T are pairwise disjoint open. Connected e24-{a2,a4} must be in one.\<close>
    have hT_open: "T \<in> top1_S2_topology" using hT_is(1) hUVW(11,12,13) by (by100 blast)
    \<comment> \<open>e24-{a2,a4} \<subseteq> P1 or \<subseteq> R1\<union>T (separation {P1, R1\<union>T}).\<close>
    \<comment> \<open>Form separation {P1, R1\<union>T} of S2-Y = P1\<union>R1\<union>T.\<close>
    have hRT_open: "R1 \<union> T \<in> top1_S2_topology"
    proof -
      from hTopS2 have "\<And>S. S \<subseteq> top1_S2_topology \<Longrightarrow> \<Union>S \<in> top1_S2_topology"
        unfolding is_topology_on_def by (by100 blast)
      from this[of "{R1, T}"] hR1_open hT_open have "\<Union>{R1, T} \<in> top1_S2_topology" by (by100 blast)
      moreover have "\<Union>{R1, T} = R1 \<union> T" by (by100 blast)
      ultimately show ?thesis by (by100 simp)
    qed
    have hTY_loc: "is_topology_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y))"
      by (rule subspace_topology_is_topology_on[OF]) (use hTopS2 in \<open>by100 blast\<close>, by100 blast)
    have hP1_oY: "P1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "P1 = (top1_S2 - ?Y) \<inter> P1" using hP1_sub_Y_compl by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hP1_open by (by100 blast)
    qed
    have hRT_oY: "R1 \<union> T \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)"
    proof -
      have "R1 \<union> T \<subseteq> top1_S2 - ?Y" using hT_union by (by100 blast)
      hence "R1 \<union> T = (top1_S2 - ?Y) \<inter> (R1 \<union> T)" by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hRT_open by (by100 blast)
    qed
    have hPRT_sep: "top1_is_separation_on (top1_S2 - ?Y)
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) P1 (R1 \<union> T)"
    proof -
      have "P1 \<inter> (R1 \<union> T) = {}"
      proof -
        \<comment> \<open>P1 \<inter> T = {} (hT\_disj). P1 \<inter> R1 = {} needs case split.
           But P1, R1, T are pairwise disjoint (they're 3 distinct elements of {U,V,W}).\<close>
        have "P1 \<inter> R1 = {}" by (rule hP1R1_disj)
        thus ?thesis using hT_disj(1) by (by100 blast)
      qed
      moreover have "P1 \<union> (R1 \<union> T) = top1_S2 - ?Y" using hT_union by (by100 blast)
      moreover have "R1 \<union> T \<noteq> {}" using hR(1) by (by100 blast)
      ultimately show ?thesis unfolding top1_is_separation_on_def
        using hP1_oY hRT_oY hP(1) by (by100 blast)
    qed
    have he24_conn_Y: "top1_connected_on (e24 - {a2, a4})
        (subspace_topology (top1_S2 - ?Y)
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) (e24 - {a2, a4}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology (e24 - {a2, a4}) =
          subspace_topology (top1_S2 - ?Y)
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ?Y)) (e24 - {a2, a4})"
        using subspace_topology_trans[of "e24 - {a2, a4}" "top1_S2 - ?Y" top1_S2 top1_S2_topology]
            he24_in_Y_compl by (by100 simp)
      thus ?thesis using he24_conn by (by100 simp)
    qed
    have "e24 - {a2, a4} \<subseteq> P1 \<or> e24 - {a2, a4} \<subseteq> R1 \<union> T"
      using Lemma_23_2[OF hTY_loc hPRT_sep he24_in_Y_compl he24_conn_Y] by (by100 blast)
    hence "e24 - {a2, a4} \<subseteq> R1 \<union> T" using he24_not_P1 by (by100 blast)
    \<comment> \<open>Then separation {R1, T} of R1\<union>T.\<close>
    moreover have "e24 - {a2, a4} \<subseteq> R1 \<or> e24 - {a2, a4} \<subseteq> T"
    proof -
      have hTRT: "is_topology_on (R1 \<union> T)
          (subspace_topology top1_S2 top1_S2_topology (R1 \<union> T))"
        by (rule subspace_topology_is_topology_on[OF hTopS2])
           (use hT_union in \<open>by100 blast\<close>)
      have hR_oRT: "R1 \<in> subspace_topology top1_S2 top1_S2_topology (R1 \<union> T)"
      proof -
        have "R1 = (R1 \<union> T) \<inter> R1" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hR1_open by (by100 blast)
      qed
      have hT_oRT: "T \<in> subspace_topology top1_S2 top1_S2_topology (R1 \<union> T)"
      proof -
        have "T = (R1 \<union> T) \<inter> T" by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hT_open by (by100 blast)
      qed
      have hRT_sep: "top1_is_separation_on (R1 \<union> T)
          (subspace_topology top1_S2 top1_S2_topology (R1 \<union> T)) R1 T"
        unfolding top1_is_separation_on_def
        using hR_oRT hT_oRT hR(1) hT_ne hT_disj(2) by (by100 blast)
      have he24_sub_RT: "e24 - {a2, a4} \<subseteq> R1 \<union> T"
        using \<open>e24 - {a2, a4} \<subseteq> R1 \<union> T\<close> .
      have he24_conn_RT: "top1_connected_on (e24 - {a2, a4})
          (subspace_topology (R1 \<union> T)
              (subspace_topology top1_S2 top1_S2_topology (R1 \<union> T)) (e24 - {a2, a4}))"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology (e24 - {a2, a4}) =
            subspace_topology (R1 \<union> T)
                (subspace_topology top1_S2 top1_S2_topology (R1 \<union> T)) (e24 - {a2, a4})"
          using subspace_topology_trans[of "e24 - {a2, a4}" "R1 \<union> T" top1_S2 top1_S2_topology]
              he24_sub_RT by (by100 simp)
        thus ?thesis using he24_conn by (by100 simp)
      qed
      from Lemma_23_2[OF hTRT hRT_sep he24_sub_RT he24_conn_RT]
      show ?thesis by (by100 blast)
    qed
    ultimately show ?thesis using he24_not_R1 by (by100 blast)
  qed
  \<comment> \<open>Step 5: Apply Theorem_63_5 to split T using cl(P1)\<union>cl(R1) and e24.\<close>
  let ?C1 = "closure_on top1_S2 top1_S2_topology P1
        \<union> closure_on top1_S2 top1_S2_topology R1"
  have hC1_eq: "?C1 = P1 \<union> R1 \<union> ?Y"
    using hcl_P1 hcl_R1 by (by100 blast)
  have hC1_closed: "closedin_on top1_S2 top1_S2_topology ?C1"
  proof -
    have "closedin_on top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology P1)"
    proof -
      have "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      thus ?thesis by (rule closure_on_closed[OF hTopS2])
    qed
    moreover have "closedin_on top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology R1)"
    proof -
      have "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      thus ?thesis by (rule closure_on_closed[OF hTopS2])
    qed
    ultimately show ?thesis by (rule closedin_on_Un[OF hTopS2])
  qed
  have hC1_conn: "top1_connected_on ?C1 (subspace_topology top1_S2 top1_S2_topology ?C1)"
  proof -
    \<comment> \<open>cl(P1) connected (closure of connected set, Theorem 23.4).\<close>
    have hclP1_sub: "closure_on top1_S2 top1_S2_topology P1 \<subseteq> top1_S2"
      using hcl_P1 hP1_sub_AB hA_sub assms(8) by (by100 blast)
    have hP1_sub_S2: "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
    have hclP1_conn: "top1_connected_on (closure_on top1_S2 top1_S2_topology P1)
        (subspace_topology top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology P1))"
      by (rule Theorem_23_4[OF hTopS2 hP1_sub_S2 hclP1_sub subset_closure_on
          closure_on_mono[OF order_refl] hP(5)])
    \<comment> \<open>cl(R1) connected.\<close>
    have hclR1_sub: "closure_on top1_S2 top1_S2_topology R1 \<subseteq> top1_S2"
      using hcl_R1 hR(4) assms(8) hC_sub by (by100 blast)
    have hR1_sub_S2: "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
    have hclR1_conn: "top1_connected_on (closure_on top1_S2 top1_S2_topology R1)
        (subspace_topology top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology R1))"
      by (rule Theorem_23_4[OF hTopS2 hR1_sub_S2 hclR1_sub subset_closure_on
          closure_on_mono[OF order_refl] hR(5)])
    \<comment> \<open>They share B = e13. B \<subseteq> cl(P1) \<inter> cl(R1).\<close>
    have hB_in_both: "?B \<subseteq> closure_on top1_S2 top1_S2_topology P1 \<inter>
        closure_on top1_S2 top1_S2_topology R1"
      using hcl_P1 hcl_R1 by (by100 blast)
    obtain p where hp: "p \<in> ?B" using assms(20) unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "p \<in> closure_on top1_S2 top1_S2_topology P1 \<inter>
        closure_on top1_S2 top1_S2_topology R1" using hB_in_both by (by100 blast)
    \<comment> \<open>Apply Theorem 23.3: indexed family with common point.\<close>
    have "top1_connected_on (closure_on top1_S2 top1_S2_topology P1 \<union>
        closure_on top1_S2 top1_S2_topology R1)
        (subspace_topology top1_S2 top1_S2_topology (closure_on top1_S2 top1_S2_topology P1 \<union>
        closure_on top1_S2 top1_S2_topology R1))"
    proof -
      let ?I = "{True, False}" and ?A = "\<lambda>b. if b then closure_on top1_S2 top1_S2_topology P1
          else closure_on top1_S2 top1_S2_topology R1"
      have "?I \<noteq> {}" by (by100 simp)
      moreover have "\<forall>i \<in> ?I. ?A i \<subseteq> top1_S2"
        using hclP1_sub hclR1_sub by (by100 simp)
      moreover have "\<forall>i \<in> ?I. top1_connected_on (?A i) (subspace_topology top1_S2 top1_S2_topology (?A i))"
        using hclP1_conn hclR1_conn by (by100 simp)
      moreover have "p \<in> \<Inter>(?A ` ?I)"
        using \<open>p \<in> closure_on top1_S2 top1_S2_topology P1 \<inter>
            closure_on top1_S2 top1_S2_topology R1\<close> by (by100 simp)
      moreover have "(\<Union>i \<in> ?I. ?A i) = closure_on top1_S2 top1_S2_topology P1 \<union>
          closure_on top1_S2 top1_S2_topology R1" by (by100 force)
      ultimately have hpremises: "?I \<noteq> {} \<and> (\<forall>i \<in> ?I. ?A i \<subseteq> top1_S2) \<and>
          (\<forall>i \<in> ?I. top1_connected_on (?A i) (subspace_topology top1_S2 top1_S2_topology (?A i))) \<and>
          p \<in> \<Inter>(?A ` ?I) \<and> (\<Union>i \<in> ?I. ?A i) = closure_on top1_S2 top1_S2_topology P1 \<union>
          closure_on top1_S2 top1_S2_topology R1" by (by100 blast)
      from Theorem_23_3[OF hTopS2, of ?I ?A p] hpremises
      show ?thesis by metis
    qed
    thus ?thesis .
  qed
  have hC1_compl: "top1_S2 - ?C1 = T"
  proof -
    have "top1_S2 - ?C1 = top1_S2 - (P1 \<union> R1 \<union> ?Y)" using hC1_eq by (by100 simp)
    also have "\<dots> = (top1_S2 - ?Y) - P1 - R1" by (by100 blast)
    also have "\<dots> = (P1 \<union> R1 \<union> T) - P1 - R1" using hT_union by (by100 simp)
    also have "\<dots> = T" using hT_disj(1,2) by (by100 blast)
    finally show ?thesis .
  qed
  have hC1_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology ?C1"
    unfolding top1_separates_on_def using hC1_compl hT_conn by (by100 simp)
  have he24_closed: "closedin_on top1_S2 top1_S2_topology e24"
    by (rule arc_in_S2_closed[OF assms(9) assms(15)])
  have he24_conn_full: "top1_connected_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
    using arc_connected[OF assms(15)] .
  have he24_no_sep: "\<not> top1_separates_on top1_S2 top1_S2_topology e24"
    by (rule Theorem_63_2_arc_no_separation[OF assms(1) assms(9) assms(15)])
  have hC1_e24_int: "?C1 \<inter> e24 = {a2, a4}"
  proof -
    \<comment> \<open>(P1 \<union> R1 \<union> Y) \<inter> e24 = (P1 \<inter> e24) \<union> (R1 \<inter> e24) \<union> (Y \<inter> e24).
       P1 \<inter> e24 = {} and R1 \<inter> e24 = {} (both \<subseteq> S2-Y, e24\<setminus>{a2,a4} \<subseteq> T).\<close>
    have "P1 \<inter> e24 = {}"
    proof -
      have "P1 \<subseteq> top1_S2 - ?Y" by (rule hP1_sub_Y_compl)
      moreover have "e24 - {a2, a4} \<subseteq> T" by (rule he24_in_T)
      moreover have "P1 \<inter> T = {}" by (rule hT_disj(1))
      moreover have "{a2, a4} \<subseteq> ?Y" using ha2_in_Y ha4_in_Y by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    moreover have "R1 \<inter> e24 = {}"
    proof -
      have "R1 \<subseteq> top1_S2 - ?Y" by (rule hR1_sub_Y_compl)
      moreover have "e24 - {a2, a4} \<subseteq> T" by (rule he24_in_T)
      moreover have "R1 \<inter> T = {}" by (rule hT_disj(2))
      moreover have "{a2, a4} \<subseteq> ?Y" using ha2_in_Y ha4_in_Y by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    ultimately have h_e24_fact: "(P1 \<union> R1) \<inter> e24 = {}" by (by100 blast)
    show ?thesis
    proof (rule set_eqI, rule iffI)
      fix x assume "x \<in> ?C1 \<inter> e24"
      hence "x \<in> (P1 \<union> R1 \<union> ?Y) \<inter> e24" using hC1_eq by (by100 blast)
      hence "x \<in> ?Y \<inter> e24" using h_e24_fact by (by100 blast)
      hence "x \<in> e24 \<inter> ?Y" by (by100 blast)
      thus "x \<in> {a2, a4}"
      proof -
        from he24_Y_int have "\<And>z. z \<in> e24 \<inter> ?Y \<Longrightarrow> z \<in> {a2, a4}" by (by100 blast)
        thus ?thesis using \<open>x \<in> e24 \<inter> ?Y\<close> by (by100 blast)
      qed
    next
      fix x assume "x \<in> {a2, a4}"
      hence "x \<in> ?Y \<inter> e24" using he24_Y_int by (by100 blast)
      hence "x \<in> (P1 \<union> R1 \<union> ?Y) \<inter> e24" by (by100 blast)
      thus "x \<in> ?C1 \<inter> e24" using hC1_eq by (by100 blast)
    qed
  qed
  have hC1_e24_card: "card (?C1 \<inter> e24) = 2"
    using hC1_e24_int hdist(5) by (by100 simp)
  obtain W1 W2 where hW: "W1 \<noteq> {}" "W2 \<noteq> {}" "W1 \<inter> W2 = {}"
      "W1 \<union> W2 = top1_S2 - (?C1 \<union> e24)"
      "top1_connected_on W1 (subspace_topology top1_S2 top1_S2_topology W1)"
      "top1_connected_on W2 (subspace_topology top1_S2 top1_S2_topology W2)"
    using Theorem_63_5_two_closed_connected[OF assms(1) hC1_closed he24_closed
        hC1_conn he24_conn_full hC1_e24_card hC1_no_sep he24_no_sep]
    by (by100 metis)
  \<comment> \<open>W1, W2 are open (via theta-space separation + two-component lemma).\<close>
  have hC1_sub_S2: "?C1 \<subseteq> top1_S2" using hC1_closed unfolding closedin_on_def by (by100 blast)
  have hC1e24_sep: "top1_separates_on top1_S2 top1_S2_topology (?C1 \<union> e24)"
    by (rule Theorem_61_4_general_separation[OF assms(1) hC1_sub_S2 assms(9)
        hC1_closed he24_closed hC1_conn he24_conn_full hC1_e24_card])
  have hC1e24_closed: "closedin_on top1_S2 top1_S2_topology (?C1 \<union> e24)"
    by (rule closedin_on_Un[OF hTopS2 hC1_closed he24_closed])
  have hC1e24_open: "top1_S2 - (?C1 \<union> e24) \<in> top1_S2_topology"
    using hC1e24_closed hTopS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
  have hC1e24_not_conn: "\<not> top1_connected_on (top1_S2 - (?C1 \<union> e24))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?C1 \<union> e24)))"
    using hC1e24_sep unfolding top1_separates_on_def by (by100 blast)
  have hW1_open: "W1 \<in> top1_S2_topology" and hW2_open: "W2 \<in> top1_S2_topology"
    using S2_two_component_open[OF hC1e24_open _ hW(1,2,3,4,5,6) hC1e24_not_conn]
    by (by100 blast)+
  \<comment> \<open>Step 6: Package the 4 components P1, R1, W1, W2.\<close>
  have hfour_union: "P1 \<union> R1 \<union> W1 \<union> W2 = top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e41 \<union> e13 \<union> e24)"
  proof -
    have "W1 \<union> W2 = top1_S2 - (?C1 \<union> e24)" by (rule hW(4))
    hence "W1 \<union> W2 = top1_S2 - ((P1 \<union> R1 \<union> ?Y) \<union> e24)" using hC1_eq by (by100 simp)
    hence "P1 \<union> R1 \<union> W1 \<union> W2 = P1 \<union> R1 \<union> (top1_S2 - (P1 \<union> R1 \<union> ?Y \<union> e24))" by (by100 blast)
    also have "\<dots> = top1_S2 - (?Y \<union> e24)"
    proof -
      have "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      moreover have "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      moreover have "P1 \<inter> ?Y = {}" using hP1_sub_Y_compl by (by100 blast)
      moreover have "R1 \<inter> ?Y = {}" using hR1_sub_Y_compl by (by100 blast)
      moreover have "P1 \<inter> e24 = {}"
      proof -
        have "P1 \<subseteq> top1_S2 - ?Y" by (rule hP1_sub_Y_compl)
        moreover have "e24 - {a2, a4} \<subseteq> T" by (rule he24_in_T)
        moreover have "P1 \<inter> T = {}" by (rule hT_disj(1))
        moreover have "{a2, a4} \<subseteq> ?Y" using ha2_in_Y ha4_in_Y by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      moreover have "R1 \<inter> e24 = {}"
      proof -
        have "R1 \<subseteq> top1_S2 - ?Y" by (rule hR1_sub_Y_compl)
        moreover have "e24 - {a2, a4} \<subseteq> T" by (rule he24_in_T)
        moreover have "R1 \<inter> T = {}" by (rule hT_disj(2))
        moreover have "{a2, a4} \<subseteq> ?Y" using ha2_in_Y ha4_in_Y by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      ultimately show ?thesis by (by100 blast)
    qed
    also have "\<dots> = top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e41 \<union> e13 \<union> e24)" by blast
    finally show ?thesis .
  qed
  have hfour_disj: "P1 \<inter> R1 = {}" "P1 \<inter> W1 = {}" "P1 \<inter> W2 = {}"
      "R1 \<inter> W1 = {}" "R1 \<inter> W2 = {}" "W1 \<inter> W2 = {}"
  proof -
    show "P1 \<inter> R1 = {}" by (rule hP1R1_disj)
    \<comment> \<open>W1, W2 \<subseteq> S2-(C1\<union>e24) = T-e24_inner, which is disjoint from P1, R1.\<close>
    have hW12_sub: "W1 \<union> W2 \<subseteq> top1_S2 - ?C1" using hW(4) by (by100 blast)
    hence "W1 \<subseteq> top1_S2 - ?C1" by (by100 blast)
    hence "P1 \<inter> W1 = {}" using hC1_eq by (by100 blast)
    thus "P1 \<inter> W1 = {}" .
    have "W2 \<subseteq> top1_S2 - ?C1" using hW12_sub by (by100 blast)
    thus "P1 \<inter> W2 = {}" using hC1_eq by (by100 blast)
    have "W1 \<subseteq> top1_S2 - ?C1" using hW12_sub by (by100 blast)
    thus "R1 \<inter> W1 = {}" using hC1_eq by (by100 blast)
    have "W2 \<subseteq> top1_S2 - ?C1" using hW12_sub by (by100 blast)
    thus "R1 \<inter> W2 = {}" using hC1_eq by (by100 blast)
    show "W1 \<inter> W2 = {}" by (rule hW(3))
  qed
  have hbd_P1: "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology P1)"
  proof -
    have "a4 \<in> P2" using hCm_in_P2 hdist(3,6) arc_endpoints_subset[of e41] assms(19) by (by100 blast)
    have "a4 \<notin> P1" using \<open>a4 \<in> P2\<close> hP(3) by (by100 blast)
    hence "a4 \<notin> P1 \<union> (?A \<union> ?B)" using ha4_not_AB by (by100 blast)
    hence "a4 \<notin> closure_on top1_S2 top1_S2_topology P1" using hcl_P1 by (by100 simp)
    thus ?thesis by (by100 blast)
  qed
  have hbd_R1: "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology R1)"
  proof -
    have "a2 \<in> R2" using hAm_in_R2 hdist(1,4) arc_endpoints_subset[of e12] assms(16) by (by100 blast)
    have "a2 \<notin> R1" using \<open>a2 \<in> R2\<close> hR(3) by (by100 blast)
    hence "a2 \<notin> R1 \<union> (?B \<union> ?C)" using ha2_not_BC by (by100 blast)
    hence "a2 \<notin> closure_on top1_S2 top1_S2_topology R1" using hcl_R1 by (by100 simp)
    thus ?thesis by (by100 blast)
  qed
  \<comment> \<open>Boundary of W1, W2 via second theta (Munkres ``symmetry'' argument).
     Second theta: arcs from a2 to a4: A' = e12\<union>e41, B' = e24, C' = e23\<union>e34.
     Lemma\_64\_1 gives 3 components. Two of them are W1, W2.
     Component with boundary A'\<union>B' misses a3. Component with boundary B'\<union>C' misses a1.\<close>
  \<comment> \<open>Step 1: Build arcs A' = e12\<union>e41 and C' = e23\<union>e34 from a2 to a4.\<close>
  have ha1_ep12: "a1 \<in> top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
    using assms(16) by (by100 blast)
  have ha1_ep41: "a1 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
    using assms(19) by (by100 blast)
  have he12_e41: "e12 \<inter> e41 = {a1}" using assms(27) by (by100 blast)
  have hA'_arc: "top1_is_arc_on (e12 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (e12 \<union> e41))"
    by (rule arcs_concatenation_is_arc[OF hS2_strict hS2_haus assms(10) assms(4)
        assms(13) assms(7) he12_e41 ha1_ep12 ha1_ep41])
  have hA'_sub: "e12 \<union> e41 \<subseteq> top1_S2" using assms(4,7) by (by100 blast)
  have ha3_ep23: "a3 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
    using assms(17) by (by100 blast)
  have ha3_ep34: "a3 \<in> top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
    using assms(18) by (by100 blast)
  have hC'_arc: "top1_is_arc_on (e23 \<union> e34) (subspace_topology top1_S2 top1_S2_topology (e23 \<union> e34))"
    by (rule arcs_concatenation_is_arc[OF hS2_strict hS2_haus assms(11) assms(5)
        assms(12) assms(6) assms(25) ha3_ep23 ha3_ep34])
  have hC'_sub: "e23 \<union> e34 \<subseteq> top1_S2" using assms(5,6) by (by100 blast)
  \<comment> \<open>Step 2: Compute endpoints and intersections for the second theta.\<close>
  have ha2_ep12': "a2 \<in> top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
    using assms(16) by (by100 blast)
  have ha4_ep41': "a4 \<in> top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41)"
    using assms(19) by (by100 blast)
  have hA'_ep: "top1_arc_endpoints_on (e12 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (e12 \<union> e41)) = {a2, a4}"
  proof -
    have hep12: "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a2, a1}"
      using assms(16) by (by100 blast)
    have hep41: "top1_arc_endpoints_on e41 (subspace_topology top1_S2 top1_S2_topology e41) = {a1, a4}"
      using assms(19) by (by100 blast)
    have "a2 \<noteq> a1" using hdist(1) by (by100 blast)
    have "a1 \<noteq> a4" by (rule hdist(3))
    show ?thesis
      by (rule arc_concat_endpoints[OF hS2_strict hS2_haus assms(10) assms(4)
          assms(13) assms(7) he12_e41 ha1_ep12 ha1_ep41 hep12 hep41 \<open>a2 \<noteq> a1\<close> \<open>a1 \<noteq> a4\<close>])
  qed
  have ha2_ep23': "a2 \<in> top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
    using assms(17) by (by100 blast)
  have ha4_ep34': "a4 \<in> top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
    using assms(18) by (by100 blast)
  have hC'_ep: "top1_arc_endpoints_on (e23 \<union> e34) (subspace_topology top1_S2 top1_S2_topology (e23 \<union> e34)) = {a2, a4}"
  proof -
    have hep23: "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2, a3}"
      using assms(17) by (by100 blast)
    have hep34: "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3, a4}"
      using assms(18) by (by100 blast)
    show ?thesis
      by (rule arc_concat_endpoints[OF hS2_strict hS2_haus assms(11) assms(5)
          assms(12) assms(6) assms(25) ha3_ep23 ha3_ep34 hep23 hep34 hdist(4) hdist(6)])
  qed
  \<comment> \<open>Pairwise intersections = {a2, a4}.\<close>
  have hA'B': "(e12 \<union> e41) \<inter> e24 = {a2, a4}"
  proof -
    have "(e12 \<union> e41) \<inter> e24 = (e12 \<inter> e24) \<union> (e41 \<inter> e24)" by (by100 blast)
    also have "\<dots> = {a2} \<union> {a4}" using assms(33) assms(36)
      apply (simp add: Int_commute)
      done
    finally show ?thesis by (by100 blast)
  qed
  have hB'C': "e24 \<inter> (e23 \<union> e34) = {a2, a4}"
  proof -
    have "e24 \<inter> (e23 \<union> e34) = (e24 \<inter> e23) \<union> (e24 \<inter> e34)" by (by100 blast)
    also have "\<dots> = {a2} \<union> {a4}" using assms(34) assms(35) by (by100 blast)
    finally show ?thesis by (by100 blast)
  qed
  have hA'C': "(e12 \<union> e41) \<inter> (e23 \<union> e34) = {a2, a4}"
  proof -
    have "(e12 \<union> e41) \<inter> (e23 \<union> e34) = (e12 \<inter> e23) \<union> (e12 \<inter> e34) \<union> (e41 \<inter> e23) \<union> (e41 \<inter> e34)"
      by (by100 blast)
    also have "\<dots> = {a2} \<union> {} \<union> {} \<union> {a4}"
      using assms(24) assms(22) assms(23) assms(26)
      apply (simp add: Int_commute)
      done
    also have "\<dots> = {a2, a4}" by (by100 blast)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 3 (Munkres symmetry): JCT component F3 of S2-(triangle a1a2a4) with a3 \<notin> closure.\<close>
  have hA'B'_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology ((e12 \<union> e41) \<union> e24)"
    by (rule arcs_form_simple_closed_curve[OF hS2_strict hS2_haus hA'_arc hA'_sub
        assms(15) assms(9) hA'B' hdist(5) hA'_ep assms(21)])
  have hA'B'_sep: "top1_separates_on top1_S2 top1_S2_topology ((e12 \<union> e41) \<union> e24)"
    by (rule Theorem_61_3_JordanSeparation_S2[OF assms(1) hA'B'_scc])
  have hA'_closed: "closedin_on top1_S2 top1_S2_topology (e12 \<union> e41)"
    by (rule closedin_on_Un[OF hTopS2 arc_in_S2_closed[OF assms(4) assms(10)] arc_in_S2_closed[OF assms(7) assms(13)]])
  have hA'_conn: "top1_connected_on (e12 \<union> e41) (subspace_topology top1_S2 top1_S2_topology (e12 \<union> e41))"
    using arc_connected[OF hA'_arc] .
  have hA'B'_card: "card ((e12 \<union> e41) \<inter> e24) = 2" using hA'B' hdist(5) by (by100 simp)
  obtain G1 G2 where hG: "G1 \<noteq> {}" "G2 \<noteq> {}" "G1 \<inter> G2 = {}"
      "G1 \<union> G2 = top1_S2 - ((e12 \<union> e41) \<union> e24)"
      "top1_connected_on G1 (subspace_topology top1_S2 top1_S2_topology G1)"
      "top1_connected_on G2 (subspace_topology top1_S2 top1_S2_topology G2)"
    using Theorem_63_5_two_closed_connected[OF assms(1) hA'_closed
        arc_in_S2_closed[OF assms(9) assms(15)]
        hA'_conn arc_connected[OF assms(15)] hA'B'_card
        Theorem_63_2_arc_no_separation[OF assms(1) hA'_sub hA'_arc]
        Theorem_63_2_arc_no_separation[OF assms(1) assms(9) assms(15)]]
    by (by100 metis)
  have hA'B'_open: "top1_S2 - ((e12 \<union> e41) \<union> e24) \<in> top1_S2_topology"
    using closedin_on_Un[OF hTopS2 hA'_closed arc_in_S2_closed[OF assms(9) assms(15)]]
    hTopS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
  have hA'B'_nc: "\<not> top1_connected_on (top1_S2 - ((e12 \<union> e41) \<union> e24))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24)))"
    using hA'B'_sep unfolding top1_separates_on_def by (by100 blast)
  have hG_open: "G1 \<in> top1_S2_topology" "G2 \<in> top1_S2_topology"
    using S2_two_component_open[OF hA'B'_open _ hG(1,2,3,4,5,6) hA'B'_nc] by (by100 blast)+
  \<comment> \<open>Vertex/edge facts for intersection arguments.\<close>
  have ha3_e34_loc: "a3 \<in> e34" using assms(18) unfolding top1_arc_endpoints_on_def by (by100 blast)
  have ha3_not_A'B': "a3 \<notin> (e12 \<union> e41) \<union> e24"
  proof -
    have "a3 \<notin> e12" using assms(22) ha3_e34_loc by (by100 blast)
    have "a3 \<notin> e41"
    proof assume "a3 \<in> e41"
      hence "a3 \<in> e41 \<inter> e34" using ha3_e34_loc by (by100 blast)
      hence "a3 = a4" using assms(26) by (by100 blast)
      thus False using hdist(6) by (by100 blast) qed
    have "a3 \<notin> e24"
    proof assume "a3 \<in> e24"
      hence "a3 \<in> e24 \<inter> e34" using ha3_e34_loc by (by100 blast)
      hence "a3 = a4" using assms(35) by (by100 blast)
      thus False using hdist(6) by (by100 blast) qed
    thus ?thesis using \<open>a3 \<notin> e12\<close> \<open>a3 \<notin> e41\<close> \<open>a3 \<notin> e24\<close> by (by100 blast)
  qed
  have ha1_e12_loc: "a1 \<in> e12" using assms(16) unfolding top1_arc_endpoints_on_def by (by100 blast)
  \<comment> \<open>Place C'int = (e23\<union>e34)-{a2,a4} in G1 or G2 via connectivity.\<close>
  have hC'_int_conn: "top1_connected_on ((e23 \<union> e34) - {a2, a4})
      (subspace_topology top1_S2 top1_S2_topology ((e23 \<union> e34) - {a2, a4}))"
    by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus hC'_sub hC'_arc hC'_ep hdist(5)])
  have hC'_int_in_SCC: "(e23 \<union> e34) - {a2, a4} \<subseteq> top1_S2 - ((e12 \<union> e41) \<union> e24)"
  proof -
    have "(e23 \<union> e34) \<inter> ((e12 \<union> e41) \<union> e24) \<subseteq> {a2, a4}"
    proof -
      have "(e23 \<union> e34) \<inter> ((e12 \<union> e41) \<union> e24) = (e23\<inter>e12) \<union> (e23\<inter>e41) \<union> (e23\<inter>e24)
          \<union> (e34\<inter>e12) \<union> (e34\<inter>e41) \<union> (e34\<inter>e24)" by (by100 blast)
      also have "\<dots> \<subseteq> {a2} \<union> {} \<union> {a2} \<union> {} \<union> {a4} \<union> {a4}"
        using assms(24) assms(23) assms(34) assms(22) assms(26) assms(35)
        apply (simp add: Int_commute) done
      finally show ?thesis by (by100 blast)
    qed
    thus ?thesis using hC'_sub by (by100 blast)
  qed
  \<comment> \<open>C'int is connected, in S2-SCC, so in G1 or G2.\<close>
  have hC'_int_ne: "(e23 \<union> e34) - {a2, a4} \<noteq> {}"
  proof -
    \<comment> \<open>a2 \<in> closure(C'-{a2,a4}) implies C'-{a2,a4} \<noteq> {} (closure of empty is empty).\<close>
    have "a2 \<in> closure_on top1_S2 top1_S2_topology ((e23 \<union> e34) - {a2, a4})"
      by (rule arc_endpoint_in_closure_of_interior(1)[OF hS2_strict hS2_haus hC'_sub hC'_arc hC'_ep hdist(5)])
    moreover have "closure_on top1_S2 top1_S2_topology {} = {}"
      by (rule top1_closure_on_empty[OF hTopS2])
    ultimately show ?thesis by (by100 force)
  qed
  \<comment> \<open>Choose F3 = the JCT component NOT containing C'int. F3' = the other.\<close>
  have hC'_in_G: "(e23 \<union> e34) - {a2, a4} \<subseteq> G1 \<or> (e23 \<union> e34) - {a2, a4} \<subseteq> G2"
  proof -
    have hT: "is_topology_on (top1_S2 - ((e12 \<union> e41) \<union> e24))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24)))"
      by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
    have hG1_oT: "G1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))"
    proof -
      have "G1 = (top1_S2 - ((e12 \<union> e41) \<union> e24)) \<inter> G1" using hG(4) by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hG_open(1) by (by100 blast)
    qed
    have hG2_oT: "G2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))"
    proof -
      have "G2 = (top1_S2 - ((e12 \<union> e41) \<union> e24)) \<inter> G2" using hG(4) by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hG_open(2) by (by100 blast)
    qed
    have hsep: "top1_is_separation_on (top1_S2 - ((e12 \<union> e41) \<union> e24))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))) G1 G2"
      unfolding top1_is_separation_on_def using hG1_oT hG2_oT hG(1,2,3,4) by (by100 blast)
    have hC'_conn_T: "top1_connected_on ((e23 \<union> e34) - {a2, a4})
        (subspace_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24)))
            ((e23 \<union> e34) - {a2, a4}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology ((e23 \<union> e34) - {a2, a4}) =
          subspace_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24)))
              ((e23 \<union> e34) - {a2, a4})"
        using subspace_topology_trans[of "(e23 \<union> e34) - {a2, a4}" "top1_S2 - ((e12 \<union> e41) \<union> e24)"
            top1_S2 top1_S2_topology] hC'_int_in_SCC by (by100 simp)
      thus ?thesis using hC'_int_conn by (by100 simp)
    qed
    from Lemma_23_2[OF hT hsep hC'_int_in_SCC hC'_conn_T] show ?thesis by (by100 blast)
  qed
  obtain F3 F3' where hF3_props: "F3 \<noteq> {}" "F3 \<in> top1_S2_topology"
      "F3 \<union> F3' = top1_S2 - ((e12 \<union> e41) \<union> e24)" "F3 \<inter> F3' = {}"
      "top1_connected_on F3 (subspace_topology top1_S2 top1_S2_topology F3)"
      "F3' \<in> top1_S2_topology"
      "top1_connected_on F3' (subspace_topology top1_S2 top1_S2_topology F3')"
      and hC'_in_F3': "(e23 \<union> e34) - {a2, a4} \<subseteq> F3'"
  proof -
    from hC'_in_G show ?thesis
    proof
      assume "(e23 \<union> e34) - {a2, a4} \<subseteq> G1"
      show ?thesis by (rule that[of G2 G1])
        (use hG(1,2,3,4,5,6) hG_open \<open>(e23 \<union> e34) - {a2, a4} \<subseteq> G1\<close> in \<open>by100 blast\<close>)+
    next
      assume "(e23 \<union> e34) - {a2, a4} \<subseteq> G2"
      show ?thesis by (rule that[of G1 G2])
        (use hG(1,2,3,4,5,6) hG_open \<open>(e23 \<union> e34) - {a2, a4} \<subseteq> G2\<close> in \<open>by100 blast\<close>)+
    qed
  qed
  \<comment> \<open>Closure bound: cl(F3) \<subseteq> F3 \<union> (A'\<union>B') since F3' open, disjoint.\<close>
  have hF3'_sub: "F3' \<subseteq> top1_S2" using hF3_props(3) by (by100 blast)
  have hcl_F3: "closedin_on top1_S2 top1_S2_topology (top1_S2 - F3')"
  proof -
    have "top1_S2 - (top1_S2 - F3') = F3'" using hF3'_sub by (by100 blast)
    hence "top1_S2 - (top1_S2 - F3') \<in> top1_S2_topology" using hF3_props(6) by (by100 simp)
    thus ?thesis unfolding closedin_on_def by (by100 blast)
  qed
  have "F3 \<subseteq> top1_S2 - F3'" using hF3_props(3,4) by (by100 blast)
  hence hcl_F3_bound: "closure_on top1_S2 top1_S2_topology F3 \<subseteq> F3 \<union> ((e12 \<union> e41) \<union> e24)"
  proof -
    have "closure_on top1_S2 top1_S2_topology F3 \<subseteq> top1_S2 - F3'"
      by (rule closure_on_subset_of_closed[OF hcl_F3 \<open>F3 \<subseteq> top1_S2 - F3'\<close>])
    thus ?thesis using hF3_props(3) by (by100 blast)
  qed
  \<comment> \<open>a3 \<notin> closure(F3): a3 \<in> C'int \<subseteq> F3', so a3 \<notin> F3; and a3 \<notin> A'\<union>B'.\<close>
  have ha3_in_F3': "a3 \<in> F3'"
    using hC'_in_F3' ha3_e34_loc hdist(4) hdist(6) by (by100 blast)
  hence "a3 \<notin> F3" using hF3_props(4) by (by100 blast)
  hence ha3_not_cl_F3: "a3 \<notin> closure_on top1_S2 top1_S2_topology F3"
    using hcl_F3_bound ha3_not_A'B' by (by100 blast)
  \<comment> \<open>e13 \<inter> F3 = {}: if not, e13-{a1,a3} connected, in S2-SCC, meets F3, so \<subseteq> F3.
     Then a3 \<in> cl(e13-{a1,a3}) \<subseteq> cl(F3). Contradicts ha3\_not\_cl\_F3.\<close>
  have he13_disj_F3: "e13 \<inter> F3 = {}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain z where "z \<in> e13" "z \<in> F3" by (by100 blast)
    have "z \<noteq> a1" using \<open>z \<in> F3\<close> hF3_props(3) ha1_e12_loc by (by100 blast)
    have "z \<noteq> a3" using \<open>z \<in> F3\<close> \<open>a3 \<notin> F3\<close> by (by100 blast)
    have "z \<in> e13 - {a1, a3}" using \<open>z \<in> e13\<close> \<open>z \<noteq> a1\<close> \<open>z \<noteq> a3\<close> by (by100 blast)
    have he13_conn: "top1_connected_on (e13 - {a1, a3})
        (subspace_topology top1_S2 top1_S2_topology (e13 - {a1, a3}))"
      by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus assms(8) assms(14) assms(20) hdist(2)])
    have he13_sub: "e13 - {a1, a3} \<subseteq> top1_S2 - ((e12 \<union> e41) \<union> e24)"
    proof -
      have "e13 \<inter> e12 = {a1}" by (rule assms(28))
      have "e13 \<inter> e41 = {a1}" by (rule assms(31))
      have "e13 \<inter> ((e12 \<union> e41) \<union> e24) \<subseteq> {a1}"
      proof -
        have "e24 \<inter> e13 = {}"
        proof -
          have "a1 \<notin> e24" proof assume "a1 \<in> e24"
            hence "a1 \<in> e24 \<inter> e12" using ha1_e12_loc by (by100 blast)
            thus False using assms(33) hdist(1) by (by100 blast) qed
          have "a3 \<notin> e24" proof assume "a3 \<in> e24"
            hence "a3 \<in> e24 \<inter> e34" using ha3_e34_loc by (by100 blast)
            thus False using assms(35) hdist(6) by (by100 blast) qed
          have "a2 \<notin> e13" proof assume "a2 \<in> e13"
            hence "a2 \<in> e13 \<inter> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
            thus False using assms(29) hdist(4) by (by100 blast) qed
          have "a4 \<notin> e13" proof assume "a4 \<in> e13"
            hence "a4 \<in> e13 \<inter> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
            hence "a4 \<in> {a1}" using assms(31) by (by100 blast)
            thus False using hdist(3) by (by100 simp) qed
          have "\<forall>x \<in> {a1,a2,a3,a4}. x \<notin> e24 \<inter> e13"
            using \<open>a1 \<notin> e24\<close> \<open>a3 \<notin> e24\<close> \<open>a2 \<notin> e13\<close> \<open>a4 \<notin> e13\<close> by (by100 blast)
          thus ?thesis using assms(32) by (by100 blast)
        qed
        thus ?thesis using \<open>e13 \<inter> e12 = {a1}\<close> \<open>e13 \<inter> e41 = {a1}\<close> by (by100 blast)
      qed
      thus ?thesis using assms(8) by (by100 blast)
    qed
    have "(e13 - {a1, a3}) \<inter> F3 \<noteq> {}" using \<open>z \<in> e13 - {a1,a3}\<close> \<open>z \<in> F3\<close> by (by100 blast)
    \<comment> \<open>e13-{a1,a3} connected, in S2-SCC, meets F3 \<Rightarrow> \<subseteq> F3 (by SCC separation).\<close>
    have "e13 - {a1, a3} \<subseteq> F3"
    proof -
      have "\<forall>x. x \<in> e13 - {a1,a3} \<longrightarrow> x \<in> F3 \<union> F3'"
        using he13_sub hF3_props(3) by (by100 blast)
      hence "\<forall>x. x \<in> e13 - {a1,a3} \<longrightarrow> x \<notin> F3 \<longrightarrow> x \<in> F3'"
        by (by100 blast)
      have "e13 - {a1,a3} \<subseteq> F3 \<or> e13 - {a1,a3} \<subseteq> F3'"
      proof -
        have hT: "is_topology_on (top1_S2 - ((e12 \<union> e41) \<union> e24))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24)))"
          by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
        have hF3_oT: "F3 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))"
        proof -
          have "F3 = (top1_S2 - ((e12 \<union> e41) \<union> e24)) \<inter> F3" using hF3_props(3) by (by100 blast)
          thus ?thesis unfolding subspace_topology_def using hF3_props(2) by (by100 blast)
        qed
        have hF3'_oT: "F3' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))"
        proof -
          have "F3' = (top1_S2 - ((e12 \<union> e41) \<union> e24)) \<inter> F3'" using hF3_props(3) by (by100 blast)
          thus ?thesis unfolding subspace_topology_def using hF3_props(6) by (by100 blast)
        qed
        have hsep: "top1_is_separation_on (top1_S2 - ((e12 \<union> e41) \<union> e24))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))) F3 F3'"
        proof -
          have "F3' \<noteq> {}" using hC'_in_F3' hC'_int_ne by (by100 blast)
          show ?thesis unfolding top1_is_separation_on_def
            using hF3_oT hF3'_oT hF3_props(1) \<open>F3' \<noteq> {}\<close> hF3_props(4,3) by (by100 blast)
        qed
        have he13_conn_T: "top1_connected_on (e13 - {a1, a3})
            (subspace_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))) (e13 - {a1, a3}))"
        proof -
          have "subspace_topology top1_S2 top1_S2_topology (e13 - {a1, a3}) =
              subspace_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))) (e13 - {a1, a3})"
            using subspace_topology_trans[of "e13-{a1,a3}" "top1_S2 - ((e12 \<union> e41) \<union> e24)" top1_S2 top1_S2_topology]
                he13_sub by (by100 simp)
          thus ?thesis using he13_conn by (by100 simp)
        qed
        from Lemma_23_2[OF hT hsep he13_sub he13_conn_T] show ?thesis by (by100 blast)
      qed
      thus ?thesis
      proof
        assume "e13 - {a1,a3} \<subseteq> F3" thus ?thesis .
      next
        assume h_sub_F3': "e13 - {a1,a3} \<subseteq> F3'"
        have "F3 \<inter> F3' = {}" by (rule hF3_props(4))
        have "(e13 - {a1,a3}) \<inter> F3 = {}"
        proof -
          have "\<forall>x. x \<in> e13 - {a1,a3} \<longrightarrow> x \<notin> F3"
          proof (intro allI impI)
            fix x assume "x \<in> e13 - {a1,a3}"
            hence "x \<in> F3'" using h_sub_F3' by (by100 blast)
            thus "x \<notin> F3" using \<open>F3 \<inter> F3' = {}\<close> by (by100 blast)
          qed
          show ?thesis
            apply (rule Int_emptyI)
            using \<open>\<forall>x. x \<in> e13 - {a1,a3} \<longrightarrow> x \<notin> F3\<close>
            apply (by100 simp)
            done
        qed
        thus ?thesis using \<open>(e13 - {a1, a3}) \<inter> F3 \<noteq> {}\<close>
          apply (by100 simp)
          done
      qed
    qed
    hence "a3 \<in> closure_on top1_S2 top1_S2_topology F3"
      using closure_on_mono[of "e13 - {a1,a3}" F3 top1_S2 top1_S2_topology]
          arc_endpoint_in_closure_of_interior(2)[OF hS2_strict hS2_haus assms(8) assms(14) assms(20) hdist(2)]
      by (by100 blast)
    thus False using ha3_not_cl_F3 by (by100 blast)
  qed
  \<comment> \<open>F3 \<subseteq> S2-X.\<close>
  have hF3_sub_SX: "F3 \<subseteq> top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e41 \<union> e13 \<union> e24)"
  proof
    fix x assume "x \<in> F3"
    hence "x \<in> top1_S2 - ((e12 \<union> e41) \<union> e24)" using hF3_props(3) by (by100 blast)
    hence "x \<notin> e12" "x \<notin> e41" "x \<notin> e24" "x \<in> top1_S2" by (by100 blast)+
    have "x \<notin> e13" using \<open>x \<in> F3\<close> he13_disj_F3 by (by100 blast)
    have "x \<notin> e23 \<and> x \<notin> e34"
    proof -
      have hF3_sub: "F3 \<subseteq> top1_S2 - ((e12 \<union> e41) \<union> e24)" using hF3_props(3,4) by (by100 force)
      \<comment> \<open>F3 \<subseteq> S2-((e12\<union>e41)\<union>e24). Need also F3 \<inter> (e23\<union>e34) = {}.
         F3 is a JCT component. C'int = (e23\<union>e34)-{a2,a4} \<subseteq> F3' (not in F3).
         And {a2,a4} \<subseteq> (e12\<union>e41)\<union>e24. So (e23\<union>e34) \<inter> F3 \<subseteq> {a2,a4} \<inter> F3 = {}.
         Because {a2,a4} \<subseteq> SCC = (e12\<union>e41)\<union>e24 and F3 \<subseteq> S2-SCC.\<close>
      have "(e23 \<union> e34) - {a2,a4} \<subseteq> F3'" by (rule hC'_in_F3')
      have "x \<notin> (e23 \<union> e34) - {a2,a4}" using \<open>x \<in> F3\<close> hF3_props(4)
        \<open>(e23 \<union> e34) - {a2,a4} \<subseteq> F3'\<close> by (by100 blast)
      moreover have "x \<notin> {a2, a4}" using \<open>x \<notin> e12\<close> \<open>x \<notin> e41\<close> \<open>x \<notin> e24\<close>
        arc_endpoints_subset[of e12] arc_endpoints_subset[of e41] arc_endpoints_subset[of e24]
        assms(16) assms(19) assms(21) by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    show "x \<in> top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e41 \<union> e13 \<union> e24)"
      using \<open>x \<in> top1_S2\<close> \<open>x \<notin> e12\<close> \<open>x \<notin> e41\<close> \<open>x \<notin> e24\<close> \<open>x \<notin> e13\<close> \<open>x \<notin> e23 \<and> x \<notin> e34\<close>
      by (by100 blast)
  qed
  \<comment> \<open>F3 \<in> {W1, W2}: F3 connected open, F3 \<subseteq> S2-X = P1\<union>R1\<union>W1\<union>W2.
     F3 \<noteq> P1: a3 \<in> cl(P1) but a3 \<notin> cl(F3). If F3 \<subseteq> P1: cl(F3) \<subseteq> cl(P1), contradiction.
     F3 \<noteq> R1: a3 \<in> cl(R1) but a3 \<notin> cl(F3). Same argument.\<close>
  have hF3_in_WW: "F3 \<in> {W1, W2}"
  proof -
    \<comment> \<open>P1 \<subseteq> S2-(A'\<union>B') = F3\<union>F3'. P1 connected \<Rightarrow> P1 \<subseteq> F3 or F3'.
       If P1 \<subseteq> F3: cl(P1) \<subseteq> cl(F3), a3 \<in> cl(P1), a3 \<notin> cl(F3). Contradiction.
       So P1 \<subseteq> F3'. Hence F3 \<inter> P1 = {}. Similarly R1.\<close>
    have hP1_sub_AB': "P1 \<subseteq> top1_S2 - ((e12 \<union> e41) \<union> e24)"
    proof -
      have "P1 \<inter> e12 = {}" using hP(4) hfour_union by (by100 blast)
      have "P1 \<inter> e41 = {}" using hP(4) hfour_union by (by100 blast)
      have "P1 \<inter> e24 = {}" using hP(4) hfour_union by (by100 blast)
      have "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      thus ?thesis using \<open>P1 \<inter> e12 = {}\<close> \<open>P1 \<inter> e41 = {}\<close> \<open>P1 \<inter> e24 = {}\<close> by (by100 blast)
    qed
    have "P1 \<subseteq> F3 \<or> P1 \<subseteq> F3'"
    proof -
      have hT_AB': "is_topology_on (top1_S2 - ((e12 \<union> e41) \<union> e24))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24)))"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
      have hF3_oT: "F3 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))"
      proof -
        have "F3 = (top1_S2 - ((e12 \<union> e41) \<union> e24)) \<inter> F3" using hF3_props(3) by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hF3_props(2) by (by100 blast)
      qed
      have hF3'_oT: "F3' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))"
      proof -
        have "F3' = (top1_S2 - ((e12 \<union> e41) \<union> e24)) \<inter> F3'" using hF3_props(3) by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hF3_props(6) by (by100 blast)
      qed
      have "F3' \<noteq> {}" using hC'_in_F3' hC'_int_ne by (by100 blast)
      have hsep: "top1_is_separation_on (top1_S2 - ((e12 \<union> e41) \<union> e24))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))) F3 F3'"
        unfolding top1_is_separation_on_def
        using hF3_oT hF3'_oT hF3_props(1) \<open>F3' \<noteq> {}\<close> hF3_props(4,3) by (by100 blast)
      have hP1_conn_AB': "top1_connected_on P1 (subspace_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))) P1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology P1 =
            subspace_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))) P1"
          using subspace_topology_trans[of P1 "top1_S2 - ((e12 \<union> e41) \<union> e24)" top1_S2 top1_S2_topology]
              hP1_sub_AB' by (by100 simp)
        thus ?thesis using hP(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hT_AB' hsep hP1_sub_AB' hP1_conn_AB'] show ?thesis by (by100 blast)
    qed
    hence hP1_in_F3': "P1 \<subseteq> F3'"
    proof
      assume "P1 \<subseteq> F3"
      hence "closure_on top1_S2 top1_S2_topology P1 \<subseteq> closure_on top1_S2 top1_S2_topology F3"
        by (rule closure_on_mono)
      have "a3 \<in> closure_on top1_S2 top1_S2_topology P1"
        using hcl_P1 ha3_e34_loc assms(25) by (by100 blast)
      hence "a3 \<in> closure_on top1_S2 top1_S2_topology F3"
        using \<open>closure_on top1_S2 top1_S2_topology P1 \<subseteq> closure_on top1_S2 top1_S2_topology F3\<close>
        by (by100 blast)
      thus ?thesis using ha3_not_cl_F3 by (by100 blast)
    next
      assume "P1 \<subseteq> F3'" thus ?thesis .
    qed
    hence hF3_not_P1: "F3 \<inter> P1 = {}" using hF3_props(4) by (by100 blast)
    \<comment> \<open>Similarly R1 \<subseteq> F3' (same argument: a3 \<in> cl(R1) but a3 \<notin> cl(F3)).\<close>
    have hR1_sub_AB': "R1 \<subseteq> top1_S2 - ((e12 \<union> e41) \<union> e24)"
    proof -
      have "R1 \<inter> e12 = {}" using hR(4) hfour_union by (by100 blast)
      have "R1 \<inter> e41 = {}" using hR(4) hfour_union by (by100 blast)
      have "R1 \<inter> e24 = {}" using hR(4) hfour_union by (by100 blast)
      have "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      thus ?thesis using \<open>R1 \<inter> e12 = {}\<close> \<open>R1 \<inter> e41 = {}\<close> \<open>R1 \<inter> e24 = {}\<close> by (by100 blast)
    qed
    have "R1 \<subseteq> F3 \<or> R1 \<subseteq> F3'"
    proof -
      have hT_AB': "is_topology_on (top1_S2 - ((e12 \<union> e41) \<union> e24))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24)))"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
      have hF3_oT: "F3 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))"
      proof -
        have "F3 = (top1_S2 - ((e12 \<union> e41) \<union> e24)) \<inter> F3" using hF3_props(3) by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hF3_props(2) by (by100 blast)
      qed
      have hF3'_oT: "F3' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))"
      proof -
        have "F3' = (top1_S2 - ((e12 \<union> e41) \<union> e24)) \<inter> F3'" using hF3_props(3) by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hF3_props(6) by (by100 blast)
      qed
      have "F3' \<noteq> {}" using hC'_in_F3' hC'_int_ne by (by100 blast)
      have hsep: "top1_is_separation_on (top1_S2 - ((e12 \<union> e41) \<union> e24))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))) F3 F3'"
        unfolding top1_is_separation_on_def
        using hF3_oT hF3'_oT hF3_props(1) \<open>F3' \<noteq> {}\<close> hF3_props(4,3) by (by100 blast)
      have hR1_conn_AB': "top1_connected_on R1 (subspace_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))) R1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology R1 =
            subspace_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))) R1"
          using subspace_topology_trans[of R1 "top1_S2 - ((e12 \<union> e41) \<union> e24)" top1_S2 top1_S2_topology]
              hR1_sub_AB' by (by100 simp)
        thus ?thesis using hR(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hT_AB' hsep hR1_sub_AB' hR1_conn_AB'] show ?thesis by (by100 blast)
    qed
    hence "R1 \<subseteq> F3'"
    proof
      assume "R1 \<subseteq> F3"
      hence "closure_on top1_S2 top1_S2_topology R1 \<subseteq> closure_on top1_S2 top1_S2_topology F3"
        by (rule closure_on_mono)
      have "a3 \<in> closure_on top1_S2 top1_S2_topology R1"
        using hcl_R1 ha3_e34_loc assms(29,30) by (by100 blast)
      hence "a3 \<in> closure_on top1_S2 top1_S2_topology F3"
        using \<open>closure_on top1_S2 top1_S2_topology R1 \<subseteq> closure_on top1_S2 top1_S2_topology F3\<close>
        by (by100 blast)
      thus ?thesis using ha3_not_cl_F3 by (by100 blast)
    next
      assume "R1 \<subseteq> F3'" thus ?thesis .
    qed
    hence hF3_not_R1: "F3 \<inter> R1 = {}" using hF3_props(4) by (by100 blast)
    \<comment> \<open>F3 \<subseteq> S2-X, F3 \<inter> P1 = {}, F3 \<inter> R1 = {} \<Rightarrow> F3 \<subseteq> W1 \<union> W2.\<close>
    have "F3 \<subseteq> W1 \<union> W2"
    proof -
      have "F3 \<subseteq> P1 \<union> R1 \<union> W1 \<union> W2" using hF3_sub_SX hfour_union by (by100 blast)
      thus ?thesis using hF3_not_P1 hF3_not_R1 by (by100 blast)
    qed
    \<comment> \<open>F3 connected, W1 and W2 open disjoint: F3 in one of them.\<close>
    moreover have "F3 \<noteq> {}" by (rule hF3_props(1))
    ultimately have "F3 \<subseteq> W1 \<or> F3 \<subseteq> W2"
    proof -
      assume hF3_sub_WW: "F3 \<subseteq> W1 \<union> W2" and hF3_ne: "F3 \<noteq> {}"
      have hF3_sub_C1e24: "F3 \<subseteq> top1_S2 - (?C1 \<union> e24)"
        using hF3_sub_WW hW(4) by (by100 blast)
      have hT_C1: "is_topology_on (top1_S2 - (?C1 \<union> e24))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?C1 \<union> e24)))"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
      have hW1_oT: "W1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?C1 \<union> e24))"
      proof -
        have "W1 = (top1_S2 - (?C1 \<union> e24)) \<inter> W1" using hW(4) by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hW1_open by (by100 blast)
      qed
      have hW2_oT: "W2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?C1 \<union> e24))"
      proof -
        have "W2 = (top1_S2 - (?C1 \<union> e24)) \<inter> W2" using hW(4) by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hW2_open by (by100 blast)
      qed
      have hsep_W: "top1_is_separation_on (top1_S2 - (?C1 \<union> e24))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?C1 \<union> e24))) W1 W2"
        unfolding top1_is_separation_on_def
        using hW1_oT hW2_oT hW(1,2,3,4) by (by100 blast)
      have hF3_conn_C1: "top1_connected_on F3 (subspace_topology (top1_S2 - (?C1 \<union> e24))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?C1 \<union> e24))) F3)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology F3 =
            subspace_topology (top1_S2 - (?C1 \<union> e24))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?C1 \<union> e24))) F3"
          using subspace_topology_trans[of F3 "top1_S2 - (?C1 \<union> e24)" top1_S2 top1_S2_topology]
              hF3_sub_C1e24 by (by100 simp)
        thus ?thesis using hF3_props(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hT_C1 hsep_W hF3_sub_C1e24 hF3_conn_C1] show ?thesis by (by100 blast)
    qed
    \<comment> \<open>F3 \<subseteq> Wi \<Rightarrow> F3 = Wi: W1 \<subseteq> S2-(C1\<union>e24) \<subseteq> S2-(A'\<union>B') = F3\<union>F3'.
       W1 connected \<Rightarrow> W1 \<subseteq> F3 or F3'. If W1 \<subseteq> F3: F3 = W1. If W1 \<subseteq> F3': F3\<inter>W1={}, contradicting F3 \<subseteq> W1, F3\<noteq>{}.\<close>
    moreover have "\<And>Wi. Wi \<in> {W1,W2} \<Longrightarrow> F3 \<subseteq> Wi \<Longrightarrow> F3 = Wi"
    proof -
      fix Wi assume hWi: "Wi \<in> {W1,W2}" and hF3_Wi: "F3 \<subseteq> Wi"
      have hWi_sub: "Wi \<subseteq> top1_S2 - (?C1 \<union> e24)"
        using hWi hW(4) by (by100 blast)
      have "?C1 \<union> e24 \<supseteq> (e12 \<union> e41) \<union> e24" using hC1_eq by (by100 blast)
      hence "Wi \<subseteq> top1_S2 - ((e12 \<union> e41) \<union> e24)" using hWi_sub by (by100 blast)
      hence "Wi \<subseteq> F3 \<union> F3'" using hF3_props(3) by (by100 blast)
      have hWi_conn: "top1_connected_on Wi (subspace_topology top1_S2 top1_S2_topology Wi)"
        using hWi hW(5,6) by (by100 blast)
      have "Wi \<subseteq> F3 \<or> Wi \<subseteq> F3'"
      proof -
        have hT_AB': "is_topology_on (top1_S2 - ((e12 \<union> e41) \<union> e24))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24)))"
          by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
        have hF3_oT: "F3 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))"
        proof -
          have "F3 = (top1_S2 - ((e12 \<union> e41) \<union> e24)) \<inter> F3" using hF3_props(3) by (by100 blast)
          thus ?thesis unfolding subspace_topology_def using hF3_props(2) by (by100 blast)
        qed
        have hF3'_oT: "F3' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))"
        proof -
          have "F3' = (top1_S2 - ((e12 \<union> e41) \<union> e24)) \<inter> F3'" using hF3_props(3) by (by100 blast)
          thus ?thesis unfolding subspace_topology_def using hF3_props(6) by (by100 blast)
        qed
        have "F3' \<noteq> {}" using hC'_in_F3' hC'_int_ne by (by100 blast)
        have hsep: "top1_is_separation_on (top1_S2 - ((e12 \<union> e41) \<union> e24))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))) F3 F3'"
          unfolding top1_is_separation_on_def
          using hF3_oT hF3'_oT hF3_props(1) \<open>F3' \<noteq> {}\<close> hF3_props(4,3) by (by100 blast)
        have hWi_conn_AB': "top1_connected_on Wi (subspace_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))) Wi)"
        proof -
          have "subspace_topology top1_S2 top1_S2_topology Wi =
              subspace_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - ((e12 \<union> e41) \<union> e24))) Wi"
            using subspace_topology_trans[of Wi "top1_S2 - ((e12 \<union> e41) \<union> e24)" top1_S2 top1_S2_topology]
                \<open>Wi \<subseteq> top1_S2 - ((e12 \<union> e41) \<union> e24)\<close> by (by100 simp)
          thus ?thesis using hWi_conn by (by100 simp)
        qed
        from Lemma_23_2[OF hT_AB' hsep \<open>Wi \<subseteq> top1_S2 - ((e12 \<union> e41) \<union> e24)\<close> hWi_conn_AB']
        show ?thesis by (by100 blast)
      qed
      thus "F3 = Wi"
      proof
        assume "Wi \<subseteq> F3" thus ?thesis using hF3_Wi by (by100 blast)
      next
        assume "Wi \<subseteq> F3'" hence "F3 \<inter> Wi = {}" using hF3_props(4) by (by100 blast)
        hence "F3 = {}" using hF3_Wi by (by100 blast)
        thus ?thesis using hF3_props(1) by (by100 blast)
      qed
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>Step 4b (symmetric): JCT component F1 of S2-(B'\<union>C') = S2-(e24\<union>(e23\<union>e34)) with a1 \<notin> closure.
     Exact symmetric copy of F3 construction. B'\<union>C' is SCC. Place A'-{a2,a4} in one component.\<close>
  have hB'C'_scc: "top1_simple_closed_curve_on top1_S2 top1_S2_topology (e24 \<union> (e23 \<union> e34))"
    by (rule arcs_form_simple_closed_curve[OF hS2_strict hS2_haus assms(15) assms(9)
        hC'_arc hC'_sub hB'C' hdist(5) assms(21) hC'_ep])
  have hB'C'_sep: "top1_separates_on top1_S2 top1_S2_topology (e24 \<union> (e23 \<union> e34))"
    by (rule Theorem_61_3_JordanSeparation_S2[OF assms(1) hB'C'_scc])
  have hC'_closed: "closedin_on top1_S2 top1_S2_topology (e23 \<union> e34)"
    by (rule closedin_on_Un[OF hTopS2 arc_in_S2_closed[OF assms(5) assms(11)] arc_in_S2_closed[OF assms(6) assms(12)]])
  have hB'C'_card: "card (e24 \<inter> (e23 \<union> e34)) = 2" using hB'C' hdist(5) by (by100 simp)
  obtain H1 H2 where hH: "H1 \<noteq> {}" "H2 \<noteq> {}" "H1 \<inter> H2 = {}"
      "H1 \<union> H2 = top1_S2 - (e24 \<union> (e23 \<union> e34))"
      "top1_connected_on H1 (subspace_topology top1_S2 top1_S2_topology H1)"
      "top1_connected_on H2 (subspace_topology top1_S2 top1_S2_topology H2)"
    using Theorem_63_5_two_closed_connected[OF assms(1)
        arc_in_S2_closed[OF assms(9) assms(15)] hC'_closed
        arc_connected[OF assms(15)] arc_connected[OF hC'_arc] hB'C'_card
        Theorem_63_2_arc_no_separation[OF assms(1) assms(9) assms(15)]
        Theorem_63_2_arc_no_separation[OF assms(1) hC'_sub hC'_arc]]
    by (by100 metis)
  have hB'C'_open: "top1_S2 - (e24 \<union> (e23 \<union> e34)) \<in> top1_S2_topology"
    using closedin_on_Un[OF hTopS2 arc_in_S2_closed[OF assms(9) assms(15)] hC'_closed]
    hTopS2 unfolding closedin_on_def is_topology_on_def by (by100 blast)
  have hB'C'_nc: "\<not> top1_connected_on (top1_S2 - (e24 \<union> (e23 \<union> e34)))
      (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34))))"
    using hB'C'_sep unfolding top1_separates_on_def by (by100 blast)
  have hH_open: "H1 \<in> top1_S2_topology" "H2 \<in> top1_S2_topology"
    using S2_two_component_open[OF hB'C'_open _ hH(1,2,3,4,5,6) hB'C'_nc] by (by100 blast)+
  \<comment> \<open>Place A'int = (e12\<union>e41)-{a2,a4}.\<close>
  have hA'_int_conn: "top1_connected_on ((e12 \<union> e41) - {a2, a4})
      (subspace_topology top1_S2 top1_S2_topology ((e12 \<union> e41) - {a2, a4}))"
    by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus hA'_sub hA'_arc hA'_ep hdist(5)])
  have hA'_int_in_SCC: "(e12 \<union> e41) - {a2, a4} \<subseteq> top1_S2 - (e24 \<union> (e23 \<union> e34))"
  proof -
    have "(e12 \<union> e41) \<inter> (e24 \<union> (e23 \<union> e34)) \<subseteq> {a2, a4}"
    proof -
      have "(e12 \<union> e41) \<inter> (e24 \<union> (e23 \<union> e34)) = (e12\<inter>e24) \<union> (e12\<inter>e23) \<union> (e12\<inter>e34)
          \<union> (e41\<inter>e24) \<union> (e41\<inter>e23) \<union> (e41\<inter>e34)" by (by100 blast)
      also have "\<dots> \<subseteq> {a2} \<union> {a2} \<union> {} \<union> {a4} \<union> {} \<union> {a4}"
        using assms(33) assms(24) assms(22) assms(36) assms(23) assms(26)
        apply (simp add: Int_commute) done
      finally show ?thesis by (by100 blast)
    qed
    thus ?thesis using hA'_sub by (by100 blast)
  qed
  have hA'_int_ne: "(e12 \<union> e41) - {a2, a4} \<noteq> {}"
  proof -
    have "a2 \<in> closure_on top1_S2 top1_S2_topology ((e12 \<union> e41) - {a2, a4})"
      by (rule arc_endpoint_in_closure_of_interior(1)[OF hS2_strict hS2_haus hA'_sub hA'_arc hA'_ep hdist(5)])
    moreover have "closure_on top1_S2 top1_S2_topology {} = {}"
      by (rule top1_closure_on_empty[OF hTopS2])
    ultimately show ?thesis by (by100 force)
  qed
  \<comment> \<open>Choose F1 = JCT component NOT containing A'int. F1' = the other.\<close>
  have hA'_in_H: "(e12 \<union> e41) - {a2, a4} \<subseteq> H1 \<or> (e12 \<union> e41) - {a2, a4} \<subseteq> H2"
  proof -
    have hT_BC': "is_topology_on (top1_S2 - (e24 \<union> (e23 \<union> e34)))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34))))"
      by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
    have hH1_oT: "H1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))"
    proof -
      have "H1 = (top1_S2 - (e24 \<union> (e23 \<union> e34))) \<inter> H1" using hH(4) by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hH_open(1) by (by100 blast)
    qed
    have hH2_oT: "H2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))"
    proof -
      have "H2 = (top1_S2 - (e24 \<union> (e23 \<union> e34))) \<inter> H2" using hH(4) by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hH_open(2) by (by100 blast)
    qed
    have hsep: "top1_is_separation_on (top1_S2 - (e24 \<union> (e23 \<union> e34)))
        (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))) H1 H2"
      unfolding top1_is_separation_on_def using hH1_oT hH2_oT hH(1,2,3,4) by (by100 blast)
    have hA'_conn_BC': "top1_connected_on ((e12 \<union> e41) - {a2, a4})
        (subspace_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34))))
            ((e12 \<union> e41) - {a2, a4}))"
    proof -
      have "subspace_topology top1_S2 top1_S2_topology ((e12 \<union> e41) - {a2, a4}) =
          subspace_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))
              (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34))))
              ((e12 \<union> e41) - {a2, a4})"
        using subspace_topology_trans[of "(e12 \<union> e41) - {a2, a4}" "top1_S2 - (e24 \<union> (e23 \<union> e34))"
            top1_S2 top1_S2_topology] hA'_int_in_SCC by (by100 simp)
      thus ?thesis using hA'_int_conn by (by100 simp)
    qed
    from Lemma_23_2[OF hT_BC' hsep hA'_int_in_SCC hA'_conn_BC'] show ?thesis by (by100 blast)
  qed
  obtain F1 F1' where hF1_props: "F1 \<noteq> {}" "F1 \<in> top1_S2_topology"
      "F1 \<union> F1' = top1_S2 - (e24 \<union> (e23 \<union> e34))" "F1 \<inter> F1' = {}"
      "top1_connected_on F1 (subspace_topology top1_S2 top1_S2_topology F1)"
      "F1' \<in> top1_S2_topology"
      "top1_connected_on F1' (subspace_topology top1_S2 top1_S2_topology F1')"
      and hA'_in_F1': "(e12 \<union> e41) - {a2, a4} \<subseteq> F1'"
  proof -
    from hA'_in_H show ?thesis
    proof
      assume h: "(e12 \<union> e41) - {a2, a4} \<subseteq> H1"
      show ?thesis
        apply (rule that[of H2 H1])
        using hH(1,2,3,4,5,6) hH_open h apply (by100 blast)+
        done
    next
      assume h: "(e12 \<union> e41) - {a2, a4} \<subseteq> H2"
      show ?thesis
        apply (rule that[of H1 H2])
        using hH(1,2,3,4,5,6) hH_open h apply (by100 blast)+
        done
    qed
  qed
  \<comment> \<open>Closure bound: cl(F1) \<subseteq> F1 \<union> (B'\<union>C').\<close>
  have hF1'_sub: "F1' \<subseteq> top1_S2" using hF1_props(3) by (by100 blast)
  have hcl_F1: "closedin_on top1_S2 top1_S2_topology (top1_S2 - F1')"
  proof -
    have "top1_S2 - (top1_S2 - F1') = F1'" using hF1'_sub by (by100 blast)
    hence "top1_S2 - (top1_S2 - F1') \<in> top1_S2_topology" using hF1_props(6) by (by100 simp)
    thus ?thesis unfolding closedin_on_def by (by100 blast)
  qed
  have "F1 \<subseteq> top1_S2 - F1'" using hF1_props(3,4) by (by100 blast)
  have hcl_F1_bound: "closure_on top1_S2 top1_S2_topology F1 \<subseteq> F1 \<union> (e24 \<union> (e23 \<union> e34))"
  proof -
    have "closure_on top1_S2 top1_S2_topology F1 \<subseteq> top1_S2 - F1'"
      by (rule closure_on_subset_of_closed[OF hcl_F1 \<open>F1 \<subseteq> top1_S2 - F1'\<close>])
    thus ?thesis using hF1_props(3) by (by100 blast)
  qed
  \<comment> \<open>a1 \<notin> closure(F1).\<close>
  have ha1_not_B'C': "a1 \<notin> e24 \<union> (e23 \<union> e34)"
  proof -
    have "a1 \<notin> e24" proof assume "a1 \<in> e24"
      hence "a1 \<in> e12 \<inter> e24" using ha1_e12_loc by (by100 blast)
      thus False using assms(33) hdist(1) by (by100 blast) qed
    have "a1 \<notin> e23" proof assume "a1 \<in> e23"
      hence "a1 \<in> e12 \<inter> e23" using ha1_e12_loc by (by100 blast)
      thus False using assms(24) hdist(1) by (by100 blast) qed
    have "a1 \<notin> e34" using assms(22) ha1_e12_loc by (by100 blast)
    thus ?thesis using \<open>a1 \<notin> e24\<close> \<open>a1 \<notin> e23\<close> \<open>a1 \<notin> e34\<close> by (by100 blast)
  qed
  have "a1 \<in> (e12 \<union> e41) - {a2, a4}"
    using ha1_e12_loc hdist(1) hdist(3) by (by100 blast)
  hence "a1 \<in> F1'" using hA'_in_F1' by (by100 blast)
  hence "a1 \<notin> F1" using hF1_props(4) by (by100 blast)
  hence ha1_not_cl_F1: "a1 \<notin> closure_on top1_S2 top1_S2_topology F1"
    using hcl_F1_bound ha1_not_B'C' by (by100 blast)
  \<comment> \<open>F1 \<in> {W1, W2}: same argument as F3 (e13\<inter>F1={}, P1\<subseteq>F1', R1\<subseteq>F1', F1\<subseteq>W1\<union>W2).\<close>
  have hF1_in_WW: "F1 \<in> {W1, W2}"
  proof -
    \<comment> \<open>e13 \<inter> F1 = {}: same argument as F3. a1 \<in> cl(e13-{a1,a3}) \<subseteq> cl(F1) if e13 meets F1.\<close>
    have he13_disj_F1: "e13 \<inter> F1 = {}"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain z where "z \<in> e13" "z \<in> F1" by (by100 force)
      have hF1_sub_BC: "F1 \<subseteq> top1_S2 - (e24 \<union> (e23 \<union> e34))" using hF1_props(3) by (by100 blast)
      have "z \<notin> e24 \<union> (e23 \<union> e34)" using \<open>z \<in> F1\<close> hF1_sub_BC by (by100 blast)
      have "z \<noteq> a2"
      proof -
        have "a2 \<in> e23" using arc_endpoints_subset[of e23] assms(17) by (by100 blast)
        thus ?thesis using \<open>z \<notin> e24 \<union> (e23 \<union> e34)\<close> by (by100 blast)
      qed
      have "z \<noteq> a4"
      proof -
        have "a4 \<in> e34" using arc_endpoints_subset[of e34] assms(18) by (by100 blast)
        thus ?thesis using \<open>z \<notin> e24 \<union> (e23 \<union> e34)\<close> by (by100 blast)
      qed
      have "z \<noteq> a1" using \<open>z \<in> F1\<close> \<open>a1 \<notin> F1\<close> by (by100 blast)
      have "z \<noteq> a3"
      proof assume "z = a3"
        hence "a3 \<in> F1" using \<open>z \<in> F1\<close> by (by100 simp)
        hence "a3 \<in> top1_S2 - (e24 \<union> (e23 \<union> e34))" using hF1_props(3) by (by100 blast)
        thus False using ha3_e34_loc by (by100 blast)
      qed
      hence "z \<in> e13 - {a1, a3}" using \<open>z \<in> e13\<close> \<open>z \<noteq> a1\<close> \<open>z \<noteq> a3\<close> by (by100 blast)
      have he13_conn: "top1_connected_on (e13 - {a1, a3})
          (subspace_topology top1_S2 top1_S2_topology (e13 - {a1, a3}))"
        by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus assms(8) assms(14) assms(20) hdist(2)])
      have he13_sub_BC: "e13 - {a1, a3} \<subseteq> top1_S2 - (e24 \<union> (e23 \<union> e34))"
      proof -
        have "e13 \<inter> e24 = {}"
        proof -
          have "a1 \<notin> e24" using ha1_not_B'C' by (by100 blast)
          have "a3 \<notin> e24" using ha3_not_A'B' by (by100 blast)
          have "a2 \<notin> e13" proof assume "a2 \<in> e13"
            hence "a2 \<in> e13 \<inter> e23" using assms(17) unfolding top1_arc_endpoints_on_def by (by100 blast)
            thus False using assms(29) hdist(4) by (by100 blast) qed
          have "a4 \<notin> e13" proof assume "a4 \<in> e13"
            hence "a4 \<in> e13 \<inter> e41" using assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
            hence "a4 \<in> {a1}" using assms(31) by (by100 blast)
            thus False using hdist(3) by (by100 simp) qed
          have "\<forall>x \<in> {a1,a2,a3,a4}. x \<notin> e24 \<inter> e13"
            using \<open>a1 \<notin> e24\<close> \<open>a3 \<notin> e24\<close> \<open>a2 \<notin> e13\<close> \<open>a4 \<notin> e13\<close> by (by100 blast)
          thus ?thesis using assms(32) by (by100 blast)
        qed
        have "e13 \<inter> e23 = {a3}" by (rule assms(29))
        have "e13 \<inter> e34 = {a3}" by (rule assms(30))
        have "e13 \<inter> (e24 \<union> (e23 \<union> e34)) \<subseteq> {a3}"
          using \<open>e13 \<inter> e24 = {}\<close> \<open>e13 \<inter> e23 = {a3}\<close> \<open>e13 \<inter> e34 = {a3}\<close> by (by100 blast)
        thus ?thesis using assms(8) by (by100 blast)
      qed
      \<comment> \<open>e13-{a1,a3} connected, in S2-(B'\<union>C'), meets F1 \<Rightarrow> \<subseteq> F1 (by separation).\<close>
      have "e13 - {a1, a3} \<subseteq> F1"
      proof -
        have hT_BC': "is_topology_on (top1_S2 - (e24 \<union> (e23 \<union> e34)))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34))))"
          by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
        have hF1_oT: "F1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))"
        proof -
          have "F1 = (top1_S2 - (e24 \<union> (e23 \<union> e34))) \<inter> F1" using hF1_props(3) by (by100 blast)
          thus ?thesis unfolding subspace_topology_def using hF1_props(2) by (by100 blast)
        qed
        have hF1'_oT: "F1' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))"
        proof -
          have "F1' = (top1_S2 - (e24 \<union> (e23 \<union> e34))) \<inter> F1'" using hF1_props(3) by (by100 blast)
          thus ?thesis unfolding subspace_topology_def using hF1_props(6) by (by100 blast)
        qed
        have "F1' \<noteq> {}" using hA'_in_F1' hA'_int_ne by (by100 blast)
        have hsep: "top1_is_separation_on (top1_S2 - (e24 \<union> (e23 \<union> e34)))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))) F1 F1'"
        proof -
          show ?thesis unfolding top1_is_separation_on_def
            using hF1_oT hF1'_oT hF1_props(1) \<open>F1' \<noteq> {}\<close> hF1_props(4,3) by (by100 blast)
        qed
        have he13_conn_BC': "top1_connected_on (e13 - {a1, a3})
            (subspace_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))) (e13 - {a1, a3}))"
        proof -
          have "subspace_topology top1_S2 top1_S2_topology (e13 - {a1, a3}) =
              subspace_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))) (e13 - {a1, a3})"
            using subspace_topology_trans[of "e13-{a1,a3}" "top1_S2 - (e24 \<union> (e23 \<union> e34))"
                top1_S2 top1_S2_topology] he13_sub_BC by (by100 simp)
          thus ?thesis using he13_conn by (by100 simp)
        qed
        from Lemma_23_2[OF hT_BC' hsep he13_sub_BC he13_conn_BC']
        have "e13 - {a1,a3} \<subseteq> F1 \<or> e13 - {a1,a3} \<subseteq> F1'" by (by100 blast)
        thus ?thesis
        proof
          assume "e13 - {a1,a3} \<subseteq> F1" thus ?thesis .
        next
          assume h_sub_F1': "e13 - {a1,a3} \<subseteq> F1'"
          have "\<forall>x. x \<in> e13 - {a1,a3} \<longrightarrow> x \<notin> F1"
          proof (intro allI impI)
            fix x assume "x \<in> e13 - {a1,a3}"
            hence "x \<in> F1'" using h_sub_F1' by (by100 blast)
            thus "x \<notin> F1" using hF1_props(4) by (by100 blast)
          qed
          have "(e13 - {a1,a3}) \<inter> F1 = {}"
            apply (rule Int_emptyI)
            using \<open>\<forall>x. x \<in> e13 - {a1,a3} \<longrightarrow> x \<notin> F1\<close> apply (by100 simp) done
          hence False using \<open>z \<in> e13 - {a1, a3}\<close> \<open>z \<in> F1\<close> by (by100 blast)
          thus ?thesis ..
        qed
      qed
      hence "a1 \<in> closure_on top1_S2 top1_S2_topology F1"
        using closure_on_mono[of "e13 - {a1,a3}" F1 top1_S2 top1_S2_topology]
            arc_endpoint_in_closure_of_interior(1)[OF hS2_strict hS2_haus assms(8) assms(14) assms(20) hdist(2)]
        by (by100 blast)
      thus False using ha1_not_cl_F1 by (by100 blast)
    qed
    \<comment> \<open>F1 \<subseteq> S2-X.\<close>
    have hF1_sub_SX: "F1 \<subseteq> top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e41 \<union> e13 \<union> e24)"
    proof
      fix x assume "x \<in> F1"
      hence "x \<in> top1_S2 - (e24 \<union> (e23 \<union> e34))" using hF1_props(3) by (by100 blast)
      hence "x \<notin> e24" "x \<notin> e23" "x \<notin> e34" "x \<in> top1_S2" by (by100 blast)+
      have "x \<notin> e13" using \<open>x \<in> F1\<close> he13_disj_F1 by (by100 blast)
      have "x \<notin> e12 \<and> x \<notin> e41"
      proof -
        have "(e12 \<union> e41) - {a2,a4} \<subseteq> F1'" by (rule hA'_in_F1')
        have "x \<notin> (e12 \<union> e41) - {a2,a4}" using \<open>x \<in> F1\<close> hF1_props(4)
          \<open>(e12 \<union> e41) - {a2,a4} \<subseteq> F1'\<close> by (by100 blast)
        moreover have "x \<notin> {a2, a4}" using \<open>x \<notin> e24\<close> \<open>x \<notin> e23\<close> \<open>x \<notin> e34\<close>
          arc_endpoints_subset[of e24] arc_endpoints_subset[of e23] arc_endpoints_subset[of e34]
          assms(21) assms(17) assms(18) by (by100 blast)
        ultimately show ?thesis by (by100 blast)
      qed
      show "x \<in> top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e41 \<union> e13 \<union> e24)"
        using \<open>x \<in> top1_S2\<close> \<open>x \<notin> e24\<close> \<open>x \<notin> e23\<close> \<open>x \<notin> e34\<close> \<open>x \<notin> e13\<close> \<open>x \<notin> e12 \<and> x \<notin> e41\<close>
        by (by100 blast)
    qed
    \<comment> \<open>P1, R1 \<subseteq> F1' (a1 \<in> cl(P1), cl(R1) but a1 \<notin> cl(F1)).\<close>
    have hP1_sub_BC': "P1 \<subseteq> top1_S2 - (e24 \<union> (e23 \<union> e34))"
    proof -
      have "P1 \<inter> e24 = {}" "P1 \<inter> e23 = {}" "P1 \<inter> e34 = {}" using hP(4) hfour_union by (by100 blast)+
      have "P1 \<subseteq> top1_S2" using hP(4) by (by100 blast)
      thus ?thesis using \<open>P1 \<inter> e24 = {}\<close> \<open>P1 \<inter> e23 = {}\<close> \<open>P1 \<inter> e34 = {}\<close> by (by100 blast)
    qed
    have "P1 \<subseteq> F1 \<or> P1 \<subseteq> F1'"
    proof -
      have hT_BC': "is_topology_on (top1_S2 - (e24 \<union> (e23 \<union> e34)))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34))))"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
      have hF1_oT: "F1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))"
      proof -
        have "F1 = (top1_S2 - (e24 \<union> (e23 \<union> e34))) \<inter> F1" using hF1_props(3) by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hF1_props(2) by (by100 blast)
      qed
      have hF1'_oT: "F1' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))"
      proof -
        have "F1' = (top1_S2 - (e24 \<union> (e23 \<union> e34))) \<inter> F1'" using hF1_props(3) by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hF1_props(6) by (by100 blast)
      qed
      have "F1' \<noteq> {}" using hA'_in_F1' hA'_int_ne by (by100 blast)
      have hsep: "top1_is_separation_on (top1_S2 - (e24 \<union> (e23 \<union> e34)))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))) F1 F1'"
        unfolding top1_is_separation_on_def
        using hF1_oT hF1'_oT hF1_props(1) \<open>F1' \<noteq> {}\<close> hF1_props(4,3) by (by100 blast)
      have hP1_conn_BC': "top1_connected_on P1 (subspace_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))) P1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology P1 =
            subspace_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))) P1"
          using subspace_topology_trans[of P1 "top1_S2 - (e24 \<union> (e23 \<union> e34))" top1_S2 top1_S2_topology]
              hP1_sub_BC' by (by100 simp)
        thus ?thesis using hP(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hT_BC' hsep hP1_sub_BC' hP1_conn_BC'] show ?thesis by (by100 blast)
    qed
    hence "P1 \<subseteq> F1'"
    proof
      assume "P1 \<subseteq> F1"
      hence "closure_on top1_S2 top1_S2_topology P1 \<subseteq> closure_on top1_S2 top1_S2_topology F1"
        by (rule closure_on_mono)
      have "a1 \<in> closure_on top1_S2 top1_S2_topology P1"
        using hcl_P1 ha1_e12_loc by (by100 blast)
      hence "a1 \<in> closure_on top1_S2 top1_S2_topology F1"
        using \<open>closure_on top1_S2 top1_S2_topology P1 \<subseteq> closure_on top1_S2 top1_S2_topology F1\<close>
        by (by100 blast)
      thus ?thesis using ha1_not_cl_F1 by (by100 blast)
    next
      assume "P1 \<subseteq> F1'" thus ?thesis .
    qed
    hence hF1_not_P1: "F1 \<inter> P1 = {}" using hF1_props(4) by (by100 blast)
    \<comment> \<open>R1 \<subseteq> F1' (same argument).\<close>
    have hR1_sub_BC': "R1 \<subseteq> top1_S2 - (e24 \<union> (e23 \<union> e34))"
    proof -
      have "R1 \<inter> e24 = {}" "R1 \<inter> e23 = {}" "R1 \<inter> e34 = {}" using hR(4) hfour_union by (by100 blast)+
      have "R1 \<subseteq> top1_S2" using hR(4) by (by100 blast)
      thus ?thesis using \<open>R1 \<inter> e24 = {}\<close> \<open>R1 \<inter> e23 = {}\<close> \<open>R1 \<inter> e34 = {}\<close> by (by100 blast)
    qed
    have "R1 \<subseteq> F1 \<or> R1 \<subseteq> F1'"
    proof -
      have hT_BC': "is_topology_on (top1_S2 - (e24 \<union> (e23 \<union> e34)))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34))))"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
      have hF1_oT: "F1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))"
      proof -
        have "F1 = (top1_S2 - (e24 \<union> (e23 \<union> e34))) \<inter> F1" using hF1_props(3) by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hF1_props(2) by (by100 blast)
      qed
      have hF1'_oT: "F1' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))"
      proof -
        have "F1' = (top1_S2 - (e24 \<union> (e23 \<union> e34))) \<inter> F1'" using hF1_props(3) by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hF1_props(6) by (by100 blast)
      qed
      have "F1' \<noteq> {}" using hA'_in_F1' hA'_int_ne by (by100 blast)
      have hsep: "top1_is_separation_on (top1_S2 - (e24 \<union> (e23 \<union> e34)))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))) F1 F1'"
        unfolding top1_is_separation_on_def
        using hF1_oT hF1'_oT hF1_props(1) \<open>F1' \<noteq> {}\<close> hF1_props(4,3) by (by100 blast)
      have hR1_conn_BC': "top1_connected_on R1 (subspace_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))) R1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology R1 =
            subspace_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))) R1"
          using subspace_topology_trans[of R1 "top1_S2 - (e24 \<union> (e23 \<union> e34))" top1_S2 top1_S2_topology]
              hR1_sub_BC' by (by100 simp)
        thus ?thesis using hR(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hT_BC' hsep hR1_sub_BC' hR1_conn_BC'] show ?thesis by (by100 blast)
    qed
    hence "R1 \<subseteq> F1'"
    proof
      assume "R1 \<subseteq> F1"
      hence "closure_on top1_S2 top1_S2_topology R1 \<subseteq> closure_on top1_S2 top1_S2_topology F1"
        by (rule closure_on_mono)
      have "a1 \<in> closure_on top1_S2 top1_S2_topology R1"
        using hcl_R1 assms(19) unfolding top1_arc_endpoints_on_def by (by100 blast)
      hence "a1 \<in> closure_on top1_S2 top1_S2_topology F1"
        using \<open>closure_on top1_S2 top1_S2_topology R1 \<subseteq> closure_on top1_S2 top1_S2_topology F1\<close>
        by (by100 blast)
      thus ?thesis using ha1_not_cl_F1 by (by100 blast)
    next
      assume "R1 \<subseteq> F1'" thus ?thesis .
    qed
    hence hF1_not_R1: "F1 \<inter> R1 = {}" using hF1_props(4) by (by100 blast)
    \<comment> \<open>F1 \<subseteq> W1\<union>W2, then in one of them.\<close>
    have "F1 \<subseteq> W1 \<union> W2"
    proof -
      have "F1 \<subseteq> P1 \<union> R1 \<union> W1 \<union> W2" using hF1_sub_SX hfour_union by (by100 blast)
      thus ?thesis using hF1_not_P1 hF1_not_R1 by (by100 blast)
    qed
    moreover have "F1 \<noteq> {}" by (rule hF1_props(1))
    ultimately have "F1 \<subseteq> W1 \<or> F1 \<subseteq> W2"
    proof -
      assume hF1_sub_WW: "F1 \<subseteq> W1 \<union> W2" and hF1_ne: "F1 \<noteq> {}"
      have hF1_sub_C1e24: "F1 \<subseteq> top1_S2 - (?C1 \<union> e24)" using hF1_sub_WW hW(4) by (by100 blast)
      have hT_C1: "is_topology_on (top1_S2 - (?C1 \<union> e24))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?C1 \<union> e24)))"
        by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
      have hW1_oT: "W1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?C1 \<union> e24))"
      proof -
        have "W1 = (top1_S2 - (?C1 \<union> e24)) \<inter> W1" using hW(4) by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hW1_open by (by100 blast)
      qed
      have hW2_oT: "W2 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?C1 \<union> e24))"
      proof -
        have "W2 = (top1_S2 - (?C1 \<union> e24)) \<inter> W2" using hW(4) by (by100 blast)
        thus ?thesis unfolding subspace_topology_def using hW2_open by (by100 blast)
      qed
      have hsep_W: "top1_is_separation_on (top1_S2 - (?C1 \<union> e24))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?C1 \<union> e24))) W1 W2"
        unfolding top1_is_separation_on_def using hW1_oT hW2_oT hW(1,2,3,4) by (by100 blast)
      have hF1_conn_C1: "top1_connected_on F1 (subspace_topology (top1_S2 - (?C1 \<union> e24))
          (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?C1 \<union> e24))) F1)"
      proof -
        have "subspace_topology top1_S2 top1_S2_topology F1 =
            subspace_topology (top1_S2 - (?C1 \<union> e24))
                (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (?C1 \<union> e24))) F1"
          using subspace_topology_trans[of F1 "top1_S2 - (?C1 \<union> e24)" top1_S2 top1_S2_topology]
              hF1_sub_C1e24 by (by100 simp)
        thus ?thesis using hF1_props(5) by (by100 simp)
      qed
      from Lemma_23_2[OF hT_C1 hsep_W hF1_sub_C1e24 hF1_conn_C1] show ?thesis by (by100 blast)
    qed
    \<comment> \<open>F1 = Wi (bidirectional subset).\<close>
    moreover have "\<And>Wi. Wi \<in> {W1,W2} \<Longrightarrow> F1 \<subseteq> Wi \<Longrightarrow> F1 = Wi"
    proof -
      fix Wi assume hWi: "Wi \<in> {W1,W2}" and hF1_Wi: "F1 \<subseteq> Wi"
      have hWi_sub: "Wi \<subseteq> top1_S2 - (?C1 \<union> e24)" using hWi hW(4) by (by100 blast)
      have "?C1 \<union> e24 \<supseteq> e24 \<union> (e23 \<union> e34)" using hC1_eq by (by100 blast)
      hence "Wi \<subseteq> top1_S2 - (e24 \<union> (e23 \<union> e34))" using hWi_sub by (by100 blast)
      hence "Wi \<subseteq> F1 \<union> F1'" using hF1_props(3) by (by100 blast)
      have hWi_conn: "top1_connected_on Wi (subspace_topology top1_S2 top1_S2_topology Wi)"
        using hWi hW(5,6) by (by100 blast)
      have "Wi \<subseteq> F1 \<or> Wi \<subseteq> F1'"
      proof -
        have hT_BC': "is_topology_on (top1_S2 - (e24 \<union> (e23 \<union> e34)))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34))))"
          by (rule subspace_topology_is_topology_on[OF hTopS2]) (by100 blast)
        have hF1_oT: "F1 \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))"
        proof -
          have "F1 = (top1_S2 - (e24 \<union> (e23 \<union> e34))) \<inter> F1" using hF1_props(3) by (by100 blast)
          thus ?thesis unfolding subspace_topology_def using hF1_props(2) by (by100 blast)
        qed
        have hF1'_oT: "F1' \<in> subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))"
        proof -
          have "F1' = (top1_S2 - (e24 \<union> (e23 \<union> e34))) \<inter> F1'" using hF1_props(3) by (by100 blast)
          thus ?thesis unfolding subspace_topology_def using hF1_props(6) by (by100 blast)
        qed
        have "F1' \<noteq> {}" using hA'_in_F1' hA'_int_ne by (by100 blast)
        have hsep: "top1_is_separation_on (top1_S2 - (e24 \<union> (e23 \<union> e34)))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))) F1 F1'"
          unfolding top1_is_separation_on_def
          using hF1_oT hF1'_oT hF1_props(1) \<open>F1' \<noteq> {}\<close> hF1_props(4,3) by (by100 blast)
        have hWi_conn_BC': "top1_connected_on Wi (subspace_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))
            (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))) Wi)"
        proof -
          have "subspace_topology top1_S2 top1_S2_topology Wi =
              subspace_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))
                  (subspace_topology top1_S2 top1_S2_topology (top1_S2 - (e24 \<union> (e23 \<union> e34)))) Wi"
            using subspace_topology_trans[of Wi "top1_S2 - (e24 \<union> (e23 \<union> e34))" top1_S2 top1_S2_topology]
                \<open>Wi \<subseteq> top1_S2 - (e24 \<union> (e23 \<union> e34))\<close> by (by100 simp)
          thus ?thesis using hWi_conn by (by100 simp)
        qed
        from Lemma_23_2[OF hT_BC' hsep \<open>Wi \<subseteq> top1_S2 - (e24 \<union> (e23 \<union> e34))\<close> hWi_conn_BC']
        show ?thesis by (by100 blast)
      qed
      thus "F1 = Wi"
      proof
        assume "Wi \<subseteq> F1" thus ?thesis using hF1_Wi by (by100 blast)
      next
        assume "Wi \<subseteq> F1'" hence "F1 \<inter> Wi = {}" using hF1_props(4) by (by100 blast)
        hence "F1 = {}" using hF1_Wi by (by100 blast)
        thus ?thesis using hF1_props(1) by (by100 blast)
      qed
    qed
    ultimately show ?thesis by (by100 blast)
  qed
  \<comment> \<open>F3 \<noteq> F1: a3 \<in> closure(F1) (from SCC boundary) but a3 \<notin> closure(F3).\<close>
  have hF3_ne_F1: "F3 \<noteq> F1"
  proof
    assume "F3 = F1"
    \<comment> \<open>a3 \<in> B'\<union>C' = e24\<union>(e23\<union>e34), specifically a3 \<in> e23\<union>e34.
       By SCC boundary property, a3 \<in> closure(F1).\<close>
    have "a3 \<in> e23 \<union> e34" using ha3_e34_loc assms(17)
      unfolding top1_arc_endpoints_on_def by (by100 blast)
    hence "a3 \<in> e24 \<union> (e23 \<union> e34)" by (by100 blast)
    \<comment> \<open>Every point of the SCC is in closure of each component (by boundary meets component lemma).\<close>
    have ha3_cl_F1: "a3 \<in> closure_on top1_S2 top1_S2_topology F1"
    proof (rule iffD2[OF Theorem_17_5a[OF hTopS2 _ _]])
      show "a3 \<in> top1_S2" using assms(3) by (by100 blast)
      have "F1 \<subseteq> top1_S2" using hF1_props(3) by (by100 blast)
      thus "F1 \<subseteq> top1_S2" .
      show "\<forall>U. neighborhood_of a3 top1_S2 top1_S2_topology U \<longrightarrow> intersects U F1"
      proof (intro allI impI)
        fix V assume hV: "neighborhood_of a3 top1_S2 top1_S2_topology V"
        have hV_open: "V \<in> top1_S2_topology" and ha3V: "a3 \<in> V"
          using hV unfolding neighborhood_of_def by (by100 blast)+
        have "V \<inter> F1 \<noteq> {}"
        proof -
          have "F1' \<noteq> {}" using hA'_in_F1' hA'_int_ne by (by100 blast)
          have hF1_conn2: "top1_connected_on F1' (subspace_topology top1_S2 top1_S2_topology F1')"
            by (rule hF1_props(7))
          show ?thesis
            by (rule simple_closed_curve_boundary_meets_component[OF assms(1) hB'C'_scc
                hF1_props(5) hF1_conn2 hF1_props(4,3) hF1_props(1) \<open>F1' \<noteq> {}\<close>
                hF1_props(2,6)
                \<open>a3 \<in> e24 \<union> (e23 \<union> e34)\<close> hV_open ha3V])
        qed
        thus "intersects V F1" unfolding intersects_def by (by100 blast)
      qed
    qed
    hence "a3 \<in> closure_on top1_S2 top1_S2_topology F3" using \<open>F3 = F1\<close> by (by100 simp)
    thus False using ha3_not_cl_F3 by (by100 blast)
  qed
  \<comment> \<open>Exact closure for F3: closure(F3) = F3 \<union> (e12\<union>e41\<union>e24) by SCC boundary-meets-component.\<close>
  have hcl_F3_sup: "(e12 \<union> e41) \<union> e24 \<subseteq> closure_on top1_S2 top1_S2_topology F3"
  proof
    fix z assume hz: "z \<in> (e12 \<union> e41) \<union> e24"
    have hz_S2: "z \<in> top1_S2" using hz hA'_sub assms(9) by (by100 blast)
    have hF3_sub_S2: "F3 \<subseteq> top1_S2" using hF3_props(3) by (by100 blast)
    show "z \<in> closure_on top1_S2 top1_S2_topology F3"
    proof (rule iffD2[OF Theorem_17_5a[OF hTopS2 hz_S2 hF3_sub_S2]])
      show "\<forall>U. neighborhood_of z top1_S2 top1_S2_topology U \<longrightarrow> intersects U F3"
      proof (intro allI impI)
        fix V assume hV: "neighborhood_of z top1_S2 top1_S2_topology V"
        have hV_open: "V \<in> top1_S2_topology" and hzV: "z \<in> V"
          using hV unfolding neighborhood_of_def by (by100 blast)+
        have "F3' \<noteq> {}" using hC'_in_F3' hC'_int_ne by (by100 blast)
        have "V \<inter> F3 \<noteq> {}"
          by (rule simple_closed_curve_boundary_meets_component[OF assms(1) hA'B'_scc
              hF3_props(5) hF3_props(7) hF3_props(4,3) hF3_props(1) \<open>F3' \<noteq> {}\<close>
              hF3_props(2,6) hz hV_open hzV])
        thus "intersects V F3" unfolding intersects_def by (by100 blast)
      qed
    qed
  qed
  have hcl_F3_exact: "closure_on top1_S2 top1_S2_topology F3 = F3 \<union> ((e12 \<union> e41) \<union> e24)"
    using hcl_F3_bound hcl_F3_sup subset_closure_on[of F3 top1_S2 top1_S2_topology]
    by (by100 blast)
  \<comment> \<open>Exact closure for F1: closure(F1) = F1 \<union> (e24\<union>(e23\<union>e34)).\<close>
  have hcl_F1_sup: "e24 \<union> (e23 \<union> e34) \<subseteq> closure_on top1_S2 top1_S2_topology F1"
  proof
    fix z assume hz: "z \<in> e24 \<union> (e23 \<union> e34)"
    have hz_S2: "z \<in> top1_S2" using hz assms(9) hC'_sub by (by100 blast)
    have hF1_sub_S2: "F1 \<subseteq> top1_S2" using hF1_props(3) by (by100 blast)
    show "z \<in> closure_on top1_S2 top1_S2_topology F1"
    proof (rule iffD2[OF Theorem_17_5a[OF hTopS2 hz_S2 hF1_sub_S2]])
      show "\<forall>U. neighborhood_of z top1_S2 top1_S2_topology U \<longrightarrow> intersects U F1"
      proof (intro allI impI)
        fix V assume hV: "neighborhood_of z top1_S2 top1_S2_topology V"
        have hV_open: "V \<in> top1_S2_topology" and hzV: "z \<in> V"
          using hV unfolding neighborhood_of_def by (by100 blast)+
        have "F1' \<noteq> {}" using hA'_in_F1' hA'_int_ne by (by100 blast)
        have "V \<inter> F1 \<noteq> {}"
          by (rule simple_closed_curve_boundary_meets_component[OF assms(1) hB'C'_scc
              hF1_props(5) hF1_props(7) hF1_props(4,3) hF1_props(1) \<open>F1' \<noteq> {}\<close>
              hF1_props(2,6) hz hV_open hzV])
        thus "intersects V F1" unfolding intersects_def by (by100 blast)
      qed
    qed
  qed
  have hcl_F1_exact: "closure_on top1_S2 top1_S2_topology F1 = F1 \<union> (e24 \<union> (e23 \<union> e34))"
    using hcl_F1_bound hcl_F1_sup subset_closure_on[of F1 top1_S2 top1_S2_topology]
    by (by100 blast)
  \<comment> \<open>Derive exact closures for W1, W2 from F3, F1 assignment.\<close>
  have hcl_W12: "(closure_on top1_S2 top1_S2_topology W1 = W1 \<union> (e12 \<union> e41 \<union> e24)
      \<and> closure_on top1_S2 top1_S2_topology W2 = W2 \<union> (e23 \<union> e34 \<union> e24))
    \<or> (closure_on top1_S2 top1_S2_topology W1 = W1 \<union> (e23 \<union> e34 \<union> e24)
      \<and> closure_on top1_S2 top1_S2_topology W2 = W2 \<union> (e12 \<union> e41 \<union> e24))"
  proof -
    from hF3_in_WW have "F3 = W1 \<or> F3 = W2" by (by100 blast)
    thus ?thesis
    proof
      assume "F3 = W1"
      hence "F1 = W2" using hF1_in_WW hF3_ne_F1 by (by100 blast)
      have "closure_on top1_S2 top1_S2_topology W1 = W1 \<union> ((e12 \<union> e41) \<union> e24)"
        using hcl_F3_exact \<open>F3 = W1\<close> by (by100 simp)
      moreover have "closure_on top1_S2 top1_S2_topology W2 = W2 \<union> (e24 \<union> (e23 \<union> e34))"
        using hcl_F1_exact \<open>F1 = W2\<close> by (by100 simp)
      ultimately show ?thesis by (by100 blast)
    next
      assume "F3 = W2"
      hence "F1 = W1" using hF1_in_WW hF3_ne_F1 by (by100 blast)
      have "closure_on top1_S2 top1_S2_topology W2 = W2 \<union> ((e12 \<union> e41) \<union> e24)"
        using hcl_F3_exact \<open>F3 = W2\<close> by (by100 simp)
      moreover have "closure_on top1_S2 top1_S2_topology W1 = W1 \<union> (e24 \<union> (e23 \<union> e34))"
        using hcl_F1_exact \<open>F1 = W1\<close> by (by100 simp)
      ultimately show ?thesis by (by100 blast)
    qed
  qed
  \<comment> \<open>Since F3, F1 \<in> {W1, W2} and F3 \<noteq> F1: {F3, F1} = {W1, W2}.\<close>
  \<comment> \<open>Conclude hbd\_W1 and hbd\_W2.\<close>
  have hbd_W1: "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology W1)"
  proof -
    from hF3_in_WW have "F3 = W1 \<or> F3 = W2" by (by100 blast)
    thus ?thesis
    proof
      assume "F3 = W1" thus ?thesis using ha3_not_cl_F3 by (by100 blast)
    next
      assume "F3 = W2"
      from hF1_in_WW have "F1 = W1 \<or> F1 = W2" by (by100 blast)
      thus ?thesis
      proof
        assume "F1 = W1" thus ?thesis using ha1_not_cl_F1 by (by100 blast)
      next
        assume "F1 = W2" hence "F3 = F1" using \<open>F3 = W2\<close> by (by100 simp)
        thus ?thesis using hF3_ne_F1 by (by100 blast)
      qed
    qed
  qed
  have hbd_W2: "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology W2)"
  proof -
    from hF3_in_WW have "F3 = W1 \<or> F3 = W2" by (by100 blast)
    thus ?thesis
    proof
      assume "F3 = W2" thus ?thesis using ha3_not_cl_F3 by (by100 blast)
    next
      assume "F3 = W1"
      from hF1_in_WW have "F1 = W1 \<or> F1 = W2" by (by100 blast)
      thus ?thesis
      proof
        assume "F1 = W2" thus ?thesis using ha1_not_cl_F1 by (by100 blast)
      next
        assume "F1 = W1" hence "F3 = F1" using \<open>F3 = W1\<close> by (by100 simp)
        thus ?thesis using hF3_ne_F1 by (by100 blast)
      qed
    qed
  qed  show ?thesis
    apply (rule exI[of _ P1])
    apply (rule exI[of _ R1])
    apply (rule exI[of _ W1])
    apply (rule exI[of _ W2])
    apply (intro conjI)
    apply (fact hP(1)) apply (fact hR(1)) apply (fact hW(1)) apply (fact hW(2))
    apply (fact hfour_disj(1)) apply (fact hfour_disj(2)) apply (fact hfour_disj(3))
    apply (fact hfour_disj(4)) apply (fact hfour_disj(5)) apply (fact hfour_disj(6))
    apply (fact hfour_union)
    apply (fact hP(5)) apply (fact hR(5)) apply (fact hW(5)) apply (fact hW(6))
    apply (fact hP1_open) apply (fact hR1_open) apply (fact hW1_open) apply (fact hW2_open)
    using hcl_P1 apply (by100 blast)
    using hcl_R1 apply (by100 blast)
    using hcl_W12 apply (by100 blast)
    done
qed

text \<open>Theorem 64.4 (K5 non-planarity). Assumptions ordered so K4-compatible ones come first.\<close>
theorem Theorem_64_4_K5_not_planar:
  assumes hS2: "is_topology_on_strict top1_S2 top1_S2_topology"
      and hcard5: "card {a1, a2, a3, a4, a5 :: real \<times> real \<times> real} = 5"
      and hvert: "{a1, a2, a3, a4, a5} \<subseteq> top1_S2"
      \<comment> \<open>K4-compatible subset of assumptions (matching K5\_K4\_sep exactly):\<close>
      and hsub12: "e12 \<subseteq> top1_S2" and hsub23: "e23 \<subseteq> top1_S2" and hsub34: "e34 \<subseteq> top1_S2"
      and hsub14: "e14 \<subseteq> top1_S2" and hsub13: "e13 \<subseteq> top1_S2" and hsub24: "e24 \<subseteq> top1_S2"
      and harc12: "top1_is_arc_on e12 (subspace_topology top1_S2 top1_S2_topology e12)"
      and harc23: "top1_is_arc_on e23 (subspace_topology top1_S2 top1_S2_topology e23)"
      and harc34: "top1_is_arc_on e34 (subspace_topology top1_S2 top1_S2_topology e34)"
      and harc14: "top1_is_arc_on e14 (subspace_topology top1_S2 top1_S2_topology e14)"
      and harc13: "top1_is_arc_on e13 (subspace_topology top1_S2 top1_S2_topology e13)"
      and harc24: "top1_is_arc_on e24 (subspace_topology top1_S2 top1_S2_topology e24)"
      and hep12: "top1_arc_endpoints_on e12 (subspace_topology top1_S2 top1_S2_topology e12) = {a1,a2}"
      and hep23: "top1_arc_endpoints_on e23 (subspace_topology top1_S2 top1_S2_topology e23) = {a2,a3}"
      and hep34: "top1_arc_endpoints_on e34 (subspace_topology top1_S2 top1_S2_topology e34) = {a3,a4}"
      and hep14: "top1_arc_endpoints_on e14 (subspace_topology top1_S2 top1_S2_topology e14) = {a4,a1}"
      and hep13: "top1_arc_endpoints_on e13 (subspace_topology top1_S2 top1_S2_topology e13) = {a1,a3}"
      and hep24: "top1_arc_endpoints_on e24 (subspace_topology top1_S2 top1_S2_topology e24) = {a2,a4}"
      and hi_12_34: "e12 \<inter> e34 = {}" and hi_23_14: "e23 \<inter> e14 = {}"
      and hi_12_23: "e12 \<inter> e23 = {a2}" and hi_23_34: "e23 \<inter> e34 = {a3}"
      and hi_34_14: "e34 \<inter> e14 = {a4}" and hi_14_12: "e14 \<inter> e12 = {a1}"
      and hi_13_12: "e13 \<inter> e12 = {a1}" and hi_13_23: "e13 \<inter> e23 = {a3}"
      and hi_13_34: "e13 \<inter> e34 = {a3}" and hi_13_14: "e13 \<inter> e14 = {a1}"
      and hi_13_24: "e13 \<inter> e24 \<subseteq> {a1,a2,a3,a4}"
      and hi_24_12: "e24 \<inter> e12 = {a2}" and hi_24_23: "e24 \<inter> e23 = {a2}"
      and hi_24_34: "e24 \<inter> e34 = {a4}" and hi_24_14: "e24 \<inter> e14 = {a4}"
      \<comment> \<open>Remaining K5-specific assumptions:\<close>
      and harc15: "top1_is_arc_on e15 (subspace_topology top1_S2 top1_S2_topology e15)"
      and harc25: "top1_is_arc_on e25 (subspace_topology top1_S2 top1_S2_topology e25)"
      and harc35: "top1_is_arc_on e35 (subspace_topology top1_S2 top1_S2_topology e35)"
      and harc45: "top1_is_arc_on e45 (subspace_topology top1_S2 top1_S2_topology e45)"
      and hsub15: "e15 \<subseteq> top1_S2" and hsub25: "e25 \<subseteq> top1_S2"
      and hsub35: "e35 \<subseteq> top1_S2" and hsub45: "e45 \<subseteq> top1_S2"
      and hep15: "top1_arc_endpoints_on e15 (subspace_topology top1_S2 top1_S2_topology e15) = {a1,a5}"
      and hep25: "top1_arc_endpoints_on e25 (subspace_topology top1_S2 top1_S2_topology e25) = {a2,a5}"
      and hep35: "top1_arc_endpoints_on e35 (subspace_topology top1_S2 top1_S2_topology e35) = {a3,a5}"
      and hep45: "top1_arc_endpoints_on e45 (subspace_topology top1_S2 top1_S2_topology e45) = {a4,a5}"
      \<comment> \<open>Intersections involving a5-edges:\<close>
      and hi_12_15: "e12 \<inter> e15 = {a1}" and hi_13_15: "e13 \<inter> e15 = {a1}"
      and hi_14_15: "e14 \<inter> e15 = {a1}" and hi_15_23: "e15 \<inter> e23 = {}"
      and hi_15_24: "e15 \<inter> e24 = {}" and hi_15_34: "e15 \<inter> e34 = {}"
      and hi_12_25: "e12 \<inter> e25 = {a2}" and hi_13_25: "e13 \<inter> e25 = {}"
      and hi_14_25: "e14 \<inter> e25 = {}" and hi_23_25: "e23 \<inter> e25 = {a2}"
      and hi_24_25: "e24 \<inter> e25 = {a2}" and hi_25_34: "e25 \<inter> e34 = {}"
      and hi_12_35: "e12 \<inter> e35 = {}" and hi_13_35: "e13 \<inter> e35 = {a3}"
      and hi_14_35: "e14 \<inter> e35 = {}" and hi_23_35: "e23 \<inter> e35 = {a3}"
      and hi_24_35: "e24 \<inter> e35 = {}" and hi_34_35: "e34 \<inter> e35 = {a3}"
      and hi_12_45: "e12 \<inter> e45 = {}" and hi_13_45: "e13 \<inter> e45 = {}"
      and hi_14_45: "e14 \<inter> e45 = {a4}" and hi_23_45: "e23 \<inter> e45 = {}"
      and hi_24_45: "e24 \<inter> e45 = {a4}" and hi_34_45: "e34 \<inter> e45 = {a4}"
      and hi_15_25: "e15 \<inter> e25 = {a5}" and hi_15_35: "e15 \<inter> e35 = {a5}"
      and hi_15_45: "e15 \<inter> e45 = {a5}" and hi_25_35: "e25 \<inter> e35 = {a5}"
      and hi_25_45: "e25 \<inter> e45 = {a5}" and hi_35_45: "e35 \<inter> e45 = {a5}"
  shows False
proof -
  have hcard4: "card {a1, a2, a3, a4} = 4"
    using hcard5 by (auto simp: card_insert_if split: if_splits)
  have hvert4: "{a1, a2, a3, a4} \<subseteq> top1_S2" using hvert by blast
  have ha5_ne: "a5 \<noteq> a1" "a5 \<noteq> a2" "a5 \<noteq> a3" "a5 \<noteq> a4"
    using hcard5 by (auto simp: card_insert_if split: if_splits)+
  \<comment> \<open>a5 \<in> e15 (from endpoints).\<close>
  have ha5_e15: "a5 \<in> e15"
    using arc_endpoints_subset[of e15 "subspace_topology top1_S2 top1_S2_topology e15"] hep15
    by blast
  \<comment> \<open>K4 graph X. a5 \<notin> X.\<close>
  define X where "X = e12 \<union> e23 \<union> e34 \<union> e14 \<union> e13 \<union> e24"
  have ha5_not_in_X: "a5 \<notin> X"
    unfolding X_def using ha5_e15 ha5_ne
      hi_12_15 hi_13_15 hi_14_15 hi_15_23 hi_15_24 hi_15_34
    by blast
  \<comment> \<open>Apply strengthened K4 separation (with boundary info).\<close>
  have hK4_sep: "\<exists>U1 U2 U3 U4.
      U1 \<noteq> {} \<and> U2 \<noteq> {} \<and> U3 \<noteq> {} \<and> U4 \<noteq> {}
      \<and> U1 \<inter> U2 = {} \<and> U1 \<inter> U3 = {} \<and> U1 \<inter> U4 = {}
      \<and> U2 \<inter> U3 = {} \<and> U2 \<inter> U4 = {} \<and> U3 \<inter> U4 = {}
      \<and> U1 \<union> U2 \<union> U3 \<union> U4 = top1_S2 - X
      \<and> top1_connected_on U1 (subspace_topology top1_S2 top1_S2_topology U1)
      \<and> top1_connected_on U2 (subspace_topology top1_S2 top1_S2_topology U2)
      \<and> top1_connected_on U3 (subspace_topology top1_S2 top1_S2_topology U3)
      \<and> top1_connected_on U4 (subspace_topology top1_S2 top1_S2_topology U4)
      \<and> U1 \<in> top1_S2_topology \<and> U2 \<in> top1_S2_topology
      \<and> U3 \<in> top1_S2_topology \<and> U4 \<in> top1_S2_topology
      \<and> closure_on top1_S2 top1_S2_topology U1 = U1 \<union> (e12 \<union> e23 \<union> e13)
      \<and> closure_on top1_S2 top1_S2_topology U2 = U2 \<union> (e13 \<union> e14 \<union> e34)
      \<and> ((closure_on top1_S2 top1_S2_topology U3 = U3 \<union> (e12 \<union> e14 \<union> e24)
          \<and> closure_on top1_S2 top1_S2_topology U4 = U4 \<union> (e23 \<union> e34 \<union> e24))
        \<or> (closure_on top1_S2 top1_S2_topology U3 = U3 \<union> (e23 \<union> e34 \<union> e24)
          \<and> closure_on top1_S2 top1_S2_topology U4 = U4 \<union> (e12 \<union> e14 \<union> e24)))"
    unfolding X_def
    apply (rule K4_four_components_with_boundary)
    apply (fact hS2) apply (fact hcard4) apply (fact hvert4)
    apply (fact hsub12) apply (fact hsub23) apply (fact hsub34)
    apply (fact hsub14) apply (fact hsub13) apply (fact hsub24)
    apply (fact harc12) apply (fact harc23) apply (fact harc34)
    apply (fact harc14) apply (fact harc13) apply (fact harc24)
    apply (fact hep12) apply (fact hep23) apply (fact hep34)
    apply (fact hep14) apply (fact hep13) apply (fact hep24)
    apply (fact hi_12_34) apply (fact hi_23_14)
    apply (fact hi_12_23) apply (fact hi_23_34) apply (fact hi_34_14) apply (fact hi_14_12)
    apply (fact hi_13_12) apply (fact hi_13_23) apply (fact hi_13_34) apply (fact hi_13_14)
    apply (fact hi_13_24)
    apply (fact hi_24_12) apply (fact hi_24_23) apply (fact hi_24_34) apply (fact hi_24_14)
    done
  from hK4_sep obtain U1 U2 U3 U4 where hU:
      "U1 \<noteq> {}" "U2 \<noteq> {}" "U3 \<noteq> {}" "U4 \<noteq> {}"
      "U1 \<inter> U2 = {}" "U1 \<inter> U3 = {}" "U1 \<inter> U4 = {}"
      "U2 \<inter> U3 = {}" "U2 \<inter> U4 = {}" "U3 \<inter> U4 = {}"
      "U1 \<union> U2 \<union> U3 \<union> U4 = top1_S2 - X"
      "top1_connected_on U1 (subspace_topology top1_S2 top1_S2_topology U1)"
      "top1_connected_on U2 (subspace_topology top1_S2 top1_S2_topology U2)"
      "top1_connected_on U3 (subspace_topology top1_S2 top1_S2_topology U3)"
      "top1_connected_on U4 (subspace_topology top1_S2 top1_S2_topology U4)"
      "U1 \<in> top1_S2_topology" "U2 \<in> top1_S2_topology"
      "U3 \<in> top1_S2_topology" "U4 \<in> top1_S2_topology"
      "closure_on top1_S2 top1_S2_topology U1 = U1 \<union> (e12 \<union> e23 \<union> e13)"
      "closure_on top1_S2 top1_S2_topology U2 = U2 \<union> (e13 \<union> e14 \<union> e34)"
      "(closure_on top1_S2 top1_S2_topology U3 = U3 \<union> (e12 \<union> e14 \<union> e24)
          \<and> closure_on top1_S2 top1_S2_topology U4 = U4 \<union> (e23 \<union> e34 \<union> e24))
        \<or> (closure_on top1_S2 top1_S2_topology U3 = U3 \<union> (e23 \<union> e34 \<union> e24)
          \<and> closure_on top1_S2 top1_S2_topology U4 = U4 \<union> (e12 \<union> e14 \<union> e24))"
    apply (elim exE conjE)
    apply (intro that; assumption)
    done
  have ha5_in_comp: "a5 \<in> U1 \<union> U2 \<union> U3 \<union> U4"
    using ha5_not_in_X hvert hU(11) X_def by (by100 blast)
  \<comment> \<open>Derive boundary conditions from exact closures.\<close>
  have hU_boundary: "\<not> ({a1, a2, a3, a4} \<subseteq> closure_on top1_S2 top1_S2_topology U1)
      \<and> \<not> ({a1, a2, a3, a4} \<subseteq> closure_on top1_S2 top1_S2_topology U2)
      \<and> \<not> ({a1, a2, a3, a4} \<subseteq> closure_on top1_S2 top1_S2_topology U3)
      \<and> \<not> ({a1, a2, a3, a4} \<subseteq> closure_on top1_S2 top1_S2_topology U4)"
  proof -
    \<comment> \<open>From exact closures: each Xi = 3 edges has only 3 vertices. The 4th is missing.\<close>
    \<comment> \<open>a4 \<notin> closure(U1): a4 \<notin> U1 (vertices on edges, U1 \<subseteq> S2-X) and a4 \<notin> e12\<union>e23\<union>e13.\<close>
    have ha4_not_U1_edges: "a4 \<notin> e12 \<union> e23 \<union> e13"
    proof -
      have ha4_e34: "a4 \<in> e34" using arc_endpoints_subset[of e34] hep34 by (by100 blast)
      have "a4 \<notin> e12" using hi_12_34 ha4_e34 by (by100 blast)
      moreover have "a4 \<notin> e23"
      proof assume "a4 \<in> e23"
        hence "a4 \<in> e23 \<inter> e34" using ha4_e34 by (by100 blast)
        hence "a4 \<in> {a3}" using hi_23_34 by (by100 blast)
        thus False using hcard5 by (auto simp: card_insert_if split: if_splits) qed
      moreover have "a4 \<notin> e13"
      proof assume "a4 \<in> e13"
        hence "a4 \<in> e13 \<inter> e34" using ha4_e34 by (by100 blast)
        hence "a4 \<in> {a3}" using hi_13_34 by (by100 blast)
        thus False using hcard5 by (auto simp: card_insert_if split: if_splits) qed
      ultimately show ?thesis by (by100 blast)
    qed
    have "a4 \<notin> U1"
    proof -
      have "a4 \<in> e34" using arc_endpoints_subset[of e34] hep34 by (by100 blast)
      hence "a4 \<in> e12 \<union> e23 \<union> e34 \<union> e14 \<union> e13 \<union> e24" by (by100 blast)
      hence "a4 \<notin> top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e14 \<union> e13 \<union> e24)" by (by100 blast)
      thus ?thesis using hU(11) X_def by (by100 blast)
    qed
    hence h1: "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U1)"
      using hU(20) ha4_not_U1_edges by (by100 blast)
    \<comment> \<open>a2 \<notin> closure(U2): a2 \<notin> e13\<union>e14\<union>e34.\<close>
    have ha2_not_U2_edges: "a2 \<notin> e13 \<union> e14 \<union> e34"
    proof -
      have ha2_e12: "a2 \<in> e12" using arc_endpoints_subset[of e12] hep12 by (by100 blast)
      have "a2 \<notin> e13" using hi_13_12 ha2_e12 hcard5 by (auto simp: card_insert_if split: if_splits)
      moreover have "a2 \<notin> e14" using hi_14_12 ha2_e12 hcard5 by (auto simp: card_insert_if split: if_splits)
      moreover have "a2 \<notin> e34" using hi_12_34 ha2_e12 by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    have "a2 \<notin> U2"
    proof -
      have "a2 \<in> e12" using arc_endpoints_subset[of e12] hep12 by (by100 blast)
      hence "a2 \<in> e12 \<union> e23 \<union> e34 \<union> e14 \<union> e13 \<union> e24" by (by100 blast)
      hence "a2 \<notin> top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e14 \<union> e13 \<union> e24)" by (by100 blast)
      thus ?thesis using hU(11) X_def by (by100 blast)
    qed
    hence h2: "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U2)"
      using hU(21) ha2_not_U2_edges by (by100 blast)
    \<comment> \<open>U3, U4: from the disjunction, each has a missing vertex.\<close>
    have ha3_not_X3: "a3 \<notin> e12 \<union> e14 \<union> e24"
    proof -
      have ha3_e34: "a3 \<in> e34" using arc_endpoints_subset[of e34] hep34 by (by100 blast)
      have "a3 \<notin> e12" using hi_12_34 ha3_e34 by (by100 blast)
      moreover have "a3 \<notin> e14"
      proof assume "a3 \<in> e14"
        hence "a3 \<in> e14 \<inter> e34" using ha3_e34 by (by100 blast)
        hence "a3 \<in> {a4}" using hi_34_14 by (by100 blast)
        thus False using hcard5 by (auto simp: card_insert_if split: if_splits) qed
      moreover have "a3 \<notin> e24"
      proof assume "a3 \<in> e24"
        hence "a3 \<in> e24 \<inter> e34" using ha3_e34 by (by100 blast)
        hence "a3 \<in> {a4}" using hi_24_34 by (by100 blast)
        thus False using hcard5 by (auto simp: card_insert_if split: if_splits) qed
      ultimately show ?thesis by (by100 blast)
    qed
    have ha1_not_X1: "a1 \<notin> e23 \<union> e34 \<union> e24"
    proof -
      have ha1_e12: "a1 \<in> e12" using arc_endpoints_subset[of e12] hep12 by (by100 blast)
      have "a1 \<notin> e23"
      proof assume "a1 \<in> e23"
        hence "a1 \<in> e12 \<inter> e23" using ha1_e12 by (by100 blast)
        hence "a1 \<in> {a2}" using hi_12_23 by (by100 blast)
        thus False using hcard5 by (auto simp: card_insert_if split: if_splits) qed
      moreover have "a1 \<notin> e34" using hi_12_34 ha1_e12 by (by100 blast)
      moreover have "a1 \<notin> e24"
      proof assume "a1 \<in> e24"
        hence "a1 \<in> e12 \<inter> e24" using ha1_e12 by (by100 blast)
        hence "a1 \<in> {a2}" using hi_24_12 by (by100 blast)
        thus False using hcard5 by (auto simp: card_insert_if split: if_splits) qed
      ultimately show ?thesis by (by100 blast)
    qed
    have ha3_not_U: "a3 \<notin> U3 \<and> a3 \<notin> U4"
    proof -
      have "a3 \<in> e34" using arc_endpoints_subset[of e34] hep34 by (by100 blast)
      hence "a3 \<notin> top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e14 \<union> e13 \<union> e24)" by (by100 blast)
      thus ?thesis using hU(11) X_def by (by100 blast)
    qed
    have ha1_not_U: "a1 \<notin> U3 \<and> a1 \<notin> U4"
    proof -
      have "a1 \<in> e12" using arc_endpoints_subset[of e12] hep12 by (by100 blast)
      hence "a1 \<notin> top1_S2 - (e12 \<union> e23 \<union> e34 \<union> e14 \<union> e13 \<union> e24)" by (by100 blast)
      thus ?thesis using hU(11) X_def by (by100 blast)
    qed
    have h34: "\<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U3)
        \<and> \<not> ({a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U4)"
      using hU(22)
    proof
      assume h: "closure_on top1_S2 top1_S2_topology U3 = U3 \<union> (e12 \<union> e14 \<union> e24)
          \<and> closure_on top1_S2 top1_S2_topology U4 = U4 \<union> (e23 \<union> e34 \<union> e24)"
      have "\<not> ({a1,a2,a3,a4} \<subseteq> U3 \<union> (e12 \<union> e14 \<union> e24))" using ha3_not_X3 ha3_not_U by (by100 blast)
      moreover have "\<not> ({a1,a2,a3,a4} \<subseteq> U4 \<union> (e23 \<union> e34 \<union> e24))" using ha1_not_X1 ha1_not_U by (by100 blast)
      ultimately show ?thesis using conjunct1[OF h] conjunct2[OF h] by (by100 simp)
    next
      assume h: "closure_on top1_S2 top1_S2_topology U3 = U3 \<union> (e23 \<union> e34 \<union> e24)
          \<and> closure_on top1_S2 top1_S2_topology U4 = U4 \<union> (e12 \<union> e14 \<union> e24)"
      have "\<not> ({a1,a2,a3,a4} \<subseteq> U3 \<union> (e23 \<union> e34 \<union> e24))" using ha1_not_X1 ha1_not_U by (by100 blast)
      moreover have "\<not> ({a1,a2,a3,a4} \<subseteq> U4 \<union> (e12 \<union> e14 \<union> e24))" using ha3_not_X3 ha3_not_U by (by100 blast)
      ultimately show ?thesis using conjunct1[OF h] conjunct2[OF h] by (by100 simp)
    qed
    show ?thesis using h1 h2 h34 by (by100 blast)
  qed
  \<comment> \<open>Each X\_i = 3 edges not incident to a\_i forms an SCC.
     By JCT, X\_i separates S2. Since e\_{i,5} \<inter> X\_i = {} and e\_{i,5} connects
     a5 to a\_i, they are on the same side of X\_i.
     But a5 being in one K4 component means a5 is on one specific side of each X\_i,
     and being on a\_i's side for ALL i is impossible (the 4 faces are disjoint).\<close>
  \<comment> \<open>X1 = e23 \<union> e24 \<union> e34 (SCC, missing a1).
     X2 = e13 \<union> e14 \<union> e34 (SCC, missing a2).
     X3 = e12 \<union> e14 \<union> e24 (SCC, missing a3).
     X4 = e12 \<union> e13 \<union> e23 (SCC, missing a4).\<close>
  \<comment> \<open>e15 \<inter> X1 = e15 \<inter> (e23\<union>e24\<union>e34) = {}\<union>{}\<union>{} = {} (from intersection assumptions).
     Similarly for e25 \<inter> X2, e35 \<inter> X3, e45 \<inter> X4.\<close>
  have he15_X1: "e15 \<inter> (e23 \<union> e24 \<union> e34) = {}"
    using hi_15_23 hi_15_24 hi_15_34 by (by100 blast)
  have he25_X2: "e25 \<inter> (e13 \<union> e14 \<union> e34) = {}"
    using hi_13_25 hi_14_25 hi_25_34 by (by100 blast)
  have he35_X3: "e35 \<inter> (e12 \<union> e14 \<union> e24) = {}"
    using hi_12_35 hi_14_35 hi_24_35 by (by100 blast)
  have he45_X4: "e45 \<inter> (e12 \<union> e13 \<union> e23) = {}"
    using hi_12_45 hi_13_45 hi_23_45 by (by100 blast)
  \<comment> \<open>Step A+B: for each component Ui containing a5, all 4 vertices are in closure(Ui).
     Generic argument for each vertex aj:
     - e\_{j,5} \<inter> X = {a\_j} (proved above)
     - e\_{j,5} - {a\_j} \<subseteq> S2-X
     - e\_{j,5} - {a\_j} is connected (arc minus one endpoint)
     - a5 \<in> e\_{j,5} - {a\_j} (a5 is endpoint, a5 \<noteq> a\_j)
     - a5 \<in> Ui, Ui is component of S2-X
     - connected subset of S2-X meeting Ui \<Rightarrow> \<subseteq> Ui
     - a\_j \<in> closure(e\_{j,5} - {a\_j, a5}) \<subseteq> closure(Ui)\<close>
  \<comment> \<open>Generic: if a5 \<in> Ui and Ui is one of the 4 components, all vertices in closure(Ui).\<close>
  have hS2_strict: "is_topology_on_strict top1_S2 top1_S2_topology" by (rule hS2)
  have hS2_haus: "is_hausdorff_on top1_S2 top1_S2_topology" by (rule top1_S2_is_hausdorff)
  have hTS2: "is_topology_on top1_S2 top1_S2_topology"
    using hS2 unfolding is_topology_on_strict_def by (by100 blast)
  have hX_sub: "X \<subseteq> top1_S2" unfolding X_def
    using hsub12 hsub23 hsub34 hsub14 hsub13 hsub24 by (by100 blast)
  have hSX_open: "top1_S2 - X \<in> top1_S2_topology"
  proof -
    have hcl12: "closedin_on top1_S2 top1_S2_topology e12" by (rule arc_in_S2_closed[OF hsub12 harc12])
    have hcl23: "closedin_on top1_S2 top1_S2_topology e23" by (rule arc_in_S2_closed[OF hsub23 harc23])
    have hcl34: "closedin_on top1_S2 top1_S2_topology e34" by (rule arc_in_S2_closed[OF hsub34 harc34])
    have hcl14: "closedin_on top1_S2 top1_S2_topology e14" by (rule arc_in_S2_closed[OF hsub14 harc14])
    have hcl13: "closedin_on top1_S2 top1_S2_topology e13" by (rule arc_in_S2_closed[OF hsub13 harc13])
    have hcl24: "closedin_on top1_S2 top1_S2_topology e24" by (rule arc_in_S2_closed[OF hsub24 harc24])
    have hclX: "closedin_on top1_S2 top1_S2_topology X"
    proof -
      have "X = \<Union>{e12, e23, e34, e14, e13, e24}" unfolding X_def by (by100 blast)
      moreover have "closedin_on top1_S2 top1_S2_topology (\<Union>{e12, e23, e34, e14, e13, e24})"
        apply (rule closedin_Union_finite[OF hTS2])
        apply (by100 simp)
        using hcl12 hcl23 hcl34 hcl14 hcl13 hcl24 apply (by100 blast)
        done
      ultimately show ?thesis by (by100 simp)
    qed
    show ?thesis using hclX hS2 unfolding is_topology_on_strict_def closedin_on_def by (by100 blast)
  qed
  \<comment> \<open>Each Ui is open in S2 (component of open set in locally path connected space).\<close>
  have hU_open: "U1 \<in> top1_S2_topology" "U2 \<in> top1_S2_topology"
      "U3 \<in> top1_S2_topology" "U4 \<in> top1_S2_topology"
    using hU(16,17,18,19) by (by100 blast)+
  \<comment> \<open>Helper: if Y connected, Y \<subseteq> S2-X, Y \<inter> Ui \<noteq> {}, then Y \<subseteq> Ui.\<close>
  have hcomp_max: "\<And>Y Ui. Ui \<in> {U1,U2,U3,U4} \<Longrightarrow>
      Y \<subseteq> top1_S2 - X \<Longrightarrow> top1_connected_on Y (subspace_topology top1_S2 top1_S2_topology Y) \<Longrightarrow>
      Y \<inter> Ui \<noteq> {} \<Longrightarrow> Y \<subseteq> Ui"
  proof -
    fix Y Ui assume hUi_mem: "Ui \<in> {U1,U2,U3,U4}" and hY_sub: "Y \<subseteq> top1_S2 - X"
        and hY_conn: "top1_connected_on Y (subspace_topology top1_S2 top1_S2_topology Y)"
        and hY_meet: "Y \<inter> Ui \<noteq> {}"
    \<comment> \<open>Ui is open and the rest (S2-X-Ui) is open (union of 3 open sets).\<close>
    have hUi_open: "Ui \<in> top1_S2_topology" using hUi_mem hU_open by (by100 blast)
    have hrest_eq: "top1_S2 - X - Ui = (U1 \<union> U2 \<union> U3 \<union> U4) - Ui"
      using hU(11) by (by100 blast)
    have hrest_open: "(top1_S2 - X) - Ui \<in> top1_S2_topology"
    proof -
      have hunion_open: "\<And>A B C. A \<in> top1_S2_topology \<Longrightarrow> B \<in> top1_S2_topology \<Longrightarrow>
          C \<in> top1_S2_topology \<Longrightarrow> A \<union> B \<union> C \<in> top1_S2_topology"
      proof -
        fix A B C assume "A \<in> top1_S2_topology" "B \<in> top1_S2_topology" "C \<in> top1_S2_topology"
        have "{A, B, C} \<subseteq> top1_S2_topology" using \<open>A \<in> _\<close> \<open>B \<in> _\<close> \<open>C \<in> _\<close> by (by100 blast)
        hence "\<Union>{A, B, C} \<in> top1_S2_topology" using hTS2 unfolding is_topology_on_def by (by100 blast)
        moreover have "\<Union>{A, B, C} = A \<union> B \<union> C" by (by100 blast)
        ultimately show "A \<union> B \<union> C \<in> top1_S2_topology" by (by100 simp)
      qed
      have h: "(U1 \<union> U2 \<union> U3 \<union> U4) - Ui \<in> top1_S2_topology"
      proof -
        { assume "Ui = U1"
          have "(U1 \<union> U2 \<union> U3 \<union> U4) - U1 = U2 \<union> U3 \<union> U4"
            using hU(5,6,7) by (by100 blast)
          hence ?thesis using \<open>Ui = U1\<close> hunion_open[OF hU_open(2) hU_open(3) hU_open(4)]
            by (by100 simp)
        }
        moreover { assume "Ui = U2"
          have "(U1 \<union> U2 \<union> U3 \<union> U4) - U2 = U1 \<union> U3 \<union> U4"
            using hU(5,8,9) by (by100 blast)
          hence ?thesis using \<open>Ui = U2\<close> hunion_open[OF hU_open(1) hU_open(3) hU_open(4)]
            by (by100 simp)
        }
        moreover { assume "Ui = U3"
          have "(U1 \<union> U2 \<union> U3 \<union> U4) - U3 = U1 \<union> U2 \<union> U4"
            using hU(6,8,10) by (by100 blast)
          hence ?thesis using \<open>Ui = U3\<close> hunion_open[OF hU_open(1) hU_open(2) hU_open(4)]
            by (by100 simp)
        }
        moreover { assume "Ui = U4"
          have "(U1 \<union> U2 \<union> U3 \<union> U4) - U4 = U1 \<union> U2 \<union> U3"
            using hU(7,9,10) by (by100 blast)
          hence ?thesis using \<open>Ui = U4\<close> hunion_open[OF hU_open(1) hU_open(2) hU_open(3)]
            by (by100 simp)
        }
        ultimately show ?thesis using hUi_mem by (by100 blast)
      qed
      thus ?thesis using hrest_eq by (by100 simp)
    qed
    \<comment> \<open>Y = (Y \<inter> Ui) \<union> (Y - Ui); both are open in Y-subspace; Y is connected.\<close>
    have hY_sub_S2: "Y \<subseteq> top1_S2" using hY_sub by (by100 blast)
    have hYUi_open_Y: "Y \<inter> Ui \<in> subspace_topology top1_S2 top1_S2_topology Y"
      unfolding subspace_topology_def using hUi_open by (by100 blast)
    have hYmUi_open_Y: "Y - Ui \<in> subspace_topology top1_S2 top1_S2_topology Y"
    proof -
      have "Y - Ui = Y \<inter> ((top1_S2 - X) - Ui)" using hY_sub by (by100 blast)
      thus ?thesis unfolding subspace_topology_def using hrest_open by (by100 blast)
    qed
    have hY_part: "Y = (Y \<inter> Ui) \<union> (Y - Ui)" by (by100 blast)
    have hY_disj: "(Y \<inter> Ui) \<inter> (Y - Ui) = {}" by (by100 blast)
    \<comment> \<open>Y connected: if both parts nonempty, contradiction.\<close>
    show "Y \<subseteq> Ui"
    proof (rule ccontr)
      assume "\<not> Y \<subseteq> Ui"
      hence "Y - Ui \<noteq> {}" by (by100 blast)
      have "\<not> top1_connected_on Y (subspace_topology top1_S2 top1_S2_topology Y)"
        unfolding top1_connected_on_def
        using hYUi_open_Y hYmUi_open_Y hY_part hY_disj hY_meet \<open>Y - Ui \<noteq> {}\<close>
        by (by100 blast)
      thus False using hY_conn by (by100 blast)
    qed
  qed
  \<comment> \<open>Helper: for each arc e\_{j,5}: e\_{j,5}-{a\_j} is connected in S2.\<close>
  have ha_ne_a5: "a1 \<noteq> a5" "a2 \<noteq> a5" "a3 \<noteq> a5" "a4 \<noteq> a5"
    using ha5_ne by (by100 blast)+
  \<comment> \<open>e\_{j,5} - {a\_j} connected: arc minus both endpoints connected (existing lemma),
     then Theorem\_23\_4 extends to include the other endpoint a5.\<close>
  have hconn15: "top1_connected_on (e15 - {a1}) (subspace_topology top1_S2 top1_S2_topology (e15 - {a1}))"
  proof -
    have h1: "top1_connected_on (e15 - {a1, a5}) (subspace_topology top1_S2 top1_S2_topology (e15 - {a1, a5}))"
      by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus hsub15 harc15 hep15 ha_ne_a5(1)])
    have h2: "e15 - {a1, a5} \<subseteq> e15 - {a1}" by (by100 blast)
    have h3: "e15 - {a1} \<subseteq> top1_S2" using hsub15 by (by100 blast)
    have h4: "e15 - {a1} \<subseteq> closure_on top1_S2 top1_S2_topology (e15 - {a1, a5})"
    proof -
      have "a5 \<in> closure_on top1_S2 top1_S2_topology (e15 - {a1, a5})"
        by (rule arc_endpoint_in_closure_of_interior(2)[OF hS2_strict hS2_haus hsub15 harc15 hep15 ha_ne_a5(1)])
      moreover have "e15 - {a1, a5} \<subseteq> closure_on top1_S2 top1_S2_topology (e15 - {a1, a5})"
        using subset_closure_on[of "e15-{a1,a5}" top1_S2 top1_S2_topology] h3 by (by100 blast)
      moreover have "e15 - {a1} = (e15 - {a1, a5}) \<union> {a5}" using ha5_e15 ha5_ne(1) by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    have h0: "e15 - {a1, a5} \<subseteq> top1_S2" using hsub15 by (by100 blast)
    from Theorem_23_4[OF hTS2 h0 h3 h2 h4 h1]
    show ?thesis .
  qed
  have hconn25: "top1_connected_on (e25 - {a2}) (subspace_topology top1_S2 top1_S2_topology (e25 - {a2}))"
  proof -
    have ha5_e25: "a5 \<in> e25"
      using arc_endpoints_subset[of e25 "subspace_topology top1_S2 top1_S2_topology e25"] hep25 by (by100 blast)
    have h1: "top1_connected_on (e25 - {a2, a5}) (subspace_topology top1_S2 top1_S2_topology (e25 - {a2, a5}))"
      by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus hsub25 harc25 hep25 ha_ne_a5(2)])
    have h0: "e25 - {a2, a5} \<subseteq> top1_S2" using hsub25 by (by100 blast)
    have h2: "e25 - {a2, a5} \<subseteq> e25 - {a2}" by (by100 blast)
    have h3: "e25 - {a2} \<subseteq> top1_S2" using hsub25 by (by100 blast)
    have h4: "e25 - {a2} \<subseteq> closure_on top1_S2 top1_S2_topology (e25 - {a2, a5})"
    proof -
      have "a5 \<in> closure_on top1_S2 top1_S2_topology (e25 - {a2, a5})"
        by (rule arc_endpoint_in_closure_of_interior(2)[OF hS2_strict hS2_haus hsub25 harc25 hep25 ha_ne_a5(2)])
      moreover have "e25 - {a2, a5} \<subseteq> closure_on top1_S2 top1_S2_topology (e25 - {a2, a5})"
        using subset_closure_on[of "e25-{a2,a5}" top1_S2 top1_S2_topology] h0 by (by100 blast)
      moreover have "e25 - {a2} = (e25 - {a2, a5}) \<union> {a5}" using ha5_e25 ha5_ne(2) by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    from Theorem_23_4[OF hTS2 h0 h3 h2 h4 h1] show ?thesis .
  qed
  have hconn35: "top1_connected_on (e35 - {a3}) (subspace_topology top1_S2 top1_S2_topology (e35 - {a3}))"
  proof -
    have ha5_e35: "a5 \<in> e35"
      using arc_endpoints_subset[of e35 "subspace_topology top1_S2 top1_S2_topology e35"] hep35 by (by100 blast)
    have h1: "top1_connected_on (e35 - {a3, a5}) (subspace_topology top1_S2 top1_S2_topology (e35 - {a3, a5}))"
      by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus hsub35 harc35 hep35 ha_ne_a5(3)])
    have h0: "e35 - {a3, a5} \<subseteq> top1_S2" using hsub35 by (by100 blast)
    have h2: "e35 - {a3, a5} \<subseteq> e35 - {a3}" by (by100 blast)
    have h3: "e35 - {a3} \<subseteq> top1_S2" using hsub35 by (by100 blast)
    have h4: "e35 - {a3} \<subseteq> closure_on top1_S2 top1_S2_topology (e35 - {a3, a5})"
    proof -
      have "a5 \<in> closure_on top1_S2 top1_S2_topology (e35 - {a3, a5})"
        by (rule arc_endpoint_in_closure_of_interior(2)[OF hS2_strict hS2_haus hsub35 harc35 hep35 ha_ne_a5(3)])
      moreover have "e35 - {a3, a5} \<subseteq> closure_on top1_S2 top1_S2_topology (e35 - {a3, a5})"
        using subset_closure_on[of "e35-{a3,a5}" top1_S2 top1_S2_topology] h0 by (by100 blast)
      moreover have "e35 - {a3} = (e35 - {a3, a5}) \<union> {a5}" using ha5_e35 ha5_ne(3) by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    from Theorem_23_4[OF hTS2 h0 h3 h2 h4 h1] show ?thesis .
  qed
  have hconn45: "top1_connected_on (e45 - {a4}) (subspace_topology top1_S2 top1_S2_topology (e45 - {a4}))"
  proof -
    have ha5_e45: "a5 \<in> e45"
      using arc_endpoints_subset[of e45 "subspace_topology top1_S2 top1_S2_topology e45"] hep45 by (by100 blast)
    have h1: "top1_connected_on (e45 - {a4, a5}) (subspace_topology top1_S2 top1_S2_topology (e45 - {a4, a5}))"
      by (rule arc_minus_endpoints_connected[OF hS2_strict hS2_haus hsub45 harc45 hep45 ha_ne_a5(4)])
    have h0: "e45 - {a4, a5} \<subseteq> top1_S2" using hsub45 by (by100 blast)
    have h2: "e45 - {a4, a5} \<subseteq> e45 - {a4}" by (by100 blast)
    have h3: "e45 - {a4} \<subseteq> top1_S2" using hsub45 by (by100 blast)
    have h4: "e45 - {a4} \<subseteq> closure_on top1_S2 top1_S2_topology (e45 - {a4, a5})"
    proof -
      have "a5 \<in> closure_on top1_S2 top1_S2_topology (e45 - {a4, a5})"
        by (rule arc_endpoint_in_closure_of_interior(2)[OF hS2_strict hS2_haus hsub45 harc45 hep45 ha_ne_a5(4)])
      moreover have "e45 - {a4, a5} \<subseteq> closure_on top1_S2 top1_S2_topology (e45 - {a4, a5})"
        using subset_closure_on[of "e45-{a4,a5}" top1_S2 top1_S2_topology] h0 by (by100 blast)
      moreover have "e45 - {a4} = (e45 - {a4, a5}) \<union> {a5}" using ha5_e45 ha5_ne(4) by (by100 blast)
      ultimately show ?thesis by (by100 blast)
    qed
    from Theorem_23_4[OF hTS2 h0 h3 h2 h4 h1] show ?thesis .
  qed
  \<comment> \<open>e\_{j,5} - {a\_j} \<subseteq> S2-X (from intersection facts).\<close>
  have he15_X: "e15 \<inter> X = {a1}"
  proof -
    have "e15 \<inter> X = (e15\<inter>e12) \<union> (e15\<inter>e23) \<union> (e15\<inter>e34) \<union> (e15\<inter>e14) \<union> (e15\<inter>e13) \<union> (e15\<inter>e24)"
      unfolding X_def by (by100 blast)
    also have "\<dots> = {a1} \<union> {} \<union> {} \<union> {a1} \<union> {a1} \<union> {}"
      using hi_12_15 hi_15_23 hi_15_34 hi_14_15 hi_13_15 hi_15_24
      apply (simp add: Int_commute)
      done
    also have "\<dots> = {a1}" by (by100 blast)
    finally show ?thesis .
  qed
  have he25_X: "e25 \<inter> X = {a2}"
  proof -
    have "e25 \<inter> X = (e25\<inter>e12) \<union> (e25\<inter>e23) \<union> (e25\<inter>e34) \<union> (e25\<inter>e14) \<union> (e25\<inter>e13) \<union> (e25\<inter>e24)"
      unfolding X_def by (by100 blast)
    also have "\<dots> = {a2} \<union> {a2} \<union> {} \<union> {} \<union> {} \<union> {a2}"
      using hi_12_25 hi_23_25 hi_25_34 hi_14_25 hi_13_25 hi_24_25
      apply (simp add: Int_commute)
      done
    also have "\<dots> = {a2}" by (by100 blast)
    finally show ?thesis .
  qed
  have he35_X: "e35 \<inter> X = {a3}"
  proof -
    have "e35 \<inter> X = (e35\<inter>e12) \<union> (e35\<inter>e23) \<union> (e35\<inter>e34) \<union> (e35\<inter>e14) \<union> (e35\<inter>e13) \<union> (e35\<inter>e24)"
      unfolding X_def by (by100 blast)
    also have "\<dots> = {} \<union> {a3} \<union> {a3} \<union> {} \<union> {a3} \<union> {}"
      using hi_12_35 hi_23_35 hi_34_35 hi_14_35 hi_13_35 hi_24_35
      apply (simp add: Int_commute)
      done
    also have "\<dots> = {a3}" by (by100 blast)
    finally show ?thesis .
  qed
  have he45_X: "e45 \<inter> X = {a4}"
  proof -
    have "e45 \<inter> X = (e45\<inter>e12) \<union> (e45\<inter>e23) \<union> (e45\<inter>e34) \<union> (e45\<inter>e14) \<union> (e45\<inter>e13) \<union> (e45\<inter>e24)"
      unfolding X_def by (by100 blast)
    also have "\<dots> = {} \<union> {} \<union> {a4} \<union> {a4} \<union> {} \<union> {a4}"
      using hi_12_45 hi_23_45 hi_34_45 hi_14_45 hi_13_45 hi_24_45
      apply (simp add: Int_commute)
      done
    also have "\<dots> = {a4}" by (by100 blast)
    finally show ?thesis .
  qed
  have hsub15X: "e15 - {a1} \<subseteq> top1_S2 - X" using he15_X hsub15 by (by100 blast)
  have hsub25X: "e25 - {a2} \<subseteq> top1_S2 - X" using he25_X hsub25 by (by100 blast)
  have hsub35X: "e35 - {a3} \<subseteq> top1_S2 - X" using he35_X hsub35 by (by100 blast)
  have hsub45X: "e45 - {a4} \<subseteq> top1_S2 - X" using he45_X hsub45 by (by100 blast)
  \<comment> \<open>a5 \<in> e\_{j,5} - {a\_j}.\<close>
  have ha5_15: "a5 \<in> e15 - {a1}" using ha5_e15 ha5_ne(1) by (by100 blast)
  have ha5_25: "a5 \<in> e25 - {a2}"
    using arc_endpoints_subset[of e25 "subspace_topology top1_S2 top1_S2_topology e25"] hep25 ha5_ne(2)
    by (by100 blast)
  have ha5_35: "a5 \<in> e35 - {a3}"
    using arc_endpoints_subset[of e35 "subspace_topology top1_S2 top1_S2_topology e35"] hep35 ha5_ne(3)
    by (by100 blast)
  have ha5_45: "a5 \<in> e45 - {a4}"
    using arc_endpoints_subset[of e45 "subspace_topology top1_S2 top1_S2_topology e45"] hep45 ha5_ne(4)
    by (by100 blast)
  \<comment> \<open>a\_j \<in> closure(e\_{j,5} - {a\_j, a5}) (arc endpoint in closure of interior).\<close>
  have hcl1: "a1 \<in> closure_on top1_S2 top1_S2_topology (e15 - {a1, a5})"
    by (rule arc_endpoint_in_closure_of_interior(1)[OF hS2_strict hS2_haus hsub15 harc15 hep15 ha_ne_a5(1)])
  have hcl2: "a2 \<in> closure_on top1_S2 top1_S2_topology (e25 - {a2, a5})"
    by (rule arc_endpoint_in_closure_of_interior(1)[OF hS2_strict hS2_haus hsub25 harc25 hep25 ha_ne_a5(2)])
  have hcl3: "a3 \<in> closure_on top1_S2 top1_S2_topology (e35 - {a3, a5})"
    by (rule arc_endpoint_in_closure_of_interior(1)[OF hS2_strict hS2_haus hsub35 harc35 hep35 ha_ne_a5(3)])
  have hcl4: "a4 \<in> closure_on top1_S2 top1_S2_topology (e45 - {a4, a5})"
    by (rule arc_endpoint_in_closure_of_interior(1)[OF hS2_strict hS2_haus hsub45 harc45 hep45 ha_ne_a5(4)])
  have hall_generic: "\<And>Ui. Ui \<in> {U1,U2,U3,U4} \<Longrightarrow> a5 \<in> Ui \<Longrightarrow>
      {a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology Ui"
  proof (intro subsetI)
    fix Ui v assume hUi: "Ui \<in> {U1,U2,U3,U4}" and ha5Ui: "a5 \<in> Ui"
        and hv: "v \<in> {a1,a2,a3,a4}"
    \<comment> \<open>Pick the right star edge for vertex v.\<close>
    have "v \<in> closure_on top1_S2 top1_S2_topology Ui"
    proof -
      obtain ej5 where hej5: "ej5 - {v} \<subseteq> top1_S2 - X"
          "top1_connected_on (ej5 - {v}) (subspace_topology top1_S2 top1_S2_topology (ej5 - {v}))"
          "a5 \<in> ej5 - {v}"
          "v \<in> closure_on top1_S2 top1_S2_topology (ej5 - {v, a5})"
        using hv hsub15X hconn15 ha5_15 hcl1
              hsub25X hconn25 ha5_25 hcl2
              hsub35X hconn35 ha5_35 hcl3
              hsub45X hconn45 ha5_45 hcl4
        by (by100 blast)
      have "ej5 - {v} \<subseteq> Ui"
        by (rule hcomp_max[OF hUi hej5(1) hej5(2)]) (use hej5(3) ha5Ui in \<open>by100 blast\<close>)
      hence "ej5 - {v, a5} \<subseteq> Ui" by (by100 blast)
      hence "closure_on top1_S2 top1_S2_topology (ej5 - {v, a5}) \<subseteq> closure_on top1_S2 top1_S2_topology Ui"
        by (rule closure_on_mono)
      thus ?thesis using hej5(4) by (by100 blast)
    qed
    thus "v \<in> closure_on top1_S2 top1_S2_topology Ui" .
  qed
  have hall1: "a5 \<in> U1 \<Longrightarrow> {a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U1"
    by (rule hall_generic) (by100 blast)
  have hall2: "a5 \<in> U2 \<Longrightarrow> {a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U2"
    by (rule hall_generic) (by100 blast)
  have hall3: "a5 \<in> U3 \<Longrightarrow> {a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U3"
    by (rule hall_generic) (by100 blast)
  have hall4: "a5 \<in> U4 \<Longrightarrow> {a1,a2,a3,a4} \<subseteq> closure_on top1_S2 top1_S2_topology U4"
    by (rule hall_generic) (by100 blast)
  \<comment> \<open>But hU\_boundary says no component has all 4 vertices in its closure.\<close>
  show False using ha5_in_comp hall1 hall2 hall3 hall4 hU_boundary by (by100 blast)
qed

end
