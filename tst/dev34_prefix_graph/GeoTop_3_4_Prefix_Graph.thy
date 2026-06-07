theory GeoTop_3_4_Prefix_Graph
  imports "GeoTop34PrefixGraphCacheDirty.GeoTop_3_4_Prefix_Graph_Cache"
begin

lemma geotop_singleton_not_edge_prefix:
  fixes v :: "real^2"
  shows "\<not> geotop_is_edge {v}"
proof
  assume hedge: "geotop_is_edge {v}"
  have hdim0: "geotop_simplex_dim {v} 0"
    by (rule geotop_singleton_is_simplex)
  have hdim1: "geotop_simplex_dim {v} 1"
    using hedge unfolding geotop_is_edge_def by (by100 simp)
  have "0 = (1::nat)"
    by (rule geotop_simplex_dim_unique[OF hdim0 hdim1])
  thus False
    by (by100 linarith)
qed

lemma geotop_degree_two_oriented_edge_successor_period_edge_orbit_no_singletons_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hx: "{v} \<in> ((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` I)"
  shows False
proof -
  let ?E = "((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` I)"
  have hE_sub: "?E \<subseteq> {e\<in>L. geotop_is_edge e}"
    by (rule geotop_degree_two_oriented_edge_successor_period_closed_segment_edge_orbit_subset_edges_prefix
        [OF hL hdegree hs])
  have hedge: "geotop_is_edge {v}"
    using hE_sub hx by (by100 blast)
  have hnot: "\<not> geotop_is_edge {v}"
    by (rule geotop_singleton_not_edge_prefix)
  show False
    using hedge hnot by (by100 blast)
qed

lemma geotop_degree_two_oriented_edge_successor_period_nonorbit_edge_face_outside_cycle_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hnot: "e \<notin> ((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p})"
  assumes hface: "geotop_is_face F e"
  shows "F \<notin> ((\<lambda>v. {v}) `
        ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
      \<union> ((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p})"
proof -
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  let ?V = "?v ` {0..<p}"
  let ?SV = "(\<lambda>v. {v}) ` ?V"
  let ?E = "((\<lambda>j. closed_segment (?v j) (?v (Suc j))) ` {0..<p})"
  have havoid: "e \<inter> ?V = {}"
    by (rule geotop_degree_two_oriented_edge_successor_period_nonorbit_edge_avoids_vertex_orbit_prefix
        [OF hL hdegree hs hp_pos hp_closed heL hedge hnot])
  obtain a b where hab: "a \<noteq> b" and heq: "e = closed_segment a b"
    by (rule geotop_edge_closed_segment_obtain_prefix[OF hedge])
  have ha_e: "a \<in> e"
    using heq by (by100 simp)
  have hb_e: "b \<in> e"
    using heq by (by100 simp)
  have hface_cases: "F = {a} \<or> F = {b} \<or> F = e"
  proof -
    have hface_seg: "geotop_is_face F (closed_segment a b)"
      using hface heq by (by100 simp)
    have "F = {a} \<or> F = {b} \<or> F = closed_segment a b"
      by (rule geotop_closed_segment_face_endpoint_or_self_prefix[OF hab hface_seg])
    thus ?thesis
      using heq by (by100 blast)
  qed
  have ha_out: "{a} \<notin> ?SV \<union> ?E"
  proof
    assume ha_cycle: "{a} \<in> ?SV \<union> ?E"
    show False
    proof (rule UnE[OF ha_cycle])
      assume haSV: "{a} \<in> ?SV"
      obtain x where hxV: "x \<in> ?V" and hax: "{a} = {x}"
        using haSV by (by100 blast)
      have haV: "a \<in> ?V"
        using hxV hax by (by100 simp)
      have "e \<inter> ?V \<noteq> {}"
        using ha_e haV by (by100 blast)
      thus False
        using havoid by (by100 blast)
    next
      assume haE: "{a} \<in> ?E"
      show False
        by (rule geotop_degree_two_oriented_edge_successor_period_edge_orbit_no_singletons_prefix
            [OF hL hdegree hs haE])
    qed
  qed
  have hb_out: "{b} \<notin> ?SV \<union> ?E"
  proof
    assume hb_cycle: "{b} \<in> ?SV \<union> ?E"
    show False
    proof (rule UnE[OF hb_cycle])
      assume hbSV: "{b} \<in> ?SV"
      obtain x where hxV: "x \<in> ?V" and hbx: "{b} = {x}"
        using hbSV by (by100 blast)
      have hbV: "b \<in> ?V"
        using hxV hbx by (by100 simp)
      have "e \<inter> ?V \<noteq> {}"
        using hb_e hbV by (by100 blast)
      thus False
        using havoid by (by100 blast)
    next
      assume hbE: "{b} \<in> ?E"
      show False
        by (rule geotop_degree_two_oriented_edge_successor_period_edge_orbit_no_singletons_prefix
            [OF hL hdegree hs hbE])
    qed
  qed
  have he_out: "e \<notin> ?SV \<union> ?E"
  proof
    assume he_cycle: "e \<in> ?SV \<union> ?E"
    show False
    proof (rule UnE[OF he_cycle])
      assume heSV: "e \<in> ?SV"
      obtain x where hxV: "x \<in> ?V" and hex: "e = {x}"
        using heSV by (by100 blast)
      have hx_e: "x \<in> e"
        using hex by (by100 simp)
      have "e \<inter> ?V \<noteq> {}"
        using hx_e hxV by (by100 blast)
      thus False
        using havoid by (by100 blast)
    next
      assume heE: "e \<in> ?E"
      show False
        using hnot heE by (by100 blast)
    qed
  qed
  show ?thesis
  proof
    assume hF_cycle: "F \<in> ?SV \<union> ?E"
    show False
    proof (rule disjE[OF hface_cases])
      assume hF: "F = {a}"
      show False
        using hF hF_cycle ha_out by (by100 blast)
    next
      assume hcase: "F = {b} \<or> F = e"
      show False
      proof (rule disjE[OF hcase])
        assume hF: "F = {b}"
        show False
          using hF hF_cycle hb_out by (by100 blast)
      next
        assume hF: "F = e"
        show False
          using hF hF_cycle he_out by (by100 blast)
      qed
    qed
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_period_cycle_complement_face_closed_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes hsigmaL: "\<sigma> \<in> L"
  assumes hsigma_out: "\<sigma> \<notin> ((\<lambda>v. {v}) `
        ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
      \<union> ((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p})"
  assumes hface: "geotop_is_face \<tau> \<sigma>"
  shows "\<tau> \<notin> ((\<lambda>v. {v}) `
        ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
      \<union> ((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p})"
proof -
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  let ?SV = "(\<lambda>v. {v}) ` (?v ` {0..<p})"
  let ?E = "((\<lambda>j. closed_segment (?v j) (?v (Suc j))) ` {0..<p})"
  have h1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_prefix[OF hL])
  have hcases: "(\<exists>v. \<sigma> = {v}) \<or>
      (\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b)"
    by (rule geotop_1dim_simplex_cases[OF h1dim hsigmaL])
  show ?thesis
  proof (rule disjE[OF hcases])
    assume "\<exists>v. \<sigma> = {v}"
    then obtain v where hsigma_eq: "\<sigma> = {v}"
      by (by100 blast)
    have htau_eq: "\<tau> = {v}"
      using hface hsigma_eq geotop_singleton_face_eq_prefix by (by100 blast)
    have "\<tau> = \<sigma>"
      using htau_eq hsigma_eq by (by100 simp)
    thus ?thesis
      using hsigma_out by (by100 simp)
  next
    assume "\<exists>a b. a \<noteq> b \<and> \<sigma> = closed_segment a b"
    then obtain a b where hab: "a \<noteq> b" and hsigma_eq: "\<sigma> = closed_segment a b"
      by (by100 blast)
    have hdim: "geotop_simplex_dim (closed_segment a b) 1"
      by (rule geotop_closed_segment_is_simplex[OF hab])
    have hedge: "geotop_is_edge \<sigma>"
      using hdim hsigma_eq unfolding geotop_is_edge_def by (by100 simp)
    have hnotE: "\<sigma> \<notin> ?E"
      using hsigma_out by (by100 blast)
    show ?thesis
      by (rule geotop_degree_two_oriented_edge_successor_period_nonorbit_edge_face_outside_cycle_prefix
          [OF hL hdegree hs hp_pos hp_closed hsigmaL hedge hnotE hface])
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_period_cycle_complement_subcomplex_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  shows "geotop_is_complex
      (L - (((\<lambda>v. {v}) `
        ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
      \<union> ((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p})))"
proof -
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  let ?Kc = "((\<lambda>v. {v}) ` (?v ` {0..<p}))
      \<union> ((\<lambda>j. closed_segment (?v j) (?v (Suc j))) ` {0..<p})"
  let ?R = "L - ?Kc"
  have hcomplexL: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have hL_simplex: "\<forall>\<sigma>\<in>L. geotop_is_simplex \<sigma>"
    by (rule geotop_is_complex_simplex[OF hcomplexL])
  have hR_fin: "finite ?R"
    using hfin by (by100 simp)
  have hsimplex: "\<forall>\<sigma>\<in>?R. geotop_is_simplex \<sigma>"
  proof
    fix \<sigma>
    assume hsigmaR: "\<sigma> \<in> ?R"
    have hsigmaL: "\<sigma> \<in> L"
      using hsigmaR by (by100 simp)
    show "geotop_is_simplex \<sigma>"
      using hL_simplex hsigmaL by (by100 blast)
  qed
  have hfaces: "\<forall>\<sigma>\<in>?R. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> ?R"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau>
    assume hsigmaR: "\<sigma> \<in> ?R"
    assume hface: "geotop_is_face \<tau> \<sigma>"
    have hsigmaL: "\<sigma> \<in> L"
      using hsigmaR by (by100 simp)
    have hsigma_out: "\<sigma> \<notin> ?Kc"
      using hsigmaR by (by100 simp)
    have htauL: "\<tau> \<in> L"
      using geotop_is_complex_face_closed[OF hcomplexL] hsigmaL hface by (by100 blast)
    have htau_out: "\<tau> \<notin> ?Kc"
      by (rule geotop_degree_two_oriented_edge_successor_period_cycle_complement_face_closed_prefix
          [OF hL hdegree hs hp_pos hp_closed hsigmaL hsigma_out hface])
    show "\<tau> \<in> ?R"
      using htauL htau_out by (by100 simp)
  qed
  have hinter:
      "\<forall>\<sigma>\<in>?R. \<forall>\<tau>\<in>?R. \<sigma> \<inter> \<tau> \<noteq> {}
        \<longrightarrow> geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma>
          \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
  proof (intro ballI impI)
    fix \<sigma> \<tau>
    assume hsigmaR: "\<sigma> \<in> ?R"
    assume htauR: "\<tau> \<in> ?R"
    assume hne: "\<sigma> \<inter> \<tau> \<noteq> {}"
    have hsigmaL: "\<sigma> \<in> L"
      using hsigmaR by (by100 simp)
    have htauL: "\<tau> \<in> L"
      using htauR by (by100 simp)
    have hL_inter: "\<forall>\<sigma>\<in>L. \<forall>\<tau>\<in>L. \<sigma> \<inter> \<tau> \<noteq> {}
        \<longrightarrow> geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma>
          \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
      by (rule geotop_is_complex_intersection[OF hcomplexL])
    show "geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma>
        \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
      using hL_inter hsigmaL htauL hne by (by100 blast)
  qed
  have hlocfin: "\<forall>\<sigma>\<in>?R. \<exists>U. open U \<and> \<sigma> \<subseteq> U
      \<and> finite {\<tau>\<in>?R. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma>
    assume hsigmaR: "\<sigma> \<in> ?R"
    show "\<exists>U. open U \<and> \<sigma> \<subseteq> U
        \<and> finite {\<tau>\<in>?R. \<tau> \<inter> U \<noteq> {}}"
    proof (rule exI[where x = "UNIV"])
      show "open UNIV \<and> \<sigma> \<subseteq> UNIV
          \<and> finite {\<tau> \<in> ?R. \<tau> \<inter> UNIV \<noteq> {}}"
        using hR_fin by (by100 simp)
    qed
  qed
  show ?thesis
    unfolding geotop_is_complex_def
    using hsimplex hfaces hinter hlocfin by (by100 blast)
qed

lemma geotop_degree_two_oriented_edge_successor_period_cycle_exhausts_connected_graph_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  shows "L =
      (((\<lambda>v. {v}) `
        ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
      \<union> ((\<lambda>j. closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ j) s))
        (fst ((geotop_oriented_edge_successor L ^^ Suc j) s))) ` {0..<p}))"
proof -
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  let ?Kc = "((\<lambda>v. {v}) ` (?v ` {0..<p}))
      \<union> ((\<lambda>j. closed_segment (?v j) (?v (Suc j))) ` {0..<p})"
  let ?R = "L - ?Kc"
  have hKc_pkg: "geotop_is_complex ?Kc \<and> ?Kc \<subseteq> L"
    by (rule geotop_degree_two_oriented_edge_successor_period_cycle_subcomplex_prefix
        [OF hL hdegree hs hp_pos hp_closed])
  have hKc_complex: "geotop_is_complex ?Kc"
    using hKc_pkg by (by100 blast)
  have hKc_sub: "?Kc \<subseteq> L"
    using hKc_pkg by (by100 blast)
  have hR_complex: "geotop_is_complex ?R"
    by (rule geotop_degree_two_oriented_edge_successor_period_cycle_complement_subcomplex_prefix
        [OF hL hfin hdegree hs hp_pos hp_closed])
  have hKc_nonempty: "?Kc \<noteq> {}"
  proof -
    have h0: "0 \<in> {0..<p}"
      using hp_pos by (by100 simp)
    have "{?v 0} \<in> ((\<lambda>v. {v}) ` (?v ` {0..<p}))"
    proof (rule image_eqI[where x = "?v 0"])
      show "{?v 0} = {?v 0}"
        by (by100 simp)
      show "?v 0 \<in> ?v ` {0..<p}"
      proof (rule image_eqI[where x = 0])
        show "?v 0 = ?v 0"
          by (by100 simp)
        show "0 \<in> {0..<p}"
          by (rule h0)
      qed
    qed
    hence "{?v 0} \<in> ?Kc"
      by (by100 blast)
    thus ?thesis
      by (by100 blast)
  qed
  show ?thesis
  proof (rule ccontr)
    assume hneq: "L \<noteq> ?Kc"
    have hnot_sub: "\<not> L \<subseteq> ?Kc"
    proof
      assume hsub: "L \<subseteq> ?Kc"
      have "L = ?Kc"
      proof
        show "L \<subseteq> ?Kc"
          by (rule hsub)
      next
        show "?Kc \<subseteq> L"
          by (rule hKc_sub)
      qed
      thus False
        using hneq by (by100 blast)
    qed
    have hR_nonempty: "?R \<noteq> {}"
    proof -
      obtain \<sigma> where h\<sigma>L: "\<sigma> \<in> L" and h\<sigma>out: "\<sigma> \<notin> ?Kc"
        using hnot_sub by (by100 blast)
      have "\<sigma> \<in> ?R"
        using h\<sigma>L h\<sigma>out by (by100 simp)
      thus ?thesis
        by (by100 blast)
    qed
    have hdisj: "?Kc \<inter> ?R = {}"
      by (by100 blast)
    have hsplit: "L = ?Kc \<union> ?R"
    proof
      show "L \<subseteq> ?Kc \<union> ?R"
        by (by100 blast)
    next
      show "?Kc \<union> ?R \<subseteq> L"
        using hKc_sub by (by100 blast)
    qed
    have hbad: "\<exists>K1 K2. K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {}
        \<and> L = K1 \<union> K2 \<and> geotop_is_complex K1 \<and> geotop_is_complex K2"
    proof (intro exI)
      show "?Kc \<noteq> {} \<and> ?R \<noteq> {} \<and> ?Kc \<inter> ?R = {}
          \<and> L = ?Kc \<union> ?R \<and> geotop_is_complex ?Kc \<and> geotop_is_complex ?R"
        using hKc_nonempty hR_nonempty hdisj hsplit hKc_complex hR_complex
        by (by100 blast)
    qed
    have hno_bad: "\<not> (\<exists>K1 K2. K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {}
        \<and> L = K1 \<union> K2 \<and> geotop_is_complex K1 \<and> geotop_is_complex K2)"
      using hconn unfolding geotop_complex_connected_def by (by100 blast)
    show False
      using hbad hno_bad by (by100 blast)
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_period_vertex_in_exhausted_cycle_prefix:
  fixes L :: "(real^2) set set" and P :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes hPL: "{P} \<in> L"
  shows "P \<in> ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p})"
proof -
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  let ?V = "?v ` {0..<p}"
  let ?SV = "(\<lambda>v. {v}) ` ?V"
  let ?E = "((\<lambda>j. closed_segment (?v j) (?v (Suc j))) ` {0..<p})"
  have hL_eq: "L = ?SV \<union> ?E"
    by (rule geotop_degree_two_oriented_edge_successor_period_cycle_exhausts_connected_graph_prefix
        [OF hL hfin hconn hdegree hs hp_pos hp_closed])
  have hP_cycle: "{P} \<in> ?SV \<union> ?E"
    using hPL hL_eq by (by100 simp)
  show ?thesis
  proof (rule UnE[OF hP_cycle])
    assume hPSV: "{P} \<in> ?SV"
    obtain v where hvV: "v \<in> ?V" and hPv: "{P} = {v}"
      using hPSV by (by100 blast)
    show "P \<in> ?V"
      using hvV hPv by (by100 simp)
  next
    assume hPE: "{P} \<in> ?E"
    show "P \<in> ?V"
    proof -
      have False
        by (rule geotop_degree_two_oriented_edge_successor_period_edge_orbit_no_singletons_prefix
            [OF hL hdegree hs hPE])
      thus ?thesis
        by (rule FalseE)
    qed
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_period_two_vertices_indices_prefix:
  fixes L :: "(real^2) set set" and P Q :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes hPL: "{P} \<in> L"
  assumes hQL: "{Q} \<in> L"
  assumes hPQ: "P \<noteq> Q"
  shows "\<exists>i j. i \<in> {0..<p} \<and> j \<in> {0..<p} \<and> i \<noteq> j
      \<and> P = fst ((geotop_oriented_edge_successor L ^^ i) s)
      \<and> Q = fst ((geotop_oriented_edge_successor L ^^ j) s)"
proof -
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  have hP_orbit: "P \<in> ?v ` {0..<p}"
    by (rule geotop_degree_two_oriented_edge_successor_period_vertex_in_exhausted_cycle_prefix
        [OF hL hfin hconn hdegree hs hp_pos hp_closed hPL])
  have hQ_orbit: "Q \<in> ?v ` {0..<p}"
    by (rule geotop_degree_two_oriented_edge_successor_period_vertex_in_exhausted_cycle_prefix
        [OF hL hfin hconn hdegree hs hp_pos hp_closed hQL])
  obtain i where hi: "i \<in> {0..<p}" and hPi: "P = ?v i"
    using hP_orbit by (by100 blast)
  obtain j where hj: "j \<in> {0..<p}" and hQj: "Q = ?v j"
    using hQ_orbit by (by100 blast)
  have hij: "i \<noteq> j"
  proof
    assume hij_eq: "i = j"
    have "P = Q"
      using hPi hQj hij_eq by (by100 simp)
    thus False
      using hPQ by (by100 blast)
  qed
  show ?thesis
  proof (intro exI conjI)
    show "i \<in> {0..<p}" by (rule hi)
    show "j \<in> {0..<p}" by (rule hj)
    show "i \<noteq> j" by (rule hij)
    show "P = ?v i" by (rule hPi)
    show "Q = ?v j" by (rule hQj)
  qed
qed

lemma geotop_degree_two_oriented_edge_successor_period_two_vertices_ordered_indices_prefix:
  fixes L :: "(real^2) set set" and P Q :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  assumes hp_pos: "0 < p"
  assumes hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
  assumes hPL: "{P} \<in> L"
  assumes hQL: "{Q} \<in> L"
  assumes hPQ: "P \<noteq> Q"
  shows "\<exists>i j. i \<in> {0..<p} \<and> j \<in> {0..<p} \<and> i < j
      \<and> {P, Q} =
        {fst ((geotop_oriented_edge_successor L ^^ i) s),
         fst ((geotop_oriented_edge_successor L ^^ j) s)}"
proof -
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  obtain i j where hi: "i \<in> {0..<p}" and hj: "j \<in> {0..<p}" and hij_ne: "i \<noteq> j"
      and hPi: "P = ?v i" and hQj: "Q = ?v j"
    using geotop_degree_two_oriented_edge_successor_period_two_vertices_indices_prefix
      [OF hL hfin hconn hdegree hs hp_pos hp_closed hPL hQL hPQ]
    by (by100 blast)
  have horder: "i < j \<or> j < i"
    using hij_ne by (by100 linarith)
  show ?thesis
  proof (rule disjE[OF horder])
    assume hij: "i < j"
    show ?thesis
    proof (intro exI conjI)
      show "i \<in> {0..<p}" by (rule hi)
      show "j \<in> {0..<p}" by (rule hj)
      show "i < j" by (rule hij)
      show "{P, Q} = {?v i, ?v j}"
        using hPi hQj by (by100 simp)
    qed
  next
    assume hji: "j < i"
    show ?thesis
    proof (intro exI conjI)
      show "j \<in> {0..<p}" by (rule hj)
      show "i \<in> {0..<p}" by (rule hi)
      show "j < i" by (rule hji)
      show "{P, Q} = {?v j, ?v i}"
        using hPi hQj by (by100 blast)
    qed
  qed
qed

lemma geotop_degree_two_started_cycle_second_vertex_index_prefix:
  fixes L :: "(real^2) set set" and P Q :: "real^2"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hPL: "{P} \<in> L"
  assumes hQL: "{Q} \<in> L"
  assumes hPQ: "P \<noteq> Q"
  shows "\<exists>s q p j. s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> fst s = P
      \<and> q \<noteq> P
      \<and> snd s = closed_segment P q
      \<and> {q} \<in> L
      \<and> 1 < p
      \<and> fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q
      \<and> (geotop_oriented_edge_successor L ^^ p) s = s
      \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow>
          (geotop_oriented_edge_successor L ^^ k) s \<noteq> s)
      \<and> inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}
      \<and> card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p
      \<and> closed_segment (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
          (fst s) \<in> L
      \<and> geotop_is_edge
          (closed_segment (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
            (fst s))
      \<and> 0 < j
      \<and> j < p
      \<and> fst ((geotop_oriented_edge_successor L ^^ j) s) = Q
      \<and> L =
          (((\<lambda>v. {v}) `
            ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
          \<union> ((\<lambda>k. closed_segment
            (fst ((geotop_oriented_edge_successor L ^^ k) s))
            (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))) ` {0..<p}))"
  (**
    Moise Figure 3.2 cycle enumeration from the first named vertex.  The
    degree-two successor orbit starts at \<open>P\<close>, closes after its least period,
    exhausts the connected graph, and the second named vertex occurs at a
    nonzero index before the closing step. **)
proof -
  let ?S = "{(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
  obtain s q p where hpkg: "s \<in> ?S
      \<and> fst s = P
      \<and> q \<noteq> P
      \<and> snd s = closed_segment P q
      \<and> {q} \<in> L
      \<and> 1 < p
      \<and> fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q
      \<and> (geotop_oriented_edge_successor L ^^ p) s = s
      \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow>
          (geotop_oriented_edge_successor L ^^ k) s \<noteq> s)
      \<and> inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}
      \<and> card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p
      \<and> closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s) \<in> L
      \<and> geotop_is_edge
          (closed_segment
            (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s))"
    using geotop_degree_two_vertex_successor_started_cycle_edge_package_prefix
      [OF hL hfin hdegree hPL] by (elim exE)
  have hs: "s \<in> ?S"
    using hpkg by (by100 simp)
  have hfst: "fst s = P"
    using hpkg by (by100 simp)
  have hq_ne: "q \<noteq> P"
    using hpkg by (by100 simp)
  have hsnd: "snd s = closed_segment P q"
    using hpkg by (by100 simp)
  have hqL: "{q} \<in> L"
    using hpkg by (by100 simp)
  have hp_gt1: "1 < p"
    using hpkg by (by100 simp)
  have hfirst: "fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q"
    using hpkg by (by100 simp)
  have hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
    using hpkg by (by100 simp)
  have hp_min: "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
      (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
    using hpkg by (by100 simp)
  have hinj: "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
    using hpkg by (by100 simp)
  have hcard: "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
    using hpkg by (by100 simp)
  have hclosingL: "closed_segment
      (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s) \<in> L"
    using hpkg by (by100 simp)
  have hclosing_edge: "geotop_is_edge
      (closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s))"
    using hpkg by (by100 simp)
  have hp_pos: "0 < p"
    using hp_gt1 by (by100 linarith)
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  have hQ_orbit: "Q \<in> ?v ` {0..<p}"
    by (rule geotop_degree_two_oriented_edge_successor_period_vertex_in_exhausted_cycle_prefix
        [OF hL hfin hconn hdegree hs hp_pos hp_closed hQL])
  obtain j where hj: "j \<in> {0..<p}" and hQj: "?v j = Q"
    using hQ_orbit by (by100 blast)
  have hj_lt: "j < p"
    using hj by (by100 simp)
  have hj_pos: "0 < j"
  proof (rule ccontr)
    assume hnot: "\<not> 0 < j"
    have hj0: "j = 0"
      using hnot by (by100 simp)
    have "Q = P"
      using hQj hj0 hfst by (by100 simp)
    thus False
      using hPQ by (by100 blast)
  qed
  have hL_eq: "L =
      (((\<lambda>v. {v}) ` (?v ` {0..<p}))
      \<union> ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<p}))"
    by (rule geotop_degree_two_oriented_edge_successor_period_cycle_exhausts_connected_graph_prefix
        [OF hL hfin hconn hdegree hs hp_pos hp_closed])
  show ?thesis
  proof (intro exI conjI)
    show "s \<in> ?S" by (rule hs)
    show "fst s = P" by (rule hfst)
    show "q \<noteq> P" by (rule hq_ne)
    show "snd s = closed_segment P q" by (rule hsnd)
    show "{q} \<in> L" by (rule hqL)
    show "1 < p" by (rule hp_gt1)
    show "fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q"
      by (rule hfirst)
    show "(geotop_oriented_edge_successor L ^^ p) s = s"
      by (rule hp_closed)
    show "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
        (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
      by (rule hp_min)
    show "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
      by (rule hinj)
    show "card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p"
      by (rule hcard)
    show "closed_segment
        (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s) \<in> L"
      by (rule hclosingL)
    show "geotop_is_edge
        (closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s))"
      by (rule hclosing_edge)
    show "0 < j" by (rule hj_pos)
    show "j < p" by (rule hj_lt)
    show "fst ((geotop_oriented_edge_successor L ^^ j) s) = Q"
      by (rule hQj)
    show "L =
        (((\<lambda>v. {v}) `
          ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
        \<union> ((\<lambda>k. closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ k) s))
          (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))) ` {0..<p}))"
      by (rule hL_eq)
  qed
qed

lemma geotop_nat_cycle_cut_index_sets_prefix:
  fixes j p :: nat
  assumes hj_pos: "0 < j"
  assumes hj_lt: "j < p"
  shows "{0..<p} = {0..<j} \<union> {j..<p}"
    and "{0..j} \<subseteq> {0..<p}"
    and "{0..<j} \<subseteq> {0..<p}"
    and "{j..<p} \<subseteq> {0..<p}"
    and "finite {0..j}"
    and "finite ({j..<p} \<union> {p})"
proof -
  show "{0..<p} = {0..<j} \<union> {j..<p}"
    using hj_pos hj_lt by (by100 auto)
  show "{0..j} \<subseteq> {0..<p}"
    using hj_lt by (by100 auto)
  show "{0..<j} \<subseteq> {0..<p}"
    using hj_lt by (by100 auto)
  show "{j..<p} \<subseteq> {0..<p}"
    by (by100 auto)
  show "finite {0..j}"
    by (by100 simp)
  show "finite ({j..<p} \<union> {p})"
    by (by100 simp)
qed

lemma geotop_finite_nonempty_card_pos_prefix:
  fixes A :: "'a set"
  assumes hfin: "finite A"
  assumes hne: "A \<noteq> {}"
  shows "0 < card A"
proof (rule ccontr)
  assume hnot: "\<not> 0 < card A"
  have hcard0: "card A = 0"
    using hnot by (by100 simp)
  have "A = {}"
    using hfin hcard0 by (by100 simp)
  thus False
    using hne by (by100 blast)
qed

lemma geotop_subset_two_card_le2_prefix:
  fixes A :: "'a set"
  assumes hsub: "A \<subseteq> {x, y}"
  shows "card A \<le> 2"
proof -
  have hcard: "card A \<le> card {x, y}"
    by (rule card_mono[OF _ hsub]) (by100 simp)
  have hpair: "card {x, y} \<le> 2"
    by (by100 simp)
  show ?thesis
    using hcard hpair by (by100 linarith)
qed

lemma geotop_finite_connected_degree_two_linear_graph_two_vertex_boundary_split_prefix:
  fixes L :: "(real^2) set set" and P Q :: "real^2"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_fin: "finite L"
  assumes hL_conn: "geotop_complex_connected L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hPL: "{P} \<in> L"
  assumes hQL: "{Q} \<in> L"
  assumes hPQ: "P \<noteq> Q"
  shows "\<exists>C\<^sub>1 C\<^sub>2.
      geotop_polyhedron L = C\<^sub>1 \<union> C\<^sub>2
      \<and> geotop_is_broken_line C\<^sub>1
      \<and> geotop_is_broken_line C\<^sub>2
      \<and> geotop_arc_endpoints C\<^sub>1 {P, Q}
      \<and> geotop_arc_endpoints C\<^sub>2 {P, Q}
      \<and> geotop_arc_interior C\<^sub>1 {P, Q} \<inter>
          geotop_arc_interior C\<^sub>2 {P, Q} = {}"
  (**
    Moise Figure 3.2 cycle-cut step.  Enumerate the finite degree-two connected
    linear graph as a cyclic edge chain and split that cyclic order at the two
    named vertices. **)
proof -
  obtain s q p j where hpkg: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}
      \<and> fst s = P
      \<and> q \<noteq> P
      \<and> snd s = closed_segment P q
      \<and> {q} \<in> L
      \<and> 1 < p
      \<and> fst ((geotop_oriented_edge_successor L ^^ Suc 0) s) = q
      \<and> (geotop_oriented_edge_successor L ^^ p) s = s
      \<and> (\<forall>k. 0 < k \<and> k < p \<longrightarrow>
          (geotop_oriented_edge_successor L ^^ k) s \<noteq> s)
      \<and> inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}
      \<and> card ((\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) ` {0..<p}) = p
      \<and> closed_segment (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
          (fst s) \<in> L
      \<and> geotop_is_edge
          (closed_segment (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s))
            (fst s))
      \<and> 0 < j
      \<and> j < p
      \<and> fst ((geotop_oriented_edge_successor L ^^ j) s) = Q
      \<and> L =
          (((\<lambda>v. {v}) `
            ((\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)) ` {0..<p}))
          \<union> ((\<lambda>k. closed_segment
            (fst ((geotop_oriented_edge_successor L ^^ k) s))
            (fst ((geotop_oriented_edge_successor L ^^ Suc k) s))) ` {0..<p}))"
    using geotop_degree_two_started_cycle_second_vertex_index_prefix
      [OF hL_linear hL_fin hL_conn hdegree hPL hQL hPQ]
    by (elim exE)
  let ?v = "\<lambda>k. fst ((geotop_oriented_edge_successor L ^^ k) s)"
  have hs: "s \<in>
      {(v, d). {v} \<in> L \<and> d \<in> L \<and> geotop_is_edge d \<and> v \<in> d}"
    using hpkg by (by100 simp)
  have hfst: "fst s = P"
    using hpkg by (by100 simp)
  have hp_gt1: "1 < p"
    using hpkg by (by100 simp)
  have hp_closed: "(geotop_oriented_edge_successor L ^^ p) s = s"
    using hpkg by (by100 simp)
  have hp_min: "\<forall>k. 0 < k \<and> k < p \<longrightarrow>
      (geotop_oriented_edge_successor L ^^ k) s \<noteq> s"
    using hpkg by (by100 simp)
  have hinj: "inj_on (\<lambda>k. (geotop_oriented_edge_successor L ^^ k) s) {0..<p}"
    using hpkg by (by100 simp)
  have hclosingL: "closed_segment (?v (p - 1)) P \<in> L"
    using hpkg hfst by (by100 simp)
  have hclosing_edge: "geotop_is_edge (closed_segment (?v (p - 1)) P)"
    using hpkg hfst by (by100 simp)
  have hj_pos: "0 < j"
    using hpkg by (by100 simp)
  have hj_lt: "j < p"
    using hpkg by (by100 simp)
  have hQj: "?v j = Q"
    using hpkg by (by100 simp)
  have hL_cycle: "L =
      (((\<lambda>v. {v}) ` (?v ` {0..<p}))
      \<union> ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<p}))"
    using hpkg by (by100 simp)
  have hp_pos: "0 < p"
    using hp_gt1 by (by100 linarith)
  have hP0: "?v 0 = P"
    using hfst by (by100 simp)
  have hPp: "?v p = P"
    using hp_closed hfst by (by100 simp)
  have hidx_partition: "{0..<p} = {0..<j} \<union> {j..<p}"
    by (rule geotop_nat_cycle_cut_index_sets_prefix(1)[OF hj_pos hj_lt])
  have hpath1_vertices: "{0..j} \<subseteq> {0..<p}"
    by (rule geotop_nat_cycle_cut_index_sets_prefix(2)[OF hj_pos hj_lt])
  have hpath1_edges: "{0..<j} \<subseteq> {0..<p}"
    by (rule geotop_nat_cycle_cut_index_sets_prefix(3)[OF hj_pos hj_lt])
  have hpath2_edges: "{j..<p} \<subseteq> {0..<p}"
    by (rule geotop_nat_cycle_cut_index_sets_prefix(4)[OF hj_pos hj_lt])
  have hpath1_vertices_fin: "finite {0..j}"
    by (rule geotop_nat_cycle_cut_index_sets_prefix(5)[OF hj_pos hj_lt])
  have hpath2_vertices_fin: "finite ({j..<p} \<union> {p})"
    by (rule geotop_nat_cycle_cut_index_sets_prefix(6)[OF hj_pos hj_lt])
  define K\<^sub>1 where "K\<^sub>1 =
      ((\<lambda>v. {v}) ` (?v ` {0..j}))
      \<union> ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<j})"
  define K\<^sub>2 where "K\<^sub>2 =
      ((\<lambda>v. {v}) ` (?v ` ({j..<p} \<union> {p})))
      \<union> ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {j..<p})"
  have hP_K\<^sub>1: "{P} \<in> K\<^sub>1"
  proof -
    have h0mem: "0 \<in> {0..j}"
      by (by100 simp)
    have "?v 0 \<in> ?v ` {0..j}"
      by (rule imageI[OF h0mem])
    hence "{?v 0} \<in> ((\<lambda>v. {v}) ` (?v ` {0..j}))"
      by (by100 blast)
    thus ?thesis
      unfolding K\<^sub>1_def using hP0 by (by100 simp)
  qed
  have hQ_K\<^sub>1: "{Q} \<in> K\<^sub>1"
  proof -
    have hjmem: "j \<in> {0..j}"
      by (by100 simp)
    have "?v j \<in> ?v ` {0..j}"
      by (rule imageI[OF hjmem])
    hence "{?v j} \<in> ((\<lambda>v. {v}) ` (?v ` {0..j}))"
      by (by100 blast)
    thus ?thesis
      unfolding K\<^sub>1_def using hQj by (by100 simp)
  qed
  have hQ_K\<^sub>2: "{Q} \<in> K\<^sub>2"
  proof -
    have "j \<in> {j..<p} \<union> {p}"
      using hj_lt by (by100 simp)
    hence "?v j \<in> ?v ` ({j..<p} \<union> {p})"
      by (rule imageI)
    hence "{?v j} \<in> ((\<lambda>v. {v}) ` (?v ` ({j..<p} \<union> {p})))"
      by (by100 blast)
    hence hQ_vertex: "{Q} \<in> ((\<lambda>v. {v}) ` (?v ` ({j..<p} \<union> {p})))"
      using hQj by (by100 simp)
    thus ?thesis
      unfolding K\<^sub>2_def by (by100 blast)
  qed
  have hP_K\<^sub>2: "{P} \<in> K\<^sub>2"
  proof -
    have "p \<in> {j..<p} \<union> {p}"
      by (by100 simp)
    hence "?v p \<in> ?v ` ({j..<p} \<union> {p})"
      by (rule imageI)
    hence "{?v p} \<in> ((\<lambda>v. {v}) ` (?v ` ({j..<p} \<union> {p})))"
      by (by100 blast)
    hence hP_vertex: "{P} \<in> ((\<lambda>v. {v}) ` (?v ` ({j..<p} \<union> {p})))"
      using hPp by (by100 simp)
    thus ?thesis
      unfolding K\<^sub>2_def by (by100 blast)
  qed
  have hK\<^sub>1_first_edge: "closed_segment P (?v (Suc 0)) \<in> K\<^sub>1"
  proof -
    have h0: "0 \<in> {0..<j}"
      using hj_pos by (by100 simp)
    have "closed_segment (?v 0) (?v (Suc 0)) \<in>
        ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<j})"
      by (rule imageI[OF h0])
    thus ?thesis
      unfolding K\<^sub>1_def using hP0 by (by100 simp)
  qed
  have hK\<^sub>1_last_edge: "closed_segment (?v (j - 1)) Q \<in> K\<^sub>1"
  proof -
    have hj_pred_mem: "j - 1 \<in> {0..<j}"
      using hj_pos by (by100 simp)
    have hSuc_pred: "Suc (j - 1) = j"
      using hj_pos by (by100 simp)
    have "closed_segment (?v (j - 1)) (?v (Suc (j - 1))) \<in>
        ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<j})"
      by (rule imageI[OF hj_pred_mem])
    thus ?thesis
      unfolding K\<^sub>1_def using hSuc_pred hQj by (by100 simp)
  qed
  have hK\<^sub>2_first_edge: "closed_segment Q (?v (Suc j)) \<in> K\<^sub>2"
  proof -
    have hj_mem: "j \<in> {j..<p}"
      using hj_lt by (by100 simp)
    have "closed_segment (?v j) (?v (Suc j)) \<in>
        ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {j..<p})"
      by (rule imageI[OF hj_mem])
    thus ?thesis
      unfolding K\<^sub>2_def using hQj by (by100 simp)
  qed
  have hK\<^sub>2_last_edge: "closed_segment (?v (p - 1)) P \<in> K\<^sub>2"
  proof -
    have hp_pred_mem: "p - 1 \<in> {j..<p}"
      using hj_lt hp_pos by (by100 simp)
    have hSuc_pred: "Suc (p - 1) = p"
      using hp_pos by (by100 simp)
    have "closed_segment (?v (p - 1)) (?v (Suc (p - 1))) \<in>
        ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {j..<p})"
      by (rule imageI[OF hp_pred_mem])
    thus ?thesis
      unfolding K\<^sub>2_def using hSuc_pred hPp by (by100 simp)
  qed
  have hK\<^sub>1_fin: "finite K\<^sub>1"
    unfolding K\<^sub>1_def using hpath1_vertices_fin by (by100 simp)
  have hK\<^sub>2_fin: "finite K\<^sub>2"
    unfolding K\<^sub>2_def using hpath2_vertices_fin by (by100 simp)
  have hK\<^sub>1_vertex_orbit:
      "?v ` {0..j} \<subseteq> {v. {v} \<in> L}"
    by (rule geotop_degree_two_oriented_edge_successor_vertex_orbit_subset_vertices_prefix
        [OF hL_linear hdegree hs])
  have hK\<^sub>2_vertex_orbit:
      "?v ` ({j..<p} \<union> {p}) \<subseteq> {v. {v} \<in> L}"
    by (rule geotop_degree_two_oriented_edge_successor_vertex_orbit_subset_vertices_prefix
        [OF hL_linear hdegree hs])
  have hK\<^sub>1_edge_orbit:
      "((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<j})
        \<subseteq> {e\<in>L. geotop_is_edge e}"
    by (rule geotop_degree_two_oriented_edge_successor_period_closed_segment_edge_orbit_subset_edges_prefix
        [OF hL_linear hdegree hs])
  have hK\<^sub>2_edge_orbit:
      "((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {j..<p})
        \<subseteq> {e\<in>L. geotop_is_edge e}"
    by (rule geotop_degree_two_oriented_edge_successor_period_closed_segment_edge_orbit_subset_edges_prefix
        [OF hL_linear hdegree hs])
  have hK\<^sub>1_first_edge_L_edge:
      "closed_segment P (?v (Suc 0)) \<in> L
        \<and> geotop_is_edge (closed_segment P (?v (Suc 0)))"
  proof -
    have h0: "0 \<in> {0..<j}"
      using hj_pos by (by100 simp)
    have "closed_segment (?v 0) (?v (Suc 0)) \<in>
        ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<j})"
      by (rule imageI[OF h0])
    hence "closed_segment (?v 0) (?v (Suc 0)) \<in> {e\<in>L. geotop_is_edge e}"
      using hK\<^sub>1_edge_orbit by (by100 blast)
    thus ?thesis
      using hP0 by (by100 simp)
  qed
  have hK\<^sub>1_last_edge_L_edge:
      "closed_segment (?v (j - 1)) Q \<in> L
        \<and> geotop_is_edge (closed_segment (?v (j - 1)) Q)"
  proof -
    have hj_pred_mem: "j - 1 \<in> {0..<j}"
      using hj_pos by (by100 simp)
    have hSuc_pred: "Suc (j - 1) = j"
      using hj_pos by (by100 simp)
    have "closed_segment (?v (j - 1)) (?v (Suc (j - 1))) \<in>
        ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<j})"
      by (rule imageI[OF hj_pred_mem])
    hence "closed_segment (?v (j - 1)) (?v (Suc (j - 1))) \<in>
        {e\<in>L. geotop_is_edge e}"
      using hK\<^sub>1_edge_orbit by (by100 blast)
    thus ?thesis
      using hSuc_pred hQj by (by100 simp)
  qed
  have hK\<^sub>2_first_edge_L_edge:
      "closed_segment Q (?v (Suc j)) \<in> L
        \<and> geotop_is_edge (closed_segment Q (?v (Suc j)))"
  proof -
    have hj_mem: "j \<in> {j..<p}"
      using hj_lt by (by100 simp)
    have "closed_segment (?v j) (?v (Suc j)) \<in>
        ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {j..<p})"
      by (rule imageI[OF hj_mem])
    hence "closed_segment (?v j) (?v (Suc j)) \<in> {e\<in>L. geotop_is_edge e}"
      using hK\<^sub>2_edge_orbit by (by100 blast)
    thus ?thesis
      using hQj by (by100 simp)
  qed
  have hK\<^sub>2_last_edge_L_edge:
      "closed_segment (?v (p - 1)) P \<in> L
        \<and> geotop_is_edge (closed_segment (?v (p - 1)) P)"
  proof -
    have hp_pred_mem: "p - 1 \<in> {j..<p}"
      using hj_lt hp_pos by (by100 simp)
    have hSuc_pred: "Suc (p - 1) = p"
      using hp_pos by (by100 simp)
    have "closed_segment (?v (p - 1)) (?v (Suc (p - 1))) \<in>
        ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {j..<p})"
      by (rule imageI[OF hp_pred_mem])
    hence "closed_segment (?v (p - 1)) (?v (Suc (p - 1))) \<in>
        {e\<in>L. geotop_is_edge e}"
      using hK\<^sub>2_edge_orbit by (by100 blast)
    thus ?thesis
      using hSuc_pred hPp by (by100 simp)
  qed
  have hP_K\<^sub>1_incident_edge:
      "\<exists>e\<in>K\<^sub>1. geotop_is_edge e \<and> P \<in> e"
  proof -
    have hP_inc: "P \<in> closed_segment P (?v (Suc 0))"
      by (by100 simp)
    show ?thesis
      using hK\<^sub>1_first_edge hK\<^sub>1_first_edge_L_edge hP_inc by (by100 blast)
  qed
  have hQ_K\<^sub>1_incident_edge:
      "\<exists>e\<in>K\<^sub>1. geotop_is_edge e \<and> Q \<in> e"
  proof -
    have hQ_inc: "Q \<in> closed_segment (?v (j - 1)) Q"
      by (by100 simp)
    show ?thesis
      using hK\<^sub>1_last_edge hK\<^sub>1_last_edge_L_edge hQ_inc by (by100 blast)
  qed
  have hQ_K\<^sub>2_incident_edge:
      "\<exists>e\<in>K\<^sub>2. geotop_is_edge e \<and> Q \<in> e"
  proof -
    have hQ_inc: "Q \<in> closed_segment Q (?v (Suc j))"
      by (by100 simp)
    show ?thesis
      using hK\<^sub>2_first_edge hK\<^sub>2_first_edge_L_edge hQ_inc by (by100 blast)
  qed
  have hP_K\<^sub>2_incident_edge:
      "\<exists>e\<in>K\<^sub>2. geotop_is_edge e \<and> P \<in> e"
  proof -
    have hP_inc: "P \<in> closed_segment (?v (p - 1)) P"
      by (by100 simp)
    show ?thesis
      using hK\<^sub>2_last_edge hK\<^sub>2_last_edge_L_edge hP_inc by (by100 blast)
  qed
  have hK\<^sub>1_subset_L: "K\<^sub>1 \<subseteq> L"
    unfolding K\<^sub>1_def using hK\<^sub>1_vertex_orbit hK\<^sub>1_edge_orbit by (by100 blast)
  have hK\<^sub>2_subset_L: "K\<^sub>2 \<subseteq> L"
    unfolding K\<^sub>2_def using hK\<^sub>2_vertex_orbit hK\<^sub>2_edge_orbit by (by100 blast)
  have hP_L_incident_edge_cases:
      "\<forall>e\<in>L. geotop_is_edge e \<and> P \<in> e \<longrightarrow>
        e = closed_segment (?v (p - 1)) P
        \<or> e = closed_segment P (?v (Suc 0))"
  proof (intro ballI impI)
    fix e
    assume heL: "e \<in> L"
    assume hedata: "geotop_is_edge e \<and> P \<in> e"
    have hedge: "geotop_is_edge e"
      using hedata by (by100 blast)
    have hinc: "fst s \<in> e"
      using hedata hfst by (by100 simp)
    have hcases:
        "e = closed_segment
          (fst ((geotop_oriented_edge_successor L ^^ (p - 1)) s)) (fst s)
        \<or> e = closed_segment (fst s)
          (fst ((geotop_oriented_edge_successor L ^^ Suc 0) s))"
      by (rule geotop_degree_two_oriented_edge_successor_period_initial_vertex_incident_edge_cases_prefix
          [OF hL_linear hdegree hs hp_pos hp_closed heL hedge hinc])
    thus "e = closed_segment (?v (p - 1)) P
        \<or> e = closed_segment P (?v (Suc 0))"
      using hfst by (by100 simp)
  qed
  have hQ_L_incident_edge_cases:
      "\<forall>e\<in>L. geotop_is_edge e \<and> Q \<in> e \<longrightarrow>
        e = closed_segment (?v (j - 1)) Q
        \<or> e = closed_segment Q (?v (Suc j))"
  proof (intro ballI impI)
    fix e
    assume heL: "e \<in> L"
    assume hedata: "geotop_is_edge e \<and> Q \<in> e"
    have hedge: "geotop_is_edge e"
      using hedata by (by100 blast)
    have hinc: "?v j \<in> e"
      using hedata hQj by (by100 simp)
    have hcases:
        "e = closed_segment
          (?v (if j = 0 then p - 1 else j - 1)) (?v j)
        \<or> e = closed_segment (?v j) (?v (Suc j))"
      by (rule geotop_degree_two_oriented_edge_successor_period_vertex_incident_edge_cases_prefix
          [OF hL_linear hdegree hs hp_pos hp_closed hj_lt heL hedge hinc])
    have hj_ne0: "j \<noteq> 0"
      using hj_pos by (by100 simp)
    thus "e = closed_segment (?v (j - 1)) Q
        \<or> e = closed_segment Q (?v (Suc j))"
      using hcases hQj by (by100 simp)
  qed
  have hP_K\<^sub>1_incident_edge_cases:
      "{e\<in>K\<^sub>1. geotop_is_edge e \<and> P \<in> e}
        \<subseteq> {closed_segment (?v (p - 1)) P,
            closed_segment P (?v (Suc 0))}"
    using hP_L_incident_edge_cases hK\<^sub>1_subset_L by (by100 blast)
  have hP_K\<^sub>2_incident_edge_cases:
      "{e\<in>K\<^sub>2. geotop_is_edge e \<and> P \<in> e}
        \<subseteq> {closed_segment (?v (p - 1)) P,
            closed_segment P (?v (Suc 0))}"
    using hP_L_incident_edge_cases hK\<^sub>2_subset_L by (by100 blast)
  have hQ_K\<^sub>1_incident_edge_cases:
      "{e\<in>K\<^sub>1. geotop_is_edge e \<and> Q \<in> e}
        \<subseteq> {closed_segment (?v (j - 1)) Q,
            closed_segment Q (?v (Suc j))}"
    using hQ_L_incident_edge_cases hK\<^sub>1_subset_L by (by100 blast)
  have hQ_K\<^sub>2_incident_edge_cases:
      "{e\<in>K\<^sub>2. geotop_is_edge e \<and> Q \<in> e}
        \<subseteq> {closed_segment (?v (j - 1)) Q,
            closed_segment Q (?v (Suc j))}"
    using hQ_L_incident_edge_cases hK\<^sub>2_subset_L by (by100 blast)
  have hP_K\<^sub>1_incident_nonempty:
      "{e\<in>K\<^sub>1. geotop_is_edge e \<and> P \<in> e} \<noteq> {}"
    using hP_K\<^sub>1_incident_edge by (by100 blast)
  have hP_K\<^sub>2_incident_nonempty:
      "{e\<in>K\<^sub>2. geotop_is_edge e \<and> P \<in> e} \<noteq> {}"
    using hP_K\<^sub>2_incident_edge by (by100 blast)
  have hQ_K\<^sub>1_incident_nonempty:
      "{e\<in>K\<^sub>1. geotop_is_edge e \<and> Q \<in> e} \<noteq> {}"
    using hQ_K\<^sub>1_incident_edge by (by100 blast)
  have hQ_K\<^sub>2_incident_nonempty:
      "{e\<in>K\<^sub>2. geotop_is_edge e \<and> Q \<in> e} \<noteq> {}"
    using hQ_K\<^sub>2_incident_edge by (by100 blast)
  have hP_K\<^sub>1_incident_card_pos:
      "0 < card {e\<in>K\<^sub>1. geotop_is_edge e \<and> P \<in> e}"
  proof -
    have hfin: "finite {e\<in>K\<^sub>1. geotop_is_edge e \<and> P \<in> e}"
      using hK\<^sub>1_fin by (by100 simp)
    show ?thesis
      by (rule geotop_finite_nonempty_card_pos_prefix
          [OF hfin hP_K\<^sub>1_incident_nonempty])
  qed
  have hP_K\<^sub>2_incident_card_pos:
      "0 < card {e\<in>K\<^sub>2. geotop_is_edge e \<and> P \<in> e}"
  proof -
    have hfin: "finite {e\<in>K\<^sub>2. geotop_is_edge e \<and> P \<in> e}"
      using hK\<^sub>2_fin by (by100 simp)
    show ?thesis
      by (rule geotop_finite_nonempty_card_pos_prefix
          [OF hfin hP_K\<^sub>2_incident_nonempty])
  qed
  have hQ_K\<^sub>1_incident_card_pos:
      "0 < card {e\<in>K\<^sub>1. geotop_is_edge e \<and> Q \<in> e}"
  proof -
    have hfin: "finite {e\<in>K\<^sub>1. geotop_is_edge e \<and> Q \<in> e}"
      using hK\<^sub>1_fin by (by100 simp)
    show ?thesis
      by (rule geotop_finite_nonempty_card_pos_prefix
          [OF hfin hQ_K\<^sub>1_incident_nonempty])
  qed
  have hQ_K\<^sub>2_incident_card_pos:
      "0 < card {e\<in>K\<^sub>2. geotop_is_edge e \<and> Q \<in> e}"
  proof -
    have hfin: "finite {e\<in>K\<^sub>2. geotop_is_edge e \<and> Q \<in> e}"
      using hK\<^sub>2_fin by (by100 simp)
    show ?thesis
      by (rule geotop_finite_nonempty_card_pos_prefix
          [OF hfin hQ_K\<^sub>2_incident_nonempty])
  qed
  have hP_K\<^sub>1_incident_card_le2:
      "card {e\<in>K\<^sub>1. geotop_is_edge e \<and> P \<in> e} \<le> 2"
    by (rule geotop_subset_two_card_le2_prefix[OF hP_K\<^sub>1_incident_edge_cases])
  have hP_K\<^sub>2_incident_card_le2:
      "card {e\<in>K\<^sub>2. geotop_is_edge e \<and> P \<in> e} \<le> 2"
    by (rule geotop_subset_two_card_le2_prefix[OF hP_K\<^sub>2_incident_edge_cases])
  have hQ_K\<^sub>1_incident_card_le2:
      "card {e\<in>K\<^sub>1. geotop_is_edge e \<and> Q \<in> e} \<le> 2"
    by (rule geotop_subset_two_card_le2_prefix[OF hQ_K\<^sub>1_incident_edge_cases])
  have hQ_K\<^sub>2_incident_card_le2:
      "card {e\<in>K\<^sub>2. geotop_is_edge e \<and> Q \<in> e} \<le> 2"
    by (rule geotop_subset_two_card_le2_prefix[OF hQ_K\<^sub>2_incident_edge_cases])
  have hP_K\<^sub>1_incident_card_one_or_two:
      "card {e\<in>K\<^sub>1. geotop_is_edge e \<and> P \<in> e} = 1
        \<or> card {e\<in>K\<^sub>1. geotop_is_edge e \<and> P \<in> e} = 2"
    using hP_K\<^sub>1_incident_card_pos hP_K\<^sub>1_incident_card_le2 by (by100 linarith)
  have hP_K\<^sub>2_incident_card_one_or_two:
      "card {e\<in>K\<^sub>2. geotop_is_edge e \<and> P \<in> e} = 1
        \<or> card {e\<in>K\<^sub>2. geotop_is_edge e \<and> P \<in> e} = 2"
    using hP_K\<^sub>2_incident_card_pos hP_K\<^sub>2_incident_card_le2 by (by100 linarith)
  have hQ_K\<^sub>1_incident_card_one_or_two:
      "card {e\<in>K\<^sub>1. geotop_is_edge e \<and> Q \<in> e} = 1
        \<or> card {e\<in>K\<^sub>1. geotop_is_edge e \<and> Q \<in> e} = 2"
    using hQ_K\<^sub>1_incident_card_pos hQ_K\<^sub>1_incident_card_le2 by (by100 linarith)
  have hQ_K\<^sub>2_incident_card_one_or_two:
      "card {e\<in>K\<^sub>2. geotop_is_edge e \<and> Q \<in> e} = 1
        \<or> card {e\<in>K\<^sub>2. geotop_is_edge e \<and> Q \<in> e} = 2"
    using hQ_K\<^sub>2_incident_card_pos hQ_K\<^sub>2_incident_card_le2 by (by100 linarith)
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL_linear])
  have hL_1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_prefix[OF hL_linear])
  have hK\<^sub>1_simplex: "\<forall>\<sigma>\<in>K\<^sub>1. geotop_is_simplex \<sigma>"
    using geotop_is_complex_simplex[OF hL_complex] hK\<^sub>1_subset_L by (by100 blast)
  have hK\<^sub>2_simplex: "\<forall>\<sigma>\<in>K\<^sub>2. geotop_is_simplex \<sigma>"
    using geotop_is_complex_simplex[OF hL_complex] hK\<^sub>2_subset_L by (by100 blast)
  have hK\<^sub>1_1dim: "geotop_complex_is_1dim K\<^sub>1"
    unfolding geotop_complex_is_1dim_def
    using hL_1dim hK\<^sub>1_subset_L unfolding geotop_complex_is_1dim_def by (by100 blast)
  have hK\<^sub>2_1dim: "geotop_complex_is_1dim K\<^sub>2"
    unfolding geotop_complex_is_1dim_def
    using hL_1dim hK\<^sub>2_subset_L unfolding geotop_complex_is_1dim_def by (by100 blast)
  have hK\<^sub>1_edge_left_vertex:
      "\<forall>k\<in>{0..<j}. {?v k} \<in> K\<^sub>1"
  proof
    fix k
    assume hk: "k \<in> {0..<j}"
    have "k \<in> {0..j}"
      using hk by (by100 simp)
    hence "?v k \<in> ?v ` {0..j}"
      by (rule imageI)
    hence "{?v k} \<in> ((\<lambda>v. {v}) ` (?v ` {0..j}))"
      by (by100 blast)
    thus "{?v k} \<in> K\<^sub>1"
      unfolding K\<^sub>1_def by (by100 blast)
  qed
  have hK\<^sub>1_edge_right_vertex:
      "\<forall>k\<in>{0..<j}. {?v (Suc k)} \<in> K\<^sub>1"
  proof
    fix k
    assume hk: "k \<in> {0..<j}"
    have "Suc k \<in> {0..j}"
      using hk by (by100 simp)
    hence "?v (Suc k) \<in> ?v ` {0..j}"
      by (rule imageI)
    hence "{?v (Suc k)} \<in> ((\<lambda>v. {v}) ` (?v ` {0..j}))"
      by (by100 blast)
    thus "{?v (Suc k)} \<in> K\<^sub>1"
      unfolding K\<^sub>1_def by (by100 blast)
  qed
  have hK\<^sub>2_edge_left_vertex:
      "\<forall>k\<in>{j..<p}. {?v k} \<in> K\<^sub>2"
  proof
    fix k
    assume hk: "k \<in> {j..<p}"
    have "k \<in> {j..<p} \<union> {p}"
      using hk by (by100 blast)
    hence "?v k \<in> ?v ` ({j..<p} \<union> {p})"
      by (rule imageI)
    hence "{?v k} \<in> ((\<lambda>v. {v}) ` (?v ` ({j..<p} \<union> {p})))"
      by (by100 blast)
    thus "{?v k} \<in> K\<^sub>2"
      unfolding K\<^sub>2_def by (by100 blast)
  qed
  have hK\<^sub>2_edge_right_vertex:
      "\<forall>k\<in>{j..<p}. {?v (Suc k)} \<in> K\<^sub>2"
  proof
    fix k
    assume hk: "k \<in> {j..<p}"
    have "Suc k \<in> {j..<p} \<union> {p}"
      using hk by (by100 auto)
    hence "?v (Suc k) \<in> ?v ` ({j..<p} \<union> {p})"
      by (rule imageI)
    hence "{?v (Suc k)} \<in> ((\<lambda>v. {v}) ` (?v ` ({j..<p} \<union> {p})))"
      by (by100 blast)
    thus "{?v (Suc k)} \<in> K\<^sub>2"
      unfolding K\<^sub>2_def by (by100 blast)
  qed
  have hsucc_ne: "\<forall>k. ?v (Suc k) \<noteq> ?v k"
  proof
    fix k
    show "?v (Suc k) \<noteq> ?v k"
      by (rule geotop_degree_two_oriented_edge_successor_funpow_next_vertex_distinct_prefix
          [OF hL_linear hdegree hs])
  qed
  have hK\<^sub>1_face_closed:
      "\<forall>\<sigma>\<in>K\<^sub>1. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K\<^sub>1"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau>
    assume h\<sigma>K: "\<sigma> \<in> K\<^sub>1"
    assume hface: "geotop_is_face \<tau> \<sigma>"
    have h\<sigma>cases: "\<sigma> \<in> ((\<lambda>v. {v}) ` (?v ` {0..j}))
        \<or> \<sigma> \<in> ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<j})"
      using h\<sigma>K unfolding K\<^sub>1_def by (by100 blast)
    show "\<tau> \<in> K\<^sub>1"
    proof (rule disjE[OF h\<sigma>cases])
      assume h\<sigma>vertex: "\<sigma> \<in> ((\<lambda>v. {v}) ` (?v ` {0..j}))"
      obtain v where hv: "v \<in> ?v ` {0..j}" and h\<sigma>eq: "\<sigma> = {v}"
        using h\<sigma>vertex by (by100 blast)
      have "\<tau> = {v}"
        using hface h\<sigma>eq geotop_singleton_face_eq_prefix by (by100 blast)
      thus "\<tau> \<in> K\<^sub>1"
        unfolding K\<^sub>1_def using hv by (by100 blast)
    next
      assume h\<sigma>edge:
          "\<sigma> \<in> ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<j})"
      obtain k where hk: "k \<in> {0..<j}"
        and h\<sigma>eq: "\<sigma> = closed_segment (?v k) (?v (Suc k))"
        using h\<sigma>edge by (by100 blast)
      have hne_rev: "?v (Suc k) \<noteq> ?v k"
        using hsucc_ne by (by100 blast)
      have hne: "?v k \<noteq> ?v (Suc k)"
      proof
        assume heq: "?v k = ?v (Suc k)"
        have heq_rev: "?v (Suc k) = ?v k"
          using heq by (by100 simp)
        show False
          by (rule notE[OF hne_rev heq_rev])
      qed
      have hface_seg: "geotop_is_face \<tau> (closed_segment (?v k) (?v (Suc k)))"
        using hface h\<sigma>eq by (by100 simp)
      have hcases: "\<tau> = {?v k} \<or> \<tau> = {?v (Suc k)}
          \<or> \<tau> = closed_segment (?v k) (?v (Suc k))"
        by (rule geotop_closed_segment_face_endpoint_or_self_prefix[OF hne hface_seg])
      show "\<tau> \<in> K\<^sub>1"
      proof (rule disjE[OF hcases])
        assume "\<tau> = {?v k}"
        thus ?thesis
          using hK\<^sub>1_edge_left_vertex hk by (by100 blast)
      next
        assume hright_or_self:
            "\<tau> = {?v (Suc k)} \<or> \<tau> = closed_segment (?v k) (?v (Suc k))"
        show ?thesis
        proof (rule disjE[OF hright_or_self])
          assume "\<tau> = {?v (Suc k)}"
          thus ?thesis
            using hK\<^sub>1_edge_right_vertex hk by (by100 blast)
        next
          assume "\<tau> = closed_segment (?v k) (?v (Suc k))"
          thus ?thesis
            unfolding K\<^sub>1_def using hk by (by100 blast)
        qed
      qed
    qed
  qed
  have hK\<^sub>2_face_closed:
      "\<forall>\<sigma>\<in>K\<^sub>2. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K\<^sub>2"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau>
    assume h\<sigma>K: "\<sigma> \<in> K\<^sub>2"
    assume hface: "geotop_is_face \<tau> \<sigma>"
    have h\<sigma>cases: "\<sigma> \<in> ((\<lambda>v. {v}) ` (?v ` ({j..<p} \<union> {p})))
        \<or> \<sigma> \<in> ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {j..<p})"
      using h\<sigma>K unfolding K\<^sub>2_def by (by100 blast)
    show "\<tau> \<in> K\<^sub>2"
    proof (rule disjE[OF h\<sigma>cases])
      assume h\<sigma>vertex: "\<sigma> \<in> ((\<lambda>v. {v}) ` (?v ` ({j..<p} \<union> {p})))"
      obtain v where hv: "v \<in> ?v ` ({j..<p} \<union> {p})" and h\<sigma>eq: "\<sigma> = {v}"
        using h\<sigma>vertex by (by100 blast)
      have "\<tau> = {v}"
        using hface h\<sigma>eq geotop_singleton_face_eq_prefix by (by100 blast)
      thus "\<tau> \<in> K\<^sub>2"
        unfolding K\<^sub>2_def using hv by (by100 blast)
    next
      assume h\<sigma>edge:
          "\<sigma> \<in> ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {j..<p})"
      obtain k where hk: "k \<in> {j..<p}"
        and h\<sigma>eq: "\<sigma> = closed_segment (?v k) (?v (Suc k))"
        using h\<sigma>edge by (by100 blast)
      have hne_rev: "?v (Suc k) \<noteq> ?v k"
        using hsucc_ne by (by100 blast)
      have hne: "?v k \<noteq> ?v (Suc k)"
      proof
        assume heq: "?v k = ?v (Suc k)"
        have heq_rev: "?v (Suc k) = ?v k"
          using heq by (by100 simp)
        show False
          by (rule notE[OF hne_rev heq_rev])
      qed
      have hface_seg: "geotop_is_face \<tau> (closed_segment (?v k) (?v (Suc k)))"
        using hface h\<sigma>eq by (by100 simp)
      have hcases: "\<tau> = {?v k} \<or> \<tau> = {?v (Suc k)}
          \<or> \<tau> = closed_segment (?v k) (?v (Suc k))"
        by (rule geotop_closed_segment_face_endpoint_or_self_prefix[OF hne hface_seg])
      show "\<tau> \<in> K\<^sub>2"
      proof (rule disjE[OF hcases])
        assume "\<tau> = {?v k}"
        thus ?thesis
          using hK\<^sub>2_edge_left_vertex hk by (by100 blast)
      next
        assume hright_or_self:
            "\<tau> = {?v (Suc k)} \<or> \<tau> = closed_segment (?v k) (?v (Suc k))"
        show ?thesis
        proof (rule disjE[OF hright_or_self])
          assume "\<tau> = {?v (Suc k)}"
          thus ?thesis
            using hK\<^sub>2_edge_right_vertex hk by (by100 blast)
        next
          assume "\<tau> = closed_segment (?v k) (?v (Suc k))"
          thus ?thesis
            unfolding K\<^sub>2_def using hk by (by100 blast)
        qed
      qed
    qed
  qed
  have hK\<^sub>1_intersection:
      "\<forall>\<sigma>\<in>K\<^sub>1. \<forall>\<tau>\<in>K\<^sub>1. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
        geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using geotop_is_complex_intersection[OF hL_complex] hK\<^sub>1_subset_L by (by100 blast)
  have hK\<^sub>2_intersection:
      "\<forall>\<sigma>\<in>K\<^sub>2. \<forall>\<tau>\<in>K\<^sub>2. \<sigma> \<inter> \<tau> \<noteq> {} \<longrightarrow>
        geotop_is_face (\<sigma> \<inter> \<tau>) \<sigma> \<and> geotop_is_face (\<sigma> \<inter> \<tau>) \<tau>"
    using geotop_is_complex_intersection[OF hL_complex] hK\<^sub>2_subset_L by (by100 blast)
  have hK\<^sub>1_locally_finite:
      "\<forall>\<sigma>\<in>K\<^sub>1. \<exists>U. open U \<and> \<sigma> \<subseteq> U
        \<and> finite {\<tau>\<in>K\<^sub>1. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma>
    assume "\<sigma> \<in> K\<^sub>1"
    show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K\<^sub>1. \<tau> \<inter> U \<noteq> {}}"
    proof (intro exI conjI)
      show "open UNIV"
        by (by100 simp)
      show "\<sigma> \<subseteq> UNIV"
        by (by100 simp)
      show "finite {\<tau> \<in> K\<^sub>1. \<tau> \<inter> UNIV \<noteq> {}}"
        using hK\<^sub>1_fin by (by100 simp)
    qed
  qed
  have hK\<^sub>2_locally_finite:
      "\<forall>\<sigma>\<in>K\<^sub>2. \<exists>U. open U \<and> \<sigma> \<subseteq> U
        \<and> finite {\<tau>\<in>K\<^sub>2. \<tau> \<inter> U \<noteq> {}}"
  proof
    fix \<sigma>
    assume "\<sigma> \<in> K\<^sub>2"
    show "\<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K\<^sub>2. \<tau> \<inter> U \<noteq> {}}"
    proof (intro exI conjI)
      show "open UNIV"
        by (by100 simp)
      show "\<sigma> \<subseteq> UNIV"
        by (by100 simp)
      show "finite {\<tau> \<in> K\<^sub>2. \<tau> \<inter> UNIV \<noteq> {}}"
        using hK\<^sub>2_fin by (by100 simp)
    qed
  qed
  have hK\<^sub>1_complex: "geotop_is_complex K\<^sub>1"
    unfolding geotop_is_complex_def
    using hK\<^sub>1_simplex hK\<^sub>1_face_closed hK\<^sub>1_intersection hK\<^sub>1_locally_finite
    by (by100 blast)
  have hK\<^sub>2_complex: "geotop_is_complex K\<^sub>2"
    unfolding geotop_is_complex_def
    using hK\<^sub>2_simplex hK\<^sub>2_face_closed hK\<^sub>2_intersection hK\<^sub>2_locally_finite
    by (by100 blast)
  have hK\<^sub>1_linear: "geotop_is_linear_graph K\<^sub>1"
    by (rule geotop_complex_1dim_imp_linear_graph_prefix[OF hK\<^sub>1_complex hK\<^sub>1_1dim])
  have hK\<^sub>2_linear: "geotop_is_linear_graph K\<^sub>2"
    by (rule geotop_complex_1dim_imp_linear_graph_prefix[OF hK\<^sub>2_complex hK\<^sub>2_1dim])
  have hvertex_idx_cover:
      "?v ` {0..<p} =
        ?v ` {0..j} \<union> ?v ` ({j..<p} \<union> {p})"
  proof -
    have hleft: "{0..<p} \<subseteq> {0..j} \<union> ({j..<p} \<union> {p})"
      using hidx_partition by (by100 auto)
    have hright_raw:
        "{0..j} \<union> ({j..<p} \<union> {p}) \<subseteq> {0..<p} \<union> {p}"
      using hpath1_vertices hpath2_edges by (by100 blast)
    have hright_image: "?v ` ({0..<p} \<union> {p}) \<subseteq> ?v ` {0..<p}"
    proof
      fix x
      assume hx: "x \<in> ?v ` ({0..<p} \<union> {p})"
      obtain k where hk: "k \<in> {0..<p} \<union> {p}" and hxk: "x = ?v k"
        using hx by (by100 blast)
      show "x \<in> ?v ` {0..<p}"
      proof (cases "k = p")
        case True
        have "x = ?v 0"
          using hxk True hPp hP0 by (by100 simp)
        moreover have "0 \<in> {0..<p}"
          using hp_pos by (by100 simp)
        ultimately show ?thesis
          by (by100 blast)
      next
        case False
        have "k \<in> {0..<p}"
          using hk False by (by100 blast)
        thus ?thesis
          using hxk by (by100 blast)
      qed
    qed
    show ?thesis
    proof
      show "?v ` {0..<p} \<subseteq> ?v ` {0..j} \<union> ?v ` ({j..<p} \<union> {p})"
        using hleft by (by100 blast)
      show "?v ` {0..j} \<union> ?v ` ({j..<p} \<union> {p}) \<subseteq> ?v ` {0..<p}"
      proof -
        have "?v ` ({0..j} \<union> ({j..<p} \<union> {p})) \<subseteq> ?v ` ({0..<p} \<union> {p})"
          using hright_raw by (by100 blast)
        hence "?v ` ({0..j} \<union> ({j..<p} \<union> {p})) \<subseteq> ?v ` {0..<p}"
          using hright_image by (by100 blast)
        thus ?thesis
          by (by100 blast)
      qed
    qed
  qed
  have hedge_idx_cover:
      "((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<p}) =
        ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<j})
        \<union> ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {j..<p})"
    using hidx_partition by (by100 blast)
  have hK_union_L: "K\<^sub>1 \<union> K\<^sub>2 = L"
  proof
    show "K\<^sub>1 \<union> K\<^sub>2 \<subseteq> L"
      using hK\<^sub>1_subset_L hK\<^sub>2_subset_L by (by100 blast)
    show "L \<subseteq> K\<^sub>1 \<union> K\<^sub>2"
    proof
      fix x
      assume hxL: "x \<in> L"
      have hx_cycle: "x \<in>
          ((\<lambda>v. {v}) ` (?v ` {0..<p}))
          \<union> ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<p})"
        using hxL hL_cycle by (by100 simp)
      show "x \<in> K\<^sub>1 \<union> K\<^sub>2"
      proof (cases "x \<in> ((\<lambda>v. {v}) ` (?v ` {0..<p}))")
        case True
        obtain y where hy: "y \<in> ?v ` {0..<p}" and hx_eq: "x = {y}"
          using True by (by100 blast)
        have hy_cut: "y \<in> ?v ` {0..j} \<union> ?v ` ({j..<p} \<union> {p})"
          using hy hvertex_idx_cover by (by100 blast)
        show ?thesis
        proof (cases "y \<in> ?v ` {0..j}")
          case True
          have "x \<in> K\<^sub>1"
            unfolding K\<^sub>1_def using True hx_eq by (by100 blast)
          thus ?thesis
            by (by100 blast)
        next
          case False
          have "y \<in> ?v ` ({j..<p} \<union> {p})"
            using hy_cut False by (by100 blast)
          hence "x \<in> K\<^sub>2"
            unfolding K\<^sub>2_def using hx_eq by (by100 blast)
          thus ?thesis
            by (by100 blast)
        qed
      next
        case False
        have hx_edge:
            "x \<in> ((\<lambda>k. closed_segment (?v k) (?v (Suc k))) ` {0..<p})"
          using hx_cycle False by (by100 blast)
        obtain k where hk_edge: "k \<in> {0..<p}"
          and hx_edge_eq: "x = closed_segment (?v k) (?v (Suc k))"
          using hx_edge by (by100 blast)
        have hk_cut: "k \<in> {0..<j} \<union> {j..<p}"
          using hk_edge hidx_partition by (by100 blast)
        show ?thesis
        proof (cases "k \<in> {0..<j}")
          case True
          have "x \<in> K\<^sub>1"
            unfolding K\<^sub>1_def using True hx_edge_eq by (by100 blast)
          thus ?thesis
            by (by100 blast)
        next
          case False
          have "k \<in> {j..<p}"
            using hk_cut False by (by100 blast)
          hence "x \<in> K\<^sub>2"
            unfolding K\<^sub>2_def using hx_edge_eq by (by100 blast)
          thus ?thesis
            by (by100 blast)
        qed
      qed
    qed
  qed
  have hpoly_K_union:
      "geotop_polyhedron L = geotop_polyhedron K\<^sub>1 \<union> geotop_polyhedron K\<^sub>2"
    using hK_union_L unfolding geotop_polyhedron_def by (by100 blast)
  have hcycle_cut:
      "\<exists>C\<^sub>1 C\<^sub>2.
        geotop_polyhedron L = C\<^sub>1 \<union> C\<^sub>2
        \<and> geotop_is_broken_line C\<^sub>1
        \<and> geotop_is_broken_line C\<^sub>2
        \<and> geotop_arc_endpoints C\<^sub>1 {P, Q}
        \<and> geotop_arc_endpoints C\<^sub>2 {P, Q}
        \<and> geotop_arc_interior C\<^sub>1 {P, Q} \<inter>
            geotop_arc_interior C\<^sub>2 {P, Q} = {}"
    (**
      Remaining book step: let \<open>C\<^sub>1\<close> be the carrier of the successor edges
      with indices \<open>{0..<j}\<close>, and let \<open>C\<^sub>2\<close> be the complementary carrier
      with indices \<open>{j..<p}\<close>.  The first is a finite endpoint linear graph
      from \<open>P\<close> to \<open>Q\<close>; the second is the endpoint linear graph from \<open>Q\<close>
      back to \<open>P\<close> through the closing edge. **)
    sorry
  show ?thesis
    by (rule hcycle_cut)
qed

(** Local combinatorial helper for Moise 4.8/4.9, L1. If a simplex has
    two distinct vertices, the segment on those vertices is a 1-face. **)
lemma geotop_simplex_vertices_pair_edge_face_prefix:
  fixes \<sigma> :: "(real^2) set" and V :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hv: "v \<in> V"
  assumes hw: "w \<in> V"
  assumes hvw: "v \<noteq> w"
  shows "\<exists>e. geotop_is_face e \<sigma> \<and> geotop_is_edge e \<and> v \<in> e"
proof -
  obtain m n where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hpair_sub: "{v, w} \<subseteq> V"
    using hv hw by (by100 blast)
  have hpair_fin: "finite {v, w}"
    by (by100 simp)
  have hpair_card: "card {v, w} = 2"
    using hvw by (by100 simp)
  have hpair_card_le: "card {v, w} \<le> card V"
    by (rule card_mono[OF hV_fin hpair_sub])
  have hn_ge1: "1 \<le> n"
    using hV_card hpair_card hpair_card_le by (by100 linarith)
  have hm_ge1: "1 \<le> m"
    using hn_ge1 hn_le_m by (by100 linarith)
  have hgp_pair: "geotop_general_position {v, w} m"
    by (rule geotop_general_position_subset[OF hgp hpair_sub])
  define e where "e = geotop_convex_hull {v, w}"
  have hedge_dim: "geotop_simplex_dim e 1"
    unfolding geotop_simplex_dim_def
  proof (intro exI conjI)
    show "finite {v, w}"
      by (rule hpair_fin)
    show "card {v, w} = 1 + 1"
      using hpair_card by (by100 simp)
    show "1 \<le> m"
      by (rule hm_ge1)
    show "geotop_general_position {v, w} m"
      by (rule hgp_pair)
    show "e = geotop_convex_hull {v, w}"
      unfolding e_def by (by100 simp)
  qed
  have hedge: "geotop_is_edge e"
    using hedge_dim unfolding geotop_is_edge_def by (by100 simp)
  have hface: "geotop_is_face e \<sigma>"
    unfolding geotop_is_face_def
  proof (intro exI conjI)
    show "geotop_simplex_vertices \<sigma> V"
      by (rule h\<sigma>V)
    show "{v, w} \<noteq> {}"
      by (by100 simp)
    show "{v, w} \<subseteq> V"
      by (rule hpair_sub)
    show "e = geotop_convex_hull {v, w}"
      unfolding e_def by (by100 simp)
  qed
  have hv_e: "v \<in> e"
  proof -
    have hv_hol: "v \<in> convex hull {v, w}"
      using hull_inc[of v "{v, w}"] by (by100 simp)
    have "geotop_convex_hull {v, w} = convex hull {v, w}"
      by (rule geotop_convex_hull_eq_HOL)
    thus ?thesis
      unfolding e_def using hv_hol by (by100 simp)
  qed
  show ?thesis
    using hface hedge hv_e by (by100 blast)
qed

lemma geotop_complex_simplex_vertex_incident_edge_prefix:
  fixes K :: "(real^2) set set" and \<sigma> :: "(real^2) set" and V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hv: "v \<in> V"
  assumes hw: "w \<in> V"
  assumes hvw: "v \<noteq> w"
  shows "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e"
proof -
  obtain e where hface: "geotop_is_face e \<sigma>"
    and hedge: "geotop_is_edge e"
    and hv_e: "v \<in> e"
    using geotop_simplex_vertices_pair_edge_face_prefix[OF h\<sigma>V hv hw hvw]
    by (by100 blast)
  have hface_closed: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have heK: "e \<in> K"
    using hface_closed h\<sigma>K hface by (by100 blast)
  show ?thesis
    using heK hedge hv_e by (by100 blast)
qed

lemma geotop_simplex_vertices_pair_edge_face_between_prefix:
  fixes \<sigma> :: "(real^2) set" and V :: "(real^2) set"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hv: "v \<in> V"
  assumes hw: "w \<in> V"
  assumes hvw: "v \<noteq> w"
  shows "\<exists>e. geotop_is_face e \<sigma> \<and> geotop_is_edge e \<and> v \<in> e \<and> w \<in> e"
proof -
  obtain m n where hV_fin: "finite V"
    and hV_card: "card V = n + 1"
    and hn_le_m: "n \<le> m"
    and hgp: "geotop_general_position V m"
    and h\<sigma>_eq: "\<sigma> = geotop_convex_hull V"
    using h\<sigma>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hpair_sub: "{v, w} \<subseteq> V"
    using hv hw by (by100 blast)
  have hpair_fin: "finite {v, w}"
    by (by100 simp)
  have hpair_card: "card {v, w} = 2"
    using hvw by (by100 simp)
  have hpair_card_le: "card {v, w} \<le> card V"
    by (rule card_mono[OF hV_fin hpair_sub])
  have hn_ge1: "1 \<le> n"
    using hV_card hpair_card hpair_card_le by (by100 linarith)
  have hm_ge1: "1 \<le> m"
    using hn_ge1 hn_le_m by (by100 linarith)
  have hgp_pair: "geotop_general_position {v, w} m"
    by (rule geotop_general_position_subset[OF hgp hpair_sub])
  define e where "e = geotop_convex_hull {v, w}"
  have hedge_dim: "geotop_simplex_dim e 1"
    unfolding geotop_simplex_dim_def
  proof (intro exI conjI)
    show "finite {v, w}"
      by (rule hpair_fin)
    show "card {v, w} = 1 + 1"
      using hpair_card by (by100 simp)
    show "1 \<le> m"
      by (rule hm_ge1)
    show "geotop_general_position {v, w} m"
      by (rule hgp_pair)
    show "e = geotop_convex_hull {v, w}"
      unfolding e_def by (by100 simp)
  qed
  have hedge: "geotop_is_edge e"
    using hedge_dim unfolding geotop_is_edge_def by (by100 simp)
  have hface: "geotop_is_face e \<sigma>"
    unfolding geotop_is_face_def
  proof (intro exI conjI)
    show "geotop_simplex_vertices \<sigma> V"
      by (rule h\<sigma>V)
    show "{v, w} \<noteq> {}"
      by (by100 simp)
    show "{v, w} \<subseteq> V"
      by (rule hpair_sub)
    show "e = geotop_convex_hull {v, w}"
      unfolding e_def by (by100 simp)
  qed
  have hv_e: "v \<in> e"
  proof -
    have "v \<in> convex hull {v, w}"
      using hull_inc[of v "{v, w}"] by (by100 simp)
    moreover have "geotop_convex_hull {v, w} = convex hull {v, w}"
      by (rule geotop_convex_hull_eq_HOL)
    ultimately show ?thesis
      unfolding e_def by (by100 simp)
  qed
  have hw_e: "w \<in> e"
  proof -
    have "w \<in> convex hull {v, w}"
      using hull_inc[of w "{v, w}"] by (by100 simp)
    moreover have "geotop_convex_hull {v, w} = convex hull {v, w}"
      by (rule geotop_convex_hull_eq_HOL)
    ultimately show ?thesis
      unfolding e_def by (by100 simp)
  qed
  show ?thesis
    using hface hedge hv_e hw_e by (by100 blast)
qed

lemma geotop_complex_simplex_vertices_incident_edge_between_prefix:
  fixes K :: "(real^2) set set" and \<sigma> :: "(real^2) set" and V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hv: "v \<in> V"
  assumes hw: "w \<in> V"
  assumes hvw: "v \<noteq> w"
  shows "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e \<and> w \<in> e"
proof -
  obtain e where hface: "geotop_is_face e \<sigma>"
    and hedge: "geotop_is_edge e"
    and hv_e: "v \<in> e"
    and hw_e: "w \<in> e"
    using geotop_simplex_vertices_pair_edge_face_between_prefix[OF h\<sigma>V hv hw hvw]
    by (by100 blast)
  have hface_closed: "\<forall>\<sigma>\<in>K. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> K"
    using hK unfolding geotop_is_complex_def by (by100 blast)
  have heK: "e \<in> K"
    using hface_closed h\<sigma>K hface by (by100 blast)
  show ?thesis
    using heK hedge hv_e hw_e by (by100 blast)
qed

lemma geotop_complex_no_incident_edge_simplex_vertices_singleton_prefix:
  fixes K :: "(real^2) set set" and \<sigma> :: "(real^2) set" and V :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hno_edge: "\<not> (\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e)"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>V: "geotop_simplex_vertices \<sigma> V"
  assumes hv: "v \<in> V"
  shows "V = {v}"
proof -
  have hV_sub: "V \<subseteq> {v}"
  proof
    fix w assume hw: "w \<in> V"
    show "w \<in> {v}"
    proof (rule ccontr)
      assume hw_not: "w \<notin> {v}"
      have hvw: "v \<noteq> w"
        using hw_not by (by100 simp)
      have "\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e"
        by (rule geotop_complex_simplex_vertex_incident_edge_prefix
            [OF hK h\<sigma>K h\<sigma>V hv hw hvw])
      thus False
        using hno_edge by (by100 blast)
    qed
  qed
  show ?thesis
    using hV_sub hv by (by100 blast)
qed

lemma geotop_complex_singleton_point_is_simplex_vertex_prefix:
  fixes K :: "(real^2) set set" and \<tau> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes hv\<tau>: "v \<in> \<tau>"
  shows "\<exists>V. geotop_simplex_vertices \<tau> V \<and> v \<in> V"
proof -
  have hnonempty: "{v} \<inter> \<tau> \<noteq> {}"
    using hv\<tau> by (by100 simp)
  have hface_int: "geotop_is_face ({v} \<inter> \<tau>) \<tau>"
    using hK hvK h\<tau>K hnonempty unfolding geotop_is_complex_def by (by100 blast)
  have hface: "geotop_is_face {v} \<tau>"
    using hface_int hv\<tau> by (by100 simp)
  obtain V W where h\<tau>V: "geotop_simplex_vertices \<tau> V"
    and hW_ne: "W \<noteq> {}"
    and hW_sub: "W \<subseteq> V"
    and hW_hull: "{v} = geotop_convex_hull W"
    using hface unfolding geotop_is_face_def by (by100 blast)
  obtain w where hw: "w \<in> W"
    using hW_ne by (by100 blast)
  have hw_hull: "w \<in> geotop_convex_hull W"
  proof -
    have "w \<in> convex hull W"
      using hw hull_inc[of w W] by (by100 simp)
    moreover have "geotop_convex_hull W = convex hull W"
      by (rule geotop_convex_hull_eq_HOL)
    ultimately show ?thesis by (by100 simp)
  qed
  have hw_v: "w = v"
    using hW_hull hw_hull by (by100 blast)
  have hvV: "v \<in> V"
    using hw hw_v hW_sub by (by100 blast)
  show ?thesis
    using h\<tau>V hvV by (by100 blast)
qed

lemma geotop_complex_no_incident_edge_simplex_containing_vertex_eq_singleton_prefix:
  fixes K :: "(real^2) set set" and \<tau> :: "(real^2) set"
  assumes hK: "geotop_is_complex K"
  assumes hno_edge: "\<not> (\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e)"
  assumes hvK: "{v} \<in> K"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes hv\<tau>: "v \<in> \<tau>"
  shows "\<tau> = {v}"
proof -
  obtain V where h\<tau>V: "geotop_simplex_vertices \<tau> V"
    and hvV: "v \<in> V"
    using geotop_complex_singleton_point_is_simplex_vertex_prefix[OF hK hvK h\<tau>K hv\<tau>]
    by (by100 blast)
  have hV_eq: "V = {v}"
    by (rule geotop_complex_no_incident_edge_simplex_vertices_singleton_prefix
        [OF hK hno_edge h\<tau>K h\<tau>V hvV])
  obtain m n where h\<tau>_eq: "\<tau> = geotop_convex_hull V"
    using h\<tau>V unfolding geotop_simplex_vertices_def by (by100 blast)
  have hsing_hull: "geotop_convex_hull {v} = {v}"
    using geotop_convex_hull_eq_HOL[of "{v}"] by (by100 simp)
  show ?thesis
    using h\<tau>_eq hV_eq hsing_hull by (by100 simp)
qed

lemma geotop_complex_no_incident_edge_vertex_open_singleton_prefix:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hno_edge: "\<not> (\<exists>e\<in>K. geotop_is_edge e \<and> v \<in> e)"
  shows "{v} \<in> subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K)"
proof -
  have hvK: "{v} \<in> K"
    using geotop_complex_vertices_eq_0_simplexes[OF hK] hv by (by100 blast)
  have hlocal_fin:
    "\<forall>\<sigma>\<in>K. \<exists>U. open U \<and> \<sigma> \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF hK[unfolded geotop_is_complex_def]]]])
  have hlocal_v: "\<exists>U. open U \<and> {v} \<subseteq> U \<and> finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    by (rule bspec[OF hlocal_fin hvK])
  obtain U where hU_open: "open U"
    and hvU: "{v} \<subseteq> U"
    and hU_fin: "finite {\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
    using hlocal_v by (elim exE conjE)
  let ?F = "{\<tau>\<in>K. \<tau> \<inter> U \<noteq> {}}"
  let ?Bad = "{\<tau>\<in>?F. v \<notin> \<tau>}"
  have hBad_fin: "finite ?Bad"
  proof -
    have "?Bad \<subseteq> ?F"
      by (by100 blast)
    show ?thesis
      by (rule finite_subset[OF \<open>?Bad \<subseteq> ?F\<close> hU_fin])
  qed
  have hBad_closed: "\<forall>\<tau>\<in>?Bad. closed \<tau>"
  proof
    fix \<tau> assume h\<tau>: "\<tau> \<in> ?Bad"
    have h\<tau>K: "\<tau> \<in> K"
      using h\<tau> by (by100 simp)
    show "closed \<tau>"
      by (rule geotop_complex_simplex_closed[OF hK h\<tau>K])
  qed
  have hB_closed: "closed (\<Union>?Bad)"
    by (rule closed_Union[OF hBad_fin hBad_closed])
  have hv_not_B: "v \<notin> \<Union>?Bad"
    by (by100 simp)
  define W where "W = U - \<Union>?Bad"
  have hW_open_HOL: "open W"
    unfolding W_def by (rule open_Diff[OF hU_open hB_closed])
  have hvW: "v \<in> W"
    unfolding W_def using hvU hv_not_B by (by100 simp)
  have hpoly_inter_W: "geotop_polyhedron K \<inter> W = {v}"
  proof
    show "geotop_polyhedron K \<inter> W \<subseteq> {v}"
    proof
      fix x assume hx: "x \<in> geotop_polyhedron K \<inter> W"
      have hx_poly: "x \<in> geotop_polyhedron K"
        using hx by (by100 simp)
      have hxW: "x \<in> W"
        using hx by (by100 simp)
      have hxU: "x \<in> U"
        using hxW unfolding W_def by (by100 simp)
      obtain \<tau> where h\<tau>K: "\<tau> \<in> K" and hx\<tau>: "x \<in> \<tau>"
        using hx_poly unfolding geotop_polyhedron_def by (by100 blast)
      have h\<tau>F: "\<tau> \<in> ?F"
        using h\<tau>K hx\<tau> hxU by (by100 blast)
      have hv\<tau>: "v \<in> \<tau>"
      proof (rule ccontr)
        assume hv_not: "v \<notin> \<tau>"
        have h\<tau>Bad: "\<tau> \<in> ?Bad"
          using h\<tau>F hv_not by (by100 simp)
        have "x \<in> \<Union>?Bad"
          using h\<tau>Bad hx\<tau> by (by100 blast)
        thus False
          using hxW unfolding W_def by (by100 simp)
      qed
      have h\<tau>_eq: "\<tau> = {v}"
        by (rule geotop_complex_no_incident_edge_simplex_containing_vertex_eq_singleton_prefix
            [OF hK hno_edge hvK h\<tau>K hv\<tau>])
      show "x \<in> {v}"
        using hx\<tau> h\<tau>_eq by (by100 simp)
    qed
    show "{v} \<subseteq> geotop_polyhedron K \<inter> W"
    proof
      fix x assume hx: "x \<in> {v}"
      have hxv: "x = v"
        using hx by (by100 simp)
      have hv_poly: "v \<in> geotop_polyhedron K"
        using hvK unfolding geotop_polyhedron_def by (by100 blast)
      show "x \<in> geotop_polyhedron K \<inter> W"
        using hxv hv_poly hvW by (by100 simp)
    qed
  qed
  have hW_top: "W \<in> geotop_euclidean_topology"
    by (metis hW_open_HOL geotop_euclidean_topology_eq_open_sets
        mem_Collect_eq top1_open_sets_def)
  show ?thesis
    unfolding subspace_topology_def
    using hW_top hpoly_inter_W by (by100 blast)
qed

lemma geotop_polygon_subspace_no_open_singleton_prefix:
  fixes J :: "(real^2) set"
  assumes hJ: "geotop_is_polygon J"
  assumes hwJ: "w \<in> J"
  shows "{w} \<notin> subspace_topology UNIV geotop_euclidean_topology J"
proof
  assume hsingle: "{w} \<in> subspace_topology UNIV geotop_euclidean_topology J"
  obtain U where hsingle_eq: "{w} = J \<inter> U"
    and hU_top: "U \<in> geotop_euclidean_topology"
    using hsingle unfolding subspace_topology_def by (by100 blast)
  have hU_open: "open U"
    using hU_top unfolding geotop_euclidean_topology_eq_open_sets top1_open_sets_def
    by (by100 simp)
  have hwU: "w \<in> U"
    using hsingle_eq hwJ by (by100 blast)
  have hlim: "w islimpt J"
    by (rule polygon_islimpt[OF hJ hwJ])
  obtain y where hyJ: "y \<in> J" and hyU: "y \<in> U" and hy_ne: "y \<noteq> w"
    by (rule islimptE[OF hlim hwU hU_open])
  have "y \<in> {w}"
    using hsingle_eq hyJ hyU by (by100 blast)
  thus False
    using hy_ne by (by100 simp)
qed

lemma geotop_finite_linear_graph_polygon_vertices_nonisolated_prefix:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_finite: "finite L"
  assumes hpolygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e)"
proof (intro allI impI)
  fix w
  assume hwL: "{w} \<in> L"
  have hL_complex: "geotop_is_complex L"
    using hL_linear unfolding geotop_is_linear_graph_def by (by100 blast)
  have hw_vertex: "w \<in> geotop_complex_vertices L"
    using geotop_complex_vertices_eq_0_simplexes[OF hL_complex] hwL
    by (by100 blast)
  have hw_poly: "w \<in> geotop_polyhedron L"
    using hwL unfolding geotop_polyhedron_def by (by100 blast)
  show "\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e"
  proof (rule ccontr)
    assume hno: "\<not> (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e)"
    have hsingle_open: "{w} \<in> subspace_topology UNIV
        geotop_euclidean_topology (geotop_polyhedron L)"
      by (rule geotop_complex_no_incident_edge_vertex_open_singleton_prefix
          [OF hL_complex hw_vertex hno])
    have hsingle_not_open: "{w} \<notin> subspace_topology UNIV
        geotop_euclidean_topology (geotop_polyhedron L)"
      by (rule geotop_polygon_subspace_no_open_singleton_prefix
          [OF hpolygon hw_poly])
    show False
      using hsingle_open hsingle_not_open by (by100 blast)
  qed
qed

lemma geotop_polygon_finite_linear_graph_vertices_no_endpoint_prefix:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_fin: "finite L"
  assumes hL_conn: "geotop_complex_connected L"
  assumes hL_polygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
  (**
    Moise Figure 3.2 boundary-cycle step, endpoint exclusion.  An endpoint in
    the finite polygonal graph would make the carrier a broken line, contrary
    to the polygonal 1-sphere carrier. **)
proof -
  have hnonisolated:
      "\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e)"
    by (rule geotop_finite_linear_graph_polygon_vertices_nonisolated_prefix
        [OF hL_linear hL_fin hL_polygon])
  have hnobranch:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    by (rule geotop_polygon_finite_linear_graph_vertices_no_branch_prefix
        [OF hL_linear hL_fin hL_conn hL_polygon])
  have hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  proof (intro allI impI)
    fix w
    assume hwL: "{w} \<in> L"
    let ?E = "{e\<in>L. geotop_is_edge e \<and> w \<in> e}"
    have hE_fin: "finite ?E"
      using hL_fin by (by100 simp)
    obtain e where heE: "e \<in> ?E"
      using hnonisolated hwL by (by100 blast)
    have hE_nonempty: "?E \<noteq> {}"
      using heE by (by100 blast)
    have hcard_pos: "0 < card ?E"
    proof -
      have hiff: "(0 < card ?E) = (?E \<noteq> {} \<and> finite ?E)"
        by (rule card_gt_0_iff)
      show ?thesis using hiff hE_nonempty hE_fin by (by100 blast)
    qed
    have hcard_le: "card ?E \<le> 2"
      using hnobranch hwL by (by100 blast)
    show "card ?E = 1 \<or> card ?E = 2"
      using hcard_pos hcard_le by (by100 linarith)
  qed
  show ?thesis
  proof (intro allI impI notI)
    fix w
    assume hwL: "{w} \<in> L"
    assume hend: "geotop_graph_endpoint L w"
    have hbroken: "geotop_is_broken_line (geotop_polyhedron L)"
    proof (rule geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_broken_line_prefix
        [where L = L])
      show "geotop_is_linear_graph L" by (rule hL_linear)
      show "finite L" by (rule hL_fin)
      show "geotop_complex_connected L" by (rule hL_conn)
      show "\<forall>w. {w} \<in> L \<longrightarrow>
          card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
          card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 2"
        by (rule hdegree12)
      show "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
        using hwL hend by (by100 blast)
    qed
    show False
      by (rule geotop_polygon_not_broken_line_graph_prefix[OF hL_polygon hbroken])
  qed
qed

lemma geotop_polygon_finite_linear_graph_vertices_degree_two_prefix:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_fin: "finite L"
  assumes hL_conn: "geotop_complex_connected L"
  assumes hL_polygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  (**
    Moise Figure 3.2 boundary-cycle step.  A finite linear graph whose carrier
    is a polygon has no endpoints and no branches; every boundary vertex has
    exactly two incident edges. **)
proof (intro allI impI)
  fix w
  assume hwL: "{w} \<in> L"
  let ?E = "{e\<in>L. geotop_is_edge e \<and> w \<in> e}"
  have hE_fin: "finite ?E"
    using hL_fin by (by100 simp)
  have hnonisolated:
      "\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e)"
    by (rule geotop_finite_linear_graph_polygon_vertices_nonisolated_prefix
        [OF hL_linear hL_fin hL_polygon])
  have hnoend: "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
    by (rule geotop_polygon_finite_linear_graph_vertices_no_endpoint_prefix
        [OF hL_linear hL_fin hL_conn hL_polygon])
  have hnobranch:
      "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    by (rule geotop_polygon_finite_linear_graph_vertices_no_branch_prefix
        [OF hL_linear hL_fin hL_conn hL_polygon])
  obtain e where heL: "e \<in> L" and hedge: "geotop_is_edge e" and hwe: "w \<in> e"
    using hnonisolated hwL by (by100 blast)
  have heE: "e \<in> ?E"
    using heL hedge hwe by (by100 blast)
  have hE_nonempty: "?E \<noteq> {}"
    using heE by (by100 blast)
  have hcard_pos: "0 < card ?E"
  proof -
    have hiff: "(0 < card ?E) = (?E \<noteq> {} \<and> finite ?E)"
      by (rule card_gt_0_iff)
    show ?thesis using hiff hE_nonempty hE_fin by (by100 blast)
  qed
  have hcard_le: "card ?E \<le> 2"
    using hnobranch hwL by (by100 blast)
  have hcard_ne1: "card ?E \<noteq> 1"
  proof
    assume hcard1: "card ?E = 1"
    have hL_complex: "geotop_is_complex L"
      using hL_linear unfolding geotop_is_linear_graph_def by (by100 blast)
    have hw_vertex: "w \<in> geotop_complex_vertices L"
      using geotop_complex_vertices_eq_0_simplexes[OF hL_complex] hwL
      by (by100 blast)
    have hend: "geotop_graph_endpoint L w"
      using hw_vertex hcard1 unfolding geotop_graph_endpoint_def by (by100 blast)
    have hnot: "\<not> geotop_graph_endpoint L w"
      using hnoend hwL by (by100 blast)
    show False
      using hend hnot by (by100 blast)
  qed
  have hcard_cases: "card ?E = 1 \<or> card ?E = 2"
    using hcard_pos hcard_le by (by100 linarith)
  show "card ?E = 2"
    using hcard_cases hcard_ne1 by (by100 blast)
qed

lemma geotop_polygon_finite_linear_graph_two_vertex_boundary_split_prefix:
  fixes L :: "(real^2) set set" and P Q :: "real^2"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_fin: "finite L"
  assumes hL_conn: "geotop_complex_connected L"
  assumes hL_polygon: "geotop_is_polygon (geotop_polyhedron L)"
  assumes hPL: "{P} \<in> L"
  assumes hQL: "{Q} \<in> L"
  assumes hPQ: "P \<noteq> Q"
  shows "\<exists>C\<^sub>1 C\<^sub>2.
      geotop_polyhedron L = C\<^sub>1 \<union> C\<^sub>2
      \<and> geotop_is_broken_line C\<^sub>1
      \<and> geotop_is_broken_line C\<^sub>2
      \<and> geotop_arc_endpoints C\<^sub>1 {P, Q}
      \<and> geotop_arc_endpoints C\<^sub>2 {P, Q}
      \<and> geotop_arc_interior C\<^sub>1 {P, Q} \<inter>
          geotop_arc_interior C\<^sub>2 {P, Q} = {}"
  (**
    Moise Figure 3.2 boundary step.  A finite polygonal linear graph is a
    cyclic graph; cutting that cycle at two distinct vertices gives the two
    polygonal boundary arcs used for the chord split. **)
proof -
  have hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
    by (rule geotop_polygon_finite_linear_graph_vertices_degree_two_prefix
        [OF hL_linear hL_fin hL_conn hL_polygon])
  have hcycle_cut:
      "\<exists>C\<^sub>1 C\<^sub>2.
        geotop_polyhedron L = C\<^sub>1 \<union> C\<^sub>2
        \<and> geotop_is_broken_line C\<^sub>1
        \<and> geotop_is_broken_line C\<^sub>2
        \<and> geotop_arc_endpoints C\<^sub>1 {P, Q}
        \<and> geotop_arc_endpoints C\<^sub>2 {P, Q}
        \<and> geotop_arc_interior C\<^sub>1 {P, Q} \<inter>
            geotop_arc_interior C\<^sub>2 {P, Q} = {}"
    by (rule geotop_finite_connected_degree_two_linear_graph_two_vertex_boundary_split_prefix
        [OF hL_linear hL_fin hL_conn hdegree hPL hQL hPQ])
  show ?thesis
    by (rule hcycle_cut)
qed

lemma geotop_degree_two_vertices_nonisolated_prefix:
  fixes L :: "(real^2) set set"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e)"
proof (intro allI impI)
  fix w
  assume hw: "{w} \<in> L"
  let ?E = "{e\<in>L. geotop_is_edge e \<and> w \<in> e}"
  have hcard: "card ?E = 2"
    using hdegree hw by (by100 blast)
  have "?E \<noteq> {}"
    using hcard by (by100 force)
  then obtain e where "e \<in> ?E"
    by (by100 blast)
  show "\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e"
    using \<open>e \<in> ?E\<close> by (by100 blast)
qed

lemma geotop_degree_two_vertices_no_graph_endpoint_prefix:
  fixes L :: "(real^2) set set"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
proof (intro allI impI)
  fix w
  assume hw: "{w} \<in> L"
  show "\<not> geotop_graph_endpoint L w"
  proof
    assume hend: "geotop_graph_endpoint L w"
    have hcard1: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1"
      using hend unfolding geotop_graph_endpoint_def by (by100 blast)
    have hcard2: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
      using hdegree hw by (by100 blast)
    show False
      using hcard1 hcard2 by (by100 simp)
  qed
qed

lemma geotop_degree_one_or_two_no_endpoint_degree_two_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hnoend: "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
  shows "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
proof (intro allI impI)
  fix w
  assume hwL: "{w} \<in> L"
  have hcase: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
    using hdegree12 hwL by (by100 blast)
  show "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  proof (rule disjE[OF hcase])
    assume hcard1: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1"
    have hw_vertex: "w \<in> geotop_complex_vertices L"
    proof -
      have hcomplex: "geotop_is_complex L"
        using hL unfolding geotop_is_linear_graph_def by (by100 blast)
      show ?thesis
        using geotop_complex_vertices_eq_0_simplexes[OF hcomplex] hwL
        by (by100 blast)
    qed
    have hend: "geotop_graph_endpoint L w"
      using hw_vertex hcard1 unfolding geotop_graph_endpoint_def by (by100 blast)
    have hnot: "\<not> geotop_graph_endpoint L w"
      using hnoend hwL by (by100 blast)
    show "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
      using hend hnot by (by100 blast)
  next
    assume hcard2: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
    show "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hcard2)
  qed
qed


end
