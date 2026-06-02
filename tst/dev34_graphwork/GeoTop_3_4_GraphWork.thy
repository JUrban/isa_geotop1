theory GeoTop_3_4_GraphWork
  imports "GeoTop34GraphFactsDirty.GeoTop_3_4_GraphFacts"
begin

lemma geotop_two_degree_one_endpoint_edge_connected_exhausts_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes hqL: "{q} \<in> L"
  assumes hqcard: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 1"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes hqw: "q \<noteq> w"
  assumes heq: "e = closed_segment w q"
  shows "L - {{w}, {q}, e} = {}"
proof -
  let ?K1 = "{\<sigma>\<in>L. \<sigma> \<subseteq> e}"
  let ?K2 = "L - {{w}, {q}, e}"
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  have hqe: "q \<in> e"
    using heq by (by100 simp)
  have hwq: "w \<noteq> q"
    using hqw by (by100 blast)
  have hK1_complex: "geotop_is_complex ?K1"
    by (rule geotop_complex_restrict_subset_is_complex[OF hcomplex])
  have hK2_complex: "geotop_is_complex ?K2"
  proof (rule geotop_two_degree_one_edge_delete_complement_complex_dev34
      [where L = L and w = w and q = q and e = e])
    show "geotop_is_linear_graph L" by (rule hL)
    show "finite L" by (rule hfin)
    show "geotop_graph_endpoint L w" by (rule hend)
    show "{q} \<in> L" by (rule hqL)
    show "card {l \<in> L. geotop_is_edge l \<and> q \<in> l} = 1" by (rule hqcard)
    show "e \<in> L" by (rule heL)
    show "geotop_is_edge e" by (rule hedge)
    show "w \<in> e" by (rule hwe)
    show "q \<in> e" by (rule hqe)
  qed
  have hK1_nonempty: "?K1 \<noteq> {}"
    using heL by (by100 blast)
  have hsplit: "L = ?K1 \<union> ?K2"
  proof
    show "L \<subseteq> ?K1 \<union> ?K2"
    proof
      fix \<sigma>
      assume h\<sigma>L: "\<sigma> \<in> L"
      show "\<sigma> \<in> ?K1 \<union> ?K2"
      proof (cases "\<sigma> \<in> ?K2")
        case True
        show ?thesis using True by (by100 blast)
      next
        case False
        have hcase: "\<sigma> = {w} \<or> \<sigma> = {q} \<or> \<sigma> = e"
          using h\<sigma>L False by (by100 simp)
        have hsub: "\<sigma> \<subseteq> e"
        proof (rule disjE[OF hcase])
          assume "\<sigma> = {w}"
          show ?thesis using \<open>\<sigma> = {w}\<close> hwe by (by100 blast)
        next
          assume hrest: "\<sigma> = {q} \<or> \<sigma> = e"
          show ?thesis
          proof (rule disjE[OF hrest])
            assume "\<sigma> = {q}"
            show ?thesis using \<open>\<sigma> = {q}\<close> hqe by (by100 blast)
          next
            assume "\<sigma> = e"
            show ?thesis using \<open>\<sigma> = e\<close> by (by100 simp)
          qed
        qed
        show ?thesis using h\<sigma>L hsub by (by100 blast)
      qed
    qed
  next
    show "?K1 \<union> ?K2 \<subseteq> L"
      by (by100 blast)
  qed
  have hdisj: "?K1 \<inter> ?K2 = {}"
  proof
    show "?K1 \<inter> ?K2 \<subseteq> {}"
    proof
      fix \<sigma>
      assume h\<sigma>int: "\<sigma> \<in> ?K1 \<inter> ?K2"
      have h\<sigma>L: "\<sigma> \<in> L"
        using h\<sigma>int by (by100 blast)
      have h\<sigma>sub: "\<sigma> \<subseteq> e"
        using h\<sigma>int by (by100 blast)
      have hcase: "\<sigma> = {w} \<or> \<sigma> = {q} \<or> \<sigma> = e"
        by (rule geotop_1dim_simplex_subset_edge_cases_dev34
            [OF hcomplex h\<sigma>L heL heq hwq h\<sigma>sub])
      have hnot: "\<sigma> \<notin> {{w}, {q}, e}"
        using h\<sigma>int by (by100 simp)
      show "\<sigma> \<in> {}"
        using hcase hnot by (by100 blast)
    qed
  next
    show "{} \<subseteq> ?K1 \<inter> ?K2"
      by (by100 simp)
  qed
  show ?thesis
  proof (rule ccontr)
    assume hnot_empty: "\<not> ?K2 = {}"
    have hK2_nonempty: "?K2 \<noteq> {}"
      using hnot_empty by (by100 blast)
    have hbad: "\<exists>K1 K2. K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {}
        \<and> L = K1 \<union> K2 \<and> geotop_is_complex K1 \<and> geotop_is_complex K2"
    proof (intro exI)
      show "?K1 \<noteq> {} \<and> ?K2 \<noteq> {} \<and> ?K1 \<inter> ?K2 = {}
          \<and> L = ?K1 \<union> ?K2 \<and> geotop_is_complex ?K1 \<and> geotop_is_complex ?K2"
        using hK1_nonempty hK2_nonempty hdisj hsplit hK1_complex hK2_complex
        by (by100 blast)
    qed
    have hno_bad: "\<not> (\<exists>K1 K2. K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {}
        \<and> L = K1 \<union> K2 \<and> geotop_is_complex K1 \<and> geotop_is_complex K2)"
      using hconn unfolding geotop_complex_connected_def by (by100 blast)
    show False
      using hbad hno_bad by (by100 blast)
  qed
qed

lemma geotop_two_degree_one_endpoint_edge_connected_polyhedron_eq_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes hqL: "{q} \<in> L"
  assumes hqcard: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 1"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes hqw: "q \<noteq> w"
  assumes heq: "e = closed_segment w q"
  shows "geotop_polyhedron L = e"
proof -
  have hqe: "q \<in> e"
    using heq by (by100 simp)
  have hexhaust: "L - {{w}, {q}, e} = {}"
  proof (rule geotop_two_degree_one_endpoint_edge_connected_exhausts_dev34
      [where L = L and w = w and q = q and e = e])
    show "geotop_is_linear_graph L" by (rule hL)
    show "finite L" by (rule hfin)
    show "geotop_complex_connected L" by (rule hconn)
    show "geotop_graph_endpoint L w" by (rule hend)
    show "{q} \<in> L" by (rule hqL)
    show "card {l \<in> L. geotop_is_edge l \<and> q \<in> l} = 1" by (rule hqcard)
    show "e \<in> L" by (rule heL)
    show "geotop_is_edge e" by (rule hedge)
    show "w \<in> e" by (rule hwe)
    show "q \<noteq> w" by (rule hqw)
    show "e = closed_segment w q" by (rule heq)
  qed
  have hsub: "L \<subseteq> {{w}, {q}, e}"
    using hexhaust by (by100 blast)
  show ?thesis
    by (rule geotop_polyhedron_two_vertices_edge_eq_dev34[OF hsub heL hwe hqe])
qed

lemma geotop_complex_add_endpoint_edge_at_vertex_dev34:
  fixes K L :: "(real^2) set set"
  assumes hL_complex: "geotop_is_complex L"
  assumes hK_complex: "geotop_is_complex K"
  assumes hK_sub: "K \<subseteq> L"
  assumes hqK: "{q} \<in> K"
  assumes heL: "e \<in> L"
  assumes heq: "e = closed_segment w q"
  assumes hqw: "q \<noteq> w"
  assumes hwL: "{w} \<in> L"
  shows "geotop_is_complex (K \<union> {{w}, e})"
proof -
  have hwq: "w \<noteq> q"
    using hqw by (by100 blast)
  have hsub: "K \<union> {{w}, e} \<subseteq> L"
    using hK_sub hwL heL by (by100 blast)
  have hfaces: "\<forall>\<sigma>\<in>K \<union> {{w}, e}. \<forall>\<tau>. geotop_is_face \<tau> \<sigma>
      \<longrightarrow> \<tau> \<in> K \<union> {{w}, e}"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau>
    assume h\<sigma>: "\<sigma> \<in> K \<union> {{w}, e}"
    assume hface: "geotop_is_face \<tau> \<sigma>"
    have hcase: "\<sigma> \<in> K \<or> \<sigma> = {w} \<or> \<sigma> = e"
      using h\<sigma> by (by100 blast)
    show "\<tau> \<in> K \<union> {{w}, e}"
    proof (rule disjE[OF hcase])
      assume h\<sigma>K: "\<sigma> \<in> K"
      have "\<tau> \<in> K"
        using geotop_is_complex_face_closed[OF hK_complex] h\<sigma>K hface by (by100 blast)
      thus ?thesis by (by100 blast)
    next
      assume hrest: "\<sigma> = {w} \<or> \<sigma> = e"
      show ?thesis
      proof (rule disjE[OF hrest])
        assume h\<sigma>w: "\<sigma> = {w}"
        have h\<tau>sub: "\<tau> \<subseteq> {w}"
          using geotop_is_face_imp_subset[OF hface] h\<sigma>w by (by100 simp)
        have h\<tau>ne: "\<tau> \<noteq> {}"
        proof -
          obtain V W where hW_ne: "W \<noteq> {}"
              and h\<tau>_hull: "\<tau> = geotop_convex_hull W"
            using hface unfolding geotop_is_face_def by (by100 blast)
          have h\<tau>_HOL: "\<tau> = convex hull W"
            using h\<tau>_hull geotop_convex_hull_eq_HOL by (by100 simp)
          show ?thesis
            using h\<tau>_HOL hW_ne convex_hull_eq_empty by (by100 simp)
        qed
        have "\<tau> = {w}"
          using h\<tau>sub h\<tau>ne by (by100 blast)
        thus ?thesis by (by100 blast)
      next
        assume h\<sigma>e: "\<sigma> = e"
        have hface_seg: "geotop_is_face \<tau> (closed_segment w q)"
          using hface h\<sigma>e heq by (by100 simp)
        have htcases: "\<tau> = {w} \<or> \<tau> = {q} \<or> \<tau> = closed_segment w q"
          by (rule geotop_segment_face_cases_dev34[OF hface_seg hwq])
        show ?thesis
        proof (rule disjE[OF htcases])
          assume "\<tau> = {w}"
          show ?thesis using \<open>\<tau> = {w}\<close> by (by100 blast)
        next
          assume hrest2: "\<tau> = {q} \<or> \<tau> = closed_segment w q"
          show ?thesis
          proof (rule disjE[OF hrest2])
            assume "\<tau> = {q}"
            show ?thesis using \<open>\<tau> = {q}\<close> hqK by (by100 blast)
          next
            assume "\<tau> = closed_segment w q"
            show ?thesis using \<open>\<tau> = closed_segment w q\<close> heq by (by100 blast)
          qed
        qed
      qed
    qed
  qed
  show ?thesis
    by (rule geotop_complex_subset_is_complex[OF hL_complex hsub hfaces])
qed

lemma geotop_graph_endpoint_delete_leaf_connected_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes hqL: "{q} \<in> L"
  assumes hqw: "q \<noteq> w"
  assumes heq: "e = closed_segment w q"
  shows "geotop_complex_connected (L - {{w}, e})"
proof -
  let ?R = "L - {{w}, e}"
  have hL_complex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  have hR_complex: "geotop_is_complex ?R"
  proof (rule geotop_graph_endpoint_delete_leaf_complex_dev34
      [where L = L and w = w and e = e])
    show "geotop_is_linear_graph L" by (rule hL)
    show "finite L" by (rule hfin)
    show "geotop_graph_endpoint L w" by (rule hend)
    show "e \<in> L" by (rule heL)
    show "geotop_is_edge e" by (rule hedge)
    show "w \<in> e" by (rule hwe)
  qed
  have hwL: "{w} \<in> L"
  proof -
    have "{w} \<in> L \<and> card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1"
    proof (rule geotop_graph_endpoint_singleton_and_card_one_dev34[where L = L and w = w])
      show "geotop_is_linear_graph L" by (rule hL)
      show "geotop_graph_endpoint L w" by (rule hend)
    qed
    thus ?thesis by (by100 blast)
  qed
  have hq_ne_w: "{q} \<noteq> {w}"
    using hqw by (by100 blast)
  have hq_ne_e: "{q} \<noteq> e"
  proof
    assume hqe_single: "{q} = e"
    have "w \<in> {q}"
      using hwe hqe_single by (by100 simp)
    hence "w = q" by (by100 simp)
    thus False using hqw by (by100 blast)
  qed
  have hqR: "{q} \<in> ?R"
    using hqL hq_ne_w hq_ne_e by (by100 simp)
  have hno_bad_L: "\<not> (\<exists>K1 K2. K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {}
      \<and> L = K1 \<union> K2 \<and> geotop_is_complex K1 \<and> geotop_is_complex K2)"
    using hconn unfolding geotop_complex_connected_def by (by100 blast)
  show ?thesis
    unfolding geotop_complex_connected_def
  proof (intro conjI notI)
    show "geotop_is_complex ?R"
      by (rule hR_complex)
  next
    assume hbad_R: "\<exists>K1 K2. K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {}
        \<and> ?R = K1 \<union> K2 \<and> geotop_is_complex K1 \<and> geotop_is_complex K2"
    from hbad_R show False
    proof (elim exE)
      fix K1 K2
      assume hsep: "K1 \<noteq> {} \<and> K2 \<noteq> {} \<and> K1 \<inter> K2 = {}
          \<and> ?R = K1 \<union> K2 \<and> geotop_is_complex K1 \<and> geotop_is_complex K2"
      have hK1_ne: "K1 \<noteq> {}" using hsep by (by100 simp)
      have hK2_ne: "K2 \<noteq> {}" using hsep by (by100 simp)
      have hdisj: "K1 \<inter> K2 = {}" using hsep by (by100 simp)
      have hR_split: "?R = K1 \<union> K2" using hsep by (by100 simp)
      have hK1_complex: "geotop_is_complex K1" using hsep by (by100 simp)
      have hK2_complex: "geotop_is_complex K2" using hsep by (by100 simp)
      have hq_in_split: "{q} \<in> K1 \<or> {q} \<in> K2"
        using hqR hR_split by (by100 blast)
      have hL_from_R: "L = ?R \<union> {{w}, e}"
      proof
        show "L \<subseteq> ?R \<union> {{w}, e}"
          by (by100 blast)
      next
        show "?R \<union> {{w}, e} \<subseteq> L"
          using hwL heL by (by100 blast)
      qed
      show False
      proof (rule disjE[OF hq_in_split])
        assume hqK1: "{q} \<in> K1"
        have hK1_sub_L: "K1 \<subseteq> L"
          using hR_split by (by100 blast)
        have hA_complex: "geotop_is_complex (K1 \<union> {{w}, e})"
        proof (rule geotop_complex_add_endpoint_edge_at_vertex_dev34
            [where K = K1 and L = L and q = q and w = w and e = e])
          show "geotop_is_complex L" by (rule hL_complex)
          show "geotop_is_complex K1" by (rule hK1_complex)
          show "K1 \<subseteq> L" by (rule hK1_sub_L)
          show "{q} \<in> K1" by (rule hqK1)
          show "e \<in> L" by (rule heL)
          show "e = closed_segment w q" by (rule heq)
          show "q \<noteq> w" by (rule hqw)
          show "{w} \<in> L" by (rule hwL)
        qed
        have hA_ne: "K1 \<union> {{w}, e} \<noteq> {}"
          using hwL by (by100 blast)
        have hA_disj: "(K1 \<union> {{w}, e}) \<inter> K2 = {}"
          using hdisj hR_split by (by100 blast)
        have hL_split: "L = (K1 \<union> {{w}, e}) \<union> K2"
          using hL_from_R hR_split by (by100 blast)
        have hbad_L: "\<exists>A B. A \<noteq> {} \<and> B \<noteq> {} \<and> A \<inter> B = {}
            \<and> L = A \<union> B \<and> geotop_is_complex A \<and> geotop_is_complex B"
        proof (intro exI)
          show "K1 \<union> {{w}, e} \<noteq> {} \<and> K2 \<noteq> {} \<and> (K1 \<union> {{w}, e}) \<inter> K2 = {}
              \<and> L = (K1 \<union> {{w}, e}) \<union> K2
              \<and> geotop_is_complex (K1 \<union> {{w}, e}) \<and> geotop_is_complex K2"
            using hA_ne hK2_ne hA_disj hL_split hA_complex hK2_complex by (by100 blast)
        qed
        show False using hbad_L hno_bad_L by (by100 blast)
      next
        assume hqK2: "{q} \<in> K2"
        have hK2_sub_L: "K2 \<subseteq> L"
          using hR_split by (by100 blast)
        have hA_complex: "geotop_is_complex (K2 \<union> {{w}, e})"
        proof (rule geotop_complex_add_endpoint_edge_at_vertex_dev34
            [where K = K2 and L = L and q = q and w = w and e = e])
          show "geotop_is_complex L" by (rule hL_complex)
          show "geotop_is_complex K2" by (rule hK2_complex)
          show "K2 \<subseteq> L" by (rule hK2_sub_L)
          show "{q} \<in> K2" by (rule hqK2)
          show "e \<in> L" by (rule heL)
          show "e = closed_segment w q" by (rule heq)
          show "q \<noteq> w" by (rule hqw)
          show "{w} \<in> L" by (rule hwL)
        qed
        have hA_ne: "K2 \<union> {{w}, e} \<noteq> {}"
          using hwL by (by100 blast)
        have hA_disj: "(K2 \<union> {{w}, e}) \<inter> K1 = {}"
          using hdisj hR_split by (by100 blast)
        have hL_split: "L = (K2 \<union> {{w}, e}) \<union> K1"
          using hL_from_R hR_split by (by100 blast)
        have hbad_L: "\<exists>A B. A \<noteq> {} \<and> B \<noteq> {} \<and> A \<inter> B = {}
            \<and> L = A \<union> B \<and> geotop_is_complex A \<and> geotop_is_complex B"
        proof (intro exI)
          show "K2 \<union> {{w}, e} \<noteq> {} \<and> K1 \<noteq> {} \<and> (K2 \<union> {{w}, e}) \<inter> K1 = {}
              \<and> L = (K2 \<union> {{w}, e}) \<union> K1
              \<and> geotop_is_complex (K2 \<union> {{w}, e}) \<and> geotop_is_complex K1"
            using hA_ne hK1_ne hA_disj hL_split hA_complex hK1_complex by (by100 blast)
        qed
        show False using hbad_L hno_bad_L by (by100 blast)
      qed
    qed
  qed
qed

lemma geotop_HOL_arcs_glue_disjoint_endpoints_start_dev34:
  fixes B\<^sub>1 B\<^sub>2 :: "(real^2) set"
  assumes hR_end_1: "\<exists>\<gamma>\<^sub>1::real \<Rightarrow> real^2.
      arc \<gamma>\<^sub>1 \<and> path_image \<gamma>\<^sub>1 = B\<^sub>1 \<and> pathstart \<gamma>\<^sub>1 = S
      \<and> pathfinish \<gamma>\<^sub>1 = R"
  assumes hR_end_2: "\<exists>\<gamma>\<^sub>2::real \<Rightarrow> real^2.
      arc \<gamma>\<^sub>2 \<and> path_image \<gamma>\<^sub>2 = B\<^sub>2 \<and> pathstart \<gamma>\<^sub>2 = R"
  assumes hdisj: "B\<^sub>1 \<inter> B\<^sub>2 = {R}"
  shows "\<exists>\<gamma>::real \<Rightarrow> real^2. arc \<gamma> \<and> path_image \<gamma> = B\<^sub>1 \<union> B\<^sub>2
      \<and> pathstart \<gamma> = S"
proof -
  obtain \<gamma>\<^sub>1 :: "real \<Rightarrow> real^2"
    where harc\<^sub>1: "arc \<gamma>\<^sub>1" and hpim\<^sub>1: "path_image \<gamma>\<^sub>1 = B\<^sub>1"
      and hstart\<^sub>1: "pathstart \<gamma>\<^sub>1 = S"
      and hfin\<^sub>1: "pathfinish \<gamma>\<^sub>1 = R"
    using hR_end_1 by (by100 blast)
  obtain \<gamma>\<^sub>2 :: "real \<Rightarrow> real^2"
    where harc\<^sub>2: "arc \<gamma>\<^sub>2" and hpim\<^sub>2: "path_image \<gamma>\<^sub>2 = B\<^sub>2"
      and hstart\<^sub>2: "pathstart \<gamma>\<^sub>2 = R"
    using hR_end_2 by (by100 blast)
  have h_fin_start: "pathfinish \<gamma>\<^sub>1 = pathstart \<gamma>\<^sub>2"
    using hfin\<^sub>1 hstart\<^sub>2 by (by100 simp)
  have h_int_sub: "path_image \<gamma>\<^sub>1 \<inter> path_image \<gamma>\<^sub>2 \<subseteq> {pathstart \<gamma>\<^sub>2}"
    using hpim\<^sub>1 hpim\<^sub>2 hdisj hstart\<^sub>2 by (by100 blast)
  have hjoin_arc: "arc (\<gamma>\<^sub>1 +++ \<gamma>\<^sub>2)"
    by (rule arc_join[OF harc\<^sub>1 harc\<^sub>2 h_fin_start h_int_sub])
  have hjoin_pim_raw: "path_image (\<gamma>\<^sub>1 +++ \<gamma>\<^sub>2) = path_image \<gamma>\<^sub>1 \<union> path_image \<gamma>\<^sub>2"
    by (rule path_image_join[OF h_fin_start])
  have hjoin_pim: "path_image (\<gamma>\<^sub>1 +++ \<gamma>\<^sub>2) = B\<^sub>1 \<union> B\<^sub>2"
    using hjoin_pim_raw hpim\<^sub>1 hpim\<^sub>2 by (by100 simp)
  have hjoin_start: "pathstart (\<gamma>\<^sub>1 +++ \<gamma>\<^sub>2) = S"
    using hstart\<^sub>1 unfolding pathstart_def joinpaths_def by (by100 simp)
  show ?thesis using hjoin_arc hjoin_pim hjoin_start by (by100 blast)
qed

lemma geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_HOL_arc_from_endpoint_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hend: "geotop_graph_endpoint L w"
  shows "\<exists>\<gamma>::real \<Rightarrow> real^2. arc \<gamma> \<and> path_image \<gamma> = geotop_polyhedron L
      \<and> pathstart \<gamma> = w"
  using hfin hL hconn hdegree12 hend
proof (induction L arbitrary: w rule: finite_psubset_induct)
  case (psubset L)
  show ?case
  proof -
    have hfinL: "finite L" by (rule psubset.hyps)
    have hL: "geotop_is_linear_graph L" by (rule psubset.prems(1))
    have hconn: "geotop_complex_connected L" by (rule psubset.prems(2))
    have hdegree12: "\<forall>x. {x} \<in> L \<longrightarrow>
        card {e \<in> L. geotop_is_edge e \<and> x \<in> e} = 1 \<or>
        card {e \<in> L. geotop_is_edge e \<and> x \<in> e} = 2"
      by (rule psubset.prems(3))
    have hend: "geotop_graph_endpoint L w" by (rule psubset.prems(4))
    have hneighbor: "\<exists>e q. e \<in> L \<and> geotop_is_edge e \<and> w \<in> e
        \<and> q \<noteq> w \<and> e = closed_segment w q \<and> {q} \<in> L"
    proof (rule geotop_graph_endpoint_unique_segment_neighbor_dev34[where L = L and w = w])
      show "geotop_is_linear_graph L" by (rule hL)
      show "finite L" by (rule hfinL)
      show "geotop_graph_endpoint L w" by (rule hend)
    qed
    obtain e q where heL: "e \<in> L" and hedge: "geotop_is_edge e"
        and hwe: "w \<in> e" and hqw: "q \<noteq> w"
        and heq: "e = closed_segment w q" and hqL: "{q} \<in> L"
      using hneighbor by (by100 blast)
    have hqcard_cases:
        "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 1 \<or>
         card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 2"
      using hdegree12 hqL by (by100 blast)
    show ?thesis
    proof (rule disjE[OF hqcard_cases])
      assume hqcard1: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 1"
      show ?thesis
      proof -
        have hpoly_eq: "geotop_polyhedron L = e"
        proof (rule geotop_two_degree_one_endpoint_edge_connected_polyhedron_eq_dev34
            [where L = L and w = w and q = q and e = e])
          show "geotop_is_linear_graph L" by (rule hL)
          show "finite L" by (rule hfinL)
          show "geotop_complex_connected L" by (rule hconn)
          show "geotop_graph_endpoint L w" by (rule hend)
          show "{q} \<in> L" by (rule hqL)
          show "card {l \<in> L. geotop_is_edge l \<and> q \<in> l} = 1" by (rule hqcard1)
          show "e \<in> L" by (rule heL)
          show "geotop_is_edge e" by (rule hedge)
          show "w \<in> e" by (rule hwe)
          show "q \<noteq> w" by (rule hqw)
          show "e = closed_segment w q" by (rule heq)
        qed
        have hwq: "w \<noteq> q"
          using hqw by (by100 blast)
        obtain \<gamma> :: "real \<Rightarrow> real^2"
          where h\<gamma>_arc: "arc \<gamma>"
            and h\<gamma>_pim: "path_image \<gamma> = closed_segment w q"
            and h\<gamma>_start: "pathstart \<gamma> = w"
          using geotop_closed_segment_HOL_arc_between_dev34[OF hwq] by (by100 blast)
        have h\<gamma>_pim_L: "path_image \<gamma> = geotop_polyhedron L"
          using h\<gamma>_pim hpoly_eq heq by (by100 simp)
        show ?thesis
          using h\<gamma>_arc h\<gamma>_pim_L h\<gamma>_start by (by100 blast)
      qed
    next
      assume hqcard2: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 2"
      show ?thesis
      proof -
        let ?R = "L - {{w}, e}"
        have hqe: "q \<in> e"
          using heq by (by100 simp)
        have hq_ne_w: "{q} \<noteq> {w}"
          using hqw by (by100 blast)
        have hq_ne_e: "{q} \<noteq> e"
        proof
          assume hqe_single: "{q} = e"
          have "w \<in> {q}"
            using hwe hqe_single by (by100 simp)
          hence "w = q" by (by100 simp)
          thus False using hqw by (by100 blast)
        qed
        have hqR: "{q} \<in> ?R"
          using hqL hq_ne_w hq_ne_e by (by100 simp)
        have hR_psubset: "?R \<subset> L"
          using heL by (by100 blast)
        have hR_linear: "geotop_is_linear_graph ?R"
        proof (rule geotop_graph_endpoint_delete_leaf_linear_graph_dev34
            [where L = L and w = w and e = e])
          show "geotop_is_linear_graph L" by (rule hL)
          show "finite L" by (rule hfinL)
          show "geotop_graph_endpoint L w" by (rule hend)
          show "e \<in> L" by (rule heL)
          show "geotop_is_edge e" by (rule hedge)
          show "w \<in> e" by (rule hwe)
        qed
        have hR_conn: "geotop_complex_connected ?R"
        proof (rule geotop_graph_endpoint_delete_leaf_connected_dev34
            [where L = L and w = w and e = e and q = q])
          show "geotop_is_linear_graph L" by (rule hL)
          show "finite L" by (rule hfinL)
          show "geotop_complex_connected L" by (rule hconn)
          show "geotop_graph_endpoint L w" by (rule hend)
          show "e \<in> L" by (rule heL)
          show "geotop_is_edge e" by (rule hedge)
          show "w \<in> e" by (rule hwe)
          show "{q} \<in> L" by (rule hqL)
          show "q \<noteq> w" by (rule hqw)
          show "e = closed_segment w q" by (rule heq)
        qed
        have hR_degree12: "\<forall>x. {x} \<in> ?R \<longrightarrow>
            card {l\<in>?R. geotop_is_edge l \<and> x \<in> l} = 1 \<or>
            card {l\<in>?R. geotop_is_edge l \<and> x \<in> l} = 2"
        proof (rule geotop_graph_endpoint_delete_leaf_degree_one_or_two_dev34
            [where L = L and w = w and e = e and q = q])
          show "geotop_is_linear_graph L" by (rule hL)
          show "finite L" by (rule hfinL)
          show "geotop_graph_endpoint L w" by (rule hend)
          show "e \<in> L" by (rule heL)
          show "geotop_is_edge e" by (rule hedge)
          show "w \<in> e" by (rule hwe)
          show "{q} \<in> L" by (rule hqL)
          show "q \<noteq> w" by (rule hqw)
          show "e = closed_segment w q" by (rule heq)
          show "\<forall>x. {x} \<in> L \<longrightarrow>
              card {l \<in> L. geotop_is_edge l \<and> x \<in> l} = 1 \<or>
              card {l \<in> L. geotop_is_edge l \<and> x \<in> l} = 2"
            by (rule hdegree12)
          show "card {l \<in> L. geotop_is_edge l \<and> q \<in> l} = 2" by (rule hqcard2)
        qed
        have hR_endpoint: "geotop_graph_endpoint ?R q"
        proof (rule geotop_graph_endpoint_delete_leaf_neighbor_endpoint_dev34
            [where L = L and w = w and e = e and q = q])
          show "geotop_is_linear_graph L" by (rule hL)
          show "finite L" by (rule hfinL)
          show "geotop_graph_endpoint L w" by (rule hend)
          show "e \<in> L" by (rule heL)
          show "geotop_is_edge e" by (rule hedge)
          show "w \<in> e" by (rule hwe)
          show "{q} \<in> L" by (rule hqL)
          show "q \<noteq> w" by (rule hqw)
          show "q \<in> e" by (rule hqe)
          show "card {l \<in> L. geotop_is_edge l \<and> q \<in> l} = 2" by (rule hqcard2)
        qed
        have hrest_arc: "\<exists>\<gamma>\<^sub>2::real \<Rightarrow> real^2. arc \<gamma>\<^sub>2
            \<and> path_image \<gamma>\<^sub>2 = geotop_polyhedron ?R \<and> pathstart \<gamma>\<^sub>2 = q"
        proof (rule psubset.IH[where B = ?R and w = q])
          show "?R \<subset> L" by (rule hR_psubset)
          show "geotop_is_linear_graph ?R" by (rule hR_linear)
          show "geotop_complex_connected ?R" by (rule hR_conn)
          show "\<forall>x. {x} \<in> ?R \<longrightarrow>
              card {l \<in> ?R. geotop_is_edge l \<and> x \<in> l} = 1 \<or>
              card {l \<in> ?R. geotop_is_edge l \<and> x \<in> l} = 2"
            by (rule hR_degree12)
          show "geotop_graph_endpoint ?R q" by (rule hR_endpoint)
        qed
        have hwq: "w \<noteq> q"
          using hqw by (by100 blast)
        have hseg_arc: "\<exists>\<gamma>\<^sub>1::real \<Rightarrow> real^2. arc \<gamma>\<^sub>1 \<and> path_image \<gamma>\<^sub>1 = e
            \<and> pathstart \<gamma>\<^sub>1 = w \<and> pathfinish \<gamma>\<^sub>1 = q"
        proof -
          obtain \<gamma>\<^sub>1 :: "real \<Rightarrow> real^2"
            where h\<gamma>1_arc: "arc \<gamma>\<^sub>1"
              and h\<gamma>1_pim: "path_image \<gamma>\<^sub>1 = closed_segment w q"
              and h\<gamma>1_start: "pathstart \<gamma>\<^sub>1 = w"
              and h\<gamma>1_finish: "pathfinish \<gamma>\<^sub>1 = q"
            using geotop_closed_segment_HOL_arc_between_dev34[OF hwq] by (by100 blast)
          show ?thesis
            using h\<gamma>1_arc h\<gamma>1_pim h\<gamma>1_start h\<gamma>1_finish heq by (by100 blast)
        qed
        have hdisj: "e \<inter> geotop_polyhedron ?R = {q}"
        proof (rule geotop_delete_leaf_edge_inter_rest_polyhedron_eq_neighbor_dev34
            [where L = L and w = w and e = e and q = q])
          show "geotop_is_linear_graph L" by (rule hL)
          show "finite L" by (rule hfinL)
          show "geotop_graph_endpoint L w" by (rule hend)
          show "e \<in> L" by (rule heL)
          show "geotop_is_edge e" by (rule hedge)
          show "w \<in> e" by (rule hwe)
          show "{q} \<in> L" by (rule hqL)
          show "q \<noteq> w" by (rule hqw)
          show "e = closed_segment w q" by (rule heq)
        qed
        have hglue: "\<exists>\<gamma>::real \<Rightarrow> real^2. arc \<gamma>
            \<and> path_image \<gamma> = e \<union> geotop_polyhedron ?R \<and> pathstart \<gamma> = w"
          by (rule geotop_HOL_arcs_glue_disjoint_endpoints_start_dev34
              [OF hseg_arc hrest_arc hdisj])
        have hpoly_union: "geotop_polyhedron L = e \<union> geotop_polyhedron ?R"
        proof (rule geotop_graph_endpoint_delete_leaf_polyhedron_union_dev34
            [where L = L and w = w and e = e])
          show "geotop_is_linear_graph L" by (rule hL)
          show "finite L" by (rule hfinL)
          show "geotop_graph_endpoint L w" by (rule hend)
          show "e \<in> L" by (rule heL)
          show "geotop_is_edge e" by (rule hedge)
          show "w \<in> e" by (rule hwe)
        qed
        obtain \<gamma> :: "real \<Rightarrow> real^2"
          where h\<gamma>_arc: "arc \<gamma>"
            and h\<gamma>_pim: "path_image \<gamma> = e \<union> geotop_polyhedron ?R"
            and h\<gamma>_start: "pathstart \<gamma> = w"
          using hglue by (by100 blast)
        have h\<gamma>_pim_L: "path_image \<gamma> = geotop_polyhedron L"
          using h\<gamma>_pim hpoly_union by (by100 simp)
        show ?thesis
          using h\<gamma>_arc h\<gamma>_pim_L h\<gamma>_start by (by100 blast)
      qed
    qed
  qed
qed

lemma geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_HOL_arc_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hend: "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
  shows "\<exists>\<gamma>::real \<Rightarrow> real^2. arc \<gamma> \<and> path_image \<gamma> = geotop_polyhedron L"
proof -
  obtain w where hend_w: "geotop_graph_endpoint L w"
    using hend by (by100 blast)
  have "\<exists>\<gamma>::real \<Rightarrow> real^2. arc \<gamma> \<and> path_image \<gamma> = geotop_polyhedron L
      \<and> pathstart \<gamma> = w"
  proof (rule geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_HOL_arc_from_endpoint_dev34
      [where L = L and w = w])
    show "geotop_is_linear_graph L" by (rule hL)
    show "finite L" by (rule hfin)
    show "geotop_complex_connected L" by (rule hconn)
    show "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
        card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hdegree12)
    show "geotop_graph_endpoint L w" by (rule hend_w)
  qed
  thus ?thesis by (by100 blast)
qed

lemma geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_arc_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hend: "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
  shows "geotop_is_arc (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
proof -
  have hex: "\<exists>\<gamma>::real \<Rightarrow> real^2. arc \<gamma> \<and> path_image \<gamma> = geotop_polyhedron L"
  proof (rule geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_HOL_arc_dev34
      [where L = L])
    show "geotop_is_linear_graph L" by (rule hL)
    show "finite L" by (rule hfin)
    show "geotop_complex_connected L" by (rule hconn)
    show "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
        card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hdegree12)
    show "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
      by (rule hend)
  qed
  obtain \<gamma> :: "real \<Rightarrow> real^2"
    where h\<gamma>_arc: "arc \<gamma>" and h\<gamma>_pim: "path_image \<gamma> = geotop_polyhedron L"
    using hex by (by100 blast)
  have hgeo_arc: "geotop_is_arc (path_image \<gamma>)
      (subspace_topology UNIV geotop_euclidean_topology (path_image \<gamma>))"
    by (rule geotop_HOL_arc_imp_geotop_is_arc[OF h\<gamma>_arc])
  show ?thesis
    using hgeo_arc h\<gamma>_pim by (by100 simp)
qed

lemma geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_broken_line_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  assumes hend: "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
  shows "geotop_is_broken_line (geotop_polyhedron L)"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  have h1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_dev34[OF hL])
  have harc: "geotop_is_arc (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
  proof (rule geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_arc_dev34
      [where L = L])
    show "geotop_is_linear_graph L" by (rule hL)
    show "finite L" by (rule hfin)
    show "geotop_complex_connected L" by (rule hconn)
    show "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
        card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule hdegree12)
    show "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
      by (rule hend)
  qed
  show ?thesis
    unfolding geotop_is_broken_line_def
    using hcomplex h1dim harc by (by100 blast)
qed

lemma geotop_finite_connected_degree_one_or_two_linear_graph_line_or_polygon_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "geotop_is_broken_line (geotop_polyhedron L) \<or>
      geotop_is_polygon (geotop_polyhedron L)"
proof -
  have hendpoint_or_noendpoint:
      "(\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w) \<or>
       (\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w)"
    by (by100 blast)
  show ?thesis
  proof (rule disjE[OF hendpoint_or_noendpoint])
    assume hend: "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
    have hline: "geotop_is_broken_line (geotop_polyhedron L)"
    proof (rule geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_broken_line_dev34
        [where L = L])
      show "geotop_is_linear_graph L" by (rule hL)
      show "finite L" by (rule hfin)
      show "geotop_complex_connected L" by (rule hconn)
      show "\<forall>w. {w} \<in> L \<longrightarrow>
          card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
          card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 2"
        by (rule hdegree12)
      show "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
        by (rule hend)
    qed
    show ?thesis
      using hline by (by100 blast)
  next
    assume hnoend: "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
    have hdegree2: "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
    proof (rule geotop_degree_one_or_two_no_endpoint_degree_two_dev34[where L = L])
      show "geotop_is_linear_graph L" by (rule hL)
      show "\<forall>w. {w} \<in> L \<longrightarrow>
          card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
          card {e \<in> L. geotop_is_edge e \<and> w \<in> e} = 2"
        by (rule hdegree12)
      show "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
        by (rule hnoend)
    qed
    have hpoly: "geotop_is_polygon (geotop_polyhedron L)"
      by (rule geotop_finite_connected_degree_two_linear_graph_polygon_dev34
          [OF hL hfin hconn hdegree2])
    show ?thesis
      using hpoly by (by100 blast)
  qed
qed

end
