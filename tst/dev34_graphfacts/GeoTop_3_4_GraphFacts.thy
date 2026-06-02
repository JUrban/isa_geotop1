theory GeoTop_3_4_GraphFacts
  imports "GeoTop34WorkFactsDirty.GeoTop_3_4_WorkFacts"
begin

text \<open>Moise \<S>4, Theorem 8: the graph-classification step used after
Lemmas 2--4.  A finite connected linear graph whose every vertex has
exactly two incident edges is a polygon.\<close>
lemma geotop_broken_line_polyhedron_finite_linear_graph_has_endpoint_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hB: "geotop_is_broken_line (geotop_polyhedron L)"
  shows "\<exists>w. {w} \<in> L \<and> geotop_graph_endpoint L w"
  sorry

lemma geotop_degree_two_linear_graph_polyhedron_not_broken_line_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "\<not> geotop_is_broken_line (geotop_polyhedron L)"
proof
  assume hB: "geotop_is_broken_line (geotop_polyhedron L)"
  obtain w where hwL: "{w} \<in> L" and hend: "geotop_graph_endpoint L w"
    using geotop_broken_line_polyhedron_finite_linear_graph_has_endpoint_dev34
      [OF hL hfin hB] by (by100 blast)
  have hnoend: "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
    by (rule geotop_degree_two_vertices_no_graph_endpoint_dev34[OF hdegree])
  show False
    using hnoend hwL hend by (by100 blast)
qed

lemma geotop_finite_connected_degree_two_linear_graph_polygon_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "geotop_is_polygon (geotop_polyhedron L)"
proof -
  have hnonisolated: "\<forall>w. {w} \<in> L \<longrightarrow> (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e)"
    by (rule geotop_degree_two_vertices_nonisolated_dev34[OF hdegree])
  have hdegree12: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1 \<or>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
    using hdegree by (by100 blast)
  have hshape: "geotop_is_broken_line (geotop_polyhedron L) \<or>
      geotop_is_polygon (geotop_polyhedron L)"
    by (rule geotop_finite_connected_degree_one_or_two_linear_graph_line_or_polygon_dev34
        [OF hL hfin hconn hdegree12])
  have hnot_line: "\<not> geotop_is_broken_line (geotop_polyhedron L)"
    by (rule geotop_degree_two_linear_graph_polyhedron_not_broken_line_dev34
        [OF hL hfin hdegree])
  show ?thesis
    using hshape hnot_line by (by100 blast)
qed

lemma geotop_link_component_preserves_incident_edge_card_one_or_two_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  assumes hdegree_link: "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
      card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
      card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 2"
  shows "\<forall>w. {w} \<in> {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C} \<longrightarrow>
      card {l\<in>{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
      card {l\<in>{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}. geotop_is_edge l \<and> w \<in> l} = 2"
proof (intro allI impI)
  fix w
  let ?L = "{\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}"
  let ?S\<^sub>C = "{l\<in>?L. geotop_is_edge l \<and> w \<in> l}"
  let ?S = "{l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l}"
  assume hwL: "{w} \<in> ?L"
  have hw_link: "{w} \<in> geotop_link K v"
    using hwL by (by100 simp)
  have hwC: "w \<in> C"
    using hwL by (by100 blast)
  have hsets: "?S\<^sub>C = ?S"
  proof
    show "?S\<^sub>C \<subseteq> ?S"
      by (by100 blast)
  next
    show "?S \<subseteq> ?S\<^sub>C"
    proof
      fix l
      assume hlS: "l \<in> ?S"
      have hl_link: "l \<in> geotop_link K v"
        using hlS by (by100 simp)
      have hw_l: "w \<in> l"
        using hlS by (by100 simp)
      have hmeet: "l \<inter> C \<noteq> {}"
        using hw_l hwC by (by100 blast)
      have hl_subC: "l \<subseteq> C"
        by (rule geotop_link_component_contains_meeting_simplex
            [OF hK hP hC hl_link hmeet])
      show "l \<in> ?S\<^sub>C"
        using hlS hl_subC by (by100 simp)
    qed
  qed
  have hdegree: "card ?S = 1 \<or> card ?S = 2"
    using hdegree_link hw_link by (by100 blast)
  show "card ?S\<^sub>C = 1 \<or> card ?S\<^sub>C = 2"
    using hsets hdegree by (by100 simp)
qed

lemma geotop_link_component_degree_one_or_two_linear_graph_witness_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hP: "P \<in> \<Union>(geotop_link K v)"
  assumes hC: "C = geotop_component_at UNIV geotop_euclidean_topology
                  (\<Union>(geotop_link K v)) P"
  assumes hdegree_link: "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
      card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
      card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 2"
  shows "\<exists>L. geotop_is_linear_graph L
      \<and> finite L
      \<and> geotop_polyhedron L = C
      \<and> geotop_complex_connected L
      \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
          card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
          card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2)"
proof -
  obtain L where hL_eq: "L = {\<sigma>\<in>geotop_link K v. \<sigma> \<subseteq> C}"
    and hL_complex: "geotop_is_complex L"
    and hL_1dim: "geotop_complex_is_1dim L"
    and hL_fin: "finite L"
    and hL_poly: "geotop_polyhedron L = C"
    using geotop_link_component_subcomplex_witness[OF hK hv hP hC]
    by (by100 blast)
  have hL_linear: "geotop_is_linear_graph L"
    by (rule geotop_complex_1dim_imp_linear_graph_dev34[OF hL_complex hL_1dim])
  have hC_conn: "top1_connected_on C
      (subspace_topology UNIV geotop_euclidean_topology C)"
    using geotop_link_component_summary[OF hK hv hP hC] by (by100 blast)
  have hpoly_conn: "top1_connected_on (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    using hC_conn hL_poly by (by100 simp)
  have hpath: "top1_path_connected_on (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
    by (rule iffD2[OF Theorem_GT_1_12(2)[OF hL_complex] hpoly_conn])
  have hL_conn: "geotop_complex_connected L"
    by (rule iffD2[OF Theorem_GT_1_12(1)[OF hL_complex] hpath])
  have hdegree_L: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
      card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2"
    using geotop_link_component_preserves_incident_edge_card_one_or_two_dev34
      [OF hK hP hC hdegree_link] hL_eq by (by100 simp)
  show ?thesis
    using hL_linear hL_fin hL_poly hL_conn hdegree_L by (by100 blast)
qed

lemma geotop_link_components_degree_one_or_two_linear_graph_witnesses_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hv: "v \<in> geotop_complex_vertices K"
  assumes hdegree_link: "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
      card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
      card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 2"
  shows "\<forall>C. (\<exists>P\<in>\<Union>(geotop_link K v).
      C = geotop_component_at UNIV geotop_euclidean_topology
            (\<Union>(geotop_link K v)) P)
    \<longrightarrow> (\<exists>L. geotop_is_linear_graph L
      \<and> finite L
      \<and> geotop_polyhedron L = C
      \<and> geotop_complex_connected L
      \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
          card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
          card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2))"
proof (intro allI impI)
  fix C
  assume hC_ex: "\<exists>P\<in>\<Union>(geotop_link K v).
      C = geotop_component_at UNIV geotop_euclidean_topology
            (\<Union>(geotop_link K v)) P"
  obtain P where hP: "P \<in> \<Union>(geotop_link K v)"
    and hC: "C = geotop_component_at UNIV geotop_euclidean_topology
            (\<Union>(geotop_link K v)) P"
    using hC_ex by (by100 blast)
  show "\<exists>L. geotop_is_linear_graph L
      \<and> finite L
      \<and> geotop_polyhedron L = C
      \<and> geotop_complex_connected L
      \<and> (\<forall>w. {w} \<in> L \<longrightarrow>
          card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
          card {l\<in>L. geotop_is_edge l \<and> w \<in> l} = 2)"
    by (rule geotop_link_component_degree_one_or_two_linear_graph_witness_dev34
        [OF hK hv hP hC hdegree_link])
qed

text \<open>Moise \<S>4, Theorem 9: the corresponding graph-classification step
for manifolds with boundary.  After Lemmas 2--4, every link vertex has
degree one or two; a finite connected linear graph with that local
degree bound is either a broken line or a polygon.\<close>
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
  sorry

end
