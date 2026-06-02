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
  have hshape: "geotop_is_broken_line (geotop_polyhedron L) \<or>
      geotop_is_polygon (geotop_polyhedron L)"
    by (rule geotop_finite_connected_nonisolated_linear_graph_line_or_polygon_dev34
        [OF hL hfin hconn hnonisolated])
  have hnot_line: "\<not> geotop_is_broken_line (geotop_polyhedron L)"
    by (rule geotop_degree_two_linear_graph_polyhedron_not_broken_line_dev34
        [OF hL hfin hdegree])
  show ?thesis
    using hshape hnot_line by (by100 blast)
qed

text \<open>Moise \<S>4, Theorem 9: the corresponding graph-classification step
for manifolds with boundary.  A finite connected linear graph with no
isolated vertex is either a broken line or a polygon.\<close>
lemma geotop_finite_connected_nonisolated_linear_graph_line_or_polygon_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hnonisolated: "\<forall>w. {w} \<in> L \<longrightarrow>
      (\<exists>e\<in>L. geotop_is_edge e \<and> w \<in> e)"
  shows "geotop_is_broken_line (geotop_polyhedron L) \<or>
      geotop_is_polygon (geotop_polyhedron L)"
  sorry

end
