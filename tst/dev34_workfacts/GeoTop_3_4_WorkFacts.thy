theory GeoTop_3_4_WorkFacts
  imports "GeoTop34FactsDirty.GeoTop_3_4_Facts"
begin

lemma geotop_linear_graph_complex_dev34:
  assumes hL: "geotop_is_linear_graph L"
  shows "geotop_is_complex L"
  using hL unfolding geotop_is_linear_graph_def by (by100 blast)

lemma geotop_linear_graph_1dim_dev34:
  assumes hL: "geotop_is_linear_graph L"
  shows "geotop_complex_is_1dim L"
  using geotop_linear_graph_imp_complex_1dim_dev34[OF hL] by (by100 blast)

lemma geotop_finite_linear_graph_vertices_finite_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  shows "finite (geotop_complex_vertices L)"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  show ?thesis
    by (rule geotop_finite_complex_vertices_finite_dev34[OF hcomplex hfin])
qed

lemma geotop_finite_incident_edges_finite_dev34:
  assumes hfin: "finite L"
  shows "finite {e\<in>L. geotop_is_edge e \<and> w \<in> e}"
  using hfin by (by100 simp)

lemma geotop_complex_connected_top1_connected_polyhedron_dev34:
  fixes K :: "(real^2) set set"
  assumes hconn: "geotop_complex_connected K"
  shows "top1_connected_on (geotop_polyhedron K)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
proof -
  have hcomplex: "geotop_is_complex K"
    using hconn unfolding geotop_complex_connected_def by (by100 blast)
  have hpath: "top1_path_connected_on (geotop_polyhedron K)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron K))"
    using Theorem_GT_1_12(1)[OF hcomplex] hconn by (by100 blast)
  show ?thesis
    using Theorem_GT_1_12(2)[OF hcomplex] hpath by (by100 blast)
qed

lemma geotop_degree_two_vertices_nonisolated_dev34:
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

text \<open>Moise \<S>4, Theorem 8: the graph-classification step used after
Lemmas 2--4.  A finite connected linear graph whose every vertex has
exactly two incident edges is a polygon.\<close>
lemma geotop_finite_connected_degree_two_linear_graph_polygon_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hconn: "geotop_complex_connected L"
  assumes hdegree: "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
  shows "geotop_is_polygon (geotop_polyhedron L)"
  sorry

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
