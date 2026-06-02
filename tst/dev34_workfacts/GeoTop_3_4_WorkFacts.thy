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

lemma geotop_degree_two_vertices_no_graph_endpoint_dev34:
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

end
