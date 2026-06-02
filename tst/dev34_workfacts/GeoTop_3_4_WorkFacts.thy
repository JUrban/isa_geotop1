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

end
