theory GeoTop_3_4_GraphWork
  imports "GeoTop34GraphFactsDirty.GeoTop_3_4_GraphFacts"
begin

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
  sorry

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
