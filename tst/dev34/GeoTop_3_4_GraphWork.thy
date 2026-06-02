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
