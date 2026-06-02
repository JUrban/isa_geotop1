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

lemma geotop_singleton_in_linear_graph_vertex_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hwL: "{w} \<in> L"
  shows "w \<in> geotop_complex_vertices L"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_dev34[OF hL])
  show ?thesis
    using geotop_complex_vertices_eq_0_simplexes[OF hcomplex] hwL by (by100 blast)
qed

lemma geotop_degree_one_vertex_graph_endpoint_dev34:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hwL: "{w} \<in> L"
  assumes hcard1: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 1"
  shows "geotop_graph_endpoint L w"
proof -
  have hw_vertex: "w \<in> geotop_complex_vertices L"
    by (rule geotop_singleton_in_linear_graph_vertex_dev34[OF hL hwL])
  show ?thesis
    using hw_vertex hcard1 unfolding geotop_graph_endpoint_def by (by100 blast)
qed

lemma geotop_degree_one_or_two_no_endpoint_degree_two_dev34:
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
    have hend: "geotop_graph_endpoint L w"
      by (rule geotop_degree_one_vertex_graph_endpoint_dev34[OF hL hwL hcard1])
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

lemma geotop_link_vertex_unique_adjacent_face_incident_link_edge_exhaust_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwL: "{w} \<in> geotop_link K v"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  assumes hw_e: "w \<in> e"
  assumes hunique: "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
  shows "\<exists>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
      \<and> (\<forall>l'. l' \<in> geotop_link K v \<and> geotop_is_edge l' \<and> w \<in> l' \<longrightarrow> l' = l)"
proof -
  obtain \<sigma> where h\<sigma>K: "\<sigma> \<in> K"
    and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
    and h\<sigma>face: "geotop_is_face e \<sigma>"
    and h\<sigma>unique: "\<forall>\<tau>. \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2
        \<and> geotop_is_face e \<tau> \<longrightarrow> \<tau> = \<sigma>"
    using hunique by (by100 blast)
  obtain V u where hV: "geotop_simplex_vertices \<sigma> V"
    and hvV: "v \<in> V"
    and hwV: "w \<in> V"
    and huV: "u \<in> V"
    and hu_ne_v: "u \<noteq> v"
    and hu_ne_w: "u \<noteq> w"
    and hu\<sigma>: "u \<in> \<sigma>"
    and hface_l: "geotop_is_face (geotop_convex_hull {w, u}) \<sigma>"
    and hlL: "geotop_convex_hull {w, u} \<in> geotop_link K v"
    and hledge: "geotop_is_edge (geotop_convex_hull {w, u})"
    and hw_l: "w \<in> geotop_convex_hull {w, u}"
    and hu_l: "u \<in> geotop_convex_hull {w, u}"
    using geotop_link_vertex_incident_2simplex_opposite_vertex_face_link_edge
      [OF hK hvK hwL heK hedge hv_e hw_e h\<sigma>K h\<sigma>2 h\<sigma>face]
    by (by100 blast)
  let ?l = "geotop_convex_hull {w, u}"
  have hv_ne_w: "v \<noteq> w"
    using hwL unfolding geotop_link_def by (by100 blast)
  have hv_ne_u: "v \<noteq> u"
    using hu_ne_v by (by100 blast)
  have hw_ne_u: "w \<noteq> u"
    using hu_ne_w by (by100 blast)
  have hexhaust:
    "\<forall>l'. l' \<in> geotop_link K v \<and> geotop_is_edge l' \<and> w \<in> l' \<longrightarrow> l' = ?l"
  proof (intro allI impI)
    fix l'
    assume hl'_inc: "l' \<in> geotop_link K v \<and> geotop_is_edge l' \<and> w \<in> l'"
    have hl'L: "l' \<in> geotop_link K v"
      using hl'_inc by (by100 blast)
    have hl'edge: "geotop_is_edge l'"
      using hl'_inc by (by100 blast)
    have hw_l': "w \<in> l'"
      using hl'_inc by (by100 blast)
    obtain \<rho> where h\<rho>K: "\<rho> \<in> K"
      and h\<rho>2: "geotop_simplex_dim \<rho> 2"
      and he\<rho>: "geotop_is_face e \<rho>"
      and hl'\<rho>: "geotop_is_face l' \<rho>"
      using geotop_link_edge_through_vertex_adjacent_2simplex_witness
        [OF hK hvK hwL heK hedge hv_e hw_e hl'L hl'edge hw_l']
      by (by100 blast)
    have h\<rho>_eq: "\<rho> = \<sigma>"
      using h\<sigma>unique h\<rho>K h\<rho>2 he\<rho> by (by100 blast)
    have hl'\<sigma>: "geotop_is_face l' \<sigma>"
      using hl'\<rho> h\<rho>_eq by (by100 simp)
    have hv_not_l': "v \<notin> l'"
      using hl'L unfolding geotop_link_def by (by100 blast)
    show "l' = ?l"
      by (rule geotop_2simplex_edge_face_through_vertex_not_other_eq_opposite_dev34
          [OF h\<sigma>2 hV hvV hwV huV hv_ne_w hv_ne_u hw_ne_u
              hl'\<sigma> hl'edge hw_l' hv_not_l'])
  qed
  show ?thesis
    using hlL hledge hw_l hexhaust by (by100 blast)
qed

lemma geotop_link_vertex_two_adjacent_faces_incident_link_edges_exhaust_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hwL: "{w} \<in> geotop_link K v"
  assumes heK: "e \<in> K"
  assumes hedge: "geotop_is_edge e"
  assumes hv_e: "v \<in> e"
  assumes hw_e: "w \<in> e"
  assumes h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
  assumes h\<sigma>K: "\<sigma> \<in> K"
  assumes h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
  assumes h\<sigma>face: "geotop_is_face e \<sigma>"
  assumes h\<tau>K: "\<tau> \<in> K"
  assumes h\<tau>2: "geotop_simplex_dim \<tau> 2"
  assumes h\<tau>face: "geotop_is_face e \<tau>"
  assumes hfaces: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
  shows "\<exists>l\<^sub>\<sigma> l\<^sub>\<tau>. l\<^sub>\<sigma> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<sigma> \<and> w \<in> l\<^sub>\<sigma>
      \<and> l\<^sub>\<tau> \<in> geotop_link K v \<and> geotop_is_edge l\<^sub>\<tau> \<and> w \<in> l\<^sub>\<tau>
      \<and> l\<^sub>\<sigma> \<noteq> l\<^sub>\<tau>
      \<and> (\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
            \<longrightarrow> l = l\<^sub>\<sigma> \<or> l = l\<^sub>\<tau>)"
proof -
  obtain V\<^sub>\<sigma> u\<^sub>\<sigma> where hV\<sigma>: "geotop_simplex_vertices \<sigma> V\<^sub>\<sigma>"
    and hvV\<sigma>: "v \<in> V\<^sub>\<sigma>"
    and hwV\<sigma>: "w \<in> V\<^sub>\<sigma>"
    and huV\<sigma>: "u\<^sub>\<sigma> \<in> V\<^sub>\<sigma>"
    and hu\<sigma>_ne_v: "u\<^sub>\<sigma> \<noteq> v"
    and hu\<sigma>_ne_w: "u\<^sub>\<sigma> \<noteq> w"
    and hface_l\<sigma>: "geotop_is_face (geotop_convex_hull {w, u\<^sub>\<sigma>}) \<sigma>"
    and hl\<sigma>L: "geotop_convex_hull {w, u\<^sub>\<sigma>} \<in> geotop_link K v"
    and hl\<sigma>edge: "geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<sigma>})"
    and hw_l\<sigma>: "w \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}"
    and hu\<sigma>_l\<sigma>: "u\<^sub>\<sigma> \<in> geotop_convex_hull {w, u\<^sub>\<sigma>}"
    using geotop_link_vertex_incident_2simplex_opposite_vertex_face_link_edge
      [OF hK hvK hwL heK hedge hv_e hw_e h\<sigma>K h\<sigma>2 h\<sigma>face]
    by (by100 blast)
  obtain V\<^sub>\<tau> u\<^sub>\<tau> where hV\<tau>: "geotop_simplex_vertices \<tau> V\<^sub>\<tau>"
    and hvV\<tau>: "v \<in> V\<^sub>\<tau>"
    and hwV\<tau>: "w \<in> V\<^sub>\<tau>"
    and huV\<tau>: "u\<^sub>\<tau> \<in> V\<^sub>\<tau>"
    and hu\<tau>_ne_v: "u\<^sub>\<tau> \<noteq> v"
    and hu\<tau>_ne_w: "u\<^sub>\<tau> \<noteq> w"
    and hface_l\<tau>: "geotop_is_face (geotop_convex_hull {w, u\<^sub>\<tau>}) \<tau>"
    and hl\<tau>L: "geotop_convex_hull {w, u\<^sub>\<tau>} \<in> geotop_link K v"
    and hl\<tau>edge: "geotop_is_edge (geotop_convex_hull {w, u\<^sub>\<tau>})"
    and hw_l\<tau>: "w \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
    and hu\<tau>_l\<tau>: "u\<^sub>\<tau> \<in> geotop_convex_hull {w, u\<^sub>\<tau>}"
    using geotop_link_vertex_incident_2simplex_opposite_vertex_face_link_edge
      [OF hK hvK hwL heK hedge hv_e hw_e h\<tau>K h\<tau>2 h\<tau>face]
    by (by100 blast)
  let ?l\<^sub>\<sigma> = "geotop_convex_hull {w, u\<^sub>\<sigma>}"
  let ?l\<^sub>\<tau> = "geotop_convex_hull {w, u\<^sub>\<tau>}"
  have hv_ne_w: "v \<noteq> w"
    using hwL unfolding geotop_link_def by (by100 blast)
  have hv_ne_u\<sigma>: "v \<noteq> u\<^sub>\<sigma>"
    using hu\<sigma>_ne_v by (by100 blast)
  have hw_ne_u\<sigma>: "w \<noteq> u\<^sub>\<sigma>"
    using hu\<sigma>_ne_w by (by100 blast)
  have hv_ne_u\<tau>: "v \<noteq> u\<^sub>\<tau>"
    using hu\<tau>_ne_v by (by100 blast)
  have hw_ne_u\<tau>: "w \<noteq> u\<^sub>\<tau>"
    using hu\<tau>_ne_w by (by100 blast)
  have hl_distinct: "?l\<^sub>\<sigma> \<noteq> ?l\<^sub>\<tau>"
    by (rule geotop_two_2simplex_opposite_edges_distinct_dev34
        [OF h\<sigma>2 h\<tau>2 hV\<sigma> hV\<tau> h\<sigma>\<tau> hv_ne_w hvV\<sigma> hwV\<sigma> huV\<sigma>
            hvV\<tau> hwV\<tau> huV\<tau> hu\<sigma>_ne_v hu\<sigma>_ne_w hu\<tau>_ne_v hu\<tau>_ne_w])
  have hexhaust:
    "\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
      \<longrightarrow> l = ?l\<^sub>\<sigma> \<or> l = ?l\<^sub>\<tau>"
  proof (intro allI impI)
    fix l
    assume hl_inc: "l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l"
    have hlL: "l \<in> geotop_link K v"
      using hl_inc by (by100 blast)
    have hledge: "geotop_is_edge l"
      using hl_inc by (by100 blast)
    have hw_l: "w \<in> l"
      using hl_inc by (by100 blast)
    obtain \<rho> where h\<rho>K: "\<rho> \<in> K"
      and h\<rho>2: "geotop_simplex_dim \<rho> 2"
      and he\<rho>: "geotop_is_face e \<rho>"
      and hl\<rho>: "geotop_is_face l \<rho>"
      using geotop_link_edge_through_vertex_adjacent_2simplex_witness
        [OF hK hvK hwL heK hedge hv_e hw_e hlL hledge hw_l]
      by (by100 blast)
    have h\<rho>in_faces: "\<rho> \<in> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>}"
      using h\<rho>K h\<rho>2 he\<rho> by (by100 simp)
    have h\<rho>case: "\<rho> = \<sigma> \<or> \<rho> = \<tau>"
      using h\<rho>in_faces hfaces by (by100 blast)
    have hv_not_l: "v \<notin> l"
      using hlL unfolding geotop_link_def by (by100 blast)
    show "l = ?l\<^sub>\<sigma> \<or> l = ?l\<^sub>\<tau>"
    proof (rule disjE[OF h\<rho>case])
      assume h\<rho>\<sigma>: "\<rho> = \<sigma>"
      have hl\<sigma>: "geotop_is_face l \<sigma>"
        using hl\<rho> h\<rho>\<sigma> by (by100 simp)
      have "l = ?l\<^sub>\<sigma>"
        by (rule geotop_2simplex_edge_face_through_vertex_not_other_eq_opposite_dev34
            [OF h\<sigma>2 hV\<sigma> hvV\<sigma> hwV\<sigma> huV\<sigma> hv_ne_w hv_ne_u\<sigma> hw_ne_u\<sigma>
                hl\<sigma> hledge hw_l hv_not_l])
      thus ?thesis
        by (by100 blast)
    next
      assume h\<rho>\<tau>: "\<rho> = \<tau>"
      have hl\<tau>: "geotop_is_face l \<tau>"
        using hl\<rho> h\<rho>\<tau> by (by100 simp)
      have "l = ?l\<^sub>\<tau>"
        by (rule geotop_2simplex_edge_face_through_vertex_not_other_eq_opposite_dev34
            [OF h\<tau>2 hV\<tau> hvV\<tau> hwV\<tau> huV\<tau> hv_ne_w hv_ne_u\<tau> hw_ne_u\<tau>
                hl\<tau> hledge hw_l hv_not_l])
      thus ?thesis
        by (by100 blast)
    qed
  qed
  show ?thesis
    using hl\<sigma>L hl\<sigma>edge hw_l\<sigma> hl\<tau>L hl\<tau>edge hw_l\<tau> hl_distinct hexhaust
    by (by100 blast)
qed

lemma geotop_link_vertices_face_count_one_or_two_incident_link_edge_card_dev34:
  fixes K :: "(real^2) set set"
  assumes hK: "geotop_is_complex K"
  assumes hvK: "{v} \<in> K"
  assumes hcases: "\<forall>e\<in>K. geotop_is_edge e \<and> v \<in> e \<longrightarrow>
      ((\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>)
       \<or> (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
          \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
          \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
          \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}))"
  shows "\<forall>w. {w} \<in> geotop_link K v \<longrightarrow>
      card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 1 \<or>
      card {l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l} = 2"
proof (intro allI impI)
  fix w
  let ?S = "{l\<in>geotop_link K v. geotop_is_edge l \<and> w \<in> l}"
  assume hwL: "{w} \<in> geotop_link K v"
  obtain e where heK: "e \<in> K"
    and hedge: "geotop_is_edge e"
    and hv_e: "v \<in> e"
    and hw_e: "w \<in> e"
    using geotop_link_vertex_incident_edge_witness[OF hK hvK hwL]
    by (by100 blast)
  have hcase:
      "(\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>)
       \<or> (\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
          \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
          \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
          \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>})"
    using hcases heK hedge hv_e by (by100 blast)
  show "card ?S = 1 \<or> card ?S = 2"
  proof (rule disjE[OF hcase])
    assume hone: "\<exists>!\<sigma>. \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>"
    obtain l where hlL: "l \<in> geotop_link K v"
      and hledge: "geotop_is_edge l"
      and hw_l: "w \<in> l"
      and hexhaust: "\<forall>l'. l' \<in> geotop_link K v \<and> geotop_is_edge l' \<and> w \<in> l' \<longrightarrow> l' = l"
      using geotop_link_vertex_unique_adjacent_face_incident_link_edge_exhaust_dev34
        [OF hK hvK hwL heK hedge hv_e hw_e hone]
      by (by100 blast)
    have hS_eq: "?S = {l}"
    proof
      show "?S \<subseteq> {l}"
        using hexhaust by (by100 blast)
    next
      show "{l} \<subseteq> ?S"
        using hlL hledge hw_l by (by100 blast)
    qed
    show "card ?S = 1 \<or> card ?S = 2"
      using hS_eq by (by100 simp)
  next
    assume htwo: "\<exists>\<sigma> \<tau>. \<sigma> \<noteq> \<tau>
          \<and> \<sigma> \<in> K \<and> geotop_simplex_dim \<sigma> 2 \<and> geotop_is_face e \<sigma>
          \<and> \<tau> \<in> K \<and> geotop_simplex_dim \<tau> 2 \<and> geotop_is_face e \<tau>
          \<and> {\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
    obtain \<sigma> \<tau> where h\<sigma>\<tau>: "\<sigma> \<noteq> \<tau>"
      and h\<sigma>K: "\<sigma> \<in> K"
      and h\<sigma>2: "geotop_simplex_dim \<sigma> 2"
      and h\<sigma>face: "geotop_is_face e \<sigma>"
      and h\<tau>K: "\<tau> \<in> K"
      and h\<tau>2: "geotop_simplex_dim \<tau> 2"
      and h\<tau>face: "geotop_is_face e \<tau>"
      and hfaces: "{\<rho>\<in>K. geotop_simplex_dim \<rho> 2 \<and> geotop_is_face e \<rho>} = {\<sigma>, \<tau>}"
      using htwo by (by100 blast)
    obtain l\<^sub>\<sigma> l\<^sub>\<tau> where hl\<sigma>L: "l\<^sub>\<sigma> \<in> geotop_link K v"
      and hl\<sigma>edge: "geotop_is_edge l\<^sub>\<sigma>"
      and hw_l\<sigma>: "w \<in> l\<^sub>\<sigma>"
      and hl\<tau>L: "l\<^sub>\<tau> \<in> geotop_link K v"
      and hl\<tau>edge: "geotop_is_edge l\<^sub>\<tau>"
      and hw_l\<tau>: "w \<in> l\<^sub>\<tau>"
      and hl_distinct: "l\<^sub>\<sigma> \<noteq> l\<^sub>\<tau>"
      and hexhaust: "\<forall>l. l \<in> geotop_link K v \<and> geotop_is_edge l \<and> w \<in> l
            \<longrightarrow> l = l\<^sub>\<sigma> \<or> l = l\<^sub>\<tau>"
      using geotop_link_vertex_two_adjacent_faces_incident_link_edges_exhaust_dev34
        [OF hK hvK hwL heK hedge hv_e hw_e h\<sigma>\<tau> h\<sigma>K h\<sigma>2 h\<sigma>face
            h\<tau>K h\<tau>2 h\<tau>face hfaces]
      by (by100 blast)
    have hS_eq: "?S = {l\<^sub>\<sigma>, l\<^sub>\<tau>}"
    proof
      show "?S \<subseteq> {l\<^sub>\<sigma>, l\<^sub>\<tau>}"
        using hexhaust by (by100 blast)
    next
      show "{l\<^sub>\<sigma>, l\<^sub>\<tau>} \<subseteq> ?S"
        using hl\<sigma>L hl\<sigma>edge hw_l\<sigma> hl\<tau>L hl\<tau>edge hw_l\<tau> by (by100 blast)
    qed
    have "card ?S = 2"
      using hS_eq hl_distinct by (by100 simp)
    show "card ?S = 1 \<or> card ?S = 2"
      using \<open>card ?S = 2\<close> by (by100 blast)
  qed
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
  sorry

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
      by (rule geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_broken_line_dev34
          [OF hL hfin hconn hdegree12 hend])
    show ?thesis
      using hline by (by100 blast)
  next
    assume hnoend: "\<forall>w. {w} \<in> L \<longrightarrow> \<not> geotop_graph_endpoint L w"
    have hdegree2: "\<forall>w. {w} \<in> L \<longrightarrow>
        card {e\<in>L. geotop_is_edge e \<and> w \<in> e} = 2"
      by (rule geotop_degree_one_or_two_no_endpoint_degree_two_dev34
          [OF hL hdegree12 hnoend])
    have hpoly: "geotop_is_polygon (geotop_polyhedron L)"
      by (rule geotop_finite_connected_degree_two_linear_graph_polygon_dev34
          [OF hL hfin hconn hdegree2])
    show ?thesis
      using hpoly by (by100 blast)
  qed
qed

end
