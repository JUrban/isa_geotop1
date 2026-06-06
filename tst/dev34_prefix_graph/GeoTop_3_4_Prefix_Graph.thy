theory GeoTop_3_4_Prefix_Graph
  imports "GeoTop34PrefixBaseDirty.GeoTop_3_4_Prefix_Base"
begin

lemma geotop_graph_endpoint_delete_leaf_complex_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "geotop_is_complex (L - {{w}, e})"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have hsub: "L - {{w}, e} \<subseteq> L"
    by (by100 simp)
  have hfaces:
      "\<forall>\<sigma>\<in>L - {{w}, e}. \<forall>\<tau>. geotop_is_face \<tau> \<sigma> \<longrightarrow> \<tau> \<in> L - {{w}, e}"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau>
    assume h\<sigma>rest: "\<sigma> \<in> L - {{w}, e}"
    assume hface: "geotop_is_face \<tau> \<sigma>"
    have h\<sigma>L: "\<sigma> \<in> L"
      using h\<sigma>rest by (by100 simp)
    have h\<tau>L: "\<tau> \<in> L"
      using geotop_is_complex_face_closed[OF hcomplex] h\<sigma>L hface by (by100 blast)
    have h\<tau>sub\<sigma>: "\<tau> \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset_prefix[OF hface])
    have h\<sigma>ne_w: "\<sigma> \<noteq> {w}"
      using h\<sigma>rest by (by100 simp)
    have h\<sigma>ne_e: "\<sigma> \<noteq> e"
      using h\<sigma>rest by (by100 simp)
    have h\<tau>ne_w: "\<tau> \<noteq> {w}"
    proof
      assume h\<tau>w: "\<tau> = {w}"
      have hw\<sigma>: "w \<in> \<sigma>"
        using h\<tau>sub\<sigma> h\<tau>w by (by100 blast)
      have hcase: "\<sigma> = {w} \<or> \<sigma> = e"
        by (rule geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_prefix
            [OF hL hfin hend heL hedge hwe h\<sigma>L hw\<sigma>])
      show False using hcase h\<sigma>ne_w h\<sigma>ne_e by (by100 blast)
    qed
    have h\<tau>ne_e: "\<tau> \<noteq> e"
    proof
      assume h\<tau>e: "\<tau> = e"
      have hw\<sigma>: "w \<in> \<sigma>"
        using h\<tau>sub\<sigma> h\<tau>e hwe by (by100 blast)
      have hcase: "\<sigma> = {w} \<or> \<sigma> = e"
        by (rule geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_prefix
            [OF hL hfin hend heL hedge hwe h\<sigma>L hw\<sigma>])
      show False using hcase h\<sigma>ne_w h\<sigma>ne_e by (by100 blast)
    qed
    show "\<tau> \<in> L - {{w}, e}"
      using h\<tau>L h\<tau>ne_w h\<tau>ne_e by (by100 simp)
  qed
  show ?thesis
    by (rule geotop_complex_subset_is_complex[OF hcomplex hsub hfaces])
qed

lemma geotop_graph_endpoint_delete_leaf_linear_graph_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  shows "geotop_is_linear_graph (L - {{w}, e})"
proof -
  have hcomplex: "geotop_is_complex (L - {{w}, e})"
    by (rule geotop_graph_endpoint_delete_leaf_complex_prefix
        [OF hL hfin hend heL hedge hwe])
  have hL1: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_prefix[OF hL])
  have hrest1: "geotop_complex_is_1dim (L - {{w}, e})"
  proof (unfold geotop_complex_is_1dim_def, rule ballI)
    fix \<sigma>
    assume h\<sigma>rest: "\<sigma> \<in> L - {{w}, e}"
    have h\<sigma>L: "\<sigma> \<in> L"
      using h\<sigma>rest by (by100 simp)
    show "\<exists>n::nat. n \<le> 1 \<and> geotop_simplex_dim \<sigma> n"
      using hL1 h\<sigma>L unfolding geotop_complex_is_1dim_def by (by100 blast)
  qed
  show ?thesis
    by (rule geotop_complex_1dim_imp_linear_graph_prefix[OF hcomplex hrest1])
qed

lemma geotop_graph_endpoint_delete_leaf_finite_prefix:
  fixes L :: "(real^2) set set"
  assumes hfin: "finite L"
  shows "finite (L - {{w}, e})"
  using hfin by (by100 simp)

lemma geotop_delete_leaf_incident_edges_neighbor_eq_prefix:
  fixes L :: "(real^2) set set"
  assumes hqw: "q \<noteq> w"
  shows "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l}
      = {l\<in>L. geotop_is_edge l \<and> q \<in> l} - {e}"
proof
  show "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l}
      \<subseteq> {l\<in>L. geotop_is_edge l \<and> q \<in> l} - {e}"
  proof
    fix l
    assume hl: "l \<in> {l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l}"
    have "l \<in> L \<and> geotop_is_edge l \<and> q \<in> l \<and> l \<noteq> e"
      using hl by (by100 simp)
    show "l \<in> {l\<in>L. geotop_is_edge l \<and> q \<in> l} - {e}"
      using \<open>l \<in> L \<and> geotop_is_edge l \<and> q \<in> l \<and> l \<noteq> e\<close> by (by100 simp)
  qed
next
  show "{l\<in>L. geotop_is_edge l \<and> q \<in> l} - {e}
      \<subseteq> {l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l}"
  proof
    fix l
    assume hl: "l \<in> {l\<in>L. geotop_is_edge l \<and> q \<in> l} - {e}"
    have hlL: "l \<in> L" and hledge: "geotop_is_edge l" and hql: "q \<in> l" and hlne: "l \<noteq> e"
      using hl by (by100 simp_all)
    have "l \<noteq> {w}"
    proof
      assume "l = {w}"
      hence "q = w" using hql by (by100 simp)
      thus False using hqw by (by100 blast)
    qed
    have "l \<in> L - {{w}, e}"
      using hlL hlne \<open>l \<noteq> {w}\<close> by (by100 simp)
    show "l \<in> {l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l}"
      using \<open>l \<in> L - {{w}, e}\<close> hledge hql by (by100 simp)
  qed
qed

lemma geotop_delete_leaf_incident_edges_away_eq_prefix:
  fixes L :: "(real^2) set set"
  assumes hwe: "w \<in> e"
  assumes hxe: "x \<notin> e"
  shows "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}
      = {l\<in>L. geotop_is_edge l \<and> x \<in> l}"
proof
  show "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}
      \<subseteq> {l\<in>L. geotop_is_edge l \<and> x \<in> l}"
  proof
    fix l
    assume hl: "l \<in> {l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}"
    show "l \<in> {l\<in>L. geotop_is_edge l \<and> x \<in> l}"
      using hl by (by100 simp)
  qed
next
  show "{l\<in>L. geotop_is_edge l \<and> x \<in> l}
      \<subseteq> {l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}"
  proof
    fix l
    assume hl: "l \<in> {l\<in>L. geotop_is_edge l \<and> x \<in> l}"
    have hlL: "l \<in> L" and hledge: "geotop_is_edge l" and hxl: "x \<in> l"
      using hl by (by100 simp_all)
    have hlne: "l \<noteq> e"
      using hxl hxe by (by100 blast)
    have "l \<noteq> {w}"
    proof
      assume "l = {w}"
      hence "x = w" using hxl by (by100 simp)
      hence "x \<in> e" using hwe by (by100 simp)
      thus False using hxe by (by100 blast)
    qed
    have "l \<in> L - {{w}, e}"
      using hlL hlne \<open>l \<noteq> {w}\<close> by (by100 simp)
    show "l \<in> {l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}"
      using \<open>l \<in> L - {{w}, e}\<close> hledge hxl by (by100 simp)
  qed
qed

lemma geotop_delete_leaf_rest_vertex_not_in_deleted_edge_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes heL: "e \<in> L"
  assumes hqw: "q \<noteq> w"
  assumes heq: "e = closed_segment w q"
  assumes hxrest: "{x} \<in> L - {{w}, e}"
  assumes hxq: "x \<noteq> q"
  shows "x \<notin> e"
proof
  assume hxe: "x \<in> e"
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have hxL: "{x} \<in> L"
    using hxrest by (by100 simp)
  have hxw: "x \<noteq> w"
  proof
    assume "x = w"
    hence "{x} = {w}" by (by100 simp)
    thus False using hxrest by (by100 simp)
  qed
  have hwq: "w \<noteq> q"
    using hqw by (by100 blast)
  have hendpoint: "x = w \<or> x = q"
    by (rule geotop_1dim_vertex_in_1simplex_is_endpoint
        [OF hcomplex hxL heL heq hwq hxe])
  show False using hendpoint hxw hxq by (by100 blast)
qed

lemma geotop_delete_leaf_rest_vertex_degree_preserved_away_neighbor_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes heL: "e \<in> L"
  assumes hqw: "q \<noteq> w"
  assumes heq: "e = closed_segment w q"
  assumes hxrest: "{x} \<in> L - {{w}, e}"
  assumes hxq: "x \<noteq> q"
  shows "card {l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}
      = card {l\<in>L. geotop_is_edge l \<and> x \<in> l}"
proof -
  have hx_not_e: "x \<notin> e"
    by (rule geotop_delete_leaf_rest_vertex_not_in_deleted_edge_prefix
        [OF hL heL hqw heq hxrest hxq])
  have hwe: "w \<in> e"
    using heq by (by100 simp)
  have "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}
      = {l\<in>L. geotop_is_edge l \<and> x \<in> l}"
    by (rule geotop_delete_leaf_incident_edges_away_eq_prefix[OF hwe hx_not_e])
  show ?thesis
    using \<open>{l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}
      = {l\<in>L. geotop_is_edge l \<and> x \<in> l}\<close>
    by (by100 simp)
qed

lemma geotop_branch_vertex_deletion_disconnects_finite_linear_graph_prefix:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_fin: "finite L"
  assumes hwL: "{w} \<in> L"
  assumes hSCC: "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
      (geotop_polyhedron L)"
  assumes hbranch: "card {e\<in>L. geotop_is_edge e \<and> w \<in> e} > 2"
  shows "\<not> top1_connected_on (geotop_polyhedron L - {w})
      (subspace_topology UNIV geotop_euclidean_topology
        (geotop_polyhedron L - {w}))"
  (**
    Finite graph cutpoint fact for Moise Figure 3.2 in the polygon-carrier
    case.  With at least three incident edge germs at \<open>w\<close> on a simple closed
    curve carrier, deleting \<open>w\<close> leaves at least three separated local
    branches, so the remaining carrier is disconnected. **)
proof -
  have hw_poly: "w \<in> geotop_polyhedron L"
    using hwL unfolding geotop_polyhedron_def by (by100 blast)
  have hSCC_punctured_connected: "top1_connected_on (geotop_polyhedron L - {w})
      (subspace_topology UNIV geotop_euclidean_topology
        (geotop_polyhedron L - {w}))"
    by (rule scc_minus_point_connected
        [OF geotop_euclidean_topology_UNIV_strict
            geotop_euclidean_topology_UNIV_hausdorff hSCC hw_poly])
  have hbranch_local_disconnect:
      "\<not> top1_connected_on (geotop_polyhedron L - {w})
        (subspace_topology UNIV geotop_euclidean_topology
          (geotop_polyhedron L - {w}))"
    sorry
  show ?thesis
    by (rule hbranch_local_disconnect)
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
    the finite polygonal graph would make the carrier locally a broken line,
    not a polygonal 1-sphere. **)
  sorry

lemma geotop_polygon_finite_linear_graph_vertices_no_branch_prefix:
  fixes L :: "(real^2) set set"
  assumes hL_linear: "geotop_is_linear_graph L"
  assumes hL_fin: "finite L"
  assumes hL_conn: "geotop_complex_connected L"
  assumes hL_polygon: "geotop_is_polygon (geotop_polyhedron L)"
  shows "\<forall>w. {w} \<in> L \<longrightarrow>
      card {e\<in>L. geotop_is_edge e \<and> w \<in> e} \<le> 2"
  (**
    Moise Figure 3.2 boundary-cycle step, branch exclusion.  More than two
    incident boundary edges at a vertex gives a local branch point, contrary
    to the polygonal 1-sphere carrier. **)
proof -
  have hSCC:
      "top1_simple_closed_curve_on UNIV geotop_euclidean_topology
        (geotop_polyhedron L)"
    by (rule geotop_polygon_top1_simple_closed_curve_prefix[OF hL_polygon])
  show ?thesis
  proof (intro allI impI)
    fix w
    assume hwL: "{w} \<in> L"
    show "card {e \<in> L. geotop_is_edge e \<and> w \<in> e} \<le> 2"
    proof (rule ccontr)
      assume hnot_le: "\<not> card {e \<in> L. geotop_is_edge e \<and> w \<in> e} \<le> 2"
      have hbranch: "card {e \<in> L. geotop_is_edge e \<and> w \<in> e} > 2"
        using hnot_le by (by100 simp)
      have hw_poly: "w \<in> geotop_polyhedron L"
        using hwL unfolding geotop_polyhedron_def by (by100 blast)
      have hdisc: "\<not> top1_connected_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w}))"
        by (rule geotop_branch_vertex_deletion_disconnects_finite_linear_graph_prefix
            [OF hL_linear hL_fin hwL hSCC hbranch])
      have hconn: "top1_connected_on (geotop_polyhedron L - {w})
          (subspace_topology UNIV geotop_euclidean_topology
            (geotop_polyhedron L - {w}))"
        by (rule scc_minus_point_connected
            [OF geotop_euclidean_topology_UNIV_strict
                geotop_euclidean_topology_UNIV_hausdorff hSCC hw_poly])
      show False
        using hdisc hconn by (by100 blast)
    qed
  qed
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
  sorry

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
