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

lemma geotop_segment_face_with_nonendpoint_eq_prefix:
  fixes F :: "(real^2) set" and a b x :: "real^2"
  assumes hface: "geotop_is_face F (closed_segment a b)"
  assumes hab: "a \<noteq> b"
  assumes hxF: "x \<in> F"
  assumes hxa: "x \<noteq> a"
  assumes hxb: "x \<noteq> b"
  shows "F = closed_segment a b"
proof -
  have hseg_sv: "geotop_simplex_vertices (closed_segment a b) {a, b}"
    by (rule geotop_closed_segment_simplex_vertices[OF hab])
  obtain V W where hV_sv: "geotop_simplex_vertices (closed_segment a b) V"
      and hW_ne: "W \<noteq> {}"
      and hW_sub: "W \<subseteq> V"
      and hF_hull: "F = geotop_convex_hull W"
    using hface unfolding geotop_is_face_def by (by100 blast)
  have hV_eq: "V = {a, b}"
    using geotop_simplex_vertices_unique[OF hV_sv hseg_sv] .
  have hW_sub_ab: "W \<subseteq> {a, b}"
    using hW_sub hV_eq by (by100 simp)
  have hW_cases: "W = {a} \<or> W = {b} \<or> W = {a, b}"
    using hW_sub_ab hW_ne by (by100 blast)
  have hF_HOL: "F = convex hull W"
    using hF_hull geotop_convex_hull_eq_HOL by (by100 simp)
  have hW_eq_ab: "W = {a, b}"
  proof (rule disjE[OF hW_cases])
    assume hW_a: "W = {a}"
    have hF_a: "F = {a}"
      using hF_HOL hW_a by (by100 simp)
    have "x = a" using hxF hF_a by (by100 blast)
    thus ?thesis using hxa by (by100 blast)
  next
    assume hW_rest: "W = {b} \<or> W = {a, b}"
    show ?thesis
    proof (rule disjE[OF hW_rest])
      assume hW_b: "W = {b}"
      have hF_b: "F = {b}"
        using hF_HOL hW_b by (by100 simp)
      have "x = b" using hxF hF_b by (by100 blast)
      thus ?thesis using hxb by (by100 blast)
    next
      assume hW_ab: "W = {a, b}"
      show ?thesis using hW_ab .
    qed
  qed
  have "F = convex hull {a, b}"
    using hF_HOL hW_eq_ab by (by100 simp)
  also have "\<dots> = closed_segment a b"
    by (simp add: segment_convex_hull)
  finally show ?thesis .
qed

lemma geotop_1dim_simplex_subset_edge_cases_prefix:
  fixes L :: "(real^2) set set"
  assumes hcomplex: "geotop_is_complex L"
  assumes h\<sigma>L: "\<sigma> \<in> L"
  assumes heL: "e \<in> L"
  assumes hweq: "e = closed_segment w q"
  assumes hwq: "w \<noteq> q"
  assumes h\<sigma>sub: "\<sigma> \<subseteq> e"
  shows "\<sigma> = {w} \<or> \<sigma> = {q} \<or> \<sigma> = e"
proof -
  have hface: "geotop_is_face \<sigma> e"
    by (rule geotop_complex_subset_simplex_face_prefix[OF hcomplex h\<sigma>L heL h\<sigma>sub])
  have hface_seg: "geotop_is_face \<sigma> (closed_segment w q)"
    using hface hweq by (by100 simp)
  have hcases: "\<sigma> = {w} \<or> \<sigma> = {q} \<or> \<sigma> = closed_segment w q"
    by (rule geotop_segment_face_cases_prefix[OF hface_seg hwq])
  show ?thesis using hcases hweq by (by100 blast)
qed

lemma geotop_delete_leaf_edge_inter_rest_polyhedron_subset_neighbor_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes hqw: "q \<noteq> w"
  assumes heq: "e = closed_segment w q"
  shows "e \<inter> geotop_polyhedron (L - {{w}, e}) \<subseteq> {q}"
proof
  fix x
  assume hx: "x \<in> e \<inter> geotop_polyhedron (L - {{w}, e})"
  have hxe: "x \<in> e"
    using hx by (by100 simp)
  obtain \<sigma> where h\<sigma>rest: "\<sigma> \<in> L - {{w}, e}" and hx\<sigma>: "x \<in> \<sigma>"
    using hx unfolding geotop_polyhedron_def by (by100 blast)
  have h\<sigma>L: "\<sigma> \<in> L"
    using h\<sigma>rest by (by100 simp)
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have hnonempty: "e \<inter> \<sigma> \<noteq> {}"
    using hxe hx\<sigma> by (by100 blast)
  have hface_e: "geotop_is_face (e \<inter> \<sigma>) e"
    using geotop_is_complex_intersection[OF hcomplex] heL h\<sigma>L hnonempty by (by100 blast)
  show "x \<in> {q}"
  proof (cases "x = q")
    case True
    show ?thesis using True by (by100 simp)
  next
    case False
    have hwq: "w \<noteq> q"
      using hqw by (by100 blast)
    show ?thesis
    proof (cases "x = w")
      case True
      have hw\<sigma>: "w \<in> \<sigma>"
        using True hx\<sigma> by (by100 simp)
      have hcase: "\<sigma> = {w} \<or> \<sigma> = e"
        by (rule geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_prefix
            [OF hL hfin hend heL hedge hwe h\<sigma>L hw\<sigma>])
      have False using hcase h\<sigma>rest by (by100 simp)
      thus ?thesis by (rule FalseE)
    next
      case hxnw: False
      have hx_inter: "x \<in> e \<inter> \<sigma>"
        using hxe hx\<sigma> by (by100 blast)
      have hface_seg: "geotop_is_face (e \<inter> \<sigma>) (closed_segment w q)"
        using hface_e heq by (by100 simp)
      have hinter_eq: "e \<inter> \<sigma> = closed_segment w q"
        by (rule geotop_segment_face_with_nonendpoint_eq_prefix
            [OF hface_seg hwq hx_inter hxnw False])
      have "w \<in> \<sigma>"
        using hinter_eq hwe heq by (by100 blast)
      have hcase: "\<sigma> = {w} \<or> \<sigma> = e"
        by (rule geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_prefix
            [OF hL hfin hend heL hedge hwe h\<sigma>L \<open>w \<in> \<sigma>\<close>])
      have False using hcase h\<sigma>rest by (by100 simp)
      thus ?thesis by (rule FalseE)
    qed
  qed
qed

lemma geotop_delete_leaf_edge_inter_rest_polyhedron_eq_neighbor_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes hqL: "{q} \<in> L"
  assumes hqw: "q \<noteq> w"
  assumes heq: "e = closed_segment w q"
  shows "e \<inter> geotop_polyhedron (L - {{w}, e}) = {q}"
proof
  show "e \<inter> geotop_polyhedron (L - {{w}, e}) \<subseteq> {q}"
    by (rule geotop_delete_leaf_edge_inter_rest_polyhedron_subset_neighbor_prefix
        [OF hL hfin hend heL hedge hwe hqw heq])
next
  show "{q} \<subseteq> e \<inter> geotop_polyhedron (L - {{w}, e})"
  proof
    fix x
    assume hx: "x \<in> {q}"
    have hxq: "x = q"
      using hx by (by100 simp)
    have hqe: "q \<in> e"
      using heq by (by100 simp)
    have hq_ne_w: "{q} \<noteq> {w}"
      using hqw by (by100 blast)
    have hq_ne_e: "{q} \<noteq> e"
    proof
      assume "{q} = e"
      have "w \<in> {q}"
        using hwe \<open>{q} = e\<close> by (by100 simp)
      hence "w = q" by (by100 simp)
      thus False using hqw by (by100 blast)
    qed
    have hqrest: "{q} \<in> L - {{w}, e}"
      using hqL hq_ne_w hq_ne_e by (by100 simp)
    have "q \<in> geotop_polyhedron (L - {{w}, e})"
      unfolding geotop_polyhedron_def using hqrest by (by100 blast)
    show "x \<in> e \<inter> geotop_polyhedron (L - {{w}, e})"
      using hxq hqe \<open>q \<in> geotop_polyhedron (L - {{w}, e})\<close> by (by100 simp)
  qed
qed

lemma geotop_closed_segment_HOL_arc_between_prefix:
  fixes w q :: "real^2"
  assumes hwq: "w \<noteq> q"
  shows "\<exists>\<gamma>::real \<Rightarrow> real^2. arc \<gamma> \<and> path_image \<gamma> = closed_segment w q
      \<and> pathstart \<gamma> = w \<and> pathfinish \<gamma> = q"
proof -
  let ?\<gamma> = "linepath w q"
  have harc: "arc ?\<gamma>"
    by (rule arc_linepath[OF hwq])
  have hpim: "path_image ?\<gamma> = closed_segment w q"
  proof -
    have "path_image ?\<gamma> = ?\<gamma> ` {0..1}"
      unfolding path_image_def by (by100 simp)
    also have "\<dots> = closed_segment w q"
      by (rule linepath_image_01)
    finally show ?thesis .
  qed
  have hstart: "pathstart ?\<gamma> = w"
    unfolding pathstart_def linepath_def by (by100 simp)
  have hfinish: "pathfinish ?\<gamma> = q"
    unfolding pathfinish_def linepath_def by (by100 simp)
  show ?thesis using harc hpim hstart hfinish by (by100 blast)
qed

lemma geotop_degree_one_vertex_simplex_containing_eq_vertex_or_edge_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hqL: "{q} \<in> L"
  assumes hqcard: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 1"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hqe: "q \<in> e"
  assumes h\<sigma>L: "\<sigma> \<in> L"
  assumes hq\<sigma>: "q \<in> \<sigma>"
  shows "\<sigma> = {q} \<or> \<sigma> = e"
proof -
  have hq_endpoint: "geotop_graph_endpoint L q"
    by (rule geotop_degree_one_vertex_graph_endpoint_prefix[OF hL hqL hqcard])
  show ?thesis
    by (rule geotop_graph_endpoint_simplex_containing_endpoint_eq_vertex_or_edge_prefix
        [OF hL hfin hq_endpoint heL hedge hqe h\<sigma>L hq\<sigma>])
qed

lemma geotop_polyhedron_two_vertices_edge_eq_prefix:
  fixes L :: "(real^2) set set"
  assumes hsub: "L \<subseteq> {{w}, {q}, e}"
  assumes heL: "e \<in> L"
  assumes hwe: "w \<in> e"
  assumes hqe: "q \<in> e"
  shows "geotop_polyhedron L = e"
proof
  show "geotop_polyhedron L \<subseteq> e"
  proof
    fix x
    assume hx: "x \<in> geotop_polyhedron L"
    obtain \<sigma> where h\<sigma>L: "\<sigma> \<in> L" and hx\<sigma>: "x \<in> \<sigma>"
      using hx unfolding geotop_polyhedron_def by (by100 blast)
    have hcases: "\<sigma> = {w} \<or> \<sigma> = {q} \<or> \<sigma> = e"
      using hsub h\<sigma>L by (by100 blast)
    show "x \<in> e"
    proof (rule disjE[OF hcases])
      assume "\<sigma> = {w}"
      show ?thesis using hx\<sigma> \<open>\<sigma> = {w}\<close> hwe by (by100 blast)
    next
      assume hrest: "\<sigma> = {q} \<or> \<sigma> = e"
      show ?thesis
      proof (rule disjE[OF hrest])
        assume "\<sigma> = {q}"
        show ?thesis using hx\<sigma> \<open>\<sigma> = {q}\<close> hqe by (by100 blast)
      next
        assume "\<sigma> = e"
        show ?thesis using hx\<sigma> \<open>\<sigma> = e\<close> by (by100 simp)
      qed
    qed
  qed
next
  show "e \<subseteq> geotop_polyhedron L"
  proof
    fix x
    assume "x \<in> e"
    show "x \<in> geotop_polyhedron L"
      unfolding geotop_polyhedron_def using heL \<open>x \<in> e\<close> by (by100 blast)
  qed
qed

lemma geotop_two_degree_one_edge_delete_complement_complex_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes hqL: "{q} \<in> L"
  assumes hqcard: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 1"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes hqe: "q \<in> e"
  shows "geotop_is_complex (L - {{w}, {q}, e})"
proof -
  have hcomplex: "geotop_is_complex L"
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have hsub: "L - {{w}, {q}, e} \<subseteq> L"
    by (by100 simp)
  have hfaces:
      "\<forall>\<sigma>\<in>L - {{w}, {q}, e}. \<forall>\<tau>. geotop_is_face \<tau> \<sigma>
        \<longrightarrow> \<tau> \<in> L - {{w}, {q}, e}"
  proof (intro ballI allI impI)
    fix \<sigma> \<tau>
    assume h\<sigma>rest: "\<sigma> \<in> L - {{w}, {q}, e}"
    assume hface: "geotop_is_face \<tau> \<sigma>"
    have h\<sigma>L: "\<sigma> \<in> L"
      using h\<sigma>rest by (by100 simp)
    have h\<tau>L: "\<tau> \<in> L"
      using geotop_is_complex_face_closed[OF hcomplex] h\<sigma>L hface by (by100 blast)
    have h\<tau>sub\<sigma>: "\<tau> \<subseteq> \<sigma>"
      by (rule geotop_is_face_imp_subset_prefix[OF hface])
    have h\<sigma>ne_w: "\<sigma> \<noteq> {w}"
      using h\<sigma>rest by (by100 simp)
    have h\<sigma>ne_q: "\<sigma> \<noteq> {q}"
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
    have h\<tau>ne_q: "\<tau> \<noteq> {q}"
    proof
      assume h\<tau>q: "\<tau> = {q}"
      have hq\<sigma>: "q \<in> \<sigma>"
        using h\<tau>sub\<sigma> h\<tau>q by (by100 blast)
      have hcase: "\<sigma> = {q} \<or> \<sigma> = e"
        by (rule geotop_degree_one_vertex_simplex_containing_eq_vertex_or_edge_prefix
            [OF hL hfin hqL hqcard heL hedge hqe h\<sigma>L hq\<sigma>])
      show False using hcase h\<sigma>ne_q h\<sigma>ne_e by (by100 blast)
    qed
    have h\<tau>ne_e: "\<tau> \<noteq> e"
    proof
      assume h\<tau>e: "\<tau> = e"
      have hq\<sigma>: "q \<in> \<sigma>"
        using h\<tau>sub\<sigma> h\<tau>e hqe by (by100 blast)
      have hcase: "\<sigma> = {q} \<or> \<sigma> = e"
        by (rule geotop_degree_one_vertex_simplex_containing_eq_vertex_or_edge_prefix
            [OF hL hfin hqL hqcard heL hedge hqe h\<sigma>L hq\<sigma>])
      show False using hcase h\<sigma>ne_q h\<sigma>ne_e by (by100 blast)
    qed
    show "\<tau> \<in> L - {{w}, {q}, e}"
      using h\<tau>L h\<tau>ne_w h\<tau>ne_q h\<tau>ne_e by (by100 simp)
  qed
  show ?thesis
    by (rule geotop_complex_subset_is_complex[OF hcomplex hsub hfaces])
qed

lemma geotop_graph_endpoint_delete_leaf_neighbor_endpoint_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes hqL: "{q} \<in> L"
  assumes hqw: "q \<noteq> w"
  assumes hqe: "q \<in> e"
  assumes hqcard: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 2"
  shows "geotop_graph_endpoint (L - {{w}, e}) q"
proof -
  let ?S = "{l\<in>L. geotop_is_edge l \<and> q \<in> l}"
  let ?T = "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l}"
  have hrest_linear: "geotop_is_linear_graph (L - {{w}, e})"
    by (rule geotop_graph_endpoint_delete_leaf_linear_graph_prefix
        [OF hL hfin hend heL hedge hwe])
  have hq_ne_singleton: "{q} \<noteq> {w}"
    using hqw by (by100 blast)
  have hq_ne_e: "{q} \<noteq> e"
  proof
    assume hqe_single: "{q} = e"
    have "w \<in> {q}"
      using hwe hqe_single by (by100 simp)
    hence "w = q" by (by100 simp)
    thus False using hqw by (by100 blast)
  qed
  have hqrest: "{q} \<in> L - {{w}, e}"
    using hqL hq_ne_singleton hq_ne_e by (by100 simp)
  have heS: "e \<in> ?S"
    using heL hedge hqe by (by100 simp)
  have hfinS: "finite ?S"
    using hfin by (by100 simp)
  have hT_eq: "?T = ?S - {e}"
    by (rule geotop_delete_leaf_incident_edges_neighbor_eq_prefix[OF hqw])
  have hcard_minus: "card (?S - {e}) = card ?S - 1"
    using hfinS heS by (by100 simp)
  have hcard_T: "card ?T = 1"
    using hT_eq hcard_minus hqcard by (by100 simp)
  show ?thesis
    by (rule geotop_degree_one_vertex_graph_endpoint_prefix
        [OF hrest_linear hqrest hcard_T])
qed

lemma geotop_graph_endpoint_delete_leaf_degree_one_or_two_prefix:
  fixes L :: "(real^2) set set"
  assumes hL: "geotop_is_linear_graph L"
  assumes hfin: "finite L"
  assumes hend: "geotop_graph_endpoint L w"
  assumes heL: "e \<in> L"
  assumes hedge: "geotop_is_edge e"
  assumes hwe: "w \<in> e"
  assumes hqL: "{q} \<in> L"
  assumes hqw: "q \<noteq> w"
  assumes heq: "e = closed_segment w q"
  assumes hdegree12: "\<forall>x. {x} \<in> L \<longrightarrow>
      card {l\<in>L. geotop_is_edge l \<and> x \<in> l} = 1 \<or>
      card {l\<in>L. geotop_is_edge l \<and> x \<in> l} = 2"
  assumes hqcard: "card {l\<in>L. geotop_is_edge l \<and> q \<in> l} = 2"
  shows "\<forall>x. {x} \<in> L - {{w}, e} \<longrightarrow>
      card {l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l} = 1 \<or>
      card {l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l} = 2"
proof (intro allI impI)
  fix x
  assume hxrest: "{x} \<in> L - {{w}, e}"
  let ?Srest = "{l\<in>L - {{w}, e}. geotop_is_edge l \<and> x \<in> l}"
  let ?Sold = "{l\<in>L. geotop_is_edge l \<and> x \<in> l}"
  have hq_in_e: "q \<in> e"
    using heq by (by100 simp)
  show "card ?Srest = 1 \<or> card ?Srest = 2"
  proof (cases "x = q")
    case True
    have hrest_linear: "geotop_is_linear_graph (L - {{w}, e})"
      by (rule geotop_graph_endpoint_delete_leaf_linear_graph_prefix
          [OF hL hfin hend heL hedge hwe])
    have hq_endpoint: "geotop_graph_endpoint (L - {{w}, e}) q"
      by (rule geotop_graph_endpoint_delete_leaf_neighbor_endpoint_prefix
          [OF hL hfin hend heL hedge hwe hqL hqw hq_in_e hqcard])
    have hq_card: "card {l\<in>L - {{w}, e}. geotop_is_edge l \<and> q \<in> l} = 1"
      using geotop_graph_endpoint_singleton_and_card_one_prefix[OF hrest_linear hq_endpoint]
      by (by100 blast)
    show ?thesis using True hq_card by (by100 simp)
  next
    case False
    have hcard_eq: "card ?Srest = card ?Sold"
      by (rule geotop_delete_leaf_rest_vertex_degree_preserved_away_neighbor_prefix
          [OF hL heL hqw heq hxrest False])
    have hxL: "{x} \<in> L"
      using hxrest by (by100 simp)
    have hdegree_x: "card ?Sold = 1 \<or> card ?Sold = 2"
      using hdegree12 hxL by (by100 blast)
    show ?thesis using hcard_eq hdegree_x by (by100 simp)
  qed
qed

lemma geotop_complex_add_endpoint_edge_at_vertex_prefix:
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
          using geotop_is_face_imp_subset_prefix[OF hface] h\<sigma>w by (by100 simp)
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
          by (rule geotop_segment_face_cases_prefix[OF hface_seg hwq])
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

lemma geotop_graph_endpoint_delete_leaf_connected_prefix:
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
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have hR_complex: "geotop_is_complex ?R"
  proof (rule geotop_graph_endpoint_delete_leaf_complex_prefix
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
    proof (rule geotop_graph_endpoint_singleton_and_card_one_prefix[where L = L and w = w])
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
        proof (rule geotop_complex_add_endpoint_edge_at_vertex_prefix
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
        proof (rule geotop_complex_add_endpoint_edge_at_vertex_prefix
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

lemma geotop_two_degree_one_endpoint_edge_connected_exhausts_prefix:
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
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have hqe: "q \<in> e"
    using heq by (by100 simp)
  have hwq: "w \<noteq> q"
    using hqw by (by100 blast)
  have hK1_complex: "geotop_is_complex ?K1"
    by (rule geotop_complex_restrict_subset_is_complex[OF hcomplex])
  have hK2_complex: "geotop_is_complex ?K2"
  proof (rule geotop_two_degree_one_edge_delete_complement_complex_prefix
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
        by (rule geotop_1dim_simplex_subset_edge_cases_prefix
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

lemma geotop_two_degree_one_endpoint_edge_connected_polyhedron_eq_prefix:
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
  proof (rule geotop_two_degree_one_endpoint_edge_connected_exhausts_prefix
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
    by (rule geotop_polyhedron_two_vertices_edge_eq_prefix[OF hsub heL hwe hqe])
qed

lemma geotop_HOL_arcs_glue_disjoint_endpoints_start_prefix:
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

lemma geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_HOL_arc_from_endpoint_prefix:
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
    proof (rule geotop_graph_endpoint_unique_segment_neighbor_prefix[where L = L and w = w])
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
        proof (rule geotop_two_degree_one_endpoint_edge_connected_polyhedron_eq_prefix
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
          using geotop_closed_segment_HOL_arc_between_prefix[OF hwq] by (by100 blast)
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
        proof (rule geotop_graph_endpoint_delete_leaf_linear_graph_prefix
            [where L = L and w = w and e = e])
          show "geotop_is_linear_graph L" by (rule hL)
          show "finite L" by (rule hfinL)
          show "geotop_graph_endpoint L w" by (rule hend)
          show "e \<in> L" by (rule heL)
          show "geotop_is_edge e" by (rule hedge)
          show "w \<in> e" by (rule hwe)
        qed
        have hR_conn: "geotop_complex_connected ?R"
        proof (rule geotop_graph_endpoint_delete_leaf_connected_prefix
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
        proof (rule geotop_graph_endpoint_delete_leaf_degree_one_or_two_prefix
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
        proof (rule geotop_graph_endpoint_delete_leaf_neighbor_endpoint_prefix
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
            using geotop_closed_segment_HOL_arc_between_prefix[OF hwq] by (by100 blast)
          show ?thesis
            using h\<gamma>1_arc h\<gamma>1_pim h\<gamma>1_start h\<gamma>1_finish heq by (by100 blast)
        qed
        have hdisj: "e \<inter> geotop_polyhedron ?R = {q}"
        proof (rule geotop_delete_leaf_edge_inter_rest_polyhedron_eq_neighbor_prefix
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
          by (rule geotop_HOL_arcs_glue_disjoint_endpoints_start_prefix
              [OF hseg_arc hrest_arc hdisj])
        have hpoly_union: "geotop_polyhedron L = e \<union> geotop_polyhedron ?R"
        proof (rule geotop_graph_endpoint_delete_leaf_polyhedron_union_prefix
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

lemma geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_HOL_arc_prefix:
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
  proof (rule geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_HOL_arc_from_endpoint_prefix
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

lemma geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_arc_prefix:
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
  proof (rule geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_HOL_arc_prefix
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

lemma geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_broken_line_prefix:
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
    by (rule geotop_linear_graph_complex_prefix[OF hL])
  have h1dim: "geotop_complex_is_1dim L"
    by (rule geotop_linear_graph_1dim_prefix[OF hL])
  have harc: "geotop_is_arc (geotop_polyhedron L)
      (subspace_topology UNIV geotop_euclidean_topology (geotop_polyhedron L))"
  proof (rule geotop_finite_connected_degree_one_or_two_endpoint_linear_graph_arc_prefix
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
